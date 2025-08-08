#!/usr/bin/env python3
"""
Verus自动证明器
使用LLM自动生成和修复Verus证明
"""

import os
import sys
import json
import time
import logging
import subprocess
from datetime import datetime
from pathlib import Path
from typing import List, Tuple, Dict, Optional
try:
    import google.generativeai as genai
except ImportError:
    genai = None

try:
    from openai import OpenAI
except ImportError:
    OpenAI = None

class VerusAutoProver:
    def __init__(self, api_key: str, max_iterations: int = 5, use_gemini: bool = False):
        """
        初始化自动证明器
        
        Args:
            api_key: API密钥
            max_iterations: 最大迭代次数
            use_gemini: 是否使用Gemini API
        """
        self.use_gemini = use_gemini
        self.max_iterations = max_iterations
        self.setup_logging()
        
        # 初始化API客户端
        if use_gemini:
            if genai is None:
                raise ImportError("google-generativeai package is required for Gemini API")
            genai.configure(api_key=api_key)
            self.gemini_model = genai.GenerativeModel('gemini-2.0-flash-exp')
        else:
            if OpenAI is None:
                raise ImportError("openai package is required for OpenAI API")
            self.client = OpenAI(api_key=api_key)
        
        # 统计信息
        self.stats = {
            'total_iterations': 0,
            'z3_counterexample_generated': False,
            'z3_counterexample_successful': False,
            'final_error_type': None,  # 'compilation_error', 'verification_error', 'success'
            'compilation_errors': 0,
            'verification_errors': 0,
            # Token统计
            'total_prompt_tokens': 0,
            'total_completion_tokens': 0,
            'total_tokens': 0,
            'api_calls': 0,
            'token_usage_by_iteration': {}  # 记录每次迭代的token使用情况
        }
        
        # 当前处理文件的CTX文件夹路径
        self.current_ctx_folder = None
        
        # 加载模型配置
        prompts = self.load_prompts()
        self.model_config = prompts.get("model_config", {})
        
    def setup_logging(self):
        """设置日志记录"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_filename = f"verus_proof_log_{timestamp}.log"
        
        # 配置日志格式
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler(log_filename, encoding='utf-8'),
                logging.StreamHandler(sys.stdout)  # 同时输出到控制台
            ]
        )
        
        self.logger = logging.getLogger(__name__)
        self.logger.info(f"=== Verus Auto Prover Session Started ===")
        self.logger.info(f"Log file: {log_filename}")
        self.logger.info(f"Max iterations: {self.max_iterations}")
        self.logger.info(f"Using {'Gemini' if self.use_gemini else 'OpenAI'} API")
        
    def log_interaction(self, step_type: str, iteration: int, prompt: str = "", response: str = "", error: str = ""):
        """记录交互信息"""
        self.logger.info(f"\n{'='*80}")
        self.logger.info(f"STEP: {step_type} - Iteration {iteration}")
        self.logger.info(f"{'='*80}")
        
        # 只记录关键信息，不重复记录prompt
        if step_type == "Z3_COUNTEREXAMPLE_GENERATION":
            self.logger.info(f"Generating Z3 counterexample code...")
        elif step_type == "Z3_COUNTEREXAMPLE_RESPONSE":
            self.logger.info(f"Z3 code generated successfully")
        elif step_type == "INITIAL_PROOF_GENERATION":
            self.logger.info(f"Generating initial proof...")
        elif step_type == "PROOF_FIX_GENERATION":
            self.logger.info(f"Generating proof fix...")
        elif step_type == "VERIFICATION_FAILED":
            self.logger.info(f"Verification failed")
            
        if response and step_type in ["Z3_COUNTEREXAMPLE_RESPONSE", "INITIAL_PROOF_RESPONSE", "PROOF_FIX_RESPONSE"]:
            self.logger.info(f"\n--- LM RESPONSE (truncated) ---")
            # 只记录响应的前200个字符
            truncated_response = response[:200] + "..." if len(response) > 200 else response
            self.logger.info(truncated_response)
            
        if error:
            self.logger.info(f"\n--- VERUS ERROR ---")
            self.logger.info(error)
            
        self.logger.info(f"{'='*80}\n")
        
    def record_token_usage(self, response, iteration: int, step_type: str):
        """
        记录token使用情况
        
        Args:
            response: API响应
            iteration: 当前迭代次数
            step_type: 步骤类型
        """
        if self.use_gemini:
            # Gemini API的token统计
            if hasattr(response, 'usage_metadata'):
                usage = response.usage_metadata
                prompt_tokens = usage.prompt_token_count
                completion_tokens = usage.candidates_token_count
                total_tokens = prompt_tokens + completion_tokens
            else:
                # 估算token使用
                prompt_tokens = len(response.text.split()) * 1.3  # 粗略估算
                completion_tokens = len(response.text.split()) * 1.3
                total_tokens = prompt_tokens + completion_tokens
        else:
            # OpenAI API的token统计
            if hasattr(response, 'usage') and response.usage:
                usage = response.usage
                prompt_tokens = usage.prompt_tokens
                completion_tokens = usage.completion_tokens
                total_tokens = usage.total_tokens
            else:
                prompt_tokens = 0
                completion_tokens = 0
                total_tokens = 0
        
        # 更新总统计
        self.stats['total_prompt_tokens'] += int(prompt_tokens)
        self.stats['total_completion_tokens'] += int(completion_tokens)
        self.stats['total_tokens'] += int(total_tokens)
        self.stats['api_calls'] += 1
        
        # 更新迭代统计
        if iteration not in self.stats['token_usage_by_iteration']:
            self.stats['token_usage_by_iteration'][iteration] = {
                'prompt_tokens': 0,
                'completion_tokens': 0,
                'total_tokens': 0,
                'api_calls': 0,
                'steps': {}
            }
        
        self.stats['token_usage_by_iteration'][iteration]['prompt_tokens'] += int(prompt_tokens)
        self.stats['token_usage_by_iteration'][iteration]['completion_tokens'] += int(completion_tokens)
        self.stats['token_usage_by_iteration'][iteration]['total_tokens'] += int(total_tokens)
        self.stats['token_usage_by_iteration'][iteration]['api_calls'] += 1
        
        # 更新步骤统计
        if step_type not in self.stats['token_usage_by_iteration'][iteration]['steps']:
            self.stats['token_usage_by_iteration'][iteration]['steps'][step_type] = {
                'prompt_tokens': 0,
                'completion_tokens': 0,
                'total_tokens': 0
            }
        
        self.stats['token_usage_by_iteration'][iteration]['steps'][step_type]['prompt_tokens'] += int(prompt_tokens)
        self.stats['token_usage_by_iteration'][iteration]['steps'][step_type]['completion_tokens'] += int(completion_tokens)
        self.stats['token_usage_by_iteration'][iteration]['steps'][step_type]['total_tokens'] += int(total_tokens)
        
        # 记录到日志
        self.logger.info(f"Token usage for {step_type} (Iteration {iteration}):")
        self.logger.info(f"  Prompt tokens: {int(prompt_tokens)}")
        self.logger.info(f"  Completion tokens: {int(completion_tokens)}")
        self.logger.info(f"  Total tokens: {int(total_tokens)}")
        self.logger.info(f"Total token usage so far:")
        self.logger.info(f"  Total prompt tokens: {self.stats['total_prompt_tokens']}")
        self.logger.info(f"  Total completion tokens: {self.stats['total_completion_tokens']}")
        self.logger.info(f"  Total tokens: {self.stats['total_tokens']}")
        self.logger.info(f"  API calls: {self.stats['api_calls']}")
        self.logger.info(f"{'='*80}")
        
    def load_prompts(self) -> dict:
        """加载prompt模板"""
        try:
            with open('prompts.json', 'r', encoding='utf-8') as f:
                return json.load(f)
        except FileNotFoundError:
            self.logger.error("prompts.json not found")
            return {}
        except json.JSONDecodeError as e:
            self.logger.error(f"Error parsing prompts.json: {e}")
            return {}
    
    def extract_rust_code(self, content: str) -> str:
        """从LLM响应中提取Rust代码"""
        # 移除markdown代码块标记
        if '```rust' in content:
            start = content.find('```rust') + 7
            end = content.find('```', start)
            if end != -1:
                return content[start:end].strip()
        
        if '```' in content:
            start = content.find('```') + 3
            end = content.find('```', start)
            if end != -1:
                return content[start:end].strip()
        
        # 如果没有代码块标记，返回整个内容
        return content.strip()
    
    def call_llm_with_retry(self, prompt: str, step_type: str, max_retries: int = 3) -> str:
        """
        调用LLM，带重试机制
        
        Args:
            prompt: 提示词
            step_type: 步骤类型
            max_retries: 最大重试次数
            
        Returns:
            LLM响应内容
        """
        for attempt in range(max_retries):
            try:
                if self.use_gemini:
                    response = self.gemini_model.generate_content(prompt)
                    content = response.text.strip()
                else:
                    response = self.client.chat.completions.create(
                        model=self.model_config.get("model", "gpt-4o"),
                        messages=[{"role": "user", "content": prompt}],
                        temperature=self.model_config.get("temperature", 0.1),
                        max_tokens=self.model_config.get("max_tokens", 4000)
                    )
                    content = response.choices[0].message.content.strip()
                
                # 检查拒绝消息
                if "I'm sorry, but I can't assist with that request" in content or "I'm sorry" in content[:50]:
                    self.logger.warning(f"LLM returned rejection message on attempt {attempt + 1}")
                    if attempt < max_retries - 1:
                        simplified_prompt = self.simplify_prompt_for_retry(prompt, step_type)
                        prompt = simplified_prompt  # 更新prompt用于重试
                        continue
                    else:
                        self.logger.error(f"All {max_retries} attempts failed for {step_type}")
                        return content
                
                return content
                
            except Exception as e:
                self.logger.error(f"LLM call failed on attempt {attempt + 1}: {e}")
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                    continue
                else:
                    raise e
        return ""
    
    def simplify_prompt_for_retry(self, original_prompt: str, step_type: str) -> str:
        """
        为重试生成简化的prompt
        
        Args:
            original_prompt: 原始prompt
            step_type: 步骤类型
            
        Returns:
            简化的prompt
        """
        if step_type == "Z3_COUNTEREXAMPLE_GENERATION":
            # 简化的Z3反例生成prompt
            try:
                code_part = original_prompt.split('**Original Rust/Verus Code:**')[1].split('**Verus Verification Error:**')[0]
                error_part = original_prompt.split('**Verus Verification Error:**')[1].split('**Task:**')[0]
                
                return f"""Generate a Python program using z3-solver to find counterexamples for this verification failure:

Code: {code_part}

Error: {error_part}

Requirements:
- Use `from z3 import *`
- Create Z3 variables for function parameters
- Find concrete variable assignments that cause the failure
- Print results clearly

Generate the Z3 solver code:"""
            except:
                return original_prompt
                
        elif step_type in ["INITIAL_PROOF_GENERATION", "PROOF_FIX_GENERATION"]:
            # 简化的证明生成prompt
            try:
                code_part = original_prompt.split('**Original Code:**')[1].split('**CRITICAL OUTPUT REQUIREMENT:**')[0]
                
                return f"""Generate Verus proof annotations for this code:

{code_part}

Add only proof annotations (invariants, assertions, proof blocks). Do not modify the original code.

Generate the complete Verus code:"""
            except:
                return original_prompt
                
        return original_prompt

    def generate_initial_proof(self, code: str) -> str:
        """生成初始证明"""
        try:
            prompts = self.load_prompts()
            prompt_template = prompts.get("initial_proof_generation", {}).get("template", "")
            
            if not prompt_template:
                self.logger.error("Initial proof generation prompt template not found")
                return code
            
            prompt = prompt_template.format(code=code)
            
            self.log_interaction("INITIAL_PROOF_GENERATION", 0, prompt)
            
            response_content = self.call_llm_with_retry(prompt, "INITIAL_PROOF_GENERATION")
            
            # 处理LLM拒绝的情况
            if "I'm sorry" in response_content[:100]:
                self.logger.warning("LLM rejected the request for initial proof generation")
                return code  # 返回原始代码
            
            # 记录token使用
            if self.use_gemini:
                # 为Gemini创建模拟响应对象
                class MockResponse:
                    def __init__(self, content):
                        self.text = content
                        self.usage_metadata = type('obj', (object,), {
                            'prompt_token_count': len(content.split()) * 1.3,
                            'candidates_token_count': len(content.split()) * 1.3
                        })()
                
                mock_response = MockResponse(response_content)
            else:
                mock_response = type('obj', (object,), {
                    'usage': type('obj', (object,), {
                        'prompt_tokens': len(prompt.split()) * 1.3,
                        'completion_tokens': len(response_content.split()) * 1.3,
                        'total_tokens': len(prompt.split()) * 1.3 + len(response_content.split()) * 1.3
                    })()
                })()
            
            self.record_token_usage(mock_response, 0, "INITIAL_PROOF_GENERATION")
            
            self.log_interaction("INITIAL_PROOF_RESPONSE", 0, "", response_content)
            
            return self.extract_rust_code(response_content)
            
        except Exception as e:
            self.logger.error(f"生成初始proof时出错: {e}")
            return code
    
    def fix_proof(self, current_code: str, error_message: str, history: List[str], counterexample_info: str = "", iteration: int = 0) -> str:
        """修复证明"""
        try:
            prompts = self.load_prompts()
            prompt_template = prompts.get("iterative_fix", {}).get("template", "")
            
            if not prompt_template:
                self.logger.error("Iterative fix prompt template not found")
                return current_code
        
            # 构建历史信息
            history_text = "\n".join([f"Attempt {i+1}: {code}" for i, code in enumerate(history[-3:])])
        
            # 构建反例信息
            counterexample_section = ""
            if counterexample_info:
                counterexample_section = f"\n**Counterexample Information:**\n{counterexample_info}\n"
            
            prompt = prompt_template.format(
                history=history_text,
                current_code=current_code,
                error_message=error_message,
                counterexample_section=counterexample_section
            )
        
            self.log_interaction("PROOF_FIX_GENERATION", iteration, prompt)
            
            response_content = self.call_llm_with_retry(prompt, "PROOF_FIX_GENERATION", iteration)
            
            # 处理LLM拒绝的情况
            if "I'm sorry" in response_content[:100]:
                self.logger.warning("LLM rejected the request for proof fix generation")
                return current_code  # 返回当前代码
            
            # 记录token使用
            if self.use_gemini:
                # 为Gemini创建模拟响应对象
                class MockResponse:
                    def __init__(self, content):
                        self.text = content
                        self.usage_metadata = type('obj', (object,), {
                            'prompt_token_count': len(content.split()) * 1.3,
                            'candidates_token_count': len(content.split()) * 1.3
                        })()
                
                mock_response = MockResponse(response_content)
            else:
                mock_response = type('obj', (object,), {
                    'usage': type('obj', (object,), {
                        'prompt_tokens': len(prompt.split()) * 1.3,
                        'completion_tokens': len(response_content.split()) * 1.3,
                        'total_tokens': len(prompt.split()) * 1.3 + len(response_content.split()) * 1.3
                    })()
                })()
            
            self.record_token_usage(mock_response, iteration, "PROOF_FIX_GENERATION")
            
            self.log_interaction("PROOF_FIX_RESPONSE", iteration, "", response_content)
            
            return self.extract_rust_code(response_content)
            
        except Exception as e:
            self.logger.error(f"修复proof时出错: {e}")
            return current_code
    
    def verify_with_verus(self, code: str, file_path: str) -> Tuple[bool, str, str]:
        """
        使用Verus验证代码
        
        Args:
            code: 要验证的代码
            file_path: 文件路径
            
        Returns:
            (是否成功, 输出, 错误信息)
        """
        try:
            # 创建临时文件
            temp_file = Path(file_path)
            temp_file.write_text(code, encoding='utf-8')
            
            # 运行Verus验证
            result = subprocess.run(
                ['verus', str(temp_file)],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            success = result.returncode == 0
            output = result.stdout
            error = result.stderr
            
            return success, output, error
                
        except subprocess.TimeoutExpired:
            return False, "", "Verification timeout"
        except Exception as e:
            return False, "", f"Verification error: {e}"
    
    def is_compilation_error(self, error_message: str) -> bool:
        """判断是否为编译错误"""
        compilation_keywords = [
            'error[E', 'syntax error', 'type error',
            'mismatched types', 'expected', 'found',
            'unknown start of token', 'expected one of',
            'missing', 'unexpected', 'invalid',
            'cannot find', 'use of moved value', 'cannot borrow'
        ]
        
        # Verus验证错误关键词（不应该被分类为编译错误）
        verus_verification_keywords = [
            'postcondition not satisfied',
            'precondition not satisfied', 
            'invariant not satisfied',
            'assertion failed',
            'verification failed',
            'loop must have a decreases clause'
        ]
        
        error_lower = error_message.lower()
        
        # 如果包含Verus验证错误关键词，则不是编译错误
        if any(keyword.lower() in error_lower for keyword in verus_verification_keywords):
            return False
            
        # 只有包含真正的编译错误关键词才认为是编译错误
        return any(keyword.lower() in error_lower for keyword in compilation_keywords)

    def needs_counterexample_generation(self, error_message: str) -> bool:
        """判断是否需要生成反例"""
        # 编译错误不需要生成反例
        if self.is_compilation_error(error_message):
            return False
        
        # 验证错误需要生成反例
        verification_keywords = [
            'postcondition not satisfied',
            'precondition not satisfied',
            'invariant not satisfied',
            'assertion failed',
            'verification failed'
        ]
        
        error_lower = error_message.lower()
        return any(keyword.lower() in error_lower for keyword in verification_keywords)

    def generate_z3_counterexample(self, code: str, error_message: str, iteration: int = 0) -> str:
        """生成Z3反例代码"""
        try:
            prompts = self.load_prompts()
            prompt_template = prompts.get("z3_counterexample_generation", {}).get("template", "")
            
            if not prompt_template:
                self.logger.error("Z3 counterexample generation prompt template not found")
                return ""
            
            prompt = prompt_template.format(
                current_code=code,
                error_message=error_message
            )
        
            self.log_interaction("Z3_COUNTEREXAMPLE_GENERATION", iteration, prompt)
            
            response_content = self.call_llm_with_retry(prompt, "Z3_COUNTEREXAMPLE_GENERATION", iteration)
            
            # 处理LLM拒绝的情况
            if "I'm sorry" in response_content[:100]:
                self.logger.warning("LLM rejected the request for Z3 counterexample generation")
                return ""
            
            # 记录token使用
            if self.use_gemini:
                # 为Gemini创建模拟响应对象
                class MockResponse:
                    def __init__(self, content):
                        self.text = content
                        self.usage_metadata = type('obj', (object,), {
                            'prompt_token_count': len(content.split()) * 1.3,
                            'candidates_token_count': len(content.split()) * 1.3
                        })()
                
                mock_response = MockResponse(response_content)
            else:
                mock_response = type('obj', (object,), {
                    'usage': type('obj', (object,), {
                        'prompt_tokens': len(prompt.split()) * 1.3,
                        'completion_tokens': len(response_content.split()) * 1.3,
                        'total_tokens': len(prompt.split()) * 1.3 + len(response_content.split()) * 1.3
                    })()
                })()
            
            self.record_token_usage(mock_response, iteration, "Z3_COUNTEREXAMPLE_GENERATION")
            
            self.log_interaction("Z3_COUNTEREXAMPLE_RESPONSE", iteration, "", response_content)
            
            return response_content
            
        except Exception as e:
            self.logger.error(f"生成z3代码时出错: {e}")
            return ""
    
    def run_z3_solver(self, z3_code: str, ctx_folder: Path) -> Tuple[bool, str]:
        """
        运行Z3求解器
        
        Args:
            z3_code: Z3代码
            ctx_folder: CTX文件夹路径
            
        Returns:
            (是否成功, 输出)
        """
        try:
            # 保存Z3代码
            z3_file = ctx_folder / "z3_counterexample.py"
            z3_file.write_text(z3_code, encoding='utf-8')
            
            # 运行Z3求解器
            result = subprocess.run(
                ['python3', str(z3_file)],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # 保存结果
            counterexample_file = ctx_folder / "counterexamples.txt"
            with open(counterexample_file, 'w', encoding='utf-8') as f:
                f.write("Z3 Solver Execution Results\n")
                f.write("=" * 25 + "\n")
                f.write(f"Return code: {result.returncode}\n")
                f.write(f"Output:\n{result.stdout}\n")
                if result.stderr:
                    f.write(f"Error:\n{result.stderr}\n")
            
            self.logger.info(f"Z3 files saved to: {ctx_folder}")
            
            return result.returncode == 0, result.stdout
                
        except subprocess.TimeoutExpired:
            return False, "Z3 solver timeout"
        except Exception as e:
            return False, f"Z3 solver error: {e}"
    
    def create_project_folder(self, original_file: Path) -> dict:
        """创建项目文件夹结构"""
        # 在results目录下创建项目文件夹
        results_dir = Path("results")
        results_dir.mkdir(exist_ok=True)
        
        project_name = original_file.stem
        project_folder = results_dir / project_name
        
        # 创建文件夹结构
        unverified_folder = project_folder / "unverified"
        verified_folder = project_folder / "verified"
        history_folder = project_folder / "history"
        ctx_folder = project_folder / "CTX"
        
        for folder in [unverified_folder, verified_folder, history_folder, ctx_folder]:
            folder.mkdir(parents=True, exist_ok=True)
        
        # 复制原始文件到unverified文件夹
        original_copy = unverified_folder / original_file.name
        original_copy.write_text(original_file.read_text(encoding='utf-8'), encoding='utf-8')
        
        self.current_ctx_folder = ctx_folder
        
        return {
            'project_folder': project_folder,
            'unverified_folder': unverified_folder,
            'verified_folder': verified_folder,
            'history_folder': history_folder,
            'ctx_folder': ctx_folder
        }
    
    def save_iteration(self, code: str, iteration: int, history_folder: Path):
        """保存迭代结果"""
        iteration_file = history_folder / f"{iteration}.rs"
        iteration_file.write_text(code, encoding='utf-8')
        print(f"保存第{iteration}次迭代到: {iteration_file}")
    
    def save_verified_result(self, code: str, verified_folder: Path):
        """保存验证成功的结果"""
        verified_file = verified_folder / "verified.rs"
        verified_file.write_text(code, encoding='utf-8')
        print(f"验证成功！保存到: {verified_file}")

    def save_token_statistics(self, results_folder: Path):
        """保存token统计信息"""
        stats_file = results_folder / "token_statistics.json"
        
        # 准备统计数据
        stats_data = {
            "total_statistics": {
                "total_prompt_tokens": self.stats['total_prompt_tokens'],
                "total_completion_tokens": self.stats['total_completion_tokens'],
                "total_tokens": self.stats['total_tokens'],
                "api_calls": self.stats['api_calls'],
                "total_iterations": self.stats['total_iterations']
            },
            "iteration_statistics": self.stats['token_usage_by_iteration'],
            "verification_results": {
                "final_error_type": self.stats['final_error_type'],
                "compilation_errors": self.stats['compilation_errors'],
                "verification_errors": self.stats['verification_errors'],
                "z3_counterexample_generated": self.stats['z3_counterexample_generated'],
                "z3_counterexample_successful": self.stats['z3_counterexample_successful']
            }
        }
        
        with open(stats_file, 'w', encoding='utf-8') as f:
            json.dump(stats_data, f, indent=2, ensure_ascii=False)
        
        print(f"Token统计信息已保存到: {stats_file}")
        
        # 打印统计摘要
        print(f"\n=== TOKEN USAGE SUMMARY ===")
        print(f"总API调用次数: {self.stats['api_calls']}")
        print(f"总Prompt Tokens: {self.stats['total_prompt_tokens']:,}")
        print(f"总Completion Tokens: {self.stats['total_completion_tokens']:,}")
        print(f"总Tokens: {self.stats['total_tokens']:,}")
        if self.stats['api_calls'] > 0:
            print(f"平均每次调用Tokens: {self.stats['total_tokens'] // self.stats['api_calls']:,}")
        print("=" * 30)
    
    def process_file(self, file_path: str) -> bool:
        """处理单个文件"""
        try:
            file_path = Path(file_path)
            if not file_path.exists():
                self.logger.error(f"File not found: {file_path}")
                return False
        
            self.logger.info(f"=== Starting file processing: {file_path} ===")
        
            # 读取原始代码
            original_code = file_path.read_text(encoding='utf-8')
            self.logger.info(f"\n--- ORIGINAL CODE ---")
            self.logger.info(original_code)
            self.logger.info(f"--- END ORIGINAL CODE ---")
            
            # 创建项目文件夹
            folders = self.create_project_folder(file_path)
            
            # 初始化历史记录
            history = []
            current_code = original_code
            
            print(f"开始处理文件: {file_path}")
            
            # 主循环
            for iteration in range(self.max_iterations + 1):
                self.stats['total_iterations'] = iteration
                
                if iteration == 0:
                    print(f"阶段1：正在生成初始proof...")
                    self.logger.info(f"=== PHASE 1: INITIAL PROOF GENERATION ===")
                    
                    # 生成初始证明
                    current_code = self.generate_initial_proof(original_code)
                    history.append(current_code)
                    
                else:
                    print(f"阶段{iteration + 1}：第{iteration}次验证...")
                    
                    # 保存当前迭代
                    self.save_iteration(current_code, iteration, folders['history_folder'])
                    
                    print(f"  子阶段2.1：Verus验证...")
                    
                    # 验证代码
                    success, output, error = self.verify_with_verus(current_code, folders['history_folder'] / f"temp_{iteration}.rs")
            
                    if success:
                        print("验证成功！")
                        self.logger.info(f"\n=== VERIFICATION SUCCESSFUL at iteration {iteration} ===")
                        self.stats['final_error_type'] = 'success'
                        
                        # 保存验证成功的结果
                        self.save_verified_result(current_code, folders['verified_folder'])
                        self.save_token_statistics(folders['project_folder'])
                        
                        # 打印详细统计
                        print(f"\n📊 详细统计信息:")
                        print(f"🔄 总迭代次数: {iteration}")
                        print(f"📝 最终状态: success")
                        print(f"🔧 编译错误次数: {self.stats['compilation_errors']}")
                        print(f"🔍 验证错误次数: {self.stats['verification_errors']}")
                        print(f"🧮 Z3反例生成尝试: {'是' if self.stats['z3_counterexample_generated'] else '否'}")
                        print(f"✅ Z3反例生成成功: {'是' if self.stats['z3_counterexample_successful'] else '否'}")
                        print(f"\n✅ 文件处理成功！")
                        
                        self.logger.info(f"=== File processing completed successfully ===")
                        return True
                    
                    else:
                        print("验证失败，错误信息:", error)
                        self.log_interaction("VERIFICATION_FAILED", iteration, "", "", error)
                        
                        # 分析错误类型
                        if self.is_compilation_error(error):
                            self.stats['compilation_errors'] += 1
                            print("  子阶段2.2：错误分析...")
                            print("  子阶段2.3：检测到编译错误，跳过反例生成")
                            
                            # 编译错误不生成反例
                            self.stats['z3_counterexample_generated'] = False
                            self.stats['z3_counterexample_successful'] = False
                            
                        else:
                            self.stats['verification_errors'] += 1
                            print("  子阶段2.2：错误分析...")
                            print("  子阶段2.3：检测到证明失败，正在生成反例...")
                            
                            # 生成反例
                            self.stats['z3_counterexample_generated'] = True
                            z3_code = self.generate_z3_counterexample(current_code, error, iteration)
                            
                            if z3_code:
                                print("  子阶段2.4：运行Z3求解器...")
                                success, output = self.run_z3_solver(z3_code, folders['ctx_folder'])
                                
                                if success and output.strip():
                                    print("反例生成成功！")
                                    self.stats['z3_counterexample_successful'] = True
                                    self.logger.info(f"\n--- COUNTEREXAMPLES GENERATED SUCCESSFULLY ---")
                                    self.logger.info(f"Counterexamples found: {len(output.strip().split('Counterexample')) - 1}")
                                    self.logger.info(f"--- END COUNTEREXAMPLES ---")
                                else:
                                    print("z3代码生成失败")
                                    self.stats['z3_counterexample_successful'] = False
                            else:
                                print("z3代码生成失败")
                                self.stats['z3_counterexample_successful'] = False
                        
                        # 记录反例统计
                        self.logger.info(f"=== COUNTEREXAMPLE STATISTICS ===")
                        self.logger.info(f"Counterexample generation attempted: {self.stats['z3_counterexample_generated']}")
                        self.logger.info(f"Counterexample generation successful: {self.stats['z3_counterexample_successful']}")
                        self.logger.info(f"=== END COUNTEREXAMPLE STATISTICS ===")
                        
                        print(f"  子阶段2.5：正在进行第{iteration}次修复...")
                        
                        # 修复证明
                        fixed_code = self.fix_proof(current_code, error, history, output if 'output' in locals() else "", iteration)
                        current_code = fixed_code
                        history.append(current_code)
            
            # 达到最大迭代次数
            print(f"达到最大迭代次数({self.max_iterations})，未能成功验证")
            self.logger.info(f"\n=== REACHED MAX ITERATIONS ({self.max_iterations}) - FAILED ===")
            
            if self.stats['compilation_errors'] > 0:
                self.stats['final_error_type'] = 'compilation_error'
            elif self.stats['verification_errors'] > 0:
                self.stats['final_error_type'] = 'verification_error'
            else:
                self.stats['final_error_type'] = 'unknown_error'
            
            self.save_token_statistics(folders['project_folder'])
            
            # 打印详细统计
            print(f"\n📊 详细统计信息:")
            print(f"🔄 总迭代次数: {self.max_iterations}")
            print(f"📝 最终状态: {self.stats['final_error_type']}")
            print(f"🔧 编译错误次数: {self.stats['compilation_errors']}")
            print(f"🔍 验证错误次数: {self.stats['verification_errors']}")
            print(f"🧮 Z3反例生成尝试: {'是' if self.stats['z3_counterexample_generated'] else '否'}")
            print(f"✅ Z3反例生成成功: {'是' if self.stats['z3_counterexample_successful'] else '否'}")
            print(f"\n❌ 文件处理失败！")
            
            self.logger.info(f"=== File processing completed with failure ===")
            return False
        
        except Exception as e:
            self.logger.error(f"处理文件时出错: {e}")
            return False

def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Verus Auto Prover')
    parser.add_argument('file', help='Rust/Verus file to process')
    parser.add_argument('--api-key', required=True, help='API key')
    parser.add_argument('--max-iterations', type=int, default=5, help='Maximum iterations')
    parser.add_argument('--use-gemini', action='store_true', default=False, help='Use Gemini API instead of OpenAI')
    
    args = parser.parse_args()
    
    # 创建prover实例
    prover = VerusAutoProver(
        api_key=args.api_key,
        max_iterations=args.max_iterations,
        use_gemini=args.use_gemini
    )
    
    # 处理文件
    success = prover.process_file(args.file)
    
    if success:
        print("✅ 处理成功")
        sys.exit(0)
    else:
        print("❌ 处理失败")
        sys.exit(1)

if __name__ == "__main__":
    main()