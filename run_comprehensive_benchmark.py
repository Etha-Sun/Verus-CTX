#!/usr/bin/env python3
"""
全面的基准测试脚本
运行所有benchmarks文件并生成详细Excel报告
"""

import os
import sys
import subprocess
import json
import re
from pathlib import Path
from datetime import datetime
import pandas as pd
from typing import List, Dict, Any

def extract_verus_error(error_output: str) -> str:
    """提取简化的Verus错误信息"""
    if not error_output:
        return ""
    
    # 提取关键错误信息
    lines = error_output.split('\n')
    error_lines = []
    
    for line in lines:
        if any(keyword in line.lower() for keyword in [
            'error:', 'failed', 'not satisfied', 'assertion failed',
            'invariant not satisfied', 'decreases not satisfied',
            'postcondition', 'precondition', 'verification failed'
        ]):
            # 简化错误信息
            simplified = line.strip()
            if len(simplified) > 80:
                simplified = simplified[:80] + "..."
            error_lines.append(simplified)
    
    return "; ".join(error_lines[:2])  # 只保留前2个错误

def extract_iteration_details(project_folder: Path, output: str) -> List[Dict[str, Any]]:
    """提取每次迭代的详细信息"""
    iteration_details = []
    
    # 读取token统计文件
    token_file = project_folder / "token_statistics.json"
    token_data = {}
    if token_file.exists():
        try:
            with open(token_file, 'r', encoding='utf-8') as f:
                token_data = json.load(f)
        except:
            pass
    
    # 从输出中提取每次迭代的验证结果
    output_lines = output.split('\n')
    verification_errors = []
    
    # 查找验证错误
    for i, line in enumerate(output_lines):
        if "验证失败，错误信息:" in line:
            error_start = i + 1
            error_lines = []
            # 收集错误信息直到下一个阶段
            for j in range(error_start, min(error_start + 10, len(output_lines))):
                if output_lines[j].strip() and not output_lines[j].startswith("  子阶段"):
                    error_lines.append(output_lines[j].strip())
                else:
                    break
            verification_errors.append("\n".join(error_lines))
    
    # 为每次迭代创建详细信息
    max_iterations = 5
    for iteration in range(1, max_iterations + 1):
        detail = {
            'iteration': iteration,
            'error_type': 'unknown',
            'verus_error': '',
            'counterexample_generated': False,
            'counterexample_count': 0,
            'token_cost': 0
        }
        
        # 从token数据中获取信息
        if str(iteration) in token_data.get('iteration_statistics', {}):
            iter_stats = token_data['iteration_statistics'][str(iteration)]
            detail['token_cost'] = iter_stats.get('total_tokens', 0)
            
            # 检查是否有反例生成
            if 'Z3_COUNTEREXAMPLE_GENERATION' in iter_stats.get('steps', {}):
                detail['counterexample_generated'] = True
        
        # 从验证结果中获取错误类型
        if iteration - 1 < len(verification_errors):
            detail['verus_error'] = extract_verus_error(verification_errors[iteration - 1])
            
            # 判断错误类型
            error_text = verification_errors[iteration - 1].lower()
            if any(keyword in error_text for keyword in ['postcondition', 'precondition', 'assertion', 'invariant']):
                detail['error_type'] = 'verification_error'
            elif any(keyword in error_text for keyword in ['error[e', 'syntax error', 'type error']):
                detail['error_type'] = 'compilation_error'
        
        # 检查反例文件
        ctx_folder = project_folder / "CTX"
        if ctx_folder.exists():
            counterexample_file = ctx_folder / "counterexamples.txt"
            if counterexample_file.exists():
                try:
                    content = counterexample_file.read_text(encoding='utf-8')
                    detail['counterexample_count'] = len(re.findall(r'counterexample', content.lower()))
                except:
                    pass
        
        iteration_details.append(detail)
    
    return iteration_details

def extract_counterexample_info(ctx_folder: Path) -> Dict[str, Any]:
    """提取反例信息"""
    counterexample_file = ctx_folder / "counterexamples.txt"
    z3_file = ctx_folder / "z3_counterexample.py"
    
    info = {
        'counterexample_generated': False,
        'counterexample_successful': False,
        'counterexample_count': 0,
        'counterexample_content': ""
    }
    
    if z3_file.exists():
        info['counterexample_generated'] = True
        
        if counterexample_file.exists():
            try:
                content = counterexample_file.read_text(encoding='utf-8')
                info['counterexample_content'] = content
                
                # 计算反例数量
                counterexample_count = len(re.findall(r'counterexample', content.lower()))
                info['counterexample_count'] = counterexample_count
                info['counterexample_successful'] = counterexample_count > 0
            except:
                pass
    
    return info

def run_single_test_detailed(file_path: str, api_key: str) -> Dict[str, Any]:
    """
    运行单个文件的详细测试
    
    Args:
        file_path: 文件路径
        api_key: API密钥
        
    Returns:
        详细的测试结果字典
    """
    print(f"\n{'='*80}")
    print(f"🔍 开始详细测试: {file_path}")
    print(f"{'='*80}")
    
    try:
        # 运行verus_auto_prover
        cmd = [
            "python3", "verus_auto_prover.py",
            "--api-key", api_key,
            file_path
        ]
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=300  # 5分钟超时
        )
        
        # 分析结果
        success = result.returncode == 0
        output = result.stdout
        error = result.stderr
        
        # 检查是否成功验证
        verification_success = "✅ 文件处理成功！" in output
        verification_failed = "❌ 文件处理失败！" in output
        
        # 提取统计信息
        stats = {}
        if "=== TOKEN USAGE SUMMARY ===" in output:
            lines = output.split('\n')
            for i, line in enumerate(lines):
                if "总API调用次数:" in line:
                    stats['api_calls'] = line.split(':')[1].strip()
                elif "总Tokens:" in line:
                    stats['total_tokens'] = line.split(':')[1].strip()
                elif "总迭代次数:" in line:
                    stats['iterations'] = line.split(':')[1].strip()
                elif "最终状态:" in line:
                    stats['final_status'] = line.split(':')[1].strip()
        
        # 获取项目文件夹信息
        project_name = Path(file_path).stem
        project_folder = Path("results") / project_name
        
        # 提取反例信息
        counterexample_info = {}
        if project_folder.exists():
            ctx_folder = project_folder / "CTX"
            if ctx_folder.exists():
                counterexample_info = extract_counterexample_info(ctx_folder)
        
        # 提取每次迭代的详细信息
        iteration_details = []
        if project_folder.exists():
            iteration_details = extract_iteration_details(project_folder, output)
        
        return {
            'file': file_path,
            'success': success,
            'verification_success': verification_success,
            'verification_failed': verification_failed,
            'stats': stats,
            'output': output,
            'error': error,
            'return_code': result.returncode,
            'counterexample_info': counterexample_info,
            'iteration_details': iteration_details,
            'project_folder': str(project_folder)
        }
        
    except subprocess.TimeoutExpired:
        return {
            'file': file_path,
            'success': False,
            'verification_success': False,
            'verification_failed': True,
            'stats': {},
            'output': '',
            'error': 'Timeout after 5 minutes',
            'return_code': -1,
            'counterexample_info': {},
            'iteration_details': [],
            'project_folder': ''
        }
    except Exception as e:
        return {
            'file': file_path,
            'success': False,
            'verification_success': False,
            'verification_failed': True,
            'stats': {},
            'output': '',
            'error': str(e),
            'return_code': -1,
            'counterexample_info': {},
            'iteration_details': [],
            'project_folder': ''
        }

def get_all_benchmark_files() -> List[str]:
    """获取所有benchmark文件"""
    files = []
    
    # CloverBench文件
    cloverbench_dir = Path("benchmarks/CloverBench/unverified")
    if cloverbench_dir.exists():
        for file in cloverbench_dir.glob("*.rs"):
            files.append(str(file))
    
    # Misc文件
    misc_dir = Path("benchmarks/Misc/unverified")
    if misc_dir.exists():
        for file in misc_dir.glob("*.rs"):
            files.append(str(file))
    
    # Diffy文件
    diffy_dir = Path("benchmarks/Diffy/unverified")
    if diffy_dir.exists():
        for file in diffy_dir.glob("*.rs"):
            files.append(str(file))
    
    # MBPP文件
    mbpp_dir = Path("benchmarks/MBPP/unverified")
    if mbpp_dir.exists():
        for file in mbpp_dir.glob("*.rs"):
            files.append(str(file))
    
    return files

def run_comprehensive_benchmark():
    """运行全面的基准测试"""
    
    # API密钥
    api_key = "your_openai_api_key_here"
    
    # 获取所有benchmark文件
    benchmark_files = get_all_benchmark_files()
    
    print("🚀 开始全面基准测试")
    print(f"📅 测试时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"📁 测试文件数量: {len(benchmark_files)}")
    
    # 运行测试
    results = []
    successful_tests = 0
    failed_tests = 0
    
    for i, file_path in enumerate(benchmark_files, 1):
        print(f"\n📊 进度: {i}/{len(benchmark_files)}")
        
        if not os.path.exists(file_path):
            print(f"❌ 文件不存在: {file_path}")
            continue
            
        result = run_single_test_detailed(file_path, api_key)
        results.append(result)
        
        if result['verification_success']:
            successful_tests += 1
            print(f"✅ 测试成功: {file_path}")
        else:
            failed_tests += 1
            print(f"❌ 测试失败: {file_path}")
    
    # 生成Excel报告
    generate_excel_report(results, successful_tests, failed_tests)
    
    return results

def generate_excel_report(results: List[Dict[str, Any]], successful_tests: int, failed_tests: int):
    """生成Excel报告"""
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    excel_file = f"comprehensive_benchmark_report_{timestamp}.xlsx"
    
    # 准备数据
    data = []
    
    for result in results:
        # 基本信息
        file_name = Path(result['file']).name
        benchmark_type = Path(result['file']).parent.name
        
        # 验证结果
        verification_status = "Success" if result['verification_success'] else "Failed"
        final_status = result['stats'].get('final_status', 'unknown')
        
        # 统计信息
        api_calls = result['stats'].get('api_calls', '0')
        total_tokens = result['stats'].get('total_tokens', '0')
        iterations = result['stats'].get('iterations', '0')
        
        # 基本行数据
        row_data = {
            'Filename': file_name,
            'Benchmark_Type': benchmark_type,
            'Verification_Status': verification_status,
            'Final_Status': final_status,
            'Total_API_Calls': api_calls,
            'Total_Token_Usage': total_tokens,
            'Total_Iterations': iterations,
        }
        
        # 为每次迭代添加详细信息 (5次迭代 × 5列信息 = 25列)
        iteration_details = result.get('iteration_details', [])
        for i in range(1, 6):  # 迭代1到5
            if i - 1 < len(iteration_details):
                detail = iteration_details[i - 1]
                row_data[f'Iteration{i}_Error_Type'] = detail.get('error_type', '')
                row_data[f'Iteration{i}_Verus_Error'] = detail.get('verus_error', '')
                row_data[f'Iteration{i}_Counterexample_Generated'] = 'Yes' if detail.get('counterexample_generated', False) else 'No'
                row_data[f'Iteration{i}_Counterexample_Count'] = detail.get('counterexample_count', 0)
                row_data[f'Iteration{i}_Token_Cost'] = detail.get('token_cost', 0)
            else:
                row_data[f'Iteration{i}_Error_Type'] = ''
                row_data[f'Iteration{i}_Verus_Error'] = ''
                row_data[f'Iteration{i}_Counterexample_Generated'] = ''
                row_data[f'Iteration{i}_Counterexample_Count'] = 0
                row_data[f'Iteration{i}_Token_Cost'] = 0
        
        # 添加项目文件夹信息
        row_data['Project_Folder'] = result['project_folder']
        
        data.append(row_data)
    
    # 创建DataFrame
    df = pd.DataFrame(data)
    
    # 创建Excel写入器
    with pd.ExcelWriter(excel_file, engine='openpyxl') as writer:
        # 主数据表
        df.to_excel(writer, sheet_name='详细结果', index=False)
        
        # 统计摘要表
        summary_data = {
            '指标': [
                '总测试数量',
                '成功测试',
                '失败测试',
                '成功率',
                '总API调用',
                '总Token使用',
                '平均每次调用Tokens',
                '反例生成成功率',
                '反例成功生成率'
            ],
            '数值': [
                len(results),
                successful_tests,
                failed_tests,
                f"{successful_tests/len(results)*100:.1f}%" if len(results) > 0 else "0%",
                sum(int(r['stats'].get('api_calls', '0')) for r in results),
                sum(int(r['stats'].get('total_tokens', '0').replace(',', '')) for r in results),
                sum(int(r['stats'].get('total_tokens', '0').replace(',', '')) for r in results) // max(1, sum(int(r['stats'].get('api_calls', '0')) for r in results)),
                f"{sum(1 for r in results if r['counterexample_info'].get('counterexample_generated', False))}/{len(results)}",
                f"{sum(1 for r in results if r['counterexample_info'].get('counterexample_successful', False))}/{len(results)}"
            ]
        }
        
        summary_df = pd.DataFrame(summary_data)
        summary_df.to_excel(writer, sheet_name='统计摘要', index=False)
        
        # 按基准类型分组统计
        benchmark_stats = df.groupby('基准类型').agg({
            '验证状态': lambda x: (x == '成功').sum(),
            '文件名': 'count'
        }).rename(columns={'验证状态': '成功数量', '文件名': '总数量'})
        benchmark_stats['成功率'] = (benchmark_stats['成功数量'] / benchmark_stats['总数量'] * 100).round(1)
        benchmark_stats.to_excel(writer, sheet_name='按基准类型统计')
    
    print(f"\n📄 Excel报告已保存到: {excel_file}")
    
    # 打印总结
    print(f"\n{'='*80}")
    print(f"🎯 全面基准测试完成")
    print(f"{'='*80}")
    print(f"📊 总测试数量: {len(results)}")
    print(f"✅ 成功测试: {successful_tests}")
    print(f"❌ 失败测试: {failed_tests}")
    print(f"📈 成功率: {successful_tests/len(results)*100:.1f}%")
    print(f"📄 详细报告: {excel_file}")

if __name__ == "__main__":
    run_comprehensive_benchmark()
