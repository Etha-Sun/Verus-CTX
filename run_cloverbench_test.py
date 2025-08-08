#!/usr/bin/env python3
"""
CloverBench批量测试脚本
"""

import os
import sys
import subprocess
import json
from pathlib import Path
from datetime import datetime

def run_single_test(file_path: str, api_key: str) -> dict:
    """
    运行单个文件的测试
    
    Args:
        file_path: 文件路径
        api_key: API密钥
        
    Returns:
        测试结果字典
    """
    print(f"\n{'='*60}")
    print(f"🔍 开始测试: {file_path}")
    print(f"{'='*60}")
    
    try:
        # 运行verus_auto_prover
        cmd = [
            "python3", "verus_auto_prover.py",
            "--api-key", api_key,
            "--use-gemini",
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
        
        return {
            'file': file_path,
            'success': success,
            'verification_success': verification_success,
            'verification_failed': verification_failed,
            'stats': stats,
            'output': output,
            'error': error,
            'return_code': result.returncode
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
            'return_code': -1
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
            'return_code': -1
        }

def run_cloverbench_test():
    """运行CloverBench测试"""
    
    # API密钥
    api_key = "your_google_api_key_here"
    
    # CloverBench文件列表
    cloverbench_files = [
        "benchmarks/CloverBench/unverified/is_prime.rs",
        "benchmarks/CloverBench/unverified/linear_search2.rs",
        "benchmarks/CloverBench/unverified/two_sum.rs",
        "benchmarks/CloverBench/unverified/binary_search.rs",
        "benchmarks/CloverBench/unverified/cal_div.rs",
        "benchmarks/CloverBench/unverified/array_product_strong.rs",
        "benchmarks/CloverBench/unverified/array_sum_strong.rs",
        "benchmarks/CloverBench/unverified/array_copy_strong.rs",
        "benchmarks/CloverBench/unverified/all_digits_strong.rs",
        "benchmarks/CloverBench/unverified/array_append_strong.rs",
        "benchmarks/CloverBench/unverified/array_concat_strong.rs"
    ]
    
    print("🚀 开始CloverBench测试")
    print(f"📅 测试时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"📁 测试文件数量: {len(cloverbench_files)}")
    
    # 运行测试
    results = []
    successful_tests = 0
    failed_tests = 0
    
    for i, file_path in enumerate(cloverbench_files, 1):
        print(f"\n📊 进度: {i}/{len(cloverbench_files)}")
        
        if not os.path.exists(file_path):
            print(f"❌ 文件不存在: {file_path}")
            continue
            
        result = run_single_test(file_path, api_key)
        results.append(result)
        
        if result['verification_success']:
            successful_tests += 1
            print(f"✅ 测试成功: {file_path}")
        else:
            failed_tests += 1
            print(f"❌ 测试失败: {file_path}")
    
    # 生成测试报告
    generate_test_report(results, successful_tests, failed_tests)
    
    return results

def generate_test_report(results, successful_tests, failed_tests):
    """生成测试报告"""
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    report_file = f"cloverbench_test_report_{timestamp}.md"
    
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write("# CloverBench测试报告\n\n")
        f.write(f"**测试时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        # 总体统计
        f.write("## 📊 总体统计\n\n")
        f.write(f"- **总测试数量**: {len(results)}\n")
        f.write(f"- **成功测试**: {successful_tests}\n")
        f.write(f"- **失败测试**: {failed_tests}\n")
        f.write(f"- **成功率**: {successful_tests/len(results)*100:.1f}%\n\n")
        
        # 详细结果
        f.write("## 📋 详细结果\n\n")
        
        for result in results:
            f.write(f"### {result['file']}\n\n")
            f.write(f"- **状态**: {'✅ 成功' if result['verification_success'] else '❌ 失败'}\n")
            f.write(f"- **返回码**: {result['return_code']}\n")
            
            if result['stats']:
                f.write("- **统计信息**:\n")
                for key, value in result['stats'].items():
                    f.write(f"  - {key}: {value}\n")
            
            if result['error']:
                f.write(f"- **错误信息**: {result['error']}\n")
            
            f.write("\n")
        
        # 成功案例
        successful_results = [r for r in results if r['verification_success']]
        if successful_results:
            f.write("## ✅ 成功案例\n\n")
            for result in successful_results:
                f.write(f"- {result['file']}\n")
            f.write("\n")
        
        # 失败案例
        failed_results = [r for r in results if not r['verification_success']]
        if failed_results:
            f.write("## ❌ 失败案例\n\n")
            for result in failed_results:
                f.write(f"- {result['file']}: {result.get('error', 'Unknown error')}\n")
            f.write("\n")
        
        # 性能分析
        f.write("## 📈 性能分析\n\n")
        
        total_tokens = 0
        total_api_calls = 0
        total_iterations = 0
        
        for result in results:
            if result['stats']:
                if 'total_tokens' in result['stats']:
                    try:
                        total_tokens += int(result['stats']['total_tokens'].replace(',', ''))
                    except:
                        pass
                if 'api_calls' in result['stats']:
                    try:
                        total_api_calls += int(result['stats']['api_calls'])
                    except:
                        pass
                if 'iterations' in result['stats']:
                    try:
                        total_iterations += int(result['stats']['iterations'])
                    except:
                        pass
        
        f.write(f"- **总Token使用**: {total_tokens:,}\n")
        f.write(f"- **总API调用**: {total_api_calls}\n")
        f.write(f"- **总迭代次数**: {total_iterations}\n")
        if total_api_calls > 0:
            f.write(f"- **平均每次调用Tokens**: {total_tokens//total_api_calls:,}\n")
        
        f.write("\n")
        
        # 结论
        f.write("## 🎯 结论\n\n")
        if successful_tests > failed_tests:
            f.write("✅ **测试结果良好**: 大部分CloverBench样例能够成功验证\n")
        else:
            f.write("⚠️ **测试结果一般**: 需要进一步优化系统性能\n")
        
        f.write(f"- 系统能够处理 {successful_tests}/{len(results)} 个CloverBench样例\n")
        f.write(f"- 成功率: {successful_tests/len(results)*100:.1f}%\n")
        f.write("- 建议进一步分析失败案例以改进系统\n")
    
    print(f"\n📄 测试报告已保存到: {report_file}")
    
    # 打印总结
    print(f"\n{'='*60}")
    print(f"🎯 CloverBench测试完成")
    print(f"{'='*60}")
    print(f"📊 总测试数量: {len(results)}")
    print(f"✅ 成功测试: {successful_tests}")
    print(f"❌ 失败测试: {failed_tests}")
    print(f"📈 成功率: {successful_tests/len(results)*100:.1f}%")
    print(f"📄 详细报告: {report_file}")

if __name__ == "__main__":
    run_cloverbench_test()
