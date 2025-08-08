#!/usr/bin/env python3
"""
监控全面基准测试的进度
"""

import subprocess
import time
import os
from pathlib import Path

def check_progress():
    """检查测试进度"""
    try:
        # 检查是否有测试进程在运行
        result = subprocess.run(
            ["ps", "aux"],
            capture_output=True,
            text=True
        )
        
        running_tests = []
        for line in result.stdout.split('\n'):
            if 'run_comprehensive_benchmark.py' in line and 'grep' not in line:
                running_tests.append(line)
        
        if running_tests:
            print("🔄 测试正在运行中...")
            for test in running_tests:
                print(f"   {test}")
        else:
            print("⏹️  没有测试进程在运行")
        
        # 检查results目录中的项目数量
        results_dir = Path("results")
        if results_dir.exists():
            project_folders = [d for d in results_dir.iterdir() if d.is_dir()]
            print(f"📁 已完成的项目数量: {len(project_folders)}")
            
            # 显示最近完成的几个项目
            recent_folders = sorted(project_folders, key=lambda x: x.stat().st_mtime, reverse=True)[:5]
            if recent_folders:
                print("📊 最近完成的项目:")
                for folder in recent_folders:
                    mtime = folder.stat().st_mtime
                    time_str = time.strftime('%H:%M:%S', time.localtime(mtime))
                    print(f"   - {folder.name} ({time_str})")
        
        # 检查是否有Excel报告生成
        excel_files = list(Path(".").glob("comprehensive_benchmark_report_*.xlsx"))
        if excel_files:
            latest_excel = max(excel_files, key=lambda x: x.stat().st_mtime)
            print(f"📄 最新Excel报告: {latest_excel.name}")
        
    except Exception as e:
        print(f"❌ 监控时出错: {e}")

def main():
    """主函数"""
    print("🔍 基准测试进度监控")
    print("=" * 50)
    
    while True:
        check_progress()
        print("=" * 50)
        
        try:
            time.sleep(30)  # 每30秒检查一次
        except KeyboardInterrupt:
            print("\n👋 监控已停止")
            break

if __name__ == "__main__":
    main()
