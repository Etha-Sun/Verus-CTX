#!/usr/bin/env python3
"""
检查将要上传到GitHub的文件
"""

import os
import subprocess
from pathlib import Path

def check_git_status():
    """检查Git状态和将要上传的文件"""
    print("🔍 检查Git状态...")
    
    try:
        # 检查是否在Git仓库中
        result = subprocess.run(['git', 'status'], capture_output=True, text=True)
        if result.returncode != 0:
            print("❌ 当前目录不是Git仓库")
            print("请先运行: git init")
            return False
        
        print("✅ 当前目录是Git仓库")
        
        # 获取将要提交的文件
        result = subprocess.run(['git', 'status', '--porcelain'], capture_output=True, text=True)
        if result.stdout.strip():
            print("\n📁 将要上传的文件:")
            for line in result.stdout.strip().split('\n'):
                if line.strip():
                    status = line[:2]
                    filename = line[3:]
                    print(f"  {status} {filename}")
        else:
            print("📝 没有新的文件需要上传")
        
        return True
        
    except FileNotFoundError:
        print("❌ Git未安装，请先安装Git")
        return False

def check_file_sizes():
    """检查文件大小，确保没有超大文件"""
    print("\n📏 检查文件大小...")
    
    large_files = []
    for root, dirs, files in os.walk('.'):
        # 跳过.git目录
        if '.git' in dirs:
            dirs.remove('.git')
        
        for file in files:
            file_path = os.path.join(root, file)
            try:
                size = os.path.getsize(file_path)
                if size > 50 * 1024 * 1024:  # 50MB
                    large_files.append((file_path, size))
            except OSError:
                continue
    
    if large_files:
        print("⚠️  发现大文件（可能影响上传）:")
        for file_path, size in large_files:
            size_mb = size / (1024 * 1024)
            print(f"  {file_path} ({size_mb:.1f}MB)")
        print("\n💡 建议: 考虑使用Git LFS处理大文件")
    else:
        print("✅ 没有发现超大文件")

def check_sensitive_info():
    """检查是否包含敏感信息"""
    print("\n🔒 检查敏感信息...")
    
    sensitive_patterns = [
        'sk-',  # OpenAI API key
        'api_key',
        'password',
        'secret',
        'token'
    ]
    
    sensitive_files = []
    for root, dirs, files in os.walk('.'):
        if '.git' in dirs:
            dirs.remove('.git')
        
        for file in files:
            if file.endswith(('.py', '.json', '.md', '.txt')):
                file_path = os.path.join(root, file)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read().lower()
                        for pattern in sensitive_patterns:
                            if pattern in content:
                                sensitive_files.append((file_path, pattern))
                                break
                except (OSError, UnicodeDecodeError):
                    continue
    
    if sensitive_files:
        print("⚠️  发现可能包含敏感信息的文件:")
        for file_path, pattern in sensitive_files:
            print(f"  {file_path} (包含: {pattern})")
        print("\n💡 建议: 检查这些文件，确保没有暴露敏感信息")
    else:
        print("✅ 没有发现明显的敏感信息")

def main():
    """主函数"""
    print("🚀 GitHub上传前检查工具")
    print("=" * 50)
    
    # 检查Git状态
    if not check_git_status():
        return
    
    # 检查文件大小
    check_file_sizes()
    
    # 检查敏感信息
    check_sensitive_info()
    
    print("\n" + "=" * 50)
    print("📋 上传建议:")
    print("1. 确保.gitignore文件正确配置")
    print("2. 检查是否包含敏感信息")
    print("3. 确保README.md文件完整")
    print("4. 考虑添加LICENSE文件")
    print("\n准备好后，运行以下命令上传:")
    print("git add .")
    print("git commit -m 'Initial commit'")
    print("git push -u origin main")

if __name__ == "__main__":
    main()
