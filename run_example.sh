#!/bin/bash

# Verus自动证明生成系统示例运行脚本

# 确保conda环境已激活
if [[ "$CONDA_DEFAULT_ENV" != "marker" ]]; then
    echo "请先激活marker环境: conda activate marker"
    exit 1
fi

# 检查是否提供了文件参数
if [ $# -eq 0 ]; then
    echo "使用方法: $0 <rust_file_path>"
    echo "示例:"
    echo "  $0 examples/fibonacci.rs"
    echo "  $0 examples/binary_search.rs"
    exit 1
fi

# 检查文件是否存在
if [ ! -f "$1" ]; then
    echo "错误: 文件 '$1' 不存在"
    exit 1
fi

echo "开始处理文件: $1"
echo "使用OpenAI o3模型进行自动proof生成..."
echo "=========================================="

# 运行主程序
python verus_auto_prover.py "$1" --max-iterations 5

echo "=========================================="
echo "处理完成！"