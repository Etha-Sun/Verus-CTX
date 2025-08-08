# 🧪 Verus Auto Prover 批量测试指南

## 📋 概述

提供两个脚本来批量测试您的Verus自动证明工具在benchmark数据集上的性能：

1. **`benchmark_batch_test.py`** - 功能完整的Python版本
2. **`benchmark_batch_test.sh`** - 简化的Shell版本

## 🚀 快速开始

### 使用Shell脚本（推荐）

```bash
# 使用默认API密钥运行
./benchmark_batch_test.sh

# 或指定API密钥
./benchmark_batch_test.sh YOUR_API_KEY_HERE
```

### 使用Python脚本（功能更全）

```bash
# 基本使用
python3 benchmark_batch_test.py --api-key YOUR_API_KEY_HERE

# 指定benchmarks目录
python3 benchmark_batch_test.py --api-key YOUR_API_KEY_HERE --benchmarks-dir /path/to/benchmarks

# 指定结果输出文件
python3 benchmark_batch_test.py --api-key YOUR_API_KEY_HERE --output my_results.json
```

## 📊 测试范围

脚本会自动测试以下数据集的`unverified`目录：

| 数据集 | 预计文件数 | 描述 |
|--------|------------|------|
| **CloverBench** | ~11 | 经典CS算法问题 |
| **MBPP** | ~78 | 编程竞赛风格问题 |
| **Diffy** | ~38 | 数组和循环验证 |
| **Misc** | ~23 | 各种算法问题 |
| **SVComp-Array-fpi** | 变动 | SV-COMP数组问题 |
| **interprocedural** | 变动 | 过程间分析问题 |

**总计约150个测试文件**

## 📈 输出结果

### 实时输出示例
```
🚀 开始Verus Auto Prover批量测试
📅 测试时间: 2025-01-04 13:30:29
🔑 API密钥: AIzaSyBb3M...oApQ
📁 找到 150 个测试文件

[  1/150] 测试: CloverBench/unverified/task1.rs
    ✅ 成功 (12.3s)

[  2/150] 测试: CloverBench/unverified/task2.rs  
    ❌ 失败 (45.2s): 验证失败，错误信息...
```

### 最终统计报告
```
🎯 VERUS AUTO PROVER 批量测试报告
============================================================
📅 测试时间: 2025-01-04T13:30:29
⏱️  总耗时: 3847.2秒
📊 总文件数: 150
✅ 成功数量: 89
❌ 失败数量: 61
📈 成功率: 59.3%

📋 数据集详细统计:
------------------------------------------------------------
CloverBench          |   8/ 11 |  72.7%
MBPP                 |  45/ 78 |  57.7%
Diffy                |  23/ 38 |  60.5%
Misc                 |  13/ 23 |  56.5%
```

## 📁 生成的文件

### Shell脚本生成：
- `benchmark_results_YYYYMMDD_HHMMSS.txt` - 测试结果汇总
- `benchmark_test_YYYYMMDD_HHMMSS.log` - 详细执行日志

### Python脚本生成：
- `benchmark_test_results_YYYYMMDD_HHMMSS.json` - 完整JSON格式结果

## ⚙️ 配置选项

### 重要参数
- **超时时间**: 每个文件5分钟超时
- **历史文件夹**: 每10个文件自动清理
- **并发**: 串行执行（避免API限制）

### 自定义修改

如需修改超时时间，编辑脚本中的：
```python
# Python版本
timeout=300  # 秒

# Shell版本  
timeout 300 python3 ...
```

## 🛠️ 故障排除

### 常见问题

1. **API限制错误**
   - 降低并发数或增加延时
   - 检查API配额

2. **磁盘空间不足**
   - 脚本会自动清理历史文件夹
   - 手动删除旧日志文件

3. **某些文件一直失败**
   - 检查文件格式是否正确
   - 查看详细日志分析错误

### 中断和恢复

- 使用 `Ctrl+C` 安全中断测试
- 脚本会自动清理临时文件
- 重新运行会从头开始（暂无断点续传）

## 📊 性能基准

基于初步测试，预期性能：

- **简单函数**: 10-30秒
- **复杂循环**: 1-3分钟  
- **超时文件**: 5分钟
- **预计总耗时**: 2-4小时（全部150个文件）

## 🎯 使用建议

1. **首次测试**: 先用少量文件测试
2. **长时间运行**: 建议在稳定网络环境下运行
3. **结果分析**: 重点关注失败率较高的数据集
4. **迭代改进**: 根据失败案例改进证明生成策略

---

**准备好开始测试了吗？运行脚本享受自动化的乐趣！** 🚀