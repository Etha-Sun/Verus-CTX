# Verus自动证明生成和验证系统

这是一个自动化的Verus形式化验证系统，可以使用大语言模型（OpenAI GPT-4o）自动生成和修复Rust/Verus代码的形式化证明。

## 功能特性

- 🤖 使用OpenAI GPT-4o模型自动生成形式化证明
- 🔄 自动迭代修复，最多支持5次修复尝试
- 📁 完善的文件管理系统，保存所有迭代历史
- 🎯 高质量的prompt工程，专门针对Verus优化
- ⚡ 支持推理模式，确保证明质量

## 系统要求

- Python 3.8+
- Verus验证器
- OpenAI API访问权限
- conda环境（推荐使用marker环境）

## 安装和配置

1. 确保已安装Verus验证器
2. 激活conda环境：
   ```bash
   conda activate marker
   ```
3. 安装依赖：
   ```bash
   pip install "openai>=1.0.0"
   ```

## 使用方法

### 基本用法

```bash
python verus_auto_prover.py <rust_file_path> --api-key <your_openai_api_key>
```

### 完整参数

```bash
python verus_auto_prover.py <rust_file_path> \
    --api-key <your_openai_api_key> \
    --max-iterations 5
```

### 示例

```bash
python verus_auto_prover.py examples/fibonacci.rs --api-key sk-xxx
```

## 文件结构

处理文件后，系统会创建以下文件结构：

```
原文件目录/
├── original_file.rs          # 原始文件
├── original_file-verified.rs # 验证成功的文件
└── History/                  # 历史文件夹
    ├── 1.rs                 # 第1次迭代
    ├── 2.rs                 # 第2次迭代
    └── ...                  # 更多迭代
```

## Prompt配置

系统使用`prompts.json`文件来配置prompt模板，你可以根据需要修改：

### 主要配置项

- `initial_proof_generation`: 初始证明生成的prompt
- `iterative_fix`: 迭代修复的prompt  
- `model_config`: 模型配置参数

### 自定义Prompt

编辑`prompts.json`文件来自定义prompt：

```json
{
  "initial_proof_generation": {
    "template": "你的自定义prompt..."
  },
  "model_config": {
    "model": "gpt-4o",
    "temperature": 0.1,
    "max_tokens": 4000
  }
}
```

## 工作流程

1. **读取输入文件**: 加载包含require/ensure的Rust代码
2. **生成初始证明**: 使用LM生成第一版proof
3. **Verus验证**: 运行Verus验证器检查proof
4. **迭代修复**: 如果验证失败，根据错误信息修复proof
5. **保存结果**: 验证成功后保存到verified文件

## 示例文件

### 输入示例 (fibonacci.rs)

```rust
use vstd::prelude::*;

verus! {

// 计算斐波那契数列的第n项
fn fibonacci(n: u32) -> (result: u32)
    requires n < 50,  // 防止溢出
    ensures result > 0,
{
    if n <= 1 {
        1
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

} // verus!
```

### 期望输出 (fibonacci-verified.rs)

系统会自动生成包含完整proof的验证版本。

## 常见问题

### Q: 如何处理复杂的循环证明？
A: 系统会自动识别需要循环不变式的情况，并生成相应的proof代码。

### Q: 验证失败怎么办？
A: 系统会自动进行最多5次迭代修复，每次都会根据Verus的错误信息优化proof。

### Q: 如何调整模型参数？
A: 编辑`prompts.json`文件中的`model_config`部分。

## API密钥配置

出于安全考虑，建议通过环境变量配置API密钥：

```bash
export OPENAI_API_KEY="your_api_key_here"
python verus_auto_prover.py examples/fibonacci.rs --api-key $OPENAI_API_KEY
```

## 注意事项

- 确保输入的Rust文件包含valid的require/ensure规约
- 对于特别复杂的证明，可能需要手动调整prompt
- 系统会保存所有中间结果，便于调试和分析
- 建议在处理重要文件前先备份

## 贡献

欢迎提交Issue和Pull Request来改进这个系统！