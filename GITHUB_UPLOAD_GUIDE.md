# GitHub上传指南

本指南将帮助你将这个Verus自动证明生成和验证系统上传到GitHub。

## 准备工作

### 1. 安装Git
如果你还没有安装Git，请先安装：
- **macOS**: `brew install git`
- **Windows**: 下载并安装 [Git for Windows](https://git-scm.com/download/win)
- **Linux**: `sudo apt-get install git` (Ubuntu/Debian) 或 `sudo yum install git` (CentOS/RHEL)

### 2. 配置Git用户信息
```bash
git config --global user.name "你的GitHub用户名"
git config --global user.email "你的邮箱地址"
```

### 3. 创建GitHub账户
如果还没有GitHub账户，请访问 [GitHub.com](https://github.com) 注册一个账户。

## 上传步骤

### 步骤1: 在GitHub上创建新仓库

1. 登录GitHub
2. 点击右上角的 "+" 号，选择 "New repository"
3. 填写仓库信息：
   - **Repository name**: `verus-auto-prover` (或你喜欢的名字)
   - **Description**: `Verus自动证明生成和验证系统`
   - **Visibility**: 选择 Public 或 Private
   - **不要**勾选 "Initialize this repository with a README"
4. 点击 "Create repository"

### 步骤2: 初始化本地Git仓库

在你的项目目录中运行以下命令：

```bash
# 进入项目目录
cd /Users/sun/Desktop/code/Pre_Exp_Verus_CTX

# 初始化Git仓库
git init

# 添加所有文件到暂存区
git add .

# 提交初始版本
git commit -m "Initial commit: Verus自动证明生成和验证系统"
```

### 步骤3: 连接到GitHub远程仓库

```bash
# 添加远程仓库（替换YOUR_USERNAME为你的GitHub用户名）
git remote add origin https://github.com/YOUR_USERNAME/verus-auto-prover.git

# 验证远程仓库已添加
git remote -v
```

### 步骤4: 推送到GitHub

```bash
# 推送到主分支
git branch -M main
git push -u origin main
```

## 后续更新

当你对代码进行修改后，使用以下命令更新GitHub：

```bash
# 查看修改状态
git status

# 添加修改的文件
git add .

# 提交修改
git commit -m "描述你的修改内容"

# 推送到GitHub
git push
```

## 重要注意事项

### 1. 敏感信息保护
- 确保 `.gitignore` 文件正确配置，避免上传敏感信息
- 不要将API密钥直接写在代码中
- 使用环境变量或配置文件来管理敏感信息

### 2. 文件大小限制
- GitHub对单个文件有100MB的限制
- 如果项目包含大文件，考虑使用Git LFS

### 3. 许可证
考虑添加许可证文件：
```bash
# 创建LICENSE文件
touch LICENSE
```

然后在GitHub网页上选择适合的许可证类型。

## 可选：创建GitHub Pages

如果你想为项目创建文档网站：

1. 在GitHub仓库页面，进入 "Settings"
2. 滚动到 "Pages" 部分
3. 选择 "Deploy from a branch"
4. 选择 "main" 分支和 "/docs" 文件夹
5. 点击 "Save"

## 故障排除

### 问题1: 推送被拒绝
```bash
# 如果远程仓库有内容，先拉取
git pull origin main --allow-unrelated-histories
```

### 问题2: 认证失败
```bash
# 使用个人访问令牌
git remote set-url origin https://YOUR_TOKEN@github.com/YOUR_USERNAME/verus-auto-prover.git
```

### 问题3: 大文件上传失败
```bash
# 安装Git LFS
git lfs install
git lfs track "*.pdf"
git lfs track "*.zip"
git add .gitattributes
```

## 项目展示优化

### 1. 更新README.md
确保README.md包含：
- 项目简介
- 安装说明
- 使用示例
- 贡献指南

### 2. 添加徽章
在README.md顶部添加徽章：
```markdown
![Python](https://img.shields.io/badge/Python-3.8+-blue.svg)
![License](https://img.shields.io/badge/License-MIT-green.svg)
```

### 3. 创建贡献指南
```bash
# 创建CONTRIBUTING.md
touch CONTRIBUTING.md
```

## 完成！

恭喜！你的项目现在已经成功上传到GitHub。你可以：
- 分享仓库链接给其他人
- 接受Issue和Pull Request
- 继续开发和维护项目

如果遇到任何问题，请参考GitHub的官方文档或联系我获取帮助。
