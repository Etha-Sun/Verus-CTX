import os
import re

def process_file(input_path, output_path):
    with open(input_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        # 检测 while ( ... ) 行
        if re.match(r'^\s*while\s*\(.*\)', line):
            # 保留 while 行
            new_lines.append(line)
            i += 1
            # 跳过中间所有内容，直到遇到 {，保留 { 单独一行
            while i < len(lines):
                if lines[i].strip() == '{':
                    new_lines.append(lines[i])  # 保留 {
                    i += 1
                    break
                i += 1
        else:
            new_lines.append(line)
            i += 1

    with open(output_path, 'w', encoding='utf-8') as f:
        f.writelines(new_lines)

def process_folder(base_folder):
    verified_dir = os.path.join(base_folder, 'verified')
    unverified_dir = os.path.join(base_folder, 'unverified')
    if not os.path.exists(unverified_dir):
        os.makedirs(unverified_dir)

    for filename in os.listdir(verified_dir):
        if filename.endswith('.rs'):
            input_path = os.path.join(verified_dir, filename)
            output_path = os.path.join(unverified_dir, filename)
            process_file(input_path, output_path)
            print(f"Processed {filename}")

if __name__ == "__main__":
    # 修改为你的目标基准集目录
    base_folder = "/Users/sun/Desktop/code/verus_proof/benchmarks/Diffy"
    process_folder(base_folder)