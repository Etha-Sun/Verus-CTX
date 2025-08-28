#!/usr/bin/env python3
import subprocess
import sys
import shutil
from pathlib import Path
from datetime import datetime

ROOT = Path(__file__).resolve().parent.parent
CONVERTER = ROOT / 'code_ver2' / 'convert_assume.py'
BENCHMARKS = ROOT / 'benchmarks'


def find_verified_rs_files() -> list[Path]:
    files: list[Path] = []
    if not BENCHMARKS.exists():
        return files
    for dataset_dir in BENCHMARKS.iterdir():
        if not dataset_dir.is_dir():
            continue
        verified_dir = dataset_dir / 'verified'
        if not verified_dir.exists():
            continue
        for f in verified_dir.glob('*.rs'):
            files.append(f)
    return files


def run_verus(file_path: Path) -> tuple[bool, str]:
    try:
        res = subprocess.run(['verus', str(file_path)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
    except FileNotFoundError:
        return (False, 'SKIP: verus not found')
    out = res.stdout
    ok = ('0 errors' in out)
    return (ok, out)


def main():
    ts = datetime.now().strftime('%H%M%S')
    out_root = ROOT / 'out' / f'assume-batch-{ts}'
    out_root.mkdir(parents=True, exist_ok=True)

    rs_files = find_verified_rs_files()
    if not rs_files:
        print('No verified .rs files found under benchmarks/*/verified', file=sys.stderr)
        sys.exit(1)

    total = 0
    converted = 0
    verified_ok = 0
    skipped_verify = 0
    failed_files = []  # Track failed files for error collection

    for f in rs_files:
        total += 1
        dataset = f.parents[0].parent.name
        dest_dir = out_root / dataset
        dest_dir.mkdir(parents=True, exist_ok=True)
        # convert
        try:
            subprocess.run([sys.executable, str(CONVERTER), str(f), str(dest_dir)], check=True)
        except subprocess.CalledProcessError as e:
            print(f'[ERROR] Conversion failed for {f}: {e}', file=sys.stderr)
            continue
        out_file = dest_dir / f.name
        if not out_file.exists():
            print(f'[WARN] Converter did not produce output for {f}', file=sys.stderr)
            continue
        # verify
        ok, out = run_verus(out_file)
        if out == 'SKIP: verus not found':
            skipped_verify += 1
            print(f'{dataset}/{out_file.name}: VERIFY SKIPPED (verus not found)')
        elif ok:
            verified_ok += 1
            print(f'{dataset}/{out_file.name}: VERIFY OK')
        else:
            print(f'{dataset}/{out_file.name}: VERIFY FAIL')
            print(out)
            failed_files.append((out_file, dataset, out))
        converted += 1

    # Create errors directory and copy failed files
    if failed_files:
        errors_dir = out_root / 'errors'
        errors_dir.mkdir(exist_ok=True)
        
        print(f'\n--- Copying {len(failed_files)} failed files to errors directory ---')
        
        for out_file, dataset, error_output in failed_files:
            # Create dataset subdirectory in errors
            error_dataset_dir = errors_dir / dataset
            error_dataset_dir.mkdir(exist_ok=True)
            
            # Copy the failed file
            error_file_path = error_dataset_dir / out_file.name
            shutil.copy2(out_file, error_file_path)
            
            # Save error output to .error file
            error_log_path = error_dataset_dir / f'{out_file.stem}.error'
            error_log_path.write_text(error_output, encoding='utf-8')
            
            print(f'Copied: {dataset}/{out_file.name} -> errors/{dataset}/')

    print(f'\nConverted {converted}/{total}. Verified OK: {verified_ok}. Skipped verify: {skipped_verify}')
    if failed_files:
        print(f'Failed files copied to: {out_root / "errors"}')
    print(f'Output root: {out_root}')


if __name__ == '__main__':
    main()


