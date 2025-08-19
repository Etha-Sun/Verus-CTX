#!/usr/bin/env python3
import subprocess
import sys
import os
from pathlib import Path
from datetime import datetime

ROOT = Path(__file__).resolve().parent.parent
CONVERTER = ROOT / 'code' / 'convert.py'
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
    out_root = ROOT / 'out' / f'result-{ts}'
    out_root.mkdir(parents=True, exist_ok=True)

    rs_files = find_verified_rs_files()
    if not rs_files:
        print('No verified .rs files found under benchmarks/*/verified', file=sys.stderr)
        sys.exit(1)

    total = 0
    converted = 0
    verified_ok = 0
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
        final_out = dest_dir / f'{f.stem}-whileloop.rs'
        out_file.replace(final_out)
        converted += 1
        # verify
        ok, out = run_verus(final_out)
        if out == 'SKIP: verus not found':
            print(f'{dataset}/{final_out.name}: VERIFY SKIPPED (verus not found)')
        elif ok:
            verified_ok += 1
            print(f'{dataset}/{final_out.name}: VERIFY OK')
        else:
            print(f'{dataset}/{final_out.name}: VERIFY FAIL')
            print(out)

    print(f'Converted {converted}/{total}. Verified OK: {verified_ok}')
    print(f'Output root: {out_root}')


if __name__ == '__main__':
    main()


