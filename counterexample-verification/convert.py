#!/usr/bin/env python3
import sys
import os
import re
from pathlib import Path


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def find_matching_brace(s: str, start_idx: int) -> int:
    depth = 0
    for i in range(start_idx, len(s)):
        if s[i] == '{':
            depth += 1
        elif s[i] == '}':
            depth -= 1
            if depth == 0:
                return i
    return -1


def find_verus_block(src: str):
    m = re.search(r"verus!\s*\{", src)
    if not m:
        return None
    start = m.end()  # position after '{'
    # find the '{' index
    brace_open = m.end() - 1
    brace_close = find_matching_brace(src, brace_open)
    if brace_close == -1:
        return None
    return (brace_open, brace_close)


def find_functions(body: str):
    # Return list of function infos in order of appearance (excluding `spec fn`)
    infos = []
    idx = 0
    while True:
        m = re.search(r"(?:pub\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", body[idx:])
        if not m:
            break
        name = m.group(1)
        sig_start = idx + m.start()
        # Find opening brace '{' after signature
        brace_idx = body.find('{', idx + m.end())
        if brace_idx == -1:
            break
        func_end = find_matching_brace(body, brace_idx)
        if func_end == -1:
            break
        signature = body[sig_start:brace_idx].rstrip()
        func_body = body[brace_idx:func_end+1]
        infos.append({
            'name': name,
            'sig_start': sig_start,
            'sig_end': brace_idx,
            'end': func_end+1,
            'signature': signature,
            'body': func_body,
        })
        idx = func_end + 1
    return infos


def parse_params(signature: str):
    # Extract the function parameter list: find the first '(' and its matching ')'
    paren_start = signature.find('(')
    if paren_start == -1:
        return []
    depth = 0
    paren_end = -1
    for i in range(paren_start, len(signature)):
        ch = signature[i]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                paren_end = i
                break
    if paren_end == -1:
        return []
    params_text = signature[paren_start+1:paren_end]
    # Split by commas not inside angle brackets
    parts = []
    depth = 0
    current = []
    for ch in params_text:
        if ch == '<':
            depth += 1
        elif ch == '>':
            depth = max(0, depth-1)
        if ch == ',' and depth == 0:
            part = ''.join(current).strip()
            if part:
                parts.append(part)
            current = []
        else:
            current.append(ch)
    last = ''.join(current).strip()
    if last:
        parts.append(last)

    params = []
    for p in parts:
        if not p:
            continue
        # name: type
        mt = re.match(r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$", p)
        if not mt:
            continue
        name = mt.group(1).strip()
        typ = mt.group(2).strip()
        params.append((name, typ))
    return params


def parse_lets_before(src: str):
    # Returns list of tuples (name, is_mut, type_or_none)
    lets = []
    for m in re.finditer(r"\blet\s+(mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(?::\s*([^=;]+))?\s*=", src):
        is_mut = bool(m.group(1))
        name = m.group(2)
        typ = m.group(3).strip() if m.group(3) else None
        # Find RHS to possibly infer type
        # Get the rest of the line
        line_end = src.find('\n', m.end())
        rhs = src[m.end(): line_end if line_end != -1 else len(src)]
        if typ is None:
            inferred = None
            if re.search(r"\\btrue\\b|\\bfalse\\b", rhs):
                inferred = "bool"
            elif re.search(r"\\.len\\s*\\(\\)", rhs) or re.search(r"as\\s+usize", rhs):
                inferred = "usize"
            elif re.search(r"^(\s*\d+\s*)$", rhs):
                inferred = "usize"
            typ = inferred
        lets.append((name, is_mut, typ))
    return lets


def find_while_loops(func_body: str):
    # func_body starts with '{'
    whiles = []
    idx = 0
    while True:
        m = re.search(r"\bwhile\s*\(", func_body[idx:])
        if not m:
            break
        start = idx + m.start()
        # Extract condition
        cond_start = start + m.group(0).find('(') + 1
        # find matching ')'
        depth = 1
        i = cond_start
        while i < len(func_body) and depth > 0:
            if func_body[i] == '(':
                depth += 1
            elif func_body[i] == ')':
                depth -= 1
            i += 1
        cond_end = i - 1
        condition = func_body[cond_start:cond_end].strip()

        # After ')', capture lines up to '{' as header decorations
        header_tail_start = cond_end + 1
        brace_header_idx = func_body.find('{', header_tail_start)
        if brace_header_idx == -1:
            break
        header_tail = func_body[header_tail_start:brace_header_idx]

        # Extract invariant clauses (split by top-level commas, preserving multi-line clauses)
        inv_clauses = []
        dec_line = None
        inv_match = re.search(r"invariant", header_tail)
        if inv_match:
            inv_block = header_tail[inv_match.end():]
            # split until 'decreases'
            dec_match = re.search(r"decreases\s+(.+?),\s*$", inv_block, re.DOTALL | re.MULTILINE)
            if dec_match:
                inv_only = inv_block[:dec_match.start()]
                dec_line = dec_match.group(1).strip()
            else:
                inv_only = inv_block
            # Split inv_only into clauses by top-level commas
            depth_paren = depth_brack = depth_angle = 0
            current = []
            def flush_clause():
                clause = ''.join(current).strip()
                if clause:
                    # remove trailing comma if any
                    if clause.endswith(','):
                        clause = clause[:-1].rstrip()
                    inv_clauses.append(clause)
            i2 = 0
            while i2 < len(inv_only):
                ch = inv_only[i2]
                if ch == '(':
                    depth_paren += 1
                elif ch == ')':
                    depth_paren = max(0, depth_paren-1)
                elif ch == '[':
                    depth_brack += 1
                elif ch == ']':
                    depth_brack = max(0, depth_brack-1)
                elif ch == '<':
                    depth_angle += 1
                elif ch == '>':
                    depth_angle = max(0, depth_angle-1)
                if ch == ',' and depth_paren == 0 and depth_brack == 0 and depth_angle == 0:
                    flush_clause()
                    current = []
                    i2 += 1
                    continue
                current.append(ch)
                i2 += 1
            flush_clause()

        # Extract while body block
        body_start = brace_header_idx
        body_end = find_matching_brace(func_body, body_start)
        if body_end == -1:
            break
        body_inner = func_body[body_start+1:body_end].rstrip('\n')

        whiles.append({
            'start': start,
            'end': body_end+1,
            'condition': condition,
            'invariants': inv_clauses,
            'decreases': dec_line,
            'body_inner': body_inner,
            'header_tail': header_tail,
        })
        idx = body_end + 1
    return whiles


def build_requires_from_invariants(inv_lines, mut_scalars, mut_vectors):
    req_lines = []
    def replace_line(line: str) -> str:
        out = line
        # Replace mut scalars first
        for name in sorted(mut_scalars, key=len, reverse=True):
            out = re.sub(rf"\b{name}\b", f"*old({name})", out)
        # Replace mut vectors
        for name in sorted(mut_vectors, key=len, reverse=True):
            out = re.sub(rf"\b{name}\b", f"old({name})", out)
        return out
    for l in inv_lines:
        req_lines.append(replace_line(l))
    return req_lines


def deref_mut_scalars_in_text(text: str, mut_scalars):
    out = text
    for name in sorted(mut_scalars, key=len, reverse=True):
        out = re.sub(rf"\b{name}\b", f"*{name}", out)
    return out


def normalize_body_indentation(text: str) -> str:
    lines = text.splitlines()
    # trim leading/trailing empty lines
    while lines and lines[0].strip() == "":
        lines.pop(0)
    while lines and lines[-1].strip() == "":
        lines.pop()
    if not lines:
        return ""
    # compute minimum leading whitespace across non-empty lines
    def leading_ws_len(s: str) -> int:
        i = 0
        while i < len(s) and s[i] in (' ', '\t'):
            i += 1
        return i
    non_empty = [l for l in lines if l.strip() != ""]
    common = min((leading_ws_len(l) for l in non_empty), default=0)
    norm = []
    for l in lines:
        if l.strip() == "":
            norm.append("")
        else:
            # only strip if line actually has that many leading ws
            ws_len = leading_ws_len(l)
            cut = min(common, ws_len)
            norm.append(l[cut:])
    return "\n".join(norm)


def generate_whileloop_fn(idx, total, orig_params, lets_before, wl, mut_scalar_names, mut_vector_names):
    # Name
    if total == 1:
        fn_name = "whileloop"
    else:
        fn_name = f"whileloop_{idx+1}"

    # Params: original params as-is, then lets_before unique by name in order of appearance
    param_strs = []
    used = set()
    for name, typ in orig_params:
        param_strs.append(f"{name}: {typ}")
        used.add(name)

    for name, is_mut, typ in lets_before:
        if name in used:
            continue
        if typ is None:
            # best-effort default
            typ = "usize"
        if is_mut:
            param_strs.append(f"{name}: &mut {typ}")
        else:
            param_strs.append(f"{name}: {typ}")
        used.add(name)

    # requires from invariants
    req_lines = build_requires_from_invariants(wl['invariants'], mut_scalar_names, mut_vector_names)

    # while header content with deref mut scalars
    cond_text = deref_mut_scalars_in_text(wl['condition'], mut_scalar_names)

    # Rebuild invariants for inside while (dereferenced mut scalars, vectors unchanged)
    inv_inside = []
    for l in wl['invariants']:
        inv_inside.append(deref_mut_scalars_in_text(l, mut_scalar_names))

    dec_text = wl['decreases']
    if dec_text is not None:
        dec_text = deref_mut_scalars_in_text(dec_text, mut_scalar_names)

    # body with deref mut scalars
    body_text = deref_mut_scalars_in_text(wl['body_inner'], mut_scalar_names)
    body_text = normalize_body_indentation(body_text)

    # Assemble function text
    lines = []
    lines.append(f"fn {fn_name}({', '.join(param_strs)})")
    if req_lines:
        lines.append("    requires")
        for idx_r, rl in enumerate(req_lines):
            sep = "," if idx_r < len(req_lines) - 1 else ""
            lines.append(f"        {rl}{sep}")
    lines.append("{")
    lines.append(f"    while ({cond_text})")
    if inv_inside:
        lines.append("        invariant")
        for idx_l, l in enumerate(inv_inside):
            sep = "," if idx_l < len(inv_inside) - 1 else ""
            lines.append(f"            {l}{sep}")
    if dec_text:
        lines.append(f"        decreases {dec_text},")
    lines.append("    {")
    # indent body lines by 8 spaces
    for bl in body_text.splitlines():
        if bl == "":
            lines.append("")
        else:
            lines.append(f"        {bl}")
    lines.append("    }")
    lines.append("}")
    return "\n".join(lines)


def convert_file(input_path: Path, output_dir: Path) -> Path:
    src = read_text(input_path)
    verus_span = find_verus_block(src)
    if not verus_span:
        raise RuntimeError("verus! block not found")
    vb_start, vb_end = verus_span
    verus_body = src[vb_start+1:vb_end]

    fn_infos = find_functions(verus_body)
    if not fn_infos:
        # No functions found; emit original file unchanged
        out_path = output_dir / input_path.name
        write_text(out_path, src)
        return out_path

    # choose the first function that actually contains a while loop
    chosen = None
    for info in fn_infos:
        inner = info['body'][1:-1]
        if find_while_loops(inner):
            chosen = info
            break
    if chosen is None:
        # fallback to the first function
        chosen = fn_infos[0]
    fn_info = chosen

    # parse original params and detect mut vectors
    orig_params_list = parse_params(fn_info['signature'])
    # store as list of (name, type)
    orig_params = orig_params_list
    mut_vectors = set()
    for name, typ in orig_params:
        if '&mut' in typ and 'Vec<' in typ:
            mut_vectors.add(name)

    # body content without outer braces
    func_body_inner = fn_info['body'][1:-1]

    # find all while loops
    whiles = find_while_loops(func_body_inner)
    if not whiles:
        # nothing to do; just copy file
        out_path = output_dir / input_path.name
        write_text(out_path, src)
        return out_path

    generated_fns = []
    # For collecting lets up to each while start
    for idx, wl in enumerate(whiles):
        pre_region = func_body_inner[:wl['start']]
        lets_total = parse_lets_before(pre_region)
        # Determine mut scalar names from lets
        mut_scalars = set(name for name, is_mut, typ in lets_total if is_mut and (typ is None or 'Vec<' not in (typ or '')))
        # plus any &mut scalar params (rare)
        for name, typ in orig_params:
            if '&mut' in typ and 'Vec<' not in typ:
                mut_scalars.add(name)

        # mut vectors include original &mut Vec params and any let mut Vec
        mut_vector_names = set(mut_vectors)
        for name, is_mut, typ in lets_total:
            if is_mut and typ and 'Vec<' in typ:
                mut_vector_names.add(name)

        # prepare parameter list: original params + lets_total
        wl_code = generate_whileloop_fn(idx, len(whiles), orig_params, lets_total, wl, mut_scalars, mut_vector_names)
        generated_fns.append(wl_code)

    insert_pos_in_verus = vb_start + 1 + fn_info['end']
    new_src = src[:insert_pos_in_verus] + "\n\n" + "\n\n".join(generated_fns) + src[insert_pos_in_verus:]

    out_path = output_dir / input_path.name
    write_text(out_path, new_src)
    return out_path


def main():
    if len(sys.argv) != 3:
        print("Usage: python convert.py path/to/input.rs path/to/save/folder", file=sys.stderr)
        sys.exit(1)
    input_path = Path(sys.argv[1]).resolve()
    output_dir = Path(sys.argv[2]).resolve()
    if not input_path.exists():
        print(f"Input file not found: {input_path}", file=sys.stderr)
        sys.exit(2)
    try:
        out = convert_file(input_path, output_dir)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(3)
    print(f"Converted written to: {out}")


if __name__ == "__main__":
    main()


