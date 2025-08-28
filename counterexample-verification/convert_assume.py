#!/usr/bin/env python3
import sys
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
    brace_open = m.end() - 1
    brace_close = find_matching_brace(src, brace_open)
    if brace_close == -1:
        return None
    return (brace_open, brace_close)


def find_functions(body: str):
    infos = []
    idx = 0
    while True:
        m = re.search(r"(?:pub\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", body[idx:])
        if not m:
            break
        name = m.group(1)
        sig_start = idx + m.start()
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
        mt = re.match(r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$", p)
        if not mt:
            continue
        name = mt.group(1).strip()
        typ = mt.group(2).strip()
        params.append((name, typ))
    return params


def strip_ensures(signature: str) -> str:
    if 'ensures' not in signature:
        return signature
    # Remove everything from the first 'ensures' line to the end of signature
    return re.sub(r"\n\s*ensures[\s\S]*$", "", signature, flags=re.MULTILINE)


def find_while_loops(func_body_inner: str):
    whiles = []
    idx = 0
    while True:
        m = re.search(r"\bwhile\b", func_body_inner[idx:])
        if not m:
            break
        start = idx + m.start()

        # Determine condition
        if func_body_inner[start + 5:start + 6] == '(':
            cond_start = start + 6
            depth = 1
            i = cond_start
            while i < len(func_body_inner) and depth > 0:
                if func_body_inner[i] == '(':
                    depth += 1
                elif func_body_inner[i] == ')':
                    depth -= 1
                i += 1
            cond_end = i - 1
            condition = func_body_inner[cond_start:cond_end].strip()
        else:
            cond_start = start + 5
            while cond_start < len(func_body_inner) and func_body_inner[cond_start].isspace():
                cond_start += 1
            cond_end = cond_start
            while cond_end < len(func_body_inner):
                if func_body_inner[cond_end] in '{' or func_body_inner[cond_end:cond_end+9] == 'invariant':
                    break
                cond_end += 1
            condition = func_body_inner[cond_start:cond_end].strip()

        # Header tail until body '{'
        header_tail_start = cond_end + 1 if func_body_inner[start + 5:start + 6] == '(' else cond_end
        brace_header_idx = func_body_inner.find('{', header_tail_start)
        if brace_header_idx == -1:
            break
        header_tail = func_body_inner[header_tail_start:brace_header_idx]

        inv_clauses = []
        inv_match = re.search(r"invariant", header_tail)
        if inv_match:
            inv_block = header_tail[inv_match.end():]
            # Remove decreases from inv parsing area if present at the tail
            dec_match = re.search(r"decreases\s+(.+?),\s*$", inv_block, re.DOTALL | re.MULTILINE)
            if dec_match:
                inv_only = inv_block[:dec_match.start()]
            else:
                inv_only = inv_block

            # Split clauses by commas that are not inside parentheses/brackets.
            # Handle forall clauses specially to avoid splitting them incorrectly
            depth_paren = 0
            depth_brack = 0
            depth_pipe = 0  # Track | | pairs in forall
            current = []
            def flush():
                clause = ''.join(current).strip()
                if clause:
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
                elif ch == '|':
                    # Track pipe depth for forall clauses
                    if i2 >= 6 and inv_only[i2-6:i2] == 'forall':
                        depth_pipe += 1
                    elif depth_pipe > 0:
                        depth_pipe -= 1
                
                # Only split on comma if we're at top level (no nesting)
                if ch == ',' and depth_paren == 0 and depth_brack == 0 and depth_pipe == 0:
                    flush()
                    current = []
                    i2 += 1
                    continue
                current.append(ch)
                i2 += 1
            flush()

        body_start = brace_header_idx
        body_end = find_matching_brace(func_body_inner, body_start)
        if body_end == -1:
            break
        body_inner = func_body_inner[body_start+1:body_end]

        whiles.append({
            'start': start,
            'end': body_end+1,
            'condition': condition,
            'invariants': inv_clauses,
            'body_inner': body_inner,
        })
        idx = body_end + 1
    return whiles


def parse_lets_before(src_before: str):
    # Collect only top-level (depth==0) let bindings before the while
    names = []
    seen = set()
    depth = 0
    i = 0
    while i < len(src_before):
        ch = src_before[i]
        if ch == '{':
            depth += 1
            i += 1
            continue
        if ch == '}':
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            m = re.match(r"let\s+(?:ghost\s+|mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\b", src_before[i:])
            if m:
                name = m.group(1)
                if name not in seen and name != 'mut':
                    seen.add(name)
                    names.append(name)
                # advance to end of line to avoid nested matches
                nl = src_before.find('\n', i)
                i = len(src_before) if nl == -1 else nl + 1
                continue
        i += 1
    return names


def normalize_body_indentation(text: str) -> str:
    lines = text.splitlines()
    # Trim empty edges
    while lines and lines[0].strip() == "":
        lines.pop(0)
    while lines and lines[-1].strip() == "":
        lines.pop()
    if not lines:
        return ""
    def leading_ws_len(s: str) -> int:
        i = 0
        while i < len(s) and s[i] in (' ', '\t'):
            i += 1
        return i
    non_empty = [l for l in lines if l.strip() != ""]
    common = min((leading_ws_len(l) for l in non_empty), default=0)
    normalized = []
    for l in lines:
        if l.strip() == "":
            normalized.append("")
        else:
            ws_len = leading_ws_len(l)
            cut = min(common, ws_len)
            normalized.append(l[cut:])
    return "\n".join(normalized)


def sanitize_loop_body_for_no_loop(body: str) -> str:
    # Remove 'break;' and 'continue;' which are invalid outside loops
    body = re.sub(r"\bbreak\s*;", "", body)
    body = re.sub(r"\bcontinue\s*;", "", body)
    return body


def indent_lines(text: str, indent: str) -> str:
    return "\n".join((indent + l) if l != "" else "" for l in text.splitlines())


def build_tuple_rebind_line(indent: str, param_name_types, let_names, label_tag: str):
    # Exclude params with &mut types and reserved identifier 'mut'
    names = []
    seen = set()
    for name, typ in param_name_types:
        if name == 'mut':
            continue
        if '&mut' in typ:
            continue
        if name not in seen:
            seen.add(name)
            names.append(name)
    for n in let_names:
        if n == 'mut':
            continue
        if n not in seen:
            seen.add(n)
            names.append(n)
    if not names:
        return None
    left = ", ".join(f"mut {n}" for n in names)
    right = ", ".join(names)
    return f"{indent}// place to add variables assignment. {label_tag}\n{indent}let ({left}) = ({right});"


def remove_while_blocks(text: str) -> str:
    out_parts = []
    i = 0
    n = len(text)
    while i < n:
        m = re.search(r"\bwhile\b", text[i:])
        if not m:
            out_parts.append(text[i:])
            break
        start = i + m.start()
        # find next '{' after while header
        brace_idx = text.find('{', start)
        if brace_idx == -1:
            out_parts.append(text[i:start])
            break
        end_idx = find_matching_brace(text, brace_idx)
        if end_idx == -1:
            out_parts.append(text[i:start])
            break
        out_parts.append(text[i:start])
        i = end_idx + 1
    return ''.join(out_parts)


def remove_asserts(text: str) -> str:
    # Remove single-line assert(...) and assert!(...) statements
    # But preserve them if they're part of the loop body (we'll handle this differently)
    text = re.sub(r"(?m)^[ \t]*assert!?\s*\([^;]*\);\s*$", "", text)
    return text


def replace_while_with_assume_assert(func_inner: str, wl, param_name_types, let_names, label_tag: str) -> str:
    # Determine indent of the while statement
    line_start = func_inner.rfind('\n', 0, wl['start']) + 1
    while_indent = re.match(r"[ \t]*", func_inner[line_start:]).group(0)

    # Prepare pieces
    tuple_line = build_tuple_rebind_line(while_indent, param_name_types, let_names, label_tag)
    def strip_inline_comments(s: str) -> str:
        return re.sub(r"//.*", "", s).strip()

    assumes = []
    assumes.append(f"{while_indent}assume({wl['condition']});")
    for inv in wl['invariants']:
        inv_clean = strip_inline_comments(inv)
        # Skip malformed quantifiers like 'forall|k: int|' with no body
        if re.match(r"^forall\s*\|[^|]+\|\s*$", inv_clean):
            continue
        if inv_clean:
            assumes.append(f"{while_indent}assume({inv_clean});")

    body = normalize_body_indentation(wl['body_inner'])
    body = sanitize_loop_body_for_no_loop(body)
    # Remove nested while loops but preserve asserts inside the loop body
    body = remove_while_blocks(body)
    # Don't remove asserts from the loop body - they should be preserved
    # body = remove_asserts(body)  # Commented out to preserve loop body asserts
    body_indented = indent_lines(body, while_indent)

    # Generate asserts from invariants
    asserts = []
    for inv in wl['invariants']:
        inv_clean = strip_inline_comments(inv)
        # Skip malformed quantifiers like 'forall|k: int|' with no body
        if re.match(r"^forall\s*\|[^|]+\|\s*$", inv_clean):
            continue
        if inv_clean:
            asserts.append(f"{while_indent}assert({inv_clean});")

    replacement_parts = []
    if tuple_line:
        replacement_parts.append(tuple_line)
        replacement_parts.append("")
    replacement_parts.extend(assumes)
    replacement_parts.append("")
    replacement_parts.append(body_indented)
    
    # Add asserts only if there are any (we removed them earlier but keeping this for consistency)
    if asserts:
        replacement_parts.append("")
        replacement_parts.extend(asserts)

    replacement = "\n".join(part for part in replacement_parts if part is not None)

    before = func_inner[:wl['start']]
    after = func_inner[wl['end']:]
    
    # Extract any final return statement or expression from after
    after_clean = remove_while_blocks(after)
    after_clean = remove_asserts(after_clean)
    
    # Look for return statements or final expressions
    final_return = extract_final_return_or_expression(after_clean, while_indent)
    
    result = before + replacement
    if final_return:
        result += "\n" + final_return
    
    return result


def extract_final_return_or_expression(text: str, indent: str) -> str:
    """Extract final return statement or expression that should be preserved"""
    text = text.strip()
    if not text:
        return ""
    
    lines = text.splitlines()
    non_empty_lines = [l for l in lines if l.strip()]
    
    if not non_empty_lines:
        return ""
    
    # Check the last non-empty line
    last_line = non_empty_lines[-1].strip()
    
    # If it's a return statement, preserve it
    if last_line.startswith('return ') or last_line == 'return;':
        return indent + last_line
    
    # If it's a simple expression (likely a return value), preserve it
    if not last_line.endswith(';') and not last_line.startswith('let ') and not '{' in last_line and not '}' in last_line:
        return indent + last_line
    
    return ""


def clean_main_function(verus_body: str) -> str:
    """Remove test assertions and function calls from main function, keeping it empty"""
    # Find main function
    main_match = re.search(r"fn\s+main\s*\(\s*\)\s*\{", verus_body)
    if not main_match:
        return verus_body
    
    main_start = main_match.start()
    brace_start = main_match.end() - 1  # position of '{'
    brace_end = find_matching_brace(verus_body, brace_start)
    if brace_end == -1:
        return verus_body
    
    # Replace main body with empty body
    before = verus_body[:main_start]
    main_header = verus_body[main_start:brace_start]
    after = verus_body[brace_end+1:]
    
    return before + main_header + " {}" + after


def convert_file(input_path: Path, output_dir: Path) -> Path:
    src = read_text(input_path)
    
    # Clean main function in the entire source first (before verus block processing)
    src = clean_main_function(src)
    
    verus_span = find_verus_block(src)
    if not verus_span:
        raise RuntimeError("verus! block not found")
    vb_start, vb_end = verus_span
    verus_body = src[vb_start+1:vb_end]

    fn_infos = find_functions(verus_body)
    if not fn_infos:
        out_path = output_dir / input_path.name
        write_text(out_path, src)
        return out_path

    new_verus_body = verus_body
    # We'll append variants after the last function body.
    append_pieces = []

    for fn in fn_infos:
        sig = fn['signature']
        body = fn['body']
        inner = body[1:-1]

        whiles = find_while_loops(inner)
        if not whiles:
            continue

        param_name_types = parse_params(sig)

        for idx, wl in enumerate(whiles):
            # Collect let names before this while
            pre_region = inner[:wl['start']]
            let_names = parse_lets_before(pre_region)

            # Build new function name and header
            new_name = f"{fn['name']}_while{idx+1}"
            pattern = r"^(\s*(?:pub\s+)?)fn\s+" + re.escape(fn['name']) + r"\b"
            replacement = r"\1fn " + new_name
            sig_renamed = re.sub(pattern, replacement, sig)
            sig_no_ens = strip_ensures(sig_renamed)

            # Replace only the chosen while with assume/assert version
            label_tag = f"[{idx+1}]"
            new_inner = replace_while_with_assume_assert(inner, wl, param_name_types, let_names, label_tag)

            new_fn_text = []
            new_fn_text.append(sig_no_ens)
            new_fn_text.append("{")
            new_fn_text.append(new_inner)
            new_fn_text.append("}")
            append_pieces.append("\n".join(new_fn_text))

    if append_pieces:
        insertion_point = fn_infos[-1]['end']  # relative to verus_body
        new_verus_body = verus_body[:insertion_point] + "\n\n" + "\n\n".join(append_pieces) + verus_body[insertion_point:]

    new_src = src[:vb_start+1] + new_verus_body + src[vb_end:]
    out_path = output_dir / input_path.name
    write_text(out_path, new_src)
    return out_path


def main():
    if len(sys.argv) != 3:
        print("Usage: python convert_assume.py path/to/input.rs path/to/save/folder", file=sys.stderr)
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


