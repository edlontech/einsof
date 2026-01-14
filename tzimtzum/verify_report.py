#!/usr/bin/env python3
"""Parse Veil #check_invariants build output and produce a verification report."""

import sys
import re
from datetime import datetime, timezone
from pathlib import Path
from collections import OrderedDict


def parse_build_log(text: str) -> dict:
    """Extract #check_invariants results from plain text build output."""
    result = {"init": OrderedDict(), "actions": OrderedDict()}

    init_match = re.search(
        r"Initialization must establish the invariant:\s*\n((?:\s+\w+\s+\.\.\.\s+[✅❌]\n?)+)",
        text,
    )
    if init_match:
        for match in re.finditer(r"(\w+)\s+\.\.\.\s+(✅|❌)", init_match.group(1)):
            result["init"][match.group(1)] = match.group(2) == "✅"

    actions_match = re.search(
        r"The following set of actions must preserve the invariant "
        r"and successfully terminate:\s*\n([\s\S]+?)(?:\nwarning:|\nerror:|\Z)",
        text,
    )
    if actions_match:
        current_action = None
        for line in actions_match.group(1).splitlines():
            line = line.rstrip()
            if not line.strip():
                continue
            prop_match = re.match(r"\s{4,}(\w+)\s+\.\.\.\s+(✅|❌)", line)
            action_match = re.match(r"  (\w+)\s*$", line)
            if prop_match and current_action:
                result["actions"].setdefault(current_action, OrderedDict())
                result["actions"][current_action][prop_match.group(1)] = (
                    prop_match.group(2) == "✅"
                )
            elif action_match:
                current_action = action_match.group(1)

    return result


def parse_timing(text: str) -> str | None:
    """Extract #time gen_spec timing."""
    match = re.search(r"(\d+\.\d+s)", text)
    if match:
        return match.group(1)
    return None


def classify_properties(names: list[str]) -> tuple[list[str], list[str], list[str]]:
    """Classify property names into safeties, invariants, and internal."""
    known_safeties = {
        "root_always_active", "default_deny", "flow_confinement",
        "flow_confinement_weak", "capability_subsumption",
        "revocation_clean", "taint_integrity",
    }
    known_internal = {"doesNotThrow"}

    safeties, invariants, internal = [], [], []
    for name in names:
        if name in known_internal:
            internal.append(name)
        elif name in known_safeties:
            safeties.append(name)
        else:
            invariants.append(name)

    return safeties, invariants, internal


def count_lines(spec_path: Path) -> int:
    if not spec_path.exists():
        return 0
    return sum(1 for line in spec_path.read_text().splitlines() if line.strip())


def render_report(data: dict, spec_path: Path, timing: str | None) -> str:
    lines = []

    all_props = list(data.get("init", {}).keys())
    actions = list(data.get("actions", {}).keys())
    safeties, invariants, internal = classify_properties(all_props)

    total_vcs, passed_vcs, failed_vcs = 0, 0, 0
    for ok in data.get("init", {}).values():
        total_vcs += 1
        passed_vcs += 1 if ok else 0
        failed_vcs += 0 if ok else 1
    for action_props in data.get("actions", {}).values():
        for ok in action_props.values():
            total_vcs += 1
            passed_vcs += 1 if ok else 0
            failed_vcs += 0 if ok else 1

    status = "PASSED" if failed_vcs == 0 else "FAILED"
    loc = count_lines(spec_path)
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    lines.append("# Tzimtzum v2.3 -- Verification Report\n")
    lines.append("| | |")
    lines.append("|---|---|")
    lines.append(f"| **Spec** | `{spec_path.name}` ({loc} lines) |")
    lines.append("| **Prover** | Lean 4 + Veil 2.0 + cvc5 (SMT) |")
    lines.append(f"| **Date** | {now} |")
    lines.append(f"| **Status** | **{status}** |")
    lines.append(f"| **VCs** | {passed_vcs}/{total_vcs} passed |")
    if timing:
        lines.append(f"| **Time** | {timing} |")
    lines.append("")

    def mark(ok: bool | None) -> str:
        if ok is True:
            return "PASS"
        if ok is False:
            return "FAIL"
        return "-"

    def render_table(props: list[str], label: str):
        if not props:
            return
        lines.append(f"## {label} ({len(props)})\n")
        header = ["Property", "Init"] + actions
        lines.append("| " + " | ".join(header) + " |")
        lines.append("| " + " | ".join(["---"] * len(header)) + " |")
        for prop in props:
            row = [f"`{prop}`"]
            row.append(mark(data.get("init", {}).get(prop)))
            for action in actions:
                row.append(mark(data.get("actions", {}).get(action, {}).get(prop)))
            lines.append("| " + " | ".join(row) + " |")
        lines.append("")

    render_table(safeties, "Safety Properties")
    render_table(invariants, "Strengthening Invariants")

    lines.append("## Summary\n")
    lines.append(f"- {len(safeties)} safety properties")
    lines.append(f"- {len(invariants)} strengthening invariants")
    lines.append(f"- {len(actions)} actions verified")
    lines.append(f"- {total_vcs} verification conditions total")
    lines.append(f"- {passed_vcs} passed, {failed_vcs} failed")
    lines.append("")

    return "\n".join(lines)


def main():
    spec_path = Path("TzimtzumV2.lean")
    text = sys.stdin.read()

    data = parse_build_log(text)
    if not data.get("init") and not data.get("actions"):
        print("No verification results found in build output.", file=sys.stderr)
        sys.exit(1)

    timing = parse_timing(text)
    report = render_report(data, spec_path, timing)
    print(report)


if __name__ == "__main__":
    main()
