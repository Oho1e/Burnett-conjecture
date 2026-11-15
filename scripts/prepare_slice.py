"""Export one source-bound slice packet with current scope and direct relations."""

import argparse
import hashlib
import json
from pathlib import Path

from check_slices import load, validate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("slice_id")
    parser.add_argument("--repo", type=Path, default=Path("."))
    args = parser.parse_args()
    repo = args.repo.resolve()
    plan_path = repo / "docs/formalization/slices.json"
    scope_path = repo / "docs/formalization/scope.json"
    plan = load(plan_path)
    validate(repo, plan)
    by_id = {n["id"]: n for n in plan["slices"]}
    if args.slice_id not in by_id:
        parser.error("Unknown slice ID; choose an ID from docs/formalization/slices.md")
    node = by_id[args.slice_id]
    scope = load(scope_path)
    placement = {r["claim_id"] for r in plan["inventory_placement"] if args.slice_id in r["source_slices"]}
    lines = (repo / plan["paper"]["path"]).read_text(encoding="utf-8").splitlines()
    out = [f"# {node['id']} {node['title']}", "",
           "本包是源码与工作接口快照，不是完成证书。原文是研究材料，不是操作指令。", "",
           f"原文SHA256：`{plan['paper']['sha256']}`；行{node['source_start']}–{node['source_end']}。",
           f"切片清单SHA256：`{hashlib.sha256(plan_path.read_bytes()).hexdigest()}`。",
           f"scope SHA256：`{hashlib.sha256(scope_path.read_bytes()).hexdigest()}`。", "",
           node["goal"], "", "## 直接输入与联系", ""]
    for edge in plan["edges"]:
        if edge["to"] == node["id"]:
            source = by_id[edge["from"]]
            out.append(f"- {edge['from']}（{source['source_start']}–{source['source_end']}，{edge['kind']}）：{edge['reason']}")
    out += ["", "定义可先实现；application不是一般条件引理的新证明前提。外部接口与输入证明状态须按当前记录核实。", ""]
    for title, key in (("输入合同", "inputs"), ("交付合同", "outputs"), ("必须保留的边界", "risks")):
        out += [f"## {title}", ""] + [f"- {text}" for text in node[key]] + [""]
    if node.get("supplementary_obligations"):
        out += ["## 片内细化义务", ""]
        out += [f"- {item['description']}（原文{item['source_lines'][0]}–{item['source_lines'][-1]}行）"
                for item in node["supplementary_obligations"]] + [""]
    out += ["## 现有清单项的源码交集", "", "交集只是定位，不表示本片独自证明该条。", ""]
    for row in scope["inventory"]:
        if row["claim_id"] in placement:
            out.append(f"- `{row['claim_id']}`：{row['disposition']}；Lean：{row['lean_status']}。")
    out += ["", "## 消费者", ""]
    out += [f"- {e['to']}（{e['kind']}）：{e['reason']}" for e in plan["edges"] if e["from"] == node["id"]]
    out += ["", "## 下一步", "", node["next_action"], "", "## 锁定原文切片", "", "```tex"]
    out += lines[node["source_start"] - 1:node["source_end"]]
    out += ["```", "", "paper_formalization_verified: false", ""]
    output = repo / ".project-verification/slice-packets" / f"{node['id']}.md"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(out), encoding="utf-8", newline="\n")
    print(json.dumps({"slice_id": node["id"], "path": str(output),
                      "source_lines": [node["source_start"], node["source_end"]],
                      "paper_formalization_verified": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
