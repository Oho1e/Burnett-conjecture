"""Check the paper-specific source partition and dependency plan.

This checks a plan's structure and source identity. It does not prove any
mathematical input, certify semantic completeness, or approve author decisions.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re


class SliceError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SliceError(message)


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def formal_environments(text: str) -> dict:
    pattern = r"\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}"
    results = {}
    for match in re.finditer(pattern, text, re.S):
        labels = re.findall(r"\\label\{([^}]+)\}", match.group(2))
        # The main theorem also contains labelled equations. Its first label
        # identifies the result; later equation labels are not new results.
        require(bool(labels), "formal-environment-label: missing result label")
        key = labels[0]
        require(key not in results, f"duplicate-formal-label: {key}")
        results[key] = {
            "kind": match.group(1),
            "start": text.count("\n", 0, match.start()) + 1,
            "end": text.count("\n", 0, match.end()) + 1,
        }
    starts = re.findall(r"\\begin\{(?:theorem|lemma|proposition|corollary)\}", text)
    require(len(results) == len(starts), "formal-environment: unmatched result environment")
    return results


def validate(repo: Path, plan: dict) -> dict:
    scope = load(repo / "docs/formalization/scope.json")
    source_index = load(repo / "docs/statements/source-index.json")
    require(plan.get("schema") == "burnett-proof-slices.v1", "schema: unsupported slice plan")
    require(plan.get("status_source") == "docs/formalization/scope.json", "status-source: use canonical scope")
    require(plan.get("paper_formalization_verified") is False, "completion: plan cannot certify paper")
    paper = plan["paper"]
    require(paper["path"] == scope["paper"]["path"], "paper-path: different article")
    data = (repo / paper["path"]).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    require(digest == paper["sha256"] == scope["paper"]["sha256"], "paper-hash: source changed")
    text = data.decode("utf-8")
    line_count = len(text.splitlines())
    require(line_count == paper["line_count"], "line-count: source changed")

    nodes = plan["slices"]
    require(bool(nodes), "partition: empty plan")
    by_id = {}
    next_line = 1
    roles = {"context", "specification", "proof-unit", "assembly", "scope-candidate"}
    for node in nodes:
        ident = node["id"]
        require(bool(re.fullmatch(r"[A-Z][A-Z0-9]*", ident)), f"slice-id: {ident}")
        require(ident not in by_id, f"duplicate-slice: {ident}")
        require(node["type"] in roles, f"slice-type: {ident}")
        start, end = node["source_start"], node["source_end"]
        require(type(start) is int and type(end) is int, f"partition: non-integer range {ident}")
        require(start == next_line and start <= end <= line_count,
                f"partition: gap/overlap/out-of-range at {ident}, expected {next_line}")
        next_line = end + 1
        for key in ("title", "goal", "next_action"):
            require(isinstance(node.get(key), str) and bool(node[key].strip()), f"interface: {ident}.{key}")
        for key in ("inputs", "outputs", "risks"):
            require(isinstance(node.get(key), list) and bool(node[key])
                    and all(isinstance(s, str) and s.strip() for s in node[key]),
                    f"interface: {ident}.{key}")
        by_id[ident] = node
    require(next_line == line_count + 1, "partition: uncovered source tail")

    actual = formal_environments(text)
    indexed = {r["label"]: r for r in source_index["formal_results"]}
    canonical = {r["claim_id"]: r for r in scope["inventory"]
                 if r["kind"] in {"theorem", "lemma", "proposition", "corollary"}}
    require(set(actual) == set(indexed) == set(canonical), "formal-inventory: source/index/scope disagree")
    for claim, result in actual.items():
        canonical_ref = canonical[claim]["source_ref"]
        require(result["kind"] == indexed[claim]["kind"] == canonical[claim]["kind"]
                and result["start"] == indexed[claim]["source_line"]
                and result["end"] == indexed[claim]["source_endline"]
                and result["start"] == canonical_ref["line"]
                and result["end"] == canonical_ref["endline"], f"formal-source-location: {claim}")
    bindings = plan["formal_results"]
    require(len(bindings) == len(actual)
            and {r["claim_id"] for r in bindings} == set(actual), "formal-binding: missing/duplicate result")
    for binding in bindings:
        claim = binding["claim_id"]
        result = actual[claim]
        statement = by_id.get(binding["statement_slice"])
        require(statement is not None and statement["type"] != "context"
                and statement["source_start"] <= result["start"]
                and result["end"] <= statement["source_end"], f"statement-binding: {claim}")
        proof = binding["proof_slices"]
        closure = binding["closure_slice"]
        require(bool(proof) and len(proof) == len(set(proof)) and all(n in by_id for n in proof),
                f"proof-binding: {claim}")
        require(closure in proof and by_id[closure]["type"] in {"proof-unit", "assembly"},
                f"closure-binding: {claim}")
        loc = indexed[claim]["argument_locator"]
        require(type(loc["source_line"]) is int and type(loc["source_endline"]) is int
                and 1 <= loc["source_line"] <= loc["source_endline"] <= line_count,
                f"proof-locator-range: {claim}")
        require(by_id[closure]["source_start"] <= loc["source_endline"] <= by_id[closure]["source_end"],
                f"closure-location: {claim}")
        for line in range(loc["source_line"], loc["source_endline"] + 1):
            require(any(by_id[n]["source_start"] <= line <= by_id[n]["source_end"] for n in proof),
                    f"proof-range-coverage: {claim} line {line}")

    required_unnumbered = {r["claim_id"]: r for r in scope["inventory"]
                          if r["kind"] == "unnumbered-result" and r["disposition"] == "formalize"}
    unnumbered_bindings = plan["required_unnumbered_results"]
    require(len(unnumbered_bindings) == len(required_unnumbered)
            and {r["claim_id"] for r in unnumbered_bindings} == set(required_unnumbered),
            "unnumbered-binding: required user decision missing")
    for binding in unnumbered_bindings:
        ref = required_unnumbered[binding["claim_id"]]["source_ref"]
        owner = by_id.get(binding["closure_slice"])
        require(owner is not None and owner["type"] in {"proof-unit", "assembly"}
                and owner["source_start"] <= ref["line"] <= ref["endline"] <= owner["source_end"],
                f"unnumbered-closure: {binding['claim_id']}")

    placement = plan["inventory_placement"]
    inventory = {row["claim_id"]: row for row in scope["inventory"]}
    require(len(placement) == len(inventory)
            and {row["claim_id"] for row in placement} == set(inventory), "inventory-placement: missing/duplicate claim")
    for row in placement:
        ref = inventory[row["claim_id"]]["source_ref"]
        require(ref["path"] == paper["path"] and type(ref["line"]) is int and type(ref["endline"]) is int
                and 1 <= ref["line"] <= ref["endline"] <= line_count,
                f"inventory-source-range: {row['claim_id']}")
        expected = [n["id"] for n in nodes if n["source_start"] <= ref["endline"]
                    and ref["line"] <= n["source_end"]]
        require(row["source_slices"] == expected, f"inventory-overlap: {row['claim_id']}")

    edges_seen = set()
    graph = {ident: [] for ident in by_id}
    indegree = Counter({ident: 0 for ident in by_id})
    for edge in plan["edges"]:
        a, b, kind = edge["from"], edge["to"], edge["kind"]
        require(a in by_id and b in by_id and a != b, f"edge-endpoint: {a}->{b}")
        require(kind in {"proof-input", "definition", "specification", "application", "explanation"}, f"edge-kind: {a}->{b}")
        key = (a, b, kind)
        require(key not in edges_seen, f"duplicate-edge: {a}->{b}/{kind}")
        edges_seen.add(key)
        require(isinstance(edge.get("reason"), str) and bool(edge["reason"].strip()), f"edge-reason: {a}->{b}")
        require(bool(edge.get("source_lines")) and all(type(i) is int and 1 <= i <= line_count
                                                     for i in edge["source_lines"]), f"edge-evidence: {a}->{b}")
        if kind in {"proof-input", "definition"}:
            graph[a].append(b)
            indegree[b] += 1
    queue = [ident for ident in by_id if indegree[ident] == 0]
    order = []
    for ident in queue:
        order.append(ident)
        for consumer in graph[ident]:
            indegree[consumer] -= 1
            if indegree[consumer] == 0:
                queue.append(consumer)
    require(len(order) == len(nodes), "dependency-cycle: retain coupled closure or correct edges explicitly")

    for group in plan["closure_groups"]:
        members = group["members"]
        require(bool(members) and all(n in by_id for n in members)
                and group["closure_slice"] in members, f"closure-group: {group['id']}")
        require(bool(group["shared_obligations"]), f"closure-obligations: {group['id']}")
    overview_nodes = plan["overview"]["nodes"]
    overview_ids = {n["id"] for n in overview_nodes}
    require(len(overview_ids) == len(overview_nodes), "overview-node: duplicate id")
    for node in overview_nodes:
        require(bool(node["title"]) and bool(node["members"])
                and all(n in by_id for n in node["members"]), f"overview-members: {node['id']}")
    for edge in plan["overview"]["edges"]:
        require(len(edge) == 2 and edge[0] in overview_ids and edge[1] in overview_ids
                and edge[0] != edge[1], "overview-edge: invalid endpoint")
    for ext in plan["external_interfaces"]:
        require(bool(ext["consumers"]) and all(n in by_id for n in ext["consumers"]),
                f"external-consumer: {ext['id']}")
        require(ext["status"] in {"exact-version-and-Lean-interface-pending", "Lean-interface-pending"},
                f"external-status: {ext['id']}")
    labels = set(re.findall(r"\\label\{([^}]+)\}", text))
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", text)
    require(all(label in labels for label in refs), "source-reference: undefined article label")
    return {
        "status": "slicing-structure-passed", "paper_sha256": digest,
        "source_lines_partitioned": line_count, "slice_count": len(nodes),
        "slice_types": dict(Counter(n["type"] for n in nodes)),
        "formal_results_mapped": len(actual), "inventory_entries_placed": len(placement),
        "required_unnumbered_results_mapped": len(unnumbered_bindings),
        "dependency_edges": len(edges_seen), "topological_order": order,
        "source_label_count": len(labels), "source_reference_count": len(refs),
        "semantic_completeness_certified": False, "paper_formalization_verified": False,
    }


def render(plan: dict) -> str:
    out = ["# 全文切片与数学依赖", "",
           "这是当前锁定文章的工作分解图。切片覆盖每一行源码；数学完成状态仍以 [scope.json](scope.json) 为准。",
           "正文范围、接口和依赖来自本次逐区阅读；结构检查不证明数学结论，也不认证全文语义无遗漏。",
           "", f"原文：`{plan['paper']['path']}`，{plan['paper']['line_count']}行，SHA256 `{plan['paper']['sha256']}`。",
           "", "机器清单：[slices.json](slices.json)。本页由 `python scripts/check_slices.py --repo . --write-view` 生成。",
           "", "## 使用方式", "",
           "先选一个切片，检查其直接输入及 scope 中的实际证明状态，再执行其下一步。完成后沿出边检查消费者；闭合组保留同一见证、参数和极限的共同责任。",
           "边类型：proof-input 是证明输入，definition/specification 是定义或规格，application 是条件引理的应用来源，explanation 是说明联系。定义可先实现，无须先闭合提供片的全部证明；application 不要求先证明其来源定理才能证明一般条件引理。",
           "例子及背景也有源码归属，其认证范围仍按既有标准和待决项处理。",
           "", "## 主线概览", "", "```mermaid", "flowchart TD"]
    for node in plan["overview"]["nodes"]:
        out.append(f'  {node["id"]}["{node["title"]}"]')
    for edge in plan["overview"]["edges"]:
        out.append(f'  {edge[0]} --> {edge[1]}')
    out += ["```", "", "该图是主线概览；全部直接依赖见下表及机器清单。附录正式结果保留独立工作支线。",
            "", "## 全文范围", "", "| 切片 | 原文行 | 类型 | 可交付结果 | 直接输入片 |", "| --- | --- | --- | --- | --- |"]
    for node in plan["slices"]:
        deps = [f"{e['from']}（{e['kind']}）" for e in plan["edges"] if e["to"] == node["id"]]
        out.append(f"| [{node['id']}](#{node['id'].lower()}) {node['title']} | {node['source_start']}–{node['source_end']} | {node['type']} | {node['goal'].replace('|', '／')} | {', '.join(deps) or '—'} |")
    out += ["", "## 正式结果的陈述与证明闭合", "",
            "陈述片与闭合片可以不同；表中归属是实施计划，不是完成标记。全部17项仍通过 scope 追踪。", "",
            "| 原文结果 | 陈述片 | 证明范围片 | 共同闭合片 |", "| --- | --- | --- | --- |"]
    for row in plan["formal_results"]:
        out.append(f"| `{row['claim_id']}` | {row['statement_slice']} | {', '.join(row['proof_slices'])} | {row['closure_slice']} |")
    out += ["", "用户另行确认必须形式化的未编号结果：", ""]
    for row in plan["required_unnumbered_results"]:
        out.append(f"- `{row['claim_id']}`：闭合片 {row['closure_slice']}；当前证明状态见 scope。")
    out += ["", "## 共同闭合组", ""]
    for group in plan["closure_groups"]:
        out += [f"### {group['id']}：{group['title']}", "",
                f"成员：{', '.join(group['members'])}；闭合于 {group['closure_slice']}。", ""]
        out += [f"- {s}" for s in group["shared_obligations"]] + [""]
    out += ["## 逐片接口与下一步", ""]
    for node in plan["slices"]:
        out += [f"<a id=\"{node['id'].lower()}\"></a>", "",
                f"### {node['id']} {node['title']}", "",
                f"原文{node['source_start']}–{node['source_end']}行；{node['type']}。{node['goal']}", "", "输入：", ""]
        out += [f"- {s}" for s in node["inputs"]] + ["", "输出：", ""]
        out += [f"- {s}" for s in node["outputs"]] + ["", "需保留的边界：", ""]
        out += [f"- {s}" for s in node["risks"]]
        consumers = [f"{e['to']}（{e['kind']}）" for e in plan["edges"] if e["from"] == node["id"]]
        out += ["", "消费者：" + ("、".join(consumers) if consumers else "此片未向其他片提供数学输入或应用。"), ""]
        if node.get("supplementary_obligations"):
            out += ["片内细化义务（不另建完成状态）：", ""]
            out += [f"- {s['description']}（原文{s['source_lines'][0]}–{s['source_lines'][-1]}行）"
                    for s in node["supplementary_obligations"]]
        out += ["", f"下一步：{node['next_action']}", ""]
    out += ["## 待核外部接口", ""]
    for ext in plan["external_interfaces"]:
        out += [f"- **{ext['id']}**：{ext['description']} 消费者：{', '.join(ext['consumers'])}；状态：`{ext['status']}`。"]
    out += ["", "## 本次发现与保留项", ""]
    out += [f"- {s}" for s in plan["review_notes"]]
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument("--write-view", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    output = repo / ".project-verification/slicing/result.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    started_at = datetime.now(timezone.utc).isoformat()
    report = {"status": "slicing-structure-failed", "error": "Run has not completed",
              "started_at": started_at, "semantic_completeness_certified": False,
              "paper_formalization_verified": False}
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    try:
        plan_path = repo / "docs/formalization/slices.json"
        plan = load(plan_path)
        report.update(validate(repo, plan))
        view_path = repo / "docs/formalization/slices.md"
        rendered = render(plan)
        if args.write_view:
            view_path.write_text(rendered, encoding="utf-8", newline="\n")
        else:
            require(view_path.read_text(encoding="utf-8") == rendered, "view-drift: regenerate slices.md with --write-view")
        report["manifest_sha256"] = hashlib.sha256(plan_path.read_bytes()).hexdigest()
        report.pop("error", None)
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(json.dumps(report, ensure_ascii=False))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        report.update(status="slicing-structure-failed", error=str(error),
                      finished_at=datetime.now(timezone.utc).isoformat())
        output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(f"slicing-structure-failed: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
