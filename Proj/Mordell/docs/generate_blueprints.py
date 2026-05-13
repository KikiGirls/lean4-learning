#!/usr/bin/env python3
"""Generate Mordell blueprint artifacts.

The full blueprint is a declaration-level graph extracted from the local Lean
files.  Edges are conservative textual references between project declarations;
the simplified blueprint is a hand-curated graph of the principal proof chain.
"""

from __future__ import annotations

import html
import json
import re
import shutil
import subprocess
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "Mordell"
OUT = ROOT / "docs" / "blueprint"

FILE_ORDER = [
    "ZsqrtdBasic.lean",
    "ZomegaBasic.lean",
    "EuclideanNegTwo.lean",
    "Approximation.lean",
    "Dedekind.lean",
    "ClassGroupApprox.lean",
    "Descent.lean",
    "ClassNumber/Common.lean",
    "ClassNumber/NegFive.lean",
    "ClassNumber/NegSix.lean",
    "ClassNumber/NegThirteen.lean",
    "Solutions.lean",
]

DECL_RE = re.compile(
    r"^(?:(?:noncomputable|protected|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance)\s*"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)?"
)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
END_RE = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?$")


@dataclass
class Decl:
    id: str
    kind: str
    name: str
    qualified: str
    file: str
    line: int
    end_line: int
    body: str


def lean_files() -> list[Path]:
    paths = [SRC / p for p in FILE_ORDER if (SRC / p).exists()]
    known = {p.resolve() for p in paths}
    extras = sorted(p for p in SRC.rglob("*.lean") if p.resolve() not in known)
    return paths + extras


def qualify(namespace: list[str], name: str) -> str:
    if "." in name or not namespace:
        return name
    return ".".join(namespace + [name])


def scan_file(path: Path) -> list[Decl]:
    rel = path.relative_to(SRC).as_posix()
    lines = path.read_text(encoding="utf-8").splitlines()
    namespace: list[str] = []
    starts: list[tuple[int, str, str, str]] = []

    for i, line in enumerate(lines, start=1):
        stripped = line.strip()
        ns = NAMESPACE_RE.match(stripped)
        if ns:
            namespace.append(ns.group(1))
            continue
        end = END_RE.match(stripped)
        if end and namespace:
            namespace.pop()
            continue
        if stripped.startswith("private "):
            continue
        decl = DECL_RE.match(stripped)
        if not decl:
            continue
        kind = decl.group("kind")
        raw_name = decl.group("name")
        if not raw_name:
            raw_name = f"anonymous_{kind}_{rel.replace('/', '_').replace('.', '_')}_{i}"
        qname = qualify(namespace, raw_name)
        starts.append((i, kind, raw_name, qname))

    decls: list[Decl] = []
    for idx, (line, kind, name, qname) in enumerate(starts):
        next_line = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines) + 1
        body = "\n".join(lines[line - 1 : next_line - 1])
        safe_id = re.sub(r"[^A-Za-z0-9_.-]+", "_", f"{rel}:{qname}:{line}")
        decls.append(
            Decl(
                id=safe_id,
                kind=kind,
                name=name,
                qualified=qname,
                file=rel,
                line=line,
                end_line=next_line - 1,
                body=body,
            )
        )
    return decls


def project_decls() -> list[Decl]:
    decls: list[Decl] = []
    for path in lean_files():
        decls.extend(scan_file(path))
    return decls


def token_regex(token: str) -> re.Pattern[str]:
    escaped = re.escape(token)
    return re.compile(rf"(?<![A-Za-z0-9_'.]){escaped}(?![A-Za-z0-9_'.])")


def dependency_edges(decls: list[Decl]) -> list[dict[str, str]]:
    by_id = {d.id: d for d in decls}
    candidates: list[tuple[Decl, str, re.Pattern[str]]] = []
    for d in decls:
        simple = d.name.split(".")[-1]
        if len(simple) >= 6 or simple in {"R5", "R6", "R13"}:
            candidates.append((d, simple, token_regex(simple)))
        if "." in d.qualified:
            candidates.append((d, d.qualified, token_regex(d.qualified)))

    edges: set[tuple[str, str]] = set()
    for target in decls:
        body = "\n".join(target.body.splitlines()[1:])
        if not body:
            continue
        for source, _token, pattern in candidates:
            if source.id == target.id:
                continue
            if pattern.search(body):
                edges.add((source.id, target.id))

    # Keep the graph readable by removing duplicate semantic edges and sorting
    # by source/target layout order.
    order = {d.id: i for i, d in enumerate(decls)}
    return [
        {"from": src, "to": dst, "kind": "textual-reference"}
        for src, dst in sorted(edges, key=lambda e: (order[e[0]], order[e[1]]))
        if src in by_id and dst in by_id
    ]


def full_graph_data(decls: list[Decl], edges: list[dict[str, str]]) -> dict:
    files = []
    grouped: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        grouped[d.file].append(d)
    for file in FILE_ORDER:
        if file in grouped:
            files.append({"file": file, "count": len(grouped[file])})
    for file in sorted(set(grouped) - set(FILE_ORDER)):
        files.append({"file": file, "count": len(grouped[file])})

    return {
        "title": "Mordell Lean 4 full declaration blueprint",
        "source_root": str(SRC),
        "node_count": len(decls),
        "edge_count": len(edges),
        "files": files,
        "nodes": [
            {
                "id": d.id,
                "kind": d.kind,
                "name": d.name,
                "qualified": d.qualified,
                "file": d.file,
                "line": d.line,
                "end_line": d.end_line,
            }
            for d in decls
        ],
        "edges": edges,
    }


def write_json(data: dict) -> None:
    (OUT / "mordell_blueprint_full.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


def write_full_html(data: dict) -> None:
    payload = json.dumps(data, ensure_ascii=False)
    html_doc = f"""<!doctype html>
<html lang="zh-CN">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Mordell Lean 4 完整蓝图</title>
  <style>
    :root {{
      --ink: #18212a;
      --muted: #5b6873;
      --line: #56616b;
      --bg: #f8fafc;
      --panel: #ffffff;
      --blue: #dff0ff;
      --green: #e3f7e7;
      --gold: #fff2c9;
      --rose: #ffe4e8;
      --violet: #eee8ff;
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      color: var(--ink);
      background: var(--bg);
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Noto Sans CJK SC",
        "Microsoft YaHei", sans-serif;
    }}
    header {{
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 18px;
      padding: 18px 22px 14px;
      background: var(--panel);
      border-bottom: 1px solid #dde4eb;
      position: sticky;
      top: 0;
      z-index: 3;
    }}
    h1 {{ margin: 0; font-size: 22px; line-height: 1.25; }}
    .meta {{ color: var(--muted); font-size: 13px; margin-top: 4px; }}
    .controls {{ display: flex; gap: 10px; align-items: center; flex-wrap: wrap; }}
    input, select, button {{
      height: 34px;
      border: 1px solid #b8c4cf;
      border-radius: 7px;
      background: #fff;
      color: var(--ink);
      padding: 0 10px;
      font: inherit;
      font-size: 13px;
    }}
    button {{ cursor: pointer; }}
    main {{ display: grid; grid-template-columns: minmax(0, 1fr) 340px; min-height: calc(100vh - 68px); }}
    #stage {{ overflow: auto; padding: 18px; }}
    #graph {{
      display: block;
      background: #fff;
      border: 1px solid #d6dee6;
      border-radius: 8px;
      box-shadow: 0 12px 34px rgba(31, 47, 70, 0.08);
    }}
    aside {{
      border-left: 1px solid #dde4eb;
      background: var(--panel);
      padding: 18px;
      position: sticky;
      top: 68px;
      height: calc(100vh - 68px);
      overflow: auto;
    }}
    aside h2 {{ margin: 0 0 10px; font-size: 17px; }}
    .detail {{ font-size: 13px; color: var(--muted); line-height: 1.55; }}
    .pill {{
      display: inline-block;
      margin: 4px 4px 0 0;
      padding: 3px 7px;
      border-radius: 999px;
      background: #eef3f7;
      color: #33424f;
      font-size: 12px;
    }}
    .file-title {{ font-size: 13px; fill: #34414c; font-weight: 700; }}
    .file-box {{ fill: #f7f9fc; stroke: #9aa8b3; stroke-width: 1.2; stroke-dasharray: 7 6; rx: 12; }}
    .edge {{ stroke: var(--line); stroke-width: 1.15; fill: none; marker-end: url(#arrow); opacity: .13; }}
    .node rect {{ stroke: #31414d; stroke-width: 1.05; rx: 7; }}
    .node text {{ pointer-events: none; }}
    .node .name {{ font-size: 12px; font-weight: 700; fill: #10202c; }}
    .node .sub {{ font-size: 10px; fill: #5a6874; }}
    .node:hover rect, .node.selected rect {{ stroke-width: 2; stroke: #111827; }}
    .node.dim {{ opacity: .16; }}
    .edge.dim {{ opacity: .015; }}
    .edge.hot {{ opacity: .82; stroke-width: 2.2; }}
    .kind-theorem rect {{ fill: var(--rose); }}
    .kind-lemma rect {{ fill: var(--green); }}
    .kind-def rect {{ fill: var(--blue); }}
    .kind-abbrev rect {{ fill: var(--violet); }}
    .kind-instance rect {{ fill: var(--gold); }}
    @media (max-width: 980px) {{
      main {{ grid-template-columns: 1fr; }}
      aside {{ position: static; height: auto; border-left: 0; border-top: 1px solid #dde4eb; }}
      header {{ position: static; align-items: flex-start; flex-direction: column; }}
    }}
  </style>
</head>
<body>
  <header>
    <div>
      <h1>Mordell Lean 4 完整蓝图</h1>
      <div class="meta"><span id="counts"></span>。箭头从依赖项指向被依赖项。</div>
    </div>
    <div class="controls">
      <input id="search" type="search" placeholder="搜索声明或文件">
      <select id="kind">
        <option value="">所有声明</option>
        <option value="theorem">theorem</option>
        <option value="lemma">lemma</option>
        <option value="def">def</option>
        <option value="abbrev">abbrev</option>
        <option value="instance">instance</option>
      </select>
      <button id="reset">重置高亮</button>
    </div>
  </header>
  <main>
    <section id="stage">
      <svg id="graph" xmlns="http://www.w3.org/2000/svg" role="img"
        aria-label="Mordell full declaration dependency blueprint"></svg>
    </section>
    <aside>
      <h2 id="detail-title">蓝图概览</h2>
      <div id="detail" class="detail"></div>
    </aside>
  </main>
  <script>
    const DATA = {payload};
    const NODE_W = 196, NODE_H = 38, X_GAP = 54, Y_GAP = 10;
    const TOP = 58, LEFT = 34;
    const colors = new Map();
    const files = DATA.files.map(f => f.file);
    const nodesByFile = new Map(files.map(f => [f, []]));
    DATA.nodes.forEach(n => {{
      if (!nodesByFile.has(n.file)) nodesByFile.set(n.file, []);
      nodesByFile.get(n.file).push(n);
    }});
    const maxRows = Math.max(...Array.from(nodesByFile.values(), a => a.length));
    const width = LEFT * 2 + files.length * NODE_W + Math.max(0, files.length - 1) * X_GAP;
    const height = TOP + maxRows * (NODE_H + Y_GAP) + 92;
    const svg = document.getElementById("graph");
    svg.setAttribute("width", width);
    svg.setAttribute("height", height);
    svg.setAttribute("viewBox", `0 0 ${{width}} ${{height}}`);
    document.getElementById("counts").textContent =
      `${{DATA.node_count}} 个声明节点，${{DATA.edge_count}} 条项目内依赖边，${{DATA.files.length}} 个 Lean 文件`;

    const nodeById = new Map(DATA.nodes.map(n => [n.id, n]));
    const incoming = new Map(DATA.nodes.map(n => [n.id, []]));
    const outgoing = new Map(DATA.nodes.map(n => [n.id, []]));
    DATA.edges.forEach(e => {{
      outgoing.get(e.from)?.push(e.to);
      incoming.get(e.to)?.push(e.from);
    }});

    const positions = new Map();
    files.forEach((file, col) => {{
      const arr = nodesByFile.get(file) || [];
      const x = LEFT + col * (NODE_W + X_GAP);
      const boxH = 44 + arr.length * (NODE_H + Y_GAP);
      svg.insertAdjacentHTML("beforeend",
        `<rect class="file-box" x="${{x - 12}}" y="18" width="${{NODE_W + 24}}" height="${{boxH}}"></rect>` +
        `<text class="file-title" x="${{x}}" y="43">${{escapeHtml(file)}} (${{arr.length}})</text>`);
      arr.forEach((n, row) => {{
        const y = TOP + row * (NODE_H + Y_GAP);
        positions.set(n.id, {{x, y}});
      }});
    }});

    svg.insertAdjacentHTML("beforeend", `<defs>
      <marker id="arrow" markerWidth="10" markerHeight="10" refX="8" refY="3"
        orient="auto" markerUnits="strokeWidth">
        <path d="M0,0 L0,6 L9,3 z" fill="#56616b"></path>
      </marker>
    </defs>`);

    const edgeLayer = document.createElementNS("http://www.w3.org/2000/svg", "g");
    edgeLayer.setAttribute("id", "edges");
    svg.appendChild(edgeLayer);
    for (const e of DATA.edges) {{
      const a = positions.get(e.from), b = positions.get(e.to);
      if (!a || !b) continue;
      const x1 = a.x + NODE_W, y1 = a.y + NODE_H / 2;
      const x2 = b.x, y2 = b.y + NODE_H / 2;
      const dx = Math.max(36, Math.abs(x2 - x1) * 0.42);
      const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
      path.setAttribute("class", "edge");
      path.setAttribute("data-from", e.from);
      path.setAttribute("data-to", e.to);
      path.setAttribute("d", `M ${{x1}} ${{y1}} C ${{x1 + dx}} ${{y1}}, ${{x2 - dx}} ${{y2}}, ${{x2}} ${{y2}}`);
      edgeLayer.appendChild(path);
    }}

    const nodeLayer = document.createElementNS("http://www.w3.org/2000/svg", "g");
    nodeLayer.setAttribute("id", "nodes");
    svg.appendChild(nodeLayer);
    for (const n of DATA.nodes) {{
      const p = positions.get(n.id);
      const g = document.createElementNS("http://www.w3.org/2000/svg", "g");
      g.setAttribute("class", `node kind-${{n.kind}}`);
      g.setAttribute("transform", `translate(${{p.x}},${{p.y}})`);
      g.setAttribute("data-id", n.id);
      g.setAttribute("tabindex", "0");
      const label = n.name.length > 25 ? n.name.slice(0, 22) + "..." : n.name;
      g.innerHTML =
        `<rect width="${{NODE_W}}" height="${{NODE_H}}"></rect>` +
        `<text class="name" x="9" y="16">${{escapeHtml(label)}}</text>` +
        `<text class="sub" x="9" y="31">${{n.kind}} · line ${{n.line}}</text>`;
      g.addEventListener("click", () => selectNode(n.id));
      g.addEventListener("mouseenter", () => previewNode(n.id));
      g.addEventListener("mouseleave", () => clearPreview());
      nodeLayer.appendChild(g);
    }}

    const detailTitle = document.getElementById("detail-title");
    const detail = document.getElementById("detail");
    const search = document.getElementById("search");
    const kind = document.getElementById("kind");
    const reset = document.getElementById("reset");

    function escapeHtml(s) {{
      return String(s).replace(/[&<>"']/g, ch => ({{
        "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
      }}[ch]));
    }}
    function graphNode(id) {{ return svg.querySelector(`.node[data-id="${{CSS.escape(id)}}"]`); }}
    function edgeEls() {{ return Array.from(svg.querySelectorAll(".edge")); }}
    function nodeEls() {{ return Array.from(svg.querySelectorAll(".node")); }}
    function relatedSet(id) {{ return new Set([id, ...(incoming.get(id)||[]), ...(outgoing.get(id)||[])]); }}
    function clearClasses() {{
      nodeEls().forEach(el => el.classList.remove("selected", "dim"));
      edgeEls().forEach(el => el.classList.remove("hot", "dim"));
    }}
    function previewNode(id) {{
      if (svg.querySelector(".node.selected")) return;
      highlight(id, false);
    }}
    function clearPreview() {{
      if (!svg.querySelector(".node.selected")) applyFilter();
    }}
    function highlight(id, selected) {{
      const rel = relatedSet(id);
      nodeEls().forEach(el => {{
        el.classList.toggle("dim", !rel.has(el.dataset.id));
        el.classList.toggle("selected", selected && el.dataset.id === id);
      }});
      edgeEls().forEach(el => {{
        const hot = el.dataset.from === id || el.dataset.to === id;
        el.classList.toggle("hot", hot);
        el.classList.toggle("dim", !hot);
      }});
    }}
    function selectNode(id) {{
      const n = nodeById.get(id);
      highlight(id, true);
      detailTitle.textContent = n.name;
      const deps = (incoming.get(id) || []).map(x => nodeById.get(x)).filter(Boolean);
      const uses = (outgoing.get(id) || []).map(x => nodeById.get(x)).filter(Boolean);
      detail.innerHTML = `
        <div><span class="pill">${{n.kind}}</span><span class="pill">${{escapeHtml(n.file)}}</span><span class="pill">line ${{n.line}}</span></div>
        <p><strong>完整名：</strong><br>${{escapeHtml(n.qualified)}}</p>
        <p><strong>依赖它的声明：</strong><br>${{deps.length ? deps.map(linkLabel).join("<br>") : "无项目内声明"}}</p>
        <p><strong>它直接引用的声明：</strong><br>${{uses.length ? uses.map(linkLabel).join("<br>") : "无项目内声明"}}</p>`;
    }}
    function linkLabel(n) {{
      return `<button style="height:auto;padding:2px 5px;margin:1px 0" onclick="selectNode('${{n.id.replace(/'/g, "\\\\'")}}')">${{escapeHtml(n.name)}}</button>`;
    }}
    function applyFilter() {{
      const q = search.value.trim().toLowerCase();
      const k = kind.value;
      const matched = new Set();
      DATA.nodes.forEach(n => {{
        const text = `${{n.name}} ${{n.qualified}} ${{n.file}}`.toLowerCase();
        if ((!q || text.includes(q)) && (!k || n.kind === k)) matched.add(n.id);
      }});
      nodeEls().forEach(el => el.classList.toggle("dim", !matched.has(el.dataset.id)));
      edgeEls().forEach(el => {{
        const show = matched.has(el.dataset.from) && matched.has(el.dataset.to);
        el.classList.toggle("dim", !show);
      }});
      detailTitle.textContent = "筛选结果";
      detail.innerHTML = `<p>当前匹配 ${{matched.size}} / ${{DATA.node_count}} 个声明。</p>`;
    }}
    search.addEventListener("input", applyFilter);
    kind.addEventListener("change", applyFilter);
    reset.addEventListener("click", () => {{
      search.value = "";
      kind.value = "";
      clearClasses();
      renderOverview();
    }});
    window.selectNode = selectNode;

    function renderOverview() {{
      const byKind = DATA.nodes.reduce((acc, n) => (acc[n.kind] = (acc[n.kind]||0)+1, acc), {{}});
      detailTitle.textContent = "蓝图概览";
      detail.innerHTML =
        `<p>完整蓝图从当前 Lean 源码自动抽取顶层公开声明，并用文本引用关系近似项目内证明依赖。</p>` +
        Object.entries(byKind).map(([k,v]) => `<span class="pill">${{k}}: ${{v}}</span>`).join("") +
        `<p>点击任一节点可查看它的直接上游和下游声明；搜索框可按声明名或文件名筛选。</p>`;
    }}
    renderOverview();
  </script>
</body>
</html>
"""
    (OUT / "mordell_blueprint_full.html").write_text(html_doc, encoding="utf-8")


def svg_text(x: int, y: int, content: str, cls: str = "txt") -> str:
    return f'<text x="{x}" y="{y}" class="{cls}">{html.escape(content)}</text>'


def rect_node(x: int, y: int, w: int, h: int, title: str, lines: list[str], cls: str) -> str:
    parts = [f'<rect x="{x}" y="{y}" width="{w}" height="{h}" class="node {cls}"/>']
    parts.append(svg_text(x + 14, y + 27, title, "node-title"))
    for i, line in enumerate(lines):
        parts.append(svg_text(x + 14, y + 52 + 21 * i, line, "node-line"))
    return "\n".join(parts)


def edge(x1: int, y1: int, x2: int, y2: int, dashed: bool = False) -> str:
    dx = max(44, abs(x2 - x1) // 2)
    cls = "edge dashed" if dashed else "edge"
    return f'<path class="{cls}" d="M{x1} {y1} C{x1 + dx} {y1}, {x2 - dx} {y2}, {x2} {y2}"/>'


def write_simplified_svg(node_count: int, edge_count: int) -> None:
    svg = f"""<svg xmlns="http://www.w3.org/2000/svg" width="1580" height="1160" viewBox="0 0 1580 1160">
  <defs>
    <marker id="arrow" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto" markerUnits="strokeWidth">
      <path d="M0,0 L0,6 L9,3 z" fill="#263238"/>
    </marker>
    <style>
      text {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Noto Sans CJK SC", "Microsoft YaHei", sans-serif; fill: #17212b; }}
      .title {{ font-size: 32px; font-weight: 700; }}
      .subtitle {{ font-size: 16px; fill: #54636f; }}
      .cluster-title {{ font-size: 17px; font-weight: 700; fill: #34414d; }}
      .cluster {{ fill: #f8fafc; stroke: #8a98a3; stroke-width: 1.5; stroke-dasharray: 8 7; rx: 16; }}
      .node {{ stroke: #30404d; stroke-width: 1.25; rx: 9; }}
      .foundation {{ fill: #e0f0ff; }}
      .dedekind {{ fill: #e5f7e6; }}
      .classinput {{ fill: #fff0c7; }}
      .descent {{ fill: #efe9ff; }}
      .final {{ fill: #ffe3e8; }}
      .node-title {{ font-size: 18px; font-weight: 700; }}
      .node-line {{ font-size: 13px; fill: #40505d; }}
      .edge {{ stroke: #263238; stroke-width: 2; fill: none; marker-end: url(#arrow); }}
      .dashed {{ stroke-dasharray: 7 5; stroke: #667782; }}
      .note {{ font-size: 13px; fill: #60717a; }}
    </style>
  </defs>
  <rect x="0" y="0" width="1580" height="1160" fill="#ffffff"/>
  {svg_text(54, 60, "Mordell Lean 4 项目简化蓝图", "title")}
  {svg_text(54, 91, f"从完整声明蓝图（{node_count} 个节点，{edge_count} 条项目内依赖边）中抽取主证明链；箭头从依赖项指向被依赖项。", "subtitle")}

  <rect x="42" y="126" width="265" height="860" class="cluster"/>
  {svg_text(66, 158, "基础代数模型", "cluster-title")}
  {rect_node(72, 190, 205, 96, "ZsqrtdBasic", ["ℤ√d, QuadRat d", "trace / norm / basis"], "foundation")}
  {rect_node(72, 330, 205, 96, "ZomegaBasic", ["ℤ[(1+√d)/2]", "备用二次整数环模型"], "foundation")}
  {rect_node(72, 470, 205, 96, "EuclideanNegTwo", ["ℤ√(-2) 除法算法", "EuclideanDomain 实例"], "foundation")}

  <rect x="352" y="126" width="280" height="860" class="cluster"/>
  {svg_text(376, 158, "Dedekind 与逼近", "cluster-title")}
  {rect_node(390, 210, 205, 104, "Dedekind", ["IsDomain", "IntegralClosure", "IsDedekindDomain"], "dedekind")}
  {rect_node(390, 390, 205, 104, "Approximation", ["有理数取整逼近", "d=-5,-6,-13", "范数估计"], "dedekind")}
  {rect_node(390, 590, 205, 104, "ClassGroupApprox", ["exists_mk0_eq_mk0", "代表元含 2 或 12"], "dedekind")}

  <rect x="680" y="126" width="300" height="860" class="cluster"/>
  {svg_text(704, 158, "小类数输入", "cluster-title")}
  {rect_node(724, 200, 218, 104, "ClassNumber/Common", ["d=-1,-2 类数为 1", "cube-root 特例", "共享理想成员判定"], "classinput")}
  {rect_node(724, 360, 218, 96, "NegFive / NegSix", ["类群至多两个元素", "gcd(classNumber,3)=1"], "classinput")}
  {rect_node(724, 520, 218, 118, "NegThirteen", ["12-约化代表", "类群至多两个元素", "classNumber_gcd_three"], "classinput")}

  <rect x="1028" y="126" width="270" height="860" class="cluster"/>
  {svg_text(1052, 158, "理想下降核心", "cluster-title")}
  {rect_node(1060, 190, 205, 96, "factor_y_sq_sub_d", ["y²-d = (y+√d)(y-√d)", "主理想分解入口"], "descent")}
  {rect_node(1060, 330, 205, 96, "span_y_add_sqrtd_coprime", ["把互素性化为整数", "Bezout 组合"], "descent")}
  {rect_node(1060, 470, 205, 118, "exists_cube_root", ["互素理想 ⇒ 立方理想", "类群消去", "单位是立方"], "descent")}
  {rect_node(1060, 640, 205, 118, "mordell_d", ["系数比较得到 m", "d = -3m² ± 1", "y = m(3d+m²)"], "descent")}

  <rect x="1340" y="126" width="200" height="860" class="cluster"/>
  {svg_text(1364, 158, "最终结论", "cluster-title")}
  {rect_node(1362, 235, 150, 116, "d = -1", ["(x,y)=(1,0)", "solution_iff"], "final")}
  {rect_node(1362, 405, 150, 116, "d = -2", ["(x,y)=(3,±5)", "solution_iff"], "final")}
  {rect_node(1362, 575, 150, 116, "d = -13", ["(x,y)=(17,±70)", "solution_iff"], "final")}
  {rect_node(1362, 755, 150, 116, "d = -5,-6", ["无整数解", "mordell_minus5/6"], "final")}

  {edge(277, 238, 390, 262)}
  {edge(277, 238, 390, 442)}
  {edge(595, 262, 1060, 518)}
  {edge(595, 442, 724, 412)}
  {edge(595, 442, 724, 575)}
  {edge(595, 642, 724, 412)}
  {edge(595, 642, 724, 575)}
  {edge(942, 252, 1060, 518)}
  {edge(942, 412, 1060, 518)}
  {edge(942, 575, 1060, 518)}
  {edge(1265, 238, 1362, 293)}
  {edge(1265, 378, 1362, 293)}
  {edge(1265, 518, 1362, 293)}
  {edge(1265, 699, 1362, 293)}
  {edge(1265, 699, 1362, 463)}
  {edge(1265, 699, 1362, 633)}
  {edge(1265, 699, 1362, 813)}
  {edge(277, 518, 724, 252, True)}
  {edge(277, 518, 1362, 463, True)}

  <rect x="54" y="1030" width="1468" height="76" fill="#fbfcfd" stroke="#d4dbe0" stroke-width="1.2" rx="12"/>
  {svg_text(78, 1060, "说明：简化图保留论文叙述中的主结果依赖；完整交互图 mordell_blueprint_full.html 包含全部公开顶层声明，可按文件、声明类型和名称筛选。", "note")}
  {svg_text(78, 1084, "ClassNumber 目前拆分为 Common / NegFive / NegSix / NegThirteen 四个文件；图中把 -5 和 -6 合并为同一类小类数输入。", "note")}
</svg>
"""
    (OUT / "mordell_blueprint_simplified.svg").write_text(svg, encoding="utf-8")


def write_paper_simplified_svg() -> None:
    """Create a caption-free crop for LaTeX figures.

    The full simplified SVG has a standalone title and explanatory footer.
    The thesis already supplies those through the LaTeX caption, so this
    variant crops to the graph body only.
    """
    svg = (OUT / "mordell_blueprint_simplified.svg").read_text(encoding="utf-8")
    svg = svg.replace(
        '<svg xmlns="http://www.w3.org/2000/svg" width="1580" height="1160" viewBox="0 0 1580 1160">',
        '<svg xmlns="http://www.w3.org/2000/svg" width="1580" height="935" viewBox="30 110 1520 900">',
        1,
    )
    (OUT / "mordell_blueprint_simplified_paper.svg").write_text(svg, encoding="utf-8")


def write_pngs_if_possible() -> None:
    sips = shutil.which("sips")
    if not sips:
        return
    for stem in ["mordell_blueprint_simplified", "mordell_blueprint_simplified_paper"]:
        subprocess.run(
            [
                sips,
                "-s",
                "format",
                "png",
                str(OUT / f"{stem}.svg"),
                "--out",
                str(OUT / f"{stem}.png"),
            ],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )


def write_readme(data: dict) -> None:
    text = f"""# Mordell Blueprints

本目录包含 Mordell Lean 4 项目的两个蓝图版本：

- `mordell_blueprint_simplified.svg`：论文中使用的简化依赖图，保留主证明链和最终结论。
- `mordell_blueprint_simplified_paper.svg` 和 `.png`：去掉图内标题和说明后的论文插图版本。
- `mordell_blueprint_full.html`：完整交互式声明蓝图，包含 {data["node_count"]} 个公开顶层声明节点和 {data["edge_count"]} 条项目内依赖边。
- `mordell_blueprint_full.json`：完整蓝图的数据源，便于后续检查或重新绘图。

可用于论文正文的表述：

> Mordell 形式化分布在 12 个 Lean 源文件中。图 X 给出了主要结果的依赖关系图，该图是从完整蓝图（包含 {data["node_count"]} 个公开顶层声明节点）中简化而来。完整交互式蓝图见项目文档中的 `mordell_blueprint_full.html`。

论文插图可使用已经复制到 `Paper/论文/正式论文/figures/` 的无标题 PNG：

```tex
\\begin{{figure}}[htbp]
  \\centering
  \\includegraphics[width=0.95\\textwidth]{{mordell_blueprint_simplified_paper.png}}
  \\caption{{Mordell 形式化依赖关系的简化蓝图。方框表示 Lean 声明或声明组；虚线轮廓按证明层次分组。箭头从依赖项指向被依赖项。}}
  \\label{{fig:mordell-blueprint-simplified}}
\\end{{figure}}
```

重新生成：

```bash
python3 Proj/Mordell/docs/generate_blueprints.py
```

完整图中的依赖边由源码中的项目内声明文本引用自动抽取，用作工程蓝图和导航图；严格证明正确性仍以 Lean kernel 和 `lake build` 为准。
"""
    (OUT / "README.md").write_text(text, encoding="utf-8")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    decls = project_decls()
    edges = dependency_edges(decls)
    data = full_graph_data(decls, edges)
    write_json(data)
    write_full_html(data)
    write_simplified_svg(data["node_count"], data["edge_count"])
    write_paper_simplified_svg()
    write_pngs_if_possible()
    write_readme(data)
    print(
        f"generated {data['node_count']} nodes and {data['edge_count']} edges in {OUT.relative_to(ROOT)}"
    )


if __name__ == "__main__":
    main()
