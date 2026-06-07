#!/usr/bin/env bash
#
# scripts/dep_graph.sh — 定理の依存グラフを Graphviz dot 形式で生成する。
#
# 起点 declaration の証明・型に現れる定数参照を辿り、推移的な依存グラフを出力する。
# プロジェクト内 (InformationTheory.*) の定理は再帰展開し、外部依存 (Mathlib 等) は
# 葉ノードとして含める (中身は追わない)。実体は scripts/DepGraph.lean。
#
set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/dep_graph.sh <RootDecl> [options]

  <RootDecl>           起点となる定理 / 定義の完全修飾名
                       例: InformationTheory.Shannon.differentialEntropy_dirac

options:
  -o, --output <file>  出力 dot ファイル (default: dep_graph.dot)
  --proof-only         証明本体 (value) のみ追う。型シグネチャの依存
                       (型クラスインスタンス等) を除外してノイズを減らす
  --max-depth <n>      内部依存の展開深さ上限 (default: 無制限)
  --raw                auto-gen 補助定義 (_proof_/match_/recOn/projection 等) も
                       畳まずノード化する (default: 畳んで非表示)
  --svg                Graphviz があれば <output>.svg も生成
  --png                Graphviz があれば <output>.png も生成
  -h, --help           このヘルプ

例:
  scripts/dep_graph.sh InformationTheory.Shannon.differentialEntropy_dirac
  scripts/dep_graph.sh My.Thm --proof-only -o thm.dot --svg

出力された dot は Graphviz で画像化できます:
  dot -Tsvg dep_graph.dot -o dep_graph.svg
EOF
}

ROOT=""
OUT="dep_graph.dot"
RENDER=""   # svg / png
export DEP_PROOF_ONLY="" DEP_RAW="" DEP_MAX_DEPTH=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -o|--output)   OUT="$2"; shift 2;;
    --proof-only)  export DEP_PROOF_ONLY=1; shift;;
    --raw)         export DEP_RAW=1; shift;;
    --max-depth)   export DEP_MAX_DEPTH="$2"; shift 2;;
    --svg)         RENDER="svg"; shift;;
    --png)         RENDER="png"; shift;;
    -h|--help)     usage; exit 0;;
    -*)            echo "unknown option: $1" >&2; usage; exit 1;;
    *)             if [[ -z "$ROOT" ]]; then ROOT="$1"; else
                     echo "extra positional arg: $1" >&2; exit 1; fi; shift;;
  esac
done

if [[ -z "$ROOT" ]]; then usage; exit 1; fi

# project root = このスクリプトの 1 つ上の階層
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ="$(dirname "$SCRIPT_DIR")"
cd "$PROJ"

export DEP_ROOT="$ROOT"
export DEP_OUT="$OUT"

lake env lean scripts/DepGraph.lean

if [[ -n "$RENDER" ]]; then
  if command -v dot >/dev/null 2>&1; then
    RENDER_OUT="${OUT%.dot}.${RENDER}"
    dot -T"$RENDER" "$OUT" -o "$RENDER_OUT"
    echo "[dep_graph] wrote $RENDER_OUT"
  else
    echo "[dep_graph] Graphviz (dot) が見つかりません。--$RENDER をスキップしました。" >&2
    echo "            brew install graphviz で導入できます。" >&2
  fi
fi
