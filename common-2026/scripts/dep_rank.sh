#!/usr/bin/env bash
#
# scripts/dep_rank.sh — entry point 限定の依存数ランキング。
#
# `@[entry_point]` でマークされた declaration を対象に、推移的依存数の多い順
# (= より複雑・難解な定理の順) に上位 N 件を出力する。実体は scripts/DepGraph.lean。
# 800+ entry point を走査するため初回は 1〜2 分かかる。
#
set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/dep_rank.sh [N] [options]

  N                    上位何件を表示するか (default: 20)

options:
  --by-total           合計 (内部+外部) でソート【default】
  --by-internal        プロジェクト内の依存数でソート (自前補題の積み上げの厚み)
  --by-external        外部 (Mathlib 等) の依存数でソート
  --with-type          型シグネチャの依存も依存数に含める (default: 証明本体のみ)
  --max-depth <n>      内部依存の展開深さ上限 (default: 無制限)
  --raw                auto-gen 補助定義も畳まず依存数に数える
  -h, --help           このヘルプ

依存数 = その entry point を起点に推移的に到達する declaration 数
         (root 自身を除く / プロジェクト内は再帰展開・外部 (Mathlib 等) は葉)。
依存数が多い定理ほど複雑・難解という想定のランキング。
internal / external でソートすると複雑さの意味が変わる:
  internal = プロジェクト内でどれだけ自前の補題を積んだか
  external = どれだけ多くの Mathlib 等の外部資産に依存しているか

例:
  scripts/dep_rank.sh                    # 上位 20 (合計)
  scripts/dep_rank.sh 30 --by-internal   # 内部依存の多い順 上位 30
  scripts/dep_rank.sh 10 --by-external --with-type
EOF
}

TOP=20
export DEP_WITH_TYPE="" DEP_RAW="" DEP_MAX_DEPTH="" DEP_SORT="total"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --by-total)     export DEP_SORT=total; shift;;
    --by-internal)  export DEP_SORT=internal; shift;;
    --by-external)  export DEP_SORT=external; shift;;
    --with-type)    export DEP_WITH_TYPE=1; shift;;
    --raw)          export DEP_RAW=1; shift;;
    --max-depth)    export DEP_MAX_DEPTH="$2"; shift 2;;
    -h|--help)      usage; exit 0;;
    -*)             echo "unknown option: $1" >&2; usage; exit 1;;
    *)              TOP="$1"; shift;;
  esac
done

if ! [[ "$TOP" =~ ^[0-9]+$ ]]; then
  echo "N は非負整数で指定してください: $TOP" >&2; exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ="$(dirname "$SCRIPT_DIR")"
cd "$PROJ"

export DEP_RANK=1 DEP_TOP="$TOP" DEP_SORT
lake env lean scripts/DepGraph.lean
