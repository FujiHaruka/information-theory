#!/usr/bin/env bash
#
# scripts/dep_consumers.sh — 共有補題の「consumer (逆依存) グラフ」を逆引きする。
#
# 指定した declaration (共有補題など) を *直接参照している* InformationTheory 内の
# decl を file:line 付きで列挙する。dep_graph.sh (forward: root が何に依存するか) の
# 逆向きで、「この補題を誰が消費しているか」を引く。
#
# 用途: 共有補題の signature を変更 (仮説 threading 等) する前に、影響範囲
# (ripple = touch が要る decl 群) を 1 度で洗い出し、初回 brief に正確な consumer
# list を載せる。--transitive で推移的 consumer 閉包 (full blast radius) も併記。
# 実体は scripts/DepGraph.lean。
#
set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/dep_consumers.sh <TargetDecl> [options]

  <TargetDecl>         逆引きする declaration の完全修飾名 (共有補題など)
                       例: InformationTheory.Shannon.integrable_negMulLog_map_condTrunc_sum

  デフォルトは direct consumers (target を直接参照する decl) を file:line 付きで列挙する。
  signature 変更時に「直接 touch が要る decl」がこれ。ripple を漏らさないため、逆引きは
  証明本体に加え型シグネチャ参照も含める。

options:
  --transitive         direct consumers を推移的に消費する全 decl (full blast radius) も併記
  -h, --help           このヘルプ

direct consumers   = target を直接参照する decl (= signature 変更で直接 touch が要る)
transitive closure = それらを推移的に消費する全 decl (= 壊れうる full blast radius)

例:
  scripts/dep_consumers.sh InformationTheory.Shannon.integrable_negMulLog_map_condTrunc_sum
  scripts/dep_consumers.sh InformationTheory.Foo.sharedLemma --transitive
EOF
}

TARGET=""
export DEP_TRANSITIVE=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --transitive)  export DEP_TRANSITIVE=1; shift;;
    -h|--help)     usage; exit 0;;
    -*)            echo "unknown option: $1" >&2; usage; exit 1;;
    *)             if [[ -z "$TARGET" ]]; then TARGET="$1"; else
                     echo "extra positional arg: $1" >&2; exit 1; fi; shift;;
  esac
done

if [[ -z "$TARGET" ]]; then usage; exit 1; fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ="$(dirname "$SCRIPT_DIR")"
cd "$PROJ"

export DEP_CONSUMERS="$TARGET"
lake env lean scripts/DepGraph.lean
