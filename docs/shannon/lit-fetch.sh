#!/usr/bin/env bash
# BC 未解決本体 (T3 / T3b / T3c) の一次文献を取得し、`pdftotext -layout` の出力を 1 か所に揃える。
#
# ⚠ 抽出テキストは scratchpad (= 本スクリプトの出力先) に置き、repo にはコミットしない。
#    リポジトリは public なので、残してよいのは「取得コマンド」だけである。
# ⚠ 本スクリプトは CLAUDE.md `## Scratchpad` の運用に対応する — scratchpad は消えるので、
#    後の leg が読むもの (= 取得手順) だけを `docs/shannon/` 側に置く。
#
# stem と URL は `docs/shannon/bc-facts.md` から逐語で写したものである
# (`## L0 (T3)` / `## L1 (T3)` / `## L2 (T3)` / `## L3 (T3)` / `## L7 (T3)` 各節の取得元と、
#  台帳内の `curl -sL … pdftotext -layout` を含む行)。
# ⚠ 台帳の逐語引用の行番号は、すべて `pdftotext -layout` 出力に対する実測値である
#    ⟹ stem 名と `-layout` オプションを変えると行番号が合わなくなる。
#
# 使い方:
#   docs/shannon/lit-fetch.sh [出力先]        # 既定は ${SCRATCH:-/tmp}/lit
#   SCRATCH=/path/to/scratchpad docs/shannon/lit-fetch.sh
#   docs/shannon/lit-fetch.sh /tmp/lit auxrec probc   # stem を指定するとその分だけ取る

set -euo pipefail

OUT="${1:-${SCRATCH:-/tmp}/lit}"
shift || true
mkdir -p "$OUT"

# stem<TAB>URL。⚠ 順序は台帳での初出順 (L0 → L1 → L2 → L3 → L7 → L10/L13/L15–L18)。
read -r -d '' DOCS <<'LIST' || true
n13	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/conceve-spr.pdf
li21	https://arxiv.org/pdf/2108.07324
sct	https://arxiv.org/pdf/2210.08309
bsp	https://arxiv.org/pdf/2101.09754
probc	http://chandra.ie.cuhk.edu.hk/pub/papers/BC/proBC.pdf
auxrec	https://chandra.ie.cuhk.edu.hk/pub/papers/NIT/Auxiliary-Receiver.pdf
BC-it07	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/BC-it07.pdf
locten	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/loc-ten-bin.pdf
sumofbc	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/sumofBC.pdf
egk4	https://arxiv.org/pdf/1001.3404v4
cpt	https://arxiv.org/pdf/1701.08402
GK-outer	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/GK-outer.pdf
2104.05634	https://arxiv.org/pdf/2104.05634
2004.08783	https://arxiv.org/pdf/2004.08783
ga09	https://arxiv.org/pdf/0904.4541v3
gea11	https://arxiv.org/pdf/1006.5166v2
gna12	https://arxiv.org/pdf/1202.0898v1
jn09	https://arxiv.org/pdf/0901.1492
ggny	https://arxiv.org/pdf/1105.5438
nwg10	https://arxiv.org/pdf/1001.1468
inineq	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/inineq.pdf
itw16	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/ITW-16.pdf
twoclass	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/twoclass-full.pdf
mp	https://arxiv.org/pdf/1609.06877
concenve	http://chandra.ie.cuhk.edu.hk/pub/papers/manuscripts/concenve.pdf
marcon	https://chandra.ie.cuhk.edu.hk/pub/papers/BC/Mar-Con.pdf
LIST

# ⚠ stem 名の注意 (台帳の逐語):
#   egk4  — `v4` を明示指定すること。`v5` は書籍への案内 1 枚に差し替わっており本文が無い。
#   probc — 著者サイト版 24pp。arXiv 版は同じ論文の別稿 (stem `ggny` = 1105.5438) で行番号が違う。
#   gjnw  — 台帳は stem `gjnw` = Nair–Wang–Geng とだけ書き、URL を記録していない。
#           ジャーナル版と思われる `inineq` を別 stem で取ってあるが、⚠ 同定は未確認である。
#   dou24 — PDF ではなく HTML なので下の別ブロックで取る。
#   0901.0595 / 2606.12839 — 台帳が novelty gate の掃引対象として id だけ挙げており、
#           `$LIT/<stem>.txt` を引く claim 行が無いので本スクリプトには入れていない。

fetch_pdf() {
  local stem="$1" url="$2"
  if [ -s "$OUT/$stem.txt" ]; then
    echo "skip  $stem (already fetched)"
    return 0
  fi
  echo "fetch $stem  <- $url"
  curl -sL "$url" -o "$OUT/$stem.pdf" && pdftotext -layout "$OUT/$stem.pdf" "$OUT/$stem.txt"
}

wanted=("$@")
while IFS=$'\t' read -r stem url; do
  [ -n "${stem:-}" ] || continue
  if [ ${#wanted[@]} -gt 0 ]; then
    case " ${wanted[*]} " in *" $stem "*) ;; *) continue ;; esac
  fi
  fetch_pdf "$stem" "$url" || echo "FAIL  $stem"
done <<< "$DOCS"

# [Dou24] だけは PDF が無く HTML なので、タグを落として本文を取る
# (`## L0 (T3)` の再検証コマンドから逐語)。⚠ User-Agent を付けないと弾かれる。
if [ ${#wanted[@]} -eq 0 ] || case " ${wanted[*]} " in *" dou24 "*) true ;; *) false ;; esac; then
  if [ ! -s "$OUT/dou24.txt" ]; then
    echo "fetch dou24 <- https://pmc.ncbi.nlm.nih.gov/articles/PMC10969477/"
    curl -sL "https://pmc.ncbi.nlm.nih.gov/articles/PMC10969477/" \
      -A "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36" \
      -o "$OUT/dou24.html" \
    && OUT="$OUT" python3 -c "
import re, html, os
out = os.environ['OUT']
s = open(os.path.join(out, 'dou24.html'), encoding='utf-8').read()
s = re.sub(r'(?is)<(script|style|nav|header|footer)[^>]*>.*?</\1>', ' ', s)
s = re.sub(r'(?is)<br\s*/?>', '\n', s)
s = re.sub(r'(?is)</(p|div|h[1-6]|li|tr|section)>', '\n', s)
s = re.sub(r'(?s)<[^>]+>', ' ', s)
s = html.unescape(s)
s = re.sub(r'[ \t]+', ' ', s)
s = re.sub(r'\n\s*\n+', '\n', s)
open(os.path.join(out, 'dou24.txt'), 'w', encoding='utf-8').write(s)
" || echo "FAIL  dou24"
  else
    echo "skip  dou24 (already fetched)"
  fi
fi

echo
echo "out: $OUT"
ls -1 "$OUT"/*.txt 2>/dev/null | sed 's/^/  /' || echo "  (nothing fetched)"
