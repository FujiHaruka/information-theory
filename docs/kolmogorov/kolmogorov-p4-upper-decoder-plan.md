# Ch.14 Kolmogorov P4 上界: type-class decoder crux 実装サブ計画

> **Parent**: [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md) §Phase P4 (上界節)

**Status**: ✅ COMPLETE (2026-07-24) — **flagship `kolmogorov_entropy_rate` 完全 proof-done・sorryAx-free・
無条件** (`EntropyRate.lean:1036`、`#print axioms` = `[propext, Classical.choice, Quot.sound]`、
load-bearing hyp なし)。上界 crux (method-of-types decoder) の再アーキ R1–R4 が全 landed し、per-string 上界
#5/#6 → 積分組立 #7 → flagship 上界が閉じ、既 proof-done の下界と squeeze。両ゲート PASS。
残は **flag-only cosmetic のみ** (下 §follow-up、proof-done 非阻害)。

## 進捗 (全 landed)

- [x] D0–D2 — 旧 candidate B 列挙器骨格 (列挙・filter・index の Primrec 合成)。旧 decoder はレート無効判明も骨格は R2 に流用。
- [x] **R1 — `encodeBlock` base-card mixed-radix 再設計** (`94b8b1f6`)。`encodeBlock_injective` 再証明 +
  `encodeBlock_lt` (`< card α^m`) + `encodeBlock_eq_ofDigits` (R2 matching 用橋)。sorryAx-free。
- [x] **R2 — decoder div/mod packing + base-card 出力** (`7a529ce8`)。`Nat.pair` 全廃 (2 倍化解消)、
  `typeDecoder_partrec : Partrec₂` 再証明。sorryAx-free。
- [x] **R3 — bit-length utility `natLen_le_of_lt_two_pow`** + length-bound 補題を `UniversalMachine.lean`
  (natLen 定義元 = DAG leaf) へ再配置 (`167a62f4`)。sorryAx-free。
- [x] **R4 — #5/#6 closure ⟹ flagship 完全 proof-done** (R4a=#6 `70f02e93` / R4b+R4c=#5→flagship
  sorryAx-free `2e0d7138`)。honesty-auditor all-OK (proof-done 独立検証、`@audit:ok` 付与) + style-auditor PASS。

**建てた helper 群** (再導出可、すべて `EntropyRate.lean` 在、詳細は git が持つ): `ofDigits_inj` /
`exists_typeDecoder_witness` (matching) / `filter_typeSig_length_le` (型クラス card 上界) /
`framing_overhead_eventually` (K + b_const + `|T_c|+1` の O(log n) overhead を n·δ に吸収) 等。

## ゴール / Approach (達成済)

decoder を **n を入力に取る単一 `Partrec₂` code** として建てる (per-n 別 code は加法定数 b 発散で o(n) 崩壊)。
block を dependent 型族 `Fin n → α` でなく **length-n 値 `List α`** として扱い (candidate B)、Mathlib `Primrec`
list API に as-is で載せた。上界は #5 `condComplexity_block_typical_le` (典型 per-string 上界、`invariance` +
matching 補題 `encodeBlock n b ∈ typeDecoder m n` + 型クラス濃度 index 上界 + `entropyByCount` 会計) と #6
`condComplexity_block_uniform_le` (literal echo + `encodeBlock_lt` + `natLen_le_of_lt_two_pow`) の 2 本に分解し、
#7 積分組立で flagship 上界に合流させて下界と squeeze した。

## 教訓 (facts 台帳候補、human-judgment)

Kolmogorov decoder を「usable asset」と認める前に **rate/length-budget チェック**を課す。`Partrec₂` /
`Computable` 認証は length-efficiency と直交し、`Nat.pair` packing / nested-pair encoding は computable でも
長さが 2 倍〜指数的に膨らむ (旧 decoder `20bdeaa3` は達成レート `2H/log2` で破綻 → R1–R2 で base-card encoding +
div/mod packing に再設計)。plan/inventory/proof-pivot-advisor が旧 #4 を「proof-done」と祝ったのは `Partrec₂`
としては正しいが、その認証は target rate 達成を保証しない。

## follow-up (flag-only、任意、proof-done 非阻害)

- flagship の未使用 `[DecidableEq α]` 除去 (blast radius 未確認)。
- 内部補助補題 ~10 件の docstring 除去 (bare 化、`docs/rules/docstrings.md`)。
- `exists_typeDecoder_witness` の "witness" naming 見直し。

## 撤退ライン (frozen slug `kolmogorov-p4-upper-decoder`、未発動)

closure 達成につき R-DEC (decoder 発散時の上界 bank) は未発動のまま。slug はコード側 `@residual` と一致する
frozen 参照として register に history として残す (他文書参照ありうるので凍結)。
