# Ch.14 Kolmogorov P4 上界: type-class decoder crux 実装サブ計画

> **Parent**: [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md) §Phase P4 (上界節)

**Status**: OPEN (2026-07-20) — 未着手。flagship `kolmogorov_entropy_rate` の残り最後の 1 本
`kolmogorov_entropy_rate_upper` (`EntropyRate.lean:99`、`@residual(plan:kolmogorov-p4-upper)`) を閉じる
method-of-types 分解のうち、唯一の Phase-U 級 crux = **helper #4 `typeDecoderPartrec`** (decoder 構成 +
`Partrec₂` 認証) の closure plan。#1-#3/#5-#7 は親 §Phase P4 上界節が持つ (Proposal-B tier)。

## Context

上界 = **method of types**。「exp(nH+o(n)) サイズの computable 集合を index して符号化」を原理的に要し、
型クラス `T_n(c) := { x : Fin n → α | ∀ a, typeCount x a = c a }` が唯一自然な候補 (組合せ的 = 有理・実数
不要ゆえ computable)。program = `⟨型記述子 c⟩ ++ ⟨index i⟩` を `invariance` (`Invariance.lean:53`) に食わせ、
長さ `q.length ≈ |α|·log n + n·entropyByCount(c)` を得る。

**crux (#4) の本質 = decoder の computability 認証**。`invariance_code (c : Code)` の加法定数
`b = encodeCode c + 2` は c にのみ依存する ⟹ decoder は **n を入力に取り n について uniform な単一 code**
でなければならない (n ごとに別 code を建てると b が n と共に発散し、上界 rate の o(n) 項が崩壊する)。
∴ decoder `A(m, n)`: `m` を `(型記述子 c : α→ℕ, index i)` に unpair → `n` と `c` から
`T_n(c)` を canonical 順で列挙 → `i` 番目の block を `encodeBlock n` して返す、を **単一 `Partrec₂` code** として
建てる。重い核 = **n 依存 dependent 型族 `Fin n → α` 上の decidable subset 列挙を n について uniform に
`Partrec₂` 認証**する部分。

**class = `plan`、NOT a Mathlib wall**。method-of-types family
(`Sanov/`・`TypeClassLowerBound.lean`・`StrongTypicality.lean`) 全体に `Partrec`/`Computable` 参照は
**0 件**、Mathlib に `Computable` × `List.filter` は **loogle Found 0** (下 §settled facts)。⟹ decoder は
既存資産で 1 行も軽くならない genuine real work。**しかし全有限・decidable ゆえ原理 computable = 「選択 (big)」で
あって「壁 (hard)」ではない**。`@residual(wall:…)` は打たない。撤退口は
`sorry + @residual(plan:kolmogorov-p4-upper-decoder)` (詰まったら親の粗い bank `kolmogorov-p4-upper` へ)。

## 進捗

- [ ] D0 — decoder 専用 Mathlib 在庫確認 (Primrec list API + 表現形の選択) 📋
- [ ] D1 — gateway atom: `typeDecoder` def + `Partrec₂` probe (make-or-break) 📋
- [ ] D2 — 列挙器 total-computability の build-out (filter/nth chain 全認証) 📋
- [ ] D3 — 出力整形: `A` を `invariance` 署名に噛み合わせる (`encodeBlock` 合成) 📋

## ゴール / Approach

### Goal

helper #4 `typeDecoderPartrec` を proof-done sorryAx-free 化する:

```lean
-- 署名は D1 で verbatim 確定 (invariance が消費する `A : ℕ → ℕ → Part ℕ` 形に合わせる)
noncomputable def typeDecoder : ℕ → ℕ → Part ℕ := ...
theorem typeDecoderPartrec : Partrec₂ typeDecoder := ...
```

これが通れば #5 (`condComplexity_block_le` = #4 を `invariance` に食わせ per-string 上界) が直線的に続き、
#6 (atypical 吸収) / #7 (積分組立) と合流して `kolmogorov_entropy_rate_upper` が閉じる。撤退口は
`sorry + @residual(plan:kolmogorov-p4-upper-decoder)` のみ。**核を `IsTypeDecodableHypothesis` 等の
load-bearing predicate に畳んで #5 に「decoder は computable と仮定して」渡すのは禁止 (tier 5、
CLAUDE.md「検証の誠実性」)**。

### Approach — uniform-in-n single code + 表現形の選択 (solution shape)

decoder は **n を入力に取る単一 `Partrec₂` code** として建てる (per-n 別 code は b 発散で崩壊、上記 Context)。
全体の流れは以下の 3 段:

1. **unpair**: `m` を `Nat.unpair` で `(型記述子, index i)` に分解。型記述子は `c : α → ℕ` を有限個の ℕ
   (`Fintype.card α` 個) に符号化した ℕ (`α ≃ Fin (card α)` 経由の tuple ⟷ ℕ)。`Nat.unpair` / `Primrec` の
   pairing は Mathlib 完備ゆえ計算量認証は機械的。
2. **enumerate**: `n` と `c` から `T_n(c)` を canonical 順で列挙し `i` 番目を取り出す。**ここが crux**。
3. **encode**: 取り出した block を `encodeBlock n` (`EntropyRate.lean:48`) して返す。

**設計上の最重要判断 = block の内部表現形 (Mathlib-shape-driven)**。crux #2 の重さは
「n 依存 dependent 型族 `Fin n → α` を uniform-in-n で `Primcodable`/`Primrec` に載せる」sticking point に
集約される。2 つの first-move 候補を D1 gateway で機械比較し、Mathlib `Primrec` list API に最も繋ぎやすい方を採る:

- **候補 A (Finset framing)**: `(Finset.univ : Finset (Fin n → α)).toList` を `Encodable` 順に取り
  `List.filter (fun x ↦ decide (typeCount x = c))` して `i` 番目。sticking point = **uniform-in-n
  `Primcodable (Fin n → α)`** (n が型に現れるため、n を走る単一 code で `Primcodable` instance を供給する部分が
  非自明)。
- **候補 B (List 表現)**: block を `Fin n → α` でなく **長さ n の `List α`** として扱う。`List α` は `α` が
  `Primcodable` なら uniform-in-n で `Primcodable` (n は値、型に現れない) ⟹ 列挙は length-n の `List α`
  candidate を生成 → `List.filter (型カウント = c)` → `i` 番目。`encodeBlock` との橋 (`List α ⟷ Fin n → α`) は
  1 本の bijection 補題で吸収。**Mathlib の `Primrec`/`Computable` list API (filter/nth/length) が値レベルの
  `List` に as-is で当たる**ため、candidate B が sticking point を型から値へ落とせる公算が高い (D1 で確認)。

**判断**: candidate B を primary の first-move とし、gateway atom で `Partrec₂` が通るか probe する。通れば
候補 A は不要。詰まれば候補 A ないし別表現へ pivot (D1 判断ログに記録)。**「型 `Fin n → α` を計算対象にしない」
= textbook 形の直訳を避けて Mathlib 出口形 (値 `List`) に定義を合わせる**、が Approach の背骨。

## Phase 詳細

各 step: 依存 / 成果物 (署名略式) / 見積行数 / proof-log / 撤退ライン。位置は着手時 `sig_view --sorry` で都度確認。

### D0 — decoder 専用 Mathlib 在庫確認 📋

- **依存**: なし (independent inventory phase、着手前 mandatory)。
- **成果物** (per-lemma、`file:line` + verbatim 署名 + `[...]` 前提):
  - `Nat.unpair` / `Nat.pair` の `Primrec` 認証 (`Mathlib/Computability/Primrec.lean`)。
  - `List.filter` / `List.get?`(`nth`) / `List.length` の `Computable`/`Primrec` API の有無と署名 (**候補 B の要**)。
  - `Primcodable (List α)` の uniform-in-n 性 (n が値である確認)、対して `Primcodable (Fin n → α)` の
    型パラメータ n 依存 (**候補 A の sticking point の裏取り**)。
  - `Partrec₂` の定義形 (`invariance` が要求する `A : ℕ → ℕ → Part ℕ` に対する具体 obligation)。
- **見積行数**: 0 (調査、docs へ per-lemma 台帳を追記 or 親 inventory に追補)。
- **proof-log**: no (調査 Phase)。
- **撤退ライン**: なし。

### D1 — gateway atom: `typeDecoder` def + `Partrec₂` probe (make-or-break) 📋

- **依存**: D0。**make-or-break** — ここが通れば #5-#7 は直線的、詰まれば定義形 (表現) を再設計。
- **成果物**: candidate B (length-n `List α` 表現) で `typeDecoder : ℕ → ℕ → Part ℕ` を建て、`Partrec₂` を
  `Computable`/`Primrec` の合成補題で証明。列挙 = 「length-n `List α` の candidate 生成 → `List.filter`
  (型カウント = c) → `i` 番目 → `encodeBlock` 相当」を値レベルで組む。
- **見積行数**: 80–200 行 (crux の主費用、`Partrec₂` の合成認証)。ファイル `EntropyRateUpper.lean` (新規、
  分割方針は親 §ファイル構成)。
- **proof-log**: **yes** (crux gateway、method-of-types decoder computability の build 根拠)。
- **撤退ライン**: candidate B で `Partrec₂` が通らず候補 A も 300 行級に発散 → **R-DEC 発動** (下 §撤退ライン)。
  退避口は `sorry + @residual(plan:kolmogorov-p4-upper-decoder)`。**computability を仮説で受ける bundling は禁止**。

### D2 — 列挙器 total-computability の build-out 📋

- **依存**: D1 (framing 確定後)。
- **成果物**: D1 gateway で `Partrec₂` の骨格が通った後、列挙器の各 leaf (candidate 生成 / filter 述語の
  decidability / nth 境界) を全 sorry-free 化。列挙が `T_n(c)` への全単射 (canonical 順、index の well-defined 性)
  であることの補題も含む — **これが #5 の index-length 会計 (`i < |T_n(c)| ≤ exp(n·entropyByCount)`) の前提**。
- **見積行数**: 40–120 行 (D1 の残 leaf 充填)。
- **proof-log**: yes (D1 と連続、build 根拠)。
- **撤退ライン**: D1 と共倒れ時のみ R-DEC。

### D3 — 出力整形: `invariance` 署名への噛み合わせ 📋

- **依存**: D2 + `invariance` (`Invariance.lean:53`、read-only 消費)。
- **成果物**: `typeDecoder` が `encodeBlock n block ∈ typeDecoder (Nat.pair ⟨c⟩ i) n` を満たすことを確認し、
  `invariance typeDecoder typeDecoderPartrec` を instantiate して #5 `condComplexity_block_le` に渡せる形に整える。
  署名の verbatim 一致 (第 1 引数 = `decodeNat q`、第 2 引数 = `y = n`) を確認 (`invariance` の
  `x ∈ A (decodeNat q) y` 規約を崩さない)。
- **見積行数**: 20–40 行 (機械寄り、#5 との境界確認が主)。
- **proof-log**: no。
- **撤退ライン**: なし (D2 まで通れば機械的)。

## gateway atom (make-or-break、最初に 1 本通す)

**D1 = 型クラス列挙器 `typeDecoder : ℕ → ℕ → Part ℕ` を建て `Partrec₂` を通せるか。** 最初に 1 本
`lean-implementer` に投げ、以下を確認する:

1. **(probe)** candidate B (length-n `List α` 表現) で列挙器を組み、Mathlib `Primrec`/`Computable` list API
   (`List.filter`/`nth`/`length`) を uniform-in-n で合成して `Partrec₂` が通るか。sticking point =
   candidate B が sticking point を「型 `Fin n → α`」から「値 `List α`」へ落とせるか。
2. 詰まれば candidate A (Finset framing) を試し、`Primcodable (Fin n → α)` の uniform-in-n 供給が
   単一 code で成立するか確認。
3. **判定**: どちらかで `Partrec₂` の骨格が通れば #5-#7 は既存資産で直線的 ⟹ 上界 closure が視界に入る。
   両方詰まれば R-DEC 発動 (上界全体を bank)。gateway leg で machine 検証 (`lake env lean` +
   `#print axioms`) を行い、settled fact 候補を facts 台帳に確定させる。

## 撤退ライン (frozen slug `kolmogorov-p4-upper-decoder`)

退避口は **`sorry` + `@residual(plan:kolmogorov-p4-upper-decoder)`** のみ。**decoder の computability を
`IsTypeDecodableHypothesis` / `IsPartrecClaim` 等の load-bearing predicate に畳んで #5 に「computable と仮定して」
渡すのは禁止 (tier 5 = honesty defect、CLAUDE.md「検証の誠実性」)**。全有限・decidable ゆえ原理 computable = 選択
(big) であり壁 (hard) ではないため、`@residual(wall:…)` も打たない。

- **R-DEC — decoder 発散時の上界 bank** (frozen slug `kolmogorov-p4-upper-decoder`)
  - **発動条件**: candidate B / A の双方で `typeDecoder` の `Partrec₂` 認証が **300 行を超えて発散**する。
  - **退避形**: #4 の skeleton (`typeDecoder` def + `typeDecoderPartrec : Partrec₂ typeDecoder := by sorry`) を
    撤去し、`kolmogorov_entropy_rate_upper` (`EntropyRate.lean:99`) を **上界全体 1 本の**
    `sorry + @residual(plan:kolmogorov-p4-upper)` (親の粗い bank) に据え置く。
  - **flagship の帰結**: `kolmogorov_entropy_rate` は「**下界 proof-done + 上界 banked**」の honest 部分勝利。
    lower (`kolmogorov_entropy_rate_lower`、proof-done sorryAx-free @audit:ok) は無影響。

## settled facts

CLAUDE.md「Don't cache settled facts」に従い、壁断定は本計画に散文で持たない。以下を **facts 台帳候補**
(`docs/kolmogorov/kolmogorov-facts.md`、confidence = `loogle-neg` (rg 二段確認済)) とし、D0 leg で確定させる:

- **claim**: method-of-types family (`Sanov/MultinomialLowerBound.lean`・`TypeClassLowerBound.lean`・
  `StrongTypicality.lean`) に `Partrec`/`Computable` 参照は 0 件 ⟹ decoder は既存資産で軽くならない。
  Mathlib に `Computable` × `List.filter` の橋は不在 (loogle Found 0)。
- **含意**: これは Mathlib 壁 **ではない** (全有限・decidable ⟹ 原理 computable = 選択 big)。∴ 途中 sorry は
  `@residual(plan:kolmogorov-p4-upper-decoder)`、`@residual(wall:…)` は打たない。第 1 波背骨に壁 residual は無い
  (唯一の genuine 壁は第 2 波 prefix 塔、slug は親 §Out が保持)。
- **代替アーキテクチャ全却下** (method-of-types + computable decoder が唯一): naive 典型集合 index は μ 実数閾値で
  非 computable / 全ブロック列挙は rate `log₂|α|` で H 未達 / 数え上げ逆用は下界しか出ない (infimum 上界化は
  witness 必須) / n ごと別 code は b 発散。上界は「exp(nH+o(n)) サイズの computable 集合を index」が原理必要で、
  型クラス (組合せ的) が自然な候補。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

1. **表現形 pivot (Approach の背骨、active)**: block を dependent 型族 `Fin n → α` でなく **length-n 値
   `List α`** として扱う (candidate B) を primary first-move とする。crux の sticking point は
   「n 依存 `Primcodable (Fin n → α)` を uniform-in-n で供給」に集約されるため、n を型から値へ落とせば Mathlib
   `Primrec` list API が as-is で当たる公算。D1 gateway で機械確認し、通れば candidate A (Finset framing) は不要。
2. **uniform-in-n single code の必然性 (active、決定的)**: `invariance_code` の加法定数 `b = encodeCode c + 2`
   は c にのみ依存するため、decoder は n を入力に取る単一 code でなければならない。per-n 別 code は b が n と共に
   発散し上界 rate の o(n) 項が崩壊する ⟹ decoder を「n を第 2 引数に取る `Partrec₂`」として建てる制約は
   crux の設計を規定する不動点 (settled)。
