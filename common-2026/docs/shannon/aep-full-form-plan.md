# AEP 完全形 (D-3) ムーンショット計画 🌙

> **シード由来**: `docs/moonshot-seeds.md` §D.D-3 (audit-2026-05 §4 🟡 #4)
> Cover-Thomas Theorem 3.1.2 **完全 3 点セット** — 既存 `typicalSet_prob_le` (上界のみ)
> に下界 + サイズ下界を補完し、Cover-Thomas (1)〜(4) の全 4 帰結を publish。
>
> 実態整合 (2026-05-20): DONE-HONEST-HYPS — 両 headline 完成済。
> `typicalSet_prob_ge` (`InformationTheory/Shannon/AEP.lean:1403`、点別下界 `exp(-n(H+ε)) ≤ p(x)`)、
> `typicalSet_card_ge` (AEP.lean:1492、`(1-η)·exp(n(H-ε)) ≤ |T|`)、
> `typicalSet_card_ge_eventually` (AEP.lean:1554) いずれも 0 sorry、
> 仮定は `iIndepFun` / `IdentDistrib` / `hpos` の i.i.d. 標準形のみ (pass-through なし)。

## 進捗

- [x] Phase 0 — 起草: 既存 `AEP.lean` 末尾の構造を把握 ✅ (2026-05-13)
- [x] Phase 1 — 点別下界 `typicalSet_prob_ge` ✅ (AEP.lean:1403)
- [x] Phase 2 — サイズ下界 `typicalSet_card_ge` ✅ (AEP.lean:1492、`_eventually` 形 :1554 も)
- [x] Phase 3 — full support 仮定の見直し ✅ (`hpos` で統一)

## ゴール / Approach

**最終目標** (Cover-Thomas Theorem 3.1.2): 任意 `ε > 0` で十分大きい `n` に対し
1. `x ∈ T_ε^n ⟹ exp(-n(H+ε)) ≤ p(x) ≤ exp(-n(H-ε))` (両側点別)
2. `Pr[T_ε^n] → 1` ✅ (既 `typicalSet_prob_tendsto_one`)
3. `|T_ε^n| ≤ exp(n(H+ε))` ✅ (既 `typicalSet_card_le`)
4. `|T_ε^n| ≥ (1-η)·exp(n(H-ε))` for `μ(T_ε^n) ≥ 1-η`

**未充足**: (1) の **下側点別下界** + (4) のサイズ下界。
**戦略**: (1) は `typicalSet_prob_le` の方向反転 (鏡像)、(4) は (2) + (3) のサンドイッチで合成。

### Approach

`typicalSet_prob_le` (上界、AEP.lean:1279-1387) と完全対称な構造で `typicalSet_prob_ge`
を立てる:
- 仮定: 同じ `iIndepFun + IdentDistrib + hpos`
- typical set 定義から `(∑ pmfLog) / n - H < ε` (上側) を取り出す
- `(∑ pmfLog) < n(H+ε)` → `-(∑ pmfLog) > -n(H+ε)` → `exp(-(∑ pmfLog)) > exp(-n(H+ε))`
- `exp(-(∑ pmfLog)) = ∏ P(x_i) = p(x)` で結論

`typicalSet_card_ge` は確率質量の保存則 `μ(T) ≤ |T|·max_{x∈T} p(x)` (上界の点別形)
+ `typicalSet_prob_tendsto_one` で n が十分大きいときに `μ(T) ≥ 1 - η` を取り、
**任意の `η > 0`** に対する size 下界 `|T| ≥ (1-η)·exp(n(H-ε))` を導出。

新規ファイルではなく既存 `InformationTheory/Shannon/AEP.lean` 末尾に追加 (Phase G として既存
`typicalSet_prob_le` と並立)。

## Phase 0 — 既存資産の棚卸し ✅

- `typicalSet` (AEP.lean:229–232): `{x | |(∑ pmfLog (x i)) / n - H| < ε}`
- `typicalSet_card_le` (AEP.lean:257–368): 上界 `|T| ≤ exp(n(H+ε))`
- `typicalSet_prob_tendsto_one` (AEP.lean:375–438): `μ(T) → 1`
- `typicalSet_prob_le` (AEP.lean:1279–1387): 点別上界 `p(x) ≤ exp(-n(H-ε))`
- 共通仮定: `iIndepFun`, `IdentDistrib (Xs i) (Xs 0)`, `hpos : ∀ x, 0 < P.real {x}`

## Phase 1 — 点別下界 `typicalSet_prob_ge` 📋

`typicalSet_prob_le` の対形。**LSB ⟺ -ε < (∑ pmfLog) / n - H** の側を使う。

- [ ] step 1: typical set からの不等式抽出: `(abs_lt.mp hx).2` で `(∑ pmfLog)/n - H < ε`
- [ ] step 2: 線形変形 `(∑ pmfLog) < n(H+ε)`、続いて `-(∑ pmfLog) > -n(H+ε)`
- [ ] step 3: `Real.exp_lt_exp.mpr` で `exp(-(∑ pmfLog)) > exp(-n(H+ε))`
- [ ] step 4: `exp(-(∑ pmfLog)) = ∏ P(x_i)` (既存補題 `hexp_pmfLog` のコピー)
- [ ] step 5: `(μ.map (jointRV Xs n)).real {x} = ∏ P(x_i)` (既存補題と同形 `hreal`)
- [ ] step 6: 結論 `exp(-n(H+ε)) ≤ p(x)` (strict → non-strict)

n = 0 ケースは `prob_le` と同じ trivial 化 (空積 = 1 ≥ exp 0)。

**見積**: ~80 行 (`typicalSet_prob_le` 109 行のほぼ鏡像、署名・boilerplate 共有)。

## Phase 2 — サイズ下界 `typicalSet_card_ge` 📋

「点別上界 × 確率質量保存」のサンドイッチ。

```
1 - η ≤ μ(T_ε^n) = (μ.map (jointRV Xs n))(T)
                  = ∑_{x ∈ T} p(x)
                  ≤ |T| · max_{x ∈ T} p(x)
                  ≤ |T| · exp(-n(H-ε))    -- by typicalSet_prob_le
```
⟹ `|T| ≥ (1-η) · exp(n(H-ε))`

- [ ] step 1: signature: `∀ ε > 0, ∀ η ∈ (0, 1), ∃ N, ∀ n ≥ N, ...`
  または直接 `μ(T) ≥ 1-η` 仮定を受ける形 (eventually-large-n 形を呼び出し側で取る)
- [ ] step 2: `(μ.map (jointRV Xs n)).real T = ∑_{x ∈ T} p(x)` を `measureReal_eq_sum_of_finite`
  または直接の finite-sum 展開で
- [ ] step 3: `∑_{x ∈ T} p(x) ≤ ∑_{x ∈ T} exp(-n(H-ε)) = |T| · exp(-n(H-ε))` を
  `Finset.sum_le_sum (typicalSet_prob_le ...)` で
- [ ] step 4: 移項 `|T| ≥ (μ(T)) / exp(-n(H-ε)) = μ(T) · exp(n(H-ε))`
- [ ] step 5 (optional): `eventually μ(T) ≥ 1-η` を `typicalSet_prob_tendsto_one` から取り、
  `∃ N` 形に bundle

**設計選択**: API 形は **`μ(T) ≥ 1-η` を仮定として受ける版**を主形にする (use side が
`typicalSet_prob_tendsto_one` を呼ぶ責任を持つ)。eventually-N 版は corollary。

**見積**: ~60 行 (本体 ~40 + corollary ~20)。

## Phase 3 — full support 仮定の見直し 📋

シードでは「`hpos : 0 < P.real {x}` 不要なはず」とあるが、現行 `typicalSet_prob_le` は
`Real.exp_log (hP_pos a)` で `hpos` を本質的に使う。除去候補:

- **Option A** (skip): `hpos` を維持し、Phase 3 は scope outside (D-3 完了判定は Phase 1+2)
- **Option B** (吸収): support 内のみで評価 (`P(a) = 0 → x_i = a` は a.s. 起こらない)。
  ただし statement 形が変わる (`a.s.-quantified`)。
- **Option C** (`log 0 = 0` 規約): `exp(0) = 1 ≠ 0` で形式的に上界/下界が破綻するため不可。

**判断**: D-3 一次目標は Phase 1+2。Phase 3 は **scope deferred** (本 plan では試行のみ、
吸収可なら採用、不可なら `hpos` 維持の判断ログ)。

## 判断ログ

1. **新規ファイル vs AEP.lean 末尾**: 既存 `typicalSet_prob_le` (Phase G, AEP.lean 末尾) と
   完全対称形のため AEP.lean に追加。新規ファイル化は cross-module dependency が増えるだけで
   downstream に利点なし。

2. **「(1-ε) · exp(-n(H+ε))」シード文言の解釈**: シード本文は per-set 形に読めるが
   Cover-Thomas 3.1.2 (1) は per-point 形が標準。本 plan では **per-point 下界 +
   per-set サイズ下界**の 2 本立てに分解 (Cover-Thomas (1) と (4) を独立に publish)。

3. **API 形**: `typicalSet_card_ge` は「`μ(T) ≥ 1-η` を仮定」形を主、`eventually` 形は
   corollary。理由: use side で `tendsto → eventually` の引き出しは標準パターン、主形を
   eventually にすると不要な `∃ N` が混入する。
