# Shannon-Hartley operational capacity closure ムーンショット計画 🌙

**Status**: 🎉 **achievability 半分 CLOSED（2026-07-18、leg 22）**。
`contAwgn_ge_shannonHartley`（`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`）=
**PROOF-DONE sorryAx-free + @audit:ok**（`ShannonHartleyMain.lean`、commits `15a111ef` / `ef401a5d` / `173adcb3`）。
hyp 全 regularity（`0<W` / `0<N₀` / `0≤P`）。**残るは converse 半分のみ** — `contAwgn_eq_shannonHartley` の残 sorry。
**leg 23（`c5822fed`/`73ec6559`）: converse の唯一の壁候補 C1（interlacing count domination）= CLOSED** ⟹ 残 sorry を
`@residual(nyquist-2w-dof)` → **`@residual(plan:shannon-hartley-phase2-spectral-plan)`** へ再分類（監査 CONFIRMED、live wall residual 0）。残 converse = C0/C2/C3/C4（project-internal、C3 = 最大 self-build）。

**leg 22 の def-fix（honesty-critical、監査 all OK で intent-preserving 確認済）**: `contAwgnOperationalCapacity` を
bounded binder `⨅ ε ∈ Set.Ioo 0 1` → **subtype infimum `⨅ ε : ↥(Set.Ioo 0 1)`** へ。旧 bounded-binder は
conditionally-complete `ℝ` 上で `ε ∉ (0,1)` の phantom 項が `sInf ∅ = 0` を拾い cap を無条件 `= 0` に潰していた
（`contAwgnRate ≥ 0`）⟹ 旧 `contAwgn_ge` / `contAwgn_eq` は **P>0 で false-as-framed だった**（壁 gated ではなく定義バグ）。
subtype は nonempty ゆえ genuine infimum = docstring intent。**偽装でない判別子 PASS**: converse 壁は無傷。
詳細 → 子 plan §⨅-binder hazard / 台帳 §BIINF-PHANTOM。

**背景（履歴）**: 3 宣言はかつて 2 度 false-as-framed だった — leg 12（`encoder_power` の窓のみ拘束、
`cause:signature-drops-constraint`）→ 子 Leg P（Karhunen-Loève def-fix、`4fd8a47c`）で解消、leg 22（phantom biInf）→
上記 def-fix で解消。**Legs A/B/C/C' の作用素資産（`TimeBandLimiting.lean`）は有効**（破棄しない）。

**壁核は解析的に CLOSED**（台帳 §SPECTRAL-ASSETS が SoT）: 固有値集中の名指す命題（第 2 モーメント `tr A−tr A²`）+
カウント両半分 `prolateCount_le` / `le_prolateCount`（`c` 自由・`D` 明示、sorryAx-free）+ achievability bridge が
全て closed。**残 sorry（`eq`）は count の下流 = converse bridge（C0–C4）**。**C1（interlacing count domination）= CLOSED
（leg 23、`finrank_le_prolateCount_of_form_gt` proof-done @audit:ok）** — crux は Leg E で既に in-tree ゆえ純線形代数。
`nyquist-2w-dof` → `plan:` 再分類済（監査 CONFIRMED）。**壁論拠は 4 度誤っていた**（C1 の advisor 見立ても含め、子 plan「完了 leg」節）。
詳細な obligation 表 + 次アクション → 子 plan「R4-CONV」節が SoT。stretch（Phase 4/5-full）不変。honesty bar 不変
（CLAUDE.md「検証の誠実性」）。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §Ch.9 Shannon-Hartley（Ch.9.6）
> **子 plan**: [`shannon-hartley-phase2-spectral-plan.md`](shannon-hartley-phase2-spectral-plan.md)（壁核 + achievability bridge + converse track、SoT）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)（sampling = CLOSED）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（per-sample coding theorem = `awgn_achievability` / `awgn_converse` / `awgn_channel_coding_theorem`）
> **Facts ledger**: [`shannon-hartley-facts.md`](shannon-hartley-facts.md)（machine 裏付けは code の `#print axioms` を SoT とし prose にキャッシュしない）

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅（commit 8bf07545）
- [x] Phase 1-fix — faithful band-limit + continuous-codeword redesign ✅（commit 7c3afc86、独立 audit PASS）
      ← Phase 1（operational infra、7e354045）/ Phase 5-min（wire、b8770fce）を統合
- [x] l2Fourier bridge（fwd+inv）+ bandlimited_sup_bound ✅ proof-done・audit PASS（9d8608a8/40c2e449/30b59a15）
- [x] **Phase 3 — achievability closure（`contAwgn_ge_shannonHartley`）✅ CLOSED（leg 22、proof-done sorryAx-free + @audit:ok）**。
      leg 1（synthSignal、`89ede2a3`）→ 子 Leg P（def-fix）→ 子 Leg D'（BddAbove、Bessel 単独）→ R4-ACH bridge（L0–L10、leg 18–22）。commits `15a111ef`/`ef401a5d`/`173adcb3`
- [~] **Phase 2 — prolate-DOF スペクトル理論** 🔄 **[解析核・カウント・achievability bridge・converse C1 interlacing = 全 CLOSED（leg 16–23）]** → [shannon-hartley-phase2-spectral-plan.md](shannon-hartley-phase2-spectral-plan.md)
- [~] Phase 4 — converse（`contAwgn_le_shannonHartley`、Phase 2 消費）🔄 **[C1 interlacing = CLOSED（leg 23）。C3 = FULLY CLOSED（leg 24/25）。C2 gateway atoms + count-domination（`gram_high_eigen_finrank_le_prolateCount` + real wrapper）+ per-coord C3 headline（`contAwgn_operational_converse_percoord`）= CLOSED + @audit:ok（leg 26、`ShannonHartleyConverseCount.lean` 新設、Mathlib Gram/eigendecomp 消費で self-build なし）。残 = C2 rotation/ellipsoid（obs 第2モーメント↔νᵢQᵢ）/ C4 water-filling+二重極限 / C0 headline / assembly、全 project-internal・壁なし・fresh-judgment]**
- [ ] Phase 5-full — `le_antisymm` 組立（`contAwgn_eq_shannonHartley` の wall-sorry 除去）📋 **[stretch / closure]**

## ゴール / Approach

### Goal（最終達成状態）

**達成済（leg 22）**: `contAwgn_ge_shannonHartley`（achievability `≥`）= proof-done sorryAx-free + @audit:ok。
`contAwgn_eq_shannonHartley`（`@[entry_point]`）は def-fix 後 **true-as-framed** な honest 単一 wall-sorry
（`@residual(nyquist-2w-dof)`、**converse 半分専用**）。
⚠️ **訂正（leg 22）**: 旧文「Phase 1-fix で true-as-framed に復帰」は不完全だった — capacity def が phantom biInf を
抱え **false-as-framed だった**（`contAwgnRate ≥ 0` ゆえ cap が `0` に潰れる）。leg 22 の subtype-infimum def-fix 後に
初めて true-as-framed。`IsTwoWDegreesOfFreedom` load-bearing predicate 除去（`ShannonHartley.lean` から消滅済）も有効。

**stretch（残）**: converse `contAwgn_le_shannonHartley`（C0–C4）を証明し `le_antisymm` で `contAwgn_eq` の wall-sorry を
除去 → 0-sorry（`@audit:ok`）。真の壁候補は converse の **C1 interlacing** 単一に縮約済。honesty bar 不変
（genuine に建て、真に詰まる sub-wall のみ honest `sorry + @residual`。load-bearing hyp / 循環 def / `:True` slot は禁止）。

### Approach（解の全体形 = 戦略）

Shannon-Hartley の operational 版 = **サンドイッチ**:
`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`（achievability, Phase 3 ✅）
`∧ contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity`（converse, Phase 4）→ `le_antisymm`（Phase 5-full）。

戦略の要は **2W という次元定数を def に埋めず、証明の 2 方向から emerge させる**（`2W` / `⌊2WT⌋` を def に含めない
= 非循環設計 C1–C4、下記「設計制約」）:

- **achievability（≥）✅ CLOSED**: 真間隔サンプリング → `awgn_channel_coding_theorem`（既所有 genuine）→
  synthesis bridge（有限サンプルベクトルを補間する帯域制限信号を構成）→ R4-ACH bridge（L0–L10、子 plan）。
  **crude 両側カウント `prolateCount T W c / T → 2W` だけで足り、tight LPS 集中を要さない**（当初「固有値カウントを
  下から読む = 壁」と読んだが実際は不要と leg 22 で判明）。
- **converse（≤）は prolate-DOF 上界が本質**: 受信信号を上位 `≈2WT` prolate 固有関数へ射影 → 有効次元を
  `prolateCount` で上から抑え（**C1 = 唯一の壁候補、interlacing**）→ `awgn_converse` / `parallel_per_input_mi_le_sum`
  （既所有 genuine）+ 次元カウント。**新しい壁はゼロ**（C1 は Mathlib 0-hit だが count + 有限 V-固有基底から導出可能な公算）。

したがって **真の壁候補は converse 側の C1 interlacing 単一に縮約**。Phase 1 周辺インフラと Phase 3 achievability は
壁でない（proof-done 済）。

### route（DAG 選択 + 次アクション）

**C1 gateway = PASS（leg 23）**: interlacing count domination `finrank_le_prolateCount_of_form_gt` proof-done @audit:ok、
crux は Leg E で既に in-tree ⟹ `nyquist-2w-dof` → `plan:` 再分類済（監査 CONFIRMED）。
**C3 = FULLY CLOSED（leg 24 骨格 + leg 25 L5）**: 新 file `ShannonHartleyConverse.lean`、`contAwgn_operational_converse`（`log M ≤ ∑½log(1+P'ᵢ/(N₀/2)) + Fano`）無条件 sorryAx-free + 全 6 leaf @audit:ok（`parallel_per_input_mi_le_sum` + `shannon_converse_single_shot` + `mutualInfo_le_of_markov` 消費、L5 = 離散 AWGN converse への genuine reduction）。
**次アクション = C2（Gauss 回転、Mathlib 在）+ C4（water-filling+極限、初等）→ C0 headline → Phase 4 → Phase 5-full（`le_antisymm`）**。詳細 → 子 plan「R4-CONV」節が SoT。

---

## 設計制約 — 循環罠 #2 回避（非循環設計の受入基準・SoT）

proof-pivot-advisor 名指しの循環罠: **連続時間 code を「長さ `⌊2WT⌋` のサンプルベクトルに制限」して定義してはならない**
（converse の DOF 限界を def に埋め込む循環で、還元定理が `rfl` 化し証明が空になる）。**受入基準 C1–C4**（全 Phase の
「循環チェック」欄で再照合）:

1. **C1 — codeword 空間**: codeword は `[0,T]` 上の任意の帯域制限 `[-W,W]` 信号。固定長サンプルベクトルへの制限は禁止。
   → `ContAwgnCode.encoder : Fin M → (ℝ → ℝ)`（関数）✓。
2. **C2 — capacity primitive**: `contAwgnOperationalCapacity` に次元定数 `2W` / `⌊2WT⌋` を一切含まない
   （leg 22 の subtype-infimum def-fix でも維持）✓。
3. **C3 — 2W の出所**: `2W` / `⌊2WT⌋` は achievability（サンプリング rate 選択）と converse（prolate 次元カウント）の
   **両側から emerge** する。どの def の入力にも現れない ✓。
4. **C4 — 雑音 / サンプル数**: 雑音は per-sample iid Gaussian、テスト関数数 `k` は自由 `ℕ`。定義段で固定しない ✓。

**違反の兆候（tell）**: `contAwgn_eq_shannonHartley` の証明が `rfl` / `unfold` のみで済む、def に `⌊2WT⌋` が出る、
reduction が per-sample capacity をそのまま返す、**`contAwgn_eq` が壁なしで閉じる**（def-fix 特有の tell）。

---

## Phase 0 / 1-fix — 完了（履歴は git）

- **Phase 0**（commit 8bf07545）: Mathlib + InformationTheory API 在庫、各 Phase feasibility + mainline GO 判定 +
  prolate = genuine 壁核の裏取り。
- **Phase 1 / 5-min → Phase 1-fix に統合**（旧 7e354045 / b8770fce は当初 def が degenerate/under-specified で
  FALSIFIED）。C2 primitive 形 + 非循環設計 C1–C4 + 雑音 route β（per-sample iid Gaussian を `errorProbAt` に inline）は
  継承・有効。`IsTwoWDegreesOfFreedom` load-bearing predicate 除去 + Option A README honesty infra は再利用資産。
- **Phase 1-fix**（commit 7c3afc86、独立 audit PASS）: `IsBandlimited` を L²-Fourier スペクトル台で再定義
  （degenerate L¹-`𝓕` junk-0 解消）+ `ContAwgnCode` に regularity field（pointwise-vs-a.e. gap 解消）。
  bridge `l2Fourier_eq_fourierIntegral`（L¹∩L² 上一致、壁でない）は既存資産で closure 済（台帳 §「Mathlib の L²
  Fourier」節が SoT: in-project に既存だった）。**この着地は「命題が偽である」ことを覆さなかった** — leg 12 / leg 22 の
  2 度の false-as-framed はこの後に発見・修理された（子 plan / 台帳）。

---

## Phase 2 — prolate-DOF スペクトル理論 🔄 **[解析核・カウント・achievability bridge = CLOSED、残 = converse C1]**

> **サブ計画**: [`shannon-hartley-phase2-spectral-plan.md`](shannon-hartley-phase2-spectral-plan.md)（SoT）
> **子 plan の 2 負債は両方とも解消済**（leg 22）: (1) def-fix（観測写像 Karhunen-Loève + capacity phantom biInf）✅、
> (2) 壁核 self-build（固有値集中の解析核 + カウント両半分）✅。**残る唯一の未着手 = converse bridge の C1 interlacing。**

**主要資産（`TimeBandLimiting.lean`、全 sorryAx-free、詳細は子 plan「完了 leg」表 + 台帳 §SPECTRAL-ASSETS）**:
`timeBandLimitingOp T W`（自己共役・コンパクト・`‖A‖≤1`）/ `prolateEigenvalues`（降順列挙 framework）/
第 2 モーメント `tsum_inner_sub_norm_sq_timeBandLimitingOp_le`（= `tr A−tr A² ≤ 2+log(1+2WT)`、壁の解析核）/
カウント両半分 `prolateCount_le` + `le_prolateCount`（`c` 自由・`D` 明示 = converse `c→0` と achievability `c→1` の両方が引ける強度）。

**循環チェック**: 本 Phase は def でなく作用素の解析。C3（`2WT` は固有値カウントの**結論**として現れ、
`prolateEigenvalues` / `timeBandLimitingOp` の def の入力ではない ✓）。
**retreat line**: 残 obligation（converse C0–C4）に壁タグを付けてよいものは無い（名指す命題は closed）— 詰まったら
`@residual(plan:shannon-hartley-phase2-spectral-plan)`。**slug 自体は retire しない**（consumer 1 本 `eq` が未 unblock、
C1 PASS で `plan:` へ）。load-bearing hyp / `*Hypothesis` predicate 化は禁止。

---

## Phase 3 — achievability closure ✅ **[CLOSED、leg 22]**

**着地**: `contAwgn_ge_shannonHartley`（`ShannonHartleyMain.lean`）= PROOF-DONE sorryAx-free + @audit:ok
（commits `15a111ef` / `ef401a5d` / `173adcb3`）。hyp 全 regularity。

構成（詳細は子 plan「R4-ACH」節が SoT）: leg 1（synthSignal band-limit/energy、`89ede2a3`、exact sinc isometry
`∫_ℝ f² = Δ·∑aᵢ²`）→ 子 Leg P（Karhunen-Loève def-fix）→ 子 Leg D'（BddAbove、Bessel 単独・壁非依存、`fb18b681`）→
R4-ACH bridge（L0–L10、leg 18–22: pre-equalizer `b=A⁻¹x` / testFn 族 / cross-map `√c` 下界 / `awgn_channel_coding_theorem`
へ transport + rate/limsup + `⨅ε→c↑1`）。

**判定が 3 度振れた軸の決着（記録）**: 2026-07-15「achievability は壁を共有する」→ leg 12「撤回、偽の命題を壁と読んだ」→
leg 14「def-fix 後は共有する（`bddAbove` は共有しない）」→ **leg 22「共有しなかった」**。実際に要したのは crude 両側
カウント `prolateCount T W c / T → 2W` だけで tight LPS を要さず、bridge で proof-done。**leg 12 の撤回は当時の（偽の）def
に対しては正しかった**（偽の命題に壁も何もない）— def が変わったので命題も変わった。
**循環チェック**: サンプリング rate 選択は achievability 側の**構成選択**であり def の入力でない（C3 ✓）。
`contAwgnMaxMessages` を `⌊2WT⌋` サンプルに制限せず、その値以上のメッセージ数を**達成できる**と示すだけ（C1/C2 ✓）。

---

## Phase 4 — converse 📋 **[stretch、残作業の実体]**

**目的**: `contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity`。詳細 obligation 表（C0–C4）+ 資産の在処 →
子 plan「R4-CONV」節が SoT。

```lean
theorem contAwgn_le_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P := ⟨サンドイッチの ≤ 方向⟩
```

**構成（子 plan の C0–C4）**: C0（headline `contAwgn_le` を実不等式として書き下ろす、指示対象なき名前の解消）→
**C1（Gram 固有値 interlacing `#{ν>c} ≤ prolateCount T W c` = 唯一の未 gateway-test、Mathlib 0-hit だが count +
有限 V-固有基底から導出可能な公算）**→ C2（等方 Gauss 回転、`map_pi_eq_stdGaussian` = Mathlib にある）→
C3（不等利得 operational converse、`parallel_per_input_mi_le_sum` = secretly in-tree、最大項）→ C4（water-filling + 極限）。
**⚠️ `ParallelGaussian` の 0-sorry 面は capacity 側（MI の `sSup`）だが consumer は operational 側（メッセージ数の `sSup`）**
= operational な parallel-Gaussian converse は存在しない = 残量の主駆動要因。

**循環チェック（最重要）**: C3 — `⌊2WT⌋` は Phase 2 固有値カウントの**結論**として converse に入り、capacity def からは
来ない ✓。受信信号を射影で次元還元するのは**証明ステップ**であり code def の制限でない（C1 維持。code をサンプル
ベクトルに制限した瞬間に循環化する — 射影は受信側の解析、codeword 空間は `encoder : Fin M → (ℝ → ℝ)` のまま）。
**⚠️ 未検証仮説（仮定してはならない）**: 「`√(T/n)` tight-frame ⟹ 有効ランク `≈2WT`」は C1 の**内容そのもの**で、
その前に仮定すると循環（子 plan 判断ログ / 台帳 §OBSERVATION-MAP 攻撃 1）。
**retreat line**: 詰まったら `@residual(plan:shannon-hartley-phase2-spectral-plan)`（名指す命題は closed ゆえ壁タグ不可）。
load-bearing hyp / `BddAbove` の hyp 化 / 射影の hyp 化は禁止。

---

## Phase 5-full — le_antisymm 組立 📋 **[stretch / closure]**

**目的**: Phase 3 `≥`（proof-done）+ Phase 4 `≤` の `le_antisymm` で `contAwgn_eq_shannonHartley` の wall-sorry を除去。
proof-log: no（wiring、小規模、概算 30–80 行）。

```lean
theorem contAwgn_eq_shannonHartley ... :=
  le_antisymm (contAwgn_le_shannonHartley ...) (contAwgn_ge_shannonHartley ...)
```

**中間状態**: Phase 4 が sorry なら `contAwgn_eq` は `≤` 経由で `@residual(nyquist-2w-dof)` を継承（`≥` は既に genuine）。
**循環チェック**: 組立後の `contAwgn_eq` が genuine 等号（`rfl` でない、Phase 3/4 の実証明を経由）であることを確認。
**受入基準**: `contAwgn_eq_shannonHartley` 0 sorry / 0 residual、`@audit:ok`（= closure）。

---

## Sub-wall map

| Phase | residual | 位置づけ |
|---|---|---|
| Phase 2（prolate 固有値集中） | ~~`nyquist-2w-dof`~~ **名指す命題は closed（leg 16–17）** | 固有値集中の解析核 + カウント両半分が sorryAx-free。**残渣は count の下流 = converse bridge の C1 interlacing**。詰まったら `@residual(plan:shannon-hartley-phase2-spectral-plan)` |
| Phase 3（achievability） | **なし ✅ CLOSED（leg 22）** | `contAwgn_ge_shannonHartley` = proof-done sorryAx-free + @audit:ok |
| Phase 4（converse） | `nyquist-2w-dof`（C1 gateway 未 → PASS で `plan:` 再分類） | consumer 1 本（`contAwgn_eq`:64）が未 unblock。C1 = 唯一の未 gateway-test |
| Phase 5-full | Phase 4 transitive 継承 | Phase 4 の `contAwgn_le` を継承。独自の新 sorry は作らない |

**register 整合**: `nyquist-2w-dof` は `docs/audit/audit-tags.md` Wall name register に既存（consumer 反映は実装 owner 担当、
本 plan は prose に壁事実をキャッシュしない）。**C1 gateway PASS で名指す命題が下流 plumbing と確定したら
`wall:` → `plan:` へ再分類**（コードタグが SoT）。各 node: 詰まったら honest `sorry + @residual`、load-bearing hyp /
循環 def / `:True` slot は全 Phase 禁止（CLAUDE.md）。

---

## 依存 DAG / ripple

```
[DONE] Phase 0 ─► 1-fix ✅ ─► Phase 3 leg 1 ✅ ─► 子 Leg P (def-fix) ✅ ─► 子 Leg D' (BddAbove) ✅
                                                                              │
        子 Leg E (LPS 解析核) ✅ ─► count R2/R3 ✅ ─► R4-ACH bridge L0–L10 ✅ ─► Phase 3 ✅ (contAwgn_ge, proof-done)
                                                                              │
   [NEXT] 子 R4-CONV: C1 interlacing (🚦 唯一の未 gateway-test) ─► C0/C2/C3/C4 ─► Phase 4 (contAwgn_le) ─► Phase 5-full (le_antisymm ─► contAwgn_eq)
                          ▲
                          └─ Legs A/B/C/C' ✅ (作用素資産) + 有限 V-固有基底 (in-tree)
```

- **mainline（現在地）**: achievability 半分は proof-done（`contAwgn_ge_shannonHartley`）。**残るは converse 半分**。
- **next**: 子 plan の **C1 gateway-atom-first probe**（interlacing atom を dispatch）→ PASS で壁 → `plan:` 再分類 +
  C0/C2/C3/C4（全 plumbing）→ Phase 4 → Phase 5-full。
- **ripple**: `IsTwoWDegreesOfFreedom` 削除は完了済で有効。entry-point 2 本は最下流 sink `ShannonHartleyMain.lean` へ
  relocation 済（leg 21、`2f9b4ec6`、import cycle なし）。残作業（C0–C4）は既存 sorry を落とす + 新 headline `contAwgn_le`
  を建てるのみで既存 consumer の署名不変。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ残す（≤ 10 entry）。

1. **achievability CLOSED、converse が唯一の未着手（active、leg 22）**: `contAwgn_ge_shannonHartley` = proof-done
   sorryAx-free + @audit:ok。残 sorry（`contAwgn_eq`:64）は converse 専用に縮約（live consumer 2→1）。
   次 = 子 plan の C1 gateway-atom-first probe → PASS で `nyquist-2w-dof` → `plan:` 再分類。子 plan が SoT。
2. **capacity 定義の phantom biInf を修理（active、leg 22、台帳 §BIINF-PHANTOM が SoT）**: bounded binder
   `⨅ ε ∈ Ioo 0 1` が `sInf ∅ = 0` を拾い cap を `0` に潰し `ge`/`eq` を false-as-framed にしていた（壁 gated でなく
   定義バグ）。subtype infimum で修理、監査 all OK（intent-preserving + converse 壁無傷）。**旧「Phase 1-fix で
   true-as-framed」は不完全**だった（Goal 節の訂正）。gateway probe が観測写像を検査しても binder 意味論の縮退は直交軸。
3. **真の壁候補は converse 側の C1 interlacing 単一（active）**: 固有値集中の名指す命題 + カウント + achievability bridge
   が全て閉じても consumer の sorry（`eq`）は落ちない。残るは C1（Mathlib 0-hit だが count + 有限 V-固有基底から
   導出可能な公算）= 未 gateway-test。**def-fix 後も壁が converse に残る**ことが、def-fix が「壁の偽装」でない判別子。
4. **`√(T/n)` tight-frame ⟹ 有効ランク `≈2WT` は C1 の内容そのもの（active）**: 正規化の**実在**は verbatim 確認済だが、
   「Gram ≈ I / 有効ランクが `sampleCount` に依らない」は C1 interlacing で証明すべき当の量で、C1 の前に**仮定してはならない**
   （Phase 4 循環チェックに警告）。BddAbove の正当化には使わない（部分空間次元側を採ると壁を誤輸入）。
5. **循環罠 #2 は設計制約節が SoT**: 各 Phase の「循環チェック」欄で C1–C4 を照合。Phase 4 の受信信号射影は
   「証明ステップであって code def の制限でない」を厳守（codeword 空間は `encoder : Fin M → (ℝ → ℝ)` のまま）。
