# Shannon-Hartley Phase 2 — 時間帯域制限作用素のスペクトル理論 + `ContAwgnCode` def-fix サブ計画 🌙

> **Parent**: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md) §Phase 2（prolate-DOF 壁核）
> **Inventory**: [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)
> **Settled facts (SoT)**: [`shannon-hartley-facts.md`](shannon-hartley-facts.md)（§SPECTRAL-ASSETS / §OBSERVATION-MAP / §BIINF-PHANTOM）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)（sinc/sampling = CLOSED）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（`awgn_converse` / `awgn_channel_coding_theorem` = per-sample 資産）

## 進捗

- [x] 作用素資産 Legs A/B/C/C' + 境界統合 ✅ genuine（`TimeBandLimiting.lean`、下「完了 leg」表）
- [x] Leg 0（gateway）/ Leg P（def-fix = Proposal O）/ Leg D'（BddAbove）✅ CLOSED（下表）
- [x] Leg W（WSEB）❌ 命題が FALSE で終了（下表・台帳 §WSEB/§REVOKED）
- [x] **Leg E — 固有値集中の解析核 ✅ CLOSED**（E-atom/E-trace/E-sharp、leg 15–16）
- [x] **count — 集中の両半分 ✅ CLOSED**（R-atom/R2/R3、leg 17。R1 は DEAD = 構成上不要）
- [x] **R4-ACH（achievability bridge）✅ CLOSED（leg 18–22）**: A1 gateway PASS / 実基底 (B) / route(ii) keystone / L0–L10 全 proof-done。**headline `contAwgn_ge_shannonHartley` = PROOF-DONE sorryAx-free + @audit:ok**（leg 22、`15a111ef`/`ef401a5d`/`173adcb3`）
- [ ] **R4-CONV（converse bridge）= 進行中**。**C1 ✅ CLOSED（leg 23）** = `finrank_le_prolateCount_of_form_gt` proof-done sorryAx-free @audit:ok（crux は Leg E で in-tree = advisor 反証、`nyquist-2w-dof`→`plan:` 再分類監査 CONFIRMED）。**C3 ✅ FULLY CLOSED（leg 25）**: 新 file `ShannonHartleyConverse.lean`、headline `contAwgn_operational_converse` = **無条件 sorryAx-free**（L5 `contAwgn_mi_W_ne_top` = 離散 AWGN converse `awgnConverseJoint_mutualInfo_ne_top` への genuine reduction で closed、@audit:ok、leg 25）。全 6 leaf @audit:ok。残 = C2（Gauss 回転）/ C4（water-filling+極限）/ C0 headline / assembly
- [ ] 残債 — `∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）

---

## ゴール / Approach

### Goal — 2 負債は両方とも解消済、残るは converse bridge のみ

1. **def-fix** ✅ 返済済（2 段）: 観測写像（Karhunen-Loève、Leg P、`4fd8a47c`）+ capacity 定義の phantom biInf
   （leg 22、下記 §⨅-binder hazard）。
2. **壁核 self-build** ✅: 解析核 CLOSED（Leg E、leg 16）+ カウント両半分 CLOSED（leg 17）+ achievability bridge
   CLOSED（leg 18–22）。

**残る唯一の未着手 = converse bridge（R4-CONV / C0–C4）** → `contAwgn_eq_shannonHartley` の残 sorry
（`ShannonHartleyMain.lean:64`、`@residual(nyquist-2w-dof)`、**converse 専用に縮約済** = live consumer 2→1）を落とす。

### Approach（解の全体形）

achievability 半分は proof-done。converse 半分は: 受信信号を prolate 固有基底の上位 `≈2WT` 個へ回転（等方 Gauss
不変性）→ Gram 固有値の interlacing で有効次元を `prolateCount` で上から抑え（**C1 = 唯一の壁候補**）→ 不等利得
operational converse（`parallel_per_input_mi_le_sum`、in-tree）+ water-filling + `T→∞` / `c→0` 極限で SH に一致。
**新しい壁はゼロ**（C1 は Mathlib 0-hit だが count + 有限 V-固有基底から導出可能な公算 = gateway-atom-first で判定）。

**⚠️ 循環判別子（不変、machine 確認済）**: def-fix が「壁の偽装」でないことは「壁が在るべき場所（converse）に残る」
ことで確認済み（achievability の proof-done は crude 両側カウント `prolateCount T W c / T → 2W` だけで足り、
tight LPS 集中を要さない。converse も同 count を**結論として**消費し、仮定しない）。

### §⨅-binder hazard（leg 22 の def-fix。台帳 §BIINF-PHANTOM が SoT）

`contAwgnOperationalCapacity` は当初 `⨅ ε ∈ Set.Ioo 0 1, contAwgnRate`（bounded binder）だった。
conditionally-complete な `ℝ` 上では `⨅ ε, ⨅ (_ : ε ∈ Ioo 0 1), g ε` に展開され、`ε ∉ (0,1)` の各項が空 index の
`sInf ∅ = 0` を拾う ⟹ `contAwgnRate ≥ 0` ゆえ cap が無条件 `= 0` に潰れ、`contAwgn_ge` / `contAwgn_eq` は
**P>0 で false-as-framed だった**（壁 gated ではなく定義バグ）。leg 22 で **subtype infimum
`⨅ ε : ↥(Set.Ioo 0 1), contAwgnRate`**（nonempty ゆえ genuine infimum = docstring intent）へ修理し、監査 all OK
（intent-preserving + converse 壁無傷 = 偽装でない判別子 PASS）。**教訓**: 過去の gateway probe は観測写像 / achievable
rate を検査したが、Lean binder 意味論の縮退（空 index の `sInf ∅` phantom）は直交した軸ゆえ捕まえられなかった
（数値 probe も rate 検査も `ε ∈ (0,1)` の範囲でしか評価せず空 index case を踏まない）。

---

## 完了 leg（履歴は git / 詳細は台帳）

| Leg | 成果 | commit |
|---|---|---|
| A/B/C/C'/境界 | 作用素 `A := P_W∘Q_T∘P_W` + 自己共役 + コンパクト + 固有値降順列挙 framework + 非空虚性 + 退化 tightness（`TimeBandLimiting.lean`） | 4d848a53 / d16a74e1 / de758f19 / a040a456 / a7595371 |
| 0（gateway） | Proposal A/C = FAIL（実装ゼロで反証）、Proposal O（正規直交テスト関数）= PASS。台帳 §OBSERVATION-MAP | leg 13 |
| P（def-fix） | 観測写像を Karhunen-Loève 展開へ。3 宣言が false-as-framed から離脱。ripple 9 decl / 2 file | 4fd8a47c |
| D'（BddAbove） | `contAwgnMaxMessages_bddAbove` を Bessel 単独で壁非依存に proof-done（`hW` 未使用）、@audit:ok | fb18b681 |
| W（WSEB） | 命題が FALSE と確定（`sup f(0)²/∫₀ᵀf² = +∞`）⟹ statement を建てない。台帳 §WSEB/§REVOKED | d2938749 |
| E（解析核） | E-atom（crude trace）/ E-trace（`∑'⟪Abᵢ,bᵢ⟫=2WT`）/ E-sharp（`tr A−tr A² ≤ 2+log(1+2WT)`）全 sorryAx-free。**壁の解析核 CLOSED** | 69152fd9 / 9f1129e1 / 552ac8de+00cb1c8b |
| count（R） | `prolateCount_le` / `le_prolateCount`（両半分、`c` 自由・`D` 明示、sorryAx-free）。R1 は DEAD（`prolateCount := finrank ℂ V` ゆえ多重度 bridge は構成上不在） | e8267457 / 65897bdb / ec0553a6 |
| R4-ACH | A1 gateway PASS / 実基底 (B) / route(ii) keystone / L0–L10 全 proof-done。**`contAwgn_ge_shannonHartley` = PROOF-DONE sorryAx-free + @audit:ok** | leg 18–22（`53723ec2` … `15a111ef`/`ef401a5d`/`173adcb3`） |

**壁論拠は 3 度誤っていた**（結論だけ生き残った。台帳 §SPECTRAL-ASSETS が SoT）:
(1)「無限次元スペクトル理論が Mathlib に無い」→ 誤（`Spectrum.lean:443`）、
(2)「trace 等式にスペクトル定理が要る」→ 誤（Parseval は任意の完全基底で効く）、
(3)「残渣 = Landau-Widom 鋭い漸近等式」→ 枠付けが強すぎ（consumer は緩い片側上界のみ = `cause:weaker-relative` の
**逆向き**適用、leg 15 E-atom の鏡像）。

---

## R4-ACH（achievability bridge）✅ CLOSED（leg 18–22）

**headline `contAwgn_ge_shannonHartley`（`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`）= PROOF-DONE
sorryAx-free + @audit:ok**（`ShannonHartleyMain.lean`、leg 22）。hyp 全 regularity。**コードが SoT** — 構成を再キャッシュしない。

達成の構成（全 proof-done、詳細は git / handoff `## R4-ACH leaf DAG`）:
- L0 `exists_preequalizer`（encoder 側 pre-equalizer `b=A⁻¹x`、L6 の `√c` 下界 → `‖b‖²≤(1/c)‖x‖²`）
- L1–L4（`TimeBandLimiting.lean`）: pointwise repr / bandlimited a.e. / 実 ONB
- L3/L5 `exists_testFn_family`（testFn φ 族 + energy identity bundle）/ L6 `exists_crossMap_lower_bound`（cross-map A の `√c` 下界）
- L7 `contAwgnMaxMessages_ge_of_awgnCode`（離散 `AwgnCode` → `ContAwgnCode` lift + error transport + `le_csSup`）
- L8 transport（rfl 級）/ L9/L10（`awgn_channel_coding_theorem` へ食わせ rate/limsup + `⨅ε → c↑1`）

補助 de-privatize（leg 22、可視性のみ・意味不変）: `contAwgn_log_le_of_pos_k` / `contAwgn_averageError_of_k_eq_zero`
（`ShannonHartleyAchievability.lean`）を L7 の lift で再利用するため private 解除。

**アーキテクチャ**（leg 21 relocation `2f9b4ec6`）: entry-point 2 本を最下流 sink **`ShannonHartleyMain.lean`**
（imports `TimeBandLimiting` + `LpPointwise`）へ移設。import 順 = `ShannonHartley ← Operational ← Achievability ← TimeBandLimiting`。

**⚠️ 監査の signature-scan 教訓（L7 で必須、leg 22 で適用済）**: `exists_crossMap_lower_bound` の `√c` 下界の
非自明性は下流が `IsBandlimited (h i) W` + `∫hᵢhⱼ=δᵢⱼ` を thread し続けることに依存（L7 が operational encoder を
組む際どちらか落とすと「下界は gameable でない」論拠が黙って壊れる = inflated 非 encoder h で充足可能）。
converse（C1）配線時も同種 signature-scan を要す。

---

## R4-CONV（converse bridge）= 進行中（C1 + C3 CLOSED、残 C2/C4/C0/assembly）

**目標**: `contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity` を証明し `contAwgn_eq_shannonHartley` の残 sorry
（`@residual(nyquist-2w-dof)`、**converse 半分専用**）を落とす。**count の下流**ゆえ R1–R3 / E-sharp では落ちない。
**新しい壁はゼロ**（proof-pivot-advisor が leg 16 で機械確認、判別子 PASS）。

| # | 要る命題 | 資産 | 級 |
|---|---|---|---|
| **C0** | headline `contAwgn_le_shannonHartley` が**宣言として存在しない**（achievability 半分が proof-done ⟹ 残 sorry は converse 専用だが、`le_antisymm` 用の `≤` 補題を実不等式として書き下ろす要あり） | 親 plan / inventory が名前だけ参照 = 指示対象なき名前 | 実装（未着手） |
| **C1 ✅ CLOSED** | `#{ν(Gram)>c} ≤ prolateCount T W c` = `finrank_le_prolateCount_of_form_gt`（`S` 上 Rayleigh 商 `>c` ⟹ `finrank S ≤ prolateCount`） | **proof-done sorryAx-free @audit:ok**（`TimeBandLimiting.lean:2617`、leg 23）。crux = 既在 in-tree `inner_timeBandLimitingOp_le_of_mem_orthogonal`（Vᗮ で `⟪Av,v⟫≤c‖v‖²`、@audit:ok、Leg E）+ matched pair `le_inner_timeBandLimitingOp_of_mem`。injection は `orthogonalProjectionOnto` + `LinearMap.finrank_le_finrank_of_injective` | ✅ 完了 |
| **C2** | 観測を Gram 固有基底へ回転（等方 Gauss 不変性）+ **利得 νᵢ を信号電力の ellipsoid 制約へ折り込む**（`∑Qᵢ/νᵢ ≤ TP`） | `stdGaussian_map` + `map_pi_eq_stdGaussian`。⚠️ **後者は `gaussianReal 0 1` 専用**（`errorProbAt` は平均≠0・分散 N₀/2）ゆえ `gaussianReal_map_const_mul` + `_add_const` の affine split を先に噛ませる（1 行 `rw` 不可） | plumbing（self-build wiring） |
| **C3 ✅ FULLY CLOSED** | operational converse `log M ≤ (mutualInfoOfChannel).toReal + Fano ≤ ∑ᵢ ½log(1+P'ᵢ/(N₀/2))`（**等雑音**、利得は C2/C4 の信号電力側） | **`ShannonHartleyConverse.lean`（leg 24 建了 + leg 25 L5 closed）。headline `contAwgn_operational_converse` = 無条件 sorryAx-free + 監査 CONFIRMED（hyp bundling なし・循環 guard PASS）。全 6 leaf @audit:ok（L5 = 離散 AWGN converse への genuine reduction、密度 chain port 回避）** | ✅ 完了 |
| **C4** | water-filling + 極限（ellipsoid `∑Qᵢ/νᵢ ≤ TP`、νᵢ≤1・`#{νᵢ>c}≤prolateCount`（C1）、`/T`、`T→∞`、`c→0`） | 初等 + C1 count | plumbing |

**次アクション（gateway-atom-first、leg 25 advisor 検証済 → [C2 design doc](shannon-hartley-converse-c2-inventory.md) が SoT）**: C3 は leg 24+25 で FULLY CLOSED、C1 は leg 23 で CLOSED。C2/C4 の数学は **SOUND + 非循環**（advisor 確認）だが **1 個の実ギャップ**発見:
1. **⚠️ C3 headline は粗すぎる（弱い親戚）**: `contAwgn_operational_converse` は等雑音の**単純和** `∑P'ᵢ≤T·P`（元座標）だけを露出。C4 の water-filling は**座標ごと** `P'ᵢ≤νᵢQᵢ` が必要。`parallel_per_input_mi_le_sum` は per-coord 束縛 `h_each` を内部証明済なのに ∃ 境界で捨てている → **C4 は C3 headline を消費してはならない**。
2. **gateway atom 1（最高リスク de-risk）**: `frame_form_le_op_form`（band-limited g で `∑ⱼ⟨Q_T g,φⱼ⟩²≤⟨A g,g⟩` = Bessel + `inner_timeBandLimitingOp_self_eq`）。これが通れば count-domination が確定。**最高リスクは Gaussian 回転でなく Gram 固有基底 domination 帰着**（C1 は抽象補題、Gram 特殊化 ~60-120 行が未構築）。
3. **gateway atom 2（同 session）**: companion `parallel_per_input_mi_le_sum_percoord`（`h_each` 露出、consumer 3 個ゆえ in-place 改変せず clone、0 ripple）。
両 atom 通過 ⇒ C2/C4 は壁なし plumbing。順序: count domination →（rotation + ellipsoid）→ C4 water-filling + `T→∞`/`c→0` 極限 → C0 `contAwgn_le_shannonHartley` → `le_antisymm` assembly。**Mathlib gap ゼロ**。
新 route（採用）= 抽象 count-domination `finrank_le_prolateCount_of_form_gt`：`S` 上 Rayleigh 商 `>c` ⟹ `S ⊓ Vᗮ = ⊥`
（Vᗮ で `≤c` の既在 crux と衝突）⟹ `orthogonalProjectionOnto` で `S ↪ V` 単射 ⟹ `finrank S ≤ finrank V = prolateCount`。
**advisor の「interlacing 非自明 = self-build 公算」は反証された** — crux（Vᗮ form bound）は Leg E で既に payが済んでおり
（`cause:loogle-blind` の再演: in-project 資産を見落とす形）、C1 は純線形代数 ~一発で通った。
**`nyquist-2w-dof` → `plan:` 再分類は監査 CONFIRMED で完了**（`73ec6559`、live wall residual 0）。

**C3/C4 leaf DAG（詳細 inventory = [`shannon-hartley-converse-c3-inventory.md`](shannon-hartley-converse-c3-inventory.md)、leg 23、verdict: Mathlib gap なし・self-build ~180–280 行）**:
新 file `ShannonHartleyConverse.lean`（leg 24 で建了）に skeleton-driven で建てた。leaf 状態（実 decl 名は sig_view で確認、以下は inventory 番号との対応）:
1. **L-CV1 ✅**: `contAwgnConverseJoint` def + `IsProbabilityMeasure` instance（`awgnConverseJoint` clone、sorryAx-free）。
2. **L-CV2 ✅**: single-shot wiring（`shannon_converse_single_shot` 消費、`contAwgn_errorProb_eq_averageError` + `_map_fst` uniform、main theorem 内で配線、sorryAx-free）。
3. **L-CV3 ✅ (L2)**: `contAwgnConverseMarkov_holds`（`W→S→Y` Markov、`mutualInfo_le_of_markov` 消費、`converseMarkov_marginalA` clone + pair-law 再利用、proof-done sorryAx-free @audit:ok、leg 24）。
4. **L-CV4 ✅ (L3)**: `contAwgn_mi_S_eq_mutualInfoOfChannel`（`joint = p_S ⊗ₘ W` bridge、`mutualInfoOfChannel_eq_mutualInfo_prod` 消費、sorryAx-free @audit:ok）。
5. **L-CV5 ✅**: `contAwgn_signalLaw_mem_constraint`（power-constraint membership、Bessel `_sum_observation_sq_le`、sorryAx-free）。
6. **L-CV6 ✅ (L5、leg 25 CLOSED)**: `contAwgn_mi_W_ne_top`（MI-finiteness `I(W;Y)≠∞`、proof-done sorryAx-free @audit:ok）。**当初の density chain port（~120 行）を回避**: `contAwgnConverseJoint` は離散 `awgnConverseJoint` と構造同型（`awgnChannel x N = gaussianReal x N` ゆえ encoder=observation・N=(N₀/2).toNNReal で定義的一致）ゆえ、既存 `awgnConverseJoint_mutualInfo_ne_top`（de-privatize）への equality 帰着 ~33 行で closed。**loogle-blind near-miss 回避例**（資産が 2 file 隣に既存）。
7. **C2**: Gauss 回転（affine split 注意、上記）+ ellipsoid 制約導出。
8. **C4**: water-filling + 極限 → `contAwgn_le_shannonHartley`（C0 headline）→ `le_antisymm(contAwgn_ge, contAwgn_le)` で `contAwgn_eq` closure、residual 削除（honesty 変更 → 独立監査必須）。
typeclass: `mutualInfo_le_of_markov` の `[StandardBorelSpace (Fin k → ℝ)]` は `pi_countable` で充足（inventory 確認済）。

**⚠️ converse で prolate カウントは Leg E の結論として使う（仮定してはならない）**: 「`√(T/n)` tight-frame ⟹ 有効ランク
`≈2WT`」を C1 の前に仮定するのは循環（`prolate_eigenvalue_count` の内容そのもの、台帳 §OBSERVATION-MAP 攻撃 1）。

**dangling name 掃除**: C0 の `contAwgn_le_shannonHartley` / `prolate_eigenvalue_count`（散文 + docstring が名前だけ参照
= 指示対象なき名前）を実名 or 削除で解消。

---

## 残債

- [ ] `∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）。退化側は解決済（a7595371）ゆえ
      `0<T` / `0<W` regime のみ。⚠️ 罠: `_hasEigenvalue` の `≠ 0` 仮説は除去可能だが除去してはいけない（除去すると
      結論が空虚化 = content のため残す、台帳 §SELF-REPORT-DRIFT）。

---

## 誠実性制約（explicit、active のみ）

- **`nyquist-2w-dof` の live residual は 0**（leg 23 で C1 PASS ⟹ `contAwgn_eq` の残 sorry を `plan:` へ再分類、
  監査 CONFIRMED、`73ec6559`）。名指す命題（tight LPS 集中 = 第 2 モーメント）は E-sharp で closure 済、
  interlacing count domination は C1 で closure 済。残 obligation（C0/C2/C3/C4）に**壁タグを付けてよいものは無い** —
  詰まったら `@residual(plan:shannon-hartley-phase2-spectral-plan)`（C3 self-build が genuine Mathlib gap を露呈したら
  その時点で新 slug を建てる、それまでは plumbing）。slug は `docs/audit/audit-tags.md` の register に残す（history）。
- **load-bearing hyp bundling 禁止（不変）**: interlacing / converse / count を `*Hypothesis` / `*Reduction` /
  `IsXxxClaim` predicate に束ねて仮説で渡さない。`contAwgn_le` へ結論の核を hyp 化しない。
- **def body に sorry 不可**: `prolateEigenvalues` / `ContAwgnCode` の field は real def（sorry は proof body のみ）。
- **散文に「壁である/ない」「sorryAx-free」をキャッシュしない**。コードの `@residual` / `#print axioms` が SoT、
  高コスト事実は `shannon-hartley-facts.md` にリンク（re-derive > cache）。
- 実装 owner が新 sorry + `@residual` を commit したら独立 honesty audit を同セッションで起動（CLAUDE.md）。
- **新 slug は** loogle-0 + two-stage conclusion-shape 検索 + template lemma 行数見積 + **in-project 先行 grep** が
  揃った時のみ（本 family は「Mathlib に無い」で 3 度焼かれた）。**散文で退けた候補はコンパイラに 1 行書いて退けさせるまで退けたことにならない。**

---

## 循環チェック（C3 受入基準・全 Leg 集約）

`2W` / `⌊2WT⌋` は `prolate_eigenvalue_count`（Leg E）の**結論としてのみ**現れ、どの def の入力にも現れない
（`timeBandLimitingOp T W` の `W` = 物理帯域幅、`prolateEigenvalues` は spectrum 由来、Leg P の全直線エネルギー予算
`∫ f² ≤ T·P` は物理電力、codeword は関数のまま C1 ✓、`sampleCount` / `k` 自由 C4 ✓）。

**tell（循環兆候）**: `contAwgn_eq` が `rfl` / `unfold` のみで済む / `prolateEigenvalues` def に `2WT` 出現 /
reduction が per-sample capacity をそのまま返す / **`contAwgn_eq` が壁なしで閉じる**（def-fix 特有の tell = 偽装なら
Leg 0 へ差し戻し）。

---

## ripple / import

- **signature 変更なし（残作業）**: C0–C4 は既存 sorry を落とす + 新 headline `contAwgn_le` を建てるのみ
  （既存 consumer の署名不変）。
- **import cycle なし**: `TimeBandLimiting.lean`（Legs A/B/C/C'/E）は Mathlib spectral/Fourier +
  `NormalizedSinc` / `WhittakerShannon` を import。entry-point 2 本は最下流 sink `ShannonHartleyMain.lean`
  （imports `TimeBandLimiting` + `LpPointwise`）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ（≤ 10 entry）。

1. **achievability CLOSED、converse が唯一の未着手（active、leg 22）**: `contAwgn_ge_shannonHartley` は proof-done
   sorryAx-free + @audit:ok（`15a111ef`/`ef401a5d`/`173adcb3`）。残 sorry（`contAwgn_eq`:64）は converse 専用に縮約
   （live consumer 2→1）。次 = C1 gateway-atom-first probe → PASS で `nyquist-2w-dof` → `plan:` 再分類。
2. **capacity 定義の phantom biInf を修理（active、leg 22、§⨅-binder hazard / 台帳 §BIINF-PHANTOM が SoT）**:
   bounded binder `⨅ ε ∈ Ioo 0 1` が `sInf ∅ = 0` を拾い cap を `0` に潰し `ge`/`eq` を false-as-framed にしていた
   （壁 gated でなく定義バグ）。subtype infimum で修理、監査 all OK（intent-preserving + converse 壁無傷）。
   gateway probe が観測写像を検査しても binder 意味論の縮退は直交軸で捕まらない。
3. **`nyquist-2w-dof` の名指す命題は CLOSED、残渣は converse bridge の下流（active）**: 解析核（E-sharp）+
   カウント両半分 + achievability bridge が全て閉じても consumer の sorry（`eq`）は落ちない。残るは C1 interlacing のみ
   = 未 gateway-test。壁論拠は 3 度誤り（台帳 §SPECTRAL-ASSETS）。
4. **strength diff は壁を継承する各 leg で再適用（active）**: 残渣を教科書の名前（Landau-Widom / interlacing）で記述
   したら、その標準対象の強度と consumer docstring の要求強度を diff せよ（`ShannonHartleyOperational.lean` の
   converse = 上半分 / achievability = 下半分）。強度は名前に張り付いて leg 間を drift する。
