# Shannon-Hartley Phase 2 — 時間帯域制限作用素のスペクトル理論 + `ContAwgnCode` def-fix サブ計画 🌙

> **Parent**: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md) §Phase 2（prolate-DOF 壁核）
> **Inventory**: [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)
> **Settled facts (SoT)**: [`shannon-hartley-facts.md`](shannon-hartley-facts.md)（§WSEB / §REVOKED / §NUMERIC-TRUE-ARTIFACT）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)（sinc/sampling = CLOSED）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（`awgn_converse` = Leg D' の trace 境界を供給）

## 進捗

- [x] M0 在庫調査 ✅（`shannon-hartley-phase2-spectral-inventory.md`）
- [x] Leg A — 作用素 + subspace + 自己共役 + 正 + `‖A‖≤1` ✅ genuine（4d848a53）
- [x] Leg B — コンパクト性 `timeBandLimitingOp_isCompact` ✅ PROOF-DONE（d16a74e1、4 leaf 全 genuine、監査 PASS）
- [x] Leg C — 固有値降順列挙 `prolateEigenvalues` framework ✅ PROOF-DONE（de758f19、監査 PASS 77a5fdf2）
- [x] Leg C' — 非空虚性 `prolateEigenvalues_zero_pos` ✅ CLOSED（a040a456、監査 PASS 569c48f0）
- [x] 境界補題 + 退化物語の統合 ✅ CLOSED（a7595371、tightness が compiler-backed）
- [x] ~~Leg W — WSEB probe~~ ❌ **命題が FALSE と確定（leg 12、`d2938749`/`67e1ff3f`）**。下記「Leg W — 終了」
- [x] **Leg 0 — 修正後 def の gateway 検査** ✅ **CLOSED（leg 13）**。verdict: **Proposal A = FAIL（反証）/
      Proposal C = FAIL（同欠陥を継承）/ Proposal O = PASS** → 台帳 §OBSERVATION-MAP。下記「Leg 0 — 終了」
- [x] **Leg P — 観測写像の def-fix（Proposal O = 正規直交テスト関数）** ✅ **CLOSED（leg 14、`4fd8a47c`、監査 all OK）**。
      3 宣言が false-as-framed から離脱。**判別子 PASS = 壁は消えなかった**（`wall:nyquist-2w-dof` の実タグ consumer 2 本）。下記「Leg P — 終了」
- [x] **Leg D' — `contAwgnMaxMessages_bddAbove` を Bessel 単独で closure** ✅ **PROOF-DONE（leg 14、`fb18b681`、監査 `@audit:ok`）**。
      sorryAx-free + 全 hyp が regularity（**`hW` は機械検査で未使用**）+ 壁を一切経由せず。下記「Leg D' — 終了」
- [ ] Leg E — tight concentration `prolate_eigenvalue_count`（LPS）📋 **[IN PROGRESS。`ge` と `eq` の両方がここ待ち]**
  - [x] **E-atom（leg 15）**: crude trace bound `c·#{λ>c} ≤ 2WT` = **壁非依存で closure**（`69152fd9` / 監査 `7c43417a`）。
        だが **tight LPS は無傷**（監査が実装者の「壁でない」verdict を refute、`cause:weaker-relative`）。
  - [ ] **E-trace（NEXT）**: 厳密 trace 等式 `∑ₙ λₙ = 2WT`（Bessel → **Parseval** 昇格）。
        **Mathlib に無限次元スペクトル定理が存在すると判明**（`Spectrum.lean:443`）= 旧壁論拠は誤り。
  - [ ] **E-sharp**: 第 2 モーメント `∑ λₙ(1-λₙ) = O(log WT)`（Landau-Widom）← **壁の真の所在の候補**
- [ ] 残債 — `∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）

---

## ゴール / Approach

### Goal

**本 plan は 2 つの負債を負う**:

1. **def-fix** ✅ **返済済（leg 14、Leg P、`4fd8a47c`）**: `contAwgnMaxMessages_bddAbove` /
   `contAwgn_eq_shannonHartley` / `contAwgn_ge_shannonHartley` の 3 宣言は **false-as-framed だった**。
   Proposal O（観測写像 → `[0,T]` 台の正規直交テスト関数 = Karhunen-Loève）で修理し、
   `@residual(defect:false-statement)` は 3 本とも離脱（→ `wall:nyquist-2w-dof` 2 本 + `plan:` 1 本）。
   根本原因は Leg 0 で入れ替わった（leg 13）: `encoder_power`（入力クラス）**ではなく**
   `sampledSignal` + `ContAwgnCode.errorProbAt`（**観測写像**）だった。証拠と機序 → 台帳 **§OBSERVATION-MAP**。
   **残る負債は 2 のみ。**
2. **壁核 self-build（従来）**: `wall:nyquist-2w-dof`（prolate/LPS の `≈2WT` DOF カウント）。
   **live consumer は 0（DORMANT）だが retire しない** — 修正後 def の下で converse が依然要する。

**Legs A/B/C/C' の資産（`TimeBandLimiting.lean`、107 decl / 0 sorry / 監査済）は本 refutation の影響を受けない**
= 有効資産。破棄しない。

### Approach（解の全体形 — gateway が先、実装は後）

```
Leg 0  修正後 def の真偽を敵対的に検査（実装ゼロ）  🚦 ✅ CLOSED（leg 13）
   │      ├ Proposal A（encoder_power → 全直線）      = FAIL  ← sub-Nyquist 漏れ、破棄
   │      ├ Proposal C（Landau-Pollak、指定退避先）   = FAIL  ← 同欠陥を継承、park 解除せず破棄
   │      └ Proposal O（点標本 → 正規直交テスト関数） = PASS  → ↓
   ▼
Leg P  def-fix: 観測写像を Karhunen-Loève 展開へ（Proposal O）  ✅ CLOSED（leg 14、ripple 実測 9 decl / 2 file）
   │      （C1 ✓ 符号語は関数 / C3 ✓ どの def にも 2W なし / C4 ✓ k は自由 — 監査が機械再導出）
   ▼
Leg D' BddAbove を **Bessel 単独**で closure（Σᵢ⟨f,φᵢ⟩² ≤ ‖f‖² ≤ TP、k 一様、壁非依存）
   │      ⚠️ **`ge` はここでは閉じない**（下記の訂正）。Leg D' が閉じるのは `bddAbove` のみ
   ▼
Leg E  tight ≈2WT DOF カウント（LPS）← **壁はここに残る**（Legs A/B/C/C' の上に建つ）
   ├──▶ contAwgn_ge_shannonHartley（achievability = ≈2WT 次元を下から読む）
   ▼
       contAwgn_eq_shannonHartley（Phase 4/5-full 組立）
```

**⚠️ DAG 訂正（leg 14）**: 旧 DAG は `contAwgn_ge_shannonHartley` が Leg D' から `le_csSup` で
**transitive に closure** すると描いていた。これは **def-fix 前の（false だった）def を前提にした線**であり、
Proposal O 下では成り立たない。`ge` は achievability = **利得 ≈1 の次元を ≈2WT 本構成する**ことを要し、
これは固有値カウントを**下から**読むこと = `wall:nyquist-2w-dof` そのもの。実装・監査が独立に同じ結論に到達し、
コード側タグ `@residual(wall:nyquist-2w-dof)` も両者の合意。**Leg P は `ge` を「偽」から「壁ブロック」へ移した**
= plan の DAG が示唆するより**難しくなった**（def-fix が achievability を楽にするという予測の逆側）。

```
```

**Proposal O — 観測写像を Karhunen-Loève 展開へ（Leg 0 PASS 済、Leg P のターゲット）**:

```lean
-- 現行（false を生む）: 点標本 + `Δ` 非依存の固定雑音。`√(T/n)` は Δ=1/(2W) でのみ等長
sampleCount : ℕ ; decoder : (Fin sampleCount → ℝ) → Fin M
sampledSignal f T n i = √(T/n) * f (i * (T/n))
-- Proposal O: [0,T] 台の正規直交テスト関数（k は自由のまま = C4）
testFn : Fin k → (ℝ → ℝ)
testFn_support    : ∀ i, Function.support (testFn i) ⊆ Set.Icc 0 T
testFn_orthonormal : ∀ i j, (∫ t, testFn i t * testFn j t) = if i = j then 1 else 0
-- 観測 yᵢ = ∫ (encoder m)·testFn i + zᵢ,  zᵢ ~ N(0, N₀/2) iid
-- + encoder_power も全直線へ（Proposal A の変更自体は独立に正しい／それ**だけ**では不十分だった）
```

**なぜこれが定義であって代用でないか（Leg 0 の核心）**: 正規直交族に対し白色雑音係数 `⟨ξ, φᵢ⟩` は
**厳密に** iid `N(0, N₀/2)` ⟹ `Measure.pi` が厳密（現行 `sampledSignal` は Nyquist 間隔でのみ等長 =
Nyquist を仮定して Nyquist を証明する代用だった）。教科書の整合フィルタ離散化そのもの。

**blast radius**: ⚠️ 下表は **Proposal A（field 1 本の型変更）で実測した旧値**であり **Proposal O には
適用できない**（観測写像の差し替えは `errorProbAt` / `averageError` / `contAwgnMaxMessages` の**署名**にも
及びうる）。**Leg P の最初の仕事は `scripts/dep_consumers.sh` での再実測**。旧値は参考のみ:
`ContAwgnCode` = direct 5 decl / 2 file、transitive 9 decl / 2 file
（`ShannonHartleyOperational.lean`: `.mk.inj` / `.errorProbAt` / `.averageError` / `contAwgnMaxMessages`
→ `contAwgnRate` / `contAwgnOperationalCapacity` / `contAwgn_eq_shannonHartley`。
`ShannonHartleyAchievability.lean`: `contAwgnMaxMessages_bddAbove` → `contAwgn_ge_shannonHartley`）。

**Leg D' が壁非依存で閉じる機構（Proposal O では Bessel 単独 = 旧 sup-境界ルートより単純）**:
`testFn` が正規直交ゆえ Bessel の不等式が直接効く。

```
∑ᵢ ⟨f, φᵢ⟩²  ≤  ‖f‖₂²  ≤  T·P                        — Bessel、k について一様、2W を経由しない
awgn_converse + log(1+x) ≤ x  ⟹  log M ≤ TP/N₀       — 有限 ⟹ BddAbove
```

**この上界は crude だが、Proposal A の crude 上界 `2WT²P/N₀` より真に強い**（rate `≤ P/N₀` = 広帯域極限で
**T→∞ でも有界**）。それでも `contAwgn_eq_shannonHartley` は閉じない — `ln(1+x) ≤ x` ゆえ
`P/N₀ ≥ W·ln(1+P/(W·N₀))` = SH で、**等号でない**。exact 定数には依然 `≈2WT` DOF カウント（Leg E）が要る。
**この非対称性が下記「禁止の撤回」の判別子そのもの**（偽装なら壁が消える → 消えない）。
**循環警報は鳴らない**（handoff の機械検査可能な予測: crude 経路が rate まで SH に閉じたら循環。閉じない ✓）。

**⚠️ 破棄された案（復活させないこと、根拠 → 台帳 §OBSERVATION-MAP）**:
- ~~**Proposal A 単独**（`encoder_power` → 全直線のみ）~~ = **FAIL**。sub-Nyquist で SH を超過。
  ただし `encoder_power` → 全直線という**変更自体は Proposal O の一部として維持**（A は誤りでなく不十分）。
- ~~**Proposal C（Landau-Pollak = 時間制限 + 帯域集中）**~~ = **FAIL**。旧 plan の指定退避先だったが
  **同じ観測写像欠陥を継承**（反例の補間子はエネルギーの 99.76% が窓内 ⟹ 時間制限で死なない）。park 解除せず破棄。
- ~~**per-sample 雑音分散を `(N₀/2)·2W·Δ` にスケール**~~ = **FAIL**。sub-Nyquist は塞ぐが oversampling で
  非有界に漏れる（`ν → 0` かつ信号部分空間は `≈2WT` 次元固定 ⟹ 部分空間内の総雑音 `2WT·ν → 0`）。
- ~~**`sampleCount ≥ ⌈2WT⌉` を field で要求**~~ = **数学的には動くが tier-5 で禁止**。DOF カウントを def に
  密輸 = C4 の存在理由そのもの。**honesty で reject（math で reject ではない）**。
---

## 禁止の撤回 — 「`ContAwgnCode` に全直線エネルギー field 追加は禁止」は **REVOKED**

**撤回対象**（本ファイル旧版の 4 箇所、いずれも同一趣旨）: 旧 `:164-165`（中心問題 verdict の「撤退」節）/
旧 `:205-206`（Leg W retreat line）/ 旧 `:244-245`（Leg D retreat line）/ 旧 `:293`（誠実性制約）。
文言 = 「`ContAwgnCode` へ全直線エネルギー field 追加は禁止（load-bearing tier-5、壁の偽装）」。

**なぜ書かれたか（当時は正しかった）**: WSEB=**TRUE** の枝で書かれた。WSEB が真なら
「窓エネルギー ⟹ 標本エネルギー」の tie は**実在する定理**（prolate/LPS）であり、それを証明する代わりに
field として仮定するのは **実在する壁の偽装** = tier-5。この推論は WSEB=TRUE の下で健全だった。

**なぜ今は誤りか**: **WSEB は FALSE**（`shannon-hartley-facts.md` §WSEB。6 行の解析証明、独立
`proof-pivot-advisor` が反証を試みて失敗）。**FALSE 枝が発火した**。そして旧 `:205-206` は
**同じ retreat line の中で自己矛盾していた**:

> 「WSEB が false → **`ContAwgnCode` / 容量 def の def-fix に escalate**（…全直線エネルギー field 追加は禁止 = 壁偽装 tier-5）」

= 「def-fix せよ」と「def-fix の唯一の内容を禁ずる」を 1 文で並べていた。禁止は TRUE 枝のために書かれ、
FALSE 枝に対して更新されないまま残った。**撤回は禁止の破棄ではなく、発火した枝への正しい解決**。

### 判別子 — 偽装と修正を分ける（主張でなく検査）

**偽装なら壁は消える。この修正では消えない。**

| | 壁偽装（tier-5） | Proposal O（正しい def-fix） |
|---|---|---|
| WSEB=TRUE 下で field 追加 | 実在する prolate 定理を仮定に降格 ⟹ **壁が消える** | — |
| `k ≥ ⌈2WT⌉` を field で要求 | DOF カウントを def に密輸 ⟹ **壁が消える**（Leg 0 で名指し reject） | — |
| Proposal O 適用後 | — | `BddAbove` は **Bessel 単独・壁非依存**で閉じるが、`contAwgn_eq_shannonHartley` は **依然 `≈2WT` DOF カウント（Leg E）を要する** ⟹ **壁は在るべき場所に残る** |

⟹ **`wall:nyquist-2w-dof` は Proposal O の後も retire されない**（DORMANT のまま Leg E で consumer が復活）。
壁が消えないことが、この field 追加が偽装でない**機械的に確認可能な**証拠。
**受入検査**: Leg P/D' 着地後に `contAwgn_eq_shannonHartley` が壁を要さず閉じたら、それは修正でなく偽装
（= 循環の tell）。その時は Leg 0 に差し戻す。

### 傍証 — 窓のみ拘束は「設計」でなく「事故」だった

`synthSignal_window_energy_le`（`ShannonHartleyAchievability.lean:451`、`@audit:ok`）の存在理由は
**全直線エネルギーを窓エネルギーへ降格すること**だけ:

```lean
theorem synthSignal_energy (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n) :
    (∫ t, (synthSignal T n a t) ^ 2) = (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2   -- 全直線、等号
theorem synthSignal_window_energy_le … :                                        -- ↑ を ≤ に落とすだけ
    (∫ t in Set.Icc (0 : ℝ) T, (synthSignal T n a t) ^ 2) ≤ (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2
  := by rw [← synthSignal_energy T n a hT hn]; exact setIntegral_le_integral …
```

**achievability 側は既に全直線で有界な信号を作っており、その強さを捨てている**。しかも
`scripts/dep_consumers.sh synthSignal_window_energy_le` = **direct consumers 0 decl / 0 file** =
**既に誰も使っていない**（窓のみ制約に合わせるためだけに先回りで建てられ、未使用のまま）。
⟹ **def-fix は achievability を難しくせず、むしろ易しくする**: 修正後 `encoder_power : ∀ m, (∫ t, (encoder m t)^2) ≤ T*P`
は `synthSignal_energy` の**等号がそのまま与える形**（`(T/n)∑aᵢ² = ∑cᵢ² ≤ T·P`）。
**予測（Leg P で確認）**: `synthSignal_window_energy_le` は def-fix 後に**恒久的に不要** = 削除候補。

---

## Leg 0 — 修正後 def の gateway 検査 🚦 ✅ **CLOSED（leg 13）— verdict: Proposal A/C = FAIL、Proposal O = PASS**

**目的だった**: 実装が 1 行も着地する前に、修正後 def の下で `contAwgn_eq_shannonHartley` が TRUE かを
敵対的に検査する。**gateway は仕事をした** — Proposal A は実装ゼロで反証された。

**証拠・機序・数値・教訓は台帳が SoT** → `shannon-hartley-facts.md` **§OBSERVATION-MAP**。
再検証: `python3 docs/shannon/leg0-gateway-probe.py`。ここに再キャッシュしない。

### verdict（3 行）

- **Proposal A（`encoder_power` → 全直線エネルギー）= FAIL**。`sampleCount` が自由（C4）ゆえ code は
  **Nyquist より粗く**標本でき、`sampledSignal` の `√(T/n)` は `Δ = 1/(2W)` でのみ等長 ⟹
  `s := P/(W·N₀) < 2` の全てで SH を超過（s→0 で比は非有界）。**厳密証明は整数事実に落ちる**（`5 > 4`）。
  独立 `proof-pivot-advisor` が周波数領域から再導出して確認 + 私の代替案（雑音分散スケール）を逆向きに反証。
- **Proposal C（Landau-Pollak）= FAIL**。plan が指定した退避先だったが**同じ欠陥を継承**する
  （反例の補間子はエネルギーの 99.76% が窓内 ⟹ 時間制限で死なない）。**park 解除せず破棄**。
- **Proposal O（点標本 → `[0,T]` 台の正規直交テスト関数）= PASS**。4 攻撃 + 収束テスト + 敵対的 φ 探索
  200 試行を生存。**Leg P の新ターゲット**。

### なぜ 4 攻撃が漏れを捕まえられなかったか（次の gateway 設計への入力）

**名指しの 4 攻撃はすべて*入力クラス*軸だった**（`encoder_power` を何に替えるか）。実際の欠陥は
**観測写像**軸（`sampledSignal` + `errorProbAt`）にあった。攻撃 1 は oversampling（`n → ∞`）だけを名指し、
**実際の漏れは真逆の向き**（under-sampling）— しかも oversampling は実際には漏れないことが確認された。
攻撃 1 が疑えと命じた「`√(T/n)` tight-frame ⟹ 実効ランク ≈2WT」という未検証仮説は、**疑うべき方向が
逆だった**（仮説は over 側では正しく、under 側で崩れる）。

**転用可能な tell（次の def にも適用せよ）**: **モデルがちょうど 1 つのパラメータ値でのみ較正されており、
その値が定理の証明すべき当の量であるとき、そのモデルは定義でなく代用である。** `sampledSignal` は
Nyquist 間隔でのみ等長 = Nyquist を仮定して Nyquist を証明する構図だった。

**gateway の無限後退を止める打ち切り**: 「新 def は代用か定義か」を問う 1 段のみ。Proposal O は
`Measure.pi`（独立雑音）を**厳密**にする（正規直交 ⟹ 白色雑音係数が厳密に iid）ので、この軸で止まる。
---

## Leg P — 終了（✅ CLOSED、leg 14、`4fd8a47c`、監査 all OK）

Proposal O を適用し 3 宣言を false-as-framed から救出。**ripple 実測 = 9 decl / 2 file**（Shannon-Hartley
の 2 ファイルに限局。`WynerZiv`/`MultipleAccess` の `.decoder` は別構造で無関係）。**def の現物がコード側 SoT**
（`ShannonHartleyOperational.lean` の `ContAwgnCode` / `ContAwgnCode.observation` / `errorProbAt`）
— **ここに field 一覧を再キャッシュしない**。

**判別子 PASS**（本 leg の存在理由）: def-fix 後も `contAwgn_eq_shannonHartley` は `≈2WT` DOF カウントを要し、
`wall:nyquist-2w-dof` は**実タグ consumer 2 本で生存**（`eq` + `ge`）。壁が消えていたら偽装 = Leg 0 差し戻しだった。

**削除**: `sampledSignal`（= 代用の本体）+ `sampledSignal_synthSignal{,_sqrt}` + `synthSignal_window_energy_le`
（consumer 0 を実測確認 = plan の予測が的中）+ field `sampleCount` / `encoder_continuous`。

**`encoder_continuous` 除去の正しい論拠**（実装側の報告した論拠は `ge` 方向で破れており、監査が是正）:
「クラスを広げるから converse が難しくなる ⟹ 救済ではない」は `bddAbove` には効くが `ge` では**逆**
（クラスを広げると achievability は*易しく*なる）。実際に成り立つのは**観測可能量の a.e. 不変性**:
`observation = ∫ t, encoder m t * testFn i t` は Bochner 積分ゆえ a.e. クラスにしか依存せず、他の全 field も
a.e. 不変 ⟹ `encoder_continuous` は唯一の代表元固定 field で、除去は**両方向に厳密に inert**。

**tier-5 は回避された**: `k` は自由 `ℕ`（C4 ✓）/ どの def / field にも `2W`・`⌊2WT⌋`・`⌈2WT⌉` なし（C3 ✓、
`bandlimited_sup_bound` / `synthSignal_bandlimited` の `2W` は**定理**であり C3 の対象外）/ `encoder` は関数（C1 ✓）/
`contAwgnMaxMessages` に `2W` なし（C2 ✓）。監査が全て機械再導出。

**残タグ**: `eq` → `wall:nyquist-2w-dof` / `ge` → `wall:nyquist-2w-dof`（**DAG 訂正の項を見よ**）/
`bddAbove` → `plan:shannon-hartley-phase2-spectral-plan`（Leg D' が閉じる）。

---

## Leg D' — 終了（✅ **PROOF-DONE**、leg 14、`fb18b681` + 監査 `@audit:ok`）

`contAwgnMaxMessages_bddAbove` を **Bessel 単独**で closure。**署名不変**（ripple 0）、~150 行、見積内。
**コードが SoT** — 証明構成をここに再キャッシュしない。

**達成した bar**: `#print axioms` = `[propext, Classical.choice, Quot.sound]`（sorryAx-free）**かつ**
全 hyp が regularity（監査が de Bruijn binder 検査で確認）。`sorryAx`-free だけでは完了 verdict にならない
（`h_opt`/`h_max_ent` の罠）ので後者が本体 — **本 leg にはそもそも project 定義の述語仮説が 1 つも無い**。

**壁非依存が機械確認された**（本 leg の存在理由）: 証明項の推移的定数閉包 55234 個に対し
`bandlimited_sup_bound` / `prolate` / `timeBandLimiting` / `Whittaker` / `Slepian` / `Nyquist` / `synthSignal` /
`sinc` はいずれも **0 hit**。予想より強く **`hW : 0 < W` は未使用**（`encoder_bandlimited` と `testFn_support`
も読まれない）。`hW` は保守的なだけで有害でないので残置（docstring に明記済）。
**循環も機械で排除**: `bandlimitedAwgnCapacity` / `contAwgn_eq_shannonHartley` / `contAwgnRate` 等はいずれも
閉包に不在。crude route の閉じる rate は `≤ P/N₀`（広帯域極限）で SH より真に弱い。

**予測が外れた 2 点（記録）**:
- **`synthSignal_memLp`（実数版）の穴は Leg D' では発火しなかった** — Leg D' は converse 方向で**全 code に
  対する量化**ゆえ code を構成せず、`encoder_memLp` は field として渡ってくる。監査の *probe* が code を
  構成したから当たっただけで、転移しなかった。**穴自体は実在** → Leg E / 将来の probe が当たる。
- **`P = 0` が plan 未記載の分岐だった**: `awgn_converse` が `0 < P'` を要求するが `T·P/k = 0`。
  `P' := (T·P+1)/k` で解決（`+1` は crude 境界が呑めるスラック、緩める向きゆえ健全、k 一様性も保存）。
  `k = 0` も独立分岐（`Measure.pi_of_empty` = 点質量、`ε<1` だけで `1/(1-ε)` に抑える）。

**非空虚性**（`proof-done` verdict が最も要する検査）: 監査が `zeroCode` で `Nonempty (ContAwgnCode 1 1 1 2)` を
sorryAx-free に再導出（台帳の leg 14 行は**未コミット** probe 引用なので `rg` で辿れず、独立に建て直した）。
leg 13 が**同じ statement を旧 def 下で FALSE（非有界）**と機械判定していることと合わせ、
**def-fix こそがこれを真にした** = 主張に実質がある。

---

## Leg E — tight concentration `prolate_eigenvalue_count`（LPS）📋 **[壁が残る場所]**

**目的**: `#{n | 1/2 < prolateEigenvalues T W n}` の `⌊2WT⌋ + O(log WT)` 集中（Landau-Pollak-Slepian）。
`contAwgn_eq_shannonHartley` の exact 定数に必須。proof-log: yes（撤退 rationale）。**Phase-4 専用**。
Legs A/B/C/C' の上に建つ（それらは本 refutation の影響を受けない有効資産）。

**位置づけ**: **`wall:nyquist-2w-dof` は live consumer 2 本**（`contAwgn_eq_shannonHartley`:477 /
`contAwgn_ge_shannonHartley`:725 — leg 14 の Leg P で復活。~~現在 0 = DORMANT~~ は失効）。
**Leg E はその 2 本を養う壁核そのもの** = 本 family の残る唯一の負債。
`@residual(wall:nyquist-2w-dof)` は本 leg の sanctioned 撤退口。

### gateway atom = 実施済（leg 15）— **壁は残るが、壁論拠が入れ替わった** 🚦

CLAUDE.md gateway-atom-first に従い decisive atom を 1 本 dispatch した。**結果は二面性を持つ**:

- ✅ **通った部分**: crude trace bound **`c · #{λ > c} ≤ 2WT`** が **壁非依存で closure**
  （`sum_inner_timeBandLimitingOp_le` / `prolateCount_mul_le`、`TimeBandLimiting.lean`、`69152fd9`、
  sorryAx-free + 監査 `@audit:ok` ×7、`7c43417a`）。機構は **Bessel + 既存の再生核表示**
  `bandLimitProj_apply_ae`（`‖k_t‖² = 2W` = 帯域の測度、`∫₀ᵀ` = 窓の測度、`2WT` は |band|×|window| として emerge）。
  **有限直交族しか要らないため無限次元 trace 理論を一切経由しない**。
- ❌ **通らなかった部分（= 壁の本体、監査が実装者の verdict を訂正）**: 本 leg が名指す **tight LPS 集中は無傷**。
  Bessel は**片方向**ゆえ下界に届かず、Markov は `1/c` 倍の過大計上で `2WT + O(log WT)` の鋭さを与えない。
  実装者は「壁は genuine でない・`cause:single-route`」と報告したが、**独立監査が逐語根拠で refute**:
  閉じたのは**弱い親戚**（crude bound）であり、弱い命題を閉じても強い命題についての壁 verdict は覆らない
  （`cause:weaker-relative` = CLAUDE.md「textbook-object strength diff」トラップ）。**verdict は監査を採用**。

**consumer が実際に要する強度（コード側 SoT、`ShannonHartleyOperational.lean:461-462`）**:
`eq` は**上下両半分を鋭く**要し、`ge` は**下半分のみ**を要す ⟹ **gateway atom はどちらも unblock しない**。
判別子とも整合（crude 経路が `eq` を閉じたら偽装 → 閉じない ✓）。

### 壁論拠の入れ替え（leg 15 の最重要成果 — 次 leg の入力）

**旧論拠「無限次元スペクトル理論が Mathlib に無い」は誤り**（grep で機械確認）:

| Mathlib 資産 | 有無 |
|---|---|
| trace-class / Schatten / Hilbert-Schmidt 作用素論 | **不在**（`SingularValues.lean` / `Trace.lean` は `[FiniteDimensional]` 専用） |
| **コンパクト自己共役の無限次元スペクトル定理** | **存在** — `Spectrum.lean:443` `orthogonalComplement_iSup_eigenspaces_eq_bot`（固有空間の iSup の直交補 = `⊥`） |
| コンパクト作用素の固有空間有限次元性 | **存在** — `Spectrum.lean:464`（本 family が既に消費中） |

⟹ **次 atom = 厳密 trace 等式 `∑ₙ λₙ = 2WT`**（`Bessel → Parseval` 昇格）。機構:
`orthogonalComplement_iSup_eigenspaces_eq_bot` から `A` の**完全**固有基底を組む ⟹ Parseval で
`∑ₙ |⟨k_t, eₙ⟩|² = ‖k_t‖²`（不等式でなく**等式**）⟹ 全項非負ゆえ Tonelli で `∑∫ = ∫∑` ⟹ `∑ₙ λₙ = ∫₀ᵀ 2W = 2WT`。
これは atom の Bessel 論法の**そのままの強化**であり、trace-class API を要さない。
**ただし trace 等式だけでは `#{λ > 1/2}` は出ない** — 第 2 モーメント `∑ λₙ² = ‖A‖²_HS` と
`∑ λₙ(1-λₙ) = O(log WT)`（Landau-Widom）が要る。**そこが壁の真の所在**か否かは次 atom が判別する。

**壁宣言の条件（未達 — 現時点で壁を「genuine」と確定させてはならない）**: loogle の過去 `Found 0` は
必要条件であって十分条件でない。two-stage conclusion-shape 検索 + template lemma 行数見積 +
**in-project 先行 grep** を揃える（`cause:loogle-blind`、本 family で 2 度発火 + leg 15 で
「Mathlib に無限次元スペクトル定理が無い」という**未検証の否定的主張**が 3 度目の近接事例）。
**散文で退けた候補は、コンパイラに 1 行書いて退けさせるまで退けたことにならない。**

**循環チェック（最重要）**: `2WT` は本カウントの**結論**としてのみ現れ、`prolateEigenvalues` /
`timeBandLimitingOp` の def の入力ではない（C3 ✓）。**statement は `True` placeholder でなく実不等式で書く**。
**retreat line**: `sorry + @residual(wall:nyquist-2w-dof)`（compound 化しない）。

---

## Leg W — 終了（WSEB）❌ **命題が FALSE**

**Leg W は「probe 保留 / make-or-break / UNKNOWN」ではない。FALSE 枝が発火し、leg は閉じた。**
`sup{f(0)²/∫₀ᵀf² : f ∈ PW_W} = +∞` ⟹ WSEB 不等式は成り立たない。
⟹ **`wseb` を statement として建てない**（偽の命題に自前構築すべき理論はない）。
Leg D（旧・WSEB 経由の BddAbove）は as-framed で dead → **Leg D' が置換**（sup 境界経由、def-fix 後）。

詳細（6 行の解析証明 / 倍精度アーティファクト / forward-evaluated witness 276.29 / 単調性違反）→
`shannon-hartley-facts.md` §WSEB・§REVOKED・§NUMERIC-TRUE-ARTIFACT。**ここに再キャッシュしない**。

---

## 完了 leg（圧縮 — 履歴は git）

| Leg | 成果 | commit |
|---|---|---|
| A | 作用素 `A := P_W ∘L Q_T ∘L P_W` + 自己共役 + 正 + `‖A‖≤1`、新 file `TimeBandLimiting.lean` | 4d848a53 |
| B | `timeBandLimitingOp_isCompact`（4 leaf 全 genuine、reusable な L²-kernel⟹compact を含む） | d16a74e1 |
| C | `prolateEigenvalues` 降順列挙 framework（counting-function の一般逆、`0 < c` guard 必須） | de758f19 / 監査 77a5fdf2 |
| C' | 非空虚性 `prolateEigenvalues_zero_pos`（framework が spectral content を運ぶことを確定） | a040a456 / 監査 569c48f0 |
| 境界 | `timeLimitSubspace_eq_bot_of_nonpos` 他、退化 4 クラスの tightness が compiler-backed | a7595371 |

**これらは WSEB refutation の影響を受けない**（作用素論の資産であり、`ContAwgnCode` の def に依存しない）。
Leg E の土台として保持する。

---

## 残債

- [ ] **`∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）**。`λ 0` の atom より厳密に
      大きい obligation（`A` が無限 rank であることを要す）。退化側は解決済（a7595371 の
      `prolateEigenvalues_eq_zero_of_*` が全 `n` で成立）ゆえ **`0<T`, `0<W` regime だけ**見ればよい。
  - ⚠️ **罠（採るな）**: 「`_hasEigenvalue` の `≠ 0` 仮説は除去可能」— 監査により**実際に除去可能**と確定
    （`ker A ⊇ ker P_W ≠ ⊥` ゆえ `0` は常に固有値）。**だが除去してはいけない**: `λ n = 0` かつ `0` が固有値なら
    結論は自明成立 = 無条件形は pin する内容が厳密に**少ない**。仮説は「必要だから」でなく **content のため**に残す。
- [ ] **散文 de-tag 3 件**（いずれも prose、tag 構文ではない。コードの意味は変えない）:
  1. **`ShannonHartley.lean:29-31`** — module docstring が「reduces the whole gap to the single genuine Mathlib wall
     `@residual(wall:nyquist-2w-dof)`」と**偽**を述べ、かつ**phantom `@residual(wall:nyquist-2w-dof)` トークン**を含む。
     `rg 'nyquist-2w-dof' InformationTheory/` = 3 hit のうち**唯一の `@residual(...)` 形**ゆえ、
     **0-consumer の壁の SoT grep 数を水増ししている**。散文へ de-tag する（他 2 hit =
     `Operational.lean:459` / `TimeBandLimiting.lean:1459` は既に散文）。
  2. **`ShannonHartleyAchievability.lean:459`** — section header が `§E — boundedness of the message set (wall-gated)`
     のまま。**wall-gated ではない**（false-statement → def-fix 後は壁非依存）。
  3. **`Operational.lean:360–363` の `sampledSignal` docstring** — brief の指示は「`d2938749` で修正済ゆえ再修正でなく
     **確認**」。**確認結果 = 修正済だが行番号がずれている**: 当該 docstring は現在 **`:388-395`**（def は `:396`）で、
     `:360-363` は今や `ContAwgnCode` docstring の defect 説明。`:393-395` は
     「The two energies agree only in the limit, not at fixed `n`: for `n = 1` the discrete energy is `T · f(0)²` …
     it is false」= **正しく修正済**。**追加作業なし**（Leg P で def-fix 後に「it is false」の時制のみ要更新）。
- [ ] **`audit-tags.md` の kind 語彙に exact な受け皿が無い**（本 plan の write scope 外 = 報告のみ）:
      「inhabited かつ内部整合だが、意図した対象を under-constrain する def」に対し `ContAwgnCode` は
      `@audit:defect(degenerate)` を**最寄りの近似**として担いでいる（auditor の判断 + stretch は記録済）。
      新 kind **`under-constrained`**（cause `signature-drops-constraint`）が exact な受け皿。promote 判断は
      audit-tags.md の owner に属す。

---

## 誠実性制約（explicit）

- **3 宣言の `sorry` は充填不能**（命題が偽）。`@residual(defect:false-statement)` +
  `@audit:defect(false-statement)` + `@audit:closed-by-successor(shannon-hartley-phase2-spectral-plan)` の
  3 点セットを **def-fix 完了まで維持する**。これは audit-tags.md **「`defect` の (b) 用法」= 正規**であり、
  **signature が defect 形のまま残るのが正しい状態**（監査は撤回してはならない — 撤回先が存在しない）。
- **`ContAwgnCode` への全直線エネルギー field 追加は REVOKED = 許可**（上記「禁止の撤回」)。
  **ただし判別子を満たすこと**: 修正後も `contAwgn_eq_shannonHartley` が `wall:nyquist-2w-dof`（Leg E）を
  要すること。壁が消えたら偽装 ⟹ Leg 0 へ差し戻し。
- **load-bearing hyp bundling 禁止（不変）**: WSEB / concentration / compact / BddAbove を
  `*Hypothesis` / `*Reduction` / `IsXxxClaim` predicate に束ねて仮説で渡さない。
  **`≥` 定理へ `BddAbove` を hyp 化しない**。
- **Leg D' の詰まりは `wall:nyquist-2w-dof` へ退避しない** — この route は壁を経由しない（詰まり = plumbing）。
  退避先は `@residual(plan:shannon-hartley-phase2-spectral-plan)`。
- **Leg E の詰まりのみ `wall:nyquist-2w-dof`**（同一 family 集約、compound 化しない）。**新 slug は**
  loogle-0 + two-stage conclusion-shape 検索 + template lemma 行数見積 + **in-project 先行 grep** が揃った時のみ。
- **def body に sorry 不可**: `prolateEigenvalues` は real def。`ContAwgnCode` の field も同様
  （def-fix は field の**型**を直す = sorry を置く場所ではない）。
- **散文に「壁である/ない」をキャッシュしない**。コードの `@residual` が SoT、高コストな事実は
  `shannon-hartley-facts.md` にリンク（re-derive > cache）。
- 実装 owner が新 sorry + `@residual` を commit したら **独立 honesty audit を同セッションで起動**（CLAUDE.md）。

---

## 循環チェック（C3 受入基準・全 Leg 集約）

**C3**: 定数 `2W`/`⌊2WT⌋` は **`prolate_eigenvalue_count`（Leg E）の結論としてのみ** 現れ、どの def の入力にも現れない。

- `timeBandLimitingOp T W` の `W` = 物理帯域幅（入力）≠ DOF カウント `2W`。✓
- `prolateEigenvalues` = spectrum から定義、`2WT` 非入力。✓
- **Leg P（def-fix）**: 全直線エネルギー `∫ t, f² ≤ T·P` は物理電力予算 = model 制約。`2W`/`⌊2WT⌋` 非出現、
  codeword はサンプルベクトルでなく関数のまま（C1 ✓）、`sampleCount` 自由（C4 ✓）。✓
- **Leg D'**: `BddAbove` は `E_s ≤ 2WT·(T·P)` で bound。**`2W` は `bandlimited_sup_bound` の結論由来**
  （`|f t| ≤ √(2W)·‖f‖₂` = Paley-Wiener の帰結）で def の入力ではない。EXACT `⌊2WT⌋` 不要。✓
- Leg E で初めて `2WT` が**カウントの結論**として出る。✓

**tell（循環兆候）**: `contAwgn_eq_shannonHartley` が `rfl`/`unfold` のみで済む、`prolateEigenvalues` def に
`2WT` 出現、reduction が per-sample capacity をそのまま返す、**`contAwgn_eq_shannonHartley` が壁なしで閉じる**
（← def-fix 特有の新 tell、上記「判別子」）。

---

## ripple / import

- **signature 変更あり（Leg P）**: `ContAwgnCode.encoder_power` の**型**が変わる。blast radius は実測
  **direct 5 decl / 2 file、transitive 9 decl / 2 file**（上記 Approach の表）。consumer の署名は不変
  （capacity 3 本 + `errorProbAt`/`averageError` は field を読まない）ゆえ実質 touch は
  **`ContAwgnCode` を構成する achievability 側**のみ。
- **Leg D' は signature 変更なし**（既存 sorry を fill）。
- **import cycle なし**: `TimeBandLimiting.lean`（Legs A/B/C/C'/E）は Mathlib spectral/Fourier +
  `NormalizedSinc`/`WhittakerShannon` を import。Leg P/D' は `ShannonHartleyOperational.lean` /
  `ShannonHartleyAchievability.lean` 内（`AWGN.Converse` の `awgn_converse` を消費、作用素 file に依存しない）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ（≤ 10 entry）。

1. **WSEB=FALSE で本 plan の負債が「壁 self-build」から「def-fix + 壁 self-build」の 2 本に増えた（leg 12、
   `d2938749`/`67e1ff3f`）**: 3 宣言（`contAwgnMaxMessages_bddAbove` / `contAwgn_eq_shannonHartley` /
   `contAwgn_ge_shannonHartley`）は false-as-framed で、コード側が
   `@audit:closed-by-successor(shannon-hartley-phase2-spectral-plan)` = **本 plan を def-fix の負い手に名指し**。
   根本原因 `ContAwgnCode.encoder_power` の窓のみ拘束（`cause:signature-drops-constraint`）。
   `wall:nyquist-2w-dof` は live consumer 0 = DORMANT だが **retire しない**（修正後 def の converse が要する）。
   settled facts → `shannon-hartley-facts.md`（再キャッシュしない）。
2. **「全直線エネルギー field 追加は禁止」を REVOKED（active、上記「禁止の撤回」節が SoT）**: 禁止は WSEB=**TRUE** の枝で
   書かれ（真なら実在する prolate 定理の偽装 = tier-5）、**FALSE 枝が発火した**のに更新されず、旧 `:205-206` で
   「def-fix に escalate」と**同一文中で自己矛盾**していた。**判別子 = 偽装なら壁が消える / この修正では消えない**
   （BddAbove は壁非依存で閉じるが `eq` は Leg E を要する）。**傍証**: `synthSignal_window_energy_le`
   （`:451`、`@audit:ok`、**consumer 0 = 既に未使用**）は全直線エネルギーを窓へ降格するためだけに存在し、
   `synthSignal_energy`（`:398`）の**全直線等号**が修正後 field をそのまま満たす ⟹ **def-fix は achievability を
   易しくする**。窓のみ拘束は設計でなく事故だった。
3. **Leg 0（gateway）を Proposal A の block に置く（active、make-or-break）**: **修正後 def で
   `contAwgn_eq_shannonHartley` が TRUE になることを誰も検査していない**。leg 9 の失敗の本体は
   「三者が『どれくらい難しいか』を問い、誰も『そもそも真か』を問わなかった」こと
   （§NUMERIC-TRUE-ARTIFACT）。⟹ 実装が 1 行も着地する前に 4 攻撃（オーバーサンプリング / 非時間制限 /
   退化境界 2 種以上 / textbook strength diff）を通す。**UNKNOWN のまま Leg P へ進むことは禁止**。
4. **orchestrator の「オーバーサンプリングは漏れない」理由付けは 2 通りあり、片方は壁を誤輸入する（active、
   Leg 0 で決着させる）**: 「雑音が固定 `≈2WT` 次元部分空間に射影される」は **DOF カウント = 壁そのもの**を
   前提するので、これを BddAbove の正当化に使うと BddAbove が壁 gated に戻る（= 2026-07-15 の
   under-estimation 是正が生じた経路と同型）。**Leg D' の実 route はこれを要さない** —
   `bandlimited_sup_bound`（点値 sup、`@audit:ok`）+ `√(T/n)` Riemann 正規化（`:396-397` verbatim 確認済）だけで
   `E_s ≤ 2WT·(T·P)` が n 一様に出る。⟹ 正当化は **sup 境界側**を採り、部分空間次元側は採らない。
5. **crude BddAbove は rate を閉じない（active、設計上の期待値の固定）**: Leg D' の上界は
   `log M ≤ 2WT²P/N₀` で、rate `limsup_T (log M)/T ≤ 2WTP/N₀` は **T→∞ で発散**する。
   これは欠陥ではなく**期待どおり**: BddAbove（各 T で有限）は閉じるが exact 定数
   `W log(1+P/(N₀W))` には `≈2WT` DOF カウント（Leg E）が要る。**この非対称性が判断ログ #2 の判別子の実体**。
   Leg D' が rate まで閉じてしまったら循環を疑う。
6. **Proposal C（Landau-Pollak）は park、削除しない（active）**: 時間制限 + 帯域集中は LPS により忠実だが
   ripple が桁違い（`IsBandlimited` の使われ方を書き換える）。**Leg 0 が Proposal A を反証したときの撤退先**。
   Leg 0 の strength diff（攻撃 4）で「Proposal A が Wyner に着地するか」を確認し、着地しないなら本 park を起こす。
