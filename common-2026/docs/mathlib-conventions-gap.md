# Mathlib 慣習との実測ギャップ分析

`linter` では捕まらない「明文化されていない慣習」を、`.lake/packages/mathlib`
(commit `043e9e0413`, 8023 files) を実際に観察して言語化し、本プロジェクト
(`InformationTheory/`, 269 files / ~118k lines) と機械実測で突き合わせた結果。

> 数値は調査時点 (2026-06-13) のスナップショット。再導出が安価なものは prose にキャッシュせず、
> 末尾の「再実測コマンド」で取り直すこと (settled-facts と同じ方針)。

## TL;DR — 最大のギャップは「証明粒度」

Mathlib の最大の暗黙規律は **1 宣言の footprint を小さく保ち、長くなったら名前付き補題に分解する** こと。
IT+Probability サブツリー全体で、theorem/lemma 1 件が占める行数 (docstring+signature+proof) は
**中央値 7 / 最大 115 行、150 行超はゼロ**。本プロジェクトは **中央値 26 / 最大 907 行、150 行超が 76 件**。
モノリシックな巨大証明 (e.g. `continuousAepGaussian_holds` ≈ 501 行) を named helper lemma に
割らないことが、Mathlib との一番大きな構造的乖離。

---

## 1. 観察された Mathlib の慣習 (実測値つき)

### 1.1 ファイル = 1 概念、しかも小さい

- 全体のファイル行数: 中央値 **185** / p90 638 / p99 1257 / 最大 **1523**。
- Mathlib 自身の `InformationTheory/` は 57–412 行 (KraftMcMillan 167, KLFun 194, Basic 389, Hamming 412)。
- ファイル名は **数学的概念**: `Hamming.lean` / `KraftMcMillan.lean` / `ChainRule.lean` / `SetAlgebra.lean`。
  開発プロセスや進捗段階を名前にしない。
- 宣言順序は「型定義 → 基本性質 → 派生 → API」。`section`/`namespace` で論理的に区切り、
  `variable` ブロックで共有仮説を一度だけ宣言して各補題で繰り返さない
  (e.g. `Hamming.lean:37` `variable {α ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]`)。

### 1.2 証明は小さく、超えたら割る

- 宣言 footprint (連続する theorem/lemma 宣言間の行数を proxy): IT+Prob で
  中央値 **7** / p90 20 / p99 48 / **最大 115**。35 行を超える証明は稀で、超えると helper lemma に分解。
- 例: `Probability/BorelCantelli.lean` は 6–7 行の小補題 3 本
  (`iIndepFun.indep_comap_natural_of_lt` 他) を積み上げて payoff `measure_limsup_eq_one` (35 行) に至る。
- `have A : ...` / `have B : ...` で中間ゴールに名前をつけ、`calc` を 1 ステップ 1 行で整列。
- term-mode 1 行証明も多用 (`SetAlgebra.lean:67` `compl_empty ▸ h𝒜.compl_mem h𝒜.empty_mem`)。

### 1.3 ヘッダ・ドキュメント

- **Copyright/License/Authors ヘッダがほぼ全ファイルに存在** (sample 300 で 289)。
- module doc `/-!` テンプレートが定型: `# Title` → `## Main definitions` → `## Main results`
  → `## References` (+必要に応じ `## Implementation notes`)。本文は **英語**。
- `@[simp]`/`@[deprecated NewName (since := "DATE")]`/`protected`/`@[refl]` 等を規律的に使う。

### 1.4 private と docstring 密度 (直感に反する実測)

- **private はほとんど使わない**: Mathlib 1500 ファイルで private は 519 / 全 40346 = **1.3%**。
  細かく割った補題は**ほぼ public** で残す (「小補題 = 再利用 API」)。private は本物の実装詳細のみ。
  本プロジェクトは 363 / 2364 = **15.4%** (~12 倍)。
- **docstring は API 表面だけ**: Mathlib は宣言の **~17–20% しか docstring を持たない**
  (Probability pub 20% / Analysis.SpecialFunctions pub 17%)。付くのは主に **def と headline 定理**で、
  支える補題群は**裸** — 名前とモジュール doc が意味を担う (docBlame linter は def に要求、theorem/lemma に要求しない)。
  本プロジェクトは private 含め **~94% を文書化** = 大幅な過剰文書化。
  この過剰 docstring が Phase/判断/audit といったプロセス語彙の漏入経路になっている (§3-A-3 と直結)。
- **aux/step 命名**: `aux1/aux2` 式の機械的連番は 0 件 (gaming パターンは現状なし)。
  `XxxAux` は名前付き補助関数 + ちゃんと命名された補題族 (Huffman/LZ78) で許容範囲。
  本物の smell な補助補題 (`*_aux`) は 5〜6 件のみ。

### 1.5 命名

- def は lowerCamelCase (`hammingDist`)、定理は snake_case (`hammingDist_eq_zero`)、型/構造は PascalCase。
- 名前が結論の形を表す: `_of_` (仮説)、`_iff_`/`_eq_`/`_le_`/`_ne_`、`_self`/`_comm`/`_assoc`。
  `eq_of_hammingDist_eq_zero` のように左辺=結論主辞。

---

## 2. 本プロジェクトの実測値 (同じ尺度)

| 指標 | Mathlib | 本プロジェクト |
|---|---|---|
| ファイル行数 中央値 / 最大 | 185 / 1523 | 322 / **3522** |
| 宣言 footprint 中央値 / 最大 | 7 / 115 | **26 / 907** |
| footprint > 150 行 | **0** | **76** |
| Copyright ヘッダ | ~96% | **2 / 269 (<1%)** |
| module doc `/-!` | ~97% | **97% (262/269)** ← 良好 |
| `protected` | 随所 | **0** |
| `private` | 選択的 | 391 |

- 最大の単一証明: `InformationTheory/Shannon/AWGN/Walls.lean:788–1289` の
  `continuousAepGaussian_holds` ≈ 501 行 (named helper への分解なし)。
- 1200 行超のファイルが 15 本 (`Walls.lean` 3522, `AchievabilityDischarge.lean` 2084,
  `ConverseDischarge.lean` 1861, …)。

---

## 3. ギャップ (ランク付け)

### A. 閉じるべき真のギャップ (品質 / upstream 性に効く)

1. **証明粒度 (最重要)** — 150 行超の宣言 76 件 / 最大 907 行。Mathlib なら named helper lemma
   (3–10 行) に割って main theorem を 20–35 行に収める。`continuousAepGaussian_holds` /
   `awgnPowerConstraintPerCodeword_holds` (≈438 行) が筆頭。
2. **ファイルサイズ・概念集中** — 1200 行超 15 本。1 ファイル 1 概念へ。
3. **プロセス語彙の永続記録への混入** — file 名 `Walls.lean` / `*Discharge.lean`、
   docstring 中の `Phase A/B/C`、`Wall N`、`判断 #2`、`Retraction log`、audit trail。
   Mathlib の永続ドキュメントは **数学だけ** を語り、開発プロセス (control state / 決定履歴) は語らない。
   本プロジェクトの CLAUDE.md が plan に対して禁じている「control state / decision history /
   settled facts の混在」が、コード docstring 側で起きている。
4. **Copyright/License ヘッダ欠如** (2/269) — 機械的に付与可能。upstream には必須。
5. **module doc が自由形式** — doc を書く習慣はある (97%) が、Mathlib テンプレ
   (Main definitions / Main results / References) ではなく `## 構成` / `## 設計メモ` で日本語。
   構造を寄せれば習慣はそのまま活きる。
6. **ファイル名がプロセス由来** — 概念名へ (`Walls` → 各 Wall の数学的対象名へ分割等)。

### B. 意図的なプロジェクト基盤 (Mathlib に「揃える」対象ではない)

- `sorry` (~326 行が言及) + `@residual(...)` (64) + `@audit:*` — honesty 規律のスキャフォールド。
  完成度の指標であって style ギャップではない。upstream 時に剥がすもの。
- `@[entry_point]` (709) — dep ツール用の独自メタ。upstream には残らないが開発中は有用。

これらを「Mathlib にないから消す」のは誤り。A と混同しないこと。

### C. 直感が外れた「folk 慣習」(実測で否定 — 追いかけない)

- ❌ **「Mathlib は bare `simp` を使わず `simp only` だけ」**: 逆。実測で Mathlib は
  bare `simp` 4472 : `simp only` 1464 ≈ 3:1 で bare 優勢。本プロジェクトは 871 : 758 ≈ 1:1 で、
  むしろ `simp only` 比率が高い。**ここはギャップではない**。
- ❌ **「Mathlib は `<;>` を避ける」**: 逆。Mathlib は 500 ファイルで 437 回多用、本プロジェクトは
  全体で 18 回と希少。`<;>` を避ける規律は存在しない。
- 教訓: 「読みやすさ系の禁則」は観察で容易に誤認する。linter 化する前に必ず実測で確認する。

---

## 4. 推奨アクション (優先順)

**閾値アンカーは Mathlib p99 = 48 行から開始** (2026-06-13 決定)。48 は固定キャップではなく
「ここに再利用可能な補題が埋まっていないか見ろ」の診断トリガー。裾カウント (>48 / >115) を
追跡指標として持ち、中央値を 7〜10 へ寄せる。pre-commit での弱い enforcement は大規模リファクタ後に判断。

1. footprint の裾を棚卸しし named lemma へ分解 (>250 の 16 本 → >115 の 137 本 → 49–115 は機会主義的)。
   まず `ConditionalMethodOfTypes/Mass.lean:318` (907)・`AWGN/AchievabilityDischarge.lean:515` (684)・
   `EPI/G2/ConvEntropyDensity.lean:117` (629)。proof done と独立に進められる純リファクタ。
   **抽出補題は Mathlib 流に「public + 記述的命名 + docstring なし」** とする (§1.4: 現状の
   private 15.4% / docstring 94% は逆方向)。新規 `_aux` 補題は作らない (名前で事実を語らせる)。
2. 1200 行超 15 ファイルを概念単位に分割。`Walls`/`*Discharge` を数学的概念名へ改名。切るのは概念の継ぎ目。
3. **Copyright ヘッダは保留**: ad-hoc な 2 ファイル (`MinkowskiDet` / `CondKLIntegral`) は 2026-06-13 に削除済
   (実 author 名義がなく文面も不統一だった)。upstream 化の段で author を確定してから全ファイル一括付与する。
4. module doc を Mathlib テンプレへ寄せ、Phase/Wall/判断/Retraction といった**プロセス語彙を
   docstring から plan/handoff 側へ移す** (コードは数学だけ語る)。過剰 docstring も Mathlib 水準へ間引く。
5. `<;>`/bare `simp` は現状維持 (ギャップではない)。

---

## 再実測コマンド

```bash
ML=.lake/packages/mathlib/Mathlib
# 宣言 footprint 分布
measure() { find "$1" -name '*.lean' | while read f; do
  grep -nE '^(@\[[^]]*\] *)?(private |protected |noncomputable |public )*(theorem|lemma) ' "$f" | cut -d: -f1; echo "---$f"
done | awk '/^---/{prev=0;next}{if(prev>0)print $1-prev;prev=$1}'; }
measure InformationTheory | sort -n | awk '{a[NR]=$1}END{print "median="a[int(NR/2)],"p90="a[int(NR*0.9)],"max="a[NR]}'
{ measure "$ML/InformationTheory"; measure "$ML/Probability"; } | sort -n | awk '{a[NR]=$1}END{print "median="a[int(NR/2)],"max="a[NR]}'
# bare simp vs simp only / <;>
find InformationTheory -name '*.lean' | xargs grep -hoE '\bsimp\b( only)?' | sort | uniq -c
# ファイルサイズ
find InformationTheory -name '*.lean' | xargs wc -l | sort -rn | head
```
