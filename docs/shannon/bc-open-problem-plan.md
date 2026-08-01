# 一般 BC の計算可能な容量領域 — 攻略の進め方 (メタプラン)

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md)

**Status**: 進め方の設計のみ。数学の attack は未着手。
**Branch**: `bc-computable-region`
**この文書の射程**: 「未解決問題に長期 relay で挑むとき、途中で諦めず、かつ嘘をつかずに、何をどの順で
回すか」という**運用の設計**。個々の attack の中身は attack ledger
([`bc-open-problem-attacks.md`](bc-open-problem-attacks.md)) が SoT で、確定事実は
[`bc-facts.md`](bc-facts.md) が SoT。本文書はこの 2 つに何をどう積むかを決める。

---

## 1. 現在地

### 1.1 文献側のランドスケープ (2026-08-01、WebSearch / WebFetch で一次確認)

| # | 事実 | 出典 | 我々への含意 |
|---|---|---|---|
| F1 | 一般 2 受信者 DM-BC の容量領域は未解決 | 定説 (EGK Ch.8) | 本丸 |
| F2 | 最良既知 inner = Marton (共通補助 `U₀` 付き) | Marton 1979 / EGK Thm 8.4 | 在庫は `U₀` 無し版 |
| F3 | 最良既知 outer = Nair–El Gamal (UV) | Nair–El Gamal 2007 | 在庫は全平面版で保有 |
| F4 | **inner ≠ outer** — BSSC で sum rate にギャップ (inner を明示評価せずに分離を示す情報不等式) | Jog–Nair, *An information inequality for the BSSC broadcast channel* (ISIT 2010) | **「inner = outer」を証明する路線は死んでいる** |
| F5 | **NEG outer は真に緩い** — 逆向き semi-deterministic 2 成分の積 BC で strictly suboptimal | Geng–Gohari–Nair–Yu, *On Marton's inner bound and its optimality for classes of product broadcast channels* | **「outer = capacity」路線も死んでいる** |
| F6 | binary input BC では randomized time-division が Marton の sum rate を達成 | Geng–Gohari–Nair–Yu 2013 (arXiv:1001.1468) | inner の**限界**を測る道具 |
| F7 | 単一文字特徴付けを一階論理で厳密化。独立性関係のみの理論が真の算術を解釈 ⟹ 決定不能。`linear entropy hierarchy` で特徴付けを論理的複雑さで階層化 | Cheuk Ting Li, arXiv:2108.07324 | 「**計算可能な特徴付け**」を*定義する*ための唯一の既存枠組み |
| F8 | 通信路容量の算法的計算可能性 (FSC / ACGN / capacity-achieving input) には否定的結果が続々。**BC の容量領域の計算可能性は未決** | Boche–Schaefer–Poor 系 | **否定的解決が現実的な標的になりうる** |

⚠ この表は現時点では `human-judgment`。**着手前に各行を原論文で verbatim 確認する (Leg 0)**。特に F4 /
F5 は「どの bound の、どの成分が、どのチャネルで分離するか」を取り違えると、以後の attack が丸ごと
空振りする。数値 (BSSC の sum rate 値など) は記憶から書かない — 原論文の値を引いて `bc-facts.md` に載せる。

### 1.2 在庫側 — 手元にあるもの

未解決問題の**両端が機械検証された形で 1 つのライブラリに並んでいる**のは、おそらく世界的にも他に例が
ない。ここが我々の唯一の構造的優位で、攻め口の設計はすべてこれを軸にする。

- 主語: 操作的容量領域 `bcCapacityRegion` (`BroadcastChannel/Operational.lean`)
- 外界: `bc_capacity_subset_uv` (全平面版、明示仮説は `W` + `[IsMarkovKernel W]` のみ)
- 内界: `marton_achievability` (無条件、private only) / `bc_achievability_of_rate_lt` (superposition)
- 橋: `marton_region_subset_uv`
- 等号クラス: degraded / less noisy / more capable の 3 本 (`Superposition/MoreCapable.lean` ほか)
- 反証基盤: `bc-marton-union-gap-check.py` — **Lean の `def` と逐語照合した数値 sim で「逆包含は偽」を
  実際に判定した実績がある** (bc-facts.md、判断ログ 18)
- 家系全体で新規 `sorry` 0 / `@residual` 0 / custom axiom 0

---

## 2. Approach

**三層 × 階段 × 台帳**。

### 2.1 三層 — 「散文 → 形式化」の間に proof-probe を挟む

ユーザー指定の二段構え (散文で証明 → 形式化で検証) を、実際に回る形に具体化すると **3 層**になる。

```
層 1  散文        アイデア + 証明スケッチ (自然言語 + 数式)
層 2  proof-probe 核 1〜2 ステップだけを機械検証 (Lean の小補題 or 数値 sim)   ← 新設
層 3  形式化      散文全体を Lean へ
```

**層 2 が本設計の心臓**。未解決問題における最大のリスクは「散文で証明できた気がする」であり、層 1 から
層 3 へ直行すると、誤りに気づくのが数 leg 先になる (= 諦めが発生する典型的な地点)。層 2 は「その散文が
主張の核として何を要求しているか」を 1 leg 以内で機械に問い合わせる装置で、
**証明が通れば核が正しい / 通らなければ核の場所が特定される**のどちらかが必ず得られる。

層 2 の 2 形態:

- **Lean probe** — 核ステップを最小の補題として書き、`lake env lean` に問う。既存の内界/外界定理を
  hypothesis として与えてよい (完全性は層 3 の仕事)。
- **数値 probe** — 命題を有限アルファベットの数値最適化に落として反例を探す。`bc-marton-union-gap-check.py`
  が完成した先例。**sim は必ず Lean の `def` と逐語照合してから信用する** (CLAUDE.md 検証の誠実性)。

### 2.2 階段 — 本丸に直行しない

未解決本体だけを目標にすると「解けない = 成果ゼロ」になり、それが諦めの唯一最大の原因になる。
**どこで止まっても成果が残る**よう、独立に価値を持つ 4 段に割る (§3)。

### 2.3 台帳 — 失敗を資産に変える

試した attack は死んだものも全部 attack ledger に残す。**死因の分類**まで書くのが要点で、「数値反例で
死んだ」「既知だった」「単に難しい」は次の一手が全く違う。台帳がないと長期 relay は同じ壁に何度も
当たり、そこで「もう無理だ」という誤った確信が生まれる。

---

## 3. ターゲットの階段

| 段 | 内容 | 完了条件 | 価値 |
|---|---|---|---|
| **T0** | ギャップの機械可読な固定 | `bcCapacityRegion` を内外で挟む形が 1 ファイルに揃い、「一致は未解決」が**署名として読める** | 在庫でほぼ達成済。残りは配線 |
| **T1** | **既知の負の結果**の形式化 | F4 (BSSC のギャップ) または F5 (NEG の suboptimality) のいずれかが Lean で機械検証される | 新規数学ではないが**形式化としては世界初**。層 2 の道具立てがここで揃う |
| **T2** | **人類未知の中間結果** ← 本命 | §4 の軸のいずれかで、文献に無い命題が Lean で機械検証される | 論文になる。ここが現実的な到達目標 |
| **T3** | 未解決本体 | 一般 BC の計算可能な特徴付け (肯定 or 否定) | 30 年級。狙うが期待値は置かない |

**期待値の置き方**: T1 を確実に、T2 を本命に、T3 を狙う。この順で「必ず何かが残る」。

---

## 4. 攻撃軸 — 未知の中間結果の候補

各軸に (a) 狙い / (b) 形式化プロジェクトゆえの優位 / (c) 最初の一手 / (d) 収穫ライン (死んだときに残るもの)
を書く。**単一の軸に賭けない** — §5-5 のラウンドロビン規約で強制的に回す。

### 軸 A — 在庫駆動の最弱仮説抽出 (優先度 1)

- **狙い**: 既に証明済の等号定理が**実際に使っている仮説**を最小化し、既知クラスより真に広いクラスを
  切り出す。親 plan の記録によれば `bc_moreCapable_uv_subset_superposition` の「唯一の新しい数学の核」は
  `IsBCMoreCapable.condMutualInfo_le` 1 本 = **証明はクラス定義そのものではなくその帰結 1 本しか
  使っていない可能性が高い**。ならばその帰結を定義に採ったクラスで同じ等号が成立する。
- **優位**: 「証明が本当は何を使ったか」は散文の論文からは読めない。**Lean は仮説を差し替えて
  `lake env lean` に問える** — これは形式化プロジェクトだけが持つ発見手段。
- **最初の一手**: `IsBCMoreCapable` を `condMutualInfo_le` の結論そのものに差し替えて再コンパイル。
  通れば新クラスで定理成立。次に「真に広いか」を数値 probe で判定 (条件付き版を満たすが more capable
  でないチャネルを探す)。既知クラス (essentially less noisy 等) との包含関係を文献照合。
- **収穫ライン**: 新クラスが既知クラスと一致しても、**「等号の必要十分に近い形」を機械検証で特定した**
  という結果が残り、軸 B の入力になる。

### 軸 B — 外界の緩みの局所化 (優先度 2)

- **狙い**: F5 より、NEG outer は真に緩い。ならば `bc_capacity_subset_uv` の証明の**どこで捨てたか**を
  特定し、捨てた項を拾って新しい outer bound を作る。
- **優位**: 証明が Lean にあるので「不等式を緩めた箇所」が構文的に列挙できる (`Csiszár sum identity` の
  適用点、`le_trans` の各段)。散文の論文では追跡できない粒度。
- **最初の一手**: `bc_uv_converse` / `bc_capacity_subset_uv` の証明本体で、等号でなく不等号を使っている
  ステップを全列挙し、各ステップについて「等号成立条件」を書き出す。すべてのステップが同時に等号に
  なるチャネルが F5 の反例と両立するかを数値で確認。
- **収穫ライン**: 新 bound が出なくても、**「NEG の緩みはこのステップに局在する」という機械検証された
  診断**が残る。これ自体が文献に無い。

### 軸 C — 情報不等式 (優先度 3)

- **狙い**: F4 の Jog–Nair 不等式の形式化 (T1) を踏み台に、新しい情報不等式を探す。
- **優位**: 情報不等式は有限の変数と有限の項からなるので、**Lean での検証と数値での反証の両方が効く**
  数少ない領域。当てずっぽうの不等式を大量に数値で殺してから、生き残ったものだけ証明に投資できる。
- **最初の一手**: Jog–Nair 不等式を Lean で述べる (証明は後)。数値 probe で成立を確認 → 形式化。
- **収穫ライン**: 不等式ライブラリ。他の多端子問題 (MAC / Han) にも効く。

### 軸 D — 「計算可能な特徴付け」の定式化 (優先度 1、T3 への唯一の現実的な橋)

- **狙い**: ユーザーの標的そのもの。F7 (Li の一階論理版) を Lean の型に落とし、
  **「`bcCapacityRegion W` が単一文字特徴付けを持つ」という命題自体を形式的に述べる**。述べられれば、
  肯定 (構成) と否定 (計算不可能性) の両方向が同じ主語の上で議論できる。
- **優位**: 我々は**操作的定義から出発している** — `bcCapacityRegion` は符号と誤り確率で定義されており、
  bound で定義されていない。「特徴付けが存在するか」を問う主語として正しい形を既に持っている。
  文献側は多くが bound を主語にしているため、この問いを formal に書けない。
- **最初の一手**: (1) multi-letter 表現を Lean で構成し `bcCapacityRegion` と一致することを証明する
  (既知だが形式化は未踏。かつ**計算可能性を論じる主語**になる)。(2) 「単一文字特徴付けを持つ」の
  Lean 上の定義候補を 2〜3 個書き、Li の hierarchy のどの層に対応するかを対応付ける。
- **収穫ライン**: 定式化だけでも未踏。F8 が示すとおり BC の計算可能性は未決なので、
  **否定的解決 (計算不可能性) は Boche 流の構成の移植で届く可能性がある** — T3 への最も現実的な橋。

### 軸 E — 積 BC とテンソル化 (優先度 3)

- **狙い**: F5 の反例は積 BC。additivity / non-additivity は形式化と相性が良い (2 つのチャネルの積は
  Lean で構成できる)。新しい非加法性の例を作れれば中間結果。
- **収穫ライン**: 積 BC の構成 API。

### 軸 F — 補助変数の濃度境界 (優先度 4)

- **狙い**: cardinality bound の改善。**ただし Fenchel–Eggleston が Mathlib 不在** (既存 plan の記録)
  なのでコストが高い。他の軸が全滅したときの予備。

---

## 5. 運用規約 — 「諦めない」を仕組みで担保する

諦めが起きるのは (i) 進捗の実感が無い (ii) 何を試したか忘れる (iii) 同じ失敗を繰り返す、の 3 つ。
以下はそれぞれへの構造的対処で、**すべての leg のブリーフに本節への参照を入れる**。

1. **no empty leg — 進捗の単位は「証明の完成」ではなく「確定事実 1 行」**
   各 leg は attack ledger または `bc-facts.md` に**最低 1 行の新しい確定事実を追加して終わる**。
   反証も、死因の特定も、「この route は既知だった」も、すべて確定事実。証明の完成だけを進捗と
   定義すると、未解決問題では 10 leg 連続でゼロ進捗になり、そこで必ず諦めが起きる。

2. **kill-first — 反証ファースト**
   候補命題を立てたら、**まず数値 probe で殺しにいく**。証明に投資するのは殺せなかった命題だけ。
   既存の `bc-marton-union-gap-check.py` が先例で、実際に 1 本の逆包含を殺して路線変更を導いた。
   これは時間の最大の節約であると同時に、自己欺瞞に対する最大の防波堤。

3. **proof-probe — 核だけ先に機械検証** (§2.1 層 2)
   散文が完成する前に、核 1〜2 ステップを Lean か数値で検証する。散文全体の形式化は最後。

4. **attack ledger — 探索木の永続化**
   1 attack = 1 行。列 = slug / 軸 / 状態 (`live` / `killed` / `parked` / `harvested`) / **死因**
   (`numeric-counterexample` / `known-result` / `probe-failed` / `too-hard` / `mathlib-wall`) /
   残った副産物 / 最終更新 leg。`killed` の行は**削除しない** (plan hygiene の「決着済は削除」の例外 —
   ここでは死因そのものが資産)。

5. **round-robin — 軸の強制切替**
   1 つの軸で **3 leg 連続で確定事実がゼロ**なら、その軸を `parked` にして別の軸へ移る。同じ思考
   パターンの周回を構造的に止める。park した軸は 3 leg 後に再検討可 (新しい確定事実が入っていれば)。

6. **harvest line — 撤退ラインではなく収穫ライン**
   通常の撤退ラインは「詰んだら諦める」だが、未解決問題では**詰んだときに何を収穫して撤退するか**を
   事前に書く (§4 の各軸 (d))。これがあると「失敗」が「別の成果」に変わり、諦めではなく移動になる。

7. **novelty gate — 新規性主張の前に文献確認**
   「未知の結果を得た」と書く前に、必ず文献確認を 1 手挟む (WebSearch + 該当論文の verbatim 確認)。
   既知結果の再発見を新規と誤認するのは、長期セッションで最も起きやすく最も高くつく事故。
   ⚠ 逆向きの事故もある — **「既知だろう」で切り捨てる**。in-repo 資産の見落としと同じ構造 (CLAUDE.md
   「Search in-project before concluding 絶対」)。既知判定にも出典を要求する。

8. **anti-self-deception — 散文にも honesty doctrine**
   CLAUDE.md の Lean 側 doctrine を散文へ移植する:
   - 散文の各補題に「その仮説は precondition か load-bearing か」のラベルを付ける。
     **核を仮説に押し込んだ散文証明は、Lean の hypothesis bundling と同じ defect**。
   - 「〜は明らかに成り立つ」「同様にして」は**その場で層 2 の probe 対象**として台帳に起票する。
     散文における `sorry` はこの 2 つの言い回しの形で現れる。
   - 数値実験で FALSE を判定するときは、sim を実 `def` と逐語照合してから。

---

## 6. relay の leg 設計

- **1 leg = 1 attack の 1 ステップ**。複数 attack を 1 leg に詰めない (台帳の粒度が壊れる)。
- **leg の終わりに必ず**: 台帳更新 → `bc-facts.md` 更新 (あれば) → handoff。
- **cap は高め** (未解決問題なので 20 leg 級を想定)。ただし §5-5 のラウンドロビンが効くので、
  同じ場所で 20 leg 回ることはない。
- **サブエージェント同時 1 体**を厳守 (CLAUDE.md)。
- **handoff に必ず書く 3 点**: 現在の軸 / その軸の連続ゼロ進捗カウント / 次の 1 手。
- **層 3 (完全形式化) に入るのは T2 の命題が層 2 を通過してから**。通過前に形式化を始めない。

---

## 7. 最初の 3 leg

| leg | 内容 | 完了条件 |
|---|---|---|
| **L0** | **文献ランドスケープの verbatim 確定** — §1.1 の F1–F8 を原論文で確認し `bc-facts.md` へ。特に F4 / F5 の「どの bound の何が、どのチャネルで分離するか」と、F7 の hierarchy の定義を正確に取る | F1–F8 が出典 + 確認方法つきで台帳に入る。attack ledger の初期版が立つ |
| **L1** | **軸 A の第一手** — `bc_moreCapable_uv_subset_superposition` が実際に使っている `IsBCMoreCapable` の帰結を特定し、仮説を最弱形に差し替えて再コンパイル | 「差し替えて通る / 通らない」が機械検証で確定。通れば新クラス候補が 1 本立つ |
| **L2** | **軸 D の第一手** — multi-letter 表現を Lean で構成し `bcCapacityRegion` との一致を述べる (証明は次 leg 以降でよい)。同時に「単一文字特徴付けを持つ」の定義候補を 2〜3 個書き出す | 主語が Lean 上に立ち、T3 の問いが**形式的に述べられる**状態になる |

L0 は必須の先行 leg (ここを飛ばすと以後の attack が空振りする)。L1 と L2 は独立なので順序は入れ替え可。

---

## 8. 成果物と置き場

| 成果物 | 置き場 | SoT |
|---|---|---|
| 進め方 (本文書) | `docs/shannon/bc-open-problem-plan.md` | 運用設計 |
| attack 台帳 | `docs/shannon/bc-open-problem-attacks.md` | 個々の attack の状態・死因 |
| 確定事実 | `docs/shannon/bc-facts.md` (既存に追記) | 文献事実・数値判定・機械検証 |
| 数値 probe | `docs/shannon/bc-*-check.py` | 反証実験 |
| 散文証明 | `docs/shannon/bc-open-problem-draft.md` (T2 に入ってから作る) | 層 1 |
| Lean | `InformationTheory/Shannon/BroadcastChannel/` 配下 | 層 2 / 層 3 |

---

## 9. 判断ログ

(空。leg が進むごとに追記。plan budget = 600 行 / active 決定 10 件を超えたら `/compact-plan`)
