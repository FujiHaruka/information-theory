# 棚卸し計画 — audit-2026-05

## 背景 / 動機

外部エージェントレビューで、本ライブラリ (19,054 行, 42 ファイル, Shannon 中心) について以下の懸念が提起された:

- 「Lean が通った」事実と「教科書定理を形式化した」事実の間にギャップがある可能性
- 大物定理に向かう推進力が強い一方、主定理の statement / 仮定 / 依存公理 / 再利用性が未検証
- 巨大ファイル (`ChannelCodingAchievability` 1890 行, `Stein` 1481 行, etc.) に局所補題が溜まっている可能性
- `Pinsker / PinskerSharp`, `Stein / StrongStein`, `SanovLDP / SanovLDPEquality` のような「弱形 → 強形」階段は良い兆候だが、強形の名前と実質が一致しているかは別問題

これを **数字で詰める** ことで、次の方向 (再利用テスト / statement 修復 / 完成度再格付け) を honest に選べるようにする。

## アプローチ (Approach)

- **新規証明はゼロ**。純粋な測定 + 文書化作業。修復は次フェーズに繰り越す。
- 出力は単一ドキュメント `docs/audit-2026-05.md` に集約。本プランは生成手順を定義する。
- 自動化できる部分 (grep, `#print axioms` 一括) と手作業 (statement 比較) を明確に分離。
- 各 Phase 終了で小コミット。途中で session が切れても次セッションが pickup できる形にする。
- Phase E (結論) では事前に決めた判定基準で **A / B / C 分岐** のどれに進むかを機械的に決定する。

想定工数: 1〜3 日 (実時間)、5 phase。

---

## Phase A — 静的健全性指標 (~半日)

### スコープ

機械的に取れる「ライブラリの健全性」指標を一発でカタログ化する。

### 作業

1. **sorry / admit / axiom / unsafe grep** を 1 コマンドにまとめる:

   ```bash
   rg -nw 'sorry|admit'  InformationTheory/  > /tmp/audit-sorry.txt
   rg -nw 'axiom'         InformationTheory/  > /tmp/audit-axiom.txt
   rg -nw 'unsafe'        InformationTheory/  > /tmp/audit-unsafe.txt
   rg -nw '@\[ext\]|@\[simp\]|@\[reducible\]' InformationTheory/ > /tmp/audit-attrs.txt
   ```

   - コメント内の `sorry` (記述上の言及) は除外する。`-w` で word boundary を取ってから目視で精査。
   - **撤退ライン**: 主定理ファイル (§Phase B カタログ対象) に `sorry` / `admit` が 1 つでもあれば赤旗。

2. **行数 + ファイル数の再カウント** (`Exam/` 除く)。本セッションで取った値 (19,054 / 42) と一致確認。

3. **`@[axiom]` 宣言の有無**: Mathlib 由来でないカスタム公理が宣言されていないか。

4. **`noncomputable` の出現箇所カタログ**: 形式上は問題ないが、`noncomputable def` の主定理は意味解釈に注意が必要 (例: `Classical.choice` 経由のオブジェクト)。

### 成果物

- `audit-2026-05.md` §1「静的健全性指標」: 各 grep の結果を表に集約。
  - ファイル × 残存 sorry 数 (`Phase B` カタログ対象 / それ以外)
  - カスタム axiom / unsafe / `noncomputable` 主定理のリスト

### 引き継ぎポイント

- Phase A 終了時点で `audit-2026-05.md` §1 のみコミット。
- 次の Phase B が pickup できるよう、§2 のスケルトン (見出しだけ) も同コミットに含める。

---

## Phase B — 主定理 statement カタログ (~半日〜1 日)

### スコープ

各 moonshot ファイルの「最終 theorem」を verbatim で抽出し、1 ページの主張カタログを作る。**証明本文ではなく statement のみ**。

### 抽出対象

`InformationTheory.lean` の import 順で、以下のカテゴリ別に主定理を 1〜3 本ずつ列挙:

| カテゴリ | ファイル | 探す主定理名 (推定) |
|---|---|---|
| Fano (PMF 形) | `Fano/Core.lean`, `Fano/DPI.lean` | `fano_inequality`, `condEntropy_le_after_dpi` |
| Fano (測度形) | `Fano/Measure.lean` | `fano_inequality_measure` 等 |
| Shannon 基本 | `Shannon/MutualInfo.lean`, `Shannon/DPI.lean`, `Shannon/Bridge.lean` | `mutualInfo_nonneg`, `klDiv_map_le`, `mutualInfo_eq_entropy_sub_condEntropy` 等 |
| 単発不等式 | `Shannon/MaxEntropy.lean`, `Shannon/Pinsker.lean`, `Shannon/PinskerSharp.lean` | `entropy_le_log_card`, `tvNorm_le_sqrt_klDiv`, `tvNorm_le_sqrt_klDiv_div_two` |
| Han / 組合せ | `Shannon/Han.lean`, `Shannon/HanD*.lean`, `Shannon/LoomisWhitney.lean`, `Shannon/BrascampLieb.lean`, `Shannon/Polymatroid.lean`, `Shannon/HypercubeEdgeBoundary*.lean` | `han_inequality`, `shearer_inequality`, `loomis_whitney`, `brascamp_lieb_finset`, `jointEntropySubset_submodular`, `edgeBoundary_*` |
| AEP / 漸近 | `Shannon/AEP.lean` | `aep_ae`, `aep_inProbability`, `typicalSet_*` |
| Sanov 系 | `Shannon/Sanov.lean`, `Shannon/SanovLDP.lean`, `Shannon/SanovLDPEquality.lean` | `typeClass_Qn_le`, `sanov_ldp_upper`, `sanov_ldp_equality` |
| Stein 系 | `Shannon/Stein.lean`, `Shannon/StrongStein.lean` | `stein_achievability`, `stein_lemma`, `stein_strong_lemma` |
| 符号化 | `Shannon/ShannonCode.lean`, `Shannon/ShannonCodeKraftReverse.lean`, `Shannon/Converse.lean`, `Shannon/SlepianWolf.lean`, `Shannon/ChannelCoding.lean`, `Shannon/ChannelCodingAchievability.lean` | `shannonCode_expected_length_bounds`, `exists_prefix_code_of_kraft`, `shannon_converse_single_shot`, `slepian_wolf_converse_*`, `channel_coding_achievability` |
| その他 | `Shannon/MIChainRule.lean` | `mutualInfo_chain_rule_fin`, `mutualInfo_iid_eq_nsmul` |

### 各エントリのテンプレート

```markdown
### <theorem-name> (<file>:<line>)

**Statement** (verbatim):
```lean
theorem ... :
    ... := by ...
```

**仮定** (instance / hypothesis を全列挙):
- `[Fintype α]`, `[MeasurableSingletonClass α]`, ...
- `hP : ∀ a, 0 < P.real {a}` (full support)
- ...

**結論の単位 / 形**:
- log の底: 自然対数 / log₂ / `logb D`
- entropy の単位: nats / bits / D-ary
- 確率: `Real` / `ENNReal.toReal` / `Measure.real`
- 極限: `Tendsto` / `≤ + o(1)` / `liminf ≥` / 単発不等式

**教科書対応**: Cover-Thomas Theorem X.Y.Z (該当なし = △)
```

### 作業手順

1. ファイル末尾から逆向きに「最後の `theorem` / `def` ブロック」を抽出。
   - 多くのファイルは末尾が主定理。
2. `theorem 名前 :` の行から `:= by` 直前までを verbatim で貼る。
3. statement 内の仮定 (`(h : ...)` `[Class ...]`) を残らず列挙。
4. 主定理名がコメントマーク (`## 主定理` 等) で示されている場合は **コメントの宣言** と **実際の statement** の両方を見て不一致がないか確認。

### 成果物

- `audit-2026-05.md` §2「主定理カタログ」: 上テンプレに従い 30〜50 件 (推定)。

### 引き継ぎポイント

- Phase B は最も労力が大きい。1 セッションで終わらない場合は、カテゴリ単位で commit を切る (`Fano 系完了` → push → 次セッションで Shannon 系)。
- 進捗マーカーとして §2 冒頭に「TODO: 残カテゴリ」を書いておく。

---

## Phase C — 公理依存チェック (~半日)

### スコープ

主定理が依存する公理を `#print axioms` で機械的に列挙し、想定外のカスタム公理 / `sorryAx` が紛れ込んでいないか確認する。

### 作業

1. **Audit 用 Lean ファイル** `InformationTheory/Audit/PrintAxioms.lean` を作成 (一時、コミット可):

   ```lean
   import InformationTheory

   -- Phase B カタログの主定理を全て #print axioms に通す
   #print axioms InformationTheory.Shannon.aep_ae
   #print axioms InformationTheory.Shannon.stein_strong_lemma
   #print axioms InformationTheory.Shannon.ChannelCoding.channel_coding_achievability
   -- ... (Phase B で列挙した全主定理)
   ```

2. `lake env lean InformationTheory/Audit/PrintAxioms.lean 2>&1 | tee /tmp/audit-axioms.txt` で出力を回収。

3. 出力を各定理について次の 4 区分に分類:

   | 区分 | 意味 |
   |---|---|
   | **clean** | `propext`, `Classical.choice`, `Quot.sound` のみ |
   | **with `sorryAx`** | 🚨 主定理が sorry を経由している |
   | **with custom axiom** | 🚨 カスタム `axiom` 宣言を引いている |
   | **suspicious** | `Lean.ofReduceBool` 等、解釈に注意が必要なもの |

### 成果物

- `audit-2026-05.md` §3「公理依存表」: 主定理 × 区分のテーブル。
- `InformationTheory/Audit/PrintAxioms.lean` (audit 終了後、§Phase E で削除 or 保持を判断)。

### 引き継ぎポイント

- もし Phase A で `sorryAx` を引いている主定理が見つかっていれば Phase C は確認作業に過ぎない。
- Phase C で clean でないものは Phase D の重点監査対象としてマーク。

---

## Phase D — 教科書対応 + 仮定/結論監査 (~半日〜1 日)

### スコープ

Phase B のカタログを Cover-Thomas (および対応する標準 reference) と並べ、**仮定の過剰 / 結論の弱化 / 定義のずれ** を 1 行コメントで指摘する。

### チェックリスト (主定理ごとに当てる)

レビュー指摘の項目を漏らさず適用:

- [ ] **alphabet 有限性**: `[Fintype α]` で済んでいるか、それとも `[DecidableEq α]` までで一般化されているか
- [ ] **support 条件**: `hP : ∀ a, 0 < P.real {a}` (full support) を仮定していないか。教科書は通常 full support 不要
- [ ] **KL = ∞ の扱い**: `μ ≪ ν` を仮定しているか、それとも `klDiv μ ν = ∞` の場合に bound が壊れる定式化か
- [ ] **log の底**: nats (自然対数) / bits (log₂) / D-ary (logb D)。教科書との単位整合
- [ ] **toReal 変換**: `ENNReal → Real` の変換で `⊤ ↦ 0` の落とし穴を踏んでいないか
- [ ] **i.i.d. 定義**: `Pairwise (· ⟂ᵢ[μ] ·)` + `IdentDistrib` の流儀か、`Measure.pi` 直接構成か
- [ ] **channel coding の code 定義**: blocklength `n` の `encoder : Fin M → α^n` + `decoder : β^n → Fin M` の通常形か
- [ ] **平均誤り率 vs 最大誤り率**: 主定理が claim しているのはどちらか
- [ ] **rate 定義**: `R := (log M) / n` か `M := ⌈exp(nR)⌉` か。`R < I(p;W)` の入力分布 `p` は最大化されているか
- [ ] **Tendsto 対象**: `n → ∞` の極限が `liminf ≥` / `limsup ≤` / `Tendsto` のどれか
- [ ] **Sanov の type method**: 標準的な method of types (`typeCount = n · P(a)` 厳密一致) と対応しているか
- [ ] **Fano の randomized decoder**: `decoder : Y → X` (deterministic) のみか、randomized も含むか

### 判定 3 段階

各主定理を以下のいずれかに分類:

| 判定 | 意味 |
|---|---|
| 🟢 **standard** | 教科書定理とほぼ同形 (微小な technical 仮定の差のみ) |
| 🟡 **specialized** | 仮定が強い / 結論が弱いが、明示的に scope を絞った宣言で正当化されている |
| 🔴 **weakened** | 名前が示唆する強さに statement が届いていない / 仮定が本質的に過剰 |

### 成果物

- `audit-2026-05.md` §4「教科書対応 + 仮定監査」:
  - 表 (主定理 × チェックリスト × 判定)
  - 🔴 判定の主定理について、何が問題かを各 1 段落で記述
  - 🟡 判定の主定理について、scope 宣言が plan ファイルにあるかどうかを確認

### 引き継ぎポイント

- §4 は判断を伴うので、不確実なものは「要相談」マークを付けて user に確認を仰ぐ。
- 一気に決めない。Cover-Thomas を引きながら 1 件ずつ。

---

## Phase E — 結論と次フェーズ判定 (~半日)

### スコープ

§1〜§4 の結果を集約し、事前に決めた判定基準で **分岐 A / B / C** のどれに進むかを機械的に決める。

### 判定基準 (事前固定)

| 条件 | 判定 |
|---|---|
| §3 で 🚨 が 1 件以上 **かつ** §4 で 🔴 が 5 件以上 | → **分岐 C** (完成度の正直な再格付け) |
| §3 はクリーン **かつ** §4 で 🟢 が 70% 以上 | → **分岐 A** (再利用テスト) |
| 上記いずれにも該当しない (中間ゾーン) | → **分岐 B** (statement 修復) |

### 分岐 A — 再利用テスト

- 目的: API がストレステストに耐えるか
- 次フェーズ plan: `docs/reuse-test-plan.md` を新規作成
- 候補ターゲット (1 つ選ぶ):
  1. Joint source-channel separation theorem (`ShannonCode` + `ChannelCoding`)
  2. Rate-distortion lower bound の入口
  3. n 変数 Fano + channel converse (`Converse.lean` の n 変数版)
- 着手前に「必要そうな API」を Phase B カタログから列挙し、不足を Bridge ファイルとして用意せず **既存 API だけで書けるか** を試す

### 分岐 B — statement 修復

- 目的: 🔴 / 🟡 判定の主定理を 🟢 に近づける
- 次フェーズ plan: `docs/statement-repair-plan.md` を新規作成、§4 の 🔴 リストを優先キューに
- ガードレール: 仮定を外せないことが判明したら、ファイル先頭コメントに **明示的な scope 宣言** を残し 🟡 として完了とする (隠さない)

### 分岐 C — 完成度の正直な再格付け

- 目的: moonshot 完成済リスト (`docs/moonshot-seeds.md` 等) と実態の整合
- 次フェーズ plan: `docs/recalibration-plan.md` を新規作成
- 作業: 各 moonshot の seed-card に「completed (strong form)」/「completed (weak form, scope 限定)」/「partial」/「skeleton only」のラベルを付け直す

### 成果物

- `audit-2026-05.md` §5「結論」:
  - §1〜§4 の数値サマリ (1 段落)
  - 分岐判定 (A / B / C のいずれか) と判定根拠
  - 次フェーズ plan ファイルへのリンク
- 上記分岐に応じた新規 plan ファイル 1 本のスケルトン (Phase E 内で作成)

---

## 終了条件 (Definition of Done)

- [ ] `docs/audit-2026-05.md` の §1〜§5 が全て埋まっている
- [ ] §5 で分岐 (A / B / C) が決定し、次フェーズ plan ファイルが新規作成されている
- [ ] Phase C の `InformationTheory/Audit/PrintAxioms.lean` の保持/削除を判断 (clean なら削除、suspicious が残るなら保持)
- [ ] 主要 commit がすべて push 済み

## ガードレール (やらないこと)

- **新規の補題 / theorem を書かない**。Phase D で 🔴 が見つかっても、修復は次フェーズ。
- **statement の書き換えをしない**。Phase D で仮定の過剰さに気づいても、現物の `InformationTheory/` には触らず `audit-2026-05.md` にメモするだけ。
- **大ファイル分割をしない**。これは別の方向で、棚卸し後に判断する。
- **新しい moonshot を始めない**。棚卸し中に「これは next moonshot 候補」と気づいても、別 plan ファイル (`docs/audit-2026-05-followups.md`) に書き留めるだけ。

## セッション間引き継ぎ用チェックリスト

次セッションで `/resume` から再開する想定:

```
[ ] Phase A: 静的健全性指標
[ ] Phase B: 主定理 statement カタログ
    [ ] Fano 系
    [ ] Shannon 基本 + 単発不等式
    [ ] Han / 組合せ
    [ ] AEP / Sanov / Stein
    [ ] 符号化
[ ] Phase C: 公理依存チェック (#print axioms)
[ ] Phase D: 教科書対応 + 仮定監査
[ ] Phase E: 結論と分岐判定
```

`.claude/handoff.md` に「現在の Phase」と「未完了サブカテゴリ」を残す。
