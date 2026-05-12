# 再利用テスト計画 — reuse-test-2026-05

## 背景 / 動機

`docs/audit-2026-05.md` Phase E で **分岐 A (再利用テスト)** を選定。本計画は次フェーズの
具体ターゲットと手順を定義する。

- audit 結果: 静的健全性 + 公理依存ともに完全クリーン、🟢 81.6% (40/49)、🔴 = 0。
- 目的: 既存 API がストレステストに耐えるかを「**新規 bridge 補題ゼロ**」を制約に検証する。
- 失敗 (bridge が必要だった) 場合は、その箇所を次々フェーズの statement 修復 (分岐 B) の
  優先キューに加える。

## アプローチ (Approach)

**Mathlib-shape-driven** 原則を再利用 phase にも適用する:

1. ターゲット定理の statement を先に書く。
2. その statement を証明するために最も自然な API 利用順を **既存カタログから列挙** する。
3. 必要そうな bridge を **絶対に書かない**。bridge が要ると判明した時点で記録し、ターゲットの
   形を bridge を回避する方向に修正できないか試す。
4. 修正不能なら「bridge 候補リスト」に追加して終了 → 修復 phase に渡す。

新規定義 / 補題 / theorem は **最大 1 本** (最終ターゲット theorem のみ) に絞る。

---

## ターゲット選定

3 案 (audit §5.4) より **#3 (Channel coding converse, n-variable Fano scaled)** を採用。

### 選定理由

- audit で 🟡 を付けた `shannon_converse_single_shot` (uniform input only) と
  `channel_coding_achievability` (fixed p, average error) の **converse 側 n-variable 化**は、
  既存 4 API:
  - `Shannon.shannon_converse_single_shot` (Converse.lean:81)
  - `Shannon.mutualInfo_chain_rule_fin` (MIChainRule.lean:117)
  - `Shannon.mutualInfo_iid_eq_nsmul` (MIChainRule.lean:392)
  - `MeasureFano.fano_inequality_measure_theoretic` (Fano/Measure.lean:224)

  を **そのまま合成** することで書けるはず。
- 既存 API の "i.i.d. 入力 + chain rule + Fano measure 形" 連携が無傷で機能するかを検証する
  純粋テスト。
- 🟡 "uniform input" 仮定が n-channel スケーリングで本質的か否かを判定可能 →
  分岐 B 修復計画への直接フィードバック。

### ターゲット statement (案)

```lean
/--
**Channel coding converse, n-variable form (with uniform input).**
任意の (n, M)-block code に対し、メッセージを一様分布で送る場合、
average error probability が小さければ rate `(log M)/n` は `I(p; W)` 以下である。

形式: `Real.log M ≤ n * I(p; W) + n · binEntropy(P_e) + n · P_e · log(M-1)` の n 変数 Fano 形。
-/
theorem channel_coding_converse_iid
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {M n : ℕ} [NeZero M] [NeZero n]
    (Msg : Ω → Fin M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (decoder : (Fin n → β) → Fin M)
    -- (一様メッセージ + i.i.d. 入力 + チャネル使用 の仮定群)
    -- 結論: (1/n) log M ≤ I(p; W) + binEntropy(P_e)/n + P_e · log(M-1)/n
    : ... := by
```

詳細な仮定列挙は実装時に確定。

---

## 作業フェーズ

### Phase 1 — API 表面確認 (~半日)

- 上記 4 API の signature を verbatim で並べる。
- ターゲット statement が、これら 4 API の合成 (compose) だけで導けるかペーパー証明をスケッチ。
- bridge 候補が出てきたら記録 (まだ書かない)。

成果物: `docs/reuse-test-2026-05.md` (新規) §1「ペーパー証明」。

### Phase 2 — Lean 化試行 (~1〜2 日)

- ターゲット theorem 1 本を `Common2026/Shannon/ChannelCodingConverse.lean` (新規) に skeleton で
  書く。
- `:= by sorry` 状態でまず compile 通過を確認 (signature 妥当性)。
- 各証明 step を埋める。**新規 lemma ゼロ**が制約。
- 詰まった step は `← bridge_X` とコメントで印を付けて先送り (bridge 候補)。

成果物: ファイル 1 本 + bridge 候補一覧 (§2)。

### Phase 3 — 結果記録 (~半日)

- 完成した場合: 「再利用テスト合格」を §3 に記載、本ライブラリの API が n-channel converse
  まで bridge-free で到達することを確認。
- 不完成の場合: bridge 候補一覧を分岐 B (statement 修復) plan に転記、何が API の弱点だったか
  分析。

成果物: §3「結論」。

---

## ガードレール (やらないこと)

- **新規補題を書かない**。Phase 2 で bridge が必要と判明したら、即座にターゲット側を修正できる
  か試す。それでも詰まったら記録のみ。
- **既存 API の statement を書き換えない**。"uniform input" scope を外したくなったら、本計画は
  中断、分岐 B (statement 修復) を先行させる。
- **複数ターゲットを同時に並走しない**。1 ターゲットの限界を見極めてから次へ。

---

## 終了条件 (Definition of Done)

- [ ] `docs/reuse-test-2026-05.md` の §1〜§3 が埋まっている
- [ ] `Common2026/Shannon/ChannelCodingConverse.lean` が存在し、`lake env lean` がパス
      (sorry 残り 0 または 計上された bridge 候補のみ)
- [ ] §3 で次のうちいずれかが宣言されている:
  - "合格: bridge 不要、既存 API のみで n-channel converse まで到達"
  - "不合格: bridge 候補 N 件、修復 plan に転記"
