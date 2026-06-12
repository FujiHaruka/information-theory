# AWGN converse: main wiring (`awgn_converse` body discharge) mini-plan

**Status**: CLOSED ✅ — `awgn_converse` body を discharger への薄い wrapper passthrough で配線、file scope で proof done。採用方針 (i) (forward import flip、逆向き import 不発火)。AWGN converse ラインは CLOSED。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C 失敗時 fallback」C-7 項 / 判断ログ #6「後続セッション送り (4)」

## 要点 (再利用可能な一行)

- wiring 専門 mini-plan は wall を headline signature に持ち上げず、private 集約のまま wrapper 1 段で透過させるのが正解 (hyp 外注は double migration を招く)。
- consumer ripple = 0 件 (`awgn_converse` の実 caller なし、出現は全て docstring 言及 or 別命名)。
