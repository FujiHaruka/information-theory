#!/usr/bin/env python3
"""Leg 0 gateway probe — is `contAwgn_eq_shannonHartley` TRUE under Proposal A?

Proposal A def-fix: `encoder_power : ∀ m, (∫ t, (encoder m t)^2) ≤ T * P`  (whole line, was `[0,T]`).

The model, verbatim from InformationTheory/Shannon/ShannonHartleyOperational.lean:
  - encoder m : ℝ → ℝ, band-limited to [-W, W], continuous, L², ‖·‖₂² ≤ T·P   (Proposal A)
  - sampledSignal f T n i = √(T/n) · f(i·T/n),  i ∈ Fin n,  n = `sampleCount` FREE (constraint C4)
  - observation = sampledSignal + iid N(0, N₀/2) per sample

Structure (analytic, probed here for confirmation).  Write t_i = i·T/n, Δ = T/n.  A band-limited
f ∈ PW_W has f(t) = ⟨f, K_t⟩ with the reproducing kernel K_t(s) = 2W·sinc(2W(s-t)) and
⟨K_t, K_u⟩ = 2W·sinc(2W(t-u)).  So the sample vector is x_i = ⟨f, √Δ·K_{t_i}⟩ and the Gram matrix of
the sampling frame is

    G_ij = Δ · 2W · sinc(2W(t_i - t_j)),      trace G = n · Δ · 2W = 2WT   (EXACT, for every n)

Diagonalizing G = Σ_k g_k u_k u_kᵀ turns the channel into independent y_k = √g_k·a_k + z_k with
Σ_k a_k² = ‖f‖² ≤ TP and z_k ~ N(0, N₀/2).  Hence

    C(n) = max_{Σ E_k ≤ TP} Σ_k ½·log(1 + g_k·E_k/(N₀/2))          (water-filling)

The three claims this probe tests, each a forward-evaluated certificate (no inverse / no regularizer):

  (1) TRACE      trace G_n = 2WT for every n           — the n-uniform degrees-of-freedom budget
  (2) NO LEAK    C(n) does not grow with n             — oversampling (n → ∞) leaks no capacity
  (3) EXACTNESS  C(n) ≈ WT·log(1 + P/(W·N₀)) = SH      — the Shannon-Hartley value is the answer

A FAIL on (2) or (3) refutes Proposal A and sends Leg 0 to Proposal C (Landau-Pollak).

Also probed:
  (4) NYQUIST BALL  G = I_n at n = 2WT  ⟹ achievable sample set is EXACTLY the ball ‖x‖² ≤ TP
  (5) DEGENERATE    P = 0 ⟹ the whole-line constraint forces f ≡ 0 (kills the superoscillation class)
  (6) PROFILE       g_k is the prolate cliff (≈1 for k < 2WT, then decay), NOT a reshapeable profile

Run: python3 docs/shannon/leg0-gateway-probe.py     (numpy only)
"""

import numpy as np


def sinc2w(x, W):
    """2W·sinc(2W·x) with numpy's sinc(x) = sin(πx)/(πx)."""
    return 2.0 * W * np.sinc(2.0 * W * x)


def gram(T, W, n):
    """G_ij = (T/n)·2W·sinc(2W(t_i - t_j)), t_i = i·T/n."""
    d = T / n
    t = np.arange(n) * d
    return d * sinc2w(t[:, None] - t[None, :], W)


def waterfill_capacity(g, TP, N0):
    """max_{Σ E_k ≤ TP} Σ ½·ln(1 + g_k·E_k/(N₀/2)), in nats. Water-filling over 1/g_k."""
    g = np.sort(g[g > 1e-12])[::-1]
    noise = (N0 / 2.0) / g  # effective per-mode noise
    for k in range(len(g), 0, -1):
        mu = (TP + noise[:k].sum()) / k
        E = mu - noise[:k]
        if E[-1] >= 0:
            return 0.5 * np.log(1.0 + E / noise[:k]).sum()
    return 0.0


def shannon_hartley(T, W, P, N0):
    """WT·ln(1 + P/(W·N₀)) in nats — the target value of contAwgn_eq_shannonHartley."""
    return W * T * np.log(1.0 + P / (W * N0))


def main():
    T, W, N0 = 8.0, 1.0, 1.0
    dof = 2 * W * T  # = 16
    print(f"model: T={T} W={W} N0={N0}   2WT = {dof}\n")

    for P in (10.0, 1.0, 0.1):
        TP = T * P
        SH = shannon_hartley(T, W, P, N0)
        print(f"--- P={P}  (SNR P/(W·N0) = {P/(W*N0)})   Shannon-Hartley = {SH:.4f} nats ---")
        print(f"{'n':>6} {'trace G':>12} {'C(n) nats':>12} {'C(n)/SH':>9}  {'#g_k>0.5':>8}")
        for n in (8, 16, 32, 64, 128, 256, 512):
            G = gram(T, W, n)
            g = np.linalg.eigvalsh(G)
            C = waterfill_capacity(g, TP, N0)
            print(f"{n:>6} {np.trace(G):>12.6f} {C:>12.4f} {C/SH:>9.4f}  {(g > 0.5).sum():>8}")
        print()

    # (4) Nyquist ball: at n = 2WT the sample spacing is 1/(2W) and G collapses to the identity.
    n = int(dof)
    G = gram(T, W, n)
    print(f"(4) NYQUIST BALL  n = 2WT = {n}:  ‖G - I‖_max = {np.abs(G - np.eye(n)).max():.3e}")
    print("    ⟹ achievable sample set = exactly {x : ‖x‖² ≤ TP}; sinc interpolation is an isometry.\n")

    # (6) Profile at heavy oversampling: the prolate cliff, and what a free profile would give.
    n = 256
    g = np.sort(np.linalg.eigvalsh(gram(T, W, n)))[::-1]
    print(f"(6) PROFILE at n={n} (oversampling ×{n/dof:g}): top eigenvalues of G")
    print("    " + " ".join(f"{v:.3f}" for v in g[:22]))
    print(f"    #(g_k > 0.99) = {(g > 0.99).sum()},  #(g_k > 0.5) = {(g > 0.5).sum()},  2WT = {dof:g}")
    print(f"    trace = {g.sum():.6f}  (= 2WT, so the cliff — not the trace — is what pins the answer)")
    print()

    # (7) THE REFUTATION — sub-Nyquist sampling.  `sampleCount` is free (C4), so a code may sample
    # SLOWER than Nyquist.  Put Δ = T/n = m/(2W) for an integer m ≥ 1, i.e. n = 2WT/m.  Then
    # 2W·sinc(2W·Δ·(i-j)) = 2W·sinc(m(i-j)) = 0 for i ≠ j, so the kernels are orthogonal and
    #
    #     G = Δ·2W·I = m·I ,   achievable set = {x : ‖x‖² ≤ m·T·P} ,
    #     C(m) = (n/2)·ln(1 + 2·(m·TP/n)/N₀) = (WT/m)·ln(1 + m²·s),   s = P/(W·N₀).
    #
    # The `√(T/n)` normalization of `sampledSignal` is an isometry ONLY at Δ = 1/(2W) (m = 1).  For
    # m ≥ 2 it over-scales: each sample carries m× the signal energy per unit of whole-line energy,
    # while `errorProbAt` fixes the per-sample noise at N₀/2 regardless of Δ.  Free `sampleCount` +
    # rate-independent noise = an SNR the whole-line energy budget does not pay for.
    #
    #     C(m)/SH = ln(1 + m²s) / (m·ln(1 + s))  >  1  ⟺  (for m = 2)  s < 2.
    print("(7) SUB-NYQUIST LEAK — closed form vs. the eigen/water-filling probe above")
    print(f"{'s = P/(W·N0)':>13} {'m':>3} {'n = 2WT/m':>10} {'C(m) closed':>12} {'C/SH closed':>12} {'C/SH probe':>11}")
    for P in (10.0, 1.0, 0.1, 0.01):
        s = P / (W * N0)
        SH = shannon_hartley(T, W, P, N0)
        for m in (1, 2, 4, 8):
            n = int(dof / m)
            if n < 1:
                continue
            C = (W * T / m) * np.log(1.0 + m * m * s)
            probe = waterfill_capacity(np.linalg.eigvalsh(gram(T, W, n)), T * P, N0)
            flag = "  ← LEAK" if C / SH > 1.0 + 1e-9 else ""
            print(f"{s:>13g} {m:>3} {n:>10} {C:>12.4f} {C/SH:>12.4f} {probe/SH:>11.4f}{flag}")
    print("\n    sup over m of (1/m)·ln(1 + m²s) ≈ 0.8·√s  as s → 0, vs. SH's ln(1+s) ≈ s:")
    print(f"{'s':>10} {'SH rate/W':>12} {'sup_m rate/W':>14} {'best m':>7} {'ratio':>9}")
    for s in (2.0, 1.0, 0.1, 0.01, 0.001):
        best = max(((1.0 / m) * np.log(1.0 + m * m * s), m) for m in range(1, 4001))
        print(f"{s:>10g} {np.log(1+s):>12.6f} {best[0]:>14.6f} {best[1]:>7} {best[0]/np.log(1+s):>9.3f}")


def proposal_o():
    """Leg 0' gateway — does Proposal O make `contAwgn_eq_shannonHartley` TRUE?

    Proposal O (replaces point-sampling): the code carries `φ : Fin k → (ℝ → ℝ)` with fields
    "each φᵢ is supported in [0,T]" and "∫ φᵢ·φⱼ = δᵢⱼ", and observes
    `yᵢ = ∫ (encoder m)·φᵢ + zᵢ`, `zᵢ ~ N(0, N₀/2)` iid.  This is the textbook Karhunen-Loève /
    matched-filter discretization: for an ORTHONORMAL family the white-noise coefficients
    `⟨ξ, φᵢ⟩` are *exactly* iid `N(0, N₀/2)`, so `Measure.pi` is exact rather than a surrogate.
    `k` stays free (C4 ✓) and no def mentions `2W` (C3 ✓).

    Structure: for f ∈ PW_W, ⟨f, φᵢ⟩ = ⟨f, P_W φᵢ⟩, so the Gram of the analysis vectors is
    `Gᵢⱼ = ⟨φᵢ, A φⱼ⟩` with A = (time-limit ∘ band-limit ∘ time-limit) on [0,T] — the PROLATE
    operator, i.e. `TimeBandLimiting.lean`'s operator.  Hence:

      - G is the compression of A to span{φᵢ}.  Cauchy interlacing + ‖A‖ ≤ 1 (already proven
        in-project, Leg A) ⟹ no choice of φ can beat the top-k prolate eigenfunctions.
      - Sub-Nyquist has no analogue: orthonormality is a FIELD, so the m-fold over-scaling that
        killed Proposal A cannot be written down.
      - Oversampling (k → ∞) is capped: gains are λᵢ ≤ 1 with Σλᵢ = 2WT.
      - BddAbove closes by BESSEL alone, k-uniformly and wall-free: Σᵢ⟨f,φᵢ⟩² ≤ ‖f‖² ≤ TP.

    The one thing armchair analysis cannot settle, and the point of this probe: at finite T the
    water-filling value is NOT exactly SH (the prolate cliff has an O(log T) transition band).  The
    theorem is `limsup_{T→∞} (log M)/T`, so the verdict hinges on whether the excess is o(T).
    TEST: C(T)/SH(T) → 1 as T → ∞.  If the ratio plateaus above 1, Proposal O leaks and FAILS.
    """
    W, N0 = 1.0, 1.0
    print("\n" + "=" * 78)
    print("Leg 0' — PROPOSAL O gateway (orthonormal test functions supported in [0,T])")
    print("=" * 78)

    for P in (10.0, 1.0, 0.1):
        s = P / (W * N0)
        print(f"\n--- P={P} (s={s})  TEST: C(T)/SH(T) → 1 as T → ∞ ---")
        print(f"{'T':>6} {'2WT':>6} {'grid n':>7} {'C(T) nats':>11} {'SH(T)':>11} {'C/SH':>8} {'excess/T':>10}")
        prev = None
        for T in (8.0, 16.0, 32.0, 64.0, 128.0):
            n = int(16 * 2 * W * T)  # grid ≫ 2WT so the discretized A resolves the prolate cliff
            lam = np.linalg.eigvalsh(gram(T, W, n))  # eigenvalues of A = prolate λ_k
            C = waterfill_capacity(lam, T * P, N0)  # φ = top-k prolate eigenfunctions (the optimum)
            SH = shannon_hartley(T, W, P, N0)
            print(f"{T:>6g} {2*W*T:>6g} {n:>7} {C:>11.4f} {SH:>11.4f} {C/SH:>8.4f} {(C-SH)/T:>10.5f}")
            prev = C / SH
        verdict = "→ 1 ✓ excess is o(T)" if abs(prev - 1.0) < 0.01 else "✗ PLATEAU ABOVE 1 = LEAK"
        print(f"       {verdict}")

    # Adversarial: can a NON-optimal φ (random ONB, or k ≠ 2WT) beat the prolate choice?
    T, P = 32.0, 1.0
    n = int(16 * 2 * W * T)
    G_full = gram(T, W, n)
    lam = np.linalg.eigvalsh(G_full)
    SH = shannon_hartley(T, W, P, N0)
    print(f"\n--- adversarial φ search (T={T}, P={P}, SH={SH:.4f}, 2WT={2*W*T:g}) ---")
    print(f"{'φ choice':>28} {'k':>6} {'C nats':>10} {'C/SH':>8}")
    print(f"{'top-k prolate (all k)':>28} {n:>6} {waterfill_capacity(lam, T*P, N0):>10.4f} "
          f"{waterfill_capacity(lam, T*P, N0)/SH:>8.4f}")
    for k in (16, 32, 64, 128, 256):
        top = np.sort(lam)[::-1][:k]
        C = waterfill_capacity(top, T * P, N0)
        print(f"{'top-k prolate':>28} {k:>6} {C:>10.4f} {C/SH:>8.4f}")
    rng = np.random.default_rng(0)
    best = 0.0
    for trial in range(200):
        k = int(rng.integers(4, 200))
        Q, _ = np.linalg.qr(rng.standard_normal((n, k)))  # random ONB of a k-dim subspace of L²[0,T]
        G = Q.T @ G_full @ Q  # compression of A — the Gram of {P_W φᵢ}
        best = max(best, waterfill_capacity(np.linalg.eigvalsh(G), T * P, N0))
    print(f"{'random ONB (200 trials, best)':>28} {'var':>6} {best:>10.4f} {best/SH:>8.4f}")
    print(f"\n    Cauchy interlacing predicts no φ beats top-k prolate: "
          f"{'✓ held' if best <= waterfill_capacity(lam, T*P, N0) + 1e-9 else '✗ VIOLATED'}")


if __name__ == "__main__":
    main()
    proposal_o()
