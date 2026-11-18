import Mathlib
import HRS.MS.PoisLipAux2

/-!
# S6.3, packet N8 (part 1): route decision and Lipschitz decay by doubling of variables

Namespace `HRS.MS.Mov63`, helper prefix `mng_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`), not manuscript rows.
Goal of packet N8: the decay clauses of `MovDecayBounds` for the solution of N5-N7: `‖∇ log Q_t‖_{C_b^j}` with `Q = ρ_t/ρ₀ ∈ [1/2,2]`
and the velocity `u_t = ν ∇log Q_t + F_t`, with amplitude `K e^{-ct}` LINEAR in `K` (`K = ε*` or `K = movInitialNorm`).

## Spike decision (route E-D, recorded also in `N8_PLAN.md`)

* E-A (Picard for `Q̂` in `C_b^{j+1}` + identification) is rejected: the mild solution is not known to be `C^{1,2}` (Schauder-type regularity is absent from the
  repository and the drift `b = -qx + O(1)` is unbounded, so `hs_duhamel` is not applicable to `Q`).
* E-B (Itô/flow Duhamel for `Q`) is rejected: it needs time-dependent Itô, localisation and Gaussian control of `D²Q`, and the Gronwall closing needs an a priori
  bound on `D²Q` that only a Gaussian-class maximum principle can supply.
* **E-D (chosen): everything by maximum principles.**
  1. (this file) Lipschitz decay of `Q` by the doubling-of-variables argument (the one that proves `pois_lipdecay`), applied directly to the bounded `Q`:
     `G = e^{-Λ(t)}(Q_t(x) - Q_t(y)) - Φ(t) f(|x-y|)`, `f = pm_ffun`; the time dependent drift `-qx + B_t` (`B_t = νB + F_t`) only needs `‖B_t‖, Lip B_t ≤ Mb`
     (no smallness of `F_t`); the zero order term `A_t` is absorbed by `Λ' = sup|A_t|` and the source `(A(x)-A(y))Q(y)` is `≤ 2 Lip(A) |x-y| ≤ 2 Lip(A) f/κ`.
  2. Higher derivatives by a Bernstein cascade (`Z = S_n + λ S_{n-1}`, `S_n = ∑_{|σ|=n} (∂_σ Q)²`, `λ` large) compared with `ψ = C K² e^{-2ct}` by `mnf_comparison`.
  3. A priori growth of the jets by 1D interpolation with `Q` bounded (exponent `κ_c(1-2^{-i}) < βq/4`).
  4. Instantiation, chain rule for `∇ log Q`, `movU = ν∇log Q + F_t` (Euler equation), the ENNReal norms.

## This file
* `mng_step`: the maximum point step of `ld_step` with the two hypotheses `‖B‖ ≤ Mb`, `Lip B ≤ Mb` instead of `HasCbBound`.
* `mng_kolmL_mul`: `kolmL` is homogeneous.
* **`mng_lip_decay`**: abstract Lipschitz decay: for `∂_tQ = ν kolmL q B_t Q + A_t Q` (classical on `[0,T]`), `|Q| ≤ M_Q`, `|A_t| ≤ α(t)`, `Lip A_t ≤ α₁(t)`,
  `Lip Q_0 ≤ L₀`, and `Φ, Λ` with `Λ' = α`, `Φ' ≥ -ν c₀ Φ + α₁ M_Q/κ`, `e^{-Λ(0)} L₀ ≤ κ Φ(0)`: `|Q_t(x)-Q_t(y)| ≤ e^{Λ(t)} Φ(t) |x-y|`
  (`κ = pm_kappa q Mb`, `c₀ = pm_c0 q Mb`, constants of `pm_ffun`).
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace NNReal

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisKolm HRS.MS.PoisMax HRS.MS.PoisLip

variable {d : ℕ}

theorem mng_step {q Mb : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hBb : ∀ z, ‖B z‖ ≤ Mb) (hBl : ∀ x y, ‖B x - B y‖ ≤ Mb * ‖x - y‖) (hd : 1 ≤ d) {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) {A' ε' : ℝ} (hA' : 0 ≤ A') (hε' : 0 ≤ ε') {x y : Euc d}
    (hf0 : 0 ≤ deriv f ‖x - y‖) (hxy : x ≠ y)
    (hmax : ∀ x' y' : Euc d,
      u x' - u y' - A' * f ‖x' - y'‖ - ε' * ‖x'‖ ^ 2 - ε' * ‖y'‖ ^ 2 + (-ε') ≤
      u x - u y - A' * f ‖x - y‖ - ε' * ‖x‖ ^ 2 - ε' * ‖y‖ ^ 2 + (-ε')) :
    kolmL q B u x - kolmL q B u y ≤
      A' * (4 * deriv (deriv f) ‖x - y‖ + pm_c q Mb ‖x - y‖ * deriv f ‖x - y‖)
        + ε' * (4 * d + 2 * Mb) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hfo, hlap⟩ := ld_maxpoint_pen hd u hu A' ε' ε' f hf x y (-ε') hmax hxy
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hBb 0)
  set r : ℝ := ‖x - y‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set e : Euc d := r⁻¹ • (x - y) with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hrpos.ne']
  have hexy : inner ℝ e (x - y) = r := by
    rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hr]
    field_simp
  set D : ℝ := deriv f r with hD
  have e1 : ∀ z, kolmL q B u z = Laplacian.laplacian u z + fderiv ℝ u z (-q • z + B z) := by
    intro z; unfold kolmL; rw [kl_inner_gradient]
  rw [e1, e1]
  obtain ⟨hx1, -⟩ := hfo (-q • x + B x)
  obtain ⟨-, hy1⟩ := hfo (-q • y + B y)
  rw [hx1, hy1]
  -- the pairing with e
  have hs : inner ℝ e (-q • x + B x) - inner ℝ e (-q • y + B y) = -(q * r) + inner ℝ e (B x - B y) := by
    rw [← inner_sub_right, show -q • x + B x - (-q • y + B y) = -q • (x - y) + (B x - B y) by module,
      inner_add_right, inner_smul_right, hexy]
    ring
  have hB1 : inner ℝ e (B x - B y) ≤ Mb * r := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [hen, one_mul]; exact hBl x y
  have hB2 : inner ℝ e (B x - B y) ≤ 2 * Mb := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [hen, one_mul]
    exact (norm_sub_le _ _).trans (by linarith [hBb x, hBb y])
  have hbr := ld_bracket hq hrpos.le hB1 hB2
  have hxb : inner ℝ x (-q • x + B x) ≤ Mb * ‖x‖ := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have : inner ℝ x (B x) ≤ ‖x‖ * Mb := (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hBb x) (norm_nonneg _))
    nlinarith [sq_nonneg ‖x‖]
  have hyb : inner ℝ y (-q • y + B y) ≤ Mb * ‖y‖ := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have : inner ℝ y (B y) ≤ ‖y‖ * Mb := (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hBb y) (norm_nonneg _))
    nlinarith [sq_nonneg ‖y‖]
  have hdr : A' * D * (inner ℝ e (-q • x + B x) - inner ℝ e (-q • y + B y)) ≤
      A' * (pm_c q Mb r * D) := by
    rw [hs]
    have := mul_le_mul_of_nonneg_left hbr (mul_nonneg hA' hf0)
    calc _ ≤ A' * D * pm_c q Mb r := this
      _ = _ := by ring
  have hnx : ‖x‖ ≤ (1 + ‖x‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hny : ‖y‖ ≤ (1 + ‖y‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hS : 0 ≤ (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hq1 : ε' * (2 * (inner ℝ x (-q • x + B x) + inner ℝ y (-q • y + B y))) ≤
      ε' * (2 * Mb * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hε'
    nlinarith [mul_le_mul_of_nonneg_left hnx hMb, mul_le_mul_of_nonneg_left hny hMb]
  have hq2 : ε' * (4 * d) ≤ ε' * (4 * d) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have : 1 ≤ 1 + ‖x‖ ^ 2 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    have h0 : 0 ≤ ε' * (4 * d) := by positivity
    calc ε' * (4 * d) = ε' * (4 * d) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this h0
  have e4 : ε' * (4 * d) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) + ε' * (2 * Mb * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2)) =
      ε' * (4 * d + 2 * Mb) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring
  have e5 : 2 * (d:ℝ) * (ε' + ε') = ε' * (4 * d) := by ring
  rw [e5] at hlap
  have e6 : A' * (4 * deriv (deriv f) r) = 4 * A' * deriv (deriv f) r := by ring
  have e7 : A' * (4 * deriv (deriv f) r + pm_c q Mb r * D) =
      A' * (4 * deriv (deriv f) r) + A' * (pm_c q Mb r * D) := by ring
  rw [e7, e6]
  linarith [hlap, hdr, hq1, hq2, e4]


lemma mng_kolmL_mul {q : ℝ} {B : Euc d → Euc d} {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ) (x : Euc d) :
    kolmL q B (fun w => c * u w) x = c * kolmL q B u x := by
  unfold kolmL
  have h1 : (fun w => c * u w) = c • u := by funext w; simp [smul_eq_mul]
  have hg : gradient (fun w => c * u w) x = c • gradient u x := by
    refine ext_inner_left ℝ fun e => ?_
    rw [kl_inner_gradient, inner_smul_right, kl_inner_gradient]
    have h : fderiv ℝ (fun w => c * u w) x = c • fderiv ℝ u x :=
      (((hu.differentiable (by norm_num)) x).hasFDerivAt.const_mul c).fderiv
    rw [h]; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h1, InnerProductSpace.laplacian_smul c hu.contDiffAt]
  rw [← h1, hg, inner_smul_right]
  simp [smul_eq_mul]; ring

set_option maxHeartbeats 1600000 in
/-- **Lipschitz decay by doubling of variables** (abstract form, see the module docstring). -/
theorem mng_lip_decay (hd : 1 ≤ d) {q Mb : ℝ} (hq : 0 < q) (hMb : 0 ≤ Mb) {ν : ℝ} (hν : 0 < ν) {T : ℝ}
    {Q : ℝ → Euc d → ℝ} {Bt : ℝ → Euc d → Euc d} {A : ℝ → Euc d → ℝ} {Φ Φ' Λ α α₁ : ℝ → ℝ}
    {MQ L0 : ℝ}
    (hQ2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (Q t))
    (hQc : ContinuousOn (fun p : ℝ × Euc d => Q p.1 p.2) (Icc 0 T ×ˢ univ))
    (hQd : ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => Q s x)
      (ν * kolmL q (Bt t) (Q t) x + A t x * Q t x) (Icc 0 T) t)
    (hBb : ∀ t ∈ Icc 0 T, ∀ z, ‖Bt t z‖ ≤ Mb)
    (hBl : ∀ t ∈ Icc 0 T, ∀ x y, ‖Bt t x - Bt t y‖ ≤ Mb * ‖x - y‖)
    (hQb : ∀ t ∈ Icc 0 T, ∀ x, |Q t x| ≤ MQ)
    (hAb : ∀ t ∈ Icc 0 T, ∀ x, |A t x| ≤ α t)
    (hAl : ∀ t ∈ Icc 0 T, ∀ x y, |A t x - A t y| ≤ α₁ t * ‖x - y‖)
    (hα₁ : ∀ t ∈ Icc 0 T, 0 ≤ α₁ t)
    (hL0 : ∀ x y, |Q 0 x - Q 0 y| ≤ L0 * ‖x - y‖)
    (hΛd : ∀ t, HasDerivAt Λ (α t) t) (hΛ0 : ∀ t ∈ Icc 0 T, 0 ≤ Λ t)
    (hΦd : ∀ t, HasDerivAt Φ (Φ' t) t) (hΦnn : ∀ t ∈ Icc 0 T, 0 ≤ Φ t)
    (hΦ' : ∀ t ∈ Icc 0 T, -(ν * pm_c0 q Mb * Φ t) + α₁ t * MQ / pm_kappa q Mb ≤ Φ' t)
    (hΦ0 : Real.exp (-Λ 0) * L0 ≤ Φ 0 * pm_kappa q Mb)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : Euc d) :
    |Q t x - Q t y| ≤ Real.exp (Λ t) * Φ t * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero, norm_zero, mul_zero]
    exact le_rfl
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hMQ : 0 ≤ MQ := (abs_nonneg _).trans (hQb 0 ⟨le_rfl, hT⟩ 0)
  obtain ⟨f, hfc, hf0, hfd, hfb, hfine⟩ := pm_ffun hq hMb
  have hκ : 0 < pm_kappa q Mb := Real.exp_pos _
  have hc0 : 0 < pm_c0 q Mb := by
    unfold pm_c0
    exact mul_pos hκ (lt_min one_pos (by linarith))
  set κ : ℝ := pm_kappa q Mb with hκdef
  set c0 : ℝ := pm_c0 q Mb with hc0def
  have hfcont : Continuous f := hfc.continuous
  have hf2 : ContDiffOn ℝ 2 f (Set.Ioi 0) :=
    (by exact_mod_cast (contDiff_infty.1 hfc) 2 : ContDiff ℝ 2 f).contDiffOn
  have hfnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ f r := fun r hr =>
    le_trans (mul_nonneg hκ.le hr) (hfb r hr).1
  have hΛc : Continuous Λ := continuous_iff_continuousAt.2 fun s => (hΛd s).continuousAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun s => (hΦd s).continuousAt
  set QE : ℝ → Euc d → ℝ := fun s x => ν * kolmL q (Bt s) (Q s) x + A s x * Q s x with hQE
  set G : ℝ → WithLp 2 (Euc d × Euc d) → ℝ := fun s z =>
    Real.exp (-Λ s) * (Q s z.fst - Q s z.snd) - Φ s * f ‖z.fst - z.snd‖ with hG
  set Gt : ℝ → WithLp 2 (Euc d × Euc d) → ℝ := fun s z =>
    -α s * Real.exp (-Λ s) * (Q s z.fst - Q s z.snd) +
      Real.exp (-Λ s) * (QE s z.fst - QE s z.snd) - Φ' s * f ‖z.fst - z.snd‖ with hGt
  have hcont : ContinuousOn (fun p : ℝ × WithLp 2 (Euc d × Euc d) => G p.1 p.2)
      (Icc 0 T ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℝ × WithLp 2 (Euc d × Euc d) => Q p.1 p.2.fst)
        (Icc 0 T ×ˢ univ) := by
      have hmp : Set.MapsTo (fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.fst))
          (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
      exact ContinuousOn.comp (g := fun p : ℝ × Euc d => Q p.1 p.2) hQc
        (by fun_prop : Continuous fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.fst)).continuousOn hmp
    have h2 : ContinuousOn (fun p : ℝ × WithLp 2 (Euc d × Euc d) => Q p.1 p.2.snd)
        (Icc 0 T ×ˢ univ) := by
      have hmp : Set.MapsTo (fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.snd))
          (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
      exact ContinuousOn.comp (g := fun p : ℝ × Euc d => Q p.1 p.2) hQc
        (by fun_prop : Continuous fun p : ℝ × WithLp 2 (Euc d × Euc d) => (p.1, p.2.snd)).continuousOn hmp
    have h3 : Continuous (fun p : ℝ × WithLp 2 (Euc d × Euc d) =>
        Real.exp (-Λ p.1)) := by fun_prop
    have h4 : Continuous (fun p : ℝ × WithLp 2 (Euc d × Euc d) =>
        Φ p.1 * f ‖p.2.fst - p.2.snd‖) := by fun_prop
    exact (h3.continuousOn.mul (h1.sub h2)).sub h4.continuousOn
  have hder : ∀ s ∈ Icc (0:ℝ) T, ∀ z : WithLp 2 (Euc d × Euc d),
      HasDerivWithinAt (fun r => G r z) (Gt s z) (Icc 0 T) s := by
    intro s hs z
    have h1 := hQd s hs z.fst
    have h2 := hQd s hs z.snd
    have h3 : HasDerivAt (fun r : ℝ => Real.exp (-Λ r)) (-α s * Real.exp (-Λ s)) s := by
      have := (hΛd s).neg.exp
      simpa [mul_comm] using this
    have h4 := ((hΦd s).mul_const (f ‖z.fst - z.snd‖))
    refine ((h3.hasDerivWithinAt.mul (h1.sub h2)).sub h4.hasDerivWithinAt).congr_deriv ?_
    simp only [hGt, hQE, Pi.sub_apply]
    try ring
  have h0 : ∀ z : WithLp 2 (Euc d × Euc d), G 0 z ≤ 0 := by
    intro z
    simp only [hG]
    have hr := norm_nonneg (z.fst - z.snd)
    have h1 := hL0 z.fst z.snd
    have h2 := (hfb ‖z.fst - z.snd‖ hr).1
    have hΦ0nn := hΦnn 0 ⟨le_rfl, hT⟩
    have he := Real.exp_pos (-Λ 0)
    have h5 := le_abs_self (Q 0 z.fst - Q 0 z.snd)
    have h6 : Real.exp (-Λ 0) * (Q 0 z.fst - Q 0 z.snd) ≤ Real.exp (-Λ 0) * (L0 * ‖z.fst - z.snd‖) :=
      mul_le_mul_of_nonneg_left (h5.trans h1) he.le
    have h7 : Real.exp (-Λ 0) * (L0 * ‖z.fst - z.snd‖) ≤ Φ 0 * κ * ‖z.fst - z.snd‖ := by
      have := mul_le_mul_of_nonneg_right hΦ0 hr
      linarith
    have h8 : Φ 0 * (κ * ‖z.fst - z.snd‖) ≤ Φ 0 * f ‖z.fst - z.snd‖ :=
      mul_le_mul_of_nonneg_left h2 hΦ0nn
    nlinarith
  have hgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s ∈ Icc (0:ℝ) T, ∀ z : WithLp 2 (Euc d × Euc d),
      G s z ≤ C + δ * ‖z‖ ^ 2 := by
    intro δ hδ
    refine ⟨2 * MQ, fun s hs z => ?_⟩
    have h1 := (abs_le.1 (hQb s hs z.fst)).2
    have h2 := (abs_le.1 (hQb s hs z.snd)).1
    have he1 : Real.exp (-Λ s) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith [hΛ0 s hs])
    have he0 := Real.exp_pos (-Λ s)
    have h3 : 0 ≤ Φ s * f ‖z.fst - z.snd‖ :=
      mul_nonneg (hΦnn s hs) (hfnn _ (norm_nonneg _))
    have h4 : 0 ≤ δ * ‖z‖ ^ 2 := by positivity
    have h5 : Real.exp (-Λ s) * (Q s z.fst - Q s z.snd) ≤ 2 * MQ := by
      have hD : Q s z.fst - Q s z.snd ≤ 2 * MQ := by linarith
      have hD' : 0 ≤ 2 * MQ := by linarith
      calc _ ≤ Real.exp (-Λ s) * (2 * MQ) := mul_le_mul_of_nonneg_left hD he0.le
        _ ≤ 1 * (2 * MQ) := mul_le_mul_of_nonneg_right he1 hD'
        _ = 2 * MQ := one_mul _
    simp only [hG]
    linarith
  have hfail : ∃ lam : ℝ, ∀ ε : ℝ, 0 < ε → ∀ s ∈ Ioc (0:ℝ) T, ∀ z : WithLp 2 (Euc d × Euc d),
      0 < G s z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) →
      (∀ z' : WithLp 2 (Euc d × Euc d), G s z' - ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * s) ≤
        G s z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * s)) →
      Gt s z < ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) := by
    refine ⟨ν * (4 * d + 2 * Mb) + 1, fun ε hε s hs z hpos hmax => ?_⟩
    have hsT : s ∈ Icc (0:ℝ) T := ⟨hs.1.le, hs.2⟩
    set lam : ℝ := ν * (4 * d + 2 * Mb) + 1 with hlam
    have hpen : ∀ z' : WithLp 2 (Euc d × Euc d),
        ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * s) =
          ε * Real.exp (lam * s) * ‖z'.fst‖ ^ 2 +
          ε * Real.exp (lam * s) * ‖z'.snd‖ ^ 2 +
          ε * Real.exp (lam * s) := fun z' => by
      rw [WithLp.prod_norm_sq_eq_of_L2]; ring
    have hexp : 0 < Real.exp (lam * s) := Real.exp_pos _
    have hε' : 0 ≤ ε * Real.exp (lam * s) := by positivity
    have he0 : 0 < Real.exp (-Λ s) := Real.exp_pos _
    have he1 : Real.exp (-Λ s) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith [hΛ0 s hsT])
    have hΦs := hΦnn s hsT
    have hxy' : z.fst ≠ z.snd := by
      intro hxy0
      have h1 : G s z = 0 := by simp [hG, hxy0, hf0]
      rw [h1] at hpos
      have : 0 < ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) := by positivity
      linarith
    have hmax' : ∀ x' y' : Euc d,
        Real.exp (-Λ s) * Q s x' - Real.exp (-Λ s) * Q s y' - Φ s * f ‖x' - y'‖
          - ε * Real.exp (lam * s) * ‖x'‖ ^ 2
          - ε * Real.exp (lam * s) * ‖y'‖ ^ 2
          + (-(ε * Real.exp (lam * s))) ≤
        Real.exp (-Λ s) * Q s z.fst - Real.exp (-Λ s) * Q s z.snd
          - Φ s * f ‖z.fst - z.snd‖
          - ε * Real.exp (lam * s) * ‖z.fst‖ ^ 2
          - ε * Real.exp (lam * s) * ‖z.snd‖ ^ 2
          + (-(ε * Real.exp (lam * s))) := by
      intro x' y'
      have h1 := hmax (WithLp.toLp 2 (x', y'))
      have e1 := hpen (WithLp.toLp 2 (x', y'))
      have e2 := hpen z
      simp only [hG, WithLp.toLp_fst, WithLp.toLp_snd] at h1 e1
      nlinarith
    have hr0 : 0 ≤ ‖z.fst - z.snd‖ := norm_nonneg _
    have hfp : 0 ≤ deriv f ‖z.fst - z.snd‖ := le_trans hκ.le (hfd _ hr0).1
    have hu2 : ContDiff ℝ 2 (fun w => Real.exp (-Λ s) * Q s w) := contDiff_const.mul (hQ2 s hsT)
    have hstep := mng_step (q := q) (Mb := Mb) hq (B := Bt s) (hBb s hsT) (hBl s hsT) hd hu2 hf2 hΦs hε' hfp
      hxy' hmax'
    rw [mng_kolmL_mul (hQ2 s hsT), mng_kolmL_mul (hQ2 s hsT)] at hstep
    have hfi := hfine _ hr0
    have hAfi : Φ s * (4 * deriv (deriv f) ‖z.fst - z.snd‖ +
        pm_c q Mb ‖z.fst - z.snd‖ * deriv f ‖z.fst - z.snd‖) ≤ Φ s * (-(c0 * f ‖z.fst - z.snd‖)) :=
      mul_le_mul_of_nonneg_left hfi hΦs
    -- positivity of the difference at the maximum
    have hpen0 : 0 ≤ ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) := by positivity
    have hfnn' : 0 ≤ Φ s * f ‖z.fst - z.snd‖ := mul_nonneg hΦs (hfnn _ hr0)
    have hD : 0 < Q s z.fst - Q s z.snd := by
      have h1 : 0 < Real.exp (-Λ s) * (Q s z.fst - Q s z.snd) := by
        simp only [hG] at hpos; linarith
      exact (pos_iff_pos_of_mul_pos h1).1 he0
    have hAx : A s z.fst ≤ α s := (abs_le.1 (hAb s hsT z.fst)).2
    have hAxy : A s z.fst - A s z.snd ≤ α₁ s * ‖z.fst - z.snd‖ :=
      (le_abs_self _).trans (hAl s hsT _ _)
    have hα1 := hα₁ s hsT
    have hQy := (abs_le.1 (hQb s hsT z.snd)).2
    have hQy' := (abs_le.1 (hQb s hsT z.snd)).1
    -- the zero order terms
    have hz1 : A s z.fst * Q s z.fst - A s z.snd * Q s z.snd - α s * (Q s z.fst - Q s z.snd) ≤
        α₁ s * ‖z.fst - z.snd‖ * MQ := by
      have e : A s z.fst * Q s z.fst - A s z.snd * Q s z.snd - α s * (Q s z.fst - Q s z.snd) =
          (A s z.fst - α s) * (Q s z.fst - Q s z.snd) + (A s z.fst - A s z.snd) * Q s z.snd := by ring
      rw [e]
      have a1 : (A s z.fst - α s) * (Q s z.fst - Q s z.snd) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
      have a2 : (A s z.fst - A s z.snd) * Q s z.snd ≤ α₁ s * ‖z.fst - z.snd‖ * MQ := by
        have hq1 : (A s z.fst - A s z.snd) * Q s z.snd ≤ |A s z.fst - A s z.snd| * |Q s z.snd| :=
          (le_abs_self _).trans (by rw [abs_mul])
        calc _ ≤ |A s z.fst - A s z.snd| * |Q s z.snd| := hq1
          _ ≤ (α₁ s * ‖z.fst - z.snd‖) * MQ :=
            mul_le_mul (hAl s hsT _ _) (hQb s hsT _) (abs_nonneg _) (by positivity)
      linarith
    have hrf : ‖z.fst - z.snd‖ ≤ f ‖z.fst - z.snd‖ / κ := by
      rw [le_div_iff₀ hκ]
      have := (hfb _ hr0).1; linarith
    have hz2 : α₁ s * ‖z.fst - z.snd‖ * MQ ≤ α₁ s * MQ / κ * f ‖z.fst - z.snd‖ := by
      have := mul_le_mul_of_nonneg_left hrf (mul_nonneg hα1 hMQ)
      calc α₁ s * ‖z.fst - z.snd‖ * MQ = α₁ s * MQ * ‖z.fst - z.snd‖ := by ring
        _ ≤ α₁ s * MQ * (f ‖z.fst - z.snd‖ / κ) := this
        _ = _ := by ring
    have hz3 : Real.exp (-Λ s) * (α₁ s * ‖z.fst - z.snd‖ * MQ) ≤ α₁ s * ‖z.fst - z.snd‖ * MQ := by
      have h0' : 0 ≤ α₁ s * ‖z.fst - z.snd‖ * MQ := by positivity
      calc _ ≤ 1 * (α₁ s * ‖z.fst - z.snd‖ * MQ) := mul_le_mul_of_nonneg_right he1 h0'
        _ = _ := one_mul _
    have hΦ's := hΦ' s hsT
    have hf0' := hfnn _ hr0
    -- assemble
    have hz4 : Real.exp (-Λ s) * (A s z.fst * Q s z.fst - A s z.snd * Q s z.snd) -
        α s * Real.exp (-Λ s) * (Q s z.fst - Q s z.snd) ≤ α₁ s * MQ / κ * f ‖z.fst - z.snd‖ := by
      have := mul_le_mul_of_nonneg_left hz1 he0.le
      nlinarith
    have hmain : Gt s z ≤ ν * (ε * Real.exp (lam * s) * (4 * d + 2 * Mb) *
        (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)) := by
      simp only [hGt, hQE]
      have e1 : Real.exp (-Λ s) * (ν * kolmL q (Bt s) (Q s) z.fst + A s z.fst * Q s z.fst -
          (ν * kolmL q (Bt s) (Q s) z.snd + A s z.snd * Q s z.snd)) =
          ν * (Real.exp (-Λ s) * kolmL q (Bt s) (Q s) z.fst - Real.exp (-Λ s) * kolmL q (Bt s) (Q s) z.snd) +
          Real.exp (-Λ s) * (A s z.fst * Q s z.fst - A s z.snd * Q s z.snd) := by ring
      have hs1 : ν * (Real.exp (-Λ s) * kolmL q (Bt s) (Q s) z.fst - Real.exp (-Λ s) * kolmL q (Bt s) (Q s) z.snd)
          ≤ ν * (Φ s * (-(c0 * f ‖z.fst - z.snd‖)) +
            ε * Real.exp (lam * s) * (4 * d + 2 * Mb) * (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hν.le
      have hs2 : -α s * Real.exp (-Λ s) * (Q s z.fst - Q s z.snd) = -(α s * Real.exp (-Λ s) * (Q s z.fst - Q s z.snd)) := by ring
      have hs3 : (-(ν * c0 * Φ s) + α₁ s * MQ / κ - Φ' s) * f ‖z.fst - z.snd‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hf0'
      nlinarith
    have hS : 0 < ε * Real.exp (lam * s) * (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) := by positivity
    have hz : ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) =
        ν * (ε * Real.exp (lam * s) * (4 * d + 2 * Mb) * (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)) +
        ε * Real.exp (lam * s) * (1 + ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) := by
      rw [WithLp.prod_norm_sq_eq_of_L2, hlam]; ring
    rw [hz]
    linarith
  have key := pm_penalized_max (E := WithLp 2 (Euc d × Euc d)) G Gt T hcont hder h0 hgrow hfail
  have hbound : ∀ a b : Euc d, Q t a - Q t b ≤ Real.exp (Λ t) * Φ t * ‖a - b‖ := by
    intro a b
    have h1 : Real.exp (-Λ t) * (Q t a - Q t b) - Φ t * f ‖a - b‖ ≤ 0 :=
      key t ht (WithLp.toLp 2 (a, b))
    have h2 : Φ t * f ‖a - b‖ ≤ Φ t * ‖a - b‖ :=
      mul_le_mul_of_nonneg_left (hfb _ (norm_nonneg _)).2 (hΦnn t ht)
    have h3 : Q t a - Q t b ≤ Real.exp (Λ t) * (Φ t * ‖a - b‖) := by
      have e : Real.exp (-Λ t) * (Q t a - Q t b) ≤ Φ t * ‖a - b‖ := by linarith
      have := mul_le_mul_of_nonneg_left e (Real.exp_pos (Λ t)).le
      rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
    linarith
  rw [abs_le]
  constructor
  · have := hbound y x
    rw [norm_sub_rev] at this
    linarith
  · exact hbound x y


end HRS.MS.Mov63

end
