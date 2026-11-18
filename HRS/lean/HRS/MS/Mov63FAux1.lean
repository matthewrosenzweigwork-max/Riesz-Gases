import HRS.MS.LcUniqAux1
import HRS.MS.PoisKolmAux2

/-!
# S6.3, packet N7 (part 1): per-packet plan, statement checks, and the abstract comparison principle

Namespace `HRS.MS.Mov63`, helper prefix `mnf_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not manuscript rows.
Files `Mov63FAux1` ... (about 1,400 lines).  Input: the signed mild solution of `mov63_signed_solution` (N6) and its classical `Q`-equation
(`mne_Q_hasDerivAt`), `Q_t = ρ_t/ρ₀ = 1 + V_t/√ρ₀` (`mneQ`).  Output: positivity and the ratio bounds `ρ₀/2 ≤ ρ_t ≤ 2ρ₀`.

## Checks against the real definitions (done before any proof)

* **The ratio is NOT controlled by the `Σ^m` norm alone.**  `Q_t - 1 = V_t/√ρ₀` and `√ρ₀` decays like a Gaussian, whereas `Σ^m ⊂ C_b^i` controls
  `V_t` only up to polynomial decay (`V = (1+|x|²)^{-m}` has `‖V‖_{Σ^{m'}}` small but `V/√ρ₀` unbounded).  So the smallness of `‖x₀‖_{Σ^m}`
  gives NO sup bound on `Q_0 - 1 = f₀`; it must be a separate hypothesis on the initial datum, and this is exactly the other half of
  `MovInitialClass` (`f₀ ∈ C_b^{j+1}`, `cbNorm (j+1) f₀ ≤ ε_*`, hence `sup|f₀| ≤ ε_* ≤ 1/4`).  Hypothesis of the output theorem:
  `∀ x, |f₀ x| ≤ 1/4` (with `f₀ = mneF0fun`).  Nothing else of `MovInitialClass` is used.
* **The a-priori growth class of `Q_t`.**  For `t ≥ 0` the only information is `|V_t| ≤ C‖v_t‖` (embedding `mn_force_bound`, `k = 0`), so
  `|Q_t(x)| ≤ 1 + C‖v_t‖/√ρ₀(x)`.  The thermal state satisfies `ν ∇log ρ₀ = -q x - ∇g*ρ₀` (`mv0_thermal_force`) with `∇g*ρ₀` bounded
  (`mne_force_facts` applied to `√ρ₀`, `mneF0`), hence `ρ₀(x) ≥ ρ₀(0) exp(-βq‖x‖²/2 - βM₀‖x‖)` (integrate along rays) and
  `|Q_t(x)| ≤ K exp(κ₀‖x‖²)`, `κ₀ = 5βq/16`, uniformly in `t ≥ 0`.  No boundedness of `Q` is available or claimed.
* **The zero-order coefficient of the `Q`-equation is bounded.**  `A_t = div F_t + ⟨∇log ρ₀, F_t⟩` has `∇log ρ₀ = -βq x + O(1)` unbounded, but
  `mn_force_bound` (`j = 0`) gives `‖A_t‖_∞ ≤ C‖v_t‖_{Σ^m}` (the weighted decay `‖x‖ |F_t| ≲ ‖v_t‖` is inside `mov_operators_force_gen`).
  The drift `b_t = ν ∇log ρ₀ + F_t` satisfies `⟨b_t(x), x⟩ ≤ -q‖x‖² + M‖x‖` with `M = M₀ + C‖v_t‖` (the Euler equation again).
* Why the maximum principle is applicable: `Q ∈ C^{1,2}` in the sense needed (`mneQ_cd`: `C³` in `x`; `mne_Q_hasDerivAt`: two-sided time derivative for
  `t > 0`; `mne_joint`: joint continuity of `(t,x) ↦ V_t(x)` on `[0,∞)×ℝ^d`).

## Route (deviation from `SC63_REPORT` 2.3(c): no separate Lyapunov `δφ`; one comparison lemma, used by `mnf_master`, used three times)

1. (`Aux1`, this file) **`mnf_comparison`**: weak maximum principle on `[0,T]×ℝ^d` in the Gaussian growth class.  `P ∈ C^{1,2}` jointly continuous,
   `P_t ≥ νΔP + ⟨b,∇P⟩ + cP` with `c ≤ 0`, `P(0,·) ≥ 0`, a positive strict supersolution `φ` of `∂_t - νΔ - ⟨b,∇·⟩` (no zero-order term), and
   `P ≥ -εφ` outside a ball for every `ε > 0`.  Then `P ≥ 0`.  Proof: a negative minimum of `P + εφ` is attained (coercivity), at a point with `t_0 > 0`,
   where `∂_t ≤ 0`, `∇ = 0`, `Δ ≥ 0` (uses `lu_laplacian_nonpos`, `pm_time_deriv_nonneg`).
2. (`Aux2`) The Lyapunov function `φ = exp(λt + κ‖x‖²)`: `∇φ = 2κ x φ`, `Δφ = (2κd + 4κ²‖x‖²)φ`, strict supersolution for `0 < κ`, `2νκ < q` (`mnf_lyap_super`).
3. (`Aux3`) Thermal data: `mnf_euler`, the Gaussian lower bound `mnf_rho_lower`; sup bounds `mnf_Vbound`, `mnf_Abound`, `mnf_drift_bound`, growth `mnf_Q_growth`
   (`|Q_t| ≤ K exp((5βq/16)‖x‖²)`), coercivity `mnf_hgrow`.
4. (`Aux4`) **`mnf_master`**: `P = γ(t) + α(t) Q_t` with `c (γ + αQ) ≤ γ' + (α' + αA) Q`, `c ≤ 0`, `|P| ≤ K_p exp((5βq/16)‖x‖²)`, `P(0) ≥ 0` ⇒ `P ≥ 0`
   (`Lyapunov exp(l t + (3βq/8)‖x‖²)`, `2νκ = 3q/4 < q`).
5. (`Aux5`) **`mnf_ratio`**: the three comparisons (`e^{-Λ}Q ≥ 0`; `5/4 - e^{-Λ}Q ≥ 0`; `e^{Λ}Q - 3/4 ≥ 0`), `Λ(t) = (C_AK/a)(1-e^{-at}) ≤ 1/4`.
6. (`Aux6`) Output for N9: **`mov63_positive_solution`** and `mov63_positive_solution_f0` (assembly with `mov63_signed_solution`: `hnn` discharged),
   `mnf_bridge`, `mnf_F0_eq`, `mnf_sup_of_initial`.

## Result (statement for N9)

For the thermal data `H : Mov2dTh d s β q ρ`: there is `c > 0` such that for every integer `m > d/2+3` there are `ε, C > 0` with: for every mass-zero `x₀ ∈ Σ^m` with
`‖x₀‖ ≤ ε` and `sup |V_{x₀}/√ρ| ≤ 1/4`, the N5/N6 mild solution gives a member of `MovInSmallClass .. (C‖x₀‖) (c/2) f₀ ρ_·` with
`ρ/2 ≤ ρ_t ≤ 2ρ` for all `t ≥ 0`, `x` (so `ρ_t > 0`, `C⁻¹ρ ≤ ρ_t ≤ Cρ` with `C = 2` is the ratio clause of `MovNonlinearConclusion`).
The hypothesis `sup |f₀| ≤ 1/4` follows from `MovInitialClass .. ε_*` with `ε_* ≤ 1/4` (`mnf_sup_of_initial`); `V_{x₀} = √ρ f₀` for `x₀ = ofFun (√ρ f₀)`, `f₀ ∈ C³`
(`mnf_bridge`; `j ≥ 2` in `MovInitialClass` gives `f₀ ∈ C³`).

## Not done (gaps)

* `IsProbDensity`, strict positivity `ρ_t > 0` and the class are inside the theorem; the other conjuncts of `MovNonlinearConclusion` (`MovInitialClass` for the given `f₀` as the
  datum of `x₀`, `MovDecayBounds`, `ψ`-class) are N8/N9.  `‖x₀‖ ≤ ε` is an `ε` depending only on `H, m`.
* The smallness of `‖x₀‖` required by N7 is only through the rate `a = c/2` and `Λ_∞ = C_AK/a ≤ 1/4`.
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.MS.Lc HRS.MS.PoisMax

variable {d : ℕ}

section Calc

lemma mnf_gradient_add_smul {f g : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (a : ℝ) :
    gradient (fun z => f z + a * g z) x = gradient f x + a • gradient g x := by
  refine ext_inner_left ℝ fun e => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, inner_add_right, inner_smul_right,
    HRS.MS.PoisKolm.kl_inner_gradient, HRS.MS.PoisKolm.kl_inner_gradient]
  have h : fderiv ℝ (fun z => f z + a * g z) x = fderiv ℝ f x + a • fderiv ℝ g x :=
    (hf.hasFDerivAt.add (hg.hasFDerivAt.const_mul a)).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma mnf_laplacian_add_smul {f g : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (a : ℝ) :
    Laplacian.laplacian (fun z => f z + a * g z) x = Laplacian.laplacian f x + a * Laplacian.laplacian g x := by
  have h1 : (fun z => f z + a * g z) = f + a • g := by
    funext z; simp [smul_eq_mul]
  have h2 : ContDiffAt ℝ 2 (a • g) x := hg.const_smul a
  rw [h1, ContDiffAt.laplacian_add hf h2, InnerProductSpace.laplacian_smul a hg]
  simp [smul_eq_mul]

end Calc

section Comparison

/-- **Weak maximum principle (comparison) in the Gaussian growth class.**  See the module docstring. -/
theorem mnf_comparison {T ν : ℝ} (hν : 0 ≤ ν)
    {P Pt φ φt : ℝ → Euc d → ℝ} {b : ℝ → Euc d → Euc d} {c : ℝ → Euc d → ℝ}
    (hP2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (P t))
    (hφ2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (φ t))
    (hPc : ContinuousOn (fun p : ℝ × Euc d => P p.1 p.2) (Icc 0 T ×ˢ univ))
    (hφc : ContinuousOn (fun p : ℝ × Euc d => φ p.1 p.2) (Icc 0 T ×ˢ univ))
    (hPd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => P s x) (Pt t x) (Icc 0 T) t)
    (hφd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => φ s x) (φt t x) (Icc 0 T) t)
    (hPeq : ∀ t ∈ Ioc 0 T, ∀ x, ν * Laplacian.laplacian (P t) x + inner ℝ (b t x) (gradient (P t) x) +
      c t x * P t x ≤ Pt t x)
    (hc : ∀ t ∈ Ioc 0 T, ∀ x, c t x ≤ 0)
    (hφs : ∀ t ∈ Ioc 0 T, ∀ x, ν * Laplacian.laplacian (φ t) x + inner ℝ (b t x) (gradient (φ t) x) < φt t x)
    (hφpos : ∀ t ∈ Icc 0 T, ∀ x, 0 < φ t x)
    (hgrow : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ → -(ε * φ t x) < P t x)
    (h0 : ∀ x, 0 ≤ P 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ P t x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t1, ht1, x1, hx1⟩ := hcon
  have hφ1 := hφpos t1 ht1 x1
  set ε : ℝ := -P t1 x1 / (2 * φ t1 x1) with hε
  have hεpos : 0 < ε := by rw [hε]; exact div_pos (by linarith) (by positivity)
  have hεφ : ε * φ t1 x1 = -P t1 x1 / 2 := by rw [hε]; field_simp
  set W : ℝ → Euc d → ℝ := fun t z => P t z + ε * φ t z with hW
  have hW1 : W t1 x1 < 0 := by simp only [hW]; linarith
  obtain ⟨R, hR⟩ := hgrow ε hεpos
  set R' : ℝ := max R ‖x1‖ with hR'
  have hK : IsCompact (Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) R') :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKne : (Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) R').Nonempty :=
    ⟨(t1, x1), ht1, by rw [mem_closedBall_zero_iff]; exact le_max_right R ‖x1‖⟩
  have hWc : ContinuousOn (fun p : ℝ × Euc d => W p.1 p.2) (Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) R') :=
    (hPc.mono (prod_mono le_rfl (subset_univ _))).add ((hφc.mono (prod_mono le_rfl (subset_univ _))).const_mul ε)
  obtain ⟨⟨t0, z0⟩, hp, hpmin⟩ := hK.exists_isMinOn hKne hWc
  have hp1 : (t1, x1) ∈ Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) R' :=
    ⟨ht1, by rw [mem_closedBall_zero_iff]; exact le_max_right R ‖x1‖⟩
  have hle1 : W t0 z0 ≤ W t1 x1 := by
    have := hpmin hp1
    simpa using this
  have hneg : W t0 z0 < 0 := lt_of_le_of_lt hle1 hW1
  have hglob : ∀ t ∈ Icc 0 T, ∀ z, W t0 z0 ≤ W t z := by
    intro t ht z
    by_cases hz : ‖z‖ ≤ R'
    · have := hpmin (show (t, z) ∈ Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) R' from ⟨ht, by simpa using hz⟩)
      simpa using this
    · push Not at hz
      have h1 := hR t ht z ((le_max_left R ‖x1‖).trans hz.le)
      have h2 : 0 < W t z := by simp only [hW]; linarith
      linarith
  have ht0 : t0 ∈ Icc 0 T := hp.1
  have ht0pos : 0 < t0 := by
    rcases ht0.1.eq_or_lt with h | h
    · exfalso
      have h1 := h0 z0
      have h2 := hφpos t0 ht0 z0
      have h3 : P t0 z0 = P 0 z0 := by rw [← h]
      have h4 : 0 < W t0 z0 := by
        simp only [hW]
        have := mul_pos hεpos h2
        linarith
      linarith
    · exact h
  have ht0' : t0 ∈ Ioc 0 T := ⟨ht0pos, ht0.2⟩
  have hPz : P t0 z0 < 0 := by
    have := hφpos t0 ht0 z0
    simp only [hW] at hneg
    nlinarith
  -- spatial extremality
  have hPc2 := hP2 t0 ht0
  have hφc2 := hφ2 t0 ht0
  have hWc2 : ContDiff ℝ 2 (W t0) := hPc2.add (contDiff_const.mul hφc2)
  have hloc : IsLocalMax (fun z => -W t0 z) z0 :=
    IsMaxOn.isLocalMax (s := univ) (fun z _ => by
      have := hglob t0 ht0 z
      simp only [Set.mem_ofPred_eq]
      linarith) Filter.univ_mem
  have hlap : 0 ≤ Laplacian.laplacian (W t0) z0 := by
    have := lu_laplacian_nonpos hWc2.neg hloc
    have e : Laplacian.laplacian (fun z => -W t0 z) z0 = -Laplacian.laplacian (W t0) z0 := by
      exact congrFun (InnerProductSpace.laplacian_neg (f := W t0)) z0
    linarith
  have hgrad : gradient (W t0) z0 = 0 := by
    have h1 : fderiv ℝ (fun z => -W t0 z) z0 = 0 := hloc.fderiv_eq_zero
    have h2 : fderiv ℝ (W t0) z0 = 0 := by
      have e : fderiv ℝ (fun z => -W t0 z) z0 = -fderiv ℝ (W t0) z0 := fderiv_fun_neg
      rw [e] at h1
      simpa using h1
    unfold gradient
    rw [h2]; simp
  have hPd0 : DifferentiableAt ℝ (P t0) z0 := (hPc2.differentiable (by norm_num)) z0
  have hφd0 : DifferentiableAt ℝ (φ t0) z0 := (hφc2.differentiable (by norm_num)) z0
  have hgW : gradient (W t0) z0 = gradient (P t0) z0 + ε • gradient (φ t0) z0 :=
    mnf_gradient_add_smul hPd0 hφd0 ε
  have hlW : Laplacian.laplacian (W t0) z0 =
      Laplacian.laplacian (P t0) z0 + ε * Laplacian.laplacian (φ t0) z0 :=
    mnf_laplacian_add_smul hPc2.contDiffAt hφc2.contDiffAt ε
  -- time derivative
  have hdW : HasDerivWithinAt (fun s => W s z0) (Pt t0 z0 + ε * φt t0 z0) (Icc 0 T) t0 :=
    (hPd t0 ht0' z0).add ((hφd t0 ht0' z0).const_mul ε)
  have hnn := pm_time_deriv_nonneg ht0pos ht0.2 hdW.neg (fun s hs => by
    have := hglob s hs z0
    show -W s z0 ≤ -W t0 z0
    linarith)
  -- the contradiction
  have e1 := hPeq t0 ht0' z0
  have e2 := hφs t0 ht0' z0
  have e3 := hc t0 ht0' z0
  have hgradP : gradient (P t0) z0 = -(ε • gradient (φ t0) z0) := by
    rw [hgrad] at hgW
    exact eq_neg_of_add_eq_zero_left (by simpa using hgW.symm)
  have hcP : 0 ≤ c t0 z0 * P t0 z0 := mul_nonneg_of_nonpos_of_nonpos e3 hPz.le
  have hlapP : -(ε * Laplacian.laplacian (φ t0) z0) ≤ Laplacian.laplacian (P t0) z0 := by
    linarith
  rw [hgradP, inner_neg_right, inner_smul_right] at e1
  have h5 : ν * (-(ε * Laplacian.laplacian (φ t0) z0)) ≤ ν * Laplacian.laplacian (P t0) z0 :=
    mul_le_mul_of_nonneg_left hlapP hν
  have h6 : 0 < ε * (φt t0 z0 - (ν * Laplacian.laplacian (φ t0) z0 + inner ℝ (b t0 z0) (gradient (φ t0) z0))) :=
    mul_pos hεpos (by linarith)
  nlinarith

end Comparison

end HRS.MS.Mov63

end
