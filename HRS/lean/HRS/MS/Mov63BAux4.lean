import HRS.MS.Mov63BAux3

/-!
# S6.3 packet N2a (4): mass conservation `∫ √ρ_* B(φ, ψ) = 0` for Schwartz data

Namespace `HRS.MS.Mov63`, helper prefix `mnb_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.

For Schwartz `φ, ψ`: `√ρ_* B(φ,ψ) = div((√ρ_* φ) ∇g*(√ρ_* ψ))`, a divergence of a `C¹` field with Gaussian-decaying
components and derivatives (`mv1_force_deriv_bound`), so its integral vanishes (`mnb_integral_fderiv_zero`, integration by
parts against the constant `1`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1

variable {d : ℕ}

section Mass

variable {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

lemma mnb_integral_fderiv_zero {g : Euc d → ℝ} (v : Euc d) (hg : Differentiable ℝ g) (h1 : Integrable g)
    (h2 : Integrable (fun x => fderiv ℝ g x v)) : ∫ x, fderiv ℝ g x v = 0 := by
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := fun _ : Euc d => (1 : ℝ)) (g := g) (v := v) (by simp) (by simpa using h2) (by simpa using h1)
    (fun x _ => differentiableAt_const _) (fun x _ => hg x)
  simpa using this

lemma mnb_gauss_int (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Euc d => Real.exp (-c * ‖x‖ ^ 2)) := by
  have := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c) (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith) hc
  simpa using this

lemma mnb_GA (hρ : MovRhoData d ρ) (w : 𝓢R) (k : ℕ) :
    ∃ c E : ℝ, 0 < c ∧ movb2_GA k c E (fun z => Real.sqrt (ρ z) * w z) := by
  obtain ⟨c, hc, hj⟩ := mv1_gauss_common (mv1_h_gauss hρ w).2 k
  choose! C hC using hj
  refine ⟨c, ∑ j ∈ Finset.range (k + 1), |C j|, hc, fun i hi y => ?_⟩
  refine (hC i hi y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega)))

/-- The force of a Schwartz-type source is `C¹` with bounded value and derivative. -/
lemma mnb_force_bdd (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : MovRhoData d ρ) (w : 𝓢R) :
    ContDiff ℝ 1 (movForce d s (fun z => Real.sqrt (ρ z) * w z)) ∧
      ∃ M : ℝ, ∀ x, ‖movForce d s (fun z => Real.sqrt (ρ z) * w z) x‖ ≤ M ∧
        ‖fderiv ℝ (movForce d s (fun z => Real.sqrt (ρ z) * w z)) x‖ ≤ M := by
  obtain ⟨c, E, hc, hga⟩ := mnb_GA hρ w 2
  have hh := (mv1_h_gauss hρ w).1
  obtain ⟨C0, hC0, h0⟩ := mv1_force_deriv_bound (d := d) (s := s) hd hs0 hsd hc 0
  obtain ⟨C1, hC1, h1⟩ := mv1_force_deriv_bound (d := d) (s := s) hd hs0 hsd hc 1
  have hh1' : ContDiff ℝ 1 (fun z => Real.sqrt (ρ z) * w z) := hh.of_le (by norm_num)
  have hh2' : ContDiff ℝ 2 (fun z => Real.sqrt (ρ z) * w z) := hh.of_le (by norm_num)
  have hh1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fun z => Real.sqrt (ρ z) * w z) := by simpa using hh1'
  have hh2 : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (fun z => Real.sqrt (ρ z) * w z) := by simpa using hh2'
  obtain ⟨-, hb0⟩ := h0 hh1 (movb2_GA_mono (by norm_num) hga)
  obtain ⟨hcd1, hb1⟩ := h1 hh2 hga
  refine ⟨by simpa using hcd1, C0 * E + C1 * E, fun x => ⟨?_, ?_⟩⟩
  · have := (hb0 x).1
    rw [norm_iteratedFDeriv_zero] at this
    have hE : 0 ≤ C1 * E := mul_nonneg hC1 (movb2_GA_nonneg hga)
    linarith
  · have := (hb1 x).1
    rw [norm_iteratedFDeriv_one] at this
    have hE : 0 ≤ C0 * E := mul_nonneg hC0 (movb2_GA_nonneg hga)
    linarith

/-- **Mass conservation on Schwartz data**: `∫ √ρ_* B(φ,ψ) = 0`. -/
theorem mnb_mass (H : Mov2dTh d s β q ρ) (φ ψ : 𝓢R) :
    ∫ x, Real.sqrt (ρ x) * movB d s ρ (⇑φ) (⇑ψ) x = 0 := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρ := mnb_rhoData H
  set F : Euc d → Euc d := movForce d s (fun z => Real.sqrt (ρ z) * ψ z) with hF
  set h : Euc d → ℝ := fun z => Real.sqrt (ρ z) * φ z with hh
  obtain ⟨hFc, M, hM⟩ := mnb_force_bdd hd1 H.hs0 H.hsd hρ ψ
  obtain ⟨c, E, hc, hga⟩ := mnb_GA hρ φ 1
  obtain ⟨hb0, hb1⟩ := movb2_GA_01 hga
  have hE := movb2_GA_nonneg hga
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have hhs : ContDiff ℝ ∞ h := (mv1_h_gauss hρ φ).1
  have hh1 : ContDiff ℝ 1 h := hhs.of_le (by norm_num)
  have hFd : Differentiable ℝ F := hFc.differentiable (by norm_num)
  have hhd : Differentiable ℝ h := hh1.differentiable (by norm_num)
  have hFi : ∀ i : Fin d, ContDiff ℝ 1 (fun y => F y i) := fun i => contDiff_euclidean.1 hFc i
  set gi : Fin d → Euc d → ℝ := fun i y => h y * F y i with hgi
  have hgic : ∀ i, ContDiff ℝ 1 (gi i) := fun i => hh1.mul (hFi i)
  have hexp := mnb_gauss_int (d := d) hd1 hc
  -- derivative formula of the components
  have hder : ∀ i : Fin d, ∀ x, fderiv ℝ (gi i) x (EuclideanSpace.single i 1) =
      h x * (fderiv ℝ F x (EuclideanSpace.single i 1)) i +
        fderiv ℝ h x (EuclideanSpace.single i 1) * F x i := by
    intro i x
    have hFi' : HasFDerivAt (fun y => F y i)
        ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ F x)) x :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x (hFd x).hasFDerivAt
    have := ((hhd x).hasFDerivAt.mul hFi').fderiv
    change fderiv ℝ (gi i) x = _ at this
    rw [this]
    simp
    ring
  -- integrability of the components and of their derivatives
  have hint1 : ∀ i, Integrable (gi i) := fun i => by
    refine Integrable.mono' (hexp.const_mul (E * M)) (hgic i).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    show ‖h y * F y i‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    have h1 : |h y| ≤ E * Real.exp (-c * ‖y‖ ^ 2) := hb0 y
    have h2 : ‖F y i‖ ≤ M := by
      have := PiLp.norm_apply_le (F y) i
      exact this.trans (hM y).1
    calc |h y| * ‖F y i‖ ≤ (E * Real.exp (-c * ‖y‖ ^ 2)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hE (Real.exp_pos _).le)
      _ = E * M * Real.exp (-c * ‖y‖ ^ 2) := by ring
  have hint2 : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (gi i) x (EuclideanSpace.single i 1)) := fun i => by
    refine Integrable.mono' (hexp.const_mul (2 * E * M))
      (((hgic i).continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    show ‖fderiv ℝ (gi i) y (EuclideanSpace.single i 1)‖ ≤ _
    rw [hder i y]
    have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    have h1 : |h y| ≤ E * Real.exp (-c * ‖y‖ ^ 2) := hb0 y
    have h2 : ‖(fderiv ℝ F y (EuclideanSpace.single i 1)) i‖ ≤ M := by
      have h3 := PiLp.norm_apply_le (fderiv ℝ F y (EuclideanSpace.single i 1)) i
      have h4 := (fderiv ℝ F y).le_opNorm (EuclideanSpace.single i (1 : ℝ) : Euc d)
      rw [hn, mul_one] at h4
      exact h3.trans (h4.trans (hM y).2)
    have h5 : ‖fderiv ℝ h y (EuclideanSpace.single i 1)‖ ≤ E * Real.exp (-c * ‖y‖ ^ 2) := by
      have h6 := (fderiv ℝ h y).le_opNorm (EuclideanSpace.single i (1 : ℝ) : Euc d)
      rw [hn, mul_one] at h6
      exact h6.trans (hb1 y)
    have h7 : ‖F y i‖ ≤ M := (PiLp.norm_apply_le (F y) i).trans (hM y).1
    have hex0 : 0 ≤ E * Real.exp (-c * ‖y‖ ^ 2) := mul_nonneg hE (Real.exp_pos _).le
    calc ‖h y * (fderiv ℝ F y (EuclideanSpace.single i 1)) i +
          fderiv ℝ h y (EuclideanSpace.single i 1) * F y i‖
        ≤ ‖h y * (fderiv ℝ F y (EuclideanSpace.single i 1)) i‖ +
          ‖fderiv ℝ h y (EuclideanSpace.single i 1) * F y i‖ := norm_add_le _ _
      _ ≤ (E * Real.exp (-c * ‖y‖ ^ 2)) * M + (E * Real.exp (-c * ‖y‖ ^ 2)) * M := by
          rw [norm_mul (h y), norm_mul (fderiv ℝ h y (EuclideanSpace.single i 1)), Real.norm_eq_abs]
          exact add_le_add (mul_le_mul h1 h2 (norm_nonneg _) hex0) (mul_le_mul h5 h7 (norm_nonneg _) hex0)
      _ = 2 * E * M * Real.exp (-c * ‖y‖ ^ 2) := by ring
  have hzero : ∀ i : Fin d, ∫ x, fderiv ℝ (gi i) x (EuclideanSpace.single i 1) = 0 := fun i =>
    mnb_integral_fderiv_zero _ ((hgic i).differentiable (by norm_num)) (hint1 i) (hint2 i)
  -- pointwise identity: `√ρ B = ∑ ∂_i (φ̃ F_i)`
  have hpt : ∀ x, Real.sqrt (ρ x) * movB d s ρ (⇑φ) (⇑ψ) x =
      ∑ i : Fin d, fderiv ℝ (gi i) x (EuclideanSpace.single i 1) := by
    intro x
    have hpos : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hρ.pos x)
    have hB : movB d s ρ (⇑φ) (⇑ψ) x =
        (Real.sqrt (ρ x))⁻¹ * movDiv (fun y => h y • F y) x := rfl
    rw [hB, mul_inv_cancel_left₀ hpos.ne', mv1_movDiv_smul (hhd x) (hFd x)]
    unfold movDiv
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hder i x]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => hint2 i)]
  exact Finset.sum_eq_zero fun i _ => hzero i

end Mass

end HRS.MS.Mov63

end
