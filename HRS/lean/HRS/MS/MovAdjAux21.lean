import HRS.MS.MovAdjAux20

/-!
# S6.7 (packet P4, part 7): `S67DuhData` for the classical adjoint solution

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.Mov63

variable {d : ℕ}

/-- `β · generatorW = kolmL (βq) B + β J`. -/
theorem s67_aL (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) {B : Euc d → Euc d}
    (hgrad : ∀ x, gradient (fun y => Real.log (ρ y)) x = (-(β * q)) • x + B x) (r : ℝ) (u : Euc d → ℝ)
    (x : Euc d) :
    β * generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u x - kolmL (β * q) B u x =
      β * s67J d s ρ u x := by
  rw [s67_gen_eq, s67_drift_eq hd hs0 hsd hq hβ hρ x, hgrad x]
  unfold kolmL
  rw [real_inner_smul_left]
  have : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
  have h2 : β * (β⁻¹ * Laplacian.laplacian u x + β⁻¹ * inner ℝ (-(β * q) • x + B x) (gradient u x) +
      s67J d s ρ u x) - (Laplacian.laplacian u x + inner ℝ (-(β * q) • x + B x) (gradient u x)) =
      β * s67J d s ρ u x := by
    linear_combination (Laplacian.laplacian u x + inner ℝ (-(β * q) • x + B x) (gradient u x)) * this
  exact h2

variable {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}

theorem s67_hmem {t β : ℝ} (hβ : 0 < β) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) (t / β)) :
    t - β * σ ∈ Icc (0 : ℝ) t := by
  constructor
  · have := (le_div_iff₀ hβ).1 hσ.2; linarith
  · have := mul_nonneg hβ.le hσ.1; linarith

/-- the integrated form (FTC), one direction -/
theorem s67_ftc_le (hf : IsClassicalAdjointW C t φ f) {β : ℝ} (hβ : 0 < β) (y : Euc d) {s0 σ : ℝ}
    (hs0 : 0 ≤ s0) (hle : s0 ≤ σ) (hσ : σ ≤ t / β) :
    f (t - β * σ) y - f (t - β * s0) y =
      ∫ r in s0..σ, β * generatorW C (t - β * r) (f (t - β * r)) y := by
  have hT : ∀ r ∈ Icc (0 : ℝ) (t / β), t - β * r ∈ Icc (0 : ℝ) t := fun r hr => s67_hmem hβ hr
  have hsub : Icc s0 σ ⊆ Icc (0 : ℝ) (t / β) := Icc_subset_Icc hs0 hσ
  have hcont : ContinuousOn (fun r => f (t - β * r) y) (Icc s0 σ) := by
    have h1 : ContinuousOn (fun r : ℝ => t - β * r) (Icc s0 σ) := by fun_prop
    exact (s67_cont_time hf y).comp h1 (fun r hr => hT r (hsub hr))
  have hderiv : ∀ r ∈ Ioo s0 σ, HasDerivAt (fun r => f (t - β * r) y)
      (β * generatorW C (t - β * r) (f (t - β * r)) y) r := by
    intro r hr
    have hr0 : 0 < r := hs0.trans_lt hr.1
    have hrT : r < t / β := hr.2.trans_le hσ
    have hrt : t - β * r ∈ Ioo (0 : ℝ) t := by
      constructor
      · have := (lt_div_iff₀ hβ).1 hrT; linarith
      · have := mul_pos hβ hr0; linarith
    have h1 := hf.time_deriv y _ hrt
    have h2 : HasDerivAt (fun r : ℝ => t - β * r) (-β) r := by
      simpa using ((hasDerivAt_id r).const_mul β).const_sub t
    have h3 := h1.scomp r h2
    refine h3.congr_deriv ?_
    simp only [smul_eq_mul]; ring
  have hint : IntervalIntegrable (fun r => β * generatorW C (t - β * r) (f (t - β * r)) y) volume s0 σ := by
    refine ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hle ?_
    have hg : ContinuousOn (fun r : ℝ => generatorW C (t - β * r) (f (t - β * r)) y) (Icc s0 σ) := by
      have := (s67_reparam (G := fun r y => generatorW C r (f r) y) hβ hf.cont_time_deriv).comp
        (show ContinuousOn (fun r : ℝ => ((r, y) : ℝ × Euc d)) (Icc s0 σ) by fun_prop)
        (fun r hr => ⟨hsub hr, mem_univ _⟩)
      exact this
    exact continuousOn_const.mul hg
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint).symm

theorem s67_ftc (hf : IsClassicalAdjointW C t φ f) {β : ℝ} (hβ : 0 < β) (y : Euc d) {s0 σ : ℝ}
    (hs0 : s0 ∈ Icc (0 : ℝ) (t / β)) (hσ : σ ∈ Icc (0 : ℝ) (t / β)) :
    f (t - β * σ) y - f (t - β * s0) y =
      ∫ r in s0..σ, β * generatorW C (t - β * r) (f (t - β * r)) y := by
  rcases le_total s0 σ with h | h
  · exact s67_ftc_le hf hβ y hs0.1 h hσ.2
  · have := s67_ftc_le hf hβ y hσ.1 h hs0.2
    rw [intervalIntegral.integral_symm, ← this]
    ring

/-- **The data.** -/
theorem s67_duhData (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) {B : Euc d → Euc d}
    (hBc : Continuous B)
    (hgrad : ∀ x, gradient (fun y => Real.log (ρ y)) x = (-(β * q)) • x + B x)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f)
    (hSb : ∃ KS : ℝ, ∀ v ∈ Icc (0 : ℝ) t, ∀ y, |s67J d s ρ (f v) y| ≤ KS) :
    S67DuhData (β * q) B (t / β) (fun σ y => f (t - β * σ) y)
      (fun σ y => β * generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) (t - β * σ)
        (f (t - β * σ)) y)
      (fun σ y => β * s67J d s ρ (f (t - β * σ)) y) := by
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (t / β), t - β * σ ∈ Icc (0 : ℝ) t := fun σ hσ => s67_hmem hβ hσ
  have hacont : ContinuousOn (fun p : ℝ × Euc d => β * generatorW ((quadraticGradientDyn d s q β).coeff
      (fun _ => ρ)) (t - β * p.1) (f (t - β * p.1)) p.2) (Icc (0 : ℝ) (t / β) ×ˢ univ) :=
    continuousOn_const.mul (s67_reparam (G := fun r y => generatorW ((quadraticGradientDyn d s q β).coeff
      (fun _ => ρ)) r (f r) y) hβ hf.cont_time_deriv)
  refine ⟨fun σ hσ => hf.c2 _ (hmem σ hσ), ?_, s67_reparam (G := fun r y => f r y) hβ (s67_cont_val hf),
    s67_reparam (G := fun r y => fderiv ℝ (f r) y) hβ (s67_cont_fderiv hf), hacont, ?_, ?_, ?_, fun σ hσ s0 hs0' y => s67_ftc hf hβ y hs0' hσ,
    fun σ hσ y => s67_aL hd hs0 hsd hq hβ hρ hgrad _ _ y⟩
  · obtain ⟨K0, K1, K2, hK⟩ := s67_bd_all hf
    exact ⟨K0, K1, K2, fun σ hσ y => hK _ (hmem σ hσ) y⟩
  · obtain ⟨Bf, hBf⟩ := hf.bdd_time_deriv
    refine ⟨|β| * |Bf|, fun σ hσ y => ?_⟩
    rw [abs_mul]
    have h1 := hBf _ (hmem σ hσ) y
    have h2 : |β| * |generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) (t - β * σ)
        (f (t - β * σ)) y| ≤ |β| * (|Bf| * (1 + ‖y‖)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
        (abs_nonneg _)
    simpa [mul_assoc] using h2
  · -- Scont: `S = a - kolmL`
    have hk : ContinuousOn (fun p : ℝ × Euc d => kolmL (β * q) B (f (t - β * p.1)) p.2)
        (Icc (0 : ℝ) (t / β) ×ˢ univ) := s67_reparam (G := fun r y => kolmL (β * q) B (f r) y) hβ (s67_cont_kolm hf (β * q) hBc)
    refine (hacont.sub hk).congr fun p hp => ?_
    exact (s67_aL hd hs0 hsd hq hβ hρ hgrad _ _ p.2).symm
  · obtain ⟨KS, hKS⟩ := hSb
    refine ⟨|β| * |KS|, fun σ hσ y => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hKS _ (hmem σ hσ) y).trans (le_abs_self _)) (abs_nonneg _)

end HRS.MS.MovAdj
