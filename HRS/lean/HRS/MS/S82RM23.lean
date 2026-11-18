import HRS.MS.S82RM22

/-!
# S8.2 R02 (S82R), M23: measure-level comparison of a pinned and an unpinned field ensemble
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

lemma s82r_int_indicator {n : ℕ} (P : Measure (Fin n → E)) [IsProbabilityMeasure P] (i0 : Fin n)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ x, A.indicator (fun _ => (1 : ℝ)) (x i0) ∂P = P.real ((fun x : Fin n → E => x i0) ⁻¹' A) := by
  have hm : MeasurableSet ((fun x : Fin n → E => x i0) ⁻¹' A) := measurable_pi_apply i0 hA
  have : (fun x : Fin n → E => A.indicator (fun _ => (1 : ℝ)) (x i0)) =
      ((fun x : Fin n → E => x i0) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext x; by_cases h : x i0 ∈ A <;> simp [Set.indicator, h]
  rw [this, integral_indicator_const _ hm]; simp

lemma s82r_Gm_int {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {lam : ℝ}
    (hlam : 0 ≤ lam) {K : ℝ} (hK : 0 ≤ K) (u : E) :
    ∫ z, s82r_Gm V lam K z u ∂μ ≤ K * (lam * V.γ) + K ^ 2 * (lam * V.γ) := by
  have hdi : Integrable (fun y => s82r_d V lam y u) μ :=
    Integrable.of_bound (s82r_d_meas V lam u).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (s82r_d_nonneg V hlam z u)]; exact s82r_d_lt_one V lam z u)
  unfold s82r_Gm
  rw [integral_add (hdi.const_mul K) (integrable_const _), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (s82r_d_int V hlam u) hK) le_rfl

/-- Measure-level comparison of the field ensembles with and without the fractional pins. -/
theorem s82r_field_compare {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    {ψ0 : E → ℝ} {M M₁ : ℝ} (hψ : IsField μ ψ0 M M₁) {m n : ℕ} [NeZero n] (p : Fin m → E)
    (t : Fin m → ℝ) (ht : ∀ ℓ, 0 ≤ t ℓ) {lam : ℝ} (hlam : 0 ≤ lam) {P : ℝ}
    (hP : (∑ ℓ, t ℓ) * V.γ + lam * n * V.γ ≤ P)
    (hθ1 : ((n : ℝ) - 1) * (Real.exp (M + (M₁ + P)) * (lam * V.γ) +
      Real.exp (M + (M₁ + P)) ^ 2 * (lam * V.γ)) < 1)
    {ρ : E → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρi : Integrable ρ μ)
    (hsup : ∀ᵐ z ∂μ, (1 - 1 / (n : ℝ)) * ρ z + (((n : ℝ) - 1) / n) *
        s82r_Gam μ (s82r_Gm V lam (Real.exp (M + (M₁ + P)))) ρ z ≤
      ρ z - (1 / (n : ℝ)) * s82r_bm V p t (Real.exp (M + (M₁ + P))) z)
    (i0 : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |(fieldLaw V ψ0 lam n).real ((fun x : Fin n → E => x i0) ⁻¹' A) -
      (fieldLaw V (s82r_Fld V p t Finset.univ ψ0) lam n).real ((fun x : Fin n → E => x i0) ⁻¹' A)| ≤
      ∫ z in A, ρ z ∂μ := by
  set K := Real.exp (M + (M₁ + P)) with hK
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hψ1 := s82r_fld_isField V hψ p t ht Finset.univ
  have hH := s82r_hyp V hψ p t ht hlam hP (n := n)
  have hD0 := s82r_kap_dens V hψ hlam n
  have hD1 := s82r_kap_dens V hψ1 hlam n
  set S0 := fieldSpec (V := V) hψ hlam n with hS0
  set S1 := fieldSpec (V := V) hψ1 hlam n with hS1
  have hθ0 : 0 ≤ K * (lam * V.γ) + K ^ 2 * (lam * V.γ) := by
    have := V.γ_nonneg; positivity
  have hθ : ∀ u, ∫ z, s82r_Gm V lam K z u ∂μ ≤ K * (lam * V.γ) + K ^ 2 * (lam * V.γ) :=
    fun u => s82r_Gm_int V hlam hK0 u
  have hsym := s82r_Gm_symm V lam K
  have e0 : S0.P = fieldLaw V ψ0 lam n := fieldSpec_P hψ hlam n
  have e1 : S1.P = fieldLaw V (s82r_Fld V p t Finset.univ ψ0) lam n := fieldSpec_P hψ1 hlam n
  haveI : IsProbabilityMeasure S0.P := S0.isProb
  haveI : IsProbabilityMeasure S1.P := S1.isProb
  have a1 := s82r_dual_bound hD0 hD1 hH hsym hθ0 hθ hθ1 hρ hρ0 hρi hsup i0 hA
  have a2 := s82r_dual_bound hD1 hD0 hH.symm hsym hθ0 hθ hθ1 hρ hρ0 hρi hsup i0 hA
  rw [s82r_int_indicator S0.P i0 hA, s82r_int_indicator S1.P i0 hA, e0, e1] at a1
  rw [s82r_int_indicator S0.P i0 hA, s82r_int_indicator S1.P i0 hA, e0, e1] at a2
  rw [abs_le]; constructor <;> linarith

end HRS.MS.S82R

end
