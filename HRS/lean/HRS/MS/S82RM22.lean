import HRS.MS.S82RM21

/-!
# S8.2 R02 (S82R), M22: the transfer hypothesis for a pinned vs unpinned field ensemble
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

/-- the interaction kernel `Γ` of the transfer -/
def s82r_Gm {μ : Measure E} (V : WeakPotential μ) (lam K : ℝ) (z u : E) : ℝ :=
  K * s82r_d V lam z u + K ^ 2 * (lam * V.γ)

/-- the pin source `b` -/
def s82r_bm {μ : Measure E} (V : WeakPotential μ) {m : ℕ} (p : Fin m → E) (t : Fin m → ℝ) (K : ℝ)
    (z : E) : ℝ := ∑ ℓ, (K * s82r_d V (t ℓ) z (p ℓ) + K ^ 2 * (t ℓ * V.γ))

lemma s82r_Gm_symm {μ : Measure E} (V : WeakPotential μ) (lam K : ℝ) (z u : E) :
    s82r_Gm V lam K z u = s82r_Gm V lam K u z := by
  unfold s82r_Gm s82r_d; rw [V.q_symm z u]

lemma s82r_hyp {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ0 : E → ℝ}
    {M M₁ : ℝ} (hψ : IsField μ ψ0 M M₁) {m n : ℕ} (p : Fin m → E) (t : Fin m → ℝ)
    (ht : ∀ ℓ, 0 ≤ t ℓ) {lam : ℝ} (hlam : 0 ≤ lam) {P : ℝ}
    (hP : (∑ ℓ, t ℓ) * V.γ + lam * n * V.γ ≤ P) :
    s82r_Hyp μ (s82r_Gm V lam (Real.exp (M + (M₁ + P)))) (s82r_bm V p t (Real.exp (M + (M₁ + P))))
      (s82r_kap (n := n) V ψ0 lam) (s82r_kap (n := n) V (s82r_Fld V p t Finset.univ ψ0) lam) := by
  classical
  set K := Real.exp (M + (M₁ + P)) with hK
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hγ : 0 ≤ V.γ := V.γ_nonneg
  have hlamP : lam * n * V.γ ≤ P := by
    have : 0 ≤ (∑ ℓ, t ℓ) * V.γ := mul_nonneg (Finset.sum_nonneg fun ℓ _ => ht ℓ) hγ
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold s82r_Gm s82r_d
    exact (measurable_const.mul (measurable_const.sub (Real.measurable_exp.comp
      (V.measurable_q.const_mul lam).neg))).add measurable_const
  · intro z u
    unfold s82r_Gm
    exact add_nonneg (mul_nonneg hK0 (s82r_d_nonneg V hlam z u)) (by positivity)
  · refine ⟨K * 1 + K ^ 2 * (lam * V.γ), fun z u => ?_⟩
    unfold s82r_Gm
    exact add_le_add (mul_le_mul_of_nonneg_left (s82r_d_lt_one V lam z u) hK0) le_rfl
  · unfold s82r_bm
    exact Finset.measurable_sum _ fun ℓ _ =>
      (measurable_const.mul (s82r_d_meas V (t ℓ) (p ℓ))).add measurable_const
  · intro z
    unfold s82r_bm
    exact Finset.sum_nonneg fun ℓ _ => add_nonneg (mul_nonneg hK0 (s82r_d_nonneg V (ht ℓ) z _))
      (by have := ht ℓ; positivity)
  · refine ⟨∑ ℓ, (K * 1 + K ^ 2 * (t ℓ * V.γ)), fun z => ?_⟩
    unfold s82r_bm
    exact Finset.sum_le_sum fun ℓ _ => add_le_add
      (mul_le_mul_of_nonneg_left (s82r_d_lt_one V (t ℓ) z _) hK0) le_rfl
  · intro i x y z
    unfold s82r_kap
    have h1 := s82r_config_chain V hψ hlam hlamP i x y (Finset.univ.erase i) (subset_refl _) z
    have h2 := s82r_pins_chain V hψ p t ht hlam i y hP Finset.univ z
    have heq : s82r_PhiC V ψ0 lam i (s82r_hyb x y (Finset.univ.erase i)) = s82r_PhiC V ψ0 lam i y := by
      funext w
      unfold s82r_PhiC
      congr 2
      refine Finset.sum_congr rfl fun l hl => ?_
      simp [s82r_hyb, hl]
    rw [heq] at h1
    refine (abs_sub_le _ (s82r_nd μ (s82r_PhiC V ψ0 lam i y) z) _).trans ?_
    unfold s82r_Gm s82r_bm
    linarith [h1, h2]

end HRS.MS.S82R

end
