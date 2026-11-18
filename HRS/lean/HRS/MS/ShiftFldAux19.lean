import HRS.MS.ShiftFldAux18

/-!
# S79P: the Lyapunov identity in `L²(μ)` (part 1): the centred class of `L u`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_memCb_one : HRS.MemCb 2 (fun _ : Euc d => (1 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ => ⟨1, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  by_cases hj0 : j = 0
  · subst hj0
    dsimp only
    rw [norm_iteratedFDeriv_zero]
    simp
  · rw [iteratedFDeriv_const_of_ne hj0]
    simp

theorem s79g_prob (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) : IsProbabilityMeasure (thermalMeasure d s a β) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  exact HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob

theorem s79g_kdata (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) [IsProbabilityMeasure (thermalMeasure d s a β)] :
    ∃ K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β),
      S45.IsKData (thermalMeasure d s a β) (rieszKernel d s) K := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  exact S45.s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)

theorem s79g_centered (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) :
    ∫ x, Aop d s a β (thermalDensity d s a β) u x ∂(thermalMeasure d s a β) = 0 := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have h1 := s79g_green hd hs0 hsd ha hβ hρ hu (g := fun _ => (1 : ℝ)) s79g_memCb_one
  have hz : ∀ i : Fin d, D1 i (fun _ : Euc d => (1 : ℝ)) = fun _ => 0 := by
    intro i; funext x; simp [D1]
  simp only [hz, zero_mul, integral_zero, Finset.sum_const_zero, one_mul] at h1
  show ∫ x, _ ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) = 0
  rw [HRS.Whole.S79.s79_integral_withDensityReal hT.prob]
  exact h1

end HRS.MS.S79G
