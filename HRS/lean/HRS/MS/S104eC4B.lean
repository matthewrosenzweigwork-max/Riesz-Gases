import HRS.MS.S104eC4A

/-!
# S104E route C, packet C4 part B: semigroup shift and tail decomposition of `Dd`

`c4_shift`: `Dd g τ (τ+h) = P_h (Dd g τ τ)` (Fubini + semigroup law).  `c4_tail`: `Dd g (α+η) (α+η) = Dd g α (α+η) + Dd (g(·+α)) η η`.
`c4_decomp`: `Dd g (τ+h) (τ+h) = P_h (Dd g τ τ) + Dd (g(·+τ)) h h`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

theorem GFam.memCb {T K : ℝ} {g : ℝ → Euc d → ℝ} (hG : GFam T K g) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) :
    HRS.MemCb 2 (g σ) :=
  ⟨by exact_mod_cast hG.c2 σ hσ, fun j hj => ⟨K, by
    rintro _ ⟨x, rfl⟩; exact hG.bd σ hσ j hj x⟩⟩

theorem c4_shift (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) {τ h : ℝ} (hτ : 0 ≤ τ) (hh : 0 ≤ h) (hτT : τ ≤ T) (x : Euc d) :
    Dd Q ν g τ (τ + h) x = ouSg Q ν h (fun y => Dd Q ν g τ τ y) x := by
  set F : ℝ → Euc d → ℝ := fun σ z =>
    ouSg Q ν (τ - clampT τ σ) (g (clampT τ σ)) z with hF
  have hmem : ∀ σ, clampT τ σ ∈ Icc (0 : ℝ) T := fun σ =>
    ⟨(clampT_mem hτ σ).1, (clampT_mem hτ σ).2.trans hτT⟩
  have hFeq : ∀ σ ∈ Icc (0 : ℝ) τ, F σ = fun z => ouSg Q ν (τ - σ) (g σ) z := by
    intro σ hσ; funext z; simp only [hF, clampT_eq hσ]
  have hFb : ∀ σ z, |F σ z| ≤ K := fun σ z =>
    ul4_ouSg_abs_le Q ν _ (fun y => hG.abs (hmem σ) y) z
  have hFc : ∀ σ, Continuous (F σ) := fun σ => ul5_ouSg_cont Q ν _ (hG.memCb (hmem σ))
  have hFm : Measurable (Function.uncurry F) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun z => ?_) (fun σ => (hFc σ).measurable)
    have hΦ := c4_phi_cont Q hν hG z (τ := τ) (t0 := τ) hτT le_rfl
    exact hΦ.comp_continuous (clampT_cont τ) (fun σ => clampT_mem hτ σ)
  have hint : Integrable (Function.uncurry fun σ y => F σ (ouExp Q h x + y))
      ((volume.restrict (Ioc (0 : ℝ) τ)).prod (ouLaw Q ν h)) := by
    refine Integrable.of_bound (C := K) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (hFm.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))).aestronglyMeasurable
    · show ‖F p.1 (ouExp Q h x + p.2)‖ ≤ K
      rw [Real.norm_eq_abs]; exact hFb _ _
  have e1 : ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ + h - σ) (g σ) x =
      ∫ σ in (0 : ℝ)..τ, (∫ y, F σ (ouExp Q h x + y) ∂(ouLaw Q ν h)) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hτ] at hσ
    have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans hτT⟩
    have := ul4_semigroup Q hν.le hh (sub_nonneg.2 hσ.2) (hG.c2 σ hσT).continuous
      (B := K) (fun y => hG.abs hσT y) x
    rw [show τ + h - σ = h + (τ - σ) by ring, this, hFeq σ hσ]
    rfl
  have e2 : ouSg Q ν h (fun y => ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (g σ) y) x =
      ∫ y, (∫ σ in (0 : ℝ)..τ, F σ (ouExp Q h x + y)) ∂(ouLaw Q ν h) := by
    show ∫ y, (∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (g σ) (ouExp Q h x + y)) ∂(ouLaw Q ν h) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hτ] at hσ
    rw [hFeq σ hσ]
  have e3 : ∫ σ in (0 : ℝ)..τ, (∫ y, F σ (ouExp Q h x + y) ∂(ouLaw Q ν h)) =
      ∫ y, (∫ σ in (0 : ℝ)..τ, F σ (ouExp Q h x + y)) ∂(ouLaw Q ν h) := by
    simp_rw [intervalIntegral.integral_of_le hτ]
    exact integral_integral_swap hint
  unfold Dd
  rw [e1, e3, e2]

theorem c4_tail (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) {α η : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η) (hT : α + η ≤ T) (x : Euc d) :
    Dd Q ν g (α + η) (α + η) x = Dd Q ν g α (α + η) x + Dd Q ν (fun σ => g (σ + α)) η η x := by
  have hΦ := c4_phi_cont Q hν hG x (τ := α + η) (t0 := α + η) hT le_rfl
  have hint1 : IntervalIntegrable (fun σ => ouSg Q ν ((α + η) - σ) (g σ) x) volume 0 α :=
    (hΦ.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hα
  have hint2 : IntervalIntegrable (fun σ => ouSg Q ν ((α + η) - σ) (g σ) x) volume α (α + η) :=
    (hΦ.mono (Icc_subset_Icc hα le_rfl)).intervalIntegrable_of_Icc (by linarith)
  unfold Dd
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  congr 1
  have := intervalIntegral.integral_comp_add_right
    (fun σ => ouSg Q ν ((α + η) - σ) (g σ) x) (a := 0) (b := η) α
  rw [zero_add, add_comm η α] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only
  rw [show α + η - (σ + α) = η - σ by ring]

theorem c4_decomp (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) {τ h : ℝ} (hτ : 0 ≤ τ) (hh : 0 ≤ h) (hτh : τ + h ≤ T) (x : Euc d) :
    Dd Q ν g (τ + h) (τ + h) x = ouSg Q ν h (fun y => Dd Q ν g τ τ y) x +
      Dd Q ν (fun σ => g (σ + τ)) h h x := by
  rw [c4_tail Q hν hG hτ hh hτh x, c4_shift Q hν hG hτ hh (by linarith) x]

end HRS.MS.S104e.C
