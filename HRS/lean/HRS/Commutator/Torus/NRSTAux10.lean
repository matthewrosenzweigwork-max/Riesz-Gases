import HRS.Commutator.Torus.NRSTAux9

/-!
# NRS-T, part 10: continuity of the commutator functional (dominated convergence)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

lemma integrable_sub_prod {Φ : Torus d → ℝ} (hΦ : Integrable Φ) (hΦm : Measurable Φ) :
    Integrable (fun p : Torus d × Torus d => Φ (p.1 - p.2)) (volume.prod volume) := by
  refine absConv_integrable_prod (ν := volume) (μ := volume)
    (hΦm.comp (measurable_fst.sub measurable_snd))
    (fun x => hΦ.comp_sub_left x) (M := ∫ z, ‖Φ z‖) fun x => ?_
  have : ∫ y : Torus d, ‖Φ (x - y)‖ = ∫ z : Torus d, ‖Φ z‖ :=
    integral_sub_left_eq_self (fun z : Torus d => ‖Φ z‖) volume x
  exact this.le

lemma CcommFunT_eq_prod (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 ≤ L)
    {v : Torus d → Euc d} (hv : IsLipschitzVF L v) {w : Torus d → ℝ} (hw : Continuous w) :
    CcommFunT (periodicRieszGrad d s) v w = ∫ p : Torus d × Torus d,
      commKernel (periodicRieszGrad d s) v p.1 p.2 * w p.1 * w p.2 ∂(volume.prod volume) := by
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |w x| ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hw.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun x => by
      have := hB x (Set.mem_univ x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)⟩
  have hint := integrable_commProd hd hs0 hsd hL hv hw.measurable hB
  unfold CcommFunT
  rw [integral_prod _ hint]

/-- Dominated convergence for the commutator functional. -/
lemma CcommFunT_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L B : ℝ} (hL : 0 ≤ L)
    (hB0 : 0 ≤ B) {v : Torus d → Euc d} (hv : IsLipschitzVF L v) {w : Torus d → ℝ}
    (hw : Continuous w) {vn : ℕ → Torus d → Euc d} {wn : ℕ → Torus d → ℝ}
    (hvn : ∀ n, IsLipschitzVF L (vn n)) (hwn : ∀ n, Continuous (wn n))
    (hwB : ∀ n x, |wn n x| ≤ B) (hvt : ∀ x, Tendsto (fun n => vn n x) atTop (𝓝 (v x)))
    (hwt : ∀ x, Tendsto (fun n => wn n x) atTop (𝓝 (w x))) :
    Tendsto (fun n => CcommFunT (periodicRieszGrad d s) (vn n) (wn n)) atTop
      (𝓝 (CcommFunT (periodicRieszGrad d s) v w)) := by
  obtain ⟨C, hC0, hC⟩ := commKernel_bound hd hs0 hsd
  have hK : 0 ≤ C * L * (B * B) := by positivity
  simp_rw [CcommFunT_eq_prod hd hs0 hsd hL (hvn _) (hwn _)]
  rw [CcommFunT_eq_prod hd hs0 hsd hL hv hw]
  set Φ : Torus d → ℝ := fun z => (C * L * (B * B)) * (‖z‖ ^ (-s) + 1) with hΦ
  have hgi : Integrable Φ volume :=
    ((KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)).const_mul _
  have hΦm : Measurable Φ := ((measurable_norm.pow_const _).add measurable_const).const_mul _
  have hvc : ∀ u : Torus d → Euc d, IsLipschitzVF L u → Measurable (fun p : Torus d × Torus d =>
      commKernel (periodicRieszGrad d s) u p.1 p.2) := by
    intro u hu
    have huc : Continuous u := IsLipschitzVF.continuous hL hu
    unfold commKernel
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
    refine Measurable.inner ?_ ?_
    · exact (huc.measurable.comp measurable_fst).sub (huc.measurable.comp measurable_snd)
    · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
  have hbound0 : ∀ (u : Torus d → Euc d), IsLipschitzVF L u → ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) u x y| ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := by
    intro u hu x y
    by_cases hxy : x = y
    · subst hxy
      unfold commKernel
      rw [if_pos rfl, abs_zero]
      exact mul_nonneg (mul_nonneg hC0 hL) (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
    · have h1 := hC L u hL hu x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
        rw [KernelGrad.tdist_eq_sub_zero]
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
          (by linarith)
      calc |commKernel (periodicRieszGrad d s) u x y|
          ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hL)
  refine tendsto_integral_of_dominated_convergence (fun p => Φ (p.1 - p.2)) ?_ ?_ ?_ ?_
  · intro n
    have := hvc (vn n) (hvn n)
    exact (((this.mul ((hwn n).measurable.comp measurable_fst)).mul
      ((hwn n).measurable.comp measurable_snd))).aestronglyMeasurable
  · exact integrable_sub_prod hgi hΦm
  · intro n
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |commKernel (periodicRieszGrad d s) (vn n) p.1 p.2| * |wn n p.1| * |wn n p.2|
        ≤ ((C * L) * (‖p.1 - p.2‖ ^ (-s) + 1)) * B * B := by
          gcongr
          · exact hbound0 _ (hvn n) _ _
          · exact hwB n _
          · exact hwB n _
      _ = Φ (p.1 - p.2) := by rw [hΦ]; ring
  · refine Filter.Eventually.of_forall fun p => ?_
    have h1 : Tendsto (fun n => commKernel (periodicRieszGrad d s) (vn n) p.1 p.2) atTop
        (𝓝 (commKernel (periodicRieszGrad d s) v p.1 p.2)) := by
      unfold commKernel
      by_cases hxy : p.1 = p.2
      · simp [hxy]
      · simp only [hxy, if_false]
        exact ((hvt p.1).sub (hvt p.2)).inner tendsto_const_nhds
    exact (h1.mul (hwt p.1)).mul (hwt p.2)

end HRS.Commutator.TorusNote.NRST
