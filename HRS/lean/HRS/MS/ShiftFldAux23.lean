import HRS.MS.ShiftFldAux22

/-!
# S79P: good backward paths (classical adjoint solutions) and the covariance helpers
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_gen_time (s a β : ℝ) (r : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    generatorW (Cst d s a β) r f x = generatorW (Cst d s a β) 0 f x := rfl

/-- The data of a backward classical solution on `[0,T]` that the Lyapunov argument uses. -/
structure GoodPath (d : ℕ) (s a β : ℝ) (T : ℝ) (u : ℝ → Euc d → ℝ) : Prop where
  memCb : ∀ r ∈ Icc (0 : ℝ) T, HRS.MemCb 2 (u r)
  deriv : ∀ x, ∀ r ∈ Ioo (0 : ℝ) T,
    HasDerivAt (fun r' => u r' x) (-(generatorW (Cst d s a β) 0 (u r) x)) r
  Lcont : ∀ r ∈ Icc (0 : ℝ) T, Continuous (generatorW (Cst d s a β) 0 (u r))
  Lbound : ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |generatorW (Cst d s a β) 0 (u r) x| ≤ B * (1 + ‖x‖)
  bound0 : ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |u r x| ≤ B
  bound1 : ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) T, ∀ (i : Fin d) x, |D1 i (u r) x| ≤ B
  cont0 : ∀ x, ContinuousOn (fun r => u r x) (Icc (0 : ℝ) T)
  cont1 : ∀ (i : Fin d) x, ContinuousOn (fun r => D1 i (u r) x) (Icc (0 : ℝ) T)

theorem GoodPath.mono {s a β : ℝ} {T T' : ℝ} {u : ℝ → Euc d → ℝ} (h : GoodPath d s a β T u)
    (hT : T' ≤ T) : GoodPath d s a β T' u := by
  have hI : Icc (0 : ℝ) T' ⊆ Icc 0 T := Icc_subset_Icc_right hT
  have hO : Ioo (0 : ℝ) T' ⊆ Ioo 0 T := Ioo_subset_Ioo_right hT
  obtain ⟨BL, hBL⟩ := h.Lbound
  obtain ⟨B0, hB0⟩ := h.bound0
  obtain ⟨B1, hB1⟩ := h.bound1
  exact ⟨fun r hr => h.memCb r (hI hr), fun x r hr => h.deriv x r (hO hr),
    fun r hr => h.Lcont r (hI hr), ⟨BL, fun r hr => hBL r (hI hr)⟩, ⟨B0, fun r hr => hB0 r (hI hr)⟩,
    ⟨B1, fun r hr => hB1 r (hI hr)⟩, fun x => (h.cont0 x).mono hI, fun i x => (h.cont1 i x).mono hI⟩

theorem goodPath_of_classical {s a β : ℝ} {T : ℝ} {φ : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW (Cst d s a β) T φ u) : GoodPath d s a β T u := by
  have hcb : ∀ r ∈ Icc (0 : ℝ) T, HRS.MemCb 2 (u r) := by
    intro r hr
    refine ⟨h.c2 r hr, fun j hj => ?_⟩
    obtain ⟨B, hB⟩ := h.bdd j hj
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩
  have hcont : ∀ j ≤ 2, ∀ (m : Fin j → Euc d) (x : Euc d),
      ContinuousOn (fun r => iteratedFDeriv ℝ j (u r) x m) (Icc (0 : ℝ) T) := by
    intro j hj m x
    have h1 := h.cont_c2 j hj
    have h2 : Continuous fun r : Icc (0 : ℝ) T => iteratedFDeriv ℝ j (u r) x m :=
      (ContinuousMultilinearMap.apply ℝ (fun _ => Euc d) ℝ m).continuous.comp
        (h1.comp (continuous_id.prodMk continuous_const))
    exact continuousOn_iff_continuous_restrict.2 h2
  refine ⟨hcb, fun x r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, fun x => ?_, fun i x => ?_⟩
  · have := h.time_deriv x r hr
    simpa only [s79g_gen_time] using this
  · have h2 : Continuous fun x : Euc d => generatorW (Cst d s a β) r (u r) x :=
      h.cont_time_deriv.comp (f := fun x : Euc d => ((⟨r, hr⟩ : Icc (0 : ℝ) T), x))
        (continuous_const.prodMk continuous_id)
    simpa only [s79g_gen_time] using h2
  · obtain ⟨B, hB⟩ := h.bdd_time_deriv
    exact ⟨B, fun r hr x => by simpa only [s79g_gen_time] using hB r hr x⟩
  · obtain ⟨B, hB⟩ := h.bdd 0 (by norm_num)
    refine ⟨B, fun r hr x => ?_⟩
    have := hB r hr x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · obtain ⟨B, hB⟩ := h.bdd 1 (by norm_num)
    refine ⟨B, fun r hr i x => ?_⟩
    exact (HRS.MS.UniqN2b.n2b_D1_le i (u r) x).trans (by have := hB r hr x; rwa [norm_iteratedFDeriv_one] at this)
  · have := hcont 0 (by norm_num) finZeroElim x
    simpa [iteratedFDeriv_zero_apply] using this
  · have := hcont 1 (by norm_num) (fun _ => EuclideanSpace.single i (1 : ℝ)) x
    simpa [iteratedFDeriv_one_apply, D1] using this

end HRS.MS.S79G
