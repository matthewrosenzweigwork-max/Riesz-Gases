import HRS.MH.DualityRdDefs
import HRS.Stochastic.EmpiricalIto

/-!
# DualityRd packet A1: the whole-space empirical lift of a test is `C^{1,2}` on `(ℝ^d)^N`

Ports `HRS.IsC12Test.hasDerivWithinAt_Icc` (`EmpiricalIto.lean:192`, packet A1a) and
`HRS.isC12On_empiricalLift` (`EmpiricalIto.lean:252`, packet A1b) with `Torus.lift (f r)` replaced by `f r`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem da1_contOn_iter {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {j : ℕ} (hj : j ≤ 2) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (f p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
  HRS.continuousOn_Icc_prod_of_subtype (hf.cont_c2 j hj)

theorem da1_contOn_lift {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ) := by
  have h := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp_continuousOn
    (da1_contOn_iter hf (j := 0) (by norm_num))
  refine h.congr fun p _ => ?_
  simp [iteratedFDeriv_zero_eq_comp]

theorem da1_continuousOn_time {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) (x : Euc d) :
    ContinuousOn (fun r => f r x) (Set.Icc 0 t) :=
  ContinuousOn.comp (da1_contOn_lift hf)
    (continuous_id.prodMk continuous_const : Continuous fun r : ℝ => (r, x)).continuousOn
    (fun r (hr : r ∈ Set.Icc (0 : ℝ) t) => (⟨hr, Set.mem_univ _⟩ : (r, x) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))))

theorem da1_continuousOn_timeDeriv {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) (x : Euc d) :
    ContinuousOn (fun r => ft r x) (Set.Icc 0 t) := by
  have h2 : Continuous fun r : Set.Icc (0 : ℝ) t => ft r x :=
    hf.cont_time_deriv.comp (continuous_id.prodMk continuous_const)
  exact continuousOn_iff_continuous_domRestrict.2 h2

theorem da1_contOn_timeDeriv {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => ft p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
  HRS.continuousOn_Icc_prod_of_subtype hf.cont_time_deriv

/-- **Packet A1a** (S, ~60 lines).  Ports `HRS.IsC12Test.hasDerivWithinAt_Icc` (`HRS/Stochastic/EmpiricalIto.lean:192`):
the time derivative `ft` of an `IsC12TestRd` test is the derivative of `r ↦ f r x` *within `[0,t]` also at the endpoints*
(`hasDerivWithinAt_Ici_of_tendsto_deriv`/`hasDerivWithinAt_Iic_of_tendsto_deriv`, continuity of `r ↦ f r x` from
`cont_c2` at `j = 0`, continuity of `ft` from `cont_time_deriv`). -/
theorem hasDerivWithinAt_Icc_testRd_proof {t : ℝ} (ht : 0 < t) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft)
    (x : Euc d) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun r' => f r' x) (ft r x) (Set.Icc 0 t) r := by
  have hdiff : DifferentiableOn ℝ (fun r => f r x) (Set.Ioo 0 t) := fun r hr =>
    (hf.time_deriv x r hr).differentiableAt.differentiableWithinAt
  have hder : ∀ r ∈ Set.Ioo 0 t, deriv (fun r => f r x) r = ft r x := fun r hr =>
    (hf.time_deriv x r hr).deriv
  rcases hr.1.eq_or_lt with rfl | h0
  · have h1 : Tendsto (fun r => ft r x) (𝓝[>] 0) (𝓝 (ft 0 x)) :=
      (((da1_continuousOn_timeDeriv hf x) 0 ⟨le_rfl, ht.le⟩).tendsto).mono_left
        (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsGT ht) Set.Ioo_subset_Icc_self))
    have h2 := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      (((da1_continuousOn_time hf x) 0 ⟨le_rfl, ht.le⟩).mono Set.Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT ht)
      (h1.congr' (eventually_of_mem (Ioo_mem_nhdsGT ht) fun r hr => (hder r hr).symm))
    exact h2.mono Set.Icc_subset_Ici_self
  rcases hr.2.eq_or_lt with rfl | h1
  · have h1 : Tendsto (fun r => ft r x) (𝓝[<] r) (𝓝 (ft r x)) :=
      (((da1_continuousOn_timeDeriv hf x) r ⟨ht.le, le_rfl⟩).tendsto).mono_left
        (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT ht) Set.Ioo_subset_Icc_self))
    have h2 := hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
      (((da1_continuousOn_time hf x) r ⟨ht.le, le_rfl⟩).mono Set.Ioo_subset_Icc_self)
      (Ioo_mem_nhdsLT ht)
      (h1.congr' (eventually_of_mem (Ioo_mem_nhdsLT ht) fun r hr => (hder r hr).symm))
    exact h2.mono Set.Icc_subset_Iic_self
  · exact (hf.time_deriv x r ⟨h0, h1⟩).hasDerivWithinAt

/-- **Packet A1b** (M, ~200 lines).  Ports `HRS.isC12On_empiricalLift` (`HRS/Stochastic/EmpiricalIto.lean:252-327`) with
`Torus.lift (f r)` replaced by `f r` and `Torus.mk (Y i)` by `Y i`.  The torus proof is verbatim reusable: it only uses the
generic lemmas `sumLift`, `contDiff_sumLift`, `hasFDerivAt_sumLift`, `fderiv_sumLift_apply`, `fderiv_fderiv_sumLift`, `psiComp`,
`curry2`, `continuousOn_Icc_prod_of_subtype`, `contOn_comp_coord` (all for `g : Euc d → ℝ`, `EmpiricalIto.lean:73-240`) and
`hasDerivWithinAt_Icc_testRd`.  `U = Set.univ`: no collision-free open set is needed (the empirical functional `N⁻¹ ∑ f(x_i)` is
smooth on all of `(ℝ^d)^N`; collisions only matter for the *drift identity*, packet A2). -/
theorem isC12On_empLiftRd_proof {N : ℕ} {t : ℝ} (ht : 0 < t) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    HRS.IsC12On t Set.univ (fun r (Y : EucConfig d N) => (N : ℝ)⁻¹ * ∑ i, f r (Y i)) := by
  have hcd : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (f r) := fun r hr => hf.c2 r hr
  have hcdN : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (HRS.sumLift N (f r)) := fun r hr =>
    HRS.contDiff_sumLift (hcd r hr)
  have hA : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (f p.1) (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) := fun i => by
    have h := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn
      (HRS.contOn_comp_coord (N := N) (da1_contOn_iter hf (j := 1) (by norm_num)) i)
    exact h.congr fun p _ => by simp [HRS.fderiv_eq_curry]
  have hB : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (fderiv ℝ (f p.1)) (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) := fun i => by
    have h := (HRS.continuous_curry2 d).comp_continuousOn
      (HRS.contOn_comp_coord (N := N) (da1_contOn_iter hf (j := 2) (by norm_num)) i)
    exact h.congr fun p _ => by simp [HRS.fderiv_fderiv_eq_curry2]
  refine
    { cont := ?_
      hasFDerivAt := ?_
      hasFDerivAt_fderiv := ?_
      cont_fderiv := ?_
      cont_fderiv₂ := ?_
      hasDerivWithinAt := ?_
      cont_deriv := ?_ }
  · have : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        (N : ℝ)⁻¹ * ∑ i, f p.1 (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        HRS.contOn_comp_coord (N := N) (da1_contOn_lift hf) i)
    exact this
  · intro r hr Y _
    exact (((hcdN r hr).differentiable (by norm_num)) Y).hasFDerivAt
  · intro r hr Y _
    exact ((((hcdN r hr).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) Y).hasFDerivAt
  · let R : Fin N → (Euc d →L[ℝ] ℝ) →L[ℝ] ((Fin N → Euc d) →L[ℝ] ℝ) := fun i =>
      (ContinuousLinearMap.compL ℝ (Fin N → Euc d) (Euc d) ℝ).flip
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)
    have h1 : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        R i (fderiv ℝ (f p.1) (p.2 i))) (Set.Icc 0 t ×ˢ Set.univ) := fun i =>
      (R i).continuous.comp_continuousOn (hA i)
    have h2 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        ∑ i, R i (fderiv ℝ (f p.1) (p.2 i))) (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_finsetSum _ fun i _ => h1 i
    have h3 := h2.const_smul ((N : ℝ)⁻¹)
    refine h3.congr fun p hp => ?_
    change fderiv ℝ (HRS.sumLift N (f p.1)) p.2 = _
    rw [(HRS.hasFDerivAt_sumLift ((hcd p.1 hp.1).differentiable (by norm_num)) p.2).fderiv]
    rfl
  · have h1 : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        HRS.psiComp d N i (fderiv ℝ (fderiv ℝ (f p.1)) (p.2 i)))
        (Set.Icc 0 t ×ˢ Set.univ) := fun i =>
      (HRS.continuous_psiComp d N i).comp_continuousOn (hB i)
    have h2 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        ∑ i, HRS.psiComp d N i (fderiv ℝ (fderiv ℝ (f p.1)) (p.2 i)))
        (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_finsetSum _ fun i _ => h1 i
    have h3 := h2.const_smul ((N : ℝ)⁻¹)
    refine h3.congr fun p hp => ?_
    change fderiv ℝ (fderiv ℝ (HRS.sumLift N (f p.1))) p.2 = _
    exact HRS.fderiv_fderiv_sumLift (hcd p.1 hp.1) p.2
  · intro Y _ r hr
    have h1 : HasDerivWithinAt (fun r => (N : ℝ)⁻¹ * ∑ i, f r (Y i))
        ((N : ℝ)⁻¹ * ∑ i, ft r (Y i)) (Set.Icc 0 t) r :=
      (HasDerivWithinAt.fun_sum fun i _ => hasDerivWithinAt_Icc_testRd_proof ht hf (Y i) hr).const_mul _
    rwa [h1.derivWithin (uniqueDiffOn_Icc ht r hr)]
  · have : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        (N : ℝ)⁻¹ * ∑ i, ft p.1 (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        HRS.contOn_comp_coord (N := N) (da1_contOn_timeDeriv hf) i)
    refine this.congr fun p hp => ?_
    have h1 : HasDerivWithinAt (fun r => (N : ℝ)⁻¹ * ∑ i, f r (p.2 i))
        ((N : ℝ)⁻¹ * ∑ i, ft p.1 (p.2 i)) (Set.Icc 0 t) p.1 :=
      (HasDerivWithinAt.fun_sum fun i _ =>
        hasDerivWithinAt_Icc_testRd_proof ht hf (p.2 i) hp.1).const_mul _
    exact h1.derivWithin (uniqueDiffOn_Icc ht p.1 hp.1)

end HRS.MH.DualityRd
