import HRS.Uniform.Comp28W3

/-!
# COMP-28, Wasserstein part, W4: restarting a stochastic convolution at time `a`, and linear combinations
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q48d

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- If `Y = ∫_0^t V(t,r) dD` and `Za = ∫_0^a V(a,r) dD`, then `Y - V(t,a) Za = ∫_a^t V(t,r) dD`. -/
lemma sc_split {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (hD : ∀ τ ∈ Icc 0 t, AEStronglyMeasurable (D τ) P)
    (hcoc : ∀ r, 0 ≤ r → r ≤ a → (V t a).comp (V a r) = V t r) {Y Za : Ω → E}
    (hY : AEStronglyMeasurable Y P) (hZ : AEStronglyMeasurable Za P)
    (hSY : SC P V D 0 t Y) (hSZ : SC P V D 0 a Za) :
    SC P V D a t (fun ω => Y ω - V t a (Za ω)) := by
  intro ε hε
  set c : ℝ := ‖V t a‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hη : (0 : ℝ) < ε / (1 + c) := by positivity
  set η' : ℝ := ε / (1 + c) with hη'
  obtain ⟨δ1, hδ1, h1⟩ := hSY η' hη
  obtain ⟨δ2, hδ2, h2⟩ := hSZ η' hη
  obtain ⟨n, p, hp0, hpl, hpm, hpmesh⟩ := exists_part ha (lt_min hδ1 hδ2)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun m q hq0 hql hqm hqmesh => ?_⟩
  obtain ⟨r, hr0, hrl, hrm, hrp, hrq⟩ := exists_concat (a := a) p q hpl hq0 hpm hqm
  have hmesh : ∀ i : Fin (n + m), r i.succ - r i.castSucc < min δ1 δ2 := by
    intro i
    refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
    · rw [(hrp i0).1, (hrp i0).2]; exact hpmesh i0
    · rw [(hrq j).1, (hrq j).2]; exact hqmesh j
  have e1 := h1 (n + m) r (hr0.trans hp0) (hrl.trans hql) hrm
    fun i => (hmesh i).trans_le (min_le_left _ _)
  have e2 := h2 n p hp0 hpl hpm fun i => (hpmesh i).trans_le (min_le_right _ _)
  have hsplit : ∀ ω, riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω =
      V t a (riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω) +
        riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω := by
    intro ω
    simp_rw [riemannSum_id]
    rw [Fin.sum_univ_add, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hrp i).1, (hrp i).2]
      have hmem : p i.castSucc ∈ Icc 0 a := by
        have := mem_Icc_of_part hp0 hpl hpm i.castSucc
        exact this
      rw [← hcoc _ hmem.1 hmem.2]
      rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hrq j).1, (hrq j).2]
  have hRp := aesm_riemannSum V (fun τ hτ => hD τ ⟨hτ.1, hτ.2.trans hat⟩) hp0 hpl hpm
  have hRr := aesm_riemannSum V hD (hr0.trans hp0) (hrl.trans hql) hrm
  have hdecomp : (fun ω => Y ω - V t a (Za ω) - riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω) =
      (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) -
      (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) := by
    funext ω
    simp only [Pi.sub_apply, hsplit ω, map_sub]
    abel
  have hm2 : AEStronglyMeasurable
      (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) P :=
    (V t a).continuous.comp_aestronglyMeasurable (hZ.sub hRp)
  have e2' : eLpNorm (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) 2 P ≤
      ENNReal.ofReal c * ENNReal.ofReal η' := by
    calc _ ≤ ENNReal.ofReal c * eLpNorm (fun ω => Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω) 2 P :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm2
            (Eventually.of_forall fun ω => (V t a).le_opNorm _) 2
      _ ≤ _ := by gcongr
  show eLpNorm (fun ω => Y ω - V t a (Za ω) - riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω) 2 P <
    ENNReal.ofReal ε
  rw [hdecomp]
  calc eLpNorm ((fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) -
        (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω))) 2 P
      ≤ eLpNorm (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P +
        eLpNorm (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) 2 P :=
        eLpNorm_sub_le (by norm_num)
    _ < ENNReal.ofReal η' + ENNReal.ofReal c * ENNReal.ofReal η' :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) e2') e1 e2'
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hη']; field_simp

end HRS.Uniform.Comp28
