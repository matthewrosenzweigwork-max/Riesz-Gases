import HRS.MS.S111K2B04h

/-!
# S11.1 continuation, B04 (part 9): measurability and integrability of `v ↦ W(v,τ)`, the interval function `Dfun`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ}

lemma s111k2_aesm_ellVec_ae {μ : Measure ℝ} {m : ℝ} (v : MultiIndex d → ℝ → ℝ)
    (hv : ∀ α, AEStronglyMeasurable (v α) μ) (hsum : ∀ᵐ t ∂μ, Summable fun α => v α t ^ 2) :
    AEStronglyMeasurable (fun t => ellVec (d := d) m (fun α => v α t)) μ := by
  set ι : ∀ α : MultiIndex d, ℝ →L[ℝ] OscDual d m := fun α =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 α with hι
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (s : Finset (MultiIndex d)) (t : ℝ) => ∑ α ∈ s, ι α (v α t)) ?_ ?_
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s fun α _ => (ι α).continuous.comp_aestronglyMeasurable (hv α)
  · filter_upwards [hsum] with t ht
    have h : Memℓp (fun α => v α t) 2 := by
      rw [memℓp_two_iff]; exact ht
    have h2 : HasSum (fun α => (lp.single 2 α (v α t) : lp (fun _ : MultiIndex d => ℝ) 2))
        (ellVec (d := d) m (fun α => v α t) : lp (fun _ : MultiIndex d => ℝ) 2) := by
      rw [s55f_ellVec_eq (m := m) h]
      exact lp.hasSum_single (by norm_num) ⟨fun α => v α t, h⟩
    exact h2

variable {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {S T u Pw : ℝ}
  {z : ℝ → (Euc d → ℝ) → ℝ}

lemma s111k2_dualCombo_single (m : ℝ) (α : MultiIndex d) : IsR2DualCombo m (oscTestFun m α) := by
  classical
  refine ⟨{α}, fun β => if β = α then 1 else 0, ?_⟩
  funext x
  simp

lemma s111k2_coord_aem (h : S111k2Drift C m c0 r b S T u Pw z) (α : MultiIndex d) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    AEMeasurable (fun v => if v ≤ u + τ then z v (propagatorW C v (u + τ) (oscTestFun m α)) else 0)
      (volume.restrict (Set.Icc (0 : ℝ) (u + T))) := by
  have h1 := h.hmeas (u + τ) ⟨by linarith [hτ.1, h.hu], by linarith [hτ.2]⟩ (oscTestFun m α)
    (s111k2_dualCombo_single m α)
  have h2 := (aemeasurable_indicator_iff (measurableSet_Icc (a := (0 : ℝ)) (b := u + τ))).2 h1
  have h3 := h2.mono_measure (Measure.restrict_le_self (μ := (volume : Measure ℝ))
    (s := Set.Icc (0 : ℝ) (u + T)))
  refine h3.congr (ae_restrict_of_forall_mem measurableSet_Icc fun v hv => ?_)
  beta_reduce
  by_cases hvτ : v ≤ u + τ
  · have hm : v ∈ Set.Icc (0 : ℝ) (u + τ) := ⟨hv.1, hvτ⟩
    rw [Set.indicator_of_mem hm, if_pos hvτ]
  · have hm : v ∉ Set.Icc (0 : ℝ) (u + τ) := fun hh => hvτ hh.2
    rw [Set.indicator_of_notMem hm, if_neg hvτ]

lemma s111k2_W_eq_ellVec (C : WholeCoeff d) (m : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (u v τ : ℝ) :
    s111k2_W C m z u v τ = ellVec (d := d) m (fun α =>
      if v ≤ u + τ then z v (propagatorW C v (u + τ) (oscTestFun m α)) else 0) := by
  unfold s111k2_W s111k2_Y
  by_cases hvτ : v ≤ u + τ
  · simp only [if_pos hvτ]
  · simp only [if_neg hvτ]
    exact (s55f_ellVec_zero (d := d) m).symm

lemma s111k2_W_aesm (h : S111k2Drift C m c0 r b S T u Pw z) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    AEStronglyMeasurable (fun v => s111k2_W C m z u v τ) (volume.restrict (Set.Icc (0 : ℝ) (u + T))) := by
  simp_rw [s111k2_W_eq_ellVec]
  refine s111k2_aesm_ellVec_ae (fun α v => if v ≤ u + τ then z v (propagatorW C v (u + τ) (oscTestFun m α)) else 0)
    (fun α => (s111k2_coord_aem h α hτ).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc fun v hv => ?_
  by_cases hvτ : v ≤ u + τ
  · simp only [if_pos hvτ]
    have := s111k2_Ycoord_memell h.hW h.hbs h.hP h.hz hv (h.hone v hv) (h.dual_lt hv) hvτ
    exact memℓp_two_iff.1 this
  · simp only [if_neg hvτ]
    simp

lemma s111k2_W_integrable (h : S111k2Drift C m c0 r b S T u Pw z) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) :
    IntegrableOn (fun v => s111k2_W C m z u v τ) (Set.Ioc a b') := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  refine ⟨(s111k2_W_aesm h hτ).mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ v in Set.Ioc a b', ‖s111k2_W C m z u v τ‖ₑ
      ≤ ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v :=
        setLIntegral_mono' measurableSet_Ioc fun v hv => s111k2_W_bound h (hsub hv) hτ
    _ = ENNReal.ofReal (s111k2_Kdrift d r Pw S) * ∫⁻ v in Set.Ioc a b', s111k2_Phi c0 u r Pw z v :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (s111k2_Kdrift d r Pw S) * ∫⁻ v in Set.Icc (0 : ℝ) (u + T), s111k2_Phi c0 u r Pw z v :=
        mul_le_mul' le_rfl (lintegral_mono_set hsub)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 (s111k2_Phi_fin h))

/-- The interval function: `Dfun a b τ = ∫_{(a,b]} W(v,τ) dv`. -/
def s111k2_Dfun (C : WholeCoeff d) (m : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (u a b τ : ℝ) : OscDual d m :=
  ∫ v in Set.Ioc a b, s111k2_W C m z u v τ

lemma s111k2_Dfun_self (C : WholeCoeff d) (m : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (u a τ : ℝ) :
    s111k2_Dfun C m z u a a τ = 0 := by
  unfold s111k2_Dfun
  simp

lemma s111k2_Dfun_bound (h : S111k2Drift C m c0 r b S T u Pw z) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) :
    ‖s111k2_Dfun C m z u a b' τ‖ₑ ≤
      ENNReal.ofReal (s111k2_Kdrift d r Pw S) * ∫⁻ v in Set.Ioc a b', s111k2_Phi c0 u r Pw z v := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  unfold s111k2_Dfun
  calc ‖∫ v in Set.Ioc a b', s111k2_W C m z u v τ‖ₑ
      ≤ ∫⁻ v in Set.Ioc a b', ‖s111k2_W C m z u v τ‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v :=
        setLIntegral_mono' measurableSet_Ioc fun v hv => s111k2_W_bound h (hsub hv) hτ
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma s111k2_Dfun_add (h : S111k2Drift C m c0 r b S T u Pw z) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    {a b' c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hbc : b' ≤ c) (hc : c ≤ u + T) :
    s111k2_Dfun C m z u a c τ = s111k2_Dfun C m z u a b' τ + s111k2_Dfun C m z u b' c τ := by
  unfold s111k2_Dfun
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union (Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]) measurableSet_Ioc
    (s111k2_W_integrable h hτ ha hab (hbc.trans hc))
    (s111k2_W_integrable h hτ (ha.trans hab) hbc hc)

end HRS.MS.S111K2
