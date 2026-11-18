import HRS.Main.A8PAux50

/-!
# Packet A8P, part 51: Itô's formula for `√(ε² + Z²)` with an `L²` bound of the martingale term
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

section ItoScalar

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ι → ℝ}

theorem a8p_fderiv_norm_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ‖fderiv ℝ (a8pG1 ε) x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [a8pG1_fderiv hε, Real.norm_eq_abs, abs_mul, one_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (a8pG1'_abs_le hε x)

theorem a8p_ito_scalar (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε)
    (σ : ι → ℝ) (X : ℝ≥0 → Ω → ℝ) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (b : ℝ≥0 → Ω → ℝ)
    (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W t ω k - W 0 ω k) • σ k) :
    ∃ (Zt : ℝ → Ω → ℝ) (M : Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal s) ω = Zt s ω) ∧
      (∀ᵐ ω ∂P, Continuous fun s => Zt s ω) ∧ Measurable M ∧
      ∫⁻ ω, ‖M ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal T * ENNReal.ofReal (∑ k, σ k ^ 2) ∧
      ∀ᵐ ω ∂P, ((1 / 2) * ∑ k, σ k ^ 2) * ∫ s in Set.Icc (0 : ℝ) T, a8pG1'' ε (Zt s ω) ≤
        |Zt T ω - Zt 0 ω| + (∫ s in Set.Icc (0 : ℝ) T, |b (Real.toNNReal s) ω|) + |M ω| := by
  classical
  let b' : ℝ → Ω → ℝ := fun s ω => if s ≤ T then b (Real.toNNReal s) ω else 0
  have hb'prog : IsProgressive ℱ b' := by
    intro i
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    have h1 := hb i
    have hs : MeasurableSet {p : Set.Iic i × Ω | (p.1 : ℝ) ≤ T} :=
      (measurable_subtype_coe.comp measurable_fst) measurableSet_Iic
    exact Measurable.ite hs h1 measurable_const
  have hb'int : ∀ T' : ℝ, ∀ᵐ ω ∂P, IntegrableOn (fun s => b' s ω) (Set.Icc 0 T') := by
    intro T'
    filter_upwards [hbint] with ω hω
    have e : (fun s => b' s ω) = Set.indicator (Set.Iic T) (fun s => b (Real.toNNReal s) ω) := by
      funext s; simp [b', Set.indicator]
    rw [e, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    refine hω.mono_set ?_
    intro s hs
    exact ⟨hs.2.1, hs.1⟩
  have hb' : IsProgressiveLocL1 P ℱ b' := ⟨hb'prog, hb'int⟩
  have hΦ : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Ω) => σ) := by
    refine ⟨isProgressive_const ℱ σ, fun T => ae_of_all _ fun ω => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hf : IsC12On T Set.univ (fun (_ : ℝ) (x : ℝ) => a8pG1 ε x) :=
    isC12On_of_contDiff T Set.univ (a8pG1 ε) (a8pG1_contDiff hε)
  have hIto := ito_formula hW hT (fun (_ : ℝ) (x : ℝ) => a8pG1 ε x) hf (X 0) hX₀ b' hb'
    (fun _ _ => σ) hΦ
  dsimp only at hIto
  set Zt : ℝ → Ω → ℝ := itoProcess P ℱ W (X 0) b' (fun _ _ => σ) with hZt
  have hXt : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal s) ω = Zt s ω := by
    filter_upwards [hX, localItoIntegralE_const hW σ] with ω h1 h2 s hs
    have h3 := h1 (Real.toNNReal s) (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
    have h4 : (∫ r in Set.Icc (0 : ℝ) (Real.toNNReal s : ℝ), b (Real.toNNReal r) ω) =
        ∫ r in Set.Icc (0 : ℝ) s, b' r ω := by
      rw [Real.coe_toNNReal _ hs.1]
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp [b', hr.2.trans hs.2]
    simp only [hZt, itoProcess]
    rw [h3, h4, h2 s, hW.zero]
    simp
  have hXprog : IsProgressive ℱ Zt := isProgressive_itoProcess (X 0) hX₀ b' hb'prog _
  have hZc : ∀ᵐ ω ∂P, Continuous fun s => Zt s ω :=
    continuous_itoProcess (X 0) b' hb' _
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, ‖fderiv ℝ (fun (x : ℝ) => a8pG1 ε x) x‖ ≤ 1 :=
    fun t _ x => a8p_fderiv_norm_le hε x
  have hΦ2 : ∀ T' : ℝ, ∫⁻ ω, (∫⁻ s in Set.Icc 0 T', ∑ k, ‖σ k‖ₑ ^ 2) ∂P < ∞ := by
    intro T'
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  set Ψ : ℝ → Ω → ι → ℝ := itoIntegrand T Set.univ (fun (_ : ℝ) (x : ℝ) => a8pG1 ε x) Zt
    (fun _ _ => σ) with hΨdef
  have hΨ : IsProgressiveL2 P ℱ Ψ :=
    isProgressiveL2_itoIntegrand (fun (_ : ℝ) (x : ℝ) => a8pG1 ε x) hf 1 hC Zt hXprog
      (fun _ _ => σ) hΦ hΦ2
  have hloc := localItoIntegral_eq_itoIntegral hW hΨ
  refine ⟨Zt, itoIntegral P ℱ W Ψ T, hXt, hZc, ?_, ?_, ?_⟩
  · exact ((adapted_itoIntegral P ℱ W Ψ T).mono (ℱ.le T) le_rfl)
  · -- isometry
    rw [lintegral_itoIntegral_sq hW hΨ T]
    have hle : sqIntegralOn P Ψ T ≤ sqIntegralOn P (fun (_ : ℝ) (_ : Ω) => σ) T := by
      refine sqIntegralOn_mono_of_enorm_le (fun s ω k => ?_) T
      simp only [hΨdef, itoIntegrand]
      by_cases hs : s ∈ Set.Icc 0 T
      · simp only [Set.indicator_of_mem hs, Set.indicator_univ, Set.mem_univ, Set.setOf_true]
        rw [a8pG1_fderiv hε, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (a8pG1'_abs_le hε _)
      · simp [Set.indicator_of_notMem hs]
    refine hle.trans (le_of_eq ?_)
    unfold sqIntegralOn
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one, sub_zero]
    rw [mul_comm, sum_enorm_sq_eq_ofReal]
  · -- the drift inequality
    filter_upwards [hIto, hloc, hZc, hbint] with ω hI hl hc hbi
    obtain ⟨hIint, hid⟩ := hI
    have hid' := hid T ⟨hT, le_rfl⟩
    rw [hl T] at hid'
    have hZ0 : Zt 0 ω = X 0 ω := itoProcess_zero P ℱ W (X 0) b' (fun _ _ => σ) ω
    set ν : ℝ := (1 / 2) * ∑ k, σ k ^ 2 with hν
    have hdr : ∀ s ∈ Set.Icc (0 : ℝ) T,
        itoDrift T (fun (_ : ℝ) (x : ℝ) => a8pG1 ε x) Zt b' (fun _ _ => σ) s ω =
          a8pG1' ε (Zt s ω) * b (Real.toNNReal s) ω + ν * a8pG1'' ε (Zt s ω) := by
      intro s hs
      unfold itoDrift
      have hb's : b' s ω = b (Real.toNNReal s) ω := by simp [b', hs.2]
      rw [hb's]
      simp only [derivWithin_fun_const, Pi.zero_apply, a8pG1_fderiv hε, a8pG1_fderiv2 hε]
      have hsum : ∑ x, σ x * σ x * a8pG1'' ε (Zt s ω) = (∑ x, σ x ^ 2) * a8pG1'' ε (Zt s ω) := by
        rw [Finset.sum_mul]; simp [sq]
      rw [hsum, hν]
      ring
    have hbd : ∀ s, ‖a8pG1' ε (Zt s ω)‖ ≤ 1 := fun s => by
      rw [Real.norm_eq_abs]; exact a8pG1'_abs_le hε _
    have hfc : Continuous fun s => a8pG1' ε (Zt s ω) := (a8pG1'_cont hε).comp hc
    have hgc : Continuous fun s => a8pG1'' ε (Zt s ω) := (a8pG1''_cont hε).comp hc
    have hint1 : IntegrableOn (fun s => a8pG1' ε (Zt s ω) * b (Real.toNNReal s) ω) (Set.Icc 0 T) :=
      Integrable.bdd_mul (c := 1) hbi hfc.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
    have hint2 : IntegrableOn (fun s => ν * a8pG1'' ε (Zt s ω)) (Set.Icc 0 T) :=
      ((hgc.continuousOn).integrableOn_compact isCompact_Icc).const_mul ν
    have hint3 : IntegrableOn (fun s => |b (Real.toNNReal s) ω|) (Set.Icc 0 T) := hbi.abs
    have hsplit : ∫ s in Set.Icc (0 : ℝ) T, itoDrift T (fun (_ : ℝ) (x : ℝ) => a8pG1 ε x) Zt b'
        (fun _ _ => σ) s ω =
        (∫ s in Set.Icc (0 : ℝ) T, a8pG1' ε (Zt s ω) * b (Real.toNNReal s) ω) +
          ν * ∫ s in Set.Icc (0 : ℝ) T, a8pG1'' ε (Zt s ω) := by
      rw [setIntegral_congr_fun measurableSet_Icc hdr, integral_add hint1 hint2, integral_const_mul]
    rw [hsplit] at hid'
    have hB : |∫ s in Set.Icc (0 : ℝ) T, a8pG1' ε (Zt s ω) * b (Real.toNNReal s) ω| ≤
        ∫ s in Set.Icc (0 : ℝ) T, |b (Real.toNNReal s) ω| := by
      refine abs_integral_le_integral_abs.trans ?_
      refine integral_mono hint1.abs hint3 fun s => ?_
      show |a8pG1' ε (Zt s ω) * b (Real.toNNReal s) ω| ≤ |b (Real.toNNReal s) ω|
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (a8pG1'_abs_le hε _)
    have hA : |a8pG1 ε (Zt T ω) - a8pG1 ε (Zt 0 ω)| ≤ |Zt T ω - Zt 0 ω| := a8pG1_lip hε _ _
    have hZ0' : a8pG1 ε (Zt 0 ω) = a8pG1 ε (X 0 ω) := by rw [hZ0]
    set Mv : ℝ := itoIntegral P ℱ W Ψ T ω with hMv
    set B1 : ℝ := ∫ s in Set.Icc (0 : ℝ) T, a8pG1' ε (Zt s ω) * b (Real.toNNReal s) ω with hB1
    have hnu : ν * ∫ s in Set.Icc (0 : ℝ) T, a8pG1'' ε (Zt s ω) =
        (a8pG1 ε (Zt T ω) - a8pG1 ε (Zt 0 ω)) - Mv - B1 := by
      rw [hZ0']; linarith
    rw [hnu]
    have h1 := abs_le.1 hA
    have h2 := abs_le.1 hB
    have h3 := le_abs_self Mv
    have h4 := neg_abs_le Mv
    nlinarith [abs_nonneg Mv, abs_nonneg (Zt T ω - Zt 0 ω)]

end ItoScalar

end HRS.Main.A8P
