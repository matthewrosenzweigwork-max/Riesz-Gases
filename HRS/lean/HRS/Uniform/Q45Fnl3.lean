import HRS.Uniform.Q45Fnl2

/-!
# Q45: assembly of Proposition 3.21 for `T > 0` (the bound for a fixed test function)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

theorem smooth_pos_fixed {T K : ℝ} (hT : 0 < T) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (S : EvolData H E) (hS : S.MaxHyp T K)
    (X₀ X₀' : Ω → H) (hX₀ : Measurable[ℱ 0] X₀) (hX₀' : Measurable[ℱ 0] X₀')
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hCb : IsDetCovDensity T Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
    (Z Zb R : ℝ → Ω → E)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
    (hZm : ∀ t, Measurable (Z t)) (hZbm : ∀ t, Measurable (Zb t)) (hRm : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → E)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω)
    (hfin1 : ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P ≠ ⊤) (hfin2 : ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P ≠ ⊤)
    {Φ : PathSp T E → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T E) 2) :
    |∫ ω, Φ (windowPath 0 T X ω) ∂P - ∫ ω, Φ (windowPath 0 T Xb ω) ∂P| ≤
      (ENNReal.ofReal (detConst T K) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P).toReal +
        (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P).toReal +
        (1 / 2) * detConst T K ^ 2 * covDiscrepancy P T Sg Cb := by
  have hev := hS.1
  have hCv := detConst_pos T K
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  -- processes
  set Y₁ : ℝ → Ω → E := fun t ω => S.VE t 0 (S.j (X₀ ω)) + Z t ω with hY₁
  set Y₂ : ℝ → Ω → E := fun t ω => S.VE t 0 (S.j (X₀' ω)) + Z t ω with hY₂
  set Y₃ : ℝ → Ω → E := fun t ω => S.VE t 0 (S.j (X₀' ω)) + Zb t ω with hY₃
  have hvm : ∀ (x : Ω → H), Measurable x → ∀ t : ℝ, Measurable fun ω => S.VE t 0 (S.j (x ω)) :=
    fun x hx t => ((S.VE t 0).continuous.comp S.j.continuous).measurable.comp hx
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (X t) := fun t ht => by
    have : X t = fun ω => S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω := funext fun ω => hXd t ht ω
    rw [this]
    exact ((hvm X₀ hX₀m t).add (hZm t)).add (hRm t)
  have hY₁m : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Y₁ t) := fun t _ => (hvm X₀ hX₀m t).add (hZm t)
  have hY₂m : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Y₂ t) := fun t _ => (hvm X₀' hX₀'m t).add (hZm t)
  have hY₃m : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Y₃ t) := fun t _ => (hvm X₀' hX₀'m t).add (hZbm t)
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => S.VE t 0 (S.j x)) (Set.Icc 0 T) :=
    fun x => continuousOn_VE_zero S hev x
  have hY₁c : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y₁ t ω) (Set.Icc 0 T) := by
    filter_upwards [hZc] with ω hω
    exact (hVc (X₀ ω)).add hω
  have hY₂c : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y₂ t ω) (Set.Icc 0 T) := by
    filter_upwards [hZc] with ω hω
    exact (hVc (X₀' ω)).add hω
  have hY₃c : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y₃ t ω) (Set.Icc 0 T) := by
    filter_upwards [hZbc] with ω hω
    exact (hVc (X₀' ω)).add hω
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 T) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hwX := aemeasurable_windowPath P hT X hXm hXc
  have hwY₁ := aemeasurable_windowPath P hT Y₁ hY₁m hY₁c
  have hwY₂ := aemeasurable_windowPath P hT Y₂ hY₂m hY₂c
  have hwY₃ := aemeasurable_windowPath P hT Y₃ hY₃m hY₃c
  -- identification of window paths
  have hXb_eq : ∀ ω, windowPath 0 T Xb ω = windowPath 0 T Y₃ ω := fun ω =>
    windowPath_congr fun t ht => hXbd t ht ω
  have hX_eq : ∀ᵐ ω ∂P, windowPath 0 T X ω = windowPath 0 T Y₁ ω + windowPath 0 T R ω := by
    filter_upwards [hY₁c, hRc] with ω h1 h2
    exact windowPath_add_of_cont h1 h2 fun t ht => hXd t ht ω
  have hY₂_eq : ∀ᵐ ω ∂P, windowPath 0 T Y₂ ω = vpath S hev (X₀' ω) + windowPath 0 T Z ω := by
    filter_upwards [hZc] with ω hω
    refine pcm_ext fun t => ?_
    rw [pcm_add, pcm_vpath, pcm_windowPath Y₂ ((hVc (X₀' ω)).add hω), pcm_windowPath Z hω]
  have hY₃_eq : ∀ᵐ ω ∂P, windowPath 0 T Y₃ ω = vpath S hev (X₀' ω) + windowPath 0 T Zb ω := by
    filter_upwards [hZbc] with ω hω
    refine pcm_ext fun t => ?_
    rw [pcm_add, pcm_vpath, pcm_windowPath Y₃ ((hVc (X₀' ω)).add hω), pcm_windowPath Zb hω]
  -- the three differences
  have hdiff1 : ∀ᵐ ω ∂P, ‖windowPath 0 T X ω - windowPath 0 T Y₁ ω‖ₑ ≤ ‖windowPath 0 T R ω‖ₑ := by
    filter_upwards [hX_eq] with ω hω
    rw [hω, add_sub_cancel_left]
  have hdiff2 : ∀ᵐ ω ∂P, ‖windowPath 0 T Y₁ ω - windowPath 0 T Y₂ ω‖ₑ ≤
      ENNReal.ofReal (detConst T K) * ‖X₀ ω - X₀' ω‖ₑ := by
    filter_upwards [hZc] with ω hω
    have h1 := (hVc (X₀ ω)).add hω
    have h2 := (hVc (X₀' ω)).add hω
    have hn : ‖windowPath 0 T Y₁ ω - windowPath 0 T Y₂ ω‖ ≤ detConst T K * ‖X₀ ω - X₀' ω‖ := by
      refine norm_pcm_le _ (by positivity) fun t => ?_
      rw [pcm_sub, pcm_windowPath Y₁ h1, pcm_windowPath Y₂ h2]
      simp only [hY₁, hY₂, add_sub_add_right_eq_sub, ← map_sub]
      exact hS.norm_le hT.le le_rfl t.2.1 t.2.2 (X₀ ω - X₀' ω)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hCv.le]
    exact ENNReal.ofReal_le_ofReal hn
  -- finiteness
  have hfinA : ∫⁻ ω, ‖windowPath 0 T X ω - windowPath 0 T Y₁ ω‖ₑ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hfin2 (lintegral_mono_ae hdiff1)
  have hfin12 : ENNReal.ofReal (detConst T K) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin1
  have hbdB : ∫⁻ ω, ‖windowPath 0 T Y₁ ω - windowPath 0 T Y₂ ω‖ₑ ∂P ≤
      ENNReal.ofReal (detConst T K) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P := by
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (detConst T K) * ‖X₀ ω - X₀' ω‖ₑ ∂P := lintegral_mono_ae hdiff2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfinB : ∫⁻ ω, ‖windowPath 0 T Y₁ ω - windowPath 0 T Y₂ ω‖ₑ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hfin12 hbdB
  have hA := cb_integral_diff_le P hΦ hwX hwY₁ hfinA
  have hB := cb_integral_diff_le P hΦ hwY₁ hwY₂ hfinB
  have hA' : (∫⁻ ω, ‖windowPath 0 T X ω - windowPath 0 T Y₁ ω‖ₑ ∂P).toReal ≤
      (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P).toReal :=
    ENNReal.toReal_mono hfin2 (lintegral_mono_ae hdiff1)
  have hB' : (∫⁻ ω, ‖windowPath 0 T Y₁ ω - windowPath 0 T Y₂ ω‖ₑ ∂P).toReal ≤
      (ENNReal.ofReal (detConst T K) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P).toReal :=
    ENNReal.toReal_mono hfin12 hbdB
  -- the CLT core
  have hC := clt_core P hT S hS hM hCb hG X₀' hX₀' Z Zb hZ hZb (fun t _ => hZm t) (fun t _ => hZbm t)
    hZc hZbc hΦ
  have e2 : ∫ ω, Φ (windowPath 0 T Y₂ ω) ∂P =
      ∫ ω, Φ (vpath S hev (X₀' ω) + windowPath 0 T Z ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hY₂_eq] with ω hω
    rw [hω]
  have e3 : ∫ ω, Φ (windowPath 0 T Xb ω) ∂P =
      ∫ ω, Φ (vpath S hev (X₀' ω) + windowPath 0 T Zb ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hY₃_eq] with ω hω
    rw [hXb_eq, hω]
  rw [abs_le] at hA hB hC ⊢
  rw [← e2, ← e3] at hC
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

end HRS.Uniform.Q45
