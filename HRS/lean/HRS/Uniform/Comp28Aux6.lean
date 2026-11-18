import HRS.Uniform.Comp28Aux5

/-!
# COMP-28, part 6: the bound for a fixed test function, and the smooth assembly for `a + T > 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem smooth_pos_fixed_w {a T K c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (ℱ : Filtration ℝ mΩ) (V : ℝ → ℝ → H →L[ℝ] H)
    (hcont : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ a + T})
    (hV : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    (X₀ X₀' : Ω → H) (hX₀ : Measurable[ℱ 0] X₀) (hX₀' : Measurable[ℱ 0] X₀')
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg)
    (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hCb : IsDetCovDensity (a + T) Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
    (Z Zb R : ℝ → Ω → H)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
    (hZm : ∀ t, Measurable (Z t)) (hZbm : ∀ t, Measurable (Zb t)) (hRm : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → H)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (X₀ ω) + Z t ω + R t ω)
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω)
    (hfin2 : ∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P ≠ ⊤)
    (hfin12 : ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P ≠ ⊤)
    {Φ : PathSp T H → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T H) 2) :
    |∫ ω, Φ (windowPath a T X ω) ∂P - ∫ ω, Φ (windowPath a T Xb ω) ∂P| ≤
      (ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P).toReal +
        (∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P).toReal +
        (1 / 2) * K ^ 2 * covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb := by
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  have hmemT : ∀ s ∈ Set.Icc (0 : ℝ) T, a + s ∈ Set.Icc (0 : ℝ) (a + T) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set Y₁ : ℝ → Ω → H := fun t ω => V t 0 (X₀ ω) + Z t ω with hY₁
  set Y₂ : ℝ → Ω → H := fun t ω => V t 0 (X₀' ω) + Z t ω with hY₂
  set Y₃ : ℝ → Ω → H := fun t ω => V t 0 (X₀' ω) + Zb t ω with hY₃
  have hvm : ∀ (x : Ω → H), Measurable x → ∀ t : ℝ, Measurable fun ω => V t 0 (x ω) :=
    fun x hx t => (V t 0).continuous.measurable.comp hx
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (X t) := fun t ht => by
    have : X t = fun ω => V t 0 (X₀ ω) + Z t ω + R t ω := funext fun ω => hXd t ht ω
    rw [this]
    exact ((hvm X₀ hX₀m t).add (hZm t)).add (hRm t)
  have hY₁m : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Y₁ t) := fun t _ => (hvm X₀ hX₀m t).add (hZm t)
  have hY₂m : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Y₂ t) := fun t _ => (hvm X₀' hX₀'m t).add (hZm t)
  have hY₃m : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Y₃ t) := fun t _ => (hvm X₀' hX₀'m t).add (hZbm t)
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => V t 0 x) (Set.Icc 0 (a + T)) :=
    fun x => continuousOn_V_zero V hcont x
  have hY₁c : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y₁ t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZc] with ω hω
    exact (hVc (X₀ ω)).add hω
  have hY₂c : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y₂ t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZc] with ω hω
    exact (hVc (X₀' ω)).add hω
  have hY₃c : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y₃ t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZbc] with ω hω
    exact (hVc (X₀' ω)).add hω
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hwX := aemeasurable_windowPath_a P ha hT hT' X hXm hXc
  have hwY₁ := aemeasurable_windowPath_a P ha hT hT' Y₁ hY₁m hY₁c
  have hwY₂ := aemeasurable_windowPath_a P ha hT hT' Y₂ hY₂m hY₂c
  have hwY₃ := aemeasurable_windowPath_a P ha hT hT' Y₃ hY₃m hY₃c
  -- identification of window paths
  have hXb_eq : ∀ ω, windowPath a T Xb ω = windowPath a T Y₃ ω := fun ω =>
    windowPath_congr_a fun t ht => hXbd (a + t) (hmemT t ht) ω
  have hX_eq : ∀ᵐ ω ∂P, windowPath a T X ω = windowPath a T Y₁ ω + windowPath a T R ω := by
    filter_upwards [hY₁c, hRc, hXc] with ω h1 h2 h3
    refine pcm_ext fun s => ?_
    rw [pcm_add, pcm_windowPath_a ha hT X h3, pcm_windowPath_a ha hT Y₁ h1, pcm_windowPath_a ha hT R h2]
    exact hXd (a + s) (hmemT s s.2) ω
  have hY₂_eq : ∀ᵐ ω ∂P, windowPath a T Y₂ ω =
      resWin a T ha hT (vpathW V hcont (X₀' ω) + windowPath 0 (a + T) Z ω) := by
    filter_upwards [hZc, hY₂c] with ω hω h2
    rw [windowPath_eq_resWin ha hT Y₂ h2]
    congr 1
    refine pcm_ext fun t => ?_
    rw [pcm_windowPath Y₂ h2, pcm_vpathW_add_window V hcont (X₀' ω) Z hω]
  have hY₃_eq : ∀ᵐ ω ∂P, windowPath a T Y₃ ω =
      resWin a T ha hT (vpathW V hcont (X₀' ω) + windowPath 0 (a + T) Zb ω) := by
    filter_upwards [hZbc, hY₃c] with ω hω h2
    rw [windowPath_eq_resWin ha hT Y₃ h2]
    congr 1
    refine pcm_ext fun t => ?_
    rw [pcm_windowPath Y₃ h2, pcm_vpathW_add_window V hcont (X₀' ω) Zb hω]
  -- the differences
  have hdiff1 : ∀ᵐ ω ∂P, ‖windowPath a T X ω - windowPath a T Y₁ ω‖ₑ ≤ ‖windowPath a T R ω‖ₑ := by
    filter_upwards [hX_eq] with ω hω
    rw [hω, add_sub_cancel_left]
  have hdiff2 : ∀ᵐ ω ∂P, ‖windowPath a T Y₁ ω - windowPath a T Y₂ ω‖ₑ ≤
      ENNReal.ofReal (K * Real.exp (-c * a)) * ‖X₀ ω - X₀' ω‖ₑ := by
    filter_upwards [hY₁c, hY₂c] with ω h1 h2
    have hn : ‖windowPath a T Y₁ ω - windowPath a T Y₂ ω‖ ≤ K * Real.exp (-c * a) * ‖X₀ ω - X₀' ω‖ := by
      refine norm_pcm_le _ (by positivity) fun s => ?_
      rw [pcm_sub, pcm_windowPath_a ha hT Y₁ h1, pcm_windowPath_a ha hT Y₂ h2]
      simp only [hY₁, hY₂, add_sub_add_right_eq_sub, ← map_sub]
      have hs := hmemT s s.2
      refine ((V _ 0).le_opNorm _).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (hV 0 (a + s) le_rfl hs.1 hs.2).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
      nlinarith [s.2.1]
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hn
  -- finiteness
  have hfinA : ∫⁻ ω, ‖windowPath a T X ω - windowPath a T Y₁ ω‖ₑ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hfin2 (lintegral_mono_ae hdiff1)
  have hbdB : ∫⁻ ω, ‖windowPath a T Y₁ ω - windowPath a T Y₂ ω‖ₑ ∂P ≤
      ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P := by
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (K * Real.exp (-c * a)) * ‖X₀ ω - X₀' ω‖ₑ ∂P := lintegral_mono_ae hdiff2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfinB : ∫⁻ ω, ‖windowPath a T Y₁ ω - windowPath a T Y₂ ω‖ₑ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hfin12 hbdB
  have hA := cb_integral_diff_le P hΦ hwX hwY₁ hfinA
  have hB := cb_integral_diff_le P hΦ hwY₁ hwY₂ hfinB
  have hA' : (∫⁻ ω, ‖windowPath a T X ω - windowPath a T Y₁ ω‖ₑ ∂P).toReal ≤
      (∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P).toReal :=
    ENNReal.toReal_mono hfin2 (lintegral_mono_ae hdiff1)
  have hB' : (∫⁻ ω, ‖windowPath a T Y₁ ω - windowPath a T Y₂ ω‖ₑ ∂P).toReal ≤
      (ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P).toReal :=
    ENNReal.toReal_mono hfin12 hbdB
  -- the CLT core
  have hC := clt_core_w P ha hT hT' hK hc hcont hV hM hCb hG X₀' hX₀' Z Zb hZ hZb (fun t _ => hZm t)
    (fun t _ => hZbm t) hZc hZbc hΦ
  have e2 : ∫ ω, Φ (windowPath a T Y₂ ω) ∂P =
      ∫ ω, Φ (resWin a T ha hT (vpathW V hcont (X₀' ω) + windowPath 0 (a + T) Z ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hY₂_eq] with ω hω
    rw [hω]
  have e3 : ∫ ω, Φ (windowPath a T Xb ω) ∂P =
      ∫ ω, Φ (resWin a T ha hT (vpathW V hcont (X₀' ω) + windowPath 0 (a + T) Zb ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hY₃_eq] with ω hω
    rw [hXb_eq, hω]
  rw [abs_le] at hA hB hC ⊢
  rw [← e2, ← e3] at hC
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

end HRS.Uniform.Comp28
