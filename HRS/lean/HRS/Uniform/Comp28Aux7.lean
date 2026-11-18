import HRS.Uniform.Comp28Aux6

/-!
# COMP-28, part 7: Proposition 3.28 (smooth assertion): positive horizon and the degenerate point window
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem smooth_pos_w {a T K c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T) (hK : 0 ≤ K)
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
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω) :
    ENNReal.ofReal (smoothDist 2 (law P (windowPath a T X)) (law P (windowPath a T Xb))) ≤
      ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P +
        ENNReal.ofReal (K ^ 2 / 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P := by
  set RHS := ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P +
        ENNReal.ofReal (K ^ 2 / 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P
    with hRHS
  by_cases htop : RHS = ⊤
  · rw [htop]; exact le_top
  have hsplit := ENNReal.add_ne_top.1 htop
  have hsplit' := ENNReal.add_ne_top.1 hsplit.1
  have hfin12 := hsplit'.1
  have hfin2 := hsplit'.2
  have hdisc := lintegral_wdisc_eq P hM hCb (a := a) hc
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  have hmemT : ∀ s ∈ Set.Icc (0 : ℝ) T, a + s ∈ Set.Icc (0 : ℝ) (a + T) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hvm : ∀ (x : Ω → H), Measurable x → ∀ t : ℝ, Measurable fun ω => V t 0 (x ω) :=
    fun x hx t => (V t 0).continuous.measurable.comp hx
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => V t 0 x) (Set.Icc 0 (a + T)) :=
    fun x => continuousOn_V_zero V hcont x
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (X t) := fun t ht => by
    have : X t = fun ω => V t 0 (X₀ ω) + Z t ω + R t ω := funext fun ω => hXd t ht ω
    rw [this]
    exact ((hvm X₀ hX₀m t).add (hZm t)).add (hRm t)
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hXbm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Xb t) := fun t ht => by
    have : Xb t = fun ω => V t 0 (X₀' ω) + Zb t ω := funext fun ω => hXbd t ht ω
    rw [this]
    exact (hvm X₀' hX₀'m t).add (hZbm t)
  have hXbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Xb t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZbc] with ω h1
    exact ((hVc (X₀' ω)).add h1).congr fun t ht => hXbd t ht ω
  have hwX := aemeasurable_windowPath_a P ha hT hT' X hXm hXc
  have hwXb := aemeasurable_windowPath_a P ha hT hT' Xb hXbm hXbc
  have hper : ∀ Φ ∈ CbUnitBall (PathSp T H) 2,
      ENNReal.ofReal |∫ z, Φ z ∂(law P (windowPath a T X)) - ∫ z, Φ z ∂(law P (windowPath a T Xb))| ≤
        RHS := by
    intro Φ hΦ
    have hΦc := (cbUnit_bounds hΦ).1.continuous
    have e1 : ∫ z, Φ z ∂(law P (windowPath a T X)) = ∫ ω, Φ (windowPath a T X ω) ∂P :=
      integral_map hwX hΦc.aestronglyMeasurable
    have e2 : ∫ z, Φ z ∂(law P (windowPath a T Xb)) = ∫ ω, Φ (windowPath a T Xb ω) ∂P :=
      integral_map hwXb hΦc.aestronglyMeasurable
    rw [e1, e2]
    have key := smooth_pos_fixed_w P ha hT hT' hK hc ℱ V hcont hV X₀ X₀' hX₀ hX₀' M Sg hM G Cb hCb hG Z Zb R
      hZ hZb hZc hZbc hRc hZm hZbm hRm X Xb hXd hXbd hfin2 hfin12 hΦ
    have hJ : 0 ≤ covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb :=
      integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ =>
        mul_nonneg (sq_nonneg _) (traceNormForm_nonneg _)
    calc ENNReal.ofReal |∫ ω, Φ (windowPath a T X ω) ∂P - ∫ ω, Φ (windowPath a T Xb ω) ∂P|
        ≤ ENNReal.ofReal ((ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P).toReal +
            (∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P).toReal +
              (1 / 2) * K ^ 2 * covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb) :=
          ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
            ∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P +
            ENNReal.ofReal (K ^ 2 / 2) * ENNReal.ofReal (covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_toReal hfin12, ENNReal.ofReal_toReal hfin2,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
      _ = RHS := by rw [hRHS, hdisc]
  have hr0 : 0 ≤ RHS.toReal := ENNReal.toReal_nonneg
  have hsd : smoothDist 2 (law P (windowPath a T X)) (law P (windowPath a T Xb)) ≤ RHS.toReal := by
    refine Real.iSup_le (fun Φ => ?_) hr0
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (hper Φ.1 Φ.2)
  calc ENNReal.ofReal (smoothDist 2 (law P (windowPath a T X)) (law P (windowPath a T Xb)))
      ≤ ENNReal.ofReal RHS.toReal := ENNReal.ofReal_le_ofReal hsd
    _ = RHS := ENNReal.ofReal_toReal htop

end HRS.Uniform.Comp28
