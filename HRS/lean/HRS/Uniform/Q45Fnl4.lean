import HRS.Uniform.Q45Fnl3

/-!
# Q45: assembly of Proposition 3.21 for `T > 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

lemma detConst_ge_one (T K : ℝ) : 1 ≤ detConst T K := by
  unfold detConst
  nlinarith [sq_nonneg K, Real.exp_pos (|K| * T / 2)]

theorem smooth_pos_final {T K : ℝ} (hT : 0 < T) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
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
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω) :
    ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb))) ≤
      ENNReal.ofReal (detConst T K ^ 2) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P +
        ENNReal.ofReal (detConst T K ^ 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P := by
  set Cv := detConst T K with hCv
  have hCv1 : 1 ≤ Cv := detConst_ge_one T K
  have hCvpos : 0 < Cv := by linarith
  set RHS := ENNReal.ofReal (Cv ^ 2) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P +
        ENNReal.ofReal (Cv ^ 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P
    with hRHS
  by_cases htop : RHS = ⊤
  · rw [htop]; exact le_top
  have hsplit := ENNReal.add_ne_top.1 htop
  have hsplit' := ENNReal.add_ne_top.1 hsplit.1
  have hC2 : ENNReal.ofReal (Cv ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'

  have hfin1 : ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P ≠ ⊤ := by
    intro h
    apply hsplit'.1
    rw [h, ENNReal.mul_top hC2]
  have hfin2 : ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P ≠ ⊤ := hsplit'.2
  have hdisc := lintegral_disc_eq P hM hCb
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  -- measurability of the window paths
  have hev := hS.1
  have hvm : ∀ (x : Ω → H), Measurable x → ∀ t : ℝ, Measurable fun ω => S.VE t 0 (S.j (x ω)) :=
    fun x hx t => ((S.VE t 0).continuous.comp S.j.continuous).measurable.comp hx
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => S.VE t 0 (S.j x)) (Set.Icc 0 T) :=
    fun x => continuousOn_VE_zero S hev x
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (X t) := fun t ht => by
    have : X t = fun ω => S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω := funext fun ω => hXd t ht ω
    rw [this]
    exact ((hvm X₀ hX₀m t).add (hZm t)).add (hRm t)
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 T) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  have hXbm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Xb t) := fun t ht => by
    have : Xb t = fun ω => S.VE t 0 (S.j (X₀' ω)) + Zb t ω := funext fun ω => hXbd t ht ω
    rw [this]
    exact (hvm X₀' hX₀'m t).add (hZbm t)
  have hXbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Xb t ω) (Set.Icc 0 T) := by
    filter_upwards [hZbc] with ω h1
    exact ((hVc (X₀' ω)).add h1).congr fun t ht => hXbd t ht ω
  have hwX := aemeasurable_windowPath P hT X hXm hXc
  have hwXb := aemeasurable_windowPath P hT Xb hXbm hXbc
  -- reduction to a bound for each test function
  have hper : ∀ Φ ∈ CbUnitBall (PathSp T E) 2,
      ENNReal.ofReal |∫ z, Φ z ∂(law P (windowPath 0 T X)) - ∫ z, Φ z ∂(law P (windowPath 0 T Xb))| ≤
        RHS := by
    intro Φ hΦ
    have hΦc := (cbUnit_bounds hΦ).1.continuous
    have e1 : ∫ z, Φ z ∂(law P (windowPath 0 T X)) = ∫ ω, Φ (windowPath 0 T X ω) ∂P :=
      integral_map hwX hΦc.aestronglyMeasurable
    have e2 : ∫ z, Φ z ∂(law P (windowPath 0 T Xb)) = ∫ ω, Φ (windowPath 0 T Xb ω) ∂P :=
      integral_map hwXb hΦc.aestronglyMeasurable
    rw [e1, e2]
    have key := smooth_pos_fixed hT P ℱ S hS X₀ X₀' hX₀ hX₀' M Sg hM G Cb hCb hG Z Zb R hZ hZb hZc hZbc
      hRc hZm hZbm hRm X Xb hXd hXbd hfin1 hfin2 hΦ
    calc ENNReal.ofReal |∫ ω, Φ (windowPath 0 T X ω) ∂P - ∫ ω, Φ (windowPath 0 T Xb ω) ∂P|
        ≤ ENNReal.ofReal ((ENNReal.ofReal Cv * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P).toReal +
            (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P).toReal + (1 / 2) * Cv ^ 2 * covDiscrepancy P T Sg Cb) :=
          ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal Cv * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P +
            ENNReal.ofReal ((1 / 2) * Cv ^ 2 * covDiscrepancy P T Sg Cb) := by
          have hJ : 0 ≤ covDiscrepancy P T Sg Cb := by
            unfold covDiscrepancy
            exact integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ =>
              traceNormForm_nonneg _
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin1),
            ENNReal.ofReal_toReal hfin2]
      _ ≤ RHS := by
          refine add_le_add (add_le_add ?_ le_rfl) ?_
          · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl
          · rw [hdisc]
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by nlinarith)
              (by
                unfold covDiscrepancy
                exact integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ =>
                  traceNormForm_nonneg _))
  -- the smooth distance
  have hr0 : 0 ≤ RHS.toReal := ENNReal.toReal_nonneg
  have hsd : smoothDist 2 (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) ≤ RHS.toReal := by
    refine Real.iSup_le (fun Φ => ?_) hr0
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (hper Φ.1 Φ.2)
  calc ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)))
      ≤ ENNReal.ofReal RHS.toReal := ENNReal.ofReal_le_ofReal hsd
    _ = RHS := ENNReal.ofReal_toReal htop

end HRS.Uniform.Q45
