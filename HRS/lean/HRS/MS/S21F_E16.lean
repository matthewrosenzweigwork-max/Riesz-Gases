import HRS.MS.S21F_E10
import HRS.MS.S21F_E11
import HRS.MS.S21F_E12
import HRS.MS.S21F_E13

/-!
# S21F, packet R26-T3.E16: equal initial laws give equal finite-dimensional strong-solution laws

For each side: the Brownian lift of the measurable time-zero map (E10), cutoff solutions `Ys M` (E12) which a.s. equal the
Picard evaluation of `(X 0, noise path)`, so the TUPLE `(Ys M (τ i))_i` has law `((law X 0) ⊗ Wiener).map G_M`; E11 gives
eventual equality of the whole tuple with `(X (τ i))_i`, and E13 passes to the limit.  The input laws coincide
(`hinit`, `bf_path_law_eq`), hence the limit laws do.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MD.EQLawPath

namespace HRS.MS.R26T3

theorem s21f_flow_meas {d N : ℕ} (s a β : ℝ) (hs : 0 ≤ s) (M : ℕ) (t : ℝ) :
    Measurable (r26t3_flow d N s a β M t) := by
  obtain ⟨B, hB⟩ := HRS.MS.S81G.s81g_pot (d := d) a
  exact HRS.MS.MfeConf.sb1Ψ_meas _
    (HRS.MS.MfeConf.sb1_driftM_isLip (quadraticGradientDyn d s a β)
      (HRS.MS.MfeConf.sb1kM_isKernel (d := d) s hs M) hB N) _ t

theorem s21f_side (d N : ℕ) (s a β : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℝ) (hS : 0 < S) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ζ t => W t ζ) P)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) S X₀ W X)
    {k : ℕ} (τ : Fin k → ℝ≥0) (hτ : ∀ i, (τ i : ℝ) ≤ S) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
      (hB : IsBrownianFiltration P ℱ W'),
      ∃ Ys : ℕ → ℝ → Ω → EucConfig d N,
        (∀ M t, Measurable (Ys M t)) ∧
        (∀ M, P.map (fun ζ i => Ys M (τ i : ℝ) ζ) =
          ((P.map (X 0)).prod (P.map (bfPath hB))).map
            (fun p i => r26t3_flow d N s a β M (τ i : ℝ) p)) ∧
        (∀ᵐ ζ ∂P, ∀ᶠ M : ℕ in atTop, ∀ i, Ys M (τ i : ℝ) ζ = X (τ i) ζ) := by
  have hind' : IndepFun (X 0) (fun ζ t => W t ζ) P :=
    hind.congr (hX.init.mono fun ζ h => h.symm) Filter.EventuallyEq.rfl
  obtain ⟨ℱ, W', hB, hX0, hcoord⟩ := r26t3_brownian_lift P (X 0) (hX.adapted 0) W hW hind'
  obtain ⟨Ys, hYs, hmeas, -⟩ := r26t3_cutoff_laws (N := N) s a β hs ha hβ P ℱ W' hB (X 0) hX0
  obtain ⟨B, hPot⟩ := HRS.MS.S81G.s81g_pot (d := d) a
  have hW'' : IsBrownianFiltration P (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) W' :=
    HRS.MP.SelfSimP4Impl.p4r_shiftFil_brownian hB
  have hlip : ∀ M : ℕ, HRS.IsLipschitzDrift (fun _ : ℝ =>
      HRS.MS.MfeConf.sb1DriftM (quadraticGradientDyn d s a β) (r26t3_regKernel d s M) N) :=
    fun M => HRS.MS.MfeConf.sb1_driftM_isLip (quadraticGradientDyn d s a β)
      (HRS.MS.MfeConf.sb1kM_isKernel (d := d) s hs M) hPot N
  have hae := r26t3_cutoff_identification (quadraticGradientDyn d s a β) rfl hPot hS hX hB hcoord
    (gM := r26t3_regKernel d s) (fun M => HRS.MS.MfeConf.sb1kM_isKernel (d := d) s hs M) hYs
  refine ⟨ℱ, W', hB, Ys, hmeas, fun M => ?_, ?_⟩
  · have hpic : ∀ᵐ ζ ∂P, ∀ i, (fun i => Ys M (τ i : ℝ) ζ) i =
        (fun i => r26t3_flow d N s a β M (τ i : ℝ) (X 0 ζ, bfPath hB ζ)) i := by
      filter_upwards [HRS.MS.MfeConf.sb1_sol_eq_picLim hW'' (hlip M) (hYs M)] with ζ h i
      exact h (τ i : ℝ) (τ i).2
    have hG : Measurable (fun (p : EucConfig d N × C(ℝ≥0, (Fin N × Fin d) → ℝ)) i =>
        r26t3_flow d N s a β M (τ i : ℝ) p) :=
      measurable_pi_iff.2 fun i => s21f_flow_meas s a β hs M _
    have hmp : Measurable (fun ζ => (X 0 ζ, bfPath hB ζ)) :=
      (hX.adapted 0).prodMk (measurable_bfPath hB)
    rw [Measure.map_congr (hpic.mono fun ζ h => funext h),
      ← HRS.MS.MfeConf.sb1_joint_law hB hX0,
      Measure.map_map hG hmp]
    rfl
  · filter_upwards [hae] with ζ h
    have := (Filter.eventually_all (ι := Fin k)).2 fun i => h.mono fun M hM => hM (τ i) (hτ i)
    exact this

theorem r26t3_strong_fdd_eq (d N : ℕ) (s a β : ℝ) (hd : 2 ≤ d)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hβ : 0 < β)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (S : ℝ) (hS : 0 < S) (X₀ : Ω → EucConfig d N) (X₀' : Ω' → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (W' : ℝ≥0 → Ω' → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) (X' : ℝ≥0 → Ω' → EucConfig d N)
    (hW : IsVectorBrownian P W) (hW' : IsVectorBrownian P' W')
    (hind : IndepFun X₀ (fun ζ t => W t ζ) P)
    (hind' : IndepFun X₀' (fun ζ t => W' t ζ) P')
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) S X₀ W X)
    (hX' : IsWholeStrongSolution P' (quadraticGradientDyn d s a β) S X₀' W' X')
    (hinit : law P X₀ = law P' X₀') (k : ℕ) (τ : Fin k → ℝ≥0)
    (hτ : ∀ i, (τ i : ℝ) ≤ S) :
    law P (fun ζ i => X (τ i) ζ) = law P' (fun ζ i => X' (τ i) ζ) := by
  have _ := hd
  have _ := hsd
  obtain ⟨ℱ, Wc, hB, Ys, hm, hlaw, hev⟩ := s21f_side d N s a β hs ha hβ P S hS X₀ W X hW hind hX τ hτ
  obtain ⟨ℱ', Wc', hB', Ys', hm', hlaw', hev'⟩ :=
    s21f_side d N s a β hs ha hβ P' S hS X₀' W' X' hW' hind' hX' τ hτ
  have h0 : P.map (X 0) = P'.map (X' 0) := by
    rw [Measure.map_congr hX.init, Measure.map_congr hX'.init]; exact hinit
  have hpath : P.map (bfPath hB) = P'.map (bfPath hB') := bf_path_law_eq hB hB'
  have hsame : ∀ M, P.map (fun ζ i => Ys M (τ i : ℝ) ζ) = P'.map (fun ζ i => Ys' M (τ i : ℝ) ζ) :=
    fun M => by rw [hlaw M, hlaw' M, h0, hpath]
  have hmeasT : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (Z : ℕ → ℝ → Ω₁ → EucConfig d N),
      (∀ M t, Measurable (Z M t)) → ∀ M, Measurable (fun ζ i => Z M (τ i : ℝ) ζ) :=
    fun Z hZ M => measurable_pi_iff.2 fun i => hZ M _
  have hXT : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (Z : ℝ≥0 → Ω₁ → EucConfig d N),
      (∀ t, Measurable (Z t)) → Measurable (fun ζ i => Z (τ i) ζ) :=
    fun Z hZ => measurable_pi_iff.2 fun i => hZ _
  have key : ∀ f : (Fin k → EucConfig d N) → ℝ, Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
      ∫ x, f x ∂(P.map (fun ζ i => X (τ i) ζ)) = ∫ x, f x ∂(P'.map (fun ζ i => X' (τ i) ζ)) := by
    intro f hf hb
    have t1 := r26t3_eventual_law_convergence P (fun M ζ i => Ys M (τ i : ℝ) ζ)
      (fun ζ i => X (τ i) ζ) (fun M => (hmeasT Ys hm M).aemeasurable)
      (hXT X hX.adapted).aemeasurable (hev.mono fun ζ h => h.mono fun M hM => funext hM) f hf hb
    have t2 := r26t3_eventual_law_convergence P' (fun M ζ i => Ys' M (τ i : ℝ) ζ)
      (fun ζ i => X' (τ i) ζ) (fun M => (hmeasT Ys' hm' M).aemeasurable)
      (hXT X' hX'.adapted).aemeasurable (hev'.mono fun ζ h => h.mono fun M hM => funext hM) f hf hb
    exact tendsto_nhds_unique t1 (t2.congr fun M => by rw [hsame M])
  refine Measure.ext fun A hA => ?_
  have hk := key (A.indicator 1) ((measurable_one).indicator hA) ⟨1, fun x => by
    by_cases hx : x ∈ A <;> simp [hx]⟩
  rw [integral_indicator_one hA, integral_indicator_one hA] at hk
  simp only [measureReal_def] at hk
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hk

end HRS.MS.R26T3
