import HRS.MS.Fp81S21PhysicalJointComparison
import HRS.ME.BiasC

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_centered_wassersteinE_translate_both_le
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B]
    (μ ν : Measure B) (a : B) :
    wassersteinE 2 (μ.map (fun x => x + a)) (ν.map (fun x => x + a)) ≤
      wassersteinE 2 μ ν := by
  unfold wassersteinE
  refine le_iInf fun π => ?_
  let T : B × B → B × B := fun z => (z.1 + a, z.2 + a)
  have hT : Measurable T := by fun_prop
  have hshift : Measurable (fun x : B => x + a) := by fun_prop
  have hπ : IsCoupling (π.1.map T) (μ.map (fun x => x + a))
      (ν.map (fun x => x + a)) := by
    constructor
    · calc
        (π.1.map T).map Prod.fst = π.1.map (fun z => (T z).1) :=
          Measure.map_map measurable_fst hT
        _ = (π.1.map Prod.fst).map (fun x => x + a) := by
          rw [Measure.map_map hshift measurable_fst]
          rfl
        _ = (μ.map (fun x => x + a)) := by rw [π.2.1]
    · calc
        (π.1.map T).map Prod.snd = π.1.map (fun z => (T z).2) :=
          Measure.map_map measurable_snd hT
        _ = (π.1.map Prod.snd).map (fun x => x + a) := by
          rw [Measure.map_map hshift measurable_snd]
          rfl
        _ = (ν.map (fun x => x + a)) := by rw [π.2.2]
  calc
    (⨅ ρ : couplings (μ.map fun x => x + a) (ν.map fun x => x + a),
        (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂ρ.1) ^ (1 / (2 : ℝ))) ≤
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂(π.1.map T)) ^ (1 / (2 : ℝ)) :=
        iInf_le _ (⟨π.1.map T, hπ⟩ : couplings (μ.map fun x => x + a) (ν.map fun x => x + a))
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π.1) ^ (1 / (2 : ℝ)) := by
      congr 1
      have hc : Measurable (fun z : B × B =>
          ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ))) := by
        have hn : Continuous (fun z : B × B => ‖z.1 - z.2‖) :=
          continuous_norm.comp (continuous_fst.sub continuous_snd)
        have hs : Measurable (fun z : B × B =>
            ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℕ))) :=
          ENNReal.measurable_ofReal.comp (hn.pow 2).measurable
        convert hs using 1
        ext z
        exact congrArg ENNReal.ofReal (Real.rpow_natCast _ 2)
      rw [lintegral_map hc hT]
      apply lintegral_congr
      intro z
      simp only [T, Prod.fst, Prod.snd]
      rw [show z.1 + a - (z.2 + a) = z.1 - z.2 by abel]

private theorem fp81s21_centered_wassersteinE_mean_diff_le
    {Ω₁ Ω₂ B : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B]
    [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B]
    (P : Measure Ω₁) [IsProbabilityMeasure P]
    (Q : Measure Ω₂) [IsProbabilityMeasure Q]
    (X : Ω₁ → B) (Y : Ω₂ → B)
    (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 Q) :
    ENNReal.ofReal ‖(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂Q)‖ ≤
      wassersteinE 1 (law P X) (law Q Y) := by
  let μ := law P X
  let ν := law Q Y
  let m := (∫ ω, X ω ∂P) - (∫ ω, Y ω ∂Q)
  letI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  obtain ⟨L, hL, hLm⟩ := exists_dual_vector'' ℝ m
  have hXint : Integrable X P := hX2.integrable (by norm_num)
  have hYint : Integrable Y Q := hY2.integrable (by norm_num)
  have hLXint : Integrable (fun ω => L (X ω)) P := by
    exact (hX2.continuousLinearMap_comp L).integrable (by norm_num)
  have hLYint : Integrable (fun ω => L (Y ω)) Q := by
    exact (hY2.continuousLinearMap_comp L).integrable (by norm_num)
  have hLμ : Integrable (fun z => L z) μ :=
    (integrable_map_measure L.continuous.aestronglyMeasurable hX.aemeasurable).2 hLXint
  have hLν : Integrable (fun z => L z) ν :=
    (integrable_map_measure L.continuous.aestronglyMeasurable hY.aemeasurable).2 hLYint
  have hmapX : (∫ z, L z ∂μ) = L (∫ ω, X ω ∂P) := by
    change (∫ z, L z ∂P.map X) = _
    rw [integral_map hX.aemeasurable L.continuous.aestronglyMeasurable]
    exact L.integral_comp_comm hXint
  have hmapY : (∫ z, L z ∂ν) = L (∫ ω, Y ω ∂Q) := by
    change (∫ z, L z ∂Q.map Y) = _
    rw [integral_map hY.aemeasurable L.continuous.aestronglyMeasurable]
    exact L.integral_comp_comm hYint
  have hdual := HRS.ME.Bias.le_wassersteinE_one_of_dual L hL hLμ hLν
  have habs : |(∫ z, L z ∂μ) - (∫ z, L z ∂ν)| = ‖m‖ := by
    calc
      |(∫ z, L z ∂μ) - (∫ z, L z ∂ν)| = |L m| := by
        rw [hmapX, hmapY, ← map_sub L]
      _ = ‖m‖ := by rw [hLm]; exact abs_of_nonneg (norm_nonneg m)
  rw [habs] at hdual
  simpa only [μ, ν, m] using hdual

/-- Centering each marginal by its own Bochner mean changes its `W₂`
comparison by at most a factor of two. The estimate uses only the normed
space structure; in particular it applies to product Banach spaces. -/
theorem fp81s21_centered_wassersteinE_le_two
    {Ω₁ Ω₂ B : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B] [CompleteSpace B]
    (P : Measure Ω₁) [IsProbabilityMeasure P]
    (Q : Measure Ω₂) [IsProbabilityMeasure Q]
    (X : Ω₁ → B) (Y : Ω₂ → B)
    (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 Q) :
    wassersteinE 2
      (law P (fun ω => X ω - ∫ ω', X ω' ∂P))
      (law Q (fun ω => Y ω - ∫ ω', Y ω' ∂Q)) ≤
      2 * wassersteinE 2 (law P X) (law Q Y) := by
  let μ := law P X
  let ν := law Q Y
  let mX := ∫ ω, X ω ∂P
  let mY := ∫ ω, Y ω ∂Q
  letI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hcX : Measurable (fun ω => X ω + (-mX)) := hX.add_const _
  have hcY : Measurable (fun ω => Y ω + (-mY)) := hY.add_const _
  letI : IsProbabilityMeasure (law P fun ω => X ω + (-mX)) :=
    (Measure.isProbabilityMeasure_map_iff hcX.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law Q fun ω => Y ω + (-mY)) :=
    (Measure.isProbabilityMeasure_map_iff hcY.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law Q fun ω => Y ω + (-mX)) :=
    (Measure.isProbabilityMeasure_map_iff (hY.add_const _).aemeasurable).2 inferInstance
  have hcenterX : law P (fun ω => X ω - mX) = μ.map (fun x => x + (-mX)) := by
    simp only [sub_eq_add_neg]
    change P.map (fun ω => X ω + (-mX)) = (P.map X).map (fun x => x + (-mX))
    exact (AEMeasurable.map_map_of_aemeasurable
      (measurable_add_const _).aemeasurable hX.aemeasurable).symm
  have hcenterY : law Q (fun ω => Y ω - mY) = ν.map (fun y => y + (-mY)) := by
    simp only [sub_eq_add_neg]
    change Q.map (fun ω => Y ω + (-mY)) = (Q.map Y).map (fun y => y + (-mY))
    exact (AEMeasurable.map_map_of_aemeasurable
      (measurable_add_const _).aemeasurable hY.aemeasurable).symm
  have hshiftY : law Q (fun ω => Y ω - mX) = ν.map (fun y => y + (-mX)) := by
    simp only [sub_eq_add_neg]
    change Q.map (fun ω => Y ω + (-mX)) = (Q.map Y).map (fun y => y + (-mX))
    exact (AEMeasurable.map_map_of_aemeasurable
      (measurable_add_const _).aemeasurable hY.aemeasurable).symm
  have hfirst : wassersteinE 2
      (law P (fun ω => X ω - mX)) (law Q (fun ω => Y ω - mX)) ≤
      wassersteinE 2 μ ν := by
    rw [hcenterX, hshiftY]
    exact fp81s21_centered_wassersteinE_translate_both_le μ ν (-mX)
  have hsecond : wassersteinE 2
      (law Q (fun ω => Y ω - mX)) (law Q (fun ω => Y ω - mY)) ≤
      ENNReal.ofReal ‖mX - mY‖ := by
    have h := wassersteinE_translate Q 2 (by norm_num) Y hY.aemeasurable (-mX) (-mY)
    have hnorm : ‖-mX + mY‖ = ‖mX + -mY‖ := by
      rw [show -mX + mY = -(mX + -mY) by abel, norm_neg]
    simpa only [sub_eq_add_neg, neg_neg, hnorm] using h
  have hmean := fp81s21_centered_wassersteinE_mean_diff_le P Q X Y hX hY hX2 hY2
  have hmean' : ENNReal.ofReal ‖mX - mY‖ ≤ wassersteinE 2 μ ν := by
    simpa [mX, mY, μ, ν] using hmean.trans (wassersteinE_one_le_two μ ν)
  calc
    wassersteinE 2 (law P (fun ω => X ω - mX))
        (law Q (fun ω => Y ω - mY)) ≤
      wassersteinE 2 (law P (fun ω => X ω - mX))
        (law Q (fun ω => Y ω - mX)) +
          wassersteinE 2 (law Q (fun ω => Y ω - mX))
            (law Q (fun ω => Y ω - mY)) :=
      wassersteinE_triangle 2 (by norm_num) _ _ _
    _ ≤ wassersteinE 2 μ ν + wassersteinE 2 μ ν :=
      add_le_add hfirst (hsecond.trans hmean')
    _ = 2 * wassersteinE 2 μ ν := by ring

private theorem fp81s21_centered_memLp_prodMk
    {Ω B C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) (f : Ω → B) (g : Ω → C)
    (hfm : MemLp f 2 P) (hgm : MemLp g 2 P) :
    MemLp (fun ω => (f ω, g ω)) 2 P := by
  have hsum : MemLp (fun ω => ‖f ω‖ + ‖g ω‖) 2 P := hfm.norm.add hgm.norm
  have hpair : AEStronglyMeasurable (fun ω => (f ω, g ω)) P :=
    hfm.aestronglyMeasurable.prodMk hgm.aestronglyMeasurable
  apply hsum.mono' hpair
  filter_upwards with ω
  change max ‖f ω‖ ‖g ω‖ ≤ ‖f ω‖ + ‖g ω‖
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

local instance fp81s21_centered_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_SmoothUH H) := borel _
local instance fp81s21_centered_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_SmoothUH H) := ⟨rfl⟩
local instance fp81s21_centered_CH_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_SmoothCH H) := borel _
local instance fp81s21_centered_CH_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_SmoothCH H) := ⟨rfl⟩

/-- Centered physical joint comparison, using the exact selections and profile
from `fp81s21_physical_joint_comparison`. -/
theorem fp81s21_physical_joint_comparison_centered (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ εAvg : ℕ → ℝ, (∀ m, 0 ≤ εAvg m) ∧ Tendsto εAvg atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ MUG : ℝ, 0 ≤ MUG ∧
        ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg,
        ∃ εN εG εB : ℕ → ℝ,
        ∃ S31 : fp81s21_Physical31 p R Es E εN εG εB,
        ∀ H : ℝ, (hH : 0 < H) →
          ∃ M2 : ℝ, 0 ≤ M2 ∧
          ∃ Savg : ℕ → fp81s21_SmoothUH H →L[ℝ] fp81s21_SmoothCH H,
          ∃ ω : ℕ → ℝ,
            (∀ k, 0 ≤ ω k) ∧ Tendsto ω atTop (𝓝 0) ∧
            (∀ k, ‖Savg k‖ ≤ Real.sqrt (((k : ℝ) + 2) / H)) ∧
          ∃ q31 : ℕ → ℝ,
            (∀ N, 0 ≤ q31 N) ∧ Tendsto q31 atTop (𝓝 0) ∧
          ∃ e : ℕ → ℝ,
            e = fp81s21_jointAvg_unifProfile ω
              (fun k => max 1 ‖Savg k‖) q31 ∧
            (∀ N, 0 ≤ e N) ∧ Tendsto e atTop (𝓝 0) ∧
            ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
              ∃ qN : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep E A.P
                  (fp81s21_particleEmpField R N A) qN M2 ∧
                ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
                  ∃ XN : A.Ω → fp81s21_SmoothCH H,
                  ∃ UN : A.Ω → fp81s21_SmoothUH H,
                  ∃ VηN : A.Ω → fp81s21_SmoothUH H,
                  ∃ UBN : A.Ω → fp81s21_SmoothUH H,
                  ∃ XG : G.Ω → fp81s21_SmoothCH H,
                  ∃ UG : G.Ω → fp81s21_SmoothUH H,
                  ∃ VηG : G.Ω → fp81s21_SmoothUH H,
                  ∃ UBG : G.Ω → fp81s21_SmoothUH H,
                    Measurable XN ∧ MemLp XN 2 A.P ∧
                    fp81s21_TimeL2Rep A.P
                      (fun u ζ => fp81s21_particle_embedField p Es E
                        (S31.qsηN N hN A u ζ)) S31.MN a H UN ∧
                    fp81s21_TimeL2Rep A.P
                      (fun u ζ => fp81s21_particle_embedField p Es E
                        (S31.qsηN N hN A u ζ)) S31.MN a H VηN ∧
                    UN =ᵐ[A.P] VηN ∧
                    Measurable UBN ∧ MemLp UBN 2 A.P ∧
                    fp81s21_TimeL2Rep A.P
                      (fun u ζ => fp81s21_particle_embedField p Es E
                        (S31.qsBN N hN A u ζ)) S31.MN a H UBN ∧
                    UN =ᵐ[A.P]
                      (fun ζ => fp81s21_smoothPathToL2 H hH (XN ζ)) ∧
                    (∀ᵐ ζ ∂A.P, ∀ t : Icc (0 : ℝ) H,
                      ∀ f : Euc p.d → ℝ, IsR2Test f →
                        fp81s21_chartAction E (XN ζ t) f =
                          fp81s21_particleEmpField R N A (a + (t : ℝ)) ζ f) ∧
                    Measurable XG ∧ MemLp XG 2 G.P ∧
                    fp81s21_TimeL2Rep G.P
                      (fp81s21_gaussian_embedFamily p Es E (S31.gaussian.qsηG G))
                      S31.gaussian.MηG a H UG ∧
                    fp81s21_TimeL2Rep G.P
                      (fp81s21_gaussian_embedFamily p Es E (S31.gaussian.qsηG G))
                      S31.gaussian.MηG a H VηG ∧
                    UG =ᵐ[G.P] VηG ∧
                    Measurable UBG ∧ MemLp UBG 2 G.P ∧
                    fp81s21_TimeL2Rep G.P (S31.gaussian.quadratic.qe G)
                      (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2)
                      a H UBG ∧
                    UG =ᵐ[G.P]
                      (fun ζ => fp81s21_smoothPathToL2 H hH (XG ζ)) ∧
                    (∀ᵐ ζ ∂G.P, ∀ t : Icc (0 : ℝ) H,
                      ∀ f : Euc p.d → ℝ, IsR2Test f →
                        fp81s21_chartAction E (XG ζ t) f =
                          OscDual.eval (G.Z (a + t) ζ) f) ∧
                    (∀ k : ℕ,
                      fp81s21_SqErr A.P XN (fun ζ => Savg k (UN ζ)) (ω k) ∧
                      fp81s21_SqErr G.P XG (fun ζ => Savg k (UG ζ)) (ω k)) ∧
                    Measurable (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) ∧
                    MemLp (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) 2 A.P ∧
                    Measurable (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) ∧
                    MemLp (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) 2 A.P ∧
                    Measurable (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) ∧
                    MemLp (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) 2 G.P ∧
                    Measurable (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) ∧
                    MemLp (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) 2 G.P ∧
                    wassersteinE 2
                      (law A.P (fun ζ => (XN ζ, UBN ζ)))
                      (law G.P (fun ζ => (XG ζ, UBG ζ))) ≤
                        ENNReal.ofReal (e N) ∧
                    wassersteinE 2
                      (law A.P (fun ζ =>
                        (XN ζ - (∫ ζ', XN ζ' ∂A.P),
                          UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
                      (law G.P (fun ζ =>
                        (XG ζ - (∫ ζ', XG ζ' ∂G.P),
                          UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
                        ENNReal.ofReal (2 * e N) := by
  obtain ⟨Es, E, εAvg, hεAvg, hεAvgLim, δ0, hδ0, hδ0h, hδ⟩ :=
    fp81s21_physical_joint_comparison p
  refine ⟨Es, E, εAvg, hεAvg, hεAvgLim, δ0, hδ0, hδ0h, ?_⟩
  intro δ hδpos hδle R
  obtain ⟨MUG, hMUG, canon, εN, εG, εB, S31, hδR⟩ := hδ δ hδpos hδle R
  refine ⟨MUG, hMUG, canon, εN, εG, εB, S31, ?_⟩
  intro H hH
  obtain ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, q31, hq31, hq31lim,
    e, he, hepos, helim, hNall⟩ := hδR H hH
  refine ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, q31, hq31, hq31lim,
    e, he, hepos, helim, ?_⟩
  intro N hN A
  obtain ⟨qN, hqN, hGall⟩ := hNall N hN A
  refine ⟨qN, hqN, ?_⟩
  intro G a ha
  obtain ⟨XN, UN, VηN, UBN, XG, UG, VηG, UBG,
    hXN, hXN2, hUNtime, hVηNtime, hUNVηN, hUBN, hUBN2, hUBNtime,
    hUNpath, hNphysical, hXG, hXG2, hUGtime, hVηGtime, hUGVηG,
    hUBG, hUBG2, hUBGtime, hUGpath, hGphysical, hSqErr, hRaw⟩ := hGall G a ha
  have hXNcenterMeas : Measurable (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) :=
    hXN.sub_const _
  have hXNcenterMem : MemLp (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) 2 A.P :=
    hXN2.sub (memLp_const _)
  have hUBNcenterMeas : Measurable (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) :=
    hUBN.sub_const _
  have hUBNcenterMem : MemLp (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) 2 A.P :=
    hUBN2.sub (memLp_const _)
  have hXGcenterMeas : Measurable (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) :=
    hXG.sub_const _
  have hXGcenterMem : MemLp (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) 2 G.P :=
    hXG2.sub (memLp_const _)
  have hUBGcenterMeas : Measurable (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) :=
    hUBG.sub_const _
  have hUBGcenterMem : MemLp (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) 2 G.P :=
    hUBG2.sub (memLp_const _)
  have hpairN : Measurable (fun ζ => (XN ζ, UBN ζ)) := hXN.prodMk hUBN
  have hpairG : Measurable (fun ζ => (XG ζ, UBG ζ)) := hXG.prodMk hUBG
  have hpairN2 := fp81s21_centered_memLp_prodMk A.P XN UBN hXN2 hUBN2
  have hpairG2 := fp81s21_centered_memLp_prodMk G.P XG UBG hXG2 hUBG2
  have hcenter := fp81s21_centered_wassersteinE_le_two
    A.P G.P (fun ζ => (XN ζ, UBN ζ)) (fun ζ => (XG ζ, UBG ζ))
    hpairN hpairG hpairN2 hpairG2
  have hmeanN : (∫ ζ, (XN ζ, UBN ζ) ∂A.P) =
      (∫ ζ, XN ζ ∂A.P, ∫ ζ, UBN ζ ∂A.P) := by
    exact integral_pair (hXN2.integrable (by norm_num)) (hUBN2.integrable (by norm_num))
  have hmeanG : (∫ ζ, (XG ζ, UBG ζ) ∂G.P) =
      (∫ ζ, XG ζ ∂G.P, ∫ ζ, UBG ζ ∂G.P) := by
    exact integral_pair (hXG2.integrable (by norm_num)) (hUBG2.integrable (by norm_num))
  have hLawN : law A.P (fun ζ =>
      (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))) =
      law A.P (fun ζ => (XN ζ, UBN ζ) - ∫ ζ', (XN ζ', UBN ζ') ∂A.P) := by
    congr 1
    funext ζ
    rw [hmeanN]
    simp
  have hLawG : law G.P (fun ζ =>
      (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P))) =
      law G.P (fun ζ => (XG ζ, UBG ζ) - ∫ ζ', (XG ζ', UBG ζ') ∂G.P) := by
    congr 1
    funext ζ
    rw [hmeanG]
    simp
  have hcenterToRaw : wassersteinE 2
      (law A.P (fun ζ =>
        (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
      (law G.P (fun ζ =>
        (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
      2 * wassersteinE 2
        (law A.P (fun ζ => (XN ζ, UBN ζ)))
        (law G.P (fun ζ => (XG ζ, UBG ζ))) := by
    rw [hLawN, hLawG]
    exact hcenter
  have hcenteredBound : wassersteinE 2
      (law A.P (fun ζ =>
        (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
      (law G.P (fun ζ =>
        (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
      ENNReal.ofReal (2 * e N) := by
    calc
      wassersteinE 2
          (law A.P (fun ζ =>
            (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
          (law G.P (fun ζ =>
            (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
        2 * wassersteinE 2
          (law A.P (fun ζ => (XN ζ, UBN ζ)))
          (law G.P (fun ζ => (XG ζ, UBG ζ))) := hcenterToRaw
      _ ≤ 2 * ENNReal.ofReal (e N) :=
        mul_le_mul_of_nonneg_left hRaw (by norm_num : (0 : ℝ≥0∞) ≤ 2)
      _ = ENNReal.ofReal (2 * e N) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  refine ⟨XN, UN, VηN, UBN, XG, UG, VηG, UBG, ?_⟩
  exact ⟨hXN, hXN2, hUNtime, hVηNtime, hUNVηN, hUBN, hUBN2, hUBNtime,
    hUNpath, hNphysical, hXG, hXG2, hUGtime, hVηGtime, hUGVηG, hUBG, hUBG2,
    hUBGtime, hUGpath, hGphysical, hSqErr, hXNcenterMeas, hXNcenterMem,
    hUBNcenterMeas, hUBNcenterMem, hXGcenterMeas, hXGcenterMem,
    hUBGcenterMeas, hUBGcenterMem, hRaw, hcenteredBound⟩

#print axioms fp81s21_centered_wassersteinE_le_two
#print axioms fp81s21_physical_joint_comparison_centered

end HRS.Fp81.S21
