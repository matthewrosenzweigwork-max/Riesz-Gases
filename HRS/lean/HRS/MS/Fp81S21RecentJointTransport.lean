import HRS.Main.Headline
import HRS.ME.BiasC

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS

private theorem fp81s21_recentJoint_translate_both_le
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

private theorem fp81s21_recentJoint_mean_diff_le
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

private theorem fp81s21_recentJoint_map_bound
    {Ω₁ Ω₂ A B : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (ν : Measure Ω₂) [IsProbabilityMeasure ν]
    (f : Ω₁ → A) (g : Ω₂ → A) (hf : Measurable f) (hg : Measurable g)
    (L : A →L[ℝ] B) (k e : ℝ) (hk : ‖L‖ ≤ k) (he : 0 ≤ e)
    (hW : wassersteinE 2 (law μ f) (law ν g) ≤ ENNReal.ofReal e) :
    wassersteinE 2 (law μ (fun ω => L (f ω))) (law ν (fun ω => L (g ω))) ≤
      ENNReal.ofReal (k * e) := by
  letI : IsProbabilityMeasure (law μ f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law ν g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hm (ρ : Measure Ω₁) : law ρ (fun ω => L (f ω)) = (law ρ f).map L :=
    (Measure.map_map L.continuous.measurable hf).symm
  have hn : law ν (fun ω => L (g ω)) = (law ν g).map L :=
    (Measure.map_map L.continuous.measurable hg).symm
  rw [hm μ, hn]
  calc
    _ ≤ ENNReal.ofReal ‖L‖ * wassersteinE 2 (law μ f) (law ν g) :=
      HRS.Main.wassersteinE_map_clm_le L 2 (by norm_num) _ _
    _ ≤ ENNReal.ofReal ‖L‖ * ENNReal.ofReal e := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = ENNReal.ofReal (‖L‖ * e) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal (k * e) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk he)

/-- Partial centering of the prediction coordinate of the joint physical triple.
Instantiate `T_H`, `D_a`, `J_a` with `smoothPathToL2`, `VDtransport`, `VJtransport`.
The covariance coordinate uses the raw linear path. Product norms are sup norms. -/
theorem fp81s21_recent_joint_transport
    {Ω₁ Ω₂ X U Y V W : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
    [SecondCountableTopology U] [CompleteSpace U]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [CompleteSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] [CompleteSpace W]
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (ν : Measure Ω₂) [IsProbabilityMeasure ν]
    (XN : Ω₁ → X) (UBN : Ω₁ → U) (XG : Ω₂ → X) (UBG : Ω₂ → U)
    (hXN : Measurable XN) (hUBN : Measurable UBN)
    (hXG : Measurable XG) (hUBG : Measurable UBG)
    (hXN2 : MemLp XN 2 μ) (_hUBN2 : MemLp UBN 2 μ)
    (hXG2 : MemLp XG 2 ν) (_hUBG2 : MemLp UBG 2 ν)
    (P : X →L[ℝ] Y) (D_a : U →L[ℝ] V) (J_a : U →L[ℝ] W) (T_H : X →L[ℝ] U)
    (Kpred dL jL e : ℝ) (hP : ‖P‖ ≤ Kpred) (hD : ‖D_a‖ ≤ dL) (hJ : ‖J_a‖ ≤ jL)
    (he : 0 ≤ e)
    (hW : wassersteinE 2 (law μ (fun ω => (XN ω, UBN ω)))
      (law ν (fun ω => (XG ω, UBG ω))) ≤ ENNReal.ofReal e) :
    wassersteinE 2
      (law μ (fun ω => (P (XN ω - ∫ ω', XN ω' ∂μ), (D_a (UBN ω), J_a (T_H (XN ω))))))
      (law ν (fun ω => (P (XG ω - ∫ ω', XG ω' ∂ν), (D_a (UBG ω), J_a (T_H (XG ω)))))) ≤
      ENNReal.ofReal (2 * max Kpred (max dL (jL * ‖T_H‖)) * e) := by
  let CL := max Kpred (max dL (jL * ‖T_H‖))
  have hK : 0 ≤ Kpred := (norm_nonneg P).trans hP
  have hCL : 0 ≤ CL := hK.trans (le_max_left _ _)
  let F : (X × U) →L[ℝ] Y × (V × W) :=
    (P.comp (ContinuousLinearMap.fst ℝ X U)).prod
      ((D_a.comp (ContinuousLinearMap.snd ℝ X U)).prod
        ((J_a.comp T_H).comp (ContinuousLinearMap.fst ℝ X U)))
  have hFn : ‖F‖ ≤ CL := by
    apply ContinuousLinearMap.opNorm_le_bound _ hCL
    intro z
    change max ‖P z.1‖ (max ‖D_a z.2‖ ‖J_a (T_H z.1)‖) ≤ CL * ‖z‖
    have hx : ‖z.1‖ ≤ ‖z‖ := le_max_left _ _
    have hu : ‖z.2‖ ≤ ‖z‖ := le_max_right _ _
    refine max_le ?_ (max_le ?_ ?_)
    · exact (P.le_opNorm _).trans (mul_le_mul
        (hP.trans (le_max_left _ _)) hx (norm_nonneg _) hCL)
    · exact (D_a.le_opNorm _).trans (mul_le_mul
        (hD.trans ((le_max_left _ _).trans (le_max_right _ _))) hu (norm_nonneg _) hCL)
    · calc
        ‖J_a (T_H z.1)‖ ≤ ‖J_a‖ * (‖T_H‖ * ‖z.1‖) :=
          (J_a.le_opNorm _).trans (mul_le_mul_of_nonneg_left (T_H.le_opNorm _) (norm_nonneg _))
        _ = (‖J_a‖ * ‖T_H‖) * ‖z.1‖ := by ring
        _ ≤ CL * ‖z‖ := mul_le_mul
          ((mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans
            ((le_max_right _ _).trans (le_max_right _ _))) hx (norm_nonneg _) hCL
  let R : (X × U) →L[ℝ] Y := P.comp (ContinuousLinearMap.fst ℝ X U)
  have hRn : ‖R‖ ≤ Kpred := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro z
    exact (P.le_opNorm _).trans
      (mul_le_mul hP (le_max_left _ _) (norm_nonneg _) hK)
  let f := fun ω => F (XN ω, UBN ω)
  let g := fun ω => F (XG ω, UBG ω)
  have hf : Measurable f := F.continuous.measurable.comp (hXN.prodMk hUBN)
  have hg : Measurable g := F.continuous.measurable.comp (hXG.prodMk hUBG)
  have hraw := fp81s21_recentJoint_map_bound μ ν _ _ (hXN.prodMk hUBN)
    (hXG.prodMk hUBG) F CL e hFn he hW
  have hpred := fp81s21_recentJoint_map_bound μ ν _ _ (hXN.prodMk hUBN)
    (hXG.prodMk hUBG) R Kpred e hRn he hW
  have hPN : Measurable (fun ω => P (XN ω)) := P.continuous.measurable.comp hXN
  have hPG : Measurable (fun ω => P (XG ω)) := P.continuous.measurable.comp hXG
  letI : IsProbabilityMeasure (law μ (fun ω => P (XN ω))) :=
    (Measure.isProbabilityMeasure_map_iff hPN.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law ν (fun ω => P (XG ω))) :=
    (Measure.isProbabilityMeasure_map_iff hPG.aemeasurable).2 inferInstance
  let mN := ∫ ω, P (XN ω) ∂μ
  let mG := ∫ ω, P (XG ω) ∂ν
  have hm : ENNReal.ofReal ‖mN - mG‖ ≤ ENNReal.ofReal (Kpred * e) :=
    (fp81s21_recentJoint_mean_diff_le μ ν _ _ hPN hPG
      (hXN2.continuousLinearMap_comp P) (hXG2.continuousLinearMap_comp P)).trans
        ((wassersteinE_one_le_two _ _).trans hpred)
  let sN : Y × (V × W) := (-mN, 0)
  let sG : Y × (V × W) := (-mG, 0)
  have hshift : wassersteinE 2 (law μ (fun ω => f ω + sN))
      (law ν (fun ω => g ω + sN)) ≤ ENNReal.ofReal (CL * e) := by
    have h := fp81s21_recentJoint_translate_both_le (law μ f) (law ν g) sN
    rw [Measure.map_map (measurable_add_const sN) hf,
      Measure.map_map (measurable_add_const sN) hg] at h
    exact h.trans hraw
  have hs : ‖sN - sG‖ = ‖mN - mG‖ := by
    simp [sN, sG, Prod.norm_def]
    rw [show -mN + mG = -(mN - mG) by abel, norm_neg]
  have hcost := (wassersteinE_translate ν 2 (by norm_num) g hg.aemeasurable sN sG)
  rw [hs] at hcost
  letI : IsProbabilityMeasure (law μ (fun ω => f ω + sN)) :=
    (Measure.isProbabilityMeasure_map_iff (hf.add_const _).aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law ν (fun ω => g ω + sN)) :=
    (Measure.isProbabilityMeasure_map_iff (hg.add_const _).aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law ν (fun ω => g ω + sG)) :=
    (Measure.isProbabilityMeasure_map_iff (hg.add_const _).aemeasurable).2 inferInstance
  have htotal := (wassersteinE_triangle 2 (by norm_num)
    (law μ (fun ω => f ω + sN)) (law ν (fun ω => g ω + sN))
    (law ν (fun ω => g ω + sG))).trans (add_le_add hshift (hcost.trans hm))
  have hbound : ENNReal.ofReal (CL * e) + ENNReal.ofReal (Kpred * e) ≤
      ENNReal.ofReal (2 * CL * e) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hCL he) (mul_nonneg hK he)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left Kpred (max dL (jL * ‖T_H‖))) he]
  have hmN := P.integral_comp_comm (hXN2.integrable (by norm_num))
  have hmG := P.integral_comp_comm (hXG2.integrable (by norm_num))
  simpa [f, g, F, sN, sG, mN, mG, hmN, hmG, map_sub, sub_eq_add_neg, CL]
    using htotal.trans hbound

#print axioms fp81s21_recent_joint_transport
end HRS.Fp81.S21
