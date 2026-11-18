import HRS.MS.Fp81S21MartBdg2
import HRS.MP.RdMartingale

/-!
# HRS S2.1(iii), B7: fourth moments of shifted brackets

This file bounds the squared bracket integral from the fixed-time squared-trace
estimate.  It is the analytic input to the final shifted BDG estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The time integral of the squared trace has a quadratic-in-time second
moment, uniformly over every nonnegative shift. -/
theorem fp81s21_b7_shiftedBracketSecondMoment
    (p : Parameters)
    {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 2 ≤ N)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A)
    (D : ℝ) (hD : 0 ≤ D)
    (htrace : ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω =>
        (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2) A.P ∧
      (∫ ω,
        (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2 ∂A.P) ≤ D)
    {b ell : ℝ} (hb : 0 ≤ b) (hell : 0 ≤ ell) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) ell,
      ∑ ia : Fin N × Fin p.d,
        ‖fp81s21_b6i_gradientNoise p E A Fp (b + r) ω ia‖ₑ ^ 2) ^ 2 ∂A.P ≤
      ENNReal.ofReal (ell ^ 2 * D) := by
  let Z := fp81s21_b6i_gradientNoise p E A Fp
  let q : ℝ → A.Ω → ℝ := fun u ω =>
    ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2
  let qe : ℝ × A.Ω → ℝ≥0∞ := fun z =>
    ∑ ia : Fin N × Fin p.d, ‖Z (b + z.1) z.2 ia‖ₑ ^ 2
  have hqnonneg : ∀ u ω, 0 ≤ q u ω := by
    intro u ω
    exact Finset.sum_nonneg fun ia _ => sq_nonneg _
  have hqe : Measurable qe := by
    have hprog : ∀ ia : Fin N × Fin p.d,
        IsProgressive Fp.ℱ (fun u ω => Z u ω ia) := by
      intro ia
      simpa [Z, fp81s21_b6i_gradientNoise] using
        fp81s21_b6i_gradient_noise_progressive p A Fp E ia
    have hmap : Measurable (fun z : ℝ × A.Ω => (b + z.1, z.2)) := by
      exact (measurable_const.add measurable_fst).prodMk measurable_snd
    refine Finset.measurable_sum _ fun ia _ => ?_
    have hz : Measurable (Function.uncurry fun u ω => Z u ω ia) :=
      HRS.MRep.isProgressive_measurable_uncurry (hprog ia)
    have hcoord : Measurable (fun z : ℝ × A.Ω => Z (b + z.1) z.2 ia) := by
      exact hz.comp hmap
    exact (measurable_enorm.comp hcoord).pow_const 2
  have hqeReal (r : ℝ) (ω : A.Ω) :
      qe (r, ω) = ENNReal.ofReal (q (b + r) ω) := by
    dsimp [qe, q, Z]
    rw [ENNReal.ofReal_sum_of_nonneg (fun ia _ => by positivity)]
    refine Finset.sum_congr rfl fun ia _ => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hqeSq (r : ℝ) (ω : A.Ω) :
      qe (r, ω) ^ 2 = ENNReal.ofReal (q (b + r) ω ^ 2) := by
    rw [hqeReal, ← ENNReal.ofReal_pow (hqnonneg _ _)]
  have hLinMoment (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) ell) :
      ∫⁻ ω, qe (r, ω) ^ 2 ∂A.P ≤ ENNReal.ofReal D := by
    have hu : 0 ≤ b + r := add_nonneg hb hr.1
    obtain ⟨hint, hbound⟩ := htrace (b + r) hu
    calc
      (∫⁻ ω, qe (r, ω) ^ 2 ∂A.P) =
          ∫⁻ ω, ENNReal.ofReal (q (b + r) ω ^ 2) ∂A.P := by
            apply lintegral_congr
            intro ω
            exact hqeSq r ω
      _ = ENNReal.ofReal (∫ ω, q (b + r) ω ^ 2 ∂A.P) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun ω => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal hbound
  let ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) ell)
  have hqeSection (ω : A.Ω) : AEMeasurable (fun r : ℝ => qe (r, ω)) ν := by
    exact (hqe.comp (measurable_id.prodMk measurable_const)).aemeasurable
  have hqSquareSection (ω : A.Ω) : AEMeasurable (fun r : ℝ => qe (r, ω) ^ 2) ν :=
    (hqeSection ω).pow_const 2
  have hholder : ∀ ω : A.Ω,
      (∫⁻ r in Set.Icc (0 : ℝ) ell, qe (r, ω) ∂volume) ^ 2 ≤
        (∫⁻ r in Set.Icc (0 : ℝ) ell, qe (r, ω) ^ 2 ∂volume) *
          ENNReal.ofReal ell := by
    intro ω
    let hpq : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq
      (f := fun r => qe (r, ω)) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      (hqeSection ω) aemeasurable_const
    have hconst : (∫⁻ r, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂ν) = ENNReal.ofReal ell := by
      simp [ν, Measure.restrict_apply_univ, Real.volume_Icc, hell]
    have hmul :
        (∫⁻ r, qe (r, ω) ∂ν) ≤
          (∫⁻ r, qe (r, ω) ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) *
            (∫⁻ r, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) := by
      simpa only [Pi.mul_apply, mul_one] using h
    rw [hconst] at hmul
    have hpow (x : ℝ≥0∞) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    calc
      (∫⁻ r, qe (r, ω) ∂ν) ^ 2 ≤
          ((∫⁻ r, qe (r, ω) ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) *
            (ENNReal.ofReal ell) ^ ((1 : ℝ) / 2)) ^ 2 := by
              exact pow_le_pow_left' hmul 2
      _ = (∫⁻ r, qe (r, ω) ^ (2 : ℝ) ∂ν) * ENNReal.ofReal ell := by
        rw [mul_pow, hpow, hpow]
      _ = (∫⁻ r in Set.Icc (0 : ℝ) ell, qe (r, ω) ^ 2 ∂volume) *
          ENNReal.ofReal ell := by
        simp only [ν, Measure.restrict_restrict]
        congr 1
        congr 1
        funext r
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hjoint : AEMeasurable
      (fun z : A.Ω × ℝ => qe (z.2, z.1) ^ 2) (A.P.prod ν) := by
    exact (hqe.comp (measurable_snd.prodMk measurable_fst)).pow_const 2 |>.aemeasurable
  have hswap :
      (∫⁻ ω, ∫⁻ r, qe (r, ω) ^ 2 ∂ν ∂A.P) =
        ∫⁻ r, ∫⁻ ω, qe (r, ω) ^ 2 ∂A.P ∂ν := by
    calc
      _ = ∫⁻ z, qe (z.2, z.1) ^ 2 ∂A.P.prod ν := (lintegral_prod _ hjoint).symm
      _ = _ := lintegral_prod_symm _ hjoint
  calc
    _ = ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) ell, qe (r, ω) ∂volume) ^ 2 ∂A.P := by
      rfl
    _ ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) ell, qe (r, ω) ^ 2 ∂volume) *
        ENNReal.ofReal ell ∂A.P := lintegral_mono fun ω => hholder ω
    _ = ENNReal.ofReal ell *
        (∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) ell, qe (r, ω) ^ 2 ∂volume ∂A.P) := by
      rw [lintegral_mul_const' _ _ (ENNReal.ofReal_ne_top)]
      simp only [mul_comm]
    _ = ENNReal.ofReal ell *
        (∫⁻ r in Set.Icc (0 : ℝ) ell, ∫⁻ ω, qe (r, ω) ^ 2 ∂A.P ∂volume) := by
      simpa only [ν] using congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal ell * x) hswap
    _ ≤ ENNReal.ofReal ell *
        (∫⁻ r in Set.Icc (0 : ℝ) ell, ENNReal.ofReal D ∂volume) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ell)
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hLinMoment r hr
    _ = ENNReal.ofReal (ell ^ 2 * D) := by
      rw [show (∫⁻ r in Set.Icc (0 : ℝ) ell, ENNReal.ofReal D ∂volume) =
        ENNReal.ofReal ell * ENNReal.ofReal D by
          simp [Real.volume_Icc, hell, hD, mul_comm]]
      have hring : ell * (ell * D) = ell ^ 2 * D := by ring
      simpa [ENNReal.ofReal_mul, hell, hD, mul_comm] using congrArg ENNReal.ofReal hring

private theorem fp81s21_b7_shiftedIncrementFourth
    (p : Parameters)
    {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 2 ≤ N)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A)
    (m : ℝ → A.Ω → r26t6_Coeff)
    (hm : Measurable (Function.uncurry m))
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation A.P Fp.ℱ T m
      (fun u ω => hsCovForm (fp81s21_b6i_gradientNoise p E A Fp u ω)))
    (D : ℝ) (hD : 0 ≤ D)
    (htrace : ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω =>
        (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2) A.P ∧
      (∫ ω,
        (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2 ∂A.P) ≤ D)
    {b ell : ℝ} (hb : 0 ≤ b) (hell : 0 ≤ ell) :
    MemLp (fun ω => m (b + ell) ω - m b ω) 4 A.P ∧
      (∫ ω, ‖m (b + ell) ω - m b ω‖ ^ 4 ∂A.P) ≤ HRS.MP.RdMart.mrmCb * D * ell ^ 2 := by
  let Z := fp81s21_b6i_gradientNoise p E A Fp
  let X : A.Ω → r26t6_Coeff := fun ω => m (b + ell) ω - m b ω
  by_cases hell0 : ell = 0
  · subst ell
    have hXzero : X = fun _ => 0 := by
      funext ω
      simp [X]
    constructor
    · simpa [hXzero] using (memLp_zero : MemLp (fun _ : A.Ω => (0 : r26t6_Coeff)) 4 A.P)
    · simp [X]
  · have hellpos : 0 < ell := lt_of_le_of_ne hell (Ne.symm hell0)
    letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
      HRS.StaticLimitAux.separable_lp (ι := ℕ)
    letI : SecondCountableTopology r26t6_Coeff :=
      UniformSpace.secondCountable_of_separable r26t6_Coeff
    have hshift := fp81s21_b7_shiftedHilbertMartingale
      Fp.filtered.brownian.complete hHM hb hellpos
    have hBDG := HRS.MP.RdMart.mrm_bdg_four (H := r26t6_Coeff)
      (κ := Fin N × Fin p.d) hell hshift
    have hBracket := fp81s21_b7_shiftedBracketSecondMoment p hN E A Fp D hD
      htrace hb hell
    have hBracketMax :
        (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) ell,
          ∑ ia : Fin N × Fin p.d, ‖Z (b + max r 0) ω ia‖ₑ ^ 2) ^ 2 ∂A.P) ≤
          ENNReal.ofReal (ell ^ 2 * D) := by
      calc
        _ = ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) ell,
            ∑ ia : Fin N × Fin p.d, ‖Z (b + r) ω ia‖ₑ ^ 2) ^ 2 ∂A.P := by
              apply lintegral_congr
              intro ω
              congr 1
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
              simp [max_eq_left hr.1]
        _ ≤ ENNReal.ofReal (ell ^ 2 * D) := hBracket
    have hlin : (∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℕ) ∂A.P) ≤
        ENNReal.ofReal (HRS.MP.RdMart.mrmCb * (ell ^ 2 * D)) := by
      calc
        _ ≤ ENNReal.ofReal HRS.MP.RdMart.mrmCb *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) ell,
              ∑ ia : Fin N × Fin p.d,
                ‖Z (b + max r 0) ω ia‖ₑ ^ 2) ^ 2 ∂A.P) := by
                simpa [X, max_eq_left hell] using hBDG
        _ ≤ ENNReal.ofReal HRS.MP.RdMart.mrmCb *
            ENNReal.ofReal (ell ^ 2 * D) :=
              mul_le_mul_of_nonneg_left hBracketMax (by positivity)
        _ = ENNReal.ofReal (HRS.MP.RdMart.mrmCb * (ell ^ 2 * D)) := by
              rw [← ENNReal.ofReal_mul HRS.MP.RdMart.mrmCb_nonneg]
    have hXmeas : Measurable X := by
      have hmAt (t : ℝ) : Measurable (fun ω => m t ω) :=
        hm.comp (measurable_const.prodMk measurable_id)
      exact (hmAt (b + ell)).sub (hmAt b)
    have hmem : MemLp X 4 A.P := by
      apply (memLp_iff).2
      apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (p := 4) (by norm_num) (by norm_num) hXmeas.aestronglyMeasurable).2
      have hfinite : (∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂A.P) < ⊤ := by
        exact lt_of_le_of_lt (by simpa [ENNReal.rpow_natCast] using hlin)
          ENNReal.ofReal_lt_top
      simpa only [ENNReal.toReal_ofNat] using hfinite
    have hlinRpow : (∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂A.P) ≤
        ENNReal.ofReal (HRS.MP.RdMart.mrmCb * (ell ^ 2 * D)) := by
      simpa [ENNReal.rpow_natCast] using hlin
    have hfourInt : Integrable (fun ω => ‖X ω‖ ^ 4) A.P :=
      hmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have hnormPow (v : r26t6_Coeff) :
        ‖v‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (‖v‖ ^ 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have hreal :
        (∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂A.P) =
          ENNReal.ofReal (∫ ω, ‖X ω‖ ^ 4 ∂A.P) := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ 4) ∂A.P := by
              apply lintegral_congr
              intro ω
              exact hnormPow (X ω)
        _ = ENNReal.ofReal (∫ ω, ‖X ω‖ ^ 4 ∂A.P) :=
              (ofReal_integral_eq_lintegral_ofReal hfourInt
                (Filter.Eventually.of_forall fun ω => by positivity)).symm
    constructor
    · exact hmem
    · have hconstnon : 0 ≤ HRS.MP.RdMart.mrmCb * D * ell ^ 2 :=
        mul_nonneg (mul_nonneg HRS.MP.RdMart.mrmCb_nonneg hD) (sq_nonneg ell)
      apply (ENNReal.ofReal_le_ofReal_iff hconstnon).1
      calc
        ENNReal.ofReal (∫ ω, ‖X ω‖ ^ 4 ∂A.P) =
            ∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂A.P := hreal.symm
        _ ≤ ENNReal.ofReal (HRS.MP.RdMart.mrmCb * (ell ^ 2 * D)) := hlinRpow
        _ = ENNReal.ofReal (HRS.MP.RdMart.mrmCb * D * ell ^ 2) := by
              congr 1
              ring

/-- One all-horizon B6-i martingale has fourth moments for every shifted
increment.  The constant is uniform in the horizon, particle number, and
filtered realization once the trajectory has been fixed. -/
theorem fp81s21_b7_shiftedFourthIncrements
    (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ R : Trajectory p δ,
        ∃ Cm : ℝ, 0 ≤ Cm ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ Fp : FilteredParticle A,
            ∃ m : ℝ → A.Ω → r26t6_Coeff,
              ((Measurable (Function.uncurry m) ∧
                (∀ T : ℝ, IsHSIntegrand A.P Fp.ℱ T
                  (fp81s21_b6i_gradientNoise p E A Fp)) ∧
                IsHilbertItoIntegral A.P Fp.ℱ Fp.Wc
                  (fp81s21_b6i_gradientNoise p E A Fp) m ∧
                (∀ H : ℝ, IsHilbertMartingaleWithCovariation A.P Fp.ℱ H m
                  (fun u ω => hsCovForm (fp81s21_b6i_gradientNoise p E A Fp u ω))) ∧
                (∀ᵐ ω ∂A.P, m 0 ω = 0) ∧
                (∀ u ω i k,
                  fp81s21_b6i_gradientNoise p E A Fp u ω (i, k) =
                    fp81s21_b6i_scale N p.β •
                      fp81s21_b6iGradientFeature
                        (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
                        (Fp.X (Real.toNNReal u) ω i) k) ∧
                ∀ x t, 0 ≤ t →
                  (fun ω => inner ℝ (m t ω) x) =ᵐ[A.P]
                    itoIntegral A.P Fp.ℱ Fp.Wc
                      (fun u ω ia => inner ℝ
                        (fp81s21_b6i_gradientNoise p E A Fp u ω ia) x) t) ∧
              (∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
                ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) H → t ∈ Set.Icc (0 : ℝ) H →
                  MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
                  (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
                    Cm * |t - s| ^ 2)) := by
  obtain ⟨δb6, hδb6, hδb6half, hb6⟩ :=
    fp81s21_b6i_hilbertMartingaleIto p E
  obtain ⟨δtrace, hδtrace, hδtracehalf, htraceAll⟩ :=
    fp81s21_b7_squaredTraceMoment p E
  let δstar := min δb6 δtrace
  have hδstar : 0 < δstar := lt_min hδb6 hδtrace
  have hδstarhalf : δstar ≤ 1 / 2 := by
    exact (min_le_left _ _).trans hδb6half
  refine ⟨δstar, hδstar, hδstarhalf, ?_⟩
  intro δ hδ hδle R
  have hδleB6 : δ ≤ δb6 := hδle.trans (min_le_left _ _)
  have hδleTrace : δ ≤ δtrace := hδle.trans (min_le_right _ _)
  obtain ⟨Cdouble, hCdouble, htraceNA⟩ := htraceAll δ hδ hδleTrace R
  obtain ⟨Cweight, hCweight, hB6NA⟩ := hb6 δ hδ hδleB6 R
  let K : ℝ := 2 * p.β⁻¹ * Classical.choose
    (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)
  let D : ℝ := K ^ 2 * Cdouble
  let Cm : ℝ := HRS.MP.RdMart.mrmCb * D
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
      (Classical.choose_spec
        (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)).1
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (sq_nonneg K) hCdouble
  have hCm : 0 ≤ Cm := by
    dsimp [Cm]
    exact mul_nonneg HRS.MP.RdMart.mrmCb_nonneg hD
  refine ⟨Cm, hCm, ?_⟩
  intro N hN A Fp
  obtain ⟨m, hm⟩ := hB6NA N hN A Fp
  rcases hm with ⟨hmMeas, hHS, hIto, hHM, hzero, hcoord, hcoordIto⟩
  have htrace : ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω =>
        (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2) A.P ∧
      (∫ ω,
        (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2 ∂A.P) ≤ D := by
    intro u hu
    obtain ⟨hi, hbound⟩ := htraceNA N hN A Fp u hu
    exact ⟨hi, by simpa [D, K] using hbound⟩
  refine ⟨m, ⟨hmMeas, hHS, hIto, hHM, hzero, hcoord, hcoordIto⟩, ?_⟩
  intro H hH a ha s t hs ht
  by_cases hst : s ≤ t
  · have hb : 0 ≤ a + s := add_nonneg ha hs.1
    have hell : 0 ≤ t - s := sub_nonneg.mpr hst
    have hstep := fp81s21_b7_shiftedIncrementFourth p hN E A Fp m hmMeas
      hHM D hD htrace hb hell
    have htime : a + s + (t - s) = a + t := by ring
    simpa [htime, abs_of_nonneg hell, Cm, D] using hstep
  · have hts : t ≤ s := le_of_lt (lt_of_not_ge hst)
    have hb : 0 ≤ a + t := add_nonneg ha ht.1
    have hell : 0 ≤ s - t := sub_nonneg.mpr hts
    have hstep := fp81s21_b7_shiftedIncrementFourth p hN E A Fp m hmMeas
      hHM D hD htrace hb hell
    have htime : a + t + (s - t) = a + s := by ring
    have hmem : MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P := by
      have hn := hstep.1.neg
      convert hn using 1
      funext ω
      simp only [Pi.neg_apply, Pi.sub_apply]
      rw [htime]
      abel
    have hmoment :
        (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) =
          (∫ ω, ‖m (a + s) ω - m (a + t) ω‖ ^ 4 ∂A.P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [norm_sub_rev]
    have habs : |t - s| = s - t := by
      calc
        |t - s| = -(t - s) := abs_of_nonpos (sub_nonpos.mpr hts)
        _ = s - t := by ring
    refine ⟨hmem, ?_⟩
    rw [hmoment, habs]
    simpa [htime, Cm, D] using hstep.2

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b7_shiftedBracketSecondMoment
#print axioms HRS.Fp81.S21.fp81s21_b7_shiftedFourthIncrements
