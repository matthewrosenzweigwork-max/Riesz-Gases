import HRS.MS.Fp81S21JointD4
import HRS.MS.Fp81S21WickApprox40
import HRS.MS.Fp81S21EmbedField12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

local instance fp81s21_jointD5_measurable (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointD5_borel (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A genuine time section is square-integrable over time and probability
space; consequently almost every time section is square-integrable in the
probability variable. -/
theorem fp81s21_TimeL2Rep_section_memLp_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U) :
    ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) H),
      MemLp (fun ω => q (a + t) ω) 2 P := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
  have hg : Measurable g := hq.comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hU2 : Integrable (fun ω => ‖U ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hrep.2.1.aestronglyMeasurable).1 hrep.2.1
  have hsections : ∀ᵐ ω ∂P, Integrable (fun t => ‖g (t, ω)‖ ^ 2) dt := by
    filter_upwards [hrep.2.2.2] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hg.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).1 hω.1
  have hnormEq : ∀ᵐ ω ∂P,
      ‖U ω‖ ^ 2 = ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt := by
    filter_upwards [hrep.2.2.2] with ω hω
    calc
      ‖U ω‖ ^ 2 = inner ℝ (U ω) (U ω) := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ t, inner ℝ ((U ω : ℝ → r26t6_Coeff) t)
            ((U ω : ℝ → r26t6_Coeff) t) ∂dt := L2.inner_def _ _
      _ = ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt := by
        apply integral_congr_ae
        filter_upwards [hω.2] with t ht
        rw [real_inner_self_eq_norm_sq, ht]
  have houter : Integrable (fun ω => ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt) P :=
    hU2.congr (hnormEq.mono fun _ h => h)
  let f : Ω × ℝ → ℝ := fun z => ‖g (z.2, z.1)‖ ^ 2
  have hf : Measurable f := (hg.comp measurable_swap).norm.pow_const 2
  have hswap : Integrable f (P.prod dt) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    refine ⟨hsections, ?_⟩
    simpa [f] using houter
  have hsq : Integrable (fun z : ℝ × Ω => ‖g z‖ ^ 2) (dt.prod P) := by
    convert hswap.swap using 1
    ext z
    simp [f]
  have hgLp : MemLp g 2 (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hsq
  have hgsq : Integrable (fun z : ℝ × Ω => ‖g z‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hgLp.aestronglyMeasurable).1 hgLp
  filter_upwards [hgsq.prod_right_ae] with t ht
  exact (memLp_two_iff_integrable_sq_norm
    (hg.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable).2 ht

/-- Pointwise centering of a genuine time section is itself represented by
centering its random time-L² class. The enlarged moment constant is harmless
and keeps the construction independent of any choice of representatives. -/
theorem fp81s21_TimeL2Rep_centered
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hrep : fp81s21_TimeL2Rep P q M a H U) :
    fp81s21_TimeL2Rep P (fun u ω => fp81s21_center P (q u) ω)
      (4 * M) a H (fp81s21_center P U) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let qbar : ℝ → Ω → r26t6_Coeff := fun u ω => fp81s21_center P (q u) ω
  let Ubar : Ω → Lp r26t6_Coeff 2 dt := fun ω => fp81s21_center P U ω
  have hmean : Measurable (fun u => ∫ ω, q u ω ∂P) :=
    hq.stronglyMeasurable.integral_prod_right.measurable
  have hqbar : Measurable (Function.uncurry qbar) := by
    exact (hq.comp (measurable_fst.prodMk measurable_snd)).sub
      (hmean.comp measurable_fst)
  have hUbar : Measurable Ubar := by
    exact hrep.1.sub measurable_const
  have hUbarLp : MemLp Ubar 2 P := by
    dsimp [Ubar, fp81s21_center]
    exact hrep.2.1.sub (memLp_const _)
  have hU2 : Integrable (fun ω => ‖U ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hrep.2.1.aestronglyMeasurable).1 hrep.2.1
  have hMeanNorm : ‖∫ ω, U ω ∂P‖ ^ 2 ≤ ∫ ω, ‖U ω‖ ^ 2 ∂P := by
    have hnormLp : MemLp (fun ω => ‖U ω‖) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa using hrep.2.1.norm
    have honeLp : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa using (memLp_const 1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun ω => norm_nonneg (U ω))
      (Filter.Eventually.of_forall fun _ => (by norm_num : 0 ≤ (1 : ℝ)))
      hnormLp honeLp
    have hholder : (∫ ω, ‖U ω‖ ∂P) ≤
        Real.sqrt (∫ ω, ‖U ω‖ ^ 2 ∂P) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hh
    have hnorm : ‖∫ ω, U ω ∂P‖ ≤
        Real.sqrt (∫ ω, ‖U ω‖ ^ 2 ∂P) :=
      (norm_integral_le_integral_norm _).trans hholder
    have hnonneg : 0 ≤ ∫ ω, ‖U ω‖ ^ 2 ∂P :=
      integral_nonneg (fun ω => sq_nonneg ‖U ω‖)
    have hsq := pow_le_pow_left₀ (norm_nonneg (∫ ω, U ω ∂P)) hnorm 2
    rw [Real.sq_sqrt hnonneg] at hsq
    exact hsq
  have hUbarSq : Integrable (fun ω => ‖Ubar ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hUbarLp.aestronglyMeasurable).1 hUbarLp
  have htarget : Integrable
      (fun ω => 2 * ‖U ω‖ ^ 2 + 2 * ‖∫ ω', U ω' ∂P‖ ^ 2) P :=
    (hU2.const_mul 2).add (integrable_const _)
  have hpt : ∀ ω, ‖Ubar ω‖ ^ 2 ≤
      2 * ‖U ω‖ ^ 2 + 2 * ‖∫ ω', U ω' ∂P‖ ^ 2 := by
    intro ω
    dsimp [Ubar, fp81s21_center]
    calc
      ‖U ω - ∫ ω', U ω' ∂P‖ ^ 2 ≤
          (‖U ω‖ + ‖∫ ω', U ω' ∂P‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ 2 * ‖U ω‖ ^ 2 + 2 * ‖∫ ω', U ω' ∂P‖ ^ 2 := by
        nlinarith [sq_nonneg (‖U ω‖ - ‖∫ ω', U ω' ∂P‖)]
  have hUbarBound : (∫ ω, ‖Ubar ω‖ ^ 2 ∂P) ≤ H * (4 * M) := by
    calc
      _ ≤ ∫ ω, (2 * ‖U ω‖ ^ 2 +
          2 * ‖∫ ω', U ω' ∂P‖ ^ 2) ∂P :=
        integral_mono_ae hUbarSq htarget (Filter.Eventually.of_forall hpt)
      _ = 2 * (∫ ω, ‖U ω‖ ^ 2 ∂P) +
          2 * ‖∫ ω', U ω' ∂P‖ ^ 2 := by
        rw [integral_add (hU2.const_mul 2) (integrable_const _),
          integral_const_mul]
        simp [IsProbabilityMeasure.measure_univ]
      _ ≤ 2 * (H * M) + 2 * (H * M) := by
        have hbound := hrep.2.2.1
        have hmean := hMeanNorm.trans hbound
        nlinarith
      _ = H * (4 * M) := by ring
  have hmeanSection := fp81s21_TimeL2Rep_mean_section P q M a H U hq hrep
  have hsections : ∀ᵐ ω ∂P,
      MemLp (fun t => qbar (a + t) ω) 2 dt ∧
        ⇑(Ubar ω) =ᵐ[dt] (fun t => qbar (a + t) ω) := by
    filter_upwards [hrep.2.2.2] with ω hω
    have hmeanLp : MemLp (fun t => ∫ ω', q (a + t) ω' ∂P) 2 dt :=
      (Lp.memLp (∫ ω', U ω' ∂P)).ae_eq hmeanSection
    have hbarLp : MemLp (fun t => qbar (a + t) ω) 2 dt := by
      dsimp [qbar, fp81s21_center]
      exact hω.1.sub hmeanLp
    refine ⟨hbarLp, ?_⟩
    have hEq : (fun t => (U ω : ℝ → r26t6_Coeff) t -
        (∫ ω', U ω' ∂P : Lp r26t6_Coeff 2 dt) t) =ᵐ[dt]
        (fun t => q (a + t) ω - ∫ ω', q (a + t) ω' ∂P) := by
      filter_upwards [hω.2, hmeanSection] with t hUt hMt
      rw [hUt, hMt]
    have hcoe : (⇑(Ubar ω) : ℝ → r26t6_Coeff) =ᵐ[dt]
        (fun t => (U ω : ℝ → r26t6_Coeff) t -
          (∫ ω', U ω' ∂P : Lp r26t6_Coeff 2 dt) t) := by
      dsimp [Ubar, fp81s21_center]
      exact Lp.coeFn_sub _ _
    filter_upwards [hcoe, hEq] with t hbar hsection
    rw [hbar, hsection]
    simpa [qbar, fp81s21_center] using hsection
  exact ⟨hUbar, hUbarLp, hUbarBound, hsections⟩

/-- For a fixed finite rank family, the particle statistic differs from the
centered raw polynomial time class by only its centered empirical diagonal.
The diagonal estimate is uniform in particle count and starting time. -/
theorem fp81s21_particle_rankDiagonal_timeSqErr_fixed
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (M2 : ℝ) (hM2 : 0 ≤ M2)
    (m : ℕ) (Ds : Fin m → fp81s21_RankKernel p.d)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (hdiag : ∀ j : Fin m, ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω => ‖(1 / 2 : ℝ) • fp81s21_center A.P
        (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
          (fp81s21_rankKernelDiagonal (Ds j))) ω‖ ^ 2) A.P ∧
      (∫ ω, ‖(1 / 2 : ℝ) • fp81s21_center A.P
        (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
          (fp81s21_rankKernelDiagonal (Ds j))) ω‖ ^ 2 ∂A.P) ≤
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / (4 * (N : ℝ)))
    (Uraw : A.Ω → Lp r26t6_Coeff 2
      (volume.restrict (Set.Icc (0 : ℝ) H)))
    (Mraw : ℝ) (qraw : ℝ → A.Ω → r26t6_Coeff)
    (hqraw : Measurable (Function.uncurry qraw))
    (hraw : ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      qraw u ω = ∑ j : Fin m,
        fp81s21_polyAtD (Ds j) (fp81s21_rawEtaAt R A u ω) •
          fp81s21_coeffBasis j)
    (hrawRep : fp81s21_TimeL2Rep A.P qraw Mraw a H Uraw)
    (Urank : A.Ω → Lp r26t6_Coeff 2
      (volume.restrict (Set.Icc (0 : ℝ) H)))
    (Mrank : ℝ) (qrank : ℝ → A.Ω → r26t6_Coeff)
    (hqrank : Measurable (Function.uncurry qrank))
    (hrank : ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      qrank u ω = ∑ j : Fin m,
        fp81s21_particleQuad A u (Ds j).kernel ω • fp81s21_coeffBasis j)
    (hrankRep : fp81s21_TimeL2Rep A.P qrank Mrank a H Urank) :
    fp81s21_SqErr A.P (fp81s21_center A.P Uraw) Urank
      ((Real.sqrt (H * ((m : ℝ) * ∑ j : Fin m,
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4))) /
        Real.sqrt (N : ℝ)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let qcenter : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_center A.P (qraw u) ω
  let Ucenter : A.Ω → Lp r26t6_Coeff 2 dt := fun ω =>
    fp81s21_center A.P Uraw ω
  have hqcenter : Measurable (Function.uncurry qcenter) := by
    have hmean : Measurable (fun u => ∫ ω, qraw u ω ∂A.P) :=
      hqraw.stronglyMeasurable.integral_prod_right.measurable
    exact (hqraw.comp (measurable_fst.prodMk measurable_snd)).sub
      (hmean.comp measurable_fst)
  have hUcenter := fp81s21_TimeL2Rep_centered A.P qraw Mraw a H Uraw
    hqraw ha (le_of_lt hH) hrawRep
  have hrawSections := fp81s21_TimeL2Rep_section_memLp_ae
    A.P qraw Mraw a H Uraw hqraw hrawRep
  have hdiagData : ∀ j : Fin m, ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω => ‖(1 / 2 : ℝ) • fp81s21_center A.P
        (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
          (fp81s21_rankKernelDiagonal (Ds j))) ω‖ ^ 2) A.P ∧
      (∫ ω, ‖(1 / 2 : ℝ) • fp81s21_center A.P
        (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
          (fp81s21_rankKernelDiagonal (Ds j))) ω‖ ^ 2 ∂A.P) ≤
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / (4 * (N : ℝ)) :=
    hdiag
  have hbound : ∀ᵐ t ∂dt,
      MemLp (fun ω => qrank (a + t) ω - qcenter (a + t) ω) 2 A.P ∧
        (∫ ω, ‖qrank (a + t) ω - qcenter (a + t) ω‖ ^ 2 ∂A.P) ≤
          (m : ℝ) * (∑ j : Fin m,
            M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
            (N : ℝ) := by
    filter_upwards [hrawSections, ae_restrict_mem measurableSet_Icc] with t hrawL2 ht
    let u := a + t
    have hu : 0 ≤ u := add_nonneg ha ht.1
    let fj : Fin m → A.Ω → ℝ := fun j ω =>
      fp81s21_polyAtD (Ds j) (fp81s21_rawEtaAt R A u ω)
    let dj : Fin m → A.Ω → ℝ := fun j ω =>
      (1 / 2 : ℝ) • fp81s21_center A.P
        (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
          (fp81s21_rankKernelDiagonal (Ds j))) ω
    have hrawEq : ∀ᵐ ω ∂A.P,
        qraw u ω = ∑ j : Fin m, fj j ω • fp81s21_coeffBasis j := by
      filter_upwards [hraw] with ω hω
      exact hω u hu
    have hfjMem : ∀ j : Fin m, MemLp (fj j) 2 A.P := by
      intro j
      let L : r26t6_Coeff →L[ℝ] ℝ :=
        innerSL ℝ (fp81s21_coeffBasis j)
      have hcomp : MemLp (fun ω => L (qraw u ω)) 2 A.P :=
        hrawL2.continuousLinearMap_comp L
      have heq : fj j =ᵐ[A.P] fun ω => L (qraw u ω) := by
        filter_upwards [hrawEq] with ω hω
        have hpick : inner ℝ (fp81s21_coeffBasis j)
            (∑ i : Fin m, fj i ω • fp81s21_coeffBasis i) = fj j ω := by
          calc
            _ = (∑ i : Fin m, fj i ω • fp81s21_coeffBasis i) j :=
              fp81s21_coeffBasis_inner_apply _ j
            _ = fj j ω := fp81s21_finite_basis_coordinate2 m
              (fun i => fj i ω) j
        dsimp [L]
        rw [hω]
        exact hpick.symm
      have hfjMeas : AEStronglyMeasurable (fj j) A.P :=
        hcomp.aestronglyMeasurable.congr heq.symm
      have hnorm : ∀ᵐ ω ∂A.P,
          ‖L (qraw u ω)‖ = ‖fj j ω‖ := heq.mono fun ω hω => by rw [hω]
      exact hcomp.congr_norm hfjMeas hnorm
    have hfjInt : ∀ j : Fin m, Integrable (fj j) A.P :=
      fun j => (hfjMem j).integrable one_le_two
    have hrawCenter : ∀ᵐ ω ∂A.P,
        fp81s21_center A.P (qraw u) ω =
          ∑ j : Fin m, fp81s21_center A.P (fj j) ω • fp81s21_coeffBasis j := by
      filter_upwards [hrawEq] with ω hωeq
      have hmean : (∫ ω', qraw u ω' ∂A.P) =
          ∑ j : Fin m, (∫ ω', fj j ω' ∂A.P) • fp81s21_coeffBasis j := by
        calc
          _ = ∫ ω', (∑ j : Fin m, fj j ω' • fp81s21_coeffBasis j) ∂A.P :=
            integral_congr_ae hrawEq
          _ = _ := by
            rw [integral_finset_sum _ (fun j _ => (hfjInt j).smul_const _)]
            simp_rw [integral_smul_const]
      simp only [fp81s21_center]
      rw [hωeq, hmean]
      calc
        (∑ j : Fin m, fj j ω • fp81s21_coeffBasis j) -
            (∑ j : Fin m, (∫ ω', fj j ω' ∂A.P) • fp81s21_coeffBasis j) =
            ∑ j : Fin m,
              (fj j ω • fp81s21_coeffBasis j -
                (∫ ω', fj j ω' ∂A.P) • fp81s21_coeffBasis j) :=
          by rw [← Finset.sum_sub_distrib]
        _ = ∑ j : Fin m,
            (fj j ω - ∫ ω', fj j ω' ∂A.P) • fp81s21_coeffBasis j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [sub_smul]
    have htermIdentity : ∀ j : Fin m, ∀ ω,
        fp81s21_particleQuad A u (Ds j).kernel ω =
          fp81s21_center A.P (fj j) ω - dj j ω := by
      intro j ω
      rw [fp81s21_particle_finiteRank_identity p hδ hδh R hN A u hu (Ds j) ω]
      have hdiagfun : fp81s21_rankKernelDiagonal (Ds j) =
          (fun x => (Ds j).kernel x x) :=
        funext (fp81s21_rankKernelDiagonal_eq_kernel (Ds j))
      simp only [fj, dj, hdiagfun]
    have hrankEq : ∀ᵐ ω ∂A.P,
        qrank u ω = ∑ j : Fin m,
          (fp81s21_center A.P (fj j) ω - dj j ω) • fp81s21_coeffBasis j := by
      filter_upwards [hrank] with ω hω
      rw [hω u hu]
      exact Finset.sum_congr rfl fun j _ => by rw [htermIdentity j ω]
    have hdiffEq : (fun ω => qrank u ω - qcenter u ω) =ᵐ[A.P]
        (fun ω => -∑ j : Fin m, dj j ω • fp81s21_coeffBasis j) := by
      filter_upwards [hrankEq, hrawCenter] with ω hq hr
      rw [hq]
      dsimp [qcenter]
      change (∑ j : Fin m,
          (fp81s21_center A.P (fj j) ω - dj j ω) • fp81s21_coeffBasis j) -
          fp81s21_center A.P (qraw u) ω =
        -∑ j : Fin m, dj j ω • fp81s21_coeffBasis j
      rw [hr]
      calc
        (∑ j : Fin m,
            (fp81s21_center A.P (fj j) ω - dj j ω) • fp81s21_coeffBasis j) -
            (∑ j : Fin m,
              fp81s21_center A.P (fj j) ω • fp81s21_coeffBasis j) =
            ∑ j : Fin m,
              ((fp81s21_center A.P (fj j) ω - dj j ω) • fp81s21_coeffBasis j -
                fp81s21_center A.P (fj j) ω • fp81s21_coeffBasis j) := by
          rw [← Finset.sum_sub_distrib]
        _ = ∑ j : Fin m, -(dj j ω • fp81s21_coeffBasis j) := by
          apply Finset.sum_congr rfl
          intro j hj
          module
        _ = -∑ j : Fin m, dj j ω • fp81s21_coeffBasis j :=
          by rw [Finset.sum_neg_distrib]
    have hX : Measurable (A.X u.toNNReal) :=
      (A.strong (u + 1)).adapted u.toNNReal
    have hdMeas : ∀ j : Fin m, Measurable (dj j) := by
      intro j
      let g := fp81s21_rankKernelDiagonal (Ds j)
      have hg : Measurable g :=
        (fp81s21_rankKernelDiagonal_isR2Test (Ds j)).1.continuous.measurable
      have hf : Measurable (fun ω => Whole.pair
          (Whole.empirical (A.X u.toNNReal ω)) g) :=
        (S45.s45_measurable_pair_empirical (by omega) hg).comp hX
      have hcenter : Measurable (fun ω => fp81s21_center A.P
          (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω')) g) ω) := by
        exact hf.sub measurable_const
      simpa [dj, g, fp81s21_center, smul_eq_mul] using hcenter.const_mul (1 / 2 : ℝ)
    have hdiagInt : ∀ j : Fin m, Integrable (fun ω => ‖dj j ω‖ ^ 2) A.P := by
      intro j
      have h := hdiagData j u hu
      simpa [dj, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ))] using h.1
    have hdiagBound : ∀ j : Fin m,
        (∫ ω, ‖dj j ω‖ ^ 2 ∂A.P) ≤
          M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 /
            (4 * (N : ℝ)) := by
      intro j
      have h := hdiagData j u hu
      simpa [dj, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ))] using h.2
    have hsumInt : Integrable
        (fun ω => (m : ℝ) * ∑ j : Fin m, ‖dj j ω‖ ^ 2) A.P := by
      exact (integrable_finset_sum _ (fun j _ => hdiagInt j)).const_mul (m : ℝ)
    have hpoint : ∀ᵐ ω ∂A.P,
        ‖qrank u ω - qcenter u ω‖ ^ 2 ≤
          (m : ℝ) * ∑ j : Fin m, ‖dj j ω‖ ^ 2 := by
      filter_upwards [hdiffEq] with ω hω
      rw [hω]
      have hnorm : ‖∑ j : Fin m, dj j ω • fp81s21_coeffBasis j‖ ≤
          ∑ j : Fin m, |dj j ω| := by
        calc
          _ ≤ ∑ j : Fin m,
              ‖dj j ω • fp81s21_coeffBasis j‖ := norm_sum_le _ _
          _ = _ := by
            simp [norm_smul, fp81s21_coeffBasis.orthonormal.norm_eq_one,
              Real.norm_eq_abs]
      have hs : (∑ j : Fin m, |dj j ω|) ^ 2 ≤
          (m : ℝ) * ∑ j : Fin m, |dj j ω| ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin m => |dj j ω|))
      have hsq := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hs
      simpa [Real.norm_eq_abs, sq_abs] using hsq
    have hdiffSq : Integrable (fun ω => ‖qrank u ω - qcenter u ω‖ ^ 2) A.P := by
      have hmeas : Measurable (fun ω => ‖qrank u ω - qcenter u ω‖ ^ 2) :=
        (((hqrank.comp (measurable_const.prodMk measurable_id)).sub
          (hqcenter.comp (measurable_const.prodMk measurable_id))).norm.pow_const 2)
      apply Integrable.mono' hsumInt hmeas.aestronglyMeasurable
      filter_upwards [hpoint] with ω hω
      simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (m : ℝ) * ∑ j : Fin m, ‖dj j ω‖ ^ 2)] using hω
    have hmem : MemLp (fun ω => qrank u ω - qcenter u ω) 2 A.P :=
      (memLp_two_iff_integrable_sq_norm
        (((hqrank.comp (measurable_const.prodMk measurable_id)).sub
          (hqcenter.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)).2 hdiffSq
    have hboundInt : (∫ ω, ‖qrank u ω - qcenter u ω‖ ^ 2 ∂A.P) ≤
        (m : ℝ) * (∑ j : Fin m,
          M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
          (N : ℝ) := by
      calc
        _ ≤ ∫ ω, (m : ℝ) * ∑ j : Fin m, ‖dj j ω‖ ^ 2 ∂A.P :=
          integral_mono_ae hdiffSq hsumInt hpoint
        _ = (m : ℝ) * ∑ j : Fin m, ∫ ω, ‖dj j ω‖ ^ 2 ∂A.P := by
          rw [integral_const_mul, integral_finset_sum _ (fun j _ => hdiagInt j)]
        _ ≤ (m : ℝ) * ∑ j : Fin m,
            M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 /
              (4 * (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
          exact Finset.sum_le_sum fun j _ => hdiagBound j
        _ = (m : ℝ) * (∑ j : Fin m,
            M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
              (N : ℝ) := by
          have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
          have hsum : (∑ j : Fin m,
              M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
                (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / (4 * (N : ℝ))) =
              (∑ j : Fin m,
                M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
                  (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
                (N : ℝ) := by
            calc
              _ = (∑ j : Fin m,
                  M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2) /
                    (4 * (N : ℝ)) := by rw [← Finset.sum_div]
              _ = ((∑ j : Fin m,
                  M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2) / 4) /
                    (N : ℝ) := by field_simp
              _ = _ := by rw [Finset.sum_div]
          rw [hsum]
          ring
    exact ⟨hmem, hboundInt⟩
  have hC : 0 ≤ (m : ℝ) * (∑ j : Fin m,
      M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) := by
    apply mul_nonneg (Nat.cast_nonneg m)
    exact Finset.sum_nonneg fun j _ => by positivity
  have hsqerr := fp81s21_TimeL2Rep_SqErr_of_section_bound A.P qrank qcenter
    Mrank (4 * Mraw) a H
    ((m : ℝ) * (∑ j : Fin m,
      M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
      (N : ℝ)) Urank Ucenter hqrank hqcenter ha (le_of_lt hH)
    (div_nonneg hC (by positivity)) hrankRep hUcenter hbound
  have hscale : Real.sqrt (H *
      ((m : ℝ) * (∑ j : Fin m,
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
        (N : ℝ))) =
      Real.sqrt (H * ((m : ℝ) * ∑ j : Fin m,
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4)) /
        Real.sqrt (N : ℝ) := by
    rw [show H * ((m : ℝ) * (∑ j : Fin m,
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4) /
        (N : ℝ)) =
      (H * ((m : ℝ) * ∑ j : Fin m,
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4)) /
        (N : ℝ) by ring]
    exact Real.sqrt_div (mul_nonneg hH.le hC) _
  have hsqerrSymm : fp81s21_SqErr A.P Ucenter Urank
      ((Real.sqrt (H * ((m : ℝ) * ∑ j : Fin m,
        M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4))) /
        Real.sqrt (N : ℝ)) := by
    simpa only [hscale, fp81s21_SqErr, norm_sub_rev] using hsqerr
  simpa only [Ucenter] using hsqerrSymm

#print axioms fp81s21_TimeL2Rep_section_memLp_ae
#print axioms fp81s21_TimeL2Rep_centered
#print axioms fp81s21_particle_rankDiagonal_timeSqErr_fixed

end HRS.Fp81.S21
end
