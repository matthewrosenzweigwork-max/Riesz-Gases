import HRS.MS.Fp81S21B6iiDrift
import HRS.MS.Fp81S21B6iiAssembly2
import HRS.MS.Fp81S21MovingMeas
import HRS.MS.Fp81S21TimeRep14
import HRS.MS.MovEntAux12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private def fp81s21_b6ii_clipTime (T u : ℝ) : ℝ := max 0 (min u T)

private def fp81s21_b6ii_pathDrift {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (N : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (f : Euc p.d → ℝ) (T : ℝ) (Y : ℝ × Ω → EucConfig p.d N)
    (v : ℝ) (ω : Ω) : ℝ :=
  HRS.Whole.r2EmpDistr (r26t3_mu R (fp81s21_b6ii_clipTime T v))
      (Y (fp81s21_b6ii_clipTime T v, ω))
      (generatorW (r26t3_coeff R) (fp81s21_b6ii_clipTime T v) f) -
    fp81s21_b6ii_cN N *
      HRS.Whole.r2CommDistr p.d p.s
        (r26t3_mu R (fp81s21_b6ii_clipTime T v))
        (Y (fp81s21_b6ii_clipTime T v, ω)) f

private theorem fp81s21_b6ii_conv_joint_meas
    {d : ℕ} {U : Type*} [MeasurableSpace U]
    (s : ℝ) (g : U → Euc d → ℝ)
    (hg : Measurable (fun q : U × Euc d => g q.1 q.2)) :
    Measurable (fun q : U × Euc d =>
      convGradConvW (rieszKernelGrad d s) (g q.1) q.2) := by
  let k : (U × Euc d) × Euc d → Euc d := fun z =>
    if ‖z.1.2 - z.2‖ ≤ 1 / 4 then
      (g z.1.1 z.2 - g z.1.1 z.1.2) • rieszKernelGrad d s (z.1.2 - z.2)
    else g z.1.1 z.2 • rieszKernelGrad d s (z.1.2 - z.2)
  have hgy : Measurable (fun z : (U × Euc d) × Euc d => g z.1.1 z.2) :=
    hg.comp (measurable_fst.fst.prodMk measurable_snd)
  have hgx : Measurable (fun z : (U × Euc d) × Euc d => g z.1.1 z.1.2) :=
    hg.comp (measurable_fst.fst.prodMk measurable_fst.snd)
  have hdiff : Measurable (fun z : (U × Euc d) × Euc d => z.1.2 - z.2) :=
    measurable_fst.snd.sub measurable_snd
  have hG : Measurable (rieszKernelGrad d s) := HRS.MS.S111X1.kG_measurable s
  have hnearSet : MeasurableSet {z : (U × Euc d) × Euc d |
      ‖z.1.2 - z.2‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_norm.comp hdiff) measurable_const
  have hk : Measurable k := by
    dsimp [k]
    exact Measurable.ite hnearSet
      ((hgy.sub hgx).smul (hG.comp hdiff))
      (hgy.smul (hG.comp hdiff))
  have hi := hk.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Euc d)))
  have hm : Measurable (fun q : U × Euc d => ∫ y, k (q, y) ∂volume) :=
    hi.measurable
  convert hm using 1
  funext q
  simp [k, convGradConvW]

private theorem fp81s21_b6ii_measurable_pair_comp
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β]
    (F : α × β → ℝ) (hF : Measurable F)
    (t : Ω → α) (x : Ω → β) (ht : Measurable t) (hx : Measurable x) :
    Measurable (fun z : Ω => F (t z, x z)) := by
  exact hF.comp (ht.prodMk hx)

private theorem fp81s21_b6ii_clipped_density_data
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hT : 0 ≤ T) :
    Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_b6ii_clipTime T q.1) q.2) ∧
    ∀ u x, 0 ≤ R.ρ (fp81s21_b6ii_clipTime T u) x := by
  let U := Set.Icc (0 : ℝ) T
  have hρ := fp81s21_moving_density_joint_meas (H := T) p R hδ hδhalf
  have hclipmem : ∀ u, fp81s21_b6ii_clipTime T u ∈ U := by
    intro u
    constructor
    · exact le_max_left _ _
    · exact max_le hT (min_le_right _ _)
  have hclip : Measurable (fp81s21_b6ii_clipTime T) := by
    change Measurable (fun u : ℝ => max 0 (min u T))
    fun_prop
  have hclipU : Measurable (fun u : ℝ => (⟨fp81s21_b6ii_clipTime T u,
      hclipmem u⟩ : U)) := by
    change Measurable (fun u : ℝ =>
      (⟨max 0 (min u T), hclipmem u⟩ : U))
    fun_prop
  have hmap : Measurable (fun q : ℝ × Euc p.d =>
      ((⟨fp81s21_b6ii_clipTime T q.1, hclipmem q.1⟩ : U), q.2)) :=
    (hclipU.comp measurable_fst).prodMk measurable_snd
  have hρclip := hρ.comp hmap
  have hglobal := R.resulting.global T
  refine ⟨hρclip, ?_⟩
  intro u x
  exact (hglobal.density _ (hclipmem u)).nonneg x

private theorem fp81s21_b6ii_generator_clipped_meas
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hT : 0 ≤ T)
    (f : Euc p.d → ℝ) (hf : IsR2Test f) :
    Measurable (fun q : ℝ × Euc p.d =>
      generatorW (r26t3_coeff R) (fp81s21_b6ii_clipTime T q.1) f q.2) := by
  let C := r26t3_coeff R
  let D := quadraticGradientDyn p.d p.s p.a p.β
  have hρclip := fp81s21_b6ii_clipped_density_data p R hδ hδhalf hT
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by norm_num)
  have hgrad : Continuous (gradient f) :=
    HRS.MH.DualityRd.db1_gradient_continuous hf2
  have hlap : Continuous (Laplacian.laplacian f) :=
    HRS.MH.DualityRd.db1_laplacian_continuous hf2
  have hconvρ : Measurable (fun q : ℝ × Euc p.d =>
      convGradConvW (rieszKernelGrad p.d p.s)
        (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x) q.2) :=
    fp81s21_b6ii_conv_joint_meas (U := ℝ) p.s
      (fun (u : ℝ) x => R.ρ (fp81s21_b6ii_clipTime T u) x) hρclip.1
  have hmatρ : Measurable (fun q : ℝ × Euc p.d =>
      Torus.matVec D.M (convGradConvW (rieszKernelGrad p.d p.s)
        (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x) q.2)) :=
    (HRS.MH.DualityRd.db1_matVec_continuous D.M).measurable.comp hconvρ
  have hV2 : ContDiff ℝ 2 D.V := by
    change ContDiff ℝ 2 (confinement p.a : Euc p.d → ℝ)
    exact (HRS.MS.MovEnt.s66_confinement_facts p.a p.ha).1.of_le (by norm_num)
  have hpot : Measurable (fun q : ℝ × Euc p.d => gradient D.V q.2) :=
    (HRS.MH.DualityRd.db1_gradient_continuous hV2).measurable.comp measurable_snd
  have hdrift : Measurable (fun q : ℝ × Euc p.d => C.drift
      (fp81s21_b6ii_clipTime T q.1) q.2) := by
    change Measurable (fun q : ℝ × Euc p.d =>
      meanFieldDriftW D
        (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x) q.2)
    change Measurable (fun q : ℝ × Euc p.d =>
      Torus.matVec D.M (convGradConvW (rieszKernelGrad p.d p.s)
        (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x) q.2) -
        gradient D.V q.2)
    exact hmatρ.sub hpot
  have hmatGrad : Measurable (fun q : ℝ × Euc p.d =>
      Torus.matVec D.M.transpose (gradient f q.2)) :=
    (HRS.MH.DualityRd.db1_matVec_continuous D.M.transpose).measurable.comp
      (hgrad.measurable.comp measurable_snd)
  have hnonlocal : Measurable (fun q : ℝ × Euc p.d =>
      ∑ j : Fin p.d,
        (convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρ (fp81s21_b6ii_clipTime T q.1) y *
            (Torus.matVec D.M.transpose (gradient f y)) j) q.2) j) := by
    apply Finset.measurable_sum
    intro j hj
    have hρj : Measurable (fun q : ℝ × Euc p.d =>
        R.ρ (fp81s21_b6ii_clipTime T q.1) q.2 *
          (Torus.matVec D.M.transpose (gradient f q.2)) j) :=
      hρclip.1.mul ((measurable_pi_apply j).comp
        ((WithLp.measurable_ofLp 2 _).comp hmatGrad))
    have hconvj := fp81s21_b6ii_conv_joint_meas (U := ℝ) p.s
      (fun (u : ℝ) y => R.ρ (fp81s21_b6ii_clipTime T u) y *
        (Torus.matVec D.M.transpose (gradient f y)) j) hρj
    exact (measurable_pi_apply j).comp
      ((WithLp.measurable_ofLp 2 _).comp hconvj)
  change Measurable (fun q : ℝ × Euc p.d =>
    C.ν * Laplacian.laplacian f q.2 +
      inner ℝ (C.drift (fp81s21_b6ii_clipTime T q.1) q.2)
        (gradient f q.2) -
      ∑ j : Fin p.d,
        (convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρ (fp81s21_b6ii_clipTime T q.1) y *
            (Torus.matVec D.M.transpose (gradient f y)) j) q.2) j)
  exact ((measurable_const.mul (hlap.measurable.comp measurable_snd)).add
    (hdrift.inner (hgrad.measurable.comp measurable_snd))).sub hnonlocal

private theorem fp81s21_b6ii_pathDrift_meas
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ)
    (A : Particle R N) (hN : 2 ≤ N) (T : ℝ) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (f : Euc p.d → ℝ) (hf : IsR2Test f)
    (Y : ℝ × A.Ω → EucConfig p.d N) (hY : Measurable Y) :
    Measurable (fun q : ℝ × A.Ω =>
      fp81s21_b6ii_pathDrift R N f T Y q.1 q.2) := by
  have hρclip := fp81s21_b6ii_clipped_density_data p R hδ hδhalf hT
  have hgenclip := fp81s21_b6ii_generator_clipped_meas p R hδ hδhalf hT f hf
  have htime : Measurable (fun q : ℝ × A.Ω =>
      fp81s21_b6ii_clipTime T q.1) := by
    dsimp [fp81s21_b6ii_clipTime]
    fun_prop
  let XX : ℝ × A.Ω → EucConfig p.d N := fun q =>
    Y (fp81s21_b6ii_clipTime T q.1, q.2)
  have hXX : Measurable XX := hY.comp (htime.prodMk measurable_snd)
  let gg : ℝ → Euc p.d → ℝ := fun u x =>
    generatorW (r26t3_coeff R) (fp81s21_b6ii_clipTime T u) f x
  have hgg : Measurable (fun q : ℝ × Euc p.d => gg q.1 q.2) :=
    hgenclip
  have hXXi : ∀ i : Fin N, Measurable (fun q : ℝ × A.Ω => XX q i) := by
    intro i
    exact (measurable_pi_apply i).comp hXX
  have hEval : ∀ i : Fin N, Measurable (fun q : ℝ × A.Ω => gg q.1 (XX q i)) := by
    intro i
    exact fp81s21_b6ii_measurable_pair_comp
      (fun z : ℝ × Euc p.d =>
        generatorW (r26t3_coeff R) (fp81s21_b6ii_clipTime T z.1) f z.2)
      hgenclip (fun q : ℝ × A.Ω => q.1)
      (fun q : ℝ × A.Ω => XX q i) measurable_fst (hXXi i)
  have hPairEmp : Measurable (fun q : ℝ × A.Ω =>
      HRS.Whole.pair (HRS.Whole.empirical (XX q)) (gg q.1)) := by
    have hEq : (fun q : ℝ × A.Ω =>
        HRS.Whole.pair (HRS.Whole.empirical (XX q)) (gg q.1)) =
      fun q => (N : ℝ)⁻¹ * ∑ i : Fin N, gg q.1 (XX q i) := by
      funext q
      exact HRS.Whole.pair_empirical (by omega : 0 < N) (XX q) (gg q.1)
    rw [hEq]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hEval i)
  have hMean : Measurable (fun u : ℝ =>
    ∫ x, gg u x ∂HRS.Whole.withDensityReal
        (fun x => R.ρ (fp81s21_b6ii_clipTime T u) x)) :=
    fp81s21_moving_spatial_integral_meas hρclip.1 hρclip.2 hgg
  let etaY : ℝ × A.Ω → ℝ := fun q =>
    HRS.Whole.r2EmpDistr
      (HRS.Whole.withDensityReal (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x))
      (XX q) (gg q.1)
  have hetaY : Measurable etaY := by
    change Measurable (fun q => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical (XX q)) (gg q.1) -
        HRS.Whole.pair (HRS.Whole.withDensityReal
          (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x)) (gg q.1)))
    exact measurable_const.mul
      (hPairEmp.sub (hMean.comp measurable_fst))
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by norm_num)
  have hgrad : Continuous (gradient f) :=
    HRS.MH.DualityRd.db1_gradient_continuous hf2
  have hker : Measurable (fun xy : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient f) xy.1 xy.2) :=
    HRS.MS.Comm.comm_meas _ hgrad.measurable
  let k : ℝ → Euc p.d → Euc p.d → ℝ := fun _ x y =>
    commutatorKernel p.d p.s (gradient f) x y
  have hkm : Measurable (fun q : ℝ × Euc p.d × Euc p.d =>
      k q.1 q.2.1 q.2.2) := hker.comp measurable_snd
  have hEnergy := fp81s21_moving_pairEnergy_joint_meas (N := N)
    hρclip.1 hρclip.2 hkm
  have hEnergyPath : Measurable (fun q : ℝ × A.Ω =>
      HRS.Whole.pairEnergy (k (fp81s21_b6ii_clipTime T q.1)) (XX q)
        (HRS.Whole.withDensityReal
          (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x))) := by
    have hh := fp81s21_b6ii_measurable_pair_comp
      (fun q : ℝ × EucConfig p.d N =>
        HRS.Whole.pairEnergy (k q.1) q.2
          (HRS.Whole.withDensityReal
            (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x)))
      hEnergy (fun q : ℝ × A.Ω => q.1) XX measurable_fst hXX
    simpa [k] using hh
  let bY : ℝ × A.Ω → ℝ := fun q => (N : ℝ) *
      HRS.Whole.pairEnergy (k (fp81s21_b6ii_clipTime T q.1)) (XX q)
        (HRS.Whole.withDensityReal
          (fun x => R.ρ (fp81s21_b6ii_clipTime T q.1) x))
  have hbY : Measurable bY := measurable_const.mul hEnergyPath
  change Measurable (fun q => etaY q - fp81s21_b6ii_cN N * bY q)
  exact hetaY.sub (measurable_const.mul hbY)

/-- Product drift integrability and coordinate identification for the raw
physical drift. The product identity uses the B3 adjoint relation, U3's
weighted action, and the raw quadratic field representative. -/
theorem fp81s21_b6ii_product_drift
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ)
    (hN : 2 ≤ N) (A : Particle R N)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB0 : ℝ → A.Ω → r26t6_Coeff) (M2 CL a H : ℝ)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hL : Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2))
    (hM2 : 0 ≤ M2) (hCL : ∀ u, 0 ≤ u → ‖L u‖ ≤ CL)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : 0 ≤ a) (hH : 0 < H)
    (hηrep : fp81s21_MomentRep Es A.P
      (fp81s21_particleEmpField R N A) qη M2)
    (hBrep : fp81s21_MomentRep E A.P
      (fp81s21_particleQuadRawField R N A) qB0 M2)
    (hgen : ∀ u, 0 ≤ u → ∀ f,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
      IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4)
        (generatorW (r26t3_coeff R) u f))
    (hadj : ∀ u, 0 ≤ u → ∀ z f,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
      fp81s21_chartAction E (L u z) f =
        fp81s21_chartAction Es z (generatorW (r26t3_coeff R) u f))
    (hU3 : ∀ u, 0 ≤ u → ∀ᵐ ω ∂A.P, ∀ f,
      IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f →
      fp81s21_chartAction Es (qη u ω) f =
        fp81s21_particleEmpField R N A u ω f) :
    Integrable
      (fun z : ℝ × A.Ω => fp81s21_b6ii_D L N qη qB0 (a + z.1) z.2)
      ((volume.restrict (Set.Icc 0 H)).prod A.P) ∧
    ∀ j, (fun z : ℝ × A.Ω =>
        fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + z.1) z.2) =ᵐ[
          (volume.restrict (Set.Icc 0 H)).prod A.P]
      (fun z => fp81s21_chartAction E
        (fp81s21_b6ii_D L N qη qB0 (a + z.1) z.2) (E.test j)) := by
  have hInt := fp81s21_b6ii_product_drift_integrable R N hN A Es E qη qB0
    M2 CL a H L hL hM2 hCL ha hH hηrep hBrep
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  have htestWt : ∀ j,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) (E.test j) := by
    intro j
    exact (weightedTestSubmodule_iff).1
      (weighted_test_of_compact_smooth
        (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2) hP
        (E.test_smooth j))
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let ν : Measure (ℝ × A.Ω) := dt.prod A.P
  let T : ℝ := a + H
  obtain ⟨Y, hYmeas, hYae⟩ := HRS.MS.R2S11.s11_X_joint
    (A.strong (1 : ℝ)).adapted (A.strong (1 : ℝ)).cont
  have hT : 0 ≤ T := add_nonneg ha hH.le
  have htimeProd : ∀ᵐ z ∂ν, z.1 ∈ Set.Icc (0 : ℝ) H := by
    exact (Measure.quasiMeasurePreserving_fst (μ := dt) (ν := A.P)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hYaeProd : ∀ᵐ z ∂ν, ∀ u : ℝ,
      Y (u, z.2) = A.X u.toNNReal z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := dt) (ν := A.P)).ae hYae
  have hqηmeas : Measurable (fun z : ℝ × A.Ω => qη (a + z.1) z.2) :=
    hηrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hqBmeas : Measurable (fun z : ℝ × A.Ω => qB0 (a + z.1) z.2) :=
    hBrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hDmeas : Measurable (fun z : ℝ × A.Ω =>
      fp81s21_b6ii_D L N qη qB0 (a + z.1) z.2) := by
    change Measurable (fun z : ℝ × A.Ω =>
      L (a + z.1) (qη (a + z.1) z.2) -
        fp81s21_b6ii_cN N • qB0 (a + z.1) z.2)
    exact (hL.comp ((measurable_const.add measurable_fst).prodMk hqηmeas)).sub
      (by
        have hcN : Measurable (fun _ : ℝ × A.Ω => fp81s21_b6ii_cN N) :=
          measurable_const
        exact hcN.smul hqBmeas)
  refine ⟨hInt, ?_⟩
  intro j
  let target : ℝ × A.Ω → ℝ := fun z =>
    fp81s21_chartAction E
      (fp81s21_b6ii_D L N qη qB0 (a + z.1) z.2) (E.test j)
  have htarget : Measurable target := by
    change Measurable (fun z : ℝ × A.Ω =>
      inner ℝ (fp81s21_b6ii_D L N qη qB0 (a + z.1) z.2)
        (E.encode (E.test j)))
    exact hDmeas.inner measurable_const
  let path : ℝ × A.Ω → ℝ := fun z =>
    fp81s21_b6ii_pathDrift R N (E.test j) T Y (a + z.1) z.2
  have hpath : Measurable path := by
    have hbase : Measurable (fun z : ℝ × A.Ω =>
        fp81s21_b6ii_pathDrift R N (E.test j) T Y z.1 z.2) :=
      fp81s21_b6ii_pathDrift_meas (p := p) (δ := δ) R N A hN T hT
        hδ hδhalf (E.test j) (E.test_smooth j) Y hYmeas
    have hshift : Measurable (fun z : ℝ × A.Ω => (a + z.1, z.2)) :=
      (measurable_const.add measurable_fst).prodMk measurable_snd
    convert hbase.comp hshift using 1
    funext z
    rfl
  have hcoordSection : ∀ u, 0 ≤ u →
      (fun ω => fp81s21_b6ii_physicalDrift p R N A (E.test j) u ω) =ᵐ[A.P]
      (fun ω => fp81s21_chartAction E
        (fp81s21_b6ii_D L N qη qB0 u ω) (E.test j)) := by
    intro u hu
    filter_upwards [hU3 u hu, (hBrep.2 u hu).2.2] with ω hU hB
    have hgenwt := hgen u hu (E.test j) (htestWt j)
    have hU' := hU (generatorW (r26t3_coeff R) u (E.test j)) hgenwt
    have hB' := hB.1 (E.test j) (E.test_smooth j)
    have hAdj := hadj u hu (qη u ω) (E.test j) (htestWt j)
    have hsmul : fp81s21_chartAction E
        (fp81s21_b6ii_cN N • qB0 u ω) (E.test j) =
        fp81s21_b6ii_cN N * fp81s21_chartAction E (qB0 u ω) (E.test j) := by
      change inner ℝ (fp81s21_b6ii_cN N • qB0 u ω)
        (E.encode (E.test j)) =
          fp81s21_b6ii_cN N * inner ℝ (qB0 u ω) (E.encode (E.test j))
      rw [real_inner_smul_left]
    have hDact : fp81s21_chartAction E
        (fp81s21_b6ii_D L N qη qB0 u ω) (E.test j) =
        fp81s21_particleEmpField R N A u ω
            (generatorW (r26t3_coeff R) u (E.test j)) -
          fp81s21_b6ii_cN N * fp81s21_particleQuadRawField R N A u ω (E.test j) := by
      calc
        _ = fp81s21_chartAction E (L u (qη u ω)) (E.test j) -
            fp81s21_chartAction E (fp81s21_b6ii_cN N • qB0 u ω) (E.test j) := by
              simp [fp81s21_b6ii_D, fp81s21_chartAction, inner_sub_left]
        _ = fp81s21_chartAction Es (qη u ω)
              (generatorW (r26t3_coeff R) u (E.test j)) -
            fp81s21_b6ii_cN N * fp81s21_chartAction E (qB0 u ω) (E.test j) := by
              rw [hAdj, hsmul]
        _ = _ := by rw [hU', hB']
    simpa [fp81s21_b6ii_physicalDrift, fp81s21_b6ii_cN] using hDact.symm
  have hsec : ∀ᵐ t ∂dt, (fun ω => path (t, ω)) =ᵐ[A.P]
      (fun ω => target (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hu : 0 ≤ a + t := add_nonneg ha ht.1
    have huT : a + t ≤ T := by dsimp [T]; linarith [ht.2]
    have hclip : fp81s21_b6ii_clipTime T (a + t) = a + t := by
      dsimp [fp81s21_b6ii_clipTime]
      rw [min_eq_left huT, max_eq_right hu]
    have hpathActual : (fun ω => path (t, ω)) =ᵐ[A.P]
        (fun ω => fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + t) ω) := by
      filter_upwards [hYae] with ω hω
      change fp81s21_b6ii_pathDrift R N (E.test j) T Y (a + t) ω = _
      simp [fp81s21_b6ii_pathDrift, hclip, hω (a + t),
        fp81s21_b6ii_physicalDrift, fp81s21_b6ii_cN, fp81s21_particleEmpField,
        fp81s21_particleQuadRawField]
    exact hpathActual.trans (hcoordSection (a + t) hu)
  have hpathTarget : path =ᵐ[dt.prod A.P] target :=
    fp81s21_product_ae_of_section_ae dt A.P path target hpath htarget hsec
  have hactualPath : (fun z : ℝ × A.Ω =>
      fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + z.1) z.2) =ᵐ[ν] path := by
    filter_upwards [htimeProd, hYaeProd] with z hz hω
    have hu : 0 ≤ a + z.1 := add_nonneg ha hz.1
    have huT : a + z.1 ≤ T := by dsimp [T]; linarith [hz.2]
    have hclip : fp81s21_b6ii_clipTime T (a + z.1) = a + z.1 := by
      dsimp [fp81s21_b6ii_clipTime]
      rw [min_eq_left huT, max_eq_right hu]
    change fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + z.1) z.2 =
      fp81s21_b6ii_pathDrift R N (E.test j) T Y (a + z.1) z.2
    simp [fp81s21_b6ii_physicalDrift, fp81s21_b6ii_cN, fp81s21_b6ii_pathDrift, hclip,
      hω (a + z.1), fp81s21_particleEmpField, fp81s21_particleQuadRawField]
  have hfinal := hactualPath.trans hpathTarget
  simpa [target, path, ν, dt] using hfinal

#print axioms fp81s21_b6ii_product_drift
end HRS.Fp81.S21
end
