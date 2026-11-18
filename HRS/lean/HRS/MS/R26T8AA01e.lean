import HRS.MS.R26T8AA01d

/-!
# S8.2 T8A A01 (part e): `tripleG(x,y,·)` is `ρ dz`-integrable for `x ≠ y`
Envelope (A01b) + integrability of the pole envelope (A01d) + a.e. strong measurability from continuity off `{x,y}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_cont_g (hs : 0 < criticalS d) (u : Euc d) :
    ContinuousOn (fun z => rieszKernelGrad d (criticalS d) (u - z)) {u}ᶜ := by
  have e : ∀ z : Euc d, z ≠ u → rieszKernelGrad d (criticalS d) (u - z) =
      (-criticalS d * ‖u - z‖ ^ (-criticalS d - 2)) • (u - z) := by
    intro z hz
    have hw : u - z ≠ 0 := sub_ne_zero.2 hz.symm
    ext j
    rw [r26t8a_rieszGrad_coord hs.ne' hw j]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have h1 : ContinuousOn (fun z : Euc d => -criticalS d * ‖u - z‖ ^ (-criticalS d - 2)) {u}ᶜ := by
    refine continuousOn_const.mul ?_
    have hn : ContinuousOn (fun z : Euc d => ‖u - z‖) {u}ᶜ :=
      (continuous_const.sub (continuous_id (X := Euc d)) : Continuous fun z : Euc d => u - z).norm.continuousOn
    refine ContinuousOn.rpow_const hn fun z hz => ?_
    left
    exact (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz))).ne'
  have h2 : ContinuousOn (fun z : Euc d => u - z) {u}ᶜ :=
    (continuous_const.sub (continuous_id (X := Euc d)) : Continuous fun z : Euc d => u - z).continuousOn
  have hc : ContinuousOn (fun z : Euc d => (-criticalS d * ‖u - z‖ ^ (-criticalS d - 2)) • (u - z)) {u}ᶜ :=
    h1.smul h2
  exact hc.congr (fun z hz => e z hz)

theorem r26t8a_a01_aesm2 (hd : 2 ≤ d) (x y : Euc d) {φ : Euc d → ℝ}
    (hφ : ContinuousOn φ ({x}ᶜ ∩ {y}ᶜ)) : AEStronglyMeasurable φ volume := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hs : MeasurableSet ({x}ᶜ ∩ {y}ᶜ : Set (Euc d)) :=
    ((measurableSet_singleton x).compl).inter (measurableSet_singleton y).compl
  have h1 : AEStronglyMeasurable φ (volume.restrict ({x}ᶜ ∩ {y}ᶜ)) := hφ.aestronglyMeasurable hs
  have h2 : (volume : Measure (Euc d)).restrict ({x}ᶜ ∩ {y}ᶜ) = volume := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have hx : ∀ᵐ u : Euc d ∂volume, u ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
    have hy : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
    filter_upwards [hx, hy] with u h1 h2
    exact ⟨h1, h2⟩
  rwa [h2] at h1

set_option maxHeartbeats 6400000 in
theorem r26t8a_a01_integrable (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {f : Euc d → ℝ} {A : ℝ}
    (hA : 0 ≤ A) {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {x y : Euc d} (hxy : x ≠ y) :
    Integrable (fun z => tripleG (critCoeff d a beta rho) rho Q x y z) (HRS.Whole.withDensityReal rho) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  haveI := s85_isProb hprob
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμ
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a beta ha hbeta rho hrho
  obtain ⟨BF0, hBF00, hBF0⟩ := hFb 0
  have hBF : ∀ u, ‖forceMean rho u‖ ≤ BF0 := fun u => by
    have := hBF0 u
    rw [norm_iteratedFDeriv_zero] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 0 (forceMean rho)) u u)]
  obtain ⟨K, M', hK0, hMM', hEnv⟩ := r26t8a_a01_env d hd a beta M hM
  have hM'0 : 0 ≤ M' := by linarith
  obtain ⟨c0, hc00, hc0⟩ := r26t8a_a01_pole_prod hxy hs0
  have hsymm := hQ.symmetric
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hae : ∀ᵐ z : Euc d ∂μ, z ≠ x ∧ z ≠ y := by
    have hx : ∀ᵐ u : Euc d ∂volume, u ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
    have hy : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
    have := (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (rho x))).ae_le
      (by filter_upwards [hx, hy] with u h1 h2 using (⟨h1, h2⟩ : u ≠ x ∧ u ≠ y))
    exact this
  -- dominating function
  set D : Euc d → ℝ := fun z => K * (1 + BF0) * A * (jbracket x ^ M' * jbracket y ^ M') *
      ((pole x y + c0) * (jbracket z ^ M' * pole x z) + (pole x y + c0) * (jbracket z ^ M' * pole y z)) with hD
  have hDi : Integrable D μ := by
    have h1 := r26t8a_a01_pole_int hd hM'0 ha hbeta hrho x
    have h2 := r26t8a_a01_pole_int hd hM'0 ha hbeta hrho y
    exact (((h1.const_mul (pole x y + c0)).add (h2.const_mul (pole x y + c0)))).const_mul _
  -- measurability
  have hmeasG : AEStronglyMeasurable (fun z => tripleG (critCoeff d a beta rho) rho Q x y z) μ := by
    have hgc := r26t8a_a01_cont_g hs0
    have c1 := r26t8a_a01_gradX_cont_fst hQ2 y
    have c2 := r26t8a_a01_gradX_cont_fst hQ2 x
    have c3 := r26t8a_a01_gradX_cont_snd hQ2 x
    have c4 := r26t8a_a01_gradX_cont_snd hQ2 y
    have hFc : Continuous (forceMean rho) := hFs.continuous
    set S : Set (Euc d) := {x}ᶜ ∩ {y}ᶜ with hS
    have mx : ∀ {φ : Euc d → ℝ}, ContinuousOn φ {x}ᶜ → ContinuousOn φ S := fun h => h.mono Set.inter_subset_left
    have my : ∀ {φ : Euc d → ℝ}, ContinuousOn φ {y}ᶜ → ContinuousOn φ S := fun h => h.mono Set.inter_subset_right
    have mxv : ∀ {φ : Euc d → Euc d}, ContinuousOn φ {x}ᶜ → ContinuousOn φ S := fun h => h.mono Set.inter_subset_left
    have myv : ∀ {φ : Euc d → Euc d}, ContinuousOn φ {y}ᶜ → ContinuousOn φ S := fun h => h.mono Set.inter_subset_right
    have gy2 : ∀ z, pairGradY Q x z = pairGradX Q z x := fun z => r26t8a_a01_gradY_symm hsymm x z
    have gy3 : ∀ z, pairGradY Q y z = pairGradX Q z y := fun z => r26t8a_a01_gradY_symm hsymm y z
    set Rc : Euc d → ℝ := fun z =>
      -inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (pairGradX Q x y - pairGradX Q z y) -
      inner ℝ (rieszKernelGrad d (criticalS d) (y - z)) (pairGradX Q y x - pairGradX Q z x) -
      inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (pairGradX Q x z - pairGradX Q y z) +
      (inner ℝ (forceMean rho x) (pairGradX Q x y) + inner ℝ (forceMean rho y) (pairGradY Q x y) +
        inner ℝ (forceMean rho x) (pairGradX Q x z) + inner ℝ (forceMean rho z) (pairGradX Q z x) +
        inner ℝ (forceMean rho y) (pairGradX Q y z) + inner ℝ (forceMean rho z) (pairGradX Q z y)) -
      pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y with hRc
    have hRcc : ContinuousOn Rc S := by
      simp only [hRc]
      have t1 : ContinuousOn (fun z => inner ℝ (rieszKernelGrad d (criticalS d) (x - z))
          (pairGradX Q x y - pairGradX Q z y)) S :=
        ContinuousOn.inner (mxv (hgc x)) (continuousOn_const.sub (myv c1))
      have t2 : ContinuousOn (fun z => inner ℝ (rieszKernelGrad d (criticalS d) (y - z))
          (pairGradX Q y x - pairGradX Q z x)) S :=
        ContinuousOn.inner (myv (hgc y)) (continuousOn_const.sub (mxv c2))
      have t3 : ContinuousOn (fun z => inner ℝ (rieszKernelGrad d (criticalS d) (x - y))
          (pairGradX Q x z - pairGradX Q y z)) S :=
        ContinuousOn.inner continuousOn_const ((mxv c3).sub (myv c4))
      have t4 : ContinuousOn (fun z => inner ℝ (forceMean rho x) (pairGradX Q x z)) S :=
        ContinuousOn.inner continuousOn_const (mxv c3)
      have t5 : ContinuousOn (fun z => inner ℝ (forceMean rho z) (pairGradX Q z x)) S :=
        ContinuousOn.inner hFc.continuousOn (mxv c2)
      have t6 : ContinuousOn (fun z => inner ℝ (forceMean rho y) (pairGradX Q y z)) S :=
        ContinuousOn.inner continuousOn_const (myv c4)
      have t7 : ContinuousOn (fun z => inner ℝ (forceMean rho z) (pairGradX Q z y)) S :=
        ContinuousOn.inner hFc.continuousOn (myv c1)
      exact ((((t1.neg.sub t2).sub t3).add ((((((continuousOn_const.add continuousOn_const).add t4).add t5).add t6).add t7))).sub continuousOn_const)
    have hRcm : AEStronglyMeasurable Rc volume := r26t8a_a01_aesm2 hd x y hRcc
    have hJx : AEStronglyMeasurable (fun z => pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x z) μ :=
      (hQ.nonlocal.1.2.1 x).aestronglyMeasurable
    have hJy : AEStronglyMeasurable (fun z => pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q y z) μ :=
      (hQ.nonlocal.1.2.1 y).aestronglyMeasurable
    have hRcμ : AEStronglyMeasurable Rc μ :=
      hRcm.mono_ac (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (rho x)))
    have hsum : AEStronglyMeasurable (fun z => (1 / 3 : ℝ) * (Rc z -
        pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x z -
        pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q y z)) μ :=
      (hRcμ.sub hJx |>.sub hJy).const_mul _
    refine hsum.congr (Filter.Eventually.of_forall fun z => ?_)
    have hk := r26t8a_a01_key (a := a) (beta := beta) (rho := rho) hsymm x y z
    rw [gy2 z, gy3 z] at hk
    simp only [hRc]
    linarith
  refine Integrable.mono' hDi hmeasG ?_
  filter_upwards [hae] with z ⟨hzx, hzy⟩
  rw [Real.norm_eq_abs]
  have hb := hEnv rho f A hA Q hQ BF0 hBF00 hBF x y z hxy hzx.symm hzy.symm
  refine hb.trans ?_
  have hpr := hc0 z
  have hpxz := r26t8a_a01_pole_ge_one x z
  have hpyz := r26t8a_a01_pole_ge_one y z
  have hpxy := r26t8a_a01_pole_ge_one x y
  have hW : 0 ≤ K * (1 + BF0) * A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') := by
    have := Real.rpow_nonneg (s83_jb_pos x).le M'
    have := Real.rpow_nonneg (s83_jb_pos y).le M'
    have := Real.rpow_nonneg (s83_jb_pos z).le M'
    positivity
  have hTP : triplePole x y z ≤ (pole x y + c0) * (pole x z + pole y z) := by
    show pole x y * pole x z + pole x y * pole y z + pole x z * pole y z ≤ _
    nlinarith
  calc K * (1 + BF0) * A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') * triplePole x y z
      ≤ K * (1 + BF0) * A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') *
          ((pole x y + c0) * (pole x z + pole y z)) := mul_le_mul_of_nonneg_left hTP hW
    _ = D z := by rw [hD]; ring

end HRS.MS.R26T8A
