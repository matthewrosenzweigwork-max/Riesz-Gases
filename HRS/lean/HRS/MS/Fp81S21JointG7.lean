import HRS.MS.Fp81S21JointG6

/-! Identification of the centered quadratic coordinate of the joint map. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The selected Wick rank time class is the Gaussian-law-centered quadratic
coordinate of the joint polynomial map. -/
theorem fp81s21_jointG_quadratic_coordinate
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (m : ℕ) (Λ : ℝ)
    (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k : ℕ) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (U : G.Ω → fp81s21_jointP_U H)
    (hU : fp81s21_GaussianRankTime31 p R Es E ε S m Λ θ D k G a H U) :
    U =ᵐ[G.P] fp81s21_center G.P
      (fun ω => (fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω)).2) := by
  let D' : Fin m → fp81s21_RankKernel p.d := fun j => D (θ j) k
  obtain ⟨Mq, q, hq, hqcoord, hU⟩ := hU
  obtain ⟨r, hr, hrsec, Mr, V, hV, hc⟩ :=
    fp81s21_GaussianRankTime31_physical p R Es E ε S G m D' q Mq a H U
      hq ha hH hqcoord hU
  have hp : ∀ᵐ ω ∂G.P, ∀ j : Fin m, ∀ t : Set.Icc (0 : ℝ) H,
      fp81s21_polyAt (D' j) (G.Z (a + t) ω) =
        fp81s21_quadPoly (D' j).c (D' j).u
          (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) t :=
    ae_all_iff.mpr (fun j => fp81s21_polyAt_gaussian_window p R G a H ha hH.le (D' j))
  let F : G.Ω → fp81s21_jointP_U H := fun ω =>
    (fp81s21_jointP_map H hH E m D'
      (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω)).2
  have heq : V =ᵐ[G.P] F := by
    filter_upwards [hV.2.2.2, hrsec, hp] with ω hv hrω hpω
    apply Lp.ext
    have hs := fp81s21_smoothPathToL2_coe H hH
      (fp81s21_jointP_quadCurve H m D'
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω))
    have ht := fp81s21_timeProject_apply H m
      (fp81s21_smoothPathToL2 H hH
        (fp81s21_jointP_quadCurve H m D'
          (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω)))
    filter_upwards [hv.2, hs, ht, ae_restrict_mem measurableSet_Icc] with t hvt hst htt htmem
    let s : Set.Icc (0 : ℝ) H := ⟨t, htmem⟩
    have hsclamp : fp81s21_smoothClamp H hH t = s := by
      exact fp81s21_smoothClamp_apply_of_mem H hH s
    have hsum : fp81s21_projectField m
        (∑ j : Fin m, fp81s21_polyAt (D' j) (G.Z (a + t) ω) •
          fp81s21_coeffBasis j) =
        ∑ j : Fin m, fp81s21_polyAt (D' j) (G.Z (a + t) ω) •
          fp81s21_coeffBasis j := by
      simpa using fp81s21_finite_basis_sub_project_supported2 m
        (fun j => fp81s21_polyAt (D' j) (G.Z (a + t) ω)) (0 : r26t6_Coeff)
    change V ω t = fp81s21_timeProject H m
      (fp81s21_smoothPathToL2 H hH (fp81s21_jointP_quadCurve H m D'
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω))) t
    rw [hvt, hrω (a + t) (add_nonneg ha htmem.1), htt, hst, hsclamp]
    have hcurve : fp81s21_jointP_quadCurve H m D'
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) s =
        ∑ j : Fin m, fp81s21_polyAt (D' j) (G.Z (a + t) ω) •
          fp81s21_coeffBasis j := by
      simp only [fp81s21_jointP_quadCurve, ContinuousMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j hj
      change fp81s21_quadPoly (D' j).c (D' j).u
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) s • fp81s21_coeffBasis j = _
      rw [← hpω j s]
    rw [hcurve, hsum]
  have hmean := integral_congr_ae heq
  filter_upwards [hc, heq] with ω hcω heω
  simpa only [fp81s21_center, heω, hmean] using hcω

/-- The projected canonical linear time class is the raw linear coordinate
of the joint map on the Gaussian window. -/
theorem fp81s21_jointG_linear_coordinate
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εG εB : ℕ → ℝ) (S : fp81s21_GaussianPhysical31 p R Es E εG εB)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (V : G.Ω → fp81s21_jointP_U H)
    (hV : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Es E (S.qsηG G)) S.MηG a H V)
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d) :
    (fun ω => fp81s21_timeProject H m (V ω)) =ᵐ[G.P]
      (fun ω => (fp81s21_jointP_map H hH E m D
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω)).1) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  have hc := fp81s21_jointG_linear_coordinates p R Es E εG εB S G a H ha hH
  have hswap := (Measure.measurePreserving_swap (μ := G.P) (ν := dt)).quasiMeasurePreserving.ae hc
  have hcoord := Measure.ae_ae_of_ae_prod hswap
  obtain ⟨_, heval⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas
    p.d G.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ H a (a + H)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G.Z (G.evolution (a + H)) hH.le ha le_rfl
  filter_upwards [hV.2.2.2, hcoord, heval] with ω hv hcω heω
  apply Lp.ext
  let X := processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω
  let C := fp81s21_jointP_linearCurveCLM p H E m X
  have hp1 := fp81s21_timeProject_apply H m (V ω)
  have hp2 := fp81s21_timeProject_apply H m (fp81s21_smoothPathToL2 H hH C)
  have hs := fp81s21_smoothPathToL2_coe H hH C
  filter_upwards [hv.2, hcω, hp1, hp2, hs, ae_restrict_mem measurableSet_Icc] with t hvt hct hp1t hp2t hst htmem
  let s : Set.Icc (0 : ℝ) H := ⟨t, htmem⟩
  have hsclamp : fp81s21_smoothClamp H hH t = s :=
    fp81s21_smoothClamp_apply_of_mem H hH s
  have hproj (z : r26t6_Coeff) : fp81s21_projectField m z =
      ∑ j : Fin m, z j • fp81s21_coeffBasis j := by
    apply fp81s21_finite_basis_of_coordinates
    intro j
    simp [fp81s21_projectField_coordinate2]
  change fp81s21_timeProject H m (V ω) t =
    fp81s21_timeProject H m (fp81s21_smoothPathToL2 H hH C) t
  rw [hp1t, hp2t, hvt, hst, hsclamp, hproj]
  have hcurve : C s = ∑ j : Fin m,
      (fp81s21_gaussian_embedFamily p Es E (S.qsηG G) (a + t) ω j) •
        fp81s21_coeffBasis j := by
    dsimp [C, X, fp81s21_jointP_linearCurveCLM]
    simp only [ContinuousLinearMap.sum_apply, ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hj : fp81s21_gaussian_embedFamily p Es E (S.qsηG G) (a + t) ω j =
        OscDual.eval (G.Z (a + t) ω) (E.test j) := hct j
    rw [← heω s] at hj
    change HRS.Whole.s21eEvalCLM (wholeSpaceIndex p.d : ℝ)
      (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) (E.test_smooth j)).2
      (OscPath.at' (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) s) •
        fp81s21_coeffBasis j = _
    rw [HRS.Whole.s21eEvalCLM_apply, ← hj]
  rw [hcurve]
  simpa using (fp81s21_finite_basis_sub_project_supported2 m
    (fun j => fp81s21_gaussian_embedFamily p Es E (S.qsηG G) (a + t) ω j)
    (0 : r26t6_Coeff)).symm

/-- Mean-square errors compose with the sum of their nonnegative radii. -/
theorem fp81s21_jointG_sqerr_trans
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    (P : Measure Ω) (f g h : Ω → V) (ε η : ℝ)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hh : AEStronglyMeasurable h P) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hfg : fp81s21_SqErr P f g ε) (hgh : fp81s21_SqErr P g h η) :
    fp81s21_SqErr P f h (ε + η) := by
  let u : Ω → ℝ := fun ω => ‖f ω - g ω‖
  let v : Ω → ℝ := fun ω => ‖g ω - h ω‖
  let w : Ω → ℝ := fun ω => ‖f ω - h ω‖
  have hu : AEStronglyMeasurable u P := (hf.sub hg).norm
  have hv : AEStronglyMeasurable v P := (hg.sub hh).norm
  have hw : AEStronglyMeasurable w P := (hf.sub hh).norm
  have huL : MemLp u 2 P := (memLp_two_iff_integrable_sq_norm hu).2 (by
    simpa [u, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfg.1)
  have hvL : MemLp v 2 P := (memLp_two_iff_integrable_sq_norm hv).2 (by
    simpa [v, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hgh.1)
  have huB : eLpNorm u 2 P ≤ ENNReal.ofReal ε :=
    HRS.MS.R2Chaos.s94_eLpNorm_le_of_sq huL hε hfg.2
  have hvB : eLpNorm v 2 P ≤ ENNReal.ofReal η :=
    HRS.MS.R2Chaos.s94_eLpNorm_le_of_sq hvL hη hgh.2
  have hwB : eLpNorm w 2 P ≤ ENNReal.ofReal (ε + η) := by
    calc
      eLpNorm w 2 P ≤ eLpNorm (u + v) 2 P := by
        apply eLpNorm_mono_ae_real hw
        filter_upwards [] with ω
        simp only [Pi.add_apply, u, v, w, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        calc
          ‖f ω - h ω‖ = ‖(f ω - g ω) + (g ω - h ω)‖ := by congr 1; abel
          _ ≤ ‖f ω - g ω‖ + ‖g ω - h ω‖ := norm_add_le _ _
      _ ≤ eLpNorm u 2 P + eLpNorm v 2 P := eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal η := add_le_add huB hvB
      _ = ENNReal.ofReal (ε + η) := (ENNReal.ofReal_add hε hη).symm
  have hwL : MemLp w 2 P := hwB.trans_lt ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · simpa [w] using hwL.integrable_sq
  · exact HRS.MS.R2Chaos.s94_integral_sq_le_of_eLpNorm hw (add_nonneg hε hη) hwB

/-- Projection onto the quadratic coordinate for law-specific centering. -/
def fp81s21_jointG_partialCenter (H : ℝ) :
    (fp81s21_jointP_U H × fp81s21_jointP_U H) →L[ℝ]
      (fp81s21_jointP_U H × fp81s21_jointP_U H) :=
  (0 : (fp81s21_jointP_U H × fp81s21_jointP_U H) →L[ℝ] fp81s21_jointP_U H).prod
    (ContinuousLinearMap.snd ℝ (fp81s21_jointP_U H) (fp81s21_jointP_U H))

/-- The fixed Gaussian physical pair is approximated by the partially centered
joint map, with separate spatial and rank-kernel errors. -/
theorem fp81s21_jointG_sqerr_physical
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εG εB : ℕ → ℝ) (S : fp81s21_GaussianPhysical31 p R Es E εG εB)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Vη VB : G.Ω → fp81s21_jointP_U H)
    (hVη : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Es E (S.qsηG G)) S.MηG a H Vη)
    (hVB : fp81s21_TimeL2Rep G.P (S.quadratic.qe G)
      (S.quadratic.Kstar ^ 4 * S.quadratic.B / 2) a H VB)
    (m : ℕ) (hεG : 0 ≤ εG m) (hεB : 0 ≤ εB m)
    (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) (U : G.Ω → fp81s21_jointP_U H)
    (hU : fp81s21_GaussianRankTime31 p R Es E εB S.quadratic m Λ θ D k G a H U)
    (hker : fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (VB ω))
      (Real.sqrt (H * (m : ℝ)) * τ)) :
    fp81s21_SqErr G.P (fun ω => (Vη ω, VB ω))
      (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
          (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) -
        fp81s21_jointG_partialCenter H (∫ ω',
          fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω') ∂G.P))
      (Real.sqrt (H * S.MηG) * εG m +
        Real.sqrt (H * (S.quadratic.Kstar ^ 4 * S.quadratic.B / 2)) * εB m +
        Real.sqrt (H * (m : ℝ)) * τ + 0) := by
  let F : G.Ω → fp81s21_jointP_U H × fp81s21_jointP_U H := fun ω =>
    fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
      (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω)
  have hlin := fp81s21_jointG_linear_coordinate p R Es E εG εB S G a H ha hH Vη hVη m
    (fun j => D (θ j) k)
  have hquad := fp81s21_jointG_quadratic_coordinate p R Es E εB S.quadratic G m Λ θ D k a H ha hH U hU
  obtain ⟨Mq, q, hq, hqcoord, hUrep⟩ := hU
  have hUint : Integrable U G.P := hUrep.2.1.integrable (by norm_num)
  have hF1int : Integrable (fun ω => (F ω).1) G.P := by
    apply ((hVη.2.1.continuousLinearMap_comp (fp81s21_timeProject H m)).integrable (by norm_num)).congr
    exact hlin
  have hF2eq : (fun ω => U ω + ∫ ω', (F ω').2 ∂G.P) =ᵐ[G.P] (fun ω => (F ω).2) := by
    filter_upwards [hquad] with ω hω
    change U ω = (F ω).2 - ∫ ω', (F ω').2 ∂G.P at hω
    rw [hω, sub_add_cancel]
  have hF2int : Integrable (fun ω => (F ω).2) G.P :=
    (hUint.add (integrable_const _)).congr hF2eq
  have hFint : Integrable F G.P := by
    have hi := hF1int.prodMk hF2int
    simpa only [Prod.mk.eta] using hi
  have hmean : (∫ ω, F ω ∂G.P).2 = ∫ ω, (F ω).2 ∂G.P := snd_integral hFint
  have htarget : (fun ω => (fp81s21_timeProject H m (Vη ω), U ω)) =ᵐ[G.P]
      (fun ω => F ω - fp81s21_jointG_partialCenter H (∫ ω', F ω' ∂G.P)) := by
    filter_upwards [hlin, hquad] with ω h1 h2
    apply Prod.ext
    · simpa [fp81s21_jointG_partialCenter] using h1
    · simpa [fp81s21_jointG_partialCenter, fp81s21_center, hmean] using h2
  have hproj := fp81s21_jointG_projection_tail p R Es E εG εB S G a H ha hH Vη VB hVη hVB m hεG hεB
  have hpair := fp81s21_jointG_kernel_pair_sqerr G.P (fun ω => fp81s21_timeProject H m (Vη ω))
    U (fun ω => fp81s21_timeProject H m (VB ω)) _ (mul_nonneg (Real.sqrt_nonneg _) hτ) hker
  have hηm := hVη.2.1.aestronglyMeasurable
  have hBm := hVB.2.1.aestronglyMeasurable
  have hUm := hUrep.2.1.aestronglyMeasurable
  have hηp := (fp81s21_timeProject H m).continuous.comp_aestronglyMeasurable hηm
  have hBp := (fp81s21_timeProject H m).continuous.comp_aestronglyMeasurable hBm
  have htotal := fp81s21_jointG_sqerr_trans G.P
    (fun ω => (Vη ω, VB ω))
    (fun ω => (fp81s21_timeProject H m (Vη ω), fp81s21_timeProject H m (VB ω)))
    (fun ω => (fp81s21_timeProject H m (Vη ω), U ω)) _ _
    (hηm.prodMk hBm) (hηp.prodMk hBp) (hηp.prodMk hUm)
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεG) (mul_nonneg (Real.sqrt_nonneg _) hεB))
    (mul_nonneg (Real.sqrt_nonneg _) hτ) hproj hpair
  have he : (fun ω => ‖(Vη ω, VB ω) - (fp81s21_timeProject H m (Vη ω), U ω)‖ ^ 2) =ᵐ[G.P]
      (fun ω => ‖(Vη ω, VB ω) - (F ω - fp81s21_jointG_partialCenter H (∫ ω', F ω' ∂G.P))‖ ^ 2) := by
    filter_upwards [htarget] with ω hω
    rw [hω]
  exact ⟨htotal.1.congr he, by simpa using (integral_congr_ae he).symm.le.trans htotal.2⟩

/-- One shared rank family has both the particle rank approximation and the
fully identified Gaussian joint approximation, uniformly over all genuine
physical time representatives. -/
theorem fp81s21_jointG_physical31_both_time (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∀ εN εG εB : ℕ → ℝ,
    (∀ m, 0 ≤ εG m) → (∀ m, 0 ≤ εB m) →
    ∀ S : fp81s21_Physical31 p R Es E εN εG εB,
    ∀ m : ℕ, ∃ Λ : ℝ, ∃ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    0 ≤ Λ ∧ (∀ j, (θ j).1 = gradient (E.test j)) ∧
    ∃ τN τG : ℕ → ℝ, (∀ k, 0 ≤ τN k) ∧ (∀ k, 0 ≤ τG k) ∧
    Tendsto τN atTop (𝓝 0) ∧ Tendsto τG atTop (𝓝 0) ∧
    (∀ H : ℝ, 0 < H → ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
      ∀ a : ℝ, 0 ≤ a →
      ∀ V : A.Ω → fp81s21_jointP_U H,
      fp81s21_TimeL2Rep A.P
        (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H V →
      ∀ k : ℕ, ∃ U, fp81s21_ParticleRankTime31 p R m Λ θ D k N A a H U ∧
        fp81s21_SqErr A.P U (fun ω => fp81s21_timeProject H m (V ω))
          (Real.sqrt (H * (m : ℝ)) * τN k)) ∧
    (∀ H : ℝ, ∀ hH : 0 < H, ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
      ∀ Vη VB : G.Ω → fp81s21_jointP_U H,
      fp81s21_TimeL2Rep G.P
        (fp81s21_gaussian_embedFamily p Es E (S.gaussian.qsηG G)) S.gaussian.MηG a H Vη →
      fp81s21_TimeL2Rep G.P (S.gaussian.quadratic.qe G)
        (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2) a H VB →
      ∀ k : ℕ,
        fp81s21_SqErr G.P (fun ω => (Vη ω, VB ω))
          (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
              (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) -
            fp81s21_jointG_partialCenter H (∫ ω',
              fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
                (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω') ∂G.P))
          (Real.sqrt (H * S.gaussian.MηG) * εG m +
            Real.sqrt (H * (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)) * εB m +
            Real.sqrt (H * (m : ℝ)) * τG k + 0)) := by
  obtain ⟨δ0, hδ0, hhalf, hboth⟩ := fp81s21_physical31_both_time p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R Es E εN εG εB hεG hεB S m
  obtain ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, hp, hg⟩ :=
    hboth δ hδ hδle R Es E εN εG εB S m
  refine ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, hp, ?_⟩
  intro H hH G a ha Vη VB hVη hVB k
  obtain ⟨U, hU, hker⟩ := hg H hH G a ha VB hVB k
  exact fp81s21_jointG_sqerr_physical p R Es E εG εB S.gaussian G a H ha hH Vη VB
    hVη hVB m (hεG m) (hεB m) Λ θ D k (τG k) (hτG k) U hU hker

#print axioms fp81s21_jointG_physical31_both_time
#print axioms fp81s21_jointG_partialCenter
#print axioms fp81s21_jointG_sqerr_physical
#print axioms fp81s21_jointG_sqerr_trans
#print axioms fp81s21_jointG_linear_coordinate
#print axioms fp81s21_jointG_quadratic_coordinate
end HRS.Fp81.S21
end
