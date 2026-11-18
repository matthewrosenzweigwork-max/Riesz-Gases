import HRS.MS.Fp81S21JointN2
import HRS.MS.GenPathAux32
import HRS.MS.WsPrepAux12

/-!
For X = flucPathW (wholeSpaceIndex p.d) H a (sqrt N) A.X R.ρ,
X(t) = etaB (wholeSpaceIndex p.d) (A.X (a+t).toNNReal ω)
  (r26t3_mu R (a+t)) almost surely, simultaneously for t in [0,H].
Thus the first coordinate of jointP_map is the time-L² class of the
first m chart evaluations of that raw fluctuation, and the second is the
class of ∑ j : Fin m, polyAt (D (θ j) k) (etaB ... ) • coeffBasis j.
Both are projected by timeProject. The quadratic coordinate is raw; the
joint target subtracts (0, its own law's mean), leaving the linear coordinate
uncentered. The etaB definition already contains the factor sqrt N.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The particle fluctuation window agrees simultaneously with the moving
mean-field fluctuation at every time of the window. -/
theorem fp81s21_jointN_particle_window_eval
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H) :
    ∀ᵐ ω ∂A.P, ∀ t : Icc (0 : ℝ) H,
      OscPath.at' (flucPathW (wholeSpaceIndex p.d : ℝ) H a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω) t =
        fp81s21_jointN_rawEtaAt R A (a + t) ω := by
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let ηfield : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    etaB m (A.X t.toNNReal ω) (HRS.Whole.withDensityReal (R.ρ t))
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by positivity]
  have hXc : ∀ᵐ ω ∂A.P, ∀ i, Continuous fun t : ℝ≥0 => A.X t ω i :=
    (A.strong (a + H)).cont
  have hprob : ∀ t ∈ Icc (0 : ℝ) (a + H), HRS.Whole.IsProbDensity (R.ρ t) := by
    intro t ht
    exact (R.resulting.global (a + H)).density t ht
  have hweak : ∀ ψ : Euc p.d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * R.ρ r x) (Icc (0 : ℝ) (a + H)) := by
    intro ψ hψ hbd
    have hβprob : HRS.Whole.IsProbDensity R.ρβ := R.thermal.2.1
    have hβpos : ∀ x, 0 < R.ρβ x := S78.s78_thermal_pos R.thermal.2
    exact (s21p_rho_weak_cont hβprob hβpos R.resulting ψ hψ hbd).mono
      (fun t ht => ht.1)
  have hηcont : ∀ᵐ ω ∂A.P,
      ContinuousOn (fun t : ℝ => ηfield t ω) (Icc 0 (a + H)) := by
    filter_upwards [hXc] with ω hω
    exact HRS.MS.GenPath.s56_xi_cont_time hd1 hm (Real.sqrt (N : ℝ)) hNpos
      R.ρ hprob hweak (fun t => A.X (Real.toNNReal t) ω)
      (fun i => (hω i).comp continuous_real_toNNReal)
  filter_upwards [hηcont] with ω hω
  have hmem : ∀ t : Icc (0 : ℝ) H, a + (t : ℝ) ∈ Icc (0 : ℝ) (a + H) := by
    intro t
    constructor <;> linarith [ha, t.2.1, t.2.2]
  have hc : Continuous fun t : Icc (0 : ℝ) H => ηfield (a + (t : ℝ)) ω :=
    hω.comp_continuous (continuous_const.add continuous_subtype_val) hmem
  have hpath : flucPathW m H a (Real.sqrt (N : ℝ)) A.X R.ρ ω =
      (⟨fun t : Icc (0 : ℝ) H => ηfield (a + (t : ℝ)) ω, hc⟩ : OscPath p.d m H) := by
    change windowPathOf m H a (fun t => ηfield t ω) = _
    unfold windowPathOf
    exact dif_pos hc
  intro t
  rw [hpath]
  rfl

/-- A genuine raw particle polynomial time class is the second coordinate
of the joint map on the particle fluctuation window. -/
theorem fp81s21_jointN_quadratic_coordinate
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Uraw : A.Ω → fp81s21_jointP_U H)
    (hraw : fp81s21_ParticleRawPolynomialTime31 p R m Λ θ D k N A a H Uraw) :
    Uraw =ᵐ[A.P] fun ω =>
      (fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
        (flucPathW (wholeSpaceIndex p.d : ℝ) H a
          (Real.sqrt (N : ℝ)) A.X R.ρ ω)).2 := by
  let D' : Fin m → fp81s21_RankKernel p.d := fun j => D (θ j) k
  obtain ⟨Mr, r, hr, hrsec, hV⟩ := hraw
  filter_upwards [hV.2.2.2, hrsec,
    fp81s21_jointN_particle_window_eval p R hN A a H ha hH] with ω hv hrω heω
  apply Lp.ext
  have hs := fp81s21_smoothPathToL2_coe H hH
    (fp81s21_jointP_quadCurve H m D'
      (flucPathW (wholeSpaceIndex p.d : ℝ) H a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω))
  have ht := fp81s21_timeProject_apply H m
    (fp81s21_smoothPathToL2 H hH
      (fp81s21_jointP_quadCurve H m D'
        (flucPathW (wholeSpaceIndex p.d : ℝ) H a
          (Real.sqrt (N : ℝ)) A.X R.ρ ω)))
  filter_upwards [hv.2, hs, ht, ae_restrict_mem measurableSet_Icc] with t hvt hst htt htmem
  let s : Icc (0 : ℝ) H := ⟨t, htmem⟩
  have hsclamp : fp81s21_smoothClamp H hH t = s :=
    fp81s21_smoothClamp_apply_of_mem H hH s
  have hsum : fp81s21_projectField m
      (∑ j : Fin m, fp81s21_polyAt (D' j) (fp81s21_jointN_rawEtaAt R A (a + t) ω) •
        fp81s21_coeffBasis j) =
      ∑ j : Fin m, fp81s21_polyAt (D' j) (fp81s21_jointN_rawEtaAt R A (a + t) ω) •
        fp81s21_coeffBasis j := by
    simpa using fp81s21_finite_basis_sub_project_supported2 m
      (fun j => fp81s21_polyAt (D' j) (fp81s21_jointN_rawEtaAt R A (a + t) ω))
      (0 : r26t6_Coeff)
  change Uraw ω t = fp81s21_timeProject H m
    (fp81s21_smoothPathToL2 H hH (fp81s21_jointP_quadCurve H m D'
      (flucPathW (wholeSpaceIndex p.d : ℝ) H a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω))) t
  rw [hvt, hrω (a + t) (add_nonneg ha htmem.1), htt, hst, hsclamp]
  have hcurve : fp81s21_jointP_quadCurve H m D'
      (flucPathW (wholeSpaceIndex p.d : ℝ) H a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω) s =
      ∑ j : Fin m, fp81s21_polyAt (D' j) (fp81s21_jointN_rawEtaAt R A (a + t) ω) •
        fp81s21_coeffBasis j := by
    simp only [fp81s21_jointP_quadCurve, ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    change fp81s21_quadPoly (D' j).c (D' j).u
      (flucPathW (wholeSpaceIndex p.d : ℝ) H a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω) s • fp81s21_coeffBasis j = _
    rw [← fp81s21_polyAt_path, heω s]
  rw [hcurve, hsum]

/-- The oscillator evaluation is the empirical fluctuation tested against
any compact smooth function, with the same square-root normalization. -/
theorem fp81s21_jointN_rawEta_eval
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (u : ℝ) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ) (hf : IsR2Test f) (ω : A.Ω) :
    OscDual.eval (fp81s21_jointN_rawEtaAt R A u ω) f =
      fp81s21_particleEmpField R N A u ω f := by
  let μ : Measure (Euc p.d) := r26t3_mu R u
  have hρ : HRS.Whole.IsProbDensity (R.ρ u) :=
    (R.resulting.global u).density u ⟨hu, le_rfl⟩
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ
  haveI : IsProbabilityMeasure (HRS.Whole.empirical (d := p.d)
      (A.X u.toNNReal ω)) := HRS.Whole.empirical_isProbabilityMeasure (by omega) _
  have hm : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by
      dsimp [wholeSpaceIndex]
      omega)
  let fS : SchwartzMap (Euc p.d) ℝ := hf.2.toSchwartzMap hf.1
  have hEval := OscDual.eval_ofMeasureDiff hm
    (HRS.Whole.empirical (d := p.d) (A.X u.toNNReal ω)) μ fS
  have hFun : (fS : Euc p.d → ℝ) = f := by
    funext x
    simp only [fS, HasCompactSupport.toSchwartzMap_toFun]
  dsimp [fp81s21_jointN_rawEtaAt, etaB, flucB]
  rw [OscDual.eval_smul]
  rw [show OscDual.eval
      (OscDual.ofMeasureDiff (wholeSpaceIndex p.d : ℝ)
        (HRS.Whole.empirical (d := p.d) (A.X u.toNNReal ω)) (r26t3_mu R u)) f =
      ∫ x, f x ∂(HRS.Whole.empirical (d := p.d) (A.X u.toNNReal ω)) -
        ∫ x, f x ∂(r26t3_mu R u) by
        simpa [hFun] using hEval]
  rfl

/-- The projected particle linear time class is the first, uncentered
coordinate of the joint polynomial map. -/
theorem fp81s21_jointN_linear_coordinate
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S : fp81s21_Physical31 p R Es E εN εG εB)
    (N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Uη : A.Ω → fp81s21_jointP_U H)
    (hUη : fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη)
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d) :
    (fun ω => fp81s21_timeProject H m (Uη ω)) =ᵐ[A.P]
      (fun ω => (fp81s21_jointP_map H hH E m D
        (flucPathW (wholeSpaceIndex p.d : ℝ) H a
          (Real.sqrt (N : ℝ)) A.X R.ρ ω)).1) := by
  obtain ⟨Vη, VB, hVη, hVB, htail⟩ := (S.particle N hN A).2.2.2.2.2.2 a ha H hH
  filter_upwards [hUη.2.2.2, hVη.2.2.2,
    fp81s21_jointN_particle_window_eval p R hN A a H ha hH] with ω hu hv heω
  apply Lp.ext
  let X := flucPathW (wholeSpaceIndex p.d : ℝ) H a
    (Real.sqrt (N : ℝ)) A.X R.ρ ω
  let C := fp81s21_jointP_linearCurveCLM p H E m X
  have hp1 := fp81s21_timeProject_apply H m (Uη ω)
  have hp2 := fp81s21_timeProject_apply H m (fp81s21_smoothPathToL2 H hH C)
  have hs := fp81s21_smoothPathToL2_coe H hH C
  filter_upwards [hu.2, hv.2, hp1, hp2, hs, ae_restrict_mem measurableSet_Icc]
    with t hut hvt hp1t hp2t hst htmem
  let s : Icc (0 : ℝ) H := ⟨t, htmem⟩
  have hsclamp : fp81s21_smoothClamp H hH t = s :=
    fp81s21_smoothClamp_apply_of_mem H hH s
  have hproj (z : r26t6_Coeff) : fp81s21_projectField m z =
      ∑ j : Fin m, z j • fp81s21_coeffBasis j := by
    apply fp81s21_finite_basis_of_coordinates
    intro j
    simp [fp81s21_projectField_coordinate2]
  change fp81s21_timeProject H m (Uη ω) t =
    fp81s21_timeProject H m (fp81s21_smoothPathToL2 H hH C) t
  rw [hp1t, hp2t, hut, hst, hsclamp, hproj]
  have hcurve : C s = ∑ j : Fin m,
      (fp81s21_particle_embedField p Es E (S.qsηN N hN A (a + t) ω) j) •
        fp81s21_coeffBasis j := by
    dsimp [C, X, fp81s21_jointP_linearCurveCLM]
    simp only [ContinuousLinearMap.sum_apply, ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith
    have htest : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) (E.test j) :=
      (weightedTestSubmodule_iff).1 (weighted_test_of_compact_smooth hP (E.test_smooth j))
    have hj : fp81s21_particle_embedField p Es E (S.qsηN N hN A (a + t) ω) j =
        OscDual.eval (fp81s21_jointN_rawEtaAt R A (a + t) ω) (E.test j) := by
      rw [← hvt.1, ← fp81s21_chartAction_test_coordinate2 E]
      rw [hvt.2 (E.test j) htest]
      exact (fp81s21_jointN_rawEta_eval p R hN A (a + t)
        (add_nonneg ha htmem.1) (E.test j) (E.test_smooth j) ω).symm
    change HRS.Whole.s21eEvalCLM (wholeSpaceIndex p.d : ℝ)
      (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) (E.test_smooth j)).2
      (OscPath.at' (flucPathW (wholeSpaceIndex p.d : ℝ) H a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω) s) • fp81s21_coeffBasis j = _
    rw [HRS.Whole.s21eEvalCLM_apply, heω s, ← hj]
  rw [hcurve]
  simpa using (fp81s21_finite_basis_sub_project_supported2 m
    (fun j => fp81s21_particle_embedField p Es E (S.qsηN N hN A (a + t) ω) j)
    (0 : r26t6_Coeff)).symm

/-- The projected linear time class and centered raw polynomial time class
form the partially centered particle joint map. -/
theorem fp81s21_jointN_centered_coordinates
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S : fp81s21_Physical31 p R Es E εN εG εB)
    (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Uη Uraw : A.Ω → fp81s21_jointP_U H)
    (hUη : fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη)
    (hraw : fp81s21_ParticleRawPolynomialTime31 p R m Λ θ D k N A a H Uraw) :
    (fun ω => (fp81s21_timeProject H m (Uη ω), fp81s21_center A.P Uraw ω)) =ᵐ[A.P]
      (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
          (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω) -
        fp81s21_jointC_partialCenter H (∫ ω',
          fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω') ∂A.P)) := by
  let F : A.Ω → fp81s21_jointP_U H × fp81s21_jointP_U H := fun ω =>
    fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
      (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω)
  have hlin := fp81s21_jointN_linear_coordinate p R Es E εN εG εB S N hN A a H ha hH Uη hUη m
    (fun j => D (θ j) k)
  have hquad := fp81s21_jointN_quadratic_coordinate p R E m Λ θ D k N hN A a H ha hH Uraw hraw
  obtain ⟨Mr, r, hr, hrsec, hUrep⟩ := hraw
  have hF1int : Integrable (fun ω => (F ω).1) A.P := by
    apply ((hUη.2.1.continuousLinearMap_comp (fp81s21_timeProject H m)).integrable (by norm_num)).congr
    exact hlin
  have hF2int : Integrable (fun ω => (F ω).2) A.P :=
    (hUrep.2.1.integrable (by norm_num)).congr hquad
  have hFint : Integrable F A.P := by
    have hi := hF1int.prodMk hF2int
    simpa only [Prod.mk.eta] using hi
  have hmean : (∫ ω, F ω ∂A.P).2 = ∫ ω, (F ω).2 ∂A.P := snd_integral hFint
  have hmean2 : (∫ ω, Uraw ω ∂A.P) = ∫ ω, (F ω).2 ∂A.P := integral_congr_ae hquad
  filter_upwards [hlin, hquad] with ω h1 h2
  apply Prod.ext
  · simpa [fp81s21_jointC_partialCenter] using h1
  · change Uraw ω - (∫ ω, Uraw ω ∂A.P) = (F ω).2 - (∫ ω, F ω ∂A.P).2
    rw [hmean, ← hmean2, h2]

/-- The particle spatial profile holds for every pair of time classes of the
fixed physical coefficient fields. -/
theorem fp81s21_jointN_projection_tail
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S : fp81s21_Physical31 p R Es E εN εG εB)
    (N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Uη UB : A.Ω → fp81s21_jointP_U H)
    (hUη : fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη)
    (hUB : fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H UB)
    (m : ℕ) (hε : 0 ≤ εN m) :
    fp81s21_SqErr A.P (fun ω => (Uη ω, UB ω))
      (fun ω => (fp81s21_timeProject H m (Uη ω), fp81s21_timeProject H m (UB ω)))
      (Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * S.MN) * εN m) := by
  let qη := fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)
  let qB := fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)
  have hqη : Measurable (Function.uncurry qη) := (S.particle N hN A).2.2.2.2.1.1
  have hqB : Measurable (Function.uncurry qB) := (S.particle N hN A).2.2.2.2.2.1.1
  obtain ⟨Vη, VB, hVη, hVB, htail⟩ := (S.particle N hN A).2.2.2.2.2.2 a ha H hH
  have hηrep : fp81s21_TimeL2Rep A.P qη S.MN a H Vη := by
    refine ⟨hVη.1, hVη.2.1, hVη.2.2.1, ?_⟩
    filter_upwards [hVη.2.2.2] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with t ht
    exact ht.1
  have hBrep : fp81s21_TimeL2Rep A.P qB S.MN a H VB := by
    refine ⟨hVB.1, hVB.2.1, hVB.2.2.1, ?_⟩
    filter_upwards [hVB.2.2.2] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with t ht
    exact ht.1
  have heη : Uη =ᵐ[A.P] Vη := fp81s21_TimeL2Rep_eq_ae A.P qη qη S.MN S.MN a H Uη Vη hqη hqη ha
    (fun _ _ => Filter.Eventually.of_forall (fun _ => rfl)) hUη hηrep
  have heB : UB =ᵐ[A.P] VB := fp81s21_TimeL2Rep_eq_ae A.P qB qB S.MN S.MN a H UB VB hqB hqB ha
    (fun _ _ => Filter.Eventually.of_forall (fun _ => rfl)) hUB hBrep
  have htη : fp81s21_SqErr A.P Uη (fun ω => fp81s21_timeProject H m (Uη ω))
      (Real.sqrt (H * S.MN) * εN m) := by
    have he : (fun ω => ‖Uη ω - fp81s21_timeProject H m (Uη ω)‖ ^ 2) =ᵐ[A.P]
        (fun ω => ‖Vη ω - fp81s21_timeProject H m (Vη ω)‖ ^ 2) := by
      filter_upwards [heη] with ω hω
      rw [hω]
    exact ⟨(htail m).1.1.congr he.symm, (integral_congr_ae he).le.trans (htail m).1.2⟩
  have htB : fp81s21_SqErr A.P UB (fun ω => fp81s21_timeProject H m (UB ω))
      (Real.sqrt (H * S.MN) * εN m) := by
    have he : (fun ω => ‖UB ω - fp81s21_timeProject H m (UB ω)‖ ^ 2) =ᵐ[A.P]
        (fun ω => ‖VB ω - fp81s21_timeProject H m (VB ω)‖ ^ 2) := by
      filter_upwards [heB] with ω hω
      rw [hω]
    exact ⟨(htail m).2.1.congr he.symm, (integral_congr_ae he).le.trans (htail m).2.2⟩
  exact fp81s21_jointG_pair_sqerr A.P Uη (fun ω => fp81s21_timeProject H m (Uη ω))
    UB (fun ω => fp81s21_timeProject H m (UB ω)) _ _
    (mul_nonneg (Real.sqrt_nonneg _) hε) (mul_nonneg (Real.sqrt_nonneg _) hε) htη htB

/-- Fixed-rank particle joint error, conditional on a genuine raw polynomial
time class and its diagonal correction estimate. -/
theorem fp81s21_jointN_sqerr_of_raw_time
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S : fp81s21_Physical31 p R Es E εN εG εB)
    (m : ℕ) (hε : 0 ≤ εN m) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Uη UB Uraw Ur : A.Ω → fp81s21_jointP_U H)
    (hUη : fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη)
    (hUB : fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H UB)
    (hraw : fp81s21_ParticleRawPolynomialTime31 p R m Λ θ D k N A a H Uraw)
    (hUr : fp81s21_ParticleRankTime31 p R m Λ θ D k N A a H Ur)
    (τ diagonalError : ℝ) (hτ : 0 ≤ τ) (hdiag0 : 0 ≤ diagonalError)
    (hker : fp81s21_SqErr A.P Ur (fun ω => fp81s21_timeProject H m (UB ω))
      (Real.sqrt (H * (m : ℝ)) * τ))
    (hdiag : fp81s21_SqErr A.P (fp81s21_center A.P Uraw) Ur diagonalError) :
    fp81s21_SqErr A.P (fun ω => (Uη ω, UB ω))
      (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
          (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω) -
        fp81s21_jointC_partialCenter H (∫ ω',
          fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω') ∂A.P))
      (Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * S.MN) * εN m +
        Real.sqrt (H * (m : ℝ)) * τ + diagonalError) := by
  have htarget := fp81s21_jointN_centered_coordinates p R Es E εN εG εB S m Λ θ D k N hN A
    a H ha hH Uη Uraw hUη hraw
  have hproj := fp81s21_jointN_projection_tail p R Es E εN εG εB S N hN A a H ha hH Uη UB hUη hUB m hε
  have hpair := fp81s21_jointG_kernel_pair_sqerr A.P
    (fun ω => fp81s21_timeProject H m (Uη ω)) Ur
    (fun ω => fp81s21_timeProject H m (UB ω)) _
    (mul_nonneg (Real.sqrt_nonneg _) hτ) hker
  obtain ⟨Mr, r, hr, hrsec, hrawrep⟩ := hraw
  obtain ⟨Mq, q, hq, hqsec, hUrrep⟩ := hUr
  have hηm := hUη.2.1.aestronglyMeasurable
  have hBm := hUB.2.1.aestronglyMeasurable
  have hηp := (fp81s21_timeProject H m).continuous.comp_aestronglyMeasurable hηm
  have hBp := (fp81s21_timeProject H m).continuous.comp_aestronglyMeasurable hBm
  have hcenter : AEStronglyMeasurable (fp81s21_center A.P Uraw) A.P :=
    hrawrep.2.1.aestronglyMeasurable.sub aestronglyMeasurable_const
  have htotal := fp81s21_jointN_pair_sqerr_compose A.P Uη UB
    (fun ω => fp81s21_timeProject H m (Uη ω))
    (fun ω => fp81s21_timeProject H m (UB ω)) Uraw Ur _ _ _
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε) (mul_nonneg (Real.sqrt_nonneg _) hε))
    (mul_nonneg (Real.sqrt_nonneg _) hτ) hdiag0 hηm hBm hηp hBp
    hUrrep.2.1.aestronglyMeasurable hcenter hproj hpair hdiag
  have he : (fun ω => ‖(Uη ω, UB ω) -
      (fp81s21_timeProject H m (Uη ω), fp81s21_center A.P Uraw ω)‖ ^ 2) =ᵐ[A.P]
      (fun ω => ‖(Uη ω, UB ω) -
        (fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω) -
          fp81s21_jointC_partialCenter H (∫ ω',
            fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
              (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω') ∂A.P))‖ ^ 2) := by
    filter_upwards [htarget] with ω hω
    rw [hω]
  exact ⟨htotal.1.congr he, (integral_congr_ae he).symm.le.trans htotal.2⟩

#print axioms fp81s21_jointN_sqerr_of_raw_time
#print axioms fp81s21_jointN_projection_tail
#print axioms fp81s21_jointN_centered_coordinates
#print axioms fp81s21_jointN_linear_coordinate
#print axioms fp81s21_jointN_rawEta_eval
#print axioms fp81s21_jointN_quadratic_coordinate
#print axioms fp81s21_jointN_particle_window_eval
end HRS.Fp81.S21
end
