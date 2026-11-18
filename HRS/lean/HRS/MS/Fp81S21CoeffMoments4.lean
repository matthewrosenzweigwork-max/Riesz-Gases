import HRS.MS.Fp81S21CoeffMoments2
import HRS.MS.Fp81S21CoeffMoments3
import HRS.MS.Fp81S21WeightedMomentsS2
import HRS.MS.Fp81S21Uniform

/-! Strong-chart coefficient moments for the raw quadratic commutator field. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
open HRS.MS.R2Interp

/-- The uncentered commutator field, before subtraction of its law mean. -/
def fp81s21_particleQuadRawField {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (N : ℕ) (A : Particle R N) (u : ℝ)
    (ζ : A.Ω) (f : Euc p.d → ℝ) : ℝ :=
  r2CommDistr p.d p.s (r26t3_mu R u) (A.X u.toNNReal ζ) f

private theorem fp81s21_coeffMoments_strong_moving_density_clip_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous (fun q : ℝ × Euc p.d =>
      R.ρ ((max q.1 0).toNNReal) q.2) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x :=
    fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  have hjoint := HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass
  have hmap : Continuous (fun q : ℝ × Euc p.d =>
      ((max q.1 0).toNNReal, q.2)) := by
    fun_prop
  exact hjoint.comp hmap

private theorem fp81s21_coeffMoments_strong_isR2Test_smul
    {d : ℕ} {c : ℝ} {f : Euc d → ℝ}
    (hf : IsR2Test f) : IsR2Test (c • f) := by
  refine ⟨hf.1.const_smul c, ?_⟩
  have hs : HasCompactSupport
      (fun x : Euc d => f x • (fun _ : Euc d => c) x) := hf.2.smul_right
  convert hs using 1
  funext x
  simp [smul_eq_mul, mul_comm]

private theorem fp81s21_coeffMoments_chartAction_smul
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (c : ℝ) (f : Euc d → ℝ)
    (hwt : IsR2WeightedTest r Pw f) :
    fp81s21_chartAction E z (c • f) =
      c * fp81s21_chartAction E z f := by
  change inner ℝ z (E.encode (c • f)) = c * inner ℝ z (E.encode f)
  rw [E.smul c f hwt]
  simp only [inner_smul_right, RCLike.conj_ofReal]

private theorem fp81s21_coeffMoments_testRep_smul
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (T : (Euc d → ℝ) → ℝ) (z : r26t6_Coeff)
    (hrep : fp81s21_TestRep E T z) (c : ℝ) (f : Euc d → ℝ)
    (hf : IsR2Test f) (hwt : IsR2WeightedTest r Pw f) :
    T (c • f) = c * T f := by
  have hcf := fp81s21_coeffMoments_strong_isR2Test_smul (c := c) hf
  calc
    T (c • f) = fp81s21_chartAction E z (c • f) := (hrep.1 _ hcf).symm
    _ = c * fp81s21_chartAction E z f :=
      fp81s21_coeffMoments_chartAction_smul E z c f hwt
    _ = c * T f := by rw [hrep.1 f hf]

/-- The raw quadratic field has a strong-chart Riesz representative with a
uniform second coefficient moment and a uniform sixth coefficient moment.
The constants are selected after the trajectory and before `N`, `A`, and `u`.
-/
theorem fp81s21_particleQuadRaw_six_momentRep_strong (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∃ qs : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es A.P
                (fp81s21_particleQuadRawField R N A) qs M2 ∧
              fp81s21_Six A.P qs M6 := by
  obtain ⟨δ0, hδ0, hδ0half, hUniform⟩ :=
    fp81s21_uniform_density_moments p
  have hPw : 0 ≤ (p.d : ℝ) + 4 := by positivity
  have hChartCond : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨Cw, hCw, hCompare⟩ := fp81s21_dualNormE_le_r2NegSobNorm
    (d := p.d) (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) hChartCond
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hReferenceMoment, hParticle⟩ :=
      hUniform δ hδ hδle R
  have hOrderStrong : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 <
      ((2 * p.d + 6 : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  have hQuadOrderStrong : (p.d : ℝ) / 2 + 2 <
      ((2 * p.d + 6 : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  obtain ⟨D2, hD2, hNegMoment2⟩ :=
    fp81s21_quad_raw_r2wfm_singleLaw_tau p (r := 2 * p.d + 6)
      (Pw := (p.d : ℝ) + 4) (M := M) (L := L) (C₀ := C₀)
      (c₀ := c₀) (pinf := pinf) (K := K) hPw hOrderStrong hc₀ hpinf
      2 (by norm_num)
  obtain ⟨D6, hD6, hNegMoment6⟩ :=
    fp81s21_quad_raw_r2wfm_singleLaw_tau p (r := 2 * p.d + 6)
      (Pw := (p.d : ℝ) + 4) (M := M) (L := L) (C₀ := C₀)
      (c₀ := c₀) (pinf := pinf) (K := K) hPw hOrderStrong hc₀ hpinf
      6 (by norm_num)
  let M2rep : ℝ := Cw ^ 2 * D2
  let M6rep : ℝ := Cw ^ 6 * D6
  have hM2rep : 0 ≤ M2rep := by dsimp [M2rep]; positivity
  have hM6rep : 0 ≤ M6rep := by dsimp [M6rep]; positivity
  refine ⟨M2rep, M6rep, hM2rep, hM6rep, ?_⟩
  intro N hN A
  let clip : ℝ → ℝ := fun u => ((max u 0).toNNReal : ℝ)
  have hclipEq : clip = fun u => max u 0 := by
    funext u
    dsimp [clip]
    exact Real.coe_toNNReal _ (le_max_right _ _)
  have hclip_nonneg : ∀ u, 0 ≤ clip u := by
    intro u
    rw [hclipEq]
    exact le_max_right _ _
  let rhoClip : ℝ → Euc p.d → ℝ := fun u x => R.ρ (clip u) x
  have hrhoJoint : Measurable (fun q : ℝ × Euc p.d => rhoClip q.1 q.2) := by
    simpa [rhoClip, clip] using
      (fp81s21_coeffMoments_strong_moving_density_clip_continuous p R hδ
        (hδle.trans hδ0half)).measurable
  have hroundClip : ∀ u, HRS.Whole.IsRound2Density p.d p.s M L
      (rhoClip u) := by
    intro u
    exact hRound2 (clip u) (hclip_nonneg u)
  have hgaussClip : ∀ u x, rhoClip u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) := by
    intro u x
    exact (hGaussian (clip u) (hclip_nonneg u)).2 x
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  obtain ⟨cComm, hcComm, hker⟩ := HRS.MS.R2Interp.s102_comm_poly
    hd1 p.hs0 hPw (2 * p.d + 6) hQuadOrderStrong
  obtain ⟨cEnv, hcEnv, hEnvBound⟩ := HRS.MS.R2Interp.s102_gk_int
    hd1 p.hs0 p.hs M C₀ c₀ hc₀ hPw
  have hXmeas : ∀ t, Measurable (A.X t) :=
    (A.strong (1 : ℝ)).adapted
  have hXcont := (A.strong (1 : ℝ)).cont
  obtain ⟨Y, hYmeas, hYae⟩ := HRS.MS.R2S11.s11_X_joint hXmeas hXcont
  let Yclip : ℝ × A.Ω → EucConfig p.d N := fun q => Y (clip q.1, q.2)
  have hclipMeas : Measurable clip := by
    rw [hclipEq]
    fun_prop
  have hYclipMeas : Measurable Yclip := by
    exact hYmeas.comp ((hclipMeas.comp measurable_fst).prodMk measurable_snd)
  have hρnonneg : ∀ u x, 0 ≤ rhoClip u x := by
    intro u x
    exact (hroundClip u).prob.nonneg x
  let T : ℝ × EucConfig p.d N → (Euc p.d → ℝ) → ℝ := fun q =>
    r2CommDistr p.d p.s (HRS.Whole.withDensityReal (rhoClip q.1)) q.2
  have hZ : ∀ q, HRS.MS.R2Interp.S102Z (2 * p.d + 6)
      ((p.d : ℝ) + 4) (T q) := by
    intro q
    let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal (rhoClip q.1)
    haveI : IsProbabilityMeasure μ :=
      HRS.Whole.Q34.isProbabilityMeasure_nu (hroundClip q.1).prob
    obtain ⟨hgi, hgH, -⟩ := hEnvBound (rhoClip q.1)
      (hroundClip q.1).prob (hroundClip q.1).bdd (hgaussClip q.1)
    let Pzero : Measure PUnit := 0
    have hEi : Integrable (fun _ : PUnit =>
        HRS.MS.R2Interp.s102_Env
          (HRS.MS.R2Interp.s102_gk p.s ((p.d : ℝ) + 4)) q.2 μ) Pzero := by
      simp [Pzero]
    have hraw := HRS.MS.R2Interp.s102_Z_quad
      (s := p.s) (Pw := (p.d : ℝ) + 4) (d := p.d)
      (2 * p.d + 6) hQuadOrderStrong hcComm hker hgi hgH
      (P := Pzero) (Y := fun _ : PUnit => q.2) measurable_const hEi PUnit.unit
    have hEq : T q = fun f => HRS.MS.R2Interp.s102_fld Pzero μ
        (fun _ : PUnit => q.2)
        (HRS.Whole.commutatorKernel p.d p.s (fun x => gradient f x))
        PUnit.unit := by
      funext f
      simp [T, HRS.Whole.r2CommDistr, HRS.MS.R2Interp.s102_fld, Pzero, μ]
    rw [hEq]
    exact hraw.1
  have hPairKernel : ∀ j, Measurable
      (fun q : ℝ × Euc p.d × Euc p.d =>
        HRS.Whole.commutatorKernel p.d p.s
          (fun x => gradient (Es.test j) x) q.2.1 q.2.2) := by
    intro j
    exact (HRS.MS.Comm.comm_meas _
      (HRS.MH.DualityRd.db1_gradient_continuous
        ((Es.test_smooth j).1.of_le (by norm_num))).measurable).comp
          measurable_snd
  have hPair : ∀ j, Measurable
      (fun q : ℝ × EucConfig p.d N =>
        pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s
            (fun x => gradient (Es.test j) x)) q.2
          (HRS.Whole.withDensityReal (rhoClip q.1))) := by
    intro j
    exact fp81s21_moving_pairEnergy_joint_meas
      (d := p.d) (N := N) (ρ := rhoClip)
      (k := fun _ : ℝ => HRS.Whole.commutatorKernel p.d p.s
        (fun x => gradient (Es.test j) x)) hrhoJoint hρnonneg
      (hPairKernel j)
  have hc : ∀ j, Measurable (fun q : ℝ × EucConfig p.d N => T q (Es.test j)) := by
    intro j
    change Measurable (fun q : ℝ × EucConfig p.d N =>
      (N : ℝ) * pairEnergy
        (HRS.Whole.commutatorKernel p.d p.s
          (fun x => gradient (Es.test j) x)) q.2
        (HRS.Whole.withDensityReal (rhoClip q.1)))
    exact measurable_const.mul (hPair j)
  obtain ⟨z, hzMeas, hzRep⟩ := fp81s21_measurable_riesz
    hChartCond Es T hZ hc
  let qRaw : ℝ → A.Ω → r26t6_Coeff := fun u ζ =>
    z (clip u, Yclip (u, ζ))
  have hqMeas : Measurable (Function.uncurry qRaw) := by
    change Measurable (fun q : ℝ × A.Ω => z (clip q.1, Yclip q))
    exact hzMeas.comp ((hclipMeas.comp measurable_fst).prodMk hYclipMeas)
  have hAt (u : ℝ) (hu : 0 ≤ u) :
      (MemLp (qRaw u) 2 A.P ∧
        (∫ ζ, ‖qRaw u ζ‖ ^ 2 ∂A.P) ≤ M2rep ∧
        ∀ᵐ ζ ∂A.P,
          (∀ f, IsR2Test f →
            fp81s21_chartAction Es (qRaw u ζ) f =
              fp81s21_particleQuadRawField R N A u ζ f) ∧
          dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (fp81s21_particleQuadRawField R N A u ζ) = ENNReal.ofReal ‖qRaw u ζ‖) ∧
        fp81s21_Moment6 A.P (qRaw u) M6rep := by
    let t : NNReal := u.toNNReal
    have hclipu : clip u = u := by
      rw [hclipEq]
      change max u 0 = u
      exact max_eq_left hu
    let YAt : A.Ω → EucConfig p.d N := fun ζ => Yclip (u, ζ)
    have hYAtMeas : Measurable YAt :=
      hYclipMeas.comp (measurable_const.prodMk measurable_id)
    have hActual0 := (hParticle N hN A u hu).1
    change HRS.Whole.HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (R.ρ u))
      (A.P.map (A.X t)) at hActual0
    let Pactual : Measure (EucConfig p.d N) := A.P.map YAt
    have hYlaw : A.P.map YAt = A.P.map (A.X t) := by
      apply Measure.map_congr
      filter_upwards [hYae] with ζ hζ
      simpa [YAt, Yclip, hclipu, t] using hζ u
    have hActual : HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal (R.ρ u)) Pactual := by
      simpa [Pactual, hYlaw] using hActual0
    have hNeg2 := hNegMoment2 (R.ρ u) (hRound2 u hu)
      (hGaussian u hu) N hN Pactual hActual
    have hNeg6 := hNegMoment6 (R.ρ u) (hRound2 u hu)
      (hGaussian u hu) N hN Pactual hActual
    let TAt : EucConfig p.d N → (Euc p.d → ℝ) → ℝ := fun X => T (u, X)
    have hTRep : ∀ X, fp81s21_TestRep Es (TAt X) (z (u, X)) := by
      intro X
      simpa [TAt, T, rhoClip, hclipu] using hzRep (u, X)
    have hZU : Measurable (fun X => z (u, X)) :=
      hzMeas.comp (measurable_const.prodMk measurable_id)
    have hL2 : (∫⁻ X, r2NegSobNorm (2 * p.d + 6)
        ((p.d : ℝ) + 4) (TAt X) ^ (2 : ℝ) ∂Pactual) ≤ ENNReal.ofReal D2 := by
      simpa [TAt, T, rhoClip, hclipu] using hNeg2
    have hL6 : (∫⁻ X, r2NegSobNorm (2 * p.d + 6)
        ((p.d : ℝ) + 4) (TAt X) ^ (6 : ℝ) ∂Pactual) ≤ ENNReal.ofReal D6 := by
      simpa [TAt, T, rhoClip, hclipu] using hNeg6
    have hHom : ∀ X c f, IsR2Test f → TAt X (c • f) = c * TAt X f := by
      intro X c f hf
      have hwt : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f :=
        (weightedTestSubmodule_iff).1
          (weighted_test_of_compact_smooth hChartCond hf)
      exact fp81s21_coeffMoments_testRep_smul Es (TAt X) (z (u, X))
        (hTRep X) c f hf hwt
    have hTransfer := fp81s21_rep_secondMoment Es Pactual TAt
      (fun X => z (u, X)) hZU hTRep Cw D2 hCw hD2
      (fun X => hCompare (TAt X) (hHom X)) hL2
    have hqAE : qRaw u =ᵐ[A.P]
        (fun ζ => z (u, YAt ζ)) := by
      filter_upwards with ζ
      simp [qRaw, YAt, hclipu]
    have hcompMem : MemLp (fun ζ => z (u, YAt ζ)) 2 A.P :=
      (memLp_map_measure_iff hTransfer.1.aestronglyMeasurable
        hYAtMeas.aemeasurable).1 hTransfer.1
    have hqMem : MemLp (qRaw u) 2 A.P :=
      (memLp_congr_ae hqAE).2 hcompMem
    have hIntZ2 : Integrable (fun X => ‖z (u, X)‖ ^ 2) Pactual := by
      have hi := (integrable_norm_rpow_iff hTransfer.1.aestronglyMeasurable
        (by norm_num) (by norm_num)).2 hTransfer.1
      simpa using hi
    have hnormAE2 : (fun ζ => ‖qRaw u ζ‖ ^ 2) =ᵐ[A.P]
        (fun ζ => ‖z (u, YAt ζ)‖ ^ 2) := by
      filter_upwards [hqAE] with ζ hζ
      rw [hζ]
    have hIntegralMap2 :
        (∫ X, ‖z (u, X)‖ ^ 2 ∂Pactual) =
          ∫ ζ, ‖z (u, YAt ζ)‖ ^ 2 ∂A.P :=
      integral_map hYAtMeas.aemeasurable hIntZ2.aestronglyMeasurable
    have hMoment2 : (∫ ζ, ‖qRaw u ζ‖ ^ 2 ∂A.P) ≤ M2rep := by
      calc
        _ = ∫ ζ, ‖z (u, YAt ζ)‖ ^ 2 ∂A.P := integral_congr_ae hnormAE2
        _ = ∫ X, ‖z (u, X)‖ ^ 2 ∂Pactual := hIntegralMap2.symm
        _ ≤ Cw ^ 2 * D2 := hTransfer.2
    have hRawEq : ∀ ζ, fp81s21_particleQuadRawField R N A u ζ =
        TAt (A.X t ζ) := by
      intro ζ
      funext f
      simp [TAt, T, fp81s21_particleQuadRawField, rhoClip, t,
        HRS.MS.R26T3.r26t3_mu, hclipu]
    have hRepAE : ∀ᵐ ζ ∂A.P,
        (∀ f, IsR2Test f →
          fp81s21_chartAction Es (qRaw u ζ) f =
            fp81s21_particleQuadRawField R N A u ζ f) ∧
        dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
          (fp81s21_particleQuadRawField R N A u ζ) = ENNReal.ofReal ‖qRaw u ζ‖ := by
      filter_upwards [hYae] with ζ hζ
      have hqeq : qRaw u ζ = z (u, A.X t ζ) := by
        simp [qRaw, YAt, hclipu, hζ u, Yclip, t]
      have hRep := hzRep (u, A.X t ζ)
      have hFieldEq : TAt (A.X t ζ) =
          fp81s21_particleQuadRawField R N A u ζ := by
        funext f
        simp [TAt, T, fp81s21_particleQuadRawField, rhoClip, hclipu, t,
          HRS.Whole.r2CommDistr, HRS.MS.R26T3.r26t3_mu]
      refine ⟨?_, ?_⟩
      · intro f hf
        calc
          fp81s21_chartAction Es (qRaw u ζ) f =
              fp81s21_chartAction Es (z (u, A.X t ζ)) f := by rw [hqeq]
          _ = TAt (A.X t ζ) f := hRep.1 f hf
          _ = fp81s21_particleQuadRawField R N A u ζ f := congrFun hFieldEq f
      · calc
          dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_particleQuadRawField R N A u ζ) =
            dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (TAt (A.X t ζ)) := by rw [← hFieldEq]
          _ = ENNReal.ofReal ‖z (u, A.X t ζ)‖ := hRep.2.2
          _ = ENNReal.ofReal ‖qRaw u ζ‖ := by rw [hqeq]
    have hqMeasU : Measurable (qRaw u) :=
      hqMeas.comp (measurable_const.prodMk measurable_id)
    have hSixConfig := fp81s21_rep_sixthMoment Es Pactual TAt
      (fun X => z (u, X)) hZU hTRep Cw D6 hCw hD6
      (fun X => hCompare (TAt X) (hHom X)) hL6
    have hNormMeas : Measurable (fun X => ‖z (u, X)‖ ^ 6) :=
      (measurable_norm.comp hZU).pow_const 6
    have hIntComp6 : Integrable
        (fun ζ => ‖z (u, YAt ζ)‖ ^ 6) A.P :=
      (integrable_map_measure hNormMeas.aestronglyMeasurable
        hYAtMeas.aemeasurable).1 hSixConfig.2.1
    have hnormAE6 : (fun ζ => ‖qRaw u ζ‖ ^ 6) =ᵐ[A.P]
        (fun ζ => ‖z (u, YAt ζ)‖ ^ 6) := by
      filter_upwards [hqAE] with ζ hζ
      rw [hζ]
    have hIntRaw6 : Integrable (fun ζ => ‖qRaw u ζ‖ ^ 6) A.P :=
      (integrable_congr hnormAE6).2 hIntComp6
    have hIntegralMap6 :
        (∫ X, ‖z (u, X)‖ ^ 6 ∂Pactual) =
          ∫ ζ, ‖z (u, YAt ζ)‖ ^ 6 ∂A.P :=
      integral_map hYAtMeas.aemeasurable hSixConfig.2.1.aestronglyMeasurable
    have hMoment6 : (∫ ζ, ‖qRaw u ζ‖ ^ 6 ∂A.P) ≤ M6rep := by
      calc
        _ = ∫ ζ, ‖z (u, YAt ζ)‖ ^ 6 ∂A.P := integral_congr_ae hnormAE6
        _ = ∫ X, ‖z (u, X)‖ ^ 6 ∂Pactual := hIntegralMap6.symm
        _ ≤ M6rep := hSixConfig.2.2
    have hSixAt : fp81s21_Moment6 A.P (qRaw u) M6rep :=
      ⟨hqMeasU.aemeasurable, hIntRaw6, hMoment6⟩
    exact ⟨⟨hqMem, hMoment2, hRepAE⟩, hSixAt⟩
  refine ⟨qRaw, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hqMeas, ?_⟩
    intro u hu
    exact (hAt u hu).1
  · intro u hu
    exact (hAt u hu).2

#print axioms HRS.Fp81.S21.fp81s21_particleQuadRaw_six_momentRep_strong

end HRS.Fp81.S21

end
