import HRS.MS.Fp81S21WeightedMomentsC
import HRS.MS.R2S11Aux10

/-! Moving-particle centered quadratic `MomentRep` and first-moment export. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
open HRS.MS.R2Interp

private theorem fp81s21_quad_density_clip_continuous
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

private theorem fp81s21_quadNegSobNorm_congr
    {d r : ℕ} {Pw : ℝ}
    (T U : (HRS.Euc d → ℝ) → ℝ)
    (hTU : ∀ f, ContDiff ℝ ∞ f → T f = U f) :
    HRS.Whole.r2NegSobNorm r Pw T = HRS.Whole.r2NegSobNorm r Pw U := by
  unfold HRS.Whole.r2NegSobNorm
  apply iSup_congr
  intro ψ
  apply iSup_congr
  intro hψ
  exact congrArg ENNReal.ofReal (congrArg abs
    (hTU _ ((HRS.MS.S85.s85_jbpow_contDiff Pw).mul (ψ.smooth ⊤))))

private theorem fp81s21_isR2Test_smul {d : ℕ} {c : ℝ} {f : HRS.Euc d → ℝ}
    (hf : HRS.Whole.IsR2Test f) : HRS.Whole.IsR2Test (c • f) := by
  refine ⟨hf.1.const_smul c, ?_⟩
  have hs : HasCompactSupport (fun x : HRS.Euc d => f x • (fun _ : HRS.Euc d => c) x) :=
    hf.2.smul_right
  convert hs using 1
  funext x
  simp [smul_eq_mul, mul_comm]

private theorem fp81s21_chartAction_smul
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (c : ℝ) (f : HRS.Euc d → ℝ)
    (hwt : IsR2WeightedTest r Pw f) :
    fp81s21_chartAction E z (c • f) = c * fp81s21_chartAction E z f := by
  change inner ℝ z (E.encode (c • f)) =
    c * inner ℝ z (E.encode f)
  rw [E.smul c f hwt]
  simp only [inner_smul_right, RCLike.conj_ofReal]

private theorem fp81s21_testRep_smul
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (T : (HRS.Euc d → ℝ) → ℝ) (z : r26t6_Coeff)
    (hrep : fp81s21_TestRep E T z) (c : ℝ) (f : HRS.Euc d → ℝ)
    (hf : IsR2Test f) (hwt : IsR2WeightedTest r Pw f) :
    T (c • f) = c * T f := by
  have hcf := fp81s21_isR2Test_smul (c := c) hf
  calc
    T (c • f) = fp81s21_chartAction E z (c • f) := (hrep.1 (c • f) hcf).symm
    _ = c * fp81s21_chartAction E z f := fp81s21_chartAction_smul E z c f hwt
    _ = c * T f := by rw [hrep.1 f hf]


/-- The centered quadratic field has a jointly measurable coefficient representative
whose coefficient second moment is uniform in particles and nonnegative times. -/
theorem fp81s21_particle_quad_momentRep (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8)
              ((p.d : ℝ) + 2),
            ∃ qB : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep E A.P
                (fp81s21_particleQuadField R N A) qB M := by
  obtain ⟨δ0, hδ0, hδ0half, hUniform⟩ :=
    fp81s21_uniform_density_moments p
  have hPw : 0 ≤ (p.d : ℝ) + 2 := by positivity
  have hChartCond : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith
  obtain ⟨Cw, hCw, hCompare⟩ := fp81s21_dualNormE_le_r2NegSobNorm
    (d := p.d) (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2) hChartCond
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hReferenceMoment, hParticle⟩ :=
      hUniform δ hδ hδle R
  obtain ⟨D, hD, hNegMoment⟩ := fp81s21_quad_r2wfm_singleLaw
    p (M := M) (L := L) (C₀ := C₀) (c₀ := c₀) (pinf := pinf) (K := K)
    hc₀ hpinf
  let Mrep : ℝ := Cw ^ 2 * D
  have hMrep : 0 ≤ Mrep := by positivity
  refine ⟨Mrep, hMrep, ?_⟩
  intro N hN A E
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
      (fp81s21_quad_density_clip_continuous p R hδ
        (hδle.trans hδ0half)).measurable
  have hroundClip : ∀ u, HRS.Whole.IsRound2Density p.d p.s M L (rhoClip u) := by
    intro u
    exact hRound2 (clip u) (hclip_nonneg u)
  have hgaussClip : ∀ u x, rhoClip u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) := by
    intro u x
    exact (hGaussian (clip u) (hclip_nonneg u)).2 x
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
  have hactualClip : ∀ v, HRS.Whole.HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (rhoClip v))
      (A.P.map (fun ζ => Yclip (v, ζ))) := by
    intro v
    let t : NNReal := Real.toNNReal (clip v)
    have hraw := (hParticle N hN A (clip v) (hclip_nonneg v)).1
    change HRS.Whole.HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (rhoClip v))
      (A.P.map (A.X t)) at hraw
    have hYlaw : A.P.map (fun ζ => Yclip (v, ζ)) = A.P.map (A.X t) := by
      apply Measure.map_congr
      filter_upwards [hYae] with ζ hζ
      simpa [Yclip, t] using hζ (clip v)
    rw [hYlaw]
    exact hraw
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hN
  obtain ⟨cQuad, hcQuad, z, hzMeas, hzRep, hbound⟩ :=
    fp81s21_quad_config_rep
      (d := p.d) (N := N) (s := p.s) (M := M) (L := L)
      (C₀ := C₀) (c₀ := c₀) (β := p.β) (pint := pinf) (K := K)
      p.hd p.hs0 p.hs hc₀ p.hβ hpinf hrhoJoint hroundClip hgaussClip hN
      A.P Yclip hYclipMeas hactualClip E
  let Mbound : ℝ := Cw ^ 2 * D
  have hMbound : 0 ≤ Mbound := by positivity
  let qB : ℝ → A.Ω → r26t6_Coeff := fun u ζ =>
    z (clip u) (Yclip (u, ζ))
  have hqMeas : Measurable (Function.uncurry qB) := by
    change Measurable (fun q : ℝ × A.Ω => z (clip q.1) (Yclip q))
    exact hzMeas.comp ((hclipMeas.comp measurable_fst).prodMk hYclipMeas)
  refine ⟨qB, hqMeas, ?_⟩
  intro u hu
  have hclipu : clip u = u := by
    rw [hclipEq]
    change max u 0 = u
    exact max_eq_left hu
  let YAt : A.Ω → EucConfig p.d N := fun ζ => Yclip (u, ζ)
  have hYAtMeas : Measurable YAt :=
    hYclipMeas.comp (measurable_const.prodMk measurable_id)
  let Pactual : Measure (EucConfig p.d N) := A.P.map YAt
  have hActual : HRS.Whole.HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (R.ρ u)) Pactual := by
    simpa [rhoClip, hclipu, Pactual, YAt] using hactualClip u
  have hLower := hNegMoment (R.ρ u) (hRound2 u hu)
    (hGaussian u hu) N hN Pactual hActual
  let T : EucConfig p.d N → (Euc p.d → ℝ) → ℝ := fun X f =>
    HRS.Whole.r2CommDistr p.d p.s
      (HRS.Whole.withDensityReal (R.ρ u)) X f -
      ∫ ζ, HRS.Whole.r2CommDistr p.d p.s
        (HRS.Whole.withDensityReal (R.ρ u)) (YAt ζ) f ∂A.P
  have hTRep : ∀ X, fp81s21_TestRep E (T X) (z u X) := by
    intro X
    simpa [T, rhoClip, hclipu] using hzRep u X
  have hTcenter : ∀ X f, ContDiff ℝ ∞ f →
      T X f = HRS.Whole.r2CommDistr p.d p.s
          (HRS.Whole.withDensityReal (R.ρ u)) X f -
        ∫ X', HRS.Whole.r2CommDistr p.d p.s
          (HRS.Whole.withDensityReal (R.ρ u)) X' f ∂Pactual := by
    intro X f hf
    let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ u)
    letI : IsProbabilityMeasure μ :=
      HRS.Whole.Q34.isProbabilityMeasure_nu (hRound2 u hu).prob
    have hgrad : Continuous (fun x : Euc p.d => gradient f x) :=
      HRS.MH.DualityRd.db1_gradient_continuous
        (hf.of_le (by norm_num))
    have hker : Measurable (fun xy : Euc p.d × Euc p.d =>
        HRS.Whole.commutatorKernel p.d p.s
          (fun x => gradient f x) xy.1 xy.2) :=
      HRS.MS.Comm.comm_meas _ hgrad.measurable
    have hpair : Measurable (fun X' : EucConfig p.d N =>
        HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s
            (fun x => gradient f x)) X' μ) :=
      HRS.MS.Wr.wr9_measurable_pairEnergy hker
    have hcomm : Measurable (fun X' : EucConfig p.d N =>
        HRS.Whole.r2CommDistr p.d p.s μ X' f) := by
      simpa [HRS.Whole.r2CommDistr] using hpair.const_mul (N : ℝ)
    have hmap : (∫ X', HRS.Whole.r2CommDistr p.d p.s μ X' f ∂Pactual) =
        ∫ ζ, HRS.Whole.r2CommDistr p.d p.s μ (YAt ζ) f ∂A.P :=
      integral_map hYAtMeas.aemeasurable hcomm.aestronglyMeasurable
    dsimp [T, μ, Pactual]
    rw [← hmap]
  have hNormEq : ∀ X,
      HRS.Whole.r2NegSobNorm (2 * p.d + 8) ((p.d : ℝ) + 2) (T X) =
        HRS.Whole.r2NegSobNorm (2 * p.d + 8) ((p.d : ℝ) + 2)
          (fun f => HRS.Whole.r2CommDistr p.d p.s
              (HRS.Whole.withDensityReal (R.ρ u)) X f -
            ∫ X', HRS.Whole.r2CommDistr p.d p.s
              (HRS.Whole.withDensityReal (R.ρ u)) X' f ∂Pactual) := by
    intro X
    exact fp81s21_quadNegSobNorm_congr (T X) _ (hTcenter X)
  have hLowerT :
      (∫⁻ X, HRS.Whole.r2NegSobNorm (2 * p.d + 8)
        ((p.d : ℝ) + 2) (T X) ^ (2 : ℝ) ∂Pactual) ≤ ENNReal.ofReal D := by
    calc
      _ = ∫⁻ X, HRS.Whole.r2NegSobNorm (2 * p.d + 8)
          ((p.d : ℝ) + 2)
          (fun f => HRS.Whole.r2CommDistr p.d p.s
              (HRS.Whole.withDensityReal (R.ρ u)) X f -
            ∫ X', HRS.Whole.r2CommDistr p.d p.s
              (HRS.Whole.withDensityReal (R.ρ u)) X' f ∂Pactual) ^ (2 : ℝ)
          ∂Pactual := by
            apply lintegral_congr
            intro X
            rw [hNormEq]
      _ ≤ ENNReal.ofReal D := hLower
  have hZU : Measurable (z u) :=
    hzMeas.comp (measurable_const.prodMk measurable_id)
  have hHom : ∀ X c f, IsR2Test f → T X (c • f) = c * T X f := by
    intro X c f hf
    have hwt : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f :=
      (weightedTestSubmodule_iff).1
        (weighted_test_of_compact_smooth hChartCond hf)
    exact fp81s21_testRep_smul E (T X) (z u X) (hTRep X) c f hf hwt
  have hTransfer := fp81s21_rep_secondMoment E Pactual T (z u)
    hZU hTRep Cw D hCw hD
    (fun X => hCompare (T X) (fun c f hf => hHom X c f hf)) hLowerT
  have hqAE : qB u =ᵐ[A.P] (fun ζ => z u (A.X u.toNNReal ζ)) := by
    filter_upwards [hYae] with ζ hζ
    simp [qB, hclipu, hζ u, Yclip, YAt]
  have hqAEMap : qB u =ᵐ[A.P] (fun ζ => z u (YAt ζ)) := by
    filter_upwards with ζ
    simp [qB, YAt, hclipu]
  have hcompMem : MemLp (fun ζ => z u (YAt ζ)) 2 A.P :=
    (memLp_map_measure_iff hTransfer.1.aestronglyMeasurable
      hYAtMeas.aemeasurable).1 hTransfer.1
  have hqMem : MemLp (qB u) 2 A.P :=
    (memLp_congr_ae hqAEMap).2 hcompMem
  have hIntZ : Integrable (fun X => ‖z u X‖ ^ 2) Pactual := by
    have hi := (integrable_norm_rpow_iff hTransfer.1.aestronglyMeasurable
      (by norm_num) (by norm_num)).2 hTransfer.1
    simpa using hi
  have hnormAE : (fun ζ => ‖qB u ζ‖ ^ 2) =ᵐ[A.P]
      (fun ζ => ‖z u (YAt ζ)‖ ^ 2) := by
    filter_upwards [hqAEMap] with ζ hζ
    rw [hζ]
  have hIntegralMap :
      (∫ X, ‖z u X‖ ^ 2 ∂Pactual) =
        ∫ ζ, ‖z u (YAt ζ)‖ ^ 2 ∂A.P :=
    integral_map hYAtMeas.aemeasurable hIntZ.aestronglyMeasurable
  have hMoment : (∫ ζ, ‖qB u ζ‖ ^ 2 ∂A.P) ≤ Mbound := by
    calc
      _ = ∫ ζ, ‖z u (YAt ζ)‖ ^ 2 ∂A.P := integral_congr_ae hnormAE
      _ = ∫ X, ‖z u X‖ ^ 2 ∂Pactual := hIntegralMap.symm
      _ ≤ Cw ^ 2 * D := hTransfer.2
  have hRepAE : ∀ᵐ ζ ∂A.P,
      (∀ f, IsR2Test f →
        fp81s21_chartAction E (qB u ζ) f =
          fp81s21_particleQuadField R N A u ζ f) ∧
      dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fp81s21_particleQuadField R N A u ζ) = ENNReal.ofReal ‖qB u ζ‖ := by
    filter_upwards [hYae] with ζ hζ
    have hqeq : qB u ζ = z u (A.X u.toNNReal ζ) := by
      simp [qB, hclipu, hζ u, Yclip, YAt]
    have hIntEq (f : Euc p.d → ℝ) :
        (∫ ζ', pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s
            (fun x => gradient f x))
          (YAt ζ') (HRS.Whole.withDensityReal (R.ρ u)) ∂A.P) =
        ∫ ζ', pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s
            (fun x => gradient f x))
          (A.X u.toNNReal ζ') (HRS.Whole.withDensityReal (R.ρ u)) ∂A.P := by
      apply integral_congr_ae
      filter_upwards [hYae] with ζ' hζ'
      simp [YAt, Yclip, hclipu, hζ' u]
    have hFieldEq : T (A.X u.toNNReal ζ) =
        fp81s21_particleQuadField R N A u ζ := by
      funext f
      dsimp [T, fp81s21_particleQuadField, HRS.Whole.r2QuadField,
        HRS.Whole.r2CommDistr, HRS.MS.R26T3.r26t3_mu]
      rw [integral_const_mul, hIntEq f]
      ring
    have h : fp81s21_TestRep E (T (A.X u.toNNReal ζ))
        (z u (A.X u.toNNReal ζ)) := by
      simpa [T, rhoClip, hclipu] using hzRep u (A.X u.toNNReal ζ)
    refine ⟨?_, ?_⟩
    · intro f hf
      calc
        fp81s21_chartAction E (qB u ζ) f =
            fp81s21_chartAction E (z u (A.X u.toNNReal ζ)) f := by rw [hqeq]
        _ = T (A.X u.toNNReal ζ) f := h.1 f hf
        _ = fp81s21_particleQuadField R N A u ζ f :=
          congrFun hFieldEq f
    · calc
        dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
            (fp81s21_particleQuadField R N A u ζ) =
          dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
            (T (A.X u.toNNReal ζ)) := by rw [← hFieldEq]
        _ = ENNReal.ofReal ‖z u (A.X u.toNNReal ζ)‖ := h.2.2
        _ = ENNReal.ofReal ‖qB u ζ‖ := by rw [hqeq]
  exact ⟨hqMem, hMoment, hRepAE⟩

/-- First-moment consequences for the moving centered quadratic field. -/
theorem fp81s21_particle_quad_firstMoment (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8)
              ((p.d : ℝ) + 2),
            ∀ u : ℝ, 0 ≤ u →
              AEMeasurable (fun ζ => dualNormE (2 * p.d + 8)
                ((p.d : ℝ) + 2)
                (fp81s21_particleQuadField R N A u ζ)) A.P ∧
              (∫⁻ ζ, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                (fp81s21_particleQuadField R N A u ζ) ∂A.P) ≤
                ENNReal.ofReal (Real.sqrt M) := by
  obtain ⟨δ0, hδ0, hδ0half, hUniform⟩ :=
    fp81s21_particle_quad_momentRep p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M, hM, hMomentRep⟩ := hUniform δ hδ hδle R
  refine ⟨M, hM, ?_⟩
  intro N hN A E u hu
  obtain ⟨qB, hrep⟩ := hMomentRep N hN A E
  exact fp81s21_MomentRep_firstMoment E A.P
    (fp81s21_particleQuadField R N A) qB M hrep u hu

#print axioms HRS.Fp81.S21.fp81s21_particle_quad_momentRep
#print axioms HRS.Fp81.S21.fp81s21_particle_quad_firstMoment

end HRS.Fp81.S21
