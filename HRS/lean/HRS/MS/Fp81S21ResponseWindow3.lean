import HRS.MS.Fp81S21ResponseWindow2
import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.R2InterpAux11
import HRS.MS.S21H2_S02
import HRS.Whole.SteinAux5
import HRS.MS.ThCorrSmAux2
import HRS.MS.S111X2Aux4
import HRS.MS.WsInitGAux4
import HRS.MS.R2WinOrbAux10

/-!
# S2.1(iii): linearity of the actual response representative

The response inverse is linear only as an L² equivalence class.  This file
uses the actual preparation's response form and the positive density of the
resulting time-zero reference to promote the resulting response identity to
the continuous representative used by the response window.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

variable {p : Parameters} {δ : ℝ}

/-- The pointwise continuous representative of the actual response is linear
on the smooth test class.  The equality is proved for every spatial point;
the intermediate response-inverse equality is only almost everywhere. -/
theorem fp81s21_response_linear
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ)
    (f g : Euc p.d → ℝ)
    (hf : MemCb (r26t3_J p.d) f) (hg : MemCb (r26t3_J p.d) g)
    (c : ℝ) (x : Euc p.d) :
    r26t3_a R (f + c • g) x = r26t3_a R f x + c * r26t3_a R g x := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c₀, S, hc₀, hTc⟩ := href 0
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hfLp : MemLp f 2 (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.MS.Tc5.tc5_memLp_of_cb hf
  have hgLp : MemLp g 2 (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.MS.Tc5.tc5_memLp_of_cb hg
  have hcg : MemCb (r26t3_J p.d) (c • g) :=
    (HRS.MS.Tc5.tc5_cb_smul c hg).1
  have hsum : MemCb (r26t3_J p.d) (f + c • g) :=
    (HRS.MS.Tc5.tc5_cb_add hf hcg).1
  have hsumLp : MemLp (f + c • g) 2 (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.MS.Tc5.tc5_memLp_of_cb hsum
  obtain ⟨η, hform⟩ := HRS.MS.R26T3.s21f_responseForm_init hδ hδh R
  have hinv := hform.linear f g hfLp hgLp c
  have hdiff : (fun y => HRS.Whole.responseInverse
      (HRS.Whole.rieszKernel p.d p.s) μ p.γ (f + c • g) y -
        HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f y) =ᵐ[μ]
      (fun y => c * HRS.Whole.responseInverse
        (HRS.Whole.rieszKernel p.d p.s) μ p.γ g y) := by
    filter_upwards [hinv] with y hy
    have hy' : HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ
          (f + c • g) y =
        HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f y +
          c * HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ g y := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hy
    change HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ
        (f + c • g) y -
          HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f y = _
    rw [hy']
    ring
  have hrespSum := hform.solution (f + c • g) hsumLp
  have hrespF := hform.solution f hfLp
  have hKsub := HRS.MS.Tc5.tc5_kop_sub_ae p.hs0 hsd M₀ c₀ S hc₀ 0 hTc
    hrespSum.1 hrespF.1
  have hKcong := HRS.MS.S98.s98_kop_congr_ae
    (ν := μ) (g := HRS.Whole.rieszKernel p.d p.s) hdiff
  have hKlin : HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
        (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ (f + c • g)) =ᵐ[μ]
      (fun y => HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
          (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f) y +
        c * HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
          (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ g) y) := by
    filter_upwards [hKsub, Filter.Eventually.of_forall fun y => congrFun hKcong y]
      with y hsub hcong
    have hsmul := HRS.MS.S98.s98_kop_smul (HRS.Whole.rieszKernel p.d p.s) μ c
      (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ g) y
    have hsub' := hsub
    change HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
        (fun z => HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ
          (f + c • g) z -
          HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f z) y = _ at hsub'
    change HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
        (fun z => HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ
          (f + c • g) z -
          HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f z) y =
      HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
        (fun z => c * HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ g z) y at hcong
    rw [hsub', hsmul] at hcong
    change HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
        (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ (f + c • g)) y -
        HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
          (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f) y =
      c * HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
        (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ g) y at hcong
    linarith
  have hproj := HRS.MS.S111X2.s111x2_projMean_lin hfLp hgLp c
  have hlinAE : r26t3_a R (f + c • g) =ᵐ[μ]
      (fun y => r26t3_a R f y + c * r26t3_a R g y) := by
    filter_upwards [hKlin] with y hKy
    change HRS.Whole.projMean μ (f + c • g) y - p.γ *
        HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
          (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ (f + c • g)) y =
      (HRS.Whole.projMean μ f y - p.γ *
        HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
          (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ f) y) +
      c * (HRS.Whole.projMean μ g y - p.γ *
        HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
          (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ g) y)
    have hproj' : HRS.Whole.projMean μ (f + c • g) y =
        HRS.Whole.projMean μ f y + c * HRS.Whole.projMean μ g y := by
      have h := hproj y
      change HRS.Whole.projMean μ (f + c • g) y =
        HRS.Whole.projMean μ f y + c * HRS.Whole.projMean μ g y at h
      exact h
    rw [hproj', hKy]
    ring
  obtain ⟨C, hC0, hsmooth⟩ := HRS.MS.R26T3.r26t3_response_smooth hδ hδh R hγ
  have hcontSum : Continuous (r26t3_a R (f + c • g)) :=
    (hsmooth (f + c • g) hsum).1.1.continuous
  have hcontF : Continuous (r26t3_a R f) := (hsmooth f hf).1.1.continuous
  have hcontG : Continuous (r26t3_a R g) := (hsmooth g hg).1.1.continuous
  have hcontR : Continuous (fun y => r26t3_a R f y + c * r26t3_a R g y) :=
    hcontF.add (continuous_const.mul hcontG)
  obtain ⟨-, -, hdensity, -⟩ := HRS.MS.R26T3.r26t3_reference_data p δ hδ hδh R
  have hρ := hdensity 0 le_rfl
  have hρmeas : Measurable (fun y : Euc p.d => ENNReal.ofReal (R.ρ 0 y)) :=
    ENNReal.measurable_ofReal.comp hρ.1.measurable
  have hlinVol : r26t3_a R (f + c • g) =ᵐ[(volume : Measure (Euc p.d))]
      (fun y => r26t3_a R f y + c * r26t3_a R g y) := by
    have h := (ae_withDensity_iff hρmeas).1 hlinAE
    filter_upwards [h] with y hy
    exact hy (by simpa using hρ.2 y)
  have hfun : r26t3_a R (f + c • g) =
      (fun y => r26t3_a R f y + c * r26t3_a R g y) :=
    (Continuous.ae_eq_iff_eq (volume : Measure (Euc p.d)) hcontSum hcontR).1 hlinVol
  exact congrFun hfun x

/-- The actual continuous response representative vanishes on zero input. -/
theorem fp81s21_response_zero
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) (x : Euc p.d) :
    r26t3_a R (0 : Euc p.d → ℝ) x = 0 := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c₀, S, hc₀, hTc⟩ := href 0
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hzeroLp : MemLp (0 : Euc p.d → ℝ) 2 μ := by
    exact MemLp.zero
  obtain ⟨η, hform⟩ := HRS.MS.R26T3.s21f_responseForm_init hδ hδh R
  have hInv := hform.solution (0 : Euc p.d → ℝ) hzeroLp
  have hzeroResp : HRS.Whole.IsResponse (HRS.Whole.rieszKernel p.d p.s) μ
      p.γ (0 : Euc p.d → ℝ) (0 : Euc p.d → ℝ) := by
    constructor
    · exact ⟨MemLp.zero, by simp⟩
    · filter_upwards with y
      simp [HRS.Whole.Kop, HRS.Whole.projMean, HRS.Whole.pair]
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hInvZero := HRS.MS.S98.s98_resp_unique hd1
    p.hs0 hsd hc₀ hTc hγ hInv hzeroResp
  have hK : HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
      (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ
        (0 : Euc p.d → ℝ)) = fun _ => 0 := by
    exact HRS.MS.S98.s98_kop_congr_ae hInvZero ▸ by
      funext y
      simp [HRS.Whole.Kop, HRS.Whole.projMean, HRS.Whole.pair]
  change HRS.Whole.projMean μ (0 : Euc p.d → ℝ) x - p.γ *
    HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s) μ
      (HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s) μ p.γ
        (0 : Euc p.d → ℝ)) x = 0
  rw [hK]
  simp [HRS.Whole.projMean, HRS.Whole.pair]

/-- The response representative is pointwise homogeneous on the smooth test
class, including the scalar operation used in terminal-time quotients. -/
theorem fp81s21_response_smul
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) (g : Euc p.d → ℝ)
    (hg : MemCb (r26t3_J p.d) g) (c : ℝ) (x : Euc p.d) :
    r26t3_a R (c • g) x = c * r26t3_a R g x := by
  have h0 : MemCb (r26t3_J p.d) (0 : Euc p.d → ℝ) :=
    ⟨contDiff_const, fun j hj => ⟨0, by
      rintro _ ⟨y, rfl⟩
      simp [iteratedFDeriv_fun_zero]⟩⟩
  have hlin := fp81s21_response_linear hδ hδh R hγ
    (0 : Euc p.d → ℝ) g h0 hg c x
  rw [fp81s21_response_zero hδ hδh R hγ x] at hlin
  simpa [Pi.zero_apply] using hlin

private theorem fp81s21_response_orbit_memCb
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (α : MultiIndex p.d) {t : ℝ} (ht : 0 ≤ t) :
    MemCb (r26t3_J p.d) (propagatorW (r26t3_coeff R) 0 t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) ∧
    MemCb (r26t3_J p.d) (propagatorW (r26t3_coeff R) 0 t
      (generatorW (r26t3_coeff R) t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) := by
  let Cf : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let A : ℝ := |Co| * HRS.MS.R2WinOrb.s103_b p.d α
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (abs_nonneg Co) (HRS.MS.R2WinOrb.s103_b_nonneg α)
  have hmono : Co * HRS.MS.R2WinOrb.s103_b p.d α ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_abs_self Co)
      (HRS.MS.R2WinOrb.s103_b_nonneg α)
  have htIcc : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have horb : HRS.MS.R2WinErr.S104nOrbit Cf φ t :=
    HRS.MS.R2WinErr.s104b_orbit_of_termRegGen hterm
      R.admissible R.resulting α t ht
  have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  have hmem_of_sup : ∀ {g : Euc p.d → ℝ},
      HRS.Whole.R2OrbitSup Cf (4 * p.d + 42) t g
        (Co * HRS.MS.R2WinOrb.s103_b p.d α) →
      (∃ f : ℝ → Euc p.d → ℝ, IsClassicalAdjointW Cf t g f) →
      MemCb (r26t3_J p.d) (propagatorW Cf 0 t g) := by
    intro g hsup hex
    have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨hex.choose, hex.choose_spec⟩
    have hU := (HRS.MS.R2WinOrb.s103_orbitSup_mono hsup hmono)
      (fun z => propagatorW Cf z t g) hcanonical 0 ⟨le_rfl, ht⟩
    have hderiv := HRS.MS.R2WinOrb.s103_cb_of_E hA0 hU.2
    have hmemK : MemCb (4 * p.d + 42) (propagatorW Cf 0 t g) := by
      refine ⟨hU.1, ?_⟩
      intro j hj
      refine ⟨A, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hderiv j hj y
    exact HRS.MS.R2Obs.s910_memCb_mono (by
      dsimp [r26t3_J]
      omega) hmemK
  have hφmem := hmem_of_sup hraw.1 (horb.ex0 t htIcc)
  have hgenmem := hmem_of_sup hraw.2.2.1 (horb.ex1 t htIcc)
  constructor
  · simpa [Cf, φ, wholeSpaceIndex, r26t3_coeff] using hφmem
  · simpa [Cf, φ, wholeSpaceIndex, r26t3_coeff] using hgenmem

private theorem fp81s21_response_quotient_linear
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) (h : ℝ) (F1 F0 D : Euc p.d → ℝ)
    (hF1 : MemCb (r26t3_J p.d) F1) (hF0 : MemCb (r26t3_J p.d) F0)
    (hD : MemCb (r26t3_J p.d) D) (x : Euc p.d) :
    MemCb (r26t3_J p.d)
        (fun y => h⁻¹ * (F1 y - F0 y) - D y) ∧
      r26t3_a R (fun y => h⁻¹ * (F1 y - F0 y) - D y) x =
        h⁻¹ * (r26t3_a R F1 x - r26t3_a R F0 x) - r26t3_a R D x := by
  let Diff : Euc p.d → ℝ := F1 + (-1) • F0
  let Scaled : Euc p.d → ℝ := h⁻¹ • Diff
  let Err : Euc p.d → ℝ := Scaled + (-1) • D
  have hDiff : MemCb (r26t3_J p.d) Diff := by
    have hneg := (HRS.MS.Tc5.tc5_cb_smul (-1) hF0).1
    have hadd := (HRS.MS.Tc5.tc5_cb_add hF1 hneg).1
    have hadd' : MemCb (r26t3_J p.d) (fun y => F1 y + (-1) * F0 y) := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd
    have heq : (fun y => F1 y + (-1) * F0 y) = Diff := by
      funext y
      simp [Diff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact heq ▸ hadd'
  have hScaled : MemCb (r26t3_J p.d) Scaled := by
    have hsm := (HRS.MS.Tc5.tc5_cb_smul h⁻¹ hDiff).1
    have heq : (fun y => h⁻¹ * Diff y) = Scaled := by
      funext y
      rfl
    exact heq ▸ hsm
  have hnegD := (HRS.MS.Tc5.tc5_cb_smul (-1) hD).1
  have hErr : MemCb (r26t3_J p.d) Err := by
    have hadd := (HRS.MS.Tc5.tc5_cb_add hScaled hnegD).1
    have hadd' : MemCb (r26t3_J p.d) (fun y => Scaled y + (-1) * D y) := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd
    have heq : (fun y => Scaled y + (-1) * D y) = Err := by
      funext y
      simp [Err, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact heq ▸ hadd'
  have hlinear1 := fp81s21_response_linear hδ hδh R hγ F1 F0 hF1 hF0 (-1) x
  have hlinear1'' : r26t3_a R Diff x =
      r26t3_a R F1 x + (-1) * r26t3_a R F0 x := by
    simpa [Diff] using hlinear1
  have hlinear1' : r26t3_a R Diff x =
      r26t3_a R F1 x - r26t3_a R F0 x := by
    rw [hlinear1'']
    ring
  have hsmul := fp81s21_response_smul hδ hδh R hγ Diff hDiff h⁻¹ x
  have hlinear2 := fp81s21_response_linear hδ hδh R hγ
    Scaled D hScaled hD (-1) x
  have hlinear2'' : r26t3_a R Err x =
      r26t3_a R Scaled x + (-1) * r26t3_a R D x := by
    simpa [Err] using hlinear2
  have hlinear2' : r26t3_a R Err x =
      r26t3_a R Scaled x - r26t3_a R D x := by
    rw [hlinear2'']
    ring
  have hErrEq : Err = (fun y => h⁻¹ * (F1 y - F0 y) - D y) := by
    funext y
    simp [Err, Scaled, Diff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hresponseErr : r26t3_a R Err x =
      h⁻¹ * (r26t3_a R F1 x - r26t3_a R F0 x) - r26t3_a R D x := by
    calc
      r26t3_a R Err x = r26t3_a R Scaled x - r26t3_a R D x := hlinear2'
      _ = h⁻¹ * r26t3_a R Diff x - r26t3_a R D x := by rw [hsmul]
      _ = _ := by rw [hlinear1']
  constructor
  · exact hErrEq ▸ hErr
  · exact (congrArg (fun f => r26t3_a R f x) hErrEq.symm).trans hresponseErr

private theorem fp81s21_response_coordinate_hasDerivWithinAt
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (α : MultiIndex p.d) {H τ : ℝ} (hH : 0 ≤ H)
    (hτ : τ ∈ Icc (0 : ℝ) H) (x : Euc p.d) :
    HasDerivWithinAt
      (fun s => r26t3_a R (propagatorW (r26t3_coeff R) 0 s
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
      (r26t3_a R (propagatorW (r26t3_coeff R) 0 τ
        (generatorW (r26t3_coeff R) τ
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x)
      (Icc (0 : ℝ) H) τ := by
  let Cf : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let Fa : ℝ → Euc p.d → ℝ := fun s => r26t3_a R (propagatorW Cf 0 s φ)
  let Fb : ℝ → Euc p.d → ℝ := fun s =>
    r26t3_a R (propagatorW Cf 0 s (generatorW Cf s φ))
  obtain ⟨C, hC0, hsmooth⟩ := fp81s21_response_smooth hδ hδh R hγ
  have hcdA : ∀ s ∈ Icc (0 : ℝ) H,
      ContDiff ℝ (0 : WithTop ℕ∞) (Fa s) := by
    intro s hs
    have hmem := fp81s21_response_orbit_memCb hδ hδh R hγ
      hclaims hterm α hs.1
    have hresp := hsmooth (propagatorW Cf 0 s φ) hmem.1
    exact hresp.1.1.of_le (by norm_num)
  have hcdB : ∀ s ∈ Icc (0 : ℝ) H,
      ContDiff ℝ (0 : WithTop ℕ∞) (Fb s) := by
    intro s hs
    have hmem := fp81s21_response_orbit_memCb hδ hδh R hγ
      hclaims hterm α hs.1
    have hresp := hsmooth
      (propagatorW Cf 0 s (generatorW Cf s φ)) hmem.2
    exact hresp.1.1.of_le (by norm_num)
  have hJleK : r26t3_J p.d ≤ 4 * p.d + 42 := by
    dsimp [r26t3_J]
    omega
  have hdata := hterm R.ε R.ψ R.ρ R.admissible R.resulting α H hH
  have hdq := hdata.2.1
  have hdiff : ∀ s ∈ Icc (0 : ℝ) H, ∀ e : ℝ, 0 < e →
      ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, h ≠ 0 → |h| < η →
        s + h ∈ Icc (0 : ℝ) H → ∀ y : Euc p.d,
          ‖iteratedFDeriv ℝ 0
            (fun z => h⁻¹ * (Fa (s + h) z - Fa s z) - Fb s z) y‖ ≤ e := by
    intro s hs e he
    let B : ℝ := C * ((r26t3_J p.d : ℝ) + 1)
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    let e0 : ℝ := e / (B + 1)
    have he0 : 0 < e0 := by
      dsimp [e0]
      positivity
    obtain ⟨η0, hη0, hquot0⟩ := hdq ⟨0, by omega⟩ (by norm_num)
      0 s le_rfl hs.1 hs.2 e0 he0
    refine ⟨η0, hη0, fun h hne hlt hsh y => ?_⟩
    have hterminalLo : 0 ≤ s + h := hsh.1
    have hterminalHi : s + h ≤ H := hsh.2
    have hmode1 := fp81s21_response_orbit_memCb hδ hδh R hγ
      hclaims hterm α hterminalLo
    have hmode0 := fp81s21_response_orbit_memCb hδ hδh R hγ
      hclaims hterm α hs.1
    let F1 := propagatorW Cf 0 (s + h) φ
    let F0 := propagatorW Cf 0 s φ
    let D := propagatorW Cf 0 s (generatorW Cf s φ)
    let Err : Euc p.d → ℝ := fun z => h⁻¹ * (F1 z - F0 z) - D z
    have hmemD : MemCb (r26t3_J p.d) D := by
      simpa [D, Cf, φ, wholeSpaceIndex, r26t3_coeff] using hmode0.2
    have hres := fp81s21_response_quotient_linear hδ hδh R hγ h F1 F0 D
      (by simpa [F1, Cf, φ, wholeSpaceIndex, r26t3_coeff] using hmode1.1)
      (by simpa [F0, Cf, φ, wholeSpaceIndex, r26t3_coeff] using hmode0.1)
      hmemD y
    have hquotBound : ∀ j ≤ 4 * p.d + 42, ∀ z : Euc p.d,
        ‖iteratedFDeriv ℝ j Err z‖ ≤ e0 := by
      intro j hj z
      have hq := hquot0 h hne hlt (by linarith [hs.1]) (by linarith [hs.2]) j hj z
      simpa [HRS.MS.R2WinOrbNL.s103nData, Cf, φ, F1, F0, D, Err,
        r26t3_coeff, wholeSpaceIndex] using hq
    have hcbErr : cbNorm (r26t3_J p.d) Err ≤
        ((r26t3_J p.d : ℝ) + 1) * e0 :=
      HRS.MS.S21.s21g_cbNorm_le (fun j hj z =>
        hquotBound j (le_trans hj hJleK) z)
    have hrespBound := hsmooth Err hres.1
    have hpoint : |r26t3_a R Err y| ≤ C * cbNorm (r26t3_J p.d) Err := by
      have h0 := HRS.MS.R2Obs.s910_norm_iter_le_cb hrespBound.1
        (j := 0) (by omega) y
      have habs : |r26t3_a R Err y| ≤
          cbNorm (r26t3_k p.d + 2) (r26t3_a R Err) := by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h0
      exact habs.trans hrespBound.2.1
    have hresponseQuot := hres.2
    have hscalar : |h⁻¹ * (Fa (s + h) y - Fa s y) - Fb s y| ≤ B * e0 := by
      have heq := congrArg abs hresponseQuot.symm
      calc
        |h⁻¹ * (Fa (s + h) y - Fa s y) - Fb s y| =
            |r26t3_a R Err y| := by
              simpa [Err, Fa, Fb, F1, F0, D, Cf, φ, r26t3_coeff] using heq
        _ ≤ C * cbNorm (r26t3_J p.d) Err := hpoint
        _ ≤ C * (((r26t3_J p.d : ℝ) + 1) * e0) :=
              mul_le_mul_of_nonneg_left hcbErr hC0
        _ = B * e0 := by
              dsimp [B]
              ring
    have hBbound : B * e0 ≤ e := by
      have hden : 0 < B + 1 := by linarith [hB0]
      calc
        B * e0 = (B * e) / (B + 1) := by
          simp [e0, div_eq_mul_inv]
          ring
        _ ≤ e := (div_le_iff₀ hden).2 (by nlinarith [he])
    have hscalar' := hscalar.trans hBbound
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Fa, Fb] using hscalar'
  exact HRS.MS.R2WinOrb.s103_hasDeriv_val hcdA hcdB hdiff x τ hτ

private theorem fp81s21_ellVec_continuous_of_coordinates
    {X : Type*} [TopologicalSpace X] (m : ℝ)
    (g : MultiIndex p.d → X → ℝ) (c : MultiIndex p.d → ℝ)
    (hc : Summable fun α => c α ^ 2)
    (hg : ∀ α, Continuous (g α))
    (hb : ∀ α x, |g α x| ≤ c α) :
    Continuous fun x => ellVec (d := p.d) m (fun α => g α x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hmem : ∀ y, Memℓp (fun α => g α y) 2 := fun y =>
    HRS.MS.CovMeas.s101_memℓp_of_bound hc (fun α => hb α y)
  have hsq : ∀ y, ‖ellVec (d := p.d) m (fun α => g α y) -
      ellVec (d := p.d) m (fun α => g α x)‖ ^ 2 =
      ∑' α, (g α y - g α x) ^ 2 := by
    intro y
    rw [HRS.MS.CovMeas.s101_norm_sq_tsum]
    refine tsum_congr fun α => ?_
    rw [HRS.MS.CovMeas.s101_coord_sub,
      HRS.MS.CovMeas.s101_ellVec_coord (hmem y),
      HRS.MS.CovMeas.s101_ellVec_coord (hmem x)]
  have ht : Tendsto (fun y => ∑' α, (g α y - g α x) ^ 2) (𝓝 x)
      (𝓝 (∑' _ : MultiIndex p.d, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun α => (2 * c α) ^ 2)
      (by simpa [mul_pow] using hc.mul_left 4 |>.congr fun α => by ring)
      (fun α => ?_) (Eventually.of_forall fun y α => ?_)
    · have h := (((hg α).tendsto x).sub_const (g α x)).pow 2
      simpa using h
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hb α y
      have h2 := hb α x
      have h3 := abs_le.mp h1
      have h4 := abs_le.mp h2
      exact sq_le_sq' (by linarith) (by linarith)
  have ht0 : Tendsto (fun y => ∑' α, (g α y - g α x) ^ 2) (𝓝 x) (𝓝 0) := by
    simpa using ht
  have hs : Tendsto (fun y => Real.sqrt (∑' α, (g α y - g α x) ^ 2))
      (𝓝 x) (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp ht0
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun y => ?_
  rw [← hsq y, Real.sqrt_sq (norm_nonneg _)]

/-!
Exact response-window statement for this packet: at the preparation's common
radius and for every spatial point, `responseWindow R b x` is the continuous
path `t ↦ r2Vprop ... (b+t) ...`; its coordinates equal the pointwise response
representative applied to the propagated oscillator tests, and the defining
coordinate sequence is in `ℓ²`. The response-inverse identity used in
`r26t3_a` is only `μ⁰`-a.e.; these path statements concern its smooth
representative and therefore hold everywhere in `x` and `t`.
-/

private theorem fp81s21_response_S102Lin
    (R : Trajectory p δ) {H : ℝ} :
    HRS.MS.R2Interp.S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
  intro u t hu hut _ht φ ψ c hφ hψ
  have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
    (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
  have hfun : φ + c • ψ = (fun x => φ x + c * ψ x) := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  change propagatorW (r26t3_coeff R) u t (φ + c • ψ) x = _
  rw [hfun]
  exact congrFun h x

private theorem fp81s21_response_weighted_hermite_eq
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (b : ℝ) (hb : 0 ≤ b) (t : Icc (0 : ℝ) p.T) (x : Euc p.d)
    (β : MultiIndex p.d) :
    (oscEigenvalue p.d β) ^ (-((wholeSpaceIndex p.d : ℝ) / 2)) *
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
          (hermiteFunD β)) x =
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x := by
  have htime : 0 ≤ b + (t : ℝ) := by linarith [hb, t.2.1]
  have htest := fp81s21_response_orbit_memCb hδ hδh R hγ
    hclaims hterm β htime
  have hlin := fp81s21_response_S102Lin R
    (H := b + p.T)
  have hherm := HRS.MS.R2Interp.s102_U_herm hlin
    (u := 0) (t := b + (t : ℝ)) le_rfl (by linarith [hb, t.2.1])
    (by linarith [t.2.2]) β
  rw [hherm]
  have hsmul := fp81s21_response_smul hδ hδh R hγ
    (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
      (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) htest.1
    ((oscEigenvalue p.d β) ^ ((wholeSpaceIndex p.d : ℝ) / 2)) x
  change (oscEigenvalue p.d β) ^ (-((wholeSpaceIndex p.d : ℝ) / 2)) *
      r26t3_a R
        (((oscEigenvalue p.d β) ^ ((wholeSpaceIndex p.d : ℝ) / 2)) •
          propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
            (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x = _
  rw [hsmul, ← mul_assoc, ← Real.rpow_add (oscEigenvalue_pos β)]
  have hexp : -((wholeSpaceIndex p.d : ℝ) / 2) +
      (wholeSpaceIndex p.d : ℝ) / 2 = 0 := by ring
  rw [hexp, Real.rpow_zero, one_mul]

private theorem fp81s21_r2Vprop_coord_of_weighted_mem
    {d : ℕ} (C : WholeCoeff d) (m t u : ℝ)
    (z : (Euc d → ℝ) → ℝ) (α : MultiIndex d)
    (hmem : Memℓp (fun β : MultiIndex d =>
      (oscEigenvalue d β) ^ (-(m / 2)) *
        z (propagatorW C u t (hermiteFunD β))) 2) :
    OscDual.coord (r2Vprop C m t u z) α =
      (oscEigenvalue d α) ^ (-(m / 2)) *
        z (propagatorW C u t (hermiteFunD α)) := by
  unfold r2Vprop
  exact OscDual.coord_ofSeq_of_mem _ hmem α

private theorem fp81s21_response_weighted_hermite_memℓp
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (b : ℝ) (hb : 0 ≤ b) (t : Icc (0 : ℝ) p.T) (x : Euc p.d) :
    Memℓp (fun β : MultiIndex p.d =>
      (oscEigenvalue p.d β) ^ (-((wholeSpaceIndex p.d : ℝ) / 2)) *
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
          (hermiteFunD β)) x) 2 := by
  have hmem := fp81s21_response_modes_memℓp_of_orbits
    hδ hδh R hγ hclaims hterm b hb t x
  have hseq : (fun β : MultiIndex p.d =>
      (oscEigenvalue p.d β) ^ (-((wholeSpaceIndex p.d : ℝ) / 2)) *
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
          (hermiteFunD β)) x) =
    (fun β : MultiIndex p.d =>
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x) := by
    funext β
    exact fp81s21_response_weighted_hermite_eq hδ hδh R hγ
      hclaims hterm b hb t x β
  have hweighted : Memℓp (fun β : MultiIndex p.d =>
      (oscEigenvalue p.d β) ^ (-((wholeSpaceIndex p.d : ℝ) / 2)) *
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
          (hermiteFunD β)) x) 2 := by
    rw [hseq]
    exact hmem
  exact hweighted

private theorem fp81s21_response_r2Vprop_coord
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (b : ℝ) (hb : 0 ≤ b) (t : Icc (0 : ℝ) p.T) (x : Euc p.d)
    (α : MultiIndex p.d) :
    OscDual.coord
        (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) α =
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
  let z : (Euc p.d → ℝ) → ℝ := fun f => r26t3_a R f x
  have hweighted := fp81s21_response_weighted_hermite_memℓp
    hδ hδh R hγ hclaims hterm b hb t x
  have hseq := fp81s21_response_weighted_hermite_eq
    hδ hδh R hγ hclaims hterm b hb t x α
  calc
    OscDual.coord
        (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 z) α =
      (oscEigenvalue p.d α) ^ (-((wholeSpaceIndex p.d : ℝ) / 2)) *
        z (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ)) (hermiteFunD α)) :=
      fp81s21_r2Vprop_coord_of_weighted_mem
        (r26t3_coeff R) (wholeSpaceIndex p.d) (b + (t : ℝ)) 0 z α hweighted
    _ = r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := hseq

private theorem fp81s21_response_coordinate_fderiv_bound
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (α : MultiIndex p.d) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc p.d,
      ‖fderiv ℝ (r26t3_a R
        (propagatorW (r26t3_coeff R) 0 t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x‖ ≤
        C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α) := by
  obtain ⟨C, hC0, hsmooth⟩ := fp81s21_response_smooth hδ hδh R hγ
  let Cf : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let A : ℝ := |Co| * HRS.MS.R2WinOrb.s103_b p.d α
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (abs_nonneg Co) (HRS.MS.R2WinOrb.s103_b_nonneg α)
  have hmono : Co * HRS.MS.R2WinOrb.s103_b p.d α ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_abs_self Co)
      (HRS.MS.R2WinOrb.s103_b_nonneg α)
  have htIcc : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have horb : HRS.MS.R2WinErr.S104nOrbit Cf φ t :=
    HRS.MS.R2WinErr.s104b_orbit_of_termRegGen hterm
      R.admissible R.resulting α t ht
  have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  have hsup := HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.1 hmono
  have hclassical := HRS.MS.Fcau.propagatorW_isClassical (horb.ex0 t htIcc)
  have hU := hsup (fun z => propagatorW Cf z t φ)
    hclassical 0 ⟨le_rfl, ht⟩
  have hderiv := HRS.MS.R2WinOrb.s103_cb_of_E hA0 hU.2
  have hmemK : MemCb (4 * p.d + 42) (propagatorW Cf 0 t φ) := by
    refine ⟨hU.1, ?_⟩
    intro j hj
    refine ⟨A, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hderiv j hj y
  have hmemJ : MemCb (r26t3_J p.d) (propagatorW Cf 0 t φ) :=
    HRS.MS.R2Obs.s910_memCb_mono (by
      dsimp [r26t3_J]
      omega) hmemK
  have hcbK : cbNorm (4 * p.d + 42) (propagatorW Cf 0 t φ) ≤ A := by
    apply (ENNReal.ofReal_le_ofReal_iff hA0).1
    rw [← HRS.MS.R2WinOrb.s103_cbE_eq hmemK]
    exact hU.2
  have hcbJ : cbNorm (r26t3_J p.d) (propagatorW Cf 0 t φ) ≤ A :=
    (HRS.MS.R2Obs.s910_cbNorm_mono (by
      dsimp [r26t3_J]
      omega) (propagatorW Cf 0 t φ)).trans hcbK
  obtain ⟨haMem, haNorm, -, -⟩ := hsmooth
    (propagatorW Cf 0 t φ) hmemJ
  refine ⟨C, hC0, fun x => ?_⟩
  have hiter := HRS.MS.R2Obs.s910_norm_iter_le_cb haMem
    (j := 1) (by dsimp [r26t3_k]; omega) x
  rw [← norm_iteratedFDeriv_one]
  calc
    ‖iteratedFDeriv ℝ 1 (r26t3_a R (propagatorW Cf 0 t φ)) x‖ ≤
        cbNorm (r26t3_k p.d + 2) (r26t3_a R (propagatorW Cf 0 t φ)) := hiter
    _ ≤ C * cbNorm (r26t3_J p.d) (propagatorW Cf 0 t φ) := haNorm
    _ ≤ C * A := mul_le_mul_of_nonneg_left hcbJ hC0
    _ = C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α) := rfl

private theorem fp81s21_response_coordinate_fderiv_bound_fixed
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) (C : ℝ) (hC0 : 0 ≤ C)
    (hsmooth : ∀ q : Euc p.d → ℝ, MemCb (r26t3_J p.d) q →
      MemCb (r26t3_k p.d + 2) (r26t3_a R q) ∧
      cbNorm (r26t3_k p.d + 2) (r26t3_a R q) ≤
        C * cbNorm (r26t3_J p.d) q)
    {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (α : MultiIndex p.d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ x : Euc p.d,
      ‖fderiv ℝ (r26t3_a R
        (propagatorW (r26t3_coeff R) 0 t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x‖ ≤
        C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α) := by
  let Cf : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let A : ℝ := |Co| * HRS.MS.R2WinOrb.s103_b p.d α
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (abs_nonneg Co) (HRS.MS.R2WinOrb.s103_b_nonneg α)
  have hmono : Co * HRS.MS.R2WinOrb.s103_b p.d α ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_abs_self Co)
      (HRS.MS.R2WinOrb.s103_b_nonneg α)
  have htIcc : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have horb : HRS.MS.R2WinErr.S104nOrbit Cf φ t :=
    HRS.MS.R2WinErr.s104b_orbit_of_termRegGen hterm
      R.admissible R.resulting α t ht
  have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  have hsup := HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.1 hmono
  have hclassical := HRS.MS.Fcau.propagatorW_isClassical (horb.ex0 t htIcc)
  have hU := hsup (fun z => propagatorW Cf z t φ) hclassical 0 ⟨le_rfl, ht⟩
  have hderiv := HRS.MS.R2WinOrb.s103_cb_of_E hA0 hU.2
  have hmemK : MemCb (4 * p.d + 42) (propagatorW Cf 0 t φ) := by
    refine ⟨hU.1, ?_⟩
    intro j hj
    refine ⟨A, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hderiv j hj y
  have hmemJ : MemCb (r26t3_J p.d) (propagatorW Cf 0 t φ) :=
    HRS.MS.R2Obs.s910_memCb_mono (by
      dsimp [r26t3_J]
      omega) hmemK
  have hcbK : cbNorm (4 * p.d + 42) (propagatorW Cf 0 t φ) ≤ A := by
    apply (ENNReal.ofReal_le_ofReal_iff hA0).1
    rw [← HRS.MS.R2WinOrb.s103_cbE_eq hmemK]
    exact hU.2
  have hcbJ : cbNorm (r26t3_J p.d) (propagatorW Cf 0 t φ) ≤ A :=
    (HRS.MS.R2Obs.s910_cbNorm_mono (by
      dsimp [r26t3_J]
      omega) (propagatorW Cf 0 t φ)).trans hcbK
  obtain ⟨haMem, haNorm⟩ := hsmooth (propagatorW Cf 0 t φ) hmemJ
  intro x
  have hiter := HRS.MS.R2Obs.s910_norm_iter_le_cb haMem
    (j := 1) (by dsimp [r26t3_k]; omega) x
  rw [← norm_iteratedFDeriv_one]
  calc
    ‖iteratedFDeriv ℝ 1 (r26t3_a R (propagatorW Cf 0 t φ)) x‖ ≤
        cbNorm (r26t3_k p.d + 2) (r26t3_a R (propagatorW Cf 0 t φ)) := hiter
    _ ≤ C * cbNorm (r26t3_J p.d) (propagatorW Cf 0 t φ) := haNorm
    _ ≤ C * A := mul_le_mul_of_nonneg_left hcbJ hC0
    _ = C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α) := rfl

private theorem fp81s21_response_coordinate_joint_continuous
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (b : ℝ) (hb : 0 ≤ b) (C : ℝ) (hC0 : 0 ≤ C)
    (hsmooth : ∀ q : Euc p.d → ℝ, MemCb (r26t3_J p.d) q →
      MemCb (r26t3_k p.d + 2) (r26t3_a R q) ∧
      cbNorm (r26t3_k p.d + 2) (r26t3_a R q) ≤
        C * cbNorm (r26t3_J p.d) q)
    (α : MultiIndex p.d) :
    Continuous (fun z : Euc p.d × Icc (0 : ℝ) p.T =>
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.1) := by
  let H : ℝ := b + p.T
  have hH : 0 ≤ H := by dsimp [H]; linarith [p.hT, hb]
  let θ : Icc (0 : ℝ) p.T → Icc (0 : ℝ) H := fun s =>
    ⟨b + (s : ℝ), ⟨add_nonneg hb s.2.1, by
      dsimp [H]
      linarith [s.2.2]⟩⟩
  have hθ : Continuous θ := by
    change Continuous (fun s : Icc (0 : ℝ) p.T =>
      (⟨b + (s : ℝ), _⟩ : Icc (0 : ℝ) H))
    fun_prop
  have htime : ∀ x : Euc p.d, Continuous (fun s : Icc (0 : ℝ) p.T =>
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (s : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) := by
    intro x
    have hcontOn : ContinuousOn
        (fun q : ℝ => r26t3_a R (propagatorW (r26t3_coeff R) 0 q
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
        (Icc (0 : ℝ) H) := by
      intro q hq
      exact (fp81s21_response_coordinate_hasDerivWithinAt
        hδ hδh R hγ hclaims hterm α hH hq x).continuousWithinAt
    exact (continuousOn_iff_continuous_restrict.mp hcontOn).comp hθ
  have hspace : ∀ (s : Icc (0 : ℝ) p.T) (x y : Euc p.d),
      |r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (s : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (s : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) y| ≤
      C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α) * ‖x - y‖ := by
    intro s x y
    have ht : 0 ≤ b + (s : ℝ) := by linarith [hb, s.2.1]
    have htest := fp81s21_response_orbit_memCb hδ hδh R hγ
      hclaims hterm α ht
    have hresp := hsmooth
      (propagatorW (r26t3_coeff R) 0 (b + (s : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) htest.1
    have hdiff := hresp.1.1.differentiable (by norm_num)
    have hderiv := fp81s21_response_coordinate_fderiv_bound_fixed
      hδ hδh R hγ C hC0 hsmooth hclaims hterm α ht
    have hLip := HRS.Whole.Stein.lip_of_fderiv_bound
      (fun y => r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (s : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) y)
      hdiff (C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α))
      (fun y => hderiv y) x y
    simpa only [Real.norm_eq_abs] using hLip
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let L : ℝ := C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hC0
      (mul_nonneg (abs_nonneg Co) (HRS.MS.R2WinOrb.s103_b_nonneg α))
  obtain ⟨δt, hδt, hcloseT⟩ := Metric.continuousAt_iff.1
    ((htime z₀.1).continuousAt (x := z₀.2)) (ε / 2) (by positivity)
  let δx : ℝ := ε / (4 * (L + 1))
  have hδx : 0 < δx := by dsimp [δx]; positivity
  refine ⟨min δx δt, lt_min hδx hδt, ?_⟩
  intro z hz
  have hzProd := hz
  rw [Prod.dist_eq, max_lt_iff] at hzProd
  have hxnorm : ‖z.1 - z₀.1‖ < δx := by
    simpa [dist_eq_norm] using
      (hzProd.1.trans_le (min_le_left δx δt))
  have htclose : dist z.2 z₀.2 < δt :=
    hzProd.2.trans_le (min_le_right δx δt)
  have hsp := hspace z.2 z.1 z₀.1
  have hsp' : |r26t3_a R (propagatorW (r26t3_coeff R) 0
        (b + (z.2 : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.1 -
      r26t3_a R (propagatorW (r26t3_coeff R) 0
        (b + (z.2 : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1| < ε / 2 := by
    calc
      _ ≤ L * ‖z.1 - z₀.1‖ := by simpa [L] using hsp
      _ ≤ L * δx := mul_le_mul_of_nonneg_left hxnorm.le hL0
      _ < ε / 2 := by
        dsimp [δx]
        have hden : 0 < 4 * (L + 1) := by positivity
        have hnum : L * ε < (ε / 2) * (4 * (L + 1)) := by
          nlinarith [hε, hL0]
        calc
          L * (ε / (4 * (L + 1))) = (L * ε) / (4 * (L + 1)) := by ring
          _ < ε / 2 := (div_lt_iff₀ hden).2 hnum
  have htemppos := hcloseT htclose
  have htemp : |r26t3_a R (propagatorW (r26t3_coeff R) 0
        (b + (z.2 : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1 -
      r26t3_a R (propagatorW (r26t3_coeff R) 0
        (b + (z₀.2 : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1| < ε / 2 := by
    simpa only [Real.dist_eq] using htemppos
  have htriangle := abs_sub_le
    (r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.1)
    (r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1)
    (r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z₀.2 : ℝ))
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1)
  calc
    |r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.1 -
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z₀.2 : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1| ≤
      |r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.1 -
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1| +
      |r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1 -
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z₀.2 : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z₀.1| := htriangle
    _ < ε := by linarith [hsp', htemp]

/-- The response-window field is continuous in the spatial point as a map
into `OscPath`. In particular it is Borel and strongly measurable for every
time-zero reference measure. -/
theorem fp81s21_responseWindow_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ b : ℝ, 0 ≤ b →
          Continuous (fun x : Euc p.d => responseWindow R b x) := by
  classical
  obtain ⟨δ0, Co, co, hδ0, hδhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ b hb => ?_⟩
  have hδh : δ ≤ 1 / 2 := hδle.trans hδhalf
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  obtain ⟨Cresp, hCresp0, hsmoothAll⟩ := fp81s21_response_smooth hδ hδh R hγ
  have hsmooth : ∀ q : Euc p.d → ℝ, MemCb (r26t3_J p.d) q →
      MemCb (r26t3_k p.d + 2) (r26t3_a R q) ∧
      cbNorm (r26t3_k p.d + 2) (r26t3_a R q) ≤
        Cresp * cbNorm (r26t3_J p.d) q := fun q hq =>
    ⟨(hsmoothAll q hq).1, (hsmoothAll q hq).2.1⟩
  obtain ⟨C, hC0, hmode⟩ := fp81s21_response_mode_bound_of_orbits
    hδ hδh R hγ hclaims hterm
  let env : MultiIndex p.d → ℝ := fun α =>
    C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α)
  have henvSq : Summable (fun α : MultiIndex p.d => env α ^ 2) := by
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    have hbase := HRS.MS.ProClosureS111.stationary_weight_square_summable hd1
    have hscaled := hbase.mul_left ((C * |Co|) ^ 2)
    convert hscaled using 1
    ext α
    dsimp [env]
    ring
  let g : MultiIndex p.d → Euc p.d × Icc (0 : ℝ) p.T → ℝ := fun α z =>
    r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (z.2 : ℝ))
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.1
  have hgCont : ∀ α, Continuous (g α) := by
    intro α
    exact fp81s21_response_coordinate_joint_continuous
      hδ hδh R hγ hclaims hterm b hb Cresp hCresp0 hsmooth α
  have hgBound : ∀ α z, |g α z| ≤ env α := by
    intro α z
    have ht : 0 ≤ b + (z.2 : ℝ) := by linarith [hb, z.2.2.1]
    simpa [g, env, mul_assoc, mul_left_comm, mul_comm] using
      hmode (b + (z.2 : ℝ)) ht α z.1
  have hellJoint : Continuous (fun z : Euc p.d × Icc (0 : ℝ) p.T =>
      ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ) (fun α => g α z)) :=
    fp81s21_ellVec_continuous_of_coordinates
      (p := p) (wholeSpaceIndex p.d : ℝ) g env henvSq hgCont hgBound
  let g0 : C(Euc p.d × Icc (0 : ℝ) p.T, OscDual p.d (wholeSpaceIndex p.d)) :=
    ⟨fun z => ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
      (fun α => g α z), hellJoint⟩
  have hvec : ∀ x : Euc p.d, ∀ t : Icc (0 : ℝ) p.T,
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (fun f => r26t3_a R f x) = g0 (x, t) := by
    intro x t
    apply HRS.MS.CovMeas.s101_ellVec_ext
    intro α
    have hmem := HRS.MS.CovMeas.s101_memℓp_of_bound henvSq
      (fun β => by simpa [g, env] using hgBound β (x, t))
    change OscDual.coord
        (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) α =
      OscDual.coord
        (ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
          (fun β => g β (x, t))) α
    rw [HRS.MS.CovMeas.s101_ellVec_coord hmem]
    exact fp81s21_response_r2Vprop_coord hδ hδh R hγ
      hclaims hterm b hb t x α
  have hpathEq : ∀ x : Euc p.d,
      responseWindow R b x = ContinuousMap.curry g0 x := by
    intro x
    have hpath0 : Continuous (fun t : Icc (0 : ℝ) p.T => g0 (x, t)) :=
      g0.continuous.comp (continuous_const.prodMk continuous_id)
    have hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) :=
      hpath0.congr fun t => (hvec x t).symm
    have hWindow : responseWindow R b x =
        (⟨fun t : Icc (0 : ℝ) p.T =>
            r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
              (b + (t : ℝ)) 0 (fun f => r26t3_a R f x), hpath⟩ : Window p) := by
      unfold responseWindow windowPathOf
      exact dif_pos hpath
    rw [hWindow]
    apply ContinuousMap.ext
    intro t
    change r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (fun f => r26t3_a R f x) = g0 (x, t)
    exact hvec x t
  have hmap : (fun x : Euc p.d => responseWindow R b x) =
      fun x => ContinuousMap.curry g0 x := funext hpathEq
  rw [hmap]
  exact (ContinuousMap.curry g0).continuous

/-- The actual response window has no zero fallback: it is continuous and
has the propagated-test coordinate identity at every `x` and every window
time. The only almost-everywhere statement is the defining inverse identity
for the response representative. -/
theorem fp81s21_responseWindow_genuine (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ b : ℝ, (hb : 0 ≤ b) → ∀ x : Euc p.d,
          ∃ hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
              r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
                (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)),
            responseWindow R b x =
              (⟨fun t : Icc (0 : ℝ) p.T =>
                  r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
                    (b + (t : ℝ)) 0 (fun f => r26t3_a R f x),
                hpath⟩ : Window p) ∧
            ∀ t : Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
              OscDual.coord (OscPath.at' (responseWindow R b x) t) α =
                r26t3_a R (propagatorW (r26t3_coeff R) 0
                  (b + (t : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
  classical
  obtain ⟨δ0, Co, co, hδ0, hδhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ b hb x => ?_⟩
  have hδh : δ ≤ 1 / 2 := hδle.trans hδhalf
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  let H : ℝ := b + p.T
  have hH : 0 ≤ H := by dsimp [H]; linarith [p.hT, hb]
  let θ : Icc (0 : ℝ) p.T → Icc (0 : ℝ) H := fun t =>
    ⟨b + (t : ℝ), ⟨add_nonneg hb t.2.1, by
      dsimp [H]
      linarith [t.2.2]⟩⟩
  have hθ : Continuous θ := by
    change Continuous (fun t : Icc (0 : ℝ) p.T =>
      (⟨b + (t : ℝ), _⟩ : Icc (0 : ℝ) H))
    fun_prop
  obtain ⟨C, hC0, hmode⟩ := fp81s21_response_mode_bound_of_orbits
    hδ hδh R hγ hclaims hterm
  let env : MultiIndex p.d → ℝ := fun α =>
    C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α)
  have henvSq : Summable (fun α : MultiIndex p.d => env α ^ 2) := by
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    have hbase := HRS.MS.ProClosureS111.stationary_weight_square_summable hd1
    have hscaled := hbase.mul_left ((C * |Co|) ^ 2)
    convert hscaled using 1
    ext α
    dsimp [env]
    ring
  let g : MultiIndex p.d → Icc (0 : ℝ) p.T → ℝ := fun α t =>
    r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x
  have hgCont : ∀ α, Continuous (g α) := by
    intro α
    have hcoordCont : ContinuousOn
        (fun s : ℝ => r26t3_a R (propagatorW (r26t3_coeff R) 0 s
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
        (Icc (0 : ℝ) H) := by
      intro s hs
      exact (fp81s21_response_coordinate_hasDerivWithinAt
        hδ hδh R hγ hclaims hterm α hH hs x).continuousWithinAt
    have hrestrict := continuousOn_iff_continuous_restrict.mp hcoordCont
    change Continuous (fun t : Icc (0 : ℝ) p.T =>
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
    exact hrestrict.comp hθ
  have hgBound : ∀ α t, |g α t| ≤ env α := by
    intro α t
    have ht : 0 ≤ b + (t : ℝ) := by linarith [hb, t.2.1]
    simpa [g, env, mul_assoc, mul_left_comm, mul_comm] using
      hmode (b + (t : ℝ)) ht α x
  have hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) := by
    have hell : Continuous (fun t : Icc (0 : ℝ) p.T =>
        ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ) (fun α => g α t)) :=
      fp81s21_ellVec_continuous_of_coordinates
        (p := p) (wholeSpaceIndex p.d : ℝ) g env henvSq hgCont hgBound
    have heq : ∀ t : Icc (0 : ℝ) p.T,
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (fun f => r26t3_a R f x) =
          ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ) (fun α => g α t) := by
      intro t
      apply HRS.MS.CovMeas.s101_ellVec_ext
      intro α
      rw [HRS.MS.CovMeas.s101_ellVec_coord]
      · exact fp81s21_response_r2Vprop_coord hδ hδh R hγ
          hclaims hterm b hb t x α
      · exact fp81s21_response_modes_memℓp_of_orbits
          hδ hδh R hγ hclaims hterm b hb t x
    exact hell.congr fun t => (heq t).symm
  have hWindow : responseWindow R b x =
      (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (fun f => r26t3_a R f x), hpath⟩ : Window p) := by
    unfold responseWindow windowPathOf
    exact dif_pos hpath
  refine ⟨hpath, hWindow, ?_⟩
  intro t α
  rw [hWindow]
  change OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) α = _
  exact fp81s21_response_r2Vprop_coord hδ hδh R hγ
    hclaims hterm b hb t x α

/-- For a possibly smaller common radius, the response-window map is
strongly measurable under the actual time-zero law and its cubic path norm is
integrable. The bound is deterministic and uses only the square-summable
orbit envelope; no moment assumption on the reference density is added. -/
theorem fp81s21_responseWindow_cubic_integrable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ b : ℝ, 0 ≤ b →
          AEStronglyMeasurable (fun x : Euc p.d => responseWindow R b x)
            (r26t3_mu R 0) ∧
          Integrable (fun x : Euc p.d => ‖responseWindow R b x‖ ^ 3)
            (r26t3_mu R 0) := by
  classical
  obtain ⟨δcommon, Co, co, hcommon0, hcommonHalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δcont, hcont0, hcontHalf, hcont⟩ :=
    fp81s21_responseWindow_continuous p
  obtain ⟨δpath, hpath0, hpathHalf, hpath⟩ :=
    fp81s21_responseWindow_genuine p
  let δ0 : ℝ := min δcommon (min δcont δpath)
  have hδ0 : 0 < δ0 := lt_min hcommon0 (lt_min hcont0 hpath0)
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hcommonHalf
  refine ⟨δ0, hδ0, hδ0Half, fun δ hδ hδle R hγ b hb => ?_⟩
  have hδcommon : δ ≤ δcommon := hδle.trans (min_le_left _ _)
  have hδcont : δ ≤ δcont := hδle.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδpath : δ ≤ δpath := hδle.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hδh : δ ≤ 1 / 2 := hδcommon.trans hcommonHalf
  obtain ⟨hclaims, -, hterm, -⟩ :=
    hcommon δ hδ hδcommon R.ρβ R.thermal
  have hmeas := hcont δ hδ hδcont R hγ b hb
  obtain ⟨C, hC0, hmode⟩ := fp81s21_response_mode_bound_of_orbits
    hδ hδh R hγ hclaims hterm
  let env : MultiIndex p.d → ℝ := fun α =>
    C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α)
  have henvSq : Summable (fun α : MultiIndex p.d => env α ^ 2) := by
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    have hbase := HRS.MS.ProClosureS111.stationary_weight_square_summable hd1
    have hscaled := hbase.mul_left ((C * |Co|) ^ 2)
    convert hscaled using 1
    ext α
    dsimp [env]
    ring
  have hwindowNorm : ∀ x : Euc p.d,
      ‖responseWindow R b x‖ ≤ Real.sqrt (∑' α, env α ^ 2) := by
    intro x
    obtain ⟨hpathCont, hWindow, -⟩ :=
      hpath δ hδ hδpath R hγ b hb x
    have hvec : ∀ t : Icc (0 : ℝ) p.T,
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (fun f => r26t3_a R f x) =
        ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
          (fun α => r26t3_a R (propagatorW (r26t3_coeff R) 0
            (b + (t : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) := by
      intro t
      apply HRS.MS.CovMeas.s101_ellVec_ext
      intro α
      have hmem := fp81s21_response_modes_memℓp_of_orbits
        hδ hδh R hγ hclaims hterm b hb t x
      change OscDual.coord
          (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) α =
        OscDual.coord
          (ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
            (fun β => r26t3_a R (propagatorW (r26t3_coeff R) 0
              (b + (t : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x)) α
      rw [HRS.MS.CovMeas.s101_ellVec_coord hmem]
      exact fp81s21_response_r2Vprop_coord hδ hδh R hγ
        hclaims hterm b hb t x α
    have henv : ∀ α (t : Icc (0 : ℝ) p.T), |r26t3_a R
        (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤ env α := by
      intro α t
      have ht : 0 ≤ b + (t : ℝ) := by linarith [hb, t.2.1]
      simpa [env, mul_assoc, mul_left_comm, mul_comm] using
        hmode (b + (t : ℝ)) ht α x
    have hnormAt : ∀ t : Icc (0 : ℝ) p.T,
        ‖OscPath.at' (responseWindow R b x) t‖ ≤
          Real.sqrt (∑' α, env α ^ 2) := by
      intro t
      rw [hWindow]
      change ‖r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)‖ ≤ _
      rw [hvec t]
      exact HRS.MS.CovMeas.s101_norm_ellVec_le henvSq
        (fun α => henv α t)
    exact (ContinuousMap.norm_le (responseWindow R b x)
      (Real.sqrt_nonneg _)).2 hnormAt
  haveI hprob : IsProbabilityMeasure (r26t3_mu R 0) := by
    obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
    obtain ⟨M₀, c₀, S, hc₀, hTc⟩ := href 0
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hcube : Integrable (fun x : Euc p.d => ‖responseWindow R b x‖ ^ 3)
      (r26t3_mu R 0) := by
    let K : ℝ := Real.sqrt (∑' α, env α ^ 2)
    have hK0 : 0 ≤ K := by dsimp [K]; exact Real.sqrt_nonneg _
    have hcubeMeas : AEStronglyMeasurable
        (fun x : Euc p.d => ‖responseWindow R b x‖ ^ 3) (r26t3_mu R 0) :=
      ((hmeas.norm.pow 3).aestronglyMeasurable)
    refine Integrable.of_bound hcubeMeas (K ^ 3)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwindowNorm x) 3
  exact ⟨hmeas.aestronglyMeasurable, hcube⟩

private theorem fp81s21_response_r2EllFun_eq_r2Vprop
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {H : ℝ} (hH : 0 ≤ H) (t : Icc (0 : ℝ) H) (x : Euc p.d) :
    r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ) =
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (t : ℝ) 0
        (fun f => r26t3_a R f x) := by
  have ht : 0 ≤ (t : ℝ) := t.2.1
  let t0 : Icc (0 : ℝ) p.T := ⟨0, le_rfl, le_of_lt p.hT⟩
  have ht0 : (t0 : ℝ) = 0 := rfl
  have hmem := fp81s21_response_modes_memℓp_of_orbits
    hδ hδh R hγ hclaims hterm (t : ℝ) ht t0 x
  have hmem' : Memℓp (fun β : MultiIndex p.d =>
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (t : ℝ)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x) 2 := by
    simpa only [ht0, add_zero] using hmem
  apply HRS.MS.CovMeas.s101_ellVec_ext
  intro α
  change OscDual.coord
      (ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
        (fun β => r26t3_a R (propagatorW (r26t3_coeff R) 0 (t : ℝ)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x)) α =
    OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (t : ℝ) 0
        (fun f => r26t3_a R f x)) α
  rw [HRS.MS.CovMeas.s101_ellVec_coord hmem']
  simpa only [ht0, add_zero] using
    (fp81s21_response_r2Vprop_coord hδ hδh R hγ hclaims hterm
      (t : ℝ) ht t0 x α).symm

private theorem fp81s21_r2EllFun_continuous
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : HRS.MS.R2WinOrbNL.S103nOrbitClaims
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen
      p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {H : ℝ} (hH : 0 ≤ H) (x : Euc p.d) :
    Continuous (fun t : Icc (0 : ℝ) H =>
      r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ)) := by
  classical
  obtain ⟨C, hC0, hmode⟩ := fp81s21_response_mode_bound_of_orbits
    hδ hδh R hγ hclaims hterm
  let env : MultiIndex p.d → ℝ := fun α =>
    C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α)
  have henvSq : Summable (fun α : MultiIndex p.d => env α ^ 2) := by
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    have hbase := HRS.MS.ProClosureS111.stationary_weight_square_summable hd1
    have hscaled := hbase.mul_left ((C * |Co|) ^ 2)
    convert hscaled using 1
    ext α
    dsimp [env]
    ring
  let g : MultiIndex p.d → Icc (0 : ℝ) H → ℝ := fun α t =>
    r26t3_a R (propagatorW (r26t3_coeff R) 0 (t : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x
  have hgCont : ∀ α, Continuous (g α) := by
    intro α
    let f : ℝ → ℝ := fun t => r26t3_a R
      (propagatorW (r26t3_coeff R) 0 t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x
    have hfOn : ContinuousOn f (Icc (0 : ℝ) H) := by
      intro t ht
      exact (fp81s21_response_coordinate_hasDerivWithinAt
        hδ hδh R hγ hclaims hterm α hH ht x).continuousWithinAt
    have hf : Continuous (fun t : Icc (0 : ℝ) H => f t) :=
      continuousOn_iff_continuous_restrict.mp hfOn
    exact hf.congr fun t => rfl
  have hgBound : ∀ α t, |g α t| ≤ env α := by
    intro α t
    have ht : 0 ≤ (t : ℝ) := t.2.1
    simpa [g, env, mul_assoc, mul_left_comm, mul_comm] using
      hmode (t : ℝ) ht α x
  have hcontinuous := fp81s21_ellVec_continuous_of_coordinates
    (p := p) (wholeSpaceIndex p.d : ℝ) g env henvSq hgCont hgBound
  change Continuous (fun t : Icc (0 : ℝ) H =>
    ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
      (fun α => r26t3_a R (propagatorW (r26t3_coeff R) 0 (t : ℝ)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x))
  exact hcontinuous

/-!
Compatibility statement for the actual preparation: for every `b ≥ 0`, the
Round2 response field `r2EllFun` on the full interval `[0,b+T]` equals the
`r2Vprop` field and is continuous, so `r2EllPath` is its genuine path; the
linear physical restriction of that path is exactly `responseWindow R b x`.
The common radius is chosen before `R`, `b`, and `x`.
-/
theorem fp81s21_response_r2EllPath_compatibility (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ b : ℝ, (hb : 0 ≤ b) → ∀ x : Euc p.d,
          ∃ hlong : Continuous (fun t : Icc (0 : ℝ) (b + p.T) =>
              r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
                (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ)),
            r2EllPath (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
                (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ)
                (b + p.T) x =
              (⟨fun t : Icc (0 : ℝ) (b + p.T) =>
                r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
                  (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ),
                hlong⟩ : OscPath p.d (wholeSpaceIndex p.d : ℝ) (b + p.T)) ∧
            (∀ t : Icc (0 : ℝ) (b + p.T),
              r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
                  (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ) =
                r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (t : ℝ) 0
                  (fun f => r26t3_a R f x)) ∧
            HRS.MS.ProClosureS111.physicalWindowRestriction
                (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
                (u := b) (H := b + p.T) hb le_rfl
                (r2EllPath (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
                  (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ)
                  (b + p.T) x) = responseWindow R b x := by
  classical
  obtain ⟨δcommon, Co, co, hcommon0, hcommonHalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δpath, hpath0, hpathHalf, hpath⟩ :=
    fp81s21_responseWindow_genuine p
  let δ0 : ℝ := min δcommon δpath
  have hδ0 : 0 < δ0 := lt_min hcommon0 hpath0
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hcommonHalf
  refine ⟨δ0, hδ0, hδ0Half, fun δ hδ hδle R hγ b hb x => ?_⟩
  have hδcommon : δ ≤ δcommon := hδle.trans (min_le_left _ _)
  have hδpath : δ ≤ δpath := hδle.trans (min_le_right _ _)
  have hδh : δ ≤ 1 / 2 := hδcommon.trans hcommonHalf
  obtain ⟨hclaims, -, hterm, -⟩ :=
    hcommon δ hδ hδcommon R.ρβ R.thermal
  let H : ℝ := b + p.T
  have hH : 0 ≤ H := by dsimp [H]; linarith [hb, p.hT]
  have hlong := fp81s21_r2EllFun_continuous
    hδ hδh R hγ hclaims hterm hH x
  let longPath : OscPath p.d (wholeSpaceIndex p.d : ℝ) H :=
    ⟨fun t : Icc (0 : ℝ) H =>
      r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ), hlong⟩
  have hLongPath :
      r2EllPath (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) H x = longPath := by
    unfold r2EllPath
    have hshift : Continuous (fun t : Icc (0 : ℝ) H =>
        r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (0 + (t : ℝ))) := by
      simpa only [zero_add] using hlong
    unfold windowPathOf
    change (if h : Continuous (fun t : Icc (0 : ℝ) H =>
        r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (0 + (t : ℝ))) then
        (⟨fun t : Icc (0 : ℝ) H =>
          r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
            (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (0 + (t : ℝ)), h⟩ :
          OscPath p.d (wholeSpaceIndex p.d : ℝ) H) else 0) = longPath
    rw [dif_pos hshift]
    change (⟨fun t : Icc (0 : ℝ) H =>
      r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (0 + (t : ℝ)),
      hshift⟩ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H) = longPath
    apply ContinuousMap.ext
    intro t
    simp only [zero_add, longPath]
  have hfield : ∀ t : Icc (0 : ℝ) H,
      r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x (t : ℝ) =
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (t : ℝ) 0
          (fun f => r26t3_a R f x) := by
    intro t
    exact fp81s21_response_r2EllFun_eq_r2Vprop
      hδ hδh R hγ hclaims hterm hH t x
  obtain ⟨hshortCont, hshortEq, -⟩ :=
    hpath δ hδ hδpath R hγ b hb x
  have hshort : responseWindow R b x =
      (⟨fun t : Icc (0 : ℝ) p.T =>
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (fun f => r26t3_a R f x), hshortCont⟩ : Window p) :=
    hshortEq
  have hrestrict :
      HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
          (u := b) (H := H) hb le_rfl
          (r2EllPath (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
            (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) H x) =
        responseWindow R b x := by
    rw [hLongPath, hshort]
    apply ContinuousMap.ext
    intro t
    change OscPath.at'
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
          (u := b) (H := H) hb (by dsimp [H]; exact le_rfl) longPath) t =
      OscPath.at'
        (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (fun f => r26t3_a R f x), hshortCont⟩ : Window p) t
    rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply
      (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
          (u := b) (H := H) hb le_rfl]
    have ht : b + (t : ℝ) ∈ Icc (0 : ℝ) H := by
      constructor
      · linarith [hb, t.2.1]
      · dsimp [H]
        linarith [t.2.2]
    have hcoerce :
        (HRS.MS.ProClosureS111.physicalWindowTime
          hb le_rfl t : ℝ) =
          b + (t : ℝ) := rfl
    change r2EllFun (r26t3_coeff R) (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (wholeSpaceIndex p.d : ℝ) x
          (HRS.MS.ProClosureS111.physicalWindowTime
            hb le_rfl t : ℝ) =
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)
    rw [hcoerce]
    exact hfield ⟨b + (t : ℝ), ht⟩
  refine ⟨hlong, ?_, hfield, ?_⟩
  · simpa only [H] using hLongPath
  · simpa only [H] using hrestrict


#print axioms fp81s21_response_linear
#print axioms fp81s21_response_zero
#print axioms fp81s21_response_smul
#print axioms fp81s21_response_orbit_memCb
#print axioms fp81s21_response_quotient_linear
#print axioms fp81s21_response_coordinate_hasDerivWithinAt
#print axioms fp81s21_ellVec_continuous_of_coordinates
#print axioms fp81s21_r2Vprop_coord_of_weighted_mem
#print axioms fp81s21_response_weighted_hermite_memℓp
#print axioms fp81s21_response_r2Vprop_coord
#print axioms fp81s21_response_coordinate_fderiv_bound
#print axioms fp81s21_response_coordinate_fderiv_bound_fixed
#print axioms fp81s21_response_coordinate_joint_continuous
#print axioms fp81s21_responseWindow_genuine
#print axioms fp81s21_responseWindow_continuous
#print axioms fp81s21_responseWindow_cubic_integrable
#print axioms fp81s21_response_r2EllFun_eq_r2Vprop
#print axioms fp81s21_r2EllFun_continuous
#print axioms fp81s21_response_r2EllPath_compatibility

end HRS.Fp81.S21

end
