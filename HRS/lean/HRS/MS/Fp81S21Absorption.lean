import HRS.MS.Fp81S21Radius
import HRS.MS.Fp81S21SmallFormFull2
import HRS.MS.Fp81S21EnergyIdentity2
import HRS.MS.WadAux37

/-!
# HRS S2.1(iii), packet 5: absorption and uniform adjoint energy decay

The moving-generator correction is absorbed using the thermal Poincare and response bounds,
and the common small-form estimate.  The resulting energy and gradient estimates are uniform
in the terminal horizon.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S111X2

private theorem fp81s21_gradient_energy_continuous
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {φ : Euc p.d → ℝ} {u : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) H φ u) :
    ContinuousOn
      (fun r : ℝ => ∫ x : Euc p.d, ‖gradient (u r) x‖ ^ 2
        ∂(HRS.Whole.withDensityReal R.ρβ))
      (Icc (0 : ℝ) H) := by
  let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμprob : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μ := hμprob
  let g : ℝ → Euc p.d → ℝ := fun r => u (s111x2_clamp H r)
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hFam, hBound⟩ :=
    s111x2_clamp_fam hH.le hu
  let F : ℝ → Euc p.d → ℝ := fun r x => ‖fderiv ℝ (g r) x‖ ^ 2
  have hFcont : Continuous (fun z : ℝ × Euc p.d => F z.1 z.2) := by
    change Continuous (fun z : ℝ × Euc p.d => ‖fderiv ℝ (g z.1) z.2‖ ^ 2)
    exact hFam.c1.norm.pow 2
  have hFbound : ∀ r ∈ Icc (0 : ℝ) H, ∀ x, |F r x| ≤ B1 ^ 2 := by
    intro r hr x
    have hb := hFam.b1 r x
    change |‖fderiv ℝ (g r) x‖ ^ 2| ≤ B1 ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    have hn := norm_nonneg (fderiv ℝ (g r) x)
    nlinarith
  have hI : ContinuousOn
      (fun r => ∫ x, F r x ∂μ) (Icc (0 : ℝ) H) := by
    exact HRS.MS.Wad.s85_cont_param (μ := μ)
      (integrable_const (B1 ^ 2)) hFcont.continuousOn hFbound
  have hEq : ∀ r ∈ Icc (0 : ℝ) H,
      (∫ x, F r x ∂μ) = ∫ x, ‖gradient (u r) x‖ ^ 2 ∂μ := by
    intro r hr
    have hclamp := s111x2_clamp_id hr
    apply integral_congr_ae
    filter_upwards with x
    change ‖fderiv ℝ (u (s111x2_clamp H r)) x‖ ^ 2 = ‖gradient (u r) x‖ ^ 2
    rw [hclamp, s111x2_norm_gradient]
  exact hI.congr fun r hr => (hEq r hr).symm

private theorem fp81s21_absorption_derivative
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {φ : Euc p.d → ℝ} {u : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) H φ u)
    (CD η gap Q : ℝ) (hCD : 0 ≤ CD) (hgap : 0 < gap)
    (hδ : 0 < δ)
    (hQdef : Q = 2 * p.β * CD / Real.sqrt gap)
    (hDsmall : ∀ t : ℝ, 0 ≤ t → ∀ f : Euc p.d → ℝ, MemCb 2 f →
      MemLp (fun x => generatorW (r26t3_coeff R) t f x -
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)) 0 f x) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
      (∫ x, (generatorW (r26t3_coeff R) t f x -
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)) 0 f x) ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ)) ≤
        (CD * δ * Real.exp (-p.c₁ * t)) ^ 2 *
          ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ))
    (hPoinG : ∀ r ∈ Icc (0 : ℝ) H,
      gap * s111x2_centeredSquare (HRS.Whole.withDensityReal R.ρβ) (u r) ≤
        ∫ x, ‖gradient (u r) x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ))
    (hResponse : ResponseForm (rieszKernel p.d p.s)
      (HRS.Whole.withDensityReal R.ρβ) p.β η)
    (huMem : ∀ r ∈ Icc (0 : ℝ) H,
      MemLp (u r) 2 (HRS.Whole.withDensityReal R.ρβ))
    (huCb : ∀ r ∈ Icc (0 : ℝ) H, MemCb 2 (u r)) :
    ∀ τ ∈ Ioo (0 : ℝ) H,
      deriv (fun q => r26t3_energy R (u (H - q))) τ ≤
        -(2 - Q * δ) *
          (∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ)) := by
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμprob
  let E : ℝ → ℝ := fun τ => r26t3_energy R (u (H - τ))
  let G : ℝ → ℝ := fun τ => ∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μstar
  have hGnn : ∀ τ, 0 ≤ G τ := fun τ =>
    integral_nonneg fun x => sq_nonneg ‖gradient (u (H - τ)) x‖
  intro τ hτ
  have hτphys : 0 ≤ H - τ := by linarith [hτ.2]
  have hτI : H - τ ∈ Icc (0 : ℝ) H := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hDsmallτ := hDsmall (H - τ) hτphys (u (H - τ))
    (huCb (H - τ) hτI)
  obtain ⟨hDlp, hDnorm⟩ := hDsmallτ
  let Df : Euc p.d → ℝ := fun x =>
    generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x -
      generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
        (fun _ => R.ρβ)) 0 (u (H - τ)) x
  have hDlp' : MemLp Df 2 μstar := by simpa [Df, μstar] using hDlp
  have hVarD : s111x2_centeredSquare μstar Df ≤ ∫ x, Df x ^ 2 ∂μstar :=
    s111x2_cs_le_sq hDlp'
  have hVarDbd : s111x2_centeredSquare μstar Df ≤
      (CD * δ * Real.exp (-p.c₁ * (H - τ))) ^ 2 * G τ := by
    calc
      s111x2_centeredSquare μstar Df ≤ ∫ x, Df x ^ 2 ∂μstar := hVarD
      _ ≤ (CD * δ * Real.exp (-p.c₁ * (H - τ))) ^ 2 * G τ := by
        simpa [Df, G, μstar] using hDnorm
  have hVarVnn : 0 ≤ s111x2_centeredSquare μstar (u (H - τ)) :=
    s111x2_cs_nonneg _ _
  have hVarDnn : 0 ≤ s111x2_centeredSquare μstar Df := s111x2_cs_nonneg _ _
  have hVarVle : s111x2_centeredSquare μstar (u (H - τ)) ≤ G τ / gap := by
    have hp := hPoinG (H - τ) hτI
    exact (le_div_iff₀ hgap).2 (by simpa [mul_comm, G, μstar] using hp)
  have hEnv : 0 ≤ CD * δ * Real.exp (-p.c₁ * (H - τ)) := by positivity
  let sv := Real.sqrt (s111x2_centeredSquare μstar (u (H - τ)))
  let sd := Real.sqrt (s111x2_centeredSquare μstar Df)
  let sg := Real.sqrt (G τ)
  have hsv : sv ≤ sg / Real.sqrt gap := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
    change (Real.sqrt (s111x2_centeredSquare μstar (u (H - τ)))) ^ 2 ≤
      (Real.sqrt (G τ) / Real.sqrt gap) ^ 2
    rw [Real.sq_sqrt hVarVnn, div_pow, Real.sq_sqrt (hGnn τ), Real.sq_sqrt hgap.le]
    exact hVarVle
  have hsd : sd ≤ (CD * δ * Real.exp (-p.c₁ * (H - τ))) * sg := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hEnv (Real.sqrt_nonneg _))).1
    change (Real.sqrt (s111x2_centeredSquare μstar Df)) ^ 2 ≤
      ((CD * δ * Real.exp (-p.c₁ * (H - τ))) * Real.sqrt (G τ)) ^ 2
    rw [Real.sq_sqrt hVarDnn, mul_pow, Real.sq_sqrt (hGnn τ)]
    exact hVarDbd
  have hProd : sv * sd ≤ (sg / Real.sqrt gap) *
      ((CD * δ * Real.exp (-p.c₁ * (H - τ))) * sg) := by
    calc
      sv * sd ≤ (sg / Real.sqrt gap) * sd :=
        mul_le_mul_of_nonneg_right hsv (Real.sqrt_nonneg _)
      _ ≤ (sg / Real.sqrt gap) *
          ((CD * δ * Real.exp (-p.c₁ * (H - τ))) * sg) :=
        mul_le_mul_of_nonneg_left hsd
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hschwarz := hResponse.schwarz (u (H - τ)) Df (huMem (H - τ) hτI) hDlp'
  have hcross : |2 * p.β * HRS.Whole.susceptibilityCov
      (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df| ≤
      Q * δ * Real.exp (-p.c₁ * (H - τ)) * G τ := by
    calc
      |2 * p.β * HRS.Whole.susceptibilityCov
          (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df| =
        (2 * p.β) * |HRS.Whole.susceptibilityCov
          (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df| := by
            rw [abs_mul, abs_of_pos (mul_pos (by norm_num) p.hβ)]
      _ ≤ (2 * p.β) * (sv * sd) :=
        mul_le_mul_of_nonneg_left hschwarz (mul_nonneg (by norm_num) p.hβ.le)
      _ ≤ (2 * p.β) * ((sg / Real.sqrt gap) *
          ((CD * δ * Real.exp (-p.c₁ * (H - τ))) * sg)) :=
        mul_le_mul_of_nonneg_left hProd (mul_nonneg (by norm_num) p.hβ.le)
      _ = Q * δ * Real.exp (-p.c₁ * (H - τ)) * G τ := by
        have hsqrtG : Real.sqrt (G τ) * Real.sqrt (G τ) = G τ := by
          nlinarith [Real.sq_sqrt (hGnn τ)]
        calc
          (2 * p.β) * ((Real.sqrt (G τ) / Real.sqrt gap) *
              ((CD * δ * Real.exp (-p.c₁ * (H - τ))) * Real.sqrt (G τ))) =
              (2 * p.β * CD / Real.sqrt gap) * δ *
                Real.exp (-p.c₁ * (H - τ)) *
                  (Real.sqrt (G τ) * Real.sqrt (G τ)) := by ring
          _ = Q * δ * Real.exp (-p.c₁ * (H - τ)) * G τ := by
            rw [hQdef, hsqrtG]
  have hExpLe : Real.exp (-p.c₁ * (H - τ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [R.resulting.cpos, hτphys]
  have hcrossUpper :
      2 * p.β * HRS.Whole.susceptibilityCov
        (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df ≤ Q * δ * G τ := by
    calc
      2 * p.β * HRS.Whole.susceptibilityCov
          (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df ≤
        |2 * p.β * HRS.Whole.susceptibilityCov
          (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df| := le_abs_self _
      _ ≤ Q * δ * Real.exp (-p.c₁ * (H - τ)) * G τ := hcross
      _ ≤ Q * δ * G τ := by
        have hcoef : 0 ≤ Q * δ := by
          rw [hQdef]
          exact mul_nonneg
            (div_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) p.hβ.le) hCD)
              (Real.sqrt_nonneg _)) hδ.le
        have hqexp := mul_le_mul_of_nonneg_right hExpLe (hGnn τ)
        nlinarith
  have hder := sol13_reversed_energy_deriv R hH hu hτ
  have hder' : deriv E τ = -2 * G τ +
      2 * p.β * HRS.Whole.susceptibilityCov
        (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ)) Df := by
    have hEq := hder.deriv
    dsimp [E, Df, G, μstar] at hEq ⊢
    exact hEq
  rw [hder']
  nlinarith [hcrossUpper]

private theorem fp81s21_weighted_energy_ac
    {H c : ℝ} (E : ℝ → ℝ)
    (hEAC : AbsolutelyContinuousOnInterval E 0 H) :
    AbsolutelyContinuousOnInterval (fun τ : ℝ => Real.exp (c * τ) * E τ) 0 H := by
  have hExpAC : AbsolutelyContinuousOnInterval (fun τ : ℝ => Real.exp (c * τ)) 0 H :=
    (ContDiff.contDiffOn
      (by fun_prop : ContDiff ℝ 1 (fun τ : ℝ => Real.exp (c * τ)))).absolutelyContinuousOnInterval
  exact hExpAC.mul hEAC

private theorem fp81s21_weighted_energy_deriv
    {H c : ℝ} (E : ℝ → ℝ)
    (hEder : ∀ τ ∈ Ioo (0 : ℝ) H, HasDerivAt E (deriv E τ) τ) :
    ∀ τ ∈ Ioo (0 : ℝ) H,
      HasDerivAt (fun τ : ℝ => Real.exp (c * τ) * E τ)
        (Real.exp (c * τ) * (c * E τ + deriv E τ)) τ := by
  intro τ hτ
  have hExp : HasDerivAt (fun x : ℝ => Real.exp (c * x))
      (Real.exp (c * τ) * c) τ := by
    simpa using ((hasDerivAt_id τ).const_mul c).exp
  have hm := hExp.mul (hEder τ hτ)
  convert hm using 1 <;> ring

private theorem fp81s21_weighted_energy_sign
    {H c : ℝ} (E : ℝ → ℝ)
    (hDerEnergy : ∀ τ ∈ Ioo (0 : ℝ) H, deriv E τ ≤ -c * E τ) :
    ∀ τ ∈ Ioo (0 : ℝ) H,
      Real.exp (c * τ) * (c * E τ + deriv E τ) ≤ 0 := by
  intro τ hτ
  have hde := hDerEnergy τ hτ
  have hnonpos : c * E τ + deriv E τ ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos

private theorem fp81s21_energy_decay
    {H c : ℝ} (E : ℝ → ℝ) (hH : 0 < H)
    (hEAC : AbsolutelyContinuousOnInterval E 0 H)
    (hDerEnergy : ∀ τ ∈ Ioo (0 : ℝ) H, deriv E τ ≤ -c * E τ)
    (hEder : ∀ τ ∈ Ioo (0 : ℝ) H, HasDerivAt E (deriv E τ) τ) :
    ∀ τ ∈ Icc (0 : ℝ) H, E τ ≤ Real.exp (-c * τ) * E 0 := by
  let F : ℝ → ℝ := fun τ => Real.exp (c * τ) * E τ
  have hFAC : AbsolutelyContinuousOnInterval F 0 H := by
    simpa [F] using fp81s21_weighted_energy_ac E hEAC
  have hFderAE : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) H)),
      HasDerivAt F (Real.exp (c * τ) * (c * E τ + deriv E τ)) τ := by
    have hh := s111x2_ae_icc_of_ioo (H := H)
      (fp81s21_weighted_energy_deriv (H := H) (c := c) E hEder)
    simpa [F] using hh
  have hFleAE : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) H)),
      Real.exp (c * τ) * (c * E τ + deriv E τ) ≤ 0 :=
    s111x2_ae_icc_of_ioo (H := H)
      (fp81s21_weighted_energy_sign (H := H) (c := c) E hDerEnergy)
  have hFstart := s111x2_ac_le_start hFAC hFderAE hFleAE hH.le
  intro τ hτ
  have hle := hFstart τ hτ
  have hmul : Real.exp (c * τ) * E τ ≤ E 0 := by
    simpa [F] using hle
  have hexp : 0 < Real.exp (c * τ) := Real.exp_pos _
  have hdiv : E τ ≤ E 0 / Real.exp (c * τ) :=
    (le_div_iff₀ hexp).2 (by simpa [mul_comm] using hmul)
  calc
    E τ ≤ E 0 / Real.exp (c * τ) := hdiv
    _ = Real.exp (-c * τ) * E 0 := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring

private theorem fp81s21_integrated_energy
    {H : ℝ} (E G Gforward : ℝ → ℝ) (hH : 0 < H)
    (hEAC : AbsolutelyContinuousOnInterval E 0 H)
    (hGcont : ContinuousOn Gforward (Icc (0 : ℝ) H))
    (hAbs : ∀ τ ∈ Ioo (0 : ℝ) H, deriv E τ ≤ -G τ)
    (hGforward : ∀ τ ∈ Icc (0 : ℝ) H, G τ = Gforward (H - τ))
    (hEder : ∀ τ ∈ Ioo (0 : ℝ) H, HasDerivAt E (deriv E τ) τ) :
    ∀ r ∈ Icc (0 : ℝ) H,
      E (H - r) + ∫ v in Icc r H, Gforward v ≤ E 0 := by
  have hderEAE : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) H)),
      HasDerivAt E (deriv E τ) τ :=
    s111x2_ae_icc_of_ioo hEder
  intro r hr
  have hτ : H - r ∈ Icc (0 : ℝ) H := by
    constructor <;> linarith [hr.1, hr.2]
  have hFTC := s111x2_integral_deriv hEAC hderEAE
    (a := 0) (b := H - r) le_rfl hτ.1 hτ.2
  have hDerInt : IntervalIntegrable (deriv E) volume 0 (H - r) := by
    apply (hEAC.intervalIntegrable_deriv).mono_set
    rw [uIcc_of_le hτ.1, uIcc_of_le hH.le]
    exact Icc_subset_Icc le_rfl hτ.2
  have hGrevCont : ContinuousOn (fun τ => Gforward (H - τ))
      (Icc (0 : ℝ) H) := by
    apply hGcont.comp (by fun_prop : ContinuousOn (fun τ : ℝ => H - τ) (Icc 0 H))
    intro τ hτ'
    exact ⟨by linarith [hτ'.2], by linarith [hτ'.1]⟩
  have hGrevInt : IntervalIntegrable (fun τ => Gforward (H - τ)) volume 0 (H - r) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hτ.1]
    exact hGrevCont.mono (Icc_subset_Icc le_rfl hτ.2)
  have hmonoInt :
      (∫ τ in (0 : ℝ)..(H - r), deriv E τ) ≤
        ∫ τ in (0 : ℝ)..(H - r), -(Gforward (H - τ)) := by
    rw [intervalIntegral.integral_of_le hτ.1,
      intervalIntegral.integral_of_le hτ.1]
    apply integral_mono_ae
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.1).1 hDerInt)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.1).1 hGrevInt.neg)
    have hAbsAE := s111x2_ae_icc_of_ioo hAbs
    have hsub : Ioc (0 : ℝ) (H - r) ⊆ Icc (0 : ℝ) H := by
      intro τ hτ'
      exact ⟨hτ'.1.le, hτ'.2.trans hτ.2⟩
    have hae := ae_restrict_of_ae_restrict_of_subset hsub hAbsAE
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with τ hAbsHere hτ'
    have hτ'' : τ ∈ Icc (0 : ℝ) H := hsub hτ'
    rw [hGforward τ hτ''] at hAbsHere
    exact hAbsHere
  have hFTC' :
      (∫ τ in (0 : ℝ)..(H - r), deriv E τ) = E (H - r) - E 0 := by
    simpa using hFTC
  have hIneRev : E (H - r) +
      ∫ τ in (0 : ℝ)..(H - r), Gforward (H - τ) ≤ E 0 := by
    have hmononeg : (∫ τ in (0 : ℝ)..(H - r), deriv E τ) ≤
        -(∫ τ in (0 : ℝ)..(H - r), Gforward (H - τ)) := by
      simpa only [intervalIntegral.integral_neg] using hmonoInt
    rw [hFTC'] at hmononeg
    linarith
  have hChange :
      (∫ τ in (0 : ℝ)..(H - r), Gforward (H - τ)) =
        ∫ v in r..H, Gforward v := by
    rw [intervalIntegral.integral_comp_sub_left (fun v => Gforward v) H]
    congr 1 <;> ring
  have hSetChange :
      (∫ v in Icc r H, Gforward v) = ∫ v in r..H, Gforward v := by
    rw [intervalIntegral.integral_of_le hr.2, ← integral_Icc_eq_integral_Ioc]
  calc
    E (H - r) + ∫ v in Icc r H, Gforward v =
        E (H - r) + ∫ v in r..H, Gforward v := by rw [hSetChange]
    _ = E (H - r) + ∫ τ in (0 : ℝ)..(H - r), Gforward (H - τ) := by rw [hChange]
    _ ≤ E 0 := hIneRev

/-- The common-radius absorption, integrated gradient estimate, and exponential energy decay
for every classical adjoint and every terminal horizon. -/
theorem sol13_uniform_adjoint_energy (p : Parameters) :
    ∃ δ0 Q C c : ℝ,
      0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      0 ≤ Q ∧ Q * δ0 ≤ 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H →
      ∀ (φ : Euc p.d → ℝ) (u : ℝ → Euc p.d → ℝ),
        IsClassicalAdjointW (r26t3_coeff R) H φ u →
        let μstar := HRS.Whole.withDensityReal R.ρβ
        let E := fun τ => r26t3_energy R (u (H - τ))
        let G := fun τ => ∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μstar
        AbsolutelyContinuousOnInterval E 0 H ∧
        (∀ τ ∈ Ioo (0 : ℝ) H, deriv E τ ≤ -(2 - Q * δ) * G τ) ∧
        IntegrableOn
          (fun r => ∫ x, ‖gradient (u r) x‖ ^ 2 ∂μstar) (Icc (0 : ℝ) H) ∧
        ∀ r ∈ Icc (0 : ℝ) H,
          (r26t3_energy R (u r) +
            ∫ v in Icc r H, ∫ x, ‖gradient (u v) x‖ ^ 2 ∂μstar)
              ≤ r26t3_energy R φ ∧
          (∫ x, (HRS.Whole.projMean μstar (u r) x) ^ 2 ∂μstar) ≤
            C * Real.exp (-c * (H - r)) *
              ∫ x, (HRS.Whole.projMean μstar φ x) ^ 2 ∂μstar := by
  obtain ⟨δdens, pinf, Kdens, η, gap, hδdens, hδdensHalf, hpinf, hη, hη1,
    hgap, hthermal, henergy, hactual, hratio⟩ := fp81s21_uniform_thermal_package p
  obtain ⟨CD, hCD, hsmall⟩ := sol13_small_form p
  let Q : ℝ := 2 * p.β * CD / Real.sqrt gap
  let δ0 : ℝ := min (1 / 2) (1 / (Q + 1))
  let C : ℝ := η⁻¹
  let c : ℝ := gap / p.β
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) p.hβ.le) hCD
    · exact Real.sqrt_nonneg _
  have hQden : 0 < Q + 1 := by linarith
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min (by norm_num) (by positivity)
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact min_le_left _ _
  have hQδ0 : Q * δ0 ≤ 1 := by
    have hδ0Q : δ0 ≤ 1 / (Q + 1) := by
      dsimp [δ0]
      exact min_le_right _ _
    have hqdiv : Q * (1 / (Q + 1)) ≤ 1 := by
      calc
        Q * (1 / (Q + 1)) = Q / (Q + 1) := by ring
        _ ≤ 1 := (div_le_iff₀ hQden).2 (by linarith)
    exact (mul_le_mul_of_nonneg_left hδ0Q hQ).trans hqdiv
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; exact div_pos hgap p.hβ
  refine ⟨δ0, Q, C, c, hδ0, hδ0half, hQ, hQδ0, hC, hc, ?_⟩
  intro δ hδ hδδ0 R H hH φ u hu
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  let E : ℝ → ℝ := fun τ => r26t3_energy R (u (H - τ))
  let G : ℝ → ℝ := fun τ => ∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μstar
  let Gforward : ℝ → ℝ := fun r => ∫ x, ‖gradient (u r) x‖ ^ 2 ∂μstar
  have hρprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hρprob
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, huB⟩ :=
    HRS.MS.S111X1.classical_bounds hu
  have huMem : ∀ r ∈ Icc (0 : ℝ) H, MemLp (u r) 2 μstar := by
    intro r hr
    exact (MemLp.of_bound (hu.c2 r hr).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (huB r hr x).1)).mono_exponent le_top
  have huCb : ∀ r ∈ Icc (0 : ℝ) H, MemCb 2 (u r) := by
    intro r hr
    refine ⟨hu.c2 r hr, fun j hj => ?_⟩
    obtain ⟨Bj, hBj⟩ := hu.bdd j hj
    refine ⟨Bj, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hBj r hr x
  have hPoincare := (hthermal R.ρβ R.thermal).1
  have hResponse := (hthermal R.ρβ R.thermal).2
  have hPoinG : ∀ r ∈ Icc (0 : ℝ) H,
      gap * s111x2_centeredSquare μstar (u r) ≤ Gforward r := by
    intro r hr
    have hgrad : ∃ Cf : ℝ, ∀ x, ‖gradient (u r) x‖ ≤ Cf :=
      ⟨B1, fun x => by rw [s111x2_norm_gradient]; exact (huB r hr x).2.1⟩
    have hp := hPoincare (u r)
      ((hu.c2 r hr).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) hgrad (huMem r hr)
    have hv : ProbabilityTheory.variance (u r) μstar =
        s111x2_centeredSquare μstar (u r) := by
      rw [ProbabilityTheory.variance_eq_integral (huMem r hr).aemeasurable]
      rfl
    rw [hv] at hp
    exact hp
  have hEnergyComp : ∀ r ∈ Icc (0 : ℝ) H,
      (p.β * η) * s111x2_centeredSquare μstar (u r) ≤ r26t3_energy R (u r) ∧
      r26t3_energy R (u r) ≤ p.β * s111x2_centeredSquare μstar (u r) := by
    intro r hr
    have he := henergy R (u r) (huMem r hr)
    simpa [s111x2_centeredSquare, r26t3_energy, μstar] using he
  have hAbsAC := sol13_reversed_energy_ac R hH hu
  have hGcont := fp81s21_gradient_energy_continuous R hH hu
  have hGint : IntegrableOn Gforward (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH.le).1
      (hGcont.intervalIntegrable_of_Icc hH.le)
  have hGnn : ∀ τ, 0 ≤ G τ := fun τ =>
    integral_nonneg fun x => sq_nonneg ‖gradient (u (H - τ)) x‖
  have hDsmall : ∀ t : ℝ, 0 ≤ t → ∀ f : Euc p.d → ℝ, MemCb 2 f →
      MemLp (fun x => generatorW (r26t3_coeff R) t f x -
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)) 0 f x) 2 μstar ∧
      (∫ x, (generatorW (r26t3_coeff R) t f x -
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)) 0 f x) ^ 2 ∂μstar) ≤
        (CD * δ * Real.exp (-p.c₁ * t)) ^ 2 *
          ∫ x, ‖gradient f x‖ ^ 2 ∂μstar := by
    intro t ht f hf
    simpa [μstar] using hsmall δ hδ (hδδ0.trans hδ0half) R t ht f hf
  have hQdef : Q = 2 * p.β * CD / Real.sqrt gap := rfl
  have hAbs : ∀ τ ∈ Ioo (0 : ℝ) H, deriv E τ ≤ -(2 - Q * δ) * G τ := by
    intro τ hτ
    simpa [E, G, μstar] using
      fp81s21_absorption_derivative R hH hu CD η gap Q hCD hgap hδ hQdef
        hDsmall hPoinG hResponse huMem huCb τ hτ
  have hEupper : ∀ τ ∈ Icc (0 : ℝ) H,
      E τ ≤ (p.β / gap) * G τ := by
    intro τ hτ
    have hτr : H - τ ∈ Icc (0 : ℝ) H := by
      constructor <;> linarith [hτ.1, hτ.2]
    obtain ⟨-, hEhi⟩ := hEnergyComp (H - τ) hτr
    have hvar := hPoinG (H - τ) hτr
    have hvarle : s111x2_centeredSquare μstar (u (H - τ)) ≤ G τ / gap :=
      (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hvar)
    calc
      E τ ≤ p.β * s111x2_centeredSquare μstar (u (H - τ)) := by
        simpa [E] using hEhi
      _ ≤ p.β * (G τ / gap) := mul_le_mul_of_nonneg_left hvarle p.hβ.le
      _ = (p.β / gap) * G τ := by ring
  have hderEnergy : ∀ τ ∈ Ioo (0 : ℝ) H,
      deriv E τ ≤ -c * E τ := by
    intro τ hτ
    have hfactor : 1 ≤ 2 - Q * δ := by
      have hQδ : Q * δ ≤ 1 :=
        (mul_le_mul_of_nonneg_left hδδ0 hQ).trans hQδ0
      linarith
    have hEbound := hEupper τ ⟨hτ.1.le, hτ.2.le⟩
    have hcE : c * E τ ≤ G τ := by
      have hscaled := mul_le_mul_of_nonneg_left hEbound hc.le
      have hcb : c * (p.β / gap) = 1 := by
        dsimp [c]
        field_simp [ne_of_gt p.hβ, ne_of_gt hgap]
      rw [← mul_assoc, hcb, one_mul] at hscaled
      exact hscaled
    have hfirst : deriv E τ ≤ -G τ := by
      have hAbs := hAbs τ hτ
      nlinarith [hGnn τ]
    have hsecond : -G τ ≤ -c * E τ := by linarith [hcE]
    exact hfirst.trans hsecond
  have hEder : ∀ τ ∈ Ioo (0 : ℝ) H, HasDerivAt E (deriv E τ) τ := by
    intro τ hτ
    have h := sol13_reversed_energy_deriv R hH hu hτ
    have hval : deriv E τ = -2 * G τ +
        2 * p.β * HRS.Whole.susceptibilityCov
          (HRS.Whole.rieszKernel p.d p.s) μstar p.β (u (H - τ))
          (fun x => generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x -
            generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
              (fun _ => R.ρβ)) 0 (u (H - τ)) x) := by
      have hh := h.deriv
      dsimp [E, G, μstar] at hh ⊢
      exact hh
    rw [hval]
    simpa [E] using h
  have hAbsNegG : ∀ τ ∈ Ioo (0 : ℝ) H, deriv E τ ≤ -G τ := by
    intro τ hτ
    have hAbsHere := hAbs τ hτ
    have hfactor : 1 ≤ 2 - Q * δ := by
      have hQδ : Q * δ ≤ 1 :=
        (mul_le_mul_of_nonneg_left hδδ0 hQ).trans hQδ0
      linarith
    have hscaled := mul_le_mul_of_nonneg_right hfactor (hGnn τ)
    have hneg : -(2 - Q * δ) * G τ ≤ -G τ := by nlinarith
    exact hAbsHere.trans hneg
  have hDecay := fp81s21_energy_decay (H := H) (c := c) E hH hAbsAC
    hderEnergy hEder
  refine ⟨hAbsAC, hAbs, hGint, ?_⟩
  intro r hr
  have hIntegrated := fp81s21_integrated_energy (H := H) E G Gforward
    hH hAbsAC hGcont hAbsNegG (fun τ hτ => by rfl) hEder r hr
  have hτ : H - r ∈ Icc (0 : ℝ) H := by
    constructor <;> linarith [hr.1, hr.2]
  have hEr : E (H - r) = r26t3_energy R (u r) := by
    simp [E]
  have hE0 : E 0 = r26t3_energy R φ := by
    simp [E, hu.terminal]
  have hVarLower := (hEnergyComp r hr).1
  have hVarUpper0 := (hEnergyComp H ⟨hH.le, le_rfl⟩).2
  have hVarUpperPhi : r26t3_energy R φ ≤
      p.β * s111x2_centeredSquare μstar φ := by
    simpa [hu.terminal] using hVarUpper0
  have hDecayEnergy := hDecay (H - r) hτ
  have hVdecay : s111x2_centeredSquare μstar (u r) ≤
      C * Real.exp (-c * (H - r)) * s111x2_centeredSquare μstar φ := by
    have hcoef : 0 < p.β * η := mul_pos p.hβ hη
    have hmult : 0 ≤ (p.β * η)⁻¹ := (inv_pos.2 hcoef).le
    have hlower : s111x2_centeredSquare μstar (u r) ≤
        (p.β * η)⁻¹ * r26t3_energy R (u r) := by
      calc
        s111x2_centeredSquare μstar (u r) ≤
            r26t3_energy R (u r) / (p.β * η) :=
          (le_div_iff₀ hcoef).2 (by simpa [mul_comm] using hVarLower)
        _ = (p.β * η)⁻¹ * r26t3_energy R (u r) := by
          rw [div_eq_mul_inv]
          ring
    have henergyChain : r26t3_energy R (u r) ≤
        Real.exp (-c * (H - r)) * r26t3_energy R φ := by
      simpa [hEr, hE0, mul_comm] using hDecayEnergy
    calc
      s111x2_centeredSquare μstar (u r) ≤
          (p.β * η)⁻¹ * r26t3_energy R (u r) := hlower
      _ ≤ (p.β * η)⁻¹ *
          (Real.exp (-c * (H - r)) * r26t3_energy R φ) :=
        mul_le_mul_of_nonneg_left henergyChain hmult
      _ ≤ (p.β * η)⁻¹ *
          (Real.exp (-c * (H - r)) *
            (p.β * s111x2_centeredSquare μstar φ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hVarUpperPhi (Real.exp_nonneg _)) hmult
      _ = C * Real.exp (-c * (H - r)) *
          s111x2_centeredSquare μstar φ := by
        dsimp [C]
        field_simp [ne_of_gt p.hβ, ne_of_gt hη]
  have hGtarget :
      (∫ x, (HRS.Whole.projMean μstar (u r) x) ^ 2 ∂μstar) =
        s111x2_centeredSquare μstar (u r) := rfl
  have hGphi :
      (∫ x, (HRS.Whole.projMean μstar φ x) ^ 2 ∂μstar) =
        s111x2_centeredSquare μstar φ := rfl
  refine ⟨?_, ?_⟩
  · simpa [hEr, hE0, Gforward] using hIntegrated
  · rw [hGtarget, hGphi]
    exact hVdecay

#print axioms sol13_uniform_adjoint_energy

end HRS.Fp81.S21

end
