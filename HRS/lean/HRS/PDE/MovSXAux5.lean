import HRS.PDE.MovSpec1
import HRS.PDE.MovSXAux3
import HRS.PDE.MovSXAux4

/-!
# MOVSX Aux5: exponential moment of a centred statistic; `movT_source_exp`

`movsx_center_exp`: if `E_Q e^{t|Φ|} ≤ e^K` then `E_Q e^{a|Φ - E_QΦ|} ≤ e^{2K}` for `0 ≤ a ≤ t` (Jensen via the tangent line).
`movsx_source_exp`: `N:eq:source-exp` from `movT_pressure_two_sided_C2_proof` (the `C²` version of `perturbed_pressure`)
and `moments_of_pressure`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movsx_center_exp {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {Φ : Ω → ℝ} (hΦ : Measurable Φ) {t a K : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hat : a ≤ t)
    (hK : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * |Φ ω|)) ∂Q ≤ ENNReal.ofReal (Real.exp K)) :
    Integrable Φ Q ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Φ ω - ∫ ω', Φ ω' ∂Q|)) ∂Q ≤
        ENNReal.ofReal (Real.exp (2 * K)) := by
  have hI : Integrable (fun ω => Real.exp (t * |Φ ω|)) Q := by
    refine ⟨(Real.measurable_exp.comp (measurable_const.mul hΦ.abs)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
    exact lt_of_le_of_lt hK ENNReal.ofReal_lt_top
  have hΦi : Integrable Φ Q := by
    refine Integrable.mono' (hI.div_const t) hΦ.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, le_div_iff₀ ht]
    have := Real.add_one_le_exp (t * |Φ ω|)
    nlinarith [abs_nonneg (Φ ω)]
  refine ⟨hΦi, ?_⟩
  set m : ℝ := ∫ ω', Φ ω' ∂Q with hm
  set E : ℝ := ∫ ω, Real.exp (t * |Φ ω|) ∂Q with hE
  have hEK : E ≤ Real.exp K := by
    have h1 : ENNReal.ofReal E = ∫⁻ ω, ENNReal.ofReal (Real.exp (t * |Φ ω|)) ∂Q :=
      ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    rw [← h1] at hK
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hK
  -- Jensen: `exp (t |m|) ≤ E`
  have hmE : Real.exp (t * |m|) ≤ E := by
    set c : ℝ := t * |m| with hc
    have habs : Integrable (fun ω => |Φ ω|) Q := hΦi.abs
    have h1 : |m| ≤ ∫ ω, |Φ ω| ∂Q := by
      rw [hm]; exact abs_integral_le_integral_abs
    have hpt : ∀ ω, Real.exp c * (t * |Φ ω| - c + 1) ≤ Real.exp (t * |Φ ω|) := by
      intro ω
      have := Real.add_one_le_exp (t * |Φ ω| - c)
      rw [Real.exp_sub] at this
      have h2 := Real.exp_pos c
      have h3 : Real.exp c * (Real.exp (t * |Φ ω|) / Real.exp c) = Real.exp (t * |Φ ω|) := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left this h2.le]
    have hsub : Integrable (fun ω => t * |Φ ω| - c) Q := (habs.const_mul t).sub (integrable_const c)
    have hsub1 : Integrable (fun ω => t * |Φ ω| - c + 1) Q := hsub.add (integrable_const 1)
    have hint : Integrable (fun ω => Real.exp c * (t * |Φ ω| - c + 1)) Q := hsub1.const_mul _
    have h4 := integral_mono hint hI hpt
    have h5 : ∫ ω, Real.exp c * (t * |Φ ω| - c + 1) ∂Q = Real.exp c * (t * ∫ ω, |Φ ω| ∂Q - c + 1) := by
      rw [integral_const_mul]
      congr 1
      rw [integral_add hsub (integrable_const (1 : ℝ)), integral_sub (habs.const_mul t) (integrable_const c),
        integral_const_mul]
      simp
    rw [h5] at h4
    have h6 : c ≤ t * ∫ ω, |Φ ω| ∂Q := by rw [hc]; exact mul_le_mul_of_nonneg_left h1 ht.le
    have h7 := Real.exp_pos c
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ t * ∫ ω, |Φ ω| ∂Q - c + 1 by linarith) h7.le]
  have hexpm : Real.exp (a * |m|) ≤ Real.exp K := by
    refine Real.exp_le_exp.2 ?_
    have := Real.exp_le_exp.1 (hmE.trans hEK)
    nlinarith [abs_nonneg m]
  -- pointwise bound
  have hpt : ∀ ω, Real.exp (a * |Φ ω - m|) ≤ Real.exp K * Real.exp (t * |Φ ω|) := by
    intro ω
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : |Φ ω - m| ≤ |Φ ω| + |m| := abs_sub _ _
    have hexp := Real.exp_le_exp.1 hexpm
    nlinarith [abs_nonneg (Φ ω), abs_nonneg m, mul_le_mul_of_nonneg_left h1 ha,
      mul_le_mul_of_nonneg_right hat (abs_nonneg (Φ ω))]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Φ ω - m|)) ∂Q
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (Real.exp (t * |Φ ω|)) ∂Q := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (Real.exp K) * ∫⁻ ω, ENNReal.ofReal (Real.exp (t * |Φ ω|)) ∂Q :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (Real.exp K) := by gcongr
    _ = ENNReal.ofReal (Real.exp (2 * K)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring

theorem movsx_source_exp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ l C : ℝ, 0 < l ∧ ∀ D : DynData d, D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
        Torus.cbNorm 2 ρ ≤ Λ₂ →
      ∀ Lu : ℝ, 0 < Lu → IsLipschitzVF Lu (mfeTransport D ρ) →
      ∀ N : ℕ, 2 ≤ N →
        Integrable (movT_commAt D N ρ)
          (modulatedGibbs (periodicRiesz d s) N D.invβ⁻¹ (withDensityReal ρ)) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l / Lu) * |movT_sourceAt D N ρ X|))
          ∂(modulatedGibbs (periodicRiesz d s) N D.invβ⁻¹ (withDensityReal ρ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨cstar, A, hA, hw, h0, hdom⟩ := movsx_hdom hd hs0 hsd
  obtain ⟨θ₀, C₁, hθ₀, hC₁, hP⟩ := movsx_pressure_two_sided_C2 hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀
    Λ₂ A
  refine ⟨βm * θ₀ / (2 * (|βp| + 1)), 2 * (2 * C₁ + 1), by positivity, ?_⟩
  intro D hDs hβ ρ hρ hck hlow hcb Lu hLu hLip N hN
  subst hDs
  have hN1 : 1 ≤ N := by omega
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hv : Continuous (mfeTransport D ρ) := Commutator.IsLipschitzVF.continuous hLu.le hLip
  have hk := hdom Lu (mfeTransport D ρ) hLu.le hLip
  obtain ⟨h, hhdef⟩ : ∃ h : Torus d → Torus d → ℝ, h = fun x y =>
      Lu⁻¹ * commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) x y := ⟨_, rfl⟩
  have hhm : Measurable (Function.uncurry h) := by
    rw [hhdef]
    exact measurable_const.mul (Q40b.q40b_commKernel_meas hsd hv)
  have hsym : ∀ x y, h x y = h y x := by
    intro x y; rw [hhdef]; simp only; rw [Q40b.q40b_commKernel_symm hsd]
  have hdomh : ∀ x y, |h x y| ≤ A * (periodicRiesz d D.s (x - y) + cstar) := by
    intro x y
    rw [hhdef]; simp only
    rw [abs_mul, abs_of_pos (inv_pos.2 hLu)]
    calc Lu⁻¹ * |commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) x y|
        ≤ Lu⁻¹ * ((A * Lu) * (periodicRiesz d D.s (x - y) + cstar)) :=
          mul_le_mul_of_nonneg_left (hk x y) (inv_pos.2 hLu).le
      _ = A * (periodicRiesz d D.s (x - y) + cstar) := by field_simp
  have hP' := hP ρ hρ hck hlow hcb h hhm hsym hdomh N hN D.invβ⁻¹ hβ
  have hρΛ : ∀ x, ρ x ≤ max Λ₂ 0 := fun x =>
    ((movsx_le_cbNorm_two hck x).trans hcb).trans (le_max_left _ _)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd D.s hs0 hsd cstar hw A (le_max_right _ _) hρΛ hhm hdomh
  have hδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN hs0 N hN1
  have hT : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
  -- the Gibbs measure is a probability measure
  have hP0 := hP' 0 (by simp [hθ₀.le])
  simp only [zero_mul, sub_zero] at hP0
  obtain ⟨hlow0, hup0⟩ := hP0
  have hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal ρ)))
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≠ 0 := by
    intro h0
    rw [h0] at hlow0
    simp at hlow0
    exact absurd hlow0 (not_le.2 (Real.exp_pos _))
  have hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal ρ)))
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup0
  haveI hQ : IsProbabilityMeasure
      (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ)) :=
    (gibbs_facts hgR hK0 hKt).2
  obtain ⟨hE, -⟩ := moments_of_pressure (N := N) (μ := withDensityReal ρ) (g := periodicRiesz d D.s)
    (h := h) hgR hhR (δ := deltaN d D.s N) (C := C₁) (θ₀ := θ₀) (βm := βm) (β := D.invβ⁻¹) hδ hC₁ hθ₀ hβm
    hβ.1 hP'
  have hΦm : Measurable (fun X : Config d N => modulatedEnergy h X (withDensityReal ρ)) :=
    measurable_modulatedEnergy hhR
  have hβ0 : 0 < D.invβ⁻¹ := hβm.trans_le hβ.1
  have hβle : D.invβ⁻¹ ≤ |βp| + 1 := hβ.2.trans ((le_abs_self _).trans (by linarith))
  have htpos : 0 < βm * θ₀ * N := by positivity
  set l : ℝ := βm * θ₀ / (2 * (|βp| + 1)) with hl
  have hl0 : 0 < l := by rw [hl]; positivity
  have ha0 : 0 ≤ l * D.invβ⁻¹ * N := by positivity
  have hat : l * D.invβ⁻¹ * N ≤ βm * θ₀ * N := by
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg N)
    rw [hl, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hβm hθ₀]
  obtain ⟨hint, hcen⟩ := movsx_center_exp
    (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ)) hΦm htpos ha0 hat
    (K := (2 * C₁ + 1) * N * deltaN d D.s N) hE
  -- `C_N = L_u Φ`
  have hCΦ : ∀ X : Config d N, movT_commAt D N ρ X =
      Lu * modulatedEnergy h X (withDensityReal ρ) := by
    intro X
    unfold movT_commAt
    have : commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) = fun x y => Lu * h x y := by
      funext x y; rw [hhdef]; simp only; rw [mul_inv_cancel_left₀ hLu.ne']
    rw [this, modulatedEnergy_smul]
    exact hhR
  have hcommfun : movT_commAt D N ρ = fun X => Lu * modulatedEnergy h X (withDensityReal ρ) := funext hCΦ
  refine ⟨?_, ?_⟩
  · rw [hcommfun]; exact hint.const_mul Lu
  · have hsrc : ∀ X : Config d N, (l / Lu) * |movT_sourceAt D N ρ X| =
        (l * D.invβ⁻¹ * N) * |modulatedEnergy h X (withDensityReal ρ) -
          ∫ X', modulatedEnergy h X' (withDensityReal ρ)
            ∂(modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ))| := by
      intro X
      unfold movT_sourceAt
      simp_rw [hCΦ]
      rw [integral_const_mul, ← mul_sub, abs_mul, abs_mul, abs_neg, abs_mul,
        abs_of_pos hβ0, abs_of_pos hLu, abs_of_nonneg (Nat.cast_nonneg N)]
      field_simp
    simp_rw [hsrc]
    refine hcen.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
    ring

end HRS

end
