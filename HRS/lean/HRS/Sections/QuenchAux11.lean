import HRS.Sections.QuenchAux10

/-!
# Packet QUENCH (Q27), part 11: `B` is a Brownian motion independent of `Y`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

section BMproc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

/-- The time of an index (`0` for the `Y`-slot). -/
def optTime : Option ℝ≥0 → ℝ
  | none => 0
  | some t => (t : ℝ)

/-- The `B`-coefficient of an index. -/
def optCoef (a : ℝ) : Option ℝ≥0 → ℝ
  | none => 0
  | some _ => a

/-- `Y` together with the Brownian motion `B`, indexed by `Option ℝ≥0` (`none ↦ Y`). -/
def wProc (lam σ : ℝ) (Y : Ω → ℝ) (G : ℝ → Ω → ℝ) : Option ℝ≥0 → Ω → ℝ :=
  fun p ω => p.elim (Y ω) (fun t => bmProc lam σ G (t : ℝ) ω)

variable (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ} (hσ : σ ^ 2 = 2 * lam * v)
include hN hv hlam hσ

theorem isGaussianProcess_wProc : IsGaussianProcess (wProc lam σ Y G) P := by
  classical
  refine ⟨fun I => ?_⟩
  have hm : ∀ p : Option ℝ≥0, AEMeasurable (wProc lam σ Y G p) P := by
    intro p
    cases p with
    | none => exact (hN.proc.hasGaussianLaw_eval none).aemeasurable
    | some t => exact (bm_single_gauss hN hv hlam hσ (NNReal.coe_nonneg t)).aemeasurable
  have hmeas : AEMeasurable (fun ω => I.restrict (wProc lam σ Y G · ω)) P :=
    aemeasurable_pi_iff.2 fun p => hm p.1
  refine ⟨hmeas, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  set a : I → ℝ := fun p => L (fun j => if p = j then 1 else 0) with ha
  set c₀ : ℝ := ∑ p : I, if p.1 = none then a p else 0 with hc₀
  set ts : I → ℝ := fun p => optTime p.1 with hts
  set c : I → ℝ := fun p => optCoef (a p) p.1 with hc
  have hts0 : ∀ p, 0 ≤ ts p := by
    intro p
    show 0 ≤ optTime p.1
    rcases hp : p.1 with _ | t
    · exact le_rfl
    · exact NNReal.coe_nonneg t
  have hLv : ∀ ω, L (I.restrict (wProc lam σ Y G · ω)) = c₀ * Y ω + ∑ p : I, c p * bmProc lam σ G (ts p) ω := by
    intro ω
    rw [show L (I.restrict (wProc lam σ Y G · ω)) = (L : (I → ℝ) →ₗ[ℝ] ℝ) (I.restrict (wProc lam σ Y G · ω)) from rfl,
      LinearMap.pi_apply_eq_sum_univ]
    simp only [hc₀, Finset.sum_mul, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Finset.restrict_def, ha]
    rcases hp : p.1 with _ | t
    · simp only [wProc, hc, hts, hp, optCoef, optTime, Option.elim_none, if_true, zero_mul, add_zero]
      rw [mul_comm]
      rfl
    · simp only [wProc, hc, hts, hp, optCoef, optTime, Option.elim_some, reduceCtorEq, if_false, zero_mul,
        zero_add]
      rw [mul_comm]
      rfl
  have hmap : (P.map (fun ω => I.restrict (wProc lam σ Y G · ω))).map L =
      P.map (fun ω => c₀ * Y ω + ∑ p : I, c p * bmProc lam σ G (ts p) ω) := by
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hmeas]
    congr 1
    funext ω
    exact hLv ω
  rw [hmap, bm_combo_law hN hv hlam hσ ts hts0 c c₀]
  exact ⟨0, _, rfl⟩

theorem bm_gaussianProcess : IsGaussianProcess (fun (t : ℝ≥0) ω => bmProc lam σ G (t : ℝ) ω) P :=
  (isGaussianProcess_wProc hN hv hlam hσ).comp_right some

theorem bm_isPreBrownian : IsPreBrownianReal (fun (t : ℝ≥0) ω => bmProc lam σ G (t : ℝ) ω) P := by
  refine (bm_gaussianProcess hN hv hlam hσ).isPreBrownianReal_of_covariance (fun t => ?_)
    (fun s t hst => ?_)
  · exact bm_single_mean hN hv hlam hσ (NNReal.coe_nonneg t)
  · have h1 := (bm_single_gauss hN hv hlam hσ (NNReal.coe_nonneg s)).memLp_two
    have h2 := (bm_single_gauss hN hv hlam hσ (NNReal.coe_nonneg t)).memLp_two
    change cov[bmProc lam σ G (s : ℝ), bmProc lam σ G (t : ℝ); P] = (s : ℝ)
    rw [covariance_eq_sub h1 h2]
    have := bm_cov_BB hN hv hlam hσ (NNReal.coe_nonneg s) (show (s : ℝ) ≤ t from hst)
    simp only [Pi.mul_apply]
    rw [this, bm_single_mean hN hv hlam hσ (NNReal.coe_nonneg s), bm_single_mean hN hv hlam hσ (NNReal.coe_nonneg t)]
    simp

theorem bm_cont : ∀ᵐ ω ∂P, Continuous fun t : ℝ≥0 => bmProc lam σ G (t : ℝ) ω := by
  filter_upwards [hN.cont] with ω hc
  set g : ℝ → ℝ := fun u => G (max u 0) ω with hg
  have hprim : Continuous fun t : ℝ => ∫ u in (0 : ℝ)..t, g u :=
    intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0
  have hfun : Continuous fun t : ℝ => (g t + lam * ∫ u in (0 : ℝ)..t, g u) / σ :=
    (hc.add (continuous_const.mul hprim)).div_const σ
  have := hfun.comp NNReal.continuous_coe
  refine this.congr fun t => ?_
  simp only [Function.comp_apply, bmProc, hg]
  have ht : (0 : ℝ) ≤ t := t.2
  rw [max_eq_left ht, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  congr 3
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le ht] at hu
  simp [max_eq_left hu.1]

theorem bm_isBrownian : IsBrownianReal (fun (t : ℝ≥0) ω => bmProc lam σ G (t : ℝ) ω) P :=
  ⟨bm_isPreBrownian hN hv hlam hσ, bm_cont hN hv hlam hσ⟩

theorem bm_indep : IndepFun Y (fun ω (t : ℝ≥0) => bmProc lam σ G (t : ℝ) ω) P := by
  have hproc : IsGaussianProcess (Sum.elim (fun _ : Unit => Y) (fun (t : ℝ≥0) ω => bmProc lam σ G (t : ℝ) ω)) P := by
    have := (isGaussianProcess_wProc hN hv hlam hσ).comp_right
      (fun p : Unit ⊕ ℝ≥0 => Sum.elim (fun _ => (none : Option ℝ≥0)) some p)
    convert this using 1
    funext p ω
    cases p <;> rfl
  have hY := (hN.proc.hasGaussianLaw_eval none).aemeasurable
  have := hproc.indepFun_of_covariance_eq_zero (X := fun _ : Unit => Y)
    (Y := fun (t : ℝ≥0) ω => bmProc lam σ G (t : ℝ) ω) (fun _ => hY)
    (fun t => (bm_single_gauss hN hv hlam hσ (NNReal.coe_nonneg t)).aemeasurable) (fun _ t => ?_)
  · have := this.comp (φ := fun f : Unit → ℝ => f ()) (ψ := id) (measurable_pi_apply (X := fun _ : Unit => ℝ) ()) measurable_id
    exact this
  · have h1 := hN.memLpY
    have h2 := (bm_single_gauss hN hv hlam hσ (NNReal.coe_nonneg t)).memLp_two
    change cov[Y, bmProc lam σ G (t : ℝ); P] = 0
    rw [covariance_eq_sub h1 h2]
    simp only [Pi.mul_apply]
    rw [bm_cov_YB hN hv hlam hσ (NNReal.coe_nonneg t), bm_single_mean hN hv hlam hσ (NNReal.coe_nonneg t)]
    simp

end BMproc

end Qch

end HRS
