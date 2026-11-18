import HRS.Whole.CriticalNoise
import HRS.MS.QsfStat1
import HRS.MS.WsStatAux13
import HRS.MS.SpecAux52

/-!
# S8.1 (worker S81Q): the linear input `LinearInputBounds` of a measurable configuration with the canonical law

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

`s81q_linear_input`: there is `Cs ≥ 0` (before `ρ`, `N`, `P`, `Y`) such that every measurable configuration `Y : Ω → (ℝ^d)^N` whose law is the
canonical Gibbs law `P_{N,β}` of the critical quadratic model satisfies `LinearInputBounds d (d/2) N (withDensityReal ρ) Cs P Y` for the thermal
density `ρ`.  The variance bound of `S45Static` is stated for the canonical law itself, for every `f ∈ L²(μ)` (not necessarily measurable); it is
transferred to `P` through the a.e.-identification of `f` with a measurable `f'` (the first marginal has a bounded density with respect to `μ`)
and `s21_evariance_map`.  This is the hypothesis `hlin`/`hvar` of the finite-noise producer `s81p_finite_noise` and of `s88_particle_decay`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81Q

variable {d : ℕ}

theorem s81q_linear_input (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
      ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y : Ω → EucConfig d N), Measurable Y →
        law P Y = HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β →
        LinearInputBounds d ((d : ℝ) / 2) N (HRS.Whole.withDensityReal ρβ) Cs P Y := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨Cs, hCs0, hStat⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  refine ⟨Cs, hCs0, fun ρβ hρβ N hN Ω _ P _ Y hY hlaw => ?_⟩
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β :=
    HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ
  have hμeq : HRS.Whole.withDensityReal ρβ = thermalMeasure d ((d : ℝ) / 2) a β := by
    rw [hρeq]; rfl
  have hSN := hStat N hN
  haveI hPcp : IsProbabilityMeasure
      (HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β) := hSN.prob
  have hN0 : 0 < N := by omega
  rw [hμeq]
  refine ⟨?_, ?_⟩
  · rw [hlaw]
    obtain ⟨φ, hφm, hφ, hφb, hφL, hφn⟩ := hSN.marg
    exact ⟨φ, hφm, hφ, hφb, hφL, hφn⟩
  · intro f hf
    obtain ⟨φ, hφm, hφ, -, -, -⟩ := hSN.marg
    set Pc := HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β with hPc
    set μ := thermalMeasure d ((d : ℝ) / 2) a β with hμ
    -- a measurable modification of `f`
    set f' : Euc d → ℝ := hf.aestronglyMeasurable.mk f with hf'
    have hf'm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hff' : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
    have hf'L : MemLp f' 2 μ := hf.ae_eq hff'
    -- each marginal is absolutely continuous with respect to `μ`
    have hac : HRS.Whole.firstMarginal Pc ≪ μ := by
      rw [hφ]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have hmarg : ∀ i : Fin N, P.map (fun z => Y z i) ≪ μ := by
      intro i
      have e : P.map (fun z => Y z i) = HRS.Whole.firstMarginal Pc := by
        have h1 : P.map (fun z => Y z i) = (P.map Y).map (fun X => X i) := by
          rw [Measure.map_map (measurable_pi_apply i) hY]; rfl
        rw [h1]
        have := HRS.MS.Spec.s8p_map_eval hN0 hSN.exch i
        rw [show P.map Y = Pc from hlaw]
        exact this
      rw [e]; exact hac
    have hae : ∀ i : Fin N, (fun z => f (Y z i)) =ᵐ[P] fun z => f' (Y z i) := by
      intro i
      have h1 : ∀ᵐ x ∂(P.map (fun z => Y z i)), f x = f' x := (hmarg i).ae_le hff'
      exact ae_of_ae_map ((measurable_pi_apply i).comp hY).aemeasurable h1
    have hls : (fun z => HRS.Whole.linStat f (Y z)) =ᵐ[P] fun z => HRS.Whole.linStat f' (Y z) := by
      have hall : ∀ᵐ z ∂P, ∀ i : Fin N, f (Y z i) = f' (Y z i) := ae_all_iff.2 hae
      filter_upwards [hall] with z hz
      unfold HRS.Whole.linStat HRS.Whole.pair HRS.Whole.empirical
      rw [integral_smul_measure, integral_smul_measure, integral_finset_sum_measure,
        integral_finset_sum_measure]
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_dirac, integral_dirac]
        exact hz i
      · intro i _; exact integrable_dirac (by simp)
      · intro i _; exact integrable_dirac (by simp)
    rw [evariance_congr hls, HRS.MS.S21.s21_evariance_map P Y hY (HRS.Whole.linStat f')
      (HRS.MS.Spec.s8p_measurable_linStat hN0 hf'm), show P.map Y = Pc from hlaw]
    have h2 := hSN.linear f' hf'L
    have h3 : ∫ x, f' x ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ :=
      integral_congr_ae (hff'.symm.mono fun x hx => by simp only [hx])
    rw [h3] at h2
    exact h2

end HRS.Whole.S81Q
