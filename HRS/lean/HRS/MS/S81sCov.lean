import HRS.MS.GenPathAux45
import HRS.MS.GenPathAux46
import HRS.MS.S81sSetup

/-!
# S8.1 (worker S81S): the covariation integral of a feature covariance density is the noise covariance

`s81s_cdet_noiseCov`: if a deterministic covariance density `Cdet` of the `𝒦`-space is given on `[0,T]` by the feature form
`featureForm m T q (Γ_{σ,·}) (withDensityReal (S.ρ N σ))`, then `∫_0^{t_a ∧ t_b} Cdet_σ(y_a, y_b) dσ = noiseCovW (S.coeff N) q t_a t_b φ_a φ_b`
for the pairing vectors `y_a = s52y1 m T t_a α_a` (copy of `s56_noiseCov_eq` with the form hypothesis in place of `s56Db_spec`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S81S

open HRS HRS.Whole HRS.MS.S52 HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

theorem s81s_cdet_noiseCov (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T)
    (Cdet : ℝ → KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ) (q : ℝ)
    (hform : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ u v, Cdet r u v = featureForm b.m b.T q
      (fun i => gradFeature (S.coeff N) b.m b.T i r) (HRS.Whole.withDensityReal (S.ρ N r)) u v)
    {ta tb : ℝ} (hta : ta ∈ Set.Icc (0 : ℝ) b.T) (htb : tb ∈ Set.Icc (0 : ℝ) b.T)
    (αa αb : MultiIndex d) :
    ∫ σ in Set.Icc (0 : ℝ) (min ta tb), Cdet σ (s52y1 b.m b.T ta αa) (s52y1 b.m b.T tb αb) =
      noiseCovW (S.coeff N) q ta tb (oscTestFun b.m αa) (oscTestFun b.m αb) := by
  unfold noiseCovW
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have hσa : σ ≤ ta := hσ.2.trans (min_le_left _ _)
  have hσb : σ ≤ tb := hσ.2.trans (min_le_right _ _)
  have hσT : σ ∈ Set.Icc (0 : ℝ) b.T := ⟨hσ.1, hσa.trans hta.2⟩
  have hcla := s56_osc_classical b hbv S N hta αa
  have hclb := s56_osc_classical b hbv S N htb αb
  obtain ⟨Ba, hBa⟩ := s56_gradComp_bdd hcla
  obtain ⟨Bb, hBb⟩ := s56_gradComp_bdd hclb
  have hρ := (S.mf N).density σ hσT
  rw [hform σ hσT]
  unfold featureForm
  have hpair : ∀ (c : Fin d) (x : Euc d), inner ℝ (gradFeature (S.coeff N) b.m b.T c σ x) (s52y1 b.m b.T ta αa) *
      inner ℝ (gradFeature (S.coeff N) b.m b.T c σ x) (s52y1 b.m b.T tb αb) =
      gradComp c (propagatorW (S.coeff N) σ ta (oscTestFun b.m αa)) x *
        gradComp c (propagatorW (S.coeff N) σ tb (oscTestFun b.m αb)) x := by
    intro c x
    rw [s52_pair_grad_y1 hC hta.2 c hσT x αa, s52_pair_grad_y1 hC htb.2 c hσT x αb, if_pos hσa, if_pos hσb]
  simp_rw [hpair]
  have hint : ∀ c : Fin d, Integrable (fun x => S.ρ N σ x *
      (gradComp c (propagatorW (S.coeff N) σ ta (oscTestFun b.m αa)) x *
        gradComp c (propagatorW (S.coeff N) σ tb (oscTestFun b.m αb)) x)) volume := by
    intro c
    refine Integrable.mono' (g := fun x => (|Ba| * |Bb|) * |S.ρ N σ x|) ?_ ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((s56_integrable_of_prob hρ).abs).const_mul _
    · have hca := s56_gradComp_cont ((hcla.c2 σ ⟨hσ.1, hσa⟩).of_le (by norm_num)) c
      have hcb := s56_gradComp_cont ((hclb.c2 σ ⟨hσ.1, hσb⟩).of_le (by norm_num)) c
      exact (hρ.measurable.mul (hca.mul hcb).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hBa σ ⟨hσ.1, hσa⟩ c x
      have h2 := hBb σ ⟨hσ.1, hσb⟩ c x
      have h3 : |gradComp c (propagatorW (S.coeff N) σ ta (oscTestFun b.m αa)) x| ≤ |Ba| := h1.trans (le_abs_self _)
      have h4 : |gradComp c (propagatorW (S.coeff N) σ tb (oscTestFun b.m αb)) x| ≤ |Bb| := h2.trans (le_abs_self _)
      calc |S.ρ N σ x| * (|gradComp c (propagatorW (S.coeff N) σ ta (oscTestFun b.m αa)) x| *
            |gradComp c (propagatorW (S.coeff N) σ tb (oscTestFun b.m αb)) x|)
          ≤ |S.ρ N σ x| * (|Ba| * |Bb|) := by gcongr
        _ = _ := by ring
  congr 1
  simp_rw [mrr_integral_withDensityReal _ hρ.measurable hρ.nonneg]
  rw [← integral_finsetSum _ (fun c _ => hint c)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∑ c : Fin d, S.ρ N σ x * (gradComp c (propagatorW (S.coeff N) σ ta (oscTestFun b.m αa)) x *
      gradComp c (propagatorW (S.coeff N) σ tb (oscTestFun b.m αb)) x) =
    inner ℝ (gradient (propagatorW (S.coeff N) σ ta (oscTestFun b.m αa)) x)
      (gradient (propagatorW (S.coeff N) σ tb (oscTestFun b.m αb)) x) * S.ρ N σ x
  rw [PiLp.inner_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [gradComp, RCLike.inner_apply, conj_trivial]
  ring

end HRS.Whole.S81S
