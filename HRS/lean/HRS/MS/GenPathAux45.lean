import HRS.MS.GenPathAux44
import HRS.MS.MovDecAux3

/-!
# S5.6 packet P8d: the covariation integral of `Db` is the noise covariance `noiseCovW`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.MP.RdRem

variable {d : ℕ}

theorem s56_gradComp_bdd {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ (c : Fin d) (x : Euc d), |gradComp c (f r) x| ≤ B := by
  obtain ⟨B, hB⟩ := hf.bdd 1 (by norm_num)
  refine ⟨B, fun r hr c x => ?_⟩
  have h1 := hB r hr x
  rw [norm_iteratedFDeriv_one] at h1
  unfold gradComp
  calc |gradient (f r) x c| = ‖gradient (f r) x c‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖gradient (f r) x‖ := PiLp.norm_apply_le _ c
    _ = ‖fderiv ℝ (f r) x‖ := HRS.MS.MovDec.mov2e_norm_gradient _ _
    _ ≤ B := h1

theorem s56_gradComp_cont {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) (c : Fin d) : Continuous (gradComp c h) := by
  have h1 : Continuous fun z : Euc d => fderiv ℝ h z := hh.continuous_fderiv one_ne_zero
  have hg : Continuous fun z : Euc d => gradient h z := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h1
  unfold gradComp
  exact (continuous_apply c).comp ((PiLp.continuous_ofLp 2 _).comp hg)

theorem s56_integrable_of_prob {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : Integrable ρ volume := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

theorem s56_noiseCov_eq (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {ta tb : ℝ} (hta : ta ∈ Set.Icc (0 : ℝ) b.T) (htb : tb ∈ Set.Icc (0 : ℝ) b.T)
    (αa αb : MultiIndex d) :
    ∫ σ in Set.Icc (0 : ℝ) (min ta tb), s56Db b S N hOM hS q hq σ (s52y1 b.m b.T ta αa) (s52y1 b.m b.T tb αb) =
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
  rw [(s56Db_spec b S N hOM hS q hq hσT).1]
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

end HRS.MS.GenPath
