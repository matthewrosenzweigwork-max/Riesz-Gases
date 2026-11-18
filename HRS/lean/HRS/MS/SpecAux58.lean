import HRS.MS.SpecAux57
import HRS.MS.QsfFeat1
import HRS.Stochastic.Ito
import HRS.Prob.MRepAux3

/-!
# S8R: the empirical integrand `Φ` is a progressive Hilbert-Schmidt integrand (S8.7, packet C3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_Fq_eq_sum`, `s8p_good_iff`: `Fq x = ∑_a ∑_l (cs x a l)²` and `good x ↔ Fq x < ∞`;
* `s8p_measurable_Gv`: `x ↦ s8p_Gv x a` is Borel measurable into `ℓ²`;
* `s8p_isHSIntegrand`: for the stationary realization, `IsHSIntegrand P ℱ T Φ` for every `T`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s8p_Fq_eq_sum (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) :
    s8p_Fq om e τ x = ∑ a, ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) := by
  unfold s8p_Fq
  rw [← Summable.tsum_finsetSum (fun a _ => ENNReal.summable)]
  refine tsum_congr fun l => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
  congr 1
  have h2 := s8p_cs_mul_sum om e τ x l l
  have h3 : Real.exp (-(τ * (om l + om l)) / 2) = Real.exp (-τ * om l) := by
    congr 1; ring
  rw [h3] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun a _ => (sq _).symm

theorem s8p_good_iff (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) :
    s8p_good om e τ x ↔ s8p_Fq om e τ x < ⊤ := by
  constructor
  · intro h
    rw [s8p_Fq_eq_sum]
    refine ENNReal.sum_lt_top.2 fun a _ => ?_
    have hs : Summable fun l => s8p_cs om e τ x a l ^ 2 := memℓp_two_iff.1 (h a)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) hs]
    exact ENNReal.ofReal_lt_top
  · exact s8p_good_of_Fq_lt_top

theorem s8p_memℓp_iff (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) (a : Fin d) :
    Memℓp (s8p_cs om e τ x a) 2 ↔ ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) < ⊤ := by
  rw [memℓp_two_iff]
  constructor
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) hs]
    exact ENNReal.ofReal_lt_top
  · intro h
    have := ENNReal.summable_toReal h.ne
    exact this.congr fun l => ENNReal.toReal_ofReal (sq_nonneg _)

theorem s8p_measurable_Gv {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ} (he : ∀ l, ContDiff ℝ ∞ (e l)) (τ : ℝ)
    (a : Fin d) : Measurable fun x => s8p_Gv om e τ x a := by
  have hcm : ∀ l, Measurable fun x : Euc d => s8p_cs om e τ x a l := fun l => by
    unfold s8p_cs
    exact measurable_const.mul
      (((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.comp (s8p_continuous_gradient (he l))).measurable)
  have hFa : Measurable fun x : Euc d => ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) :=
    Measurable.ennreal_tsum fun l => ENNReal.measurable_ofReal.comp ((hcm l).pow_const 2)
  have hG : MeasurableSet {x : Euc d | ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) < ⊤} :=
    measurableSet_lt hFa measurable_const
  have hgm : ∀ n : ℕ, Measurable (fun x : Euc d => if ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) < ⊤ then
      ∑ l ∈ Finset.range n, S45.s45_e1 l (s8p_cs om e τ x a l) else (0 : SeqL2)) := by
    intro n
    refine Measurable.ite hG ?_ measurable_const
    refine Finset.measurable_sum _ fun l _ => ?_
    rw [show (fun x : Euc d => S45.s45_e1 l (s8p_cs om e τ x a l)) =
        fun x => s8p_cs om e τ x a l • S45.s45_e1 l 1 from funext fun x => S45.s45_e1_eq l _]
    exact (hcm l).smul_const _
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun x => ?_)
  by_cases hx : ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) < ⊤
  · simp only [hx, if_true]
    have hgood : Memℓp (s8p_cs om e τ x a) 2 := (s8p_memℓp_iff om e τ x a).2 hx
    have hs := lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by simp)
      (show lp (fun _ : ℕ => ℝ) 2 from s8p_Gv om e τ x a)
    have heq : (fun l : ℕ => S45.s45_e1 l (s8p_cs om e τ x a l)) = fun l => lp.single (E := fun _ : ℕ => ℝ) 2 l
        ((show lp (fun _ : ℕ => ℝ) 2 from s8p_Gv om e τ x a) l) := by
      funext l
      unfold S45.s45_e1
      congr 1
      exact (u11_coord_ofSeq hgood l).symm
    have ht := hs.tendsto_sum_nat
    rw [← heq] at ht
    exact ht
  · simp only [hx, if_false]
    have hbad : ¬ Memℓp (s8p_cs om e τ x a) 2 := fun hm => hx ((s8p_memℓp_iff om e τ x a).1 hm)
    have : s8p_Gv om e τ x a = 0 := by
      unfold s8p_Gv SeqL2.ofSeq
      exact dif_neg hbad
    rw [this]
    exact tendsto_const_nhds

end HRS.MS.Spec
