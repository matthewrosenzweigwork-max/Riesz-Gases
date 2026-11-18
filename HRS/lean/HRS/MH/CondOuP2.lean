import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs
import HRS.Main.MeanPartMetricEval

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

theorem p_cp2_cos_shift (k : Lattice d) (j : Fin d) (hj : k j ≠ 0) (x : Torus d) :
    Torus.cosMode k (Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) + x) =
      - Torus.cosMode k x := by
  have hj' : (k j : ℝ) ≠ 0 := by exact_mod_cast hj
  conv_lhs => rw [← Torus.mk_rep x, ← Torus.mk_add, Torus.cosMode_mk]
  conv_rhs => rw [← Torus.mk_rep x, Torus.cosMode_mk]
  rw [Torus.dot_add]
  have : Lattice.dot k (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) = 1/2 := by
    simp only [Lattice.dot, EuclideanSpace.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    field_simp
  rw [this, mul_add, show 2 * Real.pi * (1/2 : ℝ) = Real.pi by ring, add_comm Real.pi,
    Real.cos_add_pi]

theorem condou_pair_firstMarginal_cos {s : ℝ} (β : ℝ) (k : Lattice d) (hk : k ≠ 0) {N : ℕ} :
    pair (firstMarginal (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β)) (PDE.cosTest k) = 0 := by
  unfold firstMarginal
  by_cases hN : 0 < N
  · rw [dif_pos hN]
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hk (funext h)
    set G := canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β with hG
    set t : Torus d := Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) with ht
    have hc : Continuous (PDE.cosTest k) :=
      continuous_const.mul (Complex.continuous_re.comp (Torus.continuous_mode _))
    have hinv : G.map (shiftEquiv t : Config d N ≃ᵐ Config d N) = G :=
      HRS.StaticLimitsAux.gibbs_inv (d := d) (N := N) (periodicRiesz d s) 0 β t
    have e1 : pair (G.map (fun X => X ⟨0, hN⟩)) (PDE.cosTest k) = ∫ X, PDE.cosTest k (X ⟨0, hN⟩) ∂G := by
      unfold pair
      exact integral_map (measurable_pi_apply _).aemeasurable hc.aestronglyMeasurable
    rw [e1]
    have e2 : ∫ X, PDE.cosTest k (X ⟨0, hN⟩) ∂G =
        ∫ X, PDE.cosTest k ((shiftEquiv t : Config d N ≃ᵐ Config d N) X ⟨0, hN⟩) ∂G := by
      exact (congrArg (fun μ => ∫ X, PDE.cosTest k (X ⟨0, hN⟩) ∂μ) hinv).symm.trans
        (integral_map_equiv (shiftEquiv t : Config d N ≃ᵐ Config d N)
          (fun X => PDE.cosTest k (X ⟨0, hN⟩)))
    have e3 : ∀ X : Config d N, PDE.cosTest k ((shiftEquiv t : Config d N ≃ᵐ Config d N) X ⟨0, hN⟩)
        = - PDE.cosTest k (X ⟨0, hN⟩) := by
      intro X
      simp only [PDE.cosTest, shiftEquiv_apply, ht, p_cp2_cos_shift k j hj, mul_neg]
    simp only [e3, integral_neg] at e2
    linarith
  · rw [dif_neg hN]
    simp [pair]

theorem condou_eval_zetaE_cosTest (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (k : Lattice d) (hk : k ≠ 0) (x : Config d N) :
    NegSobolev.eval (zetaE m (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) x) (PDE.cosTest k) =
      linCoord (volume : Measure (Torus d)) (PDE.cosTest k) x := by
  haveI : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) :=
    HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd (V := fun _ => (0 : ℝ)) (by
      exact HRS.d1_isSmooth_const 0) hβ hN
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) :=
    HRS.ME.FamV.canonicalGibbs_isExchangeable _ _ (fun x => periodicRiesz_neg x) β
  have hN0 : 0 < N := hN
  haveI := empirical_isProbabilityMeasure hN0 x
  haveI := isProbabilityMeasure_meanEmpirical
    (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) hN
  unfold zetaE
  rw [mp_eval_smul, NegSobolev.eval_ofMeasureDiff hm _ _ _ (mp_isCk_top_cosTest k),
    meanEmpirical_eq_firstMarginal _ hex hN, condou_pair_firstMarginal_cos β k hk,
    pair_empirical hN0]
  unfold linCoord pair
  rw [mp_integral_cosTest k hk]
  simp [one_div]

end HRS.MH.CondOuPackets
