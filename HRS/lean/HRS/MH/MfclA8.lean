import HRS.MH.MfclSpec
import HRS.MD.EQTransShift
import HRS.Energy.Modulated

/-!
# Mfcl packet A8: the mean of the linear statistic `linCoord` under the canonical Gibbs law

The exchangeability lemmas `exch_*` are copies of `HRS.ME.FamV.canonicalGibbs_isExchangeable`
(`HRS/ME/FamVC.lean:28-80`), so that `HRS.ME.FamVC` (not yet built) is not imported.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main HRS.LZ HRS.MD.EQ29

theorem exch_sum_pair_identity {N : ℕ} (H : Fin N → Fin N → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∑ i, ∑ j, H i j =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j + ∑ i, H i i := by
  simp only [Finset.sum_filter]
  have hpt : ∀ i j, H i j = (if i < j then H i j else 0) + (if j < i then H i j else 0) +
      (if i = j then H i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne]; ring
    · simp
    · rw [if_neg (not_lt.2 h.le), if_pos h, if_neg h.ne']; ring
  have hB : ∑ i, ∑ j, (if j < i then H i j else 0) = ∑ i, ∑ j, (if i < j then H i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hH]
  have hD : ∑ i, ∑ j, (if i = j then H i j else 0) = ∑ i, H i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hsplit : ∑ i, ∑ j, H i j = (∑ i, ∑ j, (if i < j then H i j else 0)) +
      (∑ i, ∑ j, (if j < i then H i j else 0)) + ∑ i, ∑ j, (if i = j then H i j else 0) := by
    have hrow : ∀ i, ∑ j, H i j = (∑ j, (if i < j then H i j else 0)) +
        (∑ j, (if j < i then H i j else 0)) + ∑ j, (if i = j then H i j else 0) := fun i => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpt i j
    simp only [hrow, Finset.sum_add_distrib]
  rw [hsplit, hB, hD]
  ring

theorem exch_pairSum_perm {N : ℕ} (H : Fin N → Fin N → ℝ) (hH : ∀ i j, H i j = H j i)
    (σ : Equiv.Perm (Fin N)) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H (σ i) (σ j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j := by
  have h1 := exch_sum_pair_identity (fun i j => H (σ i) (σ j)) (fun i j => hH _ _)
  have h2 := exch_sum_pair_identity H hH
  have hF : ∑ i, ∑ j, H (σ i) (σ j) = ∑ i, ∑ j, H i j := by
    calc ∑ i, ∑ j, H (σ i) (σ j) = ∑ i, ∑ j, H (σ i) j :=
          Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (H (σ i))
      _ = ∑ i, ∑ j, H i j := Equiv.sum_comp σ (fun i => ∑ j, H i j)
  have hD : ∑ i, H (σ i) (σ i) = ∑ i, H i i := Equiv.sum_comp σ (fun i => H i i)
  linarith

theorem exch_canonicalHamiltonian_comp_perm {d N : ℕ} (g V : Torus d → ℝ) (hg : ∀ x, g (-x) = g x)
    (X : Config d N) (σ : Equiv.Perm (Fin N)) :
    HRS.canonicalHamiltonian g V (X ∘ σ) = HRS.canonicalHamiltonian g V X := by
  unfold HRS.canonicalHamiltonian
  have hH : ∀ i j : Fin N, g (X i - X j) = g (X j - X i) := fun i j => by
    rw [← hg (X i - X j), neg_sub]
  have hp := exch_pairSum_perm (fun i j => g (X i - X j)) hH σ
  have hv : ∑ i, V ((X ∘ σ) i) = ∑ i, V (X i) := Equiv.sum_comp σ (fun i => V (X i))
  have hp' : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g ((X ∘ σ) i - (X ∘ σ) j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := hp
  rw [hv, hp']

theorem exch_canonicalGibbs_isExchangeable {d N : ℕ} (g V : Torus d → ℝ) (hg : ∀ x, g (-x) = g x)
    (β : ℝ) : HRS.IsExchangeable (HRS.canonicalGibbs g V N β) := by
  intro σ
  have hmeas : AEMeasurable (fun X : Config d N => X ∘ σ)
      ((volume : Measure (Config d N)).withDensity fun X =>
        ENNReal.ofReal (Real.exp (-β * HRS.canonicalHamiltonian g V X))) :=
    (HRS.permMeasEquiv σ).measurable.aemeasurable
  have hvol : (volume : Measure (Config d N)) =
      Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) := rfl
  unfold HRS.canonicalGibbs
  rw [Measure.map_smul _ hmeas]
  congr 1
  rw [hvol]
  refine HRS.map_withDensity_perm _ σ _ fun X => ?_
  simp only [exch_canonicalHamiltonian_comp_perm g V hg X σ]

theorem integral_linCoord_gibbs_proof : type_of% @HRS.MH.Mfcl.integral_linCoord_gibbs := by
  intro d hd s hs0 hsd V hV β hβ ρβ hρβ hρs N hN
  have hN0 : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  haveI hPp : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    HRS.MD.EQTransShift.et_gibbs_prob hd hs0 hsd V hV hβ hρβ hN0
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  have hexch : HRS.IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) :=
    exch_canonicalGibbs_isExchangeable (periodicRiesz d s) V (fun x => periodicRiesz_neg x) β
  have hcont : Continuous ρβ := (HRS.MD.EQTransShift.et_smooth_bound hρs).1
  have hint : ∀ g : Config d N → ℝ, Continuous g →
      Integrable g (canonicalGibbs (periodicRiesz d s) V N β) := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hρc : ∀ i : Fin N, Continuous (fun X : Config d N => ρβ (X i)) := fun i =>
    hcont.comp (continuous_apply i)
  have hsum_c : Continuous (fun X : Config d N => ∑ i, ρβ (X i)) :=
    continuous_finset_sum _ fun i _ => hρc i
  have hA : Integrable (fun X : Config d N => 1 / (N : ℝ) * ∑ i, ρβ (X i))
      (canonicalGibbs (periodicRiesz d s) V N β) :=
    hint _ (continuous_const.mul hsum_c)
  have hlin_cont : Continuous (linCoord (withDensityReal ρβ) ρβ : Config d N → ℝ) := by
    unfold linCoord
    exact continuous_const.mul ((continuous_const.mul hsum_c).sub continuous_const)
  have hmean : ∫ X, 1 / (N : ℝ) * ∑ i, ρβ (X i) ∂(canonicalGibbs (periodicRiesz d s) V N β) =
      pair (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) ρβ := by
    have h1 := HRS.integral_meanEmpirical (canonicalGibbs (periodicRiesz d s) V N β) (f := ρβ) hcont
    rw [HRS.meanEmpirical_eq_firstMarginal _ hexch hN1] at h1
    rw [one_div, integral_const_mul, integral_finset_sum _ (fun i _ => hint _ (hρc i))]
    exact h1.symm
  have hpair : ∫ X, linCoord (withDensityReal ρβ) ρβ X ∂(canonicalGibbs (periodicRiesz d s) V N β) =
      Real.sqrt N * (pair (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) ρβ -
        pair (withDensityReal ρβ) ρβ) := by
    unfold linCoord
    rw [integral_const_mul, integral_sub hA (integrable_const _), integral_const, hmean]
    simp
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure (g := fun x : ℝ => x) aestronglyMeasurable_id hlin_cont.aemeasurable]
    exact hint _ hlin_cont
  · rw [integral_map (f := fun x : ℝ => x) hlin_cont.aemeasurable aestronglyMeasurable_id]
    show ∫ X, linCoord (withDensityReal ρβ) ρβ X ∂(canonicalGibbs (periodicRiesz d s) V N β) = _
    rw [hpair]
    rfl

end HRS.MH.MfclP
