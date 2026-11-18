/-
# HRS.Equilibrium.Q84dAuxD — packet Q84d: the canonical Gibbs measure as a density against Haar

The Gibbs density `q = exp(-βH)` is bounded, positive and, for any family of pairs `T`, dominated by
`C ∏_{p∈T} exp(-(β/N) g(x_{p₁} - x_{p₂}))` (all other pair interactions are bounded below).
`Integrable F P ↔ Integrable (q F) volume`.
-/
import HRS.Equilibrium.Q84dAuxC

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ}

/-- The set of unordered pairs `{i<j}` of labels. -/
def pairsN (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

theorem q84d_H_eq (g V : Torus d → ℝ) {N : ℕ} (X : Config d N) :
    canonicalHamiltonian g V X =
      ∑ i, V (X i) + (1 / (N : ℝ)) * ∑ p ∈ pairsN N, g (X p.1 - X p.2) := by
  unfold canonicalHamiltonian pairsN
  congr 2
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem q84d_H_lower {g V : Torus d → ℝ} {B Vm : ℝ} (hB : 0 ≤ B) (hg : ∀ z, -B ≤ g z)
    (hV : ∀ x, |V x| ≤ Vm) {N : ℕ} (hN : 1 ≤ N) (T : Finset (Fin N × Fin N))
    (hT : T ⊆ pairsN N) (X : Config d N) :
    -((N : ℝ) * Vm + N * B) + (1 / (N : ℝ)) * ∑ p ∈ T, g (X p.1 - X p.2) ≤
      canonicalHamiltonian g V X := by
  rw [q84d_H_eq]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : -((N : ℝ) * Vm) ≤ ∑ i, V (X i) := by
    have : ∑ _i : Fin N, (-Vm) ≤ ∑ i, V (X i) :=
      Finset.sum_le_sum fun i _ => (neg_le_of_abs_le (hV (X i)))
    simpa using this
  have h2 : ∑ p ∈ T, g (X p.1 - X p.2) - (N : ℝ) * N * B ≤ ∑ p ∈ pairsN N, g (X p.1 - X p.2) := by
    rw [← Finset.sum_sdiff hT]
    have h3 : ∑ _p ∈ pairsN N \ T, (-B) ≤ ∑ p ∈ pairsN N \ T, g (X p.1 - X p.2) :=
      Finset.sum_le_sum fun p _ => hg _
    have h4 : (((pairsN N \ T).card : ℕ) : ℝ) ≤ (N : ℝ) * N := by
      have : (pairsN N \ T).card ≤ N * N := by
        calc (pairsN N \ T).card ≤ (pairsN N).card := Finset.card_le_card Finset.sdiff_subset
          _ ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_filter_le _ _
          _ = N * N := by simp
      exact_mod_cast this
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    nlinarith
  have h5 : (1 / (N : ℝ)) * (∑ p ∈ T, g (X p.1 - X p.2) - (N : ℝ) * N * B) ≤
      (1 / (N : ℝ)) * ∑ p ∈ pairsN N, g (X p.1 - X p.2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : (1 / (N : ℝ)) * (∑ p ∈ T, g (X p.1 - X p.2) - (N : ℝ) * N * B) =
      (1 / (N : ℝ)) * ∑ p ∈ T, g (X p.1 - X p.2) - N * B := by
    field_simp
  linarith

theorem q84d_q_le {g V : Torus d → ℝ} {B Vm : ℝ} (hB : 0 ≤ B) (hg : ∀ z, -B ≤ g z)
    (hV : ∀ x, |V x| ≤ Vm) {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (T : Finset (Fin N × Fin N))
    (hT : T ⊆ pairsN N) (X : Config d N) :
    Real.exp (-β * canonicalHamiltonian g V X) ≤
      Real.exp (β * ((N : ℝ) * Vm + N * B)) *
        ∏ p ∈ T, Real.exp (-(β / N) * g (X p.1 - X p.2)) := by
  have h := q84d_H_lower hB hg hV hN T hT X
  rw [← Real.exp_sum, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have e : ∑ p ∈ T, -(β / N) * g (X p.1 - X p.2) = -β * ((1 / (N : ℝ)) * ∑ p ∈ T, g (X p.1 - X p.2)) := by
    rw [← Finset.mul_sum]; ring
  rw [e]
  nlinarith

/-! ### Measure-theoretic facts about `canonicalGibbs` -/

section Gibbs

variable {g V : Torus d → ℝ} {N : ℕ} {β : ℝ}

theorem q84d_measurable_H (hgm : Measurable g) (hVm : Measurable V) :
    Measurable (fun X : Config d N => canonicalHamiltonian g V X) := by
  unfold canonicalHamiltonian
  refine (Finset.measurable_sum _ fun i _ => hVm.comp (measurable_pi_apply i)).add
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))
  exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem q84d_measurable_q (hgm : Measurable g) (hVm : Measurable V) :
    Measurable (fun X : Config d N => Real.exp (-β * canonicalHamiltonian g V X)) :=
  Real.measurable_exp.comp (measurable_const.mul (q84d_measurable_H hgm hVm))

theorem q84d_q_integrable (hgm : Measurable g) (hVm : Measurable V) {c : ℝ}
    (hlow : ∀ X : Config d N, -c ≤ canonicalHamiltonian g V X) (hβ : 0 ≤ β) :
    Integrable (fun X : Config d N => Real.exp (-β * canonicalHamiltonian g V X)) := by
  refine Integrable.mono' (integrable_const (Real.exp (β * c))) (q84d_measurable_q hgm hVm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hlow X]

theorem q84d_Z_pos (hgm : Measurable g) (hVm : Measurable V) {c : ℝ}
    (hlow : ∀ X : Config d N, -c ≤ canonicalHamiltonian g V X) (hβ : 0 ≤ β) :
    0 < canonicalPartition g V N β := by
  unfold canonicalPartition
  refine (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    (q84d_q_integrable hgm hVm hlow hβ)).mpr ?_
  have : Function.support (fun X : Config d N =>
      Real.exp (-β * canonicalHamiltonian g V X)) = Set.univ := by
    ext X; simp [(Real.exp_pos _).ne']
  rw [this]; simp

theorem q84d_gibbs_isProb (hgm : Measurable g) (hVm : Measurable V) {c : ℝ}
    (hlow : ∀ X : Config d N, -c ≤ canonicalHamiltonian g V X) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (canonicalGibbs g V N β) := by
  have hint := q84d_q_integrable hgm hVm hlow hβ
  have hZ := q84d_Z_pos hgm hVm hlow hβ
  refine ⟨?_⟩
  unfold canonicalGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  have := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
  unfold canonicalPartition at hZ ⊢
  rw [← this]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top

theorem q84d_gibbs_ac :
    canonicalGibbs g V N β ≪ (volume : Measure (Config d N)) := by
  unfold canonicalGibbs
  exact (withDensity_absolutelyContinuous _ _).smul_left _

theorem q84d_integrable_gibbs_iff (hgm : Measurable g) (hVm : Measurable V) {c : ℝ}
    (hlow : ∀ X : Config d N, -c ≤ canonicalHamiltonian g V X) (hβ : 0 ≤ β)
    {F : Config d N → ℝ} :
    Integrable F (canonicalGibbs g V N β) ↔
      Integrable (fun X => Real.exp (-β * canonicalHamiltonian g V X) * F X) volume := by
  have hZ := q84d_Z_pos hgm hVm hlow hβ
  unfold canonicalGibbs
  rw [integrable_smul_measure (by simpa using hZ) (by simpa using hZ)]
  have hm : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))) :=
    ENNReal.measurable_ofReal.comp (q84d_measurable_q hgm hVm)
  rw [integrable_withDensity_iff_integrable_smul' hm (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  refine integrable_congr (Filter.Eventually.of_forall fun X => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem q84d_integral_gibbs (hgm : Measurable g) (hVm : Measurable V) {c : ℝ}
    (hlow : ∀ X : Config d N, -c ≤ canonicalHamiltonian g V X) (hβ : 0 ≤ β)
    (F : Config d N → ℝ) :
    ∫ X, F X ∂(canonicalGibbs g V N β) =
      (canonicalPartition g V N β)⁻¹ *
        ∫ X, Real.exp (-β * canonicalHamiltonian g V X) * F X := by
  have hZ := q84d_Z_pos hgm hVm hlow hβ
  unfold canonicalGibbs
  have hm : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))) :=
    ENNReal.measurable_ofReal.comp (q84d_measurable_q hgm hVm)
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  have : ((ENNReal.ofReal (canonicalPartition g V N β))⁻¹).toReal = (canonicalPartition g V N β)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  rw [this]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

end Gibbs

end HRS.Q84d

end
