import HRS.MS.MainRdStatAux5
import HRS.Main.A8PAux11

/-!
# SA2, packet 6a: the deterministic covariance density on `ℝ^d`

`sa2SigBar ts U ρ c`: `Σ̄_r^{ab} = 1_{0 ≤ r < min(t_a,t_b)} c ∫ (∑_j U_{a,j}(r,x) U_{b,j}(r,x)) ρ(r,x) dx`, for bounded jointly measurable
gradient components `U` and probability densities `ρ_r` (all `r`): measurable, entrywise bounded, positive semidefinite, hence `IsDetCovMatrix`.
(Copy of `a8pSigBar` of the torus engine with `Torus d` replaced by `ℝ^d` and the probability measure of the torus by `∫ρ = 1`.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d q : ℕ}

theorem sa2_probDensity_integrable {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

def sa2SigBar (ts : Fin q → ℝ) (U : Fin q → Fin d → ℝ → Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (c : ℝ)
    (r : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun a b => if 0 ≤ r ∧ r < min (ts a) (ts b) then
    c * ∫ x, (∑ j, U a j r x * U b j r x) * ρ r x else 0

section SigBar

variable {ts : Fin q → ℝ} {U : Fin q → Fin d → ℝ → Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} {c : ℝ}

theorem sa2_sigBar_integrand_meas (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) (a b : Fin q) :
    Measurable fun p : ℝ × Euc d => (∑ j, U a j p.1 p.2 * U b j p.1 p.2) * ρ p.1 p.2 :=
  (Finset.measurable_sum _ fun j _ => (hUm a j).mul (hUm b j)).mul hρm

theorem sa2_sum_bound {B : Fin q → ℝ} (hUb : ∀ a j r x, |U a j r x| ≤ B a) (a b : Fin q) (r : ℝ)
    (x : Euc d) : |∑ j, U a j r x * U b j r x| ≤ d * (B a * B b) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |U a j r x * U b j r x| ≤ ∑ _j : Fin d, B a * B b := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hUb a j r x) (hUb b j r x) (abs_nonneg _) ((abs_nonneg _).trans (hUb a j r x))
    _ = d * (B a * B b) := by simp

theorem sa2_sigBar_integrable (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : Fin q → ℝ} (hUb : ∀ a j r x, |U a j r x| ≤ B a)
    (hρ : ∀ r, HRS.Whole.IsProbDensity (ρ r)) (a b : Fin q) (r : ℝ) :
    Integrable (fun x => (∑ j, U a j r x * U b j r x) * ρ r x) := by
  have hρi := sa2_probDensity_integrable (hρ r)
  refine Integrable.bdd_mul (c := (d : ℝ) * (B a * B b)) hρi
    (((Finset.measurable_sum _ fun j _ => (hUm a j).mul (hUm b j)).comp measurable_prodMk_left
      ).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact sa2_sum_bound hUb a b r x

theorem sa2_sigBar_entry_bound (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hUb : ∀ a j r x, |U a j r x| ≤ B a)
    (hρ : ∀ r, HRS.Whole.IsProbDensity (ρ r)) (a b : Fin q) (r : ℝ) :
    |sa2SigBar ts U ρ c r a b| ≤ |c| * (d * (B a * B b)) := by
  unfold sa2SigBar
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hρi := sa2_probDensity_integrable (hρ r)
    have hint := sa2_sigBar_integrable hUm hρm hUb hρ a b r
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |(∑ j, U a j r x * U b j r x) * ρ r x|
        ≤ ∫ x, (d * (B a * B b)) * ρ r x := by
          refine integral_mono hint.abs (hρi.const_mul _) fun x => ?_
          rw [abs_mul, abs_of_nonneg ((hρ r).nonneg x)]
          exact mul_le_mul_of_nonneg_right (sa2_sum_bound hUb a b r x) ((hρ r).nonneg x)
      _ = d * (B a * B b) := by rw [integral_const_mul, (hρ r).integral_one, mul_one]
  · simp only [abs_zero]
    have := hB0 a
    have := hB0 b
    positivity

theorem sa2_sigBar_entry_meas (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) (a b : Fin q) :
    Measurable fun r => sa2SigBar ts U ρ c r a b := by
  have hI : Measurable fun r : ℝ => ∫ x, (∑ j, U a j r x * U b j r x) * ρ r x := by
    have hsm : StronglyMeasurable fun p : ℝ × Euc d => (∑ j, U a j p.1 p.2 * U b j p.1 p.2) * ρ p.1 p.2 :=
      (sa2_sigBar_integrand_meas hUm hρm a b).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  unfold sa2SigBar
  simp only [Matrix.of_apply]
  refine Measurable.ite ?_ (measurable_const.mul hI) measurable_const
  exact (measurableSet_le measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)

theorem sa2_sigBar_meas (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) : Measurable (sa2SigBar ts U ρ c) :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => sa2_sigBar_entry_meas hUm hρm a b

theorem sa2_sigBar_psd (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : Fin q → ℝ} (hUb : ∀ a j r x, |U a j r x| ≤ B a)
    (hρ : ∀ r, HRS.Whole.IsProbDensity (ρ r)) (hc : 0 ≤ c) (r : ℝ) :
    (sa2SigBar ts U ρ c r).PosSemidef := by
  by_cases hr : 0 ≤ r
  swap
  · have : sa2SigBar ts U ρ c r = 0 := by
      ext a b
      simp [sa2SigBar, hr]
    rw [this]
    exact Matrix.PosSemidef.zero
  set g : Fin q → Fin d → Euc d → ℝ := fun a j x => if r < ts a then U a j r x else 0 with hg
  have hent : ∀ a b, sa2SigBar ts U ρ c r a b = c * ∫ x, (∑ j, g a j x * g b j x) * ρ r x := by
    intro a b
    unfold sa2SigBar
    simp only [Matrix.of_apply, hg]
    by_cases h1 : r < ts a
    · by_cases h2 : r < ts b
      · simp only [h1, h2, if_true, if_pos (show 0 ≤ r ∧ r < min (ts a) (ts b) from ⟨hr, lt_min h1 h2⟩)]
      · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h2 (lt_of_lt_of_le h.2 (min_le_right _ _))
        simp [h2, this]
    · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h1 (lt_of_lt_of_le h.2 (min_le_left _ _))
      simp [h1, this]
  have hgm : ∀ a j, Measurable (g a j) := by
    intro a j
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact (hUm a j).comp measurable_prodMk_left
    · simp only [hg, if_neg h]; exact measurable_const
  have hgb : ∀ a j x, |g a j x| ≤ |B a| := by
    intro a j x
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact (hUb a j r x).trans (le_abs_self _)
    · simp only [hg, if_neg h, abs_zero]; exact abs_nonneg _
  have hint : ∀ a b, Integrable (fun x => (∑ j, g a j x * g b j x) * ρ r x) := by
    intro a b
    have hρi := sa2_probDensity_integrable (hρ r)
    refine Integrable.bdd_mul (c := (d : ℝ) * (|B a| * |B b|)) hρi
      ((Finset.measurable_sum _ fun j _ => (hgm a j).mul (hgm b j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin d, |g a j x * g b j x| ≤ ∑ _j : Fin d, |B a| * |B b| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hgb a j x) (hgb b j x) (abs_nonneg _) (abs_nonneg _)
      _ = d * (|B a| * |B b|) := by simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    have hsym : ∀ y, (∑ j, g b j y * g a j y) = ∑ j, g a j y * g b j y :=
      fun y => Finset.sum_congr rfl fun j _ => mul_comm _ _
    simp only [star_trivial, hent, hsym]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, hent]
    have e2 : ∑ a, x a * ∑ b, c * (∫ y, (∑ j, g a j y * g b j y) * ρ r y) * x b =
        c * ∫ y, ∑ a, ∑ b, (x a * x b) * ((∑ j, g a j y * g b j y) * ρ r y) := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hint a b).const_mul _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]; ring
    rw [e2]
    refine mul_nonneg hc (integral_nonneg fun y => ?_)
    have : ∑ a, ∑ b, (x a * x b) * ((∑ j, g a j y * g b j y) * ρ r y) =
        (∑ j, (∑ a, x a * g a j y) ^ 2) * ρ r y := by
      have e1 : ∀ a b, (x a * x b) * ((∑ j, g a j y * g b j y) * ρ r y) =
          ∑ j, (x a * g a j y) * (x b * g b j y) * ρ r y := by
        intro a b
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have e2 : ∀ j, (∑ a, x a * g a j y) ^ 2 * ρ r y =
          ∑ a, ∑ b, (x a * g a j y) * (x b * g b j y) * ρ r y := by
        intro j
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_mul]
      simp_rw [e1]
      rw [Finset.sum_mul]
      simp_rw [e2]
      calc ∑ a, ∑ b, ∑ j, (x a * g a j y) * (x b * g b j y) * ρ r y
          = ∑ a, ∑ j, ∑ b, (x a * g a j y) * (x b * g b j y) * ρ r y :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ j, ∑ a, ∑ b, (x a * g a j y) * (x b * g b j y) * ρ r y := Finset.sum_comm
    rw [this]
    exact mul_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) ((hρ r).nonneg y)

theorem sa2_sigBar_isDet (hUm : ∀ a j, Measurable fun p : ℝ × Euc d => U a j p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hUb : ∀ a j r x, |U a j r x| ≤ B a) (hρ : ∀ r, HRS.Whole.IsProbDensity (ρ r)) (hc : 0 ≤ c) (T : ℝ) :
    IsDetCovMatrix T (sa2SigBar ts U ρ c) := by
  refine ⟨sa2_sigBar_meas hUm hρm, fun σ _ => sa2_sigBar_psd hUm hρm hUb hρ hc σ, ?_⟩
  have hm : Measurable fun σ => s1Norm (sa2SigBar ts U ρ c σ) :=
    measurable_traceNormMatrix (sa2SigBar ts U ρ c) (fun i j => sa2_sigBar_entry_meas hUm hρm i j)
  refine Integrable.mono' (g := fun _ => ∑ a : Fin q, ∑ b : Fin q, |c| * (d * (B a * B b)))
    (integrable_const _) hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ _ => ?_)
  rw [Real.norm_of_nonneg (traceNormMatrix_nonneg _)]
  exact (HRS.Main.A8P.a8p_s1Norm_le_sum _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    sa2_sigBar_entry_bound hUm hρm hB0 hUb hρ a b σ)

end SigBar

end HRS.MS.MainRdStat
