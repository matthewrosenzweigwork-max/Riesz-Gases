import HRS.PDE.MovGAux6
import HRS.PDE.MovFAux1

/-!
# MOVG Aux7: the Gibbs normaliser and the Gibbs expectation in terms of the unnormalised density `q`

`movg_weight_eq`: off collisions `∏ρ(x_i) e^{-βN F_N} = e^{-(βN/2) c₃} q(X)`.
`movg_K_eq`: `K_N(ρ) = e^{-(βN/2) c₃} J`, `J = ∫ q`.   `movg_J_pos`.   `movg_expect_eq`: `E_{Q}[f] = (∫ q f)/J`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- The one-body factor `π = ρ e^{β g*ρ}`. -/
def movg_pi (D : DynData d) (ρ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ρ x * Real.exp (D.invβ⁻¹ * convFun (periodicRiesz d D.s) ρ x)

/-- The unnormalised density `q` on `n+1` particles. -/
def movg_qn (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) (X : Config d (n + 1)) : ℝ :=
  movg_q d D.s (D.invβ⁻¹ / ((n + 1 : ℕ) : ℝ)) (movg_pi D ρ) X

/-- The constant `c₃ = ∬ g(x-y) ρ(x) ρ(y)`. -/
def movg_c3 (D : DynData d) (ρ : Torus d → ℝ) : ℝ := ∫ x, ρ x * convFun (periodicRiesz d D.s) ρ x

theorem movg_c3_eq (D : DynData d) {ρ : Torus d → ℝ} (hdens : IsProbDensity ρ) :
    mova_c3 (periodicRiesz d D.s) (withDensityReal ρ) = movg_c3 D ρ := by
  unfold mova_c3 movg_c3
  simp_rw [mova_integral_kernel_withDensity hdens]
  exact PDE.MFPairing.integral_withDensityReal hdens.measurable hdens.nonneg _

theorem movg_prod_ite_erase {M : Type*} [CommMonoid M] {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (f : ι → M) : ∏ j, (if i = j then 1 else f j) = ∏ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.prod_erase Finset.univ (f := fun j => if i = j then (1 : M) else f j) (a := i) (by simp)]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]

theorem movg_weight_eq (hd : 1 ≤ d) (D : DynData d) {ρ : Torus d → ℝ} (hdens : IsProbDensity ρ) (n : ℕ)
    (X : Config d (n + 1)) (hX : ∀ i k, i ≠ k → X i ≠ X k) :
    (∏ i, ρ (X i)) * Real.exp (-D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) *
        modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal ρ)) =
      Real.exp (-(D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2) * movg_c3 D ρ) * movg_qn D ρ n X := by
  set β : ℝ := D.invβ⁻¹ with hβ
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hN0 : Nr ≠ 0 := by rw [hNr]; positivity
  rw [mova_modEnergy_expand hdens, movg_c3_eq D hdens]
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d D.s (X i - X j) with hS
  have hpair : movg_pairW d D.s (β / Nr) X = Real.exp (-(β / Nr / 2) * S) := by
    unfold movg_pairW
    have : ∀ i, ∏ j, (if i = j then 1 else movg_Ga d D.s (β / Nr / 2) (X i - X j)) =
        ∏ j ∈ Finset.univ.erase i, movg_Ga d D.s (β / Nr / 2) (X i - X j) := fun i =>
      movg_prod_ite_erase i _
    simp_rw [this]
    rw [hS, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [movg_Ga_of_ne (sub_ne_zero.2 (hX i j (Ne.symm (Finset.ne_of_mem_erase hj))))]
  have hprod : ∏ i, movg_pi D ρ (X i) = (∏ i, ρ (X i)) *
      Real.exp (β * ∑ i, convFun (periodicRiesz d D.s) ρ (X i)) := by
    unfold movg_pi
    rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
  unfold movg_qn movg_q
  rw [hpair, hprod]
  have hexp : -β * Nr * ((1 / (2 * Nr ^ 2)) * S - (1 / Nr) * ∑ i, convFun (periodicRiesz d D.s) ρ (X i) +
      (1 / 2) * movg_c3 D ρ) = -(β / Nr / 2) * S + β * ∑ i, convFun (periodicRiesz d D.s) ρ (X i) +
      -(β * Nr / 2) * movg_c3 D ρ := by
    field_simp
    ring
  rw [hexp, Real.exp_add, Real.exp_add]
  ring

theorem movg_qn_bounded (hd : 1 ≤ d) (D : DynData d) (hβ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (n : ℕ) :
    Measurable (movg_qn D ρ n) ∧ (∀ X, 0 ≤ movg_qn D ρ n X) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ X, movg_qn D ρ n X ≤ C := by
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hβpos : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 < D.invβ⁻¹ / ((n + 1 : ℕ) : ℝ) := div_pos hβpos hNpos
  have hπc : Continuous (movg_pi D ρ) :=
    hρc.mul (Real.continuous_exp.comp (continuous_const.mul (PDE.MFAux.continuous_convFun hgi hρc)))
  have hπ0 : ∀ x, 0 ≤ movg_pi D ρ x := fun x => mul_nonneg (hρ0 x) (Real.exp_pos _).le
  obtain ⟨Cπ, -, hCπ⟩ := mova_bound_of_continuous hπc
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd D.hs0 D.hsd
  have hGa : Measurable (movg_Ga d D.s (D.invβ⁻¹ / ((n + 1 : ℕ) : ℝ) / 2)) :=
    (movg_Ga_continuous hd D.hs0 D.hsd (half_pos ha)).measurable
  refine ⟨movg_q_measurable hGa hπc.measurable, fun X => movg_q_nonneg hπ0 X, ?_⟩
  obtain ⟨C, hC0, hC⟩ := movg_q_le_const (N := n + 1) (s := D.s) hB ha.le hπ0
    (fun x => (le_abs_self _).trans (hCπ x))
  exact ⟨C, hC0, hC⟩

theorem movg_K_eq (hd : 1 ≤ d) (D : DynData d) {ρ : Torus d → ℝ} (hdens : IsProbDensity ρ)
    (hρc : Continuous ρ) (n : ℕ) :
    gibbsNormalizer (periodicRiesz d D.s) (n + 1) D.invβ⁻¹ (withDensityReal ρ) =
      Real.exp (-(D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2) * movg_c3 D ρ) * ∫ X, movg_qn D ρ n X := by
  unfold gibbsNormalizer
  rw [mova_integral_pi_withDensityReal hρc hdens.nonneg, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [movg_ae_noCollision (N := n + 1) hd] with X hX
  exact movg_weight_eq hd D hdens n X hX

theorem movg_J_pos (hd : 1 ≤ d) (D : DynData d) (hβ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x) (n : ℕ) : 0 < ∫ X, movg_qn D ρ n X := by
  obtain ⟨hm, hq0, C, hC0, hC⟩ := movg_qn_bounded hd D hβ hρc (fun x => (hρp x).le) n
  have hint : Integrable (movg_qn D ρ n) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 X)]; exact hC X)
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hq0) hint]
  have hpos : ∀ X : Config d (n + 1), (∀ i k, i ≠ k → X i ≠ X k) → X ∈ Function.support (movg_qn D ρ n) := by
    intro X hX
    refine (ne_of_gt ?_)
    unfold movg_qn movg_q
    refine mul_pos ?_ (Finset.prod_pos fun i _ => ?_)
    · unfold movg_pairW
      refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
      by_cases h : i = j
      · simp [h]
      · simp only [h, if_false]
        exact movg_Ga_pos (sub_ne_zero.2 (hX i j h))
    · exact mul_pos (hρp _) (Real.exp_pos _)
  by_contra hz
  have h0 : volume (Function.support (movg_qn D ρ n)) = 0 := le_antisymm (not_lt.1 hz) bot_le
  have h1 : ∀ᵐ X : Config d (n + 1), X ∉ Function.support (movg_qn D ρ n) :=
    measure_eq_zero_iff_ae_notMem.1 h0
  obtain ⟨X, hX1, hX2⟩ := ((movg_ae_noCollision (N := n + 1) hd).and h1).exists
  exact hX2 (hpos X hX1)

theorem movg_expect_eq (hd : 1 ≤ d) (D : DynData d) (hβ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hdens : IsProbDensity ρ) (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x) (n : ℕ)
    (f : Config d (n + 1) → ℝ) :
    ∫ X, f X ∂(modulatedGibbs (periodicRiesz d D.s) (n + 1) D.invβ⁻¹ (withDensityReal ρ)) =
      (∫ X, movg_qn D ρ n X * f X) / ∫ X, movg_qn D ρ n X := by
  have hJ := movg_J_pos hd D hβ hρc hρp n
  have hK := movg_K_eq hd D hdens hρc n
  have hKpos : 0 < gibbsNormalizer (periodicRiesz d D.s) (n + 1) D.invβ⁻¹ (withDensityReal ρ) := by
    rw [hK]; exact mul_pos (Real.exp_pos _) hJ
  obtain ⟨hm, -⟩ := movf_energy_facts (N := n + 1) hd D.hs0 D.hsd hdens hρc (Nat.succ_pos n)
  rw [mova_integral_modulatedGibbs (periodicRiesz d D.s) (n + 1) D.invβ⁻¹ (withDensityReal ρ)
    (W := fun X => Real.exp (-D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) *
      modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal ρ))) (fun X => rfl)
    (Real.measurable_exp.comp (measurable_const.mul hm)) f]
  rw [mova_integral_pi_withDensityReal hρc hdens.nonneg]
  have e : ∀ᵐ X : Config d (n + 1) ∂volume, (∏ i, ρ (X i)) * (Real.exp (-D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) *
      modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal ρ)) * f X) =
      Real.exp (-(D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2) * movg_c3 D ρ) * (movg_qn D ρ n X * f X) := by
    filter_upwards [movg_ae_noCollision (N := n + 1) hd] with X hX
    rw [← mul_assoc, movg_weight_eq hd D hdens n X hX]; ring
  rw [integral_congr_ae e, integral_const_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hKpos.le, hK, smul_eq_mul]
  field_simp

end HRS
