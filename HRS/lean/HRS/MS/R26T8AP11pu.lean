import HRS.MS.R26T8AP11int

/-!
# S8.2 nonlocal layer: the dyadic partition of unity (P11e, part 1)
`a_n = annulus chi (2^-n)`.  For `v != 0`: `sum_n a_n v = chi v` (telescoping), at most two `a_n v` are nonzero and `|a_n v| <= 1`;
the sum of the annular pieces `locV` equals the local Riesz integral (`r26t8a_loc_partition`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_pu_annulus_eq {chi : Euc d → ℝ} (n : ℕ) (v : Euc d) :
    r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v = chi ((2 : ℝ) ^ n • v) - chi ((2 : ℝ) ^ (n + 1) • v) := by
  unfold r26t8a_annulus
  have h1 : (((1 : ℝ) / 2) ^ n)⁻¹ = (2 : ℝ) ^ n := by rw [one_div, inv_pow, inv_inv]
  have h2 : 2 / ((1 : ℝ) / 2) ^ n = (2 : ℝ) ^ (n + 1) := by
    rw [div_eq_mul_inv, h1, pow_succ]; ring
  rw [h1, h2]

theorem r26t8a_pu_abs_le {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (n : ℕ) (v : Euc d) :
    |r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v| ≤ 1 := by
  rw [r26t8a_pu_annulus_eq]
  have h1 := hchi.2.2.1 ((2 : ℝ) ^ n • v)
  have h2 := hchi.2.2.1 ((2 : ℝ) ^ (n + 1) • v)
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem r26t8a_pu_support {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (n : ℕ) (v : Euc d)
    (h : r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v ≠ 0) :
    ((1 / 2 : ℝ) ^ n) / 2 < ‖v‖ ∧ ‖v‖ < 2 * (1 / 2 : ℝ) ^ n := by
  have hR : 0 < ((1 : ℝ) / 2) ^ n := by positivity
  constructor
  · by_contra hc
    exact h (r26t8a_annulus_zero_small hchi hR (not_lt.1 hc))
  · by_contra hc
    exact h (r26t8a_annulus_zero_large hchi hR (not_lt.1 hc))

theorem r26t8a_pu_close {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (v : Euc d) (n n' : ℕ)
    (h : r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v ≠ 0) (h' : r26t8a_annulus chi ((1 / 2 : ℝ) ^ n') v ≠ 0) :
    n ≤ n' + 1 := by
  by_contra hc
  push Not at hc
  have h1 := (r26t8a_pu_support hchi n v h).2
  have h2 := (r26t8a_pu_support hchi n' v h').1
  have h3 : ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ (n' + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h4 : ((1 : ℝ) / 2) ^ (n' + 2) = ((1 : ℝ) / 2) ^ n' / 4 := by
    rw [pow_add]; norm_num; ring
  linarith

theorem r26t8a_pu_sum_le {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (v : Euc d) (N : ℕ) :
    ∑ n ∈ Finset.range N, |r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v| ≤ 2 := by
  classical
  by_cases hS : ∃ n, r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v ≠ 0
  · set n1 := Nat.find hS with hn1
    have h1 : r26t8a_annulus chi ((1 / 2 : ℝ) ^ n1) v ≠ 0 := Nat.find_spec hS
    have hsub : ∀ n, r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v ≠ 0 → n ∈ ({n1, n1 + 1} : Finset ℕ) := by
      intro n hn
      have hge : n1 ≤ n := Nat.find_min' hS hn
      have hle : n ≤ n1 + 1 := r26t8a_pu_close hchi v n n1 hn h1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have key : ∀ n ∈ Finset.range N, |r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v| ≤
        if n ∈ ({n1, n1 + 1} : Finset ℕ) then (1 : ℝ) else 0 := by
      intro n _
      by_cases hz : r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v = 0
      · rw [hz, abs_zero]; split_ifs <;> norm_num
      · rw [if_pos (hsub n hz)]; exact r26t8a_pu_abs_le hchi n v
    refine (Finset.sum_le_sum key).trans ?_
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((Finset.range N ∩ ({n1, n1 + 1} : Finset ℕ)).card : ℝ) ≤ 2 := by
      have h2 : (Finset.range N ∩ ({n1, n1 + 1} : Finset ℕ)).card ≤ 2 :=
        (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
      exact_mod_cast h2
    exact this
  · push Not at hS
    rw [Finset.sum_eq_zero (fun n _ => by rw [hS n, abs_zero])]
    norm_num

theorem r26t8a_pu_hasSum {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (v : Euc d) (hv : v ≠ 0) :
    HasSum (fun n : ℕ => r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v) (chi v) := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (2 / ‖v‖) (by norm_num : (1 : ℝ) < 2)
  have hg : ∀ n : ℕ, n1 ≤ n → chi ((2 : ℝ) ^ n • v) = 0 := by
    intro n hn
    apply hchi.2.2.2.2
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have : (2 : ℝ) ^ n1 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [div_lt_iff₀ hvp] at hn1
    nlinarith
  have hz : ∀ n ∉ Finset.range n1, r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v = 0 := by
    intro n hn
    have hn' : n1 ≤ n := by simpa using hn
    rw [r26t8a_pu_annulus_eq, hg n hn', hg (n + 1) (by omega), sub_zero]
  have this : HasSum (fun n : ℕ => r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v)
      (∑ n ∈ Finset.range n1, r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v) := hasSum_sum_of_ne_finset_zero hz
  convert this using 1
  rw [Finset.sum_congr rfl fun n _ => r26t8a_pu_annulus_eq n v, Finset.sum_range_sub' (fun n => chi ((2 : ℝ) ^ n • v)),
    hg n1 le_rfl]
  simp

theorem r26t8a_pu_locV_eq {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (alpha : ℝ) {R : ℝ} (hR : 0 < R)
    (F : Euc d → Euc d → ℝ) (X z : Euc d) :
    r26t8a_locV alpha chi R F X z = ∫ v : Euc d, ‖z - v‖ ^ (alpha - (d : ℝ)) *
      (r26t8a_annulus chi R v * F (X + (-(1 / 2 : ℝ)) • z + v) (X + (-(1 / 2 : ℝ)) • z)) := by
  unfold r26t8a_locV r26t8a_locW
  congr 1
  funext v
  rw [← r26t8a_p11_src_eq hchi hR F]
  have e1 : X + (-(1 / 2 : ℝ)) • z + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = X + (-(1 / 2 : ℝ)) • z + v := by module
  have e2 : X + (-(1 / 2 : ℝ)) • z + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = X + (-(1 / 2 : ℝ)) • z := by module
  unfold midPair
  rw [e1, e2]

theorem r26t8a_pu_midPair_localRiesz (alpha : ℝ) (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (X z : Euc d) :
    midPair (r26t8a_localRiesz alpha chi F) X z = chi z * ∫ v : Euc d, ‖z - v‖ ^ (alpha - (d : ℝ)) *
      (chi v * F (X + (-(1 / 2 : ℝ)) • z + v) (X + (-(1 / 2 : ℝ)) • z)) := by
  unfold midPair r26t8a_localRiesz
  have e1 : X + (1 / 2 : ℝ) • z - (X - (1 / 2 : ℝ) • z) = z := by module
  have e2 : X - (1 / 2 : ℝ) • z = X + (-(1 / 2 : ℝ)) • z := by module
  rw [e1, e2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  ring

end HRS.MS.R26T8A
