import HRS.MS.S82UG2

/-!
# S8.2 A04 (S82U), part 3: pole envelopes and their `L²(canonicalP)` integrability
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The envelope `(1+‖X‖)^p ∏_{i≠j} (1 + ‖x_i-x_j‖^{-q})`. -/
def u4Env {d N : ℕ} (p q : ℝ) (X : EucConfig d N) : ℝ :=
  (1 + ‖X‖) ^ p * ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q))



lemma u4_pow_le (u : ℝ) (hu : 0 ≤ u) (k : ℕ) : (1 + u) ^ k ≤ 2 ^ k * (1 + u ^ k) := by
  by_cases h : u ≤ 1
  · calc (1 + u) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + u ^ k) := by
        have : 0 ≤ u ^ k := pow_nonneg hu k
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]
  · push_neg at h
    calc (1 + u) ^ k ≤ (2 * u) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * u ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + u ^ k) := by
        have : 0 ≤ u ^ k := pow_nonneg hu k
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]

lemma u4_rpow_le_exp {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ^ p ≤ C * Real.exp (c * t) := by
  by_cases hp0 : p = 0
  · refine ⟨1, zero_le_one, fun t ht => ?_⟩
    rw [hp0, Real.rpow_zero, one_mul]
    exact Real.one_le_exp (by positivity)
  · have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    refine ⟨(p / c) ^ p, by positivity, fun t ht => ?_⟩
    set u := c * t / p with hu
    have hu0 : 0 ≤ u := by positivity
    have ht' : t = (p / c) * u := by rw [hu]; field_simp
    have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h2 : u ^ p ≤ Real.exp (c * t) := by
      calc u ^ p ≤ (Real.exp u) ^ p := Real.rpow_le_rpow hu0 h1 hp
        _ = Real.exp (u * p) := by rw [← Real.exp_mul]
        _ = Real.exp (c * t) := by rw [hu]; congr 1; field_simp
    calc t ^ p = ((p / c) * u) ^ p := by rw [← ht']
      _ = (p / c) ^ p * u ^ p := Real.mul_rpow (by positivity) hu0
      _ ≤ (p / c) ^ p * Real.exp (c * t) := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma u4_absorb {q s c : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → (1 + r ^ (-q)) ^ k ≤ C * Real.exp (c * r ^ (-s)) := by
  obtain ⟨Cp, hCp, hpoly⟩ := u4_rpow_le_exp (p := q / s * k) (c := c) (by positivity) hc
  refine ⟨2 ^ k * (1 + Cp), by positivity, fun r hr => ?_⟩
  set t := r ^ (-s) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hr.le _
  have hrq : r ^ (-q) = t ^ (q / s) := by
    rw [ht, ← Real.rpow_mul hr.le]; congr 1; field_simp
  have h1 := u4_pow_le (r ^ (-q)) (Real.rpow_nonneg hr.le _) k
  have h2 : (r ^ (-q)) ^ k = t ^ (q / s * k) := by
    rw [hrq, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
  rw [h2] at h1
  have h3 := hpoly t ht0
  have h4 : 1 ≤ Real.exp (c * t) := Real.one_le_exp (by positivity)
  calc (1 + r ^ (-q)) ^ k ≤ 2 ^ k * (1 + t ^ (q / s * k)) := h1
    _ ≤ 2 ^ k * (1 + Cp * Real.exp (c * t)) := by gcongr
    _ ≤ 2 ^ k * (1 + Cp) * Real.exp (c * t) := by
      have : 0 ≤ Cp * Real.exp (c * t) := by positivity
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k, mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k) hCp,
        mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k) hCp) (sub_nonneg.2 h4)]


/-- pair sum `∑_{i<j} ‖x_i-x_j‖^{-s}` -/
def u4Sp {d N : ℕ} (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), ‖X i - X j‖ ^ (-criticalS d)

lemma u4_H_eq {d N : ℕ} (hd : 2 ≤ d) (a : ℝ) (X : EucConfig d N) :
    HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X =
      ∑ i, confinement a (X i) + (1 / (N : ℝ)) * u4Sp X := by
  have hs : criticalS d ≠ 0 := (u4_crit_pos hd).ne'
  unfold HRS.Whole.canonicalHamiltonian u4Sp
  simp only [rieszKernel, hs, if_false]

lemma u4_Sp_nonneg {d N : ℕ} (X : EucConfig d N) : 0 ≤ u4Sp X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _

lemma u4_sum_erase_Sp {d N : ℕ} (X : EucConfig d N) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ‖X i - X j‖ ^ (-criticalS d) = 2 * u4Sp X := by
  have := HRS.MS.S81G.s81g_sum_erase (N := N) (fun i j => ‖X i - X j‖ ^ (-criticalS d)) (fun i j => by
    rw [norm_sub_rev])
  exact this

lemma u4_pole_prod {d N : ℕ} (hd : 2 ≤ d) (hN : 0 < N) {q beta : ℝ} (hq : 0 ≤ q) (hbeta : 0 < beta) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) ^ 2 ≤
        Kc * Real.exp (beta / (2 * N) * u4Sp X) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨C, hC, habs⟩ := u4_absorb (q := q) (s := criticalS d) (c := beta / (4 * N)) hq (u4_crit_pos hd)
    (by positivity) 2
  refine ⟨∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, C, Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hC,
    fun X hX => ?_⟩
  have hne : ∀ i j : Fin N, i ≠ j → 0 < ‖X i - X j‖ := fun i j hij =>
    norm_pos_iff.2 (sub_ne_zero.2 (fun h => hX ⟨i, j, hij, h⟩))
  calc ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) ^ 2
      ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (C * Real.exp (beta / (4 * N) * ‖X i - X j‖ ^ (-criticalS d))) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => by positivity) fun i _ => ?_
        refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j hj => ?_
        exact habs _ (hne i j (Finset.ne_of_mem_erase hj).symm)
    _ = (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, C) * Real.exp (beta / (4 * N) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, ‖X i - X j‖ ^ (-criticalS d)) := by
        simp only [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum]
    _ = (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, C) * Real.exp (beta / (2 * N) * u4Sp X) := by
        rw [u4_sum_erase_Sp]; congr 2; field_simp; ring

end HRS.MS.S82U
