/-
# HRS.Equilibrium.Q84dAuxE — packet Q84d: pointwise bounds of the Gibbs density against the envelopes

For every `κ > 0` the envelopes satisfy `w e^{-κ g} ≤ C` and `w² e^{-κ g} ≤ C`; hence the Gibbs
density `q = e^{-βH}` times `w(x_i,x_j)`, `w(x_i,x_j)²` or `w(x_a,x_b) w(x_c,x_e)` (distinct pairs)
is bounded.
-/
import HRS.Equilibrium.Q84dAuxD

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ}

theorem q84d_exists_lower (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Torus d, -B ≤ periodicRiesz d s z := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  exact ⟨max B 0, le_max_right _ _, fun z => (neg_le_neg (le_max_left _ _)).trans (hB z)⟩

theorem q84d_exists_bound_smooth {V : Torus d → ℝ} (hV : Torus.IsSmooth V) :
    ∃ Vm : ℝ, ∀ x, |V x| ≤ Vm := by
  have hc : Continuous V := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).continuous
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

/-- `w^k e^{-κ g} ≤ C` for `k ∈ {1, 2}`. -/
theorem q84d_w_exp_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Torus d,
      wEnv s x y * Real.exp (-κ * periodicRiesz d s (x - y)) ≤ C ∧
      wEnv s x y ^ 2 * Real.exp (-κ * periodicRiesz d s (x - y)) ≤ C := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨B, hB0, hB⟩ := q84d_exists_lower hd hs0 hsd
  have hc : ∀ z, 0 ≤ periodicRiesz d s z + B := fun z => by linarith [hB z]
  obtain ⟨A, hA, hAw⟩ := PairCorrAux.wEnv_le_gPlus hd hcrit B hc
  set κ' : ℝ := κ / A with hκ'
  have hκ'0 : 0 < κ' := div_pos hκ hA
  refine ⟨Real.exp (κ * (1 + B)) * (24 * (1 / κ') ^ 4), by positivity, fun x y => ?_⟩
  have hw1 : 1 ≤ wEnv s x y := PairCorrAux.one_le_wEnv s x y
  have hw := hAw x y
  unfold gPlus at hw
  have hexp : Real.exp (-κ * periodicRiesz d s (x - y)) ≤
      Real.exp (κ * (1 + B)) * Real.exp (-κ' * wEnv s x y) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : wEnv s x y / A ≤ 1 + (periodicRiesz d s (x - y) + B) := by
      rw [div_le_iff₀ hA]; nlinarith
    have : κ' * wEnv s x y = κ * (wEnv s x y / A) := by rw [hκ']; ring
    nlinarith [mul_le_mul_of_nonneg_left h1 hκ.le]
  have hp := PairCorrAux.pow4_exp_le (wEnv s x y) κ' (by linarith) hκ'0
  have hmin : min (wEnv s x y) (1 / κ') ^ 4 ≤ (1 / κ') ^ 4 :=
    pow_le_pow_left₀ (le_min (by linarith) (by positivity)) (min_le_right _ _) 4
  have hK : wEnv s x y ^ 4 * Real.exp (-κ' * wEnv s x y) ≤ 24 * (1 / κ') ^ 4 := by
    linarith
  have hE : 0 < Real.exp (κ * (1 + B)) := Real.exp_pos _
  have hq : 0 < Real.exp (-κ' * wEnv s x y) := Real.exp_pos _
  have e1 : wEnv s x y ≤ wEnv s x y ^ 4 := by
    have : wEnv s x y * 1 ≤ wEnv s x y * wEnv s x y ^ 3 :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hw1) (by linarith)
    nlinarith
  have e2 : wEnv s x y ^ 2 ≤ wEnv s x y ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
  have hg0 : 0 < Real.exp (-κ * periodicRiesz d s (x - y)) := Real.exp_pos _
  constructor
  · calc wEnv s x y * Real.exp (-κ * periodicRiesz d s (x - y))
        ≤ wEnv s x y * (Real.exp (κ * (1 + B)) * Real.exp (-κ' * wEnv s x y)) :=
          mul_le_mul_of_nonneg_left hexp (by linarith)
      _ = Real.exp (κ * (1 + B)) * (wEnv s x y * Real.exp (-κ' * wEnv s x y)) := by ring
      _ ≤ Real.exp (κ * (1 + B)) * (wEnv s x y ^ 4 * Real.exp (-κ' * wEnv s x y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e1 hq.le) hE.le
      _ ≤ Real.exp (κ * (1 + B)) * (24 * (1 / κ') ^ 4) := mul_le_mul_of_nonneg_left hK hE.le
  · calc wEnv s x y ^ 2 * Real.exp (-κ * periodicRiesz d s (x - y))
        ≤ wEnv s x y ^ 2 * (Real.exp (κ * (1 + B)) * Real.exp (-κ' * wEnv s x y)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (κ * (1 + B)) * (wEnv s x y ^ 2 * Real.exp (-κ' * wEnv s x y)) := by ring
      _ ≤ Real.exp (κ * (1 + B)) * (wEnv s x y ^ 4 * Real.exp (-κ' * wEnv s x y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 hq.le) hE.le
      _ ≤ Real.exp (κ * (1 + B)) * (24 * (1 / κ') ^ 4) := mul_le_mul_of_nonneg_left hK hE.le

/-! ### Gibbs density against the pair envelopes -/

section Pairs

variable {N : ℕ}

/-- The ordered representative `(min, max)` of an unordered pair of distinct labels. -/
def ordPair (i j : Fin N) : Fin N × Fin N := if i < j then (i, j) else (j, i)

theorem ordPair_mem {i j : Fin N} (h : i ≠ j) : ordPair i j ∈ pairsN N := by
  unfold ordPair pairsN
  rcases lt_or_gt_of_ne h with h1 | h1
  · simp [h1]
  · simp [not_lt.2 h1.le, h1]

theorem g_ordPair {g : Torus d → ℝ} (hg : ∀ z, g (-z) = g z) (X : Config d N) (i j : Fin N) :
    g (X (ordPair i j).1 - X (ordPair i j).2) = g (X i - X j) := by
  unfold ordPair
  split_ifs with h
  · rfl
  · have : X j - X i = -(X i - X j) := by abel
    simp only [this, hg]

theorem ordPair_inj {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (h : ordPair i j = ordPair k l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  unfold ordPair at h
  rcases lt_or_gt_of_ne hij with h1 | h1 <;> rcases lt_or_gt_of_ne hkl with h2 | h2
  · simp only [h1, h2, if_true, Prod.mk.injEq] at h; exact Or.inl h
  · simp only [h1, if_true, not_lt.2 h2.le, if_false, Prod.mk.injEq] at h; exact Or.inr h
  · simp only [not_lt.2 h1.le, if_false, h2, if_true, Prod.mk.injEq] at h
    exact Or.inr ⟨h.2, h.1⟩
  · simp only [not_lt.2 h1.le, if_false, not_lt.2 h2.le, Prod.mk.injEq] at h
    exact Or.inl ⟨h.2, h.1⟩

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)

include hd hcrit

theorem q84d_q_one_pair {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (X : Config d N) (i j : Fin N), i ≠ j →
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) ≤
        Q * Real.exp (-(β / N) * periodicRiesz d s (X i - X j)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨B, hB0, hB⟩ := q84d_exists_lower hd hs0 hsd
  obtain ⟨Vm, hVm⟩ := q84d_exists_bound_smooth hV
  refine ⟨Real.exp (β * ((N : ℝ) * Vm + N * B)), (Real.exp_pos _).le, fun X i j hij => ?_⟩
  have h := q84d_q_le hB0 hB hVm hN hβ.le {ordPair i j}
    (by simpa using ordPair_mem hij) X
  simpa [g_ordPair (fun z => periodicRiesz_neg z) X i j] using h

theorem q84d_q_two_pairs {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (X : Config d N) (i j k l : Fin N), i ≠ j → k ≠ l →
      ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) ≤
        Q * (Real.exp (-(β / N) * periodicRiesz d s (X i - X j)) *
          Real.exp (-(β / N) * periodicRiesz d s (X k - X l))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨B, hB0, hB⟩ := q84d_exists_lower hd hs0 hsd
  obtain ⟨Vm, hVm⟩ := q84d_exists_bound_smooth hV
  refine ⟨Real.exp (β * ((N : ℝ) * Vm + N * B)), (Real.exp_pos _).le,
    fun X i j k l hij hkl hne => ?_⟩
  have hne' : ordPair i j ≠ ordPair k l := fun h => hne (ordPair_inj hij hkl h)
  have hT : ({ordPair i j, ordPair k l} : Finset (Fin N × Fin N)) ⊆ pairsN N := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ordPair_mem hij
    · exact ordPair_mem hkl
  have h := q84d_q_le hB0 hB hVm hN hβ.le {ordPair i j, ordPair k l} hT X
  rw [Finset.prod_pair hne'] at h
  simpa [g_ordPair (fun z => periodicRiesz_neg z) X i j,
    g_ordPair (fun z => periodicRiesz_neg z) X k l] using h

theorem q84d_q_mul_w_le {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Config d N) (i j : Fin N), i ≠ j →
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) * wEnv s (X i) (X j) ≤ C ∧
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) * wEnv s (X i) (X j) ^ 2 ≤ C := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Q, hQ0, hQ⟩ := q84d_q_one_pair hd hcrit hV hβ hN
  obtain ⟨C, hC0, hC⟩ := q84d_w_exp_bound hd hcrit (κ := β / N) (div_pos hβ hNp)
  refine ⟨Q * C, mul_nonneg hQ0 hC0, fun X i j hij => ?_⟩
  have h1 := hQ X i j hij
  have h2 := hC (X i) (X j)
  have hw0 : 0 ≤ wEnv s (X i) (X j) := (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _))
  constructor
  · calc _ ≤ (Q * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) * wEnv s (X i) (X j) :=
          mul_le_mul_of_nonneg_right h1 hw0
      _ = Q * (wEnv s (X i) (X j) * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) := by ring
      _ ≤ Q * C := mul_le_mul_of_nonneg_left h2.1 hQ0
  · calc _ ≤ (Q * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) * wEnv s (X i) (X j) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Q * (wEnv s (X i) (X j) ^ 2 * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) := by ring
      _ ≤ Q * C := mul_le_mul_of_nonneg_left h2.2 hQ0

theorem q84d_q_mul_ww_le {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Config d N) (i j k l : Fin N), i ≠ j → k ≠ l →
      ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) *
        (wEnv s (X i) (X j) * wEnv s (X k) (X l)) ≤ C := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Q, hQ0, hQ⟩ := q84d_q_two_pairs hd hcrit hV hβ hN
  obtain ⟨C, hC0, hC⟩ := q84d_w_exp_bound hd hcrit (κ := β / N) (div_pos hβ hNp)
  refine ⟨Q * (C * C), mul_nonneg hQ0 (mul_nonneg hC0 hC0), fun X i j k l hij hkl hne => ?_⟩
  have h1 := hQ X i j k l hij hkl hne
  have h2 := (hC (X i) (X j)).1
  have h3 := (hC (X k) (X l)).1
  have hw0 : 0 ≤ wEnv s (X i) (X j) * wEnv s (X k) (X l) :=
    mul_nonneg (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _))
      (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _))
  have hA : 0 ≤ wEnv s (X i) (X j) * Real.exp (-(β / N) * periodicRiesz d s (X i - X j)) :=
    mul_nonneg (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _)) (Real.exp_pos _).le
  calc _ ≤ (Q * (Real.exp (-(β / N) * periodicRiesz d s (X i - X j)) *
          Real.exp (-(β / N) * periodicRiesz d s (X k - X l)))) *
          (wEnv s (X i) (X j) * wEnv s (X k) (X l)) := mul_le_mul_of_nonneg_right h1 hw0
    _ = Q * ((wEnv s (X i) (X j) * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) *
          (wEnv s (X k) (X l) * Real.exp (-(β / N) * periodicRiesz d s (X k - X l)))) := by ring
    _ ≤ Q * (C * C) := mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (mul_nonneg (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _)) (Real.exp_pos _).le) hC0) hQ0

end Pairs

end HRS.Q84d

end
