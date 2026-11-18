import HRS.PDE.Toolbox.CoeffL2
import HRS.PDE.HsAnalysis

/-!
# Appendix C helper lemmas: fractional product bounds (Lemma C.5 (ii), (iii))

Auxiliary results for `HRS/PDE/Toolbox.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ProdAux
variable {d : ℕ}
open HRS HRS.Torus

/-- translation by `2^{-n} e_i` -/
def shift (n : ℕ) (i : Fin d) : Torus d :=
  Torus.mk (((1 / 2 : ℝ) ^ n) • (EuclideanSpace.single i (1 : ℝ) : Euc d))

lemma dot_shift (k : Lattice d) (n : ℕ) (i : Fin d) :
    Lattice.dot k (((1 / 2 : ℝ) ^ n) • (EuclideanSpace.single i (1 : ℝ) : Euc d)) = (k i : ℝ) * (1 / 2) ^ n := by
  simp [Lattice.dot]

lemma mode_shift (k : Lattice d) (n : ℕ) (i : Fin d) :
    mode k (shift n i) = Complex.exp (Complex.I * (((2 * Real.pi * ((k i : ℝ) * (1 / 2) ^ n) : ℝ)) : ℂ)) := by
  rw [shift, mode_mk, dot_shift, mul_comm]

/-- `|e_k(2^{-n}e_i) - 1|² = 4 sin²(π k_i 2^{-n})` -/
lemma sqnorm_mode_shift (k : Lattice d) (n : ℕ) (i : Fin d) :
    ‖mode k (shift n i) - 1‖ ^ 2 = 4 * Real.sin (Real.pi * ((k i : ℝ) * (1 / 2) ^ n)) ^ 2 := by
  rw [mode_shift, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  have : 2 * Real.pi * ((k i : ℝ) * (1 / 2) ^ n) / 2 = Real.pi * ((k i : ℝ) * (1 / 2) ^ n) := by ring
  rw [this]; ring

lemma enorm_sq (k : Lattice d) : Lattice.enorm k ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
  unfold Lattice.enorm Lattice.toEuc
  rw [EuclideanSpace.norm_sq_eq]
  simp

lemma sq_le_enorm_sq (k : Lattice d) (i : Fin d) : ((k i : ℤ) : ℝ) ^ 2 ≤ Lattice.enorm k ^ 2 := by
  rw [enorm_sq]
  exact Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma exists_enorm_sq_le (k : Lattice d) (hd : 1 ≤ d) :
    ∃ i, Lattice.enorm k ^ 2 ≤ d * ((k i : ℤ) : ℝ) ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin d => ((k i : ℤ) : ℝ) ^ 2) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [enorm_sq]
  calc ∑ j, ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ j : Fin d, ((k i : ℤ) : ℝ) ^ 2 :=
        Finset.sum_le_sum fun j _ => hi j (Finset.mem_univ j)
    _ = d * ((k i : ℤ) : ℝ) ^ 2 := by simp

lemma sin_term_le (x : ℝ) : 4 * Real.sin x ^ 2 ≤ 4 * x ^ 2 := by
  have := Real.sin_sq_le_sq (x := x); linarith

lemma upper_one (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ (m : ℤ) (N : ℕ), m ≠ 0 →
      ∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n * (4 * Real.sin (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2)
        ≤ U * ((m : ℝ) ^ 2) ^ σ := by
  set r : ℝ := (4 : ℝ) ^ σ with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hσ0
  have hr4 : r < 4 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (4 : ℝ)) (by norm_num) hσ1
    simpa [hr] using this
  set ρ : ℝ := r / 4 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  refine ⟨4 * r / (r - 1) + 4 * Real.pi ^ 2 / (1 - ρ), by
    have : 0 < r - 1 := by linarith
    have : 0 < 1 - ρ := by linarith
    positivity, fun m N hm => ?_⟩
  set T : ℕ := m.natAbs with hT
  have hT0 : T ≠ 0 := by simpa [hT] using hm
  have hTm : (m : ℝ) ^ 2 = (T : ℝ) ^ 2 := by
    rw [hT, Nat.cast_natAbs]; simp [sq_abs]
  set n₀ := Nat.log 2 T with hn₀
  have h1 : 2 ^ n₀ ≤ T := Nat.pow_log_le_self 2 hT0
  have h2 : T < 2 ^ (n₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) T
  have h1' : ((2 : ℝ) ^ n₀) ≤ (T : ℝ) := by exact_mod_cast h1
  have h2' : (T : ℝ) < (2 : ℝ) ^ (n₀ + 1) := by exact_mod_cast h2
  have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT0
  have key : ∀ n : ℕ, ((4 : ℝ) ^ σ) ^ n * (4 * Real.sin (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2) ≤
      if n ≤ n₀ then 4 * r ^ n else 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * ρ ^ n := by
    intro n
    have hrn : 0 ≤ r ^ n := by positivity
    split_ifs with h
    · calc r ^ n * (4 * Real.sin (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2) ≤ r ^ n * (4 * 1) := by
            apply mul_le_mul_of_nonneg_left _ hrn
            have := Real.sin_sq_le_one (Real.pi * ((m : ℝ) * (1 / 2) ^ n)); linarith
        _ = 4 * r ^ n := by ring
    · calc r ^ n * (4 * Real.sin (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2)
          ≤ r ^ n * (4 * (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2) :=
            mul_le_mul_of_nonneg_left (sin_term_le _) hrn
        _ = 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * ρ ^ n := by
            have : ρ ^ n = r ^ n * (1 / 4) ^ n := by
              rw [hρ, ← mul_pow]; congr 1; ring
            rw [this]
            have : ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ n = (1 / 4) ^ n := by
              rw [← mul_pow]; norm_num
            calc r ^ n * (4 * (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2)
                = 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (r ^ n * ((1 / 2) ^ n * (1 / 2) ^ n)) := by ring
              _ = _ := by rw [this]
  refine (Finset.sum_le_sum fun n _ => key n).trans ?_
  rw [Finset.sum_ite]
  have s1 : ∑ n ∈ (Finset.range N).filter (· ≤ n₀), 4 * r ^ n ≤ 4 * r / (r - 1) * r ^ n₀ := by
    calc ∑ n ∈ (Finset.range N).filter (· ≤ n₀), 4 * r ^ n
        ≤ ∑ n ∈ Finset.range (n₀ + 1), 4 * r ^ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
            omega
          · intro n _ _; positivity
      _ = 4 * ∑ n ∈ Finset.range (n₀ + 1), r ^ n := by rw [Finset.mul_sum]
      _ = 4 * ((r ^ (n₀ + 1) - 1) / (r - 1)) := by
          rw [geom_sum_eq (by linarith) ]
      _ ≤ 4 * (r ^ (n₀ + 1) / (r - 1)) := by
          gcongr
          · linarith
      _ = 4 * r / (r - 1) * r ^ n₀ := by ring
  have s2 : ∑ n ∈ (Finset.range N).filter (fun n => ¬ n ≤ n₀),
      4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * ρ ^ n ≤
      4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (ρ ^ (n₀ + 1) / (1 - ρ)) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ n ∈ (Finset.range N).filter (fun n => ¬ n ≤ n₀), ρ ^ n
        ≤ ∑ n ∈ Finset.Ico (n₀ + 1) N, ρ ^ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
            omega
          · intro n _ _; positivity
      _ ≤ ρ ^ (n₀ + 1) / (1 - ρ) := geom_sum_Ico_le_of_lt_one hρ0 hρ1
  have e1 : r ^ n₀ ≤ ((m : ℝ) ^ 2) ^ σ := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast, hTm]
    apply Real.rpow_le_rpow (by positivity) _ hσ0.le
    have : (4 : ℝ) ^ n₀ = ((2 : ℝ) ^ n₀) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by positivity) h1' 2
  have e2 : ρ ^ (n₀ + 1) ≤ ((m : ℝ) ^ 2) ^ (σ - 1) := by
    have hρeq : ρ = (4 : ℝ) ^ (σ - 1) := by
      rw [hρ, hr, Real.rpow_sub (by norm_num), Real.rpow_one]
    rw [hρeq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast, hTm]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    have : (4 : ℝ) ^ (n₀ + 1) = ((2 : ℝ) ^ (n₀ + 1)) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ hTpos.le h2'.le 2
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by rw [hTm]; positivity
  have e3 : (m : ℝ) ^ 2 * ((m : ℝ) ^ 2) ^ (σ - 1) = ((m : ℝ) ^ 2) ^ σ := by
    rw [← Real.rpow_one_add' hm2.le (by linarith)]; ring_nf
  have hr0 : 0 < r - 1 := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  calc _ ≤ 4 * r / (r - 1) * r ^ n₀ + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (ρ ^ (n₀ + 1) / (1 - ρ)) := add_le_add s1 s2
    _ ≤ 4 * r / (r - 1) * ((m : ℝ) ^ 2) ^ σ + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 * (((m : ℝ) ^ 2) ^ (σ - 1) / (1 - ρ)) := by
        gcongr
    _ = _ := by
        rw [← e3]; field_simp



lemma lower_one (m : ℤ) (hm : m ≠ 0) :
    ∃ n : ℕ, (m : ℝ) ^ 2 ≤ (4 : ℝ) ^ n ∧
      2 ≤ 4 * Real.sin (Real.pi * ((m : ℝ) * (1 / 2) ^ n)) ^ 2 := by
  set T : ℕ := m.natAbs with hT
  have hT0 : T ≠ 0 := by simpa [hT] using hm
  have hTm : (m : ℝ) ^ 2 = (T : ℝ) ^ 2 := by
    rw [hT, Nat.cast_natAbs]; simp [sq_abs]
  set n₀ := Nat.log 2 T with hn₀
  have h1 : 2 ^ n₀ ≤ T := Nat.pow_log_le_self 2 hT0
  have h2 : T < 2 ^ (n₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) T
  have h1' : ((2 : ℝ) ^ n₀) ≤ (T : ℝ) := by exact_mod_cast h1
  have h2' : (T : ℝ) < (2 : ℝ) ^ (n₀ + 1) := by exact_mod_cast h2
  have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT0
  refine ⟨n₀ + 2, ?_, ?_⟩
  · rw [hTm]
    have : (4 : ℝ) ^ (n₀ + 2) = ((2 : ℝ) ^ (n₀ + 2)) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    apply pow_le_pow_left₀ hTpos.le
    calc (T : ℝ) ≤ 2 ^ (n₀ + 1) := h2'.le
      _ ≤ 2 ^ (n₀ + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  · have hp2 : (0 : ℝ) < (2 : ℝ) ^ n₀ := by positivity
    set θ : ℝ := (T : ℝ) * (1 / 2) ^ (n₀ + 2) with hθ
    have hθeq : θ = (T : ℝ) / 2 ^ (n₀ + 2) := by rw [hθ, one_div_pow, mul_one_div]
    have hp3 : (0 : ℝ) < 2 ^ (n₀ + 2) := by positivity
    have hθ1 : (1 / 4 : ℝ) ≤ θ := by
      rw [hθeq, le_div_iff₀ hp3, pow_add]; nlinarith
    have hθ2 : θ ≤ 1 / 2 := by
      rw [hθeq, div_le_iff₀ hp3, pow_add]; rw [pow_add] at h2'; nlinarith
    have hs : Real.sin (Real.pi * θ) ^ 2 ≥ 1 / 2 := by
      have : Real.sin (Real.pi / 4) ≤ Real.sin (Real.pi * θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
      rw [Real.sin_pi_div_four] at this
      have h0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
      have := pow_le_pow_left₀ h0 this 2
      have e : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      linarith
    have hm' : Real.sin (Real.pi * ((m : ℝ) * (1 / 2) ^ (n₀ + 2))) ^ 2 =
        Real.sin (Real.pi * θ) ^ 2 := by
      have hTabs : (T : ℝ) = |(m : ℝ)| := by rw [hT, Nat.cast_natAbs]; simp
      rcases abs_choice (m : ℝ) with h | h
      · have : (m : ℝ) = T := by rw [hTabs, h]
        rw [this]
      · have : (m : ℝ) = -T := by rw [hTabs, h]; ring
        rw [this, hθ]
        have : Real.pi * (-(T : ℝ) * (1 / 2) ^ (n₀ + 2)) = -(Real.pi * ((T : ℝ) * (1 / 2) ^ (n₀ + 2))) := by ring
        rw [this, Real.sin_neg, neg_sq]
    rw [hm']; linarith

lemma sqnorm_mode_shift_nonneg (k : Lattice d) (n : ℕ) (i : Fin d) : 0 ≤ ‖mode k (shift n i) - 1‖ ^ 2 :=
  sq_nonneg _

lemma sqnorm_mode_shift_zero (k : Lattice d) (n : ℕ) (i : Fin d) (hk : k i = 0) :
    ‖mode k (shift n i) - 1‖ ^ 2 = 0 := by
  rw [sqnorm_mode_shift, hk]; simp

lemma one_le_sobWeight (σ : ℝ) (hσ : 0 ≤ σ) (k : Lattice d) : 1 ≤ sobWeight σ k := by
  unfold sobWeight
  apply Real.one_le_rpow _ hσ
  have : 0 ≤ Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  nlinarith

lemma sq_le_sobBase (k : Lattice d) (i : Fin d) :
    ((k i : ℤ) : ℝ) ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  have h1 := sq_le_enorm_sq k i
  have h2 : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (Lattice.enorm k)]

lemma upper_vec (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ (k : Lattice d) (N : ℕ),
      ∑ i, ∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2
        ≤ U * sobWeight σ k := by
  obtain ⟨U₁, hU₁, hU⟩ := upper_one σ hσ0 hσ1
  refine ⟨d * U₁, by positivity, fun k N => ?_⟩
  have hw := sobWeight_pos σ k
  calc ∑ i, ∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2
      ≤ ∑ _i : Fin d, U₁ * sobWeight σ k := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hk : k i = 0
        · rw [Finset.sum_eq_zero]
          · positivity
          · intro n _; rw [sqnorm_mode_shift_zero k n i hk]; simp
        · simp_rw [sqnorm_mode_shift]
          refine (hU (k i) N hk).trans ?_
          apply mul_le_mul_of_nonneg_left _ hU₁
          unfold sobWeight
          exact Real.rpow_le_rpow (sq_nonneg _) (sq_le_sobBase k i) hσ0.le
    _ = d * U₁ * sobWeight σ k := by simp; ring

lemma lower_vec (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ k : Lattice d, ∃ N : ℕ,
      sobWeight σ k ≤ L * (1 + ∑ i, ∑ n ∈ Finset.range N,
        ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2) := by
  set B : ℝ := (1 + 4 * Real.pi ^ 2) * d with hB
  have hB1 : 1 ≤ B := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : (1 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 := by nlinarith [sq_nonneg Real.pi]
    rw [hB]; nlinarith
  refine ⟨B ^ σ, Real.one_le_rpow hB1 hσ, fun k => ?_⟩
  by_cases hk : k = 0
  · refine ⟨0, ?_⟩
    subst hk
    have : sobWeight σ (0 : Lattice d) = 1 := by
      have h0 : Lattice.enorm (0 : Lattice d) ^ 2 = 0 := by rw [enorm_sq]; simp
      unfold sobWeight; rw [h0]; simp
    rw [this]; simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero, add_zero, mul_one]
    exact Real.one_le_rpow hB1 hσ
  · obtain ⟨i, hi⟩ := exists_enorm_sq_le k hd
    have hk1 : 1 ≤ Lattice.enorm k ^ 2 := by
      obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
        by_contra h; push Not at h; exact hk (funext h)
      have : (1 : ℝ) ≤ ((k j : ℤ) : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ (k j) ^ 2 := by nlinarith [sq_pos_of_ne_zero hj]
        exact_mod_cast this
      exact this.trans (sq_le_enorm_sq k j)
    have hm : k i ≠ 0 := by
      intro h0
      have h00 : ((k i : ℤ) : ℝ) = 0 := by exact_mod_cast h0
      rw [h00] at hi; nlinarith
    obtain ⟨n, hn1, hn2⟩ := lower_one (k i) hm
    refine ⟨n + 1, ?_⟩
    have hbase : 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤ B * (4 : ℝ) ^ n := by
      calc 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤ (1 + 4 * Real.pi ^ 2) * Lattice.enorm k ^ 2 := by
            nlinarith
        _ ≤ (1 + 4 * Real.pi ^ 2) * (d * ((k i : ℤ) : ℝ) ^ 2) := by gcongr
        _ ≤ (1 + 4 * Real.pi ^ 2) * (d * (4 : ℝ) ^ n) := by gcongr
        _ = B * 4 ^ n := by rw [hB]; ring
    have h1 : sobWeight σ k ≤ B ^ σ * ((4 : ℝ) ^ σ) ^ n := by
      unfold sobWeight
      calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ σ ≤ (B * (4 : ℝ) ^ n) ^ σ :=
            Real.rpow_le_rpow (by positivity) hbase hσ
        _ = B ^ σ * ((4 : ℝ) ^ σ) ^ n := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
              mul_comm (n : ℝ) σ, mul_comm]
    have hterm : ((4 : ℝ) ^ σ) ^ n ≤ ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 := by
      rw [sqnorm_mode_shift]
      have : (1 : ℝ) ≤ 4 * Real.sin (Real.pi * ((k i : ℝ) * (1 / 2) ^ n)) ^ 2 := by linarith
      have h4 : 0 ≤ ((4 : ℝ) ^ σ) ^ n := by positivity
      nlinarith
    have hsum : ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 ≤
        ∑ i, ∑ n ∈ Finset.range (n + 1), ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 := by
      have hs1 : ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 ≤
          ∑ n' ∈ Finset.range (n + 1), ((4 : ℝ) ^ σ) ^ n' * ‖mode k (shift n' i) - 1‖ ^ 2 :=
        Finset.single_le_sum (f := fun n' => ((4 : ℝ) ^ σ) ^ n' * ‖mode k (shift n' i) - 1‖ ^ 2)
          (fun n' _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_self n))
      refine hs1.trans ?_
      exact Finset.single_le_sum (f := fun i => ∑ n' ∈ Finset.range (n + 1),
        ((4 : ℝ) ^ σ) ^ n' * ‖mode k (shift n' i) - 1‖ ^ 2)
        (fun i _ => Finset.sum_nonneg fun n' _ => by positivity) (Finset.mem_univ i)
    have hB0 : 0 ≤ B ^ σ := by positivity
    calc sobWeight σ k ≤ B ^ σ * ((4 : ℝ) ^ σ) ^ n := h1
      _ ≤ B ^ σ * (1 + ∑ i, ∑ n ∈ Finset.range (n + 1),
          ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          linarith

/-- first-order bound `4^n |e_k(2^{-n}e_i) - 1|² ≤ 4π² k_i²`. -/
lemma four_pow_mul_sqnorm_le (k : Lattice d) (n : ℕ) (i : Fin d) :
    (4 : ℝ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2 := by
  rw [sqnorm_mode_shift]
  have h := sin_term_le (Real.pi * ((k i : ℝ) * (1 / 2) ^ n))
  have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
  calc (4 : ℝ) ^ n * (4 * Real.sin (Real.pi * ((k i : ℝ) * (1 / 2) ^ n)) ^ 2)
      ≤ 4 ^ n * (4 * (Real.pi * ((k i : ℝ) * (1 / 2) ^ n)) ^ 2) := mul_le_mul_of_nonneg_left h h4
    _ = 4 * Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2 * ((4 : ℝ) ^ n * ((1 / 2) ^ n * (1 / 2) ^ n)) := by ring
    _ = _ := by
        have : ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ n = (1 / 4) ^ n := by
          rw [← mul_pow]; norm_num
        rw [this, ← mul_pow]; norm_num

lemma tendsto_four_pow_mul_sqnorm (k : Lattice d) (i : Fin d) :
    Tendsto (fun n : ℕ => (4 : ℝ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2) atTop
      (𝓝 (4 * Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2)) := by
  by_cases hk : k i = 0
  · simp only [sqnorm_mode_shift_zero k _ i hk, mul_zero, hk]
    simp
  · set x : ℕ → ℝ := fun n => Real.pi * ((k i : ℝ) * (1 / 2) ^ n) with hx
    have hm : ((k i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk
    have hx0 : ∀ n, x n ≠ 0 := fun n => by
      simp only [hx]; exact mul_ne_zero Real.pi_ne_zero (mul_ne_zero hm (by positivity))
    have hxt : Tendsto x atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hx0⟩
      have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa [hx] using (this.const_mul ((k i : ℝ))).const_mul Real.pi
    have hs : Tendsto (fun t : ℝ => Real.sin t / t) (𝓝[≠] 0) (𝓝 1) := by
      have := (Real.hasDerivAt_sin 0).tendsto_slope_zero
      simpa [div_eq_inv_mul] using this
    have h2 := (hs.comp hxt).pow 2
    have h3 := h2.const_mul (4 * Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2)
    rw [one_pow, mul_one] at h3
    refine h3.congr fun n => ?_
    simp only [Function.comp, sqnorm_mode_shift]
    have hxn : x n ^ 2 = Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2 * (1 / 4) ^ n := by
      simp only [hx]
      have : ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ n = (1 / 4) ^ n := by
        rw [← mul_pow]; norm_num
      calc _ = Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2 * ((1 / 2) ^ n * (1 / 2) ^ n) := by ring
        _ = _ := by rw [this]
    have h4 : (4 : ℝ) ^ n * (1 / 4) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [div_pow]
    have hxne : x n ^ 2 ≠ 0 := pow_ne_zero 2 (hx0 n)
    rw [hxn] at hxne ⊢
    field_simp
    rw [mul_comm ((1 / 4 : ℝ) ^ n), h4, one_mul]
    simp only [hx]
    ring_nf

theorem integrable_conj_mode_mul {F : Torus d → ℂ} (hF : MemLp F 2 volume) (k : Lattice d) :
    Integrable (fun x => conj (Torus.mode k x) * F x) := by
  have h1 : MemLp (fun x => conj (Torus.mode k x)) ⊤ volume :=
    memLp_top_of_continuous (Complex.continuous_conj.comp (Torus.continuous_mode k))
  exact (h1.mul hF).integrable one_le_two

theorem coeffOfC_translate (F : Torus d → ℂ) (h : Torus d) (k : Lattice d) :
    coeffOfC (fun x => F (x + h)) k = Torus.mode k h * coeffOfC F k := by
  rw [coeffOfC_eq_integral', coeffOfC_eq_integral']
  have h0 := integral_add_right_eq_self (μ := (volume : Measure (Torus d)))
    (fun y => conj (Torus.mode k (y - h)) * F y) h
  simp only [add_sub_cancel_right] at h0
  rw [h0, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : Torus.mode k y = Torus.mode k (y - h) * Torus.mode k h := by
    rw [← Torus.mode_add_arg]; simp
  have e2 : conj (Torus.mode k (y - h)) = conj (Torus.mode k y) * Torus.mode k h := by
    rw [e1, map_mul]
    have : conj (Torus.mode k h) * Torus.mode k h = 1 := by
      rw [Complex.conj_mul', Torus.norm_mode]; simp
    calc conj (Torus.mode k (y - h)) = conj (Torus.mode k (y - h)) * (conj (Torus.mode k h) * Torus.mode k h) := by
          rw [this, mul_one]
      _ = _ := by ring
  simp only [e2]; ring

theorem memLp_translate {F : Torus d → ℂ} (hF : MemLp F 2 volume) (h : Torus d) :
    MemLp (fun x => F (x + h)) 2 volume := by
  have := measurePreserving_add_right (volume : Measure (Torus d)) h
  exact hF.comp_measurePreserving this


theorem coeffOfC_sub_translate {F : Torus d → ℂ} (hF : MemLp F 2 volume) (h : Torus d) (k : Lattice d) :
    coeffOfC (fun x => F (x + h) - F x) k = (Torus.mode k h - 1) * coeffOfC F k := by
  rw [coeffOfC_eq_integral']
  simp only [mul_sub]
  rw [integral_sub (integrable_conj_mode_mul (memLp_translate hF h) k) (integrable_conj_mode_mul hF k),
    ← coeffOfC_eq_integral', ← coeffOfC_eq_integral', coeffOfC_translate]
  ring

/-- Parseval for a translation difference. -/
theorem diff_parseval {F : Torus d → ℂ} (hF : MemLp F 2 volume) (h : Torus d) :
    Summable (fun k => ‖Torus.mode k h - 1‖ ^ 2 * ‖coeffOfC F k‖ ^ 2) ∧
      ∑' k, ‖Torus.mode k h - 1‖ ^ 2 * ‖coeffOfC F k‖ ^ 2 = ∫ x, ‖F (x + h) - F x‖ ^ 2 := by
  have hG : MemLp (fun x => F (x + h) - F x) 2 volume := (memLp_translate hF h).sub hF
  obtain ⟨h1, h2⟩ := hsNormSq_zero_coeffOfC _ hG
  have e : ∀ k, ‖coeffOfC (fun x => F (x + h) - F x) k‖ ^ 2 =
      ‖Torus.mode k h - 1‖ ^ 2 * ‖coeffOfC F k‖ ^ 2 := fun k => by
    rw [coeffOfC_sub_translate hF h k, norm_mul, mul_pow]
  rw [memHs_zero_iff] at h1
  simp only [e] at h1
  refine ⟨h1, ?_⟩
  rw [hsNormSq_zero] at h2
  simp only [e] at h2
  exact h2

/-- the difference quotient step for a product `bF`: if `|b| ≤ A` and `|b(x+h) - b(x)| ≤ λ` then
`‖Δ_h(bF)‖² ≤ 2A²‖Δ_hF‖² + 2λ²‖F‖²` pointwise in `L²`. -/
theorem diff_product_bound {b : Torus d → ℝ} (hb : Continuous b) {F : Torus d → ℂ}
    (hF : MemLp F 2 volume) (A lam : ℝ) (hA : ∀ x, |b x| ≤ A) (h : Torus d)
    (hl : ∀ x, |b (x + h) - b x| ≤ lam) :
    ∫ x, ‖(b (x + h) : ℂ) * F (x + h) - (b x : ℂ) * F x‖ ^ 2 ≤
      2 * A ^ 2 * (∫ x, ‖F (x + h) - F x‖ ^ 2) + 2 * lam ^ 2 * ∫ x, ‖F x‖ ^ 2 := by
  have hbF := memLp_mul_of_continuous hb hF
  have hbFh := memLp_translate hbF h
  have hG : MemLp (fun x => (b (x + h) : ℂ) * F (x + h) - (b x : ℂ) * F x) 2 volume := hbFh.sub hbF
  have hD : MemLp (fun x => F (x + h) - F x) 2 volume := (memLp_translate hF h).sub hF
  rw [← integral_const_mul (2 * A ^ 2), ← integral_const_mul (2 * lam ^ 2), ← integral_add (hD.norm.integrable_sq.const_mul _)
    (hF.norm.integrable_sq.const_mul _)]
  refine integral_mono hG.norm.integrable_sq ((hD.norm.integrable_sq.const_mul _).add
    (hF.norm.integrable_sq.const_mul _)) fun x => ?_
  have e : (b (x + h) : ℂ) * F (x + h) - (b x : ℂ) * F x =
      (b (x + h) : ℂ) * (F (x + h) - F x) + ((b (x + h) - b x : ℝ) : ℂ) * F x := by
    push_cast; ring
  rw [e]
  have h1 : ‖(b (x + h) : ℂ) * (F (x + h) - F x)‖ ≤ A * ‖F (x + h) - F x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)
  have h2 : ‖((b (x + h) - b x : ℝ) : ℂ) * F x‖ ≤ lam * ‖F x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hl x) (norm_nonneg _)
  have h3 := norm_add_le ((b (x + h) : ℂ) * (F (x + h) - F x)) (((b (x + h) - b x : ℝ) : ℂ) * F x)
  have h0 : 0 ≤ ‖(b (x + h) : ℂ) * (F (x + h) - F x) + ((b (x + h) - b x : ℝ) : ℂ) * F x‖ := norm_nonneg _
  have h4 : ‖(b (x + h) : ℂ) * (F (x + h) - F x) + ((b (x + h) - b x : ℝ) : ℂ) * F x‖ ≤
      A * ‖F (x + h) - F x‖ + lam * ‖F x‖ := h3.trans (add_le_add h1 h2)
  calc _ ≤ (A * ‖F (x + h) - F x‖ + lam * ‖F x‖) ^ 2 := pow_le_pow_left₀ h0 h4 2
    _ ≤ 2 * (A * ‖F (x + h) - F x‖) ^ 2 + 2 * (lam * ‖F x‖) ^ 2 := by
        nlinarith [sq_nonneg (A * ‖F (x + h) - F x‖ - lam * ‖F x‖)]
    _ = _ := by ring




lemma memHs_zero_of_memHs {σ : ℝ} (hσ : 0 ≤ σ) {c : Coeff d} (hc : MemHs σ c) : MemHs 0 c := by
  rw [memHs_zero_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hc
  have := one_le_sobWeight σ hσ k
  nlinarith [sq_nonneg ‖c k‖]

lemma hsNormSq_zero_le {σ : ℝ} (hσ : 0 ≤ σ) {c : Coeff d} (hc : MemHs σ c) :
    hsNormSq 0 c ≤ hsNormSq σ c := by
  rw [hsNormSq_zero]
  refine (memHs_zero_iff c).1 (memHs_zero_of_memHs hσ hc) |>.tsum_le_tsum (fun k => ?_) hc
  have := one_le_sobWeight σ hσ k
  nlinarith [sq_nonneg ‖c k‖]

lemma norm_mode_sub_one_le (k : Lattice d) (h : Torus d) : ‖Torus.mode k h - 1‖ ≤ 2 := by
  calc ‖Torus.mode k h - 1‖ ≤ ‖Torus.mode k h‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Torus.norm_mode]; norm_num

lemma summable_G_mul {c : Coeff d} (hc : MemHs 0 c) (h : Torus d) :
    Summable (fun k => ‖Torus.mode k h - 1‖ ^ 2 * ‖c k‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (((memHs_zero_iff c).1 hc).mul_left 4)
  have := norm_mode_sub_one_le k h
  have h0 := norm_nonneg (Torus.mode k h - 1)
  have h2 : ‖Torus.mode k h - 1‖ ^ 2 ≤ 4 := by nlinarith
  calc _ ≤ 4 * ‖c k‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = _ := rfl

/-- the energy bound for the product `bc` -/
theorem energy_bound {b : Torus d → ℝ} (hb : Continuous b) {c : Coeff d} (hc : MemHs 0 c)
    (A lam : ℝ) (hA : ∀ x, |b x| ≤ A) (h : Torus d) (hl : ∀ x, |b (x + h) - b x| ≤ lam) :
    Summable (fun k => ‖Torus.mode k h - 1‖ ^ 2 * ‖mulCoeff (coeffOf b) c k‖ ^ 2) ∧
    ∑' k, ‖Torus.mode k h - 1‖ ^ 2 * ‖mulCoeff (coeffOf b) c k‖ ^ 2 ≤
      2 * A ^ 2 * ∑' k, ‖Torus.mode k h - 1‖ ^ 2 * ‖c k‖ ^ 2 + 2 * lam ^ 2 * hsNormSq 0 c := by
  set F := ofCoeff c with hFdef
  have hF : MemLp F 2 volume := memLp_ofCoeff hc
  have hFc : coeffOfC F = c := coeffOfC_ofCoeff hc
  have hmul := (mulCoeff_coeffOfC_mul hb hF).2
  rw [hFc] at hmul
  rw [hmul]
  have hbF := memLp_mul_of_continuous hb hF
  obtain ⟨s1, e1⟩ := diff_parseval hbF h
  obtain ⟨s2, e2⟩ := diff_parseval hF h
  rw [hFc] at s2 e2
  have hnorm := (hsNormSq_zero_coeffOfC F hF).2
  rw [hFc] at hnorm
  refine ⟨s1, ?_⟩
  rw [e1, e2, hnorm]
  exact diff_product_bound hb hF A lam hA h hl




lemma lower_vec' (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ S : Finset (Lattice d), ∃ N : ℕ, ∀ k ∈ S,
      sobWeight σ k ≤ L * (1 + ∑ i, ∑ n ∈ Finset.range N,
        ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2) := by
  obtain ⟨L, hL, hk⟩ := lower_vec hd σ hσ
  refine ⟨L, hL, fun S => ?_⟩
  choose Nk hNk using hk
  refine ⟨S.sup Nk, fun k hkS => ?_⟩
  refine (hNk k).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have : Nk k ≤ S.sup Nk := Finset.le_sup hkS
  have hmono : ∀ i : Fin d, ∑ n ∈ Finset.range (Nk k), ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 ≤
      ∑ n ∈ Finset.range (S.sup Nk), ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 := fun i =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono this) (fun n _ _ => by positivity)
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hmono i
  linarith

/-- Hypotheses of the product estimate (`b` bounded by `A`, with `2^{-n}`-translation increments
bounded by `Λ 2^{-n}`). -/
structure ProdHyp (b : Torus d → ℝ) (A Λ : ℝ) : Prop where
  cont : Continuous b
  A_nonneg : 0 ≤ A
  Λ_nonneg : 0 ≤ Λ
  bdd : ∀ x, |b x| ≤ A
  lip : ∀ (n : ℕ) (i : Fin d) (x : Torus d), |b (x + shift n i) - b x| ≤ Λ * (1 / 2) ^ n

lemma finset_rearrange (r : ℝ) (m : Coeff d) (S : Finset (Lattice d)) (N : ℕ) :
    ∑ k ∈ S, (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n * ‖mode k (shift n i) - 1‖ ^ 2) * ‖m k‖ ^ 2 =
      ∑ k ∈ S, ‖m k‖ ^ 2 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
        r ^ n * ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 := by
  have e : ∀ k ∈ S, (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n * ‖mode k (shift n i) - 1‖ ^ 2) * ‖m k‖ ^ 2 =
      ‖m k‖ ^ 2 + ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n * (‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2) := by
    intro k _
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]


lemma claim1 {σ : ℝ} (hσ : 0 ≤ σ) {U : ℝ}
    (hU : ∀ (k : Lattice d) (N : ℕ), ∑ i, ∑ n ∈ Finset.range N,
      ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 ≤ U * sobWeight σ k)
    {c : Coeff d} (hc : MemHs σ c) (N : ℕ) :
    ∑ i : Fin d, ∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n *
      ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2 ≤ U * hsNormSq σ c := by
  have hc0 := memHs_zero_of_memHs hσ hc
  have hH : ∀ i ∈ (Finset.univ : Finset (Fin d)), HasSum (fun k => ∑ n ∈ Finset.range N,
      ((4 : ℝ) ^ σ) ^ n * (‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2))
      (∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2) := by
    intro i _
    refine hasSum_sum fun n _ => ?_
    exact (summable_G_mul hc0 (shift n i)).hasSum.mul_left _
  have hH2 := hasSum_sum hH
  have hg : HasSum (fun k => U * (sobWeight σ k * ‖c k‖ ^ 2)) (U * hsNormSq σ c) :=
    hc.hasSum.mul_left U
  refine hasSum_le (fun k => ?_) hH2 hg
  have e : ∑ i : Fin d, ∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n * (‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2) =
      (∑ i : Fin d, ∑ n ∈ Finset.range N, ((4 : ℝ) ^ σ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2) * ‖c k‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [e]
  calc _ ≤ (U * sobWeight σ k) * ‖c k‖ ^ 2 := mul_le_mul_of_nonneg_right (hU k N) (sq_nonneg _)
    _ = _ := by ring


lemma supNorm_le_of_bdd {b : Torus d → ℝ} {A : ℝ} (hA : ∀ x, |b x| ≤ A) : Torus.supNorm b ≤ A :=
  ciSup_le fun x => by simpa using hA x

lemma sum_le_tsum_sq {m : Coeff d} (hm : MemHs 0 m) (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖m k‖ ^ 2 ≤ hsNormSq 0 m := by
  rw [hsNormSq_zero]
  exact ((memHs_zero_iff m).1 hm).sum_le_tsum S (fun k _ => sq_nonneg _)

theorem frac_bound_mid (hd : 1 ≤ d) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Torus d → ℝ) (A Λ : ℝ), ProdHyp b A Λ → ∀ c : Coeff d, MemHs σ c →
      MemHs σ (mulCoeff (coeffOf b) c) ∧
      hsNormSq σ (mulCoeff (coeffOf b) c) ≤ C * (A ^ 2 + Λ ^ 2) * hsNormSq σ c := by
  obtain ⟨U, hU0, hU⟩ := upper_vec (d := d) σ h0 h1
  obtain ⟨L, hL1, hL⟩ := lower_vec' hd σ h0.le
  set r : ℝ := (4 : ℝ) ^ σ with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) h0
  have hr4 : r < 4 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (4 : ℝ)) (by norm_num) h1
    simpa [hr] using this
  set ρ : ℝ := r / 4 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hgeom : ∀ N : ℕ, ∑ n ∈ Finset.range N, ρ ^ n ≤ 1 / (1 - ρ) := by
    intro N
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hρ0 hρ1
    rw [← Finset.range_eq_Ico] at this
    simpa using this
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨L * (1 + 2 * U + 2 * d / (1 - ρ)), by positivity, fun b A Λ H c hc => ?_⟩
  have hc0 := memHs_zero_of_memHs h0.le hc
  set m := mulCoeff (coeffOf b) c with hm
  obtain ⟨hm0, hm0'⟩ := mulCoeff_l2_bound H.cont hc0
  have hsup : Torus.supNorm b ≤ A := supNorm_le_of_bdd H.bdd
  have hsup0 := supNorm_nonneg b
  have hnc0 := hsNormSq_zero_nonneg c
  have hncσ := hsNormSq_zero_le h0.le hc
  have hmA : hsNormSq 0 m ≤ A ^ 2 * hsNormSq 0 c :=
    hm0'.trans (mul_le_mul_of_nonneg_right (by gcongr) hnc0)
  set B : ℝ := L * (1 + 2 * U + 2 * d / (1 - ρ)) * (A ^ 2 + Λ ^ 2) * hsNormSq σ c with hB
  have hbound : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight σ k * ‖m k‖ ^ 2 ≤ B := by
    intro S
    obtain ⟨N, hN⟩ := hL S
    have step1 : ∑ k ∈ S, sobWeight σ k * ‖m k‖ ^ 2 ≤
        ∑ k ∈ S, L * (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n * ‖mode k (shift n i) - 1‖ ^ 2) * ‖m k‖ ^ 2 :=
      Finset.sum_le_sum fun k hk => by
        have := hN k hk
        calc sobWeight σ k * ‖m k‖ ^ 2 ≤ (L * (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
            r ^ n * ‖mode k (shift n i) - 1‖ ^ 2)) * ‖m k‖ ^ 2 :=
              mul_le_mul_of_nonneg_right this (sq_nonneg _)
          _ = _ := by ring
    have step2 : ∑ k ∈ S, L * (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
        r ^ n * ‖mode k (shift n i) - 1‖ ^ 2) * ‖m k‖ ^ 2 =
        L * (∑ k ∈ S, ‖m k‖ ^ 2 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
          r ^ n * ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2) := by
      rw [← finset_rearrange r m S N, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    -- energy bounds
    have hE : ∀ (i : Fin d) (n : ℕ), ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 ≤
        2 * A ^ 2 * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2 +
          2 * Λ ^ 2 * (1 / 4) ^ n * hsNormSq 0 c := by
      intro i n
      obtain ⟨hs, hle⟩ := energy_bound H.cont hc0 A (Λ * (1 / 2) ^ n) H.bdd (shift n i) (H.lip n i)
      refine (hs.sum_le_tsum S (fun k _ => by positivity)).trans (hle.trans (le_of_eq ?_))
      have : (Λ * (1 / 2 : ℝ) ^ n) ^ 2 = Λ ^ 2 * (1 / 4) ^ n := by
        rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]; norm_num
      rw [this]; ring
    have step3 : ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n *
        ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 ≤
        2 * A ^ 2 * (U * hsNormSq σ c) + 2 * Λ ^ 2 * hsNormSq 0 c * (d * (1 / (1 - ρ))) := by
      calc _ ≤ ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n *
            (2 * A ^ 2 * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2 +
              2 * Λ ^ 2 * (1 / 4) ^ n * hsNormSq 0 c) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun n _ =>
              mul_le_mul_of_nonneg_left (hE i n) (by positivity)
        _ = 2 * A ^ 2 * (∑ i : Fin d, ∑ n ∈ Finset.range N,
              r ^ n * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2) +
            2 * Λ ^ 2 * hsNormSq 0 c * ∑ _i : Fin d, ∑ n ∈ Finset.range N, ρ ^ n := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun n _ => ?_
            have : ρ ^ n = r ^ n * (1 / 4) ^ n := by
              rw [hρ, ← mul_pow]; congr 1; ring
            rw [this]; ring
        _ ≤ _ := by
            have a1 := claim1 h0.le hU hc N
            have a2 : ∑ _i : Fin d, ∑ n ∈ Finset.range N, ρ ^ n ≤ d * (1 / (1 - ρ)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_left (hgeom N) hdd
            have hA2 : 0 ≤ 2 * A ^ 2 := by positivity
            have hL2 : 0 ≤ 2 * Λ ^ 2 * hsNormSq 0 c := by positivity
            exact add_le_add (mul_le_mul_of_nonneg_left a1 hA2) (mul_le_mul_of_nonneg_left a2 hL2)
    have key : ∑ k ∈ S, sobWeight σ k * ‖m k‖ ^ 2 ≤
        L * (A ^ 2 * hsNormSq 0 c + (2 * A ^ 2 * (U * hsNormSq σ c) +
          2 * Λ ^ 2 * hsNormSq 0 c * (d * (1 / (1 - ρ))))) := by
      refine step1.trans (le_of_eq step2 |>.trans ?_)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact add_le_add ((sum_le_tsum_sq hm0 S).trans hmA) step3
    refine key.trans ?_
    rw [hB]
    have e1 : A ^ 2 * hsNormSq 0 c ≤ A ^ 2 * hsNormSq σ c := mul_le_mul_of_nonneg_left hncσ (sq_nonneg A)
    have e2 : Λ ^ 2 * hsNormSq 0 c ≤ Λ ^ 2 * hsNormSq σ c := mul_le_mul_of_nonneg_left hncσ (sq_nonneg Λ)
    have hdr : 0 ≤ (d : ℝ) * (1 / (1 - ρ)) := by positivity
    have e3 : 2 * Λ ^ 2 * hsNormSq 0 c * (d * (1 / (1 - ρ))) ≤
        2 * Λ ^ 2 * hsNormSq σ c * (d * (1 / (1 - ρ))) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hdr
    have hL0 : 0 ≤ L := by linarith
    have hA2 : 0 ≤ A ^ 2 * hsNormSq σ c := mul_nonneg (sq_nonneg A) (hsNormSq_nonneg σ c)
    have hΛ2 : 0 ≤ Λ ^ 2 * hsNormSq σ c := mul_nonneg (sq_nonneg Λ) (hsNormSq_nonneg σ c)
    have hfin : A ^ 2 * hsNormSq 0 c + (2 * A ^ 2 * (U * hsNormSq σ c) +
          2 * Λ ^ 2 * hsNormSq 0 c * (d * (1 / (1 - ρ)))) ≤
        (1 + 2 * U + 2 * d / (1 - ρ)) * (A ^ 2 + Λ ^ 2) * hsNormSq σ c := by
      have : 2 * Λ ^ 2 * hsNormSq σ c * (d * (1 / (1 - ρ))) = 2 * d / (1 - ρ) * (Λ ^ 2 * hsNormSq σ c) := by
        field_simp
      have hu : 0 ≤ U := hU0
      have hq : 0 ≤ 2 * (d : ℝ) / (1 - ρ) := by positivity
      nlinarith [mul_nonneg hu hA2, mul_nonneg hq hA2, mul_nonneg hu hΛ2, hΛ2]
    calc _ ≤ L * (A ^ 2 * hsNormSq σ c + (2 * A ^ 2 * (U * hsNormSq σ c) +
          2 * Λ ^ 2 * hsNormSq σ c * (d * (1 / (1 - ρ))))) := by
          apply mul_le_mul_of_nonneg_left _ hL0
          linarith
      _ ≤ L * ((1 + 2 * U + 2 * d / (1 - ρ)) * (A ^ 2 + Λ ^ 2) * hsNormSq σ c) := by
          apply mul_le_mul_of_nonneg_left _ hL0
          have : 2 * Λ ^ 2 * hsNormSq σ c * (d * (1 / (1 - ρ))) = 2 * d / (1 - ρ) * (Λ ^ 2 * hsNormSq σ c) := by
            field_simp
          have hq : 0 ≤ 2 * (d : ℝ) / (1 - ρ) := by positivity
          nlinarith [mul_nonneg hU0 hA2, mul_nonneg hq hA2, mul_nonneg hU0 hΛ2, hΛ2, hA2]
      _ = _ := by ring
  have hnn : 0 ≤ fun k => sobWeight σ k * ‖m k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_pos σ k).le (sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩




lemma sq_le_sobWeight_one (k : Lattice d) (i : Fin d) : (2 * Real.pi * ((k i : ℤ) : ℝ)) ^ 2 ≤ sobWeight 1 k := by
  rw [sobWeight_one_eq]
  have := Finset.single_le_sum (f := fun j => (2 * Real.pi * ((k j : ℤ) : ℝ)) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

theorem frac_bound_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Torus d → ℝ) (A Λ : ℝ), ProdHyp b A Λ → ∀ c : Coeff d, MemHs 1 c →
      MemHs 1 (mulCoeff (coeffOf b) c) ∧
      hsNormSq 1 (mulCoeff (coeffOf b) c) ≤ C * (A ^ 2 + Λ ^ 2) * hsNormSq 1 c := by
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨1 + 2 * d, by positivity, fun b A Λ H c hc => ?_⟩
  have hc0 := memHs_zero_of_memHs zero_le_one hc
  set m := mulCoeff (coeffOf b) c with hm
  obtain ⟨hm0, hm0'⟩ := mulCoeff_l2_bound H.cont hc0
  have hsup : Torus.supNorm b ≤ A := supNorm_le_of_bdd H.bdd
  have hsup0 := supNorm_nonneg b
  have hnc0 := hsNormSq_zero_nonneg c
  have hncσ := hsNormSq_zero_le zero_le_one hc
  have hmA : hsNormSq 0 m ≤ A ^ 2 * hsNormSq 0 c :=
    hm0'.trans (mul_le_mul_of_nonneg_right (by gcongr) hnc0)
  set Bs : ℝ := 2 * A ^ 2 * hsNormSq 1 c + 2 * Λ ^ 2 * hsNormSq 0 c with hBs
  -- per-direction bound
  have hdir : ∀ (S : Finset (Lattice d)) (i : Fin d),
      ∑ k ∈ S, (2 * Real.pi * ((k i : ℤ) : ℝ)) ^ 2 * ‖m k‖ ^ 2 ≤ Bs := by
    intro S i
    have hn : ∀ n : ℕ, ∑ k ∈ S, (4 : ℝ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 ≤ Bs := by
      intro n
      obtain ⟨hs, hle⟩ := energy_bound H.cont hc0 A (Λ * (1 / 2) ^ n) H.bdd (shift n i) (H.lip n i)
      have h4 : (0 : ℝ) < 4 ^ n := by positivity
      have e1 : ∑ k ∈ S, (4 : ℝ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 =
          4 ^ n * ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [e1]
      have e2 : ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 ≤
          2 * A ^ 2 * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2 +
            2 * (Λ * (1 / 2) ^ n) ^ 2 * hsNormSq 0 c :=
        (hs.sum_le_tsum S (fun k _ => by positivity)).trans hle
      have e3 : (4 : ℝ) ^ n * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2 ≤ hsNormSq 1 c := by
        rw [← tsum_mul_left]
        refine (((summable_G_mul hc0 (shift n i)).mul_left _)).tsum_le_tsum (fun k => ?_) hc
        calc (4 : ℝ) ^ n * (‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2)
            = ((4 : ℝ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2) * ‖c k‖ ^ 2 := by ring
          _ ≤ sobWeight 1 k * ‖c k‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact (four_pow_mul_sqnorm_le k n i).trans (by
                have := sq_le_sobWeight_one k i
                nlinarith)
      have e4 : (Λ * (1 / 2 : ℝ) ^ n) ^ 2 * 4 ^ n = Λ ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
        have : ((1 : ℝ) / 2 ^ 2) ^ n * 4 ^ n = 1 := by rw [← mul_pow]; norm_num
        calc _ = Λ ^ 2 * (((1 : ℝ) / 2) ^ 2) ^ n * 4 ^ n := rfl
          _ = Λ ^ 2 * ((((1 : ℝ) / 2) ^ 2) ^ n * 4 ^ n) := by ring
          _ = Λ ^ 2 := by rw [← mul_pow]; norm_num
      calc 4 ^ n * ∑ k ∈ S, ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2
          ≤ 4 ^ n * (2 * A ^ 2 * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2 +
            2 * (Λ * (1 / 2) ^ n) ^ 2 * hsNormSq 0 c) := mul_le_mul_of_nonneg_left e2 h4.le
        _ = 2 * A ^ 2 * (4 ^ n * ∑' k, ‖mode k (shift n i) - 1‖ ^ 2 * ‖c k‖ ^ 2) +
            2 * ((Λ * (1 / 2 : ℝ) ^ n) ^ 2 * 4 ^ n) * hsNormSq 0 c := by ring
        _ ≤ 2 * A ^ 2 * hsNormSq 1 c + 2 * Λ ^ 2 * hsNormSq 0 c := by
            rw [e4]
            have hA2 : 0 ≤ 2 * A ^ 2 := by positivity
            exact add_le_add (mul_le_mul_of_nonneg_left e3 hA2) le_rfl
    have hlim : Tendsto (fun n : ℕ => ∑ k ∈ S, (4 : ℝ) ^ n * ‖mode k (shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2)
        atTop (𝓝 (∑ k ∈ S, 4 * Real.pi ^ 2 * ((k i : ℤ) : ℝ) ^ 2 * ‖m k‖ ^ 2)) :=
      tendsto_finsetSum _ fun k _ => (tendsto_four_pow_mul_sqnorm k i).mul_const _ |>.congr
        fun n => by ring
    have := le_of_tendsto' hlim hn
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => by ring)) this
  have hbound : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight 1 k * ‖m k‖ ^ 2 ≤
      (1 + 2 * d) * (A ^ 2 + Λ ^ 2) * hsNormSq 1 c := by
    intro S
    have e : ∑ k ∈ S, sobWeight 1 k * ‖m k‖ ^ 2 = ∑ k ∈ S, ‖m k‖ ^ 2 +
        ∑ i : Fin d, ∑ k ∈ S, (2 * Real.pi * ((k i : ℤ) : ℝ)) ^ 2 * ‖m k‖ ^ 2 := by
      simp_rw [sobWeight_one_eq, add_mul, one_mul, Finset.sum_mul]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    rw [e]
    have h1 : ∑ k ∈ S, ‖m k‖ ^ 2 ≤ A ^ 2 * hsNormSq 1 c :=
      (sum_le_tsum_sq hm0 S).trans (hmA.trans (mul_le_mul_of_nonneg_left hncσ (sq_nonneg A)))
    have h2 : ∑ i : Fin d, ∑ k ∈ S, (2 * Real.pi * ((k i : ℤ) : ℝ)) ^ 2 * ‖m k‖ ^ 2 ≤ d * Bs := by
      calc _ ≤ ∑ _i : Fin d, Bs := Finset.sum_le_sum fun i _ => hdir S i
        _ = d * Bs := by simp
    have hB2 : Bs ≤ 2 * (A ^ 2 + Λ ^ 2) * hsNormSq 1 c := by
      rw [hBs]
      have : Λ ^ 2 * hsNormSq 0 c ≤ Λ ^ 2 * hsNormSq 1 c := mul_le_mul_of_nonneg_left hncσ (sq_nonneg Λ)
      nlinarith
    have hA1 : 0 ≤ A ^ 2 * hsNormSq 1 c := mul_nonneg (sq_nonneg A) (hsNormSq_nonneg 1 c)
    have hΛ1 : 0 ≤ Λ ^ 2 * hsNormSq 1 c := mul_nonneg (sq_nonneg Λ) (hsNormSq_nonneg 1 c)
    nlinarith [mul_le_mul_of_nonneg_left hB2 hdd]
  have hnn : 0 ≤ fun k => sobWeight 1 k * ‖m k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_pos 1 k).le (sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩




theorem frac_bound (hd : 1 ≤ d) (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Torus d → ℝ) (A Λ : ℝ), ProdHyp b A Λ → ∀ c : Coeff d, MemHs σ c →
      MemHs σ (mulCoeff (coeffOf b) c) ∧
      hsNormSq σ (mulCoeff (coeffOf b) c) ≤ C * (A ^ 2 + Λ ^ 2) * hsNormSq σ c := by
  rcases h0.eq_or_lt with h | h
  · subst h
    refine ⟨1, zero_le_one, fun b A Λ H c hc => ?_⟩
    obtain ⟨hm0, hm0'⟩ := mulCoeff_l2_bound H.cont hc
    refine ⟨hm0, hm0'.trans ?_⟩
    have hsup : Torus.supNorm b ≤ A := supNorm_le_of_bdd H.bdd
    have hsup0 := supNorm_nonneg b
    have hnc0 := hsNormSq_zero_nonneg c
    have : Torus.supNorm b ^ 2 ≤ A ^ 2 := by gcongr
    nlinarith [sq_nonneg Λ, mul_nonneg (sq_nonneg Λ) hnc0]
  rcases h1.eq_or_lt with h' | h'
  · subst h'
    exact frac_bound_one
  · exact frac_bound_mid hd σ h h'




lemma centeredRep_apply (z : Torus d) (i : Fin d) :
    Torus.centeredRep z i = if Torus.rep z i ≤ 1 / 2 then Torus.rep z i else Torus.rep z i - 1 := by
  simp [Torus.centeredRep]

lemma rep_coord (z : Torus d) (i : Fin d) :
    0 ≤ Torus.rep z i ∧ Torus.rep z i < 1 ∧ (((Torus.rep z i : ℝ)) : UnitAddCircle) = z i := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 (z i)).2
  simp only [zero_add] at h
  refine ⟨h.1, h.2, ?_⟩
  have := AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := z i)
  simpa [Torus.rep] using this

lemma abs_centeredRep (z : Torus d) (i : Fin d) : |Torus.centeredRep z i| = ‖z i‖ := by
  obtain ⟨h0, h1, h2⟩ := rep_coord z i
  rw [centeredRep_apply]
  split_ifs with h
  · rw [← h2, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := Torus.rep z i) (by norm_num)).2
      (by rw [abs_of_nonneg h0]; simpa using h)]
  · have : (((Torus.rep z i - 1 : ℝ)) : UnitAddCircle) = z i := by
      rw [← h2]; push_cast
      simp
    rw [← this, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := Torus.rep z i - 1) (by norm_num)).2]
    rw [abs_of_neg (by linarith)]
    push Not at h
    simp only [abs_one]; linarith

lemma tdist_le (x y : Torus d) : Torus.tdist x y ≤ Real.sqrt d * ‖x - y‖ := by
  unfold Torus.tdist
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖(Torus.centeredRep (x - y)) i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin d, ‖x - y‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs, abs_centeredRep]
        have := norm_le_pi_norm (x - y) i
        gcongr
    _ = Real.sqrt d * ‖x - y‖ := by
        simp [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg _)]


lemma norm_circle_le_abs (t : ℝ) : ‖((t : ℝ) : UnitAddCircle)‖ ≤ |t| := by
  rw [AddCircle.norm_eq]
  have := round_le (t * 1) 0
  simpa using this

lemma norm_shift_le (n : ℕ) (i : Fin d) : ‖(shift n i : Torus d)‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  have : (shift n i : Torus d) j = ((((1 / 2 : ℝ) ^ n • (EuclideanSpace.single i (1 : ℝ) : Euc d)) j : ℝ) : UnitAddCircle) := rfl
  rw [this]
  refine (norm_circle_le_abs _).trans ?_
  by_cases hj : j = i
  · subst hj; simp [abs_of_nonneg]
  · simp [hj]

/-- A Lipschitz function on the torus satisfies the hypotheses of the product estimate with
`A = ‖a‖_∞`, `Λ = [a]_{C^{0,1}}`. -/
theorem prodHyp_of_lipschitz {La : ℝ} {a : Torus d → ℝ} (h : Torus.IsLipschitz La a) :
    ProdHyp a (Torus.supNorm a) (Torus.holderSeminorm 1 a) := by
  have hdist : ∀ x y : Torus d, |a x - a y| ≤ |La| * Real.sqrt d * ‖x - y‖ := by
    intro x y
    calc |a x - a y| ≤ La * Torus.tdist x y := h x y
      _ ≤ |La| * Torus.tdist x y := by
          apply mul_le_mul_of_nonneg_right (le_abs_self _)
          exact norm_nonneg _
      _ ≤ |La| * (Real.sqrt d * ‖x - y‖) := mul_le_mul_of_nonneg_left (tdist_le x y) (abs_nonneg _)
      _ = _ := by ring
  have hcont : Continuous a := by
    have : LipschitzWith (Real.toNNReal (|La| * Real.sqrt d)) a := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      exact hdist x y
    exact this.continuous
  have hbdd : BddAbove (Set.range fun p : {p : Torus d × Torus d // p.1 ≠ p.2} =>
      |a p.1.1 - a p.1.2| / ‖p.1.1 - p.1.2‖ ^ (1 : ℝ)) := by
    refine ⟨|La| * Real.sqrt d, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hp : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
    show |a p.1.1 - a p.1.2| / ‖p.1.1 - p.1.2‖ ^ (1 : ℝ) ≤ _
    rw [Real.rpow_one, div_le_iff₀ hp]
    exact hdist _ _
  have hΛ : 0 ≤ Torus.holderSeminorm 1 a := by
    unfold Torus.holderSeminorm
    exact Real.iSup_nonneg fun p => by positivity
  refine ⟨hcont, supNorm_nonneg a, hΛ, fun x => by simpa using norm_le_supNorm hcont x, ?_⟩
  intro n i x
  by_cases hs : shift n i = 0
  · rw [hs]; simp only [add_zero, sub_self, abs_zero]; positivity
  · have hne : x + shift n i ≠ x := by simpa using hs
    have h1 : |a (x + shift n i) - a x| / ‖x + shift n i - x‖ ^ (1 : ℝ) ≤ Torus.holderSeminorm 1 a :=
      le_ciSup hbdd (⟨(x + shift n i, x), hne⟩ : {p : Torus d × Torus d // p.1 ≠ p.2})
    have hp : 0 < ‖x + shift n i - x‖ := norm_pos_iff.2 (by simpa using hs)
    rw [Real.rpow_one, div_le_iff₀ hp] at h1
    have h2 : ‖x + shift n i - x‖ ≤ (1 / 2 : ℝ) ^ n := by
      simpa using norm_shift_le n i
    calc _ ≤ _ := h1
      _ ≤ Torus.holderSeminorm 1 a * (1 / 2) ^ n := mul_le_mul_of_nonneg_left h2 hΛ




lemma sobWeight_eq_jp' (m : ℝ) (k : Lattice d) : sobWeight m k = Lattice.jp k ^ (2 * m) := by
  unfold sobWeight Lattice.jp
  have hB : 0 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hB]
  congr 1; ring

lemma coeffOf_eq_fcoef (φ : Torus d → ℝ) (k : Lattice d) : coeffOf φ k = Torus.fcoef φ k := by
  rw [coeffOf_eq_coeffOfC, coeffOfC_eq_integral']
  unfold Torus.fcoef
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show conj (Torus.mode k x) * _ = Torus.mode (-k) x * _
  rw [Torus.mode_neg]

lemma integrable_of_memLp_two {φ : Torus d → ℝ} (h : MemLp φ 2 volume) : Integrable φ :=
  h.integrable one_le_two

/-- Summability over the nonzero lattice and at zero. -/
lemma summable_of_nonzero {f : Lattice d → ℝ}
    (h : Summable fun k : NonzeroLattice d => f k.1) : Summable f := by
  rw [← Finset.summable_compl_iff ({0} : Finset (Lattice d))]
  exact (Equiv.subtypeEquivRight (p := fun k : Lattice d => k ≠ 0)
    (q := fun k : Lattice d => k ∉ ({0} : Finset (Lattice d))) (by intro k; simp)).symm.summable_iff.2 h |>.congr (fun _ => rfl)


lemma sobWeight_zero_lattice (m : ℝ) : sobWeight m (0 : Lattice d) = 1 := by
  have h0 : Lattice.enorm (0 : Lattice d) ^ 2 = 0 := by rw [enorm_sq]; simp
  unfold sobWeight; rw [h0]; simp

lemma tsum_split {f : Lattice d → ℝ} (hf : Summable f) :
    ∑' k, f k = f 0 + ∑' k : NonzeroLattice d, f k.1 := by
  have h := hf.sum_add_tsum_subtype_compl ({0} : Finset (Lattice d))
  rw [Finset.sum_singleton] at h
  rw [← h]
  congr 1
  exact (Equiv.tsum_eq (Equiv.subtypeEquivRight (p := fun k : Lattice d => k ≠ 0)
    (q := fun k : Lattice d => k ∉ ({0} : Finset (Lattice d))) (by intro k; simp)) (fun b => f b.1)).symm

theorem memHs_of_memSobolev (m : ℝ) {φ : Torus d → ℝ} (h : MemSobolev m φ) :
    MemHs m (coeffOf φ) ∧ hsNormSq m (coeffOf φ) = sobolevNorm m φ ^ 2 := by
  have hint := integrable_of_memLp_two h.1
  obtain ⟨hs1, hs2⟩ := Torus.weighted_fcoef_sq (2 * m) hint h.2
  have hf : ∀ k : Lattice d, sobWeight m k * ‖coeffOf φ k‖ ^ 2 =
      Lattice.jp k ^ (2 * m) * ‖Torus.fcoef φ k‖ ^ 2 := fun k => by
    rw [sobWeight_eq_jp', coeffOf_eq_fcoef]
  have hmem : MemHs m (coeffOf φ) := by
    unfold MemHs
    simp_rw [hf]
    exact summable_of_nonzero hs1
  refine ⟨hmem, ?_⟩
  unfold hsNormSq sobolevNorm
  rw [tsum_split hmem, Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
  congr 1
  · rw [coeffOf_eq_fcoef, Torus.fcoef_zero]
    rw [sobWeight_zero_lattice]; simp
  · simp_rw [hf]
    exact hs2


theorem memSobolev_of_memHs' (m : ℝ) {φ : Torus d → ℝ} (hL : MemLp φ 2 volume)
    (h : MemHs m (coeffOf φ)) : MemSobolev m φ ∧ sobolevNorm m φ ^ 2 = hsNormSq m (coeffOf φ) := by
  have hint := integrable_of_memLp_two hL
  have hf : ∀ k : Lattice d, sobWeight m k * ‖coeffOf φ k‖ ^ 2 =
      Lattice.jp k ^ (2 * m) * ‖Torus.fcoef φ k‖ ^ 2 := fun k => by
    rw [sobWeight_eq_jp', coeffOf_eq_fcoef]
  have hs1 : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef φ k.1‖ ^ 2 := by
    have := h.comp_injective (Subtype.val_injective (p := fun k : Lattice d => k ≠ 0))
    simpa [Function.comp_def, hf] using this
  have hs2 : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
      (fun k => ?_) (hs1.mul_left 2)
    have e := Torus.two_mul_norm_fcoef_sq hint k
    have hj : 0 ≤ Lattice.jp k.1 ^ (2 * m) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have : Torus.funRealCoeff φ k ^ 2 ≤ 2 * ‖Torus.fcoef φ k.1‖ ^ 2 := by
      rw [e]; nlinarith [sq_nonneg (Torus.funRealCoeff φ (Torus.negNZ d k))]
    calc _ ≤ Lattice.jp k.1 ^ (2 * m) * (2 * ‖Torus.fcoef φ k.1‖ ^ 2) := mul_le_mul_of_nonneg_left this hj
      _ = _ := by ring
  have hM : MemSobolev m φ := ⟨hL, hs2⟩
  exact ⟨hM, (memHs_of_memSobolev m hM).2.symm⟩




lemma memLp_real_mul {b u : Torus d → ℝ} (hb : Continuous b) (hu : MemLp u 2 volume) :
    MemLp (fun x => b x * u x) 2 volume := by
  have h1 : MemLp b ⊤ volume := hb.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact h1.mul hu

lemma coeffOf_mul' {b u : Torus d → ℝ} (hb : Continuous b) (hu : MemLp u 2 volume) :
    coeffOf (fun x => b x * u x) = mulCoeff (coeffOf b) (coeffOf u) := by
  have hF : MemLp (fun x => (u x : ℂ)) 2 volume := by
    exact (Complex.ofRealCLM.lipschitzWith.comp_memLp (by simp) hu)
  have := (mulCoeff_coeffOfC_mul hb hF).2
  have e : (fun x => ((b x * u x : ℝ) : ℂ)) = fun x => (b x : ℂ) * (u x : ℂ) := by
    funext x; push_cast; rfl
  rw [coeffOf_eq_coeffOfC, e]
  exact this.symm

/-- Real-function form of the product estimate. -/
theorem real_product_bound (hd : 1 ≤ d) (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Torus d → ℝ) (A Λ : ℝ), ProdHyp a A Λ → ∀ u : Torus d → ℝ, MemSobolev σ u →
      MemSobolev σ (fun x => a x * u x) ∧
      sobolevNorm σ (fun x => a x * u x) ≤ C * (A + Λ) * sobolevNorm σ u := by
  obtain ⟨C₀, hC₀, hC⟩ := frac_bound hd σ h0 h1
  refine ⟨Real.sqrt C₀, Real.sqrt_nonneg _, fun a A Λ H u hu => ?_⟩
  obtain ⟨hmem, hnorm⟩ := memHs_of_memSobolev σ hu
  obtain ⟨hm, hm'⟩ := hC a A Λ H _ hmem
  have hL := memLp_real_mul H.cont hu.1
  have hco := coeffOf_mul' H.cont hu.1
  rw [← hco] at hm hm'
  obtain ⟨hM, hMn⟩ := memSobolev_of_memHs' σ hL hm
  refine ⟨hM, ?_⟩
  rw [← hMn, hnorm] at hm'
  have hAΛ : 0 ≤ A + Λ := add_nonneg H.A_nonneg H.Λ_nonneg
  have hs0 : 0 ≤ sobolevNorm σ u := Real.sqrt_nonneg _
  have hs1 : 0 ≤ sobolevNorm σ (fun x => a x * u x) := Real.sqrt_nonneg _
  have : sobolevNorm σ (fun x => a x * u x) ^ 2 ≤ (Real.sqrt C₀ * (A + Λ) * sobolevNorm σ u) ^ 2 := by
    refine hm'.trans ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hC₀]
    have : A ^ 2 + Λ ^ 2 ≤ (A + Λ) ^ 2 := by nlinarith [H.A_nonneg, H.Λ_nonneg, mul_nonneg H.A_nonneg H.Λ_nonneg]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC₀) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ hs1 (by positivity) two_ne_zero).1 this




lemma sobWeight_succ_mul_sq (s : ℝ) (c : Coeff d) (k : Lattice d) :
    sobWeight (s + 1) k * ‖c k‖ ^ 2 =
      sobWeight s k * ‖c k‖ ^ 2 + ∑ j, sobWeight s k * ‖derivCoeff j c k‖ ^ 2 := by
  rw [sobWeight_add, mul_assoc, sobWeight_one_mul_sq, mul_add, Finset.mul_sum]

lemma memHs_succ_iff (s : ℝ) (c : Coeff d) :
    MemHs (s + 1) c ↔ MemHs s c ∧ ∀ j, MemHs s (derivCoeff j c) := by
  have hnn : ∀ (t : ℝ) (e : Coeff d) (k : Lattice d), 0 ≤ sobWeight t k * ‖e k‖ ^ 2 :=
    fun t e k => mul_nonneg (sobWeight_pos t k).le (sq_nonneg _)
  unfold MemHs
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · refine Summable.of_nonneg_of_le (hnn s c) (fun k => ?_) h
      rw [sobWeight_succ_mul_sq]
      have : 0 ≤ ∑ j, sobWeight s k * ‖derivCoeff j c k‖ ^ 2 := Finset.sum_nonneg fun j _ => hnn s _ k
      linarith
    · refine Summable.of_nonneg_of_le (hnn s _) (fun k => ?_) h
      rw [sobWeight_succ_mul_sq]
      have := Finset.single_le_sum (f := fun j => sobWeight s k * ‖derivCoeff j c k‖ ^ 2)
        (fun i _ => hnn s _ k) (Finset.mem_univ j)
      linarith [hnn s c k]
  · rintro ⟨h0, h1⟩
    simp_rw [sobWeight_succ_mul_sq]
    exact h0.add (summable_sum fun j _ => h1 j)

lemma hsNormSq_succ (s : ℝ) (c : Coeff d) (h : MemHs (s + 1) c) :
    hsNormSq (s + 1) c = hsNormSq s c + ∑ j, hsNormSq s (derivCoeff j c) := by
  obtain ⟨h0, h1⟩ := (memHs_succ_iff s c).1 h
  unfold hsNormSq
  simp_rw [sobWeight_succ_mul_sq]
  rw [Summable.tsum_add h0 (summable_sum fun j _ => h1 j),
    Summable.tsum_finsetSum fun j _ => h1 j]

lemma hsNormSq_add_le (s : ℝ) {x y : Coeff d} (hx : MemHs s x) (hy : MemHs s y) :
    MemHs s (x + y) ∧ hsNormSq s (x + y) ≤ 2 * hsNormSq s x + 2 * hsNormSq s y := by
  have hle : ∀ k, sobWeight s k * ‖(x + y) k‖ ^ 2 ≤
      2 * (sobWeight s k * ‖x k‖ ^ 2) + 2 * (sobWeight s k * ‖y k‖ ^ 2) := by
    intro k
    have := norm_add_le (x k) (y k)
    have h2 : ‖(x + y) k‖ ^ 2 ≤ 2 * ‖x k‖ ^ 2 + 2 * ‖y k‖ ^ 2 := by
      simp only [Pi.add_apply]
      nlinarith [norm_nonneg (x k), norm_nonneg (y k), sq_nonneg (‖x k‖ - ‖y k‖),
        norm_nonneg (x k + y k)]
    have hw := (sobWeight_pos s k).le
    nlinarith [mul_le_mul_of_nonneg_left h2 hw]
  have hs : MemHs s (x + y) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos s k).le (sq_nonneg _)) hle
      ((hx.mul_left 2).add (hy.mul_left 2))
  refine ⟨hs, ?_⟩
  unfold hsNormSq
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hx.mul_left 2).tsum_add (hy.mul_left 2)]
  exact hs.tsum_le_tsum hle ((hx.mul_left 2).add (hy.mul_left 2))




lemma cbNorm_mono {m n : ℕ} (h : m ≤ n) (φ : Torus d → ℝ) : Torus.cbNorm m φ ≤ Torus.cbNorm n φ := by
  unfold Torus.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun j _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

lemma isCk_partialDeriv {n : ℕ} {b : Torus d → ℝ} (hb : Torus.IsCk (n + 1 : ℕ) b) (j : Fin d) :
    Torus.IsCk (n : ℕ) (Torus.partialDeriv j b) := by
  have hb1 : Torus.IsCk 1 b := hb.of_le (by exact_mod_cast Nat.le_add_left 1 n)
  have e : Torus.lift (Torus.partialDeriv j b) =
      fun y => fderiv ℝ (Torus.lift b) y (EuclideanSpace.single j 1) := by
    funext y; exact partialDeriv_mk j b hb1 y
  unfold Torus.IsCk
  rw [e]
  have : ContDiff ℝ (n : ℕ) (fderiv ℝ (Torus.lift b)) := hb.fderiv_right (by push_cast; exact le_rfl)
  exact this.clm_apply contDiff_const

lemma cbNorm_partialDeriv_le {n : ℕ} {b : Torus d → ℝ} (hb : Torus.IsCk (n + 1 : ℕ) b) (j : Fin d) :
    Torus.cbNorm n (Torus.partialDeriv j b) ≤ Torus.cbNorm (n + 1) b := by
  have hb1 : Torus.IsCk 1 b := hb.of_le (by exact_mod_cast Nat.le_add_left 1 n)
  have e : Torus.lift (Torus.partialDeriv j b) =
      fun y => fderiv ℝ (Torus.lift b) y (EuclideanSpace.single j 1) := by
    funext y; exact partialDeriv_mk j b hb1 y
  unfold Torus.cbNorm
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (Torus.partialDeriv j b)) y‖) ≤
        ⨆ y : Euc d, ‖iteratedFDeriv ℝ (i + 1) (Torus.lift b) y‖ := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hcd : ContDiff ℝ ((i + 1 : ℕ)) (Torus.lift b) := hb.of_le (by exact_mod_cast Nat.succ_le_succ hi')
    refine ciSup_le fun y => ?_
    rw [e]
    have hfd : ContDiffAt ℝ ((i : ℕ) : WithTop ℕ∞) (fderiv ℝ (Torus.lift b)) y :=
      (hcd.fderiv_right (by push_cast; exact le_rfl)).contDiffAt
    have := norm_iteratedFDeriv_clm_apply_const (c := (EuclideanSpace.single j (1 : ℝ) : Euc d))
      (n := i) (N := ((i : ℕ) : WithTop ℕ∞)) hfd le_rfl
    rw [PiLp.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at this
    exact this.trans (le_ciSup (Torus.bddAbove_norm_iteratedFDeriv_lift (i + 1) b hcd) y)
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), ⨆ y : Euc d, ‖iteratedFDeriv ℝ (i + 1) (Torus.lift b) y‖ :=
        Finset.sum_le_sum hterm
    _ = ∑ i ∈ Finset.Ico 1 (n + 2), ⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift b) y‖ := by
        rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr (by simp) fun i _ => by rw [add_comm 1 i]
    _ ≤ ∑ i ∈ Finset.range (n + 1 + 1), ⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift b) y‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
          simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega)
          (fun j _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)




lemma norm_fderiv_le_cbNorm {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) (y : Euc d) :
    ‖fderiv ℝ (Torus.lift b) y‖ ≤ Torus.cbNorm 1 b := by
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 1 (Torus.lift b) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 1 b (by exact_mod_cast hb)
  have h1 := le_ciSup hbdd y
  rw [norm_iteratedFDeriv_one] at h1
  refine h1.trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift b) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num))

lemma lip_shift {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) (n : ℕ) (i : Fin d) (x : Torus d) :
    |b (x + shift n i) - b x| ≤ Torus.cbNorm 1 b * (1 / 2) ^ n := by
  set t : ℝ := (1 / 2) ^ n with ht
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hmk : Torus.mk (Torus.rep x + t • e) = x + shift n i := by
    rw [Torus.mk_add, Torus.mk_rep]; rfl
  have h1 : (hb : ContDiff ℝ 1 (Torus.lift b)) = hb := rfl
  have hMVT := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift b) (s := Set.univ)
    (C := Torus.cbNorm 1 b) (x := Torus.rep x) (y := Torus.rep x + t • e)
    (fun y _ => ((hb : ContDiff ℝ 1 (Torus.lift b)).differentiable one_ne_zero) y)
    (fun y _ => norm_fderiv_le_cbNorm hb y) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have e1 : Torus.lift b (Torus.rep x + t • e) = b (x + shift n i) := by
    simp only [Torus.lift, Function.comp, hmk]
  have e2 : Torus.lift b (Torus.rep x) = b x := by
    simp [Torus.lift, Torus.mk_rep]
  rw [e1, e2, Real.norm_eq_abs] at hMVT
  have : ‖Torus.rep x + t • e - Torus.rep x‖ = t := by
    rw [add_sub_cancel_left, norm_smul, he, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rwa [this] at hMVT

theorem prodHyp_of_isCk1 {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) :
    ProdHyp b (Torus.cbNorm 1 b) (Torus.cbNorm 1 b) where
  cont := continuous_of_isCk hb
  A_nonneg := cbNorm_nonneg 1 b
  Λ_nonneg := cbNorm_nonneg 1 b
  bdd := fun x => by
    have := norm_le_supNorm (continuous_of_isCk hb) x
    rw [Real.norm_eq_abs] at this
    exact this.trans (supNorm_le_cbNorm 1 hb)
  lip := lip_shift hb




/-- The product bound `‖b c‖_{H^σ} ≤ C ‖b‖_{C^{⌈σ⌉}} ‖c‖_{H^σ}` at the level of coefficients. -/
def ProdBound (d : ℕ) (σ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Torus d → ℝ, Torus.IsCk (⌈σ⌉₊ : ℕ) b → ∀ c : Coeff d, MemHs σ c →
    MemHs σ (mulCoeff (coeffOf b) c) ∧
    hsNormSq σ (mulCoeff (coeffOf b) c) ≤ C * Torus.cbNorm ⌈σ⌉₊ b ^ 2 * hsNormSq σ c

theorem prodBound_base (hd : 1 ≤ d) (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) : ProdBound d σ := by
  rcases h0.eq_or_lt with h | h
  · subst h
    refine ⟨1, zero_le_one, fun b hb c hc => ?_⟩
    simp only [Nat.ceil_zero] at hb ⊢
    have hcont : Continuous b := continuous_of_lift' (by simpa [Torus.IsCk] using hb.continuous)
    obtain ⟨hm0, hm0'⟩ := mulCoeff_l2_bound hcont hc
    refine ⟨hm0, hm0'.trans ?_⟩
    have := supNorm_le_cbNorm 0 hb
    have h0' := supNorm_nonneg b
    have hn := hsNormSq_zero_nonneg c
    have : Torus.supNorm b ^ 2 ≤ Torus.cbNorm 0 b ^ 2 := by gcongr
    nlinarith
  · have hce : ⌈σ⌉₊ = 1 := (Nat.ceil_eq_iff (by norm_num)).2 ⟨by simpa using h, by simpa using h1⟩
    obtain ⟨C₀, hC₀, hC⟩ := frac_bound hd σ h.le h1
    refine ⟨2 * C₀, by positivity, fun b hb c hc => ?_⟩
    rw [hce] at hb ⊢
    obtain ⟨h1', h2'⟩ := hC b _ _ (prodHyp_of_isCk1 (by simpa using hb)) c hc
    refine ⟨h1', h2'.trans (le_of_eq ?_)⟩
    ring

theorem prodBound_step (hd : 1 ≤ d) (s : ℝ) (hs : 0 ≤ s) (IH : ProdBound d s) :
    ProdBound d (s + 1) := by
  obtain ⟨C', hC', hC⟩ := IH
  have hceil : ⌈s + 1⌉₊ = ⌈s⌉₊ + 1 := Nat.ceil_add_one hs
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨(2 * d + 3) * C', by positivity, fun b hb c hc => ?_⟩
  rw [hceil] at hb ⊢
  set m := ⌈s⌉₊ with hm
  have hb1 : Torus.IsCk 1 b := hb.of_le (by exact_mod_cast Nat.le_add_left 1 m)
  have hbm : Torus.IsCk (m : ℕ) b := hb.of_le (by exact_mod_cast Nat.le_succ m)
  obtain ⟨hcs, hdc⟩ := (memHs_succ_iff s c).1 hc
  have hc1 : MemHs 1 c := MemHs.mono (by linarith) hc
  set M := Torus.cbNorm (m + 1) b with hM
  have hM0 : 0 ≤ M := cbNorm_nonneg _ b
  have hbM : Torus.cbNorm m b ≤ M := cbNorm_mono (Nat.le_succ m) b
  have hbM0 := cbNorm_nonneg m b
  have hbm2 : Torus.cbNorm m b ^ 2 ≤ M ^ 2 := by gcongr
  obtain ⟨hA1, hA2⟩ := hC b hbm c hcs
  have hB : ∀ j, MemHs s (mulCoeff (coeffOf b) (derivCoeff j c)) ∧
      hsNormSq s (mulCoeff (coeffOf b) (derivCoeff j c)) ≤
        C' * M ^ 2 * hsNormSq s (derivCoeff j c) := fun j => by
    obtain ⟨h1, h2⟩ := hC b hbm _ (hdc j)
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbm2 hC') (hsNormSq_nonneg _ _)
  have hP : ∀ j, MemHs s (mulCoeff (coeffOf (Torus.partialDeriv j b)) c) ∧
      hsNormSq s (mulCoeff (coeffOf (Torus.partialDeriv j b)) c) ≤ C' * M ^ 2 * hsNormSq s c := fun j => by
    have hpd := isCk_partialDeriv hb j
    obtain ⟨h1, h2⟩ := hC _ hpd c hcs
    refine ⟨h1, h2.trans ?_⟩
    have e1 : Torus.cbNorm m (Torus.partialDeriv j b) ≤ M := cbNorm_partialDeriv_le hb j
    have e0 := cbNorm_nonneg m (Torus.partialDeriv j b)
    have e2 : Torus.cbNorm m (Torus.partialDeriv j b) ^ 2 ≤ M ^ 2 := by gcongr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hC') (hsNormSq_nonneg _ _)
  have hsum : ∀ j, MemHs s (derivCoeff j (mulCoeff (coeffOf b) c)) ∧
      hsNormSq s (derivCoeff j (mulCoeff (coeffOf b) c)) ≤
        2 * (C' * M ^ 2 * hsNormSq s c) + 2 * (C' * M ^ 2 * hsNormSq s (derivCoeff j c)) := fun j => by
    rw [derivCoeff_mulCoeffC hb1 hc1 j]
    obtain ⟨h1, h2⟩ := hsNormSq_add_le s (hP j).1 (hB j).1
    refine ⟨h1, h2.trans ?_⟩
    linarith [(hP j).2, (hB j).2]
  have hmem : MemHs (s + 1) (mulCoeff (coeffOf b) c) := (memHs_succ_iff s _).2 ⟨hA1, fun j => (hsum j).1⟩
  refine ⟨hmem, ?_⟩
  rw [hsNormSq_succ s _ hmem, hsNormSq_succ s _ hc]
  have hX := hsNormSq_nonneg s c
  have hY : ∀ j, 0 ≤ hsNormSq s (derivCoeff j c) := fun j => hsNormSq_nonneg _ _
  have hYs : 0 ≤ ∑ j, hsNormSq s (derivCoeff j c) := Finset.sum_nonneg fun j _ => hY j
  have h2 : ∑ j, hsNormSq s (derivCoeff j (mulCoeff (coeffOf b) c)) ≤
      ∑ j, (2 * (C' * M ^ 2 * hsNormSq s c) + 2 * (C' * M ^ 2 * hsNormSq s (derivCoeff j c))) :=
    Finset.sum_le_sum fun j _ => (hsum j).2
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at h2
  have hK : 0 ≤ C' * M ^ 2 := by positivity
  have hA2' : hsNormSq s (mulCoeff (coeffOf b) c) ≤ C' * M ^ 2 * hsNormSq s c :=
    hA2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbm2 hC') hX)
  have e3 : ∑ i, C' * M ^ 2 * hsNormSq s (derivCoeff i c) = C' * M ^ 2 * ∑ i, hsNormSq s (derivCoeff i c) :=
    (Finset.mul_sum _ _ _).symm
  rw [e3] at h2
  nlinarith [mul_nonneg hK hX, mul_nonneg hK hYs, mul_nonneg (mul_nonneg hK hX) hdd,
    mul_nonneg (mul_nonneg hK hYs) hdd]

theorem prodBound_all (hd : 1 ≤ d) : ∀ k : ℕ, ∀ σ : ℝ, 0 ≤ σ → σ ≤ k + 1 → ProdBound d σ := by
  intro k
  induction k with
  | zero => intro σ h0 h1; exact prodBound_base hd σ h0 (by simpa using h1)
  | succ k ih =>
    intro σ h0 h1
    by_cases hσ : σ ≤ 1
    · exact prodBound_base hd σ h0 hσ
    · push Not at hσ
      have := prodBound_step hd (σ - 1) (by linarith) (ih (σ - 1) (by linarith) (by push_cast at h1 ⊢; linarith))
      simpa using this


theorem real_product_bound_high (hd : 1 ≤ d) (σ : ℝ) (h0 : 0 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Torus d → ℝ), Torus.IsCk (⌈σ⌉₊ : ℕ) a → ∀ u : Torus d → ℝ, MemSobolev σ u →
      MemSobolev σ (fun x => a x * u x) ∧
      sobolevNorm σ (fun x => a x * u x) ≤ C * Torus.cbNorm ⌈σ⌉₊ a * sobolevNorm σ u := by
  obtain ⟨C₀, hC₀, hC⟩ := prodBound_all hd ⌈σ⌉₊ σ h0 (by
    have := Nat.le_ceil σ; linarith)
  refine ⟨Real.sqrt C₀, Real.sqrt_nonneg _, fun a ha u hu => ?_⟩
  have hcont : Continuous a := continuous_of_lift' ha.continuous
  obtain ⟨hmem, hnorm⟩ := memHs_of_memSobolev σ hu
  obtain ⟨hm, hm'⟩ := hC a ha _ hmem
  have hL := memLp_real_mul hcont hu.1
  have hco := coeffOf_mul' hcont hu.1
  rw [← hco] at hm hm'
  obtain ⟨hM, hMn⟩ := memSobolev_of_memHs' σ hL hm
  refine ⟨hM, ?_⟩
  rw [← hMn, hnorm] at hm'
  have hAΛ : 0 ≤ Torus.cbNorm ⌈σ⌉₊ a := cbNorm_nonneg _ a
  have hs0 : 0 ≤ sobolevNorm σ u := Real.sqrt_nonneg _
  have hs1 : 0 ≤ sobolevNorm σ (fun x => a x * u x) := Real.sqrt_nonneg _
  have : sobolevNorm σ (fun x => a x * u x) ^ 2 ≤
      (Real.sqrt C₀ * Torus.cbNorm ⌈σ⌉₊ a * sobolevNorm σ u) ^ 2 := by
    refine hm'.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hC₀]
  exact (pow_le_pow_iff_left₀ hs1 (by positivity) two_ne_zero).1 this


end HRS.PDE.ProdAux
