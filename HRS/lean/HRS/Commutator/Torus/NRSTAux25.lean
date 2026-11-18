import HRS.Commutator.Torus.NRSTAux24

/-!
# NRS-T, part 25: dyadic shells for the upper bound of cut-off lifts
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_phi_decay (K : ℕ) : ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ y : 𝔼, (1 + ‖y‖) ^ K * ‖nrstr_phi (d := d) y‖ ≤ Cφ := by
  obtain ⟨s, C, hC0, hC⟩ := leibt_invF_decay (d := d) K
  refine ⟨C * (s.sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) (nrstr_theta0 (d := d)), by positivity, fun y => ?_⟩
  exact hC (nrstr_theta0 (d := d)) y

/-- Dyadic shell decomposition: every `y` lies in a box `B_j` and `φ(y/N)` is small. -/
lemma nrstr_shell (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {K : ℕ} {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ y : 𝔼, (1 + ‖y‖) ^ K * ‖nrstr_phi (d := d) y‖ ≤ Cφ) (M : ℕ) (y : 𝔼) :
    ∃ j : ℕ, y ∈ leibt_boxN d (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2) ∧
      ‖nrstr_phi (d := d) ((((d : ℝ) * ((M : ℝ) + 1) / r)⁻¹) • y)‖ ≤
        Cφ / (r / (2 * d)) ^ K * ((1 / 2 : ℝ) ^ j) ^ K := by
  classical
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set N : ℝ := (d : ℝ) * ((M : ℝ) + 1) / r with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hex : ∃ j : ℕ, y ∈ leibt_boxN d (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ‖y‖ (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, fun i => ?_⟩
    have h1 : |y i| ≤ ‖y‖ := by
      have := PiLp.norm_apply_le y i
      simpa [Real.norm_eq_abs] using this
    have h2 : (2 : ℝ) ^ j ≤ ((2 ^ j * (M + 1) : ℕ) : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    rw [mem_Ioc]
    constructor <;> [skip; skip]
    · have := (abs_le.1 (h1.trans (hj.le.trans h2) |> fun h => h.trans (le_refl _))).1
      linarith
    · have := (abs_le.1 (h1.trans (hj.le.trans h2))).2
      linarith
  set j := Nat.find hex with hj
  have hjmem : y ∈ leibt_boxN d (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2) := Nat.find_spec hex
  refine ⟨j, hjmem, ?_⟩
  set κ : ℝ := r / (2 * d) with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one (by positivity)]
    linarith
  have hκK : κ ^ K ≤ 1 := pow_le_one₀ hκpos.le hκ1
  have hφle : ∀ z : 𝔼, ‖nrstr_phi (d := d) z‖ ≤ Cφ / (1 + ‖z‖) ^ K := by
    intro z
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hφ z
  rcases Nat.eq_zero_or_pos j with h0 | hjpos
  · rw [h0]
    have h1 : ‖nrstr_phi (d := d) (N⁻¹ • y)‖ ≤ Cφ := by
      refine (hφle _).trans ?_
      refine div_le_self hCφ ?_
      exact one_le_pow₀ (by linarith [norm_nonneg (N⁻¹ • y)])
    refine h1.trans ?_
    simp only [pow_zero, one_pow, mul_one]
    calc Cφ = Cφ / 1 := (div_one _).symm
      _ ≤ Cφ / κ ^ K := div_le_div_of_nonneg_left hCφ (by positivity) hκK
  · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hnot : y ∉ leibt_boxN d (((2 ^ j' * (M + 1) : ℕ) : ℝ) + 1 / 2) :=
      Nat.find_min hex (by omega : j' < j)
    simp only [leibt_boxN, mem_setOf_eq, not_forall] at hnot
    obtain ⟨i, hi⟩ := hnot
    have hyi : ((2 ^ j' * (M + 1) : ℕ) : ℝ) + 1 / 2 ≤ |y i| := by
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hi
      rcases hi with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hyn : ((2 ^ j' * (M + 1) : ℕ) : ℝ) ≤ ‖y‖ := by
      have h1 : |y i| ≤ ‖y‖ := by
        have := PiLp.norm_apply_le y i
        simpa [Real.norm_eq_abs] using this
      linarith
    set A : ℝ := ((2 ^ j' * (M + 1) : ℕ) : ℝ) with hA
    have hApos : 0 < A := by
      rw [hA]; positivity
    have hz : A / N ≤ ‖N⁻¹ • y‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hNpos.le, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hyn hNpos.le
    have hAN : A / N = (2 : ℝ) ^ j' * (r / d) := by
      rw [hA, hN]
      push_cast
      field_simp
    have hzpos : 0 < (2 : ℝ) ^ j' * (r / d) := by positivity
    have hzK : ((2 : ℝ) ^ j' * (r / d)) ^ K ≤ (1 + ‖N⁻¹ • y‖) ^ K := by
      apply pow_le_pow_left₀ hzpos.le
      linarith [hAN ▸ hz]
    refine (hφle _).trans ?_
    calc Cφ / (1 + ‖N⁻¹ • y‖) ^ K ≤ Cφ / ((2 : ℝ) ^ j' * (r / d)) ^ K :=
          div_le_div_of_nonneg_left hCφ (by positivity) hzK
      _ = Cφ / κ ^ K * ((1 / 2 : ℝ) ^ j) ^ K := by
          have e : (2 : ℝ) ^ j' * (r / d) = κ / (1 / 2 : ℝ) ^ (j' + 1) := by
            have hd0 : (d : ℝ) ≠ 0 := (by positivity : (0 : ℝ) < d).ne'
            rw [hκ, one_div, inv_pow, div_inv_eq_mul, pow_succ]
            field_simp
          rw [hj', e, div_pow, div_div_eq_mul_div, div_mul_eq_mul_div]

end HRS.Commutator.TorusNote
