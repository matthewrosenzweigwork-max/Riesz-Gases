import HRS.MS.SA16TCo3
import HRS.MS.SA16PForce6
import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16T) Mo1: weighted regularity of mollified densities

`sa16t_regular_of_decay`: decay bounds `‖D^j ρ‖ ≤ A (1+|y|)^{-(d+3)}` give `IsRegularDensityW r ((r+2) A) ρ`.
`sa16t_conv_decay_unif`: `‖D^j (ρ_n ⋆ μ)‖ ≤ ((d+1)^k 2^{d+3} A) w` uniformly in `n` (`j ≤ k`, derivative on `μ`);
`sa16t_conv_decay_n`: the same with an `n`-dependent constant, for every order (derivative on the kernel).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P

section Mo1
variable {d : ℕ}

lemma sa16t_jbracket_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x]

lemma sa16t_w_nonneg_aux {F : Type*} [NormedAddCommGroup F] {A : ℝ} {ρ : Euc d → F}
    (h : ‖ρ 0‖ ≤ A * sa16p_w d 0) : 0 ≤ A := by
  have h1 := (norm_nonneg _).trans h
  have hw := sa16p_w_pos (d := d) 0
  by_contra hneg
  push Not at hneg
  nlinarith

lemma sa16t_regular_of_decay {r : ℕ} {A : ℝ} {ρ : Euc d → ℝ} (hρ : ContDiff ℝ r ρ)
    (hb : ∀ j ≤ r, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ A * sa16p_w d y) :
    IsRegularDensityW r ((r + 2) * A) ρ := by
  have hA : 0 ≤ A := sa16t_w_nonneg_aux (ρ := iteratedFDeriv ℝ 0 ρ) (hb 0 (Nat.zero_le _) 0)
  have hbdd : ∀ j ≤ r, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ A := fun j hj y =>
    (hb j hj y).trans (mul_le_of_le_one_right hA (sa16p_w_le_one y))
  have hmem : MemCb r ρ := ⟨hρ, fun j hj => ⟨A, by rintro _ ⟨y, rfl⟩; exact hbdd j hj y⟩⟩
  have hcb : cbNorm r ρ ≤ (r + 1) * A := by
    unfold cbNorm
    calc ∑ j ∈ Finset.range (r + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j ρ z‖ ≤ ∑ j ∈ Finset.range (r + 1), A :=
          Finset.sum_le_sum fun j hj => ciSup_le fun z => hbdd j (by have := Finset.mem_range.1 hj; omega) z
      _ = (r + 1) * A := by simp
  have hw : weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal A := by
    unfold weightedSupE derivSupE
    refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    have h1 : |partialDeriv i ρ x| ≤ A * sa16p_w d x :=
      (sa16y_pd_le_iter ρ x i).trans (hb j (by have := j.2; omega) x)
    have hjb : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)
    have h2 : jbracket x ^ ((d : ℝ) + 3) * sa16p_w d x ≤ 1 := by
      unfold sa16p_w
      have hp : 0 < (1 + ‖x‖) ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (by positivity) _
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, div_le_one hp]
      exact Real.rpow_le_rpow hjb.le (sa16t_jbracket_le x) (by positivity)
    calc jbracket x ^ ((d : ℝ) + 3) * |partialDeriv i ρ x| ≤ jbracket x ^ ((d : ℝ) + 3) * (A * sa16p_w d x) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = A * (jbracket x ^ ((d : ℝ) + 3) * sa16p_w d x) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left h2 hA
      _ = A := mul_one A
  refine ⟨hρ, hmem, ?_⟩
  calc ENNReal.ofReal (cbNorm r ρ) + weightedSupE r ((d : ℝ) + 3) ρ
      ≤ ENNReal.ofReal ((r + 1) * A) + ENNReal.ofReal A :=
        add_le_add (ENNReal.ofReal_le_ofReal hcb) hw
    _ = ENNReal.ofReal ((r + 1) * A + A) := (ENNReal.ofReal_add (by positivity) hA).symm
    _ = ENNReal.ofReal ((r + 2) * A) := by congr 1; ring

lemma sa16t_w_shift1 (x z : Euc d) (hz : ‖z‖ ≤ 1) : sa16p_w d (x - z) ≤ 2 ^ ((d : ℝ) + 3) * sa16p_w d x := by
  have := sa16p_w_shift x (x - z) 0 (by simpa using hz)
  simpa using this

/-- uniform decay of a mollification (derivative on `μ`) -/
lemma sa16t_conv_decay_unif {μ : Euc d → ℝ} {k : ℕ} {A : ℝ} (hμ : ContDiff ℝ k μ)
    (hb : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j μ y‖ ≤ A * sa16p_w d y) (n : ℕ) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (sa16j_conv (sa16y_rho d n) μ) x‖ ≤
      (((d : ℝ) + 1) ^ k * (2 ^ ((d : ℝ) + 3) * A)) * sa16p_w d x := by
  have hA : 0 ≤ A := sa16t_w_nonneg_aux (ρ := iteratedFDeriv ℝ 0 μ) (hb 0 (Nat.zero_le _) 0)
  have hsupp : ∀ z, 1 / ((n : ℝ) + 1) < ‖z‖ → sa16y_rho d n z = 0 := fun z hz => sa16y_rho_supp n z hz
  have hjr : j + (k - j) = k := by omega
  have hμ' : ContDiff ℝ ((j + (k - j) : ℕ) : WithTop ℕ∞) μ := by rw [hjr]; exact hμ
  have hw0 : 0 ≤ sa16p_w d x := (sa16p_w_pos x).le
  have hterm : ∀ r : Fin j → Fin d, |partialDeriv r (sa16j_conv (sa16y_rho d n) μ) x| ≤
      2 ^ ((d : ℝ) + 3) * A * sa16p_w d x := by
    intro r
    rw [sa16y_conv_pdN hsupp (by positivity) (sa16y_rho_integrable n) j (k - j) r μ hμ']
    have := sa16t_conv_le (k := sa16y_rho d n) (u := partialDeriv r μ) (R := 1)
      (A := 2 ^ ((d : ℝ) + 3) * A * sa16p_w d x) (sa16y_rho_integrable n)
      (fun z hz => sa16t_rho_supp n z hz) x (fun z hz => by
        refine (sa16y_pd_le_iter μ (x - z) r).trans ((hb j hj (x - z)).trans ?_)
        calc A * sa16p_w d (x - z) ≤ A * (2 ^ ((d : ℝ) + 3) * sa16p_w d x) :=
              mul_le_mul_of_nonneg_left (sa16t_w_shift1 x z hz) hA
          _ = _ := by ring)
    rw [sa16t_rho_abs_int, one_mul, Real.norm_eq_abs] at this
    exact this
  refine (sa16j_norm_iter_le _ x j).trans ?_
  calc ∑ r : Fin j → Fin d, |partialDeriv r (sa16j_conv (sa16y_rho d n) μ) x|
      ≤ ∑ r : Fin j → Fin d, 2 ^ ((d : ℝ) + 3) * A * sa16p_w d x := Finset.sum_le_sum fun r _ => hterm r
    _ = (d : ℝ) ^ j * (2 ^ ((d : ℝ) + 3) * A * sa16p_w d x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ (((d : ℝ) + 1) ^ k * (2 ^ ((d : ℝ) + 3) * A)) * sa16p_w d x := by
        have h1 : (d : ℝ) ^ j ≤ ((d : ℝ) + 1) ^ k :=
          (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) _).trans
            (pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hj)
        have h2 : 0 ≤ 2 ^ ((d : ℝ) + 3) * A * sa16p_w d x := by positivity
        calc (d : ℝ) ^ j * (2 ^ ((d : ℝ) + 3) * A * sa16p_w d x) ≤ ((d : ℝ) + 1) ^ k * (2 ^ ((d : ℝ) + 3) * A * sa16p_w d x) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = _ := by ring

/-- decay of a mollification with an `n`-dependent constant (derivative on the kernel), every order -/
lemma sa16t_conv_decay_n {μ : Euc d → ℝ} (hμ : Continuous μ) {A : ℝ} (hb : ∀ y, |μ y| ≤ A * sa16p_w d y)
    (n k : ℕ) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (sa16j_conv (sa16y_rho d n) μ) x‖ ≤
      sa16t_Crho d n k * (2 ^ ((d : ℝ) + 3) * A * sa16p_w d x) := by
  have hA : 0 ≤ A := sa16t_w_nonneg_aux (ρ := μ) (by simpa [Real.norm_eq_abs] using hb 0)
  refine sa16t_mollify_small hμ n k x (fun z hz => ?_) hj
  refine (hb (x - z)).trans ?_
  calc A * sa16p_w d (x - z) ≤ A * (2 ^ ((d : ℝ) + 3) * sa16p_w d x) :=
        mul_le_mul_of_nonneg_left (sa16t_w_shift1 x z hz) hA
    _ = _ := by ring

end Mo1

end HRS.Whole.AppendixA.Phase2SA16R
