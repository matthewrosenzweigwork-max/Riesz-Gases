import HRS.MS.SA12X3C7C8

/-!
# S.A.12 C7 (SA12X3), part C9 (7C): comparison of the lattice weights

`cellWeight d z ≤ (1+κ√d)^{d+3} cellWeight d (z/κ)` and `cellWeight d y ≤ (1+√d)^{d+3} cellWeight d (y+ε)`, `ε ∈ {0,1}^d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_jb_ge_one (a : Euc d) : 1 ≤ jbracket a := by
  unfold jbracket
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖a‖])

theorem sa12x3_jb_le {a b : Euc d} {D : ℝ} (hD : 0 ≤ D) (h : ‖b‖ ≤ ‖a‖ + D) : jbracket b ≤ jbracket a + D := by
  unfold jbracket
  have hsa : 0 ≤ Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 + ‖a‖ ^ 2) ^ 2 = 1 + ‖a‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hna : ‖a‖ ≤ Real.sqrt (1 + ‖a‖ ^ 2) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  rw [Real.sqrt_le_left (by positivity)]
  have hb0 := norm_nonneg b
  nlinarith [sq_nonneg (‖b‖ - ‖a‖ - D), mul_nonneg hD hsa, mul_nonneg hD (norm_nonneg a)]

theorem sa12x3_w_le {a b : Euc d} {D : ℝ} (hD : 0 ≤ D) (h : ‖b‖ ≤ ‖a‖ + D) :
    jbracket a ^ (-((d : ℝ) + 3)) ≤ (1 + D) ^ ((d : ℝ) + 3) * jbracket b ^ (-((d : ℝ) + 3)) := by
  have h1 := sa12x3_jb_le hD h
  have ha1 := sa12x3_jb_ge_one a
  have hb1 := sa12x3_jb_ge_one b
  have h2 : jbracket b ≤ (1 + D) * jbracket a := by nlinarith
  have h3 : jbracket b / (1 + D) ≤ jbracket a := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hp : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
  calc jbracket a ^ (-((d : ℝ) + 3)) ≤ (jbracket b / (1 + D)) ^ (-((d : ℝ) + 3)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith)
    _ = (1 + D) ^ ((d : ℝ) + 3) * jbracket b ^ (-((d : ℝ) + 3)) := by
        rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
        field_simp

theorem sa12x3_norm_latticePt_le (z : Fin d → ℤ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i, |(z i : ℝ)| ≤ B) :
    ‖latticePt z‖ ≤ Real.sqrt d * B := by
  unfold latticePt
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 fun i => (z i : ℝ) : Euc d) i‖ ^ 2) ≤ Real.sqrt (d * B ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc ∑ i, ‖(WithLp.toLp 2 fun i => (z i : ℝ) : Euc d) i‖ ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              have := hB i
              rw [Real.norm_eq_abs]
              change |(z i : ℝ)| ^ 2 ≤ B ^ 2
              nlinarith [abs_nonneg ((z i : ℝ))]
          _ = d * B ^ 2 := by simp
    _ = Real.sqrt d * B := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB0]

theorem sa12x3_latticePt_add (u v : Fin d → ℤ) : latticePt (u + v) = latticePt u + latticePt v := by
  ext i; simp [latticePt]

/-- `z = κ q + r` with `0 ≤ r_i < κ`: the weight of `z` is bounded by that of `q`. -/
theorem sa12x3_w_quo {κ : ℤ} (hκ : 1 ≤ κ) (z : Fin d → ℤ) :
    cellWeight d z ≤ (1 + κ * Real.sqrt d) ^ ((d : ℝ) + 3) * cellWeight d (fun i => z i / κ) := by
  set q : Fin d → ℤ := fun i => z i / κ with hq
  set r : Fin d → ℤ := fun i => z i % κ with hr
  have hκ0 : (0 : ℤ) < κ := by omega
  have hκR : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hz : z = κ • q + r := by
    funext i
    simp only [hq, hr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_add_emod (z i) κ).symm
  have hr0 : ∀ i, 0 ≤ r i := fun i => Int.emod_nonneg _ hκ0.ne'
  have hrκ : ∀ i, r i < κ := fun i => Int.emod_lt_of_pos _ hκ0
  have hrn : ‖latticePt r‖ ≤ Real.sqrt d * κ :=
    sa12x3_norm_latticePt_le r (by linarith) fun i => by
      rw [abs_of_nonneg (by exact_mod_cast hr0 i)]
      exact_mod_cast (hrκ i).le
  have hzeq : latticePt z = (κ : ℝ) • latticePt q + latticePt r := by
    ext i; simp [latticePt, hq, hr]
    have := congrArg (fun t : Fin d → ℤ => (t i : ℝ)) hz
    simpa using this
  have hqn : ‖latticePt q‖ ≤ ‖latticePt z‖ + κ * Real.sqrt d := by
    have h1 : (κ : ℝ) • latticePt q = latticePt z - latticePt r := by rw [hzeq]; abel
    have h2 : ‖(κ : ℝ) • latticePt q‖ = κ * ‖latticePt q‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    have h3 : ‖latticePt z - latticePt r‖ ≤ ‖latticePt z‖ + ‖latticePt r‖ := norm_sub_le _ _
    have h4 : ‖latticePt q‖ ≤ κ * ‖latticePt q‖ := by
      nlinarith [norm_nonneg (latticePt q)]
    rw [h1] at h2
    nlinarith
  have := sa12x3_w_le (a := latticePt z) (b := latticePt q) (D := κ * Real.sqrt d)
    (by positivity) hqn
  unfold cellWeight
  exact this

/-- Shifting by `ε ∈ {0,1}^d` changes the weight by a bounded factor. -/
theorem sa12x3_w_shift (y : Fin d → ℤ) (ε : Fin d → Fin 2) :
    cellWeight d y ≤ (1 + Real.sqrt d) ^ ((d : ℝ) + 3) * cellWeight d (y + fun i => ((ε i : ℕ) : ℤ)) := by
  have hε : ‖latticePt (fun i => ((ε i : ℕ) : ℤ))‖ ≤ Real.sqrt d * 1 :=
    sa12x3_norm_latticePt_le _ zero_le_one fun i => by
      have : ((ε i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp (ε i).isLt
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact this
  have hn : ‖latticePt (y + fun i => ((ε i : ℕ) : ℤ))‖ ≤ ‖latticePt y‖ + Real.sqrt d := by
    rw [sa12x3_latticePt_add]
    calc _ ≤ ‖latticePt y‖ + ‖latticePt (fun i => ((ε i : ℕ) : ℤ))‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have := sa12x3_w_le (a := latticePt y) (b := latticePt (y + fun i => ((ε i : ℕ) : ℤ)))
    (D := Real.sqrt d) (Real.sqrt_nonneg _) hn
  unfold cellWeight
  exact this

end HRS.MH.AdjointRd.Phase2SA12Near
