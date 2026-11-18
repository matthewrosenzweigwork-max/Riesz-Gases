import HRS.MS.SA12X5L1

/-!
# S.A.12 X5 LOC2: `jetSq m w ⟨db, ∇F⟩ ≤ C₀ A_b² jetSq (m+1) w F`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3

variable {d : ℕ}

/-- The constant of the drift term, depending only on `d` and `m`. -/
def sa12x5_C0 (d m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) *
    ((d : ℝ) ^ 2 * 4 ^ m * sa12z3_cT d (m + 1))

theorem sa12x5_C0_nonneg (d m : ℕ) : 0 ≤ sa12x5_C0 d m := by
  unfold sa12x5_C0
  have := sa12z3_cT_nonneg d (m + 1)
  have h : 0 ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j :=
    Finset.sum_nonneg fun j _ => by positivity
  positivity

theorem sa12x5_loc_inner_expand {F : Euc d → ℝ} (db : Euc d → Euc d) (x : Euc d) :
    inner ℝ (db x) (gradient F x) = ∑ i : Fin d, db x i * D1 i F x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [q09_gradient_apply]
  simp only [D1, RCLike.inner_apply, conj_trivial]
  ring

theorem sa12x5_loc_coord_smooth (i : Fin d) {db : Euc d → Euc d} (hdb : ContDiff ℝ ∞ db) :
    ContDiff ℝ ∞ (fun y => db y i) :=
  ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff).comp hdb

/-- Pointwise bound of the jets of the drift term. -/
theorem sa12x5_loc_drift_pt (m : ℕ) {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {db : Euc d → Euc d}
    (hdb : ContDiff ℝ ∞ db) {Ab : ℝ} (hAb0 : 0 ≤ Ab)
    (hAb : ∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j db y‖ ≤ Ab) {n : ℕ} (hn : n ≤ m) (idx : Fin n → Fin d)
    (x : Euc d) :
    |partialDeriv idx (fun y => inner ℝ (db y) (gradient F y)) x| ≤
      (d : ℝ) * (2 ^ m * Ab * sa12z3_T (m + 1) F x) := by
  have hfun : (fun y => inner ℝ (db y) (gradient F y)) =
      fun y => ∑ i ∈ Finset.univ, (1 : ℝ) * (db y i * D1 i F y) := by
    funext y; rw [sa12x5_loc_inner_expand db y]; simp
  have hPs : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => db y i * D1 i F y) := fun i =>
    (sa12x5_loc_coord_smooth i hdb).mul (sa12x5_loc_D1_smooth i hF)
  rw [hfun, sa12z3_pd_sum Finset.univ (fun i y => db y i * D1 i F y) (fun _ => 1)
    (fun i _ => sa12z3_cd_of_inf (hPs i) n) idx x]
  have hT0 := sa12z3_T_nonneg (m + 1) F x
  have hP : ∀ i : Fin d, |partialDeriv idx (fun y => db y i * D1 i F y) x| ≤
      2 ^ m * Ab * sa12z3_T (m + 1) F x := by
    intro i
    refine (sa12z3_pd_le_norm _ x idx).trans ?_
    refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (n : WithTop ℕ∞)) (n := n)
      (f := fun y => db y i) (g := D1 i F) (sa12z3_cd_of_inf (sa12x5_loc_coord_smooth i hdb) n)
      (sa12z3_cd_of_inf (sa12x5_loc_D1_smooth i hF) n) x le_rfl).trans ?_
    have hterm : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun y => db y i) x‖ *
        ‖iteratedFDeriv ℝ (n - k) (D1 i F) x‖ ≤ (n.choose k : ℝ) * (Ab * sa12z3_T (m + 1) F x) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have h1 : ‖iteratedFDeriv ℝ k (fun y => db y i) x‖ ≤ Ab := by
        have hc : ContDiffAt ℝ (k : WithTop ℕ∞) db x := (hdb.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
        have h2 := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (f := db) hc
          (n := k) (le_refl _)
        have h3 : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
            simpa using PiLp.norm_apply_le v i
        refine (h2.trans ?_)
        calc ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ k db x‖
            ≤ 1 * Ab := mul_le_mul h3 (hAb k (by omega) x) (norm_nonneg _) zero_le_one
          _ = Ab := one_mul _
      have h4 : ‖iteratedFDeriv ℝ (n - k) (D1 i F) x‖ ≤ sa12z3_T (m + 1) F x :=
        (sa12z3_norm_iter_le (D1 i F) x (n - k)).trans
          (sa12z3_sum_pd_D1_le_T (m := m + 1) (l := n - k) (by omega) hF i x)
      have hc0 : (0 : ℝ) ≤ n.choose k := Nat.cast_nonneg _
      calc (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun y => db y i) x‖ *
            ‖iteratedFDeriv ℝ (n - k) (D1 i F) x‖
          = (n.choose k : ℝ) * (‖iteratedFDeriv ℝ k (fun y => db y i) x‖ *
            ‖iteratedFDeriv ℝ (n - k) (D1 i F) x‖) := by ring
        _ ≤ (n.choose k : ℝ) * (Ab * sa12z3_T (m + 1) F x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h4 (norm_nonneg _) hAb0) hc0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum]
    have h2n : (2 : ℝ) ^ n ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hn
    have : 0 ≤ Ab * sa12z3_T (m + 1) F x := mul_nonneg hAb0 hT0
    nlinarith
  calc |∑ i : Fin d, (1 : ℝ) * partialDeriv idx (fun y => db y i * D1 i F y) x|
      ≤ ∑ i : Fin d, |(1 : ℝ) * partialDeriv idx (fun y => db y i * D1 i F y) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 2 ^ m * Ab * sa12z3_T (m + 1) F x :=
        Finset.sum_le_sum fun i _ => by rw [one_mul]; exact hP i
    _ = _ := by simp

theorem sa12x5_jetSq_drift_le (m : ℕ) {w : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {db : Euc d → Euc d} (hdb : ContDiff ℝ ∞ db) {Ab : ℝ}
    (hAb0 : 0 ≤ Ab) (hAb : ∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j db y‖ ≤ Ab) :
    jetSq m w (fun x => inner ℝ (db x) (gradient F x)) ≤ sa12x5_C0 d m * Ab ^ 2 * jetSq (m + 1) w F := by
  set K : ℝ := (d : ℝ) ^ 2 * 4 ^ m * Ab ^ 2 * sa12z3_cT d (m + 1) with hK
  have hK0 : 0 ≤ K := by
    have := sa12z3_cT_nonneg d (m + 1)
    positivity
  set Sg : ℝ := ∑ r ∈ Finset.range (m + 1 + 1), ∑ γ : Fin r → Fin d,
    ∫ x, (w x * partialDeriv γ F x) ^ 2 with hSg
  have hSgle : Sg ≤ jetSq (m + 1) w F := sa12x5_loc_sum_le_jetSq (m + 1) w F
  have hint : ∀ r (γ : Fin r → Fin d), Integrable (fun x => (w x * partialDeriv γ F x) ^ 2) := fun r γ =>
    sa12x5_loc_integrable hw hwc (sa12z3_pd_contDiff_inf hF γ).continuous
  have pt : ∀ {n : ℕ}, n ≤ m → ∀ idx : Fin n → Fin d,
      ∫ x, (w x * partialDeriv idx (fun y => inner ℝ (db y) (gradient F y)) x) ^ 2 ≤ K * Sg := by
    intro n hn idx
    have hI : Integrable (fun x => ∑ r ∈ Finset.range (m + 1 + 1), ∑ γ : Fin r → Fin d,
        (w x * partialDeriv γ F x) ^ 2) :=
      integrable_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hint r γ
    have e : ∫ x, K * ∑ r ∈ Finset.range (m + 1 + 1), ∑ γ : Fin r → Fin d,
        (w x * partialDeriv γ F x) ^ 2 = K * Sg := by
      rw [integral_const_mul, hSg, integral_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hint r γ]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_finset_sum _ fun γ _ => hint r γ]
    rw [← e]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (hI.const_mul K)
      (Eventually.of_forall fun x => ?_)
    beta_reduce
    have h1 := sa12x5_loc_drift_pt m hF hdb hAb0 hAb hn idx x
    have hT0 := sa12z3_T_nonneg (m + 1) F x
    have hsq : (partialDeriv idx (fun y => inner ℝ (db y) (gradient F y)) x) ^ 2 ≤
        ((d : ℝ) * (2 ^ m * Ab * sa12z3_T (m + 1) F x)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hTY := sa12z3_T_sq (m + 1) F x
    have hY : ∑ r ∈ Finset.range (m + 1 + 1), ∑ γ : Fin r → Fin d, (w x * partialDeriv γ F x) ^ 2 =
        w x ^ 2 * sa12z3_Y (m + 1) F x := by
      unfold sa12z3_Y
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      ring
    rw [hY]
    have hw2 : 0 ≤ w x ^ 2 := sq_nonneg _
    calc (w x * partialDeriv idx (fun y => inner ℝ (db y) (gradient F y)) x) ^ 2
        = w x ^ 2 * (partialDeriv idx (fun y => inner ℝ (db y) (gradient F y)) x) ^ 2 := by ring
      _ ≤ w x ^ 2 * ((d : ℝ) * (2 ^ m * Ab * sa12z3_T (m + 1) F x)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hw2
      _ = w x ^ 2 * ((d : ℝ) ^ 2 * 4 ^ m * Ab ^ 2 * sa12z3_T (m + 1) F x ^ 2) := by
          have : ((4 : ℝ) ^ m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [this]; ring
      _ ≤ w x ^ 2 * ((d : ℝ) ^ 2 * 4 ^ m * Ab ^ 2 * (sa12z3_cT d (m + 1) * sa12z3_Y (m + 1) F x)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTY (by positivity)) hw2
      _ = K * (w x ^ 2 * sa12z3_Y (m + 1) F x) := by rw [hK]; ring
  unfold jetSq
  calc ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        ∫ x, (w x * partialDeriv idx (fun y => inner ℝ (db y) (gradient F y)) x) ^ 2
      ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * (K * Sg)) := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        calc _ ≤ ∑ _idx : Fin j → Fin d, K * Sg := Finset.sum_le_sum fun idx _ => pt hjm idx
          _ = _ := by simp
    _ = (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) * (K * Sg) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) * (K * jetSq (m + 1) w F) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSgle hK0)
          (Finset.sum_nonneg fun j _ => by positivity)
    _ = sa12x5_C0 d m * Ab ^ 2 * jetSq (m + 1) w F := by
        unfold sa12x5_C0; rw [hK]; ring

end HRS.MH.AdjointRd.Phase2SA12X5
