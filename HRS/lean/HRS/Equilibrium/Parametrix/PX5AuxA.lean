import HRS.Equilibrium.Parametrix.PX1AuxExtApply

/-!
# Prop 4.13 parametrix, packet PX5: size bounds from conormal classes

Full derivative bounds (orders `0, 1, 2`) of a conormal kernel in the envelopes of `PsiSize`
(`px5_deriv_bound`), the numerical weight inequalities for the sharp class of `𝒩R_0` and the
coarse classes of `𝒩R_j`, `j ≥ 1`, and the additive structure `Px5Bnds`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-- The envelope of order `k` (`k = 0, 1, 2`) of `Q:eq:psi-size`. -/
def px5T (s : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun r => 1 + r ^ (2 - s) + (if s = 2 then |Real.log r| else 0)
  | 1 => fun r => 1 + r ^ (1 - s)
  | _ => fun r => 1 + r ^ (-s)

theorem px5T_ge_one (s : ℝ) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ px5T s k r := by
  rcases k with _ | _ | k
  · simp only [px5T]
    have h3 : 0 ≤ r ^ (2 - s) := Real.rpow_nonneg hr _
    have h4 : 0 ≤ (if s = 2 then |Real.log r| else (0 : ℝ)) := by split_ifs <;> positivity
    linarith
  · simp only [px5T]
    have h3 : 0 ≤ r ^ (1 - s) := Real.rpow_nonneg hr _
    linarith
  · simp only [px5T]
    have h3 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr _
    linarith

/-- weight condition: the conormal weights up to order `k` are bounded by `Cw * px5T s k`. -/
def Px5W (s τ : ℝ) (b : ℕ → ℕ) (Cw : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ 2 → ∀ c : ℕ, c ≤ k → ∀ r : ℝ, 0 < r → r < r0 →
    r ^ (-(τ + (c : ℝ))) * (1 + |Real.log r|) ^ b c ≤ Cw * px5T s k r

theorem px5T_ge_rpow (s : ℝ) (k : ℕ) (hk : k ≤ 2) {r : ℝ} (hr : 0 < r) :
    r ^ (-(s - 2 + (k : ℝ))) ≤ px5T s k r := by
  interval_cases k
  · simp only [px5T]
    have e : -(s - 2 + ((0 : ℕ) : ℝ)) = 2 - s := by push_cast; ring
    rw [e]
    have h4 : 0 ≤ (if s = 2 then |Real.log r| else (0 : ℝ)) := by split_ifs <;> positivity
    linarith
  · simp only [px5T]
    have e : -(s - 2 + ((1 : ℕ) : ℝ)) = 1 - s := by push_cast; ring
    rw [e]; linarith
  · simp only [px5T]
    have e : -(s - 2 + ((2 : ℕ) : ℝ)) = -s := by push_cast; ring
    rw [e]; linarith

theorem one_add_abs_log_le_inv {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 1 + |Real.log r| ≤ r⁻¹ := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at h
  rw [abs_of_nonpos (Real.log_nonpos hr.le hr1)]
  linarith

/-- the sharp class of `𝒩R_0`: order `s - 2`, log index `1` only at `c = 0`, `s = 2`. -/
theorem px5W_sharp {s : ℝ} (hs : 0 < s) :
    Px5W s (s - ((0 : ℕ) : ℝ) / 2 - 2)
      (fun c => 0 + if s - ((0 : ℕ) : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) 1 := by
  intro k hk c hc r hr0 hrr
  have hr1 : r ≤ 1 := by unfold r0 at hrr; linarith
  have hτ : s - ((0 : ℕ) : ℝ) / 2 - 2 = s - 2 := by push_cast; ring
  rw [hτ]
  have hmono : r ^ (-(s - 2 + (c : ℝ))) ≤ r ^ (-(s - 2 + (k : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by
      have : (c : ℝ) ≤ k := by exact_mod_cast hc
      linarith)
  have hT := px5T_ge_rpow s k hk hr0
  by_cases hcond : s - 2 + (c : ℝ) = 0 ∧ c ≠ 1
  · have hb : (0 + if (s - 2 + (c : ℝ) = 0 ∧ c ≠ 1) then 1 else 0 : ℕ) = 1 := by
      rw [if_pos hcond]
    beta_reduce
    rw [hb]
    obtain ⟨h1, h2⟩ := hcond
    have hc0 : c = 0 := by
      rcases Nat.lt_or_ge c 1 with h | h
      · omega
      · exfalso
        have : c = 2 := by omega
        subst this
        norm_num at h1
        linarith
    have hs2 : s = 2 := by subst hc0; norm_num at h1; linarith
    have he : -(s - 2 + (c : ℝ)) = 0 := by linarith
    rw [he, Real.rpow_zero, one_mul, pow_one]
    interval_cases k
    · simp only [px5T, hs2, if_true]
      norm_num
    · simp only [px5T, hs2]
      have := one_add_abs_log_le_inv hr0 hr1
      have e : (1 : ℝ) - 2 = -1 := by norm_num
      rw [e, Real.rpow_neg_one]
      linarith
    · simp only [px5T, hs2]
      have h := one_add_abs_log_le_inv hr0 hr1
      have h2 : r⁻¹ ≤ r ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by norm_num)
      linarith
  · simp only [hcond, ite_false, zero_add, pow_zero, mul_one, one_mul]
    linarith

/-- the coarse classes (`σ ≤ s - 5/2`, log index `≤ 1`). -/
theorem px5W_coarse {s τ : ℝ} (hτ : τ ≤ s - 5 / 2) (b : ℕ → ℕ) (hb : ∀ c, b c ≤ 1) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ Px5W s τ b Cw := by
  obtain ⟨C0, hC0, hC⟩ := rpow_log_pow_le (1 / 2) (by norm_num) 1
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro k hk c hc r hr0 hrr
  have hr1 : r ≤ 1 := by unfold r0 at hrr; linarith
  have hk' : (c : ℝ) ≤ k := by exact_mod_cast hc
  have h1 : r ^ (-(τ + (c : ℝ))) ≤ r ^ (-(s - 5 / 2 + (k : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  have h2 : (1 + |Real.log r|) ^ b c ≤ (1 + |Real.log r|) ^ 1 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log r)]) (hb c)
  have h3 : r ^ (-(s - 5 / 2 + (k : ℝ))) = r ^ (1 / 2 : ℝ) * r ^ (-(s - 2 + (k : ℝ))) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hT := px5T_ge_rpow s k hk hr0
  have hT1 := px5T_ge_one s k hr0.le
  have h4 := hC r hr0 hr1
  have h5 : 0 ≤ r ^ (-(s - 2 + (k : ℝ))) := Real.rpow_nonneg hr0.le _
  have h6 : 0 ≤ r ^ (-(τ + (c : ℝ))) := Real.rpow_nonneg hr0.le _
  have h7 : 0 ≤ (1 + |Real.log r|) ^ b c := by positivity
  calc r ^ (-(τ + (c : ℝ))) * (1 + |Real.log r|) ^ b c
      ≤ r ^ (-(s - 5 / 2 + (k : ℝ))) * (1 + |Real.log r|) ^ 1 :=
        mul_le_mul h1 h2 h7 (Real.rpow_nonneg hr0.le _)
    _ = (r ^ (1 / 2 : ℝ) * (1 + |Real.log r|) ^ 1) * r ^ (-(s - 2 + (k : ℝ))) := by rw [h3]; ring
    _ ≤ C0 * r ^ (-(s - 2 + (k : ℝ))) := mul_le_mul_of_nonneg_right h4 h5
    _ ≤ C0 * px5T s k r := mul_le_mul_of_nonneg_left hT hC0
    _ ≤ (C0 + 1) * px5T s k r := by nlinarith

/-- Near the diagonal, full derivatives are controlled by the typed (mixed) bounds. -/
theorem px5_near_full {F : Torus d → Torus d → ℝ} {m : ℕ} {σ : ℝ} {b : ℕ → ℕ} {B : ℝ}
    (hF : ConormalL σ b m B F) {X z : Euc d} (hz : z ≠ 0) (hzr : ‖z‖ < r0) {k : ℕ} (hk : k ≤ m)
    {W : ℝ} (hW : 0 ≤ W) (hnear : ∀ a c, a + c = k → ‖mixedDeriv a c (toChart F) X z‖ ≤ W) :
    ‖iteratedFDeriv ℝ k (lift2 F) (chartT d (X, z))‖ ≤ 4 ^ k * W := by
  have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
  have hGd : ∀ n ≤ m, ContDiffOn ℝ (n : WithTop ℕ∞) (toChart F) (Uc d) := fun n hn =>
    (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hn)
  have hTB : ∀ a c, a + c = k → TB (toChart F) (X, z) a c W := fun a c hac =>
    tb_of_norm_le isOpen_Uc (hGd (a + c) (by omega)) hq (hnear a c hac)
  have hfull := full_of_tb k (toChart F) W hW
    ((hGd k hk).contDiffAt (isOpen_Uc.mem_nhds hq)) hTB
  have hnorm : ‖iteratedFDeriv ℝ k (toChart F) (X, z)‖ ≤ 2 ^ k * W := by
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
    have := hfull w
    rw [Real.norm_eq_abs]
    linarith
  have hconv := norm_iteratedFDeriv_chart_le (lift2 F) k (X, z)
  rw [← toChart_eq] at hconv
  have h2k : (2 : ℝ) ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
  calc ‖iteratedFDeriv ℝ k (lift2 F) (chartT d (X, z))‖
      ≤ 2 ^ k * ‖iteratedFDeriv ℝ k (toChart F) (X, z)‖ := hconv
    _ ≤ 2 ^ k * (2 ^ k * W) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 4 ^ k * W := by rw [← mul_assoc, h2k]

theorem px5_near_rep {p : Euc d × Euc d} (hp : p ∈ offDiag d)
    (hdist : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) < r0) :
    ∃ (X z : Euc d) (n : Lattice d), z ≠ 0 ∧ ‖z‖ = Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) ∧
      p = chartT d (X, z) + (Lattice.toEuc n, (0 : Euc d)) := by
  set nv : Lattice d := fun i => round (p.1 i - p.2 i) with hnv
  set z0 : Euc d := WithLp.toLp 2 fun i => (p.1 i - p.2 i) - (round (p.1 i - p.2 i) : ℝ) with hz0
  have hsplit : p.1 - p.2 = Lattice.toEuc nv + z0 := by
    ext i; simp [Lattice.toEuc, hz0, hnv]
  have hnorm : ‖z0‖ = Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) := by
    rw [EuclideanSpace.norm_eq, Torus.eucDist]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Torus.mk p.1) i - (Torus.mk p.2) i = (((p.1 i - p.2 i : ℝ)) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this, UnitAddCircle.norm_eq]
    simp [hz0, sq_abs]
  have hz0ne : z0 ≠ 0 := by
    intro h
    apply (mem_offDiag_iff p).1 hp
    show Torus.mk (p.1 - p.2) = 0
    rw [hsplit, h, add_zero, mk_toEuc']
  refine ⟨p.2 + (1 / 2 : ℝ) • z0, z0, nv, hz0ne, hnorm, ?_⟩
  rw [chartT_apply]
  ext1
  · show p.1 = p.2 + (1 / 2 : ℝ) • z0 + (1 / 2 : ℝ) • z0 + Lattice.toEuc nv
    have : p.1 = p.2 + (Lattice.toEuc nv + z0) := by rw [← hsplit]; abel
    rw [this]; module
  · show p.2 = p.2 + (1 / 2 : ℝ) • z0 - (1 / 2 : ℝ) • z0 + 0
    module

theorem rTrunc_eq_of_lt {x y : Torus d} (h : Torus.eucDist x y < r0) : rTrunc x y = Torus.eucDist x y := by
  unfold rTrunc
  rw [min_eq_right]
  unfold r0 at h; linarith

theorem px5_deriv_bound {s τ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B Cw : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL τ b m B F) (hB : 0 ≤ B) (hCw0 : 0 ≤ Cw) (hCw : Px5W s τ b Cw)
    {k : ℕ} (hk : k ≤ 2) (hkm : k ≤ m) (p : Euc d × Euc d) (hp : p ∈ offDiag d) :
    ‖iteratedFDeriv ℝ k (lift2 F) p‖ ≤
      4 ^ k * (B * (1 + Cw)) * px5T s k (rTrunc (Torus.mk p.1) (Torus.mk p.2)) := by
  have hr0 : 0 ≤ rTrunc (Torus.mk p.1) (Torus.mk p.2) := le_min zero_le_one (Real.sqrt_nonneg _)
  have hT1 := px5T_ge_one s k hr0
  have hBC : 0 ≤ B * (1 + Cw) := by positivity
  by_cases hdist : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) < r0
  · obtain ⟨X, z, n, hz, hzn, hpe⟩ := px5_near_rep hp hdist
    have hzr : ‖z‖ < r0 := by rw [hzn]; exact hdist
    have hrT : rTrunc (Torus.mk p.1) (Torus.mk p.2) = ‖z‖ := by
      rw [rTrunc_eq_of_lt hdist, hzn]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hTz : 1 ≤ px5T s k ‖z‖ := px5T_ge_one s k hzpos.le
    have hnear : ∀ a c, a + c = k →
        ‖mixedDeriv a c (toChart F) X z‖ ≤ B * (1 + Cw) * px5T s k ‖z‖ := by
      intro a c hac
      refine (hF.near a c (by omega) X z hz hzr).trans ?_
      have h1 := hCw k hk c (by omega) ‖z‖ hzpos hzr
      calc B * (1 + ‖z‖ ^ (-(τ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c)
          ≤ B * (1 + Cw * px5T s k ‖z‖) := mul_le_mul_of_nonneg_left (by linarith) hB
        _ ≤ B * ((1 + Cw) * px5T s k ‖z‖) := by
            refine mul_le_mul_of_nonneg_left ?_ hB
            nlinarith
        _ = _ := by ring
    have := px5_near_full hF hz hzr hkm (by positivity) hnear
    rw [hrT, hpe, iteratedFDeriv_lift2_periodic]
    calc _ ≤ 4 ^ k * (B * (1 + Cw) * px5T s k ‖z‖) := this
      _ = _ := by ring
  · push Not at hdist
    have := hF.far k hkm p hp hdist
    have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    calc _ ≤ B := this
      _ ≤ 1 * (B * 1) * 1 := by linarith
      _ ≤ 4 ^ k * (B * (1 + Cw)) * px5T s k (rTrunc (Torus.mk p.1) (Torus.mk p.2)) := by
          refine mul_le_mul (mul_le_mul h4 (by nlinarith) (by positivity) (by positivity)) hT1
            zero_le_one (by positivity)

end HRS.Parx

end
