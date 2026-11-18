import HRS.MC.S7PIDDefs
import HRS.MC.S7PIEProp
import HRS.MC.L2C0
import HRS.MC.RegSet
import HRS.Main.A33Aux2

/-!
# Packet PI-D, sub-packet M: mode decay of the propagated test function (`s7_PID_mode_decay`)

Proof of `HRS.MC.Sec7.PIDPlan.s7_PID_mode_decay` (statement copied verbatim).

Route.  `(V^{t,u} e_k)(φ) = ∑_j pieT(k,j) φ̂_j` is the `k`-th coefficient of `U^{u,t}φ` (when `V e_k` lies in `E_m`).
For `t > 0` the finite-section bound `pieFinBd` of `S7PIEInterp` (from `pie_finBd`, `S7PIEProp`) at the INTEGER level
`L = N + m_* + 1` (with `AdjointData` at level `L`, from `l2c0_adjointData_generic` as in `S7PIDP_pie`) bounds the row
`∑_j pieT(k,j) φ̂_j` by `C ‖φ‖_{H^L}` after the weight `⟨k⟩^{-L} ≤ ⟨k⟩^{-N}`.  The case `t = 0` (`u = t = 0`, where
`pie_finBd` is not available) uses only `propagator 0 0 ψ ∈ {ψ, 0}`.  Only Mathlib and the proved PI-E modules are used.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDM

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

/-- The standing PI-E data at an arbitrary integer level `L ≥ m_*` (as `S7PIDP_pie`, with `L` in place of `n₀ + 1`). -/
theorem S7PIDM_pie (R : Regime d) (T : ℝ) (hT : 0 < T) (L : ℕ) (hL : PDE.mStar d ≤ L) :
    HRS.MC.Sec7.PIE.PIEHyp L R.D R.ρ T := by
  have hd2 : 2 ≤ d := R.hd
  have hd1 : 1 ≤ d := by omega
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob
    (fun j => HRS.MC.RegSet.reg_proof R j) hcont
  have hL1 : 1 ≤ L := by
    unfold PDE.mStar at hL
    omega
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA L hL1 T hT
  exact ⟨hd1, hL, Rg, MB, Λ, VB, ν₀, hAD⟩

theorem S7PIDM_sob_nonneg (m : ℝ) (φ : Torus d → ℝ) : 0 ≤ sobolevNorm m φ := by
  unfold sobolevNorm
  exact Real.sqrt_nonneg _

theorem S7PIDM_prop_zero (D : DynData d) (ρ : ℝ → Torus d → ℝ) (ψ : Torus d → ℝ) :
    propagator D ρ 0 0 ψ = ψ ∨ propagator D ρ 0 0 ψ = 0 := by
  unfold propagator
  split_ifs with h
  · exact Or.inl h.choose_spec.terminal
  · exact Or.inr rfl

theorem S7PIDM_g0 (D : DynData d) (ρ : ℝ → Torus d → ℝ) (k j : NonzeroLattice d) :
    |Torus.funRealCoeff (propagator D ρ 0 0 (Torus.realMode j)) k| ≤ if j = k then 1 else 0 := by
  have e : Torus.funRealCoeff (Torus.realMode j) k = if k = j then 1 else 0 := by
    unfold Torus.funRealCoeff
    exact Torus.realMode_orthonormal k j
  rcases S7PIDM_prop_zero D ρ (Torus.realMode j) with h | h
  · rw [h, e]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_neg hjk, if_neg (Ne.symm hjk)]; simp
  · have z : Torus.funRealCoeff (0 : Torus d → ℝ) k = 0 := by simp [Torus.funRealCoeff]
    rw [h, z, abs_zero]
    split_ifs <;> norm_num

/-- `|φ̂(k)| ⟨k⟩^{σ} ≤ ‖φ‖_{H^σ}` for `φ ∈ H^σ`. -/
theorem S7PIDM_coeff_le {σ : ℝ} {φ : Torus d → ℝ} (hφ : MemSobolev σ φ) (k : NonzeroLattice d) :
    |Torus.funRealCoeff φ k| ≤ Lattice.jp k.1 ^ (-σ) * sobolevNorm σ φ := by
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos k.1
  have hle : Lattice.jp k.1 ^ (2 * σ) * Torus.funRealCoeff φ k ^ 2 ≤
      ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * σ) * Torus.funRealCoeff φ j ^ 2 :=
    hφ.2.le_tsum k (fun j _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos j.1).le _) (sq_nonneg _))
  have hsn : sobolevNorm σ φ ^ 2 = (Torus.mean φ) ^ 2 +
      ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * σ) * Torus.funRealCoeff φ j ^ 2 := by
    unfold sobolevNorm
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _)
      (tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos j.1).le _) (sq_nonneg _)))
  have hsn0 : 0 ≤ sobolevNorm σ φ := S7PIDM_sob_nonneg σ φ
  have h1 : (Lattice.jp k.1 ^ σ * |Torus.funRealCoeff φ k|) ^ 2 ≤ sobolevNorm σ φ ^ 2 := by
    rw [mul_pow, sq_abs, Torus.jp_rpow_sq, hsn]
    linarith [sq_nonneg (Torus.mean φ)]
  have h2 : Lattice.jp k.1 ^ σ * |Torus.funRealCoeff φ k| ≤ sobolevNorm σ φ :=
    (abs_le_of_sq_le_sq' h1 hsn0).2
  have h3 : |Torus.funRealCoeff φ k| =
      Lattice.jp k.1 ^ (-σ) * (Lattice.jp k.1 ^ σ * |Torus.funRealCoeff φ k|) := by
    rw [← mul_assoc, Real.rpow_neg hj.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hj σ).ne', one_mul]
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hj.le _)

theorem S7PIDM_fc_modeVec (m : ℝ) (k j : NonzeroLattice d) :
    NegSobolev.fourierCoeff (modeVec m k) j = if j = k then 1 else 0 := by
  have hmem : Memℓp (fun i : NonzeroLattice d => Lattice.jp i.1 ^ (-m) *
      (if i = k then (1 : ℝ) else 0)) 2 := by
    rw [Torus.memℓp_two_iff]
    refine summable_of_ne_finset_zero (s := {k}) fun i hi => ?_
    have hik : i ≠ k := by simpa using hi
    simp [hik]
  unfold modeVec NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem (fun i => if i = k then (1 : ℝ) else 0) hmem j]
  have hj : 0 < Lattice.jp j.1 := Torus.jp_pos j.1
  have hmm : Lattice.jp j.1 ^ m * Lattice.jp j.1 ^ (-m) = 1 := by
    rw [← Real.rpow_add hj]; simp
  split_ifs with hjk
  · rw [mul_one, hmm]
  · rw [mul_zero, mul_zero]

theorem S7PIDM_eval_modeVec (m : ℝ) (k : NonzeroLattice d) (ψ : Torus d → ℝ) :
    NegSobolev.eval (modeVec m k) ψ = Torus.funRealCoeff ψ k := by
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · rw [S7PIDM_fc_modeVec, if_pos rfl, one_mul]
  · intro j hj
    rw [S7PIDM_fc_modeVec, if_neg hj, zero_mul]

theorem S7PIDM_Vprop_eq (R : Regime d) (m : ℝ) (u t : ℝ) (k : NonzeroLattice d) :
    Vprop R.D R.ρ m t u (modeVec m k) = NegSobolev.ofSeq m
      (fun j : NonzeroLattice d => Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k) := by
  unfold Vprop
  simp only [S7PIDM_eval_modeVec]

theorem S7PIDM_eval_vprop (R : Regime d) (m : ℝ) (u t : ℝ) (k : NonzeroLattice d) (φ : Torus d → ℝ)
    (hmem : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k) 2) :
    NegSobolev.eval (Vprop R.D R.ρ m t u (modeVec m k)) φ =
      ∑' j : NonzeroLattice d, Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k *
        Torus.funRealCoeff φ j := by
  rw [S7PIDM_Vprop_eq]
  unfold NegSobolev.eval
  refine tsum_congr fun j => ?_
  have hj : 0 < Lattice.jp j.1 := Torus.jp_pos j.1
  have hmm : Lattice.jp j.1 ^ m * Lattice.jp j.1 ^ (-m) = 1 := by
    rw [← Real.rpow_add hj]; simp
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem _ hmem j]
  rw [← mul_assoc, hmm, one_mul]

theorem S7PIDM_eval_vprop_not (R : Regime d) (m : ℝ) (u t : ℝ) (k : NonzeroLattice d) (φ : Torus d → ℝ)
    (hmem : ¬ Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k) 2) :
    NegSobolev.eval (Vprop R.D R.ρ m t u (modeVec m k)) φ = 0 := by
  have h0 : Vprop R.D R.ρ m t u (modeVec m k) = 0 := by
    rw [S7PIDM_Vprop_eq]
    unfold NegSobolev.ofSeq
    exact dif_neg hmem
  have hc : ∀ j : NonzeroLattice d, NegSobolev.fourierCoeff (0 : NegSobolev d m) j = 0 := by
    intro j
    have : NegSobolev.coord (0 : NegSobolev d m) j = 0 := rfl
    unfold NegSobolev.fourierCoeff
    rw [this, mul_zero]
  rw [h0]
  unfold NegSobolev.eval
  simp [hc]

/-- The `t = 0` bound: at `u = t = 0` the coefficient functional of `U^{0,0}φ` is `φ̂(k)` or `0`. -/
theorem S7PIDM_zero_bound (R : Regime d) (L : ℕ) (k : NonzeroLattice d) (φ : Torus d → ℝ)
    (hsob : MemSobolev (L : ℝ) φ) :
    |∑' j : NonzeroLattice d, Torus.funRealCoeff (propagator R.D R.ρ 0 0 (Torus.realMode j)) k *
        Torus.funRealCoeff φ j| ≤ Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ := by
  rw [tsum_eq_single k]
  · have hg : |Torus.funRealCoeff (propagator R.D R.ρ 0 0 (Torus.realMode k)) k| ≤ 1 := by
      have := S7PIDM_g0 R.D R.ρ k k
      rwa [if_pos rfl] at this
    rw [abs_mul]
    calc |Torus.funRealCoeff (propagator R.D R.ρ 0 0 (Torus.realMode k)) k| *
          |Torus.funRealCoeff φ k| ≤ 1 * |Torus.funRealCoeff φ k| :=
          mul_le_mul_of_nonneg_right hg (abs_nonneg _)
      _ = |Torus.funRealCoeff φ k| := one_mul _
      _ ≤ _ := S7PIDM_coeff_le hsob k
  · intro j hj
    have := S7PIDM_g0 R.D R.ρ k j
    rw [if_neg hj] at this
    have hg : Torus.funRealCoeff (propagator R.D R.ρ 0 0 (Torus.realMode j)) k = 0 :=
      abs_nonpos_iff.1 this
    rw [hg, zero_mul]

/-- Row bound from the finite-section estimate: for a row `i` of a matrix with `pieFinBd S C`, and `x ∈ ℓ²`,
`|∑_j S_{ij} x_j| ≤ C ‖x‖`. -/
theorem S7PIDM_row {ι : Type*} (S : ι → ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hS : HRS.MC.Sec7.PIE.pieFinBd S C) (i : ι) (x : ι → ℝ) (hx : Summable fun j => x j ^ 2)
    {B : ℝ} (hB : 0 ≤ B) (hxB : ∑' j, x j ^ 2 ≤ B ^ 2) :
    Summable (fun j => S i j * x j) ∧ |∑' j, S i j * x j| ≤ C * B := by
  have hrow : ∀ K : Finset ι, (∑ k ∈ K, S i k * x k) ^ 2 ≤ C ^ 2 * ∑ k ∈ K, x k ^ 2 := by
    intro K
    have h := hS K {i} x
    simpa using h
  have hrow2 : ∀ K : Finset ι, ∑ k ∈ K, S i k ^ 2 ≤ C ^ 2 := by
    intro K
    have h := hS K {i} (fun k => S i k)
    simp only [Finset.sum_singleton] at h
    have e : ∑ k ∈ K, S i k * S i k = ∑ k ∈ K, S i k ^ 2 :=
      Finset.sum_congr rfl fun k _ => (sq _).symm
    rw [e] at h
    have hs0 : 0 ≤ ∑ k ∈ K, S i k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos (sub_pos.2 hcon) (sub_pos.2 hcon), mul_nonneg (sq_nonneg C) (sub_pos.2 hcon).le]
  have hsq : Summable fun k => S i k ^ 2 :=
    summable_of_sum_le (fun k => sq_nonneg _) (fun K => hrow2 K)
  have hsum : Summable fun j => S i j * x j :=
    Summable.of_norm_bounded (g := fun j => (S i j ^ 2 + x j ^ 2) / 2) ((hsq.add hx).div_const 2)
      fun j => by
        rw [Real.norm_eq_abs]
        refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (S i j - x j), sq_nonneg (S i j + x j)]
  have hK : ∀ K : Finset ι, |∑ k ∈ K, S i k * x k| ≤ C * B := by
    intro K
    have h2 : ∑ k ∈ K, x k ^ 2 ≤ ∑' j, x j ^ 2 := hx.sum_le_tsum K (fun j _ => sq_nonneg _)
    have h1 : (∑ k ∈ K, S i k * x k) ^ 2 ≤ (C * B) ^ 2 := by
      calc (∑ k ∈ K, S i k * x k) ^ 2 ≤ C ^ 2 * ∑ k ∈ K, x k ^ 2 := hrow K
        _ ≤ C ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left (h2.trans hxB) (sq_nonneg C)
        _ = (C * B) ^ 2 := by ring
    exact abs_le_of_sq_le_sq h1 (mul_nonneg hC hB)
  refine ⟨hsum, abs_le.2 ⟨?_, ?_⟩⟩
  · have hlow : -(∑' j, S i j * x j) ≤ C * B := by
      refine le_of_tendsto hsum.hasSum.neg (Eventually.of_forall fun K => ?_)
      simp only [Finset.sum_neg_distrib]
      linarith [neg_le_abs (∑ k ∈ K, S i k * x k), hK K]
    linarith
  · refine le_of_tendsto hsum.hasSum (Eventually.of_forall fun K => ?_)
    linarith [le_abs_self (∑ k ∈ K, S i k * x k), hK K]

/-- The `t > 0` bound: the row of the matrix `pieT(u,t)` at level `L` applied to `φ̂`. -/
theorem S7PIDM_pos_bound (R : Regime d) (L : ℕ) (u t : ℝ) (k : NonzeroLattice d) (φ : Torus d → ℝ)
    (hsob : MemSobolev (L : ℝ) φ) (C : ℝ) (hC0 : 0 ≤ C)
    (hS : HRS.MC.Sec7.PIE.pieFinBd (HRS.MC.Sec7.PIE.pieWmat (fun j : NonzeroLattice d => Lattice.jp j.1)
      (HRS.MC.Sec7.PIE.pieT R.D R.ρ u t) (L : ℝ)) C) :
    |∑' j : NonzeroLattice d, Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k *
        Torus.funRealCoeff φ j| ≤ C * (Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ) := by
  obtain ⟨x, hx⟩ : ∃ x : NonzeroLattice d → ℝ,
      ∀ j, x j = Lattice.jp j.1 ^ (L : ℝ) * Torus.funRealCoeff φ j := ⟨_, fun j => rfl⟩
  have hxsq : Summable fun j => x j ^ 2 := by
    refine hsob.2.congr fun j => ?_
    rw [hx, mul_pow, Torus.jp_rpow_sq]
  have hsn : sobolevNorm (L : ℝ) φ ^ 2 = (Torus.mean φ) ^ 2 +
      ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (L : ℝ)) * Torus.funRealCoeff φ j ^ 2 := by
    unfold sobolevNorm
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _)
      (tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos j.1).le _) (sq_nonneg _)))
  have hxB : ∑' j, x j ^ 2 ≤ sobolevNorm (L : ℝ) φ ^ 2 := by
    have e : ∑' j, x j ^ 2 =
        ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (L : ℝ)) * Torus.funRealCoeff φ j ^ 2 :=
      tsum_congr fun j => by rw [hx, mul_pow, Torus.jp_rpow_sq]
    rw [e, hsn]
    linarith [sq_nonneg (Torus.mean φ)]
  obtain ⟨hsum, hbd⟩ := S7PIDM_row _ hC0 hS k x hxsq (S7PIDM_sob_nonneg _ _) hxB
  have hid : ∀ j : NonzeroLattice d,
      Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k * Torus.funRealCoeff φ j =
        Lattice.jp k.1 ^ (-(L : ℝ)) * (HRS.MC.Sec7.PIE.pieWmat (fun j : NonzeroLattice d => Lattice.jp j.1)
          (HRS.MC.Sec7.PIE.pieT R.D R.ρ u t) (L : ℝ) k j * x j) := by
    intro j
    have hk : 0 < Lattice.jp k.1 := Torus.jp_pos k.1
    have hj : 0 < Lattice.jp j.1 := Torus.jp_pos j.1
    have hk1 : Lattice.jp k.1 ^ (-(L : ℝ)) * Lattice.jp k.1 ^ (L : ℝ) = 1 := by
      rw [← Real.rpow_add hk]; simp
    have hj1 : Lattice.jp j.1 ^ (-(L : ℝ)) * Lattice.jp j.1 ^ (L : ℝ) = 1 := by
      rw [← Real.rpow_add hj]; simp
    have key : ∀ P A α β γ δ : ℝ, α * β = 1 → γ * δ = 1 → P * A = α * (β * P * γ * (δ * A)) := by
      intro P A α β γ δ h1 h2
      linear_combination (-(P * A * (γ * δ))) * h1 + (-(P * A)) * h2
    rw [hx]
    simp only [HRS.MC.Sec7.PIE.pieWmat, HRS.MC.Sec7.PIE.pieT]
    exact key _ _ _ _ _ _ hk1 hj1
  have hpos : 0 ≤ Lattice.jp k.1 ^ (-(L : ℝ)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  rw [tsum_congr hid, tsum_mul_left, abs_mul, abs_of_nonneg hpos]
  calc Lattice.jp k.1 ^ (-(L : ℝ)) * |∑' j, HRS.MC.Sec7.PIE.pieWmat (fun j : NonzeroLattice d => Lattice.jp j.1)
          (HRS.MC.Sec7.PIE.pieT R.D R.ρ u t) (L : ℝ) k j * x j|
      ≤ Lattice.jp k.1 ^ (-(L : ℝ)) * (C * sobolevNorm (L : ℝ) φ) := mul_le_mul_of_nonneg_left hbd hpos
    _ = C * (Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ) := by ring

/-- **Proof of `s7_PID_mode_decay`** (statement verbatim from `HRS.MC.Sec7.PIDPlan`). -/
theorem s7_PID_mode_decay_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ k : NonzeroLattice d,
      |NegSobolev.eval (Vprop R.D R.ρ m t u (modeVec m k)) φ| ≤ A * Lattice.jp k.1 ^ (-(N : ℝ)) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = N + PDE.mStar d + 1 := ⟨_, rfl⟩
  have hNL : N ≤ L := by omega
  have hmL : PDE.mStar d ≤ L := by omega
  have hH := S7PIDM_pie R T hT L hmL
  obtain ⟨C, hC0, hC⟩ := HRS.MC.Sec7.PIE.pie_finBd hH L (by omega) le_rfl
  have hsob : MemSobolev (L : ℝ) φ := HRS.A33.a33_memSob (L : ℝ) hφ
  have hsob0 : 0 ≤ sobolevNorm (L : ℝ) φ := S7PIDM_sob_nonneg _ _
  have hA0 : 0 ≤ (C + 1) * sobolevNorm (L : ℝ) φ := mul_nonneg (by linarith) hsob0
  refine ⟨(C + 1) * sobolevNorm (L : ℝ) φ, hA0, fun u t hu hut htT k => ?_⟩
  have hjN : 0 ≤ Lattice.jp k.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hjL : 0 ≤ Lattice.jp k.1 ^ (-(L : ℝ)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hjLN : Lattice.jp k.1 ^ (-(L : ℝ)) ≤ Lattice.jp k.1 ^ (-(N : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k.1)
    have : (N : ℝ) ≤ (L : ℝ) := by exact_mod_cast hNL
    linarith
  by_cases hmem : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k) 2
  · rw [S7PIDM_eval_vprop R m u t k φ hmem]
    have hcore : |∑' j : NonzeroLattice d,
        Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k * Torus.funRealCoeff φ j| ≤
          (C + 1) * sobolevNorm (L : ℝ) φ * Lattice.jp k.1 ^ (-(L : ℝ)) := by
      rcases eq_or_lt_of_le (hu.trans hut) with ht0 | htpos
      · subst ht0
        have hu0 : u = 0 := le_antisymm hut hu
        subst hu0
        refine (S7PIDM_zero_bound R L k φ hsob).trans ?_
        have e : (C + 1) * sobolevNorm (L : ℝ) φ * Lattice.jp k.1 ^ (-(L : ℝ)) =
            Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ +
              C * (Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ) := by ring
        rw [e]
        have : 0 ≤ C * (Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ) :=
          mul_nonneg hC0 (mul_nonneg hjL hsob0)
        linarith
      · refine (S7PIDM_pos_bound R L u t k φ hsob C hC0 (hC t ⟨htpos, htT⟩ u ⟨hu, hut⟩)).trans ?_
        have e : (C + 1) * sobolevNorm (L : ℝ) φ * Lattice.jp k.1 ^ (-(L : ℝ)) =
            C * (Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ) +
              Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ := by ring
        rw [e]
        have : 0 ≤ Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) φ := mul_nonneg hjL hsob0
        linarith
    calc _ ≤ (C + 1) * sobolevNorm (L : ℝ) φ * Lattice.jp k.1 ^ (-(L : ℝ)) := hcore
      _ ≤ (C + 1) * sobolevNorm (L : ℝ) φ * Lattice.jp k.1 ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_left hjLN hA0
  · rw [S7PIDM_eval_vprop_not R m u t k φ hmem, abs_zero]
    exact mul_nonneg hA0 hjN

end HRS.MC.Sec7.S7PIDM

end
