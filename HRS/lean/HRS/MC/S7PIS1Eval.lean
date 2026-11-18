import HRS.MC.S7PIS1Sum

/-!
# Packet S1: `V^{t,u}` is the adjoint of the propagator on the evaluation functionals

Proof of `HRS.MC.Sec7.PIPlan.s7_PIS_V_eval` (statement copied verbatim).  Both sides are the double series
`∑_{j,k} F̂_j T_{jk} φ̂_k` (`T = pieT u t`), which converges absolutely: the entries obey `|T_{jk}| ≤ A ⟨j⟩^{-N} ⟨k⟩^{N}`
(finite-section bound at the integer level `N`), `F̂_j ⟨j⟩^{-N}` is summable and `⟨k⟩^N φ̂_k` is summable for smooth `φ`.
The sum over `j` of the right-hand side is the matrix action `S7PIS1_hasSum`; the sum over `k` of the left-hand side is the
coordinate formula `S7PIDV_fc_V`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS1

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- the entries of the propagator matrix at an integer level -/
lemma S7PIS1_entry {D : DynData d} {μ : ℝ → Torus d → ℝ} {u t : ℝ} {M AN : ℝ} (hAN : 0 ≤ AN)
    (h : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) M) AN)
    (j k : NonzeroLattice d) :
    |pieT D μ u t j k| ≤ AN * (Lattice.jp j.1 ^ (-M) * Lattice.jp k.1 ^ M) := by
  have h1 := h {k} {j} (fun _ => 1)
  simp only [Finset.sum_singleton, mul_one, one_pow] at h1
  have h2 : |pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) M j k| ≤ AN :=
    abs_le_of_sq_le_sq' (by simpa using h1) hAN |>.elim fun a b => abs_le.2 ⟨a, b⟩
  have hj := Torus.jp_pos j.1
  have hk := Torus.jp_pos k.1
  have ha : 0 < Lattice.jp j.1 ^ M := Real.rpow_pos_of_pos hj _
  have hb : 0 < Lattice.jp k.1 ^ M := Real.rpow_pos_of_pos hk _
  have e : pieT D μ u t j k = pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) M j k *
      (Lattice.jp j.1 ^ (-M) * Lattice.jp k.1 ^ M) := by
    unfold pieWmat
    rw [Real.rpow_neg hj.le, Real.rpow_neg hk.le]
    field_simp
  rw [e, abs_mul, abs_of_pos (mul_pos (Real.rpow_pos_of_pos hj _) hb)]
  exact mul_le_mul_of_nonneg_right h2 (mul_pos (Real.rpow_pos_of_pos hj _) hb).le

/-- summability of `⟨j⟩^{-M} |F̂_j|` for `d < 2 (M - m)` -/
lemma S7PIS1_summ_F {m M : ℝ} (hM : (d : ℝ) < 2 * (M - m)) (F : NegSobolev d m) :
    Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-M) * |NegSobolev.fourierCoeff F j| := by
  obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
  have ha2 : Summable fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (m - M)) ^ 2 := by
    refine (summable_jp_rpow (d := d) (M - m) hM).congr fun k => ?_
    rw [Torus.jp_rpow_sq]; congr 1; ring
  have hb2 : Summable fun j : NonzeroLattice d => |NegSobolev.coord F j| ^ 2 := by
    simpa [sq_abs] using hF2
  have := (Torus.cs_tsum (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (m - M))
    (fun j => |NegSobolev.coord F j|) (fun j => Real.rpow_nonneg (Torus.jp_pos _).le _)
    (fun _ => abs_nonneg _) ha2 hb2).1
  refine this.congr fun j => ?_
  unfold NegSobolev.fourierCoeff
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos j.1) _), ← mul_assoc,
    ← Real.rpow_add (Torus.jp_pos j.1)]
  rw [show -M + m = m - M by ring]

/-- summability of `⟨k⟩^M |φ̂_k|` for smooth `φ` -/
lemma S7PIS1_summ_phi {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (M : ℝ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ M * |Torus.funRealCoeff φ k| := by
  have hS := (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ (M + ((d : ℝ) + 1) / 2)).2
  have ha2 : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-(((d : ℝ) + 1) / 2))) ^ 2 := by
    refine (summable_jp_rpow (d := d) (((d : ℝ) + 1) / 2) (by linarith)).congr fun k => ?_
    rw [Torus.jp_rpow_sq]; congr 1; ring
  have hb2 : Summable fun k : NonzeroLattice d =>
      (Lattice.jp k.1 ^ (M + ((d : ℝ) + 1) / 2) * |Torus.funRealCoeff φ k|) ^ 2 := by
    refine hS.congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq, sq_abs]
  have := (Torus.cs_tsum (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(((d : ℝ) + 1) / 2)))
    (fun k => Lattice.jp k.1 ^ (M + ((d : ℝ) + 1) / 2) * |Torus.funRealCoeff φ k|)
    (fun k => Real.rpow_nonneg (Torus.jp_pos _).le _)
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _)) ha2 hb2).1
  refine this.congr fun k => ?_
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  congr 2; ring

/-- the core of `V_eval` at fixed integer levels -/
lemma S7PIS1_Veval_core {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1)
    (N : ℕ) (hN : 1 ≤ N) (hNJ : N + 1 ≤ J) (hNm : (d : ℝ) < 2 * (((N : ℝ) + 1) - m))
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T) (F : NegSobolev d m) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (Vprop D μ m t u F) φ = NegSobolev.eval F (propagator D μ u t φ) := by
  classical
  obtain ⟨Am, hAm1, hAmb⟩ := S7PIDV_finBd_unif H m n₀ hn₀ hJ hm0 hm1
  obtain ⟨AN, hAN1, hANb⟩ := S7PIDV_finBd_unif H ((N : ℝ) + 1) N hN hNJ (by linarith) le_rfl
  have hHm := hAmb u t hu hut htT
  have hHN := hANb u t hu hut htT
  have hentry := S7PIS1_entry (by linarith) hHN
  have hFs := S7PIS1_summ_F hNm F
  have hξs := S7PIS1_summ_phi hφ ((N : ℝ) + 1)
  have hsumm : Summable (Function.uncurry fun (j k : NonzeroLattice d) =>
      NegSobolev.fourierCoeff F j * (Torus.funRealCoeff φ k * pieT D μ u t j k)) := by
    have hg := Summable.mul_of_nonneg hFs hξs
      (fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _))
      (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _))
    refine Summable.of_norm_bounded (hg.mul_left AN) fun p => ?_
    obtain ⟨j, k⟩ := p
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
    have h1 := hentry j k
    have h2 : 0 ≤ |NegSobolev.fourierCoeff F j| := abs_nonneg _
    have h3 : 0 ≤ |Torus.funRealCoeff φ k| := abs_nonneg _
    calc |NegSobolev.fourierCoeff F j| * (|Torus.funRealCoeff φ k| * |pieT D μ u t j k|)
        ≤ |NegSobolev.fourierCoeff F j| * (|Torus.funRealCoeff φ k| *
            (AN * (Lattice.jp j.1 ^ (-((N : ℝ) + 1)) * Lattice.jp k.1 ^ ((N : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) h2
      _ = _ := by ring
  unfold NegSobolev.eval
  have h1 : ∀ k, NegSobolev.fourierCoeff (Vprop D μ m t u F) k =
      ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k :=
    fun k => S7PIDV_fc_V D μ m t u (by linarith) hHm F k
  calc ∑' k, NegSobolev.fourierCoeff (Vprop D μ m t u F) k * Torus.funRealCoeff φ k
      = ∑' k, ∑' j, NegSobolev.fourierCoeff F j * (Torus.funRealCoeff φ k * pieT D μ u t j k) := by
        refine tsum_congr fun k => ?_
        rw [h1 k, ← tsum_mul_right]
        exact tsum_congr fun j => by ring
    _ = ∑' j, ∑' k, NegSobolev.fourierCoeff F j * (Torus.funRealCoeff φ k * pieT D μ u t j k) :=
        hsumm.tsum_comm
    _ = ∑' j, NegSobolev.fourierCoeff F j * ∑' k, Torus.funRealCoeff φ k * pieT D μ u t j k :=
        tsum_congr fun j => tsum_mul_left
    _ = ∑' j, NegSobolev.fourierCoeff F j * Torus.funRealCoeff (propagator D μ u t φ) j :=
        tsum_congr fun j => by rw [(S7PIS1_hasSum H hu hut htT hφ j).tsum_eq]

/-- **S1 (`V` is the adjoint of the propagator on the evaluation functionals)**. -/
theorem s7_PIS_V_eval_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (F : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
      NegSobolev.eval (Vprop R.D R.ρ m t u F) φ = NegSobolev.eval F (propagator R.D R.ρ u t φ) := by
  intro u t hu hut htT F φ hφ
  have hd2 : 2 ≤ d := R.hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hm0 : 0 < m := by linarith
  set Nc : ℕ := ⌈m⌉₊ with hNc
  have hmN : m ≤ (Nc : ℝ) := Nat.le_ceil m
  have hNm : (Nc : ℝ) < m + 1 := Nat.ceil_lt_add_one hm0.le
  obtain ⟨n₀, hn₀N⟩ : ∃ n₀ : ℕ, Nc = n₀ + 1 := ⟨Nc - 1, by
    have : (1 : ℝ) ≤ Nc := by linarith
    have : 1 ≤ Nc := by exact_mod_cast this
    omega⟩
  have hcast : (Nc : ℝ) = (n₀ : ℝ) + 1 := by rw [hn₀N]; push_cast; ring
  have hn₀m : (n₀ : ℝ) < m := by linarith
  have hmn₀ : m ≤ (n₀ : ℝ) + 1 := by linarith
  have hn₀big : (3 * (d : ℝ) + 7 < n₀) := by linarith
  have hn₀1 : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ n₀ := by linarith
    exact_mod_cast this
  have hmStar : PDE.mStar d ≤ n₀ + d + 1 := by
    have h1 : ((PDE.mStar d : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 3 := by
      unfold PDE.mStar
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
      linarith
    have h2 : ((PDE.mStar d : ℕ) : ℝ) ≤ ((n₀ + d + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  have H := S7PIS1_hyp R T hT (n₀ + d + 1) hmStar
  refine S7PIS1_Veval_core H m n₀ hn₀1 (by omega) hn₀m hmn₀ (n₀ + d) (by omega) (by omega) ?_ hu hut htT F hφ
  push_cast
  linarith

end HRS.MC.Sec7.S7PIS1

end
