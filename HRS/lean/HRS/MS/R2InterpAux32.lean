import HRS.MS.R2InterpAux31

/-!
# S10.2 (worker S102), part 32 (packet B1): the uniform bound of the covariance rate against bilinear forms

`|∑_{k,k'} rate_{kk'}(u) N(Λe_k, Λe_{k'})| ≤ C_b ‖N‖`, `C_b` independent of `L`, `u ∈ [0,T]` and the bilinear form `N` (torus `s7_PIB_rate_bound`).
The input on the mean-field density is a uniform weighted moment `∫ ρ_u ⟨x⟩^{2P} ≤ M_ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_Lam_vv (hT : 0 < T) (L : ℕ) (u : ℝ) (x : Euc d) (a : Fin d) :
    (s102_Lam T L (s102_vv C m hT L u x a) : OscPath d m T) =
      ∑ p ∈ s102_idx d L, s102_cc C m hT L u x a p • s102_bpath (m := m) T L p := by
  have : ∑ p ∈ s102_idx d L, s102_cc C m hT L u x a p • s102_bpath (m := m) T L p =
      ∑ k : Fin (s102_q d L), s102_cc C m hT L u x a (s102_pk d L k) • s102_bpath (m := m) T L (s102_pk d L k) := by
    rw [← Finset.sum_coe_sort (s102_idx d L)]
    exact (Fintype.sum_equiv (s102_pe d L) _ _ (fun k => rfl)).symm
  rw [this, s102_Lam_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem s102_rate_bound (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 + 1 < r) (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T) (hT : 0 < T)
    (Mρ : ℝ) (hρint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (C.ρ u))
    (hρnn : ∀ u ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ C.ρ u x)
    (hρmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x => C.ρ u x * jbracket x ^ (2 * Pw)) ∧
      ∫ x, C.ρ u x * jbracket x ^ (2 * Pw) ≤ Mρ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (L : ℕ) {u : ℝ}, u ∈ Icc (0 : ℝ) T → ∀ N : OscPath d m T [×2]→L[ℝ] ℝ,
      |∑ k, ∑ k', s102_rateM C m hT L u k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))]| ≤
          Cb * ‖N‖ := by
  obtain ⟨Ce, hCe, hF⟩ := s102_feature_norm hd hP0 hr hP hD hlin hT
  set KV := s102_KV d r Pw c with hKV
  have hKV0 : 0 ≤ KV := s102_KV_nonneg d r Pw c
  refine ⟨2 * |C.ν| * d * Ce ^ 2 * KV ^ 2 * |Mρ|, by positivity, fun L u hu N => ?_⟩
  rw [s102_gram_identity hD hT L hu (hρint u hu) N]
  have hmom := hρmom u hu
  set K := (d : ℝ) * (Ce ^ 2 * KV ^ 2) * ‖N‖ with hK
  have hpt : ∀ x, ‖C.ρ u x * ∑ a, N ![s102_Lam T L (s102_vv C m hT L u x a),
      s102_Lam T L (s102_vv C m hT L u x a)]‖ ≤ K * (C.ρ u x * jbracket x ^ (2 * Pw)) := by
    intro x
    have hρx := hρnn u hu x
    have hjb : 0 < jbracket x := HRS.MS.Who.who_jb_pos x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρx]
    have hsum : |∑ a, N ![s102_Lam T L (s102_vv C m hT L u x a), s102_Lam T L (s102_vv C m hT L u x a)]| ≤
        (d : ℝ) * (Ce ^ 2 * KV ^ 2) * jbracket x ^ (2 * Pw) * ‖N‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ a : Fin d, |N ![s102_Lam T L (s102_vv C m hT L u x a), s102_Lam T L (s102_vv C m hT L u x a)]| ≤
          Ce ^ 2 * KV ^ 2 * jbracket x ^ (2 * Pw) * ‖N‖ := by
        intro a
        have h1 := N.le_opNorm ![s102_Lam T L (s102_vv C m hT L u x a), s102_Lam T L (s102_vv C m hT L u x a)]
        rw [Real.norm_eq_abs] at h1
        refine h1.trans ?_
        rw [Fin.prod_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have hn := hF L hu x a
        rw [← s102_Lam_vv hT L u x a] at hn
        have hn0 := norm_nonneg (s102_Lam T L (s102_vv C m hT L u x a) : OscPath d m T)
        have hsq : ‖(s102_Lam T L (s102_vv C m hT L u x a) : OscPath d m T)‖ *
            ‖(s102_Lam T L (s102_vv C m hT L u x a) : OscPath d m T)‖ ≤
            Ce ^ 2 * KV ^ 2 * jbracket x ^ (2 * Pw) := by
          calc _ ≤ (Ce * jbracket x ^ Pw * KV) * (Ce * jbracket x ^ Pw * KV) := mul_le_mul hn hn hn0 (by positivity)
            _ = Ce ^ 2 * KV ^ 2 * (jbracket x ^ Pw) ^ 2 := by ring
            _ = Ce ^ 2 * KV ^ 2 * jbracket x ^ (2 * Pw) := by
                congr 1
                rw [← Real.rpow_natCast, ← Real.rpow_mul hjb.le]
                norm_num
                ring_nf
        calc ‖N‖ * (‖(s102_Lam T L (s102_vv C m hT L u x a) : OscPath d m T)‖ *
              ‖(s102_Lam T L (s102_vv C m hT L u x a) : OscPath d m T)‖) ≤
            ‖N‖ * (Ce ^ 2 * KV ^ 2 * jbracket x ^ (2 * Pw)) := mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
          _ = _ := by ring
      calc ∑ a : Fin d, |N ![s102_Lam T L (s102_vv C m hT L u x a), s102_Lam T L (s102_vv C m hT L u x a)]|
          ≤ ∑ _a : Fin d, Ce ^ 2 * KV ^ 2 * jbracket x ^ (2 * Pw) * ‖N‖ := Finset.sum_le_sum fun a _ => this a
        _ = _ := by simp [Finset.sum_const, mul_comm, mul_assoc, mul_left_comm]
    calc C.ρ u x * |∑ a, N ![s102_Lam T L (s102_vv C m hT L u x a), s102_Lam T L (s102_vv C m hT L u x a)]|
        ≤ C.ρ u x * ((d : ℝ) * (Ce ^ 2 * KV ^ 2) * jbracket x ^ (2 * Pw) * ‖N‖) :=
          mul_le_mul_of_nonneg_left hsum hρx
      _ = K * (C.ρ u x * jbracket x ^ (2 * Pw)) := by rw [hK]; ring
  have hint : Integrable (fun x => K * (C.ρ u x * jbracket x ^ (2 * Pw))) := hmom.1.const_mul K
  have hb := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hb
  rw [abs_mul, abs_mul]
  have hν : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [hν]
  have hK0 : 0 ≤ K := by positivity
  calc 2 * |C.ν| * |∫ x, C.ρ u x * ∑ a, N ![s102_Lam T L (s102_vv C m hT L u x a),
        s102_Lam T L (s102_vv C m hT L u x a)]| ≤ 2 * |C.ν| * (K * |Mρ|) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.norm_eq_abs]
        refine hb.trans (mul_le_mul_of_nonneg_left (hmom.2.trans (le_abs_self _)) hK0)
    _ = _ := by rw [hK]; ring

end HRS.MS.R2Interp

end
