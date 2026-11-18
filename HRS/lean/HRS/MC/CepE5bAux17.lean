import HRS.MC.CepE5bAux11

/-!
# Packet CEPE5B, auxiliary 17: `Φ_n(z) ≲ 1 + log n` on a bounded part of the alcove

Take the interior point `y = z + θ(ρ - z)`, `θ = n^{-1/2}`: its gaps lie in `[θ/N, 1 - θ/N]`, so `Φ(y) ≲ log(N/θ)` and
`(n/2)|z - y|² = ½|ρ - z|² ≤ C`; then `Φ_n(z) ≤ Φ(y) + (n/2)|z - y|²`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE4 (e4_rho)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

theorem e5b_sin_lower {d : ℝ} {c : ℝ} (hc : 0 ≤ c) (h1 : c ≤ d) (h2 : c ≤ 1 - d) :
    2 * c ≤ Real.sin (Real.pi * d) := by
  have hpi := Real.pi_pos
  rcases le_total d (1 / 2) with h | h
  · have := Real.mul_le_sin (x := Real.pi * d) (by nlinarith) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * d) = 2 * d := by field_simp
    rw [e] at this
    linarith
  · have h3 : Real.sin (Real.pi * d) = Real.sin (Real.pi * (1 - d)) := by
      rw [show Real.pi * (1 - d) = Real.pi - Real.pi * d by ring, Real.sin_pi_sub]
    have := Real.mul_le_sin (x := Real.pi * (1 - d)) (by nlinarith) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * (1 - d)) = 2 * (1 - d) := by field_simp
    rw [e] at this
    rw [h3]
    linarith

/-- Gaps of an interior point. -/
theorem e5b_interior_gap {z : Ch N} (hz : z ∈ cep_Alcove N) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {k l : Fin N} (hkl : k < l) :
    θ / N ≤ (z + θ • (e4_rho N - z)) l - (z + θ • (e4_rho N - z)) k ∧
    θ / N ≤ 1 - ((z + θ • (e4_rho N - z)) l - (z + θ • (e4_rho N - z)) k) := by
  have hg := HRS.MC.CepE2.cepe2_mem_alcove_iff.1 hz k l hkl
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by have := k.2; omega : 0 < N)
  have hk : ((k : ℕ) : ℝ) + 1 ≤ (l : ℕ) := by exact_mod_cast hkl
  have hl : ((l : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast l.2
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  have e : (z + θ • (e4_rho N - z)) l - (z + θ • (e4_rho N - z)) k =
      (1 - θ) * (z l - z k) + θ * ((((l : ℕ) : ℝ) - ((k : ℕ) : ℝ)) / N) := by
    simp only [e4_rho, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  rw [e]
  have h1 : 1 / (N : ℝ) ≤ (((l : ℕ) : ℝ) - ((k : ℕ) : ℝ)) / N :=
    div_le_div_of_nonneg_right (by linarith) hNp.le
  have h2 : (((l : ℕ) : ℝ) - ((k : ℕ) : ℝ)) / N ≤ 1 - 1 / (N : ℝ) := by
    rw [show (1 : ℝ) - 1 / N = ((N : ℝ) - 1) / N by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hNp.le
  have h3 : (0 : ℝ) ≤ (1 - θ) * (z l - z k) := mul_nonneg (by linarith) hg.1.le
  have h4 : (1 - θ) * (z l - z k) ≤ (1 - θ) * 1 :=
    mul_le_mul_of_nonneg_left hg.2.le (by linarith)
  constructor
  · calc θ / N = θ * (1 / N) := by ring
      _ ≤ θ * ((((l : ℕ) : ℝ) - ((k : ℕ) : ℝ)) / N) := mul_le_mul_of_nonneg_left h1 hθ0.le
      _ ≤ _ := by linarith
  · calc θ / N = θ * (1 / N) := by ring
      _ ≤ θ * (1 - ((((l : ℕ) : ℝ) - ((k : ℕ) : ℝ)) / N)) := by
          refine mul_le_mul_of_nonneg_left ?_ hθ0.le
          linarith
      _ ≤ _ := by nlinarith

theorem e5b_interior_mem {z : Ch N} (hz : z ∈ cep_Alcove N) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    z + θ • (e4_rho N - z) ∈ cep_Alcove N := by
  refine HRS.MC.CepE2.cepe2_mem_alcove_iff.2 ?_
  intro k l hkl
  have := e5b_interior_gap hz hθ0 hθ1 hkl
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by have := k.2; omega : 0 < N)
  have : 0 < θ / N := by positivity
  constructor <;> linarith [e5b_interior_gap hz hθ0 hθ1 hkl |>.1, e5b_interior_gap hz hθ0 hθ1 hkl |>.2]

/-- `Φ` at an interior point. -/
theorem e5b_Phi_interior (ha : 0 < a) {z : Ch N} (hz : z ∈ cep_Alcove N) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    cep_chamberPot a N (z + θ • (e4_rho N - z)) ≤
      (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log (N / (4 * θ)) := by
  refine le_of_eq_of_le (HRS.MC.CepE2.cepe2_Phi_eq a _) ?_
  have hc : 0 ≤ a / N := div_nonneg ha.le (Nat.cast_nonneg _)
  have e : (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log (N / (4 * θ)) =
      (a / N) * ∑ k : Fin N, ∑ l : Fin N, if k < l then Real.log (N / (4 * θ)) else 0 := by
    unfold HRS.MC.CepE2.cepe2_npairs
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    have hNp : (0 : ℝ) < N := by exact_mod_cast (by have := k.2; omega : 0 < N)
    obtain ⟨hg1, hg2⟩ := e5b_interior_gap hz hθ0 hθ1 hkl
    have hs := e5b_sin_lower (by positivity) hg1 hg2
    have hpos : 0 < 4 * θ / N := by positivity
    have hlog : Real.log (4 * θ / N) ≤ Real.log (2 * Real.sin (Real.pi * ((z + θ • (e4_rho N - z)) l -
        (z + θ • (e4_rho N - z)) k))) := by
      refine Real.log_le_log hpos ?_
      have : 4 * θ / N = 2 * (2 * (θ / N)) := by ring
      rw [this]
      linarith
    have e2 : Real.log (N / (4 * θ)) = -Real.log (4 * θ / N) := by
      rw [← Real.log_inv, inv_div]
    unfold HRS.MC.CepE2.cepe2_f
    rw [e2]
    linarith
  · simp [hkl]

/-- The logarithmic bound on `Φ_n`. -/
theorem e5b_Pn_log_le (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 1 ≤ n) {z : Ch N}
    (hz : z ∈ cep_Alcove N) {R : ℝ} (hR : ‖z‖ ≤ R) :
    e5b_Pn a N J n z ≤ (a / N) * HRS.MC.CepE2.cepe2_npairs N * (|Real.log (N / 4)| + (1 / 2) * Real.log n) +
      (1 / 2) * (R + ‖e4_rho N‖) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsq1 : 1 ≤ Real.sqrt n := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn
  set θ : ℝ := 1 / Real.sqrt n with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; exact (div_le_one hsq).2 hsq1
  have hmem := e5b_interior_mem hz hθ0 hθ1
  have h1 := e5b_Pn_le ha.le hJ hn0 z hmem
  have h2 := e5b_Phi_interior ha hz hθ0 hθ1
  have hnp : 0 ≤ HRS.MC.CepE2.cepe2_npairs N := HRS.MC.CepE2.cepe2_npairs_nonneg
  have hcoef : 0 ≤ (a / N) * HRS.MC.CepE2.cepe2_npairs N := by positivity
  have hlog : Real.log (N / (4 * θ)) ≤ |Real.log (N / 4)| + (1 / 2) * Real.log n := by
    by_cases hN : (N : ℝ) = 0
    · have := Real.log_nonneg hn
      simp [hN]
      positivity
    have hNp : 0 < (N : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hN)
    have e : N / (4 * θ) = (N / 4) * Real.sqrt n := by rw [hθ]; field_simp
    rw [e, Real.log_mul (by positivity) hsq.ne', Real.log_sqrt hn0.le]
    have := le_abs_self (Real.log (N / 4))
    linarith
  have h3 : ‖z - (z + θ • (e4_rho N - z))‖ = θ * ‖e4_rho N - z‖ := by
    rw [show z - (z + θ • (e4_rho N - z)) = -(θ • (e4_rho N - z)) by abel, norm_neg, norm_smul,
      Real.norm_of_nonneg hθ0.le]
  have h4 : n / 2 * ‖z - (z + θ • (e4_rho N - z))‖ ^ 2 = (1 / 2) * ‖e4_rho N - z‖ ^ 2 := by
    rw [h3, mul_pow, hθ, div_pow, Real.sq_sqrt hn0.le]
    field_simp
  have h5 : ‖e4_rho N - z‖ ≤ R + ‖e4_rho N‖ := by
    calc ‖e4_rho N - z‖ ≤ ‖e4_rho N‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have h6 : ‖e4_rho N - z‖ ^ 2 ≤ (R + ‖e4_rho N‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
  have h7 := mul_le_mul_of_nonneg_left hlog hcoef
  rw [h4] at h1
  linarith

end HRS.MC.CepE5b
