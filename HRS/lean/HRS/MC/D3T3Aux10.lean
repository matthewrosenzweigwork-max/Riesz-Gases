import HRS.MC.D3T3Aux9

/-!
# Packet D3T3, auxiliary facts: smoothness of `g_λ` on the torus.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_trunc_continuous (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fdlTruncT ψ s b lam) := by
  rw [d3f_truncT_eq hd hs0 hsd hψ hb hlam]
  exact (d3f_Hs_continuous hd hs0 hψ hb.1 hlam).sub continuous_const

lemma d3f_memHs (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    HRS.PDE.MemHs (m : ℝ) (HRS.PDE.coeffOf (fdlTruncT ψ s b lam)) := by
  obtain ⟨B, hB0, hB⟩ := d3f_ghat_decay hs0 hψ hb.1 hlam (m + d + 1)
  set r : ℝ := 2 * (m : ℝ) - 4 * ((m + d + 1 : ℕ) : ℝ) with hr
  have hsum := summable_enorm_rpow_aux (d := d) r (by
    rw [hr]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  have hA : Summable (fun k : NonzeroLattice d =>
      ((1 + 2 * Real.pi) ^ (2 * (m : ℝ)) * B ^ 2) * Lattice.enorm k.1 ^ r) := hsum.mul_left _
  unfold HRS.PDE.MemHs
  rw [Torus.summable_lattice_iff]
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by unfold HRS.PDE.sobWeight; positivity)
    (sq_nonneg _)) (fun k => ?_) hA
  have hk := k.2
  have hen : 1 ≤ Lattice.enorm k.1 := d3f_enorm_ge_one hk
  have hen0 : 0 < Lattice.enorm k.1 := lt_of_lt_of_le one_pos hen
  have hc : ‖HRS.PDE.coeffOf (fdlTruncT ψ s b lam) k.1‖ = fdlGhat ψ s b lam k.1 := by
    rw [HRS.PDE.coeffOf_eq_fcoef, d3f_fcoef_trunc hd hs0 hsd hψ hb hlam hk, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (d3f_ghat_nonneg (ψ := ψ) (s := s) hb.1.le hlam _)]
  rw [hc, HRS.PDE.sobWeight_eq_jp]
  have hjp : Lattice.jp k.1 ≤ (1 + 2 * Real.pi) * Lattice.enorm k.1 := jp_le_enorm k
  have h1 : Lattice.jp k.1 ^ (2 * (m : ℝ)) ≤ (1 + 2 * Real.pi) ^ (2 * (m : ℝ)) *
      Lattice.enorm k.1 ^ (2 * (m : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) hen0.le]
    exact Real.rpow_le_rpow (Torus.jp_pos _).le hjp (by positivity)
  have h2 : fdlGhat ψ s b lam k.1 ^ 2 ≤ B ^ 2 * Lattice.enorm k.1 ^ (-(4 * ((m + d + 1 : ℕ) : ℝ))) := by
    have := hB k.1 hk
    have hg0 := d3f_ghat_nonneg (ψ := ψ) (s := s) hb.1.le hlam k.1
    calc fdlGhat ψ s b lam k.1 ^ 2 ≤ (B * Lattice.enorm k.1 ^ (-(2 * ((m + d + 1 : ℕ) : ℝ)))) ^ 2 :=
          pow_le_pow_left₀ hg0 this 2
      _ = B ^ 2 * Lattice.enorm k.1 ^ (-(4 * ((m + d + 1 : ℕ) : ℝ))) := by
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hen0.le]
          congr 1
          push_cast; ring
  calc Lattice.jp k.1 ^ (2 * (m : ℝ)) * fdlGhat ψ s b lam k.1 ^ 2
      ≤ ((1 + 2 * Real.pi) ^ (2 * (m : ℝ)) * Lattice.enorm k.1 ^ (2 * (m : ℝ))) *
          (B ^ 2 * Lattice.enorm k.1 ^ (-(4 * ((m + d + 1 : ℕ) : ℝ)))) :=
        mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = ((1 + 2 * Real.pi) ^ (2 * (m : ℝ)) * B ^ 2) *
          (Lattice.enorm k.1 ^ (2 * (m : ℝ)) * Lattice.enorm k.1 ^ (-(4 * ((m + d + 1 : ℕ) : ℝ)))) := by
        ring
    _ = _ := by
        rw [← Real.rpow_add hen0, hr, sub_eq_add_neg]

lemma d3f_trunc_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ContDiff ℝ n (Torus.lift (fdlTruncT ψ s b lam)) := by
  set G := fdlTruncT ψ s b lam with hG
  have hcont : Continuous G := d3f_trunc_continuous hd hs0 hsd hψ hb hlam
  have hint : Integrable G := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreal : HRS.PDE.IsRealCoeff (HRS.PDE.coeffOf G) := HRS.PDE.isRealCoeff_coeffOf G hint
  have hm : (d : ℝ) / 2 + (n : ℝ) < ((n + d : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hmem := d3f_memHs hd hs0 hsd hψ hb hlam (n + d)
  have hsC : Summable fun k : Lattice d => ‖HRS.PDE.coeffOf G k‖ :=
    HRS.PDE.summable_norm_of_memHs ((n + d : ℕ) : ℝ) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) _ hmem
  have hinv := HRS.PDE.toFun_coeffOf G hcont hsC
  obtain ⟨C, hC⟩ := HRS.PDE.toFun_isCk_le (d := d) n ((n + d : ℕ) : ℝ) hm
  have := (hC _ hmem hreal).1
  rw [hinv] at this
  exact this

end HRS.MC.D3T3
