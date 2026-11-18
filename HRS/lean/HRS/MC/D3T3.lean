import HRS.MC.D3T3Aux10

/-!
# Packet D3T3: Lemma D.3 on `𝕋^d`, item (iii) (Fourier side).

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_torus`, the three conjuncts labelled `-- (iii)`;
standalone theorems `d3f_part_iii_a`, `d3f_part_iii_b`, `d3f_part_iii_c` whose conclusions are those conjuncts.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

/-- Lemma D.3 (iii), first conjunct: `ŵ_λ(k) = b ∫_0^λ t^{d-s} ψ̂(tk)² dt/t ≥ 0`. -/
theorem d3f_part_iii_a (hd : 1 ≤ d) {s : ℝ} (_hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ k : Lattice d,
      Torus.fcoef (fdlWT ψ s b lam) k = ((fdlWhat ψ s b lam k : ℝ) : ℂ) ∧
        0 ≤ fdlWhat ψ s b lam k := by
  intro lam hlam _ k
  have hb0 : 0 < b := hb.1
  refine ⟨?_, ?_⟩
  · have hW : fdlWT ψ s b lam = fun x => ∫ t in Ioc 0 lam, kap d s b t * (perJ ψ (x, t) - 0) := by
      funext x
      unfold fdlWT
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      simp only [kap]
      rw [d3f_perJ_eq hψ ht.1, sub_zero]
      ring
    rw [hW, d3f_fubini k (kap d s b) 0 (d3f_int_a hsd hψ k hb0 hlam)]
    unfold fdlWhat
    have key : ∀ f : ℝ → ℝ, ((∫ t in Ioc 0 lam, f t : ℝ) : ℂ) = ∫ t in Ioc 0 lam, (f t : ℂ) :=
      fun f => integral_ofReal.symm
    rw [← integral_const_mul, key]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have hf : (fun x : Torus d => perJ ψ (x, t) - 0) = fdlPer (fdlPhiScale ψ t) :=
      funext fun x => by rw [d3f_perJ_eq hψ ht.1, sub_zero]
    simp only [hf, per_fcoef hd hψ ht.1 k, kap]
    push_cast
    ring
  · unfold fdlWhat
    exact mul_nonneg hb0.le (setIntegral_nonneg measurableSet_Ioc (fun t ht =>
      div_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _)) ht.1.le))

/-- Lemma D.3 (iii), second conjunct: `ĝ_λ(k) = b ∫_λ^∞ t^{d-s} ψ̂(tk)² dt/t ≥ 0` for `k ≠ 0`. -/
theorem d3f_part_iii_b (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ k : Lattice d, k ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t)
        (Set.Ioi lam) ∧
      Torus.fcoef (fdlTruncT ψ s b lam) k = ((fdlGhat ψ s b lam k : ℝ) : ℂ) ∧
        0 ≤ fdlGhat ψ s b lam k := by
  intro lam hlam _ k hk
  have hb0 : 0 < b := hb.1
  refine ⟨d3f_int_psi hψ hs0 hlam hk, ?_, ?_⟩
  · exact d3f_fcoef_trunc hd hs0 hsd hψ hb hlam hk
  · unfold fdlGhat
    exact mul_nonneg hb0.le (setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      div_nonneg (mul_nonneg (Real.rpow_nonneg (lt_trans hlam ht).le _) (sq_nonneg _))
        (lt_trans hlam ht).le))

/-- Lemma D.3 (iii), third conjunct: `∑ |k|² ĝ_λ(k) < ∞` and
`|Δ g_λ(0)| ≤ 4π² ∑ |k|² ĝ_λ(k) ≤ C λ^{-s-2}`. -/
theorem d3f_part_iii_c (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k) ∧
      |Torus.laplacian (fdlTruncT ψ s b lam) 0| ≤
        4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ∧
      4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ≤
        C * lam ^ (-s - 2) := by
  have hb0 : 0 < b := hb.1
  obtain ⟨M, hM0, hM⟩ := d3f_ghat_partial hd hs0 hψ hb0
  refine ⟨4 * Real.pi ^ 2 * M, by positivity, fun lam hlam _ => ?_⟩
  have hnn : ∀ k : Lattice d, 0 ≤ Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k :=
    fun k => mul_nonneg (sq_nonneg _) (d3f_ghat_nonneg hb0.le hlam k)
  have hsm : Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k) :=
    summable_of_sum_le hnn (fun F => hM lam hlam F)
  have hts : ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ≤ M * lam ^ (-s - 2) :=
    Real.tsum_le_of_sum_le hnn (fun F => hM lam hlam F)
  have hS0 : 0 ≤ ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k :=
    tsum_nonneg hnn
  refine ⟨hsm, ?_, ?_⟩
  · obtain ⟨_, hlap⟩ := d3f_lap_zero (φ := fdlTruncT ψ s b lam)
      (d3f_trunc_smooth hd hs0 hsd hψ hb hlam)
    have hre : ∀ k : Lattice d, Lattice.enorm k ^ 2 * (Torus.fcoef (fdlTruncT ψ s b lam) k).re
        = Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k := by
      intro k
      by_cases hk : k = 0
      · subst hk
        have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
        simp [Lattice.enorm, this]
      · rw [d3f_fcoef_trunc hd hs0 hsd hψ hb hlam hk, Complex.ofReal_re]
    simp only [hre] at hlap
    rw [hlap, abs_neg, abs_of_nonneg (by positivity)]
  · calc 4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k
        ≤ 4 * Real.pi ^ 2 * (M * lam ^ (-s - 2)) :=
          mul_le_mul_of_nonneg_left hts (by positivity)
      _ = 4 * Real.pi ^ 2 * M * lam ^ (-s - 2) := by ring

end HRS.MC.D3T3
