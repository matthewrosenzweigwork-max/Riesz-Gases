import HRS.MC.D47Aux1
import HRS.Kernel.D1

/-!
# Packet D47, auxiliary facts 2: upper bounds for `g_η(0)`.

* `g_η(0) ≤ Σ_k a_η(k)`, which is antitone in `η` (so bounded for `η ≥ η₀`);
* `0 < s`: `g_η(0) ≤ C η^{-s}` for `η < 1` (from D.3);
* `s = 0`: `g_η(0) ≤ -log η + C` for `η < 1` (sharp coefficient; from the local singularity of `g`).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

lemma d47_a_anti {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {b : ℝ} (hb0 : 0 < b)
    {η0 η : ℝ} (h0 : 0 < η0) (h : η0 ≤ η) (k : Lattice d) :
    d47_a ψ s b η k ≤ d47_a ψ s b η0 k := by
  unfold d47_a
  split_ifs with hk
  · exact le_rfl
  · unfold fdlGhat
    refine mul_le_mul_of_nonneg_left ?_ hb0.le
    refine setIntegral_mono_set (d3f_int_psi hψ hs0 h0 hk) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans h0 ht
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (sq_nonneg _)) ht0.le
    · exact (Ioi_subset_Ioi h).eventuallyLE

lemma d47_kappa_nonneg {s : ℝ} (hsd : s < d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {b : ℝ}
    (hb0 : 0 ≤ b) {lam : ℝ} (hlam : 0 < lam) : 0 ≤ d47_kappa ψ s b lam := by
  unfold d47_kappa
  have hI0 : 0 ≤ ∫ x, fdlPhi ψ x := integral_nonneg (fdle_phi_nonneg hψ)
  have hds : 0 < (d : ℝ) - s := by linarith
  have : 0 ≤ lam ^ ((d : ℝ) - s) / ((d : ℝ) - s) := div_nonneg (Real.rpow_nonneg hlam.le _) hds.le
  positivity

lemma d47_trunc_zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    fdlTruncT ψ s b lam 0 = ∑' k, d47_a ψ s b lam k - d47_kappa ψ s b lam := by
  rw [d47_trunc_eq hd hs0 hsd hψ hb hlam]
  simp only [d47_spec_zero]

lemma d47_g0_le_tsum (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    fdlTruncT ψ s b lam 0 ≤ ∑' k, d47_a ψ s b lam k := by
  rw [d47_trunc_zero hd hs0 hsd hψ hb hlam]
  linarith [d47_kappa_nonneg hsd hψ hb.1.le hlam]

lemma d47_g0_const (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {η0 : ℝ} (h0 : 0 < η0) :
    ∃ C : ℝ, ∀ η : ℝ, η0 ≤ η → fdlTruncT ψ s b η 0 ≤ C := by
  refine ⟨∑' k, d47_a ψ s b η0 k, fun η hη => ?_⟩
  refine (d47_g0_le_tsum hd hs0 hsd hψ hb (lt_of_lt_of_le h0 hη)).trans ?_
  exact Summable.tsum_le_tsum (fun k => d47_a_anti hs0 hψ hb.1 h0 hη k)
    (d47_summable hd hs0 hψ hb.1 (lt_of_lt_of_le h0 hη)).2 (d47_summable hd hs0 hψ hb.1 h0).2

/-- `s > 0`: `g_η(0) ≤ C η^{-s}` for `η < 1`. -/
lemma d47_g0_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η < 1 → fdlTruncT ψ s b η 0 ≤ C * η ^ (-s) := by
  obtain ⟨C, hC, h⟩ := D3TG.d3tg_zero hd hs0.le hsd hψ hb
  refine ⟨C, hC, fun η h0 h1 => ?_⟩
  have := h η h0 h1
  rw [if_neg hs0.ne'] at this
  simp only [add_zero] at this
  exact (le_abs_self _).trans this

lemma d47_log_sing (hd : 1 ≤ d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d 0 (Torus.mk x) = -Real.log ‖x‖ + r (Torus.mk x) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    exact periodicLog_local_singularity_d1
  · exact periodicLog_local_singularity h

/-- Lipschitz-type bound at the origin for a spectral kernel. -/
lemma d47_spec_zero_sub {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (has2 : Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * a k)) (y : Euc d) :
    specKernel a 0 - specKernel a (Torus.mk y) ≤
      2 * Real.pi ^ 2 * ‖y‖ ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * a k := by
  have hs1 : Summable (fun k => a k * Torus.cosMode k (0 : Torus d)) := by
    simp only [d47_cosMode_zero, mul_one]; exact has
  have hs2 : Summable (fun k => a k * Torus.cosMode k (Torus.mk y)) :=
    Summable.of_norm_bounded has (fun k => norm_mul_cos_le ha0 k _)
  unfold specKernel
  rw [← Summable.tsum_sub hs1 hs2, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (hs1.sub hs2) (has2.mul_left _)
  rw [d47_cosMode_zero, Torus.cosMode_mk]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * Lattice.dot k y)
  have hdot : (Lattice.dot k y) ^ 2 ≤ Lattice.enorm k ^ 2 * ‖y‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (k i : ℝ)) (fun i => y i)
    rw [enorm_sq, EuclideanSpace.norm_sq_eq]
    simpa [Lattice.dot, Real.norm_eq_abs, sq_abs] using this
  have hak := ha0 k
  calc a k * 1 - a k * Real.cos (2 * Real.pi * Lattice.dot k y)
      = a k * (1 - Real.cos (2 * Real.pi * Lattice.dot k y)) := by ring
    _ ≤ a k * ((2 * Real.pi * Lattice.dot k y) ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hak
        linarith
    _ = a k * (2 * Real.pi ^ 2 * (Lattice.dot k y) ^ 2) := by ring
    _ ≤ a k * (2 * Real.pi ^ 2 * (Lattice.enorm k ^ 2 * ‖y‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hak
        have : 0 ≤ 2 * Real.pi ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hdot this
    _ = 2 * Real.pi ^ 2 * ‖y‖ ^ 2 * (Lattice.enorm k ^ 2 * a k) := by ring

/-- `s = 0`: `g_η(0) ≤ -log η + C` for `η < 1`. -/
lemma d47_g0_log (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {b : ℝ}
    (hb : IsFDLConst ψ 0 b) (hsd : (0 : ℝ) < d) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → η < 1 → fdlTruncT ψ 0 b η 0 ≤ -Real.log η + C := by
  obtain ⟨r, δ, hδ, hr, hloc⟩ := d47_log_sing hd
  have hrc : Continuous r := Torus.continuous_of_continuous_lift (ContDiff.continuous (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr))
  obtain ⟨R, hR0, hR⟩ := HRS.exists_abs_bound hrc
  obtain ⟨M, hM0, hM⟩ := d47_tsum_bound hd (le_refl (0 : ℝ)) hψ hb.1
  set η0 : ℝ := min (δ / 2) (1 / 4) with hη0
  have hη0pos : 0 < η0 := lt_min (by linarith) (by norm_num)
  obtain ⟨C1, hC1⟩ := d47_g0_const hd (le_refl (0 : ℝ)) hsd hψ hb hη0pos
  refine ⟨max C1 (R + 2 * Real.pi ^ 2 * M), fun η hη hη1 => ?_⟩
  by_cases hsm : η0 ≤ η
  · have h1 := hC1 η hsm
    have : 0 ≤ -Real.log η := by
      have := Real.log_nonpos hη.le hη1.le
      linarith
    linarith [le_max_left C1 (R + 2 * Real.pi ^ 2 * M)]
  · push Not at hsm
    -- the test point `y = η e₀`
    set y : Euc d := EuclideanSpace.single ⟨0, by omega⟩ η with hy
    have hynorm : ‖y‖ = η := by
      rw [hy, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hη]
    have hycoord : ∀ i, |y i| ≤ 1 / 2 := by
      intro i
      rw [hy, PiLp.single_apply]
      split_ifs
      · rw [abs_of_pos hη]; linarith [min_le_right (δ / 2) (1 / 4 : ℝ)]
      · simp
    have hyδ : ‖y‖ < δ := by
      rw [hynorm]; linarith [min_le_left (δ / 2) (1 / 4 : ℝ)]
    have hy0 : y ≠ 0 := by
      intro h; rw [h, norm_zero] at hynorm; linarith
    have htd : KernelGrad.tdist (Torus.mk y) 0 = η := by
      rw [KernelGrad.tdist_mk hycoord, hynorm]
    obtain ⟨C, hC0, hCl⟩ := (D3T1.d3t_part_i hd le_rfl hsd hψ hb)
    have heq : fdlTruncT ψ 0 b η (Torus.mk y) = periodicRiesz d 0 (Torus.mk y) :=
      ((hCl η hη hη1).2.1 (Torus.mk y) (by rw [htd])).2
    rw [hloc y hyδ hy0, hynorm] at heq
    -- the spectral bound
    have hspec := d47_spec_zero_sub (fun k => d47_a_nonneg hb.1.le hη k)
      (d47_summable hd (le_refl (0 : ℝ)) hψ hb.1 hη).2 (d47_summable hd (le_refl (0 : ℝ)) hψ hb.1 hη).1 y
    have hT := hM η hη
    rw [hynorm] at hspec
    have hη2 : η ^ 2 * (η ^ (-(0 : ℝ) - 2)) = 1 := by
      rw [show (-(0 : ℝ) - 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hη.le, Real.rpow_natCast]
      field_simp
    have hsp : specKernel (d47_a ψ 0 b η) 0 - specKernel (d47_a ψ 0 b η) (Torus.mk y) ≤
        2 * Real.pi ^ 2 * M := by
      refine hspec.trans ?_
      calc 2 * Real.pi ^ 2 * η ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * d47_a ψ 0 b η k
          ≤ 2 * Real.pi ^ 2 * η ^ 2 * (M * η ^ (-(0 : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = 2 * Real.pi ^ 2 * M * (η ^ 2 * η ^ (-(0 : ℝ) - 2)) := by ring
        _ = 2 * Real.pi ^ 2 * M := by rw [hη2, mul_one]
    have hg0 : fdlTruncT ψ 0 b η 0 = specKernel (d47_a ψ 0 b η) 0 - d47_kappa ψ 0 b η := by
      rw [d47_trunc_eq hd le_rfl hsd hψ hb hη]
    have hgy : fdlTruncT ψ 0 b η (Torus.mk y) =
        specKernel (d47_a ψ 0 b η) (Torus.mk y) - d47_kappa ψ 0 b η := by
      rw [d47_trunc_eq hd le_rfl hsd hψ hb hη]
    have hry := (abs_le.mp (hR (Torus.mk y))).2
    have hmx := le_max_right C1 (R + 2 * Real.pi ^ 2 * M)
    linarith

end HRS.MC.D47
