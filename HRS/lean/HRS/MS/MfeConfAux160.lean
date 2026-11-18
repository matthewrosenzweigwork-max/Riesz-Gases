import HRS.MS.MfeConfAux122

/-!
# S.B.1 (SB5), packet R3b: the coarse pointwise bound of the commutator energy, all `0 ≤ s < d`

`sb1_En_lowerc`: `En_r ≥ -C_E` uniformly in `r ∈ [0,T]`.
`sb1_coarse_comm`: `|C_N(v_r; Z, μ_r)| ≤ K_r (a En_r(Z) + b)` for every `K_r`-Lipschitz exact transport,
with `a > 0`, `b ≥ 0` independent of `r`, `K_r`, `Z`, and `0 ≤ a En_r + b`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the uniform lower bound constant of the modulated energy -/
def sb1CEc (d : ℕ) (s C3 : ℝ) : ℝ :=
  sb1CG d s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) + sb1kap s * (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1CEc_nonneg : 0 ≤ sb1CEc d D.s C3 := by
  have hW : 0 ≤ ∫ y : Euc d, sb1w ((d : ℝ) + 2) y := integral_nonneg fun y => (sb1w_pos _ _).le
  have hM : 0 ≤ C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y := mul_nonneg H.C3nn hW
  have hI := sb1Isig_nonneg (d := d) (sb1sig D.s)
  have hk := sb1kap_nonneg D.s
  have := H.C3nn
  unfold sb1CEc sb1CG
  positivity

theorem sb1_En_lowerc' (hN : 1 ≤ N) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (Z : Whole.EucConfig d N) :
    -sb1CEc d D.s C3 ≤ sb1En (Whole.rieszKernel d D.s) (ρ r) Z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have R := H.rho H.tr.hd hr
  have h := sb1_E_le H.tr.hd H.tr.hs0 H.tr.hsd hN (β := 1) zero_le_one (sb1KerU_riesz d D.s H.tr.hs0) R Z
  have h2 := Real.exp_le_exp.1 h
  unfold sb1CEc
  nlinarith

theorem sb1_En_lowerc (hN : 1 ≤ N) : ∃ CE : ℝ, 0 ≤ CE ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N,
    -CE ≤ sb1En (Whole.rieszKernel d D.s) (ρ r) Z :=
  ⟨_, sb1CEc_nonneg H, fun r hr Z => sb1_En_lowerc' H hN hr Z⟩

/-- the pair sum of `|z|^{-s}` is controlled by the energy -/
theorem sb1_pairsum_le (hN : 1 ≤ N) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (Z : Whole.EucConfig d N) :
    (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Z i - Z j‖ ^ (-D.s) ≤
      sb1En (Whole.rieszKernel d D.s) (ρ r) Z + sb1CEc d D.s C3 + 1 := by
  have hs0 := H.tr.hs0
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hCE := sb1CEc_nonneg H
  have hlow := sb1_En_lowerc' H hN hr Z
  by_cases h0 : D.s = 0
  · rw [h0] at hlow hCE ⊢
    simp only [neg_zero, Real.rpow_zero, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 / (2 * (N : ℝ) ^ 2)) * ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
      have : (((N - 1 : ℕ) : ℝ)) ≤ N := by exact_mod_cast Nat.sub_le N 1
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  · have R := H.rho H.tr.hd hr
    have hk : sb1kap D.s = 0 := by simp [sb1kap, h0]
    have hG : ∀ i, sb1G (Whole.rieszKernel d D.s) (ρ r) (Z i) ≤ sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) := by
      intro i
      have := sb1_G_upper H.tr.hd hs0 H.tr.hsd (sb1KerU_riesz d D.s hs0) R (Z i)
      rw [hk] at this
      linarith
    have hc := sb1_c_lower H.tr.hd hs0 H.tr.hsd (sb1KerU_riesz d D.s hs0) R
    rw [hk] at hc
    have hsum : ∑ i, sb1G (Whole.rieszKernel d D.s) (ρ r) (Z i) ≤
        N * sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hG i)
      simpa using this
    have hpair : ∀ i j, ‖Z i - Z j‖ ^ (-D.s) = Whole.rieszKernel d D.s (Z i - Z j) := by
      intro i j; unfold Whole.rieszKernel; simp [h0]
    simp only [hpair]
    unfold sb1En at hlow ⊢
    have hCEk : sb1CEc d D.s C3 = sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) := by
      unfold sb1CEc; rw [hk]; ring
    rw [hCEk]
    have : (1 / (N : ℝ)) * ∑ i, sb1G (Whole.rieszKernel d D.s) (ρ r) (Z i) ≤
        sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) := by
      rw [one_div, inv_mul_le_iff₀ hn]; linarith
    nlinarith

theorem sb1_coarse_comm (hN : 1 ≤ N) : ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧
    (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N,
      0 ≤ a * sb1En (Whole.rieszKernel d D.s) (ρ r) Z + b) ∧
    ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Kr : ℝ, 0 ≤ Kr →
      (∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) →
      ∀ Z : Whole.EucConfig d N, (∀ i j, i ≠ j → Z i ≠ Z j) →
        |sb1CN D N ρ r Z| ≤ Kr * (a * sb1En (Whole.rieszKernel d D.s) (ρ r) Z + b) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have hσ := sb1_sigma_nonneg hs0
  have hCE := sb1CEc_nonneg H
  have hCs0 : 0 ≤ sb1Cs d D.s C3 := by
    unfold sb1Cs; have := H.C3nn; have := sb1Isig_nonneg (d := d) D.s; positivity
  set σ := Whole.movtr_sigma D.s with hσdef
  set Cs := sb1Cs d D.s C3 with hCs
  refine ⟨σ + 1, σ * (sb1CEc d D.s C3 + 1) + sb1CEc d D.s C3 + 3 / 2 * (σ * Cs), by linarith, by positivity,
    fun r hr Z => ?_, fun r hr Kr hKr hL Z _ => ?_⟩
  · have := sb1_En_lowerc' H hN hr Z
    nlinarith [mul_nonneg hσ hCs0]
  · have R := H.rho hd hr
    have hb : ∀ x y, |sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)) x y| ≤
        σ * Kr * ‖x - y‖ ^ (-D.s) := by
      intro x y
      refine sb1_hk_bound hs0 (fun z hz e => ?_) hKr hL x y
      have := sb1gE_grad_le hs0 (le_refl (0 : ℝ)) hz e (d := d) (s := D.s)
      rwa [Whole.movtr_gEps_zero] at this
    have hCN : sb1CN D N ρ r = fun Z => Whole.pairEnergy
        (sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r))) Z (Whole.withDensityReal (ρ r)) :=
      funext fun Z => by unfold sb1CN; rw [sb1_commKernel_eq]
    rw [hCN]
    have h1 := sb1_pairE_abs_le hd hs0 hsd R (mul_nonneg hσ hKr) hb hN Z
    have h2 := sb1_pairsum_le H hN hr Z
    have h3 := sb1_En_lowerc' H hN hr Z
    have e : (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, σ * Kr * ‖Z i - Z j‖ ^ (-D.s) =
        σ * Kr * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Z i - Z j‖ ^ (-D.s)) := by
      simp only [← Finset.mul_sum]; ring
    rw [e] at h1
    refine h1.trans ?_
    have hσK : 0 ≤ σ * Kr := mul_nonneg hσ hKr
    have := mul_le_mul_of_nonneg_left h2 hσK
    nlinarith [mul_nonneg hσK hCs0, mul_nonneg hKr (add_nonneg (mul_nonneg hσ hCE) hCE)]

end Main

end HRS.MS.MfeConf
