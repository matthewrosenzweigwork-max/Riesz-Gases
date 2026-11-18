/-
# HRS.Equilibrium.Q84aEstimates — packet Q84a (Lemma 4.15, size bounds)

The size clauses of `triple_canonical`: for a kernel `ψ` with the conclusions of Proposition 4.13
(`IsPairCorrector`), `G_ψ` satisfies the singular triple envelope with coefficient `C K₁` and `B_ψ`
is bounded by `C K₁ w²`.

Proof (source lines 4895-4904): group each force in the symmetrised sum; the coefficient of
`∇g(a-b)` is `-(∇_xψ(a,c) - ∇_xψ(b,c))`; the gradient difference is bounded by the Hessian bound
along a segment when `|a-b| ≤ |a-c|/2` (`q84a_grad_diff`) and by the separate gradient bounds
otherwise (`q84a_Pq_bound`); the force `F_μ = -β⁻¹∇ρ/ρ - ∇V` is bounded (`q84a_force_bound`).
-/
import HRS.Equilibrium.Q84aAuxB
import HRS.Equilibrium.Q84aAuxC

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84a

variable {d : ℕ} {s : ℝ}

theorem q84a_estimates (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ →
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
          C * K₁ * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
        (∀ x y, x ≠ y → |Bpsi d s ρ ψ x y| ≤ C * K₁ * wEnv s x y ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hs : 0 < s := by linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := q84a_gg_bound hd hs0 hsd
  obtain ⟨M, hM0, hM⟩ := q84a_force_bound hβ hV hρ hρs
  have h2s : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
  refine ⟨8 * Cg * (1 + d) * 2 ^ s + 2 * M + 1 + 8 * Cg + 4 * M, fun f K₁ ψ _ hψ => ⟨?_, ?_⟩⟩
  · -- triple bound
    intro x y z hxy hxz hyz
    have hPs : PsiSize s K₁ ψ := hψ.size
    have hsym : IsSymmPair ψ := hψ.symm
    have hK : 0 ≤ K₁ := q84a_K_nonneg hPs hxy
    have hP : 0 ≤ 8 * Cg * (1 + (d : ℝ)) * 2 ^ s * K₁ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCg0) (by linarith))
        (by positivity)) hK
    have hMK : 0 ≤ M * K₁ := mul_nonneg hM0 hK
    have hwxy := PairCorrAux.one_le_wEnv s x y
    have hwxz := PairCorrAux.one_le_wEnv s x z
    have hwyz := PairCorrAux.one_le_wEnv s y z
    have hwxy0 : 0 < wEnv s x y := by linarith
    have hwxz0 : 0 < wEnv s x z := by linarith
    have hwyz0 : 0 < wEnv s y z := by linarith
    -- the three gradient-difference terms
    have P1 := q84a_Pq_bound hd hs1 hCg0 hCg hPs hxz hxy hyz.symm
    have P2 := q84a_Pq_bound hd hs1 hCg0 hCg hPs hyz hxy.symm hxz.symm
    have P3 := q84a_Pq_bound hd hs1 hCg0 hCg hPs hxy hxz hyz
    rw [PairCorrAux.wEnv_symm s z y] at P1
    rw [PairCorrAux.wEnv_symm s y x, PairCorrAux.wEnv_symm s z x] at P2
    set S := wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z with hS
    have hp1 : 0 ≤ wEnv s x y * wEnv s x z := by positivity
    have hp2 : 0 ≤ wEnv s x y * wEnv s y z := by positivity
    have hp3 : 0 ≤ wEnv s x z * wEnv s y z := by positivity
    have hq1 := mul_nonneg (sub_nonneg.2 hwxy) (sub_nonneg.2 hwxz)
    have hq2 := mul_nonneg (sub_nonneg.2 hwxz) (sub_nonneg.2 hwyz)
    have hS1 : wEnv s x y ≤ S := by nlinarith
    have hS2 : wEnv s x z ≤ S := by nlinarith
    have hS3 : wEnv s y z ≤ S := by nlinarith
    have hQ1 : wEnv s x z * wEnv s x y + wEnv s x z * wEnv s y z ≤ S := by nlinarith
    have hQ2 : wEnv s y z * wEnv s x y + wEnv s y z * wEnv s x z ≤ S := by nlinarith
    have hQ3 : wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z ≤ S := by nlinarith
    have P1' := P1.trans (mul_le_mul_of_nonneg_left hQ1 hP)
    have P2' := P2.trans (mul_le_mul_of_nonneg_left hQ2 hP)
    have P3' := P3.trans (mul_le_mul_of_nonneg_left hQ3 hP)
    -- force terms
    have F1 := q84a_force_term hs1 hPs (hM x) hxy
    have F2 := q84a_force_term hs1 hPs (hM y) hxy.symm
    have F3 := q84a_force_term hs1 hPs (hM x) hxz
    have F4 := q84a_force_term hs1 hPs (hM z) hxz.symm
    have F5 := q84a_force_term hs1 hPs (hM y) hyz
    have F6 := q84a_force_term hs1 hPs (hM z) hyz.symm
    rw [PairCorrAux.wEnv_symm s y x] at F2
    rw [PairCorrAux.wEnv_symm s z x] at F4
    rw [PairCorrAux.wEnv_symm s z y] at F6
    have F1' := F1.trans (mul_le_mul_of_nonneg_left hS1 hMK)
    have F2' := F2.trans (mul_le_mul_of_nonneg_left hS1 hMK)
    have F3' := F3.trans (mul_le_mul_of_nonneg_left hS2 hMK)
    have F4' := F4.trans (mul_le_mul_of_nonneg_left hS2 hMK)
    have F5' := F5.trans (mul_le_mul_of_nonneg_left hS3 hMK)
    have F6' := F6.trans (mul_le_mul_of_nonneg_left hS3 hMK)
    -- the pair projections
    have J1 := hψ.jpair_bound x y hxy
    have J2 := hψ.jpair_bound x z hxz
    have J3 := hψ.jpair_bound y z hyz
    have J1' := J1.trans (mul_le_mul_of_nonneg_left hS1 hK)
    have J2' := J2.trans (mul_le_mul_of_nonneg_left hS2 hK)
    have J3' := J3.trans (mul_le_mul_of_nonneg_left hS3 hK)
    have hS0 : 0 ≤ S := by rw [hS]; positivity
    have hKS : 0 ≤ K₁ * S := mul_nonneg hK hS0
    have hCgS : 0 ≤ (8 * Cg + 4 * M) * (K₁ * S) :=
      mul_nonneg (by positivity) hKS
    unfold Gpsi
    rw [q84a_Tsum_eq hsd hsym x y z]
    rw [abs_le] at P1' P2' P3' F1' F2' F3' F4' F5' F6' J1' J2' J3'
    rw [abs_le]
    constructor <;> linarith [P1'.1, P1'.2, P2'.1, P2'.2, P3'.1, P3'.2, F1'.1, F1'.2, F2'.1, F2'.2,
      F3'.1, F3'.2, F4'.1, F4'.2, F5'.1, F5'.2, F6'.1, F6'.2, J1'.1, J1'.2, J2'.1, J2'.2, J3'.1,
      J3'.2, hCgS]
  · -- pair bound
    intro x y hxy
    have hPs : PsiSize s K₁ ψ := hψ.size
    have hsym : IsSymmPair ψ := hψ.symm
    have hK : 0 ≤ K₁ := q84a_K_nonneg hPs hxy
    have hMK : 0 ≤ M * K₁ := mul_nonneg hM0 hK
    have hr := PairCorrAux.rTrunc_pos hxy
    have hr1 := PairCorrAux.rTrunc_le_one x y
    have hwxy := PairCorrAux.one_le_wEnv s x y
    have hwxy0 : 0 < wEnv s x y := by linarith
    have hrsymm : rTrunc y x = rTrunc x y := PairCorrAux.rTrunc_symm y x
    have hp : 0 ≤ rTrunc x y ^ (-s) := Real.rpow_nonneg hr.le _
    have hGb := q84a_Gb_bound hCg0 hs hCg hxy
    have hA := (q84a_grad_norm hPs hxy).trans
      (mul_le_mul_of_nonneg_left (q84a_one_add_le hr hr1 hs1) hK)
    have hB' := q84a_grad_norm hPs hxy.symm
    rw [hrsymm] at hB'
    have hB := hB'.trans (mul_le_mul_of_nonneg_left (q84a_one_add_le hr hr1 hs1) hK)
    have hΔ : ‖gradFst ψ x y - gradFst ψ y x‖ ≤
        K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) +
        K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) :=
      (norm_sub_le _ _).trans (add_le_add hA hB)
    have hinner := abs_real_inner_le_norm (periodicRieszGrad d s (x - y))
      (gradFst ψ x y - gradFst ψ y x)
    have hprod : ‖periodicRieszGrad d s (x - y)‖ * ‖gradFst ψ x y - gradFst ψ y x‖ ≤
        (2 * Cg * rTrunc x y ^ (-s - 1)) *
          (K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) +
            K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s)))) :=
      mul_le_mul hGb hΔ (norm_nonneg _) (by positivity)
    have hreq : (2 * Cg * rTrunc x y ^ (-s - 1)) *
        (K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s))) +
          K₁ * (2 * (rTrunc x y * rTrunc x y ^ (-s)))) =
        8 * Cg * K₁ * (rTrunc x y ^ (-s) * rTrunc x y ^ (-s)) := by
      rw [← q84a_rpow_mul hr s]; ring
    have hpw : rTrunc x y ^ (-s) ≤ wEnv s x y := by unfold wEnv; linarith
    have hsq : rTrunc x y ^ (-s) * rTrunc x y ^ (-s) ≤ wEnv s x y ^ 2 := by nlinarith
    have h8 : 0 ≤ 8 * Cg * K₁ := by positivity
    have hmain : |inner ℝ (periodicRieszGrad d s (x - y)) (gradFst ψ x y - gradFst ψ y x)| ≤
        8 * Cg * K₁ * wEnv s x y ^ 2 := by
      refine hinner.trans (hprod.trans ?_)
      rw [hreq]
      exact mul_le_mul_of_nonneg_left hsq h8
    -- the force terms
    have F1 := q84a_force_term hs1 hPs (hM x) hxy
    have F2 := q84a_force_term hs1 hPs (hM y) hxy.symm
    rw [PairCorrAux.wEnv_symm s y x] at F2
    have hw2 : wEnv s x y ≤ wEnv s x y ^ 2 := by nlinarith
    have F1' := F1.trans (mul_le_mul_of_nonneg_left hw2 hMK)
    have F2' := F2.trans (mul_le_mul_of_nonneg_left hw2 hMK)
    have hKW : 0 ≤ K₁ * wEnv s x y ^ 2 := mul_nonneg hK (by positivity)
    have hCW : 0 ≤ (8 * Cg + 4 * M) * (K₁ * wEnv s x y ^ 2) := mul_nonneg (by positivity) hKW
    have hC0W : 0 ≤ (8 * Cg * (1 + (d : ℝ)) * 2 ^ s + 2 * M + 1) * (K₁ * wEnv s x y ^ 2) :=
      mul_nonneg (by positivity) hKW
    unfold Bpsi Vpsi
    simp only [q84a_gradSnd_eq hsym x y]
    rw [abs_le] at hmain F1' F2'
    rw [abs_le]
    constructor <;> linarith [hmain.1, hmain.2, F1'.1, F1'.2, F2'.1, F2'.2, hCW, hC0W]

end HRS.Q84a
