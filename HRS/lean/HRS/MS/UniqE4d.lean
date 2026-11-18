import HRS.MS.UniqE4c

/-!
# E4 of `UniqPlan.md`, part 4: the exact identity `I - J = - ∫ [η_ε, ρ'] v_j · H'`

With `H' = g * ∂_iψ'`, `H_φ = g * ∂_i(η_ε * ψ') = η_ε * H'`, `z = η_ε * u`, `v` the weak gradient of `u`:
`∫ u ∂_j(ρ' H_φ) - ∫ z ∂_j(ρ' H') = - ∫ comm_ε(ρ', v_j) · H'`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

theorem e4_abs_D1_le {ρ : Euc d → ℝ} {c : ℝ} (j : Fin d) {y : Euc d} (h : ‖fderiv ℝ ρ y‖ ≤ c) :
    |D1 j ρ y| ≤ c := (e3_abs_apply_le _ j).trans h

/-- A bound for `|H|` and `|D1 j H|` (`H = g * ∂_iψ`, `ψ ∈ C²_c`). -/
theorem e4_kcd_bounds {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ y, |kernelConvDeriv d s i ψ y| ≤ M) ∧
      (∀ y, |D1 j (kernelConvDeriv d s i ψ) y| ≤ M) := by
  obtain ⟨M1, hM1⟩ := e4_kcd_bdd hs0 hsd i (hψ.of_le (by norm_num)) hψc
  obtain ⟨M2, hM2⟩ := e4_kcd_bdd hs0 hsd j (D1_contDiff hψ i) (D1_supp hψc i)
  have h0 : 0 ≤ max M1 M2 := (abs_nonneg _).trans ((hM1 0).trans (le_max_left _ _))
  refine ⟨max M1 M2, h0, fun y => (hM1 y).trans (le_max_left _ _), fun y => ?_⟩
  rw [e4_D1_kcd hs0 hsd i j hψ hψc]
  exact (hM2 y).trans (le_max_right _ _)

/-- Product bounds: `|ρ' H| ≤ A M ⟨y⟩^{-κ}`, `|∂_j(ρ' H)| ≤ 2 A M ⟨y⟩^{-κ}`. -/
theorem e4_prod_bounds {κ A M : ℝ} {ρ H : Euc d → ℝ} (j : Fin d) (hρ : ContDiff ℝ 1 ρ)
    (hH : ContDiff ℝ 1 H) (hρ0 : ∀ y, |ρ y| ≤ A * (1 + ‖y‖) ^ (-κ))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * (1 + ‖y‖) ^ (-κ)) (hH0 : ∀ y, |H y| ≤ M)
    (hH1 : ∀ y, |D1 j H y| ≤ M) (hM : 0 ≤ M) :
    (∀ y, |ρ y * H y| ≤ (2 * (A * M)) * (1 + ‖y‖) ^ (-κ)) ∧
    (∀ y, |D1 j (fun y => ρ y * H y) y| ≤ (2 * (A * M)) * (1 + ‖y‖) ^ (-κ)) := by
  have hA : 0 ≤ A := by
    have := hρ0 0
    simp at this
    exact (abs_nonneg _).trans this
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [abs_mul]
    have hp : 0 ≤ (1 + ‖y‖) ^ (-κ) := by positivity
    have hAM : 0 ≤ A * M * (1 + ‖y‖) ^ (-κ) := by positivity
    calc |ρ y| * |H y| ≤ (A * (1 + ‖y‖) ^ (-κ)) * M :=
          mul_le_mul (hρ0 y) (hH0 y) (abs_nonneg _) (by positivity)
      _ = A * M * (1 + ‖y‖) ^ (-κ) := by ring
      _ ≤ _ := by nlinarith
  · rw [e3_D1_mul (hρ.differentiable (by simp)) (hH.differentiable (by simp))]
    have e1 : |ρ y * D1 j H y| ≤ (A * (1 + ‖y‖) ^ (-κ)) * M := by
      rw [abs_mul]
      exact mul_le_mul (hρ0 y) (hH1 y) (abs_nonneg _) (by positivity)
    have e2 : |H y * D1 j ρ y| ≤ M * (A * (1 + ‖y‖) ^ (-κ)) := by
      rw [abs_mul]
      exact mul_le_mul (hH0 y) (e4_abs_D1_le j (hρ1 y)) (abs_nonneg _) hM
    calc |ρ y * D1 j H y + H y * D1 j ρ y| ≤ |ρ y * D1 j H y| + |H y * D1 j ρ y| := abs_add_le _ _
      _ ≤ (A * (1 + ‖y‖) ^ (-κ)) * M + M * (A * (1 + ‖y‖) ^ (-κ)) := add_le_add e1 e2
      _ = _ := by ring

theorem e4_identity {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (i j : Fin d)
    {B : ℝ} (hB : 0 ≤ B) {u : Euc d → ℝ} (hu : LocMass B u) {v : Euc d → Euc d}
    (hv : IsWeakGrad u v) (hvj : LocMass B (fun x => v x j)) {A : ℝ} {ρ : Euc d → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hρ0 : ∀ y, |ρ y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, u x * D1 j (fun y => ρ y * kernelConvDeriv d s i (moll d ε ψ) y) x) -
      (∫ x, moll d ε u x * D1 j (fun y => ρ y * kernelConvDeriv d s i ψ y) x) =
    - ∫ y, HRS.MS.UniqM3.comm d ε ρ (fun x => v x j) y * kernelConvDeriv d s i ψ y := by
  set κ : ℝ := (d : ℝ) + 3 with hκdef
  have hκ : (d : ℝ) < κ := by rw [hκdef]; linarith
  have hA : 0 ≤ A := by
    have := hρ0 0
    simp at this
    exact (abs_nonneg _).trans this
  set H : Euc d → ℝ := kernelConvDeriv d s i ψ with hH
  set φ : Euc d → ℝ := moll d ε ψ with hφ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hφs : ContDiff ℝ ∞ φ := moll_contDiff hε hψ.continuous.locallyIntegrable
  have hφc : HasCompactSupport φ := e3_moll_hasCompactSupport hε hψc
  have hφ2 : ContDiff ℝ 2 φ := by exact_mod_cast contDiff_infty.1 hφs 2
  have hHφ : kernelConvDeriv d s i φ = moll d ε H := e4_kcd_moll hs0 hsd hε i hψ hψc
  have hHs : ContDiff ℝ 1 H := e4_kcd_contDiff hs0 hsd i hψ hψc
  have hHφs : ContDiff ℝ 1 (kernelConvDeriv d s i φ) := e4_kcd_contDiff hs0 hsd i hφ2 hφc
  obtain ⟨MH, hMH0, hMH, hMH1⟩ := e4_kcd_bounds hs0 hsd i j hψ hψc
  obtain ⟨MP, hMP0, hMP, hMP1⟩ := e4_kcd_bounds hs0 hsd i j hφ2 hφc
  have hLoc : LocallyIntegrable u volume := hu.locallyIntegrable
  have hLocv : LocallyIntegrable (fun x => v x j) volume := hvj.locallyIntegrable
  obtain ⟨C, hC0, hC⟩ := n0_cell_decay_mul (d := d) hκ
  -- Step A: the weak gradient identity for `Θ = ρ H_φ`
  obtain ⟨hΘ0, hΘ1⟩ := e4_prod_bounds j hρ hHφs hρ0 hρ1 hMP hMP1 hMP0
  have hΘ : ContDiff ℝ 1 (fun y => ρ y * kernelConvDeriv d s i φ y) := hρ.mul hHφs
  have stepA := e4_weak_decay hκ hu hv j hvj hΘ hΘ0 hΘ1
  -- Step B: Fubini
  have hfi : Integrable (fun y => ρ y * v y j) volume := by
    have := ((hC 0 A B (fun x => v x j) ρ hA hvj (by simpa using hρ0)).2
      hρ.continuous.aestronglyMeasurable).1
    exact this.congr (Eventually.of_forall fun y => by simp [mul_comm])
  obtain ⟨hswapI, hswap⟩ := e4_swap_moll hε hfi hHs.continuous.aestronglyMeasurable hMH
  have stepB : ∫ x, v x j * (ρ x * kernelConvDeriv d s i φ x) =
      ∫ x, moll d ε (fun y => ρ y * v y j) x * H x := by
    rw [← hswap, hHφ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  -- Step C: split the commutator
  obtain ⟨Cv, hCv0, hCv⟩ := moll_iteratedFDeriv_le (d := d) hε 0
  have hmv : Continuous (moll d ε (fun x => v x j)) := e3_moll_continuous hε hLocv
  have hmvb : ∀ x, |moll d ε (fun x => v x j) x| ≤ Cv * B := fun x => by
    have := hCv B (fun x => v x j) hB hvj x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  obtain ⟨hGb0, hGb1⟩ := e4_prod_bounds j hρ hHs hρ0 hρ1 hMH hMH1 hMH0
  have hI2 : Integrable (fun y => ρ y * moll d ε (fun x => v x j) y * H y) volume := by
    refine e4_decay_integrable (M := (2 * (A * MH)) * (Cv * B)) hκ
      (((hρ.continuous.mul hmv).mul hHs.continuous).aestronglyMeasurable) fun y => ?_
    rw [show ρ y * moll d ε (fun x => v x j) y * H y =
      moll d ε (fun x => v x j) y * (ρ y * H y) by ring, abs_mul]
    calc |moll d ε (fun x => v x j) y| * |ρ y * H y| ≤ (Cv * B) * ((2 * (A * MH)) * (1 + ‖y‖) ^ (-κ)) :=
          mul_le_mul (hmvb y) (hGb0 y) (abs_nonneg _) (mul_nonneg hCv0 hB)
      _ = _ := by ring
  have hcomm : ∀ y, HRS.MS.UniqM3.comm d ε ρ (fun x => v x j) y * H y =
      moll d ε (fun y => ρ y * v y j) y * H y - ρ y * moll d ε (fun x => v x j) y * H y := by
    intro y; unfold HRS.MS.UniqM3.comm; ring
  have hIc : Integrable (fun y => HRS.MS.UniqM3.comm d ε ρ (fun x => v x j) y * H y) volume := by
    simp_rw [hcomm]; exact hswapI.sub hI2
  have stepC : ∫ x, moll d ε (fun y => ρ y * v y j) x * H x =
      (∫ y, HRS.MS.UniqM3.comm d ε ρ (fun x => v x j) y * H y) +
        ∫ y, ρ y * moll d ε (fun x => v x j) y * H y := by
    rw [← integral_add hIc hI2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hcomm]; ring
  -- Step D: integration by parts for `z = η_ε * u`
  obtain ⟨C0, hC00, hC0'⟩ := moll_iteratedFDeriv_le (d := d) hε 0
  obtain ⟨C1, hC10, hC1'⟩ := moll_iteratedFDeriv_le (d := d) hε 1
  have hz : ContDiff ℝ 1 (moll d ε u) := (moll_contDiff hε hLoc).of_le (by exact_mod_cast le_top)
  have hzb0 : ∀ x, |moll d ε u x| ≤ C0 * B := fun x => by
    have := hC0' B u hB hu x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hDz : ∀ x, D1 j (moll d ε u) x = moll d ε (fun y => v y j) x := fun x =>
    fderiv_moll_apply hε hLoc hv j x
  have hzb1 : ∀ x, |D1 j (moll d ε u) x| ≤ C1 * B := fun x => by
    have h1 := hC1' B u hB hu x
    rw [norm_iteratedFDeriv_one] at h1
    exact (e3_abs_apply_le _ j).trans h1
  have stepD := e4_ibp_decay hκ (Mf := max (C0 * B) (C1 * B)) hz (hρ.mul hHs) j
    (fun x => (hzb0 x).trans (le_max_left _ _)) (fun x => (hzb1 x).trans (le_max_right _ _))
    hGb0 hGb1
  -- assembly
  have hJ : ∫ x, moll d ε u x * D1 j (fun y => ρ y * kernelConvDeriv d s i ψ y) x =
      - ∫ y, ρ y * moll d ε (fun x => v x j) y * H y := by
    rw [show (fun y => ρ y * kernelConvDeriv d s i ψ y) = fun y => ρ y * H y from rfl, stepD]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hDz]; ring
  have hI : ∫ x, u x * D1 j (fun y => ρ y * kernelConvDeriv d s i (moll d ε ψ) y) x =
      -((∫ y, HRS.MS.UniqM3.comm d ε ρ (fun x => v x j) y * H y) +
        ∫ y, ρ y * moll d ε (fun x => v x j) y * H y) := by
    rw [stepA, stepB, stepC]
  rw [hI, hJ]
  ring

end HRS.MS.UniqE4
