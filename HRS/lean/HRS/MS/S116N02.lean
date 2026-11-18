import HRS.MS.S113EndAux31

/-!
# S11.6 packet N02 (`R26-T8B.N02`): uniform finite-`N` mean of the logarithmic modulated energy

Prefix `s116_`, namespace `HRS.MS.S116`.  For a probability density with Gaussian upper envelope `(C_g, c_g)`: `N F_N` is `μ^{⊗N}`-integrable and its mean is
`-(1/2) ∬ g(x-y) dμ dμ`, which is bounded by `B` depending only on `d, C_g, c_g` (not on `ρ`, `N ≥ 2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_energy_mean {d : ℕ} (hd : 1 ≤ d) (Cg cg : ℝ) (hcg : 0 < cg) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : Euc d → ℝ,
      HRS.Whole.IsProbDensity ρ → HasR2GaussianUpper Cg cg ρ →
      ∀ N : ℕ, 2 ≤ N →
        Integrable (fun X : EucConfig d N => (N : ℝ) *
          rieszModulatedEnergy d 0 X (HRS.Whole.withDensityReal ρ))
          (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) ∧
        |∫ X : EucConfig d N, (N : ℝ) * rieszModulatedEnergy d 0 X
          (HRS.Whole.withDensityReal ρ) ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ)| ≤ B := by
  obtain ⟨ε₁, Crow, hε₁, hWall⟩ := HRS.Whole.r2_log_row_whole hd Cg cg hcg
  set C₁ : ℝ := max Cg 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  set G : ℝ := 2 * (2 * HRS.MS.S113BD.s113x_Kq d C₁ cg) +
    2 * (2 * ∫ x : Euc d, q33b_Phi C₁ cg x) with hG
  refine ⟨|G|, abs_nonneg _, fun ρ hρ hGa N hN => ?_⟩
  have hρ0 : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ Cg * Real.exp (-cg * ‖x‖ ^ 2) := fun x => ⟨hρ.nonneg x, hGa.2 x⟩
  have hρ' : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-cg * ‖x‖ ^ 2) := fun x =>
    ⟨(hρ0 x).1, (hρ0 x).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
  obtain ⟨hprob, hrows, -, -, hG2⟩ :=
    HRS.MS.S113BD.s113x_X4_facts hd hC₁ hcg hρ.measurable hρ' hρ.integral_one
  obtain ⟨hI, -, -⟩ := hWall ρ hρ.measurable hρ0 hρ.integral_one
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set g := rieszKernel d 0 with hg
  have hok : HRS.MS.Wr.Wr8Ok μ (fun x y => g (x - y)) :=
    ⟨HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) 0, hrows, hI⟩
  have hFint := HRS.MS.Wr.wr8_integrable_modEnergyE (N := N) hok
  have hFmean := HRS.MS.Wr.wr8_integral_mul_modEnergyE (N := N) hok (by omega)
  have hpair : ∫ p : Euc d × Euc d, g (p.1 - p.2) ∂(μ.prod μ) = HRS.Whole.energyPairing g μ μ := by
    unfold HRS.Whole.energyPairing
    rw [integral_prod _ hI]
  refine ⟨hFint.const_mul (N : ℝ), ?_⟩
  have hm : ∫ X : EucConfig d N, (N : ℝ) * rieszModulatedEnergy d 0 X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / 2) * HRS.Whole.energyPairing g μ μ := by
    rw [← hpair, ← hFmean]
    rfl
  rw [hm, abs_mul]
  have h2 : |HRS.Whole.energyPairing g μ μ| ≤ G := hG2
  have h3 : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
  rw [h3]
  have := le_abs_self G
  linarith [abs_nonneg (HRS.Whole.energyPairing g μ μ)]

end HRS.MS.S116

end
