import HRS.MS.Fp81S21WickApprox3

/-! Uniform finite-rank replacement for bounded kernel operators. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The reference-product profile controls the operator outputs for the same
rank family. The profile is chosen before the target law and operator. -/
theorem fp81s21_rankKernel_operator_profile
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (B C K : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (happrox : IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
      (fun θ => commutatorKernel p.d p.s θ.1) (fun θ k => (D θ k).kernel)) :
    ∃ τ : ℕ → ℝ, (∀ k, 0 ≤ τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
      ∀ k (θ : HRS.MS.R2S11.s11V p.d Λ) {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω)
        (W : Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
          (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 P),
        ‖W‖ ≤ K →
        ∀ (hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ k).kernel xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)))
          (hg : MemLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s θ.1 xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))),
        fp81s21_SqErr P
          (fun ω => W (hf.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω)
          (fun ω => W (hg.toLp (fun xy => commutatorKernel p.d p.s θ.1 xy.1 xy.2)) ω)
          (τ k) := by
  obtain ⟨κ, hκ, hκlim, herr⟩ :=
    fp81s21_rankKernel_reference_profile p R Λ hΛ D B C hB hC happrox
  refine ⟨fun k => K * κ k, fun k => mul_nonneg hK (hκ k), ?_, ?_⟩
  · simpa using tendsto_const_nhds.mul hκlim
  · intro k θ Ω inst P W hW hf hg
    let f : Euc p.d × Euc p.d → ℝ := fun xy => (D θ k).kernel xy.1 xy.2
    let g : Euc p.d × Euc p.d → ℝ := fun xy => commutatorKernel p.d p.s θ.1 xy.1 xy.2
    have hnorm : ‖hf.toLp f - hg.toLp g‖ ≤ κ k := by
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (herr θ k)
      change (eLpNorm (fun xy => f xy - g xy) 2 _).toReal ≤ κ k
      simpa [f, g, ENNReal.toReal_ofReal (hκ k)] using hb
    exact fp81s21_operator_sqerr _ P W (hf.toLp f) (hg.toLp g) K (κ k) hK (hκ k) hW hnorm

#print axioms fp81s21_rankKernel_operator_profile
end HRS.Fp81.S21
end
