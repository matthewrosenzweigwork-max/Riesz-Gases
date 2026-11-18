import HRS.MH.ScreenedDefs

/-! Packet F2 of `B:lem:screened` (S.B.4): proof of the statement of `flow_origin` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- **F2** (size S).  `‖Ψ_τ(0)‖ ≤ e^{Cb τ} - 1`: `norm_le_gronwallBound_of_norm_deriv_right_le` applied to
`f σ = Ψ σ 0` with `δ = 0`, `K = ε = Cb`, `‖f'‖ = ‖b σ (Ψ σ 0)‖ ≤ Cb (1 + ‖f‖)`. -/
theorem flow_origin_proof (m : ℕ) (Cb T : ℝ) (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : IsAdvectingDrift m Cb T b) (hΨ : IsNegDriftFlow T b Ψ) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) :
    ‖Ψ τ 0‖ ≤ Real.exp (Cb * τ) - 1 := by
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτ.2
  have hcont : ContinuousOn (fun σ => Ψ σ 0) (Icc (0 : ℝ) τ) := fun σ hσ =>
    ((hΨ.ode 0 σ (hsub hσ)).continuousWithinAt).mono hsub
  have hderiv : ∀ x ∈ Ico (0 : ℝ) τ, HasDerivWithinAt (fun σ => Ψ σ 0) (-(b x (Ψ x 0))) (Ici x) x := by
    intro x hx
    have hxT : x < T := lt_of_lt_of_le hx.2 hτ.2
    have hnhds : Icc (0 : ℝ) T ∈ 𝓝[Ici x] x :=
      Filter.mem_of_superset (Icc_mem_nhdsGE hxT) (Icc_subset_Icc hx.1 le_rfl)
    exact (hΨ.ode 0 x ⟨hx.1, hxT.le⟩).mono_of_mem_nhdsWithin hnhds
  have hbound : ∀ x ∈ Ico (0 : ℝ) τ, ‖-(b x (Ψ x 0))‖ ≤ Cb * ‖Ψ x 0‖ + Cb := by
    intro x hx
    have hxT : x ∈ Icc (0 : ℝ) T := ⟨hx.1, (lt_of_lt_of_le hx.2 hτ.2).le⟩
    have h1 := hb.growth x hxT (Ψ x 0)
    have h2 : Cb * (1 + ‖Ψ x 0‖) = Cb * ‖Ψ x 0‖ + Cb := by ring
    rw [norm_neg]
    linarith
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun σ => Ψ σ 0)
    (f' := fun x => -(b x (Ψ x 0))) (δ := 0) (K := Cb) (ε := Cb) (a := 0) (b := τ)
    hcont hderiv (by simp [hΨ.init]) hbound
  have key := hgr τ ⟨hτ.1, le_rfl⟩
  refine key.trans (le_of_eq ?_)
  rw [sub_zero]
  by_cases hK : Cb = 0
  · subst hK
    simp [gronwallBound]
  · simp [gronwallBound, hK]

end HRS.MH.Screened
