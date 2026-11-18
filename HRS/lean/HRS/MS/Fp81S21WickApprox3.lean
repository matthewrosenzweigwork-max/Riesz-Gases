import HRS.MS.Fp81S21WickApprox2
import HRS.MS.Fp81S21RankKernel2

/-! Uniform reference-product kernel approximation for the common rank data. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The same rank family used for particles has a finite real L² error profile
on the thermal reference product measure, uniformly over the velocity ball. -/
theorem fp81s21_rankKernel_reference_profile
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (happrox : IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
      (fun θ => commutatorKernel p.d p.s θ.1) (fun θ k => (D θ k).kernel)) :
    ∃ κ : ℕ → ℝ, (∀ k, 0 ≤ κ k) ∧ Tendsto κ atTop (𝓝 0) ∧
      ∀ θ k, eLpNorm (fun xy : Euc p.d × Euc p.d =>
        (D θ k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ.1 xy.1 xy.2)
        2 ((HRS.Whole.withDensityReal R.ρβ).prod
          (HRS.Whole.withDensityReal R.ρβ)) ≤ ENNReal.ofReal (κ k) := by
  obtain ⟨Bvel, _, _, hvel, _⟩ :=
    HRS.MS.R2S11.s11_velocity_uniform_approx p.hd p.hs0 p.hs p.ha p.hβ R.thermal Λ
  have hBvel : 0 ≤ Bvel := by
    let θ0 : HRS.MS.R2S11.s11V p.d Λ :=
      ⟨fun _ => 0, ⟨contDiff_const, by simp [cbNormVecE]⟩⟩
    have hdp : 0 < p.d := lt_of_lt_of_le (by decide : 0 < 2) p.hd
    letI : NeZero p.d := ⟨Nat.ne_of_gt hdp⟩
    letI : Nontrivial (Euc p.d) := inferInstance
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Euc p.d)
    have hz : commutatorKernel p.d p.s θ0.1 x y = 0 := by simp [θ0, commutatorKernel]
    have hbnd := (hvel θ0).bound x y hxy
    rw [hz, abs_zero] at hbnd
    have hw : 0 < 1 + rieszWeight p.s (x - y) := by
      have := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
      linarith
    nlinarith
  obtain ⟨Mref, Lref, _, hR2ref, _⟩ :=
    HRS.MS.R2S11.s11_thermal_round2 p.hd p.hs0 p.hs p.ha p.hβ R.thermal
  let Bdiff : ℝ := C * B + Bvel
  have hBdiff : 0 ≤ Bdiff := by dsimp [Bdiff]; positivity
  obtain ⟨Kref, hKref, hKbound⟩ :=
    HRS.MS.R2Chaos.s94_env_L2_bound p.hd p.hs0 p.hs hR2ref Bdiff hBdiff
  let err : ℕ → ℝ≥0∞ := fun k =>
    ⨆ θ : HRS.MS.R2S11.s11V p.d Λ,
      eLpNorm (fun xy : Euc p.d × Euc p.d =>
        (D θ k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ.1 xy.1 xy.2)
        2 ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))
  have hbound : ∀ k, err k ≤ ENNReal.ofReal Kref := by
    intro k
    refine iSup_le fun θ => ?_
    have happ : IsBoundedPairKernel p.s (C * B) (D θ k).kernel := by
      refine ⟨?_, ?_, ?_⟩
      · exact HRS.MS.R2Mt.s92_finiteRank_meas (D θ k).valid
      · exact HRS.MS.R2Mt.s92_finiteRank_symm (D θ k).valid
      · exact happrox.envelope θ k
    have hdiff : IsBoundedPairKernel p.s Bdiff
        (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) := by
      refine ⟨happ.measurable.sub (hvel θ).measurable, ?_, ?_⟩
      · intro x y
        rw [happ.symm x y, (hvel θ).symm x y]
      · intro x y hxy
        calc
          |(D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y| ≤
              |(D θ k).kernel x y| + |commutatorKernel p.d p.s θ.1 x y| := abs_sub _ _
          _ ≤ (C * B) * (1 + rieszWeight p.s (x - y)) +
                Bvel * (1 + rieszWeight p.s (x - y)) :=
            add_le_add (happ.bound x y hxy) ((hvel θ).bound x y hxy)
          _ = Bdiff * (1 + rieszWeight p.s (x - y)) := by dsimp [Bdiff]; ring
    exact hKbound hdiff
  have hfinite : ∀ k, err k ≠ ⊤ := fun k =>
    ne_of_lt (lt_of_le_of_lt (hbound k) ENNReal.ofReal_lt_top)
  have hconv : Tendsto err atTop (𝓝 0) := by
    simpa [err] using happrox.converges 2 (by norm_num) (by linarith [p.hs])
  let κ : ℕ → ℝ := fun k => (err k).toReal
  have hκ : Tendsto κ atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  refine ⟨κ, fun k => ENNReal.toReal_nonneg, hκ, ?_⟩
  intro θ k
  have hle := le_iSup (fun θ' : HRS.MS.R2S11.s11V p.d Λ =>
    eLpNorm (fun xy : Euc p.d × Euc p.d =>
      (D θ' k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ'.1 xy.1 xy.2)
      2 ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))) θ
  simpa [κ, ENNReal.ofReal_toReal (hfinite k)] using hle

#print axioms fp81s21_rankKernel_reference_profile
end HRS.Fp81.S21
end
