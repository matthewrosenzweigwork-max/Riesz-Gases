import HRS.MS.R2S11Aux3

/-!
# S11.4 item (4): uniform finite-rank approximation of the commutator family over the `C_b²` velocity ball

`s11_velocity_uniform_approx`: for every `Λ` there are `B, C₂` and approximants `hj v j` of `h_v = commutatorKernel d s v`
(`v` in the ball `‖v‖_{C_b²} ≤ Λ`) such that the kernels are `IsBoundedPairKernel s B` and `IsR2UniformApprox s C₂ B μ_*` holds, for the
thermal reference `μ_* = ρ₀ dx`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_velocity_uniform_approx (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hq : 0 < q) (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) (Λ : ℝ) :
    ∃ (B C₂ : ℝ) (hj : s11V d Λ → ℕ → Euc d → Euc d → ℝ),
      (∀ v : s11V d Λ, IsBoundedPairKernel s B (commutatorKernel d s v.1)) ∧
      IsR2UniformApprox s C₂ B (HRS.Whole.withDensityReal ρ₀) (fun v : s11V d Λ => commutatorKernel d s v.1) hj := by
  classical
  obtain ⟨M, L, c, hR2, -⟩ := s11_thermal_round2 hd hs0 hs hq hβ hρ
  obtain ⟨C₂, hC₂⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  set B : ℝ := (s + 1) * max Λ 0 with hB
  have hbd : ∀ v : s11V d Λ, IsBoundedPairKernel s B (commutatorKernel d s v.1) := fun v => by
    have := S99.s99_comm_isBounded hs0 (Real.toNNReal (max Λ 0)) (s11_V_lip v)
    rwa [Real.coe_toNNReal _ (le_max_right _ _)] at this
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ₀) := HRS.Whole.U1.u1_isProb hR2.prob
  have hle : HRS.Whole.withDensityReal ρ₀ ≤ ENNReal.ofReal M • (volume : Measure (Euc d)) :=
    HRS.Whole.U1.u1_le_smul hR2.bdd
  -- approximants of each member
  have hex : ∀ w : s11V d Λ, ∃ a : ℕ → Euc d → Euc d → ℝ,
      IsRound2Approx s C₂ B (HRS.Whole.withDensityReal ρ₀) (commutatorKernel d s w.1) a := fun w =>
    hC₂ M L ρ₀ hR2 B (commutatorKernel d s w.1) (hbd w)
  choose A hA using hex
  obtain ⟨rs, hrs1, hrsd, hrs⟩ := HRS.Whole.U1.u1_rseq hd hs0 hs
  -- for each level j, a finite net and an index n_j
  have hlev : ∀ j : ℕ, ∃ (F : Finset (s11V d Λ)) (n : ℕ), ∀ v : s11V d Λ, ∃ w ∈ F,
      eLpNorm (fun p : Euc d × Euc d => A w n p.1 p.2 - commutatorKernel d s v.1 p.1 p.2) (ENNReal.ofReal (rs j))
        ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀)) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    have hε : 0 < 1 / (2 * ((j : ℝ) + 1)) := by positivity
    obtain ⟨F, hF⟩ := s11_net_Lr hs0 (hrs1 j) (hrsd j) Λ hle hε
    have hev : ∀ᶠ n in atTop, ∀ w ∈ F,
        eLpNorm (fun p : Euc d × Euc d => A w n p.1 p.2 - commutatorKernel d s w.1 p.1 p.2)
          (ENNReal.ofReal (rs j)) ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀)) ≤
          ENNReal.ofReal (1 / (2 * ((j : ℝ) + 1))) := by
      rw [Filter.eventually_all_finset]
      intro w _
      have := (hA w).converges (rs j) (hrs1 j) (hrsd j)
      exact (ENNReal.tendsto_nhds_zero.1 this) _ (ENNReal.ofReal_pos.2 hε)
    obtain ⟨n, hn⟩ := hev.exists
    refine ⟨F, n, fun v => ?_⟩
    obtain ⟨w, hwF, hw⟩ := hF v
    refine ⟨w, hwF, ?_⟩
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (rs j) := ENNReal.one_le_ofReal.2 (hrs1 j)
    have e : (fun p : Euc d × Euc d => A w n p.1 p.2 - commutatorKernel d s v.1 p.1 p.2) =
        (fun p : Euc d × Euc d => A w n p.1 p.2 - commutatorKernel d s w.1 p.1 p.2) +
          -(fun p : Euc d × Euc d => commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2) := by
      funext p; simp only [Pi.add_apply, Pi.neg_apply]; ring
    rw [e]
    refine (eLpNorm_add_le hp1).trans ?_
    rw [eLpNorm_neg]
    calc _ ≤ ENNReal.ofReal (1 / (2 * ((j : ℝ) + 1))) + ENNReal.ofReal (1 / (2 * ((j : ℝ) + 1))) :=
          add_le_add (hn w hwF) (by
            have h2 : ENNReal.ofReal (1 / (2 * ((j : ℝ) + 1))) = ENNReal.ofReal (1 / (2 * ((j : ℝ) + 1))) := rfl
            exact hw)
      _ = ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; field_simp; ring
  choose F n hFn using hlev
  choose near hnearF hnear using fun j v => hFn j v
  refine ⟨B, C₂, fun v j => A (near j v) (n j), hbd, ?_, ?_, ?_⟩
  · intro v j
    exact (hA (near j v)).finiteRank (n j)
  · intro v j x y hxy
    exact (hA (near j v)).envelope (n j) x y hxy
  · intro r hr hrs'
    obtain ⟨J, hJ⟩ := hrs r hr hrs'
    have hbound : ∀ j ≥ J, (⨆ v : s11V d Λ, eLpNorm (fun p : Euc d × Euc d =>
        A (near j v) (n j) p.1 p.2 - commutatorKernel d s v.1 p.1 p.2) (ENNReal.ofReal r)
        ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀))) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
      intro j hj
      refine iSup_le fun v => ?_
      calc _ ≤ eLpNorm (fun p : Euc d × Euc d => A (near j v) (n j) p.1 p.2 - commutatorKernel d s v.1 p.1 p.2)
              (ENNReal.ofReal (rs j)) ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀)) :=
            eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hJ j hj))
        _ ≤ _ := hnear j v
    have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun j => zero_le) ?_
    filter_upwards [eventually_ge_atTop J] with j hj
    exact hbound j hj

end HRS.MS.R2S11
