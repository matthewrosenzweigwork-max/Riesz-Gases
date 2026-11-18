import HRS.MS.R2ChaosAux24

/-!
# HRS.MS.R2ChaosAux25 -- `L²` convergence of envelope-bounded kernels upgrades to all admissible `L^r`

Packet S94 (R1, part 1), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_lp_upgrade` : `‖D_m‖₂ → 0` and `|D_m| ≤ G ∈ L^r` imply `‖D_m‖_r → 0` (Vitali).
* `s94_env_memLp_r` : envelope-bounded kernels lie in `L^r(μ⊗μ)` for every `1 ≤ r`, `r s < d` (through S9.1).
* `s94_kernel_upgrade` : `L²`-convergent sequences of `IsBoundedPairKernel s B` kernels converge in every admissible `L^r`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_lp_upgrade {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {D : ℕ → α → ℝ} {G : α → ℝ} {r : ℝ≥0∞} (hr1 : 1 ≤ r) (hrt : r ≠ ∞)
    (hD : ∀ m, AEStronglyMeasurable (D m) ν) (hG : MemLp G r ν)
    (hDG : ∀ m, ∀ᵐ x ∂ν, ‖D m x‖ ≤ ‖G x‖)
    (h2 : Tendsto (fun m => eLpNorm (D m) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (D m) r ν) atTop (𝓝 0) := by
  have hui : UnifIntegrable D r ν :=
    (unifIntegrable_const (ι := ℕ) hr1 hrt hG).ae_mono hD fun m => (hDG m).mono fun x hx =>
      enorm_le_iff_norm_le.mpr hx
  have hm : TendstoInMeasure ν D atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) (by simpa using h2)
  have := tendsto_Lp_finite_of_tendstoInMeasure hr1 hrt hD MemLp.zero hui hm
  simpa using this

section Env3

variable {s : ℝ}

theorem s94_Gker (B : ℝ) (hB : 0 ≤ B) :
    IsBoundedPairKernel s B (fun x y : Euc d => B * (1 + rieszWeight s (x - y))) where
  measurable := measurable_const.mul (measurable_const.add
    ((HRS.MS.Wr.wr3_measurable_rieszWeight (d := d) s).comp (measurable_fst.sub measurable_snd)))
  symm := fun x y => by
    unfold rieszWeight
    rw [norm_sub_rev]
  bound := fun x y _ => by
    have := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (x - y)
    rw [abs_of_nonneg (by positivity)]

theorem s94_ae_offdiag (hd : 2 ≤ d) {M L : ℝ} {ρ : Euc d → ℝ} (hρ : IsRound2Density d s M L ρ) :
    ∀ᵐ q ∂((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)), q.1 ≠ q.2 := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hle := HRS.Whole.U1.u1_le_smul hρ.bdd
  have hμ'μ : Whole.withDensityReal ρ ≪ (volume : Measure (Euc d)) :=
    Measure.absolutelyContinuous_of_le_smul hle
  have hPν : (Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ) ≪ (volume : Measure (Euc d)).prod volume :=
    Measure.AbsolutelyContinuous.prod hμ'μ hμ'μ
  exact hPν.ae_le (HRS.Whole.U1.u1_ae_offdiag (volume : Measure (Euc d)) (by rw [hfr]; omega))

/-- An envelope-bounded kernel lies in `L^r(μ ⊗ μ)` for every admissible `r` (through S9.1). -/
theorem s94_env_memLp_r (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {r : ℝ} (hr1 : 1 ≤ r) (hrs : r * s < (d : ℝ)) :
    MemLp (fun q : Euc d × Euc d => h q.1 q.2) (ENNReal.ofReal r)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨hj, hA⟩ := hC M L ρ hρ B h hh
  have hconv := hA.converges r hr1 hrs
  obtain ⟨j, hj'⟩ := (hconv.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  obtain ⟨m, c, u, ⟨_, hsm, hcp⟩, hjeq⟩ := hA.finiteRank j
  have hut : ∀ a, IsR2Test (u a) := fun a => ⟨hsm a, hcp a⟩
  have hfr : MemLp (fun q : Euc d × Euc d => hj j q.1 q.2) (ENNReal.ofReal r)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
    rw [hjeq]
    obtain ⟨C0, hC0⟩ := s94_finiteRank_bounded (c := c) hut
    exact MemLp.of_bound (s94_finiteRank_measurable hut).aestronglyMeasurable C0
      (ae_of_all _ fun q => by simpa using hC0 q.1 q.2)
  have hdiff : MemLp (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2) (ENNReal.ofReal r)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
    exact hj'
  have e : (fun q : Euc d × Euc d => h q.1 q.2) =
      fun q => hj j q.1 q.2 - (hj j q.1 q.2 - h q.1 q.2) := funext fun q => by ring
  rw [e]
  exact hfr.sub hdiff

/-- `L²` convergence of `IsBoundedPairKernel s B` kernels upgrades to every admissible `L^r`. -/
theorem s94_kernel_upgrade (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {g : ℕ → Euc d → Euc d → ℝ} (hg : ∀ m, IsBoundedPairKernel s B (g m))
    (h2 : Tendsto (fun m => eLpNorm (fun q : Euc d × Euc d => g m q.1 q.2 - h q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0))
    {r : ℝ} (hr1 : 1 ≤ r) (hrs : r * s < (d : ℝ)) :
    Tendsto (fun m => eLpNorm (fun q : Euc d × Euc d => g m q.1 q.2 - h q.1 q.2) (ENNReal.ofReal r)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hB := s94_B_nonneg hd hh
  have hG := s94_env_memLp_r hd hs0 hs hρ (s94_Gker (s := s) B hB) hr1 hrs
  refine s94_lp_upgrade (G := fun q : Euc d × Euc d => 2 * (B * (1 + rieszWeight s (q.1 - q.2))))
    (ENNReal.one_le_ofReal.mpr hr1) ENNReal.ofReal_ne_top
    (fun m => ((hg m).measurable.aestronglyMeasurable.sub hh.measurable.aestronglyMeasurable))
    (hG.const_mul 2) (fun m => ?_) (by simpa using h2)
  filter_upwards [s94_ae_offdiag hd hρ] with q hq
  have h1 := (hg m).bound q.1 q.2 hq
  have h2' := hh.bound q.1 q.2 hq
  have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (q.1 - q.2)
  have hpos : 0 ≤ B * (1 + rieszWeight s (q.1 - q.2)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * (B * (1 + rieszWeight s (q.1 - q.2))))]
  calc |g m q.1 q.2 - h q.1 q.2| ≤ |g m q.1 q.2| + |h q.1 q.2| := abs_sub _ _
    _ ≤ _ := by linarith

end Env3

end HRS.MS.R2Chaos
