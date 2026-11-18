import HRS.MS.R2S11Aux1

/-!
# S11.4 item (4), part 2: `L^r(μ×μ)`-nets of the commutator family

For a probability measure `μ'` with bounded density and `r ≥ 1`, `r s < d`: for every `ε > 0` the commutator family
`{h_v : v ∈ V Λ}` has a finite `ε`-net in `L^r(μ' × μ')` consisting of members of the family (`s11_net_Lr`).

Proof: `|h_v - h_w| ≤ (s+1) η (1 + W_s)` on `K_R × K_R` when `sup_{K_R}‖Dv - Dw‖ ≤ η` (part 1), `≤ 2 (s+1) Λ' (1 + W_s)` globally;
the `L^r` norm of `1 + W_s` is finite (`u1_lintegral_prod_Vs`) and its tail outside `K_R × K_R` tends to `0`.
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

/-- The profile `1 + W_s(x - y)` on pairs. -/
def s11Vs (s : ℝ) (p : Euc d × Euc d) : ℝ := 1 + rieszWeight s (p.1 - p.2)

theorem s11Vs_eq (s : ℝ) (p : Euc d × Euc d) : s11Vs s p = HRS.Whole.U1.u1Vs s ‖p.1 - p.2‖ := rfl

theorem s11Vs_ge_one (s : ℝ) (p : Euc d × Euc d) : 1 ≤ s11Vs s p := by
  have := s11_rieszWeight_nonneg (d := d) s (p.1 - p.2)
  unfold s11Vs; linarith

theorem s11Vs_meas (s : ℝ) : Measurable (s11Vs (d := d) s) :=
  (HRS.Whole.U1.u1Vs_measurable (E := Euc d) s).comp (measurable_fst.sub measurable_snd)

/-- The `L^r` seminorm as the `1/r`-th power of the lintegral. -/
theorem s11_eLpNorm_ofReal {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ} {r : ℝ} (hr : 1 ≤ r)
    (hg : AEStronglyMeasurable g ν) :
    eLpNorm g (ENNReal.ofReal r) ν = (∫⁻ x, ‖g x‖ₑ ^ r ∂ν) ^ (1 / r) := by
  have hr0 : 0 < r := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hr0.le]

theorem s11_Vs_lintegral {s r : ℝ} (hs0 : 0 ≤ s) (hr : 1 ≤ r) (hrs : r * s < d) {μ' : Measure (Euc d)}
    [IsProbabilityMeasure μ'] {M : ℝ} (hle : μ' ≤ ENNReal.ofReal M • (volume : Measure (Euc d))) :
    ∫⁻ p, ‖s11Vs s p‖ₑ ^ r ∂(μ'.prod μ') ≠ ⊤ := by
  have hr0 : 0 < r := by linarith
  have h := HRS.Whole.U1.u1_lintegral_prod_Vs (volume : Measure (Euc d)) hs0 hr0
    (by rw [finrank_euclideanSpace_fin]; exact hrs) μ' hle
  convert h using 2
  funext p
  rw [Real.enorm_of_nonneg (by linarith [s11Vs_ge_one s p]), ENNReal.ofReal_rpow_of_nonneg
    (by linarith [s11Vs_ge_one s p]) hr0.le]
  rfl

theorem s11_Vs_eLpNorm_ne_top {s r : ℝ} (hs0 : 0 ≤ s) (hr : 1 ≤ r) (hrs : r * s < d) {μ' : Measure (Euc d)}
    [IsProbabilityMeasure μ'] {M : ℝ} (hle : μ' ≤ ENNReal.ofReal M • (volume : Measure (Euc d))) :
    eLpNorm (s11Vs (d := d) s) (ENNReal.ofReal r) (μ'.prod μ') ≠ ⊤ := by
  rw [s11_eLpNorm_ofReal hr (s11Vs_meas s).aestronglyMeasurable]
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (s11_Vs_lintegral hs0 hr hrs hle)

/-- The box `closedBall 0 n × closedBall 0 n`. -/
def s11Box (d : ℕ) (n : ℕ) : Set (Euc d × Euc d) := closedBall (0 : Euc d) n ×ˢ closedBall (0 : Euc d) n

theorem s11Box_meas (n : ℕ) : MeasurableSet (s11Box d n) :=
  measurableSet_closedBall.prod measurableSet_closedBall

/-- The tail of the profile outside the boxes tends to `0` in `L^r`. -/
theorem s11_tail_zero {s r : ℝ} (hs0 : 0 ≤ s) (hr : 1 ≤ r) (hrs : r * s < d) {μ' : Measure (Euc d)}
    [IsProbabilityMeasure μ'] {M : ℝ} (hle : μ' ≤ ENNReal.ofReal M • (volume : Measure (Euc d))) :
    Tendsto (fun n : ℕ => eLpNorm ((s11Box d n)ᶜ.indicator (s11Vs (d := d) s)) (ENNReal.ofReal r) (μ'.prod μ'))
      atTop (𝓝 0) := by
  have hr0 : 0 < r := by linarith
  have hfin := s11_Vs_lintegral hs0 hr hrs hle
  have hmeas : ∀ n : ℕ, Measurable fun p => ‖(s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p‖ₑ ^ r := fun n =>
    ((((s11Vs_meas s).indicator (s11Box_meas n).compl).enorm)).pow_const r
  have hlim : Tendsto (fun n : ℕ => ∫⁻ p, ‖(s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p‖ₑ ^ r ∂(μ'.prod μ'))
      atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ'.prod μ')
      (F := fun (n : ℕ) p => ‖(s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p‖ₑ ^ r)
      (f := fun _ => (0 : ℝ≥0∞))
      (bound := fun p => ‖s11Vs (d := d) s p‖ₑ ^ r) (fun n => (hmeas n)) ?_ hfin ?_
    · simpa using this
    · intro n
      refine Eventually.of_forall fun p => ?_
      refine ENNReal.rpow_le_rpow ?_ hr0.le
      by_cases hp : p ∈ (s11Box d n)ᶜ
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp]; simp
    · refine Eventually.of_forall fun p => ?_
      have hev : ∀ᶠ n : ℕ in atTop, p ∈ s11Box d n := by
        obtain ⟨N, hN⟩ := exists_nat_ge (max ‖p.1‖ ‖p.2‖)
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right]; exact (le_max_left _ _).trans (hN.trans hn')
        · rw [mem_closedBall, dist_zero_right]; exact (le_max_right _ _).trans (hN.trans hn')
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      rw [indicator_of_notMem (by simpa using hn)]
      simp [ENNReal.zero_rpow_of_pos hr0]
  have hlim' := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0 |>.comp hlim
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hlim'
  refine hlim'.congr fun n => ?_
  simp only [Function.comp]
  rw [s11_eLpNorm_ofReal hr ((s11Vs_meas s).indicator (s11Box_meas n).compl).aestronglyMeasurable]

end HRS.MS.R2S11
