import HRS.MS.R2S11Aux2

/-!
# S11.4 item (4), part 3: the `L^r(μ' × μ')` net of the commutator family
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

theorem s11_comm_global_bound {s : ℝ} (hs0 : 0 ≤ s) {Λ : ℝ} (v : s11V d Λ) (x y : Euc d) :
    |commutatorKernel d s v.1 x y| ≤ (s + 1) * max Λ 0 * (1 + rieszWeight s (x - y)) := by
  by_cases hxy : x = y
  · subst hxy
    have hW := s11_rieszWeight_nonneg (d := d) s (x - x)
    have h0 : commutatorKernel d s v.1 x x = 0 := by simp [commutatorKernel]
    rw [h0, abs_zero]
    have : 0 ≤ max Λ 0 := le_max_right _ _
    positivity
  · have := (S99.s99_comm_isBounded hs0 (Real.toNNReal (max Λ 0)) (s11_V_lip v)).bound x y hxy
    simpa [Real.coe_toNNReal _ (le_max_right _ _)] using this

theorem s11_comm_diff_pointwise {s : ℝ} (hs0 : 0 ≤ s) {Λ : ℝ} (v w : s11V d Λ) {n : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hD : ∀ z ∈ closedBall (0 : Euc d) (n : ℝ), ‖fderiv ℝ v.1 z - fderiv ℝ w.1 z‖ ≤ η) (p : Euc d × Euc d) :
    |commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2| ≤
      (s + 1) * η * s11Vs s p + 2 * ((s + 1) * max Λ 0) * (s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p := by
  have hV1 := s11Vs_ge_one (d := d) s p
  have hS : 0 ≤ s + 1 := by linarith
  have hΛ : 0 ≤ max Λ 0 := le_max_right _ _
  have h1 : 0 ≤ (s + 1) * η * s11Vs s p := by positivity
  by_cases hp : p ∈ s11Box d n
  · have hp' : p ∉ (s11Box d n)ᶜ := fun h => h hp
    rw [indicator_of_notMem hp', mul_zero, add_zero]
    by_cases hxy : p.1 = p.2
    · have : commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2 = 0 := by
        rw [← hxy]; simp [commutatorKernel]
      rw [this, abs_zero]; exact h1
    · exact s11_kernel_diff_bound hs0 v w hη hD hp.1 hp.2 hxy
  · rw [indicator_of_mem (show p ∈ (s11Box d n)ᶜ from hp)]
    have hv := s11_comm_global_bound hs0 v p.1 p.2
    have hw := s11_comm_global_bound hs0 w p.1 p.2
    have : |commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2| ≤
        |commutatorKernel d s v.1 p.1 p.2| + |commutatorKernel d s w.1 p.1 p.2| := abs_sub _ _
    have e : s11Vs (d := d) s p = 1 + rieszWeight s (p.1 - p.2) := rfl
    rw [e] at h1 ⊢
    nlinarith

theorem s11_arith1 {a c0 ε : ℝ} (ha : 0 < a) (hc : 0 ≤ c0) (hε : 0 < ε) :
    a * (ε / (2 * a * (c0 + 1))) * c0 ≤ ε / 2 := by
  have h1 : a * (ε / (2 * a * (c0 + 1))) * c0 = ε / 2 * (c0 / (c0 + 1)) := by
    field_simp
  rw [h1]
  have h2 : c0 / (c0 + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h3 : 0 ≤ ε / 2 := by linarith
  calc ε / 2 * (c0 / (c0 + 1)) ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left h2 h3
    _ = ε / 2 := mul_one _

theorem s11_arith2 {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) :
    b * (ε / (2 * (b + 1))) ≤ ε / 2 := by
  have h1 : b * (ε / (2 * (b + 1))) = ε / 2 * (b / (b + 1)) := by
    field_simp
  rw [h1]
  have h2 : b / (b + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h3 : 0 ≤ ε / 2 := by linarith
  calc ε / 2 * (b / (b + 1)) ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left h2 h3
    _ = ε / 2 := mul_one _

theorem s11_net_Lr {s r : ℝ} (hs0 : 0 ≤ s) (hr : 1 ≤ r) (hrs : r * s < d) (Λ : ℝ) {μ' : Measure (Euc d)}
    [IsProbabilityMeasure μ'] {M : ℝ} (hle : μ' ≤ ENNReal.ofReal M • (volume : Measure (Euc d))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : Finset (s11V d Λ), ∀ v : s11V d Λ, ∃ w ∈ F,
      eLpNorm (fun p : Euc d × Euc d => commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2)
        (ENNReal.ofReal r) (μ'.prod μ') ≤ ENNReal.ofReal ε := by
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < s + 1 := by linarith
  have hΛ'0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hb0 : 0 ≤ (s + 1) * max Λ 0 := mul_nonneg ha0.le hΛ'0
  have hV0 := s11_Vs_eLpNorm_ne_top hs0 hr hrs hle
  obtain ⟨c0, hc00, hV0eq⟩ : ∃ c0 : ℝ, 0 ≤ c0 ∧
      eLpNorm (s11Vs (d := d) s) (ENNReal.ofReal r) (μ'.prod μ') = ENNReal.ofReal c0 :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hV0).symm⟩
  have hδ0 : 0 < ε / (2 * (2 * ((s + 1) * max Λ 0) + 1)) := by positivity
  have htail := s11_tail_zero hs0 hr hrs hle
  obtain ⟨n, hn⟩ : ∃ n : ℕ, eLpNorm ((s11Box d n)ᶜ.indicator (s11Vs (d := d) s)) (ENNReal.ofReal r)
      (μ'.prod μ') ≤ ENNReal.ofReal (ε / (2 * (2 * ((s + 1) * max Λ 0) + 1))) :=
    ((ENNReal.tendsto_nhds_zero.1 htail) _ (ENNReal.ofReal_pos.2 hδ0)).exists
  have hη0 : 0 < ε / (2 * (s + 1) * (c0 + 1)) := by positivity
  obtain ⟨F, hF⟩ := s11_net_fderiv Λ (n : ℝ) hη0
  refine ⟨F, fun v => ?_⟩
  obtain ⟨w, hwF, hw⟩ := hF v
  refine ⟨w, hwF, ?_⟩
  have hDm : Measurable fun p : Euc d × Euc d =>
      commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2 :=
    (HRS.MS.Comm.comm_meas v.1 (s11_V_lip v).continuous.measurable).sub
      (HRS.MS.Comm.comm_meas w.1 (s11_V_lip w).continuous.measurable)
  have hVm := s11Vs_meas (d := d) s
  have hIm : Measurable ((s11Box d n)ᶜ.indicator (s11Vs (d := d) s)) := hVm.indicator (s11Box_meas n).compl
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr
  have hpt : ∀ p : Euc d × Euc d,
      ‖commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2‖ ≤
        ((s + 1) * (ε / (2 * (s + 1) * (c0 + 1)))) * s11Vs (d := d) s p +
          (2 * ((s + 1) * max Λ 0)) * (s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p := by
    intro p
    rw [Real.norm_eq_abs]
    have := s11_comm_diff_pointwise hs0 v w (n := n) hη0.le hw p
    refine this.trans_eq ?_
    ring
  have e1 := eLpNorm_const_smul (((s + 1) * (ε / (2 * (s + 1) * (c0 + 1))))) (s11Vs (d := d) s)
    (ENNReal.ofReal r) (μ'.prod μ')
  have e2 := eLpNorm_const_smul (2 * ((s + 1) * max Λ 0)) ((s11Box d n)ᶜ.indicator (s11Vs (d := d) s))
    (ENNReal.ofReal r) (μ'.prod μ')
  rw [Real.enorm_of_nonneg (by positivity), hV0eq] at e1
  rw [Real.enorm_of_nonneg (by positivity)] at e2
  simp only [Pi.smul_def, smul_eq_mul] at e1 e2
  have hA : ENNReal.ofReal ((s + 1) * (ε / (2 * (s + 1) * (c0 + 1)))) * ENNReal.ofReal c0 ≤
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (s11_arith1 ha0 hc00 hε)
  have hB : ENNReal.ofReal (2 * ((s + 1) * max Λ 0)) *
      eLpNorm ((s11Box d n)ᶜ.indicator (s11Vs (d := d) s)) (ENNReal.ofReal r) (μ'.prod μ') ≤
      ENNReal.ofReal (ε / 2) := by
    calc _ ≤ ENNReal.ofReal (2 * ((s + 1) * max Λ 0)) *
          ENNReal.ofReal (ε / (2 * (2 * ((s + 1) * max Λ 0) + 1))) := by gcongr
      _ = ENNReal.ofReal (2 * ((s + 1) * max Λ 0) * (ε / (2 * (2 * ((s + 1) * max Λ 0) + 1)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal (s11_arith2 (by positivity) hε)
  calc eLpNorm (fun p : Euc d × Euc d => commutatorKernel d s v.1 p.1 p.2 - commutatorKernel d s w.1 p.1 p.2)
        (ENNReal.ofReal r) (μ'.prod μ')
      ≤ eLpNorm (fun p => ((s + 1) * (ε / (2 * (s + 1) * (c0 + 1)))) * s11Vs (d := d) s p +
            (2 * ((s + 1) * max Λ 0)) * (s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p)
          (ENNReal.ofReal r) (μ'.prod μ') := eLpNorm_mono_real hDm.aestronglyMeasurable hpt
    _ ≤ eLpNorm (fun p => ((s + 1) * (ε / (2 * (s + 1) * (c0 + 1)))) * s11Vs (d := d) s p)
            (ENNReal.ofReal r) (μ'.prod μ') +
          eLpNorm (fun p => (2 * ((s + 1) * max Λ 0)) * (s11Box d n)ᶜ.indicator (s11Vs (d := d) s) p)
            (ENNReal.ofReal r) (μ'.prod μ') :=
        eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        rw [e1, e2]; exact add_le_add hA hB
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end HRS.MS.R2S11
