import HRS.MS.R2ChaosAux40

/-!
# HRS.MS.R2ChaosAux41 -- (a) part 3: the space `{P_μ b : b ∈ C_c^∞} ⊂ L²(μ)` as a submodule

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Sub

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s94_projMean_memLp {b : Euc d → ℝ} (hb : IsR2Test b) : MemLp (Whole.projMean μ b) 2 μ := by
  obtain ⟨C, hC⟩ := s94_test_bounded hb
  have hm : Measurable (Whole.projMean μ b) := (s94_test_continuous hb).measurable.sub measurable_const
  refine MemLp.of_bound hm.aestronglyMeasurable (C + |Whole.pair μ b|) (ae_of_all _ fun x => ?_)
  simp only [Whole.projMean, Real.norm_eq_abs]
  calc |b x - Whole.pair μ b| ≤ |b x| + |Whole.pair μ b| := abs_sub _ _
    _ ≤ _ := by linarith [hC x]

open Classical in
/-- `P_μ b` as an element of `L²(μ)` (`0` if `P_μ b ∉ L²`; for tests this never happens). -/
def s94tp (μ : Measure (Euc d)) (b : Euc d → ℝ) : Lp ℝ 2 μ :=
  if h : MemLp (Whole.projMean μ b) 2 μ then h.toLp _ else 0

theorem s94tp_eq {b : Euc d → ℝ} (hb : IsR2Test b) : s94tp μ b = (s94_projMean_memLp hb).toLp _ :=
  by unfold s94tp; exact dif_pos _

theorem s94_isTest_add {a b : Euc d → ℝ} (ha : IsR2Test a) (hb : IsR2Test b) : IsR2Test (fun x => a x + b x) :=
  ⟨ha.1.add hb.1, ha.2.add hb.2⟩

theorem s94_isTest_smul (c : ℝ) {a : Euc d → ℝ} (ha : IsR2Test a) : IsR2Test (fun x => c * a x) :=
  ⟨contDiff_const.mul ha.1, ha.2.mul_left⟩

theorem s94_isTest_zero : IsR2Test (fun _ : Euc d => (0 : ℝ)) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

theorem s94tp_add {a b : Euc d → ℝ} (ha : IsR2Test a) (hb : IsR2Test b) :
    s94tp μ (fun x => a x + b x) = s94tp μ a + s94tp μ b := by
  rw [s94tp_eq (s94_isTest_add ha hb), s94tp_eq ha, s94tp_eq hb,
    ← MemLp.toLp_add (s94_projMean_memLp ha) (s94_projMean_memLp hb)]
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
  simp only [Whole.projMean, Whole.pair, Pi.add_apply]
  rw [integral_add (s94_test_integrable ha μ) (s94_test_integrable hb μ)]
  ring

theorem s94tp_smul (c : ℝ) {a : Euc d → ℝ} (ha : IsR2Test a) :
    s94tp μ (fun x => c * a x) = c • s94tp μ a := by
  rw [s94tp_eq (s94_isTest_smul c ha), s94tp_eq ha, ← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
  simp only [Whole.projMean, Whole.pair, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

theorem s94tp_zero : s94tp μ (fun _ : Euc d => (0 : ℝ)) = 0 := by
  rw [s94tp_eq s94_isTest_zero]
  have : (s94_projMean_memLp (μ := μ) s94_isTest_zero).toLp _ = (MemLp.zero : MemLp (0 : Euc d → ℝ) 2 μ).toLp 0 := by
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
    simp [Whole.projMean, Whole.pair]
  rw [this]
  exact MemLp.toLp_zero _

/-- The submodule `{P_μ b : b ∈ C_c^∞}` of `L²(μ)`. -/
def s94TestSub (μ : Measure (Euc d)) [IsProbabilityMeasure μ] : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {x | ∃ b, IsR2Test b ∧ s94tp μ b = x}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨_, s94_isTest_add ha hb, s94tp_add ha hb⟩
  zero_mem' := ⟨_, s94_isTest_zero, s94tp_zero⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨_, s94_isTest_smul c ha, s94tp_smul c ha⟩

theorem s94_inner_tp {f : Euc d → ℝ} (hf : MemLp f 2 μ) {b : Euc d → ℝ} (hb : IsR2Test b) :
    inner ℝ (hf.toLp f) (s94tp μ b) = ∫ x, f x * Whole.projMean μ b x ∂μ := by
  rw [s94tp_eq hb, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, (s94_projMean_memLp hb).coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

end Sub

end HRS.MS.R2Chaos
