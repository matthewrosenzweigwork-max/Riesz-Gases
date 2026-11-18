import HRS.MC.CepH3G1

/-!
# Packet CEPH3, part F1: convergence in probability, bounded continuous functionals
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section

section Prob
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}

/-- Convergence in probability at a fixed time from the uniform-in-time statement. -/
lemma h3f_conv_prob {Z : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N} {t : ℝ} (ht : 0 ≤ t)
    (hZc : ∀ n, 1 ≤ n → ∀ ω, Continuous fun s => Z n s ω) (hZlc : ∀ ω, Continuous fun s => Zl s ω)
    (hZl : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ s : Set.Icc (0 : ℝ) T, ‖Z n s ω - Zl s ω‖}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Z n t ω - Zl t ω‖}) atTop (𝓝 0) := by
  intro ε hε
  have h := hZl t (ε / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [mem_setOf_eq] at hω ⊢
  have hcont : Continuous fun s : Set.Icc (0:ℝ) t => ‖Z n s ω - Zl s ω‖ :=
    (((hZc n hn ω).sub (hZlc ω)).norm).comp continuous_subtype_val
  have hbdd : BddAbove (range fun s : Set.Icc (0:ℝ) t => ‖Z n s ω - Zl s ω‖) :=
    isCompact_range hcont |>.bddAbove
  have := le_ciSup hbdd ⟨t, ht, le_rfl⟩
  linarith

lemma h3f_aemeasurable {Z : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N} {t : ℝ}
    (hZm : ∀ n, 1 ≤ n → Measurable (Z n t))
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Z n t ω - Zl t ω‖}) atTop (𝓝 0)) :
    AEMeasurable (Zl t) P := by
  have hT : TendstoInMeasure P (fun n ω => Z (n + 1) t ω) atTop (Zl t) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    exact (hconv ε hε).comp (tendsto_add_atTop_nat 1)
  obtain ⟨ns, -, hns⟩ := hT.exists_seq_tendsto_ae
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hZm (ns n + 1) (by omega)).aemeasurable) hns

/-- Bounded continuous functionals pass to the limit along convergence in probability. -/
theorem h3f_integral_tendsto {Zn : ℕ → Ω → Ch N} {Zl : Ω → Ch N} {F : Ch N → ℝ} {C : ℝ}
    (hZn : ∀ n, Measurable (Zn n))
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Zn n ω - Zl ω‖}) atTop (𝓝 0))
    (hF : Continuous F) (hC : ∀ x, |F x| ≤ C) :
    Tendsto (fun n => ∫ ω, F (Zn n ω) ∂P) atTop (𝓝 (∫ ω, F (Zl ω) ∂P)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hT : TendstoInMeasure P (fun n ω => Zn (ns n) ω) atTop Zl := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    exact (hconv ε hε).comp hns
  obtain ⟨ms, -, hms⟩ := hT.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_) (integrable_const C)
    (fun n => Eventually.of_forall fun ω => ?_) ?_
  · exact (hF.measurable.comp (hZn _)).aestronglyMeasurable
  · simpa using hC _
  · filter_upwards [hms] with ω hω
    exact (hF.tendsto _).comp hω

lemma h3f_Zl_zero {Z : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N} {z₀ : Ω → Ch N}
    (hZ0 : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, Z n 0 ω = z₀ ω)
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Z n 0 ω - Zl 0 ω‖}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Zl 0 ω = z₀ ω := by
  have key : ∀ ε : ℝ, 0 < ε → P {ω | ε ≤ ‖z₀ ω - Zl 0 ω‖} = 0 := by
    intro ε hε
    have h1 : ∀ n, 1 ≤ n → P {ω | ε ≤ ‖Z n 0 ω - Zl 0 ω‖} = P {ω | ε ≤ ‖z₀ ω - Zl 0 ω‖} := by
      intro n hn
      refine measure_congr ?_
      filter_upwards [hZ0 n hn] with ω hω
      simp only [eq_iff_iff, mem_setOf_eq, hω]
    have h2 : Tendsto (fun n : ℕ => P {ω | ε ≤ ‖z₀ ω - Zl 0 ω‖}) atTop (𝓝 0) :=
      (hconv ε hε).congr' (by filter_upwards [eventually_ge_atTop 1] with n hn using h1 n hn)
    exact tendsto_nhds_unique tendsto_const_nhds h2
  have : ∀ k : ℕ, ∀ᵐ ω ∂P, ‖z₀ ω - Zl 0 ω‖ < 1 / ((k : ℝ) + 1) := by
    intro k
    have := key (1 / ((k : ℝ) + 1)) (by positivity)
    rw [measure_eq_zero_iff_ae_notMem] at this
    filter_upwards [this] with ω hω
    simpa using hω
  rw [← ae_all_iff] at this
  filter_upwards [this] with ω hω
  have h0 : ‖z₀ ω - Zl 0 ω‖ = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    linarith [hω k]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
end Prob
end
end HRS.MC.CepH3
