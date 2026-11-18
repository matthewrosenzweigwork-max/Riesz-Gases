import HRS.MS.Fp81S21TimeHistoryPast

/-! Packet 36: multiplication of Hilbert histories by a time indicator, with
its a.e. representative and past adaptation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS.MS.R26T6

variable (μ : Measure ℝ)

/-- Multiplication by the indicator of a measurable time set, as a contraction
on the actual Hilbert history space. -/
def fp81s21_timeL2_indicator (I : Set ℝ) (hI : MeasurableSet I) :
    Lp r26t6_Coeff 2 μ →L[ℝ] Lp r26t6_Coeff 2 μ := by
  let M : Lp r26t6_Coeff 2 μ → Lp r26t6_Coeff 2 μ :=
    fun z => ((Lp.memLp z).indicator hI).toLp (I.indicator z)
  have hM (z : Lp r26t6_Coeff 2 μ) : ⇑(M z) =ᵐ[μ] I.indicator z :=
    ((Lp.memLp z).indicator hI).coeFn_toLp
  let L : Lp r26t6_Coeff 2 μ →ₗ[ℝ] Lp r26t6_Coeff 2 μ := {
    toFun := M
    map_add' := by
      intro x y
      apply Lp.ext
      filter_upwards [hM (x + y), hM x, hM y, Lp.coeFn_add x y,
        Lp.coeFn_add (M x) (M y)] with s hxy hx hy hs ht
      change M (x + y) s = (M x + M y) s
      rw [hxy, ht]
      change I.indicator (x + y) s = M x s + M y s
      rw [hx, hy]
      by_cases hi : s ∈ I
      · simp only [Set.indicator_of_mem hi]
        exact hs
      · simp only [Set.indicator_of_notMem hi, add_zero]
    map_smul' := by
      intro c x
      apply Lp.ext
      filter_upwards [hM (c • x), hM x, Lp.coeFn_smul c x,
        Lp.coeFn_smul c (M x)] with s hcx hx hs ht
      by_cases hi : s ∈ I <;> simp [hcx, hx, hs, ht, Set.indicator_apply, hi] }
  apply L.mkContinuous 1
  intro z
  simp only [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hM z] with s hs
  change ‖M z s‖ ≤ ‖z s‖
  rw [hs]
  by_cases hi : s ∈ I <;> simp [Set.indicator_apply, hi]

/-- The contraction retains the expected indicator representative. -/
theorem fp81s21_timeL2_indicator_ae (I : Set ℝ) (hI : MeasurableSet I)
    (z : Lp r26t6_Coeff 2 μ) :
    ⇑(fp81s21_timeL2_indicator μ I hI z) =ᵐ[μ] I.indicator z :=
  ((Lp.memLp z).indicator hI).coeFn_toLp

/-- The time-indicator map has contraction constant one. -/
theorem fp81s21_timeL2_indicator_norm_le (I : Set ℝ) (hI : MeasurableSet I)
    (z : Lp r26t6_Coeff 2 μ) :
    ‖fp81s21_timeL2_indicator μ I hI z‖ ≤ ‖z‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fp81s21_timeL2_indicator_ae μ I hI z] with s hs
  rw [hs]
  by_cases hi : s ∈ I <;> simp [hi]

/-- Truncation preserves the exact history representation, including its
ambient almost-everywhere quantifiers. -/
theorem fp81s21_timeL2_indicator_rep
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Set ℝ) (hI : MeasurableSet I)
    (q : ℝ → Ω → r26t6_Coeff) (U : Ω → Lp r26t6_Coeff 2 μ)
    (hrep : ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun s => q s ω)) :
    ∀ᵐ ω ∂P, ⇑(fp81s21_timeL2_indicator μ I hI (U ω)) =ᵐ[μ]
      (fun s => I.indicator (fun t => q t ω) s) := by
  filter_upwards [hrep] with ω hω
  filter_upwards [fp81s21_timeL2_indicator_ae μ I hI (U ω), hω] with s hs hq
  rw [hs]
  by_cases hi : s ∈ I <;> simp [Set.indicator_apply, hi, hq]

/-- Only the coefficient times inside the truncation set need be adapted. -/
theorem fp81s21_timeL2_indicator_past
    [IsFiniteMeasure μ] {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (I : Set ℝ) (hI : MeasurableSet I)
    (q : ℝ → Ω → r26t6_Coeff) (U : Ω → Lp r26t6_Coeff 2 μ)
    (hq : Measurable (Function.uncurry q)) (hU : MemLp U 2 P)
    (hrep : ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun s => q s ω))
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (had : ∀ᵐ s ∂μ, s ∈ I → AEStronglyMeasurable[m] (q s) P) :
    AEStronglyMeasurable[m] (fun ω => fp81s21_timeL2_indicator μ I hI (U ω)) P := by
  letI : MeasurableSpace Ω := m₀
  refine fp81s21_timeL2_history_past P μ
    (fun s ω => I.indicator (fun t => q t ω) s)
    (fun ω => fp81s21_timeL2_indicator μ I hI (U ω)) ?_ ?_ ?_ m hm ?_
  · change Measurable (fun z : ℝ × Ω => if z.1 ∈ I then q z.1 z.2 else 0)
    exact Measurable.ite (hI.preimage measurable_fst) hq measurable_const
  · exact hU.continuousLinearMap_comp _
  · exact fp81s21_timeL2_indicator_rep μ P I hI q U hrep
  · filter_upwards [had] with s hs
    by_cases hi : s ∈ I
    · simpa only [Set.indicator_of_mem hi] using hs hi
    · simpa only [Set.indicator_of_notMem hi] using
        (aestronglyMeasurable_const : AEStronglyMeasurable[m] (fun _ : Ω => (0 : r26t6_Coeff)) P)

#print axioms fp81s21_timeL2_indicator
#print axioms fp81s21_timeL2_indicator_ae
#print axioms fp81s21_timeL2_indicator_norm_le
#print axioms fp81s21_timeL2_indicator_rep
#print axioms fp81s21_timeL2_indicator_past
end HRS.Fp81.S21
end
