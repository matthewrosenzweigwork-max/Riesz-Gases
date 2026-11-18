import HRS.Prob.MRepAux3

/-!
# MREP, part 4: progressive square roots and the range projection

For a progressive family of trace-class covariance forms `Σ̃_r(ω)`, the nonnegative square root `S_r(ω)` is progressive
(`exists_progressive_sqrt`), and the range projection `Q = lim S (S + ε)⁻¹` is a progressive projection
(`exists_progressive_proj`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Sqrt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The trace along a basis: the bound `c` used for the square root. -/
def trBound {ι : Type*} (e : HilbertBasis ι ℝ H) (C : H →L[ℝ] H →L[ℝ] ℝ) : ℝ :=
  1 + ∑' i, C (e i) (e i)

lemma trBound_pos {ι : Type*} (e : HilbertBasis ι ℝ H) {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : IsTraceClassCov C) : 0 < trBound e C := by
  have : 0 ≤ ∑' i, C (e i) (e i) := tsum_nonneg fun i => hC.nonneg _
  unfold trBound; linarith

lemma le_trBound {ι : Type*} (e : HilbertBasis ι ℝ H) {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : IsTraceClassCov C) (x : H) : C x x ≤ trBound e C * ‖x‖ ^ 2 := by
  obtain ⟨T, hT, hb⟩ := hC.hasSum_basis e
  unfold trBound
  rw [hT.tsum_eq]
  have := hb x
  nlinarith [sq_nonneg ‖x‖]

lemma formOp_isPSD' {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    HilbertCLTAux.IsPSDOp (HilbertCLTAux.formOp C) :=
  ⟨fun x y => by rw [HilbertCLTAux.inner_formOp, real_inner_comm, HilbertCLTAux.inner_formOp, hC.symm],
    fun x => by rw [HilbertCLTAux.inner_formOp]; exact hC.nonneg x⟩

theorem exists_progressive_sqrt {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H)
    (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) (hCt : ∀ r ω, IsTraceClassCov (Ct r ω))
    (hprog : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y)) :
    ∃ S : ℝ → Ω → H →L[ℝ] H, (∀ r ω, IsSqrtOfForm (S r ω) (Ct r ω)) ∧
      ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y) := by
  classical
  refine ⟨fun r ω => sqrtOp (trBound e (Ct r ω)) (HilbertCLTAux.formOp (Ct r ω)), fun r ω => ?_, fun x y i => ?_⟩
  · have hspec := sqrtOp_spec (formOp_isPSD' (hCt r ω)) (trBound_pos e (hCt r ω))
      (fun x => by rw [HilbertCLTAux.inner_formOp]; exact le_trBound e (hCt r ω) x)
    refine ⟨hspec.1.symm, hspec.1.nonneg, fun x y => ?_⟩
    rw [hspec.1.symm x (sqrtOp (trBound e (Ct r ω)) (HilbertCLTAux.formOp (Ct r ω)) y)]
    have : sqrtOp (trBound e (Ct r ω)) (HilbertCLTAux.formOp (Ct r ω))
        (sqrtOp (trBound e (Ct r ω)) (HilbertCLTAux.formOp (Ct r ω)) y) = HilbertCLTAux.formOp (Ct r ω) y := by
      have := congrArg (fun T : H →L[ℝ] H => T y) hspec.2
      simpa using this
    rw [this, real_inner_comm, HilbertCLTAux.inner_formOp, (hCt r ω).symm]
  · letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    set A : Set.Iic i × Ω → H →L[ℝ] H := fun z => HilbertCLTAux.formOp (Ct z.1 z.2) with hA
    have hAm : OpMeas A := by
      intro x
      refine measurable_of_inner_basis e (fun j => ?_)
      have : (fun z : Set.Iic i × Ω => inner ℝ (e j) (A z x)) =
          fun z => Ct z.1 z.2 x (e j) := by
        funext z; rw [real_inner_comm, hA]; simp [HilbertCLTAux.inner_formOp]
      rw [this]
      exact hprog x (e j) i
    set c : Set.Iic i × Ω → ℝ := fun z => trBound e (Ct z.1 z.2) with hc
    have hcm : Measurable c := by
      refine measurable_const.add (Measurable.tsum fun j => ?_)
      exact hprog (e j) (e j) i
    have := OpMeas.sqrtOp (A := A) hAm hcm (fun z => formOp_isPSD' (hCt z.1 z.2))
      (fun z => trBound_pos e (hCt z.1 z.2))
      (fun z x => by rw [hA]; simp only []; rw [HilbertCLTAux.inner_formOp]; exact le_trBound e (hCt z.1 z.2) x)
    exact (this x).inner measurable_const

/-- The progressive range projection `Q = lim_n S (S + ε_n)⁻¹`. -/
theorem exists_progressive_proj {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H)
    (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) (hCt : ∀ r ω, IsTraceClassCov (Ct r ω))
    (S : ℝ → Ω → H →L[ℝ] H) (hS : ∀ r ω, IsSqrtOfForm (S r ω) (Ct r ω))
    (hCp : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y))
    (hSp : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)) :
    ∃ Q : ℝ → Ω → H →L[ℝ] H,
      (∀ r ω x, Tendsto (fun n => S r ω (resolvent (S r ω) n x)) atTop (𝓝 (Q r ω x))) ∧
      (∀ r ω x y, inner ℝ (Q r ω x) y = inner ℝ x (Q r ω y)) ∧
      (∀ r ω x, Q r ω (Q r ω x) = Q r ω x) ∧ (∀ r ω x, Q r ω (S r ω x) = S r ω x) ∧
      ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y) := by
  classical
  have hPSD : ∀ r ω, HilbertCLTAux.IsPSDOp (S r ω) := fun r ω => ⟨(hS r ω).symm, (hS r ω).nonneg⟩
  have h : ∀ r ω, ∃ Q : H →L[ℝ] H,
      (∀ x, Tendsto (fun n => S r ω (resolvent (S r ω) n x)) atTop (𝓝 (Q x))) ∧
      (∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) ∧ (∀ x, Q (Q x) = Q x) ∧
      (∀ x, Q (S r ω x) = S r ω x) := by
    intro r ω
    obtain ⟨U, Q, -, hQ, hsym, hid, hQS, -, -⟩ := exists_polar (hPSD r ω) (S r ω) (fun x => rfl)
    exact ⟨Q, hQ, hsym, hid, hQS⟩
  choose Q hQ hQsym hQid hQS using h
  refine ⟨Q, hQ, hQsym, hQid, hQS, fun x y i => ?_⟩
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  set A : Set.Iic i × Ω → H →L[ℝ] H := fun z => S z.1 z.2 with hA
  have hAm : OpMeas A := by
    intro x
    refine measurable_of_inner_basis e (fun j => ?_)
    have : (fun z : Set.Iic i × Ω => inner ℝ (e j) (A z x)) =
        fun z => inner ℝ (S z.1 z.2 (e j)) x := by
      funext z; rw [real_inner_comm, hA]; simp only []
      rw [(hS z.1 z.2).symm (e j) x]; rw [real_inner_comm]
    rw [this]
    exact hSp (e j) x i
  set c : Set.Iic i × Ω → ℝ := fun z => trBound e (Ct z.1 z.2) with hc
  have hcm : Measurable c := by
    refine measurable_const.add (Measurable.tsum fun j => ?_)
    exact hCp (e j) (e j) i
  have hb : ∀ z x, inner ℝ (A z x) x ≤ c z * ‖x‖ ^ 2 := by
    intro z x
    have h1 : ‖S z.1 z.2 x‖ ^ 2 ≤ c z * ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, (hS z.1 z.2).sq x x]
      exact le_trBound e (hCt z.1 z.2) x
    have hc1 : 1 ≤ c z := by
      have : 0 ≤ ∑' i, Ct z.1 z.2 (e i) (e i) := tsum_nonneg fun i => (hCt z.1 z.2).nonneg _
      simp only [hc, trBound]; linarith
    have h2 : ‖S z.1 z.2 x‖ ≤ Real.sqrt (c z) * ‖x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (S z.1 z.2 x)), ← Real.sqrt_sq (norm_nonneg x),
        ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt h1
    calc inner ℝ (A z x) x ≤ ‖A z x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (Real.sqrt (c z) * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ c z * ‖x‖ ^ 2 := by
        have : Real.sqrt (c z) ≤ c z := by
          calc Real.sqrt (c z) ≤ Real.sqrt (c z) * Real.sqrt (c z) :=
                le_mul_of_one_le_left (Real.sqrt_nonneg _) (by
                  rw [Real.one_le_sqrt]; exact hc1)
            _ = c z := Real.mul_self_sqrt (by linarith)
        nlinarith [sq_nonneg ‖x‖]
  have hres : ∀ n, OpMeas fun z => resolvent (A z) n := fun n =>
    OpMeas.resolvent hAm hcm (fun z => hPSD z.1 z.2) (fun z => (trBound_pos e (hCt z.1 z.2)).le) hb n
  have hQm : OpMeas fun z : Set.Iic i × Ω => Q z.1 z.2 := by
    intro x
    refine measurable_of_tendsto_metrizable (f := fun n z => A z (resolvent (A z) n x))
      (fun n => OpMeas.apply hAm (hres n x)) (tendsto_pi_nhds.2 fun z => hQ z.1 z.2 x)
  exact (hQm x).inner measurable_const

/-- Progressivity of the coordinates of the resolvent. -/
theorem isProgressive_resolvent {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H)
    (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) (hCt : ∀ r ω, IsTraceClassCov (Ct r ω))
    (S : ℝ → Ω → H →L[ℝ] H) (hS : ∀ r ω, IsSqrtOfForm (S r ω) (Ct r ω))
    (hCp : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y))
    (hSp : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)) (n : ℕ) (x y : H) :
    IsProgressive ℱ (fun r ω => inner ℝ (resolvent (S r ω) n x) y) := by
  classical
  have hPSD : ∀ r ω, HilbertCLTAux.IsPSDOp (S r ω) := fun r ω => ⟨(hS r ω).symm, (hS r ω).nonneg⟩
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  set A : Set.Iic i × Ω → H →L[ℝ] H := fun z => S z.1 z.2 with hA
  have hAm : OpMeas A := by
    intro x
    refine measurable_of_inner_basis e (fun j => ?_)
    have : (fun z : Set.Iic i × Ω => inner ℝ (e j) (A z x)) =
        fun z => inner ℝ (S z.1 z.2 (e j)) x := by
      funext z; rw [real_inner_comm, hA]; simp only []
      rw [(hS z.1 z.2).symm (e j) x]; rw [real_inner_comm]
    rw [this]
    exact hSp (e j) x i
  set c : Set.Iic i × Ω → ℝ := fun z => trBound e (Ct z.1 z.2) with hc
  have hcm : Measurable c := by
    refine measurable_const.add (Measurable.tsum fun j => ?_)
    exact hCp (e j) (e j) i
  have hb : ∀ z x, inner ℝ (A z x) x ≤ c z * ‖x‖ ^ 2 := by
    intro z x
    have h1 : ‖S z.1 z.2 x‖ ^ 2 ≤ c z * ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, (hS z.1 z.2).sq x x]
      exact le_trBound e (hCt z.1 z.2) x
    have hc1 : 1 ≤ c z := by
      have : 0 ≤ ∑' i, Ct z.1 z.2 (e i) (e i) := tsum_nonneg fun i => (hCt z.1 z.2).nonneg _
      simp only [hc, trBound]; linarith
    have h2 : ‖S z.1 z.2 x‖ ≤ Real.sqrt (c z) * ‖x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (S z.1 z.2 x)), ← Real.sqrt_sq (norm_nonneg x),
        ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt h1
    calc inner ℝ (A z x) x ≤ ‖A z x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (Real.sqrt (c z) * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ c z * ‖x‖ ^ 2 := by
        have : Real.sqrt (c z) ≤ c z := by
          calc Real.sqrt (c z) ≤ Real.sqrt (c z) * Real.sqrt (c z) :=
                le_mul_of_one_le_left (Real.sqrt_nonneg _) (by
                  rw [Real.one_le_sqrt]; exact hc1)
            _ = c z := Real.mul_self_sqrt (by linarith)
        nlinarith [sq_nonneg ‖x‖]
  have hres : ∀ n, OpMeas fun z => resolvent (A z) n := fun n =>
    OpMeas.resolvent hAm hcm (fun z => hPSD z.1 z.2) (fun z => (trBound_pos e (hCt z.1 z.2)).le) hb n
  exact (hres n x).inner measurable_const

end Sqrt

end HRS.MRep
