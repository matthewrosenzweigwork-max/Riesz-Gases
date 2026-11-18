import HRS.MS.Fp81S21TimeRep9

/-! Packet 36: the scalar closed-subspace bridge for random time histories.
The product integrability required for Fubini is proved from the retained
second moment and the a.e. section identity, before exchanging integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance fp81s21_history_coeff_separable : TopologicalSpace.SeparableSpace r26t6_Coeff :=
  HRS.StaticLimitAux.separable_lp (ι := ℕ)
local instance fp81s21_history_coeff_secondCountable : SecondCountableTopology r26t6_Coeff :=
  UniformSpace.secondCountable_of_separable r26t6_Coeff

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- The reverse direction of the time-section moment construction: a retained
L² history and its joint representative give a product L² field. -/
theorem fp81s21_timeL2_history_product
    (q : ℝ → Ω → r26t6_Coeff) (U : Ω → Lp r26t6_Coeff 2 μ)
    (hq : Measurable (Function.uncurry q)) (hU : MemLp U 2 P)
    (hrep : ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun s => q s ω)) :
    MemLp (Function.uncurry q) 2 (μ.prod P) := by
  have hqm : AEStronglyMeasurable (Function.uncurry q) (μ.prod P) := hq.aestronglyMeasurable
  have hs : ∀ᵐ ω ∂P, MemLp (q · ω) 2 μ := by
    filter_upwards [hrep] with ω hω
    exact (Lp.memLp (U ω)).ae_eq hω
  have he : ∀ᵐ ω ∂P, (∫ s, ‖q s ω‖ ^ 2 ∂μ) = ‖U ω‖ ^ 2 := by
    filter_upwards [hrep] with ω hω
    calc
      _ = ∫ s, inner ℝ (U ω s) (U ω s) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hω] with s hs
        rw [hs, real_inner_self_eq_norm_sq]
      _ = inner ℝ (U ω) (U ω) := (L2.inner_def _ _).symm
      _ = _ := real_inner_self_eq_norm_sq _
  apply (memLp_two_iff_integrable_sq_norm hqm).2
  apply (integrable_prod_iff' (hqm.norm.pow 2)).2
  refine ⟨?_, ?_⟩
  · filter_upwards [hs] with ω hω
    exact (memLp_two_iff_integrable_sq_norm hω.aestronglyMeasurable).1 hω
  · have hi := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).1 hU
    apply hi.congr
    filter_upwards [he] with ω hω
    simpa only [Pi.pow_apply, Function.uncurry_apply_pair, norm_pow, norm_norm] using hω.symm

/-- Absolute product integrability of a history dual test times an arbitrary
scalar L² random variable. This is product-space Cauchy–Schwarz. -/
theorem fp81s21_timeL2_history_test_integrable
    (q : ℝ → Ω → r26t6_Coeff)
    (hq : MemLp (Function.uncurry q) 2 (μ.prod P))
    (e : Lp r26t6_Coeff 2 μ) (Y : Lp ℝ 2 P) :
    Integrable (fun z : ℝ × Ω => inner ℝ (q z.1 z.2) (e z.1) * Y z.2)
      (μ.prod P) := by
  have hbsm : AEStronglyMeasurable
      (fun z : ℝ × Ω => ‖e z.1‖ * ‖Y z.2‖) (μ.prod P) :=
    (Lp.aestronglyMeasurable e).norm.comp_fst.mul (Lp.aestronglyMeasurable Y).norm.comp_snd
  have hb : MemLp (fun z : ℝ × Ω => ‖e z.1‖ * ‖Y z.2‖) 2 (μ.prod P) := by
    apply (memLp_two_iff_integrable_sq_norm hbsm).2
    have he := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable e)).1 (Lp.memLp e)
    have hy := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable Y)).1 (Lp.memLp Y)
    simpa only [Real.norm_eq_abs, abs_mul, abs_norm, abs_abs, mul_pow] using he.mul_prod hy
  have hi : Integrable
      (fun z : ℝ × Ω => ‖q z.1 z.2‖ * (‖e z.1‖ * ‖Y z.2‖)) (μ.prod P) :=
    memLp_one_iff_integrable.mp (hq.norm.mul hb : MemLp _ 1 (μ.prod P))
  apply hi.mono
    ((hq.aestronglyMeasurable.inner (Lp.aestronglyMeasurable e).comp_fst).mul
      (Lp.aestronglyMeasurable Y).comp_snd)
  exact Eventually.of_forall fun z => by
    change ‖inner ℝ (q z.1 z.2) (e z.1) * Y z.2‖ ≤
      ‖‖q z.1 z.2‖ * (‖e z.1‖ * ‖Y z.2‖)‖
    simp only [norm_mul, norm_norm]
    exact (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _)

/-- Fubini for the scalar pairing of an actual retained history. -/
theorem fp81s21_timeL2_history_test_fubini
    (q : ℝ → Ω → r26t6_Coeff) (U : Ω → Lp r26t6_Coeff 2 μ)
    (hq : Measurable (Function.uncurry q)) (hU : MemLp U 2 P)
    (hrep : ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun s => q s ω))
    (e : Lp r26t6_Coeff 2 μ) (Y : Lp ℝ 2 P) :
    (∫ ω, inner ℝ (U ω) e * Y ω ∂P) =
      ∫ s, ∫ ω, inner ℝ (q s ω) (e s) * Y ω ∂P ∂μ := by
  have hi := fp81s21_timeL2_history_test_integrable P μ q
    (fp81s21_timeL2_history_product P μ q U hq hU hrep) e Y
  calc
    _ = ∫ ω, ∫ s, inner ℝ (q s ω) (e s) * Y ω ∂μ ∂P := by
      apply integral_congr_ae
      filter_upwards [hrep] with ω hω
      rw [L2.inner_def, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hω] with s hs
      rw [hs]
    _ = _ := (integral_integral_swap hi).symm

/-- Each scalar Hilbert dual test of the history belongs to the closed space of
past-measurable ambient L² classes. No jointly past-measurable version is assumed. -/
theorem fp81s21_timeL2_history_scalar_past
    (q : ℝ → Ω → r26t6_Coeff) (U : Ω → Lp r26t6_Coeff 2 μ)
    (hq : Measurable (Function.uncurry q)) (hU : MemLp U 2 P)
    (hrep : ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun s => q s ω))
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (had : ∀ᵐ s ∂μ, AEStronglyMeasurable[m] (q s) P)
    (e : Lp r26t6_Coeff 2 μ) :
    AEStronglyMeasurable[m] (fun ω => inner ℝ (U ω) e) P := by
  letI : MeasurableSpace Ω := m₀
  let A := lpMeas ℝ ℝ m 2 P
  have hc : IsClosed (A : Set (Lp ℝ 2 P)) :=
    isClosed_aestronglyMeasurable (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := P) hm
  have hx := hU.inner_const (𝕜 := ℝ) e
  let X : Lp ℝ 2 P := hx.toLp _
  have hqL := fp81s21_timeL2_history_product P μ q U hq hU hrep
  have hs : ∀ᵐ s ∂μ, MemLp (q s) 2 P := by
    have hi := (memLp_two_iff_integrable_sq_norm hqL.aestronglyMeasurable).1 hqL
    filter_upwards [hi.prod_right_ae] with s hs
    exact (memLp_two_iff_integrable_sq_norm
      (hq.comp (measurable_prodMk_left (x := s))).aestronglyMeasurable).2 hs
  have hX : X ∈ Aᗮᗮ := by
    apply (Aᗮ.mem_orthogonal' X).2
    intro Y hY
    rw [L2.inner_def]
    have he : (∫ ω, inner ℝ (X ω) (Y ω) ∂P) =
        ∫ ω, inner ℝ (U ω) e * Y ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hx.coeFn_toLp] with ω hω
      change Y ω * X ω = inner ℝ (U ω) e * Y ω
      rw [show X ω = inner ℝ (U ω) e from hω]
      exact mul_comm _ _
    rw [he, fp81s21_timeL2_history_test_fubini P μ q U hq hU hrep]
    apply integral_eq_zero_of_ae
    filter_upwards [hs, had] with s hs had
    have ht := hs.inner_const (𝕜 := ℝ) (e s)
    have htA : ht.toLp _ ∈ A :=
      (show AEStronglyMeasurable[m] (fun ω => inner ℝ (q s ω) (e s)) P
        from had.inner_const).congr ht.coeFn_toLp.symm
    have hz := (A.mem_orthogonal Y).1 hY _ htA
    rw [L2.inner_def] at hz
    calc
      _ = ∫ ω, inner ℝ (ht.toLp _ ω) (Y ω) ∂P := by
        apply integral_congr_ae
        filter_upwards [ht.coeFn_toLp] with ω hω
        change inner ℝ (q s ω) (e s) * Y ω = Y ω * (ht.toLp _ ω)
        rw [hω]
        exact mul_comm _ _
      _ = 0 := hz
  rw [A.orthogonal_orthogonal_eq_closure, hc.submodule_topologicalClosure_eq] at hX
  exact (show AEStronglyMeasurable[m] X P from hX).congr hx.coeFn_toLp

local instance fp81s21_history_borel (μ : Measure ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 μ) := borel _
local instance fp81s21_history_borelSpace (μ : Measure ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 μ) := ⟨rfl⟩

/-- A jointly measurable coefficient field whose fixed-time sections are past
adapted determines a past-adapted L² history. The time measure may be any finite
Borel measure on ℝ, in particular volume restricted to the retained horizon. -/
theorem fp81s21_timeL2_history_past
    (q : ℝ → Ω → r26t6_Coeff) (U : Ω → Lp r26t6_Coeff 2 μ)
    (hq : Measurable (Function.uncurry q)) (hU : MemLp U 2 P)
    (hrep : ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun s => q s ω))
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (had : ∀ᵐ s ∂μ, AEStronglyMeasurable[m] (q s) P) :
    AEStronglyMeasurable[m] U P := by
  letI : MeasurableSpace Ω := m₀
  let K := Lp r26t6_Coeff 2 μ
  let e : ℕ → K := TopologicalSpace.denseSeq K
  have hcoord (j : ℕ) : AEStronglyMeasurable[m]
      (fun ω => inner ℝ (U ω) (e j)) P :=
    fp81s21_timeL2_history_scalar_past P μ q U hq hU hrep m hm had (e j)
  let coords : K → (ℕ → ℝ) := fun z j => inner ℝ z (e j)
  have hc : Continuous coords := continuous_pi fun j => continuous_id.inner continuous_const
  have hi : Function.Injective coords := by
    intro x y h
    exact (TopologicalSpace.denseRange_denseSeq K).eq_of_inner_left ℝ (congrFun h)
  obtain ⟨g, hgm, hg⟩ := hc.measurableEmbedding hi |>.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨0⟩)
  let c : Ω → (ℕ → ℝ) := fun ω j =>
    (hcoord j).mk (fun ω => inner ℝ (U ω) (e j)) ω
  have hcm : Measurable[m] c := by
    letI : MeasurableSpace Ω := m
    exact measurable_pi_iff.2 fun j => (hcoord j).measurable_mk
  have he : (fun ω => g (c ω)) =ᵐ[P] U := by
    filter_upwards [ae_all_iff.2 (fun j => (hcoord j).ae_eq_mk)] with ω hω
    have hx : coords (U ω) = c ω := funext hω
    rw [← hx]
    exact congrFun hg _
  exact (hgm.comp hcm).stronglyMeasurable.aestronglyMeasurable.congr he

#print axioms fp81s21_timeL2_history_product
#print axioms fp81s21_timeL2_history_test_integrable
#print axioms fp81s21_timeL2_history_test_fubini
#print axioms fp81s21_timeL2_history_scalar_past
#print axioms fp81s21_timeL2_history_past
end HRS.Fp81.S21
end
