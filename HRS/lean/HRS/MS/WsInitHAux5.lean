import HRS.MS.WsInitHAux4
import HRS.Whole.Thermal

/-!
# S21H packet H, part 5: projection tails in `ℓ²` from coordinate second moments

For `I : Finset ℕ` let `K_I = span{e_k : k ∈ I} ⊂ ℓ² = SeqL2` (dimension `|I|`), `P_I` its orthogonal projection (`v ↦ (v_k 1_{k ∈ I})_k`).
If the coordinates of a probability law `μ` on `ℓ²` satisfy `∫⁻ v_k² dμ ≤ σ_k`, then
`∫⁻ ‖v - P_I v‖ dμ ≤ (∑_{k ∉ I} σ_k)^{1/2}` (`s21h_tail_of_coords`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole

/-- The `k`-th unit vector of `ℓ²`. -/
def s21hSingle (k : ℕ) : SeqL2 := (lp.single 2 k (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2)

theorem s21h_coord_single (j k : ℕ) : SeqL2.coord (s21hSingle k) j = if j = k then 1 else 0 := by
  unfold SeqL2.coord s21hSingle
  rw [lp.single_apply]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem s21h_coord_add (u w : SeqL2) (j : ℕ) : SeqL2.coord (u + w) j = SeqL2.coord u j + SeqL2.coord w j := rfl

theorem s21h_coord_smul (c : ℝ) (u : SeqL2) (j : ℕ) : SeqL2.coord (c • u) j = c * SeqL2.coord u j := rfl

theorem s21h_coord_zero (j : ℕ) : SeqL2.coord (0 : SeqL2) j = 0 := rfl

theorem s21h_coord_neg (u : SeqL2) (j : ℕ) : SeqL2.coord (-u) j = - SeqL2.coord u j := rfl

theorem s21h_coord_sub (u w : SeqL2) (j : ℕ) : SeqL2.coord (u - w) j = SeqL2.coord u j - SeqL2.coord w j := rfl

theorem s21h_coord_sum (I : Finset ℕ) (f : ℕ → SeqL2) (j : ℕ) :
    SeqL2.coord (∑ k ∈ I, f k) j = ∑ k ∈ I, SeqL2.coord (f k) j := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [s21h_coord_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, s21h_coord_add, ih]

theorem s21h_continuous_coord (k : ℕ) : Continuous fun v : SeqL2 => SeqL2.coord v k :=
  (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) k).continuous

theorem s21h_inner_single (k : ℕ) (v : SeqL2) : inner ℝ (s21hSingle k) v = SeqL2.coord v k := by
  classical
  have := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : ℕ => ℝ) k (1 : ℝ) (show lp (fun _ : ℕ => ℝ) 2 from v)
  have e : inner ℝ (1 : ℝ) ((show lp (fun _ : ℕ => ℝ) 2 from v) k) = SeqL2.coord v k := by
    simp [SeqL2.coord]
  exact this.trans e

/-- The coordinate restriction. -/
def s21hRestr (I : Finset ℕ) (v : SeqL2) : SeqL2 := ∑ k ∈ I, SeqL2.coord v k • s21hSingle k

theorem s21h_coord_restr (I : Finset ℕ) (v : SeqL2) (j : ℕ) :
    SeqL2.coord (s21hRestr I v) j = if j ∈ I then SeqL2.coord v j else 0 := by
  classical
  unfold s21hRestr
  rw [s21h_coord_sum]
  simp_rw [s21h_coord_smul, s21h_coord_single]
  simp [Finset.sum_ite_eq']

/-- The span of the unit vectors indexed by `I`. -/
def s21hSpan (I : Finset ℕ) : Submodule ℝ SeqL2 := Submodule.span ℝ ((fun k => s21hSingle k) '' (I : Set ℕ))

instance (I : Finset ℕ) : FiniteDimensional ℝ (s21hSpan I) :=
  FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet I).image _)

theorem s21h_restr_mem (I : Finset ℕ) (v : SeqL2) : s21hRestr I v ∈ s21hSpan I := by
  unfold s21hRestr
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨k, hk, rfl⟩

theorem s21h_starProjection_eq (I : Finset ℕ) (v : SeqL2) :
    (s21hSpan I).starProjection v = s21hRestr I v := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (s21h_restr_mem I v) fun w hw => ?_
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rw [real_inner_comm, s21h_inner_single, s21h_coord_sub, s21h_coord_restr, if_pos (Finset.mem_coe.1 hk), sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

theorem s21h_finrank_span (I : Finset ℕ) : Module.finrank ℝ (s21hSpan I) = I.card := by
  classical
  have hind : LinearIndependent ℝ (fun k : I => s21hSingle k) := by
    refine Orthonormal.linearIndependent ?_
    rw [orthonormal_iff_ite]
    intro i j
    rw [s21h_inner_single, s21h_coord_single]
    by_cases h : (j : ℕ) = (i : ℕ)
    · have hij : j = i := Subtype.ext h
      simp [hij]
    · have : i ≠ j := fun hij => h (by rw [hij])
      simp [h, this]
  have e : Set.range (fun k : I => s21hSingle k) = (fun k => s21hSingle k) '' (I : Set ℕ) := by
    ext x; simp
  rw [s21hSpan, ← e, finrank_span_eq_card hind]
  simp

theorem s21h_norm_sub_restr_sq (I : Finset ℕ) (v : SeqL2) :
    ‖v - s21hRestr I v‖ ^ 2 = ∑' k : ℕ, if k ∈ I then 0 else SeqL2.coord v k ^ 2 := by
  have h := lp_two_norm_sq (ι := ℕ) (show lp (fun _ : ℕ => ℝ) 2 from (v - s21hRestr I v))
  rw [show ‖v - s21hRestr I v‖ = ‖(show lp (fun _ : ℕ => ℝ) 2 from (v - s21hRestr I v))‖ from rfl, h]
  refine tsum_congr fun k => ?_
  have e : (show lp (fun _ : ℕ => ℝ) 2 from (v - s21hRestr I v)) k = SeqL2.coord (v - s21hRestr I v) k := rfl
  rw [e, s21h_coord_sub, s21h_coord_restr]
  by_cases hk : k ∈ I <;> simp [hk]


theorem s21h_tail_of_coords (μ : Measure SeqL2) [IsProbabilityMeasure μ] (I : Finset ℕ) (σ : ℕ → ℝ≥0∞)
    (hσ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂μ ≤ σ k) :
    ∫⁻ v, ‖v - (s21hSpan I).starProjection v‖ₑ ∂μ ≤
      (∑' k : ℕ, if k ∈ I then 0 else σ k) ^ ((1 : ℝ) / 2) := by
  classical
  simp_rw [s21h_starProjection_eq]
  have hrm' : Continuous (s21hRestr I) := by
    unfold s21hRestr
    exact continuous_finsetSum _ fun k _ => (s21h_continuous_coord k).smul continuous_const
  have hh : Measurable fun v : SeqL2 => ‖v - s21hRestr I v‖ₑ :=
    (continuous_id.sub hrm').enorm.measurable
  have h1 := HRS.lintegral_rpow_mono_meas μ hh (p := 1) (q := 2) one_pos (by norm_num)
  simp only [ENNReal.rpow_one, div_one] at h1
  refine h1.trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hsq : ∀ v : SeqL2, ‖v - s21hRestr I v‖ₑ ^ (2 : ℝ) =
      ∑' k : ℕ, ENNReal.ofReal (if k ∈ I then 0 else SeqL2.coord v k ^ 2) := by
    intro v
    have hsum : Summable fun k : ℕ => if k ∈ I then 0 else SeqL2.coord v k ^ 2 := by
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
        (lp_two_summable (ι := ℕ) (show lp (fun _ : ℕ => ℝ) 2 from v))
      · split_ifs <;> positivity
      · split_ifs
        · exact sq_nonneg _
        · exact le_rfl
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> positivity) hsum,
      ← s21h_norm_sub_restr_sq, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp_rw [hsq]
  rw [lintegral_tsum fun k => ?_]
  · refine ENNReal.tsum_le_tsum fun k => ?_
    by_cases hk : k ∈ I
    · simp [hk]
    · simpa [hk] using hσ k
  · exact (ENNReal.measurable_ofReal.comp (by
      split_ifs
      · exact measurable_const
      · exact ((s21h_continuous_coord k).pow 2).measurable)).aemeasurable

end HRS.MS.S21
