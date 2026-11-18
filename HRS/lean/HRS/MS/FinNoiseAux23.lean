import HRS.MS.FinNoiseAux22
import HRS.MS.SpecAux3

/-!
# S8.6 `finite_noise`: positive diagonal Hilbert-Schmidt operator and positivity of the pairing (S86)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

theorem s86_exists_weights {ι : Type*} [Countable ι] :
    ∃ w : ι → ℝ, (∀ j, 0 < w j) ∧ (∀ j, w j ≤ 1) ∧ Summable w := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  refine ⟨fun j => (1 / 2 : ℝ) ^ f j, fun j => by positivity, fun j => pow_le_one₀ (by norm_num) (by norm_num),
    ?_⟩
  exact summable_geometric_two.comp_injective hf

/-- The diagonal operator `∑ w_j ⟨e_j,·⟩ e_j`. -/
def diagOp {ι : Type*} (e : HilbertBasis ι ℝ K) (w : ι → ℝ) : K →L[ℝ] K :=
  ∑' j, (innerSL ℝ (e j : K)).smulRight (w j • (e j : K))

theorem s86_diagOp_spec {ι : Type*} (e : HilbertBasis ι ℝ K) {w : ι → ℝ} (hw0 : ∀ j, 0 < w j)
    (hw : Summable w) :
    HasSum (fun j => (innerSL ℝ (e j : K)).smulRight (w j • (e j : K))) (diagOp e w) ∧
    (∀ x y, inner ℝ (diagOp e w x) y = ∑' j, w j * (inner ℝ (e j : K) x * inner ℝ (e j : K) y)) ∧
    IsCompactOperator (diagOp e w) := by
  classical
  set R : ι → (K →L[ℝ] K) := fun j => (innerSL ℝ (e j : K)).smulRight (w j • (e j : K)) with hR
  have hRn : ∀ j, ‖R j‖ ≤ w j := fun j => by
    refine ContinuousLinearMap.opNorm_le_bound _ (hw0 j).le fun x => ?_
    simp only [hR, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (hw0 j), (e.orthonormal.1 j), mul_one]
    calc |inner ℝ (e j : K) x| * w j ≤ ‖(e j : K)‖ * ‖x‖ * w j :=
          mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (hw0 j).le
      _ = w j * ‖x‖ := by rw [e.orthonormal.1 j]; ring
  have hsum : Summable R := Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hRn hw)
  have hH : HasSum R (diagOp e w) := hsum.hasSum
  refine ⟨hH, fun x y => ?_, ?_⟩
  · have h1 : HasSum (fun j => R j x) (diagOp e w x) :=
      hH.map (ContinuousLinearMap.apply ℝ K x) (ContinuousLinearMap.apply ℝ K x).continuous
    have h2 : HasSum (fun j => inner ℝ y (R j x)) (inner ℝ y (diagOp e w x)) := by
      simpa using h1.mapL (innerSL ℝ y)
    rw [real_inner_comm, ← h2.tsum_eq]
    refine tsum_congr fun j => ?_
    simp [hR, inner_smul_right, real_inner_comm]
    ring
  · have hT : Tendsto (fun s : Finset ι => ∑ j ∈ s, R j) atTop (𝓝 (diagOp e w)) := hH
    refine isCompactOperator_of_tendsto hT (Eventually.of_forall fun s => ?_)
    exact s86_finsum_rankone_compact s (fun j => (e j : K)) (fun j => w j • (e j : K))

theorem s86_diagOp_eigen {ι : Type*} (e : HilbertBasis ι ℝ K) {w : ι → ℝ} (hw0 : ∀ j, 0 < w j)
    (hw : Summable w) (k : ι) : diagOp e w (e k) = w k • (e k : K) := by
  classical
  obtain ⟨-, hform, -⟩ := s86_diagOp_spec e hw0 hw
  refine ext_inner_right ℝ fun y => ?_
  rw [hform, tsum_eq_single k, inner_smul_left]
  · rw [real_inner_self_eq_norm_sq, e.orthonormal.1 k]; simp
  · intro j hj
    have : inner ℝ (e j : K) (e k : K) = 0 := by
      have := (orthonormal_iff_ite.1 e.orthonormal) j k
      simpa [hj] using this
    simp [this]

theorem s86_diagOp_props {ι : Type*} (e : HilbertBasis ι ℝ K) {w : ι → ℝ} (hw0 : ∀ j, 0 < w j)
    (hw1 : ∀ j, w j ≤ 1) (hw : Summable w) :
    (∀ x y, inner ℝ (diagOp e w x) y = inner ℝ x (diagOp e w y)) ∧
    (∀ x, 0 ≤ inner ℝ (diagOp e w x) x) ∧
    (∀ x, inner ℝ (diagOp e w x) x = 0 → x = 0) ∧
    Summable (fun j => ‖diagOp e w (e j)‖ ^ 2) := by
  classical
  obtain ⟨-, hform, -⟩ := s86_diagOp_spec e hw0 hw
  have hu : ∀ x, Summable (fun j => inner ℝ (e j : K) x ^ 2) := fun x => by
    have := (hasSum_inner_sq e x).summable
    refine this.congr fun j => ?_
    rw [real_inner_comm]
  have hsq : ∀ x, Summable fun j => w j * (inner ℝ (e j : K) x * inner ℝ (e j : K) x) := fun x =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hw0 j).le (mul_self_nonneg _)) (fun j => by
      nlinarith [hw1 j, sq_nonneg (inner ℝ (e j : K) x), hw0 j]) (hu x)
  refine ⟨fun x y => ?_, fun x => ?_, fun x hx => ?_, ?_⟩
  · rw [hform, real_inner_comm, hform]
    exact tsum_congr fun j => by ring
  · rw [hform]
    exact tsum_nonneg fun j => mul_nonneg (hw0 j).le (mul_self_nonneg _)
  · rw [hform] at hx
    have hz := (hasSum_zero_iff_of_nonneg (fun j => mul_nonneg (hw0 j).le (mul_self_nonneg
      (inner ℝ (e j : K) x)))).1 (by rw [← hx]; exact (hsq x).hasSum)
    have h0 : ∀ j, inner ℝ (e j : K) x = 0 := fun j => by
      have := congrFun hz j
      simp only [Pi.zero_apply] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hw0 j).ne'
      · exact mul_self_eq_zero.1 h
    have hrep : HasSum (fun i => inner ℝ (e i : K) x • (e i : K)) x := by
      simpa [HilbertBasis.repr_apply_apply] using e.hasSum_repr x
    have h4 : HasSum (fun i => inner ℝ (e i : K) x • (e i : K)) 0 := by
      simpa [h0] using hasSum_zero
    exact (h4.unique hrep).symm
  · simp_rw [s86_diagOp_eigen e hw0 hw, norm_smul, Real.norm_eq_abs, e.orthonormal.1, mul_one]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_) hw
    rw [sq_abs]
    nlinarith [hw0 j, hw1 j]

end HRS.MS.FinNoise
