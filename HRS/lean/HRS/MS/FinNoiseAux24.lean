import HRS.MS.FinNoiseAux23

/-!
# S8.6 `finite_noise`: positivity of the Hilbert-Schmidt pairing (S86)

`s86_pair_nonneg`: symmetric nonnegative Hilbert-Schmidt `S` and nonnegative Hilbert-Schmidt `Z` satisfy
`0 ≤ ∑_j ⟨S e_j, Z e_j⟩`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

theorem s86_pair_nonneg {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ K) {S Z : K →L[ℝ] K}
    (hS : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y)) (hS0 : ∀ x, 0 ≤ inner ℝ (S x) x)
    (hZ0 : ∀ x, 0 ≤ inner ℝ (Z x) x)
    (hSs : Summable fun j => ‖S (e j)‖ ^ 2) (hZs : Summable fun j => ‖Z (e j)‖ ^ 2) :
    0 ≤ hsPair e S Z := by
  classical
  obtain ⟨w, hw0, hw1, hw⟩ := s86_exists_weights (ι := ι)
  obtain ⟨hsymB, hposB, hinjB, hBs⟩ := s86_diagOp_props e hw0 hw1 hw
  have hBcomp := (s86_diagOp_spec e hw0 hw).2.2
  have hScomp : IsCompactOperator S := s86_hs_compact e (s86_hs2_ne_top_of_summable e hSs)
  set B := diagOp e w with hBdef
  have key : ∀ ε : ℝ, 0 < ε → 0 ≤ hsPair e S Z + ε * hsPair e B Z := by
    intro ε hε
    set T : K →L[ℝ] K := S + ε • B with hT
    have hTcomp : IsCompactOperator T := hScomp.add (hBcomp.smul ε)
    have hTsym : ((T : K →L[ℝ] K) : K →ₗ[ℝ] K).IsSymmetric := fun x y => by
      show inner ℝ (T x) y = inner ℝ x (T y)
      simp only [hT, add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, conj_trivial, hS x y, hsymB x y]
    have hTpos : ∀ x, 0 ≤ inner ℝ (T x) x := fun x => by
      simp only [hT, add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_smul_left,
        conj_trivial]
      exact add_nonneg (hS0 x) (mul_nonneg hε.le (hposB x))
    have hTinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
      have h0 : inner ℝ (T x) x = 0 := by rw [hx]; simp
      simp only [hT, add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_smul_left,
        conj_trivial] at h0
      have := hS0 x
      have := hposB x
      exact hinjB x (by nlinarith [mul_nonneg hε.le (hposB x)])
    obtain ⟨ι', φ, lam, hlam, hφ, -⟩ := HRS.MS.Spec.s8p_compact_selfadjoint_basis T hTcomp hTsym
      (fun x => by rw [real_inner_comm]; exact hTpos x) hTinj
    have h1 : 0 ≤ hsPair φ T Z := by
      refine tsum_nonneg fun k => ?_
      rw [hφ k, inner_smul_left, conj_trivial, real_inner_comm]
      exact mul_nonneg (hlam k).le (hZ0 (φ k))
    have hεB : Summable fun j => ‖(ε • B) (e j)‖ ^ 2 := by
      refine (hBs.mul_left (ε ^ 2)).congr fun j => ?_
      simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      ring
    have hTs : Summable fun j => ‖T (e j)‖ ^ 2 := s86_hs_add_summable e hSs hεB
    obtain ⟨-, h2⟩ := s86_hsPair_basis φ e hTs hZs
    rw [h2] at h1
    obtain ⟨hs1, -⟩ := s86_hsPair_formula e hSs hZs
    obtain ⟨hs2', -⟩ := s86_hsPair_formula e hBs hZs
    have hlin : hsPair e T Z = hsPair e S Z + ε * hsPair e B Z := by
      unfold hsPair
      have : ∀ j, inner ℝ (T (e j)) (Z (e j)) =
          inner ℝ (S (e j)) (Z (e j)) + ε * inner ℝ (B (e j)) (Z (e j)) := fun j => by
        simp only [hT, add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_smul_left,
          conj_trivial]
      simp_rw [this]
      rw [hs1.tsum_add (hs2'.mul_left ε), tsum_mul_left]
    rw [← hlin]; exact h1
  by_contra hneg
  push_neg at hneg
  set c := hsPair e B Z with hc
  have hε : 0 < -hsPair e S Z / (2 * (|c| + 1)) := div_pos (by linarith) (by positivity)
  have := key _ hε
  have h3 : -hsPair e S Z / (2 * (|c| + 1)) * c ≤ -hsPair e S Z / (2 * (|c| + 1)) * |c| :=
    mul_le_mul_of_nonneg_left (le_abs_self c) hε.le
  have h4 : -hsPair e S Z / (2 * (|c| + 1)) * (|c| + 1) = -hsPair e S Z / 2 := by
    field_simp
  nlinarith [abs_nonneg c]

end HRS.MS.FinNoise
