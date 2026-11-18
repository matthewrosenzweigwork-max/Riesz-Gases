import HRS.MS.Fp81S21GaussianQuadraticHilbert9
import HRS.MS.S21L_G11F

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T3
namespace HRS.Fp81.S21

/-- A separable Hilbert-valued second-chaos field admits finite Hilbert-valued
quadratic polynomial approximations in L⁴. -/
theorem fp81s21_InQ2_hilbert_L4_polynomials
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    {ι : Type} [Countable ι] (b : HilbertBasis ι ℝ B)
    (W : Ω → B) (hW : MemLp W 2 P)
    (hc : ∀ s, InQ2 hξ (fun ω => inner ℝ (b s) (W ω))) :
    MemLp W 4 P ∧
    (∫ ω, ‖W ω‖ ^ 4 ∂P) ≤ 15 * (∫ ω, ‖W ω‖ ^ 2 ∂P) ^ 2 ∧
    ∃ (S : ℕ → Finset ι) (N : ℕ → ι → ℕ) (c : ℕ → ι → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω =>
        (∑ s ∈ S n, quadSum (c n s) ξ (N n s) ω • b s) - W ω) 4 P)
        atTop (𝓝 0) := by
  classical
  have hscalar : ∀ s, Integrable (fun ω => (inner ℝ (b s) (W ω)) ^ 4) P ∧
      (∫ ω, (inner ℝ (b s) (W ω)) ^ 4 ∂P) ≤
        15 * (∫ ω, (inner ℝ (b s) (W ω)) ^ 2 ∂P) ^ 2 := fun s => s21l_inQ2_four (hc s)
  have hW4 : MemLp W 4 P := s21l_vec_four b hW hscalar
  obtain ⟨S, hS⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  let proj : ℕ → B →L[ℝ] B := fun n => ∑ s ∈ S n, (innerSL ℝ (b s)).smulRight (b s)
  have hproj : ∀ n x, proj n x = ∑ s ∈ S n, inner ℝ (b s) x • b s := by
    intro n x
    simp [proj, ContinuousLinearMap.sum_apply]
  have hnorm : ∀ n x, ‖proj n x‖ ≤ ‖x‖ := by
    intro n x
    have hy : ‖proj n x‖ ^ 2 = ∑ s ∈ S n, (inner ℝ (b s) x) ^ 2 := by
      rw [hproj, ← real_inner_self_eq_norm_sq]
      have h := b.orthonormal.inner_sum (fun s => inner ℝ (b s) x)
        (fun s => inner ℝ (b s) x) (S n)
      simp only [innerSL_apply_apply, conj_trivial, sq] at h ⊢
      exact h
    have hz := b.orthonormal.sum_inner_products_le x (s := S n)
    simp only [Real.norm_eq_abs, sq_abs] at hz
    by_contra h
    push_neg at h
    nlinarith [norm_nonneg x, norm_nonneg (proj n x)]
  have hpoint : ∀ x, Tendsto (fun n => proj n x) atTop (𝓝 x) := by
    intro x
    have hs := b.hasSum_repr x
    refine (hs.comp hS).congr fun n => ?_
    rw [hproj]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [HilbertBasis.repr_apply_apply]
  have hfourBound : (∫ ω, ‖W ω‖ ^ 4 ∂P) ≤ 15 * (∫ ω, ‖W ω‖ ^ 2 ∂P) ^ 2 := by
    have hsum := s21l_hasSum_sq b hW
    have hQn : ∀ n, MemLp (fun ω => ∑ s ∈ S n, (inner ℝ (b s) (W ω)) ^ 2) 2 P := by
      intro n
      apply memLp_finsetSum
      intro s hs
      apply (memLp_two_iff_integrable_sq ((aestronglyMeasurable_const.inner hW.aestronglyMeasurable).pow 2)).2
      convert (hscalar s).1 using 1 <;> ext ω <;> simp only [Pi.pow_apply] <;> ring
    have hae : ∀ ω, Tendsto (fun n => ∑ s ∈ S n, (inner ℝ (b s) (W ω)) ^ 2)
        atTop (𝓝 (‖W ω‖ ^ 2)) := fun ω => (s21l_hasSum_norm_sq b (W ω)).comp hS
    obtain ⟨_, hb⟩ := s21l_fatou_pw (Qn := fun n ω => ∑ s ∈ S n, (inner ℝ (b s) (W ω)) ^ 2)
      (Q := fun ω => ‖W ω‖ ^ 2) (fun n => (hQn n).aestronglyMeasurable)
      (hW.aestronglyMeasurable.norm.pow 2) (ae_of_all _ hae)
      (C := 15 * (∫ ω, ‖W ω‖ ^ 2 ∂P) ^ 2) (fun n => ⟨(hQn n).integrable_sq, by
        refine (s21l_finite_four b hW hscalar (S n)).trans ?_
        have h0 : 0 ≤ ∑ s ∈ S n, ∫ ω, (inner ℝ (b s) (W ω)) ^ 2 ∂P :=
          Finset.sum_nonneg fun s _ => integral_nonneg fun ω => sq_nonneg _
        have h1 : ∑ s ∈ S n, ∫ ω, (inner ℝ (b s) (W ω)) ^ 2 ∂P ≤ ∫ ω, ‖W ω‖ ^ 2 ∂P :=
          sum_le_hasSum (S n) (fun s _ => integral_nonneg fun ω => sq_nonneg _) hsum
        nlinarith⟩)
    convert hb using 1 <;> congr 1 <;> ext ω <;> ring
  choose N c hc4 using fun s => fp81s21_InQ2_L4_polynomials hξ (hc s)
  let g : ℕ → ℕ → Ω → B := fun n m ω =>
    ∑ s ∈ S n, quadSum (c s m) ξ (N s m) ω • b s
  let F : ℕ → Ω → B := fun n ω => proj n (W ω)
  have h1 : ∀ n, Tendsto (fun m => eLpNorm (g n m - F n) 4 P) atTop (𝓝 0) := by
    intro n
    have heq : ∀ m, g n m - F n = fun ω => ∑ s ∈ S n,
        (quadSum (c s m) ξ (N s m) ω - inner ℝ (b s) (W ω)) • b s := by
      intro m
      funext ω
      simp only [g, F, Pi.sub_apply, hproj, sub_smul, Finset.sum_sub_distrib]
    simp_rw [heq]
    have hb : ∀ m, eLpNorm (fun ω => ∑ s ∈ S n,
        (quadSum (c s m) ξ (N s m) ω - inner ℝ (b s) (W ω)) • b s) 4 P ≤
        ∑ s ∈ S n, ‖b s‖ₑ * eLpNorm (fun ω => quadSum (c s m) ξ (N s m) ω - inner ℝ (b s) (W ω)) 4 P := by
      intro m
      apply eLpNorm_finsum_smul_le (S n) b
      · intro s hs
        exact (memLp_quadSum hξ (c s m) (N s m)).aestronglyMeasurable.sub (hc s).1.aestronglyMeasurable
      · norm_num
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hb
    have ht : Tendsto (fun m => ∑ s ∈ S n, ‖b s‖ₑ * eLpNorm
        (fun ω => quadSum (c s m) ξ (N s m) ω - inner ℝ (b s) (W ω)) 4 P)
        atTop (𝓝 (∑ s ∈ S n, ‖b s‖ₑ * 0)) := by
      refine tendsto_finsetSum _ fun s hs => ?_
      exact ENNReal.Tendsto.const_mul (hc4 s) (Or.inr (by simp))
    simpa using ht
  have h2 : Tendsto (fun n => eLpNorm (F n - W) 4 P) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (fun ω => proj n (W ω) - W ω) 4 P) atTop (𝓝 0)
    simpa only [ENNReal.ofReal_ofNat] using
      dct_proj hW.aestronglyMeasurable (q := 4) (by norm_num) (by simpa using hW4) proj hnorm hpoint
  obtain ⟨mm, hmm⟩ := exists_diag (p := (4 : ℝ≥0∞)) (by norm_num) g F W h1 h2
  refine ⟨hW4, hfourBound, S, (fun n s => N s (mm n)), (fun n s => c s (mm n)), ?_⟩
  exact hmm

#print axioms fp81s21_InQ2_hilbert_L4_polynomials
end HRS.Fp81.S21
end
