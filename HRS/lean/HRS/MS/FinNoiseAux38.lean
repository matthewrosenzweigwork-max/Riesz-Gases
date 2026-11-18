import HRS.MS.FinNoiseAux37
import HRS.MS.FinNoiseAux31
import HRS.MS.FinNoiseAux29

/-!
# S8.6 `finite_noise`: the deterministic root comparison for a sum of chart blocks (S86b)

`s86_hs_block_summable`: bookkeeping for nonnegative double families with `ℝ≥0∞` row bounds.
`s86_det_root`: if `S₀, Sb₀` are the symmetric roots of the global forms `∑_p 𝒞_p(R_p^* ·, R_p^* ·)` and
`∑_p 𝒟_p(R_p^* ·, R_p^* ·)` (`𝒞_p = S_p², 𝒟_p = Sb_p²` trace class along a basis `b` of the feature space), then
`∑_k ‖(S₀ - Sb₀)e_k‖² ≤ 2 ∑_p ‖R_p‖² ∑_i ‖(S_p - Sb_p) b_i‖²`  (Araki-Yamagami through `s86_block_root` and the
Hilbert-Schmidt composition bound `s86_hs_comp_between`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

theorem s86_hs_block_summable {P Q : Type*} (a : P → Q → ℝ) (c : P → ℝ) (ha : ∀ p q, 0 ≤ a p q)
    (hc0 : ∀ p, 0 ≤ c p) (hc : Summable c)
    (hbd : ∀ p, ∑' q, ENNReal.ofReal (a p q) ≤ ENNReal.ofReal (c p)) :
    (∀ p, Summable (a p)) ∧ (∀ p, ∑' q, a p q ≤ c p) ∧ Summable (Function.uncurry a) ∧
    (∀ q, Summable fun p => a p q) ∧ Summable (fun q => ∑' p, a p q) ∧
    ∑' q, ∑' p, a p q = ∑' p, ∑' q, a p q ∧ ∑' p, ∑' q, a p q ≤ ∑' p, c p := by
  have hrow : ∀ p, Summable (a p) := by
    intro p
    have hne : ∑' q, ENNReal.ofReal (a p q) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbd p)
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (ha p _)] using this
  have hle : ∀ p, ∑' q, a p q ≤ c p := by
    intro p
    have h1 : ENNReal.ofReal (∑' q, a p q) = ∑' q, ENNReal.ofReal (a p q) :=
      ENNReal.ofReal_tsum_of_nonneg (ha p) (hrow p)
    rw [← ENNReal.ofReal_le_ofReal_iff (hc0 p), h1]
    exact hbd p
  have hnn : ∀ p, 0 ≤ ∑' q, a p q := fun p => tsum_nonneg (ha p)
  have hrowS : Summable fun p => ∑' q, a p q :=
    Summable.of_nonneg_of_le hnn hle hc
  have hprod : Summable (Function.uncurry a) :=
    (summable_prod_of_nonneg (f := Function.uncurry a) (fun x => ha x.1 x.2)).2 ⟨hrow, hrowS⟩
  have hswap : Summable fun x : Q × P => a x.2 x.1 :=
    hprod.comp_injective (Prod.swap_injective)
  have hcol : ∀ q, Summable fun p => a p q := fun q => hswap.prod_factor q
  have hcolS : Summable fun q => ∑' p, a p q := hswap.prod
  refine ⟨hrow, hle, hprod, hcol, hcolS, ?_, ?_⟩
  · exact (Summable.tsum_comm hprod)
  · exact hrowS.tsum_le_tsum hle hc

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {ι κ : Type*} [Countable ι]

theorem s86_det_root (e : HilbertBasis ι ℝ K) (b : HilbertBasis κ ℝ F)
    {P : Type*} [Countable P] (R : P → F →L[ℝ] K)
    (C D : P → F →L[ℝ] F →L[ℝ] ℝ) (S Sb : P → F →L[ℝ] F)
    (hS : ∀ p, IsSqrtOfForm (S p) (C p)) (hSb : ∀ p, IsSqrtOfForm (Sb p) (D p))
    (Λ τ : ℝ) (hΛ : 0 ≤ Λ) (hτ : 0 ≤ τ)
    (hCΛ : ∀ p x, C p x x ≤ Λ * ‖x‖ ^ 2) (hDΛ : ∀ p x, D p x x ≤ Λ * ‖x‖ ^ 2)
    (hRs : Summable fun p => ‖R p‖ ^ 2)
    (hHS : ∀ p, Summable (fun i => ‖S p (b i)‖ ^ 2) ∧ ∑' i, ‖S p (b i)‖ ^ 2 ≤ τ)
    (hHSb : ∀ p, Summable (fun i => ‖Sb p (b i)‖ ^ 2) ∧ ∑' i, ‖Sb p (b i)‖ ^ 2 ≤ τ)
    (S₀ Sb₀ : K →L[ℝ] K)
    (hS₀ : ∀ x y, inner ℝ (S₀ x) y = inner ℝ x (S₀ y)) (hS₀0 : ∀ x, 0 ≤ inner ℝ (S₀ x) x)
    (hSb₀ : ∀ x y, inner ℝ (Sb₀ x) y = inner ℝ x (Sb₀ y)) (hSb₀0 : ∀ x, 0 ≤ inner ℝ (Sb₀ x) x)
    (hSM : ∀ x y, inner ℝ (S₀ x) (S₀ y) =
      ∑' p, C p (ContinuousLinearMap.adjoint (R p) x) (ContinuousLinearMap.adjoint (R p) y))
    (hSbM : ∀ x y, inner ℝ (Sb₀ x) (Sb₀ y) =
      ∑' p, D p (ContinuousLinearMap.adjoint (R p) x) (ContinuousLinearMap.adjoint (R p) y)) :
    Summable (fun k => ‖(S₀ - Sb₀) (e k)‖ ^ 2) ∧
    Summable (fun p => ‖R p‖ ^ 2 * ∑' i, ‖(S p - Sb p) (b i)‖ ^ 2) ∧
    ∑' k, ‖(S₀ - Sb₀) (e k)‖ ^ 2 ≤ 2 * ∑' p, ‖R p‖ ^ 2 * ∑' i, ‖(S p - Sb p) (b i)‖ ^ 2 := by
  classical
  set M : P → K →L[ℝ] F := fun p => (S p).comp (ContinuousLinearMap.adjoint (R p)) with hM
  set M' : P → K →L[ℝ] F := fun p => (Sb p).comp (ContinuousLinearMap.adjoint (R p)) with hM'
  set c : P → ℝ := fun p => Real.sqrt Λ * ‖R p‖ with hc
  have hnormS : ∀ p x, ‖S p x‖ ≤ Real.sqrt Λ * ‖x‖ := by
    intro p x
    have h := s86_sqrt_sq_diag (hS p) x
    rw [← Real.sqrt_sq (norm_nonneg (S p x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hΛ]
    exact Real.sqrt_le_sqrt (by rw [h]; linarith [hCΛ p x, mul_comm Λ (‖x‖ ^ 2)])
  have hnormSb : ∀ p x, ‖Sb p x‖ ≤ Real.sqrt Λ * ‖x‖ := by
    intro p x
    have h := s86_sqrt_sq_diag (hSb p) x
    rw [← Real.sqrt_sq (norm_nonneg (Sb p x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hΛ]
    exact Real.sqrt_le_sqrt (by rw [h]; linarith [hDΛ p x, mul_comm Λ (‖x‖ ^ 2)])
  have hRadj : ∀ p, ‖ContinuousLinearMap.adjoint (R p)‖ = ‖R p‖ := fun p =>
    ContinuousLinearMap.adjoint.norm_map (R p)
  have hMc : ∀ p x, ‖M p x‖ ≤ c p * ‖x‖ := by
    intro p x
    calc ‖M p x‖ = ‖S p (ContinuousLinearMap.adjoint (R p) x)‖ := rfl
      _ ≤ Real.sqrt Λ * ‖ContinuousLinearMap.adjoint (R p) x‖ := hnormS p _
      _ ≤ Real.sqrt Λ * (‖ContinuousLinearMap.adjoint (R p)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.adjoint (R p)).le_opNorm x) (Real.sqrt_nonneg _)
      _ = c p * ‖x‖ := by rw [hRadj]; simp only [hc]; ring
  have hMc' : ∀ p x, ‖M' p x‖ ≤ c p * ‖x‖ := by
    intro p x
    calc ‖M' p x‖ = ‖Sb p (ContinuousLinearMap.adjoint (R p) x)‖ := rfl
      _ ≤ Real.sqrt Λ * ‖ContinuousLinearMap.adjoint (R p) x‖ := hnormSb p _
      _ ≤ Real.sqrt Λ * (‖ContinuousLinearMap.adjoint (R p)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.adjoint (R p)).le_opNorm x) (Real.sqrt_nonneg _)
      _ = c p * ‖x‖ := by rw [hRadj]; simp only [hc]; ring
  have hcs : Summable fun p => c p ^ 2 := by
    refine (hRs.mul_left Λ).congr fun p => ?_
    simp only [hc, mul_pow, Real.sq_sqrt hΛ]
  -- Hilbert-Schmidt bounds of the blocks
  have hHSM : ∀ p, ∑' k, ENNReal.ofReal (‖M p (e k)‖ ^ 2) ≤ ENNReal.ofReal (‖R p‖ ^ 2 * τ) := by
    intro p
    have h1 := s86_hs_comp_between e b (S p) (ContinuousLinearMap.adjoint (R p))
    rw [hRadj] at h1
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hHS p).1]
    exact ENNReal.ofReal_le_ofReal (hHS p).2
  have hHSM' : ∀ p, ∑' k, ENNReal.ofReal (‖M' p (e k)‖ ^ 2) ≤ ENNReal.ofReal (‖R p‖ ^ 2 * τ) := by
    intro p
    have h1 := s86_hs_comp_between e b (Sb p) (ContinuousLinearMap.adjoint (R p))
    rw [hRadj] at h1
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hHSb p).1]
    exact ENNReal.ofReal_le_ofReal (hHSb p).2
  have hcτ : Summable fun p => ‖R p‖ ^ 2 * τ := hRs.mul_right τ
  have hcτ0 : ∀ p, 0 ≤ ‖R p‖ ^ 2 * τ := fun p => mul_nonneg (sq_nonneg _) hτ
  obtain ⟨-, -, -, -, hMs, -, -⟩ := s86_hs_block_summable (fun p k => ‖M p (e k)‖ ^ 2)
    (fun p => ‖R p‖ ^ 2 * τ) (fun p k => sq_nonneg _) hcτ0 hcτ hHSM
  obtain ⟨-, -, -, -, hM's, -, -⟩ := s86_hs_block_summable (fun p k => ‖M' p (e k)‖ ^ 2)
    (fun p => ‖R p‖ ^ 2 * τ) (fun p k => sq_nonneg _) hcτ0 hcτ hHSM'
  -- the block identity
  have hSM' : ∀ x y, inner ℝ (S₀ x) (S₀ y) = ∑' p, inner ℝ (M p x) (M p y) := by
    intro x y
    rw [hSM]
    refine tsum_congr fun p => ?_
    exact ((hS p).sq _ _).symm
  have hSbM' : ∀ x y, inner ℝ (Sb₀ x) (Sb₀ y) = ∑' p, inner ℝ (M' p x) (M' p y) := by
    intro x y
    rw [hSbM]
    refine tsum_congr fun p => ?_
    exact ((hSb p).sq _ _).symm
  obtain ⟨hsum, hbound⟩ := s86_block_root e M M' c c hMc hcs hMc' hcs hMs hM's S₀ Sb₀ hS₀ hS₀0 hSb₀
    hSb₀0 hSM' hSbM'
  -- the difference blocks
  have hdiff : ∀ p k, ‖M p (e k) - M' p (e k)‖ ^ 2 =
      ‖(S p - Sb p) (ContinuousLinearMap.adjoint (R p) (e k))‖ ^ 2 := by
    intro p k
    simp only [hM, hM', ContinuousLinearMap.comp_apply, sub_apply]
  set h : P → ℝ := fun p => ∑' i, ‖(S p - Sb p) (b i)‖ ^ 2 with hh
  have hsubS : ∀ p, Summable (fun i => ‖(S p - Sb p) (b i)‖ ^ 2) := by
    intro p
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
      (((hHS p).1.add (hHSb p).1).mul_left 2)
    simp only [sub_apply]
    nlinarith [norm_sub_le (S p (b i)) (Sb p (b i)), norm_nonneg (S p (b i) - Sb p (b i)),
      norm_nonneg (S p (b i)), norm_nonneg (Sb p (b i)),
      sq_nonneg (‖S p (b i)‖ - ‖Sb p (b i)‖),
      sq_nonneg (‖S p (b i) - Sb p (b i)‖ - ‖S p (b i)‖ - ‖Sb p (b i)‖)]
  have hh0 : ∀ p, 0 ≤ h p := fun p => tsum_nonneg fun i => sq_nonneg _
  have hh4 : ∀ p, h p ≤ 4 * τ := by
    intro p
    have h1 : ∀ i, ‖(S p - Sb p) (b i)‖ ^ 2 ≤ 2 * (‖S p (b i)‖ ^ 2 + ‖Sb p (b i)‖ ^ 2) := by
      intro i
      simp only [sub_apply]
      nlinarith [norm_sub_le (S p (b i)) (Sb p (b i)), norm_nonneg (S p (b i) - Sb p (b i)),
        norm_nonneg (S p (b i)), norm_nonneg (Sb p (b i)),
        sq_nonneg (‖S p (b i)‖ - ‖Sb p (b i)‖)]
    calc h p ≤ ∑' i, 2 * (‖S p (b i)‖ ^ 2 + ‖Sb p (b i)‖ ^ 2) :=
          (hsubS p).tsum_le_tsum h1 (((hHS p).1.add (hHSb p).1).mul_left 2)
      _ = 2 * (∑' i, ‖S p (b i)‖ ^ 2 + ∑' i, ‖Sb p (b i)‖ ^ 2) := by
          rw [tsum_mul_left, (hHS p).1.tsum_add (hHSb p).1]
      _ ≤ 4 * τ := by linarith [(hHS p).2, (hHSb p).2]
  have hcc : Summable fun p => ‖R p‖ ^ 2 * h p :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (sq_nonneg _) (hh0 p))
      (fun p => by nlinarith [sq_nonneg ‖R p‖, hh4 p, mul_le_mul_of_nonneg_left (hh4 p) (sq_nonneg ‖R p‖)])
      (hRs.mul_right (4 * τ))
  have hrowD : ∀ p, ∑' k, ENNReal.ofReal (‖(M p - M' p) (e k)‖ ^ 2) ≤
      ENNReal.ofReal (‖R p‖ ^ 2 * h p) := by
    intro p
    have h1 := s86_hs_comp_between e b (S p - Sb p) (ContinuousLinearMap.adjoint (R p))
    rw [hRadj] at h1
    have e1 : ∀ k, ‖(M p - M' p) (e k)‖ = ‖(S p - Sb p) (ContinuousLinearMap.adjoint (R p) (e k))‖ := by
      intro k; simp only [hM, hM', ContinuousLinearMap.comp_apply, sub_apply]
    simp_rw [e1]
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) zero_le
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hsubS p)]
  obtain ⟨-, -, -, -, -, hcomm, hle⟩ := s86_hs_block_summable
    (fun p k => ‖(M p - M' p) (e k)‖ ^ 2) (fun p => ‖R p‖ ^ 2 * h p) (fun p k => sq_nonneg _)
    (fun p => mul_nonneg (sq_nonneg _) (hh0 p)) hcc hrowD
  refine ⟨hsum, hcc, ?_⟩
  have e2 : ∑' k, ∑' p, ‖M p (e k) - M' p (e k)‖ ^ 2 = ∑' k, ∑' p, ‖(M p - M' p) (e k)‖ ^ 2 := by
    simp only [sub_apply]
  calc ∑' k, ‖(S₀ - Sb₀) (e k)‖ ^ 2 ≤ 2 * ∑' k, ∑' p, ‖M p (e k) - M' p (e k)‖ ^ 2 := hbound
    _ = 2 * ∑' p, ∑' k, ‖(M p - M' p) (e k)‖ ^ 2 := by rw [e2, hcomm]
    _ ≤ 2 * ∑' p, ‖R p‖ ^ 2 * h p := by linarith [hle]

end HRS.MS.FinNoise
