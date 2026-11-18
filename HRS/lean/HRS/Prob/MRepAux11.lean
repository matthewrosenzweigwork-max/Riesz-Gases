import HRS.Prob.MRepAux10

/-!
# MREP, part 11: bounded bilinear forms from matrices

For a matrix `a` that is symmetric, positive semidefinite (on rational finitely supported vectors) and has summable
diagonal, `matForm e a` is the bounded bilinear form with `matForm e a (e i) (e j) = a i j`; it is a trace-class
covariance form.  The description by countably many conditions makes the set of good matrices measurable.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section MatForm

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- Good matrices: symmetric, positive semidefinite (tested on rational finitely supported vectors), with summable
diagonal and the Cauchy–Schwarz inequality for the entries. -/
def GoodMat (a : ι → ι → ℝ) : Prop :=
  (∀ i j, a i j = a j i) ∧ (∀ i, 0 ≤ a i i) ∧ (∀ i j, a i j ^ 2 ≤ a i i * a j j) ∧
    Summable (fun i => a i i) ∧
    ∀ (F : Finset ι) (u : F → ℚ), 0 ≤ ∑ i : F, ∑ j : F, (u i : ℝ) * (u j : ℝ) * a i j

lemma GoodMat.psd_real {a : ι → ι → ℝ} (h : GoodMat a) (F : Finset ι) (u : F → ℝ) :
    0 ≤ ∑ i : F, ∑ j : F, u i * u j * a i j := by
  have hc : Continuous (fun v : F → ℝ => ∑ i : F, ∑ j : F, v i * v j * a i j) := by fun_prop
  have hd : DenseRange (Pi.map (fun _ : F => ((↑) : ℚ → ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  exact hd.induction_on u (isClosed_le continuous_const hc) (fun v => h.2.2.2.2 F v)

lemma GoodMat.abs_le_sqrt {a : ι → ι → ℝ} (h : GoodMat a) (i j : ι) :
    |a i j| ≤ Real.sqrt (a i i) * Real.sqrt (a j j) := by
  calc |a i j| = Real.sqrt (a i j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (a i i * a j j) := Real.sqrt_le_sqrt (h.2.2.1 i j)
    _ = _ := Real.sqrt_mul (h.2.1 i) _

variable (e : HilbertBasis ι ℝ H)

lemma GoodMat.summable_sqrt {a : ι → ι → ℝ} (h : GoodMat a) (x : H) :
    Summable (fun i => |inner ℝ (e i) x| * Real.sqrt (a i i)) ∧
      ∑' i, |inner ℝ (e i) x| * Real.sqrt (a i i) ≤ Real.sqrt (∑' i, a i i) * ‖x‖ := by
  set u : ι → ℝ := fun i => |inner ℝ (e i) x| * Real.sqrt (a i i) with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have htr : 0 ≤ ∑' i, a i i := tsum_nonneg h.2.1
  have hpart : ∀ F : Finset ι, ∑ i ∈ F, u i ≤ Real.sqrt (∑' i, a i i) * ‖x‖ := by
    intro F
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq F (fun i => |inner ℝ (e i) x|)
      (fun i => Real.sqrt (a i i))
    have h2 : ∑ i ∈ F, |inner ℝ (e i) x| ^ 2 ≤ ‖x‖ ^ 2 := by
      have := e.orthonormal.sum_inner_products_le x (s := F)
      simpa [Real.norm_eq_abs] using this
    have h3 : ∑ i ∈ F, Real.sqrt (a i i) ^ 2 ≤ ∑' i, a i i := by
      have : ∑ i ∈ F, Real.sqrt (a i i) ^ 2 = ∑ i ∈ F, a i i :=
        Finset.sum_congr rfl fun i _ => Real.sq_sqrt (h.2.1 i)
      rw [this]
      exact h.2.2.2.1.sum_le_tsum F (fun i _ => h.2.1 i)
    have h4 : (∑ i ∈ F, u i) ^ 2 ≤ (Real.sqrt (∑' i, a i i) * ‖x‖) ^ 2 := by
      calc (∑ i ∈ F, u i) ^ 2 ≤ (∑ i ∈ F, |inner ℝ (e i) x| ^ 2) *
            ∑ i ∈ F, Real.sqrt (a i i) ^ 2 := h1
        _ ≤ ‖x‖ ^ 2 * ∑' i, a i i :=
            mul_le_mul h2 h3 (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
        _ = (Real.sqrt (∑' i, a i i) * ‖x‖) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt htr]; ring
    exact (sq_le_sq₀ (Finset.sum_nonneg fun i _ => hu0 i)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 h4
  have hs : Summable u := summable_of_sum_le hu0 hpart
  exact ⟨hs, hs.tsum_le_of_sum_le hpart⟩

lemma GoodMat.summable_term {a : ι → ι → ℝ} (h : GoodMat a) (x y : H) :
    Summable (fun p : ι × ι => |inner ℝ (e p.1) x * inner ℝ (e p.2) y * a p.1 p.2|) ∧
      ∑' p : ι × ι, |inner ℝ (e p.1) x * inner ℝ (e p.2) y * a p.1 p.2| ≤
        (∑' i, a i i) * ‖x‖ * ‖y‖ := by
  obtain ⟨hsx, hbx⟩ := h.summable_sqrt e x
  obtain ⟨hsy, hby⟩ := h.summable_sqrt e y
  have htr : 0 ≤ ∑' i, a i i := tsum_nonneg h.2.1
  have hprod : Summable (fun p : ι × ι => (|inner ℝ (e p.1) x| * Real.sqrt (a p.1 p.1)) *
      (|inner ℝ (e p.2) y| * Real.sqrt (a p.2 p.2))) :=
    Summable.mul_of_nonneg hsx hsy (fun i => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (fun i => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  have hle : ∀ p : ι × ι, |inner ℝ (e p.1) x * inner ℝ (e p.2) y * a p.1 p.2| ≤
      (|inner ℝ (e p.1) x| * Real.sqrt (a p.1 p.1)) *
        (|inner ℝ (e p.2) y| * Real.sqrt (a p.2 p.2)) := by
    intro p
    rw [abs_mul, abs_mul]
    calc |inner ℝ (e p.1) x| * |inner ℝ (e p.2) y| * |a p.1 p.2|
        ≤ |inner ℝ (e p.1) x| * |inner ℝ (e p.2) y| *
          (Real.sqrt (a p.1 p.1) * Real.sqrt (a p.2 p.2)) :=
          mul_le_mul_of_nonneg_left (h.abs_le_sqrt p.1 p.2) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  have hs : Summable (fun p : ι × ι => |inner ℝ (e p.1) x * inner ℝ (e p.2) y * a p.1 p.2|) :=
    Summable.of_nonneg_of_le (fun p => abs_nonneg _) hle hprod
  refine ⟨hs, ?_⟩
  calc ∑' p : ι × ι, |inner ℝ (e p.1) x * inner ℝ (e p.2) y * a p.1 p.2|
      ≤ ∑' p : ι × ι, (|inner ℝ (e p.1) x| * Real.sqrt (a p.1 p.1)) *
        (|inner ℝ (e p.2) y| * Real.sqrt (a p.2 p.2)) := hs.tsum_le_tsum hle hprod
    _ = (∑' i, |inner ℝ (e i) x| * Real.sqrt (a i i)) *
        ∑' j, |inner ℝ (e j) y| * Real.sqrt (a j j) := by
        rw [tsum_mul_tsum_of_summable_norm]
        · exact hsx.congr fun i => (Real.norm_of_nonneg
            (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).symm
        · exact hsy.congr fun i => (Real.norm_of_nonneg
            (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).symm
    _ ≤ (Real.sqrt (∑' i, a i i) * ‖x‖) * (Real.sqrt (∑' i, a i i) * ‖y‖) :=
        mul_le_mul hbx hby (tsum_nonneg fun j => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = (∑' i, a i i) * ‖x‖ * ‖y‖ := by
        have := Real.mul_self_sqrt htr
        calc (Real.sqrt (∑' i, a i i) * ‖x‖) * (Real.sqrt (∑' i, a i i) * ‖y‖)
            = (Real.sqrt (∑' i, a i i) * Real.sqrt (∑' i, a i i)) * ‖x‖ * ‖y‖ := by ring
          _ = _ := by rw [this]

end MatForm

section TraceClass

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- A nonnegative symmetric bounded form with summable diagonal along some Hilbert basis (of any index type) is a
trace-class covariance form. -/
lemma isTraceClassCov_of_summable {ι : Type*} (e : HilbertBasis ι ℝ H) {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hs : ∀ x y, C x y = C y x) (hn : ∀ x, 0 ≤ C x x) (hsum : Summable fun i => C (e i) (e i)) :
    IsTraceClassCov C := by
  obtain ⟨ι₀, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  refine ⟨hs, hn, ι₀, b, ?_⟩
  have hA : HilbertCLTAux.IsPSDOp (HilbertCLTAux.formOp C) :=
    ⟨fun x y => by rw [HilbertCLTAux.inner_formOp, real_inner_comm, HilbertCLTAux.inner_formOp, hs],
      fun x => by rw [HilbertCLTAux.inner_formOp]; exact hn x⟩
  have hc : 0 < ‖C‖ + 1 := by positivity
  have hAc : ∀ x, inner ℝ (HilbertCLTAux.formOp C x) x ≤ (‖C‖ + 1) * ‖x‖ ^ 2 := by
    intro x
    rw [HilbertCLTAux.inner_formOp]
    have h1 : C x x ≤ ‖C x x‖ := le_abs_self _
    have h2 : ‖C x x‖ ≤ ‖C‖ * ‖x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm₂ C x x
    nlinarith [sq_nonneg ‖x‖]
  obtain ⟨hSpsd, hSS⟩ := sqrtOp_spec hA hc hAc
  set S := sqrtOp (‖C‖ + 1) (HilbertCLTAux.formOp C) with hS
  have hCS : ∀ x y, C x y = inner ℝ (S x) (S y) := by
    intro x y
    rw [← HilbertCLTAux.inner_formOp, ← hSS, ContinuousLinearMap.mul_apply, hSpsd.symm]
  have hdiag : ∀ x, C x x = ‖S x‖ ^ 2 := fun x => by rw [hCS, real_inner_self_eq_norm_sq]
  -- Parseval, in `ℝ≥0∞`
  have hparsB : ∀ j, ENNReal.ofReal (C (b j) (b j)) =
      ∑' i, ENNReal.ofReal (inner ℝ (S (e i)) (b j) ^ 2) := by
    intro j
    have hh := e.hasSum_inner_mul_inner (S (b j)) (S (b j))
    rw [real_inner_self_eq_norm_sq] at hh
    have hterm : ∀ i, inner ℝ (S (b j)) (e i) * inner ℝ (e i) (S (b j)) =
        inner ℝ (S (e i)) (b j) ^ 2 := by
      intro i
      have h1 : inner ℝ (S (b j)) (e i) = inner ℝ (S (e i)) (b j) :=
        (real_inner_comm _ _).trans (hSpsd.symm _ _).symm
      have h2 : inner ℝ (e i) (S (b j)) = inner ℝ (S (e i)) (b j) := (hSpsd.symm _ _).symm
      rw [h1, h2]; ring
    simp_rw [hterm] at hh
    rw [hdiag, ← hh.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hh.summable]
  have hparsE : ∀ i, ENNReal.ofReal (C (e i) (e i)) =
      ∑' j, ENNReal.ofReal (inner ℝ (S (e i)) (b j) ^ 2) := by
    intro i
    have hh := b.hasSum_inner_mul_inner (S (e i)) (S (e i))
    rw [real_inner_self_eq_norm_sq] at hh
    have hterm : ∀ j, inner ℝ (S (e i)) (b j) * inner ℝ (b j) (S (e i)) =
        inner ℝ (S (e i)) (b j) ^ 2 := by
      intro j
      rw [real_inner_comm (b j) (S (e i))]; ring
    simp_rw [hterm] at hh
    rw [hdiag, ← hh.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hh.summable]
  have htot : ∑' j, ENNReal.ofReal (C (b j) (b j)) = ∑' i, ENNReal.ofReal (C (e i) (e i)) := by
    simp_rw [hparsB, hparsE]
    exact ENNReal.tsum_comm
  have hfin : ∑' i, ENNReal.ofReal (C (e i) (e i)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hn _) hsum]
    exact ENNReal.ofReal_ne_top
  have := ENNReal.summable_toReal (htot ▸ hfin : ∑' j, ENNReal.ofReal (C (b j) (b j)) ≠ ∞)
  refine this.congr fun j => ?_
  exact ENNReal.toReal_ofReal (hn _)

end TraceClass

section MatForm2

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} (e : HilbertBasis ι ℝ H)

/-- The double series defining the form of a matrix. -/
def matBil (a : ι → ι → ℝ) (x y : H) : ℝ :=
  ∑' p : ι × ι, inner ℝ (e p.1) x * inner ℝ (e p.2) y * a p.1 p.2

variable {e}

lemma matBil_add_left {a : ι → ι → ℝ} (h : GoodMat a) (x x' y : H) :
    matBil e a (x + x') y = matBil e a x y + matBil e a x' y := by
  have s1 := ((h.summable_term e x y).1).of_abs
  have s2 := ((h.summable_term e x' y).1).of_abs
  unfold matBil
  rw [← Summable.tsum_add s1 s2]
  refine tsum_congr fun p => ?_
  rw [inner_add_right]; ring

lemma matBil_smul_left {a : ι → ι → ℝ} (h : GoodMat a) (c : ℝ) (x y : H) :
    matBil e a (c • x) y = c * matBil e a x y := by
  unfold matBil
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [inner_smul_right]; ring

lemma matBil_add_right {a : ι → ι → ℝ} (h : GoodMat a) (x y y' : H) :
    matBil e a x (y + y') = matBil e a x y + matBil e a x y' := by
  have s1 := ((h.summable_term e x y).1).of_abs
  have s2 := ((h.summable_term e x y').1).of_abs
  unfold matBil
  rw [← Summable.tsum_add s1 s2]
  refine tsum_congr fun p => ?_
  rw [inner_add_right]; ring

lemma matBil_smul_right {a : ι → ι → ℝ} (h : GoodMat a) (c : ℝ) (x y : H) :
    matBil e a x (c • y) = c * matBil e a x y := by
  unfold matBil
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [inner_smul_right]; ring

lemma norm_matBil_le {a : ι → ι → ℝ} (h : GoodMat a) (x y : H) :
    ‖matBil e a x y‖ ≤ (∑' i, a i i) * ‖x‖ * ‖y‖ := by
  obtain ⟨hs, hb⟩ := h.summable_term e x y
  unfold matBil
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simpa [Real.norm_eq_abs] using hs
  · simpa [Real.norm_eq_abs] using hb

/-- The bounded bilinear form of a good matrix (and `0` for a bad one). -/
def matForm (e : HilbertBasis ι ℝ H) (a : ι → ι → ℝ) : H →L[ℝ] H →L[ℝ] ℝ :=
  if hg : GoodMat a then
    LinearMap.mkContinuous₂
      (LinearMap.mk₂ ℝ (fun x y => matBil e a x y) (matBil_add_left hg) (matBil_smul_left hg)
        (matBil_add_right hg) (matBil_smul_right hg))
      (∑' i, a i i) (fun x y => norm_matBil_le hg x y)
  else 0

lemma matForm_apply {a : ι → ι → ℝ} (h : GoodMat a) (x y : H) :
    matForm e a x y = matBil e a x y := by
  simp only [matForm, dif_pos h]
  rfl

lemma matForm_of_not {a : ι → ι → ℝ} (h : ¬ GoodMat a) : matForm e a = 0 := by
  simp only [matForm, dif_neg h]

lemma matBil_basis {a : ι → ι → ℝ} (i j : ι) : matBil e a (e i) (e j) = a i j := by
  unfold matBil
  rw [tsum_eq_single (i, j)]
  · simp only
    rw [orthonormal_iff_ite.1 e.orthonormal i i, orthonormal_iff_ite.1 e.orthonormal j j]
    simp
  · rintro ⟨k, l⟩ hkl
    have : k ≠ i ∨ l ≠ j := by
      by_contra hcon
      push Not at hcon
      exact hkl (by rw [hcon.1, hcon.2])
    rcases this with hk | hl
    · simp [orthonormal_iff_ite.1 e.orthonormal k i, hk]
    · simp [orthonormal_iff_ite.1 e.orthonormal l j, hl]

lemma matForm_basis {a : ι → ι → ℝ} (h : GoodMat a) (i j : ι) : matForm e a (e i) (e j) = a i j := by
  rw [matForm_apply h, matBil_basis]

lemma matBil_symm {a : ι → ι → ℝ} (h : GoodMat a) (x y : H) : matBil e a x y = matBil e a y x := by
  unfold matBil
  rw [← (Equiv.prodComm ι ι).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [h.1 p.2 p.1]; ring

lemma matBil_self_nonneg {a : ι → ι → ℝ} (h : GoodMat a) (x : H) : 0 ≤ matBil e a x x := by
  have hs : Summable (fun p : ι × ι => inner ℝ (e p.1) x * inner ℝ (e p.2) x * a p.1 p.2) :=
    ((h.summable_term e x x).1).of_abs
  have hsq : Tendsto (fun F : Finset ι => F ×ˢ F) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun s => ⟨s.image Prod.fst ∪ s.image Prod.snd, fun F hF p hp => ?_⟩
    have h1 : p.1 ∈ F := hF (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
    have h2 : p.2 ∈ F := hF (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
    exact Finset.mem_product.2 ⟨h1, h2⟩
  have hlim := hs.hasSum.comp hsq
  refine ge_of_tendsto hlim (Eventually.of_forall fun F => ?_)
  simp only [Function.comp_apply]
  rw [Finset.sum_product]
  have := h.psd_real F (fun i => inner ℝ (e i) x)
  have e1 : ∑ i : F, ∑ j : F, inner ℝ (e i) x * inner ℝ (e j) x * a i j =
      ∑ i ∈ F, ∑ j ∈ F, inner ℝ (e i) x * inner ℝ (e j) x * a i j := by
    rw [← Finset.sum_coe_sort F (fun i => ∑ j ∈ F, inner ℝ (e i) x * inner ℝ (e j) x * a i j)]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_coe_sort F (fun j => inner ℝ (e i) x * inner ℝ (e j) x * a i j)
  rw [← e1]
  exact this

lemma isTraceClassCov_matForm {a : ι → ι → ℝ} (h : GoodMat a) : IsTraceClassCov (matForm e a) := by
  refine isTraceClassCov_of_summable e (fun x y => ?_) (fun x => ?_) ?_
  · rw [matForm_apply h, matForm_apply h]; exact matBil_symm h x y
  · rw [matForm_apply h]; exact matBil_self_nonneg h x
  · simpa only [matForm_basis h] using h.2.2.2.1

end MatForm2

section FormExt

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} (e : HilbertBasis ι ℝ H)

lemma form_hasSum_left (C : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    HasSum (fun i => inner ℝ (e i) x * C (e i) y) (C x y) := by
  have h := e.hasSum_repr x
  simp only [HilbertBasis.repr_apply_apply] at h
  have h2 := (ContinuousLinearMap.apply ℝ ℝ y ∘L C).hasSum h
  simpa using h2

lemma form_hasSum_basis (C : H →L[ℝ] H →L[ℝ] ℝ) (i : ι) (y : H) :
    HasSum (fun j => inner ℝ (e j) y * C (e i) (e j)) (C (e i) y) := by
  have h := e.hasSum_repr y
  simp only [HilbertBasis.repr_apply_apply] at h
  have h2 := (C (e i)).hasSum h
  simpa using h2

lemma form_ext_basis {C₁ C₂ : H →L[ℝ] H →L[ℝ] ℝ} (h : ∀ i j, C₁ (e i) (e j) = C₂ (e i) (e j)) :
    C₁ = C₂ := by
  ext x y
  have h1 : ∀ i, C₁ (e i) y = C₂ (e i) y := fun i =>
    (form_hasSum_basis e C₁ i y).unique (by
      simpa only [h i] using form_hasSum_basis e C₂ i y)
  exact (form_hasSum_left e C₁ x y).unique (by
    simpa only [h1] using form_hasSum_left e C₂ x y)

lemma goodMat_of_trace {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    GoodMat (fun i j => C (e i) (e j)) := by
  have hA := formOp_isPSD' hC
  refine ⟨fun i j => hC.symm _ _, fun i => hC.nonneg _, fun i j => ?_, ?_, ?_⟩
  · have := hA.cs (e i) (e j)
    simpa only [HilbertCLTAux.inner_formOp] using this
  · obtain ⟨T, hT, -⟩ := hC.hasSum_basis e
    exact hT.summable
  · intro F u
    have : ∑ i : F, ∑ j : F, (u i : ℝ) * (u j : ℝ) * C (e i) (e j) =
        C (∑ i : F, (u i : ℝ) • e i) (∑ j : F, (u j : ℝ) • e j) := by
      symm
      have h1 : C (∑ i : F, (u i : ℝ) • e i) = ∑ i : F, (u i : ℝ) • C (e i) := by
        rw [map_sum]; simp only [map_smul]
      rw [h1, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]; ring
    rw [this]
    exact hC.nonneg _

lemma matForm_matrix {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    matForm e (fun i j => C (e i) (e j)) = C :=
  form_ext_basis e fun i j => matForm_basis (goodMat_of_trace e hC) i j

lemma isTraceClassCov_zero : IsTraceClassCov (0 : H →L[ℝ] H →L[ℝ] ℝ) := by
  obtain ⟨ι₀, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  exact ⟨fun x y => rfl, fun x => le_rfl, ι₀, b, by simpa using summable_zero⟩

end FormExt

section MeasMat

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

lemma summable_iff_ofReal {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    Summable f ↔ ∑' i, ENNReal.ofReal (f i) ≠ ∞ := by
  constructor
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg hf hs]
    exact ENNReal.ofReal_ne_top
  · intro h
    have := ENNReal.summable_toReal h
    exact this.congr fun i => ENNReal.toReal_ofReal (hf i)

lemma measurableSet_goodMat {α : Type*} [MeasurableSpace α] {a : ι → ι → α → ℝ}
    (ha : ∀ i j, Measurable (a i j)) : MeasurableSet {p | GoodMat (fun i j => a i j p)} := by
  have h1 : MeasurableSet {p | ∀ i j, a i j p = a j i p} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (ha i j) (ha j i)
  have h2 : MeasurableSet {p | ∀ i, 0 ≤ a i i p} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (ha i i)
  have h3 : MeasurableSet {p | ∀ i j, a i j p ^ 2 ≤ a i i p * a j j p} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le ((ha i j).pow_const 2) ((ha i i).mul (ha j j))
  have h4 : MeasurableSet {p | ∑' i, ENNReal.ofReal (a i i p) ≠ ∞} := by
    have : Measurable fun p => ∑' i, ENNReal.ofReal (a i i p) :=
      Measurable.ennreal_tsum fun i => ENNReal.measurable_ofReal.comp (ha i i)
    exact this (measurableSet_singleton (⊤ : ℝ≥0∞)).compl
  have h5 : MeasurableSet {p | ∀ (F : Finset ι) (u : F → ℚ),
      0 ≤ ∑ i : F, ∑ j : F, (u i : ℝ) * (u j : ℝ) * a i j p} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun F => MeasurableSet.iInter fun u => ?_
    refine measurableSet_le measurable_const ?_
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (measurable_const.mul measurable_const).mul (ha i j)
  have hset : {p | GoodMat (fun i j => a i j p)} =
      {p | ∀ i j, a i j p = a j i p} ∩ ({p | ∀ i, 0 ≤ a i i p} ∩
        ({p | ∀ i j, a i j p ^ 2 ≤ a i i p * a j j p} ∩ ({p | ∑' i, ENNReal.ofReal (a i i p) ≠ ∞} ∩
          {p | ∀ (F : Finset ι) (u : F → ℚ),
            0 ≤ ∑ i : F, ∑ j : F, (u i : ℝ) * (u j : ℝ) * a i j p}))) := by
    ext p
    constructor
    · rintro ⟨hs, hn, hcs, hsum, hpsd⟩
      exact ⟨hs, hn, hcs, (summable_iff_ofReal hn).1 hsum, hpsd⟩
    · rintro ⟨hs, hn, hcs, hsum, hpsd⟩
      exact ⟨hs, hn, hcs, (summable_iff_ofReal hn).2 hsum, hpsd⟩
  rw [hset]
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

lemma measurable_matForm_apply (e : HilbertBasis ι ℝ H) {α : Type*} [MeasurableSpace α]
    {a : ι → ι → α → ℝ} (ha : ∀ i j, Measurable (a i j)) (x y : H) :
    Measurable fun p => matForm e (fun i j => a i j p) x y := by
  obtain ⟨F, hF⟩ := exists_finset_seq (A := ι)
  have hsq : Tendsto (fun n => F n ×ˢ F n) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun s => ?_
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 hF (s.image Prod.fst ∪ s.image Prod.snd)
    refine ⟨N, fun n hn q hq => ?_⟩
    have := hN n hn
    have h1 : q.1 ∈ F n := this (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
    have h2 : q.2 ∈ F n := this (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
    exact Finset.mem_product.2 ⟨h1, h2⟩
  set S : ℕ → α → ℝ := fun n p => ∑ q ∈ F n ×ˢ F n,
    inner ℝ (e q.1) x * inner ℝ (e q.2) y * a q.1 q.2 p with hS
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Finset.measurable_sum _ fun q _ => measurable_const.mul (ha q.1 q.2)
  have hfun : (fun p => matForm e (fun i j => a i j p) x y) =
      fun p => if GoodMat (fun i j => a i j p) then limsup (fun n => S n p) atTop else 0 := by
    funext p
    by_cases hg : GoodMat (fun i j => a i j p)
    · simp only [hg, if_true]
      rw [matForm_apply hg]
      have hs : Summable (fun q : ι × ι => inner ℝ (e q.1) x * inner ℝ (e q.2) y * a q.1 q.2 p) :=
        ((hg.summable_term e x y).1).of_abs
      exact ((hs.hasSum.comp hsq).limsup_eq).symm
    · simp only [hg, if_false]
      rw [matForm_of_not hg]; rfl
  rw [hfun]
  exact Measurable.ite (measurableSet_goodMat ha) (Measurable.limsup hSm) measurable_const

end MeasMat

section Progressive

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A progressive modification of an entrywise measurable adapted family of trace-class forms. -/
theorem exists_progressive_forms {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (e : HilbertBasis ι ℝ H) (T : ℝ) (Sg : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ)
    (hmeas : ∀ x y, Measurable fun p : ℝ × Ω => Sg p.1 p.2 x y)
    (hadapt : ∀ σ x y, Measurable[ℱ σ] (fun ω => Sg σ ω x y))
    (htc : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc 0 T, IsTraceClassCov (Sg σ ω)) :
    ∃ Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ, (∀ r ω, IsTraceClassCov (Ct r ω)) ∧
      (∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y)) ∧
      ∀ r ∈ Set.Icc 0 T, ∀ᵐ ω ∂P, Ct r ω = Sg r ω := by
  have hex : ∀ i j, ∃ Z : ℝ → Ω → ℝ, IsProgressive ℱ Z ∧
      ∀ t, Z t =ᵐ[P] (fun ω => Sg t ω (e i) (e j)) := fun i j =>
    exists_progressive_modification (P := P) (Y := fun t ω => Sg t ω (e i) (e j))
      (hmeas _ _) (fun t => hadapt t _ _)
  choose Z hZp hZ using hex
  refine ⟨fun r ω => matForm e (fun i j => Z i j r ω), fun r ω => ?_, fun x y i => ?_, ?_⟩
  · by_cases hg : GoodMat (fun i j => Z i j r ω)
    · exact isTraceClassCov_matForm hg
    · simp only [matForm_of_not hg]
      exact isTraceClassCov_zero
  · letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact measurable_matForm_apply e (α := Set.Iic i × Ω)
      (a := fun a b p => Z a b p.1 p.2) (fun a b => hZp a b i) x y
  · intro r hr
    have h1 : ∀ᵐ ω ∂P, ∀ i j, Z i j r ω = Sg r ω (e i) (e j) :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hZ i j r
    have h2 : ∀ᵐ ω ∂P, IsTraceClassCov (Sg r ω) := htc.mono fun ω h => h r hr
    filter_upwards [h1, h2] with ω h1 h2
    have : (fun i j => Z i j r ω) = fun i j => Sg r ω (e i) (e j) := by
      funext i j; exact h1 i j
    show matForm e (fun i j => Z i j r ω) = Sg r ω
    rw [this]
    exact matForm_matrix e h2

end Progressive

end HRS.MRep
