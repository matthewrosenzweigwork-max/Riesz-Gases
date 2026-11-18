import HRS.Uniform.Comparison

/-!
# Lemma 3.29 and Lemma 3.30 (packet Q07): reference-relative covariance cost and the chart current
-/

noncomputable section

open MeasureTheory Filter Topology Matrix MatrixOrder
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace HRS
namespace Uniform
namespace RelCov

section FiniteCore
variable {n : Type*} [Fintype n]


lemma fro_eq_trace (A B : Matrix n n ℝ) (hB : Bᵀ = B) :
    ∑ i, ∑ j, A i j * B i j = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun hB j) i
  simp only [Matrix.transpose_apply] at this
  rw [this]

lemma trace_psd_mul_gram {A : Matrix n n ℝ} (hA : A.PosSemidef) (N : Matrix n n ℝ) :
    0 ≤ (A * (Nᵀ * N)).trace := by
  have h1 : (A * (Nᵀ * N)).trace = (N * A * Nᵀ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h1]
  have := hA.mul_mul_conjTranspose_same N
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.trace_nonneg

variable [DecidableEq n]

/-- The finite-dimensional core: the Bures-type bound along the optimal transport map. -/
theorem core_alg (C D T G : Matrix n n ℝ) (hTs : Tᵀ = T) (hTu : IsUnit T.det)
    (hD : D = T * T) (hG : G.PosSemidef) (hGG : G * G = T * C * T)
    (c : ℝ) (hc : 0 < c) (d : n → ℝ) (hd : ∀ i, 0 < d i)
    (hcmp : (D - c • Matrix.diagonal d).PosSemidef) :
    C.trace + D.trace - 2 * G.trace ≤
      2 * c⁻¹ * ∑ i, ∑ j, (C - D) i j ^ 2 / (d i + d j) := by
  set Ti : Matrix n n ℝ := T⁻¹ with hTi
  have hTiT : Ti * T = 1 := Matrix.nonsing_inv_mul T hTu
  have hTTi : T * Ti = 1 := Matrix.mul_nonsing_inv T hTu
  have hTis : Tiᵀ = Ti := by rw [hTi, Matrix.transpose_nonsing_inv, hTs]
  set Tm : Matrix n n ℝ := Ti * G * Ti with hTm
  have hGs : Gᵀ = G := by
    have := hG.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hTms : Tmᵀ = Tm := by
    rw [hTm, Matrix.transpose_mul, Matrix.transpose_mul, hTis, hGs, Matrix.mul_assoc]
  have hTmpsd : Tm.PosSemidef := by
    have := hG.conjTranspose_mul_mul_same Ti
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hTis] at this
  set N : Matrix n n ℝ := Tm - 1 with hN
  have hNs : Nᵀ = N := by rw [hN, Matrix.transpose_sub, hTms, Matrix.transpose_one]
  have hCeq : C = Tm * D * Tm := by
    have h1 : C = Ti * (T * C * T) * Ti := by
      calc C = (Ti * T) * C * (T * Ti) := by rw [hTiT, hTTi]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
    have h2 : Tm * D * Tm = Ti * (G * G) * Ti := by
      calc Tm * D * Tm = Ti * G * (Ti * T) * (T * Ti) * G * Ti := by
            rw [hTm, hD]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hTiT, hTTi]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    rw [h2, hGG]; exact h1
  have hTmN : Tm = N + 1 := by simp [hN]
  have hDs : Dᵀ = D := by rw [hD, Matrix.transpose_mul, hTs]
  have hΔ : C - D = D * N + N * D + N * D * N := by
    rw [hCeq, hTmN]; noncomm_ring
  -- the squared cost
  have hb2 : C.trace + D.trace - 2 * G.trace = (D * N * N).trace := by
    have e1 : (D * N * N).trace = (D * Tm * Tm).trace - 2 * (D * Tm).trace + D.trace := by
      have : D * N * N = D * Tm * Tm - 2 • (D * Tm) + D := by
        rw [hN]; noncomm_ring
      rw [this, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
      simp
    have e2 : (D * Tm * Tm).trace = C.trace := by
      rw [Matrix.trace_mul_cycle D Tm Tm, ← hCeq]
    have e3 : (D * Tm).trace = G.trace := by
      have : D * Tm = T * G * Ti := by
        calc D * Tm = T * (T * Ti) * G * Ti := by rw [hD, hTm]; simp only [Matrix.mul_assoc]
          _ = _ := by rw [hTTi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [this, Matrix.trace_mul_cycle T G Ti, hTiT, Matrix.one_mul]
    rw [e1, e2, e3]; ring
  have hτ : (( C - D) * N).trace = 2 * (D * N * N).trace + (D * N * N * N).trace := by
    rw [hΔ]
    have : (D * N + N * D + N * D * N) * N = D * N * N + N * D * N + N * D * N * N := by
      noncomm_ring
    rw [this, Matrix.trace_add, Matrix.trace_add]
    have a1 : (N * D * N).trace = (D * N * N).trace := (Matrix.trace_mul_cycle D N N).symm
    have a2 : (N * D * N * N).trace = (D * N * N * N).trace := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm N]
      simp only [Matrix.mul_assoc]
    rw [a1, a2]; ring
  -- positivity of `tr (D N N Tm)`
  have hP : (Nᵀ * Tm * N).PosSemidef := by
    have := hTmpsd.conjTranspose_mul_mul_same N
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hnn : 0 ≤ (D * N * N).trace + (D * N * N * N).trace := by
    have h1 : (D * N * N).trace + (D * N * N * N).trace = (D * (Nᵀ * Tm * N)).trace := by
      rw [hNs, hTmN, ← Matrix.trace_add]
      congr 1
      noncomm_ring
    rw [h1, Matrix.trace_mul_comm]
    have := trace_psd_mul_gram hP T
    rwa [hD, hTs] at *
  -- diagonal weight comparison
  have hcd : c * ∑ i, ∑ j, d i * N i j ^ 2 ≤ (D * N * N).trace := by
    have h1 := trace_psd_mul_gram hcmp N
    rw [hNs, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul] at h1
    have h2 : ∑ i, ∑ j, d i * N i j ^ 2 = (Matrix.diagonal d * (N * N)).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun hNs j) i
      simp only [Matrix.transpose_apply] at this
      rw [this]; ring
    rw [h2]
    simp only [smul_eq_mul] at h1
    rw [Matrix.mul_assoc D N N]
    linarith
  -- termwise AM-GM
  have hterm : ∀ i j, (C - D) i j * N i j - (c / 4) * ((d i + d j) * N i j ^ 2) ≤
      c⁻¹ * ((C - D) i j ^ 2 / (d i + d j)) := by
    intro i j
    have hs : 0 < d i + d j := add_pos (hd i) (hd j)
    have hcs : 0 < c * (d i + d j) := mul_pos hc hs
    have key : c⁻¹ * ((C - D) i j ^ 2 / (d i + d j)) -
        ((C - D) i j * N i j - (c / 4) * ((d i + d j) * N i j ^ 2)) =
        ((C - D) i j - c * (d i + d j) * N i j / 2) ^ 2 / (c * (d i + d j)) := by
      field_simp
      ring
    have : 0 ≤ ((C - D) i j - c * (d i + d j) * N i j / 2) ^ 2 / (c * (d i + d j)) := by positivity
    linarith
  have hamgm : ∑ i, ∑ j, (C - D) i j * N i j - (c / 4) * ∑ i, ∑ j, (d i + d j) * N i j ^ 2 ≤
      c⁻¹ * ∑ i, ∑ j, (C - D) i j ^ 2 / (d i + d j) := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset n)) =>
      Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset n)) => hterm i j
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
    exact h
  have hsym : ∑ i, ∑ j, (d i + d j) * N i j ^ 2 = 2 * ∑ i, ∑ j, d i * N i j ^ 2 := by
    have : ∑ i, ∑ j, (d i + d j) * N i j ^ 2 =
        ∑ i, ∑ j, d i * N i j ^ 2 + ∑ i, ∑ j, d j * N i j ^ 2 := by
      simp only [add_mul, Finset.sum_add_distrib]
    rw [this, Finset.sum_comm (f := fun i j => d j * N i j ^ 2)]
    have h2 : ∑ j, ∑ i, d j * N i j ^ 2 = ∑ i, ∑ j, d i * N i j ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      have := congrFun (congrFun hNs j) i
      simp only [Matrix.transpose_apply] at this
      rw [this]
    rw [h2]; ring
  have hfro : ∑ i, ∑ j, (C - D) i j * N i j = ((C - D) * N).trace := fro_eq_trace _ _ hNs
  rw [hfro, hsym, hτ] at hamgm
  nlinarith [hamgm, hcd, hnn, hb2]



lemma mulVec_dot_mulVec (K : Matrix n n ℝ) (x y : n → ℝ) :
    (K *ᵥ x) ⬝ᵥ (K *ᵥ y) = x ⬝ᵥ ((Kᵀ * K) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm]

theorem svd_lower (G K : Matrix n n ℝ) (hG : G.PosSemidef) (hK : Kᵀ * K = G * G) :
    ∃ (m : ℕ) (u v : Fin m → (n → ℝ)),
      (∀ a b, u a ⬝ᵥ u b = if a = b then 1 else 0) ∧
      (∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0) ∧
      ∑ a, v a ⬝ᵥ (K *ᵥ u a) = G.trace := by
  classical
  set b := hG.1.eigenvectorBasis with hb
  set lam : n → ℝ := hG.1.eigenvalues with hlam
  have hlam0 : ∀ i, 0 ≤ lam i := hG.eigenvalues_nonneg
  have hGb : ∀ i, G *ᵥ (b i).ofLp = lam i • (b i).ofLp := hG.1.mulVec_eigenvectorBasis
  have hon : ∀ i j, (b i).ofLp ⬝ᵥ (b j).ofLp = if i = j then 1 else 0 := by
    intro i j
    have h := orthonormal_iff_ite.1 b.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct_comm] using h
  have hGG : ∀ j, (G * G) *ᵥ (b j).ofLp = (lam j ^ 2) • (b j).ofLp := by
    intro j
    rw [← Matrix.mulVec_mulVec, hGb, Matrix.mulVec_smul, hGb, smul_smul, sq]
  let P := {i : n // 0 < lam i}
  let σ : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  have hKu : ∀ i j, (K *ᵥ (b i).ofLp) ⬝ᵥ (K *ᵥ (b j).ofLp) = (lam j ^ 2) * (if i = j then 1 else 0) := by
    intro i j
    rw [mulVec_dot_mulVec, hK, hGG, dotProduct_smul, hon]; simp
  refine ⟨Fintype.card P, fun a => (b (σ a).1).ofLp,
    fun a => (lam (σ a).1)⁻¹ • (K *ᵥ (b (σ a).1).ofLp), ?_, ?_, ?_⟩
  · intro a c
    rw [hon]
    by_cases h : a = c
    · subst h; simp
    · have : (σ a).1 ≠ (σ c).1 := fun h' => h (σ.injective (Subtype.ext h'))
      simp [h, this]
  · intro a c
    have hpa := (σ a).2
    have hpc := (σ c).2
    rw [smul_dotProduct, dotProduct_smul, hKu]
    by_cases hac : a = c
    · subst hac
      simp only [ite_true, smul_eq_mul]
      field_simp
    · have : (σ a).1 ≠ (σ c).1 := fun h => hac (σ.injective (Subtype.ext h))
      simp [hac, this]
  · have h1 : ∀ a, ((lam (σ a).1)⁻¹ • (K *ᵥ (b (σ a).1).ofLp)) ⬝ᵥ (K *ᵥ (b (σ a).1).ofLp) =
        lam (σ a).1 := by
      intro a
      have hpa := (σ a).2
      rw [smul_dotProduct, hKu]
      simp only [ite_true, smul_eq_mul]
      field_simp
    simp only [h1]
    rw [Equiv.sum_comp σ (fun p : P => lam p.1)]
    rw [hG.1.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [← Finset.sum_filter_of_ne (p := fun i => 0 < lam i) (fun i _ hi => lt_of_le_of_ne (hlam0 i) (Ne.symm hi))]
    exact (Finset.sum_subtype _ (fun i => by simp) (fun i => lam i)).symm

lemma exists_psd_sqrt (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = A := by
  refine ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, ?_⟩
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma psd_symm {A : Matrix n n ℝ} (hA : A.PosSemidef) : Aᵀ = A := by
  have := hA.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma psd_congr_psd {A : Matrix n n ℝ} (hA : A.PosSemidef) (B : Matrix n n ℝ) (hB : Bᵀ = B) :
    (B * A * B).PosSemidef := by
  have := hA.conjTranspose_mul_mul_same B
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hB] at this

lemma mulVec_dot_transpose (A : Matrix n n ℝ) (a b : n → ℝ) :
    (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Aᵀ *ᵥ b) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

lemma mulVec_dot_symm {A : Matrix n n ℝ} (hA : Aᵀ = A) (a b : n → ℝ) :
    (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (A *ᵥ b) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

end FiniteCore

section Bridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*} [DecidableEq ι] (e : HilbertBasis ι ℝ H) (F : Finset ι)

/-- coordinates of `x` along `e_i`, `i ∈ F`. -/
def crd (x : H) : F → ℝ := fun i => inner ℝ (e i : H) x

/-- the vector with coordinates `v` along `e_i`, `i ∈ F`. -/
def vecOf (v : F → ℝ) : H := ∑ i : F, v i • (e i : H)

/-- the finite-rank operator with matrix `M` in the basis `e_F`. -/
def mop (M : Matrix F F ℝ) : H →L[ℝ] H :=
  ∑ i : F, ∑ j : F, M i j • ((innerSL ℝ (e j : H)).smulRight (e i : H))

lemma inner_e_vecOf (v : F → ℝ) (j : F) : inner ℝ (e j : H) (vecOf e F v) = v j := by
  have h := orthonormal_iff_ite.1 e.orthonormal
  simp only [vecOf, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single j]
  · rw [h j j]; simp
  · intro i _ hij
    have : (j : ι) ≠ i := fun h' => hij (Subtype.ext h'.symm)
    rw [h j i]; simp [this]
  · simp

lemma crd_vecOf (v : F → ℝ) : crd e F (vecOf e F v) = v := funext fun j => inner_e_vecOf e F v j

lemma inner_vecOf_left (v : F → ℝ) (x : H) : inner ℝ (vecOf e F v) x = v ⬝ᵥ crd e F x := by
  simp only [vecOf, sum_inner, inner_smul_left, dotProduct, crd, conj_trivial]

lemma inner_vecOf_vecOf (v w : F → ℝ) : inner ℝ (vecOf e F v) (vecOf e F w) = v ⬝ᵥ w := by
  rw [inner_vecOf_left, crd_vecOf]

lemma mop_apply (M : Matrix F F ℝ) (x : H) : mop e F M x = vecOf e F (M *ᵥ crd e F x) := by
  simp only [mop, vecOf, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Matrix.mulVec, dotProduct, crd,
    Finset.sum_smul, smul_smul]

lemma crd_mop (M : Matrix F F ℝ) (x : H) : crd e F (mop e F M x) = M *ᵥ crd e F x := by
  rw [mop_apply, crd_vecOf]

lemma mop_mul (M N : Matrix F F ℝ) : mop e F M * mop e F N = mop e F (M * N) := by
  ext x
  simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, mop_apply, crd_vecOf, Matrix.mulVec_mulVec]

lemma inner_mop (M : Matrix F F ℝ) (x y : H) :
    inner ℝ (mop e F M x) y = (M *ᵥ crd e F x) ⬝ᵥ crd e F y := by
  rw [mop_apply, inner_vecOf_left]

lemma mop_symm {M : Matrix F F ℝ} (hM : Mᵀ = M) (x y : H) :
    inner ℝ (mop e F M x) y = inner ℝ x (mop e F M y) := by
  rw [inner_mop, real_inner_comm, inner_mop, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hM]

lemma mop_nonneg {M : Matrix F F ℝ} (hM : M.PosSemidef) (x : H) :
    0 ≤ inner ℝ (mop e F M x) x := by
  rw [inner_mop, dotProduct_comm]
  simpa using hM.dotProduct_mulVec_nonneg (crd e F x)

/-- the matrix `(C (e_i, e_j))_{i,j ∈ F}` of a bilinear form. -/
def fmat (C : H →L[ℝ] H →L[ℝ] ℝ) : Matrix F F ℝ := Matrix.of fun i j => C (e i) (e j)

lemma form_vecOf (C : H →L[ℝ] H →L[ℝ] ℝ) (v w : F → ℝ) :
    C (vecOf e F v) (vecOf e F w) = v ⬝ᵥ (fmat e F C *ᵥ w) := by
  simp only [vecOf, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, fmat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- the projection onto `span e_F`. -/
abbrev proj : H →L[ℝ] H := mop e F 1

lemma proj_apply (x : H) : proj e F x = vecOf e F (crd e F x) := by
  rw [proj, mop_apply, Matrix.one_mulVec]

/-- the compression `C(Px, Py)` of a bilinear form. -/
def compF (C : H →L[ℝ] H →L[ℝ] ℝ) : H →L[ℝ] H →L[ℝ] ℝ := C.bilinearComp (proj e F) (proj e F)

lemma compF_apply (C : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    compF e F C x y = crd e F x ⬝ᵥ (fmat e F C *ᵥ crd e F y) := by
  simp only [compF, ContinuousLinearMap.bilinearComp_apply, proj_apply, form_vecOf]

end Bridge

section TraceClass

open HilbertCLTAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma exists_isSqrtOfForm {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    ∃ S : H →L[ℝ] H, IsSqrtOfForm S C := by
  have hAp : IsPSDOp (formOp C) :=
    ⟨fun x y => by rw [inner_formOp, real_inner_comm, inner_formOp, hC.symm],
     fun x => by rw [inner_formOp]; exact hC.nonneg x⟩
  have hc : 0 < ‖C‖ + 1 := by positivity
  have hAc : ∀ x, inner ℝ (formOp C x) x ≤ (‖C‖ + 1) * ‖x‖ ^ 2 := by
    intro x
    rw [inner_formOp]
    have h1 := C.le_opNorm₂ x x
    have h2 : (C x) x ≤ ‖C‖ * ‖x‖ * ‖x‖ := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)
    nlinarith [sq_nonneg ‖x‖, norm_nonneg C]
  have hspec := sqrtOp_spec hAp hc hAc
  refine ⟨sqrtOp (‖C‖ + 1) (formOp C), hspec.1.symm, hspec.1.nonneg, fun x y => ?_⟩
  rw [hspec.1.symm x (sqrtOp (‖C‖ + 1) (formOp C) y)]
  have : sqrtOp (‖C‖ + 1) (formOp C) (sqrtOp (‖C‖ + 1) (formOp C) y) = formOp C y := by
    have := congrArg (fun T : H →L[ℝ] H => T y) hspec.2
    simpa using this
  rw [this, real_inner_comm, inner_formOp, hC.symm]

lemma formSqrt_spec {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    IsSqrtOfForm (formSqrt C) C := by
  have h := exists_isSqrtOfForm hC
  simp only [formSqrt, h, dite_true]
  exact h.choose_spec

end TraceClass

section HS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

lemma hasSum_sq_inner (e : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun j => inner ℝ (e j : H) x ^ 2) (‖x‖ ^ 2) := by
  have h := e.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext j
  rw [sq, real_inner_comm x (e j)]

/-- adjoint has the same Hilbert-Schmidt sum -/
lemma hs_adjoint (e : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (hA : Summable fun j => ‖A (e j)‖ ^ 2) :
    Summable (fun j => ‖ContinuousLinearMap.adjoint A (e j)‖ ^ 2) ∧
      ∑' j, ‖ContinuousLinearMap.adjoint A (e j)‖ ^ 2 = ∑' j, ‖A (e j)‖ ^ 2 := by
  classical
  set B := ContinuousLinearMap.adjoint A with hB
  have hf : Summable fun p : ι × ι => (inner ℝ (e p.2 : H) (A (e p.1))) ^ 2 := by
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    refine ⟨fun k => (hasSum_sq_inner e (A (e k))).summable, ?_⟩
    have : ∀ k, ∑' j, (inner ℝ (e j : H) (A (e k))) ^ 2 = ‖A (e k)‖ ^ 2 :=
      fun k => (hasSum_sq_inner e (A (e k))).tsum_eq
    simp only [this]
    exact hA
  have hrow : ∀ j, HasSum (fun k => (inner ℝ (e j : H) (A (e k))) ^ 2) (‖B (e j)‖ ^ 2) := by
    intro j
    have hfun : (fun k => (inner ℝ (e j : H) (A (e k))) ^ 2) =
        fun k => (inner ℝ (e k : H) (B (e j))) ^ 2 := by
      funext k
      rw [hB, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    rw [hfun]
    exact hasSum_sq_inner e (B (e j))
  have hs1 : Summable (fun p : ι × ι => (inner ℝ (e p.1 : H) (A (e p.2))) ^ 2) :=
    hf.prod_symm
  have hs2 : Summable (fun j => ‖B (e j)‖ ^ 2) := by
    have h := ((summable_prod_of_nonneg (fun _ => sq_nonneg _)).1 hs1).2
    refine h.congr fun j => ?_
    exact (hrow j).tsum_eq
  refine ⟨hs2, ?_⟩
  have e1 : ∑' j, ‖B (e j)‖ ^ 2 = ∑' p : ι × ι, (inner ℝ (e p.1 : H) (A (e p.2))) ^ 2 := by
    rw [hs1.tsum_prod' (fun j => (hrow j).summable)]
    exact tsum_congr fun j => (hrow j).tsum_eq.symm
  have e2 : ∑' k, ‖A (e k)‖ ^ 2 = ∑' p : ι × ι, (inner ℝ (e p.2 : H) (A (e p.1))) ^ 2 := by
    rw [hf.tsum_prod' (fun k => (hasSum_sq_inner e (A (e k))).summable)]
    exact tsum_congr fun k => (hasSum_sq_inner e _).tsum_eq.symm
  rw [e1, e2]
  exact (Equiv.prodComm ι ι).tsum_eq (fun p : ι × ι => (inner ℝ (e p.2 : H) (A (e p.1))) ^ 2)

/-- the Hilbert-Schmidt norm is dominated along orthonormal families (Bessel for HS). -/
lemma hs_bessel (e : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (hA : Summable fun j => ‖A (e j)‖ ^ 2)
    {κ : Type*} [Fintype κ] (u : κ → H) (hu : Orthonormal ℝ u) :
    ∑ i, ‖A (u i)‖ ^ 2 ≤ ∑' j, ‖A (e j)‖ ^ 2 := by
  classical
  obtain ⟨hB, hBe⟩ := hs_adjoint e A hA
  set B := ContinuousLinearMap.adjoint A with hBdef
  have h1 : ∀ i, HasSum (fun j => (inner ℝ (B (e j)) (u i)) ^ 2) (‖A (u i)‖ ^ 2) := by
    intro i
    convert hasSum_sq_inner e (A (u i)) using 2 with j
    rw [hBdef, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have h2 : ∑ i, ‖A (u i)‖ ^ 2 = ∑' j, ∑ i, (inner ℝ (B (e j)) (u i)) ^ 2 := by
    rw [Summable.tsum_finsetSum fun i _ => (h1 i).summable]
    exact Finset.sum_congr rfl fun i _ => (h1 i).tsum_eq.symm
  rw [h2, ← hBe]
  refine Summable.tsum_le_tsum (fun j => ?_) ?_ hB
  · have := hu.sum_inner_products_le (B (e j)) (s := Finset.univ)
    simp only [Real.norm_eq_abs, sq_abs] at this
    simpa [real_inner_comm] using this
  · exact summable_sum fun i _ => (h1 i).summable.congr fun j => rfl

lemma sum_abs_inner_le (e : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : Summable fun j => ‖A (e j)‖ ^ 2) (hB : Summable fun j => ‖B (e j)‖ ^ 2)
    {m : ℕ} (u v : Fin m → H) (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∑ i, |inner ℝ (A (u i)) (B (v i))| ≤
      Real.sqrt (∑' j, ‖A (e j)‖ ^ 2) * Real.sqrt (∑' j, ‖B (e j)‖ ^ 2) := by
  calc ∑ i, |inner ℝ (A (u i)) (B (v i))| ≤ ∑ i, ‖A (u i)‖ * ‖B (v i)‖ :=
        Finset.sum_le_sum fun i _ => (abs_real_inner_le_norm _ _)
    _ ≤ Real.sqrt (∑ i, ‖A (u i)‖ ^ 2) * Real.sqrt (∑ i, ‖B (v i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := by
        gcongr
        · exact hs_bessel e A hA u hu
        · exact hs_bessel e B hB v hv



end HS

section CompF

open HilbertCLTAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [DecidableEq ι] (e : HilbertBasis ι ℝ H) (F : Finset ι)

lemma compF_apply' (C : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    compF e F C x y = C (proj e F x) (proj e F y) := rfl

lemma fmat_posSemidef {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    (fmat e F C).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp [fmat, hC.symm (e j) (e i)]
  · have := hC.nonneg (vecOf e F v)
    rw [form_vecOf] at this
    simpa [dotProduct_comm] using this

lemma isTraceClassCov_compF {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    IsTraceClassCov (compF e F C) := by
  refine ⟨fun x y => hC.symm _ _, fun x => hC.nonneg _, ?_⟩
  obtain ⟨κ, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  refine ⟨κ, b, ?_⟩
  have h : ∀ k l : F, Summable fun i => inner ℝ (e k : H) (b i) * inner ℝ (e l : H) (b i) := by
    intro k l
    refine (b.hasSum_inner_mul_inner (e k) (e l)).summable.congr fun i => ?_
    rw [real_inner_comm (b i) (e l)]
  have : (fun i => compF e F C (b i) (b i)) = fun i =>
      ∑ k : F, ∑ l : F, fmat e F C k l * (inner ℝ (e k : H) (b i) * inner ℝ (e l : H) (b i)) := by
    funext i
    rw [compF_apply]
    simp only [dotProduct, Matrix.mulVec, crd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this]
  exact summable_sum fun k _ => summable_sum fun l _ => (h k l).mul_left _

lemma proj_e (j : ι) : proj e F (e j : H) = if j ∈ F then (e j : H) else 0 := by
  have h := orthonormal_iff_ite.1 e.orthonormal
  rw [proj_apply]
  simp only [vecOf, crd, h]
  have : ∑ i : F, (if (i : ι) = j then (1 : ℝ) else 0) • (e i : H) =
      ∑ i ∈ F, (if i = j then (1 : ℝ) else 0) • (e i : H) :=
    Finset.sum_coe_sort F (fun i => (if i = j then (1 : ℝ) else 0) • (e i : H))
  rw [this]
  simp [ite_smul, Finset.sum_ite_eq']

lemma compF_e (C : H →L[ℝ] H →L[ℝ] ℝ) (j : ι) :
    compF e F C (e j) (e j) = if j ∈ F then C (e j) (e j) else 0 := by
  rw [compF_apply', proj_e]
  split_ifs <;> simp


lemma summable_tail (a : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha : Summable a) :
    Summable (fun j => if j ∈ F then (0 : ℝ) else a j) :=
  ha.of_nonneg_of_le (fun j => by split_ifs <;> simp [ha0 j]) (fun j => by split_ifs <;> simp [ha0 j])

lemma summable_head (a : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha : Summable a) :
    Summable (fun j => if j ∈ F then a j else (0 : ℝ)) :=
  ha.of_nonneg_of_le (fun j => by split_ifs <;> simp [ha0 j]) (fun j => by split_ifs <;> simp [ha0 j])

/-- the trace norm of `C - C_F` is small: `‖C - C_F‖₁ ≤ 2 ‖S‖₂ (∑_{j ∉ F} ‖S e_j‖²)^{1/2}`. -/
lemma traceNormForm_sub_compF_le {C : H →L[ℝ] H →L[ℝ] ℝ} {S : H →L[ℝ] H} (hS : IsSqrtOfForm S C)
    (hSs : Summable fun j => ‖S (e j)‖ ^ 2) :
    traceNormForm (C - compF e F C) ≤
      2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) *
        Real.sqrt (∑' j, (if j ∈ F then (0 : ℝ) else ‖S (e j)‖ ^ 2)) := by
  set Q : H →L[ℝ] H := 1 - proj e F with hQ
  have hQe : ∀ j, Q (e j) = if j ∈ F then 0 else (e j : H) := by
    intro j
    rw [hQ, _root_.sub_apply, one_apply_eq_self, proj_e]
    split_ifs <;> simp
  have hsQ : Summable fun j => ‖(S.comp Q) (e j)‖ ^ 2 := by
    refine (summable_tail F _ (fun j => by positivity) hSs).congr fun j => ?_
    simp only [ContinuousLinearMap.comp_apply, hQe]
    split_ifs <;> simp
  have hsQ' : ∑' j, ‖(S.comp Q) (e j)‖ ^ 2 = ∑' j, (if j ∈ F then (0 : ℝ) else ‖S (e j)‖ ^ 2) := by
    refine tsum_congr fun j => ?_
    simp only [ContinuousLinearMap.comp_apply, hQe]
    split_ifs <;> simp
  have hsP : Summable fun j => ‖(S.comp (proj e F)) (e j)‖ ^ 2 := by
    refine (summable_head F _ (fun j => by positivity) hSs).congr fun j => ?_
    simp only [ContinuousLinearMap.comp_apply, proj_e]
    split_ifs <;> simp
  have hsP' : ∑' j, ‖(S.comp (proj e F)) (e j)‖ ^ 2 ≤ ∑' j, ‖S (e j)‖ ^ 2 := by
    refine Summable.tsum_le_tsum (fun j => ?_) hsP hSs
    simp only [ContinuousLinearMap.comp_apply, proj_e]
    split_ifs <;> simp
  have hcomp : ∀ x y, (C - compF e F C) x y =
      inner ℝ ((S.comp Q) x) (S y) + inner ℝ ((S.comp (proj e F)) x) ((S.comp Q) y) := by
    intro x y
    have hx : S x = (S.comp (proj e F)) x + (S.comp Q) x := by
      simp [hQ]
    have hy : S y = (S.comp (proj e F)) y + (S.comp Q) y := by
      simp [hQ]
    rw [_root_.sub_apply, _root_.sub_apply, compF_apply', ← hS.sq, ← hS.sq]
    simp only [ContinuousLinearMap.comp_apply] at hx hy ⊢
    rw [hx, hy]
    simp only [inner_add_left, inner_add_right]
    ring
  have hsqrt := Real.sqrt_nonneg (∑' j, ‖S (e j)‖ ^ 2)
  refine Real.iSup_le (fun p => ?_) (by positivity)
  have h1 := sum_abs_inner_le e (S.comp Q) S hsQ hSs p.1.2.1 p.1.2.2 p.2.1 p.2.2
  have h2 := sum_abs_inner_le e (S.comp (proj e F)) (S.comp Q) hsP hsQ p.1.2.1 p.1.2.2 p.2.1 p.2.2
  rw [hsQ'] at h1 h2
  have hnn := Real.sqrt_nonneg (∑' j, (if j ∈ F then (0 : ℝ) else ‖S (e j)‖ ^ 2))
  calc ∑ i, |(C - compF e F C) (p.1.2.1 i) (p.1.2.2 i)|
      ≤ ∑ i, (|inner ℝ ((S.comp Q) (p.1.2.1 i)) (S (p.1.2.2 i))| +
          |inner ℝ ((S.comp (proj e F)) (p.1.2.1 i)) ((S.comp Q) (p.1.2.2 i))|) :=
        Finset.sum_le_sum fun i _ => by rw [hcomp]; exact abs_add_le _ _
    _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        have := Real.sqrt_le_sqrt hsP'
        nlinarith [mul_le_mul_of_nonneg_right this hnn]


/-- Lower bound for the trace norm of the form `(x,y) ↦ ⟨T S x, y⟩` (`T` symmetric): its sum along
orthonormal pairs. -/
lemma sum_inner_le_traceNormForm (e : HilbertBasis ι ℝ H) (S T : H →L[ℝ] H)
    (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hSs : Summable fun j => ‖S (e j)‖ ^ 2) (hTs : Summable fun j => ‖T (e j)‖ ^ 2)
    {m : ℕ} (u v : Fin m → H) (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∑ a, inner ℝ (T (S (u a))) (v a) ≤ traceNormForm ((innerSL ℝ).comp (T.comp S)) := by
  have hform : ∀ x y, ((innerSL ℝ).comp (T.comp S)) x y = inner ℝ (S x) (T y) := by
    intro x y
    simp [hT]
  have hb : BddAbove (Set.range fun p : OrthonormalPairs H =>
      ∑ i, |((innerSL ℝ).comp (T.comp S)) (p.1.2.1 i) (p.1.2.2 i)|) := by
    refine ⟨Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (∑' j, ‖T (e j)‖ ^ 2), ?_⟩
    rintro _ ⟨p, rfl⟩
    simp only [hform]
    exact sum_abs_inner_le e S T hSs hTs p.1.2.1 p.1.2.2 p.2.1 p.2.2
  have := pairSum_le_traceNormForm hb ⟨⟨m, u, v⟩, ⟨hu, hv⟩⟩
  simp only [hform] at this
  refine le_trans ?_ (by simpa only [hform] using this)
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hT]
  exact le_abs_self _

lemma sq_norm_eq_diag {C : H →L[ℝ] H →L[ℝ] ℝ} {S : H →L[ℝ] H} (hS : IsSqrtOfForm S C) (x : H) :
    ‖S x‖ ^ 2 = C x x := by
  rw [← hS.sq, real_inner_self_eq_norm_sq]

lemma summable_sqrt_diag {C : H →L[ℝ] H →L[ℝ] ℝ} {S : H →L[ℝ] H} (hS : IsSqrtOfForm S C)
    (hC : IsTraceClassCov C) : Summable fun j => ‖S (e j)‖ ^ 2 := by
  obtain ⟨T, hT, -⟩ := hC.hasSum_basis e
  exact hT.summable.congr fun j => (sq_norm_eq_diag hS _).symm

lemma summable_compF_diag {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    Summable fun j => compF e F C (e j) (e j) := by
  obtain ⟨T, hT, -⟩ := hC.hasSum_basis e
  refine (summable_head F _ (fun j => hC.nonneg _) hT.summable).congr fun j => ?_
  rw [compF_e]

/-- Hilbert-Schmidt distance of a square root to its finite-rank approximant. -/
lemma hs_sub_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {S S' : H →L[ℝ] H}
    (hS : IsSqrtOfForm S C) (hS' : IsSqrtOfForm S' (compF e F C)) :
    Summable (fun j => ‖(S - S') (e j)‖ ^ 2) ∧
      ∑' j, ‖(S - S') (e j)‖ ^ 2 ≤ 2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) *
        Real.sqrt (∑' j, (if j ∈ F then (0 : ℝ) else ‖S (e j)‖ ^ 2)) := by
  obtain ⟨T, hT, -⟩ := hC.hasSum_basis e
  have := powers_stormer e hS hS' hC (isTraceClassCov_compF e F hC) hT.summable
    (summable_compF_diag e F hC)
  exact ⟨this.1, this.2.trans (traceNormForm_sub_compF_le e F hS (summable_sqrt_diag e hS hC))⟩

lemma hs_compF_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {S S' : H →L[ℝ] H}
    (hS : IsSqrtOfForm S C) (hS' : IsSqrtOfForm S' (compF e F C)) :
    Summable (fun j => ‖S' (e j)‖ ^ 2) ∧ ∑' j, ‖S' (e j)‖ ^ 2 ≤ ∑' j, ‖S (e j)‖ ^ 2 := by
  have h1 := summable_compF_diag e F hC
  have h2 := summable_sqrt_diag e hS hC
  refine ⟨h1.congr fun j => (sq_norm_eq_diag hS' _).symm, ?_⟩
  refine Summable.tsum_le_tsum (fun j => ?_) (h1.congr fun j => (sq_norm_eq_diag hS' _).symm) h2
  rw [sq_norm_eq_diag hS', sq_norm_eq_diag hS, compF_e]
  split_ifs
  · exact le_rfl
  · exact hC.nonneg _

lemma fmat_diag_form (D₀ : H →L[ℝ] H →L[ℝ] ℝ) (dd : ι → ℝ)
    (hD₀e : ∀ i y, D₀ (e i) y = dd i * inner ℝ (e i : H) y) :
    fmat e F D₀ = Matrix.diagonal (fun i : F => dd i) := by
  ext i j
  have h := orthonormal_iff_ite.1 e.orthonormal
  simp only [fmat, Matrix.of_apply, hD₀e, h, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have : (i : ι) ≠ j := fun h' => hij (Subtype.ext h')
    simp [hij, this]

lemma compare_psd {D D₀ : H →L[ℝ] H →L[ℝ] ℝ} (hD : IsTraceClassCov D) (dd : ι → ℝ)
    (hD₀e : ∀ i y, D₀ (e i) y = dd i * inner ℝ (e i : H) y) (c : ℝ)
    (hcD : ∀ x, c * D₀ x x ≤ D x x) :
    (fmat e F D - c • Matrix.diagonal (fun i : F => dd i)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [fmat, Matrix.of_apply, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, hD.symm (e j) (e i)]
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
      exact hD.symm _ _
  · have h1 := hcD (vecOf e F v)
    have h2 : D₀ (vecOf e F v) (vecOf e F v) = v ⬝ᵥ (Matrix.diagonal (fun i : F => dd i) *ᵥ v) := by
      rw [form_vecOf, fmat_diag_form e F D₀ dd hD₀e]
    rw [h2, form_vecOf] at h1
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
    simp only [star_trivial, smul_eq_mul]
    linarith

/-- the tail of the Hilbert-Schmidt sum of `S` outside `F`. -/
def tailS (S : H →L[ℝ] H) (F : Finset ι) : ℝ :=
  ∑' j, (if j ∈ F then (0 : ℝ) else ‖S (e j)‖ ^ 2)

/-- the approximation error in the trace-norm lower bound. -/
def epsF (S T : H →L[ℝ] H) (F : Finset ι) : ℝ :=
  Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (2 * Real.sqrt (∑' j, ‖T (e j)‖ ^ 2) *
      Real.sqrt (tailS e T F)) +
    Real.sqrt (2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (tailS e S F)) *
      Real.sqrt (∑' j, ‖T (e j)‖ ^ 2)

/-- Finite-dimensional lower bound for the trace norm of `√D √C` (compression to `e_F`). -/
theorem lower_bound_F {C D : H →L[ℝ] H →L[ℝ] ℝ} (dd : ι → ℝ) (hdd : ∀ i, 0 < dd i)
    (D₀ : H →L[ℝ] H →L[ℝ] ℝ) (hD₀e : ∀ i y, D₀ (e i) y = dd i * inner ℝ (e i : H) y)
    (c : ℝ) (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x)
    (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) (q : ℝ)
    (hq : ∑ i ∈ F, ∑ j ∈ F, (C - D) (e i) (e j) ^ 2 / (dd i + dd j) ≤ q) :
    (1 / 2) * (∑ i ∈ F, C (e i) (e i) + ∑ i ∈ F, D (e i) (e i)) - c⁻¹ * q -
        epsF e (formSqrt C) (formSqrt D) F ≤
      traceNormForm ((innerSL ℝ).comp ((formSqrt D).comp (formSqrt C))) := by
  classical
  set S := formSqrt C with hSdef
  set T := formSqrt D with hTdef
  have hS : IsSqrtOfForm S C := formSqrt_spec hC
  have hT : IsSqrtOfForm T D := formSqrt_spec hD
  have hSs := summable_sqrt_diag e hS hC
  have hTs := summable_sqrt_diag e hT hD
  set Cm := fmat e F C with hCmdef
  set Dm := fmat e F D with hDmdef
  have hCm : Cm.PosSemidef := fmat_posSemidef e F hC
  have hcmp := compare_psd e F hD dd hD₀e c hcD
  have hDm : Dm.PosDef := by
    have h1 : (c • Matrix.diagonal (fun i : F => dd i)).PosDef := by
      refine Matrix.PosDef.smul ?_ hc
      exact Matrix.PosDef.diagonal (fun i => hdd i)
    have := h1.add_posSemidef hcmp
    rwa [add_sub_cancel] at this
  have hDm0 : Dm.PosSemidef := hDm.posSemidef
  obtain ⟨Sx, hSxp, hSxSx⟩ := exists_psd_sqrt Cm hCm
  obtain ⟨Tx, hTxp, hTxTx⟩ := exists_psd_sqrt Dm hDm0
  have hTxs : Txᵀ = Tx := psd_symm hTxp
  have hSxs : Sxᵀ = Sx := psd_symm hSxp
  have hTxu : IsUnit Tx.det := by
    have h1 : Tx.det * Tx.det = Dm.det := by rw [← Matrix.det_mul, hTxTx]
    have h2 : Dm.det ≠ 0 := (Matrix.PosDef.det_pos hDm).ne'
    have : IsUnit (Tx.det * Tx.det) := by rw [h1]; exact (Matrix.isUnit_iff_isUnit_det Dm).1 hDm.isUnit
    exact (IsUnit.mul_iff.1 this).1
  have hCTC : (Tx * Cm * Tx).PosSemidef := psd_congr_psd hCm Tx hTxs
  obtain ⟨Gm, hGp, hGG⟩ := exists_psd_sqrt _ hCTC
  have hcore := core_alg Cm Dm Tx Gm hTxs hTxu hTxTx.symm hGp hGG c hc (fun i : F => dd i)
    (fun i => hdd i) hcmp
  have hK : (Sx * Tx)ᵀ * (Sx * Tx) = Gm * Gm := by
    rw [hGG, Matrix.transpose_mul, hTxs, hSxs, ← hSxSx]
    simp only [Matrix.mul_assoc]
  obtain ⟨m, u, v, hu, hv, hsum⟩ := svd_lower Gm (Sx * Tx) hGp hK
  -- the finite-rank approximants
  set SF : H →L[ℝ] H := mop e F Sx with hSFdef
  set TF : H →L[ℝ] H := mop e F Tx with hTFdef
  have hSF : IsSqrtOfForm SF (compF e F C) := by
    refine ⟨mop_symm e F hSxs, mop_nonneg e F hSxp, fun x y => ?_⟩
    rw [hSFdef, inner_mop, crd_mop, compF_apply, mulVec_dot_mulVec, hSxs, hSxSx]
  have hTF : IsSqrtOfForm TF (compF e F D) := by
    refine ⟨mop_symm e F hTxs, mop_nonneg e F hTxp, fun x y => ?_⟩
    rw [hTFdef, inner_mop, crd_mop, compF_apply, mulVec_dot_mulVec, hTxs, hTxTx]
  -- the orthonormal families
  set xx : Fin m → H := fun a => vecOf e F (v a) with hxx
  set yy : Fin m → H := fun a => vecOf e F (u a) with hyy
  have hxo : Orthonormal ℝ xx := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [hxx]; simp only []
    rw [inner_vecOf_vecOf, hv]
  have hyo : Orthonormal ℝ yy := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [hyy]; simp only []
    rw [inner_vecOf_vecOf, hu]
  have hlow := sum_inner_le_traceNormForm e S T hT.symm hSs hTs xx yy hxo hyo
  -- main term
  have hmain : ∑ a, inner ℝ (TF (SF (xx a))) (yy a) = Gm.trace := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hTFdef, hSFdef, hxx, hyy]
    simp only [mop_apply, crd_vecOf, inner_vecOf_vecOf, Matrix.mulVec_mulVec]
    rw [mulVec_dot_transpose, Matrix.transpose_mul, hTxs, hSxs]
  -- error terms
  have hdecomp : ∀ a, inner ℝ (T (S (xx a))) (yy a) = inner ℝ (TF (SF (xx a))) (yy a) +
      inner ℝ (S (xx a)) ((T - TF) (yy a)) + inner ℝ ((S - SF) (xx a)) (TF (yy a)) := by
    intro a
    rw [hT.symm, hTF.symm]
    simp only [_root_.sub_apply, inner_sub_left, inner_sub_right]
    ring
  obtain ⟨hHT1, hHT2⟩ := hs_sub_le e F hD hT hTF
  obtain ⟨hHS1, hHS2⟩ := hs_sub_le e F hC hS hSF
  obtain ⟨hHF1, hHF2⟩ := hs_compF_le e F hD hT hTF
  have herr1 := sum_abs_inner_le e S (T - TF) hSs hHT1 xx yy hxo hyo
  have herr2 := sum_abs_inner_le e (S - SF) TF hHS1 hHF1 xx yy hxo hyo
  have hsum_lb : Gm.trace - (Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) *
        Real.sqrt (∑' j, ‖(T - TF) (e j)‖ ^ 2) +
      Real.sqrt (∑' j, ‖(S - SF) (e j)‖ ^ 2) * Real.sqrt (∑' j, ‖TF (e j)‖ ^ 2)) ≤
      ∑ a, inner ℝ (T (S (xx a))) (yy a) := by
    rw [← hmain]
    simp only [hdecomp, Finset.sum_add_distrib]
    have h1 : -(∑ a, |inner ℝ (S (xx a)) ((T - TF) (yy a))|) ≤
        ∑ a, inner ℝ (S (xx a)) ((T - TF) (yy a)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun a _ => neg_abs_le _
    have h2 : -(∑ a, |inner ℝ ((S - SF) (xx a)) (TF (yy a))|) ≤
        ∑ a, inner ℝ ((S - SF) (xx a)) (TF (yy a)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun a _ => neg_abs_le _
    linarith
  have htr : Cm.trace = ∑ i ∈ F, C (e i) (e i) := by
    simp only [Matrix.trace, Matrix.diag, hCmdef, fmat, Matrix.of_apply]
    exact Finset.sum_coe_sort F (fun i => C (e i) (e i))
  have htrD : Dm.trace = ∑ i ∈ F, D (e i) (e i) := by
    simp only [Matrix.trace, Matrix.diag, hDmdef, fmat, Matrix.of_apply]
    exact Finset.sum_coe_sort F (fun i => D (e i) (e i))
  have hQF : ∑ i : F, ∑ j : F, (Cm - Dm) i j ^ 2 / (dd i + dd j) =
      ∑ i ∈ F, ∑ j ∈ F, (C - D) (e i) (e j) ^ 2 / (dd i + dd j) := by
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hCmdef, hDmdef, fmat]
  have hG : (1 / 2) * (∑ i ∈ F, C (e i) (e i) + ∑ i ∈ F, D (e i) (e i)) - c⁻¹ * q ≤ Gm.trace := by
    have h1 := hcore
    rw [hQF, htr, htrD] at h1
    have hc' : 0 ≤ c⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq hc']
  have he1 : Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (∑' j, ‖(T - TF) (e j)‖ ^ 2) ≤
      Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (2 * Real.sqrt (∑' j, ‖T (e j)‖ ^ 2) *
        Real.sqrt (tailS e T F)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHT2) (Real.sqrt_nonneg _)
  have he2 : Real.sqrt (∑' j, ‖(S - SF) (e j)‖ ^ 2) * Real.sqrt (∑' j, ‖TF (e j)‖ ^ 2) ≤
      Real.sqrt (2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (tailS e S F)) *
        Real.sqrt (∑' j, ‖T (e j)‖ ^ 2) :=
    mul_le_mul (Real.sqrt_le_sqrt hHS2) (Real.sqrt_le_sqrt hHF2) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have : epsF e S T F = Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (2 * Real.sqrt (∑' j, ‖T (e j)‖ ^ 2) *
        Real.sqrt (tailS e T F)) +
      Real.sqrt (2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) * Real.sqrt (tailS e S F)) *
        Real.sqrt (∑' j, ‖T (e j)‖ ^ 2) := rfl
  rw [this] at *
  linarith


lemma tailS_eq {S : H →L[ℝ] H} (hSs : Summable fun j => ‖S (e j)‖ ^ 2) (F : Finset ι) :
    tailS e S F = ∑' j, ‖S (e j)‖ ^ 2 - ∑ j ∈ F, ‖S (e j)‖ ^ 2 := by
  have h1 : HasSum (fun j => if j ∈ F then ‖S (e j)‖ ^ 2 else (0 : ℝ))
      (∑ j ∈ F, ‖S (e j)‖ ^ 2) := by
    have : HasSum (fun j => if j ∈ F then ‖S (e j)‖ ^ 2 else (0 : ℝ))
        (∑ j ∈ F, if j ∈ F then ‖S (e j)‖ ^ 2 else (0 : ℝ)) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hj])
    simpa [Finset.sum_ite_mem, Finset.inter_self] using this
  have h2 := hSs.hasSum.sub h1
  rw [tailS, ← h2.tsum_eq]
  refine tsum_congr fun j => ?_
  split_ifs <;> simp

lemma tendsto_tailS {S : H →L[ℝ] H} (hSs : Summable fun j => ‖S (e j)‖ ^ 2) :
    Tendsto (fun F : Finset ι => tailS e S F) atTop (𝓝 0) := by
  have h0 := hSs.hasSum
  have h : Tendsto (fun F : Finset ι => ∑ j ∈ F, ‖S (e j)‖ ^ 2) atTop
      (𝓝 (∑' j, ‖S (e j)‖ ^ 2)) := h0
  have := (tendsto_const_nhds (x := ∑' j, ‖S (e j)‖ ^ 2)).sub h
  simp only [sub_self] at this
  refine this.congr fun F => ?_
  rw [tailS_eq e hSs]

lemma tendsto_epsF {S T : H →L[ℝ] H} (hSs : Summable fun j => ‖S (e j)‖ ^ 2)
    (hTs : Summable fun j => ‖T (e j)‖ ^ 2) :
    Tendsto (fun F : Finset ι => epsF e S T F) atTop (𝓝 0) := by
  have h1 := tendsto_tailS e hSs
  have h2 := tendsto_tailS e hTs
  have h1' := (Real.continuous_sqrt.tendsto 0).comp h1
  have h2' := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h1' h2'
  have a1 : Tendsto (fun F : Finset ι => Real.sqrt (2 * Real.sqrt (∑' j, ‖T (e j)‖ ^ 2) *
      Real.sqrt (tailS e T F))) atTop (𝓝 0) := by
    have hm := (tendsto_const_nhds (x := 2 * Real.sqrt (∑' j, ‖T (e j)‖ ^ 2))).mul h2'
    rw [mul_zero] at hm
    have := (Real.continuous_sqrt.tendsto 0).comp hm
    rw [Real.sqrt_zero] at this
    exact this
  have a2 : Tendsto (fun F : Finset ι => Real.sqrt (2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2) *
      Real.sqrt (tailS e S F))) atTop (𝓝 0) := by
    have hm := (tendsto_const_nhds (x := 2 * Real.sqrt (∑' j, ‖S (e j)‖ ^ 2))).mul h1'
    rw [mul_zero] at hm
    have := (Real.continuous_sqrt.tendsto 0).comp hm
    rw [Real.sqrt_zero] at this
    exact this
  have := ((tendsto_const_nhds (x := Real.sqrt (∑' j, ‖S (e j)‖ ^ 2))).mul a1).add
    (a2.mul (tendsto_const_nhds (x := Real.sqrt (∑' j, ‖T (e j)‖ ^ 2))))
  simpa [epsF] using this
/-- The Bures-type bound, real form. -/
theorem bures2_le_real {C D : H →L[ℝ] H →L[ℝ] ℝ} (dd : ι → ℝ) (hdd : ∀ i, 0 < dd i)
    (D₀ : H →L[ℝ] H →L[ℝ] ℝ) (hD₀e : ∀ i y, D₀ (e i) y = dd i * inner ℝ (e i : H) y)
    (c : ℝ) (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x)
    (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) (q : ℝ)
    (hq : ∀ F : Finset ι, ∑ i ∈ F, ∑ j ∈ F, (C - D) (e i) (e j) ^ 2 / (dd i + dd j) ≤ q) :
    Uniform.bures2 C D ≤ 2 * c⁻¹ * q := by
  classical
  set S := formSqrt C with hSdef
  set T := formSqrt D with hTdef
  have hS : IsSqrtOfForm S C := formSqrt_spec hC
  have hT : IsSqrtOfForm T D := formSqrt_spec hD
  have hSs := summable_sqrt_diag e hS hC
  have hTs := summable_sqrt_diag e hT hD
  obtain ⟨tC, hCt, -⟩ := hC.hasSum_basis e
  obtain ⟨tD, hDt, -⟩ := hD.hasSum_basis e
  have hnC : traceNormForm C = tC :=
    le_antisymm ((traceNormForm_le_basis_trace hC e).trans hCt.tsum_eq.le)
      (hCt.tsum_eq ▸ hC.tsum_basis_le e)
  have hnD : traceNormForm D = tD :=
    le_antisymm ((traceNormForm_le_basis_trace hD e).trans hDt.tsum_eq.le)
      (hDt.tsum_eq ▸ hD.tsum_basis_le e)
  have hbound : ∀ F : Finset ι, Uniform.bures2 C D ≤
      (tC - ∑ i ∈ F, C (e i) (e i)) + (tD - ∑ i ∈ F, D (e i) (e i)) + 2 * c⁻¹ * q +
        2 * epsF e S T F := by
    intro F
    have h := lower_bound_F e F dd hdd D₀ hD₀e c hc hcD hC hD q (hq F)
    unfold Uniform.bures2
    rw [hnC, hnD]
    linarith
  have hlim : Tendsto (fun F : Finset ι => (tC - ∑ i ∈ F, C (e i) (e i)) +
      (tD - ∑ i ∈ F, D (e i) (e i)) + 2 * c⁻¹ * q + 2 * epsF e S T F) atTop
      (𝓝 ((tC - tC) + (tD - tD) + 2 * c⁻¹ * q + 2 * 0)) := by
    have a1 : Tendsto (fun F : Finset ι => ∑ i ∈ F, C (e i) (e i)) atTop (𝓝 tC) := hCt
    have a2 : Tendsto (fun F : Finset ι => ∑ i ∈ F, D (e i) (e i)) atTop (𝓝 tD) := hDt
    exact (((tendsto_const_nhds.sub a1).add (tendsto_const_nhds.sub a2)).add
      tendsto_const_nhds).add ((tendsto_epsF e hSs hTs).const_mul 2)
  have := ge_of_tendsto' hlim hbound
  simpa using this

theorem bures2_le {C D : H →L[ℝ] H →L[ℝ] ℝ} (dd : ι → ℝ) (hdd : ∀ i, 0 < dd i)
    (D₀ : H →L[ℝ] H →L[ℝ] ℝ) (hD₀e : ∀ i y, D₀ (e i) y = dd i * inner ℝ (e i : H) y)
    (c : ℝ) (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x)
    (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) :
    ENNReal.ofReal (Uniform.bures2 C D) ≤
      2 * ENNReal.ofReal c⁻¹ * Uniform.relQuad e dd (C - D) := by
  by_cases htop : Uniform.relQuad e dd (C - D) = ⊤
  · rw [htop]
    have : (2 : ℝ≥0∞) * ENNReal.ofReal c⁻¹ ≠ 0 := by
      refine mul_ne_zero (by norm_num) ?_
      simpa using hc
    rw [ENNReal.mul_top this]
    exact le_top
  · set q := (Uniform.relQuad e dd (C - D)).toReal with hqdef
    have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
    have hqe : Uniform.relQuad e dd (C - D) = ENNReal.ofReal q := (ENNReal.ofReal_toReal htop).symm
    have hqF : ∀ F : Finset ι, ∑ i ∈ F, ∑ j ∈ F, (C - D) (e i) (e j) ^ 2 / (dd i + dd j) ≤ q := by
      intro F
      have hnn : ∀ p : ι × ι, 0 ≤ (C - D) (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2) := fun p =>
        div_nonneg (sq_nonneg _) (add_pos (hdd _) (hdd _)).le
      have h1 : ∑ p ∈ F ×ˢ F, ENNReal.ofReal ((C - D) (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2)) ≤
          Uniform.relQuad e dd (C - D) := ENNReal.sum_le_tsum _
      rw [hqe, ← ENNReal.ofReal_sum_of_nonneg (fun p _ => hnn p),
        ENNReal.ofReal_le_ofReal_iff hq0] at h1
      rw [Finset.sum_product] at h1
      exact h1
    have hr := bures2_le_real e dd hdd D₀ hD₀e c hc hcD hC hD q hqF
    calc ENNReal.ofReal (Uniform.bures2 C D) ≤ ENNReal.ofReal (2 * c⁻¹ * q) :=
          ENNReal.ofReal_le_ofReal hr
      _ = 2 * ENNReal.ofReal c⁻¹ * Uniform.relQuad e dd (C - D) := by
          rw [hqe, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp


end CompF

section Compare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι κ : Type*}

/-- expansion of a bounded bilinear form in the first slot. -/
lemma hasSum_form_left (e₀ : HilbertBasis κ ℝ H) (Δ : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    HasSum (fun k => inner ℝ (e₀ k : H) x * Δ (e₀ k) y) (Δ x y) := by
  have h := e₀.hasSum_repr x
  have := h.mapL ((ContinuousLinearMap.apply ℝ ℝ y).comp Δ)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, map_smul,
    HilbertBasis.repr_apply_apply, smul_eq_mul] at this
  exact this

/-- expansion of a bounded bilinear form in the second slot. -/
lemma hasSum_form_right (e₀ : HilbertBasis κ ℝ H) (Δ : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    HasSum (fun k => inner ℝ (e₀ k : H) y * Δ x (e₀ k)) (Δ x y) := by
  have h := e₀.hasSum_repr y
  have := h.mapL (Δ x)
  simp only [map_smul, HilbertBasis.repr_apply_apply, smul_eq_mul] at this
  exact this

/-- diagonal forms. -/
lemma hasSum_form_diag (e₀ : HilbertBasis κ ℝ H) (D₀ : H →L[ℝ] H →L[ℝ] ℝ) (dd₀ : κ → ℝ)
    (hD₀e : ∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i : H) y) (x y : H) :
    HasSum (fun k => dd₀ k * (inner ℝ (e₀ k : H) x * inner ℝ (e₀ k : H) y)) (D₀ x y) := by
  convert hasSum_form_left e₀ D₀ x y using 2 with k
  rw [hD₀e]; ring
/-- the double expansion of a form with finite relative quadratic energy. -/
lemma hasSum_pair (e₀ : HilbertBasis κ ℝ H) (D₀ : H →L[ℝ] H →L[ℝ] ℝ) (dd₀ : κ → ℝ)
    (hdd₀ : ∀ i, 0 < dd₀ i) (hD₀e : ∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i : H) y)
    (Δ : H →L[ℝ] H →L[ℝ] ℝ)
    (hq : Summable fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2)) (x y : H) :
    HasSum (fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) *
      (inner ℝ (e₀ p.1 : H) x * inner ℝ (e₀ p.2 : H) y)) (Δ x y) := by
  set a : κ → ℝ := fun k => inner ℝ (e₀ k : H) x with ha
  set b : κ → ℝ := fun k => inner ℝ (e₀ k : H) y with hb
  have hA : Summable fun k => dd₀ k * a k ^ 2 :=
    (hasSum_form_diag e₀ D₀ dd₀ hD₀e x x).summable.congr fun k => by simp [ha, sq]
  have hA' : Summable fun k => dd₀ k * b k ^ 2 :=
    (hasSum_form_diag e₀ D₀ dd₀ hD₀e y y).summable.congr fun k => by simp [hb, sq]
  have hB : Summable fun k => a k ^ 2 := (hasSum_sq_inner e₀ x).summable
  have hB' : Summable fun k => b k ^ 2 := (hasSum_sq_inner e₀ y).summable
  have hp1 : Summable fun p : κ × κ => (dd₀ p.1 * a p.1 ^ 2) * b p.2 ^ 2 :=
    hA.mul_of_nonneg hB' (fun k => by have := hdd₀ k; positivity) (fun k => sq_nonneg _)
  have hp2 : Summable fun p : κ × κ => a p.1 ^ 2 * (dd₀ p.2 * b p.2 ^ 2) :=
    hB.mul_of_nonneg hA' (fun k => sq_nonneg _) (fun k => by have := hdd₀ k; positivity)
  have hbd : Summable fun p : κ × κ => (1 / 2 : ℝ) * (Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2) +
      ((dd₀ p.1 * a p.1 ^ 2) * b p.2 ^ 2 + a p.1 ^ 2 * (dd₀ p.2 * b p.2 ^ 2))) :=
    (hq.add (hp1.add hp2)).mul_left _
  have hs : Summable fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) * (a p.1 * b p.2) := by
    refine Summable.of_norm_bounded hbd fun p => ?_
    have hs0 : 0 < dd₀ p.1 + dd₀ p.2 := add_pos (hdd₀ _) (hdd₀ _)
    rw [Real.norm_eq_abs]
    have key : |Δ (e₀ p.1) (e₀ p.2) * (a p.1 * b p.2)| ≤ (1 / 2) *
        (Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2) +
          (dd₀ p.1 + dd₀ p.2) * (a p.1 * b p.2) ^ 2) := by
      generalize Δ (e₀ p.1) (e₀ p.2) = Dl
      generalize a p.1 * b p.2 = z
      generalize dd₀ p.1 + dd₀ p.2 = s at hs0 ⊢
      rw [abs_le]
      have h1 : 0 ≤ (Dl - s * z) ^ 2 / s := by positivity
      have h2 : 0 ≤ (Dl + s * z) ^ 2 / s := by positivity
      have e1 : (Dl - s * z) ^ 2 / s = Dl ^ 2 / s + s * z ^ 2 - 2 * (Dl * z) := by
        field_simp; ring
      have e2 : (Dl + s * z) ^ 2 / s = Dl ^ 2 / s + s * z ^ 2 + 2 * (Dl * z) := by
        field_simp; ring
      constructor <;> nlinarith
    refine key.trans (le_of_eq ?_)
    ring
  have hrow : ∀ k, HasSum (fun l => Δ (e₀ k) (e₀ l) * (a k * b l)) (a k * Δ (e₀ k) y) := by
    intro k
    have := (hasSum_form_right e₀ Δ (e₀ k) y).mul_left (a k)
    convert this using 2 with l
    simp only [hb]; ring
  have htsum : ∑' p : κ × κ, Δ (e₀ p.1) (e₀ p.2) * (a p.1 * b p.2) = Δ x y := by
    rw [hs.tsum_prod' (fun k => (hrow k).summable)]
    rw [← (hasSum_form_left e₀ Δ x y).tsum_eq]
    exact tsum_congr fun k => (hrow k).tsum_eq
  rw [← htsum]
  exact hs.hasSum


end Compare
section CompareMain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι κ : Type*} [DecidableEq ι]

/-- the matrix of the finite-rank form `∑_{ij ∈ F} w_ij ⟨e_i, ·⟩⟨e_j, ·⟩` in the basis `e₀`. -/
def X0 (e : HilbertBasis ι ℝ H) (e₀ : HilbertBasis κ ℝ H) (F : Finset ι) (w : ι → ι → ℝ)
    (k l : κ) : ℝ :=
  ∑ i ∈ F, ∑ j ∈ F, w i j * (inner ℝ (e₀ k : H) (e i) * inner ℝ (e₀ l : H) (e j))

lemma form_diag_sum (e : HilbertBasis ι ℝ H) (dd : ι → ℝ) (D : H →L[ℝ] H →L[ℝ] ℝ)
    (hDe : ∀ i y, D (e i) y = dd i * inner ℝ (e i : H) y) (F : Finset ι) (α : ι → ℝ) :
    D (∑ i ∈ F, α i • (e i : H)) (∑ i ∈ F, α i • (e i : H)) = ∑ i ∈ F, dd i * α i ^ 2 := by
  have h := orthonormal_iff_ite.1 e.orthonormal
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, hDe, inner_sum,
    inner_smul_right, smul_eq_mul, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hji
    simp [hji, Ne.symm hji]
  · intro hi; exact absurd ‹_› hi
lemma compare_tail (e : HilbertBasis ι ℝ H) (e₀ : HilbertBasis κ ℝ H) (dd : ι → ℝ)
    (D : H →L[ℝ] H →L[ℝ] ℝ) (hDe : ∀ i y, D (e i) y = dd i * inner ℝ (e i : H) y)
    (dd₀ : κ → ℝ) (hdd₀ : ∀ i, 0 < dd₀ i) (D₀ : H →L[ℝ] H →L[ℝ] ℝ)
    (hD₀e : ∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i : H) y)
    (c : ℝ) (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x) (F : Finset ι) (w : ι → ι → ℝ) :
    Summable (fun p : κ × κ => dd₀ p.1 * X0 e e₀ F w p.1 p.2 ^ 2) ∧
      ∑' p : κ × κ, dd₀ p.1 * X0 e e₀ F w p.1 p.2 ^ 2 ≤
        c⁻¹ * ∑ i ∈ F, dd i * ∑ j ∈ F, w i j ^ 2 := by
  classical
  have h := orthonormal_iff_ite.1 e.orthonormal
  set β : ι → κ → ℝ := fun i l => ∑ j ∈ F, w i j * inner ℝ (e₀ l : H) (e j) with hβ
  set u : ι → H := fun i => ∑ j ∈ F, w i j • (e j : H) with hu
  have hβu : ∀ i l, inner ℝ (e₀ l : H) (u i) = β i l := by
    intro i l; simp [hu, hβ, inner_sum, inner_smul_right]
  set v : κ → H := fun l => ∑ i ∈ F, β i l • (e i : H) with hv
  have hX : ∀ k l, X0 e e₀ F w k l = inner ℝ (e₀ k : H) (v l) := by
    intro k l
    simp only [X0, hv, inner_sum, inner_smul_right, hβ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrow : ∀ l, HasSum (fun k => dd₀ k * X0 e e₀ F w k l ^ 2) (D₀ (v l) (v l)) := by
    intro l
    convert hasSum_form_diag e₀ D₀ dd₀ hD₀e (v l) (v l) using 2 with k
    rw [hX, sq]
  have hDv : ∀ l, D₀ (v l) (v l) ≤ c⁻¹ * ∑ i ∈ F, dd i * β i l ^ 2 := by
    intro l
    have h1 := hcD (v l)
    rw [hv, form_diag_sum e dd D hDe F (fun i => β i l)] at h1
    calc D₀ (v l) (v l) = c⁻¹ * (c * D₀ (v l) (v l)) := by field_simp
      _ ≤ c⁻¹ * ∑ i ∈ F, dd i * β i l ^ 2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc.le)
  have hnorm : ∀ i, ‖u i‖ ^ 2 = ∑ j ∈ F, w i j ^ 2 := by
    intro i
    rw [← real_inner_self_eq_norm_sq]
    simp only [hu, sum_inner, inner_sum, inner_smul_left, inner_smul_right, h, conj_trivial]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [sq]
    · intro j' _ hj'; simp [hj', Ne.symm hj']
    · intro hj; exact absurd ‹_› hj
  have hβsq : ∀ i, HasSum (fun l => β i l ^ 2) (∑ j ∈ F, w i j ^ 2) := by
    intro i
    have := hasSum_sq_inner e₀ (u i)
    rw [hnorm i] at this
    convert this using 2 with l
    rw [hβu]
  have hl : Summable (fun l => c⁻¹ * ∑ i ∈ F, dd i * β i l ^ 2) :=
    (summable_sum fun i _ => (hβsq i).summable.mul_left (dd i)).mul_left _
  set g' : κ × κ → ℝ := fun p => dd₀ p.2 * X0 e e₀ F w p.2 p.1 ^ 2 with hg'
  have hg'nn : ∀ p, 0 ≤ g' p := fun p => by have := hdd₀ p.2; positivity
  have hg's : Summable g' := by
    rw [summable_prod_of_nonneg hg'nn]
    refine ⟨fun l => (hrow l).summable, ?_⟩
    refine hl.of_nonneg_of_le (fun l => tsum_nonneg fun k => hg'nn (l, k)) fun l => ?_
    have : ∑' k, g' (l, k) = D₀ (v l) (v l) := (hrow l).tsum_eq
    rw [this]; exact hDv l
  refine ⟨hg's.prod_symm, ?_⟩
  have e1 : ∑' p : κ × κ, dd₀ p.1 * X0 e e₀ F w p.1 p.2 ^ 2 = ∑' p : κ × κ, g' p :=
    (Equiv.prodComm κ κ).tsum_eq g'
  rw [e1, hg's.tsum_prod' (fun l => (hrow l).summable)]
  calc ∑' l, ∑' k, g' (l, k) ≤ ∑' l, c⁻¹ * ∑ i ∈ F, dd i * β i l ^ 2 := by
        refine Summable.tsum_le_tsum (fun l => ?_) ?_ hl
        · rw [(hrow l).tsum_eq]; exact hDv l
        · refine hl.of_nonneg_of_le (fun l => tsum_nonneg fun k => hg'nn (l, k)) fun l => ?_
          rw [(hrow l).tsum_eq]; exact hDv l
    _ = c⁻¹ * ∑ i ∈ F, dd i * ∑ j ∈ F, w i j ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun i _ => (hβsq i).summable.mul_left (dd i)]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tsum_mul_left, (hβsq i).tsum_eq]

lemma finite_compare (e : HilbertBasis ι ℝ H) (e₀ : HilbertBasis κ ℝ H) (dd : ι → ℝ)
    (hdd : ∀ i, 0 < dd i)
    (D : H →L[ℝ] H →L[ℝ] ℝ) (hDe : ∀ i y, D (e i) y = dd i * inner ℝ (e i : H) y)
    (dd₀ : κ → ℝ) (hdd₀ : ∀ i, 0 < dd₀ i) (D₀ : H →L[ℝ] H →L[ℝ] ℝ)
    (hD₀e : ∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i : H) y)
    (c : ℝ) (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x)
    (Δ : H →L[ℝ] H →L[ℝ] ℝ) (hΔ : ∀ x y, Δ x y = Δ y x)
    (hsum₀ : Summable fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2))
    (F : Finset ι) :
    ∑ i ∈ F, ∑ j ∈ F, Δ (e i) (e j) ^ 2 / (dd i + dd j) ≤
      c⁻¹ * ∑' p : κ × κ, Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2) := by
  classical
  set w : ι → ι → ℝ := fun i j => Δ (e i) (e j) / (dd i + dd j) with hwdef
  have hws : ∀ i j, w i j = w j i := fun i j => by
    simp only [hwdef]; rw [hΔ (e i) (e j), add_comm]
  have hΔw : ∀ i j, Δ (e i) (e j) = (dd i + dd j) * w i j := fun i j => by
    have : 0 < dd i + dd j := add_pos (hdd i) (hdd j)
    simp only [hwdef]; field_simp
  set V : ℝ := ∑ i ∈ F, ∑ j ∈ F, Δ (e i) (e j) * w i j with hV
  have hV1 : ∑ i ∈ F, ∑ j ∈ F, Δ (e i) (e j) ^ 2 / (dd i + dd j) = V := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hwdef]; ring
  have hVsq : ∑ i ∈ F, ∑ j ∈ F, (dd i + dd j) * w i j ^ 2 = V := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΔw i j]; ring
  have hR : ∑ i ∈ F, ∑ j ∈ F, (dd i + dd j) * w i j ^ 2 =
      2 * ∑ i ∈ F, dd i * ∑ j ∈ F, w i j ^ 2 := by
    have e1 : ∑ i ∈ F, ∑ j ∈ F, (dd i + dd j) * w i j ^ 2 =
        ∑ i ∈ F, ∑ j ∈ F, dd i * w i j ^ 2 + ∑ i ∈ F, ∑ j ∈ F, dd j * w i j ^ 2 := by
      simp only [add_mul, Finset.sum_add_distrib]
    have e2 : ∑ i ∈ F, ∑ j ∈ F, dd j * w i j ^ 2 = ∑ i ∈ F, ∑ j ∈ F, dd i * w i j ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hws j i]
    have e3 : ∑ i ∈ F, ∑ j ∈ F, dd i * w i j ^ 2 = ∑ i ∈ F, dd i * ∑ j ∈ F, w i j ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [e1, e2, e3]; ring
  obtain ⟨hgAs, hgA⟩ := compare_tail e e₀ dd D hDe dd₀ hdd₀ D₀ hD₀e c hc hcD F w
  have hXsym : ∀ k l, X0 e e₀ F w k l = X0 e e₀ F w l k := by
    intro k l
    simp only [X0]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hws i j]; ring
  have hgB : Summable fun p : κ × κ => (dd₀ p.1 + dd₀ p.2) * X0 e e₀ F w p.1 p.2 ^ 2 := by
    have h2 : Summable fun p : κ × κ => dd₀ p.2 * X0 e e₀ F w p.1 p.2 ^ 2 := by
      refine hgAs.prod_symm.congr fun p => ?_
      simp [hXsym p.1 p.2]
    simpa only [add_mul] using hgAs.add h2
  have hgB' : ∑' p : κ × κ, (dd₀ p.1 + dd₀ p.2) * X0 e e₀ F w p.1 p.2 ^ 2 ≤
      c⁻¹ * V := by
    have h2 : ∑' p : κ × κ, dd₀ p.2 * X0 e e₀ F w p.1 p.2 ^ 2 =
        ∑' p : κ × κ, dd₀ p.1 * X0 e e₀ F w p.1 p.2 ^ 2 := by
      rw [← (Equiv.prodComm κ κ).tsum_eq (fun p : κ × κ => dd₀ p.2 * X0 e e₀ F w p.1 p.2 ^ 2)]
      refine tsum_congr fun p => ?_
      simp [hXsym p.1 p.2]
    have h3 : ∑' p : κ × κ, (dd₀ p.1 + dd₀ p.2) * X0 e e₀ F w p.1 p.2 ^ 2 =
        2 * ∑' p : κ × κ, dd₀ p.1 * X0 e e₀ F w p.1 p.2 ^ 2 := by
      simp only [add_mul]
      rw [hgAs.tsum_add (by
        refine hgAs.prod_symm.congr fun p => ?_
        simp [hXsym p.1 p.2]), h2]
      ring
    rw [h3, ← hVsq, hR]
    linarith
  -- the pairing
  have hA : HasSum (fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) * X0 e e₀ F w p.1 p.2) V := by
    have hij : ∀ i j, HasSum (fun p : κ × κ => w i j * (Δ (e₀ p.1) (e₀ p.2) *
        (inner ℝ (e₀ p.1 : H) (e i) * inner ℝ (e₀ p.2 : H) (e j)))) (w i j * Δ (e i) (e j)) :=
      fun i j => (hasSum_pair e₀ D₀ dd₀ hdd₀ hD₀e Δ hsum₀ (e i) (e j)).mul_left (w i j)
    have h1 : HasSum (fun p : κ × κ => ∑ i ∈ F, ∑ j ∈ F, w i j * (Δ (e₀ p.1) (e₀ p.2) *
        (inner ℝ (e₀ p.1 : H) (e i) * inner ℝ (e₀ p.2 : H) (e j))))
        (∑ i ∈ F, ∑ j ∈ F, w i j * Δ (e i) (e j)) :=
      hasSum_sum fun i _ => hasSum_sum fun j _ => hij i j
    have h2 : (fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) * X0 e e₀ F w p.1 p.2) =
        fun p : κ × κ => ∑ i ∈ F, ∑ j ∈ F, w i j * (Δ (e₀ p.1) (e₀ p.2) *
        (inner ℝ (e₀ p.1 : H) (e i) * inner ℝ (e₀ p.2 : H) (e j))) := by
      funext p
      simp only [X0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    convert h1 using 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  -- AM-GM
  have hamgm : ∀ p : κ × κ, Δ (e₀ p.1) (e₀ p.2) * X0 e e₀ F w p.1 p.2 ≤
      (c / 2) * ((dd₀ p.1 + dd₀ p.2) * X0 e e₀ F w p.1 p.2 ^ 2) +
        (1 / (2 * c)) * (Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2)) := by
    intro p
    have hs0 : 0 < dd₀ p.1 + dd₀ p.2 := add_pos (hdd₀ _) (hdd₀ _)
    generalize Δ (e₀ p.1) (e₀ p.2) = Dl
    generalize X0 e e₀ F w p.1 p.2 = x
    generalize dd₀ p.1 + dd₀ p.2 = s at hs0 ⊢
    have h1 : 0 ≤ (Dl - c * s * x) ^ 2 / (2 * c * s) := by positivity
    have e1 : (Dl - c * s * x) ^ 2 / (2 * c * s) = (1 / (2 * c)) * (Dl ^ 2 / s) +
        (c / 2) * (s * x ^ 2) - Dl * x := by field_simp; ring
    linarith
  have hsum2 : Summable fun p : κ × κ => (c / 2) * ((dd₀ p.1 + dd₀ p.2) * X0 e e₀ F w p.1 p.2 ^ 2) +
        (1 / (2 * c)) * (Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2)) :=
    (hgB.mul_left _).add (hsum₀.mul_left _)
  have hle := Summable.tsum_le_tsum hamgm hA.summable hsum2
  rw [hA.tsum_eq, Summable.tsum_add (hgB.mul_left _) (hsum₀.mul_left _), tsum_mul_left,
    tsum_mul_left] at hle
  rw [hV1]
  have h1 : (c / 2) * ∑' p : κ × κ, (dd₀ p.1 + dd₀ p.2) * X0 e e₀ F w p.1 p.2 ^ 2 ≤
      (c / 2) * (c⁻¹ * V) := mul_le_mul_of_nonneg_left hgB' (by positivity)
  have h2 : (c / 2) * (c⁻¹ * V) = V / 2 := by field_simp
  set Q₀ := ∑' p : κ × κ, Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2) with hQ₀
  have h3 : V ≤ V / 2 + 1 / (2 * c) * Q₀ := by linarith
  have h4 : V / 2 ≤ 1 / (2 * c) * Q₀ := by linarith
  have h5 : 1 / (2 * c) * Q₀ = (c⁻¹ * Q₀) / 2 := by field_simp
  linarith

/-- Comparison of relative quadratic forms: `𝒬_D ≤ c⁻¹ 𝒬_{D₀}` when `D ≥ c D₀`. -/
theorem relQuad_le_of_cmp (e : HilbertBasis ι ℝ H) (e₀ : HilbertBasis κ ℝ H) (dd : ι → ℝ)
    (hdd : ∀ i, 0 < dd i)
    (D : H →L[ℝ] H →L[ℝ] ℝ) (hDe : ∀ i y, D (e i) y = dd i * inner ℝ (e i : H) y)
    (dd₀ : κ → ℝ) (hdd₀ : ∀ i, 0 < dd₀ i) (D₀ : H →L[ℝ] H →L[ℝ] ℝ)
    (hD₀e : ∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i : H) y)
    (c : ℝ) (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x)
    (Δ : H →L[ℝ] H →L[ℝ] ℝ) (hΔ : ∀ x y, Δ x y = Δ y x) :
    Uniform.relQuad e dd Δ ≤ ENNReal.ofReal c⁻¹ * Uniform.relQuad e₀ dd₀ Δ := by
  classical
  by_cases htop : Uniform.relQuad e₀ dd₀ Δ = ⊤
  · rw [htop, ENNReal.mul_top]
    · exact le_top
    · simpa using hc
  · have hnn : ∀ p : κ × κ, 0 ≤ Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2) := fun p =>
      div_nonneg (sq_nonneg _) (add_pos (hdd₀ _) (hdd₀ _)).le
    have hsum₀ : Summable fun p : κ × κ => Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2) := by
      have := ENNReal.summable_toReal htop
      refine this.congr fun p => ?_
      exact ENNReal.toReal_ofReal (hnn p)
    have hq : Uniform.relQuad e₀ dd₀ Δ = ENNReal.ofReal
        (∑' p : κ × κ, Δ (e₀ p.1) (e₀ p.2) ^ 2 / (dd₀ p.1 + dd₀ p.2)) :=
      (ENNReal.ofReal_tsum_of_nonneg hnn hsum₀).symm
    rw [hq, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
    unfold Uniform.relQuad
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    set F : Finset ι := s.image Prod.fst ∪ s.image Prod.snd with hF
    have hsub : s ⊆ F ×ˢ F := by
      intro p hp
      simp only [Finset.mem_product, hF, Finset.mem_union, Finset.mem_image]
      exact ⟨Or.inl ⟨p, hp, rfl⟩, Or.inr ⟨p, hp, rfl⟩⟩
    have hnn' : ∀ p : ι × ι, 0 ≤ Δ (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2) := fun p =>
      div_nonneg (sq_nonneg _) (add_pos (hdd _) (hdd _)).le
    calc ∑ p ∈ s, ENNReal.ofReal (Δ (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2))
        ≤ ∑ p ∈ F ×ˢ F, ENNReal.ofReal (Δ (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2)) :=
          Finset.sum_le_sum_of_subset hsub
      _ = ENNReal.ofReal (∑ p ∈ F ×ˢ F, Δ (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2)) :=
          (ENNReal.ofReal_sum_of_nonneg fun p _ => hnn' p).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.sum_product]
          exact finite_compare e e₀ dd hdd D hDe dd₀ hdd₀ D₀ hD₀e c hc hcD Δ hΔ hsum₀ F


end CompareMain

end RelCov
section Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma 3.29, operator part (proved here; statement identical to `relative_covariance_cost`). -/
theorem relative_covariance_cost_proof [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {ι : Type*} (e : HilbertBasis ι ℝ H) (dd : ι → ℝ) (hdd : ∀ i, 0 < dd i)
    (D C : H →L[ℝ] H →L[ℝ] ℝ) (hD : IsTraceClassCov D) (hDe : ∀ i y, D (e i) y = dd i * inner ℝ (e i) y)
    (hC : IsTraceClassCov C) :
    ENNReal.ofReal (bures2 C D) ≤ 2 * relQuad e dd (C - D) ∧
      ∀ (D₀ : H →L[ℝ] H →L[ℝ] ℝ) {ι₀ : Type*} (e₀ : HilbertBasis ι₀ ℝ H) (dd₀ : ι₀ → ℝ),
        (∀ i, 0 < dd₀ i) → (∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i) y) → ∀ c : ℝ, 0 < c →
        (∀ x, c * D₀ x x ≤ D x x) →
        2 * relQuad e dd (C - D) ≤ 2 * ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D) := by
  classical
  have hsymm : ∀ x y, (C - D) x y = (C - D) y x := fun x y => by
    simp only [_root_.sub_apply, hC.symm x y, hD.symm x y]
  refine ⟨?_, ?_⟩
  · have h := RelCov.bures2_le e dd hdd D hDe 1 one_pos (fun x => by rw [one_mul]) hC hD
    simpa using h
  · intro D₀ ι₀ e₀ dd₀ hdd₀ hD₀e c hc hcD
    have h := RelCov.relQuad_le_of_cmp e e₀ dd hdd D hDe dd₀ hdd₀ D₀ hD₀e c hc hcD (C - D) hsymm
    calc 2 * relQuad e dd (C - D) ≤ 2 * (ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D)) :=
          by gcongr
      _ = 2 * ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D) := by rw [mul_assoc]

example [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] :=
  (@relative_covariance_cost_proof H _ _ _ _ _ _ : type_of% (@relative_covariance_cost H _ _ _ _ _ _))

end Main

namespace ChartAux
section ChartPart2
open ProbabilityTheory Filter Topology


/-- bias-variance identity for a bounded random variable. -/
lemma integral_sq_sub_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (B : ℝ) (hB : ∀ ω, |Y ω| ≤ B) (a : ℝ) :
    ∫ ω, (Y ω - a) ^ 2 ∂P = Var[Y; P] + (∫ ω, Y ω ∂P - a) ^ 2 := by
  have hint : Integrable Y P :=
    Integrable.of_bound (C := B) hY.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hB ω)
  have hmem : MemLp Y 2 P := MemLp.of_bound hY.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB ω)
  rw [variance_eq_integral hY.aemeasurable]
  set m := ∫ ω, Y ω ∂P with hm
  have h1 : ∀ ω, (Y ω - a) ^ 2 = (Y ω - m) ^ 2 + 2 * (m - a) * (Y ω - m) + (m - a) ^ 2 := by
    intro ω; ring
  simp_rw [h1]
  have hi1 : Integrable (fun ω => (Y ω - m) ^ 2) P := (hmem.sub (memLp_const m)).integrable_sq
  have hi2 : Integrable (fun ω => Y ω - m) P := hint.sub (integrable_const m)
  have hA : Integrable (fun ω => (Y ω - m) ^ 2 + 2 * (m - a) * (Y ω - m)) P :=
    hi1.add (hi2.const_mul _)
  rw [integral_add (f := fun ω => (Y ω - m) ^ 2 + 2 * (m - a) * (Y ω - m))
    (g := fun _ => (m - a) ^ 2) hA (integrable_const _),
    integral_add (f := fun ω => (Y ω - m) ^ 2) (g := fun ω => 2 * (m - a) * (Y ω - m)) hi1
      (hi2.const_mul _), integral_const_mul, integral_sub hint (integrable_const m)]
  simp [hm]

lemma integral_add3 {X : Type*} [MeasurableSpace X] (μ : Measure X) {a b c : X → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) :
    ∫ x, (a x + b x + c x) ∂μ = ∫ x, a x ∂μ + ∫ x, b x ∂μ + ∫ x, c x ∂μ := by
  have hab : Integrable (fun x => a x + b x) μ := ha.add hb
  rw [integral_add (f := fun x => a x + b x) (g := c) hab hc, integral_add (f := a) (g := b) ha hb]

lemma integrable_mul_L2 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f h : X → ℝ)
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) : Integrable (fun x => f x * h x) μ := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hh2 : Integrable (fun x => h x ^ 2) μ := hh.integrable_sq
  refine Integrable.mono' (hf2.add hh2) (hf.aestronglyMeasurable.mul hh.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|f x| - |h x|), sq_abs (f x), sq_abs (h x), abs_nonneg (f x), abs_nonneg (h x)]

/-- Cauchy–Schwarz in `L²`. -/
lemma integral_mul_sq_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (f h : X → ℝ)
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    (∫ x, f x * h x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, h x ^ 2 ∂μ := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hh2 : Integrable (fun x => h x ^ 2) μ := hh.integrable_sq
  have hfh : Integrable (fun x => f x * h x) μ := integrable_mul_L2 μ f h hf hh
  have key : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, f x * h x ∂μ) * t +
      ∫ x, h x ^ 2 ∂μ := by
    intro t
    have : ∫ x, (t * f x + h x) ^ 2 ∂μ = (∫ x, f x ^ 2 ∂μ) * (t * t) +
        (2 * ∫ x, f x * h x ∂μ) * t + ∫ x, h x ^ 2 ∂μ := by
      have e1 : ∀ x, (t * f x + h x) ^ 2 = (t * t) * f x ^ 2 + (2 * t) * (f x * h x) + h x ^ 2 := by
        intro x; ring
      simp_rw [e1]
      rw [integral_add3 μ (hf2.const_mul _) (hfh.const_mul _) hh2, integral_const_mul,
        integral_const_mul]
      ring
    rw [← this]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- the expectation of the empirical statistic. -/
lemma integral_empirical {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (xs : Fin N → Ω → X) (hxs : ∀ i, Measurable (xs i))
    (g : X → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (F : X → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    ∫ ω, (N : ℝ)⁻¹ * ∑ i, F (xs i ω) ∂P = ∫ x, max (g x) 0 * F x ∂μ := by
  have hFi : ∀ i, Integrable (fun ω => F (xs i ω)) P := fun i =>
    Integrable.of_bound (C := B) (hF.comp (hxs i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  have hFm : ∀ i, Integrable F (P.map (xs i)) := fun i =>
    Integrable.of_bound (C := B) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB _)
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hFi i]
  have h1 : ∀ i, ∫ ω, F (xs i ω) ∂P = ∫ x, F x ∂(P.map (xs i)) := fun i =>
    (integral_map (hxs i).aemeasurable hF.aestronglyMeasurable).symm
  simp_rw [h1]
  have h2 : ∫ x, F x ∂((N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i)) =
      (N : ℝ)⁻¹ * ∑ i, ∫ x, F x ∂(P.map (xs i)) := by
    rw [integral_smul_measure, integral_finsetSum_measure fun i _ => hFm i, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, smul_eq_mul]
  rw [← h2, hmarg, integral_withDensity_eq_integral_toReal_smul (hg.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal', smul_eq_mul]

/-- second moment of the centered empirical statistic. -/
lemma second_moment_bound {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) [IsFiniteMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → X) (hxs : ∀ i, Measurable (xs i))
    (g : X → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (Cin δ : ℝ)
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
    (hvar : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
        ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ))
    (F : X → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    ∫ ω, ((N : ℝ)⁻¹ * ∑ i, F (xs i ω) - ∫ x, F x ∂μ) ^ 2 ∂P ≤
      |Cin| * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ + (∫ x, F x ^ 2 ∂μ) * (Cin * δ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set Y : Ω → ℝ := fun ω => (N : ℝ)⁻¹ * ∑ i, F (xs i ω) with hYdef
  have hYm : Measurable Y :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hF.comp (hxs i))
  have hYB : ∀ ω, |Y ω| ≤ B := by
    intro ω
    simp only [hYdef]
    rw [abs_mul, abs_of_pos (inv_pos.2 hN0)]
    have : |∑ i, F (xs i ω)| ≤ N * B := by
      calc |∑ i, F (xs i ω)| ≤ ∑ i, |F (xs i ω)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
        _ = N * B := by simp
    calc (N : ℝ)⁻¹ * |∑ i, F (xs i ω)| ≤ (N : ℝ)⁻¹ * (N * B) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hN0.le)
      _ = B := by field_simp
  have hFint : Integrable F μ :=
    Integrable.of_bound (C := B) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB _)
  have hFmem : MemLp F 2 μ := MemLp.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB _)
  have hYmem : MemLp Y 2 P := MemLp.of_bound hYm.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYB ω)
  -- bias-variance
  have hbv := integral_sq_sub_eq P Y hYm B hYB (∫ x, F x ∂μ)
  have hEY : ∫ ω, Y ω ∂P = ∫ x, max (g x) 0 * F x ∂μ :=
    integral_empirical μ P N xs hxs g hg hmarg F hF B hB
  -- the density deviation
  set h : X → ℝ := fun x => max (g x) 0 - 1 with hh
  have hhm : Measurable h := (hg.max measurable_const).sub measurable_const
  have hhle : ∀ x, |h x| ≤ |g x - 1| := by
    intro x
    simp only [hh]
    rcases le_total (g x) 0 with hx | hx
    · rw [max_eq_right hx]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [max_eq_left hx]
  have hhint : Integrable (fun x => h x ^ 2) μ := by
    refine ⟨(hhm.pow_const 2).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hgL2 ENNReal.ofReal_lt_top)
    refine lintegral_mono fun x => ?_
    rw [enorm_pow]
    gcongr
    exact enorm_le_iff_norm_le.mpr (by simpa [Real.norm_eq_abs] using hhle x)
  have hhmem : MemLp h 2 μ := (memLp_two_iff_integrable_sq hhm.aestronglyMeasurable).2 hhint
  have hh2le : ∫ x, h x ^ 2 ∂μ ≤ (Cin * δ) ^ 2 := by
    have h1 : ENNReal.ofReal (∫ x, h x ^ 2 ∂μ) = ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hhint (Filter.Eventually.of_forall fun x => sq_nonneg _)
    have h2 : ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ ≤ ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ := by
      refine lintegral_mono fun x => ?_
      rw [← Real.enorm_of_nonneg (sq_nonneg (h x)), enorm_pow]
      gcongr
      exact enorm_le_iff_norm_le.mpr (by simpa [Real.norm_eq_abs] using hhle x)
    have := h1.le.trans (h2.trans hgL2)
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 this
  -- bias
  have hbias : (∫ ω, Y ω ∂P - ∫ x, F x ∂μ) ^ 2 ≤ (∫ x, F x ^ 2 ∂μ) * (Cin * δ) ^ 2 := by
    have hFh : Integrable (fun x => F x * h x) μ := integrable_mul_L2 μ F h hFmem hhmem
    have e1 : ∫ ω, Y ω ∂P - ∫ x, F x ∂μ = ∫ x, F x * h x ∂μ := by
      have : (fun x => max (g x) 0 * F x) = fun x => F x * h x + F x := by
        funext x; simp only [hh]; ring
      rw [hEY, this, integral_add hFh hFint]
      ring
    rw [e1]
    calc (∫ x, F x * h x ∂μ) ^ 2 ≤ (∫ x, F x ^ 2 ∂μ) * ∫ x, h x ^ 2 ∂μ :=
          integral_mul_sq_le μ F h hFmem hhmem
      _ ≤ (∫ x, F x ^ 2 ∂μ) * (Cin * δ) ^ 2 :=
          mul_le_mul_of_nonneg_left hh2le (integral_nonneg fun x => sq_nonneg _)
  -- variance
  have hvar' : Var[Y; P] ≤ |Cin| * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ := by
    have h1 := hvar F hF hFmem
    have h2 : ENNReal.ofReal Var[Y; P] ≤ ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ) := by
      rw [hYmem.ofReal_variance_eq]; exact h1
    have hA : 0 ≤ ∫ x, F x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hC : Cin * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ ≤ |Cin| * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ := by
      have hn : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN0.le
      have hc := le_abs_self Cin
      nlinarith [mul_nonneg hn hA, mul_nonneg (mul_nonneg hn hA) (sub_nonneg.2 hc)]
    rcases (ENNReal.ofReal_le_ofReal_iff' ).1 h2 with h | h
    · exact h.trans hC
    · have := variance_nonneg Y P
      have h0 : 0 ≤ |Cin| * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ := by positivity
      linarith
  rw [hbv]
  linarith



end ChartPart2

section ChartPart1
open ProbabilityTheory Filter Topology
variable {d : ℕ}


variable {d : ℕ}

lemma chartWeight_pos (r : ℕ) (k : Lattice d) : 0 < chartWeight r k := by
  unfold chartWeight; positivity

lemma abs_chartBasis_le (k : Lattice d) (u : Torus d) : |chartBasis k u| ≤ Real.sqrt 2 := by
  unfold chartBasis
  split_ifs with h
  · rw [abs_one]
    exact Real.one_le_sqrt.2 (by norm_num)
  · exact Torus.abs_realMode_le _ u

lemma chartBasis_sq_le (k : Lattice d) (u : Torus d) : chartBasis k u ^ 2 ≤ 2 := by
  have h := abs_chartBasis_le k u
  have := sq_le_sq' (by linarith [abs_nonneg (chartBasis k u)]) h
  rw [Real.sq_sqrt (by norm_num)] at this
  simpa using this

lemma continuous_chartBasis (k : Lattice d) : Continuous (chartBasis k : Torus d → ℝ) := by
  unfold chartBasis
  split_ifs with h
  · exact continuous_const
  · exact Torus.continuous_realMode _

lemma chartBasis_zero (u : Torus d) : chartBasis (0 : Lattice d) u = 1 := by
  simp [chartBasis]

lemma chartBasis_ne (k : Lattice d) (hk : k ≠ 0) (u : Torus d) :
    chartBasis k u = Torus.realMode ⟨k, hk⟩ u := by
  simp [chartBasis, hk]

lemma integral_chartBasis_mul (k l : Lattice d) :
    ∫ u : Torus d, chartBasis k u * chartBasis l u = if k = l then 1 else 0 := by
  by_cases hk : k = 0 <;> by_cases hl : l = 0
  · subst hk; subst hl; simp [chartBasis_zero]
  · subst hk
    simp only [chartBasis_zero, chartBasis_ne l hl, one_mul]
    rw [Torus.integral_realMode]
    simp [Ne.symm hl]
  · subst hl
    simp only [chartBasis_zero, chartBasis_ne k hk, mul_one]
    rw [Torus.integral_realMode]
    simp [hk]
  · simp only [chartBasis_ne k hk, chartBasis_ne l hl]
    rw [Torus.realMode_orthonormal ⟨k, hk⟩ ⟨l, hl⟩]
    simp [Subtype.ext_iff]

lemma summable_one_add_enorm_rpow (a : ℝ) (ha : (d : ℝ) < 2 * a) :
    Summable fun k : Lattice d => (1 + Lattice.enorm k ^ 2) ^ (-a) := by
  rw [Torus.summable_lattice_iff]
  have hs := summable_jp_rpow (d := d) a ha
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hs.mul_left ((4 * Real.pi ^ 2) ^ a))
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hA : 0 < 1 + Lattice.enorm k.1 ^ 2 := by positivity
  have hB : 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 := by positivity
  have hjp : Lattice.jp k.1 ^ (-(2 * a)) = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) ^ (-a) := by
    unfold Lattice.jp
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hB.le]
    congr 1; ring
  have hle : (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) / (4 * Real.pi ^ 2) ≤
      1 + Lattice.enorm k.1 ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Lattice.enorm k.1)]
  have ha0 : -a ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  rw [hjp]
  calc (1 + Lattice.enorm k.1 ^ 2) ^ (-a)
      ≤ ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) / (4 * Real.pi ^ 2)) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle ha0
    _ = (4 * Real.pi ^ 2) ^ a * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) ^ (-a) := by
        have hc : 0 < 4 * Real.pi ^ 2 := by positivity
        rw [Real.div_rpow hB.le hc.le, Real.rpow_neg hc.le a, div_inv_eq_mul, mul_comm]

lemma summable_chartWeight (r : ℕ) (hr : d < r) : Summable (chartWeight r : Lattice d → ℝ) := by
  have := summable_one_add_enorm_rpow (d := d) (r : ℝ) (by
    have : (d : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  exact this

lemma summable_sqrt_chartWeight (r : ℕ) (hr : d < r) :
    Summable (fun k : Lattice d => Real.sqrt (chartWeight r k)) := by
  have := summable_one_add_enorm_rpow (d := d) ((r : ℝ) / 2) (by
    have : (d : ℝ) < r := by exact_mod_cast hr
    linarith)
  refine this.congr fun k => ?_
  unfold chartWeight
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1; ring

lemma memℓp_chartFeature (r : ℕ) (hr : d < r) (u : Torus d) :
    Memℓp (fun k : Lattice d => Real.sqrt (chartWeight r k) * chartBasis k u) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hs := (summable_chartWeight (d := d) r hr).mul_left 2
  refine hs.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Real.sq_sqrt (chartWeight_pos r k).le]
  nlinarith [chartBasis_sq_le k u, (chartWeight_pos r k)]

lemma chartFeature_def (r : ℕ) (hr : d < r) (u : Torus d) :
    (chartFeature (d := d) r u : Lattice d → ℝ) =
      fun k => Real.sqrt (chartWeight r k) * chartBasis k u := by
  unfold chartFeature
  rw [dif_pos (memℓp_chartFeature r hr u)]

lemma chartFeature_apply (r : ℕ) (hr : d < r) (u : Torus d) (k : Lattice d) :
    (chartFeature (d := d) r u) k = Real.sqrt (chartWeight r k) * chartBasis k u :=
  congrFun (chartFeature_def r hr u) k

lemma norm_sq_lp (f : FeatureSpace d) : ‖f‖ ^ 2 = ∑' k, (f k) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  exact h

lemma norm_sq_chartFeature (r : ℕ) (hr : d < r) (u : Torus d) :
    ‖chartFeature (d := d) r u‖ ^ 2 = ∑' k, chartWeight r k * chartBasis k u ^ 2 := by
  rw [norm_sq_lp]
  refine tsum_congr fun k => ?_
  rw [chartFeature_apply r hr, mul_pow, Real.sq_sqrt (chartWeight_pos r k).le]

lemma norm_sq_chartFeature_le (r : ℕ) (hr : d < r) (u : Torus d) :
    ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k := by
  rw [norm_sq_chartFeature r hr, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((summable_chartWeight r hr).mul_left 2)
  · nlinarith [chartBasis_sq_le k u, chartWeight_pos r k]
  · refine ((summable_chartWeight (d := d) r hr).mul_left 2).of_nonneg_of_le
      (fun k => by have := chartWeight_pos r k; positivity) fun k => ?_
    nlinarith [chartBasis_sq_le k u, chartWeight_pos r k]

lemma continuous_chartFeature (r : ℕ) (hr : d < r) :
    Continuous (chartFeature (d := d) r) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hG : Continuous fun v : Torus d => ∑' k, chartWeight r k * (chartBasis k v - chartBasis k u) ^ 2 := by
    refine continuous_tsum (u := fun k => 8 * chartWeight r k)
      (fun k => continuous_const.mul (((continuous_chartBasis k).sub continuous_const).pow 2))
      ((summable_chartWeight r hr).mul_left 8) (fun k v => ?_)
    have hw := chartWeight_pos r k
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := chartBasis_sq_le k v
    have h2 := chartBasis_sq_le k u
    nlinarith [sq_nonneg (chartBasis k v + chartBasis k u)]
  have hG0 : ∑' k, chartWeight r k * (chartBasis k u - chartBasis k u) ^ 2 = 0 := by simp
  have hnorm : ∀ v, ‖chartFeature (d := d) r v - chartFeature r u‖ =
      Real.sqrt (∑' k, chartWeight r k * (chartBasis k v - chartBasis k u) ^ 2) := by
    intro v
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_lp]
    congr 1
    refine tsum_congr fun k => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, chartFeature_apply r hr, chartFeature_apply r hr]
    have := (chartWeight_pos r k).le
    rw [show Real.sqrt (chartWeight r k) * chartBasis k v - Real.sqrt (chartWeight r k) * chartBasis k u =
      Real.sqrt (chartWeight r k) * (chartBasis k v - chartBasis k u) by ring, mul_pow,
      Real.sq_sqrt this]
  simp only [hnorm]
  have := (Real.continuous_sqrt.tendsto _).comp (hG.tendsto u)
  rw [hG0, Real.sqrt_zero] at this
  exact this

section Outer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- the integrand of `outerCov`. -/
def Phi (b : Torus d → H) (u : Torus d) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ (b u)).smulRight (innerSL ℝ (b u))

lemma Phi_apply (b : Torus d → H) (u : Torus d) (x y : H) :
    Phi b u x y = inner ℝ (b u) x * inner ℝ (b u) y := by
  simp [Phi, mul_comm]

lemma norm_Phi (b : Torus d → H) (u : Torus d) : ‖Phi b u‖ = ‖b u‖ ^ 2 := by
  simp [Phi, ContinuousLinearMap.norm_smulRight_apply, sq]

lemma continuous_Phi {b : Torus d → H} (hb : Continuous b) : Continuous (Phi b) := by
  have h1 : Continuous fun u => innerSL ℝ (b u) := (innerSL ℝ (E := H)).continuous.comp hb
  have := (ContinuousLinearMap.smulRightL ℝ H (H →L[ℝ] ℝ)).continuous₂.comp (h1.prodMk h1)
  exact this

lemma integral_clm2_apply {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → H →L[ℝ] H →L[ℝ] ℝ) (hc : Continuous f) (M : ℝ) (hM : ∀ a, ‖f a‖ ≤ M) (x y : H) :
    (∫ a, f a ∂μ) x y = ∫ a, f a x y ∂μ := by
  have h1 : @TopologicalSpace.PseudoMetrizableSpace (H →L[ℝ] H →L[ℝ] ℝ)
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace := inferInstance
  have h2 : @TopologicalSpace.PseudoMetrizableSpace (H →L[ℝ] H →L[ℝ] ℝ)
      ContinuousLinearMap.topologicalSpace := h1
  have hI := Integrable.of_bound (E := H →L[ℝ] H →L[ℝ] ℝ) (μ := μ) (f := f) (C := M)
    hc.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  rw [ContinuousLinearMap.integral_apply hI x]
  have hc2 : Continuous fun a => f a x :=
    (ContinuousLinearMap.apply ℝ (H →L[ℝ] ℝ) x).continuous.comp hc
  have hI2 : Integrable (fun a => f a x) μ := by
    refine Integrable.of_bound (C := M * ‖x‖) hc2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    calc ‖f a x‖ ≤ ‖f a‖ * ‖x‖ := (f a).le_opNorm x
      _ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hM a) (norm_nonneg _)
  rw [ContinuousLinearMap.integral_apply hI2 y]

lemma outerCov_apply {b : Torus d → H} (hb : Continuous b) {M : ℝ} (hM : ∀ u, ‖b u‖ ^ 2 ≤ M)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] (x y : H) :
    outerCov b μ x y = ∫ u, inner ℝ (b u) x * inner ℝ (b u) y ∂μ := by
  have e1 : outerCov b μ = ∫ u, Phi b u ∂μ := rfl
  rw [e1, integral_clm2_apply μ (Phi b) (continuous_Phi hb) M (fun u => by rw [norm_Phi]; exact hM u)]
  simp only [Phi_apply]

lemma integrable_inner_mul {b : Torus d → H} (hb : Continuous b) {M : ℝ} (hM : ∀ u, ‖b u‖ ^ 2 ≤ M)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] (x y : H) :
    Integrable (fun u => inner ℝ (b u) x * inner ℝ (b u) y) μ := by
  have hc : Continuous fun u => inner ℝ (b u) x * inner ℝ (b u) y :=
    (hb.inner continuous_const).mul (hb.inner continuous_const)
  refine Integrable.of_bound (C := M * (‖x‖ * ‖y‖)) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |inner ℝ (b u) x| ≤ ‖b u‖ * ‖x‖ := abs_real_inner_le_norm _ _
  have h2 : |inner ℝ (b u) y| ≤ ‖b u‖ * ‖y‖ := abs_real_inner_le_norm _ _
  calc |inner ℝ (b u) x| * |inner ℝ (b u) y| ≤ (‖b u‖ * ‖x‖) * (‖b u‖ * ‖y‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = ‖b u‖ ^ 2 * (‖x‖ * ‖y‖) := by ring
    _ ≤ M * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_right (hM u) (by positivity)

lemma isTraceClassCov_outerCov [SecondCountableTopology H] {b : Torus d → H} (hb : Continuous b)
    {M : ℝ} (hM : ∀ u, ‖b u‖ ^ 2 ≤ M)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] : IsTraceClassCov (outerCov b μ) := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · rw [outerCov_apply hb hM, outerCov_apply hb hM]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  · rw [outerCov_apply hb hM]
    exact integral_nonneg fun u => mul_self_nonneg _
  · obtain ⟨κ, -, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
    refine ⟨κ, e, ?_⟩
    have hnn : ∀ i, 0 ≤ outerCov b μ (e i) (e i) := fun i => by
      rw [outerCov_apply hb hM]; exact integral_nonneg fun u => mul_self_nonneg _
    refine summable_of_sum_le (c := M * (μ Set.univ).toReal) hnn fun F => ?_
    simp only [outerCov_apply hb hM]
    rw [← integral_finset_sum _ fun i _ => integrable_inner_mul hb hM μ (e i) (e i)]
    calc ∫ u, ∑ i ∈ F, inner ℝ (b u) (e i) * inner ℝ (b u) (e i) ∂μ
        ≤ ∫ u, M ∂μ := by
          refine integral_mono (integrable_finset_sum _ fun i _ => integrable_inner_mul hb hM μ _ _)
            (integrable_const _) fun u => ?_
          have := e.orthonormal.sum_inner_products_le (b u) (s := F)
          simp only [Real.norm_eq_abs, sq_abs] at this
          calc ∑ i ∈ F, inner ℝ (b u) (e i) * inner ℝ (b u) (e i)
              = ∑ i ∈ F, inner ℝ (e i) (b u) ^ 2 := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [real_inner_comm (b u) (e i)]; ring
            _ ≤ ‖b u‖ ^ 2 := this
            _ ≤ M := hM u
      _ = M * (μ Set.univ).toReal := by
          rw [integral_const, smul_eq_mul]; simp [Measure.real, mul_comm]

end Outer

section Feat

/-- the standard Hilbert basis of the feature space. -/
def hb (d : ℕ) : HilbertBasis (Lattice d) ℝ (FeatureSpace d) := default

lemma inner_hb_left (k : Lattice d) (x : FeatureSpace d) : inner ℝ (hb d k : FeatureSpace d) x = x k := by
  rw [← HilbertBasis.repr_apply_apply]
  rfl

lemma inner_hb_right (k : Lattice d) (x : FeatureSpace d) : inner ℝ x (hb d k : FeatureSpace d) = x k := by
  rw [real_inner_comm, inner_hb_left]

lemma inner_chartFeature_hb (r : ℕ) (hr : d < r) (u : Torus d) (k : Lattice d) :
    inner ℝ (chartFeature (d := d) r u) (hb d k : FeatureSpace d) =
      Real.sqrt (chartWeight r k) * chartBasis k u := by
  rw [inner_hb_right, chartFeature_apply r hr]

lemma inner_chartFeature (r : ℕ) (hr : d < r) (u : Torus d) (y : FeatureSpace d) :
    inner ℝ (chartFeature (d := d) r u) y =
      ∑' k, y k * (Real.sqrt (chartWeight r k) * chartBasis k u) := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [chartFeature_apply r hr]
  simp [mul_comm]

lemma summable_abs_mul_sqrt (r : ℕ) (hr : d < r) (y : FeatureSpace d) :
    Summable fun k => |y k| * Real.sqrt (chartWeight r k) := by
  have hy : Summable fun k => y k ^ 2 := by
    have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).1 y.2
    simpa [Real.rpow_two] using this
  have hw := summable_chartWeight (d := d) r hr
  refine ((hy.add hw).mul_left (1 / 2)).of_nonneg_of_le (fun k => by
    have := (chartWeight_pos r k).le; positivity) fun k => ?_
  have h0 := (chartWeight_pos r k).le
  have h1 := Real.sq_sqrt h0
  nlinarith [sq_nonneg (|y k| - Real.sqrt (chartWeight r k)), sq_abs (y k)]

end Feat

section Diag

lemma outerCov_chart_apply (r : ℕ) (hr : d < r) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (x y : FeatureSpace d) :
    outerCov (chartFeature (d := d) r) μ x y =
      ∫ u, inner ℝ (chartFeature (d := d) r u) x * inner ℝ (chartFeature (d := d) r u) y ∂μ :=
  outerCov_apply (continuous_chartFeature r hr) (M := 2 * ∑' k : Lattice d, chartWeight r k)
    (fun u => norm_sq_chartFeature_le r hr u) μ x y

lemma outerCov_vol_diag (r : ℕ) (hr : d < r) (i : Lattice d) (y : FeatureSpace d) :
    outerCov (chartFeature (d := d) r) (volume : Measure (Torus d)) (hb d i) y =
      chartWeight r i * inner ℝ (hb d i : FeatureSpace d) y := by
  rw [outerCov_chart_apply r hr]
  simp_rw [inner_chartFeature_hb r hr, inner_chartFeature r hr, inner_hb_left]
  set F : Lattice d → Torus d → ℝ := fun k u =>
    Real.sqrt (chartWeight r i) * chartBasis i u * (y k * (Real.sqrt (chartWeight r k) * chartBasis k u))
    with hF
  have hmul : ∀ u : Torus d, Real.sqrt (chartWeight r i) * chartBasis i u *
      ∑' k, y k * (Real.sqrt (chartWeight r k) * chartBasis k u) = ∑' k, F k u := by
    intro u; rw [← tsum_mul_left]
  simp_rw [hmul]
  have hcont : ∀ k, Continuous (F k) := fun k => by
    simp only [hF]
    exact (continuous_const.mul (continuous_chartBasis i)).mul
      (continuous_const.mul (continuous_const.mul (continuous_chartBasis k)))
  have hFint : ∀ k, Integrable (F k) (volume : Measure (Torus d)) := fun k =>
    (hcont k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ k u, ‖F k u‖ ≤ 2 * Real.sqrt (chartWeight r i) * (|y k| * Real.sqrt (chartWeight r k)) := by
    intro k u
    simp only [hF]
    rw [Real.norm_eq_abs]
    have h1 := abs_chartBasis_le i u
    have h2 := abs_chartBasis_le k u
    have hs0 := Real.sqrt_nonneg (chartWeight r i)
    have hs1 := Real.sqrt_nonneg (chartWeight r k)
    have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hs1]
    calc Real.sqrt (chartWeight r i) * |chartBasis i u| * (|y k| * (Real.sqrt (chartWeight r k) * |chartBasis k u|))
        ≤ Real.sqrt (chartWeight r i) * Real.sqrt 2 * (|y k| * (Real.sqrt (chartWeight r k) * Real.sqrt 2)) := by
          gcongr
      _ = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt (chartWeight r i) *
            (|y k| * Real.sqrt (chartWeight r k))) := by ring
      _ = 2 * Real.sqrt (chartWeight r i) * (|y k| * Real.sqrt (chartWeight r k)) := by
          rw [h22]; ring
  have hsumn : Summable fun k => ∫ u, ‖F k u‖ := by
    refine ((summable_abs_mul_sqrt r hr y).mul_left (2 * Real.sqrt (chartWeight r i))).of_nonneg_of_le
      (fun k => integral_nonneg fun u => norm_nonneg _) fun k => ?_
    calc ∫ u, ‖F k u‖ ≤ ∫ u : Torus d, 2 * Real.sqrt (chartWeight r i) * (|y k| * Real.sqrt (chartWeight r k)) :=
          integral_mono ((hFint k).norm) (integrable_const _) (hbd k)
      _ = _ := by simp
  rw [← integral_tsum_of_summable_integral_norm hFint hsumn]
  have hk : ∀ k, ∫ u, F k u = if k = i then chartWeight r i * y i else 0 := by
    intro k
    have : ∀ u, F k u = (Real.sqrt (chartWeight r i) * (y k * Real.sqrt (chartWeight r k))) *
        (chartBasis i u * chartBasis k u) := fun u => by simp only [hF]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_chartBasis_mul]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, mul_one]
      have h0 := (chartWeight_pos r k).le
      have h3 := Real.mul_self_sqrt h0
      rw [show Real.sqrt (chartWeight r k) * (y k * Real.sqrt (chartWeight r k)) =
        (Real.sqrt (chartWeight r k) * Real.sqrt (chartWeight r k)) * y k by ring, h3]
    · simp [hki, Ne.symm hki]
  simp_rw [hk]
  rw [tsum_eq_single i (fun k hk' => by simp [hk'])]
  simp

end Diag

section Cmp

lemma measure_cmp (ν : Measure (Torus d)) (h : Torus d → ℝ)
    (hν : ν = volume.withDensity fun u => ENNReal.ofReal (h u)) (lo hi : ℝ)
    (hh : ∀ᵐ u : Torus d, lo ≤ h u ∧ h u ≤ hi) :
    ENNReal.ofReal lo • (volume : Measure (Torus d)) ≤ ν ∧ ν ≤ ENNReal.ofReal hi • volume := by
  constructor
  · rw [Measure.le_iff]
    intro s hs
    rw [hν, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_of_ae hh).mono fun u hu => ENNReal.ofReal_le_ofReal hu.1)
  · rw [Measure.le_iff]
    intro s hs
    rw [hν, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_of_ae hh).mono fun u hu => ENNReal.ofReal_le_ofReal hu.2)

lemma chart_hcD (r : ℕ) (hr : d < r) (ν : Measure (Torus d)) [IsFiniteMeasure ν] (lo : ℝ) (hlo : 0 ≤ lo)
    (hle : ENNReal.ofReal lo • (volume : Measure (Torus d)) ≤ ν) (x : FeatureSpace d) :
    lo * outerCov (chartFeature (d := d) r) (volume : Measure (Torus d)) x x ≤
      outerCov (chartFeature (d := d) r) ν x x := by
  rw [outerCov_chart_apply r hr, outerCov_chart_apply r hr]
  have hint := integrable_inner_mul (continuous_chartFeature (d := d) r hr)
    (M := 2 * ∑' k : Lattice d, chartWeight r k) (fun u => norm_sq_chartFeature_le r hr u) ν x x
  have hnn : (0 : Torus d → ℝ) ≤ᵐ[ν] fun u => inner ℝ (chartFeature (d := d) r u) x *
      inner ℝ (chartFeature (d := d) r u) x :=
    Filter.Eventually.of_forall fun u => mul_self_nonneg _
  have := integral_mono_measure hle hnn hint
  rw [integral_smul_measure, ENNReal.toReal_ofReal hlo, smul_eq_mul] at this
  exact this

lemma outerCov_chart_entry (r : ℕ) (hr : d < r) (ν : Measure (Torus d)) [IsFiniteMeasure ν]
    (i j : Lattice d) :
    outerCov (chartFeature (d := d) r) ν (hb d i) (hb d j) =
      Real.sqrt (chartWeight r i) * Real.sqrt (chartWeight r j) *
        ∫ u, chartBasis i u * chartBasis j u ∂ν := by
  rw [outerCov_chart_apply r hr, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [inner_chartFeature_hb r hr]
  ring

lemma integral_chart_empirical {X : Type*} [MeasurableSpace X] (U : Set X) (hU : MeasurableSet U)
    (ψ : X → Torus d) (hψ : Measurable ψ) (N : ℕ) (pts : Fin N → X) (φ : Torus d → ℝ)
    (hφ : Measurable φ) (B : ℝ) (hB : ∀ u, |φ u| ≤ B) :
    ∫ u, φ u ∂(((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)).restrict U).map ψ)) =
      (N : ℝ)⁻¹ * ∑ i, U.indicator (φ ∘ ψ) (pts i) := by
  have hF : Measurable (U.indicator (φ ∘ ψ)) := (hφ.comp hψ).indicator hU
  rw [integral_map hψ.aemeasurable hφ.aestronglyMeasurable]
  have : ∫ x, φ (ψ x) ∂(((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)).restrict U) =
      ∫ x, U.indicator (φ ∘ ψ) x ∂((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)) := by
    rw [integral_indicator hU]; rfl
  rw [this, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  rw [integral_finsetSum_measure]
  · exact Finset.sum_congr rfl fun i _ => integral_dirac' _ _ hF.stronglyMeasurable
  · intro i _
    refine Integrable.of_bound (C := B) hF.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx, Function.comp]; exact hB _
    · simp only [Set.indicator_of_notMem hx, abs_zero]
      exact (abs_nonneg _).trans (hB 0)

lemma integral_chart_nu {X : Type*} [MeasurableSpace X] (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (ψ : X → Torus d) (hψ : Measurable ψ) (φ : Torus d → ℝ) (hφ : Measurable φ) :
    ∫ u, φ u ∂((μ.restrict U).map ψ) = ∫ x, U.indicator (φ ∘ ψ) x ∂μ := by
  rw [integral_map hψ.aemeasurable hφ.aestronglyMeasurable, integral_indicator hU]
  rfl

lemma isFiniteMeasure_empirical {X : Type*} [MeasurableSpace X] (N : ℕ) (hN : 1 ≤ N) (pts : Fin N → X) :
    IsFiniteMeasure ((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by exact_mod_cast hN)) (ENNReal.natCast_lt_top N)

lemma secondCountable_featureSpace (d : ℕ) : SecondCountableTopology (FeatureSpace d) := by
  let b : HilbertBasis (Lattice d) ℝ (lp (fun _ : Lattice d => ℝ) 2) := default
  have hdense := b.dense_span
  have hcount : (Set.range b).Countable := Set.countable_range _
  have hsep := TopologicalSpace.IsSeparable.span (R := ℝ) hcount.isSeparable
  have : TopologicalSpace.IsSeparable (Set.univ : Set (lp (fun _ : Lattice d => ℝ) 2)) := by
    have h2 := hsep.closure
    rwa [← Submodule.topologicalClosure_coe, hdense, Submodule.top_coe] at h2
  have : TopologicalSpace.SeparableSpace (lp (fun _ : Lattice d => ℝ) 2) :=
    TopologicalSpace.isSeparable_univ_iff.mp this
  exact (inferInstance : SecondCountableTopology (lp (fun _ : Lattice d => ℝ) 2))

lemma relQuad_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*}
    (e : HilbertBasis ι ℝ H) (dd : ι → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (Δ : H →L[ℝ] H →L[ℝ] ℝ) :
    relQuad e dd (κ • Δ) = ENNReal.ofReal (κ ^ 2) * relQuad e dd Δ := by
  unfold relQuad
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg κ)]
  congr 1
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma isTraceClassCov_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsTraceClassCov (κ • C) := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hC.symm x y]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hκ (hC.nonneg x)
  · obtain ⟨ι, b, hs⟩ := hC.trace
    exact ⟨ι, b, (hs.mul_left κ).congr fun i => by simp⟩

lemma abs_chart_prod_le (i j : Lattice d) (u : Torus d) :
    |chartBasis i u * chartBasis j u| ≤ 2 := by
  rw [abs_mul]
  have h1 := abs_chartBasis_le i u
  have h2 := abs_chartBasis_le j u
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc |chartBasis i u| * |chartBasis j u| ≤ Real.sqrt 2 * Real.sqrt 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 := h22

lemma integral_chart_prod_sq_le (i j : Lattice d) :
    ∫ u : Torus d, (chartBasis i u * chartBasis j u) ^ 2 ≤ 2 := by
  have h1 : ∫ u : Torus d, chartBasis j u * chartBasis j u = 1 := by
    rw [integral_chartBasis_mul]; simp
  have hc : ∀ k : Lattice d, Continuous fun u : Torus d => chartBasis k u * chartBasis k u :=
    fun k => (continuous_chartBasis k).mul (continuous_chartBasis k)
  have hint : ∀ k : Lattice d, Integrable (fun u : Torus d => chartBasis k u * chartBasis k u) volume :=
    fun k => (hc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun u : Torus d => (chartBasis i u * chartBasis j u) ^ 2) volume :=
    (((continuous_chartBasis i).mul (continuous_chartBasis j)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ∫ u : Torus d, (chartBasis i u * chartBasis j u) ^ 2
      ≤ ∫ u : Torus d, 2 * (chartBasis j u * chartBasis j u) := by
        refine integral_mono hint2 ((hint j).const_mul 2) fun u => ?_
        have := chartBasis_sq_le i u
        nlinarith [mul_self_nonneg (chartBasis j u)]
    _ = 2 := by rw [integral_const_mul, h1]; ring

lemma sq_integral_chart_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (ψ : X → Torus d) (hψ : Measurable ψ)
    (hi : ℝ) (hle : (μ.restrict U).map ψ ≤ ENNReal.ofReal hi • (volume : Measure (Torus d)))
    (i j : Lattice d) :
    ∫ x, (U.indicator (fun x => chartBasis i (ψ x) * chartBasis j (ψ x)) x) ^ 2 ∂μ ≤
      2 * max hi 0 := by
  have hφ : Measurable fun u : Torus d => (chartBasis i u * chartBasis j u) ^ 2 :=
    (((continuous_chartBasis i).mul (continuous_chartBasis j)).pow 2).measurable
  have e1 : ∫ x, (U.indicator (fun x => chartBasis i (ψ x) * chartBasis j (ψ x)) x) ^ 2 ∂μ =
      ∫ u, (chartBasis i u * chartBasis j u) ^ 2 ∂((μ.restrict U).map ψ) := by
    rw [integral_chart_nu μ U hU ψ hψ _ hφ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U <;> simp [Set.indicator, hx, Function.comp]
  rw [e1]
  have hint : Integrable (fun u : Torus d => (chartBasis i u * chartBasis j u) ^ 2)
      (ENNReal.ofReal hi • (volume : Measure (Torus d))) := by
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    exact (((continuous_chartBasis i).mul (continuous_chartBasis j)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnn : (0 : Torus d → ℝ) ≤ᵐ[ENNReal.ofReal hi • (volume : Measure (Torus d))]
      fun u => (chartBasis i u * chartBasis j u) ^ 2 := Filter.Eventually.of_forall fun u => sq_nonneg _
  have := integral_mono_measure hle hnn hint
  rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal' ] at this
  refine this.trans ?_
  exact mul_le_mul_of_nonneg_left (integral_chart_prod_sq_le i j) (le_max_right _ _) |>.trans_eq (by ring)

lemma chart_entry_eq (r : ℕ) (hr : d < r) {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : Set X) (hU : MeasurableSet U)
    (ψ : X → Torus d) (hψ : Measurable ψ) (N : ℕ) (hN : 1 ≤ N) (pts : Fin N → X) (i j : Lattice d) :
    ((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (pts k)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) (hb d i) (hb d j)) ^ 2 /
          (chartWeight r i + chartWeight r j) =
      chartWeight r i * chartWeight r j / (chartWeight r i + chartWeight r j) *
        ((N : ℝ)⁻¹ * ∑ k, U.indicator ((fun u => chartBasis i u * chartBasis j u) ∘ ψ) (pts k) -
          ∫ x, U.indicator ((fun u => chartBasis i u * chartBasis j u) ∘ ψ) x ∂μ) ^ 2 := by
  have hfm : Measurable fun u : Torus d => chartBasis i u * chartBasis j u :=
    ((continuous_chartBasis i).mul (continuous_chartBasis j)).measurable
  haveI := isFiniteMeasure_empirical N hN pts
  rw [_root_.sub_apply, ContinuousLinearMap.sub_apply, outerCov_chart_entry r hr,
    outerCov_chart_entry r hr]
  have e1 := integral_chart_empirical U hU ψ hψ N pts _ hfm 2 (fun u => abs_chart_prod_le i j u)
  have e2 := integral_chart_nu μ U hU ψ hψ _ hfm
  rw [e1, e2, ← mul_sub]
  have hi0 := chartWeight_pos r i
  have hj0 := chartWeight_pos r j
  have h1 := Real.sq_sqrt hi0.le
  have h2 := Real.sq_sqrt hj0.le
  rw [mul_pow, mul_pow, h1, h2]
  field_simp

lemma pair_bound (r : ℕ) (hr : d < r) {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : Set X) (hU : MeasurableSet U)
    (ψ : X → Torus d) (hψ : Measurable ψ) (hi : ℝ)
    (hle : (μ.restrict U).map ψ ≤ ENNReal.ofReal hi • (volume : Measure (Torus d)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → X) (hxs : ∀ i, Measurable (xs i))
    (g : X → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (Cin δ : ℝ)
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
    (hvar : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
        ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ))
    (i j : Lattice d) :
    ∫⁻ ω, ENNReal.ofReal (((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) (hb d i) (hb d j)) ^ 2 /
          (chartWeight r i + chartWeight r j)) ∂P ≤
      ENNReal.ofReal (chartWeight r i * chartWeight r j / (chartWeight r i + chartWeight r j) *
        (2 * max hi 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2))) := by
  set fij : Torus d → ℝ := fun u => chartBasis i u * chartBasis j u with hfij
  have hfm : Measurable fij := ((continuous_chartBasis i).mul (continuous_chartBasis j)).measurable
  set F : X → ℝ := U.indicator (fij ∘ ψ) with hF
  have hFm : Measurable F := (hfm.comp hψ).indicator hU
  have hFB : ∀ x, |F x| ≤ 2 := by
    intro x
    by_cases hx : x ∈ U
    · simp only [hF, Set.indicator_of_mem hx, Function.comp]; exact abs_chart_prod_le i j _
    · simp only [hF, Set.indicator_of_notMem hx, abs_zero]; norm_num
  have hAle : ∫ x, F x ^ 2 ∂μ ≤ 2 * max hi 0 := sq_integral_chart_le μ U hU ψ hψ hi hle i j
  have hA0 : 0 ≤ ∫ x, F x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  set a : ℝ := ∫ x, F x ∂μ with ha
  set Y : Ω → ℝ := fun ω => (N : ℝ)⁻¹ * ∑ k, F (xs k ω) with hY
  have hYm : Measurable Y := measurable_const.mul (Finset.measurable_sum _ fun k _ => hFm.comp (hxs k))
  set w : ℝ := chartWeight r i * chartWeight r j / (chartWeight r i + chartWeight r j) with hw
  have hw0 : 0 ≤ w := by
    have := chartWeight_pos r i; have := chartWeight_pos r j; positivity
  have hentry : ∀ ω, ((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) (hb d i) (hb d j)) ^ 2 /
          (chartWeight r i + chartWeight r j) = w * (Y ω - a) ^ 2 :=
    fun ω => chart_entry_eq r hr μ U hU ψ hψ N hN (fun k => xs k ω) i j
  simp_rw [hentry]
  have hYB : ∀ ω, |Y ω| ≤ 2 := by
    intro ω
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [hY]
    rw [abs_mul, abs_of_pos (inv_pos.2 hN0)]
    have : |∑ k, F (xs k ω)| ≤ N * 2 := by
      calc |∑ k, F (xs k ω)| ≤ ∑ k, |F (xs k ω)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin N, (2 : ℝ) := Finset.sum_le_sum fun k _ => hFB _
        _ = N * 2 := by simp
    calc (N : ℝ)⁻¹ * |∑ k, F (xs k ω)| ≤ (N : ℝ)⁻¹ * (N * 2) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hN0.le)
      _ = 2 := by field_simp
  have hint : Integrable (fun ω => (Y ω - a) ^ 2) P := by
    refine Integrable.of_bound (C := (2 + |a|) ^ 2) ((hYm.sub_const a).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have : |Y ω - a| ≤ 2 + |a| := (abs_sub _ _).trans (by linarith [hYB ω])
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hsm := second_moment_bound μ P N hN xs hxs g hg hmarg Cin δ hgL2 hvar F hFm 2 hFB
  have hbd : ∫ ω, (Y ω - a) ^ 2 ∂P ≤ 2 * max hi 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) := by
    refine hsm.trans ?_
    have hfac : 0 ≤ |Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2 := by positivity
    calc |Cin| * (N : ℝ)⁻¹ * ∫ x, F x ^ 2 ∂μ + (∫ x, F x ^ 2 ∂μ) * (Cin * δ) ^ 2
        = (∫ x, F x ^ 2 ∂μ) * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAle hfac
  calc ∫⁻ ω, ENNReal.ofReal (w * (Y ω - a) ^ 2) ∂P
      = ENNReal.ofReal w * ∫⁻ ω, ENNReal.ofReal ((Y ω - a) ^ 2) ∂P := by
        rw [← lintegral_const_mul _ ((hYm.sub_const a).pow_const 2).ennreal_ofReal]
        exact lintegral_congr fun ω => ENNReal.ofReal_mul hw0
    _ = ENNReal.ofReal w * ENNReal.ofReal (∫ ω, (Y ω - a) ^ 2 ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal (2 * max hi 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)) :=
        by gcongr
    _ = _ := (ENNReal.ofReal_mul hw0).symm

lemma sum_w_le (r : ℕ) (hr : d < r) :
    ∑' p : Lattice d × Lattice d, ENNReal.ofReal (chartWeight r p.1 * chartWeight r p.2 /
        (chartWeight r p.1 + chartWeight r p.2)) ≤
      ENNReal.ofReal ((∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2) := by
  have hs := summable_sqrt_chartWeight (d := d) r hr
  have hnn : ∀ k : Lattice d, 0 ≤ Real.sqrt (chartWeight r k) := fun k => Real.sqrt_nonneg _
  have hq : Summable fun p : Lattice d × Lattice d =>
      Real.sqrt (chartWeight r p.1) * Real.sqrt (chartWeight r p.2) :=
    hs.mul_of_nonneg hs hnn hnn
  have htsum : ∑' p : Lattice d × Lattice d, Real.sqrt (chartWeight r p.1) * Real.sqrt (chartWeight r p.2) =
      (∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2 := by
    rw [sq, tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_of_nonneg (hnn _)] using hs)
      (by simpa [Real.norm_of_nonneg (hnn _)] using hs)]
  calc ∑' p : Lattice d × Lattice d, ENNReal.ofReal (chartWeight r p.1 * chartWeight r p.2 /
        (chartWeight r p.1 + chartWeight r p.2))
      ≤ ∑' p : Lattice d × Lattice d, ENNReal.ofReal
        (Real.sqrt (chartWeight r p.1) * Real.sqrt (chartWeight r p.2)) := by
        refine ENNReal.tsum_le_tsum fun p => ENNReal.ofReal_le_ofReal ?_
        have h1 := chartWeight_pos r p.1
        have h2 := chartWeight_pos r p.2
        have e1 := Real.sq_sqrt h1.le
        have e2 := Real.sq_sqrt h2.le
        set x := Real.sqrt (chartWeight r p.1)
        set y := Real.sqrt (chartWeight r p.2)
        have hx : 0 < x := Real.sqrt_pos.2 h1
        have hy : 0 < y := Real.sqrt_pos.2 h2
        rw [← e1, ← e2, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (x - y), mul_pos hx hy]
    _ = ENNReal.ofReal (∑' p : Lattice d × Lattice d,
        Real.sqrt (chartWeight r p.1) * Real.sqrt (chartWeight r p.2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (hnn _) (hnn _)) hq).symm
    _ = _ := by rw [htsum]

theorem chart_aux (r : ℕ) (hr : d < r) (c Cdens Cin : ℝ) (hc : 0 < c)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (ψ : X → Torus d) (hψ : Measurable ψ)
    (α : ℝ) (hα : 0 < α) (h : Torus d → ℝ)
    (hν : (μ.restrict U).map ψ = volume.withDensity fun u => ENNReal.ofReal (h u))
    (hh : ∀ᵐ u : Torus d, c * α ≤ h u ∧ h u ≤ Cdens * α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → X) (hxs : ∀ i, Measurable (xs i)) (δ : ℝ)
    (g : X → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
    (hvar : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
        ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ))
    (κ : ℝ) (hκ : 0 < κ) :
    ∫⁻ ω, ENNReal.ofReal (bures2
        (κ • outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)))
        (κ • outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ))) ∂P ≤
      ENNReal.ofReal (κ * (4 * (∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2 * max Cdens 0 *
        (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) / c)) := by
  classical
  letI : MeasurableSpace (FeatureSpace d) := borel _
  haveI : BorelSpace (FeatureSpace d) := ⟨rfl⟩
  haveI := secondCountable_featureSpace d
  have hbc := continuous_chartFeature (d := d) r hr
  have hM : ∀ u, ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k :=
    fun u => norm_sq_chartFeature_le r hr u
  set ν : Measure (Torus d) := (μ.restrict U).map ψ with hνdef
  have hD : IsTraceClassCov (outerCov (chartFeature (d := d) r) ν) :=
    isTraceClassCov_outerCov hbc hM ν
  have hD₀e : ∀ i y, outerCov (chartFeature (d := d) r) (volume : Measure (Torus d)) (hb d i) y =
      chartWeight r i * inner ℝ (hb d i : FeatureSpace d) y := outerCov_vol_diag r hr
  have hmc := measure_cmp ν h hν (c * α) (Cdens * α) hh
  have hcD0 := chart_hcD r hr ν (c * α) (by positivity) hmc.1
  have hdd : ∀ i : Lattice d, 0 < chartWeight r i := chartWeight_pos r
  have hcα : 0 < c * α := by positivity
  -- pointwise application of the Bures bound
  have hpt : ∀ ω, ENNReal.ofReal (bures2
        (κ • outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)))
        (κ • outerCov (chartFeature (d := d) r) ν)) ≤
      ENNReal.ofReal (2 * κ / (c * α)) * relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) := by
    intro ω
    haveI := isFiniteMeasure_empirical N hN (fun k => xs k ω)
    have hCN := isTraceClassCov_outerCov hbc hM
      (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))
    have K := RelCov.bures2_le (hb d) (chartWeight r) hdd _ hD₀e (c * α * κ) (by positivity)
      (fun x => by
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (hcD0 x) hκ.le
        nlinarith)
      (isTraceClassCov_smul hCN hκ.le) (isTraceClassCov_smul hD hκ.le)
    have esub : ∀ A B : FeatureSpace d →L[ℝ] FeatureSpace d →L[ℝ] ℝ, κ • A - κ • B = κ • (A - B) :=
      fun A B => (smul_sub κ A B).symm
    rw [esub, relQuad_smul _ _ κ hκ.le] at K
    refine K.trans (le_of_eq ?_)
    rw [← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  -- integrate in ω
  set S1 : ℝ := ∑' k : Lattice d, Real.sqrt (chartWeight r k) with hS1
  set Bα : ℝ := 2 * max (Cdens * α) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) with hBα
  have hmeas : ∀ p : Lattice d × Lattice d, AEMeasurable (fun ω => ENNReal.ofReal
      (((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
          (chartWeight r p.1 + chartWeight r p.2))) P := by
    intro p
    refine Measurable.aemeasurable ?_
    have hfm : Measurable fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u :=
      ((continuous_chartBasis p.1).mul (continuous_chartBasis p.2)).measurable
    have hFm : Measurable (U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ)) :=
      (hfm.comp hψ).indicator hU
    have hfun : (fun ω => ENNReal.ofReal
      (((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
          (chartWeight r p.1 + chartWeight r p.2))) = fun ω => ENNReal.ofReal
      (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2) *
        ((N : ℝ)⁻¹ * ∑ k, U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ) (xs k ω) -
          ∫ x, U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ) x ∂μ) ^ 2) := by
      funext ω
      rw [hνdef, chart_entry_eq r hr μ U hU ψ hψ N hN (fun k => xs k ω) p.1 p.2]
    rw [hfun]
    exact Measurable.ennreal_ofReal (measurable_const.mul
      (((measurable_const.mul (Finset.measurable_sum _ fun k _ => hFm.comp (hxs k))).sub
        measurable_const).pow_const 2))
  have hrq : ∫⁻ ω, relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) ∂P ≤
      ENNReal.ofReal (S1 ^ 2) * ENNReal.ofReal Bα := by
    have e1 : ∫⁻ ω, relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r)
            (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
            outerCov (chartFeature (d := d) r) ν) ∂P =
        ∑' p : Lattice d × Lattice d, ∫⁻ ω, ENNReal.ofReal
          (((outerCov (chartFeature (d := d) r)
            (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
            outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
              (chartWeight r p.1 + chartWeight r p.2)) ∂P := by
      rw [← lintegral_tsum hmeas]; rfl
    have e2 : ∑' p : Lattice d × Lattice d, ∫⁻ ω, ENNReal.ofReal
          (((outerCov (chartFeature (d := d) r)
            (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
            outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
              (chartWeight r p.1 + chartWeight r p.2)) ∂P ≤
        ∑' p : Lattice d × Lattice d, ENNReal.ofReal
          (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2)) *
            ENNReal.ofReal Bα := by
      refine ENNReal.tsum_le_tsum fun p => ?_
      have hw0 : 0 ≤ chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2) := by
        have := chartWeight_pos r p.1; have := chartWeight_pos r p.2; positivity
      rw [← ENNReal.ofReal_mul hw0]
      exact pair_bound r hr μ U hU ψ hψ (Cdens * α) hmc.2 P N hN xs hxs g hg hmarg Cin δ hgL2 hvar p.1 p.2
    have e3 : ∑' p : Lattice d × Lattice d, ENNReal.ofReal
          (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2)) *
            ENNReal.ofReal Bα =
        (∑' p : Lattice d × Lattice d, ENNReal.ofReal
          (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2))) *
            ENNReal.ofReal Bα := ENNReal.tsum_mul_right
    refine e1.le.trans (e2.trans (e3.le.trans ?_))
    gcongr
    exact sum_w_le r hr
  calc ∫⁻ ω, ENNReal.ofReal (bures2
        (κ • outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)))
        (κ • outerCov (chartFeature (d := d) r) ν)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * κ / (c * α)) * relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * κ / (c * α)) * ∫⁻ ω, relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * κ / (c * α)) * (ENNReal.ofReal (S1 ^ 2) * ENNReal.ofReal Bα) := by
        gcongr
    _ = ENNReal.ofReal (2 * κ / (c * α) * (S1 ^ 2 * Bα)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        have hmx : max (Cdens * α) 0 = max Cdens 0 * α := by
          rcases le_total Cdens 0 with h0 | h0
          · rw [max_eq_right (by nlinarith), max_eq_right h0]; simp
          · rw [max_eq_left (mul_nonneg h0 hα.le), max_eq_left h0]
        simp only [hBα, hmx]
        field_simp
        ring


end Cmp


end ChartPart1
end ChartAux


open ProbabilityTheory in
/-- Lemma 3.30, restated (downstream proof). -/
theorem chart_current_proof {d : ℕ} (hd : 1 ≤ d) (r : ℕ) (hr : d < r) (c Cdens Cin : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
        (U : Set X) (_ : MeasurableSet U) (ψ : X → Torus d) (_ : Measurable ψ)
        (α : ℝ) (_ : 0 < α) (h : Torus d → ℝ)
        (_ : (μ.restrict U).map ψ = volume.withDensity fun u => ENNReal.ofReal (h u))
        (_ : ∀ᵐ u, c * α ≤ h u ∧ h u ≤ Cdens * α)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (_ : 1 ≤ N) (xs : Fin N → Ω → X) (_ : ∀ i, Measurable (xs i)) (δ : ℝ)
        (g : X → ℝ) (_ : Measurable g)
        (_ : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
        (_ : ∀ᵐ x ∂μ, g x ≤ Cin)
        (_ : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
        (_ : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
          evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
            ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ)),
        (∫⁻ ω, ENNReal.ofReal (bures2
            (outerCov (chartFeature (d := d) r)
              ((((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))))
            (outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ))) ∂P ≤
          ENNReal.ofReal (C * ((N : ℝ)⁻¹ + δ ^ 2))) ∧
        ∀ κ : ℝ, 0 < κ →
          ∫⁻ ω, ENNReal.ofReal (bures2
            (κ • outerCov (chartFeature (d := d) r)
              ((((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))))
            (κ • outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ))) ∂P ≤
          ENNReal.ofReal (κ * (C * ((N : ℝ)⁻¹ + δ ^ 2))) := by
  set S1 : ℝ := ∑' k : Lattice d, Real.sqrt (chartWeight r k) with hS1
  set C0 : ℝ := 4 * S1 ^ 2 * max Cdens 0 * max |Cin| (Cin ^ 2) / c with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have hbd : ∀ (N : ℕ) (δ : ℝ), 4 * S1 ^ 2 * max Cdens 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) / c ≤
      C0 * ((N : ℝ)⁻¹ + δ ^ 2) := by
    intro N δ
    simp only [hC0]
    have h1 : |Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2 ≤ max |Cin| (Cin ^ 2) * ((N : ℝ)⁻¹ + δ ^ 2) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      have := le_max_left |Cin| (Cin ^ 2)
      have := le_max_right |Cin| (Cin ^ 2)
      rw [mul_pow]
      nlinarith [mul_nonneg hN0 (sub_nonneg.2 (le_max_left |Cin| (Cin ^ 2))),
        mul_nonneg (sq_nonneg δ) (sub_nonneg.2 (le_max_right |Cin| (Cin ^ 2)))]
    have hA : 0 ≤ 4 * S1 ^ 2 * max Cdens 0 / c := by positivity
    calc 4 * S1 ^ 2 * max Cdens 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) / c
        = (4 * S1 ^ 2 * max Cdens 0 / c) * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) := by ring
      _ ≤ (4 * S1 ^ 2 * max Cdens 0 / c) * (max |Cin| (Cin ^ 2) * ((N : ℝ)⁻¹ + δ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hA
      _ = _ := by ring
  refine ⟨C0, hC0nn, ?_⟩
  intro X _ μ _ U hU ψ hψ α hα h hν hh Ω _ P _ N hN xs hxs δ g hg hmarg _ hgL2 hvar
  refine ⟨?_, fun κ hκ => ?_⟩
  · have := ChartAux.chart_aux r hr c Cdens Cin hc μ U hU ψ hψ α hα h hν hh P N hN xs hxs δ g hg hmarg
      hgL2 hvar 1 one_pos
    simp only [one_smul, one_mul] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (hbd N δ))
  · have := ChartAux.chart_aux r hr c Cdens Cin hc μ U hU ψ hψ α hα h hν hh P N hN xs hxs δ g hg hmarg
      hgL2 hvar κ hκ
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (hbd N δ) hκ.le



section CheckStatements
open ProbabilityTheory
example {d : ℕ} := (@chart_current_proof d : type_of% (@chart_current d))
end CheckStatements

end Uniform
end HRS
