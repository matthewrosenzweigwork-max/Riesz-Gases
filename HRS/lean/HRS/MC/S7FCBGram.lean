import HRS.MC.S7FCBLpConv

/-!
# FC-B, part 9: the finite-rank structure of the averaged kernels

`FcbGram k` : `k(x,x') = ∑_i p_i(x) p_i(x')` with smooth `p_i`.  The Landau kernel `K_n(x - x')` is of this form,
hence `fcbT n f` is a smooth finite-rank symmetric kernel for symmetric integrable `f`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

theorem fcb_smooth_const (c : ℝ) : Torus.IsSmooth (fun _ : Torus d => c) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact contDiff_const

theorem fcb_smooth_mul {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    Torus.IsSmooth (fun x => φ x * ψ x) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift at *
  exact ContDiff.mul hφ hψ

theorem fcb_smooth_cs (k : Fin d) : Torus.IsSmooth (fcbCs k) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  have : (fcbCs k ∘ Torus.mk) = fun y : Euc d => Real.cos (2 * Real.pi * y k) := by
    funext y; exact fcbCs_mk k y
  rw [this]
  exact Real.contDiff_cos.comp (contDiff_const.mul ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff))

theorem fcb_smooth_sn (k : Fin d) : Torus.IsSmooth (fcbSn k) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  have : (fcbSn k ∘ Torus.mk) = fun y : Euc d => Real.sin (2 * Real.pi * y k) := by
    funext y; exact fcbSn_mk k y
  rw [this]
  exact Real.contDiff_sin.comp (contDiff_const.mul ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff))

theorem fcb_smooth_continuous {φ : Torus d → ℝ} (h : Torus.IsSmooth φ) : Continuous φ := by
  unfold Torus.IsSmooth Torus.IsCk at h
  exact KernelGrad.continuous_of_lift h.continuous

/-- `k(x,x') = ∑_i p_i(x) p_i(x')` with smooth `p_i`. -/
def FcbGram (k : Torus d → Torus d → ℝ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → Torus d → ℝ), (∀ i, Torus.IsSmooth (p i)) ∧
    ∀ x x', k x x' = ∑ i, p i x * p i x'

theorem FcbGram.one : FcbGram (d := d) (fun _ _ => 1) :=
  ⟨1, fun _ _ => 1, fun _ => fcb_smooth_const 1, fun x x' => by simp⟩

theorem FcbGram.const {c : ℝ} (hc : 0 ≤ c) : FcbGram (d := d) (fun _ _ => c) :=
  ⟨1, fun _ _ => Real.sqrt c, fun _ => fcb_smooth_const _, fun x x' => by
    simp [← sq, Real.sq_sqrt hc]⟩

theorem FcbGram.mul {k1 k2 : Torus d → Torus d → ℝ} (h1 : FcbGram k1) (h2 : FcbGram k2) :
    FcbGram (fun x x' => k1 x x' * k2 x x') := by
  obtain ⟨m1, p1, hs1, he1⟩ := h1
  obtain ⟨m2, p2, hs2, he2⟩ := h2
  refine ⟨m1 * m2, fun i => fun x => p1 (finProdFinEquiv.symm i).1 x * p2 (finProdFinEquiv.symm i).2 x,
    fun i => fcb_smooth_mul (hs1 _) (hs2 _), fun x x' => ?_⟩
  show k1 x x' * k2 x x' = ∑ i, (p1 (finProdFinEquiv.symm i).1 x * p2 (finProdFinEquiv.symm i).2 x) *
    (p1 (finProdFinEquiv.symm i).1 x' * p2 (finProdFinEquiv.symm i).2 x')
  rw [he1, he2, Finset.sum_mul_sum, ← Fintype.sum_prod_type' (f := fun a b =>
    p1 a x * p1 a x' * (p2 b x * p2 b x'))]
  refine (Fintype.sum_equiv finProdFinEquiv _ _ fun ab => ?_)
  simp only [Equiv.symm_apply_apply, finProdFinEquiv_symm_apply]
  ring

theorem FcbGram.pow {k : Torus d → Torus d → ℝ} (h : FcbGram k) (n : ℕ) :
    FcbGram (fun x x' => k x x' ^ n) := by
  induction n with
  | zero => simpa using (FcbGram.one (d := d))
  | succ n ih =>
    have := ih.mul h
    simpa [pow_succ] using this

theorem FcbGram.prod {ι : Type*} (s : Finset ι) {k : ι → Torus d → Torus d → ℝ}
    (h : ∀ i ∈ s, FcbGram (k i)) : FcbGram (fun x x' => ∏ i ∈ s, k i x x') := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (FcbGram.one (d := d))
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.prod_insert ha] using h1.mul h2

theorem fcbGram_base (k : Fin d) :
    FcbGram (fun x x' : Torus d => (1 + (fcbCs k x * fcbCs k x' + fcbSn k x * fcbSn k x')) / 2) := by
  refine ⟨3, ![fun _ => 1 / Real.sqrt 2, fun x => fcbCs k x / Real.sqrt 2,
    fun x => fcbSn k x / Real.sqrt 2], ?_, fun x x' => ?_⟩
  · intro i
    fin_cases i
    · exact fcb_smooth_const _
    · have := fcb_smooth_mul (fcb_smooth_cs k) (fcb_smooth_const (1 / Real.sqrt 2))
      simpa [div_eq_mul_inv] using this
    · have := fcb_smooth_mul (fcb_smooth_sn k) (fcb_smooth_const (1 / Real.sqrt 2))
      simpa [div_eq_mul_inv] using this
  · rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    have h3 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
    simp only [div_eq_mul_inv]
    linear_combination (-(1 + (fcbCs k x * fcbCs k x' + fcbSn k x * fcbSn k x'))) * h3

theorem fcbK_gram (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) :
    FcbGram (fun x x' : Torus d => fcbK d n (x - x')) := by
  have hZ := (fcbZ_pos hd hn).le
  have h1 : FcbGram (fun x x' : Torus d => ∏ k : Fin d, ((1 + (fcbCs k x * fcbCs k x' + fcbSn k x * fcbSn k x')) / 2) ^ n) :=
    FcbGram.prod Finset.univ fun k _ => (fcbGram_base k).pow n
  have h2 := (FcbGram.const (d := d) (inv_nonneg.2 hZ)).mul h1
  have e : (fun x x' : Torus d => fcbK d n (x - x')) =
      fun x x' => (fun (_ _ : Torus d) => (fcbZ d n)⁻¹) x x' *
        (fun x x' : Torus d => ∏ k : Fin d, ((1 + (fcbCs k x * fcbCs k x' + fcbSn k x * fcbSn k x')) / 2) ^ n) x x' := by
    funext x x'
    simp only [fcbK, fcbV, fcbU, fcbCs_sub]
    rw [div_eq_inv_mul]
  rw [e]; exact h2

end HRS.MC.Sec7.FCB
