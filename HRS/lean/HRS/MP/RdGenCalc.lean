import HRS.MP.RdGenAux

/-!
# Packet MPRGEN, stage 3b: weighted derivative classes and the pieces of the generator

`RgW w k c u`: `u ∈ C^k` with `‖D^n u(x)‖ ≤ c w(x)`, `n ≤ k`; closure under sums, products; the Laplacian, the
gradient components, and the components of the cancellation-convention convolution `∇g * h`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdGen
open HRS HRS.Whole

variable {d : ℕ}

/-- `C^k` with `‖D^n u(x)‖ ≤ c w(x)` for `n ≤ k`. -/
def RgW (w : Euc d → ℝ) (k : ℕ) (c : ℝ) (u : Euc d → ℝ) : Prop :=
  ContDiff ℝ k u ∧ ∀ n, n ≤ k → ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ c * w x

section RgW
variable {w : Euc d → ℝ} {k : ℕ}

lemma RgW.mono {c c' : ℝ} {u : Euc d → ℝ} (hw : ∀ x, 0 ≤ w x) (h : RgW w k c u) (hc : c ≤ c') :
    RgW w k c' u :=
  ⟨h.1, fun n hn x => (h.2 n hn x).trans (mul_le_mul_of_nonneg_right hc (hw x))⟩

lemma RgW.add {c c' : ℝ} {u v : Euc d → ℝ} (hu : RgW w k c u) (hv : RgW w k c' v) :
    RgW w k (c + c') (fun x => u x + v x) := by
  refine ⟨hu.1.add hv.1, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ k := by exact_mod_cast hn
  change ‖iteratedFDeriv ℝ n (u + v) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hu.1.of_le hn').contDiffAt (hv.1.of_le hn').contDiffAt]
  calc _ ≤ ‖iteratedFDeriv ℝ n u x‖ + ‖iteratedFDeriv ℝ n v x‖ := norm_add_le _ _
    _ ≤ c * w x + c' * w x := add_le_add (hu.2 n hn x) (hv.2 n hn x)
    _ = _ := by ring

lemma RgW.sub {c c' : ℝ} {u v : Euc d → ℝ} (hu : RgW w k c u) (hv : RgW w k c' v) :
    RgW w k (c + c') (fun x => u x - v x) := by
  refine ⟨hu.1.sub hv.1, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ k := by exact_mod_cast hn
  change ‖iteratedFDeriv ℝ n (u - v) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (hu.1.of_le hn').contDiffAt (hv.1.of_le hn').contDiffAt]
  calc _ ≤ ‖iteratedFDeriv ℝ n u x‖ + ‖iteratedFDeriv ℝ n v x‖ := norm_sub_le _ _
    _ ≤ c * w x + c' * w x := add_le_add (hu.2 n hn x) (hv.2 n hn x)
    _ = _ := by ring

lemma RgW.const_mul {c : ℝ} {u : Euc d → ℝ} (a : ℝ) (hu : RgW w k c u) :
    RgW w k (|a| * c) (fun x => a * u x) := by
  refine ⟨contDiff_const.mul hu.1, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ k := by exact_mod_cast hn
  have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := a) (f := u) (x := x)
    (hu.1.of_le hn').contDiffAt
  simp only [smul_eq_mul] at this
  rw [this, norm_smul, Real.norm_eq_abs]
  calc |a| * ‖iteratedFDeriv ℝ n u x‖ ≤ |a| * (c * w x) :=
        mul_le_mul_of_nonneg_left (hu.2 n hn x) (abs_nonneg _)
    _ = _ := by ring

lemma RgW.sum {ι : Type*} (s : Finset ι) {c : ι → ℝ} {u : ι → Euc d → ℝ}
    (hu : ∀ i ∈ s, RgW w k (c i) (u i)) :
    RgW w k (∑ i ∈ s, c i) (fun x => ∑ i ∈ s, u i x) := by
  refine ⟨ContDiff.sum fun i hi => (hu i hi).1, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ k := by exact_mod_cast hn
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hu i hi).1.of_le hn').contDiffAt)]
  calc _ ≤ ∑ i ∈ s, ‖iteratedFDeriv ℝ n (u i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, c i * w x := Finset.sum_le_sum fun i hi => (hu i hi).2 n hn x
    _ = _ := by rw [Finset.sum_mul]

lemma RgW.mul {cu cv : ℝ} {u v : Euc d → ℝ} (hw : ∀ x, 0 ≤ w x) (hcu : 0 ≤ cu) (hcv : 0 ≤ cv)
    (hu : RgW w k cu u) (hv : RgW (fun _ => 1) k cv v) :
    RgW w k (2 ^ k * cu * cv) (fun x => u x * v x) := by
  refine ⟨hu.1.mul hv.1, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ k := by exact_mod_cast hn
  refine (norm_iteratedFDeriv_mul_le hu.1 hv.1 x hn').trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (cu * w x) * cv := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have h1 := hu.2 i (by omega) x
        have h2 := hv.2 (n - i) (by omega) x
        simp only [mul_one] at h2
        have : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
        have := hw x
        gcongr
    _ = (2 ^ n : ℝ) * (cu * w x) * cv := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast; ring
    _ ≤ 2 ^ k * cu * cv * w x := by
        have h2 : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn
        have := hw x
        have h3 : 0 ≤ cu * w x * cv := by positivity
        nlinarith

end RgW


lemma rg_norm_single (i : Fin d) : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp

lemma rg_diruv {n : ℕ} {φ : Euc d → ℝ} (hφ : ContDiff ℝ (n + 1) φ) (e : Euc d) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ φ y e) x‖ ≤ ‖e‖ * ‖iteratedFDeriv ℝ (n + 1) φ x‖ := by
  have h := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ φ) (c := e) (x := x)
    (N := n) (n := n) ((hφ.fderiv_right (m := n) (by exact le_rfl)).contDiffAt) le_rfl
  rwa [norm_iteratedFDeriv_fderiv] at h

lemma rg_grad_comp {k : ℕ} {B : ℝ} {φ : Euc d → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hB : ∀ n, n ≤ k + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) (j : Fin d) :
    RgW (fun _ => 1) k B (fun x => gradient φ x j) := by
  have e : (fun x => gradient φ x j) = fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) := by
    funext x; exact movtr_gradient_apply φ x j
  rw [e]
  refine ⟨(hφ.fderiv_right (m := k) (by exact le_rfl)).clm_apply contDiff_const,
    fun n hn x => ?_⟩
  have := rg_diruv (n := n) (hφ.of_le (by exact_mod_cast Nat.succ_le_succ hn)) (EuclideanSpace.single j 1) x
  rw [rg_norm_single, one_mul] at this
  simpa using this.trans (hB (n + 1) (by omega) x)

lemma rg_fderiv_dir (φ : Euc d → ℝ) (hφ : ContDiff ℝ 2 φ) (e x : Euc d) :
    fderiv ℝ (fun y => fderiv ℝ φ y e) x e = fderiv ℝ (fderiv ℝ φ) x e e := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by exact le_rfl)).differentiable (by norm_num)) x
  have := fderiv_clm_apply (c := fderiv ℝ φ) (u := fun _ : Euc d => e) (x := x) h1
    (differentiableAt_const e)
  rw [this]
  simp

lemma rg_laplacian {k : ℕ} {B : ℝ} {φ : Euc d → ℝ} (hφ : ContDiff ℝ (k + 2) φ)
    (hB : ∀ n, n ≤ k + 2 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) :
    RgW (fun _ => 1) k (d * B) (fun x => Laplacian.laplacian φ x) := by
  have hL := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin d) ℝ)
  have hterm : ∀ i : Fin d, RgW (fun _ => 1) k B (fun x => iteratedFDeriv ℝ 2 φ x
      ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]) := by
    intro i
    set e : Euc d := EuclideanSpace.basisFun (Fin d) ℝ i with he
    have hen : ‖e‖ = 1 := by simp [he]
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
    set g : Euc d → ℝ := fun y => fderiv ℝ φ y e with hg
    have hgc : ContDiff ℝ (k + 1) g :=
      (hφ.fderiv_right (m := k + 1) (by push_cast; ring_nf; exact le_rfl)).clm_apply contDiff_const
    have eq : (fun x => iteratedFDeriv ℝ 2 φ x ![e, e]) = fun x => fderiv ℝ g x e := by
      funext x
      rw [rg_fderiv_dir φ hφ2 e x, iteratedFDeriv_two_apply]
      simp
    rw [eq]
    refine ⟨(hgc.fderiv_right (m := k) (by exact le_rfl)).clm_apply contDiff_const,
      fun n hn x => ?_⟩
    have h1 := rg_diruv (n := n) (φ := g) (hgc.of_le (by exact_mod_cast Nat.succ_le_succ hn)) e x
    have h2 := rg_diruv (n := n + 1) (φ := φ) (hφ.of_le (by exact_mod_cast (by omega : n + 1 + 1 ≤ k + 2))) e x
    have e1 : (fun y => fderiv ℝ g y e) = fun y => fderiv ℝ g y e := rfl
    rw [hen, one_mul] at h1 h2
    have h3 : ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ ‖iteratedFDeriv ℝ (n + 1 + 1) φ x‖ := h2
    calc _ ≤ ‖iteratedFDeriv ℝ (n + 1) g x‖ := h1
      _ ≤ ‖iteratedFDeriv ℝ (n + 1 + 1) φ x‖ := h3
      _ ≤ B := hB _ (by omega) x
      _ = B * 1 := by ring
  have := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := k) Finset.univ
    (fun i _ => hterm i)
  rw [hL]
  simpa using this


/-- Every component of `∇g * h` (cancellation convention) is `C^k` with bounded derivatives. -/
lemma rg_conv_comp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {h : Euc d → ℝ} (hh : RgDecay (k + 2) (fun _ => A) h) (j : Fin d) :
    RgW (fun _ => 1) k (movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d))
      (fun x => (convGradConvW (rieszKernelGrad d s) h x) j) := by
  have hκ := rgKerComp_ok (d := d) hs0 j
  obtain ⟨hc, hb⟩ := rg_Tdiff hd hs0 hsd hκ k (fun _ => A) (fun _ => hA) h hh
  obtain ⟨h2, h0, h1, -⟩ := rg_decay_parts (n := k + 2) (by omega) (a := fun _ => A) (fun _ => hA) hh
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h1' : ∀ y, ‖fderiv ℝ h y‖ ≤ A := fun y =>
    (h1 y).trans (by calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 :=
                          mul_le_mul_of_nonneg_left (hw y) hA
                      _ = A := mul_one _)
  have hfun : (fun x => (convGradConvW (rieszKernelGrad d s) h x) j) = rgT (fun z => (rieszKernelGrad d s z) j) h := by
    funext x
    exact rg_force_comp hd hs0 hsd (h2.differentiable (by norm_num)) hA hA h0 h1' x j
  rw [hfun]
  exact ⟨hc, fun n hn x => by simpa using hb n hn x⟩

end HRS.MP.RdGen
