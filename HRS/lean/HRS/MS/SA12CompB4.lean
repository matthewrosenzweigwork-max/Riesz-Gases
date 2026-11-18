import HRS.MS.SA12CompB4B
import HRS.MP.RdGenerator
import HRS.MP.RdGenAux
import HRS.Whole.Q09BAux2

/-!
# S.A.12 B4: the generator along a continuous `C²` path is jointly continuous with linear growth

The generator is `νΔu + b·∇u - ∑_j (∇g * (μ (Mᵀ∇u)_j))_j`.  The Laplacian and gradient are continuous by the
supplied jets; the drift and the nonlocal term are cancellation convolutions `rgT` of the density path, which are
jointly continuous by `sa12z_rgT_continuousOn` and `sa12z_density_joint_cont`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen

variable {d : ℕ}

/-- The `j`-th component of `Mᵀ∇φ` is a `C¹` function with the derivative bounds of `φ` through order `2`. -/
lemma sa12z_matgrad1 {B MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {φ : Euc d → ℝ}
    (hMB : HRS.PDE.MatBound MB M) (hφ : ContDiff ℝ (1 + 1) φ)
    (hB : ∀ n, n ≤ 1 + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) (j : Fin d) :
    RgW (fun _ => 1) 1 (d * MB * B) (fun y => Torus.matVec M.transpose (gradient φ y) j) := by
  have hfun : (fun y => Torus.matVec M.transpose (gradient φ y) j) =
      fun y => ∑ i : Fin d, M i j * gradient φ y i := by
    funext y
    rw [HRS.Whole.Q09B.q09b_matVec_apply]
    simp
  rw [hfun]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), RgW (fun _ => (1 : ℝ)) 1 (|M i j| * B)
      (fun y => M i j * gradient φ y i) := fun i _ =>
    RgW.const_mul (M i j) (rg_grad_comp hφ hB i)
  have hs := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := 1) Finset.univ hterm
  refine hs.mono (fun _ => zero_le_one) ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  calc ∑ i : Fin d, |M i j| * B ≤ ∑ i : Fin d, MB * B :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hMB i j) hB0
    _ = d * MB * B := by simp [Finset.sum_const]; ring

/-- Data of the nonlocal integrand `ρ · (Mᵀ∇φ)_j`: differentiable, decaying, with bounded derivative. -/
lemma sa12z_nl_data {Aρ B MB : ℝ} (hAρ : 0 ≤ Aρ) (hMB0 : 0 ≤ MB) {M : Matrix (Fin d) (Fin d) ℝ}
    (hMB : HRS.PDE.MatBound MB M) {ρ : Euc d → ℝ} (hρ : RgDecay 1 (fun _ => Aρ) ρ)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ (1 + 1) φ)
    (hB : ∀ n, n ≤ 1 + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) (j : Fin d) :
    Differentiable ℝ (fun y => ρ y * Torus.matVec M.transpose (gradient φ y) j) ∧
      (∀ y, ‖ρ y * Torus.matVec M.transpose (gradient φ y) j‖ ≤
        (2 ^ 1 * Aρ * (d * MB * B)) * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ (fun y => ρ y * Torus.matVec M.transpose (gradient φ y) j) y‖ ≤
        2 ^ 1 * Aρ * (d * MB * B)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  have hw0 : ∀ y : Euc d, 0 ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => Real.rpow_nonneg (by positivity) _
  have hcv : 0 ≤ (d : ℝ) * MB * B := by positivity
  have hmul := RgW.mul (w := fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) (k := 1) hw0 hAρ hcv hρ
    (sa12z_matgrad1 hMB hφ hB j)
  have hw1 : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨hmul.1.differentiable (by norm_num), fun y => ?_, fun y => ?_⟩
  · simpa using hmul.2 0 (by norm_num) y
  · have h1 := hmul.2 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at h1
    refine h1.trans ?_
    have : 0 ≤ 2 ^ 1 * Aρ * (d * MB * B) := by positivity
    calc _ ≤ 2 ^ 1 * Aρ * (d * MB * B) * 1 := mul_le_mul_of_nonneg_left (hw1 y) this
      _ = _ := by ring


lemma sa12z_decay1 {A : ℝ} (hA : 0 ≤ A) {ρ : Euc d → ℝ} (h : RgDecay 1 (fun _ => A) ρ) :
    Differentiable ℝ ρ ∧ (∀ y, ‖ρ y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧ (∀ y, ‖fderiv ℝ ρ y‖ ≤ A) := by
  have hw1 : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨h.1.differentiable (by norm_num), fun y => ?_, fun y => ?_⟩
  · simpa using h.2 0 (by norm_num) y
  · have h1 := h.2 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at h1
    exact h1.trans (by nlinarith [hw1 y, Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + ‖y‖ by positivity) (-((d : ℝ) + 1))])

lemma sa12z_gradient_cont {u : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)}
    (hcont1 : ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ 1 (u q.1) q.2) S) (i : Fin d) :
    ContinuousOn (fun q : ℝ × Euc d => gradient (u q.1) q.2 i) S := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
    (![EuclideanSpace.single i (1 : ℝ)] : Fin 1 → Euc d)).continuous.comp_continuousOn hcont1
  refine h.congr fun q _ => ?_
  rw [movtr_gradient_apply, Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_one_apply]
  rfl

lemma sa12z_laplacian_cont {u : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)}
    (hcont2 : ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ 2 (u q.1) q.2) S) :
    ContinuousOn (fun q : ℝ × Euc d => Laplacian.laplacian (u q.1) q.2) S := by
  have hL : ∀ q : ℝ × Euc d, Laplacian.laplacian (u q.1) q.2 = ∑ i : Fin d,
      iteratedFDeriv ℝ 2 (u q.1) q.2
        ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i] := fun q =>
    by rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (u q.1)
      (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp_rw [hL]
  refine continuousOn_finset_sum _ fun i _ => ?_
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    (![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i] : Fin 2 → Euc d)).continuous.comp_continuousOn hcont2


-- BEGIN SA12.B4
theorem generator_on_continuous_c2_path (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) (u : ℝ → Euc d → ℝ)
    (hc2 : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (u τ))
    (hb : ∃ B : ℝ, ∀ j ≤ 2, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x,
      ‖iteratedFDeriv ℝ j (u τ) x‖ ≤ B)
    (hcont : ∀ j ≤ 2, ContinuousOn
      (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (u q.1) q.2)
      (Icc (0 : ℝ) t ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × Euc d =>
      generatorW (D.coeff μ) (t - q.1) (u q.1) q.2) (Icc (0 : ℝ) t ×ˢ univ) ∧
      ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x,
        |generatorW (D.coeff μ) (t - τ) (u τ) x| ≤ B * (1 + ‖x‖) := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hs0' : 0 ≤ D.s := by rw [hDs]; exact hs0
  have hsd' : D.s < d := by rw [hDs]; exact hsd
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) 0 ⟨le_rfl, ht.1.le⟩ 0)
  have htT : ∀ τ ∈ Icc (0 : ℝ) t, t - τ ∈ Icc (0 : ℝ) T := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  -- constants
  set MB' : ℝ := max MB 0 with hMB'
  set Λ' : ℝ := max Λ 0 with hΛ'
  set ΛV' : ℝ := max ΛV 0 with hΛV'
  set G₀' : ℝ := max G₀ 0 with hG₀'
  set ν' : ℝ := max νbar 0 with hν'
  set Aρ : ℝ := (d : ℝ) ^ (m + 3) * Λ' * 2 ^ ((d : ℝ) + 3) with hAρ
  have hMB0 : 0 ≤ MB' := le_max_right _ _
  have hΛ0 : 0 ≤ Λ' := le_max_right _ _
  have hΛV0 : 0 ≤ ΛV' := le_max_right _ _
  have hG0 : 0 ≤ G₀' := le_max_right _ _
  have hν0 : 0 ≤ ν' := le_max_right _ _
  have hA0 : 0 ≤ Aρ := by rw [hAρ]; positivity
  have hMB'' : HRS.PDE.MatBound MB' D.M := fun i j => (hD.hM i j).trans (le_max_left _ _)
  have hV' : VHypRd (1 + 1) ΛV' G₀' D.V :=
    rg_VHyp_mono hD.hV (by omega) (le_max_left _ _) (le_max_left _ _)
  have hνD : 0 ≤ D.invβ ∧ D.invβ ≤ ν' := ⟨hD.hν.1, hD.hν.2.trans (le_max_left _ _)⟩
  -- the density slices
  have hdec3 : ∀ τ ∈ Icc (0 : ℝ) t, RgDecay (1 + 2) (fun _ => Aρ) (μ (t - τ)) := by
    intro τ hτ
    obtain ⟨hcb1, hcb2, hcb3⟩ := hD.hμ.regular.1 (t - τ) (htT τ hτ)
    have hcb0 : 0 ≤ HRS.cbNorm (m + 3) (μ (t - τ)) := sa12z_cb_nonneg hcb1
    exact rg_decay_mono (by omega) (rg_rho_decay hd (r := m + 3) (Λ := Λ') hcb1 hcb2
      (by linarith [hcb3, le_max_left Λ 0]))
  have hdec1 : ∀ τ ∈ Icc (0 : ℝ) t, RgDecay 1 (fun _ => Aρ) (μ (t - τ)) :=
    fun τ hτ => rg_decay_mono (by omega) (hdec3 τ hτ)
  have hμT : ContinuousOn (fun q : ℝ × Euc d => μ (t - q.1) q.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    have h := sa12z_density_joint_cont hD.hμ
    exact h.comp (f := fun q : ℝ × Euc d => (t - q.1, q.2))
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq => ⟨htT q.1 hq.1, mem_univ _⟩)
  -- the solution slices
  have hu2 : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ (1 + 1) (u τ) := fun τ hτ => by
    rw [one_add_one_eq_two]; exact hc2 τ hτ
  have hB' : ∀ τ ∈ Icc (0 : ℝ) t, ∀ n, n ≤ 1 + 1 → ∀ x, ‖iteratedFDeriv ℝ n (u τ) x‖ ≤ B :=
    fun τ hτ n hn x => hB n (by omega) τ hτ x
  have hgradC : ∀ i, ContinuousOn (fun q : ℝ × Euc d => gradient (u q.1) q.2 i)
      (Icc (0 : ℝ) t ×ˢ univ) := fun i => sa12z_gradient_cont (hcont 1 (by norm_num)) i
  have hlapC := sa12z_laplacian_cont (hcont 2 le_rfl)
  have hjc : ∀ j, ContinuousOn (fun q : ℝ × Euc d => Torus.matVec D.M.transpose (gradient (u q.1) q.2) j)
      (Icc (0 : ℝ) t ×ˢ univ) := by
    intro j
    simp_rw [HRS.Whole.Q09B.q09b_matVec_apply]
    exact continuousOn_finset_sum _ fun i _ => continuousOn_const.mul (hgradC i)
  -- the drift
  have hdriftEq : ∀ (ρ : Euc d → ℝ) (x : Euc d) (j : Fin d), meanFieldDriftW D ρ x j =
      (∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d D.s) ρ x) i) - gradient D.V x j := by
    intro ρ x j
    unfold meanFieldDriftW
    rw [PiLp.sub_apply, HRS.Whole.Q09B.q09b_matVec_apply]
  have hgV : ∀ j : Fin d, Continuous fun x : Euc d => gradient D.V x j := by
    intro j
    have h1 : ContDiff ℝ 1 D.V := hD.hV.1.of_le (by exact_mod_cast le_top)
    have e : (fun x : Euc d => gradient D.V x j) =
        fun x => fderiv ℝ D.V x (EuclideanSpace.single j (1 : ℝ)) := funext fun x => movtr_gradient_apply D.V x j
    rw [e]
    exact (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdec : ∀ τ ∈ Icc (0 : ℝ) t, Differentiable ℝ (μ (t - τ)) ∧
      (∀ y, ‖μ (t - τ) y‖ ≤ Aρ * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧ (∀ y, ‖fderiv ℝ (μ (t - τ)) y‖ ≤ Aρ) :=
    fun τ hτ => sa12z_decay1 hA0 (hdec1 τ hτ)
  have hconvC : ∀ i, ContinuousOn (fun q : ℝ × Euc d =>
      (convGradConvW (rieszKernelGrad d D.s) (μ (t - q.1)) q.2) i) (Icc (0 : ℝ) t ×ˢ univ) := by
    intro i
    have hrg := sa12z_rgT_continuousOn hd hs0' hsd' (rgKerComp_ok (d := d) hs0' i)
      (S := Icc (0 : ℝ) t) (g := fun τ => μ (t - τ)) (fun τ hτ => (hdec τ hτ).1) hA0 hA0
      (fun τ hτ => (hdec τ hτ).2.1) (fun τ hτ => (hdec τ hτ).2.2) hμT
    exact hrg.congr (fun q hq => rg_force_comp hd hs0' hsd' (hdec q.1 hq.1).1 hA0 hA0
      (hdec q.1 hq.1).2.1 (hdec q.1 hq.1).2.2 q.2 i)
  have hdriftC : ∀ j, ContinuousOn (fun q : ℝ × Euc d => meanFieldDriftW D (μ (t - q.1)) q.2 j)
      (Icc (0 : ℝ) t ×ˢ univ) := by
    intro j
    simp_rw [hdriftEq]
    exact (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul (hconvC i)).sub
      ((hgV j).comp_continuousOn continuous_snd.continuousOn)
  -- the nonlocal term
  have hnl : ∀ j : Fin d, ∀ τ ∈ Icc (0 : ℝ) t,
      Differentiable ℝ (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) ∧
      (∀ y, ‖μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j‖ ≤
        (2 ^ 1 * Aρ * (d * MB' * B)) * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) y‖ ≤
        2 ^ 1 * Aρ * (d * MB' * B)) :=
    fun j τ hτ => sa12z_nl_data hA0 hMB0 hMB'' (hdec1 τ hτ) (hu2 τ hτ) (hB' τ hτ) j
  have hnlC : ∀ j : Fin d, ContinuousOn (fun q : ℝ × Euc d =>
      (convGradConvW (rieszKernelGrad d D.s)
        (fun y => μ (t - q.1) y * Torus.matVec D.M.transpose (gradient (u q.1) y) j) q.2) j)
      (Icc (0 : ℝ) t ×ˢ univ) := by
    intro j
    have hC1 : 0 ≤ 2 ^ 1 * Aρ * ((d : ℝ) * MB' * B) := by positivity
    have hrg := sa12z_rgT_continuousOn hd hs0' hsd' (rgKerComp_ok (d := d) hs0' j)
      (S := Icc (0 : ℝ) t)
      (g := fun τ y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j)
      (fun τ hτ => (hnl j τ hτ).1) hC1 hC1 (fun τ hτ => (hnl j τ hτ).2.1)
      (fun τ hτ => (hnl j τ hτ).2.2) (hμT.mul (hjc j))
    exact hrg.congr (fun q hq => rg_force_comp hd hs0' hsd' (hnl j q.1 hq.1).1 hC1 hC1
      (hnl j q.1 hq.1).2.1 (hnl j q.1 hq.1).2.2 q.2 j)
  have hgen : ∀ τ x, generatorW (D.coeff μ) (t - τ) (u τ) x = D.invβ * Laplacian.laplacian (u τ) x +
      inner ℝ (meanFieldDriftW D (μ (t - τ)) x) (gradient (u τ) x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
        (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) x) j :=
    fun τ x => rfl
  refine ⟨?_, ?_⟩
  · simp_rw [hgen, HRS.Whole.Q09B.q09b_inner_euc]
    refine ((continuousOn_const.mul hlapC).add ?_).sub (continuousOn_finset_sum _ fun j _ => hnlC j)
    exact continuousOn_finset_sum _ fun i _ => (hdriftC i).mul (hgradC i)
  · -- linear growth
    set C1 : ℝ := 2 ^ 1 * Aρ * ((d : ℝ) * MB' * B) with hC1d
    have hC1 : 0 ≤ C1 := by rw [hC1d]; positivity
    set Knl : ℝ := movtr_sigma D.s * (C1 * rgNear d D.s + 4 ^ (D.s + 1) * C1 * rgW d) with hKnl
    have hKnl0 : 0 ≤ Knl := by
      have := rg_near_nonneg (d := d) D.s
      have := rg_W_nonneg (d := d)
      have := rg_sigma_nonneg hs0'
      rw [hKnl]; positivity
    set Bb : ℝ := d * MB' * (movtr_sigma D.s * (Aρ * rgNear d D.s + 4 ^ (D.s + 1) * Aρ * rgW d)) +
      (G₀' + ΛV') with hBb
    have hBb0 : 0 ≤ Bb := by
      have := rg_near_nonneg (d := d) D.s
      have := rg_W_nonneg (d := d)
      have := rg_sigma_nonneg hs0'
      rw [hBb]; positivity
    refine ⟨ν' * (d * B) + d * (2 ^ 1 * Bb * B) + d * Knl, fun τ hτ x => ?_⟩
    rw [hgen]
    have hφ1 : ContDiff ℝ ((1 : ℕ) + 1) (u τ) := by simpa [one_add_one_eq_two] using hc2 τ hτ
    have hφ0 : ContDiff ℝ ((0 : ℕ) + 2) (u τ) := by simpa using hc2 τ hτ
    -- Laplacian
    have hlap := rg_laplacian (k := 0) (B := B) hφ0 (fun n hn y => hB n (by omega) τ hτ y)
    have hlap' : |Laplacian.laplacian (u τ) x| ≤ d * B := by
      have := hlap.2 0 le_rfl x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      simpa using this
    have h1 : |D.invβ * Laplacian.laplacian (u τ) x| ≤ ν' * (d * B) := by
      rw [abs_mul, abs_of_nonneg hνD.1]
      exact mul_le_mul hνD.2 hlap' (abs_nonneg _) hν0
    -- transport
    have htr := rg_transport (k := 1) (B := B) (Bb := Bb) hB0 hBb0 hφ1
      (fun n hn y => hB n (by omega) τ hτ y) (b := meanFieldDriftW D (μ (t - τ)))
      (fun j => rg_drift hd hs0' hsd' (k := 1) le_rfl hA0 (D := D) rfl hMB'' hV' (hdec3 τ hτ) j)
    have h2 : |inner ℝ (meanFieldDriftW D (μ (t - τ)) x) (gradient (u τ) x)| ≤
        d * (2 ^ 1 * Bb * B) * (1 + ‖x‖) := by
      have := htr.2 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    -- nonlocal
    have h3j : ∀ j : Fin d, |(convGradConvW (rieszKernelGrad d D.s)
        (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) x) j| ≤ Knl := by
      intro j
      rw [rg_force_comp hd hs0' hsd' (hnl j τ hτ).1 hC1 hC1 (hnl j τ hτ).2.1 (hnl j τ hτ).2.2 x j]
      have := rg_norm_T_le hd hs0' hsd' (rgKerComp_ok (d := d) hs0' j) (hnl j τ hτ).1 hC1 hC1
        (hnl j τ hτ).2.1 (hnl j τ hτ).2.2 x
      rw [Real.norm_eq_abs] at this
      exact this
    have h3 : |∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
        (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) x) j| ≤ d * Knl := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ j : Fin d, Knl := Finset.sum_le_sum fun j _ => h3j j
        _ = d * Knl := by simp
    have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hP : 0 ≤ ν' * (d * B) := by positivity
    have hQ : 0 ≤ (d : ℝ) * (2 ^ 1 * Bb * B) := by positivity
    have hR : 0 ≤ (d : ℝ) * Knl := by positivity
    calc |D.invβ * Laplacian.laplacian (u τ) x + inner ℝ (meanFieldDriftW D (μ (t - τ)) x) (gradient (u τ) x) -
          ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
            (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) x) j|
        ≤ |D.invβ * Laplacian.laplacian (u τ) x| +
            |inner ℝ (meanFieldDriftW D (μ (t - τ)) x) (gradient (u τ) x)| +
            |∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
              (fun y => μ (t - τ) y * Torus.matVec D.M.transpose (gradient (u τ) y) j) x) j| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ ν' * (d * B) + d * (2 ^ 1 * Bb * B) * (1 + ‖x‖) + d * Knl := by linarith
      _ ≤ (ν' * (d * B) + d * (2 ^ 1 * Bb * B) + d * Knl) * (1 + ‖x‖) := by nlinarith
-- END SA12.B4

end HRS.MH.AdjointRd.Phase2SA12Companions
