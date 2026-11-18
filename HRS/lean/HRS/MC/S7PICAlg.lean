import HRS.Sections.Q17Aux8

/-!
# PI-C (uniqueness of the covariance tensor `J`), part 1: the finite-rank algebra

DECISION NOTE (route).  The statement `s7_PI_C_J_unique` does NOT need the approximation property.  Both `J₁, J₂`
lie in `projTensor X 2`, where `X = C([0,T];E_m)`.  `projection_strong_proof` (Q17Aux8) gives contractions `P_L`
(spatial Fourier cut-off + dyadic polygonal interpolation) with `P_L^{⊗2} v → v` for every `v ∈ projTensor X 2`.
Each `P_L` has FINITE RANK of the form `P_L w = ∑_a ℓ_a(w) • v_a` with `ℓ_a(w) = ⟨w(t_i), e_k⟩` an evaluation
functional `ℓ_{t_i, e_k}` (`e_k = realMode k`, smooth), so `(P_L^{⊗2} J)(M) = ∑_{a,b} M(v_a,v_b) J(ℓ_a ⊗ ℓ_b)`
is determined by the values of `J` on the products of evaluation functionals, which `IsJValue` prescribes.
Hence `P_L^{⊗2} J₁ = P_L^{⊗2} J₂` for all `L`, and letting `L → ∞` gives `J₁ = J₂`.
The case `T = 0` (where `projection_strong` is unavailable) uses the pointwise projection `w ↦ Π_L ∘ w`, and
`T < 0` is trivial (`X` is the zero space).

This file: the abstract algebra.  If `P w = ∑_a ℓ_a(w) • v_a`, then `P^{⊗2}` of a tensor depends only on its values
on the `ℓ_a ⊗ ℓ_b`.
-/

noncomputable section

open Filter Topology

namespace HRS.MC.Sec7.S7PIC

open HRS HRS.Sec7

set_option maxSynthPendingDepth 3

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The product tensor `ℓ₁ ⊗ ℓ₂` as a bounded bilinear form on `X`. -/
abbrev S7PIC_prodForm (l₁ l₂ : StrongDual ℝ X) : X [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]

theorem S7PIC_compCLM_eq {ι : Type*} [Fintype ι] (P : X →L[ℝ] X) (l : ι → StrongDual ℝ X) (v : ι → X)
    (hP : ∀ w, P w = ∑ a, l a w • v a) (M : X [×2]→L[ℝ] ℝ) :
    M.compContinuousLinearMap (fun _ => P) =
      ∑ a, ∑ b, M ![v a, v b] • S7PIC_prodForm (l a) (l b) := by
  classical
  ext w
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hP,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousMultilinearMap.map_sum M (fun i (a : ι) => l a (w i) • v a)]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (piFinTwoEquiv (fun _ => ι)) _ _ (fun r => ?_)
  have h1 : (fun i => l (r i) (w i) • v (r i)) = fun i => l (r i) (w i) • v (r i) := rfl
  show M (fun i => l (r i) (w i) • v (r i)) = _
  rw [M.map_smul_univ]
  simp only [S7PIC_prodForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_two, smul_eq_mul]
  have e : (fun i => v (r i)) = ![v (r 0), v (r 1)] := by
    funext i; fin_cases i <;> rfl
  rw [e]
  simp [piFinTwoEquiv, mul_comm, mul_left_comm, mul_assoc]

theorem S7PIC_tensorPow_eq {ι : Type*} [Fintype ι] (P : X →L[ℝ] X) (l : ι → StrongDual ℝ X) (v : ι → X)
    (hP : ∀ w, P w = ∑ a, l a w • v a) (J₁ J₂ : TensorDual X 2)
    (h : ∀ a b, J₁ (S7PIC_prodForm (l a) (l b)) = J₂ (S7PIC_prodForm (l a) (l b))) :
    tensorPow 2 P J₁ = tensorPow 2 P J₂ := by
  ext M
  have e : ∀ J : TensorDual X 2, tensorPow 2 P J M = J (M.compContinuousLinearMap (fun _ => P)) :=
    fun J => rfl
  rw [e, e, S7PIC_compCLM_eq P l v hP M]
  simp only [map_sum, map_smul, h]

/-- Uniqueness of limits: if the contractions `P_L` converge strongly on `projTensor X 2` and the two tensors have
equal images, then they coincide. -/
theorem S7PIC_eq_of_proj (Pj : ℕ → (X →L[ℝ] X)) (J₁ J₂ : TensorDual X 2)
    (h₁ : Tendsto (fun L => tensorPow 2 (Pj L) J₁) atTop (𝓝 J₁))
    (h₂ : Tendsto (fun L => tensorPow 2 (Pj L) J₂) atTop (𝓝 J₂))
    (h : ∀ L, tensorPow 2 (Pj L) J₁ = tensorPow 2 (Pj L) J₂) : J₁ = J₂ := by
  have : Tendsto (fun L => tensorPow 2 (Pj L) J₁) atTop (𝓝 J₂) := by
    simpa [h] using h₂
  exact tendsto_nhds_unique h₁ this

end HRS.MC.Sec7.S7PIC
