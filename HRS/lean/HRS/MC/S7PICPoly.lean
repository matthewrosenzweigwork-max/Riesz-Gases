import HRS.MC.S7PICFou

/-!
# PI-C, part 3: `P_L` has finite rank of the form `∑ ℓ_{t_i,k}(w) • v_{i,k}`, and `J` is determined on it
-/

noncomputable section

open Filter Topology

namespace HRS.MC.Sec7.S7PIC

open HRS HRS.Sec7

set_option maxSynthPendingDepth 3

variable {d : ℕ} {m T : ℝ}

/-- The grid node `t_i = i T / 2^L` as a point of `[0,T]`. -/
def S7PIC_node (T : ℝ) (hT : 0 ≤ T) (L : ℕ) (i : ℕ) : Set.Icc (0 : ℝ) T :=
  Set.projIcc 0 T hT (i * T / 2 ^ L)

/-- The path `t ↦ hat_i(t 2^L / T) • E_k`. -/
def S7PIC_vpath (m T : ℝ) (L : ℕ) (i : ℕ) (k : NonzeroLattice d) : PathSpace d m T :=
  (show PathSpace d m T from
    (⟨fun t => q17_hat ((t : ℝ) * 2 ^ L / T) i • S7PIC_E m k, by
      unfold q17_hat; fun_prop⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)))

theorem S7PIC_path_ext {w w' : PathSpace d m T} (h : ∀ t, PathSpace.at' w t = PathSpace.at' w' t) :
    w = w' :=
  ContinuousMap.ext (show ∀ t, (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) t =
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w') t from h)

theorem S7PIC_at_sum {ι : Type*} (s : Finset ι) (f : ι → PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (∑ a ∈ s, f a) t = ∑ a ∈ s, PathSpace.at' (f a) t := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, q17_at_add, ih, Finset.sum_insert ha]

theorem S7PIC_at_vpath (L : ℕ) (i : ℕ) (k : NonzeroLattice d) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (S7PIC_vpath m T L i k) t = q17_hat ((t : ℝ) * 2 ^ L / T) i • S7PIC_E m k := rfl

theorem S7PIC_projPoly_eq_sum (hT : 0 ≤ T) (L : ℕ) (w : PathSpace d m T) :
    projPoly m T hT L w = ∑ a : Fin (2 ^ L + 1) × ↥(S7PIC_box d L),
      S7PIC_lf m T (S7PIC_node T hT L a.1) a.2 w • S7PIC_vpath m T L a.1 a.2 := by
  classical
  apply S7PIC_path_ext
  intro t
  rw [S7PIC_at_sum]
  show (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT L w) t = _
  rw [q17_projPoly_apply]
  rw [Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [S7PIC_fourierProj_eq_sum, Finset.smul_sum]
  rw [← Finset.sum_coe_sort (S7PIC_box d L)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [q17_at_smul, S7PIC_at_vpath, S7PIC_lf_apply, smul_comm]
  rfl

/-- `J` is determined on the product tensors `ℓ_{t,k} ⊗ ℓ_{t',k'}` by `IsJValue`. -/
theorem S7PIC_agree (D : DynData d) (ρ : ℝ → Torus d → ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    (J₁ J₂ : TensorDual (PathSpace d m T) 2) (h₁ : IsJValue D ρ m T z I J₁) (h₂ : IsJValue D ρ m T z I J₂)
    (ta tb : Set.Icc (0 : ℝ) T) (k k' : NonzeroLattice d) :
    J₁ (S7PIC_prodForm (S7PIC_lf m T ta k) (S7PIC_lf m T tb k')) =
      J₂ (S7PIC_prodForm (S7PIC_lf m T ta k) (S7PIC_lf m T tb k')) := by
  have e₁ := h₁.2 ta tb (Torus.realMode k) (Torus.realMode k') (S7PIC_lf m T ta k) (S7PIC_lf m T tb k')
    (FieldSingAux.isSmooth_realMode k) (FieldSingAux.isSmooth_realMode k') ta.2 tb.2
    (fun w => S7PIC_lf_eq_eval ta k w) (fun w => S7PIC_lf_eq_eval tb k' w)
  have e₂ := h₂.2 ta tb (Torus.realMode k) (Torus.realMode k') (S7PIC_lf m T ta k) (S7PIC_lf m T tb k')
    (FieldSingAux.isSmooth_realMode k) (FieldSingAux.isSmooth_realMode k') ta.2 tb.2
    (fun w => S7PIC_lf_eq_eval ta k w) (fun w => S7PIC_lf_eq_eval tb k' w)
  exact e₁.trans e₂.symm

/-- For `T ≥ 0` and any `L`, `P_L^{⊗2}` (with `P_L` any bounded operator equal to `projPoly`) identifies `J₁, J₂`. -/
theorem S7PIC_tensorPow_projPoly (D : DynData d) (ρ : ℝ → Torus d → ℝ) (z : ℝ → NegSobolev d m)
    (I : Set ℝ) (J₁ J₂ : TensorDual (PathSpace d m T) 2) (h₁ : IsJValue D ρ m T z I J₁)
    (h₂ : IsJValue D ρ m T z I J₂) (hT : 0 ≤ T) (L : ℕ) (P : PathSpace d m T →L[ℝ] PathSpace d m T)
    (hP : ∀ w, P w = projPoly m T hT L w) :
    tensorPow 2 P J₁ = tensorPow 2 P J₂ := by
  refine S7PIC_tensorPow_eq P
    (fun a : Fin (2 ^ L + 1) × ↥(S7PIC_box d L) => S7PIC_lf m T (S7PIC_node T hT L a.1) a.2)
    (fun a => S7PIC_vpath m T L a.1 a.2) (fun w => ?_) J₁ J₂ (fun a b => ?_)
  · rw [hP, S7PIC_projPoly_eq_sum]
  · exact S7PIC_agree D ρ z I J₁ J₂ h₁ h₂ _ _ _ _

end HRS.MC.Sec7.S7PIC
