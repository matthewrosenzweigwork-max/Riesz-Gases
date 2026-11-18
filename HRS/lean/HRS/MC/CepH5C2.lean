import HRS.MC.CepH5C1

/-!
# Packet C: `h5Comp_isOpen` and `h5Comp_iUnion` (continuation of `CepH5C1.lean`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Components

variable {N : ℕ} [NeZero N]

lemma h5c_mk_isOpenMap : IsOpenMap (Torus.mk : Euc 1 → Torus 1) := by
  have h1 : IsOpenMap (Pi.map (fun _ : Fin 1 => (fun a : ℝ => (a : UnitAddCircle)))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe) (by simp [Filter.cofinite_eq_bot])
  exact h1.comp (PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).isOpenMap

lemma h5c_mkN_isOpenMap : IsOpenMap (fun y : Fin N → Euc 1 => fun i => Torus.mk (y i)) :=
  IsOpenMap.piMap (f := fun _ => (Torus.mk : Euc 1 → Torus 1)) (fun _ => h5c_mk_isOpenMap)
    (by simp [Filter.cofinite_eq_bot])

lemma h5c_isOpen_ordered (σ : Equiv.Perm (Fin N)) : IsOpen {y : Fin N → Euc 1 | cep_StrictlyOrdered σ y} := by
  have hc : ∀ i : Fin N, Continuous fun y : Fin N → Euc 1 => y i 0 := fun i => by fun_prop
  have : {y : Fin N → Euc 1 | cep_StrictlyOrdered σ y} =
      (⋂ k : Fin N, ⋂ k' : Fin N, ⋂ (_ : k < k'), {y : Fin N → Euc 1 | y (σ k) 0 < y (σ k') 0}) ∩
      ⋂ k : Fin N, ⋂ k' : Fin N, {y : Fin N → Euc 1 | y (σ k') 0 < y (σ k) 0 + 1} := by
    ext y; simp [cep_StrictlyOrdered]
  rw [this]
  refine IsOpen.inter (isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun k' =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (hc _) (hc _)) ?_
  exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun k' =>
    isOpen_lt (hc _) ((hc _).add continuous_const)

theorem h5Comp_isOpen_proof (σ : Equiv.Perm (Fin N)) : IsOpen (h5Comp σ) := by
  have : h5Comp σ = (fun y : Fin N → Euc 1 => fun i => Torus.mk (y i)) '' {y | cep_StrictlyOrdered σ y} := by
    ext x; simp only [h5Comp, mem_setOf_eq, mem_image]
    constructor
    · rintro ⟨y, h1, h2⟩; exact ⟨y, h2, h1⟩
    · rintro ⟨y, h1, h2⟩; exact ⟨y, h2, h1⟩
  rw [this]
  exact h5c_mkN_isOpenMap _ (h5c_isOpen_ordered σ)

end Components

end HRS.MC.CepH5Pf
