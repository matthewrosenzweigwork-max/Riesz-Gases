import HRS.MS.R2InterpAux3
import HRS.MS.S111TermAux1

/-!
# S11.1 terminal wave, T08: projective tensors are determined by the coordinate products

The `n`-fold version of `s102_J_unique`: `P_L = Σ_p ℓ_p(·) b_p` gives
`κ(M∘(P_L,…,P_L)) = Σ_r M(b_{r_1},…,b_{r_n}) κ(ℓ_{r_1}⊗…⊗ℓ_{r_n})`, and `κ ∘ P_L^{⊗n} → κ`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S111T

open HRS HRS.Sec7 HRS.Whole HRS.MS.R2Interp

variable {d : ℕ} {m T : ℝ}

/-- The pairing of `κ` with `M ∘ (P_L,…,P_L)` as a finite sum over products of evaluation functionals. -/
theorem s111t_expand (n : ℕ) (hT : 0 < T) (L : ℕ) (M : OscPath d m T [×n]→L[ℝ] ℝ)
    (J : TensorDual (OscPath d m T) n) :
    J (M.compContinuousLinearMap fun _ => s102_Pj T hT L) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n => s102_idx d L),
        M (fun i => s102_bpath T L (r i)) *
          J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
            fun i => s102_ellp hT L (r i)) := by
  classical
  have hmap : M.compContinuousLinearMap (fun _ => s102_Pj T hT L) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n => s102_idx d L),
        M (fun i => s102_bpath T L (r i)) •
          (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
            fun i => s102_ellp hT L (r i) := by
    ext x
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp_rw [s102_Pj_decomp]
    rw [M.map_sum_finset
      (fun (i : Fin n) (p : ℕ × MultiIndex d) => s102_ellp hT L p (x i) • s102_bpath T L p)
      (fun _ => s102_idx d L)]
    simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp [mul_comm]
  rw [hmap, map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- **T08 (general arity).** Two projective tensors with the same values on products of coordinate evaluations
`w ↦ ∏ᵢ coord(wᵢ(τᵢ), αᵢ)` coincide. -/
theorem s111t_tensor_ext (n : ℕ) (hT : 0 < T) (kappa kappab : projTensor (OscPath d m T) n)
    (h : ∀ tau : Fin n → Set.Icc (0 : ℝ) T, ∀ alpha : Fin n → MultiIndex d,
      ∀ M : (OscPath d m T) [×n]→L[ℝ] ℝ,
      (∀ w : Fin n → OscPath d m T, M w = ∏ i, OscDual.coord (OscPath.at' (w i) (tau i)) (alpha i)) →
      (kappa : TensorDual (OscPath d m T) n) M = (kappab : TensorDual (OscPath d m T) n) M) :
    kappa = kappab := by
  classical
  obtain ⟨_, _, hP3⟩ := s102_projection_strong (d := d) m T hT
  have hL : ∀ (L : ℕ) (M : OscPath d m T [×n]→L[ℝ] ℝ),
      (kappa : TensorDual (OscPath d m T) n) (M.compContinuousLinearMap fun _ => s102_Pj T hT L) =
        (kappab : TensorDual (OscPath d m T) n) (M.compContinuousLinearMap fun _ => s102_Pj T hT L) := by
    intro L M
    rw [s111t_expand, s111t_expand]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    refine h (fun i => s102_node hT L (r i).1) (fun i => (r i).2) _ (fun w => ?_)
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      s102_ellp, s102_ell_apply]
  apply Subtype.ext
  refine ContinuousLinearMap.ext fun M => ?_
  have t1 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp
    (hP3 n (kappa : TensorDual (OscPath d m T) n) kappa.2)
  have t2 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp
    (hP3 n (kappab : TensorDual (OscPath d m T) n) kappab.2)
  have t2' : Tendsto ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow n (s102_Pj T hT L)
      (kappa : TensorDual (OscPath d m T) n)) atTop (𝓝 ((kappab : TensorDual (OscPath d m T) n) M)) := by
    refine t2.congr (fun L => ?_)
    exact (hL L M).symm
  exact tendsto_nhds_unique t1 t2'

/-- **T08.** The cubic case on the frozen path space `R2X`. -/
theorem s111t_cubic_coordinates_determine (d : ℕ) (T : ℝ) (hT : 0 < T)
    (kappa kappab : projTensor (R2X d T) 3)
    (h : ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T, ∀ alpha : Fin 3 → MultiIndex d,
      ∀ M : (R2X d T) [×3]→L[ℝ] ℝ,
      (∀ w : Fin 3 → R2X d T,
        M w = ∏ i, OscDual.coord (OscPath.at' (w i) (tau i)) (alpha i)) →
      (kappa : TensorDual (R2X d T) 3) M = (kappab : TensorDual (R2X d T) 3) M) :
    kappa = kappab :=
  s111t_tensor_ext 3 hT kappa kappab h

end HRS.MS.S111T
