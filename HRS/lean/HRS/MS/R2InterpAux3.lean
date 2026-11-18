import HRS.MS.R2InterpAux2
import HRS.Whole.Window

/-!
# S10.2 (worker S102), part 3: uniqueness of the covariance tensor `J` (`IsR2JValue`)

Two tensors `J, J' ∈ projTensor (OscPath d m T) 2` with the same values `IsR2JValue` on all products of evaluation functionals coincide:
`P_L = ∑_p ℓ_p(·) b_p` (finite sum over the grid nodes and Hermite indices of degree `≤ L`) gives `J(M∘(P_L,P_L)) = ∑ M(b_p,b_q) J(ℓ_p⊗ℓ_q)`, and
`(P_L)^{⊗2}J → J`.  Consequently `r2JPair` (which uses `Exists.choose`) is independent of the choice (the torus analogue is PI-C).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.R2Interp

open HRS HRS.Sec7 HRS.Whole

variable {d : ℕ} {m T : ℝ}

/-- The coordinate functional `u ↦ u(φ_α)` of `B_m`. -/
def s102_coordCLM (α : MultiIndex d) : OscDual d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => OscDual.coord u α
      map_add' := fun u v => OscDual.coord_add u v α
      map_smul' := fun c u => by simpa using OscDual.coord_smul c u α } 1
    (fun u => by
      have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (show lp (fun _ : MultiIndex d => ℝ) 2 from u) α
      rw [one_mul]
      exact this)

/-- The evaluation functional `w ↦ w(τ)(φ_α)` on the path space. -/
def s102_ell (τ : Set.Icc (0 : ℝ) T) (α : MultiIndex d) : StrongDual ℝ (OscPath d m T) :=
  (s102_coordCLM α).comp (ContinuousMap.evalCLM ℝ τ)

theorem s102_ell_apply (τ : Set.Icc (0 : ℝ) T) (α : MultiIndex d) (w : OscPath d m T) :
    s102_ell τ α w = OscDual.coord (OscPath.at' w τ) α := rfl

/-- The unit coordinate vector of `B_m`. -/
def s102_e (α : MultiIndex d) : OscDual d m := (lp.single 2 α (1 : ℝ) : lp (fun _ : MultiIndex d => ℝ) 2)

theorem s102_coord_e (α β : MultiIndex d) :
    OscDual.coord (s102_e (m := m) α) β = if β = α then 1 else 0 := by
  classical
  simp [OscDual.coord, s102_e, lp.single_apply, Pi.single_apply]

/-- The path `t ↦ hat_i(t 2^L/T) e_α`. -/
def s102_bpath (T : ℝ) (L : ℕ) (p : ℕ × MultiIndex d) : OscPath d m T :=
  (⟨fun t => q17_hat ((t : ℝ) * 2 ^ L / T) p.1 • s102_e p.2, by unfold q17_hat; fun_prop⟩ :
    C(Set.Icc (0 : ℝ) T, OscDual d m))

/-- The grid node `t_i = iT/2^L` as a point of `[0,T]`. -/
def s102_node (hT : 0 < T) (L i : ℕ) : Set.Icc (0 : ℝ) T := Set.projIcc 0 T hT.le (i * T / 2 ^ L)

/-- The finite index set of the decomposition of `P_L`. -/
def s102_idx (d L : ℕ) : Finset (ℕ × MultiIndex d) :=
  (Finset.range (2 ^ L + 1)) ×ˢ (multiIndex_sublevel_finite d L).toFinset

/-- The evaluation functional of the index `p = (i,α)`. -/
def s102_ellp (hT : 0 < T) (L : ℕ) (p : ℕ × MultiIndex d) : StrongDual ℝ (OscPath d m T) :=
  s102_ell (s102_node hT L p.1) p.2

theorem s102_trunc_eq_sum (L : ℕ) (u : OscDual d m) :
    s102_trunc L u = ∑ α ∈ (multiIndex_sublevel_finite d L).toFinset, OscDual.coord u α • s102_e α := by
  classical
  apply s102_ext
  intro β
  rw [s102_coord_trunc]
  have hsum : OscDual.coord (∑ α ∈ (multiIndex_sublevel_finite d L).toFinset,
      OscDual.coord u α • s102_e (m := m) α) β =
      ∑ α ∈ (multiIndex_sublevel_finite d L).toFinset, OscDual.coord u α * OscDual.coord (s102_e (m := m) α) β := by
    induction (multiIndex_sublevel_finite d L).toFinset using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, OscDual.coord_add, OscDual.coord_smul, ih]
  rw [hsum]
  simp_rw [s102_coord_e]
  by_cases h : β.degree ≤ L
  · rw [if_pos h]
    rw [Finset.sum_eq_single β]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hb; exact absurd (by simpa using h) hb
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun a ha => ?_).symm
    have : a ≠ β := by
      rintro rfl
      exact h (by simpa using ha)
    simp [Ne.symm this]

theorem s102_Pj_decomp (hT : 0 < T) (L : ℕ) (w : OscPath d m T) :
    s102_Pj T hT L w = ∑ p ∈ s102_idx d L, s102_ellp hT L p w • s102_bpath T L p := by
  apply ContinuousMap.ext (f := (s102_Pj T hT L w : C(Set.Icc (0 : ℝ) T, OscDual d m)))
  intro t
  refine Eq.trans (s102_Pj_apply T hT L w t) ?_
  refine Eq.trans ?_ (ContinuousMap.sum_apply _ _ _).symm
  simp_rw [s102_trunc_eq_sum, Finset.smul_sum, s102_idx, Finset.sum_product]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun α _ => ?_))
  simp only [ContinuousMap.smul_apply, s102_bpath, s102_ellp, s102_ell_apply, s102_node, ContinuousMap.coe_mk]
  rw [smul_comm]
  rfl

theorem s102_isDualCombo (α : MultiIndex d) : IsR2DualCombo m (oscTestFun m α) :=
  ⟨{α}, fun _ => 1, by funext x; simp⟩

theorem s102_ellp_eval (hT : 0 < T) (L : ℕ) (p : ℕ × MultiIndex d) (w : OscPath d m T) :
    s102_ellp hT L p w = OscDual.eval (r2PathAt w ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ))
      (oscTestFun m p.2) := by
  rw [r2PathAt, dif_pos (s102_node hT L p.1).2, OscDual.eval_oscTestFun]
  rfl

/-- The pairing of `J` with `M ∘ (P_L, P_L)` as a finite sum of values on products of evaluations. -/
theorem s102_pair_expand (hT : 0 < T) (L : ℕ) (M : OscPath d m T [×2]→L[ℝ] ℝ)
    (J : TensorDual (OscPath d m T) 2) :
    J (M.compContinuousLinearMap fun _ => s102_Pj T hT L) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin 2 => s102_idx d L),
        M (fun i => s102_bpath T L (r i)) *
          J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)]) := by
  classical
  have hmap : M.compContinuousLinearMap (fun _ => s102_Pj T hT L) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin 2 => s102_idx d L),
        M (fun i => s102_bpath T L (r i)) •
          (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)] := by
    ext x
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp_rw [s102_Pj_decomp]
    rw [M.map_sum_finset
      (fun (i : Fin 2) (p : ℕ × MultiIndex d) => s102_ellp hT L p (x i) • s102_bpath T L p)
      (fun _ => s102_idx d L)]
    simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp [Fin.prod_univ_two, mul_comm]
  rw [hmap, map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- **Uniqueness of the covariance tensor** (`r2JPair` does not depend on the `Exists.choose`). -/
theorem s102_J_unique (C : WholeCoeff d) (hT : 0 < T) (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    {J J' : TensorDual (OscPath d m T) 2} (hJ : IsR2JValue C m T z I J)
    (hJ' : IsR2JValue C m T z I J') : J = J' := by
  classical
  obtain ⟨_, _, hP3⟩ := s102_projection_strong (d := d) m T hT
  have hL : ∀ (L : ℕ) (M : OscPath d m T [×2]→L[ℝ] ℝ),
      J (M.compContinuousLinearMap fun _ => s102_Pj T hT L) =
        J' (M.compContinuousLinearMap fun _ => s102_Pj T hT L) := by
    intro L M
    rw [s102_pair_expand, s102_pair_expand]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    have key : ∀ K : TensorDual (OscPath d m T) 2, IsR2JValue C m T z I K →
        K ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)]) =
          2 * C.ν * ∫ u in I ∩ Set.Icc (0 : ℝ) (min ((s102_node hT L (r 0).1 : Set.Icc (0 : ℝ) T) : ℝ)
              ((s102_node hT L (r 1).1 : Set.Icc (0 : ℝ) T) : ℝ)), z u (fun x =>
            inner ℝ (gradient (propagatorW C u ((s102_node hT L (r 0).1 : Set.Icc (0 : ℝ) T) : ℝ)
              (oscTestFun m (r 0).2)) x)
              (gradient (propagatorW C u ((s102_node hT L (r 1).1 : Set.Icc (0 : ℝ) T) : ℝ)
              (oscTestFun m (r 1).2)) x)) := by
      intro K hK
      exact hK.2 _ _ _ _ _ _ (s102_isDualCombo _) (s102_isDualCombo _) (s102_node hT L (r 0).1).2
        (s102_node hT L (r 1).1).2 (s102_ellp_eval hT L (r 0)) (s102_ellp_eval hT L (r 1))
    rw [key J hJ, key J' hJ']
  refine ContinuousLinearMap.ext fun M => ?_
  have t1 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp (hP3 2 J hJ.1)
  have t2 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp (hP3 2 J' hJ'.1)
  have e : ∀ L, ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow 2 (s102_Pj T hT L) J) L =
      ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow 2 (s102_Pj T hT L) J') L := by
    intro L
    exact hL L M
  have t2' : Tendsto ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow 2 (s102_Pj T hT L) J)
      atTop (𝓝 (J' M)) := by
    refine t2.congr (fun L => (e L).symm)
  exact tendsto_nhds_unique t1 t2'

end HRS.MS.R2Interp

end
