import HRS.MP.SelfSimP5CoreSpec

/-!
# P5 dissipation on `Fin N`: the transport `e : EuclideanSpace ℝ (Fin N) ≃ EucConfig 1 N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Ds

/-- The linear equivalence `z ↦ (k ↦ single 0 (z k))`. -/
def p5d_eL (N : ℕ) : EuclideanSpace ℝ (Fin N) ≃ₗ[ℝ] EucConfig 1 N where
  toFun z := fun k => EuclideanSpace.single (0 : Fin 1) (z k)
  invFun w := WithLp.toLp 2 (fun k => w k 0)
  map_add' x y := by
    funext k
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp
  map_smul' c x := by
    funext k
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp
  left_inv z := by
    ext k
    simp
  right_inv w := by
    funext k
    ext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp

/-- The continuous linear equivalence. -/
def p5d_e (N : ℕ) : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EucConfig 1 N :=
  (p5d_eL N).toContinuousLinearEquiv

theorem p5d_e_apply {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) (k : Fin N) (j : Fin 1) :
    p5d_e N z k j = z k := by
  have : j = 0 := Subsingleton.elim _ _
  subst this
  simp [p5d_e, p5d_eL]

theorem p5d_e_symm_apply {N : ℕ} (w : EucConfig 1 N) (k : Fin N) :
    (p5d_e N).symm w k = w k 0 := by
  rfl

theorem p5d_norm_Euc1 (x : Euc 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

theorem p5d_norm_e_comp {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) (k : Fin N) :
    ‖p5d_e N z k‖ = |z k| := by
  rw [p5d_norm_Euc1, p5d_e_apply]

theorem p5d_abs_le_norm {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) (k : Fin N) : |z k| ≤ ‖z‖ := by
  have := PiLp.norm_apply_le z k
  simpa using this

theorem p5d_norm_e_le {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) : ‖p5d_e N z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun k => ?_
  rw [p5d_norm_e_comp]
  exact p5d_abs_le_norm z k

theorem p5d_norm_le_sqrt {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) :
    ‖z‖ ≤ Real.sqrt N * ‖p5d_e N z‖ := by
  rw [EuclideanSpace.norm_eq]
  have hk : ∀ k, ‖z k‖ ≤ ‖p5d_e N z‖ := fun k => by
    have := norm_le_pi_norm (p5d_e N z) k
    rw [p5d_norm_e_comp] at this
    simpa using this
  calc Real.sqrt (∑ i, ‖z i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin N, ‖p5d_e N z‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hk i) 2
    _ = Real.sqrt N * ‖p5d_e N z‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem p5d_innerL_e {N : ℕ} (a v : EuclideanSpace ℝ (Fin N)) :
    p4InnerL (p5d_e N a) (p5d_e N v) = inner ℝ a v := by
  simp only [p4InnerL, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.proj_apply, innerSL_apply_apply]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PiLp.inner_apply]
  simp [p5d_e_apply, Fin.sum_univ_one, mul_comm]

theorem p5d_measurePreserving (N : ℕ) :
    MeasurePreserving (p5d_e N) (volume : Measure (EuclideanSpace ℝ (Fin N)))
      (volume : Measure (EucConfig 1 N)) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin N)
  have hf : MeasurePreserving (fun x : ℝ => (EuclideanSpace.single (0 : Fin 1) x : Euc 1))
      volume volume := by
    have := (PiLp.volume_preserving_toLp (Fin 1)).comp (volume_preserving_funUnique (Fin 1) ℝ).symm
    convert this using 1
    funext x
    ext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp
  have h2 : MeasurePreserving (fun (w : Fin N → ℝ) k => (EuclideanSpace.single (0 : Fin 1) (w k) : Euc 1))
      volume volume := volume_preserving_pi (fun _ => hf)
  have := h2.comp h1
  convert this using 1
  funext z k
  rfl

end HRS.MP.SelfSimP5Ds
