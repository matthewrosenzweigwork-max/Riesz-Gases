import HRS.PDE.TorusFPExistAux11

/-!
# D1 existence, helper 12: mollification (generic part)

`C²` approximation of periodic functions by smooth ones, with convergence of the first and second
derivatives: this is the generic Euclidean-space part (convolution with a normed bump function).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped Convolution

namespace HRS

variable {n : ℕ}

section Mollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Mollification `(ρ ⋆ G)(y) = ∫ ρ(t) G(y - t) dt`. -/
def d1_mol (ρ : Euc n → ℝ) (G : Euc n → E) (y : Euc n) : E := ∫ t, ρ t • G (y - t)

theorem d1_mol_eq_conv (ρ : Euc n → ℝ) (G : Euc n → E) :
    d1_mol ρ G = (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) := rfl

theorem d1_mol_hasFDerivAt {ρ : Euc n → ℝ} (hρ : Integrable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    {G : Euc n → E} (hG : ContDiff ℝ 1 G) {B M : ℝ} (hB : ∀ y, ‖G y‖ ≤ B)
    (hM : ∀ y, ‖fderiv ℝ G y‖ ≤ M) (y : Euc n) :
    HasFDerivAt (d1_mol ρ G) (d1_mol ρ (fderiv ℝ G) y) y := by
  have hGc : Continuous G := hG.continuous
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hG'c : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hmeas : ∀ x, AEStronglyMeasurable (fun t => ρ t • G (x - t)) volume := fun x =>
    hρ.aestronglyMeasurable.smul (hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Euc n) (t : Euc n) => ρ t • G (x - t))
    (F' := fun (x : Euc n) (t : Euc n) => ρ t • fderiv ℝ G (x - t))
    (bound := fun t => ρ t * M) (s := Set.univ) (x₀ := y) (μ := volume) Filter.univ_mem
    (Eventually.of_forall hmeas)
    (by
      refine (hρ.mul_const B).mono' (hmeas y) (ae_of_all _ fun t => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
      exact mul_le_mul_of_nonneg_left (hB _) (hρ0 t))
    (hρ.aestronglyMeasurable.smul (hG'c.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (ae_of_all _ fun t x _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
      exact mul_le_mul_of_nonneg_left (hM _) (hρ0 t))
    (hρ.mul_const M)
    (ae_of_all _ fun t x _ => by
      have h1 : HasFDerivAt (fun x : Euc n => x - t) (ContinuousLinearMap.id ℝ (Euc n)) x :=
        (hasFDerivAt_id x).sub_const t
      have h2 := (hGd (x - t)).hasFDerivAt.comp x h1
      have h3 := h2.const_smul (ρ t)
      exact h3.congr_fderiv (by ext v; simp))
  exact h

end Mollify


section Periodic

variable {E : Type*} [NormedAddCommGroup E]

theorem d1_rep_mem_cube (x : Torus n) :
    Torus.rep x ∈ (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  refine ⟨fun i => Torus.rep x i, fun i _ => ?_, rfl⟩
  have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
  simp only [zero_add] at this
  exact ⟨this.1, this.2.le⟩

theorem d1_periodic_bounded {G : Euc n → E} (hc : Continuous G)
    (hp : ∀ (y : Euc n) (k : Lattice n), G (y + Lattice.toEuc k) = G y) : ∃ B, ∀ y, ‖G y‖ ≤ B := by
  let K : Set (Euc n) := (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B, fun y => ?_⟩
  rw [← periodic_rep_mk G hp y]
  exact hB _ (d1_rep_mem_cube _)

theorem d1_periodic_uniformContinuous {G : Euc n → E} (hc : Continuous G)
    (hp : ∀ (y : Euc n) (k : Lattice n), G (y + Lattice.toEuc k) = G y) : UniformContinuous G := by
  let K : Set (Euc n) := (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hK' : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  have hu := hK'.uniformContinuousOn_of_continuous hc.continuousOn
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun y y' hyy' => ?_⟩
  obtain ⟨k, hk⟩ := exists_lattice_of_mk_eq (x := Torus.rep (Torus.mk y)) (y := y) (Torus.mk_rep _)
  have hz : Torus.rep (Torus.mk y) ∈ K := d1_rep_mem_cube _
  set z := Torus.rep (Torus.mk y) with hzdef
  have hy : G y = G z := by rw [hk, hp]
  have hy' : G y' = G (y' + Lattice.toEuc k) := (hp y' k).symm
  have hdist : dist z (y' + Lattice.toEuc k) = dist y y' := by
    rw [hk, dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have h1 : dist z (y' + Lattice.toEuc k) < min δ₀ 1 := by rw [hdist]; exact hyy'
  have hz' : y' + Lattice.toEuc k ∈ Metric.cthickening 1 K :=
    Metric.mem_cthickening_of_dist_le _ z 1 K hz (by
      have := lt_of_lt_of_le h1 (min_le_right _ _); rw [dist_comm]; exact this.le)
  have hzK : z ∈ Metric.cthickening 1 K := Metric.self_subset_cthickening _ hz
  rw [hy, hy']
  exact hδ z hzK _ hz' (lt_of_lt_of_le h1 (min_le_left _ _))

end Periodic

theorem d1_laplacian_eq_sum (F : Euc n → ℝ) (y : Euc n) :
    Laplacian.laplacian F y = ∑ i : Fin n, fderiv ℝ (fderiv ℝ F) y (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F
      (EuclideanSpace.basisFun (Fin n) ℝ)) y
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp

end HRS
