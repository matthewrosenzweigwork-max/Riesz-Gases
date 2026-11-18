import HRS.Energy.KIDAux8

/-!
# KID helper file 9: the identification of the time-`r` expectation
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section PerR

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.aesm_offDiag (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (hN : 0 < N) {r : ℝ} (hr : r ∈ Set.Icc 0 T) {Z : Ω → Config d N}
    (hZ : Measurable Z) (hcol : ∀ᵐ ω ∂P, Z ω ∉ collisionSet d N) :
    AEStronglyMeasurable (fun ω => offDiagDiffPairing (Torus.laplacian h) (Z ω) (withDensityReal (ρ r))) P := by
  have hh2 := isCk2_of_smooth hsm
  have hlap : Continuous (Torus.laplacian h) := HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh2
  have hφ : Torus.IsCk 2 (fK h ρ r) := ContDiff.of_le (c.contDiff_fK hsm hev hr) two_le_top
  have hlφ : Continuous (Torus.laplacian (fK h ρ r)) :=
    HRS.PDE.MFApriori.continuous_laplacian_of_isCk hφ
  have hs1 : Measurable fun ω => ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (Z ω i - Z ω j) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hlap.measurable.comp (((measurable_pi_apply i).comp hZ).sub ((measurable_pi_apply j).comp hZ))
  have hs2 : Measurable fun ω => ∑ i, Torus.laplacian (fK h ρ r) (Z ω i) :=
    Finset.measurable_sum _ fun i _ => hlφ.measurable.comp ((measurable_pi_apply i).comp hZ)
  have hm : Measurable fun ω => (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        Torus.laplacian h (Z ω i - Z ω j)
      - (2 / (N : ℝ)) * ∑ i, Torus.laplacian (fK h ρ r) (Z ω i)
      + ∫ x, ρ r x * Torus.laplacian (fK h ρ r) x :=
    ((hs1.const_mul _).sub (hs2.const_mul _)).add measurable_const
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hcol] with ω hω
  exact (c.offDiag_eval hsm hev hr hN (Z ω) hω).symm

theorem MFctx.per_r (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) {r : ℝ}
    (hr : r ∈ Set.Icc 0 t)
    (hmr : Integrable (fun ω => microTerm D h (ρ r) (X (Real.toNNReal r) ω)) P) :
    ∫ ω, Jc D h ρ T X r ω ∂P =
      (1 / 2) * ∫ ω, commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r)) (X (Real.toNNReal r) ω)
          (withDensityReal (ρ r)) ∂P +
        ∫ ω, microTerm D h (ρ r) (X (Real.toNNReal r) ω) ∂P +
        D.invβ * ∫ ω, offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω)
          (withDensityReal (ρ r)) ∂P := by
  have hN0 : 0 < N := by omega
  have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans htT⟩
  have hZ : Measurable (X (Real.toNNReal r)) := hsol.adapted _
  have hcol : ∀ᵐ ω ∂P, X (Real.toNNReal r) ω ∉ collisionSet d N := by
    filter_upwards [hsol.no_collision] with ω hω
    exact hω _ (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans htT)
  obtain ⟨C₁, C₂, hCb⟩ := c.Cb_bound hsm hev hN0
  have hJω : ∀ᵐ ω ∂P, Jc D h ρ T X r ω =
      (1 / 2) * commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r)) (X (Real.toNNReal r) ω)
          (withDensityReal (ρ r)) +
        microTerm D h (ρ r) (X (Real.toNNReal r) ω) +
        D.invβ * offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω) (withDensityReal (ρ r)) := by
    filter_upwards [hcol] with ω hω
    have hmain := c.main_alg hsm hev hrT hN0 (X (Real.toNNReal r) ω) hω
    have hj : Jc D h ρ T X r ω = ppDrift D h (X (Real.toNNReal r) ω) -
        fDrift D h ρ r (X (Real.toNNReal r) ω) + wkG D ρ (fK h ρ r) r := by
      unfold Jc
      rw [clampT_of_mem hrT]
    rw [hj]
    exact hmain
  have hoff_m := c.aesm_offDiag hsm hev hN0 hrT hZ hcol
  have hoff_i : Integrable (fun ω => offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω)
      (withDensityReal (ρ r))) P := by
    refine Integrable.of_bound hoff_m C₂ ?_
    filter_upwards [hcol] with ω hω
    simpa [Real.norm_eq_abs] using (hCb r hrT _ hω).2
  have hJm : Measurable fun ω => Jc D h ρ T X r ω :=
    by
    have := (c.measurable_Jc hF hsm hev).comp ((measurable_const (a := r)).prodMk (measurable_id (α := Ω)))
    simpa only [Function.comp_def, id_eq] using this
  have hcomm_m : AEStronglyMeasurable (fun ω => commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
      (X (Real.toNNReal r) ω) (withDensityReal (ρ r))) P := by
    have hm : AEStronglyMeasurable (fun ω => 2 * (Jc D h ρ T X r ω -
        microTerm D h (ρ r) (X (Real.toNNReal r) ω) -
        D.invβ * offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω) (withDensityReal (ρ r)))) P :=
      (aestronglyMeasurable_const.mul ((hJm.aestronglyMeasurable.sub hmr.1).sub
        (aestronglyMeasurable_const.mul hoff_m)))
    refine hm.congr ?_
    filter_upwards [hJω] with ω hω
    rw [hω]
    ring
  have hcomm_i : Integrable (fun ω => commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
      (X (Real.toNNReal r) ω) (withDensityReal (ρ r))) P := by
    refine Integrable.of_bound hcomm_m C₁ ?_
    filter_upwards [hcol] with ω hω
    simpa [Real.norm_eq_abs] using (hCb r hrT _ hω).1
  rw [integral_congr_ae hJω]
  have e1 := integral_add ((hcomm_i.const_mul (1 / 2)).add hmr) (hoff_i.const_mul D.invβ)
  have e2 := integral_add (hcomm_i.const_mul (1 / 2)) hmr
  rw [integral_const_mul] at e2
  rw [integral_const_mul] at e1
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2]

end PerR

end HRS.KID
