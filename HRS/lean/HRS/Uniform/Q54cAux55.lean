import HRS.Uniform.Q54cAux54

/-!
# Q54c, part 55: measurability in time of the weak integrand
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

/-- clamping to `[0,T]` -/
def clampT (T r : ℝ) : ℝ := max 0 (min r T)

theorem continuous_clampT (T : ℝ) : Continuous (clampT T) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampT_of_mem {T r : ℝ} (hr : r ∈ Icc 0 T) : clampT T r = r := by
  unfold clampT
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : clampT T r ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem measurable_uncurry_rho (ρ : ℝ → Torus d → ℝ) (hc : ∀ r, Continuous (ρ r))
    (hpt : ∀ x, Measurable fun r => ρ r x) : Measurable fun p : ℝ × Torus d => ρ p.1 p.2 := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (x : Torus d) (r : ℝ) => ρ r x)
    (fun r => hc r) (fun x => hpt x)
  exact this.comp measurable_swap

theorem measurable_wkG (D : DynData d) (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) (hV : Torus.IsCk 1 D.V)
    (ρ : ℝ → Torus d → ℝ)
    (hp : ∀ r, IsProbDensity (ρ r)) (hc : ∀ r, Continuous (ρ r)) (hpt : ∀ x, Measurable fun r => ρ r x) :
    Measurable fun r => wkG D ρ ψ r := by
  have hψ1 := isCk_one_of_two hψ
  have hjm := measurable_uncurry_rho ρ hc hpt
  have hgc : Continuous (Torus.grad ψ) := HRS.PDE.MFLinear.continuous_grad hψ1
  have hLc : Continuous (fun x => D.invβ * Torus.laplacian ψ x -
      inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) := by
    refine (continuous_const.mul (HRS.PDE.MFApriori.continuous_laplacian_of_isCk hψ)).sub ?_
    exact (HRS.PDE.MFLinear.continuous_grad hV).inner hgc
  unfold wkG
  refine Measurable.add ?_ ?_
  · have e1 : (fun r => pair (withDensityReal (ρ r)) (fun x => D.invβ * Torus.laplacian ψ x -
        inner ℝ (Torus.grad D.V x) (Torus.grad ψ x))) = fun r => ∫ x, (D.invβ * Torus.laplacian ψ x -
        inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) * ρ r x := funext fun r => pair_wDR (hp r) _
    rw [e1]
    have : StronglyMeasurable (fun p : ℝ × Torus d => (D.invβ * Torus.laplacian ψ p.2 -
        inner ℝ (Torus.grad D.V p.2) (Torus.grad ψ p.2)) * ρ p.1 p.2) :=
      ((hLc.measurable.comp measurable_snd).mul hjm).stronglyMeasurable
    exact (this.integral_prod_right' (ν := volume)).measurable
  · set kf : Torus d → Torus d → ℝ := fun x y => if x = y then 0 else
      inner ℝ (Torus.grad ψ x - Torus.grad ψ y) (Torus.matVec D.M (periodicRieszGrad d D.s (x - y))) with hkf
    have e2 : ∀ r, interactionPairing D ψ (withDensityReal (ρ r)) (withDensityReal (ρ r)) =
        (1 / 2) * ∫ x, ρ r x * ∫ y, ρ r y * kf x y := by
      intro r
      unfold interactionPairing
      simp_rw [HRS.PDE.MFPairing.integral_withDensityReal (hp r).measurable (hp r).nonneg]
      rfl
    have hmat : Measurable (fun v : Euc d => Torus.matVec D.M v) :=
      (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)).measurable
    have hkm : Measurable (fun q : Torus d × Torus d => kf q.1 q.2) := by
      refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
      refine Measurable.inner ?_ ?_
      · exact (hgc.measurable.comp measurable_fst).sub (hgc.measurable.comp measurable_snd)
      · exact hmat.comp ((HRS.KernelGrad.measurable_periodicRieszGrad D.hsd).comp
          (measurable_fst.sub measurable_snd))
    have hI : Measurable (fun p : ℝ × Torus d => ∫ y, ρ p.1 y * kf p.2 y) := by
      have : StronglyMeasurable (fun q : (ℝ × Torus d) × Torus d => ρ q.1.1 q.2 * kf q.1.2 q.2) :=
        ((hjm.comp (measurable_fst.fst.prodMk measurable_snd)).mul
          (hkm.comp (measurable_fst.snd.prodMk measurable_snd))).stronglyMeasurable
      exact (this.integral_prod_right' (ν := volume)).measurable
    have hO : Measurable (fun r : ℝ => ∫ x, ρ r x * ∫ y, ρ r y * kf x y) := by
      have : StronglyMeasurable (fun p : ℝ × Torus d => ρ p.1 p.2 * ∫ y, ρ p.1 y * kf p.2 y) :=
        (hjm.mul hI).stronglyMeasurable
      exact (this.integral_prod_right' (ν := volume)).measurable
    have : (fun r => interactionPairing D ψ (withDensityReal (ρ r)) (withDensityReal (ρ r))) =
        fun r => (1 / 2) * ∫ x, ρ r x * ∫ y, ρ r y * kf x y := funext e2
    rw [this]
    exact hO.const_mul _

end HRS.Uniform.Q54c
