import HRS.Energy.G336C1Aux3
import HRS.Stochastic.Wiener

/-!
# G336C1, helper file 4: the comparison-kernel identity along a deterministic path (zero temperature)

For a deterministic collision-free path (the covering path `Y` solving the integrated ODE of
`IsStrongSolution` with `invβ = 0`), build a probability space with a filtered Brownian family
(`exists_isBrownianFiltration_type`) on which the constant process is a filtered strong solution, and read off
`comparison_kernel_identity_proof` with the expectations being constants.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- A probability space with a filtered Brownian family carrying the deterministic path `x t = mk (Y t)`
as a filtered strong solution (zero temperature). -/
theorem g336c1_space (D : DynData d) (hinvβ : D.invβ = 0) {T : ℝ}
    (Y : ℝ≥0 → Fin N → Euc d)
    (hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      IntegrableOn (fun s : ℝ => particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
        (Set.Icc 0 (t : ℝ)))
    (hy : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, Y t i = Y 0 i +
      ∫ s in Set.Icc (0 : ℝ) t, particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
    (hcont : ∀ i, Continuous fun t : ℝ≥0 => Torus.mk (Y t i))
    (hcol : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y t i)) ∉ collisionSet d N) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      (∀ t ω, X t ω = fun i => Torus.mk (Y t i)) ∧ IsVectorBrownian P W ∧
      IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P ∧ IsStrongSolution P D T X₀ W X ∧
      ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W'' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W'' W X := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, W', hW'⟩ := exists_isBrownianFiltration_type (Fin N × Fin d)
  let x : ℝ≥0 → Config d N := fun t i => Torus.mk (Y t i)
  have hxc : Continuous x := continuous_pi hcont
  let X : ℝ≥0 → Ω → Config d N := fun t _ => x t
  let X₀ : Ω → Config d N := fun _ => x 0
  let W : ℝ≥0 → Ω → (Fin N → Euc d) := ofCoords W'
  have hW : IsVectorBrownian P W := isVectorBrownian_of_isBrownianFiltration P ℱ W' hW'
  have hind : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P := indepFun_const_left _ _
  have hsol : IsStrongSolution P D T X₀ W X := by
    refine ⟨⟨fun t _ => Y t, Filter.Eventually.of_forall fun ω t htT => ⟨hint t htT, fun i => ?_⟩, rfl⟩,
      Filter.Eventually.of_forall fun ω => rfl, Filter.Eventually.of_forall fun ω i => ?_,
      fun t => measurable_const, Filter.Eventually.of_forall fun ω t htT => hcol t htT⟩
    · rw [hinvβ]
      simp only [mul_zero, Real.sqrt_zero, zero_smul, add_zero]
      exact hy t htT i
    · exact (continuous_apply i).comp hxc
  have hfilt : IsFilteredSolution P ℱ W' W X := by
    refine ⟨hW', Filter.Eventually.of_forall fun ω t i j => rfl, fun t => measurable_const, ?_⟩
    intro i
    have hm : Measurable (fun u : Set.Iic i => x (Real.toNNReal (u : ℝ))) :=
      (hxc.comp (continuous_real_toNNReal.comp continuous_subtype_val)).measurable
    exact hm.comp measurable_fst
  exact ⟨Ω, mΩ, P, hP, X₀, W, X, fun t ω => rfl, hW, hind, hsol, ℱ, W', hfilt⟩

theorem g336c1_identity_det (hd : 1 ≤ d) (D : DynData d) (hinvβ : D.invβ = 0) (hN : 2 ≤ N)
    (hV : Torus.IsCk 2 D.V) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {Λ : ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    (Y : ℝ≥0 → Fin N → Euc d)
    (hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      IntegrableOn (fun s : ℝ => particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
        (Set.Icc 0 (t : ℝ)))
    (hy : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, Y t i = Y 0 i +
      ∫ s in Set.Icc (0 : ℝ) t, particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
    (hcont : ∀ i, Continuous fun t : ℝ≥0 => Torus.mk (Y t i))
    (hcol : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y t i)) ∉ collisionSet d N)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hmicro : IntegrableOn (fun r : ℝ =>
      microTerm D h (ρ r) (fun i => Torus.mk (Y (Real.toNNReal r) i))) (Set.Icc 0 t)) :
    modulatedEnergyKernel h (fun i => Torus.mk (Y (Real.toNNReal t) i)) (withDensityReal (ρ t)) -
        modulatedEnergyKernel h (fun i => Torus.mk (Y 0 i)) (withDensityReal (ρ 0)) =
      ∫ r in Set.Icc 0 t,
        ((1 / 2) * commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
            (fun i => Torus.mk (Y (Real.toNNReal r) i)) (withDensityReal (ρ r)) +
          microTerm D h (ρ r) (fun i => Torus.mk (Y (Real.toNNReal r) i))) := by
  obtain ⟨Ω, mΩ, P, hP, X₀, W, X, hXe, hW, hind, hsol, hfilt⟩ := g336c1_space D hinvβ Y hint hy hcont hcol
  have := hP
  have hmicro' : Integrable (fun p : ℝ × Ω => microTerm D h (ρ p.1) (X (Real.toNNReal p.1) p.2))
      ((volume.restrict (Set.Icc 0 t)).prod P) := by
    have := Integrable.comp_fst (f := fun r : ℝ =>
      microTerm D h (ρ r) (fun i => Torus.mk (Y (Real.toNNReal r) i))) hmicro P
    simpa only [hXe] using this
  have key := HRS.KID.comparison_kernel_identity_proof hd D N hN hV h hsm hev T hT ρ Λ hmf hreg P X₀ W X
    hW hind hsol hfilt t ht hmicro'
  simp only [hXe, integral_const, probReal_univ, one_smul, hinvβ, zero_mul, add_zero] at key
  exact key

open HRS.KID HRS.Uniform.Q54c in
/-- The integrand of the identity is measurable on `[0,T]` (through the pointwise algebra `main_alg` and the
joint measurability of `Jc`). -/
theorem g336c1_integrand_measurable (hd : 1 ≤ d) (D : DynData d) (hinvβ : D.invβ = 0) (hN : 2 ≤ N)
    (hV : Torus.IsCk 2 D.V) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {Λ : ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    (Y : ℝ≥0 → Fin N → Euc d)
    (hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
      IntegrableOn (fun s : ℝ => particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
        (Set.Icc 0 (t : ℝ)))
    (hy : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, Y t i = Y 0 i +
      ∫ s in Set.Icc (0 : ℝ) t, particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
    (hcont : ∀ i, Continuous fun t : ℝ≥0 => Torus.mk (Y t i))
    (hcol : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y t i)) ∉ collisionSet d N) :
    AEMeasurable (fun r : ℝ =>
        ((1 / 2) * commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
            (fun i => Torus.mk (Y (Real.toNNReal r) i)) (withDensityReal (ρ r)) +
          microTerm D h (ρ r) (fun i => Torus.mk (Y (Real.toNNReal r) i))))
      (volume.restrict (Set.Icc 0 T)) := by
  obtain ⟨Ω, mΩ, P, hP, X₀, W, X, hXe, hW, hind, hsol, ℱ, W', hfilt⟩ :=
    g336c1_space D hinvβ Y hint hy hcont hcol
  have := hP
  have c : HRS.KID.MFctx D T Λ ρ := ⟨hd, hT, hV, hmf, hreg⟩
  have hN0 : 0 < N := by omega
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hm : Measurable fun r : ℝ => HRS.KID.Jc D h ρ T X r ω₀ := by
    have := (c.measurable_Jc hfilt hsm hev).comp
      (measurable_id.prodMk (measurable_const (a := ω₀)))
    simpa only [Function.comp_def, id_eq] using this
  refine hm.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  have hX : X (Real.toNNReal r) ω₀ ∉ collisionSet d N := by
    rw [hXe]
    exact hcol _ (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
  have hj : HRS.KID.Jc D h ρ T X r ω₀ = ppDrift D h (X (Real.toNNReal r) ω₀) -
      fDrift D h ρ r (X (Real.toNNReal r) ω₀) + wkG D ρ (fK h ρ r) r := by
    unfold HRS.KID.Jc
    rw [clampT_of_mem hr]
  show HRS.KID.Jc D h ρ T X r ω₀ = _
  rw [hj, c.main_alg hsm hev hr hN0 _ hX, hinvβ, zero_mul, add_zero, hXe]

end HRS
