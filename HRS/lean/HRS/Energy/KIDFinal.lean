import HRS.Energy.KIDAux9
import HRS.Energy.Coercivity

/-!
# KID final: proof of Proposition 3.38 `HRS.comparison_kernel_identity`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.integrable_energy (c : MFctx D T Λ ρ) (hN : 2 ≤ N)
    (hsol : IsStrongSolution P D T X₀ W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) :
    Integrable (fun ω => modulatedEnergyKernel h (X (Real.toNNReal r) ω) (withDensityReal (ρ r))) P := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC⟩ := c.energy_bound hsm hev hN0
  have hm := (c.measurable_energy hsm hev hN0 hr).comp (hsol.adapted (Real.toNNReal r))
  refine Integrable.of_bound (C := C) (by simpa only [Function.comp_def] using hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  simpa [Real.norm_eq_abs] using hC r hr _

theorem MFctx.kid_main (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (hmicro : Integrable (fun p : ℝ × Ω => microTerm D h (ρ p.1) (X (Real.toNNReal p.1) p.2))
      ((volume.restrict (Set.Icc 0 t)).prod P)) :
    ∫ ω, modulatedEnergyKernel h (X (Real.toNNReal t) ω) (withDensityReal (ρ t)) ∂P -
        ∫ ω, modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) ∂P =
      ∫ r in Set.Icc 0 t,
        ((1 / 2) * ∫ ω, commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
            (X (Real.toNNReal r) ω) (withDensityReal (ρ r)) ∂P +
          ∫ ω, microTerm D h (ρ r) (X (Real.toNNReal r) ω) ∂P +
          D.invβ * ∫ ω, offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω)
            (withDensityReal (ρ r)) ∂P) := by
  obtain ⟨hΨpp, hΨf, hpath⟩ := kid_pathwise c hN ht0 htT hsol hF hsm hev
  have hJ := c.integrable_Jc hN ht0 htT hsol hF hsm hev hmicro
  have hEt := c.integrable_energy hN hsol hsm hev (r := t) ⟨ht0.le, htT⟩
  have hE0 : Integrable (fun ω => modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0))) P := by
    have := c.integrable_energy hN hsol hsm hev (r := 0) ⟨le_rfl, c.hT⟩
    simpa using this
  have hI1 := (memLp_two_itoIntegral hF.brownian hΨpp t).integrable one_le_two
  have hI2 := (memLp_two_itoIntegral hF.brownian hΨf t).integrable one_le_two
  have hz1 := integral_itoIntegral hF.brownian hΨpp t
  have hz2 := integral_itoIntegral hF.brownian hΨf t
  have hJint : Integrable (fun ω => ∫ r in Set.Icc 0 t, Jc D h ρ T X r ω ∂volume) P :=
    hJ.integral_prod_right
  have hcongr : ∀ ω, (∫ r in Set.Icc (0 : ℝ) t, Jfull D h ρ X r ω) =
      ∫ r in Set.Icc 0 t, Jc D h ρ T X r ω := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr =>
      (Jc_eq (T := T) ⟨hr.1, hr.2.trans htT⟩ ω).symm
  have hA : ∫ ω, (modulatedEnergyKernel h (X (Real.toNNReal t) ω) (withDensityReal (ρ t)) -
      modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0))) ∂P =
      ∫ ω, ((∫ r in Set.Icc 0 t, Jc D h ρ T X r ω ∂volume) +
        itoIntegral P ℱ W' (fun s ω k => fkeRef D t (Φpp h) X s ω k) t ω -
        itoIntegral P ℱ W' (empiricalNoiseIntegrand D t (fK h ρ) X) t ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hpath] with ω hω
    rw [hω, hcongr]
  have e1 := integral_sub (hJint.add hI1) hI2
  have e2 := integral_add hJint hI1
  simp only [Pi.add_apply] at e1 e2
  rw [← integral_sub hEt hE0, hA, e1, e2, hz1, hz2]
  simp only [add_zero, sub_zero]
  have hswap := integral_integral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)
    (f := fun r ω => Jc D h ρ T X r ω) hJ
  rw [← hswap]
  refine setIntegral_congr_ae measurableSet_Icc ?_
  have h1 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      Integrable (fun ω => microTerm D h (ρ r) (X (Real.toNNReal r) ω)) P :=
    hmicro.prod_right_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 h1] with r hr1 hr
  exact c.per_r hN htT hsol hF hsm hev hr (hr1 hr)

end Main

theorem comparison_kernel_identity_proof (hd : 1 ≤ d) (D : DynData d) (N : ℕ) (hN : 2 ≤ N)
    (hV : Torus.IsCk 2 D.V)
    (h : Torus d → ℝ) (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → Torus d → ℝ) (Λ : ℝ)
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P)
    (hsol : IsStrongSolution P D T X₀ W X)
    (hfilt : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T)
    (hmicro : Integrable (fun p : ℝ × Ω => microTerm D h (ρ p.1) (X (Real.toNNReal p.1) p.2))
      ((volume.restrict (Set.Icc 0 t)).prod P)) :
    ∫ ω, modulatedEnergyKernel h (X (Real.toNNReal t) ω) (withDensityReal (ρ t)) ∂P -
        ∫ ω, modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) ∂P =
      ∫ r in Set.Icc 0 t,
        ((1 / 2) * ∫ ω, commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
            (X (Real.toNNReal r) ω) (withDensityReal (ρ r)) ∂P +
          ∫ ω, microTerm D h (ρ r) (X (Real.toNNReal r) ω) ∂P +
          D.invβ * ∫ ω, offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω)
            (withDensityReal (ρ r)) ∂P) := by
  obtain ⟨ℱ, W', hF⟩ := hfilt
  have c : HRS.KID.MFctx D T Λ ρ := ⟨hd, hT, hV, hmf, hreg⟩
  rcases ht.1.eq_or_lt with h0 | h0
  · subst h0
    simp
  · exact c.kid_main hN h0 ht.2 hsol hF hsm hev hmicro

end HRS.KID

example := (@HRS.KID.comparison_kernel_identity_proof : type_of% @HRS.comparison_kernel_identity)
