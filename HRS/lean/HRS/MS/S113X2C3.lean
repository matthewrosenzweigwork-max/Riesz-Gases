import HRS.MS.S113X2B9
import HRS.MS.S113X2A3e

/-!
# S11.3 X2 wiring (worker S11W), C3: coordinate transport and the slice subsolution inequality in `ℝ^{Nd}`

`Jc d N : EuclideanSpace ℝ (Fin (N*d)) ≃L (Fin N → Euc d)` transports the part-A objects to the Euclidean space of part B.
* `s113c_J_integral`: `∫_E g∘J = c ∫ g` for a constant `c > 0` (Lebesgue measure is carried to a multiple of Lebesgue measure).
* `s113c_lap_comp`, `s113c_genx_comp`: the generator `s113a_genx` in `ℝ^{Nd}` coordinates is `β⁻¹ Δ + D·[b_E]`.
* `s113c_sub`: the `sub` field of `s113b_Data` for the density `u_E = u∘J / c` of the killed laws, from `s113a_killed_slice_subsolution`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)

variable {d N : ℕ}

/-- Lebesgue measure on `ℝ^{Nd}` is carried by `Jc` to a positive multiple of Lebesgue measure on `(ℝ^d)^N`. -/
theorem s113c_J_integral (d N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : EucConfig d N → ℝ, ∫ z, g (Jc d N z) = c * ∫ x, g x := by
  haveI : (volume : Measure (EuclideanSpace ℝ (Fin (N * d)))).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (EucConfig d N)).IsAddHaarMeasure := inferInstance
  haveI : (Measure.map (Jc d N) (volume : Measure (EuclideanSpace ℝ (Fin (N * d))))).IsAddHaarMeasure :=
    (Jc d N).isAddHaarMeasure_map _
  set μ' := Measure.map (Jc d N) (volume : Measure (EuclideanSpace ℝ (Fin (N * d)))) with hμ'
  have h := Measure.isAddLeftInvariant_eq_smul μ' (volume : Measure (EucConfig d N))
  have hne : μ'.addHaarScalarFactor volume ≠ 0 := by
    intro h0
    have h00 : μ' = 0 := by rw [h, h0]; simp
    have hpos := Measure.IsOpenPosMeasure.open_pos (μ := μ') univ isOpen_univ univ_nonempty
    rw [h00] at hpos
    simp at hpos
  refine ⟨(μ'.addHaarScalarFactor volume : ℝ), by exact_mod_cast pos_iff_ne_zero.2 hne, fun g => ?_⟩
  have hemb : MeasurableEmbedding (Jc d N) := (Jc d N).toHomeomorph.measurableEmbedding
  have h1 : ∫ z, g (Jc d N z) = ∫ x, g x ∂μ' := (hemb.integral_map g).symm
  have h2 : ∫ x, g x ∂μ' = ∫ x, g x ∂((μ'.addHaarScalarFactor volume) • (volume : Measure (EucConfig d N))) :=
    congrArg (fun m : Measure (EucConfig d N) => ∫ x, g x ∂m) h
  rw [h1, h2, integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

/-- The constant of `s113c_J_integral`. -/
def s113c_c (d N : ℕ) : ℝ := Classical.choose (s113c_J_integral d N)

theorem s113c_c_pos (d N : ℕ) : 0 < s113c_c d N := (Classical.choose_spec (s113c_J_integral d N)).1

theorem s113c_c_integral (d N : ℕ) (g : EucConfig d N → ℝ) :
    ∫ z, g (Jc d N z) = s113c_c d N * ∫ x, g x := (Classical.choose_spec (s113c_J_integral d N)).2 g

/-- The Laplacian of a composition with `Jc`. -/
theorem s113c_lap_comp {φ : EucConfig d N → ℝ} (hφ : ContDiff ℝ 2 φ) (z : s113b_E (N * d)) :
    s113b_lap (fun y => φ (Jc d N y)) z =
      ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ φ) (Jc d N z) (configBasis d N k) (configBasis d N k) := by
  unfold s113b_lap
  have h : ∀ m : Fin (N * d),
      fderiv ℝ (fderiv ℝ (fun y => φ (Jc d N y))) z (EuclideanSpace.single m 1) (EuclideanSpace.single m 1) =
        fderiv ℝ (fderiv ℝ φ) (Jc d N z) (configBasis d N (finProdFinEquiv.symm m))
          (configBasis d N (finProdFinEquiv.symm m)) := by
    intro m
    have := fderiv2_comp_clm (Jc d N : s113b_E (N * d) →L[ℝ] EucConfig d N) hφ z
      (EuclideanSpace.single m 1) (EuclideanSpace.single m 1)
    simpa [Jc_single] using this
  rw [Finset.sum_congr rfl fun m _ => h m]
  exact Equiv.sum_comp (finProdFinEquiv.symm : Fin (N * d) ≃ Fin N × Fin d)
    (fun k => fderiv ℝ (fderiv ℝ φ) (Jc d N z) (configBasis d N k) (configBasis d N k))

theorem s113c_fderiv_comp {φ : EucConfig d N → ℝ} (hφ : Differentiable ℝ φ) (z v : s113b_E (N * d)) :
    fderiv ℝ (fun y => φ (Jc d N y)) z v = fderiv ℝ φ (Jc d N z) (Jc d N v) := by
  have := (hφ (Jc d N z)).hasFDerivAt.comp z (Jc d N).hasFDerivAt
  have e : fderiv ℝ (fun y => φ (Jc d N y)) z = (fderiv ℝ φ (Jc d N z)).comp (Jc d N : s113b_E (N * d) →L[ℝ] EucConfig d N) :=
    this.fderiv
  rw [e]
  rfl

/-- The physical drift in `ℝ^{Nd}` coordinates. -/
def s113c_bE (d : ℕ) (s q β : ℝ) (N : ℕ) (z : s113b_E (N * d)) : s113b_E (N * d) :=
  (Jc d N).symm (fun i => particleDriftW (quadraticGradientDyn d s q β) (Jc d N z) i)

theorem s113c_genx_comp (s q β : ℝ) {φ : EucConfig d N → ℝ} (hφ : ContDiff ℝ 2 φ) (z : s113b_E (N * d)) :
    s113a_genx d s q β N φ (Jc d N z) =
      β⁻¹ * s113b_lap (fun y => φ (Jc d N y)) z +
        fderiv ℝ (fun y => φ (Jc d N y)) z (s113c_bE d s q β N z) := by
  rw [s113c_lap_comp hφ, s113c_fderiv_comp (hφ.differentiable (by norm_num))]
  unfold s113a_genx s113c_bE
  simp

/-- The density of the killed law in `ℝ^{Nd}` coordinates. -/
def s113c_uE (d N : ℕ) (u : ℝ → EucConfig d N → ℝ) (t : ℝ) (z : s113b_E (N * d)) : ℝ :=
  u t (Jc d N z) / s113c_c d N

/-- Integrals against a density are the `ℝ^{Nd}` integrals against `u_E`. -/
theorem s113c_integral_density {u : EucConfig d N → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hum : Measurable u)
    (g : EucConfig d N → ℝ) :
    ∫ x, g x ∂(volume.withDensity (fun x => ENNReal.ofReal (u x))) =
      ∫ z, g (Jc d N z) * (u (Jc d N z) / s113c_c d N) := by
  have hc := s113c_c_pos d N
  have hm : Measurable (fun x => ENNReal.ofReal (u x)) := ENNReal.measurable_ofReal.comp hum
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have : ∀ z : s113b_E (N * d), g (Jc d N z) * (u (Jc d N z) / s113c_c d N) =
      (fun x => (ENNReal.ofReal (u x)).toReal • g x) (Jc d N z) / s113c_c d N := by
    intro z
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hu0 _)]
    ring
  simp_rw [this]
  rw [integral_div, s113c_c_integral d N (fun x => (ENNReal.ofReal (u x)).toReal • g x)]
  field_simp

/-- **The `sub` field of `s113b_Data`.**  For a family of densities `u_t` of the killed laws on `[0,T]`, `G` an open set
of `ℝ^{Nd}` away from collisions, and a drift `b̃` agreeing with the physical drift on `G`: the every-time slice
inequality in `ℝ^{Nd}` coordinates. -/
theorem s113c_sub {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    (u : ℝ → EucConfig d N → ℝ) (hu0 : ∀ t x, 0 ≤ u t x) (hum : ∀ t, Measurable (u t)) {T : ℝ}
    (hdens : ∀ t ∈ Set.Icc 0 T, s113a_killedLaw P D X₀ X chi t.toNNReal =
      volume.withDensity (fun x => ENNReal.ofReal (u t x)))
    (G : Set (s113b_E (N * d))) (hGfree : ∀ z ∈ G, Jc d N z ∉ eucCollisionSet d N)
    (b' : s113b_E (N * d) → s113b_E (N * d)) (hb' : ∀ z ∈ G, b' z = s113c_bE d s q β N z) :
    ∀ ψ : s113b_E (N * d) → ℝ, s113b_Cinf ψ → HasCompactSupport ψ → (∀ z, 0 ≤ ψ z) → tsupport ψ ⊆ G →
      ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T →
        ∫ z, ψ z * s113c_uE d N u t z ≤ (∫ z, ψ z * s113c_uE d N u s' z) +
          ∫ τ in s'..t, ∫ z, (β⁻¹ * s113b_lap ψ z + fderiv ℝ ψ z (b' z)) * s113c_uE d N u τ z := by
  intro ψ hψ hψc hψ0 hψG s' t hs' hst htT
  set φ : EucConfig d N → ℝ := fun x => ψ ((Jc d N).symm x) with hφdef
  have hφJ : ∀ z, φ (Jc d N z) = ψ z := fun z => by simp [hφdef]
  have hφsm : ContDiff ℝ ∞ φ := hψ.comp (Jc d N).symm.contDiff
  have hφ2 : ContDiff ℝ 2 φ := hφsm.of_le (by simp)
  have hφfun : (fun y => φ (Jc d N y)) = ψ := funext hφJ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => hψ0 _
  set K' : Set (EucConfig d N) := (Jc d N) '' (tsupport ψ) with hK'
  have hK'c : IsCompact K' := hψc.isCompact.image (Jc d N).continuous
  have hK'free : ∀ x ∈ K', x ∉ eucCollisionSet d N := by
    rintro x ⟨z, hz, rfl⟩
    exact hGfree z (hψG hz)
  have hsupp : ∀ x, x ∉ K' → φ x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    refine ⟨(Jc d N).symm x, subset_tsupport _ ?_, by simp⟩
    exact hne
  obtain ⟨-, hmain⟩ := s113a_killed_slice_subsolution hβ hX D hD chi hchi hchi0 hchi1 φ hφsm hφ0 hK'c hK'free hsupp
    hs' hst
  -- the integrand identification
  have hrep : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ g : EucConfig d N → ℝ,
      ∫ x, g x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) =
        ∫ z, g (Jc d N z) * s113c_uE d N u r z := fun r hr g => by
    rw [hdens r hr, s113c_integral_density (hu0 r) (hum r) g]
    rfl
  have hgen : ∀ z, s113a_genx d s q β N φ (Jc d N z) = β⁻¹ * s113b_lap ψ z + fderiv ℝ ψ z (b' z) := by
    intro z
    rw [s113c_genx_comp s q β hφ2, hφfun]
    by_cases hz : z ∈ tsupport ψ
    · rw [hb' z (hψG hz)]
    · rw [fderiv_of_notMem_tsupport ℝ hz]; simp
  have hb : ∫ x, φ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal) = ∫ z, ψ z * s113c_uE d N u t z := by
    rw [hrep t ⟨hs'.trans hst, htT⟩]
    simp_rw [hφJ]
  have ha : ∫ x, φ x ∂(s113a_killedLaw P D X₀ X chi s'.toNNReal) = ∫ z, ψ z * s113c_uE d N u s' z := by
    rw [hrep s' ⟨hs', hst.trans htT⟩]
    simp_rw [hφJ]
  have hint : ∫ r in Set.Ioo s' t, ∫ x, s113a_genx d s q β N φ x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) =
      ∫ τ in s'..t, ∫ z, (β⁻¹ * s113b_lap ψ z + fderiv ℝ ψ z (b' z)) * s113c_uE d N u τ z := by
    rw [intervalIntegral.integral_of_le hst, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hs'.trans hr.1.le, hr.2.le.trans htT⟩
    rw [hrep r hr' (s113a_genx d s q β N φ)]
    simp_rw [hgen]
  rw [hb, ha, hint] at hmain
  exact hmain

/-- `s113c_sub` for the undivided density `z ↦ u_t(Jc z)` (the inequality is homogeneous in `u`). -/
theorem s113c_sub' {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    (u : ℝ → EucConfig d N → ℝ) (hu0 : ∀ t x, 0 ≤ u t x) (hum : ∀ t, Measurable (u t)) {T : ℝ}
    (hdens : ∀ t ∈ Set.Icc 0 T, s113a_killedLaw P D X₀ X chi t.toNNReal =
      volume.withDensity (fun x => ENNReal.ofReal (u t x)))
    (G : Set (s113b_E (N * d))) (hGfree : ∀ z ∈ G, Jc d N z ∉ eucCollisionSet d N)
    (b' : s113b_E (N * d) → s113b_E (N * d)) (hb' : ∀ z ∈ G, b' z = s113c_bE d s q β N z) :
    ∀ ψ : s113b_E (N * d) → ℝ, s113b_Cinf ψ → HasCompactSupport ψ → (∀ z, 0 ≤ ψ z) → tsupport ψ ⊆ G →
      ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T →
        ∫ z, ψ z * u t (Jc d N z) ≤ (∫ z, ψ z * u s' (Jc d N z)) +
          ∫ τ in s'..t, ∫ z, (β⁻¹ * s113b_lap ψ z + fderiv ℝ ψ z (b' z)) * u τ (Jc d N z) := by
  intro ψ hψ hψc hψ0 hψG s' t hs' hst htT
  have h := s113c_sub hβ hX D hD chi hchi hchi0 hchi1 u hu0 hum hdens G hGfree b' hb' ψ hψ hψc hψ0 hψG s' t hs' hst htT
  have hc := s113c_c_pos d N
  have e : ∀ (F : s113b_E (N * d) → ℝ) (r : ℝ), ∫ z, F z * s113c_uE d N u r z = (∫ z, F z * u r (Jc d N z)) / s113c_c d N := by
    intro F r
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [s113c_uE]
    ring
  simp_rw [e] at h
  rw [intervalIntegral.integral_div, ← add_div, div_le_div_iff_of_pos_right hc] at h
  exact h

end HRS.MS.S113X2C

end
