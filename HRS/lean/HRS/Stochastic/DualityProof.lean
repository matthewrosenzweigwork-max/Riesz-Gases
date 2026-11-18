import HRS.Stochastic.Duality

/-!
# HRS.Stochastic.DualityProof — Proposition 3.7 (`M:B:prop:duality-identity`), Packet 3

The duality identity
`⟨φ, ρ_N^t⟩ = ⟨U^{0,t}φ, ρ_N^0⟩ + M_N^t[f] + ∫_0^t B_{f^r}(ρ_N^r, ρ_N^r) dr`
(`ρ_N = μ_N − μ`), obtained by subtracting the time-dependent weak form of the mean-field equation
(`meanField_pairing_timeDependent`) from the empirical Itô formula (`empirical_ito_of_contact`,
Lemma 3.6) with the adjoint solution `f` as the test function, and by Lemma 3.1 in its pointwise
form (`flucInteraction_eq`, `integral_nonlocalTerm_eq_neg`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- The pointwise (in time) algebra: the difference of the empirical Itô integrand and the
mean-field integrand, both for the test function with time derivative `-𝓛_r f^r`, is
`flucInteraction`. -/
theorem fluc_pointwise (hd : 1 ≤ d) (hN : 0 < N) {D : DynData d} {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ) {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ)
    (X : Config d N) :
    (pair (empirical X) (fun x => -(backwardGenerator D ρ ψ x) + D.invβ * Torus.laplacian ψ x
        - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x))
      + interactionPairing D ψ (empirical X) (empirical X))
    - pair (withDensityReal ρ) (fun x => -(backwardGenerator D ρ ψ x) + D.invβ * Torus.laplacian ψ x
        + inner ℝ (meanFieldDrift D ρ x) (Torus.grad ψ x))
      = flucInteraction D ψ X ρ := by
  rw [flucInteraction_eq hd hψ hρ hρ1 hLip hN X]
  have h1 : (fun x => -(backwardGenerator D ρ ψ x) + D.invβ * Torus.laplacian ψ x
        - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x))
      = fun x => PDE.nonlocalTerm D ρ ψ x - inner ℝ (Torus.grad ψ x)
          (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)) := by
    funext x
    rw [PDE.backwardGenerator_eq]
    unfold meanFieldDrift
    rw [inner_sub_left, real_inner_comm (Torus.grad ψ x)]
    ring
  have h2 : (fun x => -(backwardGenerator D ρ ψ x) + D.invβ * Torus.laplacian ψ x
        + inner ℝ (meanFieldDrift D ρ x) (Torus.grad ψ x)) = PDE.nonlocalTerm D ρ ψ := by
    funext x
    rw [PDE.backwardGenerator_eq]
    ring
  rw [h1, h2, pair_empirical hN X]
  have h3 : pair (withDensityReal ρ) (PDE.nonlocalTerm D ρ ψ)
      = -∫ x, ρ x * inner ℝ (Torus.grad ψ x)
          (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)) := by
    rw [← integral_nonlocalTerm_eq_neg hd D hψ hρ hρ1 hLip]
    exact PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg _
  rw [h3]
  have h4 : ∑ i, (PDE.nonlocalTerm D ρ ψ (X i) - inner ℝ (Torus.grad ψ (X i))
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ (X i))))
      = -∑ i, (inner ℝ (Torus.grad ψ (X i))
          (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ (X i)))
          - PDE.nonlocalTerm D ρ ψ (X i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  ring

/-- **Proposition 3.7** (`M:B:prop:duality-identity`, main paper L1654-1674). -/
theorem duality_identity
    (hd : 1 ≤ d) (hN : 2 ≤ N) [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} (hV : Torus.IsCk 2 D.V)
    {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Ioc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution D ρ t φ f) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) ∧
    ∀ᵐ ω ∂P,
      IntegrableOn (fun r => flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)) (Icc 0 t) ∧
      flucPair (X (Real.toNNReal t) ω) (ρ t) φ
        = flucPair (X 0 ω) (ρ 0) (f 0)
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal t) ω
          + ∫ r in (0 : ℝ)..t, flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r) := by
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  have hNpos : 0 < N := by omega
  have hC := hf.isC12Test
  have hRg := MFReg.of_regular hρ hreg
  obtain ⟨hprog, hae⟩ := empirical_ito_of_contact hN hV hX hF hocc ht' hC
  obtain ⟨hint2, heq2⟩ := meanField_pairing_timeDependent hd hV hρ hreg ht' hC
  refine ⟨hprog, ?_⟩
  filter_upwards [hae] with ω hω
  obtain ⟨hint1, heq1⟩ := hω t ⟨ht.1.le, le_rfl⟩
  -- the pointwise identity on `[0,t]`
  have hpt : ∀ r ∈ Icc 0 t,
      (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω)))
      - pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))
      = flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r) := by
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    exact fluc_pointwise hd hNpos (hRg.dens r hrT) (hRg.c1 r hrT) (hRg.lip r hrT)
      (hC.c2 r hr) (X (Real.toNNReal r) ω)
  have hint : IntegrableOn (fun r => flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)) (Icc 0 t) := by
    refine (hint1.sub hint2).congr_fun (fun r hr => ?_) measurableSet_Icc
    exact hpt r hr
  refine ⟨hint, ?_⟩
  have hii1 : IntervalIntegrable (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le]
    exact hint1
  have hii2 : IntervalIntegrable (fun r => pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le]
    exact hint2
  have hsplit : ∫ r in (0 : ℝ)..t, flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)
      = (∫ r in (0 : ℝ)..t, (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))))
        - ∫ r in (0 : ℝ)..t, pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x)) := by
    rw [← intervalIntegral.integral_sub hii1 hii2]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht.1.le] at hr
    exact (hpt r hr).symm
  rw [hsplit]
  have hφt : f t = φ := hf.terminal
  unfold flucPair
  rw [← hφt]
  linarith

/-- Restriction of a `C^{1,2}` test on `[0,t]` to `[0,τ]` for `τ ∈ [0,t]`. -/
theorem IsC12Test.restrict {t τ : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft)
    (hτ : τ ∈ Icc 0 t) : IsC12Test τ f ft where
  c2 r hr := hf.c2 r ⟨hr.1, hr.2.trans hτ.2⟩
  cont_c2 j hj := by
    have hmap : Continuous fun p : Icc (0:ℝ) τ × Euc d =>
        ((⟨p.1.1, p.1.2.1, p.1.2.2.trans hτ.2⟩ : Icc (0:ℝ) t), p.2) :=
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    exact (hf.cont_c2 j hj).comp hmap
  time_deriv x r hr := hf.time_deriv x r ⟨hr.1, hr.2.trans_le hτ.2⟩
  cont_time_deriv := by
    have hmap : Continuous fun p : Icc (0:ℝ) τ × Torus d =>
        ((⟨p.1.1, p.1.2.1, p.1.2.2.trans hτ.2⟩ : Icc (0:ℝ) t), p.2) :=
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    exact hf.cont_time_deriv.comp hmap

/-- **Proposition 3.7 for every `τ ∈ [0,t]`** (`M:B:prop:duality-identity`, TeX L1656-1658:
"almost surely, for every `τ ∈ [0,t]`"). -/
theorem duality_identity_all
    (hd : 1 ≤ d) (hN : 2 ≤ N) [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} (hV : Torus.IsCk 2 D.V)
    {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Ioc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution D ρ t φ f) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 t,
      IntegrableOn (fun r => flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)) (Icc 0 τ) ∧
      flucPair (X (Real.toNNReal τ) ω) (ρ τ) (f τ)
        = flucPair (X 0 ω) (ρ 0) (f 0)
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω
          + ∫ r in (0 : ℝ)..τ, flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r) := by
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  have hNpos : 0 < N := by omega
  have hC := hf.isC12Test
  have hRg := MFReg.of_regular hρ hreg
  obtain ⟨hprog, hae⟩ := empirical_ito_of_contact hN hV hX hF hocc ht' hC
  refine ⟨hprog, ?_⟩
  filter_upwards [hae] with ω hω
  intro τ hτ
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans ht'.2⟩
  obtain ⟨hint1, heq1⟩ := hω τ hτ
  obtain ⟨hint2, heq2⟩ := meanField_pairing_timeDependent hd hV hρ hreg hτT (hC.restrict hτ)
  -- the pointwise identity on `[0,τ]`
  have hpt : ∀ r ∈ Icc 0 τ,
      (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω)))
      - pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))
      = flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r) := by
    intro r hr
    have hrt : r ∈ Icc 0 t := ⟨hr.1, hr.2.trans hτ.2⟩
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans (hτ.2.trans ht'.2)⟩
    exact fluc_pointwise hd hNpos (hRg.dens r hrT) (hRg.c1 r hrT) (hRg.lip r hrT)
      (hC.c2 r hrt) (X (Real.toNNReal r) ω)
  have hint : IntegrableOn (fun r => flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r))
      (Icc 0 τ) := by
    refine (hint1.sub hint2).congr_fun (fun r hr => ?_) measurableSet_Icc
    exact hpt r hr
  refine ⟨hint, ?_⟩
  have hii1 : IntervalIntegrable (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact hint1
  have hii2 : IntervalIntegrable (fun r => pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact hint2
  have hsplit : ∫ r in (0 : ℝ)..τ, flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)
      = (∫ r in (0 : ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))))
        - ∫ r in (0 : ℝ)..τ, pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x)) := by
    rw [← intervalIntegral.integral_sub hii1 hii2]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hτ.1] at hr
    exact (hpt r hr).symm
  rw [hsplit]
  unfold flucPair
  linarith

/-- **Proposition 3.7, final form** (`M:B:eq:duality-identity-final`, TeX L1660-1664), with
`U^{0,t}φ = propagator D ρ 0 t φ` and the adjoint solution `f^r = propagator D ρ r t φ`
(existence hypothesis `hex`, cf. Proposition 3.9). The factor `σ_N` of the TeX is a scalar
multiple of both sides and is omitted, as in `PART01_REST_SPEC.md` §3. -/
theorem duality_identity_final
    (hd : 1 ≤ d) (hN : 2 ≤ N) [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} (hV : Torus.IsCk 2 D.V)
    {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Ioc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    (hex : ∃ f, IsClassicalAdjointSolution D ρ t φ f) :
    ∀ᵐ ω ∂P, flucPair (X (Real.toNNReal t) ω) (ρ t) φ
      = flucPair (X 0 ω) (ρ 0) (propagator D ρ 0 t φ)
        + empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X (Real.toNNReal t) ω
        + ∫ r in (0 : ℝ)..t, flucInteraction D (propagator D ρ r t φ) (X (Real.toNNReal r) ω) (ρ r) := by
  have hf : IsClassicalAdjointSolution D ρ t φ (fun r => propagator D ρ r t φ) := by
    have hp : (fun r => propagator D ρ r t φ) = hex.choose := by
      funext r
      unfold propagator
      rw [dif_pos hex]
    rw [hp]
    exact hex.choose_spec
  have hall := (duality_identity_all hd hN hV hρ hreg hX hF hocc ht hφ hf).2
  have hterm : propagator D ρ t t φ = φ := hf.terminal
  filter_upwards [hall] with ω hω
  have h := (hω t ⟨ht.1.le, le_rfl⟩).2
  simp only [hterm] at h
  exact h

/-! ### Quadratic variation, covariation and the zero-temperature case
(`M:B:eq:qv-formula`, `M:B:eq:qv-cross`, L1665-1673) -/

/-- The integrand of `M_N[f]` is bounded uniformly in `s`, `ω` and the coordinate `k`. -/
theorem empiricalNoise_bound {D : DynData d} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) :
    ∃ B : ℝ, ∀ (s : ℝ) (ω : Ω) (k : Fin N × Fin d),
      |empiricalNoiseIntegrand D t f X s ω k| ≤ B := by
  obtain ⟨C, hC⟩ := grad_bound ht hf
  refine ⟨|Real.sqrt (2 * D.invβ) / N| * |C|, fun s ω k => ?_⟩
  rw [empiricalNoiseIntegrand_eq_noiseG]
  exact abs_noiseG_le ht hf hC s _ k

/-- Fibre-wise integrability: for fixed `ω` and `i`, the sum over the `d` coordinates of a
product of two bounded progressive integrands is integrable on any finite-measure set. -/
theorem integrableOn_fiber {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {Φ Φ' : ℝ → Ω → (Fin N × Fin d) → ℝ}
    (hΦ : IsProgressive ℱ Φ) (hΦ' : IsProgressive ℱ Φ') {B B' : ℝ}
    (hB : ∀ s ω k, |Φ s ω k| ≤ B) (hB' : ∀ s ω k, |Φ' s ω k| ≤ B') (ω : Ω) (i : Fin N)
    (S : Set ℝ) (hS : volume S ≠ ⊤) :
    IntegrableOn (fun s => ∑ j : Fin d, Φ s ω (i, j) * Φ' s ω (i, j)) S := by
  refine integrable_finsetSum _ fun j _ => ?_
  refine Measure.integrableOn_of_bounded (M := B * B') hS ?_ ?_
  · exact ((measurable_slice (isProgressive_coord hΦ (i, j)) ω).mul
      (measurable_slice (isProgressive_coord hΦ' (i, j)) ω)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB s ω (i, j)) (hB' s ω (i, j)) (abs_nonneg _)
      ((abs_nonneg _).trans (hB s ω (i, j)))

/-- The covariation process split over the particles. -/
theorem covProcess_eq_sum_fiber {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {Φ Φ' : ℝ → Ω → (Fin N × Fin d) → ℝ}
    (hΦ : IsProgressive ℱ Φ) (hΦ' : IsProgressive ℱ Φ') {B B' : ℝ}
    (hB : ∀ s ω k, |Φ s ω k| ≤ B) (hB' : ∀ s ω k, |Φ' s ω k| ≤ B') (ω : Ω) (τ : ℝ) :
    covProcess Φ Φ' τ ω
      = ∑ i : Fin N, ∫ s in Icc 0 τ, ∑ j : Fin d, Φ s ω (i, j) * Φ' s ω (i, j) := by
  unfold covProcess
  simp only [Fintype.sum_prod_type]
  exact integral_finsetSum _ fun i _ =>
    integrableOn_fiber hΦ hΦ' hB hB' ω i _ measure_Icc_lt_top.ne

/-- The empirical covariation `[M_N[f], M_N[g]]_τ` for `τ ∈ [0,t]` (pointwise in `ω`). -/
theorem covProcess_empirical {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}
    (hF : IsFilteredSolution P ℱ W' W X) {t : ℝ} (ht : 0 ≤ t) {f ft g gt : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (hg : IsC12Test t g gt) (ω : Ω) {τ : ℝ} (hτ : τ ∈ Icc 0 t) :
    covProcess (empiricalNoiseIntegrand D t f X) (empiricalNoiseIntegrand D t g X) τ ω
      = (2 * D.invβ / (N:ℝ)^2) * ∑ i : Fin N, ∫ r in (0:ℝ)..τ,
          inner ℝ (Torus.grad (f r) (X (Real.toNNReal r) ω i))
            (Torus.grad (g r) (X (Real.toNNReal r) ω i)) := by
  obtain ⟨B, hB⟩ := empiricalNoise_bound (D := D) ht hf (Ω := Ω) X
  obtain ⟨B', hB'⟩ := empiricalNoise_bound (D := D) ht hg (Ω := Ω) X
  have hΦ := (isProgressiveL2_empiricalNoiseIntegrand (P := P) (D := D) hF.progressive ht hf).prog
  have hΦ' := (isProgressiveL2_empiricalNoiseIntegrand (P := P) (D := D) hF.progressive ht hg).prog
  rw [covProcess_eq_sum_fiber hΦ hΦ' hB hB' ω τ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hτ0 : (0:ℝ) ≤ τ := hτ.1
  have hpt : ∀ s ∈ Icc 0 τ, ∑ j : Fin d, empiricalNoiseIntegrand D t f X s ω (i, j)
        * empiricalNoiseIntegrand D t g X s ω (i, j)
      = (2 * D.invβ / (N:ℝ)^2) * inner ℝ (Torus.grad (f s) (X (Real.toNNReal s) ω i))
          (Torus.grad (g s) (X (Real.toNNReal s) ω i)) := by
    intro s hs
    have hs' : s ∈ Icc 0 t := ⟨hs.1, hs.2.trans hτ.2⟩
    have hc : Real.sqrt (2 * D.invβ) / (N:ℝ) * (Real.sqrt (2 * D.invβ) / (N:ℝ))
        = 2 * D.invβ / (N:ℝ)^2 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by linarith [D.hβ])]
      ring
    simp only [empiricalNoiseIntegrand, hs', ite_true, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial]
    rw [← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hpt, integral_const_mul,
    intervalIntegral.integral_of_le hτ0, integral_Icc_eq_integral_Ioc]

/-- **Quadratic variation of the empirical martingale** (`M:B:eq:qv-formula`, L1665-1667):
`M_N[f]` is a continuous square-integrable martingale with quadratic variation
`(2/(N²β_N)) ∑_i ∫_0^τ |∇f^r(x_i^r)|² dr`, for `τ ∈ [0,t]` almost surely. -/
theorem empiricalMartingale_qv {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}
    (hF : IsFilteredSolution P ℱ W' W X) {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    IsQuadraticVariation P ℱ t (empiricalMartingale P ℱ W' D t f X)
        (qvProcess (empiricalNoiseIntegrand D t f X)) ∧
      ∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 t,
        qvProcess (empiricalNoiseIntegrand D t f X) τ ω
          = (2 * D.invβ / (N:ℝ)^2) * ∑ i : Fin N, ∫ r in (0:ℝ)..τ,
              ‖Torus.grad (f r) (X (Real.toNNReal r) ω i)‖ ^ 2 := by
  have hprog := isProgressiveL2_empiricalNoiseIntegrand (P := P) (D := D) hF.progressive ht hf
  refine ⟨itoIntegral_isQuadraticVariation hF.brownian hprog t, ?_⟩
  refine Filter.Eventually.of_forall fun ω τ hτ => ?_
  have hq : qvProcess (empiricalNoiseIntegrand D t f X)
      = covProcess (empiricalNoiseIntegrand D t f X) (empiricalNoiseIntegrand D t f X) := by
    funext τ' ω'
    simp only [qvProcess, covProcess, sq]
  rw [hq, covProcess_empirical hF ht hf hf ω hτ]
  simp only [real_inner_self_eq_norm_sq]

/-- **Quadratic covariation** (`M:B:eq:qv-cross`, L1669-1672): for two classical adjoint
solutions `f, g` on `[0,t]`, `M_N[f] M_N[g] - [M_N[f], M_N[g]]` is a martingale and
`[M_N[f], M_N[g]]_τ = (2/(N²β_N)) ∑_i ∫_0^τ ∇f^r(x_i^r)·∇g^r(x_i^r) dr`. -/
theorem empiricalMartingale_cov {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}
    (hF : IsFilteredSolution P ℱ W' W X) {t : ℝ} (ht : 0 ≤ t) {f ft g gt : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (hg : IsC12Test t g gt) :
    Martingale (fun τ ω => empiricalMartingale P ℱ W' D t f X τ ω
        * empiricalMartingale P ℱ W' D t g X τ ω
        - covProcess (empiricalNoiseIntegrand D t f X) (empiricalNoiseIntegrand D t g X) τ ω) ℱ P ∧
      ∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 t,
        covProcess (empiricalNoiseIntegrand D t f X) (empiricalNoiseIntegrand D t g X) τ ω
          = (2 * D.invβ / (N:ℝ)^2) * ∑ i : Fin N, ∫ r in (0:ℝ)..τ,
              inner ℝ (Torus.grad (f r) (X (Real.toNNReal r) ω i))
                (Torus.grad (g r) (X (Real.toNNReal r) ω i)) :=
  ⟨martingale_itoIntegral_mul_sub hF.brownian
      (isProgressiveL2_empiricalNoiseIntegrand (P := P) (D := D) hF.progressive ht hf)
      (isProgressiveL2_empiricalNoiseIntegrand (P := P) (D := D) hF.progressive ht hg),
    Filter.Eventually.of_forall fun ω τ hτ => covProcess_empirical hF ht hf hg ω hτ⟩

/-- **Zero temperature** (`M:B:prop:duality-identity`, L1673: `β_N = ∞`, i.e. `invβ = 0`):
`M_N[f] ≡ 0` almost surely. -/
theorem empiricalMartingale_zero_temp {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}
    (hF : IsFilteredSolution P ℱ W' W X) (h0 : D.invβ = 0) {t : ℝ} {f : ℝ → Torus d → ℝ}
    (hprog : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X)) :
    ∀ᵐ ω ∂P, ∀ τ ≤ t, empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω = 0 := by
  have hΦ0 : ∀ (s : ℝ) (ω : Ω) (k : Fin N × Fin d),
      empiricalNoiseIntegrand D t f X s ω k = 0 := by
    intro s ω k
    simp [empiricalNoiseIntegrand, h0]
  have key : empiricalNoiseIntegrand D t f X
      = fun s ω => (0:ℝ) • empiricalNoiseIntegrand D t f X s ω := by
    funext s ω k
    simp [hΦ0]
  have h := itoIntegral_smul hF.brownian hprog 0
  rw [← key] at h
  filter_upwards [h] with ω hω τ _
  have hτ := hω (Real.toNNReal τ)
  rw [zero_mul] at hτ
  exact hτ

end HRS
