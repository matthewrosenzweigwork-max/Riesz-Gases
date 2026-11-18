import HRS.MS.MfeConfAux13

/-!
# S.B.1, packet F11 (conditional assembly): (DISS) from the moving-reference entropy inequality and the normaliser identity

Whole-space version of the proof of the torus `mov_mfe_ineq` (`HRS/PDE/MovSpec3.lean`).  The two remaining analytic inputs
are stated as clean propositions:

* `SbMovEnt` (plan packet F9, the whole-space `mov_ent_ineq`): the integrated entropy inequality along the moving reference
  `Q_t = ℚ_{N,β}(μ_t)` with the exact source `R_N = -βN(C_N - E_Q C_N)`, `C_N = pairEnergy (h_{u_V}) = ½ Comm_N`;
* `SbLogK` (plan packet F3, the whole-space `movT_logK_integral`): `log K_t - log K_0 = βN ∫_0^t E_{Q_r}[C_N] dr`.

`sb1_diss_of_parts`: `SbMovEnt ∧ SbLogK ⇒ MfeDiss` (using `sb1_relEntropy_split`, packet F2, proved).  The exact statement
`MfeDiss` is what `sb1_super_of_diss` / `sb1_sub_of_diss` consume.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- The moving reference `Q_t = ℚ_{N,β}(μ_t)`, `β = invβ⁻¹`. -/
def sb1Q (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) : Measure (Whole.EucConfig d N) :=
  Whole.modulatedGibbs (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ r))

/-- `C_N(u_V^r; μ_r) = 𝖥_N^{h_u}(Z, μ_r)` (`pairEnergy` of the commutator kernel), `= ½ Comm_N`. -/
def sb1CN (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (Z : Whole.EucConfig d N) : ℝ :=
  Whole.pairEnergy (Whole.commutatorKernel d D.s (Whole.mfeTransportW D (ρ r))) Z (Whole.withDensityReal (ρ r))

/-- `E_{Q_r}[C_N]`. -/
def sb1EQ (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  ∫ Z, sb1CN D N ρ r Z ∂(sb1Q D N ρ r)

/-- The exact source `R_N^r = -βN (C_N - E_{Q_r} C_N)`. -/
def sb1Src (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (Z : Whole.EucConfig d N) : ℝ :=
  -(D.invβ⁻¹ * N) * (sb1CN D N ρ r Z - sb1EQ D N ρ r)

theorem sb1_commN_eq (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (Z : Whole.EucConfig d N) :
    Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z (Whole.withDensityReal (ρ r)) = 2 * sb1CN D N ρ r Z := by
  unfold Whole.commN sb1CN Whole.centeredPairFunctional Whole.pairEnergy
  ring

/-- **F9 (statement)**: the whole-space `mov_ent_ineq` (Fisher term dropped). -/
def SbMovEnt (D : Whole.WholeDyn d) (N : ℕ) (T : ℝ) (ρ : ℝ → Euc d → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X₀ : Ω → Whole.EucConfig d N) (X : ℝ≥0 → Ω → Whole.EucConfig d N) : Prop :=
  relEntropy (P.map X₀) (sb1Q D N ρ 0) ≠ ⊤ →
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      relEntropy (P.map (X t.toNNReal)) (sb1Q D N ρ t) ≠ ⊤ ∧
      (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (sb1Src D N ρ r) (P.map (X r.toNNReal))) ∧
      IntegrableOn (fun r => ∫ Z, sb1Src D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 t) ∧
      (relEntropy (P.map (X t.toNNReal)) (sb1Q D N ρ t)).toReal ≤
        (relEntropy (P.map X₀) (sb1Q D N ρ 0)).toReal +
          ∫ r in Set.Icc (0 : ℝ) t, ∫ Z, sb1Src D N ρ r Z ∂(P.map (X r.toNNReal))) ∧
    ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (sb1CN D N ρ r) (sb1Q D N ρ r)

/-- **F3 (statement)**: the whole-space `movT_logK_integral`. -/
def SbLogK (D : Whole.WholeDyn d) (N : ℕ) (T : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  IntegrableOn (sb1EQ D N ρ) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t))) -
        Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ 0))) =
      D.invβ⁻¹ * N * ∫ r in Set.Icc (0 : ℝ) t, sb1EQ D N ρ r

/-- The entropy split in the form of the modulated free energy: `𝖤_N(ν,μ_r) = (β⁻¹/N)(H(ν|Q_r) - log K_r)`. -/
theorem sb1_mfe_split (hd : 2 ≤ d) {D : Whole.WholeDyn d} {N : ℕ} (hN : 2 ≤ N) {T Λ : ℝ} {r : ℕ} {ρ : ℝ → Euc d → ℝ}
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) (hβ : 0 < D.invβ) (hdens : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.IsProbDensity (ρ t))
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.IsRegularDensityW r Λ (ρ t))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ν : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν] :
    (relEntropy ν (sb1Q D N ρ t) ≠ ⊤ ↔ Whole.MFEFiniteW d D.s ν (Whole.withDensityReal (ρ t))) ∧
    (Whole.MFEFiniteW d D.s ν (Whole.withDensityReal (ρ t)) →
      Whole.modulatedFreeEnergyW d D.s D.invβ ν (Whole.withDensityReal (ρ t)) =
        D.invβ / N * ((relEntropy ν (sb1Q D N ρ t)).toReal -
          Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t))))) := by
  obtain ⟨Lm, hLm⟩ := sb1_regular_density_bounds (d := d) r Λ
  obtain ⟨hρM, -, hlog⟩ := hLm (ρ t) (hdens t ht) (hreg t ht)
  have hβ' : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  obtain ⟨h1, h2⟩ := sb1_relEntropy_split hd hs0 hsd (hdens t ht) hρM (fun _ => hlog) hN hβ' (ν := ν)
  refine ⟨h1, fun hfin => ?_⟩
  have h3 := h2 hfin
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold Whole.modulatedFreeEnergyW
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hinv : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
  have h4 : (relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ t))).toReal =
      (relEntropy ν (sb1Q D N ρ t)).toReal -
        D.invβ⁻¹ * N * ∫ X, Whole.rieszModulatedEnergy d D.s X (Whole.withDensityReal (ρ t)) ∂ν -
        Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t))) := by
    unfold sb1Q; linarith
  rw [h4]
  field_simp
  have : D.invβ * (D.invβ⁻¹ * (N : ℝ) * ∫ X, Whole.rieszModulatedEnergy d D.s X (Whole.withDensityReal (ρ t)) ∂ν) =
      N * ∫ X, Whole.rieszModulatedEnergy d D.s X (Whole.withDensityReal (ρ t)) ∂ν := by
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
  nlinarith


/-- **F11 (conditional assembly)**: `SbMovEnt` and `SbLogK` give the dissipation inequality (DISS) `MfeDiss` for the
standing hypotheses of S.B.1 (`d ≥ 2`; the entropy split is `sb1_relEntropy_split`). -/
theorem sb1_diss_of_parts (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Whole.WholeDyn d} {N : ℕ} (hN : 2 ≤ N) {T Λ : ℝ} {r : ℕ}
    {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Whole.EucConfig d N} (h : Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) (hEnt : SbMovEnt D N T ρ P X₀ X) (hK : SbLogK D N T ρ) :
    MfeDiss d D N T ρ P X₀ X := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hβ := h.pos_temp
  have hXm : ∀ s : ℝ≥0, Measurable (X s) := h.sol.adapted
  haveI hfp : ∀ r : ℝ, IsProbabilityMeasure (P.map (X r.toNNReal)) := fun r => inferInstance
  haveI hf0 : IsProbabilityMeasure (P.map X₀) := inferInstance
  have hsplit := fun {r' : ℝ} (hr : r' ∈ Set.Icc (0 : ℝ) T) (ν : Measure (Whole.EucConfig d N))
      [IsProbabilityMeasure ν] => sb1_mfe_split hd hN hs0 hsd hβ h.mf.density h.mf_reg hr ν
  have hfinQ : relEntropy (P.map X₀) (sb1Q D N ρ 0) ≠ ⊤ :=
    ((hsplit ⟨le_rfl, hT⟩ (P.map X₀)).1).2 h.mfe_init
  obtain ⟨hHt, hint, hintOn, hineq⟩ := (hEnt hfinQ).1 t ht
  have hMFEt := ((hsplit ht (P.map (X t.toNNReal))).1).1 hHt
  obtain ⟨hlogKint, hlogK⟩ := hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set f : ℝ → Measure (Whole.EucConfig d N) := fun r => P.map (X r.toNNReal) with hf
  set Cf : ℝ → ℝ := fun r => ∫ Z, sb1CN D N ρ r Z ∂(f r) with hCf
  set EQ : ℝ → ℝ := sb1EQ D N ρ with hEQ
  set G : ℝ → ℝ := fun r => ∫ Z, sb1Src D N ρ r Z ∂(f r) with hG
  have hsrc : ∀ r Z, sb1Src D N ρ r Z = -(D.invβ⁻¹ * N) * (sb1CN D N ρ r Z - EQ r) := fun r Z => rfl
  have hβN : D.invβ⁻¹ * (N : ℝ) ≠ 0 := (mul_pos (inv_pos.2 hβ) hNpos).ne'
  have hcomm_int : ∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (sb1CN D N ρ r) (f r) := by
    intro r hr
    have h1 := hint r hr
    have h2 : Integrable (fun Z => EQ r - (D.invβ⁻¹ * N)⁻¹ * sb1Src D N ρ r Z) (f r) :=
      (integrable_const _).sub (h1.const_mul _)
    refine h2.congr (Eventually.of_forall fun Z => ?_)
    simp only [hsrc]
    field_simp
    ring
  have hG_eq : ∀ r ∈ Set.Icc (0 : ℝ) t, G r = -(D.invβ⁻¹ * N) * (Cf r - EQ r) := by
    intro r hr
    haveI := hfp r
    simp only [hG, hCf, hsrc]
    rw [integral_const_mul, integral_sub (hcomm_int r hr) (integrable_const _)]
    simp
  have hCf_eq : ∀ r ∈ Set.Icc (0 : ℝ) t, Cf r = EQ r - (D.invβ⁻¹ * N)⁻¹ * G r := by
    intro r hr
    rw [hG_eq r hr]
    field_simp
    ring
  have hEQint : IntegrableOn EQ (Set.Icc 0 t) := hlogKint.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have hCfint : IntegrableOn Cf (Set.Icc 0 t) := by
    have : IntegrableOn (fun r => EQ r - (D.invβ⁻¹ * N)⁻¹ * G r) (Set.Icc 0 t) :=
      hEQint.sub (hintOn.const_mul _)
    exact this.congr_fun (fun r hr => (hCf_eq r hr).symm) measurableSet_Icc
  have hint_G : ∫ r in Set.Icc (0 : ℝ) t, G r =
      -(D.invβ⁻¹ * N) * ((∫ r in Set.Icc (0 : ℝ) t, Cf r) - ∫ r in Set.Icc (0 : ℝ) t, EQ r) := by
    rw [← integral_sub hCfint hEQint, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hG_eq r hr
  have hq : ∀ r Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z (Whole.withDensityReal (ρ r)) =
      2 * sb1CN D N ρ r Z := fun r Z => sb1_commN_eq D N ρ r Z
  refine ⟨hMFEt, fun r hr => ?_, ?_, ?_⟩
  · have := (hcomm_int r hr).const_mul 2
    exact this.congr (Eventually.of_forall fun Z => (hq r Z).symm)
  · have this : IntegrableOn (fun r => 2 * Cf r) (Set.Icc 0 t) := hCfint.const_mul 2
    refine this.congr_fun (fun r hr => ?_) measurableSet_Icc
    simp only [hCf]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun Z => (hq r Z).symm)
  · have hE0 := (hsplit ⟨le_rfl, hT⟩ (P.map X₀)).2 h.mfe_init
    have hEt := (hsplit ht (P.map (X t.toNNReal))).2 hMFEt
    rw [hEt, hE0]
    have hK' := hlogK t ht
    have hcq : ∫ r in Set.Icc (0 : ℝ) t, ∫ Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
        (Whole.withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)) = 2 * ∫ r in Set.Icc (0 : ℝ) t, Cf r := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      simp only [hCf, hf]
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun Z => hq r Z)
    rw [hcq]
    have hH : (relEntropy (P.map (X t.toNNReal)) (sb1Q D N ρ t)).toReal ≤
        (relEntropy (P.map X₀) (sb1Q D N ρ 0)).toReal + ∫ r in Set.Icc (0 : ℝ) t, G r := hineq
    have hinvβ : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have hpos : 0 < D.invβ / N := div_pos hβ hNpos
    have key : (relEntropy (P.map (X t.toNNReal)) (sb1Q D N ρ t)).toReal -
        Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t))) ≤
        (relEntropy (P.map X₀) (sb1Q D N ρ 0)).toReal -
        Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ 0))) -
          D.invβ⁻¹ * N * ∫ r in Set.Icc (0 : ℝ) t, Cf r := by
      rw [hint_G] at hH
      have hK'' : Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹
          (Whole.withDensityReal (ρ t))) =
          Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹
            (Whole.withDensityReal (ρ 0))) + D.invβ⁻¹ * N * ∫ r in Set.Icc (0 : ℝ) t, EQ r := by
        have := hK'; simp only [hEQ] at *; linarith
      rw [hK'']
      nlinarith
    have := mul_le_mul_of_nonneg_left key hpos.le
    have h5 : D.invβ / N * (D.invβ⁻¹ * N * ∫ r in Set.Icc (0 : ℝ) t, Cf r) = ∫ r in Set.Icc (0 : ℝ) t, Cf r := by
      field_simp
    nlinarith

end HRS.MS.MfeConf
