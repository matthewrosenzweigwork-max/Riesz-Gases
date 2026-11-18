import HRS.MS.MfeConfAux174
import HRS.MS.MfeConfAux14
import HRS.MS.MfeConfAux60

/-!
# S.B.1 (SB5), the super row at `d = 1`: a dimension-free entropy split

`sb1_relEntropy_split'` is `sb1_relEntropy_split` for every `d ≥ 1`: it is obtained from `sb1_kl_Q` (Aux109, `H(ν|Q) = H(ν|μ^{⊗N}) + βN∫En dν + log K`
when `H(ν|μ^{⊗N}) < ∞` and `En ∈ L¹(ν)`) and its converse `sb1_Q_conv` (Aux140), with `Sb1Rho` for regular densities
(`sb1_rho_of_regular`).  The primed copies of `sb1_mfe_split`, `sb1_diss_of_parts`, `sb1_superDiss_of_movEnt`, `sb1_super_of_movEnt` differ from the
originals only by `1 ≤ d` and the call to the new split.
-/

noncomputable section

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_rho_of_dec {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hdens : Whole.IsProbDensity ρ) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ y, ρ y ≤ c * sb1w ((d : ℝ) + 3) y) :
    Sb1Rho ρ c (c * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) where
  dens := hdens
  le := fun y => (hb y).trans (mul_le_of_le_one_right hc (sb1w_le_one (by positivity) y))
  mom := by
    have hd2 := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
    refine (hd2.const_mul c).mono' (hdens.measurable.mul measurable_norm).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have h0 := hdens.nonneg y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (norm_nonneg y))]
    have h1 := hb y
    have h2 := sb1w_succ ((d : ℝ) + 2) y
    have h3 := sb1w_pos ((d : ℝ) + 3) y
    have e : (d : ℝ) + 2 + 1 = (d : ℝ) + 3 := by ring
    rw [e] at h2
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_right h1 (norm_nonneg y)]
  momle := by
    have hI := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y =>
      mul_nonneg (hdens.nonneg y) (norm_nonneg y)) (hI.const_mul c) (Eventually.of_forall fun y => ?_)
    have h0 := hdens.nonneg y
    have h1 := hb y
    have h2 := sb1w_succ ((d : ℝ) + 2) y
    have h3 := sb1w_pos ((d : ℝ) + 3) y
    have e : (d : ℝ) + 2 + 1 = (d : ℝ) + 3 := by ring
    rw [e] at h2
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_right h1 (norm_nonneg y)]

theorem sb1_rho_of_regular {ρ : Euc d → ℝ} {r : ℕ} {Λ : ℝ} (hd : 1 ≤ d) (hdens : Whole.IsProbDensity ρ)
    (hreg : Whole.IsRegularDensityW r Λ ρ) : ∃ Cρ M1 : ℝ, Sb1Rho ρ Cρ M1 := by
  have hw : Whole.weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal Λ := le_trans le_add_self hreg.2.2
  have hfin : Whole.weightedSupE r ((d : ℝ) + 3) ρ < ⊤ := lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hΛ : (Whole.weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ max Λ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
    rw [ENNReal.toReal_ofReal'] at this
    exact this
  have hc : 0 ≤ (d : ℝ) ^ r * max Λ 0 * 2 ^ ((d : ℝ) + 3) := by positivity
  refine ⟨_, _, sb1_rho_of_dec hd hdens hc fun y => ?_⟩
  have := sb1_dec3_of_regular hd hreg.2.1 hfin hΛ (l := 0) (Nat.zero_le r) y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

section Split

variable {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ}

theorem sb1_relEntropy_split' (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) (hN : 1 ≤ N) {b : ℝ}
    (hb : 0 < b) {ν : Measure (Whole.EucConfig d N)} [IsProbabilityMeasure ν] :
    (relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ0)) ≠ ⊤ ↔
      Whole.MFEFiniteW d s ν (Whole.withDensityReal ρ0)) ∧
    (Whole.MFEFiniteW d s ν (Whole.withDensityReal ρ0) →
      (relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N b
          (Whole.withDensityReal ρ0))).toReal =
        (relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)).toReal +
          b * N * ∫ X, Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ0) ∂ν +
          Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ0))) := by
  have hk := sb1KerU_riesz d s hs0
  have hen : (fun X : Whole.EucConfig d N => Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ0)) =
      sb1En (Whole.rieszKernel d s) ρ0 := funext fun X => sb1_modEnergy_eq R.dens _ X
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · obtain ⟨h1, h2⟩ := sb1_Q_conv hd hs0 hsd hN hb hk R h
    exact ⟨h1, by rw [hen]; exact h2⟩
  · exact (sb1_kl_Q hd hs0 hsd hN hb.le hk R h.1 (by rw [← hen]; exact h.2)).1
  · have := (sb1_kl_Q hd hs0 hsd hN hb.le hk R h.1 (by rw [← hen]; exact h.2)).2
    rw [this]
    simp only [hen]

/-- The entropy split in the form of the modulated free energy: `𝖤_N(ν,μ_r) = (β⁻¹/N)(H(ν|Q_r) - log K_r)`. -/
theorem sb1_mfe_split' (hd : 1 ≤ d) {D : Whole.WholeDyn d} {N : ℕ} (hN : 2 ≤ N) {T Λ : ℝ} {r : ℕ} {ρ : ℝ → Euc d → ℝ}
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) (hβ : 0 < D.invβ) (hdens : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.IsProbDensity (ρ t))
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.IsRegularDensityW r Λ (ρ t))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ν : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν] :
    (relEntropy ν (sb1Q D N ρ t) ≠ ⊤ ↔ Whole.MFEFiniteW d D.s ν (Whole.withDensityReal (ρ t))) ∧
    (Whole.MFEFiniteW d D.s ν (Whole.withDensityReal (ρ t)) →
      Whole.modulatedFreeEnergyW d D.s D.invβ ν (Whole.withDensityReal (ρ t)) =
        D.invβ / N * ((relEntropy ν (sb1Q D N ρ t)).toReal -
          Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t))))) := by
  obtain ⟨Cρ, M1, R⟩ := sb1_rho_of_regular hd (hdens t ht) (hreg t ht)
  have hβ' : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  obtain ⟨h1, h2⟩ := sb1_relEntropy_split' hd hs0 hsd R (by omega) hβ' (ν := ν)
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
theorem sb1_diss_of_parts' (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
      [IsProbabilityMeasure ν] => sb1_mfe_split' hd hN hs0 hsd hβ h.mf.density h.mf_reg hr ν
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

theorem sb1_superDiss_of_movEnt' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hE : SuperMovEnt d s) : SuperDiss d s := by
  intro D hDs hV3 hB hc N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  have hL := sb1_superLogK hd hs0 hsd D hDs hV3 hB hc N hN T Λ r hT P ρ X₀ W X h K hKi hK
  have hEn := hE D hDs hV3 hB hc N hN T Λ r hT P ρ X₀ W X h K hKi hK
  subst hDs
  exact sb1_diss_of_parts' hd hN h hs0 hsd hEn hL

/-- The frozen alternative (i) of S.B.1 (all `d ≥ 1`) from the whole-space `mov_ent_ineq` alone. -/
theorem sb1_super_of_movEnt' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s)
    (hE : SuperMovEnt d s) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : Whole.WholeDyn d), D.s = s → ContDiff ℝ 3 D.V →
      (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) →
      (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Whole.EucConfig d N),
        Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        Whole.MFEFiniteW d s (P.map (X (Real.toNNReal t))) (Whole.withDensityReal (ρ t)) ∧
        Whole.modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t)))
            (Whole.withDensityReal (ρ t)) + oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (Whole.modulatedFreeEnergyW d s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) :=
  sb1_super_of_diss hd hs0 hsd hsc (sb1_superDiss_of_movEnt' hd hs0 hsd hE)


theorem sb1_super_tie (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s) :
    type_of% (@HRS.Whole.mfe_confined_rd_gradient_super d hd s hs0 hsd hsc) :=
  sb1_super_of_movEnt' hd hs0 hsd hsc (sb1_superMovEnt hd hs0 hsd)

example := (@sb1_super_tie : type_of% @HRS.Whole.mfe_confined_rd_gradient_super)

end Split

end HRS.MS.MfeConf
