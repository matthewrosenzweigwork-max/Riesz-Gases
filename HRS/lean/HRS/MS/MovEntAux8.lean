import HRS.MS.MovEntAux7

/-!
# S6.6, packet P6 (part 3): the Grönwall core of clause (1)

`s66_clause1_core`: along the class, `MfeDiss` for the quadratic gradient dynamics, the split identity `H(f|Q) = βN𝖤_N + log K`,
the pressure bound `|log K| ≤ C N δ_N` and `s66_comm_bound` give `H(f_t|Q_t) ≤ C₅ (H(f_0|Q_0) + Nδ_N)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

/-- `β N 𝖤_N(f, μ) = H(f|μ^{⊗N}) + β N ∫F` for `invβ = β⁻¹` (real parts). -/
theorem s66_mfe_eq {s : ℝ} {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) (f : Measure (EucConfig d N))
    (μ : Measure (Euc d)) :
    β * N * modulatedFreeEnergyW d s β⁻¹ f μ =
      (relEntropy f (Measure.pi fun _ : Fin N => μ)).toReal + β * N * ∫ X, rieszModulatedEnergy d s X μ ∂f := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold modulatedFreeEnergyW
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast]
  field_simp

set_option maxHeartbeats 1600000 in
theorem s66_clause1_core (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L β Kbar : ℝ) (hβ : 0 < β) (hKbar0 : 0 ≤ Kbar) :
    ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∀ (q : ℝ) (N : ℕ), 2 ≤ N → ∀ T : ℝ, 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N) (K : ℝ → ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) T, Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
        (s = 0 → HasLogMoment (wd (ρ r)) L)) →
      (∀ t, Measurable (X t)) → AEMeasurable X₀ P →
      IntegrableOn K (Set.Icc 0 T) → (∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ K r) →
      (∫ r in Set.Icc 0 T, K r) ≤ Kbar →
      (∀ r ∈ Set.Icc (0 : ℝ) T, HasLipBoundW (mfeTransportW (quadraticGradientDyn d s q β) (ρ r)) (K r)) →
      HRS.MS.MfeConf.MfeDiss d (quadraticGradientDyn d s q β) N T ρ P X₀ X →
      relEntropy (P.map X₀) (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ 0))) ≠ ⊤ →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        relEntropy (P.map (X t.toNNReal)) (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ t))) ≤
          ENNReal.ofReal C₅ * (relEntropy (P.map X₀)
            (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ 0))) + ENNReal.ofReal (N * deltaN d s N)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cp, hCp⟩ := s66_gibbs_data hd hs0 hsd M L (β / 2) (2 * β) (by positivity) (by linarith)
  obtain ⟨C₆, hC₆0, hC₆⟩ := s66_comm_bound hd hs0 hsd M L β hβ
  set Cp' : ℝ := max Cp 0 with hCp'
  have hCp'0 : 0 ≤ Cp' := le_max_right _ _
  set C₅ : ℝ := (2 * Cp' + 1) * Real.exp (β * C₆ * Kbar) with hC₅
  refine ⟨C₅, ?_, ?_⟩
  · have h1 : 1 ≤ 2 * Cp' + 1 := by linarith
    have h2 : 1 ≤ Real.exp (β * C₆ * Kbar) := Real.one_le_exp (by positivity)
    nlinarith
  intro q N hN T hT Ω _ P _ ρ X₀ X K hρ hXm hX₀ hKi hK0 hKbar hLip hDiss hH0 t ht
  set D : WholeDyn d := quadraticGradientDyn d s q β with hD
  have hDs : D.s = s := rfl
  have hDinv : D.invβ = β⁻¹ := rfl
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hδ0, hδ1, -, -⟩ := s66_delta_facts hd1 hs0 hsd (C₀ := 1) le_rfl hN
  set δ : ℝ := deltaN d s N with hδ
  have hNδ : 0 < (N : ℝ) * δ := mul_pos hN0 hδ0
  haveI : ∀ r : ℝ, IsProbabilityMeasure (P.map (X r.toNNReal)) := fun r =>
    inferInstance
  haveI hP0 : IsProbabilityMeasure (P.map X₀) := inferInstance
  have hmem : β ∈ Set.Icc (β / 2) (2 * β) := ⟨by linarith, by linarith⟩
  have hρp : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (wd (ρ r)) := fun r hr =>
    HRS.MS.Thm.cb_withDensityReal_isProb (hρ r hr).1
  -- notation for the time `r` quantities
  set Q : ℝ → Measure (EucConfig d N) := fun r => Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ r)) with hQ
  set Hs : ℝ → ℝ := fun r => (relEntropy (P.map (X r.toNNReal)) (Q r)).toReal with hHs
  set lK : ℝ → ℝ := fun r => Real.log (Whole.gibbsNormalizer (rieszKernel d s) N β (wd (ρ r))) with hlK
  have hlK_bd : ∀ r ∈ Set.Icc (0 : ℝ) T, |lK r| ≤ Cp' * (N * δ) := by
    intro r hr
    have := (hCp (ρ r) (hρ r hr).1 (hρ r hr).2.1 (hρ r hr).2.2 N hN β hmem).2
    have h2 : Cp * N * δ ≤ Cp' * (N * δ) := by
      have := mul_le_mul_of_nonneg_right (le_max_left Cp 0) hNδ.le
      linarith
    exact (le_trans this h2 : _)
  -- finiteness and split at each time
  have hfin : ∀ r ∈ Set.Icc (0 : ℝ) T, MFEFiniteW d s (P.map (X r.toNNReal)) (wd (ρ r)) :=
    fun r hr => (hDiss r hr).1
  have hsplit : ∀ r ∈ Set.Icc (0 : ℝ) T,
      relEntropy (P.map (X r.toNNReal)) (Q r) ≠ ⊤ ∧
      Hs r = (relEntropy (P.map (X r.toNNReal)) (Measure.pi fun _ : Fin N => wd (ρ r))).toReal +
        β * N * ∫ Z, rieszModulatedEnergy d s Z (wd (ρ r)) ∂(P.map (X r.toNNReal)) + lK r := by
    intro r hr
    obtain ⟨h1, h2⟩ := s66_split hd hs0 hsd M L β hβ (hρ r hr).1 (hρ r hr).2.1 (hρ r hr).2.2 hN
      (P.map (X r.toNNReal))
    exact ⟨h1.2 (hfin r hr), h2 (hfin r hr)⟩
  -- the same at time 0 for the initial law `P.map X₀`
  have h0 : MFEFiniteW d s (P.map X₀) (wd (ρ 0)) ∧
      (relEntropy (P.map X₀) (Q 0)).toReal =
        (relEntropy (P.map X₀) (Measure.pi fun _ : Fin N => wd (ρ 0))).toReal +
          β * N * ∫ Z, rieszModulatedEnergy d s Z (wd (ρ 0)) ∂(P.map X₀) + lK 0 := by
    have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    obtain ⟨h1, h2⟩ := s66_split hd hs0 hsd M L β hβ (hρ 0 h00).1 (hρ 0 h00).2.1 (hρ 0 h00).2.2 hN
      (P.map X₀)
    exact ⟨h1.1 hH0, h2 (h1.1 hH0)⟩
  -- the commutator integral and its bound
  set cc : ℝ → ℝ := fun r => ∫ Z, commN d s (mfeTransportW D (ρ r)) Z (wd (ρ r)) ∂(P.map (X r.toNNReal)) with hcc
  set Hn : ℝ := (relEntropy (P.map X₀) (Q 0)).toReal with hHn
  have hccb : ∀ r ∈ Set.Icc (0 : ℝ) T, |cc r| ≤ 2 * K r * C₆ * (Hs r + N * δ) / N := by
    intro r hr
    have hlt : relEntropy (P.map (X r.toNNReal)) (Q r) < ⊤ := lt_top_iff_ne_top.2 (hsplit r hr).1
    exact (hC₆ (ρ r) (hρ r hr).1 (hρ r hr).2.1 (hρ r hr).2.2 N hN (P.map (X r.toNNReal)) inferInstance hlt
      (mfeTransportW D (ρ r)) (K r) (hLip r hr)).2
  -- Grönwall
  set u : ℝ → ℝ := fun r => Hs r + N * δ with hu
  set a : ℝ → ℝ := fun r => β * C₆ * K r with ha
  set G : ℝ → ℝ := fun r => -(β * N / 2) * cc r with hG
  set u0 : ℝ := Hn + (2 * Cp' + 1) * (N * δ) with hu0
  have hDT := hDiss T ⟨hT, le_rfl⟩
  have hGi : IntegrableOn G (Set.Icc 0 T) := hDT.2.2.1.const_mul _
  have hHn0 : 0 ≤ Hn := ENNReal.toReal_nonneg
  have hineq : ∀ r ∈ Set.Icc (0 : ℝ) T, u r ≤ u0 + ∫ r' in Set.Icc 0 r, G r' := by
    intro r hr
    have hDr := hDiss r hr
    have hmf := hDr.2.2.2
    have e1 := s66_mfe_eq (s := s) (by omega : 1 ≤ N) hβ (P.map (X r.toNNReal)) (wd (ρ r))
    have e0 := s66_mfe_eq (s := s) (by omega : 1 ≤ N) hβ (P.map X₀) (wd (ρ 0))
    have hmf' : modulatedFreeEnergyW d s β⁻¹ (P.map (X r.toNNReal)) (wd (ρ r)) ≤
        modulatedFreeEnergyW d s β⁻¹ (P.map X₀) (wd (ρ 0)) -
          (1 / 2) * ∫ r' in Set.Icc 0 r, cc r' := hmf
    have hmul := mul_le_mul_of_nonneg_left hmf' (by positivity : 0 ≤ β * N)
    have hGint : ∫ r' in Set.Icc 0 r, G r' = -(β * N / 2) * ∫ r' in Set.Icc 0 r, cc r' := by
      simp only [hG]; rw [integral_const_mul]
    have s1 := (hsplit r hr).2
    have s0 := h0.2
    have hl1 := hlK_bd r hr
    have hl0 := hlK_bd 0 ⟨le_rfl, hT⟩
    have hl1' := (abs_le.1 hl1).2
    have hl0' := (abs_le.1 hl0).1
    simp only [hu, hu0, hHs] at *
    rw [hGint]
    nlinarith
  have hGu : ∀ r ∈ Set.Icc (0 : ℝ) T, G r ≤ a r * u r := by
    intro r hr
    have hb := hccb r hr
    have hlt : relEntropy (P.map (X r.toNNReal)) (Q r) < ⊤ := lt_top_iff_ne_top.2 (hsplit r hr).1
    have hKr := hK0 r hr
    have hHs0 : 0 ≤ Hs r := ENNReal.toReal_nonneg
    have h1 : -(β * N / 2) * cc r ≤ (β * N / 2) * |cc r| := by
      have := neg_abs_le (cc r)
      have h2 : 0 ≤ β * N / 2 := by positivity
      nlinarith [neg_le_abs (cc r), le_abs_self (cc r)]
    have h2 : (β * N / 2) * |cc r| ≤ (β * N / 2) * (2 * K r * C₆ * (Hs r + N * δ) / N) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h3 : (β * N / 2) * (2 * K r * C₆ * (Hs r + N * δ) / N) = β * C₆ * K r * (Hs r + N * δ) := by
      field_simp
    simp only [hG, ha, hu]
    linarith
  have hai : IntegrableOn a (Set.Icc 0 T) := hKi.const_mul _
  have ha0 : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ a r := fun r hr => by
    have := hK0 r hr
    simp only [ha]; positivity
  have hgr := movspec_gronwall_var ha0 hai hGi hineq hGu t ht
  have hint_a : ∫ r in Set.Icc 0 t, a r ≤ β * C₆ * Kbar := by
    have h1 : ∫ r in Set.Icc 0 t, a r = β * C₆ * ∫ r in Set.Icc 0 t, K r := by
      simp only [ha]; rw [integral_const_mul]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ hKbar
    exact setIntegral_mono_set hKi (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => hK0 r hr)
      (Set.Icc_subset_Icc le_rfl ht.2).eventuallyLE
  -- conclude
  have hexp : Real.exp (∫ r in Set.Icc 0 t, a r) ≤ Real.exp (β * C₆ * Kbar) := Real.exp_le_exp.2 hint_a
  have hu0pos : 0 ≤ u0 := by simp only [hu0]; positivity
  have hHs0 : 0 ≤ Hs t := ENNReal.toReal_nonneg
  have hHsu : Hs t ≤ u t := by simp only [hu]; nlinarith
  have hfinal : Hs t ≤ C₅ * (Hn + N * δ) := by
    have h1 : u t ≤ u0 * Real.exp (β * C₆ * Kbar) :=
      hgr.trans (mul_le_mul_of_nonneg_left hexp hu0pos)
    have h2 : u0 ≤ (2 * Cp' + 1) * (Hn + N * δ) := by
      simp only [hu0]; nlinarith
    calc Hs t ≤ u t := hHsu
      _ ≤ u0 * Real.exp (β * C₆ * Kbar) := h1
      _ ≤ ((2 * Cp' + 1) * (Hn + N * δ)) * Real.exp (β * C₆ * Kbar) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = C₅ * (Hn + N * δ) := by simp only [hC₅]; ring
  have hfin_t : relEntropy (P.map (X t.toNNReal)) (Q t) = ENNReal.ofReal (Hs t) :=
    (ENNReal.ofReal_toReal (hsplit t ht).1).symm
  have hfin_0 : relEntropy (P.map X₀) (Q 0) = ENNReal.ofReal Hn :=
    (ENNReal.ofReal_toReal hH0).symm
  show relEntropy (P.map (X t.toNNReal)) (Q t) ≤ ENNReal.ofReal C₅ * (relEntropy (P.map X₀) (Q 0) +
    ENNReal.ofReal (N * deltaN d s N))
  rw [hfin_t, hfin_0, ← ENNReal.ofReal_add hHn0 hNδ.le,
    ← ENNReal.ofReal_mul (by simp only [hC₅]; positivity)]
  exact ENNReal.ofReal_le_ofReal hfinal

end HRS.MS.MovEnt

end
