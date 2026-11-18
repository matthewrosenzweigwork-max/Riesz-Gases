import HRS.Main.T25PAux26

/-!
# T25P, part 27: clause 1 of Theorem 2.5 (smooth and `W₁` bounds)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Main HRS.T25

variable {d : ℕ}

theorem t25p_B_nonneg (S : PreparedData d) {N : ℕ} (hN : 2 ≤ N) (f0 : Measure (Config d N)) :
    0 ≤ S.B N f0 := by
  have h := one_le_mul_deltaN (d := d) S.hs0 N (by omega)
  unfold PreparedData.B
  have := ENNReal.toReal_nonneg (a := relEntropy f0 (S.refMeasure N 0))
  linarith

theorem t25p_comb {p1 q1 p2 q2 p3 q3 : ℝ} (h1 : 0 ≤ p1) (g1 : 0 ≤ q1) (h2 : 0 ≤ p2) (g2 : 0 ≤ q2)
    (h3 : 0 ≤ p3) (g3 : 0 ≤ q3) :
    ENNReal.ofReal p1 * ENNReal.ofReal q1 +
      (ENNReal.ofReal p2 * ENNReal.ofReal q2 + ENNReal.ofReal p3 * ENNReal.ofReal q3) =
    ENNReal.ofReal (p1 * q1 + (p2 * q2 + p3 * q3)) := by
  rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3,
    ← ENNReal.ofReal_add (mul_nonneg h2 g2) (mul_nonneg h3 g3),
    ← ENNReal.ofReal_add (mul_nonneg h1 g1) (add_nonneg (mul_nonneg h2 g2) (mul_nonneg h3 g3))]

theorem t25p_rpow_aux {Ct x : ℝ} (hCt : 0 ≤ Ct) (hx : 0 ≤ x) :
    (Ct * Real.sqrt x) ^ ((1 : ℝ) / 2) = Real.sqrt Ct * x ^ ((1 : ℝ) / 4) := by
  rw [Real.mul_rpow hCt (Real.sqrt_nonneg _), Real.sqrt_eq_rpow Ct, Real.sqrt_eq_rpow x,
    ← Real.rpow_mul hx]
  norm_num

theorem t25p_clause1 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (S.initW m 1 P X₀ ν ≠ ⊤ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.exp (-c * a) * (S.initW m 1 P X₀ ν).toReal +
              S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N)) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) * (S.initW m 1 P X₀ ν).toReal +
              S.B N (law P X₀) / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4)))) := by
  classical
  have hd : 2 ≤ d := S.hd
  have htr := t25_traj S
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hpkg⟩ := t25p_ev_pkg hd htr m
  obtain ⟨Cmax, hCmax0, hEv⟩ := hpkg T hT
  obtain ⟨CΨ, hCΨ0, hΨ⟩ := t25p_Psi_L1 hd htr hm hcr hT
  obtain ⟨Ct, hCt0, hTr⟩ := t25p_trace_int hd htr hm hcr hT
  set Kw : ℝ := 2 * (Cr ^ 2 + Real.sqrt Cmax) + Cr + 1 with hKw
  have hKw0 : 0 < Kw := by positivity
  refine ⟨1 + Cr + Cr * CΨ + Cr ^ 2 / 2 * Ct + Kw + Kw * Real.sqrt Ct, cr, by positivity, hcr, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel ν Ω' _ P' _ Y₀ Y hY hfin
  have hW1 : wassersteinE 1 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≠ ⊤ := hfin
  set Wd := S.initW m 1 P X₀ ν with hWd
  have hWr : ENNReal.ofReal Wd.toReal = Wd := ENNReal.ofReal_toReal hfin
  set B := S.B N (law P X₀) with hB
  have hB0 : 0 ≤ B := t25p_B_nonneg S hN (law P X₀)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have hXs := t25_isParticleSystem S hSel
  have hX₀ae : AEMeasurable X₀ P := (hXs.sol.adapted 0).aemeasurable.congr hXs.sol.init
  have hent0 : relEntropy (law P X₀) (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) ≠ ⊤ :=
    hrel.ne
  -- the bounds for each coupling
  have key : ∀ δ : ℝ, 0 < δ →
      (ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y))) ≤
        ENNReal.ofReal (Cr * Real.exp (-cr * a)) * (Wd + ENNReal.ofReal δ) +
          (ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * B / Real.sqrt N) +
            ENNReal.ofReal (Cr ^ 2 / 2) * ENNReal.ofReal (Ct * Real.sqrt (B / N)))) ∧
      (wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
        ENNReal.ofReal (Kw * Real.exp (-cr * a)) * (Wd + ENNReal.ofReal δ) +
          (ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * B / Real.sqrt N) +
            ENNReal.ofReal Kw * ENNReal.ofReal (Real.sqrt Ct * (B / N) ^ ((1 : ℝ) / 4)))) := by
    intro δ hδ
    obtain ⟨π₀, hπ₀, hcost⟩ := t25p_exists_coupling 1 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν hfin
      (δ := ENNReal.ofReal δ) (by simpa using hδ)
    obtain ⟨Ω'', mΩ'', P'', hP'', π, hπ, hXp, ⟨ℱ'', W'', hF''⟩, hs, hw⟩ :=
      t25p_prep S hm hT hCr hcr hdual hEv ha hN P X₀ W X hSel hfilt P' Y₀ Y hY π₀ hπ₀
    have hc1 : ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π₀ ≤ Wd + ENNReal.ofReal δ := by
      have e : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π₀ = ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π₀ :=
        lintegral_congr fun z => by rw [Real.rpow_one, ofReal_norm]
      rw [e, div_one, ENNReal.rpow_one] at hcost
      exact hcost
    have hc1' : (∫⁻ z, ‖z.1 - z.2‖ₑ ^ (1 : ℝ) ∂π₀) ^ (1 / (1 : ℝ)) ≤ Wd + ENNReal.ofReal δ := by
      simpa using hc1
    have hlawX₀ : P''.map (fun ω => X₀ (π ω)) = law P X₀ := t25p_law_pullback hπ hX₀ae
    have hent : relEntropy (P''.map (fun ω => X₀ (π ω)))
        (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) ≠ ⊤ := by
      rw [hlawX₀]; exact hent0
    have hPsi := hΨ N hN a ha P'' (fun ω => X₀ (π ω)) (fun t ω => W t (π ω)) (fun t ω => X t (π ω)) hXp
      ⟨ℱ'', W'', hF''⟩ hent
    rw [hlawX₀] at hPsi
    have hBe : entropyScale d S.s N (law P X₀)
        (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) = B := rfl
    rw [hBe] at hPsi
    obtain ⟨Mart, Z, hM, -⟩ := t25p_stage1 hd htr hm hT hCr hcr hdual hEv hN ha P'' _ _ _ hXp ℱ'' W'' hF''
    have hTr' := hTr N hN a ha P'' _ _ _ hXp ⟨ℱ'', W'', hF''⟩ hent ℱ'' Mart hM
    rw [hlawX₀, hBe] at hTr'
    have hPsi' : ∫⁻ ω, ENNReal.ofReal Cr * t25p_Psi d S.s S.ρ m cr a T (fun t ω => X t (π ω)) ω ∂P'' ≤
        ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * B / Real.sqrt N) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl hPsi
    obtain ⟨hs1, hs2⟩ : _ ∧ _ := ⟨hs, hw 1 (Or.inl rfl)⟩
    constructor
    · refine hs1.trans ?_
      rw [add_assoc]
      exact add_le_add (mul_le_mul' le_rfl hc1) (add_le_add hPsi' (mul_le_mul' le_rfl hTr'))
    · refine hs2.trans ?_
      have h2 : (∫⁻ ω, (ENNReal.ofReal Cr * t25p_Psi d S.s S.ρ m cr a T (fun t ω => X t (π ω)) ω) ^ (1 : ℝ)
          ∂P'') ^ (1 / (1 : ℝ)) ≤ ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * B / Real.sqrt N) := by
        simpa using hPsi'
      have h3 : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
          ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
            (covForm m S.β⁻¹ (empirical (X r.toNNReal (π ω))) - covDensT m S.β⁻¹ (a + T) S.ρ r))) ∂P'') ^
            (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Ct * (B / N) ^ ((1 : ℝ) / 4)) := by
        refine (ENNReal.rpow_le_rpow hTr' (by norm_num)).trans ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), one_div,
          ← one_div, t25p_rpow_aux hCt0 (by positivity)]
      rw [add_assoc]
      exact add_le_add (mul_le_mul' le_rfl hc1') (add_le_add h2 (mul_le_mul' le_rfl h3))
  obtain ⟨hS, hW⟩ : (∀ δ : ℝ, 0 < δ → _) ∧ (∀ δ : ℝ, 0 < δ → _) :=
    ⟨fun δ hδ => (key δ hδ).1, fun δ hδ => (key δ hδ).2⟩
  have hexp0 : 0 < Real.exp (-cr * a) := Real.exp_pos _
  have hS' := t25p_lim (c0 := Cr * Real.exp (-cr * a)) (by positivity) hS
  have hW' := t25p_lim (c0 := Kw * Real.exp (-cr * a)) (by positivity) hW
  set Wr := Wd.toReal with hWrdef
  have hWr0 : 0 ≤ Wr := ENNReal.toReal_nonneg
  rw [← hWr] at hS' hW'
  have hf0 : 0 ≤ B / Real.sqrt N := by positivity
  have hg0 : 0 ≤ Real.sqrt (B / N) := Real.sqrt_nonneg _
  have hh0 : 0 ≤ (B / N) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hx0 : 0 ≤ Real.exp (-cr * a) * Wr := by positivity
  have hs0 : 0 ≤ Real.sqrt Ct := Real.sqrt_nonneg _
  set Cc : ℝ := 1 + Cr + Cr * CΨ + Cr ^ 2 / 2 * Ct + Kw + Kw * Real.sqrt Ct with hCc
  have hCc1 : Cr ≤ Cc := by
    have : 0 ≤ Cr * CΨ := by positivity
    have : 0 ≤ Cr ^ 2 / 2 * Ct := by positivity
    have : 0 ≤ Kw * Real.sqrt Ct := by positivity
    linarith
  have hCc2 : Cr * CΨ ≤ Cc := by
    have : 0 ≤ Cr ^ 2 / 2 * Ct := by positivity
    have : 0 ≤ Kw * Real.sqrt Ct := by positivity
    linarith
  have hCc3 : Cr ^ 2 / 2 * Ct ≤ Cc := by
    have : 0 ≤ Cr * CΨ := by positivity
    have : 0 ≤ Kw * Real.sqrt Ct := by positivity
    linarith
  have hCc4 : Kw ≤ Cc := by
    have : 0 ≤ Cr * CΨ := by positivity
    have : 0 ≤ Cr ^ 2 / 2 * Ct := by positivity
    have : 0 ≤ Kw * Real.sqrt Ct := by positivity
    linarith
  have hCc5 : Kw * Real.sqrt Ct ≤ Cc := by
    have : 0 ≤ Cr * CΨ := by positivity
    have : 0 ≤ Cr ^ 2 / 2 * Ct := by positivity
    linarith
  constructor
  · rw [t25p_comb (by positivity) hWr0 hCr.le (by positivity) (by positivity) (by positivity)] at hS'
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hS'
    refine this.trans ?_
    have hcg : CΨ * B / Real.sqrt N = CΨ * (B / Real.sqrt N) := mul_div_assoc _ _ _
    rw [hcg]
    have k1 : Cr * Real.exp (-cr * a) * Wr ≤ Cc * (Real.exp (-cr * a) * Wr) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hCc1 hx0
    have k2 : Cr * (CΨ * (B / Real.sqrt N)) ≤ Cc * (B / Real.sqrt N) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCc2 hf0
    have k3 : Cr ^ 2 / 2 * (Ct * Real.sqrt (B / N)) ≤ Cc * Real.sqrt (B / N) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCc3 hg0
    calc _ ≤ Cc * (Real.exp (-cr * a) * Wr) + (Cc * (B / Real.sqrt N) + Cc * Real.sqrt (B / N)) :=
          add_le_add k1 (add_le_add k2 k3)
      _ = _ := by ring
  · rw [t25p_comb (by positivity) hWr0 hCr.le (by positivity) hKw0.le (by positivity)] at hW'
    refine hW'.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcg : CΨ * B / Real.sqrt N = CΨ * (B / Real.sqrt N) := mul_div_assoc _ _ _
    rw [hcg]
    have k1 : Kw * Real.exp (-cr * a) * Wr ≤ Cc * (Real.exp (-cr * a) * Wr) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hCc4 hx0
    have k2 : Cr * (CΨ * (B / Real.sqrt N)) ≤ Cc * (B / Real.sqrt N) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCc2 hf0
    have k3 : Kw * (Real.sqrt Ct * (B / N) ^ ((1 : ℝ) / 4)) ≤ Cc * (B / N) ^ ((1 : ℝ) / 4) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCc5 hh0
    calc _ ≤ Cc * (Real.exp (-cr * a) * Wr) + (Cc * (B / Real.sqrt N) + Cc * (B / N) ^ ((1 : ℝ) / 4)) :=
          add_le_add k1 (add_le_add k2 k3)
      _ = _ := by ring

end HRS.T25P
