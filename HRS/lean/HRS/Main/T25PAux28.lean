import HRS.Main.T25PAux27

/-!
# T25P, part 28: the `W₂` bound of Theorem 2.5
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Main HRS.T25

variable {d : ℕ}

theorem t25p_psi_pow {c : ℝ≥0∞} (hc : c ≠ ⊤) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Ψ : Ω → ℝ≥0∞) :
    (∫⁻ ω, (c * Ψ ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = c * (∫⁻ ω, Ψ ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  · rw [← ENNReal.rpow_mul]; norm_num
  · simp_rw [ENNReal.rpow_two]

theorem t25p_W2 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) (p₀ : ℝ)
    (hp₀ : 1 < p₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        MemLp (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
          (S.refMeasure N 0) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        S.initW m 2 P X₀ ν ≠ ⊤ →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) * (S.initW m 2 P X₀ ν).toReal +
              S.J N (law P X₀) p₀ / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) := by
  classical
  have hd : 2 ≤ d := S.hd
  have htr := t25_traj S
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hpkg⟩ := t25p_ev_pkg hd htr m
  obtain ⟨Cmax, hCmax0, hEv⟩ := hpkg T hT
  obtain ⟨CΨ, hCΨ0, hΨ⟩ := t25p_Psi_L2 hd htr hm hcr hT p₀ hp₀
  obtain ⟨Ct, hCt0, hTr⟩ := t25p_trace_int hd htr hm hcr hT
  set Kw : ℝ := 2 * (Cr ^ 2 + Real.sqrt Cmax) + Cr + 1 with hKw
  have hKw0 : 0 < Kw := by positivity
  refine ⟨1 + Cr * CΨ + Kw + Kw * Real.sqrt Ct, cr, by positivity, hcr, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel hmem ν Ω' _ P' _ Y₀ Y hY hfin
  have hW2 : wassersteinE 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≠ ⊤ := hfin
  set Wd := S.initW m 2 P X₀ ν with hWd
  have hWr : ENNReal.ofReal Wd.toReal = Wd := ENNReal.ofReal_toReal hfin
  set B := S.B N (law P X₀) with hB
  have hB0 : 0 ≤ B := t25p_B_nonneg S hN (law P X₀)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have hXs := t25_isParticleSystem S hSel
  have hX₀ae : AEMeasurable X₀ P := (hXs.sol.adapted 0).aemeasurable.congr hXs.sol.init
  have hent0 : relEntropy (law P X₀) (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) ≠ ⊤ :=
    hrel.ne
  -- absolute continuity and the `L^{p₀}` norm of the density
  have hac : law P X₀ ≪ modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0)) := by
    by_contra h
    exact hent0 (InformationTheory.klDiv_of_not_ac h)
  have hfinite : ∀ᵐ x ∂(S.refMeasure N 0), ((law P X₀).rnDeriv (S.refMeasure N 0)) x < ⊤ :=
    Measure.rnDeriv_lt_top _ _
  have hnormeq : eLpNorm ((law P X₀).rnDeriv (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))))
      (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) =
      eLpNorm (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
        (S.refMeasure N 0) := by
    refine eLpNorm_congr_enorm_ae (Measure.measurable_rnDeriv _ _).aestronglyMeasurable
      hmem.aestronglyMeasurable ?_
    filter_upwards [hfinite] with x hx
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
    exact enorm_eq_self _
  have hfin' : eLpNorm ((law P X₀).rnDeriv (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))))
      (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) < ⊤ := by
    rw [hnormeq]; exact hmem.eLpNorm_lt_top
  have hJeq : S.J N (law P X₀) p₀ = logMomentScale d S.s N p₀ (law P X₀)
      (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) := by
    unfold PreparedData.J logMomentScale
    have e := hnormeq
    simp only [PreparedData.refMeasure] at e ⊢
    rw [e]
  have hJ1 : 1 ≤ S.J N (law P X₀) p₀ := by
    rw [hJeq]
    exact t25p_J_ge_one hd htr hN P hXs hp₀ hac hfin'
  set J := S.J N (law P X₀) p₀ with hJ
  have key : ∀ δ : ℝ, 0 < δ →
      (wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
        ENNReal.ofReal (Kw * Real.exp (-cr * a)) * (Wd + ENNReal.ofReal δ) +
          (ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * J / Real.sqrt N) +
            ENNReal.ofReal Kw * ENNReal.ofReal (Real.sqrt Ct * (B / N) ^ ((1 : ℝ) / 4)))) := by
    intro δ hδ
    obtain ⟨π₀, hπ₀, hcost⟩ := t25p_exists_coupling 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν hfin
      (δ := ENNReal.ofReal δ) (by simpa using hδ)
    obtain ⟨Ω'', mΩ'', P'', hP'', π, hπ, hXp, ⟨ℱ'', W'', hF''⟩, hs, hw⟩ :=
      t25p_prep S hm hT hCr hcr hdual hEv ha hN P X₀ W X hSel hfilt P' Y₀ Y hY π₀ hπ₀
    have hc1' : (∫⁻ z, ‖z.1 - z.2‖ₑ ^ (2 : ℝ) ∂π₀) ^ (1 / (2 : ℝ)) ≤ Wd + ENNReal.ofReal δ := by
      have e : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ = ∫⁻ z, ‖z.1 - z.2‖ₑ ^ (2 : ℝ) ∂π₀ :=
        lintegral_congr fun z => t25p_ofReal_norm_rpow _ (by norm_num)
      rw [e] at hcost
      exact hcost
    have hlawX₀ : P''.map (fun ω => X₀ (π ω)) = law P X₀ := t25p_law_pullback hπ hX₀ae
    have hent : relEntropy (P''.map (fun ω => X₀ (π ω)))
        (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) ≠ ⊤ := by
      rw [hlawX₀]; exact hent0
    have hPsi := hΨ N hN a ha P'' (fun ω => X₀ (π ω)) (fun t ω => W t (π ω)) (fun t ω => X t (π ω)) hXp
      ⟨ℱ'', W'', hF''⟩ (by rw [hlawX₀]; exact hac) (by rw [hlawX₀]; exact hfin')
    rw [hlawX₀, ← hJeq] at hPsi
    have hBe : entropyScale d S.s N (law P X₀)
        (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) = B := rfl
    obtain ⟨Mart, Z, hM, -⟩ := t25p_stage1 hd htr hm hT hCr hcr hdual hEv hN ha P'' _ _ _ hXp ℱ'' W'' hF''
    have hTr' := hTr N hN a ha P'' _ _ _ hXp ⟨ℱ'', W'', hF''⟩ hent ℱ'' Mart hM
    rw [hlawX₀, hBe] at hTr'
    have hPsi' : (∫⁻ ω, (ENNReal.ofReal Cr * t25p_Psi d S.s S.ρ m cr a T (fun t ω => X t (π ω)) ω) ^ (2 : ℝ)
          ∂P'') ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * J / Real.sqrt N) := by
      rw [t25p_psi_pow ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl hPsi
    refine (hw 2 (Or.inr rfl)).trans ?_
    have h3 : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
          (covForm m S.β⁻¹ (empirical (X r.toNNReal (π ω))) - covDensT m S.β⁻¹ (a + T) S.ρ r))) ∂P'') ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Ct * (B / N) ^ ((1 : ℝ) / 4)) := by
      refine (ENNReal.rpow_le_rpow hTr' (by norm_num)).trans ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), one_div,
        ← one_div, t25p_rpow_aux hCt0 (by positivity)]
    rw [add_assoc]
    exact add_le_add (mul_le_mul' le_rfl hc1') (add_le_add hPsi' (mul_le_mul' le_rfl h3))
  have hexp0 : 0 < Real.exp (-cr * a) := Real.exp_pos _
  have hW' := t25p_lim (c0 := Kw * Real.exp (-cr * a)) (by positivity) key
  set Wr := Wd.toReal with hWrdef
  have hWr0 : 0 ≤ Wr := ENNReal.toReal_nonneg
  rw [← hWr] at hW'
  have hf0 : 0 ≤ J / Real.sqrt N := by positivity
  have hh0 : 0 ≤ (B / N) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hx0 : 0 ≤ Real.exp (-cr * a) * Wr := by positivity
  have hs0 : 0 ≤ Real.sqrt Ct := Real.sqrt_nonneg _
  set Cc : ℝ := 1 + Cr * CΨ + Kw + Kw * Real.sqrt Ct with hCc
  have hCc2 : Cr * CΨ ≤ Cc := by
    have : 0 ≤ Kw * Real.sqrt Ct := by positivity
    linarith
  have hCc4 : Kw ≤ Cc := by
    have : 0 ≤ Cr * CΨ := by positivity
    have : 0 ≤ Kw * Real.sqrt Ct := by positivity
    linarith
  have hCc5 : Kw * Real.sqrt Ct ≤ Cc := by
    have : 0 ≤ Cr * CΨ := by positivity
    linarith
  rw [t25p_comb (by positivity) hWr0 hCr.le (by positivity) hKw0.le (by positivity)] at hW'
  refine hW'.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcg : CΨ * J / Real.sqrt N = CΨ * (J / Real.sqrt N) := mul_div_assoc _ _ _
  rw [hcg]
  have k1 : Kw * Real.exp (-cr * a) * Wr ≤ Cc * (Real.exp (-cr * a) * Wr) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hCc4 hx0
  have k2 : Cr * (CΨ * (J / Real.sqrt N)) ≤ Cc * (J / Real.sqrt N) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCc2 hf0
  have k3 : Kw * (Real.sqrt Ct * (B / N) ^ ((1 : ℝ) / 4)) ≤ Cc * (B / N) ^ ((1 : ℝ) / 4) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCc5 hh0
  calc _ ≤ Cc * (Real.exp (-cr * a) * Wr) + (Cc * (J / Real.sqrt N) + Cc * (B / N) ^ ((1 : ℝ) / 4)) :=
        add_le_add k1 (add_le_add k2 k3)
    _ = _ := by ring

end HRS.T25P
