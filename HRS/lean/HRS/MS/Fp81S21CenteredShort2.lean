import HRS.MS.Fp81S21CenteredShort

/-!
# S2.1(iii): consumer-ready centered short-window comparison

For each fixed history length `L`, the recent-window estimate applies to the
length-`T` windows consumed by the expansion.  Its constants may depend on
that fixed `L`; this estimate is combined with the separate remote term
`e^{-cL}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- For each fixed history length `L`, the centered comparison for the
recent restrictions is the same bound for the length-`T` windows at `a₀`.
The constants retain the original order and therefore may depend on `L`. -/
theorem fp81s21_centered_recentWindow_short (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ, ∀ L : ℝ, (hL : 0 < L) →
        ∃ C₀ C : ℝ, 0 ≤ C ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ G : GaussianRealization R,
            ∀ a₀ : ℝ, (ha₀ : 0 ≤ a₀) →
              wassersteinE 1
                (law A.P (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ)
                  p.T a₀ A.P A.X))
                (law G.P (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ)
                  p.T a₀ G.Z)) ≤
                2 * ENNReal.ofReal (C * (Real.sqrt N * deltaN p.d p.s N +
                  Real.sqrt (localizationRate p.d p.s C₀ N) +
                  jN p.d p.s p.γ N)) := by
  obtain ⟨δ0, hδ0, hraw⟩ := fp81s21_centered_recentWindow p
  refine ⟨δ0, hδ0, ?_⟩
  intro δ hδ hδle R L hL
  obtain ⟨C₀, C, hC, hraw⟩ := hraw δ hδ hδle R L hL
  refine ⟨C₀, C, hC, ?_⟩
  intro N hN A G a₀ ha₀
  have hrawbound := hraw N hN A G a₀ ha₀
  have hparticle := fp81s21_particle_short_window_identity
    p R hN A L a₀ hL ha₀
  have hgaussian := fp81s21_gaussian_short_window_identity
    p R G L a₀ hL ha₀
  have hgeo := fp81s21_recent_geometry ha₀ hL p.hT
  have hparticleLaw :
      law A.P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
        hgeo.1 hgeo.2
        (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T)
          (max (a₀ - L) 0) A.P A.X ω)) =
      law A.P (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) p.T a₀ A.P A.X) := by
    simpa [HRS.law] using (Measure.map_congr hparticle)
  have hgaussianLaw :
      law G.P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
        hgeo.1 hgeo.2
        (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T)
          (max (a₀ - L) 0) G.Z ω)) =
      law G.P (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) p.T a₀ G.Z) := by
    simpa [HRS.law] using (Measure.map_congr hgaussian)
  rw [← hparticleLaw, ← hgaussianLaw]
  exact hrawbound

/-- The explicit centered-window rate tends to zero for every admissible
parameter record and every fixed pair of constants. -/
theorem fp81s21_centered_recentWindow_profile
    (p : Parameters) (C₀ C : ℝ) :
    Tendsto
      (fun N : ℕ => ENNReal.ofReal
        (C * (Real.sqrt N * deltaN p.d p.s N +
          Real.sqrt (localizationRate p.d p.s C₀ N) +
          jN p.d p.s p.γ N)))
      atTop (𝓝 0) := by
  have hs23 : p.s < 2 * (p.d : ℝ) / 3 := by
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    have hdpos : (0 : ℝ) < (p.d : ℝ) := by linarith
    nlinarith [p.hs]
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  have hdelta := HRS.Main.deltaN_errors_tendsto hd1 p.hs0 hs23
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hnegpow : ∀ y : ℝ, 0 < y →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-y)) atTop (𝓝 0) := fun y hy =>
    (tendsto_rpow_neg_atTop hy).comp hnat
  have hdpos : (0 : ℝ) < (p.d : ℝ) := by
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    linarith
  have hsdiv : p.s / (p.d : ℝ) < 1 := by
    rw [div_lt_one hdpos]
    linarith [p.hs]
  have hpower : Tendsto
      (fun N : ℕ => (N : ℝ) ^ (p.s / (p.d : ℝ) - 1)) atTop (𝓝 0) := by
    simpa only [show p.s / (p.d : ℝ) - 1 = -(1 - p.s / (p.d : ℝ)) by ring] using
      hnegpow (1 - p.s / (p.d : ℝ)) (by linarith)
  have hlogratio : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero |>.comp hnat
  have hlogterm : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (2 * (p.d : ℝ) * (N : ℝ)))
      atTop (𝓝 0) := by
    have hconst := hlogratio.const_mul (1 / (2 * (p.d : ℝ)))
    have heq : (fun N : ℕ => Real.log (N : ℝ) / (2 * (p.d : ℝ) * (N : ℝ))) =
        fun N : ℕ => (1 / (2 * (p.d : ℝ))) * (Real.log (N : ℝ) / (N : ℝ)) := by
      funext N
      by_cases hN : N = 0
      · simp [hN]
      · have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        have hdne : (2 * (p.d : ℝ)) ≠ 0 := by positivity
        field_simp [hNne, hdne]
    rw [heq]
    simpa using hconst
  have hoN : Tendsto (fun N : ℕ => oN p.d p.s C₀ N) atTop (𝓝 0) := by
    have hformula : (fun N : ℕ => oN p.d p.s C₀ N) =
        fun N : ℕ => C₀ * (N : ℝ) ^ (p.s / (p.d : ℝ) - 1) +
          (if p.s = 0 then
            Real.log (N : ℝ) / (2 * (p.d : ℝ) * (N : ℝ)) else 0) := by
      funext N
      exact HRS.Whole.oN_eq C₀
    rw [hformula]
    by_cases hs0 : p.s = 0
    · simp only [if_pos hs0]
      simpa using (hpower.const_mul C₀).add hlogterm
    · simp only [if_neg hs0, add_zero]
      simpa using hpower.const_mul C₀
  have hsqrtO : Tendsto (fun N : ℕ => Real.sqrt (oN p.d p.s C₀ N))
      atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hoN
    change Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘ (fun N : ℕ => oN p.d p.s C₀ N))
      atTop (𝓝 (Real.sqrt 0)) at h
    have h' : Tendsto
        ((fun x : ℝ => Real.sqrt x) ∘ (fun N : ℕ => oN p.d p.s C₀ N))
        atTop (𝓝 0) := by simpa using h
    change Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘ (fun N : ℕ => oN p.d p.s C₀ N))
      atTop (𝓝 0)
    exact h'
  have hNpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / (p.d : ℝ))))
      atTop (𝓝 0) := hnegpow (1 / (p.d : ℝ)) (by positivity)
  have hloc : Tendsto (fun N : ℕ => localizationRate p.d p.s C₀ N)
      atTop (𝓝 0) := by
    have hbase := hNpow.add hsqrtO
    rw [add_zero] at hbase
    have hq : 0 ≤ 4 / ((p.d : ℝ) + 4) := by positivity
    have h := ((Real.continuous_rpow_const hq).tendsto 0).comp hbase
    unfold localizationRate
    rwa [Real.zero_rpow (by positivity)] at h
  have hrootLoc : Tendsto
      (fun N : ℕ => Real.sqrt (localizationRate p.d p.s C₀ N))
      atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hloc
    change Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘
        (fun N : ℕ => localizationRate p.d p.s C₀ N)) atTop (𝓝 (Real.sqrt 0)) at h
    have h' : Tendsto
        ((fun x : ℝ => Real.sqrt x) ∘
          (fun N : ℕ => localizationRate p.d p.s C₀ N)) atTop (𝓝 0) := by
      simpa using h
    change Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘
        (fun N : ℕ => localizationRate p.d p.s C₀ N)) atTop (𝓝 0)
    exact h'
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hj : Tendsto (fun N : ℕ => jN p.d p.s p.γ N) atTop (𝓝 0) := by
    by_cases hγ0 : p.γ = 0
    · have hpow := hnegpow (1 / (4 * (p.d : ℝ) + 6)) (by positivity)
      have heq : (fun N : ℕ => jN p.d p.s p.γ N) =
          fun N : ℕ => (N : ℝ) ^ (-(1 / (4 * (p.d : ℝ) + 6))) := by
        funext N
        simp [HRS.Whole.jN, hγ0]
      rw [heq]
      exact hpow
    · have hδ := HRS.External.RefMarg.tendsto_deltaN p.hd p.hs0 hsd
      have hδpow := hδ.rpow_const
        (Or.inr (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 20))
      have hδpow' : Tendsto
          (fun N : ℕ => deltaN p.d p.s N ^ ((3 : ℝ) / 20)) atTop (𝓝 0) := by
        simpa using hδpow
      have heq : (fun N : ℕ => jN p.d p.s p.γ N) =
          fun N => deltaN p.d p.s N ^ ((3 : ℝ) / 20) := by
        funext N
        simp [HRS.Whole.jN, hγ0]
      rw [heq]
      exact hδpow'
  have hsum : Tendsto
      (fun N : ℕ => Real.sqrt N * deltaN p.d p.s N +
        Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)
      atTop (𝓝 0) := by
    simpa using hdelta.1.add hrootLoc |>.add hj
  have hscaled : Tendsto
      (fun N : ℕ => C * (Real.sqrt N * deltaN p.d p.s N +
        Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N))
      atTop (𝓝 0) := by
    simpa using hsum.const_mul C
  have hfinal := (ENNReal.continuous_ofReal.tendsto 0).comp hscaled
  change Tendsto
    ((fun x : ℝ => ENNReal.ofReal x) ∘
      (fun N : ℕ => C * (Real.sqrt N * deltaN p.d p.s N +
        Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)))
    atTop (𝓝 (ENNReal.ofReal 0)) at hfinal
  have hfinal' : Tendsto
      ((fun x : ℝ => ENNReal.ofReal x) ∘
        (fun N : ℕ => C * (Real.sqrt N * deltaN p.d p.s N +
          Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)))
      atTop (𝓝 0) := by simpa using hfinal
  change Tendsto
    ((fun x : ℝ => ENNReal.ofReal x) ∘
      (fun N : ℕ => C * (Real.sqrt N * deltaN p.d p.s N +
        Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)))
    atTop (𝓝 0)
  exact hfinal'

#print axioms fp81s21_centered_recentWindow_short
#print axioms fp81s21_centered_recentWindow_profile

end HRS.Fp81.S21

end
