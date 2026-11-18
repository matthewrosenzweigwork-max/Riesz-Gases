import HRS.MS.R2WinOrbAux6

/-!
# S10.3 (stationary half), part 7: the five orbit claims for the stationary coefficient

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_data`: uniform constant `K` in the data bounds for `g_a = L^a φ_α`, `a ≤ 2`.
`s103_orbit_claims`: the orbit part of `r2_window_orbits` (terminal data `φ`, `Lφ`, `L²φ + ∂_tL φ`) for the stationary coefficient and
the thermal density `ρ_β`, constants independent of `α` and `t`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.MovAdj HRS.MS.Ul HRS.MS.MovOsc

variable {d : ℕ}

theorem s103_b_nonneg (α : MultiIndex d) : 0 ≤ s103_b d α :=
  Real.rpow_nonneg (oscEigenvalue_pos α).le _

theorem s103_data {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : ℕ), a ≤ 2 → ∀ α : MultiIndex d,
        ContDiff ℝ ∞ ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) ∧
        cbNormVecE (4 * d + 42) (fun x => gradient
          ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
            (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) x) ≤ ENNReal.ofReal (K * s103_b d α) ∧
        (∀ x, |((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a]
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) x| ≤ K * s103_b d α) ∧
        MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ ((fun g x => generatorW
          ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))) ∧
        oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ ((fun g x => generatorW
          ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))) ≤
          K * s103_b d α := by
  obtain ⟨Kd, hKd0, hKd⟩ := s103_data_of_chain hd hs0 hsd hq hβ hρ
  obtain ⟨B0, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨hρsm, cρ, hcρ, hkρ⟩ := HRS.MS.Mov0.mv0_hgauss_gapref hq' hR
  obtain ⟨ψρ, hψρ⟩ := HRS.MS.MovC1.movc1_G_schwartz (⟨hρsm, cρ, hcρ, hkρ⟩ : HRS.MS.MovC1.MovcG ρβ)
  have hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => (fun _ : Euc d => (0 : Euc d)) x i :=
    fun i => ⟨0, by ext x; simp⟩
  have hch : ∀ a : ℕ, ∃ Ka : ℝ, 0 ≤ Ka ∧ ∀ f : SchwartzMap (Euc d) ℝ, ul6S (-(s + 1)) (8 * d + 80)
      (Ka * oscNorm (s103_nstar d s (8 * d + 80 + 2 * a) : ℝ) f)
      ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[a] ⇑f) := by
    intro a
    have h := s103_chain hd hs0 hsd β⁻¹ ((q : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ⟨ψρ, hψρ⟩ hσ
      (c := fun x => (fun _ : Euc d => (0 : Euc d)) x - convGradConvW (rieszKernelGrad d s) ρβ x) rfl a
      (8 * d + 80)
    rw [← s103_coeff_eq s q β ρβ] at h
    exact h
  choose Kc hKc0 hKc using hch
  refine ⟨Kd * (Kc 0 + Kc 1 + Kc 2), by have := hKc0 0; have := hKc0 1; have := hKc0 2; positivity, ?_⟩
  intro a ha α
  have hle : Kc a ≤ Kc 0 + Kc 1 + Kc 2 := by
    interval_cases a <;> linarith [hKc0 0, hKc0 1, hKc0 2]
  have hb0 := s103_b_nonneg α
  obtain ⟨h1, h2, h3, h4, h5⟩ := hKd a ha (Kc a) (hKc0 a) (hKc a) α
  have hmono : Kd * Kc a * s103_b d α ≤ Kd * (Kc 0 + Kc 1 + Kc 2) * s103_b d α :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hKd0) hb0
  exact ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal hmono), fun x => (h3 x).trans hmono, h4, h5.trans hmono⟩

theorem s103_orbitSup_mono {C : WholeCoeff d} {k : ℕ} {t : ℝ} {g : Euc d → ℝ} {A A' : ℝ}
    (h : R2OrbitSup C k t g A) (hA : A ≤ A') : R2OrbitSup C k t g A' :=
  fun f hf r hr => ⟨(h f hf r hr).1, (h f hf r hr).2.trans (ENNReal.ofReal_le_ofReal hA)⟩

theorem s103_orbitGrad_mono {C : WholeCoeff d} {k : ℕ} {t : ℝ} {g : Euc d → ℝ} {A A' c : ℝ}
    (h : R2OrbitGrad C k t g A c) (hA : A ≤ A') : R2OrbitGrad C k t g A' c :=
  fun f hf r hr => ⟨(h f hf r hr).1, (h f hf r hr).2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le))⟩

theorem s103_orbit_claims {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) :
    ∃ C c : ℝ, 0 < c ∧ ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      let Cf := (quadraticGradientDyn d s q β).coeff (fun _ => ρβ)
      let φ := oscTestFun ((24 * d + 240 : ℕ) : ℝ) α
      R2OrbitSup Cf (4 * d + 42) t φ (C * s103_b d α) ∧ R2OrbitGrad Cf (4 * d + 42) t φ (C * s103_b d α) c ∧
      R2OrbitSup Cf (4 * d + 42) t (generatorW Cf t φ) (C * s103_b d α) ∧
      R2OrbitGrad Cf (4 * d + 42) t (generatorW Cf t φ) (C * s103_b d α) c ∧
      R2OrbitSup Cf (4 * d + 42) t (fun x => generatorW Cf t (generatorW Cf t φ) x +
        deriv (fun t' => generatorW Cf t' φ x) t) (C * s103_b d α) := by
  obtain ⟨Cg, cg, Cz, hCg, hcg, hCz, horb⟩ := s103_orbit_of_data hd hs0 hsd hq hβ hρ
  obtain ⟨K, hK0, hK⟩ := s103_data hd hs0 hsd hq hβ hρ
  refine ⟨max (2 * Cg * K) ((1 + Cz) * K + 2 * Cg * K), cg, hcg, fun α t ht => ?_⟩
  intro Cf φ
  have hb0 := s103_b_nonneg α
  have hB0 : 0 ≤ K * s103_b d α := mul_nonneg hK0 hb0
  have hm1 : 2 * Cg * (K * s103_b d α) ≤ max (2 * Cg * K) ((1 + Cz) * K + 2 * Cg * K) * s103_b d α := by
    calc 2 * Cg * (K * s103_b d α) = (2 * Cg * K) * s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  have hm2 : (1 + Cz) * (K * s103_b d α) + 2 * Cg * (K * s103_b d α) ≤
      max (2 * Cg * K) ((1 + Cz) * K + 2 * Cg * K) * s103_b d α := by
    calc (1 + Cz) * (K * s103_b d α) + 2 * Cg * (K * s103_b d α) =
        ((1 + Cz) * K + 2 * Cg * K) * s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
  have key : ∀ a : ℕ, a ≤ 2 →
      R2OrbitGrad Cf (4 * d + 42) t ((fun g x => generatorW Cf 0 g x)^[a] φ)
        (max (2 * Cg * K) ((1 + Cz) * K + 2 * Cg * K) * s103_b d α) cg ∧
      R2OrbitSup Cf (4 * d + 42) t ((fun g x => generatorW Cf 0 g x)^[a] φ)
        (max (2 * Cg * K) ((1 + Cz) * K + 2 * Cg * K) * s103_b d α) := by
    intro a ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := hK a ha α
    have hgd := horb _ (K * s103_b d α) hB0 (h1.of_le (s103_cast_le_infty _)) h2 h3 h4 h5 t ht
    exact ⟨s103_orbitGrad_mono hgd.1 hm1, s103_orbitSup_mono hgd.2 hm2⟩
  have e0 : (fun g x => generatorW Cf 0 g x)^[0] φ = φ := rfl
  have e1 : (fun g x => generatorW Cf 0 g x)^[1] φ = generatorW Cf t φ := rfl
  have e2 : (fun g x => generatorW Cf 0 g x)^[2] φ = fun x => generatorW Cf t (generatorW Cf t φ) x +
        deriv (fun t' => generatorW Cf t' φ x) t := by
    funext x
    have : (fun t' => generatorW Cf t' φ x) = fun _ => generatorW Cf 0 φ x := rfl
    rw [this, deriv_const]
    simp only [add_zero]
    rfl
  obtain ⟨g0, s0⟩ := key 0 (by norm_num)
  obtain ⟨g1, s1⟩ := key 1 (by norm_num)
  obtain ⟨g2, s2⟩ := key 2 (by norm_num)
  rw [e0] at g0 s0
  rw [e1] at g1 s1
  rw [e2] at s2
  exact ⟨s0, g0, s1, g1, s2⟩

end HRS.MS.R2WinOrb

end
