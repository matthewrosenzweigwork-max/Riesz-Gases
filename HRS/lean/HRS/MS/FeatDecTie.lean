import HRS.MS.FeatDecAux12

/-!
# S8.5 tie: `HRS.Whole.feature_decay`

`feature_decay_proof` has the statement of the frozen `HRS.Whole.feature_decay`.  Route: `ρβ = thermalDensity` (unique), a Schwartz
density; `critCoeff = (⟨d/2, -1, quadV (a•1) 0, β⁻¹⟩).coeff (fun _ => ρβ)`; weighted orbit data (`s85_orbit_weighted`: the S4.12-type
decay for `0 ≤ s < d`, `s85_adjoint_decay`), weighted Hermite data, and the weighted `𝒦`-valued assembly
(`s85_features_weighted`).  The oscillator indices stay below `4.5d + 24 < m - 2d`, so the Hermite sums converge.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj HRS.MS.S52B HRS.MS.UlW

variable {d : ℕ}

theorem feature_decay_proof : type_of% @HRS.Whole.feature_decay := by
  intro d hd a β ha hβ m hm Hz hHz
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set s : ℝ := (d : ℝ) / 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hs0' : 0 < s := by simp only [hs]; linarith
  have hsd : s < (d : ℝ) := by simp only [hs]; linarith
  have hmR : (24 : ℝ) * d + 240 ≤ m := by
    have : ((wholeSpaceIndex d : ℕ) : ℝ) = 24 * d + 240 := by
      unfold wholeSpaceIndex; push_cast; ring
    rw [← this]; exact hm
  set ρ₀ : Euc d → ℝ := thermalDensity d s a β with hρ₀
  have hρS : IsSchwartzDensity ρ₀ := s85_thermal_schwartz hd hs0' hsd ha hβ
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  set Q : Matrix (Fin d) (Fin d) ℝ := a • (1 : Matrix (Fin d) (Fin d) ℝ) with hQdef
  have hQ : Q.IsSymm := by
    unfold Matrix.IsSymm
    simp [hQdef]
  set n : ℕ := d + 2 with hn
  have hn2 : 2 ≤ n := by omega
  obtain ⟨Co, hCo0, J1, hJ1, hCo⟩ := s85_orbit_weighted hd hs0 hsd n hn2 m (T := Hz) hHz.le hν Q hQ ρ₀ hρS
  obtain ⟨Cb, hCb0, J2, hJ2, hCb⟩ := s85_base_weighted (d := d) hs0 n m
  -- the summable majorant
  have hJbound : ∀ J : ℕ, (J : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 → (d : ℝ) < (m - J) / 2 := by
    intro J hJ
    have : (n : ℝ) = d + 2 := by simp [hn]
    simp only [hs] at hJ
    rw [this] at hJ
    linarith
  have hsum : ∀ J : ℕ, (J : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 →
      Summable fun α : MultiIndex d => oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    intro J hJ
    have h := (summable_oscEigenvalue_rpow_iff hd1 ((m - J) / 2)).2 (hJbound J hJ)
    have e : -((m - (J : ℝ)) / 2) = ((J : ℝ) - m) / 2 := by ring
    rwa [e] at h
  have hpos : ∀ (J : ℕ) (α : MultiIndex d), 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    fun J α => Real.rpow_nonneg (oscEv_pos α).le _
  set c : MultiIndex d → ℝ := fun α => Co * oscEigenvalue d α ^ (((J1 : ℝ) - m) / 2) +
    Cb * oscEigenvalue d α ^ (((J2 : ℝ) - m) / 2) with hc
  have hc0 : ∀ α, 0 ≤ c α := fun α => add_nonneg (mul_nonneg hCo0 (hpos J1 α))
    (mul_nonneg hCb0 (hpos J2 α))
  have hcs : Summable c := ((hsum J1 hJ1).mul_left Co).add ((hsum J2 hJ2).mul_left Cb)
  -- t-measurability
  have hcoeff := s85_coeff_fv (s := s) (ν := β⁻¹) Q hQ ρ₀
  have hmeas : ∀ (a' : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) Hz, ∀ (α : MultiIndex d) (x : Euc d),
      AEStronglyMeasurable (fun t => gradComp a' (propagatorW
        ((⟨s, -1, quadV Q 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ₀)) r t
        (generatorW ((⟨s, -1, quadV Q 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ₀)) t
          (oscTestFun m α))) x) (volume.restrict (Set.Ioc r Hz)) := by
    intro a' r hr α x
    have hn' : (d : ℝ) / 2 + 6 < ((d + 6 + 1 : ℕ) : ℝ) := by push_cast; linarith
    obtain ⟨Co', hCo', hall⟩ := s52b_orbit_data hd hs0 hsd (d + 6) hn' m hHz.le hν Q ρ₀ hρS.2
      (fun _ => 0) (s85_sigma d) (s85c s ρ₀) rfl (s85_uniq hd hs0 hsd hν Q hQ hρS Hz)
    obtain ⟨-, hmc⟩ := hall α a'
    have hcont := hmc r hr x
    rw [hcoeff]
    exact (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  -- the weighted feature lemma
  obtain ⟨Cf, hCf⟩ := s85_features_weighted (n := n) (m := m) (T := Hz) (p := s + 2) hd1
    (by linarith) ((⟨s, -1, quadV Q 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ₀)) c hc0 hcs
    (fun a' α => by
      obtain ⟨hcd, hb⟩ := hCb α a'
      refine ⟨hcd, fun j hj x => (hb j hj x).trans ?_⟩
      have h1 : Cb * oscEigenvalue d α ^ (((J2 : ℝ) - m) / 2) ≤ c α := by
        simp only [hc]
        have := mul_nonneg hCo0 (hpos J1 α)
        linarith
      have h2 : 0 ≤ jbracket x ^ (-(s + 2 + (j : ℝ))) := Real.rpow_nonneg (u2_jb_pos x).le _
      exact mul_le_mul_of_nonneg_right h1 h2)
    (fun a' α r t hr hrt htT => by
      obtain ⟨hcd, hb⟩ := hCo α a' r t hr hrt htT
      refine ⟨hcd, fun j hj x => (hb j hj x).trans ?_⟩
      have h1 : Co * oscEigenvalue d α ^ (((J1 : ℝ) - m) / 2) ≤ c α := by
        simp only [hc]
        have := mul_nonneg hCb0 (hpos J2 α)
        linarith
      have h2 : 0 ≤ jbracket x ^ (-(s + 2 + (j : ℝ))) := Real.rpow_nonneg (u2_jb_pos x).le _
      exact mul_le_mul_of_nonneg_right h1 h2)
    hmeas
  refine ⟨Cf, fun ρβ hρβ => ?_⟩
  have hEq : ρβ = ρ₀ := (s85_thermal_eq hd hs0' hsd ha hβ hρβ).1
  subst hEq
  rw [s85_crit_eq]
  refine ⟨fun α t ht => s85_exists_adjoint hd hs0 hsd hν Q hQ hρS Hz hHz.le m α t ht, fun i r hr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hCf i r hr
  exact ⟨h1, h2, fun x l hl => h3 l hl x⟩

end HRS.MS.S85

example := (@HRS.MS.S85.feature_decay_proof : type_of% @HRS.Whole.feature_decay)
