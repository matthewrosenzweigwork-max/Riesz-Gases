import HRS.MS.OrbFeatAux3

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S52B

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- **`orbit_feature_bounded`, conditional on the uniqueness of classical adjoint solutions** (`S52bUniq`):
exactly the frozen conclusion of `HRS.Whole.orbit_feature_bounded` (same hypotheses), with the single extra hypothesis
`huniq` for the frozen coefficient. -/
theorem orbit_feature_bounded_of_uniq (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d)
    (hT : 0 ≤ T) (hν : 0 < ν) (hρ : IsSchwartzDensity ρ)
    (hc : ∃ σ : Euc d → Euc d, (∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) ∧
      c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x)
    (huniq : S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T) :
    ∀ b : ℕ, b + 1 ≤ k → ∃ Cb : ℝ, ∀ a : Fin d, ∀ r ∈ Set.Icc 0 T,
      ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun x => gradFeature (fixedViscosityCoeff s (-1) Q ν c ρ) m T a r x) ∧
      ∀ x : Euc d, ‖iteratedFDeriv ℝ b
        (fun y => gradFeature (fixedViscosityCoeff s (-1) Q ν c ρ) m T a r y) x‖ ≤ Cb := by
  have hd1 : 1 ≤ d := by omega
  have hk6 : (6 : ℝ) < k := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by
    have : 1 ≤ k := by exact_mod_cast (by linarith : (1 : ℝ) ≤ k)
    omega⟩
  intro b hb
  obtain ⟨σ, hσ, hc'⟩ := hc
  set K : ℕ := s52bK d n with hK
  set J : ℕ := s52bIdx d s (K + 2) with hJ
  have hKJ : K ≤ J := by
    show s52bK d n ≤ s52bIdx d s (s52bK d n + 2)
    unfold s52bIdx; omega
  obtain ⟨Co, hCo0, hCo⟩ := s52b_orbit_data hd hs0 hsd n hk m hT hν Q ρ hρ.2 σ hσ c hc' huniq
  obtain ⟨Cb, hCb0, hCb⟩ := s52b_base_data (d := d) n m hKJ
  -- the exponent
  have hJm : (d : ℝ) < (m - J) / 2 := by
    have h1 : (J : ℝ) = 2 * (n : ℝ) + 3 * (⌊(d : ℝ) / 2⌋₊ : ℝ) + 9 + (⌈s + 1⌉₊ : ℝ) := by
      simp only [hJ, hK, s52bIdx, s52bK]; push_cast; ring
    have h2 : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    have h3 : (⌈s + 1⌉₊ : ℝ) < s + 1 + 1 := Nat.ceil_lt_add_one (by linarith)
    have h4 : ((2 * (n + 1) + 2 * d + 20 : ℕ) : ℝ) = 2 * (n : ℝ) + 2 + 2 * d + 20 := by push_cast; ring
    rw [h4] at hm
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    have h := (summable_oscEigenvalue_rpow_iff hd1 ((m - J) / 2)).2 hJm
    have e : -((m - (J : ℝ)) / 2) = ((J : ℝ) - m) / 2 := by ring
    rwa [e] at h
  set Cc : ℝ := max Cb Co with hCc
  set cc : MultiIndex d → ℝ := fun α => Cc * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) with hcc
  have hpos : ∀ α, 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun α =>
    Real.rpow_nonneg (oscEv_pos α).le _
  have hc0 : ∀ α, 0 ≤ cc α := fun α => mul_nonneg (le_max_of_le_left hCb0) (hpos α)
  have hcs : Summable cc := hsum.mul_left Cc
  obtain ⟨Cf, hCf⟩ := s52b_features_of_data (n := n) (m := m) (T := T) hd1
    (fixedViscosityCoeff s (-1) Q ν c ρ) cc hc0 hcs
    (fun a α => ⟨(hCb a α).1, fun j hj x => ((hCb a α).2 j hj x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos α))⟩)
    (fun a α r t hr hrt htT => ⟨((hCo α a).1 r t hr hrt htT).1, fun j hj x =>
      (((hCo α a).1 r t hr hrt htT).2 j hj x).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (hpos α))⟩)
    (fun a r hr α x => ((hCo α a).2 r hr x).mono Ioc_subset_Icc_self |>.aestronglyMeasurable
      measurableSet_Ioc)
  refine ⟨Cf, fun a r hr => ⟨?_, fun x => ?_⟩⟩
  · simpa using (hCf a r hr).1
  · exact (hCf a r hr).2 b (by omega) x

end HRS.MS.S52B
