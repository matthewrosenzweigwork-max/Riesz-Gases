import HRS.MD.EQEvoUnif
import HRS.MD.EQEvoTopDecay
import HRS.MD.EQEvoProjTest
import HRS.MD.EQEvoChain
import HRS.Uniform.Q54Aux23

/-!
# EQP7D: P7.7 `eqevo_level_stat`, the stationary analogue of `exists_levelInput`

For the constant density `μ = fun _ => ρβ` (the frozen propagator, no mean-field path) the constants
`c, Cr, cr` are chosen before `β` and `ρβ`; only the evolution `Vev` depends on `β`.

Route (copy of `HRS.Uniform.Q54.exists_levelInput`, `Q54Aux23.lean:55-188`):
* all `β`-independent data are fixed first: `choose_params` (level `j`, step `δ`, `n`), the truncation `K`,
  the thermal constants `eqevo_thermal_unif` at level `L = j + 6 + mStar d`, `eqevo_genhyp_unif`,
  the top decay `eqevo_top_decay`, the uniform projected test `eqevo_proj_test_unif`, the quasi/hold
  constants with `ν₀ = βp⁻¹`, `νM = βm⁻¹`, the smoothing constants `Ms i` (`prop_smooth`), and the
  decay chain `eqevo_decay_chain` (explicit `Cr`);
* for each `β`: `adjointData_frozen_level` gives `AdjointData`, then `evoCore_upF`, `exists_evol`,
  `strong_cont` give the evolution, and the duality is proved as in `exists_levelInput`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MD.EQEvoLevel

open HRS HRS.PDE HRS.PDE.ET HRS.PDE.MFAdjoint HRS.PDE.MFSemigroup HRS.Uniform.Q48b HRS.Uniform
open HRS.Uniform.Q54 HRS.MD.EQEvoUnif

variable {d : ℕ}

/-- **P7.7.** Stationary (constant coefficient `ρβ`) analytic input, with uniform constants. -/
theorem eqevo_level_stat_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (M : ℝ) :
    ∃ c Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∃ Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) M Vev ∧
        (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (c * (t - u))) ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- discrete parameters (fixed before `β`)
  obtain ⟨j, n, δ, -, hjd, hjr, hδ0, hδ1, hjn, hn1⟩ := choose_params d M
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj2 : (2 : ℝ) ≤ j := by linarith
  have hjJ : ((j + 3 : ℕ) : ℝ) = (j : ℝ) + 3 := by push_cast; ring
  have hJ3 : (3 : ℝ) < ((j + 3 : ℕ) : ℝ) := by rw [hjJ]; linarith
  have hJm : mStar d ≤ j + 3 := by
    have h1 := mStar_le_aux d
    have h2 : (mStar d : ℝ) ≤ ((j + 3 : ℕ) : ℝ) := by rw [hjJ]; linarith
    exact_mod_cast h2
  have hβp0 : 0 < βp⁻¹ := inv_pos.2 (hβm.trans_le hββ)
  have habs : ∀ a : ℝ, M - 2 ≤ a → a ≤ (j : ℝ) → |a| ≤ |M| + j := fun a h1 h2 =>
    abs_le.2 ⟨by linarith [abs_nonneg M, neg_abs_le M], by linarith [abs_nonneg M, le_abs_self M]⟩
  -- the truncation level and the thermal level (fixed before `β`)
  obtain ⟨K, hKa, hKb⟩ : ∃ K : ℕ, ⌈(d : ℝ) + |M| + (j : ℝ) + 4⌉₊ ≤ K ∧
      2 * (j + 6 + mStar d) + 6 * d + 30 ≤ K :=
    ⟨⌈(d : ℝ) + |M| + (j : ℝ) + 4⌉₊ + 2 * (j + 6 + mStar d) + 6 * d + 30, by omega, by omega⟩
  have hKr : (d : ℝ) + |M| + (j : ℝ) + 4 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hKa)
  obtain ⟨Λ₀, c₀, lam, Lam, B, hc₀, -, -, hTh⟩ :=
    eqevo_thermal_unif hd s βm βp hs0 hsd hβm hββ V hV (j + 6 + mStar d) K hKb
  obtain ⟨Bμ, BV, hBμ0, hBV0, hGH⟩ :=
    eqevo_genhyp_unif hd s βm βp hs0 hsd hβm hββ V hV K (by omega)
  obtain ⟨Cp, cp, hCp, hcp, hTD⟩ :=
    HRS.MD.EQEvoTopDecay.eqevo_top_decay hd s j (by linarith) (βp⁻¹) (βm⁻¹) c₀ Λ₀
  obtain ⟨Kp, hKp0, hKp⟩ := HRS.MD.EQEvoProjTest.eqevo_proj_test_unif (d := d) (j : ℝ) (by linarith)
  -- quasi-contractivity and holding bounds at the levels `M` and `M - 2`
  obtain ⟨C₁, hC₁, hq1⟩ := quasi_upF hd1 s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ0 hBV0 M
    (by linarith [abs_nonneg M]) (βp⁻¹) hβp0 (j + 3) (by rw [hjJ]; linarith) hJ3 hJm
  obtain ⟨C₂, hC₂, hq2⟩ := quasi_upF hd1 s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ0 hBV0 (M - 2)
    (by have := habs (M - 2) le_rfl (by linarith); linarith) (βp⁻¹) hβp0 (j + 3)
    (by rw [hjJ]; linarith) hJ3 hJm
  obtain ⟨A, B', hA0, hB0, hhold⟩ := hold_upF hd1 s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ0 hBV0 (M - 2)
    (by have := habs (M - 2) le_rfl (by linarith); linarith) (βp⁻¹) (βm⁻¹) hβp0 (j + 3)
    (by rw [hjJ]; linarith) hJ3 hJm
  -- smoothing constants `Ms i` (uniform in `β`, `ρβ`, `Vev`)
  have hsmU : ∀ i : ℕ, ∃ Mi : ℝ, 0 ≤ Mi ∧ (i < n → ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp)
      (ρβ : Torus d → ℝ), IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) M Vev →
        ∀ s' : ℝ, 0 ≤ s' → WB2 ((j : ℝ) - ((i : ℝ) + 1) * δ) ((j : ℝ) - (i : ℝ) * δ) Mi
          (q48bMat M (Vev (s' + 1) s'))) := by
    intro i
    by_cases hi : i < n
    · have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : i + 1 ≤ n)
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hδi : 0 ≤ (i : ℝ) * δ := mul_nonneg hi0 hδ0.le
      have hδi1 : 0 ≤ ((i : ℝ) + 1) * δ := mul_nonneg (by linarith) hδ0.le
      have hnδ : ((i : ℝ) + 1) * δ ≤ (n : ℝ) * δ := mul_le_mul_of_nonneg_right hin hδ0.le
      obtain ⟨Mi, hM0, hM⟩ := prop_smooth hd1 s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ0 hBV0
        ((j : ℝ) - ((i : ℝ) + 1) * δ) δ hδ0 hδ1
        (by have := habs ((j : ℝ) - ((i : ℝ) + 1) * δ) (by linarith) (by linarith); linarith)
        (by have := habs ((j : ℝ) - ((i : ℝ) + 1) * δ + δ) (by linarith) (by linarith); linarith)
        (βp⁻¹) hβp0 (j + 3) (by rw [hjJ]; linarith) hJ3 hJm
      refine ⟨Mi, hM0, fun _ β hβ ρβ hρβ Vev hdV s' hs' => ?_⟩
      have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
      have hν : βp⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hβ.2
      have hFj : FrozenHyp d s (j + 3 + 3) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ :=
        FrozenHyp.mono (by omega) (hTh β hβ ρβ hρβ).1
      have hAD : ∀ T : ℝ, 0 < T → AdjointData s (j + 3) (frozenRegime d s c₀) 1 Λ₀ Λ₀
          (PDE.mfData d s hs0 hsd V β hβ0) (βp⁻¹) T (fun _ => ρβ) :=
        fun T hT => adjointData_frozen_level (j + 3) hFj (βp⁻¹) T hT
      have hG : GenHyp d s (K : ℝ) 1 Bμ BV (PDE.mfData d s hs0 hsd V β hβ0) ρβ :=
        hGH β hβ ρβ hρβ
      have hdual := hdV
      have hab : (j : ℝ) - ((i : ℝ) + 1) * δ + δ = (j : ℝ) - (i : ℝ) * δ := by ring
      have hW := wb2_of_duality (r := M) (a := (j : ℝ) - ((i : ℝ) + 1) * δ) (b := (j : ℝ) - ((i : ℝ) + 1) * δ + δ)
        (propagator (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ) s' (s' + 1))
        (Vev (s' + 1) s') (fun z φ hφ => hdual s' (s' + 1) hs' (by linarith) z φ hφ) Mi hM0
        (fun T c => by
          have hdom : Dom (j + 3) (q48bTest T c) := dom_smooth (q48bTest_smooth T c)
          have := hM (frozenRegime d s c₀) 1 Λ₀ Λ₀ (βp⁻¹) (PDE.mfData d s hs0 hsd V β hβ0) (s' + 1)
            (fun _ => ρβ) (hAD (s' + 1) (by linarith)) (fun _ _ => hG) hν hdom hs' le_rfl
          refine ⟨this.1, ?_⟩
          rw [q48bTest_sobolevNorm] at this
          exact this.2)
      rw [hab] at hW
      exact hW
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  choose Ms hMs0 hMs using hsmU
  -- the decay chain with explicit constant
  obtain ⟨Cr, hCr, hdec⟩ := HRS.MD.EQEvoChain.eqevo_decay_chain (r := M) (j := (j : ℝ)) (δ := δ)
    (cj := cp) (Cj := Cp * Kp) (C := C₁) n hδ0 hjn hcp Ms
  refine ⟨C₁, Cr, cp, hCr, hcp, fun β hβ ρβ hρβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hν : βp⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hβ.2
  have hνM : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
  have hFL : FrozenHyp d s (j + 6 + mStar d) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ := (hTh β hβ ρβ hρβ).1
  have Hj3 : FrozenHyp d s (j + 3 + 3) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ := FrozenHyp.mono (by omega) hFL
  have Hjm : FrozenHyp d s (j + mStar d) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ := FrozenHyp.mono (by omega) hFL
  have hAD : ∀ T : ℝ, 0 < T → AdjointData s (j + 3) (frozenRegime d s c₀) 1 Λ₀ Λ₀
      (PDE.mfData d s hs0 hsd V β hβ0) (βp⁻¹) T (fun _ => ρβ) :=
    fun T hT => adjointData_frozen_level (j + 3) Hj3 (βp⁻¹) T hT
  have hG : GenHyp d s (K : ℝ) 1 Bμ BV (PDE.mfData d s hs0 hsd V β hβ0) ρβ := hGH β hβ ρβ hρβ
  have hG' : ∀ t : ℝ, 0 ≤ t → GenHyp d s (K : ℝ) 1 Bμ BV (PDE.mfData d s hs0 hsd V β hβ0)
      ((fun _ => ρβ) t) := fun _ _ => hG
  have hcore : EvoCore (j + 3) (UpF (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ)) :=
    evoCore_upF hd1 s hs0 hsd (j + 3) hJm (frozenRegime d s c₀) 1 Λ₀ Λ₀ _ (βp⁻¹) (fun _ => ρβ) hAD
  have hq1' := hq1 (frozenRegime d s c₀) 1 Λ₀ Λ₀ (βp⁻¹) (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ)
    hAD hG' hν
  have hq2' := hq2 (frozenRegime d s c₀) 1 Λ₀ Λ₀ (βp⁻¹) (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ)
    hAD hG' hν
  have hhold' := hhold (frozenRegime d s c₀) 1 Λ₀ Λ₀ (βp⁻¹) (PDE.mfData d s hs0 hsd V β hβ0)
    (fun _ => ρβ) hAD hG' hν hνM
  -- the evolution
  obtain ⟨Vev, hdualJ, hbound, hid, hcoc⟩ :=
    exists_evol (j + 3) (UpF (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ)) hcore M C₁
      (by rw [hjJ]; linarith) hq1'
  have hCD : ContData (j + 3) (UpF (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ)) M Vev C₁ C₂ A B' :=
    ⟨hcore, by rw [hjJ]; linarith, hq1', hq2', hhold', hB0, hdualJ, hbound⟩
  -- duality with the true propagator on smooth functions
  have hdual : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ) M Vev := by
    intro u t hu hut z φ hφ
    have h1 := hdualJ u t hu hut z φ (dom_smooth hφ)
    rw [h1]
    by_cases h : u = t
    · subst h
      rw [upF_self]
      rcases hu.eq_or_lt with h0 | h0
      · rw [← h0]
        rw [prop_self_zero hd1 s hs0 hsd (j + 3) (frozenRegime d s c₀) 1 Λ₀ Λ₀
          (PDE.mfData d s hs0 hsd V β hβ0) (βp⁻¹) 1 (fun _ => ρβ) (hAD 1 one_pos) hφ]
      · rw [prop_self_pos hd1 s hs0 hsd (j + 3) hJm (frozenRegime d s c₀) 1 Λ₀ Λ₀
          (PDE.mfData d s hs0 hsd V β hβ0) (βp⁻¹) u (fun _ => ρβ) (hAD u h0) ⟨h0, le_rfl⟩
          (dom_smooth hφ)]
    · rw [upF_of_ne (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ) h]
  have hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T := by
    intro T _
    refine ⟨fun t ht => hid t ht.1, fun s' r' t hs hsr hrt _ => hcoc s' r' t hs hsr hrt, fun x => ?_⟩
    exact strong_cont hCD T x
  -- top-level decay of the projected propagator
  have htop : ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      WB2 (j : ℝ) (j : ℝ) ((Cp * Kp) * Real.exp (-cp * (t - u))) (q48bMat M (Vev t u)) := by
    intro u t hu hut
    have hb := q48b_wbound_of_duality (m := M) (a := (j : ℝ)) ρβ
      (propagator (PDE.mfData d s hs0 hsd V β hβ0) (fun _ => ρβ) u t) (Vev t u)
      (fun z φ hφ => hdual u t hu hut z φ hφ) Kp hKp0 (fun T c => hKp ρβ hρβ.1 T c)
      (Cp * Real.exp (-cp * (t - u))) (by positivity)
      (fun φ hc hmem => hTD β V ρβ Hjm φ hc hmem u t hu hut)
    have e : Cp * Real.exp (-cp * (t - u)) * Kp = (Cp * Kp) * Real.exp (-cp * (t - u)) := by ring
    rw [e] at hb
    exact WB2.of_wbound hb
  have hsm : ∀ i : ℕ, i < n → ∀ s' : ℝ, 0 ≤ s' →
      WB2 ((j : ℝ) - ((i : ℝ) + 1) * δ) ((j : ℝ) - (i : ℝ) * δ) (Ms i)
        (q48bMat M (Vev (s' + 1) s')) :=
    fun i hi s' hs' => hMs i hi β hβ ρβ hρβ Vev hdual s' hs'
  exact ⟨Vev, hdual, hplain, hbound, fun u t hu hut => hdec Vev hbound hcoc htop hsm u t hu hut⟩

end HRS.MD.EQEvoLevel
