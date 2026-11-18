import HRS.ME.FamUF1
import HRS.MD.EQEvoFinal
import HRS.MD.EQBurnDefs

/-!
# Chunk E, packet F4: V-uniform stationary evolution package (namespace `HRS.ME.FamU`)

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`; fixed data first, then the constants,
then `∀ V, Torus.IsSmooth V → (∀ j, Torus.cbNorm j V ≤ Bf j) → …`):
* `HRS.MD.EQEvoLevel.eqevo_level_stat_proof` (`HRS/MD/EQEvoLevel.lean:36`) becomes `eqevo_level_stat_unifV`.
  The `choose Ms` is taken over the V-uniform `hsmU`, so `Ms` depends only on `Bf` (through `Bμ, BV`
  of `eqevo_genhyp_unifV` and `Λ₀, c₀, lam, Lam, B` of `HRS.ME.EVU.eqevo_thermal_unifV` at level `K+2`).
  The per-`V` facts (existence of `Vev`, duality, tail identities) stay per `V`.
* `HRS.MD.EQEvoFinal.eq_evolution_uniform_proof` (`HRS/MD/EQEvoFinal.lean:29`) becomes `eq_evolution_uniform_unifV`.
* `HRS.MD.EQBurnWire.eqbw_evoPkg` (`HRS/MD/EQBurnWire.lean:27`) becomes `eqbw_evoPkg_unifV`, with the family
  predicate `EvoPkgFam` (a `∀ V` reuse of `HRS.MD.EQBurn.EvoPkg`, `HRS/MD/EQBurnDefs.lean:29`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.ME.FamU

open HRS HRS.PDE HRS.PDE.ET HRS.PDE.MFAdjoint HRS.PDE.MFSemigroup HRS.Uniform.Q48b HRS.Uniform
open HRS.Uniform.Q54 HRS.MD.EQEvoUnif

variable {d : ℕ}

/-- **F4a (V-uniform copy of `eqevo_level_stat_proof`).** The fixed data are `d s hs0 hsd βm βp hβm hββ M`
and the bound sequence `Bf`; the constants `c, Cr, cr` are chosen before `V`. -/
theorem eqevo_level_stat_unifV (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (M : ℝ) (Bf : ℕ → ℝ) :
    ∃ c Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V →
      (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∃ Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) M Vev ∧
        (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (c * (t - u))) ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- discrete parameters (fixed before `V` and `β`)
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
  -- the truncation level and the thermal level (fixed before `V`)
  obtain ⟨K, hKa, hKb⟩ : ∃ K : ℕ, ⌈(d : ℝ) + |M| + (j : ℝ) + 4⌉₊ ≤ K ∧
      2 * (j + 6 + mStar d) + 6 * d + 30 ≤ K :=
    ⟨⌈(d : ℝ) + |M| + (j : ℝ) + 4⌉₊ + 2 * (j + 6 + mStar d) + 6 * d + 30, by omega, by omega⟩
  have hKr : (d : ℝ) + |M| + (j : ℝ) + 4 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hKa)
  obtain ⟨Λ₀, c₀, lam, Lam, B, hc₀, -, -, hTh⟩ :=
    HRS.ME.EVU.eqevo_thermal_unifV hd s βm βp hs0 hsd hβm hββ (Bf (K + 2)) (j + 6 + mStar d) K hKb
  obtain ⟨Bμ, BV, hBμ0, hBV0, hGH⟩ :=
    eqevo_genhyp_unifV hd s βm βp hs0 hsd hβm hββ Bf K (by omega)
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
  -- smoothing constants `Ms i` (uniform in `V`, `β`, `ρβ`, `Vev`)
  have hsmU : ∀ i : ℕ, ∃ Mi : ℝ, 0 ≤ Mi ∧ (i < n → ∀ (V : Torus d → ℝ), Torus.IsSmooth V →
      (∀ k : ℕ, Torus.cbNorm k V ≤ Bf k) → ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp)
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
      refine ⟨Mi, hM0, fun _ V hV hb β hβ ρβ hρβ Vev hdV s' hs' => ?_⟩
      have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
      have hν : βp⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hβ.2
      have hFj : FrozenHyp d s (j + 3 + 3) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ :=
        FrozenHyp.mono (by omega) (hTh V hV (hb (K + 2)) β hβ ρβ hρβ).1
      have hAD : ∀ T : ℝ, 0 < T → AdjointData s (j + 3) (frozenRegime d s c₀) 1 Λ₀ Λ₀
          (PDE.mfData d s hs0 hsd V β hβ0) (βp⁻¹) T (fun _ => ρβ) :=
        fun T hT => adjointData_frozen_level (j + 3) hFj (βp⁻¹) T hT
      have hG : GenHyp d s (K : ℝ) 1 Bμ BV (PDE.mfData d s hs0 hsd V β hβ0) ρβ :=
        hGH V hV hb β hβ ρβ hρβ
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
  refine ⟨C₁, Cr, cp, hCr, hcp, fun V hV hb β hβ ρβ hρβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hν : βp⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hβ.2
  have hνM : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
  have hFL : FrozenHyp d s (j + 6 + mStar d) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ :=
    (hTh V hV (hb (K + 2)) β hβ ρβ hρβ).1
  have Hj3 : FrozenHyp d s (j + 3 + 3) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ := FrozenHyp.mono (by omega) hFL
  have Hjm : FrozenHyp d s (j + mStar d) (βp⁻¹) (βm⁻¹) c₀ Λ₀ β V ρβ := FrozenHyp.mono (by omega) hFL
  have hAD : ∀ T : ℝ, 0 < T → AdjointData s (j + 3) (frozenRegime d s c₀) 1 Λ₀ Λ₀
      (PDE.mfData d s hs0 hsd V β hβ0) (βp⁻¹) T (fun _ => ρβ) :=
    fun T hT => adjointData_frozen_level (j + 3) Hj3 (βp⁻¹) T hT
  have hG : GenHyp d s (K : ℝ) 1 Bμ BV (PDE.mfData d s hs0 hsd V β hβ0) ρβ :=
    hGH V hV hb β hβ ρβ hρβ
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
    fun i hi s' hs' => hMs i hi V hV hb β hβ ρβ hρβ Vev hdual s' hs'
  exact ⟨Vev, hdual, hplain, hbound, fun u t hu hut => hdec Vev hbound hcoc htop hsm u t hu hut⟩

/-- **F4b (V-uniform copy of `eq_evolution_uniform_proof`).** The fixed data are `d s hs0 hsd βm βp hβm hββ M T hT`
and `Bf`; the constants `K, c, Cmax` are chosen before `V`, `β`, `ρβ`. -/
theorem eq_evolution_uniform_unifV (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (M : ℝ) (T : ℝ) (hT : 0 ≤ T) (Bf : ℕ → ℝ) :
    ∃ K c Cmax : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ Cmax ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V →
      (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∃ Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) M Vev ∧
        (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) ∧
        MaxWindows.{0, 0} Vev T Cmax ∧
        ∀ S : ℝ, 0 ≤ S → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ mΩ) (Mart : ℝ → Ω → NegSobolev d M)
          (Sg : ℝ → Ω → (NegSobolev d M →L[ℝ] NegSobolev d M →L[ℝ] ℝ)),
          IsHilbertMartingaleWithCovariation P ℱ S Mart Sg →
          ∃ Z : ℝ → Ω → NegSobolev d M,
            (∀ t ∈ Set.Icc (0 : ℝ) S,
              IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d M)) Mart 0 t (Z t)) ∧
            (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 S)) ∧
            ∀ t ∈ Set.Icc (0 : ℝ) S, AEMeasurable (Z t) P := by
  obtain ⟨c, Cr, cr, hCr, hcr, hL⟩ :=
    eqevo_level_stat_unifV hd hs0 hsd βm βp hβm hββ M Bf
  refine ⟨Cr, cr, Kot.CD 2 (2 * c) T, hCr.le, hcr, Kot.CD_nonneg _ _ _, ?_⟩
  intro V hV hb β hβ ρβ hρβ
  obtain ⟨Vev, hdual, hplain, hgrow, hdec⟩ := hL V hV hb β hβ ρβ hρβ
  have hq : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp ((2 * c) * (t - u) / 2) := by
    intro u t hu hut
    rw [show (2 * c) * (t - u) / 2 = c * (t - u) by ring]
    exact hgrow u t hu hut
  refine ⟨Vev, hdual, hplain, hdec, ?_, ?_⟩
  · exact HRS.T25MW.t25mw_maxWindows_of_winMaxU
      (HRS.Uniform.Q48e.winmax_of_quasi.{0} hplain (K := 2 * c) hq hT)
  · intro S hS Ω mΩ P _ ℱ Mart Sg hM
    have hW := HRS.Uniform.Q48e.winmax_of_quasi.{0} hplain (K := 2 * c) hq hS
    obtain ⟨Z, h1, h2, h3, -⟩ := hW Ω P ℱ 0 le_rfl Mart Sg (by rw [zero_add]; exact hM)
    rw [zero_add] at h1 h2 h3
    exact ⟨Z, h1, h3, fun t ht => (h2 t ht).aemeasurable⟩

/-- The family predicate: for every smooth `V` with `cbNorm j V ≤ Bf j` (all `j`), the package
`HRS.MD.EQBurn.EvoPkg` holds with the constants `m K c T Cmax` (chosen before `V`). -/
def EvoPkgFam (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Bf : ℕ → ℝ) (βm βp : ℝ) (hβm : 0 < βm)
    (m K c T Cmax : ℝ) : Prop :=
  ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    HRS.MD.EQBurn.EvoPkg d s hs0 hsd V βm βp hβm m K c T Cmax

/-- **F4c (V-uniform copy of `eqbw_evoPkg`).** The fixed data are `d s hs0 hsd βm βp hβm hββ m T hT` and `Bf`;
the constants `K, c, Cmax` come before `V`, and the package is the family predicate `EvoPkgFam`. -/
theorem eqbw_evoPkg_unifV {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (m : ℝ) (T : ℝ) (hT : 0 ≤ T) (Bf : ℕ → ℝ) :
    ∃ K c Cmax : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ Cmax ∧ EvoPkgFam d s hs0 hsd Bf βm βp hβm m K c T Cmax := by
  obtain ⟨K, c, Cmax, hK, hc, hCmax, h⟩ :=
    eq_evolution_uniform_unifV hd hs0 hsd βm βp hβm hββ m T hT Bf
  refine ⟨K, c, Cmax, hK, hc, hCmax, ?_⟩
  intro V hV hb β hβ ρβ hρ
  obtain ⟨Vev, hdual, hplain, hdec, hmax, hconv⟩ := h V hV hb β hβ ρβ hρ
  refine ⟨Vev, ⟨hplain, hdec, ?_, ?_⟩, hdual⟩
  · intro Ω mΩ P _ ℱ a ha M Sg hM Z hZS hZc hZm
    exact hmax Ω P ℱ a ha M Sg hM Z (fun t _ => (hZm t).aemeasurable) hZS hZc
  · intro T' hT' Ω mΩ P _ ℱ M Sg hM
    exact hconv T' hT'.le Ω P ℱ M Sg hM

end HRS.ME.FamU
