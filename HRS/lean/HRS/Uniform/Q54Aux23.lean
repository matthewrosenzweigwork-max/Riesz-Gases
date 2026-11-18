import HRS.Uniform.Q54Aux22
import HRS.Uniform.Q54Aux1

/-!
# Q54, part 23: the per-level analytic input `LevelInput` of Lemma 3.27 from Proposition 5.1 / 5.2

For a real level `r` there is `K₀` such that for every `K ≥ K₀` and every solution `ρc` of Proposition 5.1 (`β₋ = β₊ = β`) the
strongly continuous dual evolution on `E_r` exists, is quasi-contractive and has exponential decay (`LevelInput`).

Route: even level `j ≥ r + 1` (`j > d/2 + 4`), `J = j + 3`;
* `finiteReg_hypotheses` gives `AdjointData` of level `J` on every window; `genHyp_of_mf` gives `GenHyp`;
* `evoCore_upF`, `quasi_upF`, `hold_upF` and `exists_evol` / `strong_cont` give the evolution and its strong continuity;
* Proposition 5.2 at level `j` (via `q48b_wbound_of_duality`) gives the decay at the top level; `prop_smooth` the unit-time
  smoothing; `decay_chain` combines them to the decay at level `r`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform.Q48b HRS.Uniform

variable {d : ℕ}

theorem mStar_le_aux (d : ℕ) : (mStar d : ℝ) ≤ (d : ℝ) / 2 + 3 := by
  unfold mStar
  push_cast
  have := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
  linarith

theorem choose_params (d : ℕ) (r : ℝ) : ∃ (j n : ℕ) (δ : ℝ), Even j ∧ (d : ℝ) / 2 + 5 ≤ j ∧
    r + 1 ≤ j ∧ 0 < δ ∧ δ ≤ 1 ∧ (j : ℝ) = r + n * δ ∧ 1 ≤ n := by
  set N₀ : ℕ := ⌈max (r + 1) ((d : ℝ) / 2 + 5)⌉₊ with hN₀
  have hN : max (r + 1) ((d : ℝ) / 2 + 5) ≤ N₀ := Nat.le_ceil _
  have hj : (((2 * N₀ : ℕ)) : ℝ) = 2 * N₀ := by push_cast; ring
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hj1 : r + 1 ≤ ((2 * N₀ : ℕ) : ℝ) := by
    rw [hj]; have := (le_max_left (r + 1) ((d : ℝ) / 2 + 5)).trans hN; linarith
  have hj2 : (d : ℝ) / 2 + 5 ≤ ((2 * N₀ : ℕ) : ℝ) := by
    rw [hj]; have := (le_max_right (r + 1) ((d : ℝ) / 2 + 5)).trans hN; linarith
  set j : ℕ := 2 * N₀ with hjdef
  set n : ℕ := ⌈(j : ℝ) - r⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h0 => by
    have : 0 < ⌈(j : ℝ) - r⌉₊ := Nat.ceil_pos.2 (by linarith)
    omega)
  have hnle : (j : ℝ) - r ≤ n := Nat.le_ceil _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨j, n, ((j : ℝ) - r) / n, even_two_mul N₀, hj2, hj1, by apply div_pos <;> linarith, ?_, ?_, hn1⟩
  · rw [div_le_one hnpos]; exact hnle
  · field_simp; ring

theorem exists_levelInput (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (r : ℝ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ (β : ℝ) (hβ : 0 < β) (V ρ₀ : Torus d → ℝ),
      PDE.FiniteRegHyp d s β β K V ρ₀ → ∀ ρc : ℝ → PDE.Coeff d,
      PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc → LevelInput d s hs0 hsd V β hβ ρc r := by
  obtain ⟨j, n, δ, hjev, hjd, hjr, hδ0, hδ1, hjn, hn1⟩ := choose_params d r
  set J : ℕ := j + 3 with hJ
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hJr : (J : ℝ) = j + 3 := by rw [hJ]; push_cast; ring
  refine ⟨⌈(d : ℝ) + |r| + j + 4⌉₊ + 2 * J + 4 * d + 20, fun K hK β hβ V ρ₀ H ρc hρc => ?_⟩
  have hKr : (d : ℝ) + |r| + j + 4 ≤ K := by
    have h1 : (d : ℝ) + |r| + j + 4 ≤ ⌈(d : ℝ) + |r| + j + 4⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(d : ℝ) + |r| + j + 4⌉₊ + 2 * J + 4 * d + 20 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at h2
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  have hKJ : 2 * J + 4 * d + 20 ≤ K := by omega
  have hKj : 2 * j + 4 * d + 20 ≤ K := by omega
  -- numerical facts
  have habsr : (0 : ℝ) ≤ |r| := abs_nonneg r
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hJd : (d : ℝ) / 2 + 4 < J := by rw [hJr]; linarith
  have hJm : mStar d ≤ J := by
    have h1 := mStar_le_aux d
    have : (mStar d : ℝ) ≤ J := by rw [hJr]; linarith
    exact_mod_cast this
  have hJ3 : (3 : ℝ) < J := by rw [hJr]; linarith
  have hrJ : r + 4 ≤ (J : ℝ) := by rw [hJr]; linarith
  -- Proposition 5.1 data
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  obtain ⟨ρβ, hρβ, hρC, hpos, -⟩ := finite_reg_thermal hd s β β K V ρ₀ H β hβI
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    MFAdjoint.finiteReg_hypotheses hd s β β K V ρ₀ H J hJd hKJ
  obtain ⟨-, hAD, -⟩ := hall β hβI ρc hρc ρβ hρβ hρC hpos
  obtain ⟨Bμ, BV, hBμ, hBV, hGH⟩ := genHyp_of_mf hd s β β K V ρ₀ H
  have hβ' : 0 < β⁻¹ := inv_pos.2 hβ
  set D : DynData d := mfData d s hs0 hsd V β hβ with hD
  set μ : ℝ → Torus d → ℝ := mfPath ρc with hμ
  have hAD' : ∀ T : ℝ, 0 < T → AdjointData s J R 1 Λ (Torus.cbNorm (J + 3) V) D β⁻¹ T μ := hAD
  have hG : ∀ t : ℝ, 0 ≤ t → GenHyp d s (K : ℝ) 1 Bμ BV D (μ t) := fun t ht => hGH β hβI ρc hρc t ht
  have hν : β⁻¹ ≤ D.invβ := le_rfl
  have hνM : D.invβ ≤ β⁻¹ := le_rfl
  have hcore : EvoCore J (UpF D μ) := evoCore_upF hd s hs0 hsd J hJm R 1 Λ _ D β⁻¹ μ hAD'
  -- quasi-contractivity at the levels `r` and `r - 2`
  have hK1 : (d : ℝ) + |r| + 4 ≤ K := by linarith
  have hK2 : (d : ℝ) + |r - 2| + 4 ≤ K := by
    have : |r - 2| ≤ |r| + 2 := by
      calc |r - 2| ≤ |r| + |(2 : ℝ)| := abs_sub _ _
        _ = |r| + 2 := by norm_num
    have hj2 : (2 : ℝ) ≤ j := by linarith
    linarith
  obtain ⟨C₁, hC₁, hq1⟩ := quasi_upF hd s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ hBV r hK1 β⁻¹ hβ' J
    (by linarith) hJ3 hJm
  obtain ⟨C₂, hC₂, hq2⟩ := quasi_upF hd s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ hBV (r - 2) hK2 β⁻¹
    hβ' J (by linarith) hJ3 hJm
  obtain ⟨A, B, hA0, hB0, hhold⟩ := hold_upF hd s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ hBV (r - 2) hK2
    β⁻¹ β⁻¹ hβ' J (by linarith) hJ3 hJm
  have hq1' := hq1 R 1 Λ _ β⁻¹ D μ hAD' hG hν
  have hq2' := hq2 R 1 Λ _ β⁻¹ D μ hAD' hG hν
  have hhold' := hhold R 1 Λ _ β⁻¹ D μ hAD' hG hν hνM
  -- the evolution
  obtain ⟨Vev, hdualJ, hbound, hid, hcoc⟩ :=
    exists_evol J (UpF D μ) hcore r C₁ (by linarith) hq1'
  have hCD : ContData J (UpF D μ) r Vev C₁ C₂ A B :=
    ⟨hcore, by linarith, hq1', hq2', hhold', hB0, hdualJ, hbound⟩
  -- duality with the true propagator on smooth functions
  have hdual : IsDualEvolution D μ r Vev := by
    intro u t hu hut z φ hφ
    have h1 := hdualJ u t hu hut z φ (dom_smooth hφ)
    rw [h1]
    by_cases h : u = t
    · subst h
      rw [upF_self]
      rcases hu.eq_or_lt with h0 | h0
      · rw [← h0]
        rw [prop_self_zero hd s hs0 hsd J R 1 Λ _ D β⁻¹ 1 μ (hAD' 1 one_pos) hφ]
      · rw [prop_self_pos hd s hs0 hsd J hJm R 1 Λ _ D β⁻¹ u μ (hAD' u h0) ⟨h0, le_rfl⟩ (dom_smooth hφ)]
    · rw [upF_of_ne D μ h]
  have hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T := by
    intro T hT
    refine ⟨fun t ht => hid t ht.1, fun s' r' t hs hsr hrt _ => hcoc s' r' t hs hsr hrt, fun x => ?_⟩
    exact strong_cont hCD T x
  -- the decay
  obtain ⟨Cp, cp, κp, hCp, hcp, hκp, hP52⟩ := adjoint_decay_comparison hd s β β K V ρ₀ H j hjev
    (by linarith) hKj
  have hρprob : IsProbDensity ρβ := hρβ.1
  obtain ⟨Kp, hKp0, hKp⟩ := q48b_proj_test_bound ρβ hρprob (j : ℝ) (by linarith)
  have htop : ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      WB2 (j : ℝ) (j : ℝ) ((Cp * Kp) * Real.exp (-cp * (t - u))) (q48bMat r (Vev t u)) := by
    intro u t hu hut
    have hb := q48b_wbound_of_duality (m := r) (a := (j : ℝ)) ρβ (propagator D μ u t) (Vev t u)
      (fun z φ hφ => hdual u t hu hut z φ hφ) Kp hKp0 hKp (Cp * Real.exp (-cp * (t - u)))
      (by positivity) (fun φ hc hmem => by
        have := hP52 β hβI ρc hρc ρβ hρβ hρC hpos φ hc hmem u t hu hut
        exact ⟨this.1, this.2.1⟩)
    have e : Cp * Real.exp (-cp * (t - u)) * Kp = (Cp * Kp) * Real.exp (-cp * (t - u)) := by ring
    rw [e] at hb
    exact WB2.of_wbound hb
  have hsm : ∀ i : ℕ, i < n → ∃ M : ℝ, 0 ≤ M ∧ ∀ s' : ℝ, 0 ≤ s' →
      WB2 ((j : ℝ) - ((i : ℝ) + 1) * δ) ((j : ℝ) - (i : ℝ) * δ) M (q48bMat r (Vev (s' + 1) s')) := by
    intro i hi
    have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : i + 1 ≤ n)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    set a : ℝ := (j : ℝ) - ((i : ℝ) + 1) * δ with ha
    have har : r ≤ a := by rw [ha]; nlinarith
    have haj : a ≤ j := by rw [ha]; nlinarith
    have hab : a + δ = (j : ℝ) - (i : ℝ) * δ := by rw [ha]; ring
    have habj : a + δ ≤ j := by rw [hab]; nlinarith
    have habr : r ≤ a + δ := by linarith
    have hKa : (d : ℝ) + |a| + 4 ≤ K := by
      have : |a| ≤ |r| + j := by
        rw [abs_le]; constructor <;> [skip; skip] <;> linarith [neg_abs_le r, le_abs_self r]
      linarith
    have hKb : (d : ℝ) + |a + δ| + 4 ≤ K := by
      have : |a + δ| ≤ |r| + j := by
        rw [abs_le]; constructor <;> linarith [neg_abs_le r, le_abs_self r]
      linarith
    obtain ⟨M, hM0, hM⟩ := prop_smooth hd s hs0 hsd (K : ℝ) 1 Bμ BV zero_le_one hBμ hBV a δ hδ0 hδ1
      hKa hKb β⁻¹ hβ' J (by rw [hJr]; linarith) hJ3 hJm
    refine ⟨M, hM0, fun s' hs' => ?_⟩
    have hW := wb2_of_duality (r := r) (a := a) (b := a + δ) (propagator D μ s' (s' + 1))
      (Vev (s' + 1) s') (fun z φ hφ => hdual s' (s' + 1) hs' (by linarith) z φ hφ) M hM0
      (fun T c => by
        have hdom : Dom J (q48bTest T c) := dom_smooth (q48bTest_smooth T c)
        have := hM R 1 Λ _ β⁻¹ D (s' + 1) μ (hAD' (s' + 1) (by linarith))
          (fun t ht => hG t ht.1) hν hdom hs' le_rfl
        refine ⟨this.1, ?_⟩
        rw [q48bTest_sobolevNorm] at this
        exact this.2)
    rw [hab] at hW
    exact hW
  obtain ⟨Cr, cr, hCr, hcr, hdec⟩ := decay_chain (r := r) (j := (j : ℝ)) (δ := δ) (cj := cp)
    (Cj := Cp * Kp) (C := C₁) n hδ0 hjn Vev (fun u t hu hut => hbound u t hu hut) hcoc
    (mul_nonneg hCp.le hKp0) hcp htop hsm
  exact ⟨Vev, hdual, hplain, ⟨C₁, fun u t hu hut => hbound u t hu hut⟩, Cr, cr, hCr, hcr, hdec⟩

end HRS.Uniform.Q54
