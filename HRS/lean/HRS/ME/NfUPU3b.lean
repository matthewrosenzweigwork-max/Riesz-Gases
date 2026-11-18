import HRS.ME.NfUPU3a
import HRS.Equilibrium.PinComparison

/-!
# Packet PU3b (uniform pin chain, part b)

Uniform versions (namespace `HRS.ME.NfU`) of the three lemmas of `HRS/Equilibrium/PinComparison.lean`:

* `dim_step_unif` of `HRS.PinAux.dim_step` (l.189), constant `exp 4 * C * (1 + pinGamma βm)` with the
  uniform `C` of `pin_step_set_unif`;
* `chain_unpinned_unif` of `HRS.PinAux.chain_unpinned` (l.319), constant `C3` of `dim_step_unif`;
* `pin_comparison_proof_unif` of `HRS.pin_comparison_proof` (l.389). The smallness threshold is the
  single `γ₁ = pinGamma βp`; `hrow` (for `γ₁`) implies the threshold `pinGamma β` for every
  `β ∈ [βm, βp]` since `pinGamma` is antitone. The constant is
  `max (βp * (C1 + j * C3)) (exp (4 + a) * (a + 1))`, chosen after `q, a, j` and before `β, ρ`.

The per-`β` equalities `V.γ = pinGamma β`, `V.M = β * pinGamma β + 1` stay in the per-`β` clause.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.PinAux HRS.External HRS.External.RefMarg HRS.ME.PmU

variable {d : ℕ}

theorem dim_step_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ0 : 0 ≤ Λ₀)
    (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (a : ℕ) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (_ : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma β))
        (N n : ℕ), a + 1 ≤ N → n + 1 ≤ N → ∀ (i : Fin (n + 1)) (j : Fin n) (B : Set (Torus d)),
        MeasurableSet B →
        |((pinnedLaw V (β / N) (n + 1) (fun e : Empty => e.elim)).map
              (fun y => y (i.succAbove j))).real B
          - ((pinnedLaw V (β / N) n (fun e : Empty => e.elim)).map (fun y => y j)).real B|
          ≤ C3 * (β / N) * (withDensityReal ρ).real B := by
  obtain ⟨C, hC0, hC⟩ := pin_step_set_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ0 q hq0 hqm Cq hqenv hdec a
  refine ⟨Real.exp 4 * C * (1 + pinGamma βm), by have := pinGamma_pos hβm; positivity, ?_⟩
  intro β hβI ρ U V hVq hVγ hVM hVM' hrow N n hNa hn1 i j B hB
  have hβ : 0 < β := U.hβpos
  have hρ : SmoothPosDensity ρ := U.rho
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  have hγΓ : γ₀ ≤ pinGamma βm := pinGamma_le_of_le hβm hβI.1
  set Kc : ℝ := Real.exp ((β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀) with hKc
  have hbg : β * γ₀ = 1 / (16 * Real.exp 10) := beta_mul_pinGamma hβ
  have hbg1 : β * γ₀ ≤ 1 := by
    rw [hbg, div_le_one (by positivity)]
    nlinarith [Real.exp_pos 10, Real.add_one_le_exp (10 : ℝ)]
  have hKle : Kc ≤ Real.exp 4 := by
    rw [hKc]; apply Real.exp_le_exp.2; linarith
  have hγle : 1 + γ₀ ≤ 1 + pinGamma βm := by linarith
  have key : Kc * (1 + γ₀) ≤ Real.exp 4 * (1 + pinGamma βm) :=
    mul_le_mul hKle hγle (by positivity) (by positivity)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hnz : NeZero n := ⟨(Fin.pos j).ne'⟩
  set lam : ℝ := β / N with hlamdef
  set E0 : Empty → Torus d := fun e => e.elim with hE0
  -- the mixture
  have hmix := pinned_marginal_succ V hlam E0 i j hB
  have hω := measurable_pinWeight V hlam E0 n
  have hω1 := lintegral_pinWeight V hlam E0 i j
  have hωKm : (withDensityReal ρ).withDensity (pinWeight V lam E0 n) ≤ ENNReal.ofReal Kc • withDensityReal ρ := by
    rw [← marginal_eq_pinWeight V hlam E0 i]
    have := pinned_marginal_le (μ := withDensityReal ρ) V hβ.le (by omega : 0 < N) (by omega : n + 1 ≤ N) E0 i
    have e : V.M + V.M' + β * (1 + (Fintype.card Empty : ℝ)) * V.γ
        = (β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀ := by rw [hVM, hVM', hVγ]; simp
    rw [e] at this
    exact this
  -- pointwise pin step for the extra coordinate
  have hγnn : 0 ≤ γ₀ := hγ₀.le
  have hlamβ : lam ≤ β := by
    rw [hlamdef, div_le_iff₀ hNpos]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hint : ∀ x, Integrable (fun z => q (z - x)) (withDensityReal ρ) := fun x => by
    have := integrable_q_left V x
    simpa [hVq] using this
  have hx : ∀ x, |((pinnedLaw V lam n (pinsWith E0 x)).map (fun y => y j)).real B
      - ((pinnedLaw V lam n E0).map (fun y => y j)).real B|
      ≤ ∫ z in B, (C * lam) * (1 + q (z - x)) ∂(withDensityReal ρ) := by
    intro x
    have hψ := isField_pinField V hlam E0
    have hψ' := isField_pinField V hlam (pinsWith E0 x)
    have := hC β hβI ρ U V hVq hVγ hVM hVM' N n 1 hNa (by omega) (by omega) (fun _ => x) _ _ _ _ hψ hψ'
      (by simp [hVM', hVγ]; nlinarith [mul_nonneg hβ.le hγnn])
      (by
        simp [hVM', hVγ]
        nlinarith [mul_nonneg (sub_nonneg.2 hlamβ) hγnn])
      (fun z => by
        rw [pinField_pinsWith, sub_sub_cancel_left, abs_neg, abs_of_nonneg
          (mul_nonneg hlam (V.q_nonneg _ _))]
        simp [pinDelta, hVq, hlamdef])
      j B hB
    refine this.trans (le_of_eq ?_)
    simp [hlamdef]
  have hP1 := isProb_pinnedLaw V hlam (n + 1) E0
  have hP0 := isProb_pinnedLaw V hlam n E0
  have hPx : ∀ x, IsProbabilityMeasure (pinnedLaw V lam n (pinsWith E0 x)) :=
    fun x => isProb_pinnedLaw V hlam n _
  set c0 : ℝ := C * lam with hc0
  have hc0nn : 0 ≤ c0 := mul_nonneg hC0 hlam
  have hKc0 : 0 ≤ Kc := (Real.exp_pos _).le
  have he_eq := fun x => e_eq (μ := withDensityReal ρ) hq0 hint hc0nn B x
  have hae : ∀ x, ((pinnedLaw V lam n (pinsWith E0 x)).map (fun y => y j)) B
      ≤ ((pinnedLaw V lam n E0).map (fun y => y j)) B
        + ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂(withDensityReal ρ) := by
    intro x
    rw [← he_eq x]
    haveI := hPx x
    exact le_add_of_abs_real_le (hx x)
  have hea : ∀ x, ((pinnedLaw V lam n E0).map (fun y => y j)) B
      ≤ ((pinnedLaw V lam n (pinsWith E0 x)).map (fun y => y j)) B
        + ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂(withDensityReal ρ) := by
    intro x
    rw [← he_eq x]
    haveI := hPx x
    exact le_add_of_abs_real_le (by rw [abs_sub_comm]; exact hx x)
  have hεb := Ie_bound (μ := withDensityReal ρ) hqm hq0 hω hKc0 hωKm hc0nn hγnn hrow B hB
  obtain ⟨h1, h2⟩ := mixture_le (μ := withDensityReal ρ) (a := fun x =>
      ((pinnedLaw V lam n (pinsWith E0 x)).map (fun y => y j)) B)
    (e := fun x => ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂(withDensityReal ρ))
    hω (measurable_e hqm B) hω1 hae hea hεb
  rw [← hmix] at h1 h2
  have hεe : ENNReal.ofReal (Kc * c0 * (1 + γ₀)) * (withDensityReal ρ) B
      = ENNReal.ofReal (Kc * c0 * (1 + γ₀) * (withDensityReal ρ).real B) := by
    have hμB : (withDensityReal ρ) B = ENNReal.ofReal ((withDensityReal ρ).real B) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [hμB, ← ENNReal.ofReal_mul (by positivity)]
  rw [hεe] at h1 h2
  have hεnn : 0 ≤ Kc * c0 * (1 + γ₀) * (withDensityReal ρ).real B := by
    have : 0 ≤ (withDensityReal ρ).real B := measureReal_nonneg
    positivity
  refine (abs_real_le_of_le_add hεnn h1 h2).trans ?_
  have hK : 0 ≤ C * (β / N) * (withDensityReal ρ).real B :=
    mul_nonneg (mul_nonneg hC0 (by positivity)) measureReal_nonneg
  rw [hc0]
  calc Kc * (C * (β / N)) * (1 + γ₀) * (withDensityReal ρ).real B
      = (Kc * (1 + γ₀)) * (C * (β / N) * (withDensityReal ρ).real B) := by ring
    _ ≤ (Real.exp 4 * (1 + pinGamma βm)) * (C * (β / N) * (withDensityReal ρ).real B) :=
        mul_le_mul_of_nonneg_right key hK
    _ = Real.exp 4 * C * (1 + pinGamma βm) * (β / N) * (withDensityReal ρ).real B := by ring

theorem chain_unpinned_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ0 : 0 ≤ Λ₀)
    (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (a : ℕ) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (_ : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma β))
        (N : ℕ) (n0 : ℕ) (j : ℕ), a + 1 ≤ N → 1 ≤ n0 → n0 + j ≤ N → ∀ (B : Set (Torus d)),
        MeasurableSet B →
        |cavM V (β / N) (n0 + j) B - cavM V (β / N) n0 B|
          ≤ j * (C3 * (β / N) * (withDensityReal ρ).real B) := by
  obtain ⟨C3, hC3, hdim⟩ := dim_step_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ0 q hq0 hqm Cq hqenv hdec a
  refine ⟨C3, hC3, ?_⟩
  intro β hβI ρ U V hVq hVγ hVM hVM' hrow N n0 j hNa hn0 hN B hB
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu U.rho
  induction j with
  | zero => simp
  | succ j ih =>
    have hih := ih (by omega)
    have hn : 0 < n0 + j := by omega
    have hstep := hdim β hβI ρ U V hVq hVγ hVM hVM' hrow N (n0 + j) hNa (by omega) ⟨0, by omega⟩ ⟨0, hn⟩ B hB
    rw [coord_eq_cavM, coord_eq_cavM] at hstep
    have e : n0 + (j + 1) = n0 + j + 1 := rfl
    rw [e]
    calc |cavM V (β / N) (n0 + j + 1) B - cavM V (β / N) n0 B|
        ≤ |cavM V (β / N) (n0 + j + 1) B - cavM V (β / N) (n0 + j) B|
          + |cavM V (β / N) (n0 + j) B - cavM V (β / N) n0 B| := abs_sub_le _ _ _
      _ ≤ C3 * (β / N) * (withDensityReal ρ).real B + j * (C3 * (β / N) * (withDensityReal ρ).real B) :=
          add_le_add hstep hih
      _ = ((j + 1 : ℕ) : ℝ) * (C3 * (β / N) * (withDensityReal ρ).real B) := by push_cast; ring

set_option maxHeartbeats 1000000 in
theorem pin_comparison_proof_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ0 : 0 ≤ Λ₀) :
    ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
      (∀ z, q (-z) = q z) →
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 → periodicRiesz d s z = q z + k z + c) →
      (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
      ∀ a j : ℕ, ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₁) →
        ∀ N : ℕ, j + 2 ≤ N → ∀ h : Torus d → ℝ, Measurable h →
        (∀ x, |h x| ≤ 1) → ∀ (A : Fin a → Torus d) (i : Fin (N - j)),
          coordMarginal (pinnedReference q (fun x => β * convMeasure q (withDensityReal ρ) x + h x)
              (withDensityReal ρ) (N - j) (β / N) A) i ≪ withDensityReal ρ ∧
          weakRefMarginal q h (withDensityReal ρ) β N ≪ withDensityReal ρ ∧
          ∀ᵐ z ∂(withDensityReal ρ),
            |((coordMarginal (pinnedReference q
                  (fun x => β * convMeasure q (withDensityReal ρ) x + h x)
                  (withDensityReal ρ) (N - j) (β / N) A) i).rnDeriv (withDensityReal ρ) z).toReal -
              ((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv
                (withDensityReal ρ) z).toReal| ≤
              C * min 1 ((1 / (N : ℝ)) * (1 + ∑ k, q (z - A k))) := by
  refine ⟨pinGamma βp, pinGamma_pos (lt_of_lt_of_le hβm hββ), ?_⟩
  intro q Cq hqm hq0 hqe hdec hqenv a j
  obtain ⟨C1, hC1, hstep⟩ := pin_step_set_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ0 q hq0 hqm Cq hqenv hdec a
  obtain ⟨C3, hC3, hchain⟩ :=
    chain_unpinned_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ0 q hq0 hqm Cq hqenv hdec a
  refine ⟨max (βp * (C1 + j * C3)) (Real.exp (4 + (a : ℝ)) * (a + 1)), ?_⟩
  intro β hβI ρ U hrow N hN h hhm hh1 A i
  have hβ : 0 < β := U.hβpos
  have hρ : SmoothPosDensity ρ := U.rho
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hrowβ : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (pinGamma β) :=
    fun x => (hrow x).trans (ENNReal.ofReal_le_ofReal (pinGamma_le_of_le hβ hβI.2))
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  set K0 : ℝ := Real.exp ((β * γ₀ + 1) + 1 + β * (1 + a) * γ₀) with hK0
  have hK0pos : 0 < K0 := Real.exp_pos _
  have hbg : β * γ₀ = 1 / (16 * Real.exp 10) := beta_mul_pinGamma hβ
  have hbg1 : β * γ₀ ≤ 1 := by
    rw [hbg, div_le_one (by positivity)]
    nlinarith [Real.exp_pos 10, Real.add_one_le_exp (10 : ℝ)]
  have hK0le : K0 ≤ Real.exp (4 + (a : ℝ)) := by
    rw [hK0]; apply Real.exp_le_exp.2
    have hA : β * (1 + a) * γ₀ ≤ 1 + a := by
      have e : β * (1 + a) * γ₀ = (1 + (a : ℝ)) * (β * γ₀) := by ring
      have := mul_le_mul_of_nonneg_left hbg1 (show (0 : ℝ) ≤ 1 + a by positivity)
      linarith
    linarith
  have hCC' : β * (C1 + j * C3)
      ≤ max (βp * (C1 + j * C3)) (Real.exp (4 + (a : ℝ)) * (a + 1)) :=
    le_trans (mul_le_mul_of_nonneg_right hβI.2 (by positivity)) (le_max_left _ _)
  have hCK : K0 ≤ max (βp * (C1 + j * C3)) (Real.exp (4 + (a : ℝ)) * (a + 1)) :=
    le_trans (hK0le.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]))) (le_max_right _ _)
  have hKC : K0 * (a + 1) ≤ max (βp * (C1 + j * C3)) (Real.exp (4 + (a : ℝ)) * (a + 1)) :=
    (mul_le_mul_of_nonneg_right hK0le (by positivity)).trans (le_max_right _ _)
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨V, hVq, hVφ, hVγ, hVM, hVM'⟩ := exists_weakPotential (withDensityReal ρ) β γ₀ hγ₀ q h
    hqm hq0 hqe hrowβ hhm hh1 hβ
  have hlam : 0 ≤ β / N := by positivity
  set E0 : Empty → Torus d := fun e => e.elim with hE0
  have hnz : NeZero (N - j) := ⟨(Fin.pos i).ne'⟩
  have hid1 : coordMarginal (pinnedReference q (fun x => β * convMeasure q (withDensityReal ρ) x + h x)
      (withDensityReal ρ) (N - j) (β / N) A) i = (pinnedLaw V (β / N) (N - j) A).map (fun y => y i) := by
    rw [pinnedReference_eq_pinnedLaw (withDensityReal ρ) V q _ hVq hVφ (N - j) hlam A]
    rfl
  have hid2 : weakRefMarginal q h (withDensityReal ρ) β N
      = (pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩) := by
    unfold weakRefMarginal firstMarginal
    rw [dif_pos hNpos, pinnedReference_eq_pinnedLaw (withDensityReal ρ) V q _ hVq hVφ N hlam,
      pinnedLaw_isEmpty V (β / N) N (Fin.elim0 : Fin 0 → Torus d), pinnedLaw_isEmpty V (β / N) N E0]
  have hac1 : coordMarginal (pinnedReference q (fun x => β * convMeasure q (withDensityReal ρ) x + h x)
      (withDensityReal ρ) (N - j) (β / N) A) i ≪ withDensityReal ρ := by
    unfold pinnedReference
    exact coordMarginal_tilt_ac _ _ _ i
  have hac2 : weakRefMarginal q h (withDensityReal ρ) β N ≪ withDensityReal ρ := by
    unfold weakRefMarginal firstMarginal pinnedReference
    rw [dif_pos hNpos]
    exact coordMarginal_tilt_ac _ _ _ ⟨0, hNpos⟩
  refine ⟨hac1, hac2, ?_⟩
  rw [hid1, hid2]
  have hP1 := isProb_pinnedLaw V hlam (N - j) A
  have hP2 := isProb_pinnedLaw V hlam N E0
  -- density bounds
  have hbA : ((pinnedLaw V (β / N) (N - j) A).map (fun y => y i))
      ≤ ENNReal.ofReal K0 • withDensityReal ρ := by
    have := pinned_marginal_le (μ := withDensityReal ρ) V hβ.le hNpos (by omega : N - j ≤ N) A i
    have e : V.M + V.M' + β * (1 + (Fintype.card (Fin a) : ℝ)) * V.γ
        = (β * γ₀ + 1) + 1 + β * (1 + a) * γ₀ := by rw [hVM, hVM', hVγ]; simp
    rw [e] at this
    exact this
  have hbN : ((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩))
      ≤ ENNReal.ofReal K0 • withDensityReal ρ := by
    have := pinned_marginal_le (μ := withDensityReal ρ) V hβ.le hNpos (le_refl N) E0 ⟨0, hNpos⟩
    refine this.trans (Measure.le_iff'.2 fun B => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
    rw [hVM, hVM', hVγ]
    simp
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith [mul_nonneg hβ.le hγ₀.le, mul_nonneg (mul_nonneg hβ.le hγ₀.le) this]
  have hρA := ae_rnDeriv_le_of_le (hid1 ▸ hac1) hK0pos.le hbA
  have hρN := ae_rnDeriv_le_of_le (hid2 ▸ hac2) hK0pos.le hbN
  have hK : ∀ᵐ z ∂(withDensityReal ρ),
      |(((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).rnDeriv (withDensityReal ρ) z).toReal
        - (((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩)).rnDeriv
            (withDensityReal ρ) z).toReal| ≤ K0 := by
    filter_upwards [hρA, hρN] with z h1 h2
    rw [abs_le]
    constructor <;> nlinarith [ENNReal.toReal_nonneg (a := (((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).rnDeriv (withDensityReal ρ) z)),
      ENNReal.toReal_nonneg (a := (((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩)).rnDeriv (withDensityReal ρ) z))]
  by_cases hNa : a + 1 ≤ N
  · -- large N
    have hnN : N - j ≤ N := by omega
    have hintq : ∀ x, Integrable (fun z => q (z - x)) (withDensityReal ρ) := fun x => by
      have := integrable_q_left V x
      simpa [hVq] using this
    have hgi : Integrable (fun z => 1 + ∑ k, q (z - A k)) (withDensityReal ρ) :=
      (integrable_const (1 : ℝ)).add (integrable_finsetSum _ fun k _ => hintq (A k))
    have hg1 : ∀ z, 1 ≤ 1 + ∑ k, q (z - A k) := fun z => by
      have : 0 ≤ ∑ k, q (z - A k) := Finset.sum_nonneg fun k _ => hq0 _
      linarith
    have hC1nn := hC1
    have hjC3 : 0 ≤ (j : ℝ) * C3 := mul_nonneg (Nat.cast_nonneg j) hC3
    set Ψ : Torus d → ℝ := fun z => (C1 + j * C3) * (β / N) * (1 + ∑ k, q (z - A k)) with hΨ
    have hΨi : Integrable Ψ (withDensityReal ρ) := hgi.const_mul _
    have hset : ∀ B, MeasurableSet B →
        |((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩)).real B
          - ((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).real B|
          ≤ ∫ z in B, Ψ z ∂(withDensityReal ρ) := by
      intro B hB
      have hlamβ : β / N * a ≤ β := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hNr]
        have : (a : ℝ) ≤ N := by exact_mod_cast (by omega : a ≤ N)
        nlinarith
      have hS1 := hstep β hβI ρ U V hVq hVγ hVM hVM' N (N - j) a hNa hnN (Nat.le_succ a) A
        (pinField V (β / N) A) (pinField V (β / N) E0) _ _ (isField_pinField V hlam A)
        (isField_pinField V hlam E0)
        (by simp [hVM', hVγ]; nlinarith [mul_nonneg hγ₀.le (sub_nonneg.2 hlamβ)])
        (by simp [hVM', hVγ]; nlinarith [mul_nonneg hβ.le hγ₀.le])
        (fun z => by
          have : pinField V (β / N) E0 z - pinField V (β / N) A z
              = (β / N) * ∑ k, V.q z (A k) := by
            simp [pinField]
          rw [this, abs_of_nonneg (mul_nonneg hlam (Finset.sum_nonneg fun k _ => V.q_nonneg _ _))]
          simp [pinDelta, hVq])
        i B hB
      have e1 : ((fieldLaw V (pinField V (β / N) E0) (β / N) (N - j)).map (fun x => x i)).real B
          = cavM V (β / N) (N - j) B := coord_eq_cavM V (β / N) i B
      have hch := hchain β hβI ρ U V hVq hVγ hVM hVM' hrowβ N (N - j) j hNa (by omega) (by omega) B hB
      have e0 : N - j + j = N := by omega
      rw [e0] at hch
      have e2 : cavM V (β / N) N B
          = ((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩)).real B := by
        unfold cavM; rw [dif_pos hNpos]
      rw [e2] at hch
      have hS1' : |cavM V (β / N) (N - j) B
          - ((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).real B|
          ≤ ∫ z in B, C1 * (β / N) * (1 + ∑ k, q (z - A k)) ∂(withDensityReal ρ) := by
        rw [← e1]; exact hS1
      have hI1 : Integrable (fun z => C1 * (β / N) * (1 + ∑ k, q (z - A k))) (withDensityReal ρ) :=
        hgi.const_mul _
      have hI2 : Integrable (fun z => ((j : ℝ) * C3 * (β / N)) * (1 + ∑ k, q (z - A k)))
          (withDensityReal ρ) := hgi.const_mul _
      have hdec : ∀ z, Ψ z = C1 * (β / N) * (1 + ∑ k, q (z - A k))
          + ((j : ℝ) * C3 * (β / N)) * (1 + ∑ k, q (z - A k)) := fun z => by simp only [hΨ]; ring
      have hintΨ : ∫ z in B, Ψ z ∂(withDensityReal ρ)
          = (∫ z in B, C1 * (β / N) * (1 + ∑ k, q (z - A k)) ∂(withDensityReal ρ))
            + ∫ z in B, ((j : ℝ) * C3 * (β / N)) * (1 + ∑ k, q (z - A k)) ∂(withDensityReal ρ) := by
        simp_rw [hdec]
        exact integral_add hI1.integrableOn hI2.integrableOn
      have hlow : ((j : ℝ) * (C3 * (β / N) * (withDensityReal ρ).real B))
          ≤ ∫ z in B, ((j : ℝ) * C3 * (β / N)) * (1 + ∑ k, q (z - A k)) ∂(withDensityReal ρ) := by
        have hc : 0 ≤ (j : ℝ) * C3 * (β / N) := by positivity
        have := setIntegral_mono (μ := withDensityReal ρ) (s := B)
          (f := fun _ => ((j : ℝ) * C3 * (β / N))) (g := fun z => ((j : ℝ) * C3 * (β / N)) * (1 + ∑ k, q (z - A k)))
          (integrableOn_const (by exact measure_ne_top _ _)) hI2.integrableOn
          (fun z => by
            have := hg1 z
            nlinarith)
        rw [setIntegral_const, smul_eq_mul] at this
        calc ((j : ℝ) * (C3 * (β / N) * (withDensityReal ρ).real B))
            = (withDensityReal ρ).real B * ((j : ℝ) * C3 * (β / N)) := by ring
          _ ≤ _ := this
      calc |((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩)).real B
            - ((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).real B|
          ≤ |((pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩)).real B - cavM V (β / N) (N - j) B|
            + |cavM V (β / N) (N - j) B - ((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).real B| :=
            abs_sub_le _ _ _
        _ ≤ ((j : ℝ) * (C3 * (β / N) * (withDensityReal ρ).real B))
            + ∫ z in B, C1 * (β / N) * (1 + ∑ k, q (z - A k)) ∂(withDensityReal ρ) := by
            exact add_le_add hch hS1'
        _ ≤ ∫ z in B, Ψ z ∂(withDensityReal ρ) := by rw [hintΨ]; linarith
    have hν1 := hid1 ▸ hac1
    have hν2 := hid2 ▸ hac2
    have hsetρ := ae_abs_rnDeriv_sub_le (μ := withDensityReal ρ) hν1 hν2 hΨi hset
    filter_upwards [hsetρ, hK] with z hz1 hz2
    rw [abs_sub_comm] at hz1
    refine min_aux (t := |(((pinnedLaw V (β / N) (N - j) A).map (fun y => y i)).rnDeriv
        (withDensityReal ρ) z).toReal - (((pinnedLaw V (β / N) N E0).map
          (fun y => y ⟨0, hNpos⟩)).rnDeriv (withDensityReal ρ) z).toReal|)
      (K := K0) (C' := β * (C1 + j * C3)) (x := (1 / (N : ℝ)) * (1 + ∑ k, q (z - A k)))
      ?_ hz2 ?_ hCC' hCK
    · refine hz1.trans (le_of_eq ?_)
      simp only [hΨ]; field_simp
    · have := hg1 z
      have : 0 ≤ ∑ k, q (z - A k) := Finset.sum_nonneg fun k _ => hq0 _
      positivity
  · -- small N
    push Not at hNa
    filter_upwards [hK] with z hz
    refine small_aux (a := a) (N := N) (by omega) (by omega) hz hK0pos.le ?_ hKC
    have h0 : 0 ≤ ∑ k, q (z - A k) := Finset.sum_nonneg fun k _ => hq0 _
    rw [one_div]
    have : (1 : ℝ) / N ≤ 1 / N * (1 + ∑ k, q (z - A k)) := by
      nlinarith [one_div_nonneg.2 hNr.le]
    simpa [one_div] using this
end HRS.ME.NfU
