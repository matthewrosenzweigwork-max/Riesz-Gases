import HRS.ME.NfUPU4b

/-!
# Packet PU7a (helpers for the uniform `exists_setting`)

* `gL_zero_nonneg_of_gram`, `abs_gL_le_of_gram`: the two facts `RefHyp.gL_zero_nonneg`, `RefHyp.abs_gL_le`
  from the Gram representation `gL (x - y) = ⟪Ψ x, Ψ y⟫` alone (no density, no calibration).
* `gibbs_le_smul_mono`: monotonicity of `μ ≤ ENNReal.ofReal a • ν` in the constant `a`.
* `reference_marginal_linf_ev_unifG`: `reference_marginal_linf_ev_unif` (`HRS/ME/NfUPU4b.lean:32`) with the
  existential `∃ γ₀ > 0` moved in front of the kernel `q`. The witness is `pinGamma βp` in the proof of the
  original (`NfUPU4b.lean:62`), which does not depend on `q`; the statement is otherwise identical. This is
  needed because the split parameters (`exists_split_params_unif`) must be chosen with the row bound `γ₀`
  before the kernel `q` exists. The proof body is the body of `reference_marginal_linf_ev_unif`, unchanged.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.NfU

open HRS HRS.PinAux HRS.External HRS.External.RefMarg HRS.ME.PmU

variable {d : ℕ}

/-- `0 ≤ gL 0` from the Gram representation. -/
theorem gL_zero_nonneg_of_gram {M : ℕ} {gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
    (hΨ : ∀ x y, gL (x - y) = inner ℝ (Ψ x) (Ψ y)) : 0 ≤ gL 0 := by
  have h := hΨ 0 0
  rw [sub_self] at h
  rw [h]
  exact real_inner_self_nonneg

/-- `|gL z| ≤ gL 0` from the Gram representation (the content of `RefHyp.abs_gL_le`). -/
theorem abs_gL_le_of_gram {M : ℕ} {gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
    (hΨ : ∀ x y, gL (x - y) = inner ℝ (Ψ x) (Ψ y)) (z : Torus d) : |gL z| ≤ gL 0 := by
  have hsq : ∀ x, gL 0 = ‖Ψ x‖ ^ 2 := by
    intro x
    have h := hΨ x x
    rw [sub_self] at h
    rw [h, real_inner_self_eq_norm_sq]
  have hnorm : ∀ x, ‖Ψ x‖ = Real.sqrt (gL 0) := by
    intro x
    rw [hsq x, Real.sqrt_sq (norm_nonneg _)]
  have h1 := hΨ z 0
  rw [sub_zero] at h1
  rw [h1]
  calc |inner ℝ (Ψ z) (Ψ 0)| ≤ ‖Ψ z‖ * ‖Ψ 0‖ := abs_real_inner_le_norm _ _
    _ = Real.sqrt (gL 0) * Real.sqrt (gL 0) := by rw [hnorm z, hnorm 0]
    _ = gL 0 := Real.mul_self_sqrt (gL_zero_nonneg_of_gram hΨ)

/-- Monotonicity of a Gibbs bound in its constant. -/
theorem gibbs_le_smul_mono {X : Type*} [MeasurableSpace X] {μ ν : Measure X} {a b : ℝ}
    (h : μ ≤ ENNReal.ofReal a • ν) (hab : a ≤ b) : μ ≤ ENNReal.ofReal b • ν := by
  refine h.trans ?_
  rw [Measure.le_iff']
  intro A
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  gcongr

/-- Uniform-in-`(β, ρ, hN)` version of `reference_marginal_linf_ev` with the row constant `γ₀` chosen
before the kernel `q` (the witness `pinGamma βp` of `reference_marginal_linf_ev_unif`). -/
theorem reference_marginal_linf_ev_unifG {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    {βm βp c₀ Λ₀ : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ0 : 0 ≤ Λ₀) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
    (∀ z, q (-z) = q z) →
    (∃ k0 : Torus d → ℝ, Torus.IsSmooth k0 ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k0 z + c) →
    (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
    ∀ (k : Torus d → ℝ) (Ck : ℝ), Measurable k → (∀ z, |k z| ≤ Ck) →
    ∀ (Ns : ℕ), 2 ≤ Ns → ∀ (C₁ : ℝ) (Nthr : ℝ → ℕ),
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      RhoU d βm βp c₀ Λ₀ β ρ →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₀) →
      ∀ hN : ℕ → Torus d → ℝ,
      (∀ N, Ns ≤ N → Measurable (hN N) ∧ ∀ x, |hN N x| ≤ 1) →
      (∀ N, Ns ≤ N → weakRefMarginal q (hN N) (withDensityReal ρ) β N ≪ withDensityReal ρ) →
      (∀ N, Ns ≤ N → ∃ cN : ℝ, ∀ x, hN N x = -β * ∫ y, k (x - y) *
          (((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1)
            ∂(withDensityReal ρ) + cN) →
      (∀ N, Ns ≤ N → eLpNorm (fun y => ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C₁ * deltaN d s N)) →
      (∀ ε > 0, ∀ N, Nthr ε ≤ N → ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ ε) →
      ∀ N, Ns ≤ N → ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * deltaN d s N := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  refine ⟨pinGamma βp, pinGamma_pos hβp, fun q Cq hqm hq0 hqe hdec hqenv k Ck hkm hkb Ns hNs C₁ Nthr => ?_⟩
  obtain ⟨Eδ, N₁, hEδ, hstep⟩ := linf_one_step_unif hd hcrit hβm hββ hΛ0 q hq0 hqm hqe Cq hqenv hdec
    k Ck hkm hkb C₁
  have htend := (tendsto_deltaN (d := d) hd hs0 hsd).const_mul Eδ
  have hev := htend.eventually (gt_mem_nhds (by norm_num : Eδ * 0 < 1 / 32))
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 hev
  set N₂ : ℕ := max (max (Nthr (1 / 2)) N₁) (max N₃ Ns) with hN₂
  refine ⟨max (8 * Eδ) (max 1 (Real.exp 10) * N₂), ?_⟩
  intro β hβI ρ U hrowβp hN hNb hac hcal hL2 hunif
  have hβ : 0 < β := U.hβpos
  have hβle : β ≤ βp := U.hβle
  have hprob : IsProbabilityMeasure (withDensityReal ρ) :=
    PoleCavityAux.isProbabilityMeasure_mu U.rho
  have hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (pinGamma β) :=
    fun x => (hrowβp x).trans (ENNReal.ofReal_le_ofReal (pinGamma_le_of_le hβ hβle))
  have hstep := hstep β hβI ρ U hrowβp
  have hN₀ := hunif (1 / 2) (by norm_num)
  intro N hN2
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg hcrit (by omega)
  have hδ1 : 1 / (N : ℝ) ≤ deltaN d s N := deltaN_ge_inv hcrit (by omega)
  by_cases hbig : N₂ ≤ N
  · -- large N: iterate the one-step estimate
    have hN0 : Nthr (1 / 2) ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
    have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbig
    have hε : Eδ * deltaN d s N < 1 / 32 := by
      have := hN₃ N hN3
      simpa using this
    obtain ⟨cN, hcN⟩ := hcal N hN2
    set θ : ℝ := 4 * (β * pinGamma β) with hθ
    have hg : β * pinGamma β ≤ 1 / 16 := beta_mul_pinGamma_le_unif hβ
    have hg0 : 0 ≤ β * pinGamma β := mul_nonneg hβ.le (pinGamma_pos hβ).le
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hθ1 : θ ≤ 1 / 4 := by rw [hθ]; linarith
    have hind : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ M ≤ 1 / 2 ∧ M ≤ θ ^ m / 2 + 8 * (Eδ * deltaN d s N) ∧
        ∀ᵐ y ∂(withDensityReal ρ), |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ M := by
      intro m
      induction m with
      | zero =>
        refine ⟨1 / 2, by norm_num, le_rfl, ?_, hN₀ N hN0⟩
        have : 0 ≤ Eδ * deltaN d s N := mul_nonneg hEδ hδ0
        simp only [pow_zero]; linarith
      | succ m ih =>
        obtain ⟨M, hM0, hM1, hMθ, hMae⟩ := ih
        have hstp := hstep (hN N) (hNb N hN2).1 (hNb N hN2).2 N hN1 (by omega) cN hcN
          (hL2 N hN2) (by linarith) M hM0 hM1 hMae
        have hε0 : 0 ≤ Eδ * deltaN d s N := mul_nonneg hEδ hδ0
        refine ⟨4 * (β * pinGamma β * M + Eδ * deltaN d s N), by positivity, ?_, ?_, hstp⟩
        · nlinarith
        · have : θ ^ (m + 1) = θ * θ ^ m := by ring
          rw [this]
          rw [hθ] at hθ0 hθ1 ⊢
          nlinarith [mul_nonneg hθ0 hε0, mul_le_mul_of_nonneg_left hMθ hθ0]
    have hall : ∀ᵐ y ∂(withDensityReal ρ), ∀ m : ℕ,
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1|
          ≤ θ ^ m / 2 + 8 * (Eδ * deltaN d s N) := by
      rw [ae_all_iff]
      intro m
      obtain ⟨M, -, -, hM, hae⟩ := hind m
      filter_upwards [hae] with y hy
      exact hy.trans hM
    filter_upwards [hall] with y hy
    have hlim : Filter.Tendsto (fun m : ℕ => θ ^ m / 2 + 8 * (Eδ * deltaN d s N)) Filter.atTop
        (nhds (0 / 2 + 8 * (Eδ * deltaN d s N))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 (by linarith)).div_const 2).add_const _
    have := ge_of_tendsto hlim (Filter.Eventually.of_forall hy)
    refine this.trans ?_
    rw [zero_div, zero_add]
    calc 8 * (Eδ * deltaN d s N) = (8 * Eδ) * deltaN d s N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  · -- small N: the density is bounded by `exp 10` uniformly
    push Not at hbig
    have hK := weakRef_density_le β hβ ρ U.rho q hq0 hqm hqe hrow (hN N) (hNb N hN2).1
      (hNb N hN2).2 N (by omega)
    have hKu : Real.exp ((β * pinGamma β + 1) + 1 + β * (1 + 0) * pinGamma β) ≤ Real.exp 10 := by
      apply Real.exp_le_exp.2
      have e : β * (1 + 0) * pinGamma β = β * pinGamma β := by ring
      rw [e]
      linarith [beta_mul_pinGamma_le_unif hβ]
    filter_upwards [hK] with y hy
    have hnn : 0 ≤ ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
        (withDensityReal ρ) y).toReal := ENNReal.toReal_nonneg
    have h1 : |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1|
        ≤ max 1 (Real.exp 10) := by
      rw [abs_le]
      constructor
      · linarith [le_max_left 1 (Real.exp 10)]
      · linarith [le_max_right 1 (Real.exp 10), le_max_left 1 (Real.exp 10)]
    refine h1.trans ?_
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hN2r : (N : ℝ) ≤ N₂ := by exact_mod_cast hbig.le
    have hmax : 1 ≤ max 1 (Real.exp 10) := le_max_left _ _
    have h2 : max 1 (Real.exp 10) ≤ (max 1 (Real.exp 10) * N₂) * (1 / (N : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ (by linarith)]
      nlinarith
    calc max 1 (Real.exp 10) ≤ (max 1 (Real.exp 10) * N₂) * (1 / (N : ℝ)) := h2
      _ ≤ (max 1 (Real.exp 10) * N₂) * deltaN d s N :=
          mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0

end HRS.ME.NfU

end
