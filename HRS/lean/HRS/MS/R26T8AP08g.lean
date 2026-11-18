import HRS.MS.R26T8AP08f

/-!
# S8.2 T8A P08 (part g): Fubini for a conormal pair function
`r26t8a_f25_fubini`: `R` conormal of order `σ < d`, `μ = ρ dx`, `ρ` continuous probability density with `ρ ≤ Kρ (1+|y|)^(-(M+d+1))`:
`R` is `μ⊗μ`-integrable and the two iterated integrals agree; also every row/column is integrable with a uniform bound `B jb^M`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_f25_fubini (hd : 2 ≤ d) (b : ℕ) {σ M : ℝ} (hM : 0 ≤ M) (hσd : σ < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hρc : Continuous ρ) {Kρ : ℝ} (hKρ0 : 0 ≤ Kρ)
    (hK : ∀ y, ρ y ≤ Kρ * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1))) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ {k : ℕ} {A : ℝ}, 0 ≤ A → ∀ {R : Euc d → Euc d → ℝ}, Conormal k b M σ A R →
      Integrable (fun p : Euc d × Euc d => R p.1 p.2)
        ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ∧
      (∀ x, Integrable (R x) (HRS.Whole.withDensityReal ρ)) ∧
      (∀ x, ∫ y, ‖R x y‖ ∂(HRS.Whole.withDensityReal ρ) ≤ Bq * A * jbracket x ^ M) ∧
      ∫ x, ∫ y, R x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) =
        ∫ y, ∫ x, R x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  haveI hprob := s85_isProb hρ
  obtain ⟨sp, hsp⟩ : ∃ sp : ℝ, sp = max σ 0 := ⟨_, rfl⟩
  have hsp0 : 0 ≤ sp := by rw [hsp]; exact le_max_right _ _
  have hsp1 : σ ≤ sp := by rw [hsp]; exact le_max_left _ _
  have hspd : sp < d := by rw [hsp]; exact max_lt hσd (by linarith)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (sp + d) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hσs : σ < s := by rw [hs]; linarith
  obtain ⟨C, hC0, hC⟩ := r26t8a_f25_pt_bound (d := d) b hσs hs0
  obtain ⟨Ω, hΩ0, hΩ⟩ := r26t8a_f25_conv_bound hd hs0 hsd
  set a : Euc d → ℝ := fun y => ρ y * jbracket y ^ M with ha
  have ha0 : ∀ y, 0 ≤ a y := fun y =>
    mul_nonneg (hρ.nonneg y) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have haK : ∀ y, a y ≤ Kρ * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro y
    have h1 : jbracket y ^ M ≤ (1 + ‖y‖) ^ M :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM
    have h2 : (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)) * (1 + ‖y‖) ^ M = (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; ring
    calc a y = ρ y * jbracket y ^ M := rfl
      _ ≤ (Kρ * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1))) * (1 + ‖y‖) ^ M :=
          mul_le_mul (hK y) h1 (Real.rpow_nonneg (s83_jb_pos y).le _) (by
            have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) (-(M + (d : ℝ) + 1)); positivity)
      _ = Kρ * ((1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)) * (1 + ‖y‖) ^ M) := by ring
      _ = Kρ * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by rw [h2]
  have haK1 : ∀ y, a y ≤ Kρ := fun y => by
    refine (haK y).trans ?_
    have : (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)
    nlinarith
  have hrank : (Module.finrank ℝ (Euc d) : ℝ) < (d : ℝ) + 1 := by simp
  have hai : Integrable a := by
    refine Integrable.mono' ((integrable_one_add_norm hrank).const_mul Kρ)
      (hρc.mul (s85_jb_rpow_continuous M)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (ha0 y)]; exact haK y
  have hac : Continuous a := hρc.mul (s85_jb_rpow_continuous M)
  have hI0 : 0 ≤ ∫ y, a y := integral_nonneg ha0
  refine ⟨C * (3 * (∫ y, a y) + Kρ * Ω), mul_nonneg hC0 (by positivity), ?_⟩
  intro k A hA R hR
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ with hμ
  have hcR : ContinuousOn (Function.uncurry R) {p : Euc d × Euc d | p.1 ≠ p.2} := hR.1.continuousOn
  have hbd := hC hA hR
  have hJ0 : 0 ≤ (∫ y, a y) := hI0
  set Bq : ℝ := C * (3 * (∫ y, a y) + Kρ * Ω) with hBq
  have hae0 : ∀ x : Euc d, ∀ᵐ y : Euc d ∂volume, y ≠ x := fun x => compl_mem_ae_iff.2 (measure_singleton x)
  have hrowaes : ∀ x : Euc d, AEStronglyMeasurable (fun y => ρ y * R x y) volume := by
    intro x
    refine r26t8a_p10a_aesm hd x ?_
    have h1 : ContinuousOn (fun y => R x y) {x}ᶜ := by
      have := hcR.comp (f := fun y : Euc d => (x, y)) (s := ({x}ᶜ : Set (Euc d)))
        (continuous_const.prodMk continuous_id).continuousOn
        (fun y hy => show x ≠ y from fun h => hy h.symm)
      exact this
    exact hρc.continuousOn.mul h1
  have hrow : ∀ x : Euc d, Integrable (fun y => ρ y * ‖R x y‖) ∧
      ∫ y, ρ y * ‖R x y‖ ≤ Bq * A * jbracket x ^ M := by
    intro x
    have hjx : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
    obtain ⟨hI, hIb⟩ := hΩ a Kρ ha0 haK1 hac hai x
    set Dm : Euc d → ℝ := fun y => A * C * jbracket x ^ M * (a y * (1 + ‖x - y‖ ^ (-s))) with hDm
    have hDi : Integrable Dm := hI.const_mul _
    have hpt : ∀ y, y ≠ x → ρ y * ‖R x y‖ ≤ Dm y := by
      intro y hy
      have h1 := hbd x y (Ne.symm hy)
      have h2 : ‖R x y‖ ≤ A * C * (jbracket x ^ M * jbracket y ^ M) * (1 + ‖x - y‖ ^ (-s)) := h1
      have := mul_le_mul_of_nonneg_left h2 (hρ.nonneg y)
      calc ρ y * ‖R x y‖ ≤ ρ y * (A * C * (jbracket x ^ M * jbracket y ^ M) * (1 + ‖x - y‖ ^ (-s))) := by
            exact this
        _ = Dm y := by rw [hDm, ha]; ring
    have hmeas : AEStronglyMeasurable (fun y => ρ y * ‖R x y‖) volume := by
      have := (hrowaes x).norm
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
    have hint : Integrable (fun y => ρ y * ‖R x y‖) :=
      Integrable.mono' hDi hmeas (by
        filter_upwards [hae0 x] with y hy
        rw [Real.norm_of_nonneg (mul_nonneg (hρ.nonneg y) (norm_nonneg _))]
        exact hpt y hy)
    refine ⟨hint, ?_⟩
    refine (integral_mono_ae hint hDi (by filter_upwards [hae0 x] with y hy using hpt y hy)).trans ?_
    rw [hDm, integral_const_mul]
    have hAC : 0 ≤ A * C * jbracket x ^ M := by positivity
    calc A * C * jbracket x ^ M * ∫ y, a y * (1 + ‖x - y‖ ^ (-s)) ≤
          A * C * jbracket x ^ M * (3 * (∫ y, a y) + Kρ * Ω) := mul_le_mul_of_nonneg_left hIb hAC
      _ = Bq * A * jbracket x ^ M := by rw [hBq]; ring
  have hrowμ : ∀ x : Euc d, Integrable (R x) μ := by
    intro x
    rw [hμ, r26t8a_f25_wd_integrable hρ]
    refine Integrable.mono' (hrow x).1 (hrowaes x) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hρ.nonneg y)]
  have hnorm : ∀ x : Euc d, ∫ y, ‖R x y‖ ∂μ ≤ Bq * A * jbracket x ^ M := by
    intro x
    rw [hμ, r26t8a_f25_wd_integral hρ]
    exact (hrow x).2
  -- measurability on the product
  have hfm : AEStronglyMeasurable (fun p : Euc d × Euc d => R p.1 p.2) (μ.prod μ) := by
    have hs : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    have h1 : AEStronglyMeasurable (Function.uncurry R) ((μ.prod μ).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hcR.aestronglyMeasurable hs
    have h2 : (μ.prod μ).restrict {p : Euc d × Euc d | p.1 ≠ p.2} = μ.prod μ :=
      Measure.restrict_eq_self_of_ae_mem (r26t8a_f25_diag_null hd hρ)
    rw [h2] at h1
    exact h1
  have hjbI : Integrable (fun x => jbracket x ^ M) μ := by
    rw [hμ, r26t8a_f25_wd_integrable hρ]
    exact hai
  have hprod : Integrable (fun p : Euc d × Euc d => R p.1 p.2) (μ.prod μ) := by
    rw [integrable_prod_iff hfm]
    refine ⟨Filter.Eventually.of_forall hrowμ, ?_⟩
    refine Integrable.mono' (hjbI.const_mul (Bq * A)) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hfm.norm).integral_prod_right'
    · rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      exact hnorm x
  refine ⟨hprod, hrowμ, hnorm, ?_⟩
  exact integral_integral_swap (f := fun x y => R x y) hprod

end HRS.MS.R26T8A
