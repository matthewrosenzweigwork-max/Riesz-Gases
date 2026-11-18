import HRS.Equilibrium.MarginalDensity

/-!
# EQ-MARG-U, part 1: uniform (in `ρ ≤ Λ`) kernel data, calibration smallness and pole variance clause

`equilibrium_marginal_L2` needs the constant of Prop. 4.2 to be uniform along the thermal densities
`ρ_β`, `β ∈ [β₋,β₊]`.  The proof of 4.2 depends on `ρ` only through the upper bound `Λ ≥ ρ`; the
parts that were stated with `∃ C` after `ρ` are re-proved here with `∃ C` before `∀ ρ ≤ Λ`
(same proofs, with the constants taken from `Λ`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace EqMarg

open HRS.External HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

/-- Uniform kernel data: `B`, `Cc` depend only on `Λ`. -/
theorem eqmarg_kerData (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ B Cc : ℝ, 0 ≤ B ∧ 0 ≤ Cc ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      KerData (periodicRiesz d s) (withDensityReal ρ) B Cc := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hgi := KernelAux.integrable_periodicRiesz hd hs0 hsd
  set g := periodicRiesz d s with hg
  set C0 : ℝ := (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal ‖g y‖).toReal with hC0
  refine ⟨max B 0, |C0|, le_max_right _ _, abs_nonneg _, fun ρ hρ hΛ => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hC : ∀ x, |convMeasure g (withDensityReal ρ) x| ≤ C0 := by
    intro x
    have h1 := norm_integral_le_lintegral_norm (μ := withDensityReal ρ) (fun y => g (x - y))
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (ENNReal.toReal_mono ?_ (KernelAux2.lintegral_conv_le ρ Λ hΛ
      (fun z => ENNReal.ofReal ‖g z‖) x))
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have := hgi.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    simp only [← ofReal_norm] at this
    exact this.ne
  have hint : ∀ x, Integrable (fun y => g (x - y)) (withDensityReal ρ) := by
    intro x
    refine ⟨(hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖g z‖ₑ) x) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hgi.hasFiniteIntegral
  have hCc : ∀ x, |convMeasure g (withDensityReal ρ) x| ≤ |C0| := fun x => (hC x).trans (le_abs_self _)
  refine
    { meas := hgm
      even := fun z => periodicRiesz_neg z
      lower := hB'
      int := hint
      int2 := ?_
      conv := hCc }
  have hm : AEStronglyMeasurable (fun q : Torus d × Torus d => g (q.1 - q.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    (hgm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨Filter.Eventually.of_forall hint, ?_⟩
  have hmeas : Measurable fun x => ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) := by
    have : StronglyMeasurable (Function.uncurry fun x y : Torus d => ‖g (x - y)‖) :=
      (hgm.comp (measurable_fst.sub measurable_snd)).norm.stronglyMeasurable
    exact (this.integral_prod_right' (ν := withDensityReal ρ)).measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable (|C0| + 2 * max B 0)
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 : ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) ≤
      ∫ y, (g (x - y) + 2 * max B 0) ∂(withDensityReal ρ) := by
    refine integral_mono (hint x).norm ((hint x).add (integrable_const _)) fun y => ?_
    have := hB' (x - y)
    have h0 := le_max_right B 0
    simp only [Real.norm_eq_abs]
    rcases le_total 0 (g (x - y)) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  rw [integral_add (hint x) (integrable_const _)] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have h2 : ∫ y, g (x - y) ∂(withDensityReal ρ) = convMeasure g (withDensityReal ρ) x := rfl
  have h3 := hCc x
  have h4 : 0 ≤ ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) := integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h4]
  have := le_abs_self (convMeasure g (withDensityReal ρ) x)
  linarith

open InformationTheory HRS.External.Entropy in
/-- Quantitative form of `Entropy.tendsto_tvDist_firstMarginal`: for an exchangeable law with
`KL(R ‖ μ^{⊗(N+1)}) ≤ K`, the first marginal is within `√(K/(2(N+1)))` of `μ` in total variation. -/
theorem eqmarg_tv_of_kl {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ : Measure E) [IsProbabilityMeasure μ] {N : ℕ} (R : Measure (Fin (N + 1) → E))
    [IsProbabilityMeasure R] (hex : HRS.External.Entropy.IsExchangeable R) {K : ℝ} (hK : 0 ≤ K)
    (hkl : klDiv R (Measure.pi fun _ : Fin (N + 1) => μ) ≤ ENNReal.ofReal K) :
    tvDist (R.map fun x => x 0) μ ≤ Real.sqrt (K / ((N : ℝ) + 1) / 2) := by
  have h := hex.mul_klDiv_marginal_le μ 0 R
  have : IsProbabilityMeasure (R.map fun x : Fin (N + 1) → E => x 0) := inferInstance
  have h2 := h.trans hkl
  have hne : klDiv (R.map fun x : Fin (N + 1) → E => x 0) μ ≠ ⊤ := by
    intro htop
    rw [htop] at h2
    simp at h2
  have h3 : (((N + 1 : ℕ) : ℝ≥0∞) * klDiv (R.map fun x : Fin (N + 1) → E => x 0) μ).toReal ≤ K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    refine this.trans ?_
    exact (ENNReal.toReal_ofReal hK).le
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h3
  push_cast at h3
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h4 : (klDiv (R.map fun x : Fin (N + 1) → E => x 0) μ).toReal ≤ K / ((N : ℝ) + 1) := by
    rw [le_div_iff₀ hN]; linarith
  refine (tvDist_le_sqrt_klDiv _ _ hne).trans ?_
  gcongr

theorem eqmarg_aN_nonneg (d : ℕ) (s : ℝ) (N : ℕ) : 0 ≤ aN d s N := by
  unfold aN
  refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  split_ifs
  · have := Real.log_natCast_nonneg N
    linarith
  · norm_num

open HRS.External.Entropy HeatSplit in
/-- `KL(R⁰_N ‖ μ^{⊗N}) ≤ β N C a_N` with `C`, `N₀` independent of `β` and of `ρ ≤ Λ`. -/
theorem eqmarg_klDiv_R0small (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ β : ℝ, 0 ≤ β → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
        InformationTheory.klDiv (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) N)
            (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
          ENNReal.ofReal (β * N * (C * aN d s N)) := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := RefSmall.modulatedEnergy_weakSplit_ge hd hs0 hsd hτ L hΛ1
  refine ⟨C, hC, N₀, hN₀, fun β hβ ρ hρ hΛ N hN => ?_⟩
  exact RefSmall.klDiv_R0small_le (by omega) (RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L) hρ hΛ hβ
    (by omega) (A := C * aN d s N) (fun X hX => h ρ hρ hΛ N hN X hX)

open HRS.External.Calib HeatSplit HRS.External.PoleVar HRS.External.Entropy in
/-- Uniform smallness of the calibration field: `n₀` depends only on the split data and `Λ`. -/
theorem eqmarg_small_calib (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) (βp : ℝ) (hβp : 0 < βp) :
    ∃ n₀ : ℕ, ∀ β : ℝ, 0 < β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ n ≥ n₀, ∀ x : Torus d,
      |inner ℝ (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n) (Xi (withDensityReal ρ) Ψ x)| ≤ 1 := by
  obtain ⟨C, hC, N₀, hN₀, hkl⟩ := eqmarg_klDiv_R0small hd hs0 hsd hτ L hΛ1
  set Bd : ℝ := 2 * Real.sqrt ((weakSplit d s τ L).gL 0) with hBd
  have hB0 : 0 ≤ Bd := by positivity
  have h1 : Tendsto (fun N : ℕ => aN d s (N + 1)) atTop (𝓝 0) :=
    (RefSmall.tendsto_aN (by omega) hs0 hsd).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun N : ℕ => 2 * βp * Bd ^ 2 * Real.sqrt (βp * (C * aN d s (N + 1)) / 2))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => βp * (C * aN d s (N + 1)) / 2) atTop (𝓝 0) := by
      simpa using ((h1.const_mul C).const_mul βp).div_const 2
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    simpa [Function.comp_def] using h3.const_mul (2 * βp * Bd ^ 2)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds one_pos))
  refine ⟨max N₀ N₁ + 1, fun β hβ hβP ρ hρ hΛ n hn x => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hNN : max N₀ N₁ ≤ N := by omega
  have hN0 : N₀ ≤ N + 1 := by omega
  have hN1 : N₁ ≤ N := by omega
  haveI := isProb_withDensityReal hρ
  have hq := RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ
  haveI : IsProbabilityMeasure
      (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)) :=
    hq.isProb_R0small hρ hΛ hβ.le (N + 1)
  have hmean := RefSmall.meanFeature_eq_firstMarginal
    (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1))
    (RefSmall.R0small_isExchangeable hq.meas hq.even β _ (N + 1)) h.measurable_Xi
    (B := Bd) (fun x => h.norm_Xi_le x)
  have hnorm := RefSmall.norm_integral_sub_le_two_mul_tvDist
    ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ) h.measurable_Xi hB0 (fun x => h.norm_Xi_le x)
  rw [h.integral_Xi, sub_zero] at hnorm
  rw [← hmean] at hnorm
  have ht := h.tN_norm_le hβ (N := N + 1) (Nat.succ_pos N)
  rw [integral_empXi_R0 h hβ.le (Nat.succ_pos N)] at ht
  have h2 : ‖tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (N + 1)‖ ≤ β * (2 * Bd * tvDist
      ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ)) := ht.trans (mul_le_mul_of_nonneg_left hnorm hβ.le)
  have haN := eqmarg_aN_nonneg d s (N + 1)
  have hK : 0 ≤ β * ((N + 1 : ℕ) : ℝ) * (C * aN d s (N + 1)) := by positivity
  have htv := eqmarg_tv_of_kl (withDensityReal ρ)
    (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1))
    (RefSmall.R0small_isExchangeable hq.meas hq.even β _ (N + 1)) hK
    (hkl β hβ.le ρ hρ hΛ (N + 1) hN0)
  have e : β * ((N + 1 : ℕ) : ℝ) * (C * aN d s (N + 1)) / ((N : ℝ) + 1) / 2 =
      β * (C * aN d s (N + 1)) / 2 := by
    push_cast
    field_simp
  rw [e] at htv
  have htv0 := tvDist_nonneg
    ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ)
  have h3 := hN₁ N hN1
  calc |inner ℝ (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (N + 1)) (Xi (withDensityReal ρ) Ψ x)|
      ≤ ‖tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (N + 1)‖ * ‖Xi (withDensityReal ρ) Ψ x‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * Bd * tvDist
        ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
        (withDensityReal ρ))) * Bd :=
        mul_le_mul h2 (h.norm_Xi_le x) (norm_nonneg _) (by positivity)
    _ = 2 * β * Bd ^ 2 * tvDist
        ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
        (withDensityReal ρ) := by ring
    _ ≤ 2 * β * Bd ^ 2 * Real.sqrt (β * (C * aN d s (N + 1)) / 2) :=
        mul_le_mul_of_nonneg_left htv (by positivity)
    _ ≤ 2 * βp * Bd ^ 2 * Real.sqrt (βp * (C * aN d s (N + 1)) / 2) := by
        have hCa : 0 ≤ C * aN d s (N + 1) := by positivity
        gcongr
    _ ≤ 1 := h3.le

open HRS.External.Calib HeatSplit HRS.External.PoleVar HRS.External.Entropy in
/-- Choice of the split for the density bound `Λ0`: `Λ = max Λ0 1`. -/
theorem eqmarg_split_params (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βp : ℝ) (hβp : 0 < βp) (Λ0 : ℝ) :
    ∃ (τ : ℝ) (L : ℕ) (Λ : ℝ) (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      0 < τ ∧ τ ≤ 1 ∧ 1 ≤ Λ ∧ Λ0 ≤ Λ ∧
      (∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      0 ≤ (weakSplit d s τ L).c ∧ 0 ≤ (weakSplit d s τ L).gL 0 ∧
      βp * (Λ * (weakSplit d s τ L).c) ≤ 1 / (16 * Real.exp 3) := by
  set Λ := max Λ0 1 with hΛ
  have hΛpos : 0 < Λ := lt_max_of_lt_right one_pos
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hΛb : Λ0 ≤ Λ := le_max_left _ _
  set u : ℝ := 1 / (16 * Real.exp 3) with hu
  have hu0 : 0 < u := by positivity
  obtain ⟨τ, hτ, hτ1, L₀, hL₀⟩ := weakSplit_small hd hs0 hsd (ε := u / (βp * Λ)) (by positivity)
  obtain ⟨M, Ψ, -, hΨ, -⟩ := RefSmall.exists_continuous_features_weakSplit hd hs0 hsd hτ L₀
  have hg0 : 0 ≤ (weakSplit d s τ L₀).gL 0 := by
    have := hΨ 0 0
    rw [sub_self] at this
    rw [this]; exact real_inner_self_nonneg
  obtain ⟨-, -, -, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L₀
  have hc := hL₀ L₀ le_rfl
  refine ⟨τ, L₀, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛb, hΨ, hc0, hg0, ?_⟩
  calc βp * (Λ * (weakSplit d s τ L₀).c) ≤ βp * (Λ * (u / (βp * Λ))) := by gcongr
    _ = u := by field_simp

open HRS.External.Entropy in
/-- Crude bound for the pole variance, with the kernel data as hypothesis (constant `e^{Kbound}`). -/
theorem eqmarg_crude_of_kerData (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {B Cc : ℝ} (hB : 0 ≤ B)
    (hK : KerData (periodicRiesz d s) (withDensityReal ρ) B Cc) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d n => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) ≤
          ENNReal.ofReal (Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1) * (n : ℝ) ^ 2) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
              periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  intro n hn x t ht f hf
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hl : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := by positivity
  have hlb : β / ((n + 1 : ℕ) : ℝ) ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  have hln : β / ((n + 1 : ℕ) : ℝ) * (n : ℝ) ≤ β := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have : IsProbabilityMeasure
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) :=
    PoleCavityAux.pole_isProb hd hs0 hsd β hρ n _ hl x t ht.1
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t with hP
  have hF : Measurable fun Y : Config d n => ∑ i, f (Y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (evariance_le_lintegral_sub P hF.aestronglyMeasurable 0).trans ?_
  -- Cauchy-Schwarz
  have hCS : ∀ Y : Config d n, ‖∑ i, f (Y i) - 0‖ₑ ^ 2 ≤ (n : ℝ≥0∞) * ∑ i, ‖f (Y i)‖ₑ ^ 2 := by
    intro Y
    rw [sub_zero]
    have h1 : (∑ i, f (Y i)) ^ 2 ≤ (n : ℝ) * ∑ i, f (Y i) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => f (Y i))
      simpa using this
    have e1 : ‖∑ i, f (Y i)‖ₑ ^ 2 = ENNReal.ofReal ((∑ i, f (Y i)) ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i, ‖f (Y i)‖ₑ ^ 2 = ENNReal.ofReal (f (Y i) ^ 2) := fun i => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    calc ENNReal.ofReal ((∑ i, f (Y i)) ^ 2) ≤ ENNReal.ofReal ((n : ℝ) * ∑ i, f (Y i) ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (n : ℝ≥0∞) * ∑ i, ENNReal.ofReal (f (Y i) ^ 2) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  refine (lintegral_mono hCS).trans ?_
  rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum Finset.univ
    (f := fun (i : Fin n) (Y : Config d n) => ‖f (Y i)‖ₑ ^ 2)
    (fun i _ => ((hf.comp (measurable_pi_apply i)).enorm.pow_const 2))]
  have hone : ∀ i : Fin n, ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (Real.exp
      (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1)) *
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
        periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
    intro i
    have hle := PoleCavityAux.pole_one_le hK hB i hβ.le ht.1 ht.2 hl hlb hln x
    have hm : Measurable fun Y : Config d n => Y i := measurable_pi_apply i
    calc ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(P.map fun Y : Config d n => Y i) := by
          rw [lintegral_map (hf.enorm.pow_const 2) hm]
      _ ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(withDensityReal ρ |>.withDensity (fun y => ENNReal.ofReal
            (Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1)) *
            ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - y))))) :=
          lintegral_mono' hle le_rfl
      _ = _ := by
          rw [lintegral_withDensity_eq_lintegral_mul₀]
          · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun z => ?_
            simp only [Pi.mul_apply]
            ring
          · exact ((measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              ((hK.meas.comp (measurable_const.sub measurable_id)).const_mul _))))).aemeasurable
          · exact (hf.enorm.pow_const 2).aemeasurable
  calc (n : ℝ≥0∞) * ∑ i : Fin n, ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P
      ≤ (n : ℝ≥0∞) * ∑ _i : Fin n, ENNReal.ofReal (Real.exp
        (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1)) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
        gcongr with i _
        exact hone i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (Nat.cast_nonneg n),
          ENNReal.ofReal_natCast]
        ring


/-- `Kbound` is nondecreasing in `β`. -/
theorem eqmarg_Kbound_mono (g : Torus d → ℝ) {B Cc : ℝ} (hB : 0 ≤ B) (hCc : 0 ≤ Cc) {β β' : ℝ}
    (hβ : 0 ≤ β) (hββ : β ≤ β') :
    PoleCavityAux.Kbound g B Cc β 1 ≤ PoleCavityAux.Kbound g B Cc β' 1 := by
  have h0 := abs_nonneg (g 0)
  have e : ∀ b : ℝ, PoleCavityAux.Kbound g B Cc b 1 = b * (Cc + (1 / 2) * (B + |g 0|) + B + 2 * Cc +
      (1 / 2) * ((|g 0| + Cc) + |g 0|) + Cc) := by
    intro b; unfold PoleCavityAux.Kbound; ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hββ (by positivity)

open HRS.External.Calib HeatSplit HRS.External.PoleVar HRS.External.Entropy in
/-- Uniform variance clause of Lemma 4.1 (`A:eq:pole-variance`): `C` depends only on `[β₋,β₊]` and `Λ0`. -/
theorem eqmarg_pole_variance (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (Λ0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ) := by
  by_cases hemp : βp < βm
  · refine ⟨1, one_pos, fun β hβ1 hβ2 => ?_⟩
    exact absurd (hβ1.trans hβ2) (not_le.2 hemp)
  have hβpm : βm ≤ βp := not_lt.1 hemp
  have hβp0 : 0 < βp := lt_of_lt_of_le hβm hβpm
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ0Λ, hΨ, hc0, hg0, hsmall⟩ :=
    eqmarg_split_params hd hs0 hsd βp hβp0 Λ0
  obtain ⟨n₀, hn₀⟩ := eqmarg_small_calib hd hs0 hsd hτ hτ1 L hΛ1 Ψ hΨ βp hβp0
  obtain ⟨B, Cc, hB, hCc0, hKU⟩ := eqmarg_kerData hd hs0 hsd Λ0
  set K : ℝ := Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc βp 1) with hKdef
  have hK0 : 0 < K := Real.exp_pos _
  have hΛc : 0 ≤ Λ * (weakSplit d s τ L).c := mul_nonneg (by linarith) hc0
  set C₁ : ℝ := 2 * Real.exp (52 * βp * (weakSplit d s τ L).gL 0) *
    Real.exp (2 * βp * (Λ * (weakSplit d s τ L).c) + 1 + βp * (weakSplit d s τ L).gL 0) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  refine ⟨max C₁ (K * n₀), lt_max_of_lt_left hC₁pos, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛρ N hN x t ht f hf
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hΛ : ∀ y, ρ y ≤ Λ := fun y => (hΛρ y).trans hΛ0Λ
  have hκ : KappaSmall β (Λ * (weakSplit d s τ L).c) :=
    kappaSmall_of_le hβ hΛc ((mul_le_mul_of_nonneg_right hβ2 hΛc).trans hsmall)
  have hC₁β : 2 * Real.exp (52 * β * (weakSplit d s τ L).gL 0) *
      Real.exp (2 * β * (Λ * (weakSplit d s τ L).c) + 1 + β * (weakSplit d s τ L).gL 0) ≤ C₁ := by
    rw [hC₁]
    gcongr
  have hKle : Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1) ≤ K :=
    Real.exp_le_exp.2 (eqmarg_Kbound_mono _ hB hCc0 hβ.le hβ2)
  have hKb := eqmarg_crude_of_kerData hd hs0 hsd β hβ hρ hB (hKU ρ hρ hΛρ)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  show evariance (fun Y : Config d n => ∑ i, f (Y i))
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) ≤
    ENNReal.ofReal (max C₁ (K * n₀) * (n : ℝ)) *
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
        periodicRiesz d s (x - y))) ∂(withDensityReal ρ)
  by_cases hlarge : n₀ ≤ n + 1
  · have h1 := riesz_pole_variance_large hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ hκ n hn
      (hn₀ β hβ hβ2 ρ hρ.density hΛ (n + 1) hlarge) x ht.1 ht.2 hf
    refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_right (hC₁β.trans (le_max_left _ _)) this
  · have h1 := hKb n hn x t ht f hf
    refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have hn1 : (n : ℝ) ≤ n₀ := by exact_mod_cast (by omega : n ≤ n₀)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1) * (n : ℝ) ^ 2
        ≤ K * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hKle (sq_nonneg _)
      _ = (K * n) * n := by ring
      _ ≤ (K * n₀) * n := by gcongr
      _ ≤ max C₁ (K * n₀) * n := mul_le_mul_of_nonneg_right (le_max_right _ _) hn0

end EqMarg

end HRS
