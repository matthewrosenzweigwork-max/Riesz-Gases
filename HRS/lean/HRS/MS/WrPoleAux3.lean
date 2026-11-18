import HRS.MS.WrPoleAux2

/-!
# HRS.MS.WrPoleAux3 -- pole variance, part 3: the Riesz pole law, crude bound, final assembly (WR-13b)

Packet WR-13b (T8 of `docs/WR_B_PLAN.md`), namespace `HRS.MS.Wr`, helper prefix `wr13b_`.

Main statements (`0 < s < d`, `2 ≤ d`, `μ = ρ dx`, `ρ ≤ M`, `0 < β ≤ βp`, `N ≥ 2`, `0 ≤ t ≤ 1`):
* `wr13b_pole_variance`: `∃ C > 0, ∀ ρ β N x t f measurable,
  evariance (∑ f (Y i)) (poleLaw d s N β μ x t) ≤ ofReal (C (N-1)) * ∫⁻ ‖f‖ₑ² e^{-tλ g(x-y)} dμ`
  (the extended-variance form of the `S:eq:input-pole-variance` clause of `Bias.StaticInputConclusion`);
* `wr13b_pole_variance_clause`: the same bound in the exact real form of the clause of
  `Bias.StaticInputConclusion` (`Integrable` hypothesis, Bochner integral, `C (N-1)` with `N - 1` real).

Adjustments with respect to the plan (all harmless): `β` ranges over `(0, βp]` (the plan quantifies `[βm, βp]`,
which is contained); the constant `C` depends only on `(d, s, βp, M)` and is quantified before `ρ, β, N, x, t, f`.
Small `N` (below the threshold `N0` of `euc_transfer_setup`) are handled by Cauchy-Schwarz and the one-coordinate
pole density bound `wr13a_pole_bundle`, which needs exchangeability of the pole law (`wr13b_poleLaw_exchangeable`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External
open HRS.Whole (rieszKernel EucConfig)

/-! ### The normalised tilt is the Mathlib tilt -/

section Tilt

variable {α : Type*} [MeasurableSpace α]

theorem wr13b_tilt_eq_tilted (P : Measure α) [IsProbabilityMeasure P] {w : α → ℝ} (hw : Measurable w)
    {W : ℝ} (hW : ∀ a, w a ≤ W) : wr13a_tilt P w = P.tilted w := by
  have hint : Integrable (fun a => Real.exp (w a)) P :=
    wr11_integrable_of_abs_le (Real.measurable_exp.comp hw) (Real.exp W) fun a => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (hW a)
  have hZ := integral_exp_pos hint
  have hc : ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P = ENNReal.ofReal (∫ a, Real.exp (w a) ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
  unfold wr13a_tilt Measure.tilted
  rw [hc]
  have hne : (ENNReal.ofReal (∫ a, Real.exp (w a) ∂P))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne'
  have hfun : (fun x => ENNReal.ofReal (Real.exp (w x) / ∫ a, Real.exp (w a) ∂P)) =
      (ENNReal.ofReal (∫ a, Real.exp (w a) ∂P))⁻¹ • fun a => ENNReal.ofReal (Real.exp (w a)) := by
    funext x
    rw [ENNReal.ofReal_div_of_pos hZ, Pi.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul]
  rw [hfun, withDensity_smul' _ _ hne]

end Tilt

/-! ### Crude bound for an exchangeable law with a dominated one-point marginal -/

section Crude

variable {d : ℕ}

/-- Cauchy-Schwarz: for an exchangeable probability law whose one-point marginal is dominated by `ν`,
`Var(∑ f(Y_i)) ≤ m² ∫ |f|² dν`. -/
theorem wr13b_crude_core {m : ℕ} (hm : 0 < m) (P : Measure (Fin m → Euc d)) [IsProbabilityMeasure P]
    (hex : HRS.External.Entropy.IsExchangeable P) {ν : Measure (Euc d)}
    (hmarg : P.map (fun Y => Y ⟨0, hm⟩) ≤ ν) {f : Euc d → ℝ} (hf : Measurable f) :
    evariance (fun Y : Fin m → Euc d => ∑ i, f (Y i)) P ≤ (m : ℝ≥0∞) ^ 2 * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν := by
  have hF : Measurable fun Y : Fin m → Euc d => ∑ i, f (Y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (evariance_le_lintegral_sub P hF.aestronglyMeasurable 0).trans ?_
  have hCS : ∀ Y : Fin m → Euc d, ‖∑ i, f (Y i) - 0‖ₑ ^ 2 ≤ (m : ℝ≥0∞) * ∑ i, ‖f (Y i)‖ₑ ^ 2 := by
    intro Y
    rw [sub_zero]
    have h1 : (∑ i, f (Y i)) ^ 2 ≤ (m : ℝ) * ∑ i, f (Y i) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin m => f (Y i))
      simpa using this
    have e1 : ‖∑ i, f (Y i)‖ₑ ^ 2 = ENNReal.ofReal ((∑ i, f (Y i)) ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i, ‖f (Y i)‖ₑ ^ 2 = ENNReal.ofReal (f (Y i) ^ 2) := fun i => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    calc ENNReal.ofReal ((∑ i, f (Y i)) ^ 2) ≤ ENNReal.ofReal ((m : ℝ) * ∑ i, f (Y i) ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (m : ℝ≥0∞) * ∑ i, ENNReal.ofReal (f (Y i) ^ 2) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  refine (lintegral_mono hCS).trans ?_
  rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum Finset.univ
    (f := fun (i : Fin m) (Y : Fin m → Euc d) => ‖f (Y i)‖ₑ ^ 2)
    (fun i _ => ((hf.comp (measurable_pi_apply i)).enorm.pow_const 2))]
  have hone : ∀ i : Fin m, ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν := by
    intro i
    have hmi : Measurable fun Y : Fin m → Euc d => Y i := measurable_pi_apply i
    calc ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(P.map fun Y : Fin m → Euc d => Y i) := by
          rw [lintegral_map (hf.enorm.pow_const 2) hmi]
      _ = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(P.map fun Y : Fin m → Euc d => Y ⟨0, hm⟩) := by
          rw [hex.marginal_eq i ⟨0, hm⟩]
      _ ≤ _ := lintegral_mono' hmarg le_rfl
  calc (m : ℝ≥0∞) * ∑ i : Fin m, ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P
      ≤ (m : ℝ≥0∞) * ∑ _i : Fin m, ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν := by
        gcongr with i _
        exact hone i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Crude

/-! ### The Riesz pole law: tilt, exchangeability, crude bound -/

section Riesz

variable {d : ℕ} {s : ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem wr13b_poleLaw_isProb (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) : IsProbabilityMeasure (HRS.Whole.poleLaw d s N β μ x t) := by
  rw [wr13a_poleLaw_eq hs0 hconv hβ ht N x]
  exact wr13a_tilt_isProb _ (wr13a_Ep_meas hs0 μ _ β x t)
    (fun Y => wr13a_Ep_le hs0 hconv (div_nonneg hβ (Nat.cast_nonneg _)) hβ ht x Y)

theorem wr13b_poleLaw_eq_tilted (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (n : ℕ) (x : Euc d) :
    HRS.Whole.poleLaw d s (n + 1) β μ x t =
      (Measure.pi fun _ : Fin n => μ).tilted (wr13a_Ep d s μ (β / ((n + 1 : ℕ) : ℝ)) β x t) := by
  rw [wr13a_poleLaw_eq hs0 hconv hβ ht (n + 1) x]
  exact wr13b_tilt_eq_tilted _ (wr13a_Ep_meas hs0 μ _ β x t)
    (fun Y => wr13a_Ep_le hs0 hconv (div_nonneg hβ (Nat.cast_nonneg _)) hβ ht x Y)

theorem wr13b_Ep_perm (lam β t : ℝ) (x : Euc d) {n : ℕ} (σ : Equiv.Perm (Fin n)) (Y : EucConfig d n) :
    wr13a_Ep d s μ lam β x t (Y ∘ σ) = wr13a_Ep d s μ lam β x t Y := by
  have hg : ∀ z, rieszKernel d s (-z) = rieszKernel d s z := fun z => HRS.Whole.rieszKernel_neg z
  have h1 : wr13a_pairSum (rieszKernel d s) (Y ∘ σ) = wr13a_pairSum (rieszKernel d s) Y := by
    rw [wr13b_pairSum_eq hg, wr13b_pairSum_eq hg]
    have : ∑ a, ∑ b, rieszKernel d s ((Y ∘ σ) a - (Y ∘ σ) b) = ∑ a, ∑ b, rieszKernel d s (Y a - Y b) := by
      calc ∑ a, ∑ b, rieszKernel d s ((Y ∘ σ) a - (Y ∘ σ) b)
          = ∑ a, ∑ b, rieszKernel d s ((Y ∘ σ) a - Y b) :=
            Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => rieszKernel d s ((Y ∘ σ) a - Y b))
        _ = ∑ a, ∑ b, rieszKernel d s (Y a - Y b) :=
            Equiv.sum_comp σ (fun a => ∑ b, rieszKernel d s (Y a - Y b))
    rw [this]
  have h2 : ∑ i, HRS.Whole.convMeasure (rieszKernel d s) μ ((Y ∘ σ) i)
      = ∑ i, HRS.Whole.convMeasure (rieszKernel d s) μ (Y i) :=
    Equiv.sum_comp σ (fun i => HRS.Whole.convMeasure (rieszKernel d s) μ (Y i))
  have h3 : ∑ i, rieszKernel d s (x - (Y ∘ σ) i) = ∑ i, rieszKernel d s (x - Y i) :=
    Equiv.sum_comp σ (fun i => rieszKernel d s (x - Y i))
  unfold wr13a_Ep wr13a_E
  rw [h1, h2, h3]

/-- The pole law is exchangeable. -/
theorem wr13b_poleLaw_exchangeable (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) :
    HRS.External.Entropy.IsExchangeable (HRS.Whole.poleLaw d s N β μ x t) := by
  intro σ
  rw [wr13a_poleLaw_eq hs0 hconv hβ ht N x]
  unfold wr13a_tilt
  have h1 : (fun (y : Fin (N - 1) → Euc d) i => y (σ i)) = ⇑(HRS.Whole.permEquiv (E := Euc d) σ) := rfl
  rw [h1, Measure.map_smul]
  · congr 1
    exact HRS.Whole.map_withDensity_of_invariant (Measure.pi fun _ : Fin (N - 1) => μ)
      (HRS.Whole.permEquiv σ) (HRS.Whole.pi_map_perm μ σ)
      (fun a => ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / N) β x t a)))
      (fun Y => by
        show ENNReal.ofReal (Real.exp (wr13a_Ep d s μ (β / N) β x t (Y ∘ σ))) = _
        rw [wr13b_Ep_perm])
  · exact (HRS.Whole.permEquiv σ).measurable.aemeasurable

/-- **Crude pole variance bound** (small `N`): from Cauchy-Schwarz and the one-coordinate pole density
bound of `wr13a_pole_bundle`. -/
theorem wr13b_pole_variance_crude (hd : 2 ≤ d) (hs : 0 < s) (hsd : s < d) {βp : ℝ} (hβp : 0 ≤ βp)
    (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 ≤ β → β ≤ βp → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ f : Euc d → ℝ, Measurable f →
          evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i))
              (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
            ENNReal.ofReal (K * ((N - 1 : ℕ) : ℝ) ^ 2) *
              ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))
                ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC1, hb⟩ := wr13a_pole_bundle hd hs hsd hβp M
  refine ⟨C, by linarith, fun ρ hρ hM β hβ hββp N hN x t ht f hf => ?_⟩
  have := wr13a_isProb_density hρ
  have hMg0 := wr13a_potentialBound_nonneg (by omega : 1 ≤ d) hs hsd hρ hM
  have hconv := wr13a_conv_le_density (by omega : 1 ≤ d) hs hsd hρ hM
  have := wr13b_poleLaw_isProb hs hconv hβ ht.1 N x
  have hmarg := ((hb ρ hρ hM β hβ hββp N hN).2.2 x t ht).2.1
  have hm : 0 < N - 1 := by omega
  have hmarg' : (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t).map
      (fun Y => Y ⟨0, hm⟩) ≤ (HRS.Whole.withDensityReal ρ).withDensity
        (fun y => ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))) := by
    have : HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) =
        (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t).map (fun Y => Y ⟨0, hm⟩) := by
      unfold HRS.Whole.firstMarginal
      simp only [hm, dite_true]
    rw [← this]
    exact hmarg
  have hcore := wr13b_crude_core hm _ (wr13b_poleLaw_exchangeable hs hconv hβ ht.1 N x) hmarg' hf
  refine hcore.trans ?_
  have hWm : Measurable fun y : Euc d => ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
      rieszKernel d s (x - y))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (((wr13a_g_meas hs).comp (measurable_const.sub measurable_id)).const_mul _)))
  rw [lintegral_withDensity_eq_lintegral_mul₀ hWm.aemeasurable (hf.enorm.pow_const 2).aemeasurable]
  have hC0 : 0 ≤ C := by linarith
  simp only [Pi.mul_apply]
  have e1 : ∫⁻ z, ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * rieszKernel d s (x - z))) * ‖f z‖ₑ ^ 2
        ∂(HRS.Whole.withDensityReal ρ)
      = ENNReal.ofReal C * ∫⁻ z, ‖f z‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - z)))
            ∂(HRS.Whole.withDensityReal ρ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul hC0]
    ring
  rw [e1]
  have e2 : ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ) ^ 2) = ENNReal.ofReal C * ((N - 1 : ℕ) : ℝ≥0∞) ^ 2 := by
    rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [e2]
  refine le_of_eq ?_
  ring

end Riesz

/-! ### Large `N`: the transferred bound -/

section Large

variable {d : ℕ} {s : ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a β : ℝ} {q k : Euc d → ℝ} {Ψ : Euc d → H}

theorem wr13b_ae_pi_ne_coord (hatom : ∀ z : Euc d, μ {z} = 0) (n : ℕ) (x : Euc d) :
    ∀ᵐ Y ∂(Measure.pi fun _ : Fin n => μ), ∀ i, Y i ≠ x := by
  rw [ae_all_iff]
  intro i
  have : NullSingletonClass μ := ⟨hatom⟩
  have := Measure.pi_hyperplane (fun _ : Fin n => μ) i x
  rw [ae_iff]
  simpa using this

theorem wr13b_ae_ne_pt (hatom : ∀ z : Euc d, μ {z} = 0) (y : Euc d) : ∀ᵐ z ∂μ, z ≠ y := by
  rw [ae_iff]
  simpa using hatom y

/-- The cavity exponent of the Riesz kernel equals the exponent for `q + k`, almost everywhere. -/
theorem wr13b_Ep_ae_eq {g : Euc d → ℝ} (hgS : ∀ z : Euc d, z ≠ 0 → g z = q z + k z)
    (hatom : ∀ z : Euc d, μ {z} = 0) (n : ℕ) (lam β t : ℝ) (x : Euc d) :
    (fun Y : Fin n → Euc d => -lam * wr13a_pairSum g Y + β * ∑ i, HRS.Whole.convMeasure g μ (Y i)
        - t * lam * ∑ i, g (x - Y i)) =ᵐ[Measure.pi fun _ : Fin n => μ]
      wr13b_EP (fun w => q w + k w) μ n lam β t x := by
  filter_upwards [ae_injective_pi_Euc (N := n) hatom, wr13b_ae_pi_ne_coord hatom n x] with Y hY hx
  have h1 : wr13a_pairSum g Y = wr13a_pairSum (fun w => q w + k w) Y := by
    unfold wr13a_pairSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.1 hj).2
    exact hgS _ (sub_ne_zero.2 (hY i j hij.ne))
  have h2 : ∀ y : Euc d, HRS.Whole.convMeasure g μ y = HRS.Whole.convMeasure (fun w => q w + k w) μ y := by
    intro y
    unfold HRS.Whole.convMeasure
    refine integral_congr_ae ?_
    filter_upwards [wr13b_ae_ne_pt hatom y] with z hz
    exact hgS _ (sub_ne_zero.2 hz.symm)
  have h3 : ∑ i, g (x - Y i) = ∑ i, (fun w => q w + k w) (x - Y i) :=
    Finset.sum_congr rfl fun i _ => hgS _ (sub_ne_zero.2 (hx i).symm)
  unfold wr13b_EP
  rw [h1, h3]
  simp_rw [h2]
  ring

/-- **The variance clause for large `N`** (the calibration field `t_{n+1}·Ξ` is small): the pole law of the Riesz
kernel satisfies `Var_P(∑ f(y_i)) ≤ C n ∫ |f|² e^{-tλ g(x-y)} dμ`, with an explicit constant independent of
`n, x, t, f`. -/
theorem wr13b_pole_variance_large (hs : 0 < s) {Mg : ℝ}
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg)
    (h : TransferHyp μ a q k (rieszKernel d s) Ψ) (hβ : 0 < β) (hκ : wr11b_KappaSmall β a)
    (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : Euc d → ℝ} (hf : Measurable f) :
    evariance (fun Y : Fin n → Euc d => ∑ i, f (Y i))
        (HRS.Whole.poleLaw d s (n + 1) β μ x t) ≤
      ENNReal.ofReal (2 * Real.exp (52 * β * k 0) * Real.exp (2 * β * a + 1 + β * k 0) * n) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          rieszKernel d s (x - y))) ∂μ := by
  have hlam0 := wr13b_lamN_nonneg hβ n
  have hk0 := h.feat.k_zero_nonneg
  have hP : HRS.Whole.poleLaw d s (n + 1) β μ x t = (Measure.pi fun _ : Fin n => μ).tilted
      (wr13b_EP (fun w => q w + k w) μ n (wr13b_lamN β n) β t x) := by
    rw [wr13b_poleLaw_eq_tilted hs hconv hβ.le ht0 n x]
    refine tilted_congr ?_
    filter_upwards [wr13b_Ep_ae_eq (g := rieszKernel d s) (fun z hz => h.split z hz) h.atomless n
      (wr13b_lamN β n) β t x] with Y hY
    exact hY
  have hProb := wr13b_poleLaw_isProb hs hconv hβ.le ht0 (n + 1) x
  have hmain := wr13b_pole_evariance_le h hβ n hn ht hκ x ht0 ht1 _ hP hf
  have hlamle : wr13b_lamN β n ≤ β := by
    unfold wr13b_lamN
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  have htl : t * wr13b_lamN β n ≤ β := by
    calc t * wr13b_lamN β n ≤ 1 * β := mul_le_mul ht1 hlamle hlam0 (by norm_num)
      _ = β := one_mul _
  have htl0 : 0 ≤ t * wr13b_lamN β n := mul_nonneg ht0 hlam0
  have hpt : ∀ z : Euc d, z ≠ x →
      β * a + HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z ≤
        2 * β * a + 1 + β * k 0 + (-(t * wr13b_lamN β n) * rieszKernel d s (x - z)) := by
    intro z hz
    have h1 : β * rowIntE (wr11b_dk q) μ z ≤ β * a :=
      mul_le_mul_of_nonneg_left (h.weak.wr1_rowInt_le h.a_nonneg z) hβ.le
    have h2 : inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ z) ≤ 1 := (le_abs_self _).trans (ht z)
    have hsz := h.split (x - z) (sub_ne_zero.2 (Ne.symm hz))
    have hqe : q (z - x) = q (x - z) := by
      have := h.weak.symm z x
      simpa using this
    have hkl : k (x - z) ≤ k 0 := (abs_le.1 (h.feat.k_abs_le (x - z))).2
    have h3 : -(t * wr13b_lamN β n) * q (z - x)
        ≤ β * k 0 + (-(t * wr13b_lamN β n) * rieszKernel d s (x - z)) := by
      rw [hqe]
      have hq : q (x - z) = rieszKernel d s (x - z) - k (x - z) := by rw [hsz]; ring
      rw [hq]
      have a1 := mul_le_mul_of_nonneg_left hkl htl0
      have a3 := mul_le_mul_of_nonneg_right htl hk0
      nlinarith
    have : HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z
        = β * rowIntE (wr11b_dk q) μ z
          + inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ z)
          + -(t * wr13b_lamN β n) * q (z - x) := by
      simp only [HRS.External.PoleVar.psiPole, wr13b_Vp, weakPotE_φ, weakPotE_q]
      ring
    rw [this]
    linarith
  have hint : ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * a +
        HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (2 * β * a + 1 + β * k 0)) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          rieszKernel d s (x - y))) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [wr13b_ae_ne_pt h.atomless x] with z hz
    have h1 := hpt z hz
    have h2 : ENNReal.ofReal (Real.exp (β * a +
          HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z))
        ≤ ENNReal.ofReal (Real.exp (2 * β * a + 1 + β * k 0)) *
          ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * rieszKernel d s (x - z))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 h1
    calc ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * a +
          HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z))
        ≤ ‖f z‖ₑ ^ 2 * (ENNReal.ofReal (Real.exp (2 * β * a + 1 + β * k 0)) *
          ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * rieszKernel d s (x - z)))) := by
          gcongr
      _ = _ := by ring
  refine hmain.trans ?_
  calc ENNReal.ofReal (Real.exp (52 * β * k 0)) * (2 * n * ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal
        (Real.exp (β * a + HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z)) ∂μ)
      ≤ ENNReal.ofReal (Real.exp (52 * β * k 0)) * (2 * n * (ENNReal.ofReal
        (Real.exp (2 * β * a + 1 + β * k 0)) * ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal
          (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * rieszKernel d s (x - y))) ∂μ)) := by
        gcongr
    _ = _ := by
        have e : ENNReal.ofReal (2 * Real.exp (52 * β * k 0) *
            Real.exp (2 * β * a + 1 + β * k 0) * n)
            = ENNReal.ofReal (Real.exp (52 * β * k 0)) * (2 *  n *
              ENNReal.ofReal (Real.exp (2 * β * a + 1 + β * k 0))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num)]
          simp
          ring
        rw [e]
        ring

end Large

/-! ### Final assembly -/

section Main

variable {d : ℕ} {s : ℝ}

/-- **Pole variance** (`euc-pole-var`, conjunct of `S:prop:static-input` for the whole range `0 < s < d`):
for `2 ≤ d`, `0 < s < d`, `βp, M` there is `C > 0` such that for every probability density `ρ ≤ M`,
`β ∈ (0, βp]`, `N ≥ 2`, `x`, `t ∈ [0,1]` and every measurable `f`,
`Var_{P_n^{x,t}}[∑ f(y_i)] ≤ C (N-1) ∫ |f|² e^{-tλ g(x-y)} dμ`  (`n = N-1`, `λ = β/N`, extended variance
and lower Lebesgue integral, so no integrability hypothesis is needed). -/
theorem wr13b_pole_variance (hd : 2 ≤ d) (hs : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ f : Euc d → ℝ, Measurable f →
          evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i))
              (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
            ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
              ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))
                ∂(HRS.Whole.withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨τ, hτ, N0, hN0, hset⟩ := euc_transfer_setup hd1 hs hsd βp M
  have := featMap_separableSpace (d := d) hs hτ
  obtain ⟨K, hK0, hK⟩ := wr13b_pole_variance_crude hd hs hsd (le_max_right βp 0) M
  set a : ℝ := wr11b_aRow d s M τ with ha
  set k0 : ℝ := HRS.MS.Psd.kTau d s τ 0 with hk0def
  have hk0 : 0 ≤ k0 := (featMap_hyp (d := d) hs hτ).k_zero_nonneg
  set βp' : ℝ := max βp 0 with hβp'
  have hβp0 : 0 ≤ βp' := le_max_right _ _
  set C₁ : ℝ := 2 * Real.exp (52 * βp' * k0) * Real.exp (2 * βp' * |a| + 1 + βp' * k0) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  refine ⟨max C₁ (K * N0), lt_max_of_lt_left hC₁pos, ?_⟩
  intro ρ hρ hM β hβ hββp N hN x t ht f hf
  have := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density hd1 hs hsd hρ hM
  by_cases hlarge : N0 ≤ N
  · obtain ⟨hT, hsmall, hκ⟩ := hset ρ hρ hM β hβ hββp N hlarge
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    have h1 := wr13b_pole_variance_large (μ := HRS.Whole.withDensityReal ρ) hs hconv hT hβ hκ n hn
      hsmall x ht.1 ht.2 hf
    show evariance (fun Y : Fin n → Euc d => ∑ i, f (Y i))
        (HRS.Whole.poleLaw d s (n + 1) β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal (max C₁ (K * N0) * (n : ℝ)) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ)
    refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hββ : β ≤ βp' := hββp.trans (le_max_left _ _)
    have e1 : Real.exp (52 * β * k0) ≤ Real.exp (52 * βp' * k0) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e2 : Real.exp (2 * β * a + 1 + β * k0) ≤ Real.exp (2 * βp' * |a| + 1 + βp' * k0) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : 2 * β * a ≤ 2 * βp' * |a| := by
        calc 2 * β * a ≤ 2 * β * |a| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self a) (by positivity)
          _ ≤ 2 * βp' * |a| := by
              exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg a)
      nlinarith
    have : 2 * Real.exp (52 * β * k0) * Real.exp (2 * β * a + 1 + β * k0) ≤ C₁ := by
      rw [hC₁]
      exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e2 (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _)) hn0
  · have hlt : N < N0 := by omega
    have h1 := hK ρ hρ hM β hβ.le (hββp.trans (le_max_left _ _)) N hN x t ht f hf
    refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have hm : ((N - 1 : ℕ) : ℝ) ≤ N0 := by exact_mod_cast (by omega : N - 1 ≤ N0)
    have hm0 : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc K * ((N - 1 : ℕ) : ℝ) ^ 2 = (K * ((N - 1 : ℕ) : ℝ)) * ((N - 1 : ℕ) : ℝ) := by ring
      _ ≤ (K * N0) * ((N - 1 : ℕ) : ℝ) := by gcongr
      _ ≤ max C₁ (K * N0) * ((N - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hm0

/-- **The pole variance clause of `Bias.StaticInputConclusion`** (`S:eq:input-pole-variance`), in its exact real form
(`Integrable` hypothesis, Bochner integral, `C * (N - 1)` with `N - 1` computed in `ℝ`), for the whole range
`0 < s < d`, uniformly in `ρ ≤ M` and `β ∈ (0, βp]`. -/
theorem wr13b_pole_variance_clause (hd : 2 ≤ d) (hs : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ f : Euc d → ℝ, Measurable f →
          Integrable (fun y => |f y| ^ 2 * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))
            (HRS.Whole.withDensityReal ρ) →
          evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i))
              (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
            ENNReal.ofReal (C * ((N : ℝ) - 1) *
              ∫ y, |f y| ^ 2 * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y))
                ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨C, hC, hmain⟩ := wr13b_pole_variance hd hs hsd βp M
  refine ⟨C, hC, fun ρ hρ hM β hβ hββp N hN x t ht f hf hint => ?_⟩
  refine (hmain ρ hρ hM β hβ hββp N hN x t ht f hf).trans (le_of_eq ?_)
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hnn : ∀ y, 0 ≤ |f y| ^ 2 * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)) :=
    fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hI : ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))
        ∂(HRS.Whole.withDensityReal ρ)
      = ENNReal.ofReal (∫ y, |f y| ^ 2 * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y))
        ∂(HRS.Whole.withDensityReal ρ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    simp
  rw [hI, ← ENNReal.ofReal_mul (by positivity), hcast]

end Main

end HRS.MS.Wr
