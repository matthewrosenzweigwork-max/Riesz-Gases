import HRS.MS.WrSmlAux1
import HRS.MS.WrCal
import HRS.External.Entropy

/-!
# HRS.MS.WrSmlAux2 -- entropy, total variation and field smallness (WR-12a, part 2)

Packet WR-12a of `docs/WR_B_PLAN.md` (T5), namespace `HRS.MS.Wr`, helper prefix `wr12_`.
Notation: `μ = ρ dx = withDensityReal ρ`, `g = rieszKernel d s`, `q_τ = qTau d s τ`,
`R0 = pairGibbsLawE (q_τ (x-y)) N β μ`, `Q = modulatedGibbs g N β μ`, `0 < s < d`, `1 ≤ d`.

Main results (all constants `C` are quantified before `ρ, β, N`, depend only on `(d, s, M)`, and the
bounds are linear in `β ≥ 0`, hence uniform for `β` in compact sets; they do not depend on `τ`):
* `EWeakKernel.wr12_klDiv_le`, `wr12_klDiv_tilted_le`: generic entropy bound `KL(R0 ‖ μ^{⊗N}) ≤ β N A`
  when `F_N ≥ -A` a.s. (via `pairGibbsLawE = (μ^{⊗N}).tilted (-β N F_N)`, Jensen `K ≥ 1`).
* `euc_klDiv_R0_le`, `euc_klDiv_Q_le`: `klDiv ≤ ofReal (β (C N^{s/d}))` for `R0` and for `Q`
  (`g(x-y)` is itself an `EWeakKernel`: `wr12_g_weak`; `Q = R0`-type by `pairGibbs_eq_pairGibbsLawE`).
* `euc_tv_R0_le`, `euc_tv_Q_le`: `tvDist (firstMarginal ·) μ ≤ √(β C N^{s/d-1} / 2)`
  (quantitative core of `Entropy.tendsto_tvDist_firstMarginal`: `wr12_tv_of_kl`, exchangeability
  `wr12_pairGibbsLawE_exchangeable`).
* `wr12_norm_empXi_le`: `‖E_R[μ_N(Ξ)]‖ ≤ 2 B ‖π - μ‖_TV` (`H`-valued, `CalFeat Ψ B`), `wr12_norm_Xi_le`
  (`‖Ξ‖ ≤ 2B`; for `B = √(k 0)` this is `‖Ξ‖ ≤ 2√k(0)`).
* `euc_field_small`: `∃ N0, ∀ ρ ≤ M, β ∈ (0, βp], N ≥ N0, ∀ t, ‖t‖ ≤ β ‖E_{R0}[μ_N(Ξ)]‖ → ∀ x,
  |⟪t, Ξ x⟫| ≤ 1`; the hypothesis on `t` is exactly the conclusion of `WrCal.tN_norm_le`, which is not used.

Adjustments with respect to the plan (documented, harmless): the feature map is any `Ψ` with
`CalFeat Ψ B` (continuity and `‖Ψ‖ ≤ B`, as in `WrCal`), not a `FeatHyp`; `N0` depends on `B`; the
TV and entropy statements hold for all `β ≥ 0` (and `τ > 0`) with `C` independent of `β` and `τ`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace HRS.MS.Wr

open HRS.Whole HRS.MS.Psd

variable {d N : ℕ}

/-! ### Relative entropy of a tilted probability measure -/

/-- If `f ≤ B` a.e. and `∫ e^f dπ ≥ 1` then `KL(π tilted by f ‖ π) ≤ B`. -/
theorem wr12_klDiv_tilted_le {α : Type*} [MeasurableSpace α] (π : Measure α)
    [IsProbabilityMeasure π] {f : α → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ᵐ x ∂π, f x ≤ B)
    (hexp : Integrable (fun x => Real.exp (f x)) π) (hZ : 1 ≤ ∫ x, Real.exp (f x) ∂π) :
    klDiv (π.tilted f) π ≤ ENNReal.ofReal B := by
  haveI := isProbabilityMeasure_tilted hexp
  set R := π.tilted f with hR
  set Z := ∫ x, Real.exp (f x) ∂π with hZdef
  have hac : R ≪ π := tilted_absolutelyContinuous π f
  have hllr : llr R π =ᵐ[R] fun x => f x - Real.log Z :=
    hac.ae_le (log_rnDeriv_tilted_left_self hexp)
  have hfR : Integrable f R := by
    rw [integrable_tilted_iff hexp]
    refine Integrable.mono' (integrable_const (|B| * Real.exp |B| + 1))
      ((Real.measurable_exp.comp hf).mul hf).aestronglyMeasurable ?_
    filter_upwards [hB] with x hx
    simp only [smul_eq_mul, Real.norm_eq_abs]
    rcases le_or_gt 0 (f x) with h0 | h0
    · rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0), mul_comm]
      have h1 : f x ≤ |B| := hx.trans (le_abs_self B)
      have h2 : Real.exp (f x) ≤ Real.exp |B| := Real.exp_le_exp.2 h1
      have : f x * Real.exp (f x) ≤ |B| * Real.exp |B| :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (abs_nonneg _)
      linarith
    · rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h0.le)]
      have h3 : -f x + 1 ≤ Real.exp (-f x) := Real.add_one_le_exp _
      have h4 : Real.exp (-f x) * Real.exp (f x) = 1 := by rw [← Real.exp_add]; simp
      have h5 : -(Real.exp (f x) * f x) = (-f x) * Real.exp (f x) := by ring
      have h6 : (-f x) * Real.exp (f x) ≤ Real.exp (-f x) * Real.exp (f x) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      have : 0 ≤ |B| * Real.exp |B| := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
      linarith
  have hint : Integrable (llr R π) R := (hfR.sub (integrable_const _)).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hint]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : π.real univ = 1 := by simp [Measure.real]
  have h2 : R.real univ = 1 := by simp [Measure.real]
  rw [h1, h2, integral_congr_ae hllr, integral_sub hfR (integrable_const _), integral_const]
  simp only [h2, smul_eq_mul, one_mul]
  have hfB : ∫ x, f x ∂(π.tilted f) ≤ B := by
    have := integral_mono_ae hfR (integrable_const B) (hac.ae_le hB)
    simpa [h2] using this
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ
  linarith

/-! ### The weak reference as a tilted measure -/

section Tilt

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ}
  {q : E → E → ℝ}

theorem EWeakKernel.wr12_measurable_energy (h : EWeakKernel μ a q) (N : ℕ) :
    Measurable (fun X : Fin N → E => modEnergyE q X μ) := by
  unfold modEnergyE
  have h1 : Measurable (fun X : (Fin N → E) => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have := h.meas.comp (f := fun X : (Fin N → E) => (X i, X j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact this
  have h2 : Measurable (fun X : (Fin N → E) => ∑ i, ∫ y, q (X i) y ∂μ) :=
    Finset.measurable_sum _ fun i _ => h.wr1_measurable_rowInt.comp (measurable_pi_apply i)
  exact ((h1.const_mul _).sub (h2.const_mul _)).add_const _

theorem EWeakKernel.wr12_integrable_exp (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun X : Fin N → E => Real.exp (-β * N * modEnergyE q X μ))
      (Measure.pi fun _ : Fin N => μ) := by
  refine Integrable.of_bound
    (Real.measurable_exp.comp ((h.wr12_measurable_energy N).const_mul _)).aestronglyMeasurable
    (Real.exp (β * N * a)) (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have := h.wr1_pairWeight_le ha hβ hN X
  unfold pairWeightE at this
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 this |> Real.exp_le_exp.1

theorem EWeakKernel.wr12_partition_eq (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) :
    pairPartitionE q N β μ =
      ENNReal.ofReal (∫ X, Real.exp (-β * N * modEnergyE q X μ) ∂(Measure.pi fun _ : Fin N => μ)) := by
  unfold pairPartitionE pairWeightE
  rw [ofReal_integral_eq_lintegral_ofReal (h.wr12_integrable_exp ha hβ hN)
    (Eventually.of_forall fun X => (Real.exp_pos _).le)]

theorem EWeakKernel.wr12_one_le_integral (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) :
    1 ≤ ∫ X, Real.exp (-β * N * modEnergyE q X μ) ∂(Measure.pi fun _ : Fin N => μ) := by
  have := h.one_le_partition_E ha hβ hN
  rw [h.wr12_partition_eq ha hβ hN] at this
  exact ENNReal.one_le_ofReal.1 this

/-- `pairGibbsLawE` is the exponential tilt of `μ^{⊗N}` by `-β N F_N`. -/
theorem EWeakKernel.wr12_eq_tilted (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) :
    pairGibbsLawE q N β μ =
      (Measure.pi fun _ : Fin N => μ).tilted (fun X => -β * N * modEnergyE q X μ) := by
  have hpos : 0 < ∫ X, Real.exp (-β * N * modEnergyE q X μ) ∂(Measure.pi fun _ : Fin N => μ) :=
    lt_of_lt_of_le one_pos (h.wr12_one_le_integral ha hβ hN)
  unfold pairGibbsLawE Measure.tilted
  congr 1
  funext X
  rw [h.wr12_partition_eq ha hβ hN, ENNReal.ofReal_div_of_pos hpos]
  rfl

/-- **Entropy bound for the weak reference.**  If `F_N^q ≥ -A` almost surely then
`KL(R0 ‖ μ^{⊗N}) ≤ β N A` (`β ≥ 0`). -/
theorem EWeakKernel.wr12_klDiv_le (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 0 < N) {A : ℝ}
    (hA : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), -A ≤ modEnergyE q X μ) :
    klDiv (pairGibbsLawE q N β μ) (Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal (β * N * A) := by
  rw [h.wr12_eq_tilted ha hβ hN]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine wr12_klDiv_tilted_le _ ((h.wr12_measurable_energy N).const_mul _) ?_
    (h.wr12_integrable_exp ha hβ hN) (h.wr12_one_le_integral ha hβ hN)
  filter_upwards [hA] with X hX
  have : 0 ≤ β * N := mul_nonneg hβ hN0
  nlinarith

end Tilt

/-! ### The Riesz kernel is a weak kernel -/

/-- For `0 < s < d` and `ρ ≤ M` the kernel `g(x-y) = |x-y|^{-s}` is an `EWeakKernel` for `μ = ρ dx`. -/
theorem wr12_g_weak (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    ∃ a : ℝ, 0 ≤ a ∧
      EWeakKernel (HRS.Whole.withDensityReal ρ) a (fun x y : Euc d => rieszKernel d s (x - y)) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have hs0 : s ≠ 0 := hs.ne'
  refine ⟨M * HRS.sphereArea d / ((d : ℝ) - s) + 1, by positivity, ?_, ?_, ?_, ?_⟩
  · exact (HRS.Whole.Q34.measurable_rieszKernel (d := d) hs0).comp (measurable_fst.sub measurable_snd)
  · intro x y
    rw [HRS.Whole.Q34.rieszKernel_eq hs0, HRS.Whole.Q34.rieszKernel_eq hs0, ← norm_neg (x - y),
      neg_sub]
  · intro x y
    rw [HRS.Whole.Q34.rieszKernel_eq hs0]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · intro x
    simp_rw [HRS.Whole.Q34.rieszKernel_eq hs0]
    exact HRS.Whole.Q34.lintegral_kernel_le hd hs hsd hρ hM x

/-! ### Exchangeability -/

/-- The weak reference `pairGibbsLawE (g (x-y))` is exchangeable. -/
theorem wr12_pairGibbsLawE_exchangeable (g : Euc d → ℝ) (β : ℝ) (μ : Measure (Euc d)) :
    HRS.External.Entropy.IsExchangeable
      (pairGibbsLawE (fun x y : Euc d => g (x - y)) N β μ) := by
  intro σ
  unfold pairGibbsLawE
  have h1 : (fun (x : Fin N → Euc d) i => x (σ i)) = ⇑(HRS.Whole.permEquiv (E := Euc d) σ) := rfl
  rw [h1]
  exact HRS.Whole.map_withDensity_of_invariant (Measure.pi fun _ : Fin N => μ) (HRS.Whole.permEquiv σ) (HRS.Whole.pi_map_perm μ σ)
    (fun X : EucConfig d N => pairWeightE (fun x y : Euc d => g (x - y)) N β μ X /
      pairPartitionE (fun x y : Euc d => g (x - y)) N β μ)
    (fun X => by
      show pairWeightE (fun x y : Euc d => g (x - y)) N β μ (X ∘ σ) / _ = _
      unfold pairWeightE
      rw [show modEnergyE (fun x y : Euc d => g (x - y)) (X ∘ σ) μ = HRS.Whole.modulatedEnergy g (X ∘ σ) μ
        from rfl, HRS.Whole.modulatedEnergy_perm]
      rfl)

/-! ### Total variation of the first marginal -/

open HRS.External.Entropy in
/-- Quantitative form of `Entropy.tendsto_tvDist_firstMarginal`: for an exchangeable law with
`KL(R ‖ μ^{⊗N}) ≤ K`, each marginal is within `√(K/(2N))` of `μ` in total variation. -/
theorem wr12_tv_of_kl {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ : Measure E) [IsProbabilityMeasure μ] {N : ℕ} (R : Measure (Fin N → E))
    [IsProbabilityMeasure R] (hex : HRS.External.Entropy.IsExchangeable R) {K : ℝ} (hK : 0 ≤ K)
    (hkl : klDiv R (Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal K) (i : Fin N) :
    tvDist (R.map fun x => x i) μ ≤ Real.sqrt (K / (N : ℝ) / 2) := by
  have h := hex.mul_klDiv_marginal_le μ i R
  have : IsProbabilityMeasure (R.map fun x : Fin N → E => x i) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (measurable_pi_apply i))).2
      inferInstance
  have h2 := h.trans hkl
  have hne : klDiv (R.map fun x : Fin N → E => x i) μ ≠ ⊤ := by
    intro htop
    rw [htop] at h2
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fin.pos i).ne'
    rw [ENNReal.mul_top hN0] at h2
    exact absurd h2 (by simp)
  have h3 : (((N : ℝ≥0∞)) * klDiv (R.map fun x : Fin N → E => x i) μ).toReal ≤ K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    refine this.trans ?_
    exact (ENNReal.toReal_ofReal hK).le
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h3
  have hN : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := Fin.pos i
    exact_mod_cast this
  have h4 : (klDiv (R.map fun x : Fin N → E => x i) μ).toReal ≤ K / (N : ℝ) := by
    rw [le_div_iff₀ hN]; linarith
  refine (tvDist_le_sqrt_klDiv _ _ hne).trans ?_
  gcongr

/-! ### Entropy and total variation bounds, uniform in `ρ ≤ M` -/

theorem wr12_div_le {K E : ℝ} (hN : 0 < N) (h : -K ≤ (N : ℝ) * E) : -(K / N) ≤ E := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [neg_div', div_le_iff₀ hN']
  linarith

theorem wr12_rpow_div {s : ℝ} (hN : 0 < N) (K : ℝ) :
    K * (N : ℝ) ^ (s / d) / N = K * (N : ℝ) ^ (s / d - 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_sub_one hN'.ne']
  ring

/-- **`KL(R0 ‖ μ^{⊗N}) ≤ β C N^{s/d}`** for the weak reference `R0 = pairGibbsLawE q_τ N β μ`,
uniformly in the probability densities `ρ ≤ M`, `β ≥ 0` and `τ > 0`; `C` depends only on `(d, s, M)`. -/
theorem euc_klDiv_R0_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
        klDiv (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β (HRS.Whole.withDensityReal ρ))
          (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (β * (C * (N : ℝ) ^ (s / d))) := by
  obtain ⟨C, hC, h⟩ := euc_energy_lower_q hd hs hsd M
  refine ⟨C, hC, fun τ hτ ρ hρ hM β hβ N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hq := wr12_qTau_weak hd hs hsd hτ hρ hM
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have ha : 0 ≤ M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2)) := by
    have := (Real.rpow_pos_of_pos hτ (((d : ℝ) - s) / 2)).le
    rw [show aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s from rfl]
    have := wr12_cq_nonneg (d := d) hs hsd
    positivity
  have hae : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ),
      -(C * (N : ℝ) ^ (s / d) / N) ≤
        modEnergyE (fun x y : Euc d => qTau d s τ (x - y)) X (HRS.Whole.withDensityReal ρ) := by
    filter_upwards [ae_injective_pi_Euc (N := N) (wr12_atomless hd ρ)] with X hX
    exact wr12_div_le (by omega) (h τ hτ ρ hρ hM N hN X hX)
  have := hq.wr12_klDiv_le ha hβ (by omega : 0 < N) hae
  refine this.trans (le_of_eq ?_)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  congr 1
  field_simp

/-- **`KL(Q_N ‖ μ^{⊗N}) ≤ β C N^{s/d}`** for the modulated Gibbs law of the Riesz kernel
(`β ≥ 0`, `C` depends only on `(d, s, M)`). -/
theorem euc_klDiv_Q_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
        klDiv (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ))
          (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (β * (C * (N : ℝ) ^ (s / d))) := by
  obtain ⟨C, hC, h⟩ := euc_energy_lower hd hs hsd M
  refine ⟨C, hC, fun ρ hρ hM β hβ N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  obtain ⟨a, ha, hq⟩ := wr12_g_weak hd hs hsd hρ hM
  have hW := (hq.gibbsWellDefined_E ha hβ (by omega : 0 < N)).1
  have hQ : HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) =
      pairGibbsLawE (fun x y : Euc d => rieszKernel d s (x - y)) N β (HRS.Whole.withDensityReal ρ) :=
    (HRS.Whole.pairGibbs_diff (N := N) (HRS.Whole.rieszKernel d s) β
      (HRS.Whole.withDensityReal ρ)).symm.trans (pairGibbs_eq_pairGibbsLawE hW)
  rw [hQ]
  have hae : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ),
      -(C * (N : ℝ) ^ (s / d) / N) ≤
        modEnergyE (fun x y : Euc d => rieszKernel d s (x - y)) X (HRS.Whole.withDensityReal ρ) := by
    filter_upwards [ae_injective_pi_Euc (N := N) (wr12_atomless hd ρ)] with X hX
    exact wr12_div_le (by omega) (h ρ hρ hM N hN X hX)
  have := hq.wr12_klDiv_le ha hβ (by omega : 0 < N) hae
  refine this.trans (le_of_eq ?_)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  congr 1
  field_simp

/-- From an exchangeable law with `KL ≤ β C N^{s/d}` to `‖π₁ - μ‖_TV ≤ √(β C N^{s/d-1}/2)`. -/
theorem wr12_tv_first {s : ℝ} (hN : 1 ≤ N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (R : Measure (EucConfig d N)) [IsProbabilityMeasure R]
    (hex : HRS.External.Entropy.IsExchangeable R) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hkl : klDiv R (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (β * (C * (N : ℝ) ^ (s / d)))) :
    HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal R) μ ≤
      Real.sqrt (β * (C * (N : ℝ) ^ (s / d - 1)) / 2) := by
  have hN0 : 0 < N := hN
  have hK : 0 ≤ β * (C * (N : ℝ) ^ (s / d)) :=
    mul_nonneg hβ (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  have h := wr12_tv_of_kl μ R hex hK hkl ⟨0, hN0⟩
  unfold HRS.Whole.firstMarginal
  rw [dif_pos hN0]
  refine h.trans (le_of_eq ?_)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  congr 2
  rw [Real.rpow_sub_one hN'.ne']
  field_simp

theorem wr12_isProb_R0 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}
    {q : Euc d → Euc d → ℝ} (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) :
    IsProbabilityMeasure (pairGibbsLawE q N β μ) := by
  rw [h.wr12_eq_tilted ha hβ hN]
  exact isProbabilityMeasure_tilted (h.wr12_integrable_exp ha hβ hN)

/-- **Explicit TV bound for the weak reference**:
`‖π⁰_N - μ‖_TV ≤ √(β C N^{s/d-1}/2)`, uniformly in `ρ ≤ M`, `β ≥ 0`, `τ > 0`; `C = C(d, s, M)`. -/
theorem euc_tv_R0_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
        HRS.External.Entropy.tvDist
          (HRS.Whole.firstMarginal
            (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.withDensityReal ρ) ≤ Real.sqrt (β * (C * (N : ℝ) ^ (s / d - 1)) / 2) := by
  obtain ⟨C, hC, h⟩ := euc_klDiv_R0_le hd hs hsd M
  refine ⟨C, hC, fun τ hτ ρ hρ hM β hβ N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hq := wr12_qTau_weak hd hs hsd hτ hρ hM
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have ha : 0 ≤ M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2)) := by
    have := (Real.rpow_pos_of_pos hτ (((d : ℝ) - s) / 2)).le
    rw [show aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s from rfl]
    have := wr12_cq_nonneg (d := d) hs hsd
    positivity
  haveI := wr12_isProb_R0 hq ha hβ (by omega : 0 < N)
  exact wr12_tv_first hN _ _ (wr12_pairGibbsLawE_exchangeable _ β _) hβ hC (h τ hτ ρ hρ hM β hβ N hN)

/-- **Explicit TV bound for the Gibbs law**: `‖π_N - μ‖_TV ≤ √(β C N^{s/d-1}/2)` for
`π_N = firstMarginal Q_N`, `Q_N = modulatedGibbs g N β μ`, uniformly in `ρ ≤ M`, `β ≥ 0`. -/
theorem euc_tv_Q_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
        HRS.External.Entropy.tvDist
          (HRS.Whole.firstMarginal
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.withDensityReal ρ) ≤ Real.sqrt (β * (C * (N : ℝ) ^ (s / d - 1)) / 2) := by
  obtain ⟨C, hC, h⟩ := euc_klDiv_Q_le hd hs hsd M
  refine ⟨C, hC, fun ρ hρ hM β hβ N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  obtain ⟨a, ha, hq⟩ := wr12_g_weak hd hs hsd hρ hM
  have hW := (hq.gibbsWellDefined_E ha hβ (by omega : 0 < N)).1
  have hQ : HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) =
      pairGibbsLawE (fun x y : Euc d => rieszKernel d s (x - y)) N β (HRS.Whole.withDensityReal ρ) :=
    (HRS.Whole.pairGibbs_diff (N := N) (HRS.Whole.rieszKernel d s) β
      (HRS.Whole.withDensityReal ρ)).symm.trans (pairGibbs_eq_pairGibbsLawE hW)
  haveI := wr12_isProb_R0 hq ha hβ (by omega : 0 < N)
  have hkl := h ρ hρ hM β hβ N hN
  rw [hQ] at hkl ⊢
  exact wr12_tv_first hN _ _ (wr12_pairGibbsLawE_exchangeable _ β _) hβ hC hkl

/-! ### Total variation controls bounded test functions -/

section TVInt

open HRS.External.Entropy

variable {α : Type*} [MeasurableSpace α]

theorem wr12_abs_integral_sub_le_tvDist_of_nonneg (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {g : α → ℝ} (hgm : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hg0 : ∀ x, 0 ≤ g x) (hgM : ∀ x, g x ≤ M) :
    |∫ x, g x ∂P - ∫ x, g x ∂Q| ≤ M * tvDist P Q := by
  have hint : ∀ Pm : Measure α, IsProbabilityMeasure Pm → Integrable g Pm := fun Pm hR =>
    Integrable.of_bound hgm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgM x)
  have hform : ∀ Pm : Measure α, IsProbabilityMeasure Pm →
      ∫ x, g x ∂Pm = ∫ t in Ioc 0 M, Pm.real {a | t ≤ g a} :=
    fun Pm hR => (hint Pm hR).integral_eq_integral_Ioc_meas_le (Eventually.of_forall hg0)
      (Eventually.of_forall hgM)
  have hI : ∀ Pm : Measure α, IsProbabilityMeasure Pm →
      IntegrableOn (fun t : ℝ => Pm.real {a | t ≤ g a}) (Ioc 0 M) := by
    intro Pm hR
    refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.ennreal_toReal ?_
      exact Antitone.measurable (fun _ _ hst => measure_mono (fun _ h => le_trans hst h))
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  rw [hform P inferInstance, hform Q inferInstance,
    ← integral_sub (hI P inferInstance) (hI Q inferInstance)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) M)
    (f := fun t : ℝ => P.real {a | t ≤ g a} - Q.real {a | t ≤ g a}) (C := tvDist P Q)
    (by simp) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact abs_le_tvDist P Q (measurableSet_le measurable_const hgm))
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  simp [Measure.real, Real.volume_Ioc, hM]
  ring

/-- `|∫ f dP - ∫ f dQ| ≤ 2 M ‖P - Q‖_TV` for `|f| ≤ M`. -/
theorem wr12_abs_integral_sub_le_two_mul_tvDist (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {f : α → ℝ} (hfm : Measurable f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, |f x| ≤ M) :
    |∫ x, f x ∂P - ∫ x, f x ∂Q| ≤ 2 * M * tvDist P Q := by
  set fp : α → ℝ := fun x => max (f x) 0 with hfp
  set fn : α → ℝ := fun x => max (-f x) 0 with hfn
  have hpm : Measurable fp := hfm.max measurable_const
  have hnm : Measurable fn := hfm.neg.max measurable_const
  have hp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hn0 : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hpM : ∀ x, fp x ≤ M := fun x => max_le (le_trans (le_abs_self _) (hM x)) hM0
  have hnM : ∀ x, fn x ≤ M := fun x => max_le (le_trans (neg_le_abs _) (hM x)) hM0
  have hdec : ∀ x, f x = fp x - fn x := fun x => by
    simp only [hfp, hfn]
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hint : ∀ (Pm : Measure α), IsProbabilityMeasure Pm → ∀ {g : α → ℝ}, Measurable g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ M) → Integrable g Pm := fun Pm hR g hgm hg0 hgM =>
    Integrable.of_bound hgm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgM x)
  have e : ∀ Pm : Measure α, IsProbabilityMeasure Pm →
      ∫ x, f x ∂Pm = ∫ x, fp x ∂Pm - ∫ x, fn x ∂Pm := by
    intro Pm hR
    rw [← integral_sub (hint Pm hR hpm hp0 hpM) (hint Pm hR hnm hn0 hnM)]
    exact integral_congr_ae (Eventually.of_forall hdec)
  rw [e P inferInstance, e Q inferInstance]
  have h1 := wr12_abs_integral_sub_le_tvDist_of_nonneg P Q hpm hM0 hp0 hpM
  have h2 := wr12_abs_integral_sub_le_tvDist_of_nonneg P Q hnm hM0 hn0 hnM
  have : ∫ x, fp x ∂P - ∫ x, fn x ∂P - (∫ x, fp x ∂Q - ∫ x, fn x ∂Q) =
      (∫ x, fp x ∂P - ∫ x, fp x ∂Q) - (∫ x, fn x ∂P - ∫ x, fn x ∂Q) := by ring
  rw [this]
  calc _ ≤ |∫ x, fp x ∂P - ∫ x, fp x ∂Q| + |∫ x, fn x ∂P - ∫ x, fn x ∂Q| := abs_sub _ _
    _ ≤ M * tvDist P Q + M * tvDist P Q := add_le_add h1 h2
    _ = 2 * M * tvDist P Q := by ring

end TVInt

/-! ### The `H`-valued feature mean and the field bound -/

section FieldSmall

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem wr12_integrable_feat {Ψ : Euc d → H} {B : ℝ} (h : CalFeat Ψ B) (P0 : Measure (Euc d))
    [IsFiniteMeasure P0] : Integrable Ψ P0 :=
  Integrable.of_bound h.cont.aestronglyMeasurable B (Eventually.of_forall h.bound)

/-- `‖∫ Ψ dP - ∫ Ψ dQ‖ ≤ 2 B ‖P - Q‖_TV` for a continuous `H`-valued `Ψ` with `‖Ψ‖ ≤ B`. -/
theorem wr12_norm_integral_sub_le (P Q : Measure (Euc d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Ψ : Euc d → H} {B : ℝ} (h : CalFeat Ψ B) :
    ‖∫ x, Ψ x ∂P - ∫ x, Ψ x ∂Q‖ ≤ 2 * B * HRS.External.Entropy.tvDist P Q := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h.bound 0)
  have htv := HRS.External.Entropy.tvDist_nonneg P Q
  set w : H := ∫ x, Ψ x ∂P - ∫ x, Ψ x ∂Q with hw
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]; positivity
  · set v : H := (‖w‖⁻¹) • w with hv
    have hvn : ‖v‖ = 1 := norm_smul_inv_norm hw0
    have hfm : Measurable (fun x => inner ℝ v (Ψ x)) :=
      (continuous_const.inner h.cont).measurable
    have hf : ∀ x, |inner ℝ v (Ψ x)| ≤ B := fun x => by
      have := abs_real_inner_le_norm v (Ψ x)
      rw [hvn, one_mul] at this
      exact this.trans (h.bound x)
    have key := wr12_abs_integral_sub_le_two_mul_tvDist P Q hfm hB hf
    rw [integral_inner (wr12_integrable_feat h P) v, integral_inner (wr12_integrable_feat h Q) v,
      ← inner_sub_right] at key
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have e : inner ℝ v w = ‖w‖ := by
      rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [← hw, e, abs_of_nonneg hn.le] at key
    exact key

/-- `E_{R0}[μ_N(Ξ)] = ∫ Ψ dπ - ∫ Ψ dμ` for an exchangeable `P0` with first marginal `π`. -/
theorem wr12_integral_empXi (hN : 1 ≤ N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (P0 : Measure (EucConfig d N)) [IsProbabilityMeasure P0]
    (hex : HRS.External.Entropy.IsExchangeable P0) {Ψ : Euc d → H} {B : ℝ} (h : CalFeat Ψ B) :
    ∫ X, empXi μ Ψ X ∂P0 =
      ∫ x, Ψ x ∂(HRS.Whole.firstMarginal P0) - ∫ x, Ψ x ∂μ := by
  have hN0 : 0 < N := hN
  have hmI : ∀ i : Fin N, Measurable (fun X : EucConfig d N => X i) := fun i => measurable_pi_apply i
  have hXc : Continuous (Xi μ Ψ) := h.cont.sub continuous_const
  have hXi : ∀ i : Fin N, Integrable (fun X : EucConfig d N => Xi μ Ψ (X i)) P0 := fun i => by
    refine Integrable.of_bound ((hXc.comp (continuous_apply i)).aestronglyMeasurable) (2 * B)
      (Eventually.of_forall fun X => ?_)
    have h1 : ‖∫ y, Ψ y ∂μ‖ ≤ B := by
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := B)
        (Eventually.of_forall h.bound)
      simpa using this
    calc ‖Xi μ Ψ (X i)‖ ≤ ‖Ψ (X i)‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
      _ ≤ 2 * B := by have := h.bound (X i); linarith
  have hπ : ∀ i : Fin N, P0.map (fun X : EucConfig d N => X i) =
      HRS.Whole.firstMarginal P0 := fun i => by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos hN0]
    exact hex.marginal_eq i ⟨0, hN0⟩
  have hint : ∀ i : Fin N, ∫ X, Xi μ Ψ (X i) ∂P0 = ∫ x, Xi μ Ψ x ∂(HRS.Whole.firstMarginal P0) := fun i => by
    rw [← hπ i, integral_map (hmI i).aemeasurable hXc.aestronglyMeasurable]
  haveI : IsProbabilityMeasure (HRS.Whole.firstMarginal P0) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos hN0]
    exact (Measure.isProbabilityMeasure_map_iff (hmI ⟨0, hN0⟩).aemeasurable).2 inferInstance
  have hsub : ∫ x, Xi μ Ψ x ∂(HRS.Whole.firstMarginal P0) =
      ∫ x, Ψ x ∂(HRS.Whole.firstMarginal P0) - ∫ x, Ψ x ∂μ := by
    unfold Xi
    rw [integral_sub (wr12_integrable_feat h _) (integrable_const _), integral_const]
    simp
  unfold empXi
  rw [integral_smul, integral_finset_sum _ (fun i _ => hXi i)]
  simp_rw [hint, hsub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ hN', one_smul]

theorem wr12_norm_Xi_le (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ}
    (h : CalFeat Ψ B) (x : Euc d) : ‖Xi μ Ψ x‖ ≤ 2 * B := by
  have h1 : ‖∫ y, Ψ y ∂μ‖ ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := B)
      (Eventually.of_forall h.bound)
    simpa using this
  calc ‖Xi μ Ψ x‖ ≤ ‖Ψ x‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
    _ ≤ 2 * B := by have := h.bound x; linarith

/-- `‖E_R[μ_N(Ξ)]‖ ≤ 2 B ‖π - μ‖_TV` for an exchangeable `P0`. -/
theorem wr12_norm_empXi_le (hN : 1 ≤ N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (P0 : Measure (EucConfig d N)) [IsProbabilityMeasure P0]
    (hex : HRS.External.Entropy.IsExchangeable P0) {Ψ : Euc d → H} {B : ℝ} (h : CalFeat Ψ B) :
    ‖∫ X, empXi μ Ψ X ∂P0‖ ≤
      2 * B * HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal P0) μ := by
  have hN0 : 0 < N := hN
  haveI : IsProbabilityMeasure (HRS.Whole.firstMarginal P0) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos hN0]
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_pi_apply (⟨0, hN0⟩ : Fin N)).aemeasurable).2 inferInstance
  rw [wr12_integral_empXi hN μ P0 hex h]
  exact wr12_norm_integral_sub_le _ _ h

end FieldSmall

theorem wr12_final_arith {K Y n : ℝ} (hK : 0 ≤ K) (hY : 0 ≤ Y) (hn : 0 ≤ n)
    (hnδ : n ≤ 1 / (K ^ 2 * Y + 1)) : K * Real.sqrt (Y * n) ≤ 1 := by
  have hpos : 0 < K ^ 2 * Y + 1 := by positivity
  have hu : 0 ≤ Real.sqrt (Y * n) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (Y * n) ^ 2 = Y * n := Real.sq_sqrt (mul_nonneg hY hn)
  have h1 : n * (K ^ 2 * Y + 1) ≤ 1 := by
    rw [le_div_iff₀ hpos] at hnδ; exact hnδ
  have h2 : (K * Real.sqrt (Y * n)) ^ 2 ≤ 1 := by
    rw [mul_pow, hsq]
    nlinarith [mul_nonneg (sq_nonneg K) (mul_nonneg hY hn), sq_nonneg K, hn]
  exact (pow_le_one_iff_of_nonneg (mul_nonneg hK hu) two_ne_zero).1 h2

/-- **Uniform smallness of the calibrated field** (T5, item 5).  For `H` a real Hilbert space there is
`N0` (depending only on `(d, s, βp, M, B)`; not on `τ`, `ρ`, `β`, `Ψ`, `H`) such that for every
probability density `ρ ≤ M`, `β ∈ (0, βp]`, `N ≥ N0`, every continuous feature map `Ψ` with `‖Ψ‖ ≤ B`,
and every `t` with `‖t‖ ≤ β ‖E_{R0}[μ_N(Ξ)]‖` (the content of `tN_norm_le`), one has
`|⟪t, Ξ x⟫| ≤ 1` for all `x`.  Here `Ξ = Xi μ Ψ`, `‖Ξ‖ ≤ 2B` (`wr12_norm_Xi_le`), and
`‖E_{R0}[μ_N(Ξ)]‖ ≤ 2 B ‖π⁰_N - μ‖_TV ≤ 2 B √(β C N^{s/d-1}/2)`. -/
theorem euc_field_small {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (βp M B : ℝ) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ τ : ℝ, 0 < τ → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
        ∀ Ψ : Euc d → H, CalFeat Ψ B → ∀ t : H,
          ‖t‖ ≤ β * ‖∫ X, empXi (HRS.Whole.withDensityReal ρ) Ψ X
            ∂(pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β
              (HRS.Whole.withDensityReal ρ))‖ →
          ∀ x : Euc d, |inner ℝ t (Xi (HRS.Whole.withDensityReal ρ) Ψ x)| ≤ 1 := by
  obtain ⟨C, hC, hTV⟩ := euc_tv_R0_le hd hs hsd M
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hy : 0 < 1 - s / d := by
    rw [sub_pos, div_lt_one hd0]; exact hsd
  set K : ℝ := 4 * B ^ 2 * max βp 0 with hKdef
  set Y : ℝ := max βp 0 * C / 2 with hYdef
  have hK : 0 ≤ K := by positivity
  have hY : 0 ≤ Y := by positivity
  have hδ : 0 < 1 / (K ^ 2 * Y + 1) := by positivity
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - s / d))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 _ hδ)
  refine ⟨max N1 1, le_max_right _ _, fun τ hτ ρ hρ hM β hβ hβp N hN Ψ hΨ t ht x => ?_⟩
  have hN1' : 1 ≤ N := le_trans (le_max_right _ _) hN
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hq := wr12_qTau_weak hd hs hsd hτ hρ hM
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have ha : 0 ≤ M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2)) := by
    have := (Real.rpow_pos_of_pos hτ (((d : ℝ) - s) / 2)).le
    rw [show aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s from rfl]
    have := wr12_cq_nonneg (d := d) hs hsd
    positivity
  haveI := wr12_isProb_R0 hq ha hβ.le (by omega : 0 < N)
  have hex := wr12_pairGibbsLawE_exchangeable (N := N) (fun w : Euc d => qTau d s τ w) β
    (HRS.Whole.withDensityReal ρ)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hΨ.bound 0)
  have h1 := wr12_norm_empXi_le hN1' (HRS.Whole.withDensityReal ρ) _ hex hΨ
  have h2 := hTV τ hτ ρ hρ hM β hβ.le N hN1'
  have hNe : (N : ℝ) ^ (s / d - 1) ≤ 1 / (K ^ 2 * Y + 1) := by
    have := hN1 N (le_trans (le_max_left _ _) hN)
    have e : s / d - 1 = -(1 - s / d) := by ring
    rw [e]; exact this.le
  have hNe0 : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hβm : β ≤ max βp 0 := hβp.trans (le_max_left _ _)
  have h3 : Real.sqrt (β * (C * (N : ℝ) ^ (s / d - 1)) / 2) ≤
      Real.sqrt (Y * (N : ℝ) ^ (s / d - 1)) := by
    apply Real.sqrt_le_sqrt
    have : β * (C * (N : ℝ) ^ (s / d - 1)) ≤ max βp 0 * (C * (N : ℝ) ^ (s / d - 1)) :=
      mul_le_mul_of_nonneg_right hβm (mul_nonneg hC hNe0)
    rw [hYdef]; nlinarith
  have h4 := wr12_final_arith hK hY hNe0 hNe
  have hXi := wr12_norm_Xi_le (HRS.Whole.withDensityReal ρ) hΨ x
  have htv := HRS.External.Entropy.tvDist_nonneg (HRS.Whole.firstMarginal
    (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β (HRS.Whole.withDensityReal ρ)))
    (HRS.Whole.withDensityReal ρ)
  calc |inner ℝ t (Xi (HRS.Whole.withDensityReal ρ) Ψ x)|
      ≤ ‖t‖ * ‖Xi (HRS.Whole.withDensityReal ρ) Ψ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * B * HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal
          (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.withDensityReal ρ))) * (2 * B) := by
        gcongr
        exact ht.trans (mul_le_mul_of_nonneg_left h1 hβ.le)
    _ = (4 * B ^ 2 * β) * HRS.External.Entropy.tvDist (HRS.Whole.firstMarginal
          (pairGibbsLawE (fun x y : Euc d => qTau d s τ (x - y)) N β (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.withDensityReal ρ) := by ring
    _ ≤ K * Real.sqrt (Y * (N : ℝ) ^ (s / d - 1)) := by
        apply mul_le_mul _ (h2.trans h3) htv hK
        rw [hKdef]
        have : 0 ≤ 4 * B ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hβm this
    _ ≤ 1 := h4

end HRS.MS.Wr
