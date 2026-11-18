/-
# HRS.Equilibrium.ReferenceSmallness -- smallness of the calibration field (EXT-5, E7 part 2)

Source: main paper, weak reference `R⁰_N` and calibration (`A:eq:coarse-entropy`, TeX lines 3405-3545);
plan `docs/external/variance-plan.md`, §2 "Calibration / smallness" (ii) and §3 row E7.

For a nonnegative even kernel `q` with `∫ q < ∞` (in the application `q = (weakSplit d s τ L).q`),
the weak reference is
`dR⁰_N ∝ exp[β N μ_N(q*μ) - (β/N) ∑_{i<j} q(x_i - x_j)] dμ^{⊗N}` (`R0small`).
Proved here:
1. `R0small_isExchangeable`;
2. the entropy identity `KL(R⁰_N ‖ μ^N) = -β N E_{R⁰}[F_N^q] - log K^q` (`klDiv_R0small`);
3. the modulated-energy lower bound `F_N^q ≥ -C a_N` (`modulatedEnergy_weakSplit_ge`), by the
   heat-truncation argument for `q = g - g_L + c` (Fourier coefficients `ĉ_ε - ĝ_τ ≥ 0` for `ε ≤ τ`);
4. Jensen `K^q ≥ 1` and `KL(R⁰_N ‖ μ^N) = o(N)`;
5. `‖π⁰_N - μ‖_TV → 0` and the smallness `sup_x |t_N · Ξ(x)| ≤ 1`.
-/
import HRS.Energy.Coercivity
import HRS.Equilibrium.HeatSplit
import HRS.External.Entropy

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.External.RefSmall

open HRS

variable {d : ℕ}

/-! ### The weak reference -/

/-- The weak reference `R⁰_N`: density `∝ exp[β N μ_N(q*μ) - (β/N) ∑_{i<j} q(x_i - x_j)]` with respect
to `μ^{⊗N}` (`N μ_N(q*μ) = ∑_i (q*μ)(x_i)`), written with the repository's `tiltMeasure`. -/
def R0small (q : Torus d → ℝ) (β : ℝ) (μ : Measure (Torus d)) (N : ℕ) : Measure (Config d N) :=
  tiltMeasure (Measure.pi fun _ : Fin N => μ)
    fun X => β * ∑ i, convMeasure q μ (X i) - (β / N) * pairSum q X

/-- The log-density (before normalisation) of the weak reference. -/
def R0w (q : Torus d → ℝ) (β : ℝ) (μ : Measure (Torus d)) (N : ℕ) (X : Config d N) : ℝ :=
  β * ∑ i, convMeasure q μ (X i) - (β / N) * pairSum q X

lemma R0small_eq (q : Torus d → ℝ) (β : ℝ) (μ : Measure (Torus d)) (N : ℕ) :
    R0small q β μ N = tiltMeasure (Measure.pi fun _ : Fin N => μ) (R0w q β μ N) := rfl

lemma tiltMeasure_eq_tilted {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (w : α → ℝ) (hw : Measurable w) (W : ℝ) (hW : ∀ a, w a ≤ W) :
    tiltMeasure P w = P.tilted w := by
  have hint : Integrable (fun a => Real.exp (w a)) P := by
    refine Integrable.mono' (integrable_const (Real.exp W)) (Real.measurable_exp.comp hw).aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hW a)
  have hZ : 0 < ∫ a, Real.exp (w a) ∂P := integral_exp_pos hint
  have hZl : ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P = ENNReal.ofReal (∫ a, Real.exp (w a) ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun a => (Real.exp_pos _).le)).symm
  unfold tiltMeasure Measure.tilted
  rw [hZl]
  ext s hs
  rw [Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs, smul_eq_mul]
  have hmeas : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
  have : ∀ a, ENNReal.ofReal (Real.exp (w a) / ∫ a, Real.exp (w a) ∂P) =
      (ENNReal.ofReal (∫ a, Real.exp (w a) ∂P))⁻¹ * ENNReal.ofReal (Real.exp (w a)) := by
    intro a
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), ENNReal.ofReal_inv_of_pos hZ]
  simp_rw [this]
  rw [lintegral_const_mul _ hmeas]

/-! ### Exchangeability -/

lemma pi_map_perm {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {N : ℕ}
    (σ : Equiv.Perm (Fin N)) :
    (Measure.pi fun _ : Fin N => μ).map (fun (X : Fin N → E) i => X (σ i)) =
      Measure.pi fun _ : Fin N => μ := by
  have h := (measurePreserving_arrowCongr' (fun _ : Fin N => μ) (fun _ : Fin N => μ) σ.symm
    (MeasurableEquiv.refl E) (fun _ => MeasurePreserving.id μ)).map_eq
  have e : (fun (X : Fin N → E) i => X (σ i)) =
      ⇑(MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl E)) := by
    funext X i
    simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  rw [e]; exact h

lemma tiltMeasure_map_perm {α : Type*} [MeasurableSpace α] (P : Measure α) (w : α → ℝ)
    (hwm : Measurable w) (T : α → α)
    (hT : Measurable T) (hP : P.map T = P) (hw : ∀ a, w (T a) = w a) :
    (tiltMeasure P w).map T = tiltMeasure P w := by
  unfold tiltMeasure
  rw [Measure.map_smul]
  congr 1
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs]
  have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hwm)
  calc ∫⁻ a in T ⁻¹' s, ENNReal.ofReal (Real.exp (w a)) ∂P
      = ∫⁻ a, (T ⁻¹' s).indicator (fun a => ENNReal.ofReal (Real.exp (w a))) a ∂P :=
        (lintegral_indicator (hT hs) _).symm
    _ = ∫⁻ a, (s.indicator fun a => ENNReal.ofReal (Real.exp (w a))) (T a) ∂P := by
        congr 1; funext a; simp only [Set.indicator, Set.mem_preimage, hw a]; rfl
    _ = ∫⁻ b, (s.indicator fun a => ENNReal.ofReal (Real.exp (w a))) b ∂(P.map T) :=
        (lintegral_map (hm.indicator hs) hT).symm
    _ = ∫⁻ a in s, ENNReal.ofReal (Real.exp (w a)) ∂P := by
        rw [hP, lintegral_indicator hs]
  exact hT.aemeasurable

lemma pairSum_eq_half {q : Torus d → ℝ} (hq : ∀ x, q (-x) = q x) {N : ℕ} (X : Config d N) :
    pairSum q X = (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j) := by
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, q (X i - X j) =
      ∑ j, (if i < j then q (X i - X j) else 0) + ∑ j, (if j < i then q (X i - X j) else 0) := by
    intro i
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_erase (f := fun j => (if i < j then q (X i - X j) else 0) +
      (if j < i then q (X i - X j) else 0)) Finset.univ (a := i) (by simp)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hji with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]
  have hA : pairSum q X = ∑ i, ∑ j, (if i < j then q (X i - X j) else 0) := by
    unfold pairSum
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
  have hB : ∑ i, ∑ j, (if j < i then q (X i - X j) else 0) = pairSum q X := by
    rw [hA, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · have : q (X j - X i) = q (X i - X j) := by
        rw [← hq (X i - X j), neg_sub]
      simp [h, this]
    · simp [h]
  simp_rw [h1]
  rw [Finset.sum_add_distrib, hB, ← hA]
  ring

lemma R0w_perm {q : Torus d → ℝ} (hq : ∀ x, q (-x) = q x) (β : ℝ) (μ : Measure (Torus d)) {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (X : Config d N) :
    R0w q β μ N (fun i => X (σ i)) = R0w q β μ N X := by
  unfold R0w
  have e1 : ∑ i, convMeasure q μ (X (σ i)) = ∑ i, convMeasure q μ (X i) :=
    Equiv.sum_comp σ (fun i => convMeasure q μ (X i))
  have e2 : ∑ i, ∑ j ∈ Finset.univ.erase i, q (X (σ i) - X (σ j)) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j) := by
    have key : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, q (X (σ i) - X (σ j)) =
        ∑ b ∈ Finset.univ.erase (σ i), q (X (σ i) - X b) := by
      intro i
      refine Finset.sum_bij (fun j _ => σ j) (fun j hj => ?_) (fun a _ b _ h => σ.injective h)
        (fun b hb => ?_) (fun j _ => rfl)
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
        exact fun h => hj (σ.injective h)
      · refine ⟨σ.symm b, ?_, by simp⟩
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb ⊢
        intro h; apply hb; rw [← h]; simp
    simp_rw [key]
    exact Equiv.sum_comp σ (fun a => ∑ b ∈ Finset.univ.erase a, q (X a - X b))
  rw [pairSum_eq_half hq, pairSum_eq_half hq, e1, e2]

theorem R0small_isExchangeable {q : Torus d → ℝ} (hqm : Measurable q) (hq : ∀ x, q (-x) = q x)
    (β : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    HRS.External.Entropy.IsExchangeable (R0small q β μ N) := by
  intro σ
  have hm : Measurable (R0w q β μ N) := by
    unfold R0w
    refine Measurable.sub ?_ ?_
    · exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        (PoleCavityAux.measurable_convMeasure hqm μ).comp (measurable_pi_apply i))
    · exact measurable_const.mul (PoleCavityAux.measurable_pairSum hqm)
  exact tiltMeasure_map_perm _ _ hm _
    (measurable_pi_iff.2 fun k => measurable_pi_apply _) (pi_map_perm μ σ) (R0w_perm hq β μ σ)

/-! ### Standing hypotheses on the kernel `q` and the density `ρ` -/

/-- The properties of the nonnegative part `q` of the heat split that are used for the entropy
bookkeeping (all of them are proved for `(weakSplit d s τ L).q`, see `smallKernel_weakSplit`). -/
structure SmallKernel (q : Torus d → ℝ) : Prop where
  meas : Measurable q
  nonneg : ∀ x, 0 ≤ q x
  integrable : Integrable q
  even : ∀ x, q (-x) = q x

section Ctx

variable {q ρ : Torus d → ℝ} {Λ : ℝ}

lemma SmallKernel.integrable_conv (hq : SmallKernel q) (hΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    Integrable (fun y => q (x - y)) (withDensityReal ρ) :=
  CoercAux.integrable_conv_density hΛ hq.meas hq.integrable x

lemma SmallKernel.conv_nonneg (hq : SmallKernel q) (μ : Measure (Torus d)) (x : Torus d) :
    0 ≤ convMeasure q μ x :=
  integral_nonneg fun y => hq.nonneg _

lemma SmallKernel.conv_le (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    convMeasure q (withDensityReal ρ) x ≤ Λ * ∫ y, q y :=
  CoercAux.integral_conv_density_le ((hρ.nonneg 0).trans (hΛ 0)) hΛ hq.nonneg hq.meas hq.integrable x

lemma SmallKernel.integrable_prod (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) :
    Integrable (fun p : Torus d × Torus d => q (p.1 - p.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  haveI := isProb_withDensityReal hρ
  have hm : Measurable fun p : Torus d × Torus d => q (p.1 - p.2) :=
    hq.meas.comp (measurable_fst.sub measurable_snd)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => hq.integrable_conv hΛ x, ?_⟩
  have hb : ∀ x, ∫ y, ‖q (x - y)‖ ∂(withDensityReal ρ) ≤ Λ * ∫ y, q y := fun x => by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hq.nonneg _)]
    exact hq.conv_le hρ hΛ x
  refine Integrable.mono' (integrable_const (Λ * ∫ y, q y)) ?_ (Eventually.of_forall fun x => ?_)
  · exact (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hb x

lemma pairSum_nonneg (hq : SmallKernel q) {N : ℕ} (X : Config d N) : 0 ≤ pairSum q X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hq.nonneg _

lemma SmallKernel.measurable_R0w (hq : SmallKernel q) (β : ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (N : ℕ) : Measurable (R0w q β μ N) := by
  unfold R0w
  refine Measurable.sub ?_ ?_
  · exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (PoleCavityAux.measurable_convMeasure hq.meas μ).comp (measurable_pi_apply i))
  · exact measurable_const.mul (PoleCavityAux.measurable_pairSum hq.meas)

lemma SmallKernel.R0w_le (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ}
    (hβ : 0 ≤ β) (N : ℕ) (X : Config d N) :
    R0w q β (withDensityReal ρ) N X ≤ β * N * (Λ * ∫ y, q y) := by
  unfold R0w
  have h1 : ∑ i, convMeasure q (withDensityReal ρ) (X i) ≤ N * (Λ * ∫ y, q y) := by
    calc ∑ i, convMeasure q (withDensityReal ρ) (X i) ≤ ∑ _i : Fin N, Λ * ∫ y, q y :=
          Finset.sum_le_sum fun i _ => hq.conv_le hρ hΛ _
      _ = N * (Λ * ∫ y, q y) := by simp
  have h2 : 0 ≤ (β / N) * pairSum q X :=
    mul_nonneg (div_nonneg hβ (Nat.cast_nonneg _)) (pairSum_nonneg hq X)
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ]

lemma SmallKernel.isProb_R0small (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) : IsProbabilityMeasure (R0small q β (withDensityReal ρ) N) := by
  haveI := isProb_withDensityReal hρ
  exact PoleCavityAux.tilt_isProb _ _ (hq.measurable_R0w β _ N) _ (hq.R0w_le hρ hΛ hβ N)

lemma SmallKernel.integrable_pairSum (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (N : ℕ) : Integrable (fun X : Config d N => pairSum q X)
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  unfold pairSum
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
  exact integrable_pair_comp (withDensityReal ρ) hij (H := fun p => q (p.1 - p.2))
    (hq.integrable_prod hρ hΛ)

/-- `G = ∬ q(x - y) dμ dμ`. -/
def dblInt (q : Torus d → ℝ) (μ : Measure (Torus d)) : ℝ := ∫ x, ∫ y, q (x - y) ∂μ ∂μ

lemma SmallKernel.R0w_eq (hq : SmallKernel q) (hρ : IsProbDensity ρ) (β : ℝ) (N : ℕ)
    (X : Config d N) :
    R0w q β (withDensityReal ρ) N X =
      -β * N * modulatedEnergyKernel q X (withDensityReal ρ) +
        (β * N / 2) * dblInt q (withDensityReal ρ) := by
  have h := energy_identity q hq.even ρ hρ.measurable hρ.nonneg X
  have hc : ∀ i, convMeasure q (withDensityReal ρ) (X i) = convFun q ρ (X i) := by
    intro i
    unfold convMeasure
    rw [integral_withDensityReal_eq ρ hρ.measurable hρ.nonneg]
    unfold convFun
    exact integral_congr_ae (Eventually.of_forall fun y => by simp [mul_comm])
  unfold R0w dblInt
  simp_rw [hc]
  unfold pairSum at *
  have : -β * N * modulatedEnergyKernel q X (withDensityReal ρ) =
      -β * ((N : ℝ) * modulatedEnergyKernel q X (withDensityReal ρ)) := by ring
  rw [this, h]
  ring

lemma SmallKernel.measurable_energy (hq : SmallKernel q) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (N : ℕ) :
    Measurable fun X : Config d N => modulatedEnergyKernel q X μ := by
  unfold modulatedEnergyKernel modulatedEnergy
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact hq.meas.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (PoleCavityAux.measurable_convMeasure hq.meas μ).comp (measurable_pi_apply i)

lemma SmallKernel.integrable_energy (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (N : ℕ) : Integrable (fun X : Config d N => modulatedEnergyKernel q X (withDensityReal ρ))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => q (X i - X j)) (Measure.pi fun _ : Fin N => withDensityReal ρ) :=
    fun i j hij => integrable_pair_comp _ hij (H := fun p => q (p.1 - p.2)) (hq.integrable_prod hρ hΛ)
  have hconv : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, q (X i - y) ∂(withDensityReal ρ))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
    intro i
    refine Integrable.mono' (integrable_const (Λ * ∫ y, q y)) ?_ (Eventually.of_forall fun X => ?_)
    · exact ((PoleCavityAux.measurable_convMeasure hq.meas (withDensityReal ρ)).comp
        (measurable_pi_apply i)).aestronglyMeasurable
    · show ‖convMeasure q (withDensityReal ρ) (X i)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (hq.conv_nonneg (withDensityReal ρ) (X i))]
      exact hq.conv_le hρ hΛ _
  unfold modulatedEnergyKernel modulatedEnergy
  refine Integrable.add (Integrable.sub ?_ ?_) (integrable_const _)
  · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm).const_mul _
  · exact (integrable_finsetSum _ fun i _ => hconv i).const_mul _

lemma SmallKernel.integrable_R0w_exp (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    Integrable (fun X : Config d N => Real.exp (R0w q β (withDensityReal ρ) N X))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  refine Integrable.mono' (integrable_const (Real.exp (β * N * (Λ * ∫ y, q y))))
    (Real.measurable_exp.comp (hq.measurable_R0w β _ N)).aestronglyMeasurable (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (hq.R0w_le hρ hΛ hβ N X)

/-- The normaliser of the weak reference, `Z = ∫ exp(w) dμ^N = e^{βNG/2} K^q`. -/
lemma SmallKernel.normalizer_eq (hq : SmallKernel q) (hρ : IsProbDensity ρ) (β : ℝ) (N : ℕ) :
    ∫ X, Real.exp (R0w q β (withDensityReal ρ) N X) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) =
      gibbsNormalizer q N β (withDensityReal ρ) *
        Real.exp (β * N / 2 * dblInt q (withDensityReal ρ)) := by
  unfold gibbsNormalizer
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only
  rw [hq.R0w_eq hρ, ← Real.exp_add]

open InformationTheory in
/-- **Entropy identity** for the weak reference:
`KL(R⁰_N ‖ μ^{⊗N}) = -β N E_{R⁰_N}[F_N^q(·, μ)] - log K^q_{N,β}(μ)`, with
`K^q_{N,β}(μ) = ∫ exp(-β N F_N^q) dμ^{⊗N}` (`gibbsNormalizer`). -/
theorem klDiv_R0small (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ}
    (hβ : 0 ≤ β) (N : ℕ) :
    klDiv (R0small q β (withDensityReal ρ) N) (Measure.pi fun _ : Fin N => withDensityReal ρ) =
      ENNReal.ofReal (-β * N * ∫ X, modulatedEnergyKernel q X (withDensityReal ρ)
          ∂(R0small q β (withDensityReal ρ) N)
        - Real.log (gibbsNormalizer q N β (withDensityReal ρ))) := by
  haveI hμ := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμdef
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  set w := R0w q β μ N with hw
  set R := R0small q β μ N with hRdef
  haveI hRp : IsProbabilityMeasure R := hq.isProb_R0small hρ hΛ hβ N
  have hR : R = P.tilted w :=
    tiltMeasure_eq_tilted P w (hq.measurable_R0w β μ N) _ (hq.R0w_le hρ hΛ hβ N)
  have hexp : Integrable (fun X => Real.exp (w X)) P := hq.integrable_R0w_exp hρ hΛ hβ N
  set Z := ∫ X, Real.exp (w X) ∂P with hZ
  have hZpos : 0 < Z := integral_exp_pos hexp
  have hF : Integrable (fun X : Config d N => modulatedEnergyKernel q X μ) P :=
    hq.integrable_energy hρ hΛ N
  have hFR : Integrable (fun X : Config d N => modulatedEnergyKernel q X μ) R := by
    rw [hR, integrable_tilted_iff hexp]
    refine Integrable.bdd_mul (c := Real.exp (β * N * (Λ * ∫ y, q y))) hF
      (Real.measurable_exp.comp (hq.measurable_R0w β μ N)).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hq.R0w_le hρ hΛ hβ N X)
  have hweq : w = fun X => -β * N * modulatedEnergyKernel q X μ + (β * N / 2) * dblInt q μ := by
    funext X; exact hq.R0w_eq hρ β N X
  have hwR : Integrable w R := by
    rw [hweq]; exact (hFR.const_mul _).add (integrable_const _)
  have hac : R ≪ P := by rw [hR]; exact tilted_absolutelyContinuous P w
  have hllr : llr R P =ᵐ[R] fun X => w X - Real.log Z := by
    have := log_rnDeriv_tilted_left_self hexp
    rw [← hR] at this
    exact hac.ae_le this
  have hllrI : Integrable (llr R P) R := (hwR.sub (integrable_const _)).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hllrI]
  congr 1
  have hZeq := hq.normalizer_eq hρ β N
  set K := gibbsNormalizer q N β μ with hK
  set G := dblInt q μ with hG
  have hKpos : 0 < K := by
    have h1 : 0 < K * Real.exp (β * N / 2 * G) := by rw [← hZeq]; exact hZpos
    exact pos_of_mul_pos_left h1 (Real.exp_pos _).le |> fun h => by
      by_contra hneg
      have : K * Real.exp (β * N / 2 * G) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (Real.exp_pos _).le
      linarith
  have hlogZ : Real.log Z = Real.log K + β * N / 2 * G := by
    rw [hZ, hZeq, Real.log_mul hKpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hint : ∫ X, llr R P X ∂(R) = ∫ X, w X ∂(R) - Real.log Z := by
    rw [integral_congr_ae hllr, integral_sub hwR (integrable_const _), integral_const]
    simp
  have hw' : ∫ X, w X ∂(R) = -β * N * ∫ X, modulatedEnergyKernel q X μ ∂(R) + (β * N / 2) * G := by
    rw [hweq]
    simp only
    rw [integral_add (hFR.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp
  have h1 : P.real Set.univ = 1 := by simp [Measure.real]
  have h2 : R.real Set.univ = 1 := by simp [Measure.real]
  rw [h1, h2, hint, hw', hlogZ]
  ring

end Ctx

/-! ### The lower bound on the modulated energy: an abstract form -/

section LowerBound

variable {q n : Torus d → ℝ} {e : Lattice d → ℝ} {ρ : Torus d → ℝ} {c B Λ : ℝ}

lemma continuous_trigSum (hes : Summable fun k => |e k|) : Continuous (CoercAux.trigSum e) := by
  unfold CoercAux.trigSum
  refine continuous_tsum (u := fun k => |e k|) (fun k => continuous_const.mul (Torus.continuous_cosMode k))
    hes (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |e k| * |Torus.cosMode k x| ≤ |e k| * 1 :=
        mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (abs_nonneg _)
    _ = _ := mul_one _

lemma ae_ne_withDensity (hd : 1 ≤ d) (hρ : IsProbDensity ρ) (x : Torus d) :
    ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := by
  have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
    rw [ae_iff]
    have := volume_singleton_torus hd x
    simpa using this
  exact withDensity_absolutelyContinuous _ _ h0

/-- Convolution bounds for the near part `n` (`-B ≤ n`, `∫ n = 0`). -/
lemma conv_near_bounds (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (hn_meas : Measurable n) (hn_int : Integrable n) (hnB : ∀ z, -B ≤ n z) (hB : 0 ≤ B)
    (hn0 : ∫ z, n z = 0) (x : Torus d) :
    -B ≤ ∫ y, n (x - y) ∂(withDensityReal ρ) ∧ ∫ y, n (x - y) ∂(withDensityReal ρ) ≤ Λ * B := by
  haveI := isProb_withDensityReal hρ
  have hint := CoercAux.integrable_conv_density hΛ hn_meas hn_int x
  refine ⟨?_, ?_⟩
  · have := integral_mono (integrable_const (-B)) hint (fun y => hnB (x - y))
    simpa using this
  · set H : Torus d → ℝ := fun z => n z + B with hH
    have hH0 : ∀ z, 0 ≤ H z := fun z => by have := hnB z; simp only [hH]; linarith
    have hHm : Measurable H := hn_meas.add measurable_const
    have hHi : Integrable H := hn_int.add (integrable_const _)
    have h1 := CoercAux.integral_conv_density_le ((hρ.nonneg 0).trans (hΛ 0)) hΛ hH0 hHm hHi x
    have h2 : ∫ y, H y = B := by
      simp only [hH]
      rw [integral_add hn_int (integrable_const _), hn0]
      simp
    have h3 : ∫ y, H (x - y) ∂(withDensityReal ρ) = ∫ y, n (x - y) ∂(withDensityReal ρ) + B := by
      simp only [hH]
      rw [integral_add hint (integrable_const _)]
      simp
    rw [h2, h3] at h1
    nlinarith

theorem energy_lower_abstract (hd : 1 ≤ d) (hq : SmallKernel q) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) (he0 : ∀ k, 0 ≤ e k) (hes : Summable e)
    (hn_meas : Measurable n) (hn_int : Integrable n) (hnB : ∀ z, -B ≤ n z) (hB : 0 ≤ B)
    (hn0 : ∫ z, n z = 0)
    (hqe : ∀ z, z ≠ 0 → q z = CoercAux.trigSum e z + c + n z)
    {N : ℕ} (hN : 0 < N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    -(CoercAux.trigSum e 0) / (2 * N) - c / (2 * N) - (1 + Λ) * B ≤
      modulatedEnergyKernel q X (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  set T := CoercAux.trigSum e with hT
  have hes' : Summable fun k => |e k| := hes.abs
  have hTc : Continuous T := continuous_trigSum hes'
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdist : ∀ i j : Fin N, i ≠ j → X i - X j ≠ 0 := fun i j hij h =>
    hX ⟨i, j, hij, sub_eq_zero.mp h⟩
  have hTint : ∀ x, Integrable (fun y => T (x - y)) μ := fun x =>
    (hTc.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- pair term
  have hpair : ∑ i, ∑ j ∈ Finset.univ.erase i, T (X i - X j) + N * (N - 1) * (c - B) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j) := by
    have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, T (X i - X j) + ((N : ℝ) - 1) * (c - B) ≤
        ∑ j ∈ Finset.univ.erase i, q (X i - X j) := by
      intro i
      have h2 : ∀ j ∈ Finset.univ.erase i, T (X i - X j) + (c - B) ≤ q (X i - X j) := by
        intro j hj
        have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
        rw [hqe _ (hdist i j hij)]
        have := hnB (X i - X j)
        linarith
      have h3 := Finset.sum_le_sum h2
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hN] at h3
      simpa using h3
    have h4 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    rw [Finset.sum_add_distrib] at h4
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
    linarith
  -- cross term
  have hcross : ∀ x, ∫ y, q (x - y) ∂μ = ∫ y, T (x - y) ∂μ + c + ∫ y, n (x - y) ∂μ := by
    intro x
    have hnint := CoercAux.integrable_conv_density hΛ hn_meas hn_int x
    have hae : ∀ᵐ y ∂μ, q (x - y) = T (x - y) + c + n (x - y) := by
      filter_upwards [ae_ne_withDensity hd hρ x] with y hy
      exact hqe _ (sub_ne_zero.mpr (Ne.symm hy))
    have e1 : ∫ y, (T (x - y) + c + n (x - y)) ∂μ =
        ∫ y, (T (x - y) + c) ∂μ + ∫ y, n (x - y) ∂μ :=
      integral_add ((hTint x).add (integrable_const c)) hnint
    have e2 : ∫ y, (T (x - y) + c) ∂μ = ∫ y, T (x - y) ∂μ + ∫ y, c ∂μ :=
      integral_add (hTint x) (integrable_const c)
    rw [integral_congr_ae hae, e1, e2]
    simp
  have hcross_le : ∀ x, ∫ y, q (x - y) ∂μ ≤ ∫ y, T (x - y) ∂μ + c + Λ * B := fun x => by
    rw [hcross x]
    have := (conv_near_bounds hρ hΛ hn_meas hn_int hnB hB hn0 x).2
    linarith
  have hcross_ge : ∀ x, ∫ y, T (x - y) ∂μ + c - B ≤ ∫ y, q (x - y) ∂μ := fun x => by
    rw [hcross x]
    have := (conv_near_bounds hρ hΛ hn_meas hn_int hnB hB hn0 x).1
    linarith
  have hcr : ∑ i, ∫ y, q (X i - y) ∂μ ≤ ∑ i, ∫ y, T (X i - y) ∂μ + N * c + N * (Λ * B) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcross_le (X i))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    simpa using this
  -- double integral
  have hqI : Integrable (fun x => ∫ y, q (x - y) ∂μ) μ :=
    (hq.integrable_prod hρ hΛ).integral_prod_left
  have hTI : Integrable (fun x => ∫ y, T (x - y) ∂μ) μ :=
    ((continuous_conv0 hTc μ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hD : ∫ x, ∫ y, T (x - y) ∂μ ∂μ + c - B ≤ ∫ x, ∫ y, q (x - y) ∂μ ∂μ := by
    have h1 : ∫ x, (∫ y, T (x - y) ∂μ + c - B) ∂μ ≤ ∫ x, ∫ y, q (x - y) ∂μ ∂μ :=
      integral_mono ((hTI.add (integrable_const c)).sub (integrable_const B)) hqI
        (fun x => hcross_ge x)
    have e1 : ∫ x, (∫ y, T (x - y) ∂μ + c - B) ∂μ =
        ∫ x, (∫ y, T (x - y) ∂μ + c) ∂μ - ∫ x, B ∂μ :=
      integral_sub (hTI.add (integrable_const c)) (integrable_const B)
    have e2 : ∫ x, (∫ y, T (x - y) ∂μ + c) ∂μ = ∫ x, ∫ y, T (x - y) ∂μ ∂μ + ∫ x, c ∂μ :=
      integral_add hTI (integrable_const c)
    rw [e1, e2] at h1
    simpa using h1
  -- the Fourier identity
  have hQ := CoercAux.Q_eq_tsum hN hes' X μ
  have hQnn : 0 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, T (X i - X j)
      - (2 / (N : ℝ)) * ∑ i, ∫ y, T (X i - y) ∂μ + ∫ x, ∫ y, T (x - y) ∂μ ∂μ := by
    rw [hQ]
    exact tsum_nonneg fun k => mul_nonneg (he0 k) (sq_nonneg _)
  have hdiag : ∑ i, ∑ j, T (X i - X j) = ∑ i, ∑ j ∈ Finset.univ.erase i, T (X i - X j) + N * T 0 := by
    have : ∀ i : Fin N, ∑ j, T (X i - X j) = ∑ j ∈ Finset.univ.erase i, T (X i - X j) + T 0 := by
      intro i
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp
  rw [hdiag] at hQnn
  -- assemble
  unfold modulatedEnergyKernel modulatedEnergy
  show _ ≤ 1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j) -
        1 / (N : ℝ) * ∑ i, ∫ y, q (X i - y) ∂μ + 1 / 2 * ∫ x, ∫ y, q (x - y) ∂μ ∂μ
  set SPq := ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j)
  set SPT := ∑ i, ∑ j ∈ Finset.univ.erase i, T (X i - X j)
  set CRq := ∑ i, ∫ y, q (X i - y) ∂μ
  set CRT := ∑ i, ∫ y, T (X i - y) ∂μ
  set DQ := ∫ x, ∫ y, q (x - y) ∂μ ∂μ
  set DT := ∫ x, ∫ y, T (x - y) ∂μ ∂μ
  set T0 := T 0
  have hQ' : 0 ≤ SPT + N * T0 - 2 * N * CRT + (N : ℝ) ^ 2 * DT := by
    have h := mul_nonneg (sq_nonneg (N : ℝ)) hQnn
    have e : (N : ℝ) ^ 2 * ((1 / (N : ℝ) ^ 2) * (SPT + N * T0) - (2 / (N : ℝ)) * CRT + DT) =
        SPT + N * T0 - 2 * N * CRT + (N : ℝ) ^ 2 * DT := by
      field_simp
    rw [← e]; exact h
  have key : 1 / (2 * (N : ℝ) ^ 2) * SPq - 1 / (N : ℝ) * CRq + 1 / 2 * DQ -
      (-T0 / (2 * N) - c / (2 * N) - (1 + Λ) * B) =
      1 / (2 * (N : ℝ) ^ 2) * (SPq - 2 * N * CRq + (N : ℝ) ^ 2 * DQ + N * T0 + N * c +
        2 * (N : ℝ) ^ 2 * (1 + Λ) * B) := by
    field_simp
    ring
  have hpos : 0 ≤ SPq - 2 * N * CRq + (N : ℝ) ^ 2 * DQ + N * T0 + N * c +
        2 * (N : ℝ) ^ 2 * (1 + Λ) * B := by
    have a1 : (N : ℝ) * (N - 1) * (c - B) + SPT ≤ SPq := by linarith
    have a2 : 2 * (N : ℝ) * CRq ≤ 2 * N * (CRT + N * c + N * (Λ * B)) :=
      mul_le_mul_of_nonneg_left hcr (by positivity)
    have a3 : (N : ℝ) ^ 2 * (DT + c - B) ≤ (N : ℝ) ^ 2 * DQ :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    nlinarith [mul_nonneg hNpos.le hB]
  have : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) * (SPq - 2 * N * CRq + (N : ℝ) ^ 2 * DQ + N * T0 + N * c +
        2 * (N : ℝ) ^ 2 * (1 + Λ) * B) := mul_nonneg (by positivity) hpos
  linarith

end LowerBound

/-! ### The kernel `q` of the heat split -/

section WeakSplitKernel

open HRS.External HeatSplit

variable {s : ℝ}

lemma psiFn_neg (x : Torus d) (u : ℝ) : psiFn (-x) u = psiFn x u := by
  unfold psiFn
  refine tsum_congr fun k => ?_
  rw [StaticLimitAux.cosMode_neg_arg]

lemma hQ_even (τ : ℝ) (L : ℕ) (x : Torus d) : hQ d s τ L (-x) = hQ d s τ L x := by
  unfold hQ hNear hRest
  simp only [psiFn_neg, StaticLimitAux.cosMode_neg_arg]

theorem smallKernel_weakSplit (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (L : ℕ) : SmallKernel (weakSplit d s τ L).q where
  meas := measurable_hQ hd hs0 hsd hτ L
  nonneg := hQ_nonneg hd hs0 hsd hτ L
  integrable := integrable_hQ hd hs0 hsd hτ L
  even := hQ_even τ L

open Classical in
/-- Fourier coefficients `ĉ_ε(k) - ĝ_τ(k) 1_{|k|≤L}` of the truncated kernel `g_ε - g_L`
(`ε = η²`, `η = N^{-1/d}` up to constants). -/
def eCoeff (d : ℕ) (s τ ε : ℝ) (L : ℕ) (k : Lattice d) : ℝ :=
  CoercAux.cT d s ε k - (if k ∈ hModes d L then hCoeff d s τ k else 0)

lemma hCoeff_le_cT (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ ε : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ)
    (k : Lattice d) : hCoeff d s τ k ≤ CoercAux.cT d s ε k := by
  by_cases hk : k = 0
  · simp [hCoeff, CoercAux.cT, hk]
  · unfold hCoeff CoercAux.cT
    simp only [hk, if_false]
    refine mul_le_mul_of_nonneg_left ?_ (CoercAux.subA_nonneg_one (by omega) hs0 hsd)
    have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
    have hint := CoercAux.integrableOn_T ha hε k hk
    have h1 : ∫ t in Ioi τ, hW d s t * Real.exp (-t * Lattice.enorm k ^ 2) =
        ∫ t in Ioi τ, t ^ (((d : ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t)) := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hW]
      congr 2; ring
    rw [h1]
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall (Ioi_subset_Ioi hετ))
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := lt_trans hε hu
    have := Real.rpow_pos_of_pos hu0 (((d : ℝ) - s) / 2 - 1)
    show 0 ≤ u ^ (((d : ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))
    positivity

lemma eCoeff_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ ε : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ)
    (L : ℕ) (k : Lattice d) : 0 ≤ eCoeff d s τ ε L k := by
  unfold eCoeff
  by_cases hk : k ∈ hModes d L
  · simp only [hk, if_true]
    linarith [hCoeff_le_cT hd hs0 hsd hε hετ k]
  · simp only [hk, if_false, sub_zero]
    exact CoercAux.cT_nonneg (by omega) hs0 hsd hε k

lemma summable_eCoeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    Summable (eCoeff d s τ ε L) := by
  have h1 := CoercAux.summable_cT (d := d) (s := s) (by omega) hs0 hsd hε
  have h2 : Summable fun k : Lattice d => (if k ∈ hModes d L then hCoeff d s τ k else 0) :=
    summable_of_ne_finset_zero (s := hModes d L) fun k hk => by simp [hk]
  exact h1.sub h2

lemma trigSum_eCoeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ ε : ℝ} (hε : 0 < ε) (L : ℕ)
    (x : Torus d) :
    CoercAux.trigSum (eCoeff d s τ ε L) x = CoercAux.gT d s ε x - hGL d s τ L x := by
  have hsm := summable_eCoeff hd hs0 hsd hε (τ := τ) L
  have hcs : Summable fun k : Lattice d => CoercAux.cT d s ε k * Torus.cosMode k x := by
    refine Summable.of_norm_bounded (CoercAux.summable_cT (d := d) (s := s) (by omega) hs0 hsd hε) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (CoercAux.cT_nonneg (by omega) hs0 hsd hε k)]
    calc CoercAux.cT d s ε k * |Torus.cosMode k x| ≤ CoercAux.cT d s ε k * 1 :=
          mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (CoercAux.cT_nonneg (by omega) hs0 hsd hε k)
      _ = _ := mul_one _
  have hfs : Summable fun k : Lattice d =>
      (if k ∈ hModes d L then hCoeff d s τ k else 0) * Torus.cosMode k x :=
    summable_of_ne_finset_zero (s := hModes d L) fun k hk => by simp [hk]
  unfold CoercAux.trigSum CoercAux.gT hGL
  have e1 : ∀ k : Lattice d, eCoeff d s τ ε L k * Torus.cosMode k x =
      CoercAux.cT d s ε k * Torus.cosMode k x -
        (if k ∈ hModes d L then hCoeff d s τ k else 0) * Torus.cosMode k x := by
    intro k; unfold eCoeff; ring
  simp_rw [e1]
  rw [Summable.tsum_sub hcs hfs]
  congr 1
  rw [tsum_eq_sum (s := hModes d L) (fun k hk => by simp [hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [hk]

lemma hGL_zero_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    0 ≤ hGL d s τ L 0 := by
  unfold hGL
  refine Finset.sum_nonneg fun k hk => mul_nonneg (hCoeff_pos hd hs0 hsd hτ
    (ne_zero_of_mem_hModes hk)).le ?_
  simp [Torus.cosMode, StaticLimitAux.mode_apply_zero]

/-- The lower bound at a fixed truncation scale `ε ≤ τ`:
`F_N^q ≥ -ĝ_ε(0)/(2N) - c/(2N) - (1+Λ) B_ε`. -/
theorem weakSplit_energy_ge_fixed (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (L : ℕ) {ε : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) {N : ℕ} (hN : 0 < N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    -(CoercAux.gT d s ε 0) / (2 * N) - hC d s τ L / (2 * N) - (1 + Λ) * CoercAux.nearB d s ε ≤
      modulatedEnergyKernel (weakSplit d s τ L).q X (withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  have h := energy_lower_abstract (q := hQ d s τ L) (n := CoercAux.nearF d s ε)
    (e := eCoeff d s τ ε L) (c := hC d s τ L) (B := CoercAux.nearB d s ε) (Λ := Λ) hd1
    (smallKernel_weakSplit hd hs0 hsd hτ L) hρ hΛ (eCoeff_nonneg hd hs0 hsd hε hετ L)
    (summable_eCoeff hd hs0 hsd hε L) (CoercAux.measurable_nearF hd1 hs0 hsd hε)
    (CoercAux.integrable_nearF hd1 hs0 hsd hε) (CoercAux.nearF_ge hd1 hs0 hsd hε)
    (CoercAux.nearB_nonneg hd1 hs0 hsd hε) (CoercAux.integral_nearF hd1 hs0 hsd hε)
    (fun z hz => by
      rw [trigSum_eCoeff hd hs0 hsd hε L z]
      have h1 := periodicRiesz_eq_gL_add hd hs0 hsd hτ L z hz
      have h2 := CoercAux.periodicRiesz_eq_add (s := s) (ε := ε) z hz
      linarith) hN X hX
  rw [trigSum_eCoeff hd hs0 hsd hε L 0] at h
  have h0 := hGL_zero_nonneg hd hs0 hsd hτ L
  have hN2 : (0 : ℝ) < 2 * N := by positivity
  have : -(CoercAux.gT d s ε 0) / (2 * N) ≤ -(CoercAux.gT d s ε 0 - hGL d s τ L 0) / (2 * N) := by
    apply div_le_div_of_nonneg_right _ hN2.le
    linarith
  exact le_trans (by linarith) h

lemma inv_le_aN (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)⁻¹ ≤ aN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold aN
  have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (s / d - 1) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by have := div_nonneg hs0 hd0.le; linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 : (1 : ℝ) ≤ 1 + (if s = 0 then Real.log N else 0) := by
    split_ifs
    · linarith [Real.log_nonneg hN1]
    · linarith
  have h3 : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (by linarith) _
  calc (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (s / d - 1) := h1
    _ = 1 * (N : ℝ) ^ (s / d - 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 h3

lemma eventually_smearScale_sq_le (hd : 1 ≤ d) {Λ τ : ℝ} (hΛ : 0 < Λ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, smearScale d N Λ ^ 2 ≤ τ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) * Λ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).atTop_mul_const hΛ
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) * Λ) ^ (-(1 / (d : ℝ)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp h1
  have h3 : Tendsto (fun N : ℕ => smearScale d N Λ ^ 2) atTop (𝓝 0) := by
    have : (fun N : ℕ => smearScale d N Λ ^ 2) =
        fun N : ℕ => (((N : ℝ) * Λ) ^ (-(1 / (d : ℝ)))) ^ 2 := by
      funext N; unfold smearScale; rw [neg_div]
    rw [this]
    simpa using h2.pow 2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h3.eventually (gt_mem_nhds hτ))
  exact ⟨N₀, fun N hN => (hN₀ N hN).le⟩

/-- **Lower bound on the modulated energy of the kernel `q`** (the heat-truncation argument of
`periodic_coercivity`, rerun for `q = g - g_L + c`): for the heat split at `(τ, L)` and a density
bound `Λ ≥ 1` there are `C, N₀` with `F_N^q(X, μ) ≥ -C a_N` for all `N ≥ N₀`, all `X` off the
collision set, and all probability densities `ρ ≤ Λ` (`a_N = (1 + 1_{s=0} log N) N^{s/d-1}`). -/
theorem modulatedEnergy_weakSplit_ge (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, N₀ ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        -(C * aN d s N) ≤ modulatedEnergyKernel (weakSplit d s τ L).q X (withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨C₀, hC₀, hconst⟩ := CoercAux.diag_const hd1 hs0 hsd
  obtain ⟨C₀', hC₀', hCa⟩ := oNΛ_le_aN hd1 hs0 hsd C₀ hC₀ Λ hΛ1
  obtain ⟨N₁, hN₁⟩ := eventually_smearScale_sq_le hd1 hΛ0 hτ
  have hc := hC_nonneg hd hs0 hsd hτ L
  refine ⟨C₀' + hC d s τ L / 2, by positivity, max N₁ 2, le_max_right _ _, fun ρ hρ hΛ N hN X hX => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hε : 0 < smearScale d N Λ ^ 2 := by
    have := CoercAux.smearScale_pos (d := d) hN1 hΛ0; positivity
  have h := weakSplit_energy_ge_fixed hd hs0 hsd hτ L hε (hN₁ N hNN₁) hρ hΛ (by omega) X hX
  have h2 := hconst Λ hΛ1 N hN2
  have h3 := hCa N hN2
  have h4 := inv_le_aN d hd1 s hs0 hN1
  have e1 : -(CoercAux.gT d s (smearScale d N Λ ^ 2) 0) / (2 * N) =
      -(CoercAux.gT d s (smearScale d N Λ ^ 2) 0 / (2 * N)) := by ring
  have e2 : hC d s τ L / (2 * N) = hC d s τ L / 2 * (N : ℝ)⁻¹ := by field_simp
  have h5 : hC d s τ L / 2 * (N : ℝ)⁻¹ ≤ hC d s τ L / 2 * aN d s N :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [e1] at h
  rw [e2] at h
  nlinarith

end WeakSplitKernel

/-! ### Jensen for the modulated partition function and `KL(R⁰_N ‖ μ^N) = o(N)` -/

section Entropy

variable {q ρ : Torus d → ℝ} {Λ : ℝ}

lemma dblInt_eq_prod (hq : SmallKernel q) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) :
    ∫ p : Torus d × Torus d, q (p.1 - p.2) ∂((withDensityReal ρ).prod (withDensityReal ρ)) =
      dblInt q (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  unfold dblInt
  rw [integral_prod _ (hq.integrable_prod hρ hΛ)]

lemma dblInt_nonneg (hq : SmallKernel q) (μ : Measure (Torus d)) : 0 ≤ dblInt q μ :=
  integral_nonneg fun x => integral_nonneg fun y => hq.nonneg _

/-- **Jensen for the modulated partition function**: `K^q_{N,β}(μ) ≥ 1 + βG/2 ≥ 1`
(`E_{μ^N}[F_N^q] = -G/(2N) ≤ 0`, `e^x ≥ 1 + x`). -/
theorem SmallKernel.one_add_le_gibbsNormalizer (hq : SmallKernel q) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    1 + β / 2 * dblInt q (withDensityReal ρ) ≤ gibbsNormalizer q N β (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hF : Integrable (fun X : Config d N => modulatedEnergyKernel q X μ) P :=
    hq.integrable_energy hρ hΛ N
  have hexpF : Integrable (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel q X μ)) P := by
    have h := (hq.integrable_R0w_exp hρ hΛ hβ N).mul_const (Real.exp (-(β * N / 2 * dblInt q μ)))
    refine h.congr (Eventually.of_forall fun X => ?_)
    simp only
    rw [hq.R0w_eq hρ, ← Real.exp_add]
    congr 1; ring
  have hE : ∫ X, modulatedEnergyKernel q X μ ∂P = -(1 / (2 * N)) * dblInt q μ := by
    rw [← dblInt_eq_prod hq hρ hΛ]
    exact expectation_modulatedEnergy_iid q μ hN (hq.integrable_prod hρ hΛ)
      (fun x => hq.integrable_conv hΛ x)
  have h1 : ∫ X, (1 + (-β * N) * modulatedEnergyKernel q X μ) ∂P ≤
      ∫ X, Real.exp (-β * N * modulatedEnergyKernel q X μ) ∂P := by
    refine integral_mono ((integrable_const _).add (hF.const_mul _)) hexpF fun X => ?_
    have := Real.add_one_le_exp (-β * N * modulatedEnergyKernel q X μ)
    linarith
  rw [integral_add (integrable_const _) (hF.const_mul _), integral_const_mul, hE] at h1
  have hP1 : P.real Set.univ = 1 := by simp [Measure.real]
  simp only [integral_const, hP1, smul_eq_mul, one_mul] at h1
  unfold gibbsNormalizer
  have : (-β * N) * (-(1 / (2 * (N : ℝ))) * dblInt q μ) = β / 2 * dblInt q μ := by
    field_simp
  rw [this] at h1
  exact h1

lemma SmallKernel.one_le_gibbsNormalizer (hq : SmallKernel q) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ gibbsNormalizer q N β (withDensityReal ρ) := by
  have := hq.one_add_le_gibbsNormalizer hρ hΛ hβ hN
  have := dblInt_nonneg hq (withDensityReal ρ)
  nlinarith

/-- `μ^{⊗N}`-almost every configuration is collision free (`μ ≪ dx`). -/
lemma ae_not_collision (hd : 1 ≤ d) (hρ : IsProbDensity ρ) (N : ℕ) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => withDensityReal ρ), X ∉ collisionSet d N := by
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ
  have hij : ∀ i j : Fin N, i ≠ j → ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), X i ≠ X j := by
    intro i j hne
    have hm : Measurable fun X : Config d N => (X i, X j) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    refine ae_of_ae_map (p := fun z : Torus d × Torus d => z.1 ≠ z.2) hm.aemeasurable ?_
    rw [pi_map_pair μ hne]
    have hs : MeasurableSet {z : Torus d × Torus d | z.1 ≠ z.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
    exact Eventually.of_forall fun x => (ae_ne_withDensity hd hρ x).mono fun y hy => fun h => hy h.symm
  have : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i j : Fin N, i ≠ j → X i ≠ X j := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases h : i = j
    · exact Eventually.of_forall fun X hh => absurd hh (by simpa using h)
    · exact (hij i j h).mono fun X hX _ => hX
  filter_upwards [this] with X hX ⟨i, j, hne, he⟩
  exact hX i j hne he

lemma SmallKernel.integrable_energy_R0small (hq : SmallKernel q) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    Integrable (fun X : Config d N => modulatedEnergyKernel q X (withDensityReal ρ))
      (R0small q β (withDensityReal ρ) N) := by
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμdef
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  have hR : R0small q β μ N = P.tilted (R0w q β μ N) :=
    tiltMeasure_eq_tilted P _ (hq.measurable_R0w β μ N) _ (hq.R0w_le hρ hΛ hβ N)
  have hexp : Integrable (fun X => Real.exp (R0w q β μ N X)) P := hq.integrable_R0w_exp hρ hΛ hβ N
  rw [hR, integrable_tilted_iff hexp]
  refine Integrable.bdd_mul (c := Real.exp (β * N * (Λ * ∫ y, q y))) (hq.integrable_energy hρ hΛ N)
    (Real.measurable_exp.comp (hq.measurable_R0w β μ N)).aestronglyMeasurable
    (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (hq.R0w_le hρ hΛ hβ N X)

open InformationTheory in
/-- If `F_N^q ≥ -A` off the collision set, then `KL(R⁰_N ‖ μ^{⊗N}) ≤ β N A`. -/
theorem klDiv_R0small_le (hd : 1 ≤ d) (hq : SmallKernel q) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) {A : ℝ}
    (hA : ∀ X : Config d N, X ∉ collisionSet d N →
      -A ≤ modulatedEnergyKernel q X (withDensityReal ρ)) :
    klDiv (R0small q β (withDensityReal ρ) N) (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
      ENNReal.ofReal (β * N * A) := by
  haveI := isProb_withDensityReal hρ
  haveI hRp := hq.isProb_R0small hρ hΛ hβ N
  rw [klDiv_R0small hq hρ hΛ hβ N]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK := Real.log_nonneg (hq.one_le_gibbsNormalizer hρ hΛ hβ hN)
  have hac : R0small q β (withDensityReal ρ) N ≪ Measure.pi fun _ : Fin N => withDensityReal ρ := by
    rw [R0small_eq, tiltMeasure_eq_tilted _ _ (hq.measurable_R0w β _ N) _ (hq.R0w_le hρ hΛ hβ N)]
    exact tilted_absolutelyContinuous _ _
  have hae : ∀ᵐ X ∂(R0small q β (withDensityReal ρ) N),
      -A ≤ modulatedEnergyKernel q X (withDensityReal ρ) :=
    hac.ae_le ((ae_not_collision hd hρ N).mono fun X hX => hA X hX)
  have hint : -A ≤ ∫ X, modulatedEnergyKernel q X (withDensityReal ρ) ∂(R0small q β (withDensityReal ρ) N) := by
    have := integral_mono_ae (integrable_const (-A)) (hq.integrable_energy_R0small hρ hΛ hβ N) hae
    simpa using this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_nonneg hβ hN0]

end Entropy

/-- `a_N = (1 + 1_{s=0} log N) N^{s/d-1} → 0` for `s < d`. -/
theorem tendsto_aN (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun N : ℕ => aN d s N) atTop (𝓝 0) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  by_cases hs : s = 0
  · subst hs
    have h1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hcast
    have h2 : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) :=
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hcast
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr fun N => ?_
    unfold aN
    simp only [if_true, zero_div, zero_sub, Real.rpow_neg_one]
    ring
  · have hδ : 0 < 1 - s / d := by
      rw [sub_pos, div_lt_one hd0]; exact hsd
    have h := (tendsto_rpow_neg_atTop hδ).comp hcast
    refine h.congr fun N => ?_
    unfold aN
    simp only [hs, if_false, add_zero, one_mul, Function.comp]
    congr 1; ring

open InformationTheory in
/-- **`KL(R⁰_N ‖ μ^{⊗N}) ≤ C β N a_N`** for the weak reference of the heat split: the entropy of the
weak reference is `o(N)`. -/
theorem klDiv_R0small_weakSplit_le (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, N₀ ≤ N →
        klDiv (R0small (weakSplit d s τ L).q β (withDensityReal ρ) N)
            (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
          ENNReal.ofReal (β * N * (C * aN d s N)) := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := modulatedEnergy_weakSplit_ge hd hs0 hsd hτ L hΛ1
  refine ⟨C, hC, N₀, hN₀, fun ρ hρ hΛ N hN => ?_⟩
  exact klDiv_R0small_le (by omega) (smallKernel_weakSplit hd hs0 hsd hτ L) hρ hΛ hβ (by omega)
    (A := C * aN d s N) (fun X hX => h ρ hρ hΛ N hN X hX)

open InformationTheory in
/-- **`KL(R⁰_{N+1} ‖ μ^{⊗(N+1)}) = o(N)`.** -/
theorem tendsto_klDiv_R0small_weakSplit (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun N : ℕ =>
      klDiv (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1))
        (Measure.pi fun _ : Fin (N + 1) => withDensityReal ρ) / ((N : ℝ≥0∞) + 1))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := klDiv_R0small_weakSplit_le hd hs0 hsd hτ L hΛ1 hβ
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (β * (C * aN d s (N + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => aN d s (N + 1)) atTop (𝓝 0) :=
      (tendsto_aN (by omega) hs0 hsd).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N : ℕ => β * (C * aN d s (N + 1))) atTop (𝓝 0) := by
      simpa using (h1.const_mul C).const_mul β
    have := (ENNReal.tendsto_ofReal h2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => bot_le) ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN1 := h ρ hρ hΛ (N + 1) (by omega)
  have e : ENNReal.ofReal (β * ((N + 1 : ℕ) : ℝ) * (C * aN d s (N + 1))) =
      ((N : ℝ≥0∞) + 1) * ENNReal.ofReal (β * (C * aN d s (N + 1))) := by
    have : β * ((N + 1 : ℕ) : ℝ) * (C * aN d s (N + 1)) =
        ((N : ℝ) + 1) * (β * (C * aN d s (N + 1))) := by push_cast; ring
    rw [this, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  rw [e] at hN1
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  exact hN1

/-! ### Total variation controls bounded test functions -/

section TVInt

open HRS.External.Entropy

variable {α : Type*} [MeasurableSpace α]

lemma abs_integral_sub_le_tvDist_of_nonneg (P Q : Measure α) [IsProbabilityMeasure P]
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
  rw [hform P inferInstance, hform Q inferInstance, ← integral_sub (hI P inferInstance) (hI Q inferInstance)]
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
theorem abs_integral_sub_le_two_mul_tvDist (P Q : Measure α) [IsProbabilityMeasure P]
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
  have h1 := abs_integral_sub_le_tvDist_of_nonneg P Q hpm hM0 hp0 hpM
  have h2 := abs_integral_sub_le_tvDist_of_nonneg P Q hnm hM0 hn0 hnM
  have : ∫ x, fp x ∂P - ∫ x, fn x ∂P - (∫ x, fp x ∂Q - ∫ x, fn x ∂Q) =
      (∫ x, fp x ∂P - ∫ x, fp x ∂Q) - (∫ x, fn x ∂P - ∫ x, fn x ∂Q) := by ring
  rw [this]
  calc _ ≤ |∫ x, fp x ∂P - ∫ x, fp x ∂Q| + |∫ x, fn x ∂P - ∫ x, fn x ∂Q| := abs_sub _ _
    _ ≤ M * tvDist P Q + M * tvDist P Q := add_le_add h1 h2
    _ = 2 * M * tvDist P Q := by ring

end TVInt

/-! ### The first marginal of `R⁰_N` converges to `μ` in total variation -/

open HRS.External.Entropy InformationTheory in
/-- **`‖π⁰_N - μ‖_TV → 0`** for the first marginal `π⁰_N` of the weak reference `R⁰_N`
(`N + 1` particles; `μ = ρ dx`, `ρ ≤ Λ` a probability density, `β ≥ 0`). -/
theorem tendsto_tvDist_R0small_firstMarginal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {τ : ℝ} (hτ : 0 < τ) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun N : ℕ =>
      tvDist ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
        (withDensityReal ρ)) atTop (𝓝 0) := by
  haveI := isProb_withDensityReal hρ
  have hq := smallKernel_weakSplit hd hs0 hsd hτ L
  haveI : ∀ N : ℕ, IsProbabilityMeasure
      (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)) :=
    fun N => hq.isProb_R0small hρ hΛ hβ (N + 1)
  exact tendsto_tvDist_firstMarginal (E := Torus d) (withDensityReal ρ)
    (fun N => R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1))
    (fun N => R0small_isExchangeable hq.meas hq.even β _ (N + 1))
    (tendsto_klDiv_R0small_weakSplit hd hs0 hsd hτ L hρ hΛ1 hΛ hβ)

/-! ### Smallness of the calibration field -/

section Features

open HRS.External.Entropy

variable {M : ℕ}

/-- `‖∫ Ξ dP - ∫ Ξ dQ‖ ≤ 2 B ‖P - Q‖_TV` for a bounded measurable vector `Ξ`. -/
theorem norm_integral_sub_le_two_mul_tvDist {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {Ξ : α → EuclideanSpace ℝ (Fin M)}
    (hΞm : Measurable Ξ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖Ξ x‖ ≤ B) :
    ‖∫ x, Ξ x ∂P - ∫ x, Ξ x ∂Q‖ ≤ 2 * B * tvDist P Q := by
  have hint : ∀ Pm : Measure α, IsProbabilityMeasure Pm → Integrable Ξ Pm := fun Pm hPm =>
    Integrable.of_bound hΞm.aestronglyMeasurable B (Eventually.of_forall hB)
  set v := ∫ x, Ξ x ∂P - ∫ x, Ξ x ∂Q with hv
  have hcomm : ∀ Pm : Measure α, IsProbabilityMeasure Pm →
      ∫ x, inner ℝ v (Ξ x) ∂Pm = inner ℝ v (∫ x, Ξ x ∂Pm) := fun Pm hPm => by
    have := (innerSL ℝ v).integral_comp_comm (hint Pm hPm)
    simpa using this
  have h1 : ‖v‖ ^ 2 = ∫ x, inner ℝ v (Ξ x) ∂P - ∫ x, inner ℝ v (Ξ x) ∂Q := by
    rw [hcomm P inferInstance, hcomm Q inferInstance, ← inner_sub_right, ← hv,
      real_inner_self_eq_norm_sq]
  have hfm : Measurable fun x => inner ℝ v (Ξ x) := measurable_const.inner hΞm
  have h2 : |∫ x, inner ℝ v (Ξ x) ∂P - ∫ x, inner ℝ v (Ξ x) ∂Q| ≤
      2 * (‖v‖ * B) * tvDist P Q :=
    abs_integral_sub_le_two_mul_tvDist P Q hfm (mul_nonneg (norm_nonneg _) hB0) (fun x => by
      calc |inner ℝ v (Ξ x)| ≤ ‖v‖ * ‖Ξ x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖v‖ * B := mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))
  rw [← h1, abs_of_nonneg (by positivity)] at h2
  have htv := tvDist_nonneg P Q
  by_cases hv0 : ‖v‖ = 0
  · rw [hv0]; positivity
  · have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
    nlinarith

/-- `E_P[μ_n(Ξ)] = ∫ (∫ Ξ dμ_n(X)) dP(X)`, the expected empirical average of the vector `Ξ`. -/
def meanFeature {n : ℕ} (Ξ : Torus d → EuclideanSpace ℝ (Fin M)) (P : Measure (Config d n)) :
    EuclideanSpace ℝ (Fin M) :=
  ∫ X, ∫ x, Ξ x ∂(empirical X) ∂P

lemma integral_empirical_vec {n : ℕ} (hn : 0 < n) (X : Config d n)
    {Ξ : Torus d → EuclideanSpace ℝ (Fin M)} (hΞm : Measurable Ξ) :
    ∫ x, Ξ x ∂(empirical X) = ((n : ℝ)⁻¹) • ∑ i, Ξ (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finset_sum_measure]
  · have hd : ∀ a, ∫ x, Ξ x ∂(Measure.dirac a) = Ξ a := fun a =>
      integral_dirac' Ξ a hΞm.stronglyMeasurable
    simp [hd, ENNReal.toReal_inv]
  · intro i _
    exact integrable_dirac' hΞm.stronglyMeasurable (by simp)

/-- For an exchangeable law, `E[μ_{N+1}(Ξ)] = ∫ Ξ dπ_N` with `π_N` the first marginal. -/
theorem meanFeature_eq_firstMarginal {N : ℕ} (P : Measure (Config d (N + 1)))
    [IsProbabilityMeasure P] (hex : HRS.External.Entropy.IsExchangeable P) {Ξ : Torus d → EuclideanSpace ℝ (Fin M)}
    (hΞm : Measurable Ξ) {B : ℝ} (hB : ∀ x, ‖Ξ x‖ ≤ B) :
    meanFeature Ξ P = ∫ x, Ξ x ∂(P.map fun X => X 0) := by
  unfold meanFeature
  have h1 : ∀ X : Config d (N + 1), ∫ x, Ξ x ∂(empirical X) =
      (((N + 1 : ℕ) : ℝ)⁻¹) • ∑ i, Ξ (X i) := fun X =>
    integral_empirical_vec (Nat.succ_pos N) X hΞm
  simp_rw [h1]
  have hint : ∀ i : Fin (N + 1), Integrable (fun X : Config d (N + 1) => Ξ (X i)) P := fun i =>
    Integrable.of_bound (hΞm.comp (measurable_pi_apply i)).aestronglyMeasurable B
      (Eventually.of_forall fun X => hB _)
  rw [integral_smul, integral_finsetSum _ fun i _ => hint i]
  have h2 : ∀ i : Fin (N + 1), ∫ X : Config d (N + 1), Ξ (X i) ∂P =
      ∫ x, Ξ x ∂(P.map fun X => X 0) := by
    intro i
    rw [← integral_map (φ := fun X : Config d (N + 1) => X i) (measurable_pi_apply i).aemeasurable
      hΞm.aestronglyMeasurable,
      HRS.External.Entropy.IsExchangeable.marginal_eq hex i 0]
  simp_rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (((N + 1 : ℕ) : ℝ)⁻¹) * ((N + 1 : ℕ) : ℝ) = 1 :=
    inv_mul_cancel₀ (by positivity)
  rw [this, one_smul]

end Features

section Smallness

open HRS.External.Entropy

/-- **Smallness of the calibration field.** Let `Ξ` be a bounded measurable feature map with
`μ(Ξ) = 0` (`μ = ρ dx`; in the application `Ξ = Ψ - μ(Ψ)`), and let `t_n` be any vectors with
`|t_n| ≤ β |E_{R⁰_n}[μ_n Ξ]|` (the bound of the calibration, `t_n` being the calibrated field).
Then `sup_x |t_n · Ξ(x)| ≤ 1` for all `n` large enough. -/
theorem sup_calibration_field_le_one (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} {Ξ : Torus d → EuclideanSpace ℝ (Fin M)}
    (hΞm : Measurable Ξ) {B : ℝ} (hB : ∀ x, ‖Ξ x‖ ≤ B)
    (hΞ0 : ∫ x, Ξ x ∂(withDensityReal ρ) = 0) (t : ℕ → EuclideanSpace ℝ (Fin M))
    (ht : ∀ n : ℕ, 1 ≤ n →
      ‖t n‖ ≤ β * ‖meanFeature Ξ (R0small (weakSplit d s τ L).q β (withDensityReal ρ) n)‖) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : Torus d, |inner ℝ (t n) (Ξ x)| ≤ 1 := by
  haveI := isProb_withDensityReal hρ
  have hq := smallKernel_weakSplit hd hs0 hsd hτ L
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hTV := tendsto_tvDist_R0small_firstMarginal hd hs0 hsd hτ L hρ hΛ1 hΛ hβ
  have hT2 := hTV.const_mul (2 * β * B ^ 2)
  rw [mul_zero] at hT2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hT2.eventually (gt_mem_nhds one_pos))
  refine ⟨N₀ + 1, fun n hn x => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hNN : N₀ ≤ N := by omega
  haveI : IsProbabilityMeasure (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)) :=
    hq.isProb_R0small hρ hΛ hβ (N + 1)
  have hmean := meanFeature_eq_firstMarginal
    (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1))
    (R0small_isExchangeable hq.meas hq.even β _ (N + 1)) hΞm hB
  have hnorm := norm_integral_sub_le_two_mul_tvDist
    ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ) hΞm hB0 hB
  rw [hΞ0, sub_zero] at hnorm
  rw [← hmean] at hnorm
  have h1 := ht (N + 1) (by omega)
  have h2 : ‖t (N + 1)‖ ≤ β * (2 * B * tvDist
      ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ)) := h1.trans (mul_le_mul_of_nonneg_left hnorm hβ)
  have h3 := hN₀ N hNN
  have htv := tvDist_nonneg
    ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ)
  calc |inner ℝ (t (N + 1)) (Ξ x)| ≤ ‖t (N + 1)‖ * ‖Ξ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * B * tvDist
      ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ))) * B := mul_le_mul h2 (hB x) (norm_nonneg _) (by positivity)
    _ = 2 * β * B ^ 2 * tvDist
      ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ) := by ring
    _ ≤ 1 := h3.le

end Smallness

/-! ### Specialisations to the heat split, and plug-in helpers -/

section PlugIn

open HRS.External.Entropy HeatSplit

/-- `R⁰_N` of the heat split is exchangeable. -/
theorem R0small_weakSplit_isExchangeable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (L : ℕ) (β : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    IsExchangeable (R0small (weakSplit d s τ L).q β μ N) :=
  R0small_isExchangeable (smallKernel_weakSplit hd hs0 hsd hτ L).meas
    (smallKernel_weakSplit hd hs0 hsd hτ L).even β μ N

open InformationTheory in
/-- The entropy identity for the weak reference of the heat split. -/
theorem klDiv_R0small_weakSplit {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    klDiv (R0small (weakSplit d s τ L).q β (withDensityReal ρ) N)
        (Measure.pi fun _ : Fin N => withDensityReal ρ) =
      ENNReal.ofReal (-β * N * ∫ X, modulatedEnergyKernel (weakSplit d s τ L).q X (withDensityReal ρ)
          ∂(R0small (weakSplit d s τ L).q β (withDensityReal ρ) N)
        - Real.log (gibbsNormalizer (weakSplit d s τ L).q N β (withDensityReal ρ))) :=
  klDiv_R0small (smallKernel_weakSplit hd hs0 hsd hτ L) hρ hΛ hβ N

/-- Centering a bounded measurable feature map: `Ξ = Ψ - μ(Ψ)` is bounded by `2b`, measurable and
has `μ(Ξ) = 0`. -/
theorem centered_features {M : ℕ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} (hΨm : Measurable Ψ)
    {b : ℝ} (hb : ∀ x, ‖Ψ x‖ ≤ b) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Measurable (fun x => Ψ x - ∫ y, Ψ y ∂μ) ∧ (∀ x, ‖Ψ x - ∫ y, Ψ y ∂μ‖ ≤ 2 * b) ∧
      ∫ x, (Ψ x - ∫ y, Ψ y ∂μ) ∂μ = 0 := by
  have hint : Integrable Ψ μ :=
    Integrable.of_bound hΨm.aestronglyMeasurable b (Eventually.of_forall hb)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have hmean : ‖∫ y, Ψ y ∂μ‖ ≤ b := by
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hb)).trans ?_
    simp
  refine ⟨hΨm.sub measurable_const, fun x => ?_, ?_⟩
  · calc ‖Ψ x - ∫ y, Ψ y ∂μ‖ ≤ ‖Ψ x‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
      _ ≤ 2 * b := by linarith [hb x]
  · rw [integral_sub hint (integrable_const _)]
    simp

/-- Continuous trigonometric features: `∑_k a_k cos(2πk·(x - y)) = ⟪Ψ x, Ψ y⟫` with `Ψ` continuous
(the version of `HeatSplit.exists_features` with continuity of the feature map). -/
theorem exists_continuous_features (Λs : Finset (Lattice d)) (a : Lattice d → ℝ)
    (ha : ∀ k ∈ Λs, 0 ≤ a k) :
    ∃ (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)), Continuous Ψ ∧
      (∀ x y : Torus d, ∑ k ∈ Λs, a k * Torus.cosMode k (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      ∀ x : Torus d, ‖Ψ x‖ ^ 2 = ∑ k ∈ Λs, a k * Torus.cosMode k 0 := by
  classical
  let ι := Λs × Bool
  let f : ι → Torus d → ℝ := fun i x =>
    if i.2 then Real.sqrt (a i.1) * Torus.cosMode i.1 x else Real.sqrt (a i.1) * Torus.sinMode i.1 x
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have key : ∀ x y : Torus d, ∑ k ∈ Λs, a k * Torus.cosMode k (x - y) =
      inner ℝ (WithLp.toLp 2 (fun m : Fin (Fintype.card ι) => f (e.symm m) x) :
        EuclideanSpace ℝ (Fin (Fintype.card ι)))
        (WithLp.toLp 2 (fun m : Fin (Fintype.card ι) => f (e.symm m) y)) := by
    intro x y
    rw [PiLp.inner_apply]
    simp only [WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
    rw [Equiv.sum_comp e.symm (fun i => f i y * f i x)]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_coe_sort Λs (fun k => a k * Torus.cosMode k (x - y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fintype.sum_bool, f, if_true, Bool.false_eq_true, if_false]
    rw [Repulsive.rp04_cosMode_sub]
    have hs := Real.mul_self_sqrt (ha k.1 k.2)
    linear_combination (-(Torus.cosMode (k : Lattice d) x * Torus.cosMode (k : Lattice d) y +
      Torus.sinMode (k : Lattice d) x * Torus.sinMode (k : Lattice d) y)) * hs
  have hcont : Continuous fun x : Torus d =>
      (WithLp.toLp 2 (fun m : Fin (Fintype.card ι) => f (e.symm m) x) :
        EuclideanSpace ℝ (Fin (Fintype.card ι))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun m => ?_)
    simp only [f]
    split_ifs
    · exact continuous_const.mul (Torus.continuous_cosMode _)
    · exact continuous_const.mul (Torus.continuous_sinMode _)
  refine ⟨Fintype.card ι, fun x => WithLp.toLp 2 (fun m => f (e.symm m) x), hcont, key, fun x => ?_⟩
  have h := key x x
  rw [sub_self] at h
  show ‖(WithLp.toLp 2 (fun m => f (e.symm m) x) : EuclideanSpace ℝ (Fin (Fintype.card ι)))‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq]
  exact h.symm

/-- Continuous features of the heat split: `g_L(x - y) = ⟪Ψ x, Ψ y⟫`, `‖Ψ x‖² = g_L(0)`. -/
theorem exists_continuous_features_weakSplit {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    ∃ (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)), Continuous Ψ ∧
      (∀ x y : Torus d, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      ∀ x : Torus d, ‖Ψ x‖ ^ 2 = (weakSplit d s τ L).gL 0 := by
  obtain ⟨M, Ψ, hc, h1, h2⟩ := exists_continuous_features (hModes d L) (hCoeff d s τ)
    (fun k hk => (hCoeff_pos hd hs0 hsd hτ (ne_zero_of_mem_hModes hk)).le)
  exact ⟨M, Ψ, hc, h1, h2⟩

end PlugIn

end HRS.External.RefSmall

end
