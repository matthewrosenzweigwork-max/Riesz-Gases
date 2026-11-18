/-
# HRS.Equilibrium.MarginalCavity -- the exact cavity decomposition of `Q_{N,β}(μ)` (EQ-02)

`Q_{N,β}(μ) = cavityLaw g μ N (β/N) β` (`modulatedGibbs_eq_cavity`).  With `Y = (y₂,…,y_N)` the other
coordinates, the density of `Q` is `exp(β (g*μ)(x₁)) · exp(-λ ∑_j g(x₁ - y_j)) · (cavity weight of Y)`:
`firstMarginal_cavity` identifies the first marginal `π_N`, and `lintegral_disintegrate` the conditional
law of `Y` given `x₁ = x` as the pole law `P_n^{x,1}`.
-/
import HRS.Equilibrium.PoleVariance
import HRS.Equilibrium.ReferenceGlue
import HRS.Equilibrium.MarginalKernel
import HRS.Equilibrium.MarginalExpFamily

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MarginalAux

variable {d : ℕ}

/-! ### Splitting off the first coordinate -/

theorem lintegral_pi_succ {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {n : ℕ}
    (F : (Fin (n + 1) → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ x, ∫⁻ Y, F (Fin.cons x Y) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have e := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  have h1 := e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F
  rw [← h1]
  have hm : Measurable fun p : E × (Fin n → E) => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm p) :=
    hF.comp (MeasurableEquiv.measurable _)
  rw [lintegral_prod _ hm.aemeasurable]
  congr 1
  funext x
  congr 1
  funext Y
  congr 1
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_zero' x Y

theorem pairSum_cons (g : Torus d → ℝ) {n : ℕ} (x : Torus d) (Y : Config d n) :
    pairSum g (Fin.cons x Y : Config d (n + 1)) = ∑ j, g (x - Y j) + pairSum g Y := by
  unfold pairSum
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Finset.sum_filter, Fin.sum_univ_succ]
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.cons_succ]
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
    simp

/-! ### `Q_{N,β}(μ)` is the cavity law with `n = N` particles -/

section Cavity

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

theorem measurable_cavityW {g : Torus d → ℝ} (hg : Measurable g) (μ : Measure (Torus d)) [SFinite μ]
    (n : ℕ) (lam β : ℝ) :
    Measurable fun Y : Config d n => -lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) :=
  ((measurable_pairSum hg).const_mul _).add
    ((Finset.measurable_sum _ fun i _ =>
      (measurable_convMeasure hg μ).comp (measurable_pi_apply i)).const_mul _)

theorem modulatedGibbs_eq_cavity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (N : ℕ) (hN : 0 < N) :
    modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) =
      cavityLaw (periodicRiesz d s) (withDensityReal ρ) N (β / N) β := by
  haveI := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμ
  set g := periodicRiesz d s with hgdef
  have hg : Measurable g := measurable_periodicRiesz hd hs0 hsd
  have heven : ∀ x, g (-x) = g x := fun x => periodicRiesz_neg x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set w : Config d N → ℝ := fun Y => -(β / N) * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) with hw
  have hwm : Measurable w := measurable_cavityW hg μ N (β / N) β
  have hE : ∀ X : Config d N, -β * N * modulatedEnergyKernel g X μ = w X - β * N * Calib.Kq g μ := by
    intro X
    rw [Calib.modEnergy_q_eq hN β X]
    unfold Calib.E0
    simp only [hw]
    rw [RefSmall.pairSum_eq_half heven X, ← Finset.mul_sum]
    ring
  obtain ⟨W, hW⟩ := cavity_weight_le hd hs0 hsd β hρ N (β / N) (by positivity)
  have hint : Integrable (fun X : Config d N => Real.exp (-β * N * modulatedEnergyKernel g X μ))
      (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.of_bound (C := Real.exp (W - β * N * Calib.Kq g μ)) ?_
      (Filter.Eventually.of_forall fun X => ?_)
    · refine (Real.measurable_exp.comp ?_).aestronglyMeasurable
      have : (fun X : Config d N => -β * N * modulatedEnergyKernel g X μ) =
          fun X => w X - β * N * Calib.Kq g μ := funext hE
      rw [this]; exact hwm.sub measurable_const
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hE X]
      exact Real.exp_le_exp.2 (by linarith [hW X])
  rw [Calib.modulatedGibbs_eq_tilted hint]
  have : (fun X : Config d N => -β * N * modulatedEnergyKernel g X μ) =
      fun X => w X + (-(β * N * Calib.Kq g μ)) := by
    funext X; rw [hE X]; ring
  rw [this, Calib.tilted_add_const]
  unfold cavityLaw
  exact (Glue.tiltMeasure_eq_tilted_of_measurable _ w hwm).symm

end Cavity


/-! ### The joint law of `(x₁, Y)` -/

section Joint

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-- The exponent of the cavity law with `n + 1` particles splits along the first coordinate. -/
theorem cavityW_cons (g : Torus d → ℝ) (μ : Measure (Torus d)) {n : ℕ} (lam β : ℝ) (x : Torus d)
    (Y : Config d n) :
    -lam * pairSum g (Fin.cons x Y : Config d (n + 1)) +
        β * ∑ i, convMeasure g μ ((Fin.cons x Y : Config d (n + 1)) i) =
      (β * convMeasure g μ x - lam * ∑ j, g (x - Y j)) +
        (-lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i)) := by
  rw [pairSum_cons, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem tilt_normalizer_ne {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (w : α → ℝ) (hw : Measurable w) (W : ℝ) (hW : ∀ a, w a ≤ W) :
    (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ 0 ∧ (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ ∞ := by
  have hZfin : (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≠ ∞ := by
    apply ne_of_lt
    calc (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P) ≤ ∫⁻ _a, ENNReal.ofReal (Real.exp W) ∂P :=
          lintegral_mono fun a => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hW a))
      _ = ENNReal.ofReal (Real.exp W) := by simp
      _ < ∞ := ENNReal.ofReal_lt_top
  refine ⟨?_, hZfin⟩
  intro h0
  have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
  rw [lintegral_eq_zero_iff hm] at h0
  have h1 : ∀ᵐ a ∂P, False := h0.mono fun a ha => by
    have := (ENNReal.ofReal_eq_zero.1 ha)
    exact absurd this (not_le.2 (Real.exp_pos _))
  obtain ⟨a, ha⟩ := h1.exists
  exact ha

/-- `cavityLaw` as a normalised density: for any measurable `G ≥ 0`. -/
theorem lintegral_cavityLaw (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    (G : Config d n → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ Y, G Y ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      (∫⁻ Y, ENNReal.ofReal (Real.exp (-lam * pairSum (periodicRiesz d s) Y +
          β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)))
        ∂(Measure.pi fun _ : Fin n => withDensityReal ρ))⁻¹ *
      ∫⁻ Y, G Y * ENNReal.ofReal (Real.exp (-lam * pairSum (periodicRiesz d s) Y +
          β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)))
        ∂(Measure.pi fun _ : Fin n => withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hwm := measurable_cavityW hgm (withDensityReal ρ) n lam β
  have hm : Measurable fun Y : Config d n => ENNReal.ofReal (Real.exp (-lam * pairSum (periodicRiesz d s) Y +
          β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hwm)
  unfold cavityLaw tiltMeasure
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hm hG, smul_eq_mul]
  congr 1
  refine lintegral_congr fun Y => ?_
  rw [Pi.mul_apply, mul_comm]

end Joint


section Joint2

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-- The weight `D(x, Y) = exp(β (g*μ)(x) - λ ∑_j g(x - y_j))` of the joint law of `(x₁, Y)`. -/
def jointW (g : Torus d → ℝ) (μ : Measure (Torus d)) {n : ℕ} (lam β : ℝ) (p : Torus d × Config d n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (β * convMeasure g μ p.1 - lam * ∑ j, g (p.1 - p.2 j)))

theorem measurable_jointW {g : Torus d → ℝ} (hg : Measurable g) (μ : Measure (Torus d)) [SFinite μ]
    {n : ℕ} (lam β : ℝ) : Measurable (jointW g μ (n := n) lam β) := by
  unfold jointW
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  exact (((measurable_convMeasure hg μ).comp measurable_fst).const_mul β).sub
    ((Finset.measurable_sum _ fun j _ =>
      hg.comp (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).const_mul lam)

theorem map_cons_cavity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ κ : ℝ≥0∞, (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β).map
        (fun X : Config d (n + 1) => (X 0, Fin.tail X)) =
      κ • ((withDensityReal ρ).prod (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)).withDensity
        (jointW (periodicRiesz d s) (withDensityReal ρ) lam β) := by
  have hμ := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμdef
  set g := periodicRiesz d s with hgdef
  have hgm : Measurable g := measurable_periodicRiesz hd hs0 hsd
  haveI hPn := cavity_isProb hd hs0 hsd β hρ n lam hlam
  -- normalisers
  set wn : Config d n → ℝ := fun Y => -lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) with hwn
  set wn1 : Config d (n + 1) → ℝ := fun Y => -lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) with hwn1
  have hwnm : Measurable wn := measurable_cavityW hgm μ n lam β
  have hwn1m : Measurable wn1 := measurable_cavityW hgm μ (n + 1) lam β
  obtain ⟨Wn, hWn⟩ := cavity_weight_le hd hs0 hsd β hρ n lam hlam
  have hZn := tilt_normalizer_ne (Measure.pi fun _ : Fin n => μ) wn hwnm Wn hWn
  set Zn := ∫⁻ Y, ENNReal.ofReal (Real.exp (wn Y)) ∂(Measure.pi fun _ : Fin n => μ) with hZn_def
  set Zn1 := ∫⁻ Y, ENNReal.ofReal (Real.exp (wn1 Y)) ∂(Measure.pi fun _ : Fin (n + 1) => μ) with hZn1_def
  refine ⟨Zn1⁻¹ * Zn, ?_⟩
  have hT : Measurable fun X : Config d (n + 1) => (X 0, Fin.tail X) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  ext A hA
  rw [Measure.map_apply hT hA, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul,
    ← lintegral_indicator hA, lintegral_prod _ ((measurable_jointW hgm μ lam β).indicator hA).aemeasurable]
  -- left side
  set T : Config d (n + 1) → Torus d × Config d n := fun X => (X 0, Fin.tail X) with hTdef
  have hLHS : cavityLaw g μ (n + 1) lam β (T ⁻¹' A) =
      Zn1⁻¹ * ∫⁻ x, ∫⁻ Y, (A.indicator (jointW g μ lam β)) (x, Y) *
        ENNReal.ofReal (Real.exp (wn Y)) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
    rw [← lintegral_indicator_one (hT hA)]
    rw [lintegral_cavityLaw hd hs0 hsd β hρ (n + 1) lam hlam _ (measurable_one.indicator (hT hA))]
    congr 1
    have hFm : Measurable fun X : Config d (n + 1) => (T ⁻¹' A).indicator (1 : Config d (n + 1) → ℝ≥0∞) X *
        ENNReal.ofReal (Real.exp (wn1 X)) :=
      (measurable_one.indicator (hT hA)).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hwn1m))
    rw [lintegral_pi_succ μ _ hFm]
    refine lintegral_congr fun x => lintegral_congr fun Y => ?_
    have hc : wn1 (Fin.cons x Y) = (β * convMeasure g μ x - lam * ∑ j, g (x - Y j)) + wn Y :=
      cavityW_cons g μ lam β x Y
    rw [hc, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hmem : (Fin.cons x Y : Config d (n + 1)) ∈ T ⁻¹' A ↔ (x, Y) ∈ A := by
      simp [hTdef]
    by_cases h : (x, Y) ∈ A
    · simp [Set.indicator, hmem, h, jointW]
    · simp [Set.indicator, hmem, h]
  -- right side
  have hRHS : ∀ x : Torus d, ∫⁻ Y, (A.indicator (jointW g μ lam β)) (x, Y) ∂(cavityLaw g μ n lam β) =
      Zn⁻¹ * ∫⁻ Y, (A.indicator (jointW g μ lam β)) (x, Y) *
        ENNReal.ofReal (Real.exp (wn Y)) ∂(Measure.pi fun _ : Fin n => μ) := by
    intro x
    exact lintegral_cavityLaw hd hs0 hsd β hρ n lam hlam _
      (((measurable_jointW hgm μ lam β).indicator hA).comp measurable_prodMk_left)
  rw [hLHS]
  simp_rw [hRHS]
  rw [lintegral_const_mul _ (Measurable.lintegral_prod_right' (f := fun q : Torus d × Config d n =>
      (A.indicator (jointW g μ lam β)) q * ENNReal.ofReal (Real.exp (wn q.2)))
      (((measurable_jointW hgm μ lam β).indicator hA).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hwnm.comp measurable_snd)))))]
  rw [← mul_assoc, mul_assoc Zn1⁻¹, ENNReal.mul_inv_cancel hZn.1 hZn.2, mul_one]

end Joint2


/-! ### The first marginal -/

section Marginal

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-- `Φ_x = E_{P_n^0}[e^{-λ ∑_j g(x - y_j)}]`. -/
def phiIns (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d) : ℝ :=
  ∫ Y, Real.exp (-lam * ∑ j, g (x - Y j)) ∂(cavityLaw g μ n lam β)

theorem exp_neg_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {n : ℕ} {lam β : ℝ} (hlam : 0 ≤ lam)
    (hln : lam * n ≤ β) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ periodicRiesz d s z)
    (x : Torus d) (Y : Config d n) :
    Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j)) ≤ Real.exp (β * B) := by
  refine Real.exp_le_exp.2 ?_
  have h1 := sum_ge_of_ge (periodicRiesz d s) hB x Y
  have h2 : -(B * n) ≤ ∑ j, periodicRiesz d s (x - Y j) := h1
  have : lam * (B * n) ≤ β * B := by
    have : lam * (B * n) = (lam * n) * B := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hln hB0
  nlinarith

theorem measurable_expS {g : Torus d → ℝ} (hg : Measurable g) {n : ℕ} (lam : ℝ) :
    Measurable fun p : Torus d × Config d n => Real.exp (-lam * ∑ j, g (p.1 - p.2 j)) := by
  refine Real.measurable_exp.comp (Measurable.const_mul ?_ _)
  exact Finset.measurable_sum _ fun j _ => hg.comp (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))

end Marginal


section Marginal2

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
  {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam * n ≤ β)

include hd hs0 hsd hρ hlam hln

theorem integrable_expS (x : Torus d) :
    Integrable (fun Y : Config d n => Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j)))
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  obtain ⟨B, hB0, hB⟩ := rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine Integrable.of_bound (C := Real.exp (β * B)) ?_ (Filter.Eventually.of_forall fun Y => ?_)
  · exact ((measurable_expS hgm lam).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_le hd hs0 hsd hlam hln hB0 hB x Y

theorem phiIns_pos (x : Torus d) :
    0 < phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  exact integral_exp_pos (integrable_expS hd hs0 hsd hρ hlam hln x)

theorem phiIns_le_of {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ periodicRiesz d s z) (x : Torus d) :
    phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x ≤ Real.exp (β * B) := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  have := norm_integral_le_of_norm_le_const (μ := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)
    (f := fun Y : Config d n => Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j))) (C := Real.exp (β * B))
    (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_neg_le hd hs0 hsd hlam hln hB0 hB x Y)
  unfold phiIns
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

theorem phiIns_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x ≤ Real.exp (β * B) := by
  obtain ⟨B, hB0, hB⟩ := rieszB hd hs0 hsd
  exact ⟨B, hB0, phiIns_le_of hd hs0 hsd hρ hlam hln hB0 hB⟩

theorem measurable_phiIns :
    Measurable (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have : StronglyMeasurable (Function.uncurry fun (x : Torus d) (Y : Config d n) =>
      Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j))) :=
    (measurable_expS hgm lam).stronglyMeasurable
  exact (this.integral_prod_right' (ν := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)).measurable

theorem lintegral_jointW (x : Torus d) :
    ∫⁻ Y, jointW (periodicRiesz d s) (withDensityReal ρ) lam β (x, Y)
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      ENNReal.ofReal (Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)) *
        ENNReal.ofReal (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  have hint := integrable_expS hd hs0 hsd hρ hlam hln x
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have h1 : ∀ Y : Config d n, jointW (periodicRiesz d s) (withDensityReal ρ) lam β (x, Y) =
      ENNReal.ofReal (Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)) *
        ENNReal.ofReal (Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j))) := by
    intro Y
    unfold jointW
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hm : Measurable fun Y : Config d n => ENNReal.ofReal (Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _))
  have h3 : ENNReal.ofReal (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) =
      ∫⁻ Y, ENNReal.ofReal (Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j)))
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) :=
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun Y => (Real.exp_pos _).le)
  calc ∫⁻ Y, jointW (periodicRiesz d s) (withDensityReal ρ) lam β (x, Y)
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)
      = ∫⁻ Y, ENNReal.ofReal (Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)) *
        ENNReal.ofReal (Real.exp (-lam * ∑ j, periodicRiesz d s (x - Y j)))
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := lintegral_congr h1
    _ = _ := by rw [lintegral_const_mul _ hm, h3]

end Marginal2


section Marginal3

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-- The log-density `u(x) = β (g*μ)(x) + log Φ_x(1)` of the first marginal (up to the constant). -/
def uIns (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d) : ℝ :=
  β * convMeasure g μ x + Real.log (phiIns g μ n lam β x)

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
  {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam * n ≤ β)

include hd hs0 hsd hρ hlam hln

theorem exp_uIns (x : Torus d) :
    Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) =
      Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x) *
        phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x := by
  unfold uIns
  rw [Real.exp_add, Real.exp_log (phiIns_pos hd hs0 hsd hρ hlam hln x)]

theorem measurable_uIns :
    Measurable (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hμ := isProbabilityMeasure_mu hρ
  unfold uIns
  exact ((measurable_convMeasure hgm _).const_mul β).add
    (Real.measurable_log.comp (measurable_phiIns hd hs0 hsd hρ hlam hln))

theorem exp_uIns_le : ∃ M : ℝ, 0 < M ∧ ∀ x,
    Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) ≤ M := by
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B', hB'0, hB'⟩ := phiIns_le hd hs0 hsd hρ hlam hln
  refine ⟨Real.exp (|β| * Cc) * Real.exp (β * B') , by positivity, fun x => ?_⟩
  rw [exp_uIns hd hs0 hsd hρ hlam hln x]
  have h1 : Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x) ≤ Real.exp (|β| * Cc) := by
    refine Real.exp_le_exp.2 ?_
    calc β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x
        ≤ |β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x| := le_abs_self _
      _ = |β| * |convMeasure (periodicRiesz d s) (withDensityReal ρ) x| := abs_mul _ _
      _ ≤ |β| * Cc := mul_le_mul_of_nonneg_left (hK.conv x) (abs_nonneg _)
  exact mul_le_mul h1 (hB' x) (phiIns_pos hd hs0 hsd hρ hlam hln x).le (Real.exp_pos _).le

theorem kappa_spec :
    ∃ κ : ℝ≥0∞, (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β).map
        (fun X : Config d (n + 1) => (X 0, Fin.tail X)) =
      κ • ((withDensityReal ρ).prod (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)).withDensity
        (jointW (periodicRiesz d s) (withDensityReal ρ) lam β) ∧
      (∀ x, κ * ENNReal.ofReal (Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x)) =
        ENNReal.ofReal (Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x -
          Real.log (∫ y, Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y)
            ∂(withDensityReal ρ))))) ∧
      firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) =
        (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (Real.exp
          (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x -
            Real.log (∫ y, Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y)
              ∂(withDensityReal ρ))))) := by
  have hμ := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμdef
  set g := periodicRiesz d s with hgdef
  have hgm : Measurable g := measurable_periodicRiesz hd hs0 hsd
  haveI hQ := cavity_isProb hd hs0 hsd β hρ (n + 1) lam hlam
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  obtain ⟨κ, hκ⟩ := map_cons_cavity hd hs0 hsd β hρ n lam hlam
  set Q := cavityLaw g μ (n + 1) lam β with hQdef
  set P0 := cavityLaw g μ n lam β with hP0def
  have hT : Measurable fun X : Config d (n + 1) => (X 0, Fin.tail X) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  have hfm : firstMarginal Q = (Q.map fun X : Config d (n + 1) => (X 0, Fin.tail X)).map Prod.fst := by
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n), Measure.map_map measurable_fst hT]
    rfl
  have hum := measurable_uIns hd hs0 hsd hρ hlam hln
  obtain ⟨M, hM0, hM⟩ := exp_uIns_le hd hs0 hsd hρ hlam hln
  have hint : Integrable (fun y => Real.exp (uIns g μ n lam β y)) μ :=
    Integrable.of_bound (C := M) (Real.measurable_exp.comp hum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hM y)
  set Zu := ∫ y, Real.exp (uIns g μ n lam β y) ∂μ with hZu
  have hZu0 : 0 < Zu := integral_exp_pos hint
  have hfm2 : Measurable fun x : Torus d => ENNReal.ofReal (Real.exp (uIns g μ n lam β x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hum)
  -- the marginal as `κ • μ.withDensity (e^u)`
  have hπ : firstMarginal Q = κ • μ.withDensity (fun x => ENNReal.ofReal (Real.exp (uIns g μ n lam β x))) := by
    rw [hfm, hκ]
    ext A hA
    rw [Measure.map_apply measurable_fst hA, Measure.smul_apply, withDensity_apply _ (measurable_fst hA),
      Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [← lintegral_indicator (measurable_fst hA),
      lintegral_prod _ (((measurable_jointW hgm μ lam β).indicator (measurable_fst hA)).aemeasurable),
      ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · have : ∀ Y : Config d n, (Prod.fst ⁻¹' A : Set (Torus d × Config d n)).indicator
          (jointW g μ lam β) (x, Y) = jointW g μ lam β (x, Y) := fun Y => by
        simp [Set.indicator, hx]
      simp_rw [this, Set.indicator_of_mem hx]
      rw [lintegral_jointW hd hs0 hsd hρ hlam hln x, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← exp_uIns hd hs0 hsd hρ hlam hln x]
    · have : ∀ Y : Config d n, (Prod.fst ⁻¹' A : Set (Torus d × Config d n)).indicator
          (jointW g μ lam β) (x, Y) = 0 := fun Y => by
        simp [Set.indicator, hx]
      simp_rw [this, Set.indicator_of_notMem hx]
      simp
  -- normalisation
  have hone : κ * ENNReal.ofReal Zu = 1 := by
    have h1 : firstMarginal Q Set.univ = 1 := by
      rw [firstMarginal, dif_pos (Nat.succ_pos n)]
      exact measure_univ (μ := Q.map fun X : Config d (n + 1) => X ⟨0, Nat.succ_pos n⟩)
    rw [hπ, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)] at h1
    exact h1
  have hκ' : κ = ENNReal.ofReal (Zu⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hZu0]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hone)
  have hpt : ∀ x, κ * ENNReal.ofReal (Real.exp (uIns g μ n lam β x)) =
      ENNReal.ofReal (Real.exp (uIns g μ n lam β x - Real.log Zu)) := by
    intro x
    rw [hκ', ← ENNReal.ofReal_mul (inv_nonneg.2 hZu0.le), Real.exp_sub,
      Real.exp_log hZu0, div_eq_inv_mul]
  refine ⟨κ, hκ, hpt, ?_⟩
  rw [hπ]
  rw [← withDensity_smul _ hfm2]
  congr 1
  funext x
  rw [Pi.smul_apply, smul_eq_mul, hpt x]

theorem firstMarginal_cavity_eq :
    firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) =
      (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (Real.exp
        (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x -
          Real.log (∫ y, Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y)
            ∂(withDensityReal ρ))))) :=
  (kappa_spec hd hs0 hsd hρ hlam hln).choose_spec.2.2

end Marginal3



section Exch

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

theorem pairSum_perm {g : Torus d → ℝ} (heven : ∀ z, g (-z) = g z) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (Y : Config d n) : pairSum g (fun i => Y (σ i)) = pairSum g Y := by
  rw [pairSum_eq heven, pairSum_eq heven]
  congr 2
  calc ∑ a, ∑ b, g (Y (σ a) - Y (σ b)) = ∑ a, ∑ b, g (Y (σ a) - Y b) :=
        Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => g (Y (σ a) - Y b))
    _ = ∑ a, ∑ b, g (Y a - Y b) := Equiv.sum_comp σ (fun a => ∑ b, g (Y a - Y b))

theorem cavityLaw_exchangeable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) :
    Entropy.IsExchangeable (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  intro σ
  unfold cavityLaw
  exact RefSmall.tiltMeasure_map_perm _ _ (measurable_cavityW hgm _ n lam β) _
    (measurable_pi_iff.2 fun k => measurable_pi_apply _) (RefSmall.pi_map_perm _ σ) (fun Y => by
      show -lam * pairSum (periodicRiesz d s) (fun i => Y (σ i)) +
          β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y (σ i)) =
        -lam * pairSum (periodicRiesz d s) Y +
          β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)
      rw [pairSum_perm (fun z => periodicRiesz_neg z) σ Y,
        Equiv.sum_comp σ (fun i => convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i))])

end Exch


end MarginalAux

end HRS
