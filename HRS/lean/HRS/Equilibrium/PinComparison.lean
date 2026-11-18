/-
# HRS.Equilibrium.PinComparison -- proof of Lemma 4.10 (`pin_comparison`, EQ-01b)

Downstream of `PairCorrection` (the proof uses the pole-volume bounds `twopole_vol` etc. proved
there, through `HRS.Equilibrium.PinStep`).  The abstract weighted Dobrushin comparison is
`HRS.External.WeakPointwise`.

Route (source lines 4503-4550, function-side form): one pin step by the weighted Dobrushin
comparison (`pin_step_set`), then dimension changes `n → n+1` by disintegration over the extra
coordinate (`pinned_marginal_succ`) and the pin step with one pin.
-/
import HRS.Equilibrium.PinStep

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace PinAux

open HRS.External HRS.External.RefMarg

section Mixture

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- Two-sided comparison of a mixture. -/
theorem mixture_le {ω a e : ι → ℝ≥0∞} {c ε : ℝ≥0∞} (hω : Measurable ω) (he : Measurable e)
    (hω1 : ∫⁻ x, ω x ∂μ = 1) (hae : ∀ x, a x ≤ c + e x) (hea : ∀ x, c ≤ a x + e x)
    (hε : ∫⁻ x, ω x * e x ∂μ ≤ ε) :
    ∫⁻ x, ω x * a x ∂μ ≤ c + ε ∧ c ≤ ∫⁻ x, ω x * a x ∂μ + ε := by
  have hc : ∫⁻ x, ω x * c ∂μ = c := by
    rw [lintegral_mul_const _ hω, hω1, one_mul]
  constructor
  · calc ∫⁻ x, ω x * a x ∂μ ≤ ∫⁻ x, ω x * (c + e x) ∂μ := lintegral_mono fun x => mul_le_mul' le_rfl (hae x)
      _ = ∫⁻ x, (ω x * c + ω x * e x) ∂μ := by simp_rw [mul_add]
      _ = ∫⁻ x, ω x * c ∂μ + ∫⁻ x, ω x * e x ∂μ := lintegral_add_left (hω.mul_const c) _
      _ ≤ c + ε := by rw [hc]; exact add_le_add le_rfl hε
  · calc c = ∫⁻ x, ω x * c ∂μ := hc.symm
      _ ≤ ∫⁻ x, ω x * (a x + e x) ∂μ := lintegral_mono fun x => mul_le_mul' le_rfl (hea x)
      _ = ∫⁻ x, (ω x * a x + ω x * e x) ∂μ := by simp_rw [mul_add]
      _ = ∫⁻ x, ω x * a x ∂μ + ∫⁻ x, ω x * e x ∂μ := lintegral_add_right _ (hω.mul he)
      _ ≤ ∫⁻ x, ω x * a x ∂μ + ε := add_le_add le_rfl hε

end Mixture


section DimStep2

variable {d : ℕ}

/-- The pin weight of the unpinned ensemble is a constant times a measurable function. -/
theorem pinWeight_eq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    {lam : ℝ} (hlam : 0 ≤ lam) {B : Type*} [Fintype B] (a : B → Torus d) (n : ℕ) (x : Torus d) :
    pinWeight V lam a n x
      = (fieldNorm V (pinField V lam a) lam n * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹) *
          (ENNReal.ofReal (Real.exp (pinField V lam a x)) * ENNReal.ofReal (cavU V lam n a x)) := by
  unfold pinWeight
  rw [lintegral_fieldWeight_pinsWith V hlam a n x]
  ring

theorem measurable_pinWeight {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    {lam : ℝ} (hlam : 0 ≤ lam) {B : Type*} [Fintype B] (a : B → Torus d) (n : ℕ) :
    Measurable (pinWeight V lam a n) := by
  have : pinWeight V lam a n = fun x =>
      (fieldNorm V (pinField V lam a) lam n * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹) *
          (ENNReal.ofReal (Real.exp (pinField V lam a x)) * ENNReal.ofReal (cavU V lam n a x)) :=
    funext fun x => pinWeight_eq V hlam a n x
  rw [this]
  exact measurable_const.mul
    ((ENNReal.measurable_ofReal.comp (isField_pinField V hlam a).measurable.exp).mul
      (ENNReal.measurable_ofReal.comp (measurable_cavU V hlam n a)))

/-- The law of the extra coordinate is `μ` with density the pin weight. -/
theorem marginal_eq_pinWeight {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    {lam : ℝ} (hlam : 0 ≤ lam) {B : Type*} [Fintype B] (a : B → Torus d) {n : ℕ} (i : Fin (n + 1)) :
    (pinnedLaw V lam (n + 1) a).map (fun y => y i) = μ.withDensity (pinWeight V lam a n) := by
  rw [marginal_eq_withDensity V hlam a i]
  congr 1
  funext x
  exact (pinWeight_eq V hlam a n x).symm

end DimStep2


section IeBound

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q : Torus d → ℝ}

theorem e_eq (hq0 : ∀ z, 0 ≤ q z) (hint : ∀ x, Integrable (fun z => q (z - x)) μ) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (B : Set (Torus d)) (x : Torus d) :
    ENNReal.ofReal (∫ z in B, c0 * (1 + q (z - x)) ∂μ)
      = ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ := by
  refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (((integrable_const (1 : ℝ)).add (hint x)).const_mul c0).integrableOn
  · have := hq0 (z - x); positivity

theorem measurable_e (hqm : Measurable q) {c0 : ℝ} (B : Set (Torus d)) :
    Measurable (fun x : Torus d => ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ) := by
  have : Measurable (fun p : Torus d × Torus d => ENNReal.ofReal (c0 * (1 + q (p.2 - p.1)))) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.add ?_))
    exact hqm.comp (measurable_snd.sub measurable_fst)
  exact this.lintegral_prod_right' (ν := μ.restrict B)

/-- `∫ ω e dμ ≤ K c₀ (1 + γ₀) μ(B)` when `ω μ ≤ K μ`. -/
theorem Ie_bound (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {ω : Torus d → ℝ≥0∞} (hω : Measurable ω) {K : ℝ} (hK : 0 ≤ K)
    (hωK : μ.withDensity ω ≤ ENNReal.ofReal K • μ) {c0 γ₀ : ℝ} (hc0 : 0 ≤ c0) (hγ₀ : 0 ≤ γ₀)
    (hrow : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂μ ≤ ENNReal.ofReal γ₀)
    (B : Set (Torus d)) (hB : MeasurableSet B) :
    ∫⁻ x, ω x * (∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ) ∂μ
      ≤ ENNReal.ofReal (K * c0 * (1 + γ₀)) * μ B := by
  have hem := measurable_e (μ := μ) hqm (c0 := c0) B
  have hwd : ∫⁻ x, (∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ) ∂(μ.withDensity ω)
      = ∫⁻ x, ω x * (∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hω hem]; rfl
  rw [← hwd]
  calc ∫⁻ x, ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ ∂(μ.withDensity ω)
      ≤ ∫⁻ x, ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ ∂(ENNReal.ofReal K • μ) :=
        lintegral_mono' hωK le_rfl
    _ = ENNReal.ofReal K * ∫⁻ x, ∫⁻ z in B, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ ∂μ := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal K * ∫⁻ z in B, ∫⁻ x, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ ∂μ := by
        congr 1
        refine lintegral_lintegral_swap ?_
        have : Measurable (Function.uncurry fun (x z : Torus d) => ENNReal.ofReal (c0 * (1 + q (z - x)))) := by
          refine ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.add ?_))
          exact hqm.comp (measurable_snd.sub measurable_fst)
        exact this.aemeasurable
    _ ≤ ENNReal.ofReal K * ∫⁻ z in B, ENNReal.ofReal c0 * (1 + ENNReal.ofReal γ₀) ∂μ := by
        gcongr with z
        calc ∫⁻ x, ENNReal.ofReal (c0 * (1 + q (z - x))) ∂μ
            = ∫⁻ x, ENNReal.ofReal c0 * (1 + ENNReal.ofReal (q (z - x))) ∂μ := by
              refine lintegral_congr fun x => ?_
              have := hq0 (z - x)
              rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add zero_le_one this, ENNReal.ofReal_one]
          _ = ENNReal.ofReal c0 * (∫⁻ x, 1 ∂μ + ∫⁻ x, ENNReal.ofReal (q (z - x)) ∂μ) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                lintegral_add_left measurable_const]
          _ ≤ ENNReal.ofReal c0 * (1 + ENNReal.ofReal γ₀) := by
              gcongr
              · simp
              · exact hrow z
    _ = ENNReal.ofReal (K * c0 * (1 + γ₀)) * μ B := by
        rw [setLIntegral_const, ENNReal.ofReal_mul (mul_nonneg hK hc0),
          ENNReal.ofReal_mul hK, ENNReal.ofReal_add zero_le_one hγ₀, ENNReal.ofReal_one]
        ring

end IeBound


section RealEnn

variable {α : Type*} [MeasurableSpace α]

theorem le_add_of_abs_real_le {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q] {B : Set α}
    {E : ℝ} (h : |P.real B - Q.real B| ≤ E) : P B ≤ Q B + ENNReal.ofReal E := by
  rw [abs_le] at h
  have hE : 0 ≤ E := by linarith [h.1, h.2, abs_nonneg (P.real B - Q.real B)]
  have h1 : P B = ENNReal.ofReal (P.real B) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have h2 : Q B = ENNReal.ofReal (Q.real B) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [h1, h2, ← ENNReal.ofReal_add measureReal_nonneg hE]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem abs_real_le_of_le_add {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q] {B : Set α}
    {E : ℝ} (hE : 0 ≤ E) (h1 : P B ≤ Q B + ENNReal.ofReal E) (h2 : Q B ≤ P B + ENNReal.ofReal E) :
    |P.real B - Q.real B| ≤ E := by
  have a1 : P.real B ≤ Q.real B + E := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hE] at this
  have a2 : Q.real B ≤ P.real B + E := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) h2
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hE] at this
  rw [abs_le]; constructor <;> linarith

end RealEnn


section DimStep3

variable {d : ℕ}

theorem dim_step {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z)
    (hqm : Measurable q) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (a : ℕ) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (_ : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma β))
        (N n : ℕ), a + 1 ≤ N → n + 1 ≤ N → ∀ (i : Fin (n + 1)) (j : Fin n) (B : Set (Torus d)),
        MeasurableSet B →
        |((pinnedLaw V (β / N) (n + 1) (fun e : Empty => e.elim)).map
              (fun y => y (i.succAbove j))).real B
          - ((pinnedLaw V (β / N) n (fun e : Empty => e.elim)).map (fun y => y j)).real B|
          ≤ C3 * (β / N) * (withDensityReal ρ).real B := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨C, hC0, hC⟩ := pin_step_set hd hcrit β hβ ρ hρ q hq0 hqm Cq hqenv hdec a
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  set Kc : ℝ := Real.exp ((β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀) with hKc
  refine ⟨Kc * C * (1 + γ₀), by positivity, ?_⟩
  intro V hVq hVγ hVM hVM' hrow N n hNa hn1 i j B hB
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
    have := hC V hVq hVγ hVM hVM' N n 1 hNa (by omega) (by omega) (fun _ => x) _ _ _ _ hψ hψ'
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
  refine (abs_real_le_of_le_add hεnn h1 h2).trans (le_of_eq ?_)
  rw [hc0]; ring

end DimStep3


section Chain

variable {d : ℕ}

open Classical in
/-- Coordinate-free value of the `n`-particle unpinned marginal on `B`. -/
def cavM {μ : Measure (Torus d)} (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (B : Set (Torus d)) : ℝ :=
  if h : 0 < n then ((pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun y => y ⟨0, h⟩)).real B
  else 0

theorem coord_eq_cavM {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (lam : ℝ) {n : ℕ} (k : Fin n) (B : Set (Torus d)) :
    ((pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun y => y k)).real B = cavM V lam n B := by
  have hn : 0 < n := Fin.pos k
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold cavM
  rw [dif_pos hn]
  have h1 := pinnedLaw_marginal_eq V (lam := lam) n k
  have h2 := pinnedLaw_marginal_eq V (lam := lam) n ⟨0, hn⟩
  rw [h1, h2]

theorem chain_unpinned {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z)
    (hqm : Measurable q) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (a : ℕ) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (_ : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma β))
        (N : ℕ) (n0 : ℕ) (j : ℕ), a + 1 ≤ N → 1 ≤ n0 → n0 + j ≤ N → ∀ (B : Set (Torus d)),
        MeasurableSet B →
        |cavM V (β / N) (n0 + j) B - cavM V (β / N) n0 B|
          ≤ j * (C3 * (β / N) * (withDensityReal ρ).real B) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨C3, hC3, hdim⟩ := dim_step hd hcrit β hβ ρ hρ q hq0 hqm Cq hqenv hdec a
  refine ⟨C3, hC3, ?_⟩
  intro V hVq hVγ hVM hVM' hrow N n0 j hNa hn0 hN B hB
  induction j with
  | zero => simp
  | succ j ih =>
    have hih := ih (by omega)
    have hn : 0 < n0 + j := by omega
    have hstep := hdim V hVq hVγ hVM hVM' hrow N (n0 + j) hNa (by omega) ⟨0, by omega⟩ ⟨0, hn⟩ B hB
    rw [coord_eq_cavM, coord_eq_cavM] at hstep
    have e : n0 + (j + 1) = n0 + j + 1 := rfl
    rw [e]
    calc |cavM V (β / N) (n0 + j + 1) B - cavM V (β / N) n0 B|
        ≤ |cavM V (β / N) (n0 + j + 1) B - cavM V (β / N) (n0 + j) B|
          + |cavM V (β / N) (n0 + j) B - cavM V (β / N) n0 B| := abs_sub_le _ _ _
      _ ≤ C3 * (β / N) * (withDensityReal ρ).real B + j * (C3 * (β / N) * (withDensityReal ρ).real B) :=
          add_le_add hstep hih
      _ = ((j + 1 : ℕ) : ℝ) * (C3 * (β / N) * (withDensityReal ρ).real B) := by push_cast; ring

end Chain

theorem min_aux {t K C' C x : ℝ} (ht : t ≤ C' * x) (htK : t ≤ K) (hx : 0 ≤ x) (hCC' : C' ≤ C)
    (hCK : K ≤ C) : t ≤ C * min 1 x := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    exact ht.trans (mul_le_mul_of_nonneg_right hCC' hx)
  · push Not at hx1
    rw [min_eq_left hx1.le, mul_one]
    exact htK.trans hCK

theorem small_aux {t K C x : ℝ} {a N : ℕ} (hN : 1 ≤ N) (hNa : N ≤ a) (ht : t ≤ K) (hK : 0 ≤ K)
    (hx : 1 / (N : ℝ) ≤ x) (hC : K * (a + 1) ≤ C) : t ≤ C * min 1 x := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNa' : (N : ℝ) ≤ a := by exact_mod_cast hNa
  have h1 : 1 / ((a : ℝ) + 1) ≤ min 1 x := by
    refine le_min ?_ ?_
    · rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) a]
    · refine le_trans ?_ hx
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
  calc t ≤ K := ht
    _ = K * (a + 1) * (1 / ((a : ℝ) + 1)) := by field_simp
    _ ≤ C * min 1 x := by
        refine mul_le_mul hC h1 (by positivity) ?_
        exact hK.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) a, hC, hK])


end PinAux

section Main

variable {d : ℕ} {s : ℝ}

open PinAux HRS.External HRS.External.RefMarg in
/-- Lemma 4.10 `M:Q:lem:pin` (restatement of `HRS.pin_comparison`, proved here because the proof
uses the volume estimates proved after the statement in `PairCorrection`). -/
theorem pin_comparison_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
      (∀ z, q (-z) = q z) →
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 → periodicRiesz d s z = q z + k z + c) →
      (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₀) →
      ∀ a j : ℕ, ∃ C : ℝ, ∀ N : ℕ, j + 2 ≤ N → ∀ h : Torus d → ℝ, Measurable h →
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
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  refine ⟨pinGamma β, pinGamma_pos hβ, ?_⟩
  intro q Cq hqm hq0 hqe hdec hqenv hrow a j
  obtain ⟨C1, hC1, hstep⟩ := pin_step_set hd hcrit β hβ ρ hρ q hq0 hqm Cq hqenv hdec a
  obtain ⟨C3, hC3, hchain⟩ := chain_unpinned hd hcrit β hβ ρ hρ q hq0 hqm Cq hqenv hdec a
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  set K0 : ℝ := Real.exp ((β * γ₀ + 1) + 1 + β * (1 + a) * γ₀) with hK0
  have hK0pos : 0 < K0 := Real.exp_pos _
  refine ⟨max (β * (C1 + j * C3)) (K0 * (a + 1)), ?_⟩
  intro N hN h hhm hh1 A i
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨V, hVq, hVφ, hVγ, hVM, hVM'⟩ := exists_weakPotential (withDensityReal ρ) β γ₀ hγ₀ q h
    hqm hq0 hqe hrow hhm hh1 hβ
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
      have hS1 := hstep V hVq hVγ hVM hVM' N (N - j) a hNa hnN (Nat.le_succ a) A
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
      have hch := hchain V hVq hVγ hVM hVM' hrow N (N - j) j hNa (by omega) (by omega) B hB
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
      ?_ hz2 ?_ (le_max_left _ _) (le_trans (by nlinarith [Nat.cast_nonneg (α := ℝ) a, hK0pos]) (le_max_right _ _))
    · refine hz1.trans (le_of_eq ?_)
      simp only [hΨ]; field_simp
    · have := hg1 z
      have : 0 ≤ ∑ k, q (z - A k) := Finset.sum_nonneg fun k _ => hq0 _
      positivity
  · -- small N
    push Not at hNa
    filter_upwards [hK] with z hz
    refine small_aux (a := a) (N := N) (by omega) (by omega) hz hK0pos.le ?_ (le_max_right _ _)
    have h0 : 0 ≤ ∑ k, q (z - A k) := Finset.sum_nonneg fun k _ => hq0 _
    rw [one_div]
    have : (1 : ℝ) / N ≤ 1 / N * (1 + ∑ k, q (z - A k)) := by
      nlinarith [one_div_nonneg.2 hNr.le]
    simpa [one_div] using this

end Main

end HRS
