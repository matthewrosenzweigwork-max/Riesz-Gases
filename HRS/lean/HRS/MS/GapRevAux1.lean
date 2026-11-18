import HRS.MS.GapRefAux1
import HRS.MS.PoisInvAux2
import HRS.MS.PoisLipAux3

/-!
# GAP-2: reversibility of the semigroup `sg` with respect to a `GapRef` measure

Supplement foundation packet GAP-2 (`docs/S4_PLAN.md`, section 2.4, step 3; row S4.9).  Namespace
`HRS.MS.Gap`, helper prefix `gap234_`.

Main theorem `gap_reversible`: for `GapRef d ρ q B` (so `μ = ρ dx` is a probability measure with finite second
moment and `∇ρ = ρ(-qx+B)`), `q > 0`, `B ∈ C_b^2`, a Brownian filtration `(Ω, P, ℱ, W)`, and `g, h ∈ C²` with
bounded `g, Dg, D²g` (and the same for `h`) one has, for every `t ≥ 0`,
`∫ P_t g · h dμ = ∫ g · P_t h dμ`
(`P_t = sg P W q B t`), both integrands being `μ`-integrable.

Proof.  For fixed `x` the function `s ↦ P_{t-s} g(x) · P_s h(x)` is continuous on `[0,t]` and has derivative
`-P_{t-s}(Lg) P_s h + P_{t-s} g P_s(Lh)` on `(0,t)` (`pois_kolmogorov`).  The derivative is bounded by
`K (1 + ‖x‖²)` (second moment of the flow, `inv_sg_bound`) and jointly continuous (`kl_cont_integral`), so by
Fubini `∫ (g P_t h - P_t g h) dμ = ∫_0^t ∫ (...) dμ ds`.  For each `s`, `P_r L k = L P_r k` (`inv_commute`) and
the Dirichlet identity `gap_dirichlet` (applied twice, with the roles of the two functions exchanged) show that
the inner integral is `-∫⟨∇φ,∇ψ⟩ + ∫⟨∇ψ,∇φ⟩ = 0`.

Statement adjustments relative to the plan sketch (documented, harmless): the generator, the semigroup and the
hypotheses are the explicit objects of `PoisKolm`/`PoisSg` (the bound `HasCbBound 2 Mb B` is used, `GapRef`
provides it for every order); the bounded `C²` class is the predicate `gap234_Sm M g`
(`C²`, `‖D^i g‖ ≤ M` for `i ≤ 2`); integrability of both integrands is part of the conclusion (so the equality
is not a junk value of a Bochner integral).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Interval
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisInv HRS.MS.PoisLip
open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

noncomputable section

namespace HRS.MS.Gap

universe u

variable {d : ℕ}

/-- The class of `C²` functions with all derivatives of order `≤ 2` (including order `0`) bounded by `M`. -/
def gap234_Sm (M : ℝ) (g : Euc d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M

theorem gap234_sm_zero {M : ℝ} {g : Euc d → ℝ} (h : gap234_Sm M g) (y : Euc d) : ‖g y‖ ≤ M := by
  have := h.2 0 (by norm_num) y
  rwa [norm_iteratedFDeriv_zero] at this

theorem gap234_sm_one {M : ℝ} {g : Euc d → ℝ} (h : gap234_Sm M g) (y : Euc d) :
    ‖fderiv ℝ g y‖ ≤ M := by
  have := h.2 1 (by norm_num) y
  rwa [norm_iteratedFDeriv_one] at this

theorem gap234_sm_two {M : ℝ} {g : Euc d → ℝ} (h : gap234_Sm M g) (y : Euc d) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M := by
  rw [kl_norm_fderiv_fderiv']
  exact h.2 2 le_rfl y

theorem gap234_sm_nonneg {M : ℝ} {g : Euc d → ℝ} (h : gap234_Sm M g) : 0 ≤ M :=
  (norm_nonneg _).trans (gap234_sm_zero h 0)

theorem gap234_sm_mono {M M' : ℝ} {g : Euc d → ℝ} (h : gap234_Sm M g) (hM : M ≤ M') :
    gap234_Sm M' g := ⟨h.1, fun i hi y => (h.2 i hi y).trans hM⟩

theorem gap234_sm_of_bounds {M : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (h0 : ∀ y, ‖g y‖ ≤ M)
    (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M) : gap234_Sm M g := by
  refine ⟨hg, fun i hi y => ?_⟩
  interval_cases i
  · rw [norm_iteratedFDeriv_zero]; exact h0 y
  · rw [norm_iteratedFDeriv_one]; exact h1 y
  · rw [← kl_norm_fderiv_fderiv']; exact h2 y

/-- The semigroup preserves the bounded `C²` class, with a constant uniform in `s ∈ [0,T]`. -/
theorem gap234_sg_sm {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → Fin d → ℝ} [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {B : Euc d → Euc d} (hB : HasCbBound 2 Mb B) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {g : Euc d → ℝ} {M : ℝ}, gap234_Sm M g → ∀ s ∈ Icc (0 : ℝ) T,
      gap234_Sm (C * M) (sg P W q B s g) := by
  have hn := sgNoise_of_brownian hW
  obtain ⟨C, hC1, hC⟩ := sg_contDiff (d := d) q Mb hq 2 le_rfl T hT 2 le_rfl
  refine ⟨C, hC1, fun {g M} hg s hs => ?_⟩
  obtain ⟨hu, -, hub⟩ := hC P W hn B hB g (by exact_mod_cast hg.1) M hg.2 s hs
  exact ⟨by exact_mod_cast hu, fun i hi y => hub i hi y⟩

section Rev

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- Joint continuity of `(s, x) ↦ P_{clamp(τ s)} k x` for continuous `k` of linear growth. -/
theorem gap234_cont_clamp [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {B : Euc d → Euc d} (hB : HasCbBound 2 Mb B) {T : ℝ} (hT : 0 ≤ T) {k : Euc d → ℝ}
    (hk : Continuous k) {a : ℝ} (ha : 0 ≤ a) (hka : ∀ y, |k y| ≤ a * (1 + ‖y‖)) {τ : ℝ → ℝ}
    (hτ : Continuous τ) :
    Continuous (fun p : ℝ × Euc d => sg P W q B (clampT T (τ p.1)) k p.2) := by
  have hcont := kl_cont_integral hq le_rfl hB hW hT hk ha hka
  have h1 : Continuous (fun p : ℝ × Euc d => (clampT T (τ p.1), p.2)) :=
    ((continuous_clampT T).comp (hτ.comp continuous_fst)).prodMk continuous_snd
  exact hcont.comp_continuous h1 (fun p => ⟨clampT_mem hT _, mem_univ _⟩)

/-- Linear growth constants of the generator applied to a bounded `C²` function. -/
theorem gap234_L_growth {q Mb : ℝ} {B : Euc d → Euc d} (hBb : ∀ y, ‖B y‖ ≤ Mb) {M : ℝ}
    {g : Euc d → ℝ} (hg : gap234_Sm M g) (y : Euc d) :
    |kolmL q B g y| ≤ (d * M + M * Mb) + (M * |q|) * ‖y‖ :=
  kl_L_growth q hBb (gap234_sm_one hg) (gap234_sm_two hg) y

theorem gap234_lin_form {k : Euc d → ℝ} {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hk : ∀ y, |k y| ≤ a + a' * ‖y‖) (y : Euc d) : |k y| ≤ (a + a') * (1 + ‖y‖) := by
  refine (hk y).trans ?_
  nlinarith [mul_nonneg ha (norm_nonneg y), norm_nonneg y]

theorem gap234_bdd_lin {k : Euc d → ℝ} {M : ℝ} (hM : 0 ≤ M) (hk : ∀ y, ‖k y‖ ≤ M) (y : Euc d) :
    |k y| ≤ M * (1 + ‖y‖) := by
  have := hk y
  rw [Real.norm_eq_abs] at this
  nlinarith [norm_nonneg y]

set_option maxHeartbeats 1600000 in
/-- **GAP-2: reversibility.**  `P_t` is symmetric in `L²(μ)` on the bounded `C²` class, `μ = ρ dx`. -/
theorem gap_reversible [IsProbabilityMeasure P] {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ}
    (hR : GapRef d ρ q B) (hq : 0 < q) (hB : HasCbBound 2 Mb B)
    (hW : IsBrownianFiltration P ℱ W) {g h : Euc d → ℝ} {Mg Mh : ℝ} (hg : gap234_Sm Mg g)
    (hh : gap234_Sm Mh h) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => sg P W q B t g x * h x) (HRS.Whole.withDensityReal ρ) ∧
    Integrable (fun x => g x * sg P W q B t h x) (HRS.Whole.withDensityReal ρ) ∧
    ∫ x, sg P W q B t g x * h x ∂(HRS.Whole.withDensityReal ρ) =
      ∫ x, g x * sg P W q B t h x ∂(HRS.Whole.withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  have hm2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) (HRS.Whole.withDensityReal ρ) := (gap_moment hR).2.1
  have hn := sgNoise_of_brownian hW
  have hBc : Continuous B := hB.1.continuous
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hBb 0)
  have hMg := gap234_sm_nonneg hg
  have hMh := gap234_sm_nonneg hh
  obtain ⟨C, hC1, hC⟩ := gap234_sg_sm hW hq hB ht
  obtain ⟨Cm, hCm, hmom⟩ := sg_second_moment (d := d) q Mb hq t ht
  have hmom' := fun s hs x => hmom P ℱ W hW 2 (by norm_num) B hB s hs x
  -- growth of the generator
  set ag : ℝ := (d : ℝ) * Mg + Mg * Mb with hag
  set ag' : ℝ := Mg * |q| with hag'
  set bh : ℝ := (d : ℝ) * Mh + Mh * Mb with hbh
  set bh' : ℝ := Mh * |q| with hbh'
  have hag0 : 0 ≤ ag := by positivity
  have hag'0 : 0 ≤ ag' := by positivity
  have hbh0 : 0 ≤ bh := by positivity
  have hbh'0 : 0 ≤ bh' := by positivity
  have hLg : ∀ y, |kolmL q B g y| ≤ ag + ag' * ‖y‖ := gap234_L_growth hBb hg
  have hLh : ∀ y, |kolmL q B h y| ≤ bh + bh' * ‖y‖ := gap234_L_growth hBb hh
  have hLgc : Continuous (kolmL q B g) := kl_L_continuous q hBc hg.1
  have hLhc : Continuous (kolmL q B h) := kl_L_continuous q hBc hh.1
  -- clamped, jointly continuous families
  obtain ⟨D, hD⟩ : ∃ D : ℝ → Euc d → ℝ, ∀ s x, D s x =
      -(sg P W q B (clampT t (t - s)) (kolmL q B g) x) * sg P W q B (clampT t s) h x +
        sg P W q B (clampT t (t - s)) g x * sg P W q B (clampT t s) (kolmL q B h) x :=
    ⟨_, fun _ _ => rfl⟩
  have hcU : Continuous (fun p : ℝ × Euc d => sg P W q B (clampT t p.1) h p.2) :=
    gap234_cont_clamp hW hq hB ht hh.1.continuous hMh (gap234_bdd_lin hMh (gap234_sm_zero hh))
      (τ := fun s => s) continuous_id
  have hcV : Continuous (fun p : ℝ × Euc d => sg P W q B (clampT t (t - p.1)) g p.2) :=
    gap234_cont_clamp hW hq hB ht hg.1.continuous hMg (gap234_bdd_lin hMg (gap234_sm_zero hg))
      (τ := fun s => t - s) (continuous_const.sub continuous_id)
  have hcU' : Continuous (fun p : ℝ × Euc d => sg P W q B (clampT t p.1) (kolmL q B h) p.2) :=
    gap234_cont_clamp hW hq hB ht hLhc (add_nonneg hbh0 hbh'0) (gap234_lin_form hbh0 hbh'0 hLh)
      (τ := fun s => s) continuous_id
  have hcV' : Continuous (fun p : ℝ × Euc d => sg P W q B (clampT t (t - p.1)) (kolmL q B g) p.2) :=
    gap234_cont_clamp hW hq hB ht hLgc (add_nonneg hag0 hag'0) (gap234_lin_form hag0 hag'0 hLg)
      (τ := fun s => t - s) (continuous_const.sub continuous_id)
  have hDc : Continuous (fun p : ℝ × Euc d => D p.1 p.2) := by
    simp_rw [hD]
    exact (hcV'.neg.mul hcU).add (hcV.mul hcU')
  -- pointwise bound
  set A0 : ℝ := (ag + ag' * (1 + Cm)) * Mh + Mg * (bh + bh' * (1 + Cm)) with hA0
  set A1 : ℝ := ag' * Cm * Mh + Mg * (bh' * Cm) with hA1
  have hA10 : 0 ≤ A1 := by positivity
  have hDb : ∀ s x, |D s x| ≤ A0 + A1 * ‖x‖ ^ 2 := by
    intro s x
    have hs1 : clampT t s ∈ Icc (0 : ℝ) t := clampT_mem ht s
    have hs2 : clampT t (t - s) ∈ Icc (0 : ℝ) t := clampT_mem ht (t - s)
    have hU : |sg P W q B (clampT t s) h x| ≤ Mh := by
      have := ld_sg_bound (P := P) (W := W) (q := q) (B := B) (h := h) (M0 := Mh)
        (gap234_sm_zero hh) (clampT t s) x
      rwa [Real.norm_eq_abs] at this
    have hV : |sg P W q B (clampT t (t - s)) g x| ≤ Mg := by
      have := ld_sg_bound (P := P) (W := W) (q := q) (B := B) (h := g) (M0 := Mg)
        (gap234_sm_zero hg) (clampT t (t - s)) x
      rwa [Real.norm_eq_abs] at this
    have hV' : |sg P W q B (clampT t (t - s)) (kolmL q B g) x| ≤
        ag + ag' * (1 + Cm * (1 + ‖x‖ ^ 2)) :=
      (inv_sg_bound hW hq.le (m := 2) (by norm_num) hB hs2.1 (fun y => hmom' _ hs2 y) hLgc hag'0
        hLg x).2
    have hU' : |sg P W q B (clampT t s) (kolmL q B h) x| ≤ bh + bh' * (1 + Cm * (1 + ‖x‖ ^ 2)) :=
      (inv_sg_bound hW hq.le (m := 2) (by norm_num) hB hs1.1 (fun y => hmom' _ hs1 y) hLhc hbh'0
        hLh x).2
    rw [hD]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg]
    have e1 : |sg P W q B (clampT t (t - s)) (kolmL q B g) x| * |sg P W q B (clampT t s) h x| ≤
        (ag + ag' * (1 + Cm * (1 + ‖x‖ ^ 2))) * Mh :=
      mul_le_mul hV' hU (abs_nonneg _) (by positivity)
    have e2 : |sg P W q B (clampT t (t - s)) g x| * |sg P W q B (clampT t s) (kolmL q B h) x| ≤
        Mg * (bh + bh' * (1 + Cm * (1 + ‖x‖ ^ 2))) :=
      mul_le_mul hV hU' (abs_nonneg _) hMg
    have e3 : (ag + ag' * (1 + Cm * (1 + ‖x‖ ^ 2))) * Mh + Mg * (bh + bh' * (1 + Cm * (1 + ‖x‖ ^ 2))) =
        A0 + A1 * ‖x‖ ^ 2 := by rw [hA0, hA1]; ring
    linarith
  have hΦ : Integrable (fun x : Euc d => A0 + A1 * ‖x‖ ^ 2) (HRS.Whole.withDensityReal ρ) :=
    (integrable_const A0).add (hm2.const_mul A1)
  -- Fubini
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) t) with hν
  have hmeas : Measurable (fun p : Euc d × ℝ => D p.2 p.1) := hDc.measurable.comp measurable_swap
  have hint : Integrable (Function.uncurry fun (x : Euc d) (s : ℝ) => D s x) ((HRS.Whole.withDensityReal ρ).prod ν) := by
    have hb : Integrable (fun p : Euc d × ℝ => (A0 + A1 * ‖p.1‖ ^ 2) * (1 : ℝ)) ((HRS.Whole.withDensityReal ρ).prod ν) :=
      Integrable.mul_prod (f := fun x : Euc d => A0 + A1 * ‖x‖ ^ 2) (g := fun _ : ℝ => (1 : ℝ))
        hΦ (integrable_const 1)
    refine hb.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, mul_one]
    exact hDb p.2 p.1
  have hswap := integral_integral_swap hint
  -- the inner integral over `x` vanishes
  have hzero : ∫ s, ∫ x, D s x ∂(HRS.Whole.withDensityReal ρ) ∂ν = 0 := by
    refine integral_eq_zero_of_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
    have hs'' : t - s ∈ Icc (0 : ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hφ := hC hg (t - s) hs''
    have hψ := hC hh s hs'
    set φ := sg P W q B (t - s) g with hφdef
    set ψ := sg P W q B s h with hψdef
    have hDx : ∀ x, D s x = -(kolmL q B φ x * ψ x) + φ x * kolmL q B ψ x := fun x => by
      rw [hD, clampT_of_mem hs', clampT_of_mem hs'']
      rw [inv_commute hW hq le_rfl hB hg.1 hg.2 ht hs'' x, inv_commute hW hq le_rfl hB hh.1 hh.2 ht hs' x]
      ring
    have d1 := gap_dirichlet hR hφ.1 (gap234_sm_one hφ) (gap234_sm_two hφ)
      (hψ.1.of_le (by norm_num)) (Cψ := C * Mh)
      (fun x => by have := gap234_sm_zero hψ x; rwa [Real.norm_eq_abs] at this) (gap234_sm_one hψ)
    have d2 := gap_dirichlet hR hψ.1 (gap234_sm_one hψ) (gap234_sm_two hψ)
      (hφ.1.of_le (by norm_num)) (Cψ := C * Mg)
      (fun x => by have := gap234_sm_zero hφ x; rwa [Real.norm_eq_abs] at this) (gap234_sm_one hφ)
    obtain ⟨i1, -, e1⟩ := d1
    obtain ⟨i2, -, e2⟩ := d2
    have i2' : Integrable (fun x => φ x * kolmL q B ψ x) (HRS.Whole.withDensityReal ρ) := by
      refine i2.congr (ae_of_all _ fun x => ?_)
      simp only [mul_comm]
    have e2' : ∫ x, φ x * kolmL q B ψ x ∂(HRS.Whole.withDensityReal ρ) = -∫ x, inner ℝ (gradient φ x) (gradient ψ x) ∂(HRS.Whole.withDensityReal ρ) := by
      have : ∀ x, φ x * kolmL q B ψ x = kolmL q B ψ x * φ x := fun x => mul_comm _ _
      simp_rw [this]
      rw [e2]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      exact real_inner_comm _ _
    simp_rw [hDx]
    have i1' : Integrable (fun x => -(kolmL q B φ x * ψ x)) (HRS.Whole.withDensityReal ρ) := i1.neg
    rw [integral_add i1' i2', integral_neg, e1, e2', Pi.zero_apply]
    ring
  -- the pointwise fundamental theorem of calculus
  have hpt : ∀ x, ∫ s, D s x ∂ν = g x * sg P W q B t h x - sg P W q B t g x * h x := by
    intro x
    have hkh := (pois_kolmogorov hq le_rfl hB hW hh.1 (gap234_sm_one hh)
      (fun y => hh.2 2 le_rfl y)).2.2.1 x
    have hkg := (pois_kolmogorov hq le_rfl hB hW hg.1 (gap234_sm_one hg)
      (fun y => hg.2 2 le_rfl y)).2.2.1 x
    have hcont : ContinuousOn (fun s : ℝ => sg P W q B (t - s) g x * sg P W q B s h x) (Icc 0 t) := by
      have hc : Continuous (fun s : ℝ => sg P W q B (clampT t (t - s)) g x *
          sg P W q B (clampT t s) h x) :=
        (hcV.comp (continuous_id.prodMk continuous_const)).mul
          (hcU.comp (continuous_id.prodMk continuous_const))
      refine hc.continuousOn.congr (fun s hs => ?_)
      have hs'' : t - s ∈ Icc (0 : ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simp only [clampT_of_mem hs, clampT_of_mem hs'']
    have hder : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt (fun s : ℝ => sg P W q B (t - s) g x * sg P W q B s h x)
        (D s x) s := by
      intro s hs
      have h1 := hkg (t - s) (by linarith [hs.2])
      have h2 := h1.scomp s ((hasDerivAt_id s).const_sub t)
      have h3 := h2.mul (hkh s hs.1)
      have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.le⟩
      have hs'' : t - s ∈ Icc (0 : ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      refine h3.congr_deriv ?_
      rw [hD, clampT_of_mem hs', clampT_of_mem hs'']
      simp
    have hii : IntervalIntegrable (fun s => D s x) volume 0 t :=
      (hDc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hder hii
    have e1 : ∫ s, D s x ∂ν = ∫ s in (0 : ℝ)..t, D s x := by
      rw [hν, intervalIntegral.integral_of_le ht]
    rw [e1, hftc]
    simp only [sub_self, sub_zero]
    rw [ld_sg_zero hn hq.le (m := 2) (by norm_num) hB g x, ld_sg_zero hn hq.le (m := 2) (by norm_num) hB h x]
  -- conclusion
  have hcg : Continuous g := hg.1.continuous
  have hch : Continuous h := hh.1.continuous
  have hst := hC hh t ⟨ht, le_rfl⟩
  have hsg := hC hg t ⟨ht, le_rfl⟩
  have I1 : Integrable (fun x => sg P W q B t g x * h x) (HRS.Whole.withDensityReal ρ) := by
    refine (integrable_const (C * Mg * Mh)).mono' (hsg.1.continuous.mul hch).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (gap234_sm_zero hsg x) (gap234_sm_zero hh x) (norm_nonneg _)
      ((norm_nonneg _).trans (gap234_sm_zero hsg 0))
  have I2 : Integrable (fun x => g x * sg P W q B t h x) (HRS.Whole.withDensityReal ρ) := by
    refine (integrable_const (Mg * (C * Mh))).mono' (hcg.mul hst.1.continuous).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (gap234_sm_zero hg x) (gap234_sm_zero hst x) (norm_nonneg _) hMg
  refine ⟨I1, I2, ?_⟩
  have key : ∫ x, (g x * sg P W q B t h x - sg P W q B t g x * h x) ∂(HRS.Whole.withDensityReal ρ) = 0 := by
    have : ∀ x, g x * sg P W q B t h x - sg P W q B t g x * h x = ∫ s, D s x ∂ν := fun x => (hpt x).symm
    simp_rw [this]
    rw [hswap]
    exact hzero
  rw [integral_sub I2 I1] at key
  linarith

end Rev

end HRS.MS.Gap

end
