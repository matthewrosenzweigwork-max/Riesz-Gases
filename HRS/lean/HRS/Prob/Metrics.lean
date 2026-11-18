import Mathlib
import HRS.Prob.YurinskiiStrassen
import HRS.Prob.YurinskiiLindeberg

/-!
# Probability metrics on Banach spaces: `C_b^k` smooth distances and Wasserstein distances

Source: HRS periodic main paper, display `H:eq:metrics` (source lines 507-516):

* `‖Φ‖_{C_b^k(B)} = ∑_{j=0}^k sup_{z∈B} ‖D^jΦ(z)‖` (SUM over orders, multilinear
  operator norms);
* `d_k^B(P,Q) = sup_{‖Φ‖_{C_b^k(B)} ≤ 1} |∫Φ d(P-Q)|`;
* `W_p^B`, `1 ≤ p < ∞`, uses the norm of `B` and the usual infimum over couplings.

Also: Lemma 4.27 `M:R:lem:smooth-translation` (source lines 5660-5682),
Lemma A.26 `M:B:lem:dc2-to-w1` (10704-10710), Lemma A.31
`M:B:newprob:gaussian-covariance` (11003-11014), Lemma A.37 `M:B:lem:yurinskii`
(11573-11579).

## Representation

* Test functions are arbitrary `Φ : B → ℝ`; the `C_b^k` unit ball is the set of
  `Φ` with `ContDiff ℝ k Φ` and `cbNorm k Φ ≤ 1` (`ContDiff` guarantees the
  derivatives `iteratedFDeriv ℝ j Φ` exist; `iteratedFDeriv` is the multilinear
  derivative with operator norm).
* `smoothDist k P Q` is a real-valued supremum; for finite measures `P, Q` the set
  is bounded (by `P univ + Q univ`), so the real `iSup` is the true supremum.
* `wassersteinE p P Q : ℝ≥0∞` is the infimum over couplings of
  `(∫⁻ ‖x-y‖^p dπ)^{1/p}`; it is `∞` when no coupling has finite cost, exactly as
  in the source.  `wasserstein p P Q := (wassersteinE p P Q).toReal` is the real
  version (0 when infinite; theorem statements below use the `ℝ≥0∞` version where
  finiteness is part of the claim).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

section Metrics

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]

/-- `‖Φ‖_{C_b^k(B)} = ∑_{j=0}^k sup_z ‖D^jΦ(z)‖` (source line 510). -/
def cbNorm (k : ℕ) (Φ : B → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖

/-- The `C_b^k(B)` unit ball: `C^k` functions with `‖Φ‖_{C_b^k} ≤ 1`. The boundedness conjunct
encodes the subscript `b` of `C_b^k` and prevents the junk value `0` of the real `iSup` in
`cbNorm` for unbounded derivatives. -/
def CbUnitBall (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] (k : ℕ) : Set (B → ℝ) :=
  {Φ | ContDiff ℝ k Φ ∧ (∀ j ≤ k, BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ j Φ z‖)) ∧
    cbNorm k Φ ≤ 1}

/-- `d_k^B(P,Q) = sup_{‖Φ‖_{C_b^k(B)} ≤ 1} |∫Φ dP - ∫Φ dQ|` (source line 511). -/
def smoothDist (k : ℕ) (P Q : Measure B) : ℝ :=
  ⨆ Φ : CbUnitBall B k, |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q|

/-- `π` is a coupling of `P` and `Q`. -/
def IsCoupling (π : Measure (B × B)) (P Q : Measure B) : Prop :=
  π.map Prod.fst = P ∧ π.map Prod.snd = Q

/-- The set of couplings of `P` and `Q`. -/
def couplings (P Q : Measure B) : Set (Measure (B × B)) := {π | IsCoupling π P Q}

/-- `W_p^B(P,Q)` in `ℝ≥0∞`: `inf_π (∫ ‖x - y‖^p dπ)^{1/p}` over couplings. -/
def wassersteinE (p : ℝ) (P Q : Measure B) : ℝ≥0∞ :=
  ⨅ π : couplings P Q, (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p)

/-- Real-valued `W_p^B` (equal to `0` when `wassersteinE = ∞`). -/
def wasserstein (p : ℝ) (P Q : Measure B) : ℝ := (wassersteinE p P Q).toReal

/-- The law of a random variable. -/
abbrev law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B) : Measure B :=
  P.map X

/-- `p`-th moment `E‖X‖^p`. -/
def momentNorm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) (X : Ω → B) : ℝ :=
  ∫ ω, ‖X ω‖ ^ p ∂P

/-- The leading smooth-distance constant `𝔠_k^B(G,h) := sup_{‖Φ‖_{C_b^k}≤1} E[DΦ(G)[h]]`
of Lemma 4.27 (source line 5674 region). -/
def smoothConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (k : ℕ)
    (G : Ω → B) (h : B) : ℝ :=
  ⨆ Φ : CbUnitBall B k, ∫ ω, fderiv ℝ Φ.1 (G ω) h ∂P

/-- The centered Gaussian measures of Mathlib (`IsGaussian` with zero mean). -/
def IsCenteredGaussian [TopologicalSpace B] [BorelSpace B] (γ : Measure B) : Prop :=
  ProbabilityTheory.IsGaussian γ ∧ ∀ L : StrongDual ℝ B, ∫ z, L z ∂γ = 0

end Metrics

/-! ### Elementary properties of the metrics (work package METR-01) -/

section MetricFacts

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

/-! #### Helpers for the Wasserstein facts -/

/-- Hölder/Jensen for `lintegral` on a probability space, measurable case. -/
theorem lintegral_rpow_mono_meas {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {h : α → ℝ≥0∞} (hh : Measurable h) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) :
    (∫⁻ a, h a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ a, h a ^ q ∂μ) ^ (1 / q) := by
  rcases hpq.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hq : 0 < q := hp.trans hlt
  set r : ℝ := q / p with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hp]; linarith
  have hconj : r.HolderConjugate (r / (r - 1)) :=
    Real.HolderConjugate.conjExponent hr1 |>.symm.symm
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj (f := fun a => h a ^ p) (g := fun _ => 1)
    (hh.pow_const p).aemeasurable aemeasurable_const
  have e1 : ∀ a, (h a ^ p) ^ r = h a ^ q := fun a => by
    rw [← ENNReal.rpow_mul]; congr 1; rw [hr]; field_simp
  simp only [Pi.mul_apply, mul_one, e1, ENNReal.one_rpow, lintegral_const, measure_univ] at H
  have e2 : 1 / r = p / q := by rw [hr]; field_simp
  rw [e2] at H
  calc (∫⁻ a, h a ^ p ∂μ) ^ (1 / p) ≤ ((∫⁻ a, h a ^ q ∂μ) ^ (p / q)) ^ (1 / p) := by
        gcongr
    _ = (∫⁻ a, h a ^ q ∂μ) ^ (1 / q) := by
        rw [← ENNReal.rpow_mul]; congr 1; field_simp

/-- Hölder/Jensen for the (lower) `lintegral` of an arbitrary, not necessarily measurable,
function on a probability space. -/
theorem lintegral_rpow_mono {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (c : α → ℝ≥0∞) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∫⁻ a, c a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ a, c a ^ q ∂μ) ^ (1 / q) := by
  have hq : 0 < q := hp.trans_le hpq
  obtain ⟨g, hgm, hgc, hint⟩ := exists_measurable_le_lintegral_eq μ (fun a => c a ^ p)
  set h : α → ℝ≥0∞ := fun a => g a ^ (1 / p) with hh
  have hhm : Measurable h := hgm.pow_const _
  have hhp : ∀ a, h a ^ p = g a := fun a => by
    rw [hh]; simp only; rw [← ENNReal.rpow_mul]
    rw [one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  have hhq : ∀ a, h a ^ q ≤ c a ^ q := fun a => by
    have : h a ≤ c a := by
      have := hgc a
      calc h a = g a ^ (1 / p) := rfl
        _ ≤ (c a ^ p) ^ (1 / p) := by gcongr
        _ = c a := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
    gcongr
  calc (∫⁻ a, c a ^ p ∂μ) ^ (1 / p) = (∫⁻ a, h a ^ p ∂μ) ^ (1 / p) := by
        rw [hint]; simp only [hhp]
    _ ≤ (∫⁻ a, h a ^ q ∂μ) ^ (1 / q) := lintegral_rpow_mono_meas μ hhm hp hpq
    _ ≤ _ := ENNReal.rpow_le_rpow (lintegral_mono fun a => hhq a) (by positivity)

open ProbabilityTheory in
theorem exists_glue {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {Q : Measure α} [IsProbabilityMeasure Q]
    {π₁ π₂ : Measure (α × α)} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : π₁.map Prod.snd = Q) (h₂ : π₂.map Prod.fst = Q) :
    ∃ ν : Measure ((α × α) × α), IsProbabilityMeasure ν ∧ ν.map Prod.fst = π₁ ∧
      ν.map (fun w => (w.1.2, w.2)) = π₂ := by
  let κ : Kernel α α := π₂.condKernel
  let κ' : Kernel (α × α) α := Kernel.comap κ Prod.snd measurable_snd
  refine ⟨π₁ ⊗ₘ κ', inferInstance, Measure.fst_compProd π₁ κ', ?_⟩
  ext s hs
  have hm : Measurable fun w : (α × α) × α => (w.1.2, w.2) := by fun_prop
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs)]
  have e : ∀ a : α × α, κ' a (Prod.mk a ⁻¹' ((fun w : (α × α) × α => (w.1.2, w.2)) ⁻¹' s)) =
      κ a.2 (Prod.mk a.2 ⁻¹' s) := fun a => rfl
  simp_rw [e]
  have hmeas : Measurable fun y : α => κ y (Prod.mk y ⁻¹' s) := Kernel.measurable_kernel_prodMk_left hs
  rw [← lintegral_map hmeas measurable_snd]
  change _ = _
  conv_rhs => rw [← Measure.disintegrate π₂ κ]
  rw [Measure.compProd_apply hs]
  have : π₂.fst = Q := h₂
  rw [this]
  rw [h₁]

/-- A coupling bounds `W_p` by its cost. -/
theorem wassersteinE_le_cost {p : ℝ} {P Q : Measure B} {π : Measure (B × B)}
    (hπ : IsCoupling π P Q) :
    wassersteinE p P Q ≤ (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) :=
  iInf_le (fun π : couplings P Q => (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p))
    ⟨π, hπ⟩

theorem IsCoupling.isProbabilityMeasure {P Q : Measure B} [IsProbabilityMeasure P]
    {π : Measure (B × B)} (hπ : IsCoupling π P Q) : IsProbabilityMeasure π := by
  refine ⟨?_⟩
  have := congrArg (fun μ : Measure B => μ Set.univ) hπ.1
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using this

theorem ofReal_norm_rpow {E : Type*} [NormedAddCommGroup E] {x : E} {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (‖x‖ ^ p) = ENNReal.ofReal ‖x‖ ^ p :=
  (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp).symm

theorem wassersteinE_mono_aux (p q : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q) (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    wassersteinE p P Q ≤ wassersteinE q P Q := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  refine le_iInf fun π => ?_
  have := π.2.isProbabilityMeasure
  refine (wassersteinE_le_cost (p := p) π.2).trans ?_
  simp only [ofReal_norm_rpow (p := p) hp0.le, ofReal_norm_rpow (p := q) hq0.le]
  exact lintegral_rpow_mono π.1 (fun z => ENNReal.ofReal ‖z.1 - z.2‖) hp0 hpq

/-! #### Helpers for the smooth distances (on the `C_b^k` unit ball) -/

theorem iteratedFDeriv_norm_le_of_mem {k : ℕ} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k) {j : ℕ}
    (hj : j ≤ k) (z : B) : ‖iteratedFDeriv ℝ j Φ z‖ ≤ 1 := by
  obtain ⟨_, hb, hn⟩ := hΦ
  have h1 : ‖iteratedFDeriv ℝ j Φ z‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ := le_ciSup (hb j hj) z
  have h2 : (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm k Φ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  linarith

theorem abs_apply_le_of_mem {k : ℕ} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k) (z : B) :
    |Φ z| ≤ 1 := by
  have := iteratedFDeriv_norm_le_of_mem hΦ (Nat.zero_le k) z
  simpa [norm_iteratedFDeriv_zero] using this

theorem zero_mem_cbUnitBall (k : ℕ) : (0 : B → ℝ) ∈ CbUnitBall B k := by
  refine ⟨contDiff_const, fun j _ => ?_, ?_⟩
  · exact ⟨0, by rintro _ ⟨z, rfl⟩; simp⟩
  · simp [cbNorm]

theorem cbUnitBall_mono {k : ℕ} : CbUnitBall B (k + 1) ⊆ CbUnitBall B k := by
  rintro Φ ⟨h1, h2, h3⟩
  refine ⟨h1.of_le (by exact_mod_cast Nat.le_succ k), fun j hj => h2 j (by omega), ?_⟩
  refine le_trans ?_ h3
  unfold cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.succ_le_succ (Nat.le_succ k)))
    (fun i _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

theorem abs_integral_sub_le_of_mem {k : ℕ} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k)
    (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    |∫ z, Φ z ∂P - ∫ z, Φ z ∂Q| ≤ (P Set.univ).toReal + (Q Set.univ).toReal := by
  have hb : ∀ z, ‖Φ z‖ ≤ 1 := fun z => by simpa using abs_apply_le_of_mem hΦ z
  have hP := norm_integral_le_of_norm_le_const (μ := P) (f := Φ) (C := 1) (ae_of_all _ hb)
  have hQ := norm_integral_le_of_norm_le_const (μ := Q) (f := Φ) (C := 1) (ae_of_all _ hb)
  simp only [Measure.real, one_mul] at hP hQ
  calc _ ≤ |∫ z, Φ z ∂P| + |∫ z, Φ z ∂Q| := abs_sub _ _
    _ ≤ _ := add_le_add hP hQ

theorem bddAbove_smoothDist (k : ℕ) (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    BddAbove (Set.range fun Φ : CbUnitBall B k => |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q|) :=
  ⟨_, by rintro _ ⟨Φ, rfl⟩; exact abs_integral_sub_le_of_mem Φ.2 P Q⟩

theorem abs_integral_sub_le_smoothDist {k : ℕ} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k)
    (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    |∫ z, Φ z ∂P - ∫ z, Φ z ∂Q| ≤ smoothDist k P Q :=
  le_ciSup (f := fun Φ : CbUnitBall B k => |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q|)
    (bddAbove_smoothDist k P Q) ⟨Φ, hΦ⟩

theorem smoothDist_nonneg (k : ℕ) (P Q : Measure B) : 0 ≤ smoothDist k P Q :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- Elements of the repaired `C_b^1` ball are `1`-Lipschitz. -/
theorem norm_sub_le_of_mem_one {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 1) (x y : B) :
    ‖Φ x - Φ y‖ ≤ ‖x - y‖ := by
  have hd : Differentiable ℝ Φ := hΦ.1.differentiable (by norm_num)
  have hb : ∀ z, ‖fderiv ℝ Φ z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact iteratedFDeriv_norm_le_of_mem hΦ le_rfl z
  have := (convex_univ (𝕜 := ℝ) (E := B)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) (fun z _ => hb z) (Set.mem_univ y) (Set.mem_univ x)
  simpa using this

theorem cbUnitBall_anti {j k : ℕ} (hjk : j ≤ k) : CbUnitBall B k ⊆ CbUnitBall B j := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (cbUnitBall_mono (B := B)).trans ih

theorem cbUnitBall_translate {k : ℕ} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k) (v : B) :
    (fun z => Φ (z + v)) ∈ CbUnitBall B k := by
  obtain ⟨h1, h2, h3⟩ := hΦ
  have e : ∀ j, (fun z : B => ‖iteratedFDeriv ℝ j (fun z => Φ (z + v)) z‖) =
      fun z => ‖iteratedFDeriv ℝ j Φ (z + v)‖ := fun j => by
    funext z; rw [iteratedFDeriv_comp_add_right]
  have e2 : ∀ j, (⨆ z : B, ‖iteratedFDeriv ℝ j (fun z => Φ (z + v)) z‖) =
      ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ := fun j => by
    rw [e j]
    exact (Equiv.addRight v).iSup_comp (g := fun z => ‖iteratedFDeriv ℝ j Φ z‖)
  refine ⟨h1.comp (contDiff_id.add contDiff_const), fun j hj => ?_, ?_⟩
  · rw [e j]
    obtain ⟨M, hM⟩ := h2 j hj
    exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM ⟨z + v, rfl⟩⟩
  · unfold cbNorm at h3 ⊢
    simpa only [e2] using h3

/-- Second-order Taylor bound for the repaired `C_b^k` ball, `k ≥ 2`. -/
theorem taylor_bound_of_mem {k : ℕ} (hk : 2 ≤ k) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k) (z h : B)
    {r : ℝ} (hr : 0 < r) :
    |Φ (z + r • h) - Φ z - r * fderiv ℝ Φ z h| ≤ (1 / 2) * r ^ 2 * ‖h‖ ^ 2 := by
  have hΦ2 : Φ ∈ CbUnitBall B 2 := cbUnitBall_anti hk hΦ
  have hd : Differentiable ℝ Φ := hΦ2.1.differentiable (by norm_num)
  have hd' : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ2.1.fderiv_right (m := 1) (by norm_num)
  -- Lipschitz bound of the derivative
  have hL : ∀ x y, ‖fderiv ℝ Φ x - fderiv ℝ Φ y‖ ≤ ‖x - y‖ := by
    intro x y
    have hb : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ 1 := fun w => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
      exact iteratedFDeriv_norm_le_of_mem hΦ2 le_rfl w
    have := (convex_univ (𝕜 := ℝ) (E := B)).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (hd'.differentiable one_ne_zero) w) (fun w _ => hb w) (Set.mem_univ y)
      (Set.mem_univ x)
    simpa using this
  set F : ℝ → ℝ := fun t => Φ (z + t • h) - Φ z - t * fderiv ℝ Φ z h with hF
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Φ (z + t • h)) (fderiv ℝ Φ (z + t • h) h) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => z + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add z
    exact (hd (z + t • h)).hasFDerivAt.comp_hasDerivAt t h1
  have hF' : ∀ t : ℝ, HasDerivAt F (fderiv ℝ Φ (z + t • h) h - fderiv ℝ Φ z h) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ => t * fderiv ℝ Φ z h) (fderiv ℝ Φ z h) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ Φ z h)
    exact ((hg t).sub_const (Φ z)).sub h2
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 / 2) * t ^ 2 * ‖h‖ ^ 2) (t * ‖h‖ ^ 2) t := by
    intro t
    have := (((hasDerivAt_pow 2 t).const_mul (1 / 2 : ℝ)).mul_const (‖h‖ ^ 2))
    convert this using 1
    simp
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := r)
    (f := F) (f' := fun t => fderiv ℝ Φ (z + t • h) h - fderiv ℝ Φ z h)
    (B := fun t => (1 / 2) * t ^ 2 * ‖h‖ ^ 2) (B' := fun t => t * ‖h‖ ^ 2)
    (fun t _ => (hF' t).continuousAt.continuousWithinAt)
    (fun t _ => (hF' t).hasDerivWithinAt) (by simp [hF]) hB ?_ (Set.right_mem_Icc.2 hr.le)
  · simpa [hF, Real.norm_eq_abs] using hbound
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    calc ‖fderiv ℝ Φ (z + t • h) h - fderiv ℝ Φ z h‖
        = ‖(fderiv ℝ Φ (z + t • h) - fderiv ℝ Φ z) h‖ := by simp
      _ ≤ ‖fderiv ℝ Φ (z + t • h) - fderiv ℝ Φ z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(z + t • h) - z‖ * ‖h‖ := by gcongr; exact hL _ _
      _ = t * ‖h‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]; ring

/-- `d_k` is bounded by total masses; in particular finite for probability measures. -/
theorem smoothDist_le (k : ℕ) (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    smoothDist k P Q ≤ (P Set.univ).toReal + (Q Set.univ).toReal :=
  Real.iSup_le (fun Φ => abs_integral_sub_le_of_mem Φ.2 P Q)
    (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- `d_{k+1} ≤ d_k`. -/
theorem smoothDist_succ_le (k : ℕ) (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    smoothDist (k + 1) P Q ≤ smoothDist k P Q :=
  Real.iSup_le (fun Φ => abs_integral_sub_le_smoothDist (cbUnitBall_mono Φ.2) P Q)
    (smoothDist_nonneg k P Q)

/-- `d_k` triangle inequality. -/
theorem smoothDist_triangle (k : ℕ) (P Q R : Measure B)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure R] :
    smoothDist k P R ≤ smoothDist k P Q + smoothDist k Q R := by
  refine Real.iSup_le (fun Φ => ?_) (add_nonneg (smoothDist_nonneg k P Q)
    (smoothDist_nonneg k Q R))
  have e : ∀ a b c : ℝ, a - c = (a - b) + (b - c) := fun a b c => by ring
  rw [e _ (∫ z, Φ.1 z ∂Q)]
  exact (abs_add_le _ _).trans (add_le_add (abs_integral_sub_le_smoothDist Φ.2 P Q)
        (abs_integral_sub_le_smoothDist Φ.2 Q R))

/-- `d_1 ≤ W_1` (Lipschitz tests are 1-Lipschitz). -/
theorem smoothDist_one_le_wasserstein (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal (smoothDist 1 P Q) ≤ wassersteinE 1 P Q := by
  refine le_iInf fun π => ?_
  have := π.2.isProbabilityMeasure
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  rcases eq_or_ne (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1) ⊤ with htop | hfin
  · rw [htop]; exact le_top
  have hmain : ∀ Φ : CbUnitBall B 1, ENNReal.ofReal |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q| ≤
      ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 := by
    intro Φ
    have hc : Continuous Φ.1 := Φ.2.1.continuous
    have hm1 : Measurable fun z : B × B => Φ.1 z.1 := hc.measurable.comp measurable_fst
    have hm2 : Measurable fun z : B × B => Φ.1 z.2 := hc.measurable.comp measurable_snd
    have hi : ∀ f : B × B → ℝ, Measurable f → (∀ z, |f z| ≤ 1) → Integrable f π.1 := fun f hf hb =>
      Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun z => by simpa using hb z)
    have hi1 := hi _ hm1 fun z => abs_apply_le_of_mem Φ.2 _
    have hi2 := hi _ hm2 fun z => abs_apply_le_of_mem Φ.2 _
    have e1 : ∫ z, Φ.1 z ∂P = ∫ z, Φ.1 z.1 ∂π.1 := by
      have := integral_map (μ := π.1) (φ := Prod.fst) (f := Φ.1) measurable_fst.aemeasurable
        (by rw [π.2.1]; exact hc.aestronglyMeasurable)
      rwa [π.2.1] at this
    have e2 : ∫ z, Φ.1 z ∂Q = ∫ z, Φ.1 z.2 ∂π.1 := by
      have := integral_map (μ := π.1) (φ := Prod.snd) (f := Φ.1) measurable_snd.aemeasurable
        (by rw [π.2.2]; exact hc.aestronglyMeasurable)
      rwa [π.2.2] at this
    rw [e1, e2, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
    calc ENNReal.ofReal ‖∫ z, (Φ.1 z.1 - Φ.1 z.2) ∂π.1‖
        ≤ ENNReal.ofReal (∫ z, ‖Φ.1 z.1 - Φ.1 z.2‖ ∂π.1) :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
      _ = ∫⁻ z, ‖Φ.1 z.1 - Φ.1 z.2‖ₑ ∂π.1 := ofReal_integral_norm_eq_lintegral_enorm (hi1.sub hi2)
      _ ≤ _ := by
          refine lintegral_mono fun z => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_sub_le_of_mem_one Φ.2 _ _)
  rw [ENNReal.ofReal_le_iff_le_toReal hfin]
  refine Real.iSup_le (fun Φ => ?_) ENNReal.toReal_nonneg
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hmain Φ)

/-- `W_1 ≤ W_2` for probability measures (Jensen). -/
theorem wassersteinE_one_le_two (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    wassersteinE 1 P Q ≤ wassersteinE 2 P Q :=
  wassersteinE_mono_aux 1 2 le_rfl (by norm_num) P Q

/-- Monotonicity in `p`. -/
theorem wassersteinE_mono (p q : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q) (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    wassersteinE p P Q ≤ wassersteinE q P Q :=
  wassersteinE_mono_aux p q hp hpq P Q

/-- Triangle inequality for `W_p` on a separable Banach space (gluing). -/
theorem wassersteinE_triangle (p : ℝ) (hp : 1 ≤ p) (P Q R : Measure B)
    [SecondCountableTopology B] [CompleteSpace B]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    wassersteinE p P R ≤ wassersteinE p P Q + wassersteinE p Q R := by
  have hp0 : 0 < p := by linarith
  have : Nonempty B := ⟨0⟩
  have key : ∀ π₁ ∈ couplings P Q, ∀ π₂ ∈ couplings Q R,
      wassersteinE p P R ≤ (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π₁) ^ (1 / p) +
        (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π₂) ^ (1 / p) := by
    intro π₁ h₁ π₂ h₂
    have := IsCoupling.isProbabilityMeasure h₁
    have := IsCoupling.isProbabilityMeasure h₂
    obtain ⟨ν, hν, hν1, hν2⟩ := exists_glue (Q := Q) h₁.2 h₂.1
    let g : (B × B) × B → B × B := fun w => (w.1.1, w.2)
    have hg : Measurable g := by fun_prop
    have hπ : IsCoupling (ν.map g) P R := by
      constructor
      · rw [Measure.map_map measurable_fst hg, ← h₁.1, ← hν1, Measure.map_map measurable_fst
          measurable_fst]
        rfl
      · rw [Measure.map_map measurable_snd hg, ← h₂.2, ← hν2, Measure.map_map measurable_snd
          (by fun_prop)]
        rfl
    refine (wassersteinE_le_cost hπ).trans ?_
    simp only [ofReal_norm_rpow (p := p) hp0.le]
    set u : (B × B) × B → ℝ≥0∞ := fun w => ENNReal.ofReal ‖w.1.1 - w.1.2‖ with hu
    set v : (B × B) × B → ℝ≥0∞ := fun w => ENNReal.ofReal ‖w.1.2 - w.2‖ with hv
    have hum : Measurable u := by rw [hu]; fun_prop
    have hvm : Measurable v := by rw [hv]; fun_prop
    have hcost1 : ∫⁻ w, u w ^ p ∂ν = ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ p ∂π₁ := by
      rw [← hν1, lintegral_map (by fun_prop) measurable_fst]
    have hcost2 : ∫⁻ w, v w ^ p ∂ν = ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ p ∂π₂ := by
      rw [← hν2, lintegral_map (by fun_prop) (by fun_prop)]
    calc (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ p ∂ν.map g) ^ (1 / p)
        ≤ (∫⁻ w, ENNReal.ofReal ‖(g w).1 - (g w).2‖ ^ p ∂ν) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (lintegral_map_le _ hg.aemeasurable) (by positivity)
      _ ≤ (∫⁻ w, (u + v) w ^ p ∂ν) ^ (1 / p) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono fun w => ?_) (by positivity)
          refine ENNReal.rpow_le_rpow ?_ hp0.le
          simp only [Pi.add_apply, hu, hv, g]
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ ≤ (∫⁻ w, u w ^ p ∂ν) ^ (1 / p) + (∫⁻ w, v w ^ p ∂ν) ^ (1 / p) :=
          ENNReal.lintegral_Lp_add_le hum.aemeasurable hvm.aemeasurable hp
      _ = _ := by rw [hcost1, hcost2]
  simp only [ofReal_norm_rpow (p := p) hp0.le] at key
  rw [← tsub_le_iff_right]
  refine le_iInf fun π₁ => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_iInf fun π₂ => ?_
  rw [tsub_le_iff_left]
  simpa [ofReal_norm_rpow (p := p) hp0.le] using key π₁.1 π₁.2 π₂.1 π₂.2

/-- A coupling realised by two random variables on one probability space bounds `W_p`. -/
theorem wassersteinE_le_of_coupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : 1 ≤ p)
    (X Y : Ω → B) (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    wassersteinE p (law P X) (law P Y) ≤
      (∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ p) ∂P) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hXe : X =ᵐ[P] hX.mk X := hX.ae_eq_mk
  have hYe : Y =ᵐ[P] hY.mk Y := hY.ae_eq_mk
  have hm : Measurable fun ω => (hX.mk X ω, hY.mk Y ω) :=
    hX.measurable_mk.prodMk hY.measurable_mk
  have hπ : IsCoupling (P.map fun ω => (hX.mk X ω, hY.mk Y ω)) (law P X) (law P Y) := by
    constructor
    · rw [Measure.map_map measurable_fst hm]
      exact (Measure.map_congr hXe).symm
    · rw [Measure.map_map measurable_snd hm]
      exact (Measure.map_congr hYe).symm
  refine (wassersteinE_le_cost hπ).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (‖hX.mk X ω - hY.mk Y ω‖ ^ p) ∂P :=
        lintegral_map_le (fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ p)) hm.aemeasurable
    _ = _ := lintegral_congr_ae (by
        filter_upwards [hXe, hYe] with ω h1 h2
        simp only [← h1, ← h2])

/-- `W_p` of a translate: `W_p(Law(X + a), Law(X + b)) ≤ ‖a - b‖`. -/
theorem wassersteinE_translate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : 1 ≤ p) (X : Ω → B) (hX : AEMeasurable X P)
    (a b : B) :
    wassersteinE p (law P (fun ω => X ω + a)) (law P (fun ω => X ω + b)) ≤
      ENNReal.ofReal ‖a - b‖ := by
  have hp0 : 0 < p := by linarith
  refine (wassersteinE_le_of_coupling P p hp (fun ω => X ω + a) (fun ω => X ω + b)
    (hX.add_const a) (hX.add_const b)).trans ?_
  have : ∀ ω, ENNReal.ofReal (‖(X ω + a) - (X ω + b)‖ ^ p) = ENNReal.ofReal (‖a - b‖ ^ p) := by
    intro ω; congr 3; abel_nf
  simp only [this, lintegral_const, measure_univ, mul_one]
  rw [ofReal_norm_rpow (p := p) hp0.le, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne',
    ENNReal.rpow_one]

end MetricFacts

/-! ### Lemma 4.27: uniform first variation under deterministic translation
`M:R:lem:smooth-translation` (source lines 5660-5682). -/

section SmoothTranslation

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem integrable_comp_of_continuous {f : B → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ z, |f z| ≤ C) {Y : Ω → B} (hY : AEMeasurable Y P) :
    Integrable (fun ω => f (Y ω)) P :=
  Integrable.of_bound (hf.aestronglyMeasurable.comp_aemeasurable hY) C
    (ae_of_all _ fun ω => by simpa using hC _)

theorem abs_fderiv_apply_le {k : ℕ} (hk : 1 ≤ k) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k) (z h : B) :
    |fderiv ℝ Φ z h| ≤ ‖h‖ := by
  have hΦ1 : Φ ∈ CbUnitBall B 1 := cbUnitBall_anti hk hΦ
  have : ‖fderiv ℝ Φ z‖ ≤ 1 := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact iteratedFDeriv_norm_le_of_mem hΦ1 le_rfl z
  calc |fderiv ℝ Φ z h| = ‖fderiv ℝ Φ z h‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ Φ z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖h‖ := by gcongr
    _ = ‖h‖ := one_mul _

theorem cbUnitBall_neg {k : ℕ} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k) :
    (fun z => -Φ z) ∈ CbUnitBall B k := by
  obtain ⟨h1, h2, h3⟩ := hΦ
  have e : ∀ j, (fun z : B => ‖iteratedFDeriv ℝ j (fun z => -Φ z) z‖) =
      fun z => ‖iteratedFDeriv ℝ j Φ z‖ := fun j => by
    funext z; change ‖iteratedFDeriv ℝ j (-Φ) z‖ = _; rw [iteratedFDeriv_neg_apply, norm_neg]
  refine ⟨h1.neg, fun j hj => ?_, ?_⟩
  · rw [e j]; exact h2 j hj
  · unfold cbNorm at h3 ⊢
    simpa only [show ∀ j, (⨆ z : B, ‖iteratedFDeriv ℝ j (fun z => -Φ z) z‖) =
      ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ from fun j => by rw [e j]] using h3

theorem abs_integral_fderiv_le {k : ℕ} (hk : 1 ≤ k) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B k)
    (G : Ω → B) (h : B) : |∫ ω, fderiv ℝ Φ (G ω) h ∂P| ≤ ‖h‖ := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => fderiv ℝ Φ (G ω) h)
    (C := ‖h‖) (ae_of_all _ fun ω => by simpa using abs_fderiv_apply_le hk hΦ (G ω) h)
  simpa [Measure.real] using this

theorem bddAbove_smoothConstant {k : ℕ} (hk : 1 ≤ k) (G : Ω → B) (h : B) :
    BddAbove (Set.range fun Φ : CbUnitBall B k => ∫ ω, fderiv ℝ Φ.1 (G ω) h ∂P) :=
  ⟨‖h‖, by rintro _ ⟨Φ, rfl⟩; exact (le_abs_self _).trans (abs_integral_fderiv_le P hk Φ.2 G h)⟩

theorem integral_fderiv_le_smoothConstant {k : ℕ} (hk : 1 ≤ k) {Φ : B → ℝ}
    (hΦ : Φ ∈ CbUnitBall B k) (G : Ω → B) (h : B) :
    ∫ ω, fderiv ℝ Φ (G ω) h ∂P ≤ smoothConstant P k G h :=
  le_ciSup (f := fun Φ : CbUnitBall B k => ∫ ω, fderiv ℝ Φ.1 (G ω) h ∂P)
    (bddAbove_smoothConstant P hk G h) ⟨Φ, hΦ⟩

theorem smoothConstant_nonneg {k : ℕ} (hk : 1 ≤ k) (G : Ω → B) (h : B) :
    0 ≤ smoothConstant P k G h := by
  have := integral_fderiv_le_smoothConstant P hk (zero_mem_cbUnitBall k) G h
  simpa using this

theorem abs_integral_fderiv_le_smoothConstant {k : ℕ} (hk : 1 ≤ k) {Φ : B → ℝ}
    (hΦ : Φ ∈ CbUnitBall B k) (G : Ω → B) (h : B) :
    |∫ ω, fderiv ℝ Φ (G ω) h ∂P| ≤ smoothConstant P k G h := by
  refine abs_le.2 ⟨?_, integral_fderiv_le_smoothConstant P hk hΦ G h⟩
  have := integral_fderiv_le_smoothConstant P hk (cbUnitBall_neg hΦ) G h
  have e : ∀ ω, fderiv ℝ (fun z => -Φ z) (G ω) h = -fderiv ℝ Φ (G ω) h := fun ω => by
    change fderiv ℝ (-Φ) (G ω) h = _; rw [fderiv_neg]; rfl
  simp only [e, integral_neg] at this
  linarith

/-- Lemma 4.27, display `R:eq:abstract-smooth-expansion` (source lines 5665-5671):
for `k ≥ 2`, `r > 0`, uniformly over the `C_b^k(B)` unit ball,
`|E[Φ(X+a)] - E[Φ(G)] - r E[DΦ(G)[h]]| ≤ d_k(Law X, Law G) + ‖a - rh‖ + ½ r² ‖h‖²`.
No coupling or moment assumption. -/
theorem smooth_translation_expansion (X G : Ω → B) (hX : AEMeasurable X P) (hG : AEMeasurable G P)
    (a h : B) (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 2 ≤ k) (Φ : B → ℝ) (hΦ : Φ ∈ CbUnitBall B k) :
    |∫ ω, Φ (X ω + a) ∂P - ∫ ω, Φ (G ω) ∂P - r * ∫ ω, fderiv ℝ Φ (G ω) h ∂P| ≤
      smoothDist k (law P X) (law P G) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 := by
  have hc : Continuous Φ := hΦ.1.continuous
  have hΦ1 : Φ ∈ CbUnitBall B 1 := cbUnitBall_anti (by omega) hΦ
  have hb : ∀ z, |Φ z| ≤ 1 := abs_apply_le_of_mem hΦ
  have hDc : Continuous fun z => fderiv ℝ Φ z h :=
    (hΦ.1.continuous_fderiv (by norm_cast; omega)).clm_apply continuous_const
  have hDb : ∀ z, |fderiv ℝ Φ z h| ≤ ‖h‖ := fun z => abs_fderiv_apply_le (by omega) hΦ z h
  have hΨ := cbUnitBall_translate hΦ (r • h)
  have hcΨ : Continuous fun z => Φ (z + r • h) := hc.comp (continuous_id.add continuous_const)
  have i1 := integrable_comp_of_continuous P hc hb (hX.add_const a)
  have i2 := integrable_comp_of_continuous P hc hb (hX.add_const (r • h))
  have i3 := integrable_comp_of_continuous P hc hb hG
  have i4 := integrable_comp_of_continuous P hc hb (hG.add_const (r • h))
  have i5 := integrable_comp_of_continuous P hDc hDb hG
  -- the three-term decomposition
  have hsplit : ∫ ω, Φ (X ω + a) ∂P - ∫ ω, Φ (G ω) ∂P - r * ∫ ω, fderiv ℝ Φ (G ω) h ∂P =
      (∫ ω, (Φ (X ω + a) - Φ (X ω + r • h)) ∂P) +
      ((∫ ω, Φ (X ω + r • h) ∂P) - ∫ ω, Φ (G ω + r • h) ∂P) +
      ∫ ω, (Φ (G ω + r • h) - Φ (G ω) - r * fderiv ℝ Φ (G ω) h) ∂P := by
    have e3 : ∫ ω, (Φ (G ω + r • h) - Φ (G ω) - r * fderiv ℝ Φ (G ω) h) ∂P =
        ∫ ω, Φ (G ω + r • h) ∂P - ∫ ω, Φ (G ω) ∂P - r * ∫ ω, fderiv ℝ Φ (G ω) h ∂P := by
      have i43 : Integrable (fun ω => Φ (G ω + r • h) - Φ (G ω)) P := i4.sub i3
      rw [integral_sub i43 (i5.const_mul r), integral_sub i4 i3, integral_const_mul]
    rw [integral_sub i1 i2, e3]
    ring
  have hA : |∫ ω, (Φ (X ω + a) - Φ (X ω + r • h)) ∂P| ≤ ‖a - r • h‖ := by
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => Φ (X ω + a) - Φ (X ω + r • h)) (C := ‖a - r • h‖)
      (ae_of_all _ fun ω => by
        simpa using norm_sub_le_of_mem_one (cbUnitBall_anti (by omega) hΦ) (X ω + a)
          (X ω + r • h))
    simpa [Measure.real] using this
  have hBB : |(∫ ω, Φ (X ω + r • h) ∂P) - ∫ ω, Φ (G ω + r • h) ∂P| ≤
      smoothDist k (law P X) (law P G) := by
    have e1 : ∫ ω, Φ (X ω + r • h) ∂P = ∫ z, Φ (z + r • h) ∂(law P X) :=
      (integral_map hX hcΨ.aestronglyMeasurable).symm
    have e2 : ∫ ω, Φ (G ω + r • h) ∂P = ∫ z, Φ (z + r • h) ∂(law P G) :=
      (integral_map hG hcΨ.aestronglyMeasurable).symm
    rw [e1, e2]
    exact abs_integral_sub_le_smoothDist (Φ := fun z => Φ (z + r • h)) hΨ _ _
  have hC : |∫ ω, (Φ (G ω + r • h) - Φ (G ω) - r * fderiv ℝ Φ (G ω) h) ∂P| ≤
      (1 / 2) * r ^ 2 * ‖h‖ ^ 2 := by
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => Φ (G ω + r • h) - Φ (G ω) - r * fderiv ℝ Φ (G ω) h)
      (C := (1 / 2) * r ^ 2 * ‖h‖ ^ 2)
      (ae_of_all _ fun ω => by
        simpa [Real.norm_eq_abs] using taylor_bound_of_mem hk hΦ (G ω) h hr)
    simpa [Measure.real] using this
  rw [hsplit]
  generalize (∫ ω, (Φ (X ω + a) - Φ (X ω + r • h)) ∂P) = A at hA ⊢
  generalize ((∫ ω, Φ (X ω + r • h) ∂P) - ∫ ω, Φ (G ω + r • h) ∂P) = Bt at hBB ⊢
  generalize (∫ ω, (Φ (G ω + r • h) - Φ (G ω) - r * fderiv ℝ Φ (G ω) h) ∂P) = C at hC ⊢
  have h1 := abs_add_le (A + Bt) C
  have h2 := abs_add_le A Bt
  linarith

/-- Lemma 4.27, display `R:eq:abstract-smooth-distance` (source lines 5672-5676):
`|d_k(Law(X+a), Law G) - r 𝔠_k^B(G,h)|` has the same bound. -/
theorem smooth_translation_distance (X G : Ω → B) (hX : AEMeasurable X P) (hG : AEMeasurable G P)
    (a h : B) (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 2 ≤ k) :
    |smoothDist k (law P (fun ω => X ω + a)) (law P G) - r * smoothConstant P k G h| ≤
      smoothDist k (law P X) (law P G) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 := by
  set T := smoothDist k (law P X) (law P G) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 with hT
  have hT0 : 0 ≤ T := by
    have := smoothDist_nonneg k (law P X) (law P G)
    positivity
  have hk1 : 1 ≤ k := by omega
  set D := smoothDist k (law P (fun ω => X ω + a)) (law P G) with hD
  set c := smoothConstant P k G h with hc
  have hc0 : 0 ≤ c := smoothConstant_nonneg P hk1 G h
  have hXa : AEMeasurable (fun ω => X ω + a) P := hX.add_const a
  have hv : ∀ Φ ∈ CbUnitBall B k,
      ∫ z, Φ z ∂(law P (fun ω => X ω + a)) - ∫ z, Φ z ∂(law P G) =
        ∫ ω, Φ (X ω + a) ∂P - ∫ ω, Φ (G ω) ∂P := fun Φ hΦ => by
    rw [integral_map hXa hΦ.1.continuous.aestronglyMeasurable,
      integral_map hG hΦ.1.continuous.aestronglyMeasurable]
  have hexp := fun Φ (hΦ : Φ ∈ CbUnitBall B k) =>
    smooth_translation_expansion P X G hX hG a h r hr k hk Φ hΦ
  -- upper bound for `D`
  have h1 : D ≤ r * c + T := by
    refine Real.iSup_le (fun Φ => ?_) (by positivity)
    have e := hexp Φ.1 Φ.2
    have e2 := abs_integral_fderiv_le_smoothConstant P hk1 Φ.2 G h
    rw [hv Φ.1 Φ.2]
    have : |∫ ω, Φ.1 (X ω + a) ∂P - ∫ ω, Φ.1 (G ω) ∂P| ≤
        r * |∫ ω, fderiv ℝ Φ.1 (G ω) h ∂P| + T := by
      have := abs_sub_abs_le_abs_sub (∫ ω, Φ.1 (X ω + a) ∂P - ∫ ω, Φ.1 (G ω) ∂P)
        (r * ∫ ω, fderiv ℝ Φ.1 (G ω) h ∂P)
      rw [abs_mul, abs_of_pos hr] at this
      linarith
    nlinarith
  -- lower bound for `r * c`
  have h2 : r * c ≤ D + T := by
    have : c ≤ (D + T) / r := by
      refine Real.iSup_le (fun Φ => ?_) (div_nonneg (add_nonneg (smoothDist_nonneg _ _ _) hT0)
        hr.le)
      rw [le_div_iff₀ hr]
      have e := hexp Φ.1 Φ.2
      have e3 := abs_integral_sub_le_smoothDist Φ.2 (law P (fun ω => X ω + a)) (law P G)
      rw [hv Φ.1 Φ.2] at e3
      have := (abs_le.1 e).1
      have := (abs_le.1 e3).2
      nlinarith [this]
    rwa [le_div_iff₀ hr, mul_comm] at this
  rw [abs_le]
  constructor <;> linarith

/-- The test function `z ↦ sin (L z) / (k+1)` lies in the `C_b^k` unit ball when `‖L‖ ≤ 1`. -/
theorem sin_dual_mem (L : StrongDual ℝ B) (hL : ‖L‖ ≤ 1) (k : ℕ) :
    (fun z => (1 / ((k : ℝ) + 1)) * Real.sin (L z)) ∈ CbUnitBall B k := by
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hcd : ContDiff ℝ k (Real.sin ∘ L) := Real.contDiff_sin.comp L.contDiff
  have hb : ∀ j ≤ k, ∀ z, ‖iteratedFDeriv ℝ j (fun z => ε * Real.sin (L z)) z‖ ≤ ε := by
    intro j hj z
    have e : (fun z => ε * Real.sin (L z)) = ε • (Real.sin ∘ L) := by
      funext z; simp
    rw [e, iteratedFDeriv_const_smul_apply (hcd.of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
    have h2 := L.iteratedFDeriv_comp_right (Real.contDiff_sin (n := j)) z (i := j) le_rfl
    have h3 : ‖iteratedFDeriv ℝ j Real.sin (L z)‖ ≤ 1 := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_sin_le_one j (L z)
    calc ε * ‖iteratedFDeriv ℝ j (Real.sin ∘ L) z‖
        ≤ ε * 1 := by
          gcongr
          rw [h2]
          refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
          have : ∏ _i : Fin j, ‖L‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)
          calc _ ≤ ‖iteratedFDeriv ℝ j Real.sin (L z)‖ * 1 := by gcongr
            _ ≤ 1 := by linarith
      _ = ε := mul_one _
  refine ⟨contDiff_const.mul (Real.contDiff_sin.comp L.contDiff), fun j hj => ⟨ε, ?_⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩; exact hb j hj z
  · unfold cbNorm
    calc ∑ j ∈ Finset.range (k + 1), ⨆ z : B, ‖iteratedFDeriv ℝ j (fun z => ε * Real.sin (L z)) z‖
        ≤ ∑ j ∈ Finset.range (k + 1), ε := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact Real.iSup_le (hb j (by simpa [Nat.lt_succ_iff] using hj)) hε0.le
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hε]
          push_cast; field_simp

/-- Lemma 4.27, display `R:eq:positive-smooth-constant` (source lines 5678-5681):
if `G` is centered Gaussian (possibly degenerate), `0 < 𝔠_k^B(G,h) ≤ ‖h‖` for `h ≠ 0`
and `𝔠_k^B(G,0) = 0`. -/
theorem smoothConstant_pos_of_gaussian (G : Ω → B) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (k : ℕ) (hk : 2 ≤ k) (h : B) (hh : h ≠ 0) :
    0 < smoothConstant P k G h ∧ smoothConstant P k G h ≤ ‖h‖ := by
  refine ⟨?_, ?_⟩
  swap
  · have : Nonempty (CbUnitBall B k) := ⟨⟨0, zero_mem_cbUnitBall k⟩⟩
    exact Real.iSup_le (fun Φ => (le_abs_self _).trans (abs_integral_fderiv_le P (by omega) Φ.2 G h))
      (norm_nonneg _)
  obtain ⟨L, hL1, hLh⟩ := exists_dual_vector'' ℝ h
  have := hGauss.1
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hmem := sin_dual_mem L hL1 k
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  -- derivative of the test function
  have hderiv : ∀ z, fderiv ℝ (fun z => ε * Real.sin (L z)) z h = ε * ‖h‖ * Real.cos (L z) := by
    intro z
    have h1 : HasFDerivAt (fun z => Real.sin (L z)) (Real.cos (L z) • L) z :=
      ((Real.hasDerivAt_sin (L z)).hasFDerivAt.comp z L.hasFDerivAt).congr_fderiv (by ext; simp; ring)
    have h2 := (h1.const_mul ε).fderiv
    rw [h2]
    simp [hLh]; ring
  -- the integral
  have hint : ∫ ω, fderiv ℝ (fun z => ε * Real.sin (L z)) (G ω) h ∂P =
      ε * ‖h‖ * Real.exp (-(ProbabilityTheory.variance L (law P G)) / 2) := by
    simp only [hderiv]
    rw [integral_const_mul]
    congr 1
    have hc := ProbabilityTheory.IsGaussian.charFunDual_eq_of_forall_strongDual_eq_zero (μ := law P G) hGauss.2 L
    have hcos : ∫ ω, Real.cos (L (G ω)) ∂P = ∫ v, Real.cos (L v) ∂(law P G) :=
      (integral_map hG (Real.continuous_cos.comp L.continuous).aestronglyMeasurable).symm
    rw [hcos]
    have := congrArg Complex.re hc
    rw [charFunDual_apply] at this
    have hI : Integrable (fun v => Complex.exp (↑(L v) * Complex.I)) (law P G) := by
      refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun v => by simp)
      exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp L.continuous).mul
        continuous_const)).aestronglyMeasurable
    have e1 : ∫ v, Real.cos (L v) ∂law P G =
        (∫ v, Complex.exp (↑(L v) * Complex.I) ∂law P G).re := by
      have := integral_re hI
      simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at this
      exact this
    set v : ℝ := ProbabilityTheory.variance L (law P G) with hv
    have e2 : (-(v : ℂ) / 2) = ((-v / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, this, e2, Complex.exp_ofReal_re]
  have hle := integral_fderiv_le_smoothConstant P (by omega : 1 ≤ k) hmem G h
  rw [hint] at hle
  exact lt_of_lt_of_le (by positivity) hle

theorem smoothConstant_zero (G : Ω → B) (k : ℕ) :
    smoothConstant P k G 0 = 0 := by
  have : Nonempty (CbUnitBall B k) := ⟨⟨0, zero_mem_cbUnitBall k⟩⟩
  unfold smoothConstant
  simp

end SmoothTranslation

/-! ### Finite-dimensional lemmas: A.26, A.31, A.37 -/

section FiniteDim

variable {p : ℕ}

/-- Finite-dimensional Euclidean space `ℝ^p`. -/
local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-! #### Kantorovich-Rubinstein upper bound for `W_1` (finite transport duality, discretisation) -/

section KantorovichUpper

set_option linter.unusedSectionVars false
open scoped Pointwise


section KR
variable {E : Type*} [NormedAddCommGroup E]

/-- The Lipschitz test function built from dual potentials. -/
lemma lipschitz_inf_cone {N : ℕ} [NeZero N] (z : Fin N → E) (G : Fin N → ℝ) :
    LipschitzWith 1 (fun x : E => Finset.univ.inf' Finset.univ_nonempty (fun l => ‖x - z l‖ - G l)) := by
  refine LipschitzWith.of_le_add fun x y => ?_
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun l => ‖y - z l‖ - G l)
  rw [hl]
  refine (Finset.inf'_le _ (Finset.mem_univ l)).trans ?_
  have : ‖x - z l‖ ≤ ‖y - z l‖ + dist x y := by
    rw [dist_eq_norm]
    calc ‖x - z l‖ = ‖(y - z l) + (x - y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith


/-- A continuous linear functional on `ι → ℝ` with `ι = Fin N ⊕ Fin N ⊕ Unit` is determined by
coefficients. -/
lemma functional_decomp {N : ℕ} (φ : ((Fin N ⊕ Fin N ⊕ Unit) → ℝ) →L[ℝ] ℝ) (v : (Fin N ⊕ Fin N ⊕ Unit) → ℝ) :
    φ v = ∑ k, v (Sum.inl k) * φ (Pi.single (Sum.inl k) 1) +
      ∑ l, v (Sum.inr (Sum.inl l)) * φ (Pi.single (Sum.inr (Sum.inl l)) 1) +
      v (Sum.inr (Sum.inr ())) * φ (Pi.single (Sum.inr (Sum.inr ())) 1) := by
  have := φ.toLinearMap.pi_apply_eq_sum_univ v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hs : ∀ x : Fin N ⊕ Fin N ⊕ Unit, (fun j => if x = j then (1:ℝ) else 0) = Pi.single x 1 := by
    intro x; ext j; simp [Pi.single_apply, eq_comm]
  simp only [hs]
  rw [add_assoc]


/-- Probability vectors on pairs. -/
def pairSimplex (N : ℕ) : Set (Fin N × Fin N → ℝ) := {π | (∀ q, 0 ≤ π q) ∧ ∑ q, π q = 1}

lemma pairSimplex_convex (N : ℕ) : Convex ℝ (pairSimplex N) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun q => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 q)) (mul_nonneg hb (hy.1 q))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2, hy.2]
    linarith

lemma pairSimplex_compact (N : ℕ) : IsCompact (pairSimplex N) := by
  refine (isCompact_Icc (a := (0 : Fin N × Fin N → ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {π : Fin N × Fin N → ℝ | ∀ q, 0 ≤ π q} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun q => isClosed_le (f := fun _ : Fin N × Fin N → ℝ => (0 : ℝ))
        (g := fun π => π q) continuous_const (continuous_apply q)
    have h2 : IsClosed {π : Fin N × Fin N → ℝ | ∑ q, π q = 1} :=
      isClosed_eq (continuous_finset_sum _ fun q _ => continuous_apply q) continuous_const
    exact h1.inter h2
  · rintro π ⟨h0, h1⟩ 
    refine ⟨fun q => h0 q, fun q => ?_⟩
    show π q ≤ 1
    rw [← h1]
    exact Finset.single_le_sum (f := fun q => π q) (fun q _ => h0 q) (Finset.mem_univ q)

lemma single_rowsum {N : ℕ} (k l k' : Fin N) : ∑ l', (Pi.single (k, l) (1:ℝ) : Fin N × Fin N → ℝ) (k', l') = if k' = k then 1 else 0 := by
  by_cases h : k' = k
  · subst h
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ hl'; simp [Pi.single_apply, hl']
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun l' _ => by simp [Pi.single_apply, h]
lemma single_colsum {N : ℕ} (k l l' : Fin N) : ∑ k', (Pi.single (k, l) (1:ℝ) : Fin N × Fin N → ℝ) (k', l') = if l' = l then 1 else 0 := by
  by_cases h : l' = l
  · subst h
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'; simp [Pi.single_apply, hk']
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun k' _ => by simp [Pi.single_apply, h]
lemma single_cost {N : ℕ} (z : Fin N → E) (k l : Fin N) : ∑ q, (Pi.single (k, l) (1:ℝ) : Fin N × Fin N → ℝ) q * ‖z q.1 - z q.2‖ = ‖z k - z l‖ := by
  rw [Finset.sum_eq_single (k, l)]
  · simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp

lemma single_mem {N : ℕ} (k l : Fin N) : (Pi.single (k, l) (1 : ℝ) : Fin N × Fin N → ℝ) ∈ pairSimplex N := by
  refine ⟨fun q => ?_, ?_⟩
  · by_cases h : q = (k, l) <;> simp [Pi.single_apply, h]
  · simp

lemma finite_transport {N : ℕ} [NeZero N] (z : Fin N → E) (a b : Fin N → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hsa : ∑ k, a k = 1) (hsb : ∑ k, b k = 1)
    (S : ℝ) (hS : ∀ h : E → ℝ, LipschitzWith 1 h → ∑ k, h (z k) * (a k - b k) ≤ S)
    (η : ℝ) (hη : 0 < η) :
    ∃ π ∈ pairSimplex N, (∀ k, ∑ l, π (k, l) = a k) ∧
      (∀ l, ∑ k, π (k, l) = b l) ∧ ∑ q, π q * ‖z q.1 - z q.2‖ ≤ S + η := by
  by_contra hno
  push Not at hno
  let Ψl : (Fin N × Fin N → ℝ) →ₗ[ℝ] ((Fin N ⊕ Fin N ⊕ Unit) → ℝ) :=
    { toFun := fun π => Sum.elim (fun k => ∑ l, π (k, l)) (Sum.elim (fun l => ∑ k, π (k, l))
        (fun _ => ∑ q, π q * ‖z q.1 - z q.2‖))
      map_add' := by
        intro x y; ext i; rcases i with k | l | u <;> simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c x; ext i; rcases i with k | l | u <;> simp [Finset.mul_sum, mul_assoc] }
  have hΨc : Continuous Ψl := LinearMap.continuous_of_finiteDimensional Ψl
  let R : Set ((Fin N ⊕ Fin N ⊕ Unit) → ℝ) := {v | (∀ k, v (Sum.inl k) = 0) ∧
    (∀ l, v (Sum.inr (Sum.inl l)) = 0) ∧ 0 ≤ v (Sum.inr (Sum.inr ()))}
  have hRc : IsClosed R := by
    have : R = (⋂ k, {v : (Fin N ⊕ Fin N ⊕ Unit) → ℝ | v (Sum.inl k) = 0}) ∩
        ((⋂ l, {v : (Fin N ⊕ Fin N ⊕ Unit) → ℝ | v (Sum.inr (Sum.inl l)) = 0}) ∩
          {v | 0 ≤ v (Sum.inr (Sum.inr ()))}) := by
      ext v; simp [R]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun k => ?_) (IsClosed.inter (isClosed_iInter fun l => ?_) ?_)
    · exact isClosed_eq (continuous_apply _) continuous_const
    · exact isClosed_eq (continuous_apply _) continuous_const
    · exact isClosed_le continuous_const (continuous_apply _)
  have hRv : Convex ℝ R := by
    intro x hx y hy c d hc hd hcd
    refine ⟨fun k => ?_, fun l => ?_, ?_⟩
    · simp [hx.1 k, hy.1 k]
    · simp [hx.2.1 l, hy.2.1 l]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hc hx.2.2) (mul_nonneg hd hy.2.2)
  let K := Ψl '' pairSimplex N + R
  have hKc : IsClosed K := hRc.add_left_of_isCompact ((pairSimplex_compact N).image hΨc)
  have hKv : Convex ℝ K := ((pairSimplex_convex N).linear_image Ψl).add hRv
  let P : (Fin N ⊕ Fin N ⊕ Unit) → ℝ := Sum.elim a (Sum.elim b (fun _ => S + η))
  have hP : P ∉ K := by
    rintro ⟨_, ⟨π, hπ, rfl⟩, r, hr, hPe⟩
    have e1 : ∀ k, ∑ l, π (k, l) = a k := fun k => by
      have := congrFun hPe (Sum.inl k); simpa [P, Ψl, hr.1 k] using this
    have e2 : ∀ l, ∑ k, π (k, l) = b l := fun l => by
      have := congrFun hPe (Sum.inr (Sum.inl l)); simpa [P, Ψl, hr.2.1 l] using this
    have e3 := congrFun hPe (Sum.inr (Sum.inr ()))
    simp only [P, Ψl, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Sum.elim_inr] at e3
    have := hno π hπ e1 e2
    have := hr.2.2
    linarith
  obtain ⟨φ, u, hφP, hφK⟩ := geometric_hahn_banach_point_closed hKv hKc hP
  set f : Fin N → ℝ := fun k => φ (Pi.single (Sum.inl k) 1) with hf
  set g : Fin N → ℝ := fun l => φ (Pi.single (Sum.inr (Sum.inl l)) 1) with hg
  set lam : ℝ := φ (Pi.single (Sum.inr (Sum.inr ())) 1) with hlam
  have hdec : ∀ v, φ v = ∑ k, v (Sum.inl k) * f k + ∑ l, v (Sum.inr (Sum.inl l)) * g l +
      v (Sum.inr (Sum.inr ())) * lam := fun v => functional_decomp φ v
  -- values on `Ψ π + s e`
  have hval : ∀ π ∈ pairSimplex N, ∀ s : ℝ, 0 ≤ s → u < (∑ k, (∑ l, π (k, l)) * f k +
      ∑ l, (∑ k, π (k, l)) * g l + (∑ q, π q * ‖z q.1 - z q.2‖ + s) * lam) := by
    intro π hπ s hs
    have hm : Ψl π + (Pi.single (Sum.inr (Sum.inr ())) s : (Fin N ⊕ Fin N ⊕ Unit) → ℝ) ∈ K := by
      refine ⟨Ψl π, ⟨π, hπ, rfl⟩, Pi.single (Sum.inr (Sum.inr ())) s, ⟨?_, ?_, ?_⟩, rfl⟩
      · intro k; simp
      · intro l; simp
      · simpa using hs
    have := hφK _ hm
    rw [hdec] at this
    simpa [Ψl, Pi.single_apply] using this
  have hsingle : ∀ k l (s : ℝ), 0 ≤ s → u < f k + g l + (‖z k - z l‖ + s) * lam := by
    intro k l s hs
    have := hval _ (single_mem k l) s hs
    simp only [single_rowsum, single_colsum, single_cost, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hlam0 : 0 ≤ lam := by
    by_contra hneg
    push Not at hneg
    obtain k0 : Fin N := ⟨0, Nat.pos_of_neZero N⟩
    set X := f k0 + g k0 + ‖z k0 - z k0‖ * lam with hX
    have hs : 0 ≤ (|X - u| + 1) / (-lam) := div_nonneg (by positivity) (by linarith)
    have h1 := hsingle k0 k0 _ hs
    have e2 : (|X - u| + 1) / (-lam) * lam = -(|X - u| + 1) := by
      have : lam ≠ 0 := hneg.ne
      field_simp
    have h2 := le_abs_self (X - u)
    rw [add_mul, e2] at h1
    linarith
  have hφP' : ∑ k, a k * f k + ∑ l, b l * g l + (S + η) * lam < u := by
    have := hφP
    rw [hdec] at this
    simpa [P] using this
  have hlam : 0 < lam := by
    rcases hlam0.eq_or_lt with h0 | h0
    · exfalso
      have hπ : (fun q : Fin N × Fin N => a q.1 * b q.2) ∈ pairSimplex N := by
        refine ⟨fun q => mul_nonneg (ha _) (hb _), ?_⟩
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, hsb, mul_one, hsa]
      have := hval _ hπ 0 le_rfl
      have r1 : ∀ k, ∑ l, a k * b l = a k := fun k => by rw [← Finset.mul_sum, hsb, mul_one]
      have r2 : ∀ l, ∑ k, a k * b l = b l := fun l => by rw [← Finset.sum_mul, hsa, one_mul]
      simp only [r1, r2, ← h0, mul_zero, add_zero] at this hφP'
      linarith
    · exact h0
  set F : Fin N → ℝ := fun k => -f k / lam with hF
  set G : Fin N → ℝ := fun l => -g l / lam with hG
  have hf' : ∀ k, f k = -lam * F k := fun k => by simp only [hF]; field_simp
  have hg' : ∀ l, g l = -lam * G l := fun l => by simp only [hG]; field_simp
  set D : ℝ := ∑ k, F k * a k + ∑ l, G l * b l with hD
  have hsa_f : ∑ k, a k * f k = -lam * ∑ k, F k * a k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [hf' k]; ring
  have hsb_g : ∑ l, b l * g l = -lam * ∑ l, G l * b l := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [hg' l]; ring
  have hFG : ∀ k l, F k + G l + (S + η) - D < ‖z k - z l‖ := by
    intro k l
    have h1 := hsingle k l 0 le_rfl
    rw [add_zero, hf' k, hg' l] at h1
    have key : lam * (F k + G l + (S + η) - D) < lam * ‖z k - z l‖ := by
      have e : lam * D = -(∑ k, a k * f k) - ∑ l, b l * g l := by
        rw [hsa_f, hsb_g, hD]; ring
      nlinarith
    exact lt_of_mul_lt_mul_left key hlam.le
  let h : E → ℝ := fun x => Finset.univ.inf' Finset.univ_nonempty (fun l => ‖x - z l‖ - G l)
  have hLip : LipschitzWith 1 h := lipschitz_inf_cone z G
  have h1 : ∀ k, F k + (S + η) - D ≤ h (z k) := fun k =>
    Finset.le_inf' _ _ fun l _ => by linarith [hFG k l]
  have h2 : ∀ l, h (z l) ≤ -G l := fun l => by
    refine (Finset.inf'_le _ (Finset.mem_univ l)).trans ?_
    simp
  have hlow : S + η ≤ ∑ k, h (z k) * (a k - b k) := by
    have : ∀ k, (F k + (S + η) - D) * a k + G k * b k ≤ h (z k) * (a k - b k) := fun k => by
      nlinarith [mul_le_mul_of_nonneg_right (h1 k) (ha k), mul_le_mul_of_nonneg_right (h2 k) (hb k)]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun k _ => this k)
    have e : ∀ k, (F k + (S + η) - D) * a k + G k * b k =
        F k * a k + (S + η - D) * a k + G k * b k := fun k => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hsa]
    rw [hD]; ring
  have := hS h hLip
  linarith

end KR


open Classical in
lemma law_eq_sum_dirac {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (z : Fin N → E)
    (hz : Function.Injective z) (T : Ω → E) (hT : Measurable T) (hrange : ∀ ω, ∃ k, T ω = z k) :
    P.map T = ∑ k, ENNReal.ofReal (P (T ⁻¹' {z k})).toReal • Measure.dirac (z k) := by
  ext A hA
  rw [Measure.map_apply hT hA, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  have hfin : ∀ k, P (T ⁻¹' {z k}) ≠ ⊤ := fun k => measure_ne_top _ _
  simp only [ENNReal.ofReal_toReal (hfin _)]
  have : T ⁻¹' A = ⋃ k ∈ Finset.univ.filter (fun k => z k ∈ A), T ⁻¹' {z k} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := hrange ω
      exact ⟨k, by rwa [← hk], hk⟩
    · rintro ⟨k, hk, hk'⟩; rwa [hk']
  rw [this, measure_biUnion_finset]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : z k ∈ A <;> simp [h, Set.indicator]
  · intro i _ j _ hij
    refine Set.disjoint_left.2 fun ω hi hj => hij (hz ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi hj
    rw [← hi, ← hj]
  · intro k _; exact hT (measurableSet_singleton _)


section Discrete
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  {Ω : Type*} [MeasurableSpace Ω]

lemma integral_sum_dirac {N : ℕ} (z : Fin N → B) (w : Fin N → ℝ) (hw : ∀ k, 0 ≤ w k) (h : B → ℝ)
    (hc : Continuous h) :
    ∫ x, h x ∂(∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k)) = ∑ k, w k * h (z k) := by
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac' _ _ hc.stronglyMeasurable]
    simp [ENNReal.toReal_ofReal (hw k)]
  · intro k _
    exact (integrable_dirac (enorm_lt_top)).smul_measure ENNReal.ofReal_ne_top

lemma coupling_sum_dirac {N : ℕ} (z : Fin N → B) (π : Fin N × Fin N → ℝ) (a' b' : Fin N → ℝ)
    (hπ : ∀ q, 0 ≤ π q) (h1 : ∀ k, ∑ l, π (k, l) = a' k) (h2 : ∀ l, ∑ k, π (k, l) = b' l) :
    IsCoupling (∑ q : Fin N × Fin N, ENNReal.ofReal (π q) • Measure.dirac (z q.1, z q.2))
      (∑ k, ENNReal.ofReal (a' k) • Measure.dirac (z k))
      (∑ k, ENNReal.ofReal (b' k) • Measure.dirac (z k)) := by
  constructor
  · ext A hA
    rw [Measure.map_apply measurable_fst hA]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    simp only [Measure.dirac_apply' _ (measurable_fst hA), Measure.dirac_apply' _ hA]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h1 k, ENNReal.ofReal_sum_of_nonneg (fun l _ => hπ _), Finset.sum_mul]
    by_cases h : z k ∈ A <;> simp [Set.indicator, Set.preimage, h]
  · ext A hA
    rw [Measure.map_apply measurable_snd hA]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    simp only [Measure.dirac_apply' _ (measurable_snd hA), Measure.dirac_apply' _ hA]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← h2 l, ENNReal.ofReal_sum_of_nonneg (fun k _ => hπ _), Finset.sum_mul]
    by_cases h : z l ∈ A <;> simp [Set.indicator, Set.preimage, h]

lemma wasserstein_discrete (P : Measure Ω) [IsProbabilityMeasure P] (T : B → B) (hT : Measurable T)
    (hfin : (Set.range T).Finite) (X Y : Ω → B) (hX : Measurable X) (hY : Measurable Y) (S : ℝ)
    (hS : ∀ h : B → ℝ, LipschitzWith 1 h →
      ∫ ω, h (T (X ω)) ∂P - ∫ ω, h (T (Y ω)) ∂P ≤ S) (η : ℝ) (hη : 0 < η) :
    wassersteinE 1 (law P (fun ω => T (X ω))) (law P (fun ω => T (Y ω))) ≤ ENNReal.ofReal (S + η) := by
  classical
  have hne : (Set.range T).Nonempty := ⟨T 0, 0, rfl⟩
  set s := hfin.toFinset with hs
  set N := s.card with hN
  have hN0 : NeZero N := ⟨by
    rw [hN]; exact (Finset.card_pos.2 (by simpa [hs] using hne)).ne'⟩
  let e := s.equivFin
  let z : Fin N → B := fun k => (e.symm k : B)
  have hz : Function.Injective z := fun i j h => e.symm.injective (Subtype.ext h)
  have hzmem : ∀ x, ∃ k, T x = z k := fun x => by
    have : T x ∈ s := by simp [hs]
    exact ⟨e ⟨T x, this⟩, by simp [z]⟩
  have hTXm : Measurable (fun ω => T (X ω)) := hT.comp hX
  have hTYm : Measurable (fun ω => T (Y ω)) := hT.comp hY
  set a : Fin N → ℝ := fun k => (P ((fun ω => T (X ω)) ⁻¹' {z k})).toReal with ha
  set b : Fin N → ℝ := fun k => (P ((fun ω => T (Y ω)) ⁻¹' {z k})).toReal with hb
  have hlawX : law P (fun ω => T (X ω)) = ∑ k, ENNReal.ofReal (a k) • Measure.dirac (z k) := by
    have := law_eq_sum_dirac P z hz _ hTXm (fun ω => hzmem (X ω))
    simpa [law, ha] using this
  have hlawY : law P (fun ω => T (Y ω)) = ∑ k, ENNReal.ofReal (b k) • Measure.dirac (z k) := by
    have := law_eq_sum_dirac P z hz _ hTYm (fun ω => hzmem (Y ω))
    simpa [law, hb] using this
  have ha0 : ∀ k, 0 ≤ a k := fun _ => ENNReal.toReal_nonneg
  have hb0 : ∀ k, 0 ≤ b k := fun _ => ENNReal.toReal_nonneg
  have hsum : ∀ w : Fin N → ℝ, (∀ k, 0 ≤ w k) →
      (∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k)) Set.univ = 1 → ∑ k, w k = 1 := by
    intro w hw h
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hw k)] at h
    have := (ENNReal.ofReal_eq_one).1 h
    exact this
  have hsa : ∑ k, a k = 1 := by
    refine hsum a ha0 ?_
    rw [← hlawX]; simp [law, Measure.map_apply hTXm MeasurableSet.univ]
  have hsb : ∑ k, b k = 1 := by
    refine hsum b hb0 ?_
    rw [← hlawY]; simp [law, Measure.map_apply hTYm MeasurableSet.univ]
  have hint : ∀ (W : Ω → B) (hW : Measurable W) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) →
      law P W = ∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k) → ∀ h : B → ℝ, Continuous h →
      ∫ ω, h (W ω) ∂P = ∑ k, w k * h (z k) := by
    intro W hW w hw hl h hc
    rw [← integral_map hW.aemeasurable hc.aestronglyMeasurable]
    have : P.map W = ∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k) := hl
    rw [this]
    exact integral_sum_dirac z w hw h hc
  obtain ⟨π, hπs, hπa, hπb, hπc⟩ := finite_transport z a b ha0 hb0 hsa hsb S (fun h hh => by
    have h1 := hint _ hTXm a ha0 hlawX h hh.continuous
    have h2 := hint _ hTYm b hb0 hlawY h hh.continuous
    have := hS h hh
    rw [h1, h2] at this
    simpa [mul_sub, Finset.sum_sub_distrib, mul_comm] using this) η hη
  have hcoup := coupling_sum_dirac z π a b hπs.1 hπa hπb
  rw [← hlawX, ← hlawY] at hcoup
  refine (wassersteinE_le_cost hcoup).trans ?_
  simp only [div_one, ENNReal.rpow_one, Real.rpow_one]
  rw [lintegral_finsetSum_measure]
  have hm : Measurable fun x : B × B => ENNReal.ofReal ‖x.1 - x.2‖ :=
    (ENNReal.continuous_ofReal.comp (continuous_norm.comp (continuous_fst.sub continuous_snd))).measurable
  simp only [lintegral_smul_measure, lintegral_dirac' _ hm, smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (hπs.1 _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (hπs.1 q) (norm_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hπc

end Discrete


section Grid

/-- Grid truncation: round to the grid `δℤ^p` inside the ball of radius `R`, send the rest to `0`. -/
def gridTrunc (δ R : ℝ) (x : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin p) :=
  if ‖x‖ ≤ R then WithLp.toLp 2 (fun i => δ * (⌊x i / δ⌋ : ℝ)) else 0

lemma measurable_gridTrunc (δ R : ℝ) : Measurable (gridTrunc (p := p) δ R) := by
  unfold gridTrunc
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ measurable_const
  have : Measurable fun x : EuclideanSpace ℝ (Fin p) => (fun i => δ * (⌊x i / δ⌋ : ℝ)) := by
    refine Measurable.of_eval fun i => ?_
    refine measurable_const.mul ?_
    have hproj : Measurable fun x : EuclideanSpace ℝ (Fin p) => x i :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).measurable
    exact (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (Int.measurable_floor.comp (hproj.div_const δ))
  exact (MeasurableEquiv.toLp 2 (Fin p → ℝ)).measurable.comp this

lemma norm_sub_gridTrunc_le {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (x : EuclideanSpace ℝ (Fin p)) :
    ‖x - gridTrunc δ R x‖ ≤ δ * Real.sqrt p + ‖x‖ ^ 2 / R := by
  have h1 : 0 ≤ δ * Real.sqrt p := by positivity
  have h2 : 0 ≤ ‖x‖ ^ 2 / R := by positivity
  unfold gridTrunc
  by_cases hx : ‖x‖ ≤ R
  · rw [if_pos hx]
    refine le_trans ?_ (le_add_of_nonneg_right h2)
    rw [EuclideanSpace.norm_eq]
    have hc : ∀ i : Fin p, (x i - δ * (⌊x i / δ⌋ : ℝ)) ^ 2 ≤ δ ^ 2 := fun i => by
      have a1 := Int.floor_le (x i / δ)
      have a2 := Int.lt_floor_add_one (x i / δ)
      rw [le_div_iff₀ hδ] at a1
      rw [div_lt_iff₀ hδ] at a2
      have b1 : 0 ≤ x i - δ * (⌊x i / δ⌋ : ℝ) := by nlinarith
      have b2 : x i - δ * (⌊x i / δ⌋ : ℝ) ≤ δ := by nlinarith
      nlinarith
    calc Real.sqrt (∑ i, ‖(x - WithLp.toLp 2 fun i => δ * (⌊x i / δ⌋ : ℝ)) i‖ ^ 2)
        ≤ Real.sqrt (∑ _i : Fin p, δ ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
          simpa [Real.norm_eq_abs, sq_abs] using hc i
      _ = δ * Real.sqrt p := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le, mul_comm]
  · rw [if_neg hx]
    push Not at hx
    simp only [sub_zero]
    refine le_trans ?_ (le_add_of_nonneg_left h1)
    rw [le_div_iff₀ hR]
    nlinarith [norm_nonneg x]


lemma finite_range_gridTrunc {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    (Set.range (gridTrunc (p := p) δ R)).Finite := by
  set M : ℤ := ⌈R / δ⌉ + 1 with hM
  have hfin : (Set.pi Set.univ (fun _ : Fin p => Set.Icc (-M) M)).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine ((hfin.image (fun m : Fin p → ℤ => (WithLp.toLp 2 (fun i => δ * (m i : ℝ)) :
    EuclideanSpace ℝ (Fin p)))).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  unfold gridTrunc
  by_cases hx : ‖x‖ ≤ R
  · rw [if_pos hx]
    right
    refine ⟨fun i => ⌊x i / δ⌋, fun i _ => ?_, rfl⟩
    have hxi : |x i| ≤ R := by
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      linarith
    have hc : R / δ ≤ ⌈R / δ⌉ := Int.le_ceil _
    have hxd : |x i / δ| ≤ R / δ := by
      rw [abs_div, abs_of_pos hδ]; exact div_le_div_of_nonneg_right hxi hδ.le
    have hlo := (abs_le.1 hxd).1
    have hhi := (abs_le.1 hxd).2
    simp only [Set.mem_Icc]
    constructor
    · rw [Int.le_floor]
      push_cast
      have : ((⌈R / δ⌉ : ℤ) : ℝ) ≥ R / δ := hc
      rw [hM]; push_cast
      linarith
    · have := Int.floor_le (x i / δ)
      have h2 : (⌊x i / δ⌋ : ℝ) ≤ M := by rw [hM]; push_cast; linarith
      exact_mod_cast h2
  · rw [if_neg hx]; left; rfl

end Grid

end KantorovichUpper

section KantorovichDual
set_option linter.unusedSectionVars false
variable {Ω : Type*} [MeasurableSpace Ω]

local notation "𝔼" => EuclideanSpace ℝ (Fin p)

lemma integrable_lip_comp (P : Measure Ω) [IsProbabilityMeasure P] {h : 𝔼 → ℝ}
    (hh : LipschitzWith 1 h) {Z : Ω → 𝔼} (hZ : Measurable Z) (hZi : Integrable (fun ω => ‖Z ω‖) P) :
    Integrable (fun ω => h (Z ω)) P := by
  refine Integrable.mono' ((integrable_const (|h 0|)).add hZi)
    (hh.continuous.measurable.comp hZ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have := hh.dist_le_mul (Z ω) 0
  simp only [NNReal.coe_one, one_mul, dist_zero_right, Real.dist_eq] at this
  rw [Real.norm_eq_abs, Pi.add_apply]
  have h2 := abs_sub_abs_le_abs_sub (h (Z ω)) (h 0)
  linarith

lemma abs_integral_lip_sub_le (P : Measure Ω) [IsProbabilityMeasure P] {h : 𝔼 → ℝ}
    (hh : LipschitzWith 1 h) {Z W : Ω → 𝔼} (hZ : Measurable Z) (hW : Measurable W)
    (hZi : Integrable (fun ω => ‖Z ω‖) P) (hWi : Integrable (fun ω => ‖W ω‖) P) :
    |∫ ω, h (W ω) ∂P - ∫ ω, h (Z ω) ∂P| ≤ ∫ ω, ‖W ω - Z ω‖ ∂P := by
  rw [← integral_sub (integrable_lip_comp P hh hW hWi) (integrable_lip_comp P hh hZ hZi)]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ?_ (ae_of_all _ fun ω => ?_))
  · exact (hWi.add hZi).mono' ((hW.sub hZ).norm.aestronglyMeasurable) (ae_of_all _ fun ω => by
      simpa using norm_sub_le (W ω) (Z ω))
  · have := hh.dist_le_mul (W ω) (Z ω)
    simpa [Real.dist_eq, dist_eq_norm] using this


lemma integral_err_gridTrunc (P : Measure Ω) [IsProbabilityMeasure P] {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    {Z : Ω → 𝔼} (hZ : Measurable Z) (hZ2 : MemLp Z 2 P) :
    Integrable (fun ω => ‖Z ω - gridTrunc δ R (Z ω)‖) P ∧
    ∫ ω, ‖Z ω - gridTrunc δ R (Z ω)‖ ∂P ≤ δ * Real.sqrt p + (∫ ω, ‖Z ω‖ ^ 2 ∂P) / R := by
  have hsq : Integrable (fun ω => ‖Z ω‖ ^ 2) P := hZ2.norm.integrable_sq
  have hb : Integrable (fun ω => δ * Real.sqrt p + ‖Z ω‖ ^ 2 / R) P :=
    (integrable_const _).add (hsq.div_const R)
  have hmeas : Measurable fun ω => ‖Z ω - gridTrunc δ R (Z ω)‖ :=
    (hZ.sub ((measurable_gridTrunc δ R).comp hZ)).norm
  have hle : ∀ ω, ‖Z ω - gridTrunc δ R (Z ω)‖ ≤ δ * Real.sqrt p + ‖Z ω‖ ^ 2 / R :=
    fun ω => norm_sub_gridTrunc_le hδ hR (Z ω)
  have hint : Integrable (fun ω => ‖Z ω - gridTrunc δ R (Z ω)‖) P :=
    hb.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hle ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖Z ω - gridTrunc δ R (Z ω)‖ ∂P ≤ ∫ ω, (δ * Real.sqrt p + ‖Z ω‖ ^ 2 / R) ∂P :=
        integral_mono hint hb hle
    _ = δ * Real.sqrt p + (∫ ω, ‖Z ω‖ ^ 2 ∂P) / R := by
        rw [integral_add (integrable_const _) (hsq.div_const R), integral_const, integral_div]
        simp


lemma wasserstein_le_integral (P : Measure Ω) [IsProbabilityMeasure P] {Z W : Ω → 𝔼}
    (hZ : Measurable Z) (hW : Measurable W) (hi : Integrable (fun ω => ‖Z ω - W ω‖) P) :
    wassersteinE 1 (law P Z) (law P W) ≤ ENNReal.ofReal (∫ ω, ‖Z ω - W ω‖ ∂P) := by
  refine (wassersteinE_le_of_coupling P 1 le_rfl Z W hZ.aemeasurable hW.aemeasurable).trans ?_
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => norm_nonneg _)]


theorem wassersteinE_one_le_of_dual (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → 𝔼)
    (hX : Measurable X) (hY : Measurable Y) (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P) (t : ℝ)
    (ht : ∀ h : 𝔼 → ℝ, LipschitzWith 1 h → ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤ t) :
    wassersteinE 1 (law P X) (law P Y) ≤ ENNReal.ofReal t := by
  set mX : ℝ := ∫ ω, ‖X ω‖ ^ 2 ∂P with hmX
  set mY : ℝ := ∫ ω, ‖Y ω‖ ^ 2 ∂P with hmY
  have hmX0 : 0 ≤ mX := integral_nonneg fun _ => by positivity
  have hmY0 : 0 ≤ mY := integral_nonneg fun _ => by positivity
  have hXi : Integrable (fun ω => ‖X ω‖) P := (hX2.integrable one_le_two).norm
  have hYi : Integrable (fun ω => ‖Y ω‖) P := (hY2.integrable one_le_two).norm
  -- main estimate for fixed parameters
  have main : ∀ δ R η : ℝ, 0 < δ → 0 < R → 0 < η →
      wassersteinE 1 (law P X) (law P Y) ≤
        ENNReal.ofReal (t + 4 * (δ * Real.sqrt p + (mX + mY) / R) + η) := by
    intro δ R η hδ hR hη
    set T := gridTrunc (p := p) δ R with hT
    have hTm : Measurable T := measurable_gridTrunc δ R
    have hTXm : Measurable fun ω => T (X ω) := hTm.comp hX
    have hTYm : Measurable fun ω => T (Y ω) := hTm.comp hY
    obtain ⟨hEXi, hEX⟩ := integral_err_gridTrunc P hδ hR hX hX2
    obtain ⟨hEYi, hEY⟩ := integral_err_gridTrunc P hδ hR hY hY2
    set e0 : ℝ := δ * Real.sqrt p + (mX + mY) / R with he0
    have hEX' : ∫ ω, ‖X ω - T (X ω)‖ ∂P ≤ e0 := by
      refine hEX.trans ?_
      rw [he0]; gcongr
      · linarith
    have hEY' : ∫ ω, ‖Y ω - T (Y ω)‖ ∂P ≤ e0 := by
      refine hEY.trans ?_
      rw [he0]; gcongr
      · linarith
    have hTXi : Integrable (fun ω => ‖T (X ω)‖) P := by
      refine (hXi.add hEXi).mono' (hTm.comp hX).norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply]
      calc ‖T (X ω)‖ = ‖X ω - (X ω - T (X ω))‖ := by congr 1; abel
        _ ≤ _ := by
          refine (norm_sub_le _ _).trans ?_
          exact le_rfl
    have hTYi : Integrable (fun ω => ‖T (Y ω)‖) P := by
      refine (hYi.add hEYi).mono' (hTm.comp hY).norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply]
      calc ‖T (Y ω)‖ = ‖Y ω - (Y ω - T (Y ω))‖ := by congr 1; abel
        _ ≤ _ := by
          refine (norm_sub_le _ _).trans ?_
          exact le_rfl
    -- discrete step
    have hdisc := wasserstein_discrete P T hTm (finite_range_gridTrunc hδ R) X Y hX hY
      (t + 2 * e0) (fun h hh => by
        have h1 := abs_integral_lip_sub_le P hh hX hTXm hXi hTXi
        have h2 := abs_integral_lip_sub_le P hh hY hTYm hYi hTYi
        have e1 : ∫ ω, ‖T (X ω) - X ω‖ ∂P = ∫ ω, ‖X ω - T (X ω)‖ ∂P :=
          integral_congr_ae (ae_of_all _ fun ω => norm_sub_rev _ _)
        have e2 : ∫ ω, ‖T (Y ω) - Y ω‖ ∂P = ∫ ω, ‖Y ω - T (Y ω)‖ ∂P :=
          integral_congr_ae (ae_of_all _ fun ω => norm_sub_rev _ _)
        rw [e1] at h1; rw [e2] at h2
        have := ht h hh
        have a1 := (abs_le.1 h1).2
        have a2 := (abs_le.1 h2).1
        linarith) η hη
    -- couplings of the originals with their truncations
    have hc1 := wasserstein_le_integral P hX hTXm hEXi
    have hc2 := wasserstein_le_integral P hTYm hY (by
      refine hEYi.congr (ae_of_all _ fun ω => ?_)
      exact (norm_sub_rev _ _))
    have hc2' : wassersteinE 1 (law P fun ω => T (Y ω)) (law P Y) ≤ ENNReal.ofReal e0 := by
      refine hc2.trans (ENNReal.ofReal_le_ofReal ?_)
      refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun ω => norm_sub_rev _ _))) hEY'
    have hc1' : wassersteinE 1 (law P X) (law P fun ω => T (X ω)) ≤ ENNReal.ofReal e0 :=
      hc1.trans (ENNReal.ofReal_le_ofReal hEX')
    have tri1 := wassersteinE_triangle 1 le_rfl (law P X) (law P fun ω => T (X ω)) (law P Y)
    have tri2 := wassersteinE_triangle 1 le_rfl (law P fun ω => T (X ω)) (law P fun ω => T (Y ω))
      (law P Y)
    have ht0 : 0 ≤ t := by simpa using ht (fun _ => 0) ((LipschitzWith.const (0:ℝ)).weaken zero_le)
    have he0nn : 0 ≤ e0 := by
      rw [he0]; positivity
    calc wassersteinE 1 (law P X) (law P Y)
        ≤ wassersteinE 1 (law P X) (law P fun ω => T (X ω)) +
          wassersteinE 1 (law P fun ω => T (X ω)) (law P Y) := tri1
      _ ≤ ENNReal.ofReal e0 + (wassersteinE 1 (law P fun ω => T (X ω)) (law P fun ω => T (Y ω)) +
          wassersteinE 1 (law P fun ω => T (Y ω)) (law P Y)) := by gcongr
      _ ≤ ENNReal.ofReal e0 + (ENNReal.ofReal (t + 2 * e0 + η) + ENNReal.ofReal e0) := by
          gcongr
      _ = ENNReal.ofReal (t + 4 * e0 + η) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hp1 : 0 < Real.sqrt p + 1 := by positivity
  have hm1 : 0 < mX + mY + 1 := by positivity
  have := main (ε / (16 * (Real.sqrt p + 1))) (16 * (mX + mY + 1) / ε) (ε / 2) (by positivity)
    (by positivity) (by positivity)
  refine this.trans ?_
  have hbound : 4 * (ε / (16 * (Real.sqrt p + 1)) * Real.sqrt p + (mX + mY) / (16 * (mX + mY + 1) / ε))
      + ε / 2 ≤ ε := by
    have a1 : ε / (16 * (Real.sqrt p + 1)) * Real.sqrt p ≤ ε / 16 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.sqrt_nonneg p]
    have a2 : (mX + mY) / (16 * (mX + mY + 1) / ε) ≤ ε / 16 := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  calc ENNReal.ofReal (t + 4 * (ε / (16 * (Real.sqrt p + 1)) * Real.sqrt p +
          (mX + mY) / (16 * (mX + mY + 1) / ε)) + ε / 2) ≤ ENNReal.ofReal (t + ε) := by
        apply ENNReal.ofReal_le_ofReal; linarith
    _ ≤ ENNReal.ofReal t + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal t + ε := by rw [ENNReal.ofReal_coe_nnreal]

end KantorovichDual

section GaussSmoothing

open ProbabilityTheory Complex
open scoped Real

local notation "𝔼" => EuclideanSpace ℝ (Fin p)

/-- The Gaussian density `(b/π)^{p/2} exp(-b‖z‖²)` (variance `ε² = 1/(2b)` per coordinate). -/
def gaussKernel (p : ℕ) (b : ℝ) (z : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (b / π) ^ ((p : ℝ) / 2) * Real.exp (-b * ‖z‖ ^ 2)

lemma gaussKernel_pos {b : ℝ} (hb : 0 < b) (z : 𝔼) : 0 < gaussKernel p b z := by
  unfold gaussKernel; positivity

lemma continuous_gaussKernel (b : ℝ) : Continuous (gaussKernel p b) := by
  unfold gaussKernel; fun_prop

lemma integrable_exp_neg_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : 𝔼 => Real.exp (-b * ‖z‖ ^ 2)) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := 𝔼) (b := (b : ℂ))
    (by simpa using hb) 0 0
  refine (this.norm).congr (ae_of_all _ fun z => ?_)
  simp only [mul_zero, add_zero]
  rw [Complex.norm_exp]
  simp
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma integral_exp_neg_norm_sq {b : ℝ} (hb : 0 < b) :
    ∫ z : 𝔼, Real.exp (-b * ‖z‖ ^ 2) = (π / b) ^ ((p : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp

lemma integral_gaussKernel {b : ℝ} (hb : 0 < b) : ∫ z : 𝔼, gaussKernel p b z = 1 := by
  unfold gaussKernel
  rw [integral_const_mul, integral_exp_neg_norm_sq hb, ← Real.mul_rpow (by positivity) (by positivity)]
  have : b / π * (π / b) = 1 := by field_simp
  rw [this, Real.one_rpow]

lemma integrable_gaussKernel {b : ℝ} (hb : 0 < b) : Integrable (gaussKernel p b) :=
  (integrable_exp_neg_norm_sq hb).const_mul _


/-- `N(0, ε² I)` on `ℝ^p` has Lebesgue density `gaussKernel p (1/(2ε²))`. -/
lemma mvGaussian_eq_withDensity {ε : ℝ} (hε : 0 < ε) :
    multivariateGaussian (0 : 𝔼) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) =
      volume.withDensity (fun z => ENNReal.ofReal (gaussKernel p (1 / (2 * ε ^ 2)) z)) := by
  set b : ℝ := 1 / (2 * ε ^ 2) with hb
  have hb0 : 0 < b := by positivity
  have hpsd : (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by positivity)
  have : IsFiniteMeasure (volume.withDensity (fun z : 𝔼 => ENNReal.ofReal (gaussKernel p b z))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_gaussKernel hb0).2
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_multivariateGaussian hpsd, charFun_apply, 
    integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (gaussKernel p b z)) (ENNReal.measurable_ofReal.comp (continuous_gaussKernel b).measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hK : ∀ x : 𝔼, (ENNReal.ofReal (gaussKernel p b x)).toReal = gaussKernel p b x := fun x =>
    ENNReal.toReal_ofReal (gaussKernel_pos hb0 x).le
  simp_rw [hK]
  have h1 : ∀ x : 𝔼, gaussKernel p b x • cexp (↑(inner ℝ x t) * I) =
      ((b / π) ^ ((p : ℝ) / 2) : ℝ) * cexp (-(b : ℂ) * ‖x‖ ^ 2 + I * (inner ℝ t x : ℝ)) := fun x => by
    rw [Complex.real_smul, gaussKernel, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add, real_inner_comm]
    congr 3
    · push_cast; ring
    · ring
  simp_rw [h1]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb0)]
  have hfr : (Module.finrank ℝ 𝔼 : ℂ) / 2 = (((p : ℝ) / 2 : ℝ) : ℂ) := by
    simp
  have hc : (((b / π) ^ ((p : ℝ) / 2) : ℝ) : ℂ) * ((π : ℂ) / (b : ℂ)) ^ (((p : ℝ) / 2 : ℝ) : ℂ) = 1 := by
    have : ((π : ℂ) / (b : ℂ)) = (((π / b : ℝ)) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul,
      ← Real.mul_rpow (by positivity) (by positivity)]
    have : b / π * (π / b) = 1 := by field_simp
    rw [this, Real.one_rpow]; simp
  rw [hfr, ← mul_assoc, hc, one_mul]
  congr 1
  have hn : ‖t‖ ^ 2 = ∑ i, t i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hq : t.ofLp ⬝ᵥ (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).mulVec t.ofLp = ε ^ 2 * ‖t‖ ^ 2 := by
    rw [hn, Finset.mul_sum]
    simp [dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.one_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq]
  have hb' : (b : ℂ) = 1 / (2 * (ε : ℂ) ^ 2) := by rw [hb]; push_cast; rfl
  rw [hb']
  have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  simp
  field_simp
  push_cast
  ring


/-- The real inner product as a continuous bilinear map. -/
def ipCLM (p : ℕ) : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ := innerSL ℝ

lemma ipCLM_apply (x y : 𝔼) : ipCLM p x y = inner ℝ x y := rfl

lemma norm_ipCLM_apply (x : 𝔼) : ‖ipCLM p x‖ = ‖x‖ := innerSL_apply_norm ℝ x

lemma norm_ipCLM_le : ‖ipCLM p‖ ≤ 1 := norm_innerSL_le ℝ

lemma hasFDerivAt_gaussKernel (b : ℝ) (z : 𝔼) :
    HasFDerivAt (gaussKernel p b) ((-2 * b * gaussKernel p b z) • ipCLM p z) z := by
  have h1 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := ((h1.const_mul (-b)).exp).const_mul ((b / π) ^ ((p : ℝ) / 2))
  refine h2.congr_fderiv ?_
  ext w
  have e : ((innerSL ℝ : 𝔼 →L⋆[ℝ] 𝔼 →L[ℝ] ℝ) z) w = inner ℝ z w := rfl
  simp [gaussKernel, ipCLM]
  rw [e]
  ring

lemma fderiv_gaussKernel (b : ℝ) :
    fderiv ℝ (gaussKernel p b) = fun z => (-2 * b * gaussKernel p b z) • ipCLM p z := by
  ext1 z; exact (hasFDerivAt_gaussKernel b z).fderiv

lemma contDiff_gaussKernel (b : ℝ) : ContDiff ℝ ⊤ (gaussKernel p b) := by
  unfold gaussKernel
  refine contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul ?_))
  exact contDiff_norm_sq ℝ

lemma hasFDerivAt_fderiv_gaussKernel (b : ℝ) (z : 𝔼) :
    HasFDerivAt (fderiv ℝ (gaussKernel p b))
      ((-2 * b * gaussKernel p b z) • ipCLM p +
        ((-2 * b) • ((-2 * b * gaussKernel p b z) • ipCLM p z)).smulRight (ipCLM p z)) z := by
  rw [fderiv_gaussKernel]
  have hc : HasFDerivAt (fun z => -2 * b * gaussKernel p b z)
      ((-2 * b) • ((-2 * b * gaussKernel p b z) • ipCLM p z)) z := by
    refine ((hasFDerivAt_gaussKernel b z).const_mul (-2 * b)).congr_fderiv ?_
    ext w; simp
  exact hc.smul (ipCLM p).hasFDerivAt


lemma mul_exp_le (a t : ℝ) (ha : 0 < a) :
    t * Real.exp (-(a / 2) * t ^ 2) ≤ 1 + 1 / a := by
  have h1 : t ≤ (1 + 1 / a) * (1 + a / 2 * t ^ 2) := by
    have : 0 < a := ha
    have h2 : t ≤ a / 2 * t ^ 2 + 1 / a := by
      have : 0 ≤ (a * t - 1) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ (a * t - 1) ^ 2 / (2 * a) := by positivity
      have h4 : (a * t - 1) ^ 2 / (2 * a) = a / 2 * t ^ 2 + 1 / (2 * a) - t := by
        field_simp; ring
      have : 1 / (2 * a) ≤ 1 / a := by
        rw [div_le_div_iff₀ (by positivity) ha]; nlinarith
      linarith
    nlinarith [mul_nonneg ha.le (sq_nonneg t), one_div_pos.2 ha]
  have h5 : (1 + a / 2 * t ^ 2) * Real.exp (-(a / 2) * t ^ 2) ≤ 1 := by
    have := Real.add_one_le_exp (a / 2 * t ^ 2)
    have h6 : Real.exp (-(a / 2) * t ^ 2) * Real.exp (a / 2 * t ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(a / 2) * t ^ 2)]
  calc t * Real.exp (-(a / 2) * t ^ 2)
      ≤ (1 + 1 / a) * (1 + a / 2 * t ^ 2) * Real.exp (-(a / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (1 + 1 / a) * ((1 + a / 2 * t ^ 2) * Real.exp (-(a / 2) * t ^ 2)) := by ring
    _ ≤ (1 + 1 / a) * 1 := by gcongr
    _ = 1 + 1 / a := mul_one _

lemma sq_mul_exp_le (a t : ℝ) (ha : 0 < a) :
    t ^ 2 * Real.exp (-(a / 2) * t ^ 2) ≤ 2 / a := by
  have h1 : a / 2 * t ^ 2 * Real.exp (-(a / 2) * t ^ 2) ≤ 1 := by
    have := Real.add_one_le_exp (a / 2 * t ^ 2)
    have h6 : Real.exp (-(a / 2) * t ^ 2) * Real.exp (a / 2 * t ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(a / 2) * t ^ 2), mul_nonneg ha.le (sq_nonneg t)]
  rw [le_div_iff₀ ha]
  nlinarith


lemma exp_split (b t : ℝ) : Real.exp (-b * t ^ 2) =
    Real.exp (-(b / 2) * t ^ 2) * Real.exp (-(b / 2) * t ^ 2) := by
  rw [← Real.exp_add]; ring_nf

lemma gaussKernel_le {b : ℝ} (hb : 0 < b) (z : 𝔼) :
    ‖gaussKernel p b z‖ ≤ (b / π) ^ ((p : ℝ) / 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
  rw [Real.norm_eq_abs, abs_of_pos (gaussKernel_pos hb z)]
  unfold gaussKernel
  gcongr
  nlinarith [sq_nonneg ‖z‖]

lemma norm_fderiv_gaussKernel_le {b : ℝ} (hb : 0 < b) (z : 𝔼) :
    ‖fderiv ℝ (gaussKernel p b) z‖ ≤
      2 * b * (b / π) ^ ((p : ℝ) / 2) * (1 + 1 / b) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
  rw [fderiv_gaussKernel, norm_smul, norm_ipCLM_apply, Real.norm_eq_abs]
  have hK := gaussKernel_pos hb z
  rw [abs_of_neg (by nlinarith)]
  unfold gaussKernel
  rw [exp_split]
  have := mul_exp_le b ‖z‖ hb
  have hc : 0 < (b / π) ^ ((p : ℝ) / 2) := by positivity
  have he := Real.exp_pos (-(b / 2) * ‖z‖ ^ 2)
  calc -(-2 * b * ((b / π) ^ ((p : ℝ) / 2) * (Real.exp (-(b / 2) * ‖z‖ ^ 2) *
        Real.exp (-(b / 2) * ‖z‖ ^ 2)))) * ‖z‖
      = 2 * b * (b / π) ^ ((p : ℝ) / 2) * (‖z‖ * Real.exp (-(b / 2) * ‖z‖ ^ 2)) *
          Real.exp (-(b / 2) * ‖z‖ ^ 2) := by ring
    _ ≤ 2 * b * (b / π) ^ ((p : ℝ) / 2) * (1 + 1 / b) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
        gcongr

lemma norm_fderiv_fderiv_gaussKernel_le {b : ℝ} (hb : 0 < b) (z : 𝔼) :
    ‖fderiv ℝ (fderiv ℝ (gaussKernel p b)) z‖ ≤
      10 * b * (b / π) ^ ((p : ℝ) / 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
  rw [(hasFDerivAt_fderiv_gaussKernel b z).fderiv]
  have hK := gaussKernel_pos hb z
  have hc : 0 < (b / π) ^ ((p : ℝ) / 2) := by positivity
  have he := Real.exp_pos (-(b / 2) * ‖z‖ ^ 2)
  refine (norm_add_le ((-2 * b * gaussKernel p b z) • ipCLM p)
    (((-2 * b) • ((-2 * b * gaussKernel p b z) • ipCLM p z)).smulRight (ipCLM p z))).trans ?_
  have hA : ‖(-2 * b * gaussKernel p b z) • ipCLM p‖ ≤ 2 * b * gaussKernel p b z := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_neg (by nlinarith)]
    have := norm_ipCLM_le (p := p)
    have : 0 ≤ 2 * b * gaussKernel p b z := by positivity
    nlinarith
  have hB : ‖((-2 * b) • ((-2 * b * gaussKernel p b z) • ipCLM p z)).smulRight (ipCLM p z)‖ ≤
      4 * b ^ 2 * gaussKernel p b z * ‖z‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_ipCLM_apply]
    have h3 : ‖(-2 * b) • ((-2 * b * gaussKernel p b z) • ipCLM p z)‖ ≤
        4 * b ^ 2 * gaussKernel p b z * ‖z‖ := by
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _)).trans (le_of_eq ?_)
      rw [norm_ipCLM_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (by nlinarith),
        abs_of_neg (by nlinarith)]
      ring
    calc _ ≤ 4 * b ^ 2 * gaussKernel p b z * ‖z‖ * ‖z‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = _ := by ring
  refine (add_le_add hA hB).trans ?_
  have hK' : gaussKernel p b z = (b / π) ^ ((p : ℝ) / 2) * (Real.exp (-(b / 2) * ‖z‖ ^ 2) *
      Real.exp (-(b / 2) * ‖z‖ ^ 2)) := by
    unfold gaussKernel; rw [exp_split]
  have he1 : Real.exp (-(b / 2) * ‖z‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖z‖]
  have hsq := sq_mul_exp_le b ‖z‖ hb
  have e3 : 4 * b ^ 2 * gaussKernel p b z * ‖z‖ ^ 2 =
      4 * b ^ 2 * (b / π) ^ ((p : ℝ) / 2) * (‖z‖ ^ 2 * Real.exp (-(b / 2) * ‖z‖ ^ 2)) *
        Real.exp (-(b / 2) * ‖z‖ ^ 2) := by rw [hK']; ring
  have e4 : 2 * b * gaussKernel p b z ≤ 2 * b * (b / π) ^ ((p : ℝ) / 2) *
      Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
    rw [hK']
    have : Real.exp (-(b / 2) * ‖z‖ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) ≤
        Real.exp (-(b / 2) * ‖z‖ ^ 2) := by nlinarith
    have : 0 ≤ 2 * b * (b / π) ^ ((p : ℝ) / 2) := by positivity
    nlinarith
  have e5 : 4 * b ^ 2 * (b / π) ^ ((p : ℝ) / 2) * (‖z‖ ^ 2 * Real.exp (-(b / 2) * ‖z‖ ^ 2)) *
        Real.exp (-(b / 2) * ‖z‖ ^ 2) ≤ 4 * b ^ 2 * (b / π) ^ ((p : ℝ) / 2) * (2 / b) *
        Real.exp (-(b / 2) * ‖z‖ ^ 2) := by gcongr
  have e6 : 4 * b ^ 2 * (b / π) ^ ((p : ℝ) / 2) * (2 / b) = 8 * b * (b / π) ^ ((p : ℝ) / 2) := by
    field_simp; norm_num
  rw [e6] at e5
  nlinarith


lemma dom_bound {a : ℝ} (ha : 0 < a) (x0 x y : 𝔼) (hx : ‖x - x0‖ < 1) :
    (1 + ‖y‖) * Real.exp (-a * ‖x - y‖ ^ 2) ≤
      (1 + ‖x0‖) * Real.exp a * (2 + 2 / a) * Real.exp (-(a / 4) * ‖y - x0‖ ^ 2) := by
  set u := ‖y - x0‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  have h1 : 1 + ‖y‖ ≤ (1 + ‖x0‖) * (1 + u) := by
    have : ‖y‖ ≤ ‖x0‖ + u := by
      calc ‖y‖ = ‖x0 + (y - x0)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    nlinarith [norm_nonneg x0]
  have h2 : u ^ 2 / 2 - 1 ≤ ‖x - y‖ ^ 2 := by
    have : u ≤ ‖x - y‖ + ‖x - x0‖ := by
      calc u = ‖(x - x0) - (x - y)‖ := by rw [hu]; congr 1; abel
        _ ≤ ‖x - x0‖ + ‖x - y‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have h0 : 0 ≤ ‖x - x0‖ := norm_nonneg _
    have hsq : u ^ 2 ≤ (‖x - y‖ + ‖x - x0‖) ^ 2 := pow_le_pow_left₀ hu0 this 2
    have h5 : ‖x - x0‖ ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (‖x - y‖ - ‖x - x0‖)]
  have h3 : Real.exp (-a * ‖x - y‖ ^ 2) ≤ Real.exp a * Real.exp (-(a / 2) * u ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h4 : (1 + u) * Real.exp (-(a / 2) * u ^ 2) ≤ (2 + 2 / a) * Real.exp (-(a / 4) * u ^ 2) := by
    have e : Real.exp (-(a / 2) * u ^ 2) = Real.exp (-((a / 2) / 2) * u ^ 2) *
        Real.exp (-(a / 4) * u ^ 2) := by rw [← Real.exp_add]; ring_nf
    have hm := mul_exp_le (a / 2) u (by positivity)
    have he1 : Real.exp (-((a / 2) / 2) * u ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
    have hpos := Real.exp_pos (-(a / 4) * u ^ 2)
    have : 1 + 1 / (a / 2) = 1 + 2 / a := by field_simp
    rw [e]
    calc (1 + u) * (Real.exp (-((a / 2) / 2) * u ^ 2) * Real.exp (-(a / 4) * u ^ 2))
        = (Real.exp (-((a / 2) / 2) * u ^ 2) + u * Real.exp (-((a / 2) / 2) * u ^ 2)) *
            Real.exp (-(a / 4) * u ^ 2) := by ring
      _ ≤ (1 + (1 + 2 / a)) * Real.exp (-(a / 4) * u ^ 2) := by
          gcongr
          · rw [← this]; exact hm
      _ = _ := by ring
  have hx0 : 0 ≤ 1 + ‖x0‖ := by positivity
  calc (1 + ‖y‖) * Real.exp (-a * ‖x - y‖ ^ 2)
      ≤ ((1 + ‖x0‖) * (1 + u)) * (Real.exp a * Real.exp (-(a / 2) * u ^ 2)) :=
        mul_le_mul h1 h3 (Real.exp_pos _).le (by positivity)
    _ = (1 + ‖x0‖) * Real.exp a * ((1 + u) * Real.exp (-(a / 2) * u ^ 2)) := by ring
    _ ≤ (1 + ‖x0‖) * Real.exp a * ((2 + 2 / a) * Real.exp (-(a / 4) * u ^ 2)) := by gcongr
    _ = _ := by ring


section KernelIntegral
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma kernel_term_bound {h : 𝔼 → ℝ} {A : ℝ} (hA : ∀ y, |h y| ≤ A * (1 + ‖y‖))
    {κ : 𝔼 → F} {C a : ℝ} (ha : 0 < a) (hκ0 : ∀ z, ‖κ z‖ ≤ C * Real.exp (-a * ‖z‖ ^ 2))
    (x0 x y : 𝔼) (hx : ‖x - x0‖ < 1) :
    ‖h y • κ (x - y)‖ ≤ A * C * ((1 + ‖x0‖) * Real.exp a * (2 + 2 / a)) *
      Real.exp (-(a / 4) * ‖y - x0‖ ^ 2) := by
  have hA0 : 0 ≤ A := by
    have := hA 0; simp at this; linarith [abs_nonneg (h 0)]
  have hC0 : 0 ≤ C := by
    have := hκ0 0
    have hp := Real.exp_pos (-a * ‖(0 : 𝔼)‖ ^ 2)
    by_contra hc; push Not at hc
    nlinarith [norm_nonneg (κ 0)]
  rw [norm_smul, Real.norm_eq_abs]
  have hd := dom_bound ha x0 x y hx
  calc |h y| * ‖κ (x - y)‖ ≤ (A * (1 + ‖y‖)) * (C * Real.exp (-a * ‖x - y‖ ^ 2)) :=
        mul_le_mul (hA y) (hκ0 _) (norm_nonneg _) (by positivity)
    _ = A * C * ((1 + ‖y‖) * Real.exp (-a * ‖x - y‖ ^ 2)) := by ring
    _ ≤ A * C * ((1 + ‖x0‖) * Real.exp a * (2 + 2 / a) * Real.exp (-(a / 4) * ‖y - x0‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma integrable_dom (a : ℝ) (ha : 0 < a) (D : ℝ) (x0 : 𝔼) :
    Integrable (fun y : 𝔼 => D * Real.exp (-(a / 4) * ‖y - x0‖ ^ 2)) :=
  ((integrable_exp_neg_norm_sq (p := p) (b := a / 4) (by positivity)).comp_sub_right x0).const_mul D

lemma hasFDerivAt_kernel_integral {h : 𝔼 → ℝ} (hh : Continuous h) {A : ℝ}
    (hA : ∀ y, |h y| ≤ A * (1 + ‖y‖)) {κ : 𝔼 → F} (hκ : ContDiff ℝ 1 κ) {C a : ℝ} (ha : 0 < a)
    (hκ0 : ∀ z, ‖κ z‖ ≤ C * Real.exp (-a * ‖z‖ ^ 2))
    (hκ1 : ∀ z, ‖fderiv ℝ κ z‖ ≤ C * Real.exp (-a * ‖z‖ ^ 2)) (x0 : 𝔼) :
    HasFDerivAt (fun x => ∫ y, h y • κ (x - y)) (∫ y, h y • fderiv ℝ κ (x0 - y)) x0 := by
  have hκc : Continuous κ := hκ.continuous
  have hκ'c : Continuous (fderiv ℝ κ) := hκ.continuous_fderiv one_ne_zero
  set D := A * C * ((1 + ‖x0‖) * Real.exp a * (2 + 2 / a)) with hD
  have hc0 : ∀ x : 𝔼, Continuous fun y => h y • κ (x - y) := fun x =>
    hh.smul (hκc.comp (continuous_const.sub continuous_id))
  have hc1 : Continuous fun y => h y • fderiv ℝ κ (x0 - y) :=
    hh.smul (hκ'c.comp (continuous_const.sub continuous_id))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x0 1)
    (F := fun x y => h y • κ (x - y)) (F' := fun x y => h y • fderiv ℝ κ (x - y))
    (bound := fun y => D * Real.exp (-(a / 4) * ‖y - x0‖ ^ 2)) (Metric.ball_mem_nhds x0 one_pos)
    (Filter.Eventually.of_forall fun x => (hc0 x).aestronglyMeasurable) ?_
    hc1.aestronglyMeasurable ?_
    (integrable_dom a ha D x0) ?_
  · refine (integrable_dom a ha D x0).mono' (hc0 x0).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    exact kernel_term_bound hA ha hκ0 x0 x0 y (by simp)
  · refine ae_of_all _ fun y x hx => ?_
    exact kernel_term_bound hA ha hκ1 x0 x y (by simpa [dist_eq_norm] using hx)
  · refine ae_of_all _ fun y x _ => ?_
    have h1 : HasFDerivAt κ (fderiv ℝ κ (x - y)) (x - y) :=
      ((hκ.differentiable one_ne_zero) (x - y)).hasFDerivAt
    have h2 := h1.comp x ((hasFDerivAt_id x).sub_const y)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2.const_smul (h y)

lemma continuous_kernel_integral {h : 𝔼 → ℝ} (hh : Continuous h) {A : ℝ}
    (hA : ∀ y, |h y| ≤ A * (1 + ‖y‖)) {κ : 𝔼 → F} (hκc : Continuous κ) {C a : ℝ} (ha : 0 < a)
    (hκ0 : ∀ z, ‖κ z‖ ≤ C * Real.exp (-a * ‖z‖ ^ 2)) :
    Continuous (fun x => ∫ y, h y • κ (x - y)) := by
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  set D := A * C * ((1 + ‖x0‖) * Real.exp a * (2 + 2 / a)) with hD
  refine continuousAt_of_dominated (bound := fun y => D * Real.exp (-(a / 4) * ‖y - x0‖ ^ 2))
    (Filter.Eventually.of_forall fun x =>
      (hh.smul (hκc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) ?_
    (integrable_dom a ha D x0) (ae_of_all _ fun y => ?_)
  · filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
    exact ae_of_all _ fun y => kernel_term_bound hA ha hκ0 x0 x y (by simpa [dist_eq_norm] using hx)
  · exact (continuous_const.smul (hκc.comp (continuous_id.sub continuous_const))).continuousAt

end KernelIntegral


lemma integral_norm_sq_mvGaussian {Δ : Matrix (Fin p) (Fin p) ℝ} (hΔ : Δ.PosSemidef) :
    ∫ y, ‖y‖ ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Δ) = Matrix.trace Δ := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Δ with hμ
  have hmem : ∀ i, MemLp (fun y : EuclideanSpace ℝ (Fin p) => y i) 2 μ := by
    intro i
    have := (IsGaussian.memLp_two_id (μ := μ))
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp_memLp' this
  have hint : ∀ i, Integrable (fun y : EuclideanSpace ℝ (Fin p) => (y i) ^ 2) μ := fun i =>
    (hmem i).integrable_sq
  have hmean : ∀ i, ∫ y : EuclideanSpace ℝ (Fin p), y i ∂μ = 0 := by
    intro i
    have h1 := ContinuousLinearMap.integral_comp_id_comm (μ := μ)
      (IsGaussian.integrable_id (μ := μ)) (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    simpa [hμ] using h1
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun i _ => hint i, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin p))) hΔ i
  rw [Matrix.diag_apply, ← this, variance_of_integral_eq_zero (Measurable.aemeasurable (by fun_prop)) (hmean i)]

lemma integral_kernel_eq_mvG {ε : ℝ} (hε : 0 < ε) (f : 𝔼 → ℝ) :
    ∫ z, gaussKernel p (1 / (2 * ε ^ 2)) z * f z =
      ∫ z, f z ∂(multivariateGaussian (0 : 𝔼) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))) := by
  rw [mvGaussian_eq_withDensity hε, integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (gaussKernel p (1 / (2 * ε ^ 2)) z))
    (ENNReal.measurable_ofReal.comp (continuous_gaussKernel _).measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (gaussKernel_pos (by positivity) z).le]

lemma sq_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) : (∫ a, f a ∂μ) ^ 2 ≤ ∫ a, f a ^ 2 ∂μ := by
  set m := ∫ a, f a ∂μ
  have hi : Integrable f μ := hf.integrable one_le_two
  have hi2 : Integrable (fun a => f a ^ 2) μ := hf.integrable_sq
  have h0 : 0 ≤ ∫ a, (f a - m) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have e : ∫ a, (f a - m) ^ 2 ∂μ = ∫ a, f a ^ 2 ∂μ - m ^ 2 := by
    have : ∀ a, (f a - m) ^ 2 = f a ^ 2 - 2 * m * f a + m ^ 2 := fun a => by ring
    simp_rw [this]
    rw [integral_add (f := fun a => f a ^ 2 - 2 * m * f a) (g := fun _ => m ^ 2)
        (hi2.sub (hi.const_mul _)) (integrable_const _),
      integral_sub (f := fun a => f a ^ 2) (g := fun a => 2 * m * f a) hi2 (hi.const_mul _),
      integral_const_mul, integral_const]
    simp; ring
  linarith

lemma integral_le_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) : ∫ a, f a ∂μ ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) :=
  Real.le_sqrt_of_sq_le (sq_integral_le μ hf)

lemma integral_kernel_norm_le {ε : ℝ} (hε : 0 < ε) :
    ∫ z, gaussKernel p (1 / (2 * ε ^ 2)) z * ‖z‖ ≤ ε * Real.sqrt p := by
  rw [integral_kernel_eq_mvG hε]
  set γ := multivariateGaussian (0 : 𝔼) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))
  have hpsd : (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by positivity)
  have hm : MemLp (fun z : 𝔼 => ‖z‖) 2 γ := (IsGaussian.memLp_two_id (μ := γ)).norm
  refine (integral_le_sqrt γ hm).trans (le_of_eq ?_)
  rw [integral_norm_sq_mvGaussian hpsd]
  simp [Matrix.trace_smul, Matrix.trace_one]
  left; exact Real.sqrt_sq hε.le


lemma norm_fderiv_gaussKernel_eq {b : ℝ} (hb : 0 < b) (z : 𝔼) :
    ‖fderiv ℝ (gaussKernel p b) z‖ = 2 * b * (gaussKernel p b z * ‖z‖) := by
  rw [fderiv_gaussKernel, norm_smul, norm_ipCLM_apply, Real.norm_eq_abs]
  have hK := gaussKernel_pos hb z
  rw [abs_of_neg (by nlinarith)]
  ring

lemma integrable_fderiv_gaussKernel {b : ℝ} (hb : 0 < b) :
    Integrable (fderiv ℝ (gaussKernel p b)) := by
  refine ((integrable_exp_neg_norm_sq (p := p) (b := b / 2) (by positivity)).const_mul
    (2 * b * (b / π) ^ ((p : ℝ) / 2) * (1 + 1 / b))).mono'
    ((contDiff_gaussKernel (p := p) b).continuous_fderiv (by simp)).aestronglyMeasurable
    (ae_of_all _ fun z => norm_fderiv_gaussKernel_le hb z)

lemma integral_norm_fderiv_gaussKernel_le {ε : ℝ} (hε : 0 < ε) :
    ∫ z, ‖fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) z‖ ≤ Real.sqrt p / ε := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  simp_rw [norm_fderiv_gaussKernel_eq hb]
  rw [integral_const_mul]
  calc 2 * (1 / (2 * ε ^ 2)) * ∫ z, gaussKernel p (1 / (2 * ε ^ 2)) z * ‖z‖
      ≤ 2 * (1 / (2 * ε ^ 2)) * (ε * Real.sqrt p) := by
        gcongr; exact integral_kernel_norm_le hε
    _ = Real.sqrt p / ε := by field_simp

section Conv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma conv_comm (f : 𝔼 → ℝ) (κ : 𝔼 → F) (x : 𝔼) :
    ∫ y, f y • κ (x - y) = ∫ z, f (x - z) • κ z := by
  have := integral_sub_left_eq_self (fun z => f (x - z) • κ z) (volume : Measure 𝔼) x
  simpa using this

lemma integrable_bdd_smul {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, |f y| ≤ R)
    {κ : 𝔼 → F} (hκc : Continuous κ) (hκ : Integrable κ) :
    Integrable (fun z => f z • κ z) :=
  (hκ.norm.const_mul R).mono' (hf.smul hκc).aestronglyMeasurable (ae_of_all _ fun z => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (hR z) (norm_nonneg _))

lemma norm_conv_sub_le {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, |f y| ≤ R)
    (hL : LipschitzWith 1 f) {κ : 𝔼 → F} (hκc : Continuous κ) (hκ : Integrable κ) (x x' : 𝔼) :
    ‖(∫ y, f y • κ (x - y)) - ∫ y, f y • κ (x' - y)‖ ≤ ‖x - x'‖ * ∫ z, ‖κ z‖ := by
  rw [conv_comm f κ x, conv_comm f κ x']
  have i1 : Integrable (fun z => f (x - z) • κ z) :=
    integrable_bdd_smul (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _) hκc hκ
  have i2 : Integrable (fun z => f (x' - z) • κ z) :=
    integrable_bdd_smul (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _) hκc hκ
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hκ.norm.const_mul _) (ae_of_all _ fun z => ?_)
  rw [← sub_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have := hL.norm_sub_le (x - z) (x' - z)
  simpa using this

lemma norm_conv_le {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, |f y| ≤ R)
    {κ : 𝔼 → F} (hκc : Continuous κ) (hκ : Integrable κ) (x : 𝔼) :
    ‖∫ y, f y • κ (x - y)‖ ≤ R * ∫ z, ‖κ z‖ := by
  rw [conv_comm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hκ.norm.const_mul _) (ae_of_all _ fun z => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hR _) (norm_nonneg _)

end Conv

/-- Gaussian smoothing at scale `ε`. -/
def gsmooth (ε : ℝ) (f : 𝔼 → ℝ) (x : 𝔼) : ℝ :=
  ∫ y, f y • gaussKernel p (1 / (2 * ε ^ 2)) (x - y)

lemma gsmooth_sub_le {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (hL : LipschitzWith 1 f) (x : 𝔼) :
    |gsmooth ε f x - f x| ≤ ε * Real.sqrt p := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  unfold gsmooth
  rw [conv_comm]
  set K := gaussKernel p (1 / (2 * ε ^ 2))
  have hK : Integrable K := integrable_gaussKernel hb
  have hKc : Continuous K := continuous_gaussKernel _
  have e : f x = ∫ z, f x • K z := by
    rw [integral_smul, integral_gaussKernel hb, smul_eq_mul, mul_one]
  have i1 : Integrable (fun z => f (x - z) • K z) :=
    integrable_bdd_smul (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _) hKc hK
  rw [e, ← integral_sub (g := fun z => f x • K z) i1 (hK.smul (f x)), ← Real.norm_eq_abs]
  have hm : Integrable (fun z => K z * ‖z‖) := by
    refine ((integrable_fderiv_gaussKernel (p := p) hb).norm.const_mul
      (1 / (2 * (1 / (2 * ε ^ 2))))).congr (ae_of_all _ fun z => ?_)
    simp only
    rw [norm_fderiv_gaussKernel_eq hb]
    field_simp
    exact mul_comm _ _
  refine (norm_integral_le_of_norm_le hm (ae_of_all _ fun z => ?_)).trans
    (integral_kernel_norm_le hε)
  rw [← sub_smul, norm_smul, mul_comm, Real.norm_of_nonneg (gaussKernel_pos hb z).le]
  refine mul_le_mul_of_nonneg_left ?_ (gaussKernel_pos hb z).le
  have := hL.norm_sub_le (x - z) x
  simpa using this


lemma kernel_bounds {b : ℝ} (hb : 0 < b) : ∃ C, ∀ z : 𝔼,
    ‖gaussKernel p b z‖ ≤ C * Real.exp (-(b / 2) * ‖z‖ ^ 2) ∧
    ‖fderiv ℝ (gaussKernel p b) z‖ ≤ C * Real.exp (-(b / 2) * ‖z‖ ^ 2) ∧
    ‖fderiv ℝ (fderiv ℝ (gaussKernel p b)) z‖ ≤ C * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
  set c := (b / π) ^ ((p : ℝ) / 2)
  have hc : 0 ≤ c := by positivity
  have h1 : 0 ≤ 2 * b * c * (1 + 1 / b) := by positivity
  have h2 : 0 ≤ 10 * b * c := by positivity
  refine ⟨c + 2 * b * c * (1 + 1 / b) + 10 * b * c, fun z => ?_⟩
  have he := (Real.exp_pos (-(b / 2) * ‖z‖ ^ 2)).le
  refine ⟨(gaussKernel_le hb z).trans ?_, (norm_fderiv_gaussKernel_le hb z).trans ?_,
    (norm_fderiv_fderiv_gaussKernel_le hb z).trans ?_⟩ <;>
  · apply mul_le_mul_of_nonneg_right _ he; linarith

lemma gsmooth_hasFDerivAt {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (x : 𝔼) :
    HasFDerivAt (gsmooth ε f) (∫ y, f y • fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) (x - y)) x := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  obtain ⟨C, hC⟩ := kernel_bounds (p := p) hb
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR 0)
  exact hasFDerivAt_kernel_integral hf (A := R)
    (fun y => (hR y).trans (le_mul_of_one_le_right hR0 (by linarith [norm_nonneg y])))
    ((contDiff_gaussKernel _).of_le le_top) (by positivity : 0 < (1 / (2 * ε ^ 2)) / 2)
    (fun z => (hC z).1) (fun z => (hC z).2.1) x

lemma gsmooth1_hasFDerivAt {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (x : 𝔼) :
    HasFDerivAt (fun x => ∫ y, f y • fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) (x - y))
      (∫ y, f y • fderiv ℝ (fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2)))) (x - y)) x := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  obtain ⟨C, hC⟩ := kernel_bounds (p := p) hb
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR 0)
  exact hasFDerivAt_kernel_integral hf (A := R)
    (fun y => (hR y).trans (le_mul_of_one_le_right hR0 (by linarith [norm_nonneg y])))
    ((contDiff_gaussKernel _).fderiv_right le_top) (by positivity : 0 < (1 / (2 * ε ^ 2)) / 2)
    (fun z => (hC z).2.1) (fun z => (hC z).2.2) x

lemma fderiv_gsmooth {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) :
    fderiv ℝ (gsmooth ε f) =
      fun x => ∫ y, f y • fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) (x - y) :=
  funext fun x => (gsmooth_hasFDerivAt hε hf hR x).fderiv

lemma contDiff_gsmooth {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) : ContDiff ℝ 2 (gsmooth ε f) := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  obtain ⟨C, hC⟩ := kernel_bounds (p := p) hb
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR 0)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (gsmooth_hasFDerivAt hε hf hR x).differentiableAt, by simp, ?_⟩
  rw [fderiv_gsmooth hε hf hR, contDiff_one_iff_fderiv]
  refine ⟨fun x => (gsmooth1_hasFDerivAt hε hf hR x).differentiableAt, ?_⟩
  rw [show fderiv ℝ (fun x => ∫ y, f y • fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) (x - y)) =
    fun x => ∫ y, f y • fderiv ℝ (fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2)))) (x - y) from
    funext fun x => (gsmooth1_hasFDerivAt hε hf hR x).fderiv]
  exact continuous_kernel_integral hf (A := R)
    (fun y => (hR y).trans (le_mul_of_one_le_right hR0 (by linarith [norm_nonneg y])))
    (((contDiff_gaussKernel _).fderiv_right le_top).continuous_fderiv one_ne_zero)
    (by positivity : 0 < (1 / (2 * ε ^ 2)) / 2) (fun z => (hC z).2.2)

lemma integral_norm_gaussKernel {b : ℝ} (hb : 0 < b) : ∫ z : 𝔼, ‖gaussKernel p b z‖ = 1 := by
  simp_rw [Real.norm_of_nonneg (gaussKernel_pos hb _).le]
  exact integral_gaussKernel hb

lemma abs_gsmooth_le {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (x : 𝔼) : |gsmooth ε f x| ≤ R := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  have := norm_conv_le hf hR (continuous_gaussKernel _) (integrable_gaussKernel (p := p) hb) x
  rw [integral_norm_gaussKernel hb, mul_one] at this
  exact this

lemma norm_fderiv_gsmooth_le {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (hL : LipschitzWith 1 f) (x : 𝔼) :
    ‖fderiv ℝ (gsmooth ε f) x‖ ≤ 1 := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  refine norm_fderiv_le_of_lip' ℝ zero_le_one (Filter.Eventually.of_forall fun x' => ?_)
  have := norm_conv_sub_le hf hR hL (continuous_gaussKernel _)
    (integrable_gaussKernel (p := p) hb) x' x
  rw [integral_norm_gaussKernel hb, mul_one] at this
  rw [one_mul]; exact this

lemma norm_fderiv_fderiv_gsmooth_le {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (hL : LipschitzWith 1 f) (x : 𝔼) :
    ‖fderiv ℝ (fderiv ℝ (gsmooth ε f)) x‖ ≤ Real.sqrt p / ε := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  rw [fderiv_gsmooth hε hf hR]
  refine norm_fderiv_le_of_lip' ℝ (by positivity) (Filter.Eventually.of_forall fun x' => ?_)
  have := norm_conv_sub_le hf hR hL
    ((contDiff_gaussKernel (p := p) _).continuous_fderiv (by simp))
    (integrable_fderiv_gaussKernel (p := p) hb) x' x
  refine this.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (integral_norm_fderiv_gaussKernel_le hε) (norm_nonneg _)


lemma mem_cbUnitBall_of_bounds {g : 𝔼 → ℝ} (hg : ContDiff ℝ 2 g) {M0 M1 M2 : ℝ}
    (h0 : ∀ z, |g z| ≤ M0) (h1 : ∀ z, ‖fderiv ℝ g z‖ ≤ M1)
    (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M2) (hM : 0 < M0 + M1 + M2) :
    ((M0 + M1 + M2)⁻¹ • g) ∈ CbUnitBall 𝔼 2 := by
  set M := M0 + M1 + M2
  have hMi : 0 ≤ M⁻¹ := inv_nonneg.2 hM.le
  have hb : ∀ j ≤ 2, ∀ z, ‖iteratedFDeriv ℝ j (M⁻¹ • g) z‖ ≤
      M⁻¹ * (if j = 0 then M0 else if j = 1 then M1 else M2) := by
    intro j hj z
    rw [iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le (by exact_mod_cast hj)), norm_smul,
      Real.norm_of_nonneg hMi]
    refine mul_le_mul_of_nonneg_left ?_ hMi
    interval_cases j
    · simpa [norm_iteratedFDeriv_zero] using h0 z
    · simpa [norm_iteratedFDeriv_one] using h1 z
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]; simpa using h2 z
  refine ⟨?_, fun j hj => ⟨_, by rintro _ ⟨z, rfl⟩; exact hb j hj z⟩, ?_⟩
  · exact_mod_cast hg.const_smul M⁻¹
  unfold cbNorm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e : ∀ j ≤ 2, (⨆ z, ‖iteratedFDeriv ℝ j (M⁻¹ • g) z‖) ≤
      M⁻¹ * (if j = 0 then M0 else if j = 1 then M1 else M2) := fun j hj =>
    ciSup_le fun z => hb j hj z
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  simp only [ite_true, ite_false, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at e0 e1 e2
  have : M⁻¹ * M0 + M⁻¹ * M1 + M⁻¹ * M2 = 1 := by
    rw [← mul_add, ← mul_add]; exact inv_mul_cancel₀ hM.ne'
  linarith

lemma clamp_err {R : ℝ} (hR : 0 < R) {u N : ℝ} (hu : |u| ≤ N) :
    |u - max (-R) (min R u)| ≤ N ^ 2 / (4 * R) := by
  have h1 : N - R ≤ N ^ 2 / (4 * R) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (N - 2 * R)]
  have h2 : 0 ≤ N ^ 2 / (4 * R) := by positivity
  rw [abs_le] at hu ⊢
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Per-test-function estimate behind Lemma A.26. -/
lemma dc2_test_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → 𝔼) (hX : Measurable X) (hY : Measurable Y) (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    {h : 𝔼 → ℝ} (hh : LipschitzWith 1 h) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤
      (∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P) / (4 * R) + 2 * ε * Real.sqrt p +
        (R + 1 + Real.sqrt p / ε) * smoothDist 2 (law P X) (law P Y) := by
  set u : 𝔼 → ℝ := fun x => h x - h 0
  have hu : LipschitzWith 1 u := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [u, Real.dist_eq] using hh.dist_le_mul x y
  set f : 𝔼 → ℝ := fun x => max (-R) (min R (u x))
  have hfL : LipschitzWith 1 f := (hu.const_min R).const_max (-R)
  have hfc : Continuous f := hfL.continuous
  have hfR : ∀ y, |f y| ≤ R := fun y => by
    rw [abs_le]; simp only [f]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have huf : ∀ x, |u x - f x| ≤ ‖x‖ ^ 2 / (4 * R) := fun x => by
    refine clamp_err hR ?_
    have := hu.dist_le_mul x 0
    simpa [u, Real.dist_eq] using this
  set g := gsmooth ε f
  have hgc : ContDiff ℝ 2 g := contDiff_gsmooth hε hfc hfR
  have hfg : ∀ x, |f x - g x| ≤ ε * Real.sqrt p := fun x => by
    rw [abs_sub_comm]; exact gsmooth_sub_le hε hfc hfR hfL x
  set M := R + 1 + Real.sqrt p / ε
  have hM : 0 < M := by positivity
  have hΦ : (M⁻¹ • g) ∈ CbUnitBall 𝔼 2 :=
    mem_cbUnitBall_of_bounds hgc (abs_gsmooth_le hε hfc hfR) (norm_fderiv_gsmooth_le hε hfc hfR hfL)
      (norm_fderiv_fderiv_gsmooth_le hε hfc hfR hfL) hM
  -- integrability
  have hXi : Integrable (fun ω => ‖X ω‖) P := (hX2.integrable one_le_two).norm
  have hYi : Integrable (fun ω => ‖Y ω‖) P := (hY2.integrable one_le_two).norm
  have hX2i : Integrable (fun ω => ‖X ω‖ ^ 2) P := hX2.integrable_norm_pow two_ne_zero
  have hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P := hY2.integrable_norm_pow two_ne_zero
  have hhX := integrable_lip_comp P hh hX hXi
  have hhY := integrable_lip_comp P hh hY hYi
  have hgb : ∀ z, |g z| ≤ R := abs_gsmooth_le hε hfc hfR
  have hgX : Integrable (fun ω => g (X ω)) P :=
    integrable_comp_of_continuous P hgc.continuous hgb hX.aemeasurable
  have hgY : Integrable (fun ω => g (Y ω)) P :=
    integrable_comp_of_continuous P hgc.continuous hgb hY.aemeasurable
  -- pointwise bound
  have hpt : ∀ ω, h (X ω) - h (Y ω) ≤
      (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R) + 2 * ε * Real.sqrt p + (g (X ω) - g (Y ω)) := by
    intro ω
    have a1 := abs_le.1 (huf (X ω))
    have a2 := abs_le.1 (huf (Y ω))
    have a3 := abs_le.1 (hfg (X ω))
    have a4 := abs_le.1 (hfg (Y ω))
    have e : h (X ω) - h (Y ω) = u (X ω) - u (Y ω) := by simp [u]
    rw [e, add_div]
    linarith [a1.2, a2.1, a3.2, a4.1]
  have hint : ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤
      (∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P) / (4 * R) + 2 * ε * Real.sqrt p +
        (∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P) := by
    have hc : ∫ _ω, (2 * ε * Real.sqrt p) ∂P = 2 * ε * Real.sqrt p := by simp
    rw [← integral_sub hhX hhY, ← integral_sub hgX hgY, ← integral_add hX2i hY2i,
      ← integral_div, ← hc,
      ← integral_add (f := fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R))
        (g := fun _ => 2 * ε * Real.sqrt p) ((hX2i.add hY2i).div_const _) (integrable_const _),
      ← integral_add (f := fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R) + 2 * ε * Real.sqrt p)
        (g := fun ω => g (X ω) - g (Y ω))
        (((hX2i.add hY2i).div_const _).add (integrable_const _)) (hgX.sub hgY)]
    exact integral_mono (hhX.sub hhY)
      ((((hX2i.add hY2i).div_const _).add (integrable_const _)).add (hgX.sub hgY)) hpt
  -- the smooth part
  have hΦc : Continuous (M⁻¹ • g) := hgc.continuous.const_smul _
  have hd := abs_integral_sub_le_smoothDist hΦ (law P X) (law P Y)
  rw [integral_map hX.aemeasurable hΦc.aestronglyMeasurable,
    integral_map hY.aemeasurable hΦc.aestronglyMeasurable] at hd
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul] at hd
  have hg : ∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P ≤ M * smoothDist 2 (law P X) (law P Y) := by
    have := (le_abs_self _).trans hd
    rw [← mul_sub] at this
    have h' := mul_le_mul_of_nonneg_left this hM.le
    rwa [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] at h'
  linarith


/-- The scalar optimisation behind Lemma A.26. -/
lemma dc2_real {a m ς d s : ℝ} (hs : 0 ≤ s) (hm0 : 0 ≤ m) (hm : m ≤ ς ^ 2) (hς : 0 ≤ ς)
    (hd : 0 ≤ d)
    (H : ∀ ε R : ℝ, 0 < ε → 0 < R → a ≤ m / (4 * R) + 2 * ε * s + (R + 1 + s / ε) * d) :
    a ≤ 3 * (s + ς) * Real.sqrt d + 3 * d := by
  rcases hd.eq_or_lt with h0 | hpos
  · subst h0
    simp only [Real.sqrt_zero, mul_zero, add_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have h := H (η / (4 * (s + 1))) ((m + 1) / η) (by positivity) (by positivity)
    simp only [mul_zero, add_zero] at h
    have h1 : m / (4 * ((m + 1) / η)) ≤ η / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : η / 4 * (4 * ((m + 1) / η)) = m + 1 := by field_simp
      linarith
    have h2 : 2 * (η / (4 * (s + 1))) * s ≤ η / 2 := by
      rw [show 2 * (η / (4 * (s + 1))) * s = (η * s) / (2 * (s + 1)) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · set t := Real.sqrt d with ht
    have ht0 : 0 < t := Real.sqrt_pos.2 hpos
    have hdt : d = t ^ 2 := (Real.sq_sqrt hd).symm
    have h := H t ((ς + t) / t) ht0 (by positivity)
    have hR' : ((ς + t) / t + 1 + s / t) * d = ς * t + 2 * t ^ 2 + s * t := by
      rw [hdt]; field_simp; ring
    have hm' : m / (4 * ((ς + t) / t)) ≤ ς * t / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : ς * t / 4 * (4 * ((ς + t) / t)) = ς * (ς + t) := by field_simp
      rw [this]; nlinarith
    rw [hR'] at h
    nlinarith

/-- Lemma A.26 under the side condition `0 ≤ ς` implicit in the source (M L10704-10710).
Without it the statement `dc2_to_w1` below fails: for `p = 1`, `X = 0`, `Y = e₁` and `ς = -10`
the right side is `ofReal (C·(1 - 10)·√d + C·d) = 0` (as `d ≤ 2`) while `W₁ = 1`. Proved with
`C = 3` by Gaussian smoothing of truncated `1`-Lipschitz test functions and the
Kantorovich–Rubinstein upper bound `wassersteinE_one_le_of_dual`. -/
theorem dc2_to_w1_of_nonneg : ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → EuclideanSpace ℝ (Fin p))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P) (ς : ℝ) (hς : 0 ≤ ς)
    (hmom : momentNorm P 2 X + momentNorm P 2 Y ≤ ς ^ 2),
    wassersteinE 1 (law P X) (law P Y) ≤
      ENNReal.ofReal (C * (Real.sqrt p + ς) * Real.sqrt (smoothDist 2 (law P X) (law P Y)) +
        C * smoothDist 2 (law P X) (law P Y)) := by
  refine ⟨3, by norm_num, fun p Ω _ P _ X Y hX hY hX2 hY2 ς hς hmom => ?_⟩
  have hXe : law P X = law P (hX.mk X) := Measure.map_congr hX.ae_eq_mk
  have hYe : law P Y = law P (hY.mk Y) := Measure.map_congr hY.ae_eq_mk
  have hX2' : MemLp (hX.mk X) 2 P := hX2.ae_eq hX.ae_eq_mk
  have hY2' : MemLp (hY.mk Y) 2 P := hY2.ae_eq hY.ae_eq_mk
  have hmX : momentNorm P 2 X = ∫ ω, ‖hX.mk X ω‖ ^ 2 ∂P := by
    unfold momentNorm
    refine integral_congr_ae (hX.ae_eq_mk.mono fun ω hω => ?_)
    simp [hω]
  have hmY : momentNorm P 2 Y = ∫ ω, ‖hY.mk Y ω‖ ^ 2 ∂P := by
    unfold momentNorm
    refine integral_congr_ae (hY.ae_eq_mk.mono fun ω hω => ?_)
    simp [hω]
  rw [hmX, hmY] at hmom
  rw [hXe, hYe]
  have hm0 : 0 ≤ ∫ ω, ‖hX.mk X ω‖ ^ 2 ∂P + ∫ ω, ‖hY.mk Y ω‖ ^ 2 ∂P :=
    add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
  refine wassersteinE_one_le_of_dual P _ _ hX.measurable_mk hY.measurable_mk hX2' hY2' _
    fun h hh => ?_
  have := dc2_real (a := ∫ ω, h (hX.mk X ω) ∂P - ∫ ω, h (hY.mk Y ω) ∂P)
    (Real.sqrt_nonneg p) hm0 hmom hς (smoothDist_nonneg 2 _ _)
    (fun ε R hε hR => dc2_test_bound P _ _ hX.measurable_mk hY.measurable_mk hX2' hY2' hh hε hR)
  linarith

end GaussSmoothing

/-- Lemma A.26 `M:B:lem:dc2-to-w1` (source lines 10704-10710): for random vectors in `ℝ^p`
with `E|X|² + E|Y|² ≤ ς²` and `𝖽 = d_2(Law X, Law Y)`,
`W_1(Law X, Law Y) ≤ C(√p + ς) 𝖽^{1/2} + C 𝖽` for a universal constant `C`. The scale `ς` is
nonnegative in the source (it bounds `(E|X|² + E|Y|²)^{1/2}`); without `0 ≤ ς` the statement is
false (`docs/ISSUES.md` §E). -/
theorem dc2_to_w1 : ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ^p)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P) (ς : ℝ) (hς : 0 ≤ ς)
    (hmom : momentNorm P 2 X + momentNorm P 2 Y ≤ ς ^ 2),
    wassersteinE 1 (law P X) (law P Y) ≤
      ENNReal.ofReal (C * (Real.sqrt p + ς) * Real.sqrt (smoothDist 2 (law P X) (law P Y)) +
        C * smoothDist 2 (law P X) (law P Y)) :=
  dc2_to_w1_of_nonneg

/-- The trace (Schatten-1) norm of a `p × p` real matrix, `‖Q‖_{S_1} = tr (QᵀQ)^{1/2}`,
represented through the variational formula
`‖Q‖_{S_1} = sup { tr(QᵀU) : U orthogonal }`. -/
def traceNormMatrix (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ⨆ U : Matrix.orthogonalGroup (Fin p) ℝ, Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ))

/-! #### Helpers for the Gaussian covariance comparison (work package METR-03) -/

section GaussianCovHelpers

open ProbabilityTheory
open scoped Convolution


lemma traceNormMatrix_bddAbove (Q : Matrix (Fin p) (Fin p) ℝ) :
    BddAbove (Set.range fun U : Matrix.orthogonalGroup (Fin p) ℝ =>
      Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ))) := by
  refine ⟨∑ i, ∑ j, |Q j i|, ?_⟩
  rintro _ ⟨U, rfl⟩
  have hU : ∀ i j, |(U : Matrix (Fin p) (Fin p) ℝ) i j| ≤ 1 := by
    intro i j
    have := entry_norm_bound_of_unitary U.2 i j
    simpa using this
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  calc Q j i * (U : Matrix (Fin p) (Fin p) ℝ) j i ≤ |Q j i * (U : Matrix (Fin p) (Fin p) ℝ) j i| := le_abs_self _
    _ = |Q j i| * |(U : Matrix (Fin p) (Fin p) ℝ) j i| := abs_mul _ _
    _ ≤ |Q j i| * 1 := by gcongr; exact hU j i
    _ = |Q j i| := mul_one _

lemma le_traceNormMatrix (Q : Matrix (Fin p) (Fin p) ℝ) (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ)) ≤ traceNormMatrix Q :=
  le_ciSup (f := fun U : Matrix.orthogonalGroup (Fin p) ℝ =>
      Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ))) (traceNormMatrix_bddAbove Q) U

lemma traceNormMatrix_nonneg (Q : Matrix (Fin p) (Fin p) ℝ) : 0 ≤ traceNormMatrix Q := by
  have h1 := le_traceNormMatrix Q 1
  have hm : (-1 : Matrix (Fin p) (Fin p) ℝ) ∈ Matrix.orthogonalGroup (Fin p) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  have h2 := le_traceNormMatrix Q ⟨-1, hm⟩
  simp at h1 h2
  linarith

lemma exists_psd_split (Δ : Matrix (Fin p) (Fin p) ℝ) (hΔ : Δ.IsHermitian) :
    ∃ Dp Dm : Matrix (Fin p) (Fin p) ℝ, Dp.PosSemidef ∧ Dm.PosSemidef ∧ Δ = Dp - Dm ∧
      Matrix.trace Dp + Matrix.trace Dm ≤ traceNormMatrix Δ := by
  classical
  set Uu := hΔ.eigenvectorUnitary with hUu
  set W : Matrix (Fin p) (Fin p) ℝ := (Uu : Matrix (Fin p) (Fin p) ℝ) with hW
  set d := hΔ.eigenvalues with hd
  have hWW : star W * W = 1 := by
    have := Uu.2.1
    simpa [hW] using this
  have hspec : Δ = W * Matrix.diagonal d * star W := by
    have := hΔ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hW, hd] using this
  have hWW' : W * star W = 1 := by
    have := Uu.2.2
    simpa [hW] using this
  have hpsd : ∀ f : Fin p → ℝ, (∀ i, 0 ≤ f i) → (W * Matrix.diagonal f * star W).PosSemidef := by
    intro f hf
    have h1 := (Matrix.posSemidef_diagonal_iff.2 hf).conjTranspose_mul_mul_same (star W)
    simpa [Matrix.star_eq_conjTranspose] using h1
  have htr : ∀ f : Fin p → ℝ, Matrix.trace (W * Matrix.diagonal f * star W) = ∑ i, f i := by
    intro f
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWW]
    simp [Matrix.trace]
  refine ⟨W * Matrix.diagonal (fun i => max (d i) 0) * star W,
    W * Matrix.diagonal (fun i => max (-d i) 0) * star W,
    hpsd _ (fun i => le_max_right _ _), hpsd _ (fun i => le_max_right _ _), ?_, ?_⟩
  · have e : Matrix.diagonal d = Matrix.diagonal (fun i => max (d i) 0) -
        Matrix.diagonal (fun i => max (-d i) 0) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.diagonal_apply]
      split_ifs with h
      · rcases le_total 0 (d i) with h' | h'
        · rw [max_eq_left h', max_eq_right (by linarith)]; ring
        · rw [max_eq_right h', max_eq_left (by linarith)]; ring
      · simp
    rw [hspec, ← Matrix.sub_mul, ← Matrix.mul_sub, ← e]
  · rw [htr, htr, ← Finset.sum_add_distrib]
    -- the orthogonal matrix
    set s : Fin p → ℝ := fun i => if 0 ≤ d i then 1 else -1 with hs
    have hss : ∀ i, s i * s i = 1 := fun i => by
      by_cases h : 0 ≤ d i <;> simp [hs, h]
    have hV : W * Matrix.diagonal s * star W ∈ Matrix.orthogonalGroup (Fin p) ℝ := by
      rw [Matrix.mem_unitaryGroup_iff']
      have h1 : star (W * Matrix.diagonal s * star W) = W * Matrix.diagonal s * star W := by
        rw [star_mul, star_mul, star_star, Matrix.star_eq_conjTranspose (Matrix.diagonal s)]
        simp [Matrix.mul_assoc]
      rw [h1]
      calc W * Matrix.diagonal s * star W * (W * Matrix.diagonal s * star W)
          = W * (Matrix.diagonal s * (star W * W) * Matrix.diagonal s) * star W := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hWW, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
            have : Matrix.diagonal (fun i => s i * s i) = (1 : Matrix (Fin p) (Fin p) ℝ) := by
              simp_rw [hss]; exact Matrix.diagonal_one
            rw [this, Matrix.mul_one, hWW']
    have hle := le_traceNormMatrix Δ ⟨_, hV⟩
    refine le_trans (le_of_eq ?_) hle
    have hΔt : Δ.transpose = Δ := by
      have := hΔ.eq; rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    simp only [hΔt]
    have e : Δ * (W * Matrix.diagonal s * star W) = W * Matrix.diagonal (fun i => d i * s i) * star W := by
      rw [hspec, ← Matrix.diagonal_mul_diagonal]
      calc W * Matrix.diagonal d * star W * (W * Matrix.diagonal s * star W)
          = W * Matrix.diagonal d * (star W * W) * Matrix.diagonal s * star W := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hWW, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, htr]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 0 ≤ d i
    · simp [hs, h, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    · have h : d i < 0 := not_le.1 h
      simp [hs, not_le.2 h, max_eq_right h.le, max_eq_left (neg_nonneg.2 h.le)]


lemma norm_fderiv_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M) (x y : E) :
    ‖fderiv ℝ h y - fderiv ℝ h x‖ ≤ M * ‖y - x‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ h) (s := Set.univ)
    (fun z _ => (hd.differentiable one_ne_zero) z) (fun z _ => ?_) convex_univ trivial trivial
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := h) (x := z) (n := 1)
  rw [norm_iteratedFDeriv_one] at this
  rw [this]; exact hM z

lemma taylor_two_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M) (x w : E) :
    |h (x + w) - h x - fderiv ℝ h x w| ≤ M / 2 * ‖w‖ ^ 2 := by
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  set φ : ℝ → ℝ := fun t => h (x + t • w) - h x - t * fderiv ℝ h x w with hφ
  have hφd : ∀ t, HasDerivAt φ (fderiv ℝ h (x + t • w) w - fderiv ℝ h x w) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add x
    have h2 := (hdiff (x + t • w)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * fderiv ℝ h x w) (fderiv ℝ h x w) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ h x w)
    exact (h2.sub_const (h x)).sub h3
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := φ) (a := 0) (b := 1)
    (f' := fun t => fderiv ℝ h (x + t • w) w - fderiv ℝ h x w)
    (fun t _ => (hφd t).continuousAt.continuousWithinAt)
    (fun t _ => (hφd t).hasDerivWithinAt)
    (B := fun t => M * ‖w‖ ^ 2 * (t ^ 2 / 2)) (B' := fun t => M * ‖w‖ ^ 2 * t)
    (by simp [hφ])
    (by fun_prop)
    (fun t _ => by
      have := ((hasDerivAt_pow 2 t).div_const 2).const_mul (M * ‖w‖ ^ 2)
      convert this.hasDerivWithinAt using 1
      norm_num)
    (fun t ht => by
      have h1 := norm_fderiv_sub_le hh hM x (x + t • w)
      have h2 : ‖fderiv ℝ h (x + t • w) w - fderiv ℝ h x w‖ ≤
          ‖fderiv ℝ h (x + t • w) - fderiv ℝ h x‖ * ‖w‖ := by
        rw [← sub_apply]; exact ContinuousLinearMap.le_opNorm _ _
      have h3 : ‖(x + t • w) - x‖ = t * ‖w‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      rw [h3] at h1
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      calc _ ≤ _ := h2
        _ ≤ M * (t * ‖w‖) * ‖w‖ := by gcongr
        _ = _ := by ring)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  have e : φ 1 = h (x + w) - h x - fderiv ℝ h x w := by simp [hφ]
  rw [e, Real.norm_eq_abs] at key
  calc _ ≤ _ := key
    _ = _ := by ring

lemma mvGaussian_conv {A B : Matrix (Fin p) (Fin p) ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (multivariateGaussian 0 A) ∗ (multivariateGaussian 0 B) = multivariateGaussian 0 (A + B) := by
  have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) A) := inferInstance
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hA, charFun_multivariateGaussian hB,
    charFun_multivariateGaussian (hA.add hB), ← Complex.exp_add]
  congr 1
  simp [Matrix.add_mulVec, dotProduct_add]
  ring

section step
variable {h : EuclideanSpace ℝ (Fin p) → ℝ}

lemma integrable_shift_gaussian (hh : ContDiff ℝ 2 h) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M) (γ : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure γ] [IsGaussian γ] (x : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun y => h (x + y)) γ := by
  have hm2 : MemLp id 2 γ := IsGaussian.memLp_two_id
  have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin p) => ‖y‖) γ := (hm2.integrable (by norm_num)).norm
  have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ ^ 2) γ := hm2.norm.integrable_sq
  have hg : Integrable (fun y : EuclideanSpace ℝ (Fin p) =>
      |h x| + ‖fderiv ℝ h x‖ * ‖y‖ + M / 2 * ‖y‖ ^ 2) γ :=
    ((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _)
  refine Integrable.mono' hg (hh.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  have := taylor_two_bound hh hM x y
  have h3 : |fderiv ℝ h x y| ≤ ‖fderiv ℝ h x‖ * ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact (fderiv ℝ h x).le_opNorm y
  rw [Real.norm_eq_abs]
  calc |h (x + y)| = |(h (x + y) - h x - fderiv ℝ h x y) + h x + fderiv ℝ h x y| := by ring_nf
    _ ≤ |h (x + y) - h x - fderiv ℝ h x y| + |h x| + |fderiv ℝ h x y| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

lemma gaussian_step {R Δ : Matrix (Fin p) (Fin p) ℝ} (hR : R.PosSemidef) (hΔ : Δ.PosSemidef)
    (hh : ContDiff ℝ 2 h) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M) :
    |∫ x, h x ∂(multivariateGaussian 0 (R + Δ)) - ∫ x, h x ∂(multivariateGaussian 0 R)| ≤
      M / 2 * Matrix.trace Δ := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) R with hμ
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Δ with hν
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hconv : multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (R + Δ) = μ ∗ ν :=
    (mvGaussian_conv hR hΔ).symm
  have hint0 : Integrable h (μ ∗ ν) := by
    rw [← hconv]
    simpa using integrable_shift_gaussian hh hM (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (R + Δ)) 0
  have hIμ : Integrable h μ := by simpa using integrable_shift_gaussian hh hM μ 0
  rw [hconv, integral_conv hint0]
  have hpt : ∀ x, ‖∫ y, h (x + y) ∂ν - h x‖ ≤ M / 2 * Matrix.trace Δ := by
    intro x
    have hmem : MemLp id 2 ν := IsGaussian.memLp_two_id
    have hy : Integrable (fun y : EuclideanSpace ℝ (Fin p) => y) ν := hmem.integrable (by norm_num)
    have hsq : Integrable (fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ ^ 2) ν := hmem.norm.integrable_sq
    have hlin : ∫ y, fderiv ℝ h x y ∂ν = 0 := by
      rw [ContinuousLinearMap.integral_comp_id_comm hy (fderiv ℝ h x)]
      simp [hν]
    have hi1 := integrable_shift_gaussian hh hM ν x
    have hi2 : Integrable (fun y => fderiv ℝ h x y) ν :=
      (fderiv ℝ h x).integrable_comp hy
    have : ∫ y, h (x + y) ∂ν - h x = ∫ y, (h (x + y) - h x - fderiv ℝ h x y) ∂ν := by
      rw [integral_sub (f := fun y => h (x + y) - h x) (g := fun y => fderiv ℝ h x y)
        (hi1.sub (integrable_const _)) hi2, integral_sub (f := fun y => h (x + y))
        (g := fun _ => h x) hi1 (integrable_const _), hlin]
      simp
    rw [this]
    calc _ ≤ ∫ y, M / 2 * ‖y‖ ^ 2 ∂ν := by
          refine norm_integral_le_of_norm_le (hsq.const_mul _) (ae_of_all _ fun y => ?_)
          rw [Real.norm_eq_abs]; exact taylor_two_bound hh hM x y
      _ = M / 2 * Matrix.trace Δ := by
          rw [integral_const_mul, hν, integral_norm_sq_mvGaussian hΔ]
  have hint_outer : Integrable (fun x => ∫ y, h (x + y) ∂ν) μ := by
    have hprod : Integrable (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
        h (z.1 + z.2)) (μ.prod ν) := by
      have := hint0
      unfold Measure.conv at this
      exact (integrable_map_measure (hh.continuous.aestronglyMeasurable) (by fun_prop)).1 this
    exact hprod.integral_prod_left
  have hμ' : ∫ x, h x ∂μ = ∫ x, ∫ y, h x ∂ν ∂μ := by simp
  rw [hμ', ← integral_sub hint_outer (by simpa using hIμ)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := M / 2 * Matrix.trace Δ)
    (f := fun x => ∫ y, h (x + y) ∂ν - ∫ y, h x ∂ν) (ae_of_all _ fun x => by simpa using hpt x)
  simpa using this
end step

end GaussianCovHelpers

/-- Lemma A.31 `M:B:newprob:gaussian-covariance` (source lines 11003-11014): for symmetric
nonnegative `Q, Q'` and `h ∈ C_b^2(ℝ^p)`,
`|∫ h dN(0,Q) - ∫ h dN(0,Q')| ≤ ½ sup_x ‖D²h(x)‖_op ‖Q - Q'‖_{S_1}`. -/
theorem gaussian_covariance_comparison (Q Q' : Matrix (Fin p) (Fin p) ℝ)
    (hQ : Q.PosSemidef) (hQ' : Q'.PosSemidef) (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h)
    (hbdd : BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 2 h x‖)) :
    |∫ x, h x ∂(ProbabilityTheory.multivariateGaussian 0 Q) -
        ∫ x, h x ∂(ProbabilityTheory.multivariateGaussian 0 Q')| ≤
      (1 / 2) * (⨆ x, ‖iteratedFDeriv ℝ 2 h x‖) * traceNormMatrix (Q - Q') := by
  -- Route: split `Q - Q' = D₊ - D₋` spectrally, so that `N(Q + D₋) = N(Q) * N(D₋)` and
  -- `N(Q' + D₊) = N(Q') * N(D₊)` are the same measure, and bound each convolution step by the
  -- second-order Taylor remainder (instead of interpolating in the covariance).
  set M : ℝ := ⨆ x, ‖iteratedFDeriv ℝ 2 h x‖ with hMdef
  have hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M := fun x => le_ciSup hbdd x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨Dp, Dm, hDp, hDm, hsplit, htr⟩ := exists_psd_split (Q - Q') (hQ.1.sub hQ'.1)
  have hR : Q + Dm = Q' + Dp :=
    calc Q + Dm = (Q - Q') + Dm + Q' := by abel
      _ = (Dp - Dm) + Dm + Q' := by rw [hsplit]
      _ = Q' + Dp := by abel
  have h1 := gaussian_step hQ hDm hh hM
  have h2 := gaussian_step hQ' hDp hh hM
  rw [hR] at h1
  have hT : Matrix.trace Dm + Matrix.trace Dp ≤ traceNormMatrix (Q - Q') := by linarith
  have h3 := mul_le_mul_of_nonneg_left hT hM0
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith

/-- Lemma A.31, consequence: `d_3(N(0,Q), N(0,Q')) ≤ ½ ‖Q - Q'‖_{S_1}`. -/
theorem smoothDist_gaussian_covariance (Q Q' : Matrix (Fin p) (Fin p) ℝ)
    (hQ : Q.PosSemidef) (hQ' : Q'.PosSemidef) :
    smoothDist 3 (ProbabilityTheory.multivariateGaussian 0 Q)
        (ProbabilityTheory.multivariateGaussian 0 Q') ≤
      (1 / 2) * traceNormMatrix (Q - Q') := by
  have hT := traceNormMatrix_nonneg (Q - Q')
  have : Nonempty (CbUnitBall (EuclideanSpace ℝ (Fin p)) 3) := ⟨⟨0, zero_mem_cbUnitBall 3⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨hΦ, hb, hc⟩ := Φ.2
  have hΦ2 : ContDiff ℝ 2 Φ.1 := hΦ.of_le (by norm_num)
  have hb2 := hb 2 (by norm_num)
  have hsum : (⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖) ≤ 1 := by
    refine le_trans ?_ hc
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : EuclideanSpace ℝ (Fin p),
      ‖iteratedFDeriv ℝ j Φ.1 z‖) (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _)
      (by simp : 2 ∈ Finset.range (3 + 1))
  have := gaussian_covariance_comparison Q Q' hQ hQ' Φ.1 hΦ2 hb2
  refine this.trans ?_
  have h0 : 0 ≤ ⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  nlinarith

/-- The covariance matrix `Var(S)` of a random vector. -/
def covMatrix {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → ℝ^p) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => ProbabilityTheory.covariance (fun ω => S ω i) (fun ω => S ω j) P

section YurinskiiCoupling

open ProbabilityTheory
open scoped Real

local notation "𝔼" => EuclideanSpace ℝ (Fin p)

lemma kernel_hess_apply (b : ℝ) (z v : 𝔼) :
    fderiv ℝ (fderiv ℝ (gaussKernel p b)) z v v =
      gaussKernel p b z * (4 * b ^ 2 * (inner ℝ z v) ^ 2 - 2 * b * ‖v‖ ^ 2) := by
  rw [(hasFDerivAt_fderiv_gaussKernel b z).fderiv]
  simp [ipCLM_apply, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v z]
  ring

lemma integral_kernel_inner_sq {ε : ℝ} (hε : 0 < ε) (v : 𝔼) :
    ∫ z, gaussKernel p (1 / (2 * ε ^ 2)) z * (inner ℝ z v) ^ 2 = ε ^ 2 * ‖v‖ ^ 2 := by
  rw [integral_kernel_eq_mvG hε (fun z => (inner ℝ z v) ^ 2)]
  have hpsd : (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by positivity)
  set γ := multivariateGaussian (0 : 𝔼) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))
  have e : ∀ z : 𝔼, (inner ℝ z v) ^ 2 = ∑ c, ∑ d, (v c * v d) * (z c * z d) := by
    intro z
    have : inner ℝ z v = ∑ c, z c * v c := by
      simp [PiLp.inner_apply, mul_comm]
    rw [this, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  simp_rw [e]
  have hi : ∀ c d : Fin p, Integrable (fun z : 𝔼 => (v c * v d) * (z c * z d)) γ := fun c d =>
    ((Yurinskii.memLp_coord (Q := ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) c 2 (by simp)).integrable_mul
      (Yurinskii.memLp_coord (Q := ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) d 2 (by simp))).const_mul _
  rw [integral_finsetSum _ (fun c _ => integrable_finset_sum _ (fun d _ => hi c d))]
  have : ∀ c, ∫ z, ∑ d, (v c * v d) * (z c * z d) ∂γ = ∑ d, (v c * v d) * (if c = d then ε ^ 2 else 0) := by
    intro c
    rw [integral_finsetSum _ (fun d _ => hi c d)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, Yurinskii.integral_coord_mul hpsd]
    simp [Matrix.one_apply]
  simp_rw [this]
  simp [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma integrable_of_gauss_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : 𝔼 → F} (hg : Continuous g) {C a : ℝ} (ha : 0 < a)
    (hb : ∀ z, ‖g z‖ ≤ C * Real.exp (-a * ‖z‖ ^ 2)) : Integrable g :=
  ((integrable_exp_neg_norm_sq (p := p) ha).const_mul C).mono' hg.aestronglyMeasurable
    (ae_of_all _ hb)

lemma continuous_hess_kernel (b : ℝ) :
    Continuous (fderiv ℝ (fderiv ℝ (gaussKernel p b))) :=
  (((contDiff_gaussKernel b).fderiv_right le_top).continuous_fderiv one_ne_zero)

/-- the evaluation `T ↦ T v v` -/
def evVV (v : 𝔼) : (𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ (𝔼 →L[ℝ] ℝ) v)

lemma evVV_apply (v : 𝔼) (T : 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) : evVV v T = T v v := rfl

lemma exists_hess_bound {b : ℝ} (hb : 0 < b) : ∃ C : ℝ, ∀ z : 𝔼,
    ‖fderiv ℝ (fderiv ℝ (gaussKernel p b)) z‖ ≤ C * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
  obtain ⟨C, hC⟩ := kernel_bounds (p := p) hb
  exact ⟨C, fun z => (hC z).2.2⟩

lemma integrable_ev {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F →L[ℝ] ℝ)
    {g : 𝔼 → F} (hg : Integrable g) : Integrable (fun z => L (g z)) := L.integrable_comp hg

lemma integrable_hess_kernel_apply {b : ℝ} (hb : 0 < b) (v : 𝔼) :
    Integrable (fun z : 𝔼 => fderiv ℝ (fderiv ℝ (gaussKernel p b)) z v v) := by
  obtain ⟨C, hC⟩ := exists_hess_bound (p := p) hb
  exact integrable_ev (F := 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) (evVV v) (integrable_of_gauss_bound (F := 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ)
    (continuous_hess_kernel b) (a := b / 2) (by positivity) (fun z => hC z))

lemma conv_ev_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : F →L[ℝ] ℝ) {g : 𝔼 → F} (hg : Continuous g) (hgi : Integrable g)
    {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, |f y| ≤ R) (x : 𝔼) :
    L (∫ y, f y • g (x - y)) = ∫ z, f (x - z) * L (g z) := by
  have hint : Integrable (fun y => f y • g (x - y)) := by
    have := (integrable_bdd_smul (f := fun z => f (x - z)) (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _)
      hg hgi).comp_sub_left x
    simpa using this
  rw [← L.integral_comp_comm hint]
  have := conv_comm f (fun z => L (g z)) x
  simpa [smul_eq_mul] using this

lemma hess_gsmooth_formula {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (x v : 𝔼) :
    fderiv ℝ (fderiv ℝ (gsmooth ε f)) x v v =
      ∫ z, f (x - z) * (fderiv ℝ (fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2)))) z v v) := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  have e1 : fderiv ℝ (fderiv ℝ (gsmooth ε f)) x =
      ∫ y, f y • fderiv ℝ (fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2)))) (x - y) := by
    rw [fderiv_gsmooth hε hf hR]; exact (gsmooth1_hasFDerivAt hε hf hR x).fderiv
  rw [e1, ← evVV_apply]
  obtain ⟨C, hC⟩ := exists_hess_bound (p := p) hb
  exact conv_ev_comm (evVV v) (continuous_hess_kernel _)
    (integrable_of_gauss_bound (F := 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) (continuous_hess_kernel _)
      (a := (1 / (2 * ε ^ 2)) / 2) (by positivity) (fun z => hC z)) hf hR x

lemma integral_abs_hess_kernel_le {ε : ℝ} (hε : 0 < ε) (v : 𝔼) :
    ∫ z, |fderiv ℝ (fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2)))) z v v| ≤ 2 / ε ^ 2 * ‖v‖ ^ 2 := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  set b := 1 / (2 * ε ^ 2) with hbd
  set κ := gaussKernel p b
  have hκi : Integrable κ := integrable_gaussKernel hb
  have hhi : Integrable (fun z : 𝔼 => fderiv ℝ (fderiv ℝ κ) z v v) :=
    integrable_hess_kernel_apply hb v
  have hi2 : Integrable (fun z : 𝔼 => κ z * (inner ℝ z v) ^ 2) := by
    have := (hhi.add (hκi.const_mul (2 * b * ‖v‖ ^ 2))).const_mul (1 / (4 * b ^ 2))
    refine this.congr (ae_of_all _ fun z => ?_)
    have hk : fderiv ℝ (fderiv ℝ κ) z v v =
        κ z * (4 * b ^ 2 * (inner ℝ z v) ^ 2 - 2 * b * ‖v‖ ^ 2) := kernel_hess_apply b z v
    simp only [Pi.add_apply, hk]
    field_simp
    ring
  have hm : ∀ z, |fderiv ℝ (fderiv ℝ κ) z v v| ≤
      κ z * (4 * b ^ 2 * (inner ℝ z v) ^ 2) + κ z * (2 * b * ‖v‖ ^ 2) := by
    intro z
    have hk : fderiv ℝ (fderiv ℝ κ) z v v =
        κ z * (4 * b ^ 2 * (inner ℝ z v) ^ 2 - 2 * b * ‖v‖ ^ 2) := kernel_hess_apply b z v
    rw [hk]
    have h0 := (gaussKernel_pos hb z).le
    have h1 : 0 ≤ 4 * b ^ 2 * (inner ℝ z v) ^ 2 := by positivity
    have h2 : 0 ≤ 2 * b * ‖v‖ ^ 2 := by positivity
    have h0' : 0 ≤ κ z := h0
    rw [abs_mul, abs_of_nonneg h0', ← mul_add]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by rw [abs_of_nonneg h1, abs_of_nonneg h2])) h0'
  have hI : Integrable (fun z : 𝔼 => κ z * (4 * b ^ 2 * (inner ℝ z v) ^ 2) + κ z * (2 * b * ‖v‖ ^ 2)) := by
    refine Integrable.add ?_ ?_
    · refine (hi2.const_mul (4 * b ^ 2)).congr (ae_of_all _ fun z => ?_); simp only; ring
    · exact hκi.mul_const _
  refine (integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hI (ae_of_all _ hm)).trans ?_
  rw [integral_add (by refine (hi2.const_mul (4 * b ^ 2)).congr (ae_of_all _ fun z => ?_); simp only; ring)
    (hκi.mul_const _)]
  have e1 : ∫ z, κ z * (4 * b ^ 2 * (inner ℝ z v) ^ 2) = 4 * b ^ 2 * (ε ^ 2 * ‖v‖ ^ 2) := by
    rw [← integral_kernel_inner_sq hε v, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_); simp only [κ]; ring
  rw [e1, integral_mul_const, integral_gaussKernel hb, one_mul]
  apply le_of_eq
  rw [hbd]; field_simp; ring

lemma hess_gsmooth_lip {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) {c : ℝ} (hc : 0 ≤ c) (hL : ∀ x y, |f x - f y| ≤ c * ‖x - y‖)
    (x x' v : 𝔼) :
    |fderiv ℝ (fderiv ℝ (gsmooth ε f)) x v v - fderiv ℝ (fderiv ℝ (gsmooth ε f)) x' v v| ≤
      c * (2 / ε ^ 2) * ‖x - x'‖ * ‖v‖ ^ 2 := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  set h : 𝔼 → ℝ := fun z => fderiv ℝ (fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2)))) z v v with hhd
  have hhi : Integrable h := integrable_hess_kernel_apply hb v
  have hhc : Continuous h := (evVV v).continuous.comp (continuous_hess_kernel _)
  have hi : ∀ w : 𝔼, Integrable (fun z => f (w - z) * h z) := fun w => by
    simpa [smul_eq_mul] using integrable_bdd_smul (f := fun z => f (w - z))
      (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _) hhc hhi
  rw [hess_gsmooth_formula hε hf hR x v, hess_gsmooth_formula hε hf hR x' v, ← integral_sub (hi x) (hi x')]
  rw [← Real.norm_eq_abs]
  have hbd := integral_abs_hess_kernel_le hε v
  have key : ‖∫ z, (f (x - z) * h z - f (x' - z) * h z)‖ ≤ ∫ z, c * ‖x - x'‖ * |h z| := by
    refine norm_integral_le_of_norm_le (hhi.abs.const_mul _) (ae_of_all _ fun z => ?_)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := hL (x - z) (x' - z)
    simpa using this
  refine key.trans ?_
  rw [integral_const_mul]
  calc c * ‖x - x'‖ * ∫ z, |h z| ≤ c * ‖x - x'‖ * (2 / ε ^ 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = _ := by ring

/-! ### The cutoff function and the set inequality -/

/-- `f₁(x) = max 0 (δ - d(x, A^δ))`, a 1-Lipschitz bump. -/
def f1 (δ : ℝ) (A : Set 𝔼) : 𝔼 → ℝ :=
  fun x => max 0 (δ - Metric.infDist x (Metric.cthickening δ A))

lemma f1_nonneg (δ : ℝ) (A : Set 𝔼) (x : 𝔼) : 0 ≤ f1 δ A x := le_max_left _ _

lemma f1_le (δ : ℝ) (A : Set 𝔼) (x : 𝔼) (hδ : 0 ≤ δ) : f1 δ A x ≤ δ := by
  unfold f1
  refine max_le hδ ?_
  linarith [Metric.infDist_nonneg (x := x) (s := Metric.cthickening δ A)]

lemma abs_f1_le (δ : ℝ) (A : Set 𝔼) (hδ : 0 ≤ δ) (x : 𝔼) : |f1 δ A x| ≤ δ := by
  rw [abs_of_nonneg (f1_nonneg δ A x)]; exact f1_le δ A x hδ

lemma f1_lip (δ : ℝ) (A : Set 𝔼) (x y : 𝔼) : |f1 δ A x - f1 δ A y| ≤ 1 * ‖x - y‖ := by
  set dx := Metric.infDist x (Metric.cthickening δ A)
  set dy := Metric.infDist y (Metric.cthickening δ A)
  have h1 := abs_max_sub_max_le_abs (δ - dx) (δ - dy) 0
  rw [max_comm (δ - dx) 0, max_comm (δ - dy) 0] at h1
  have h2 := (Metric.lipschitz_infDist_pt (Metric.cthickening δ A)).dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm] at h2
  have e : (δ - dx) - (δ - dy) = -(dx - dy) := by ring
  rw [e, abs_neg] at h1
  have h3 : |dx - dy| ≤ ‖x - y‖ := by simpa using h2
  exact (show |f1 δ A x - f1 δ A y| ≤ |dx - dy| from h1).trans (by simpa using h3)

lemma f1_lipschitz (δ : ℝ) (A : Set 𝔼) : LipschitzWith 1 (f1 δ A) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, dist_eq_norm]; simpa using f1_lip δ A x y

lemma continuous_f1 (δ : ℝ) (A : Set 𝔼) : Continuous (f1 δ A) := (f1_lipschitz δ A).continuous

lemma f1_of_mem {δ : ℝ} (hδ : 0 ≤ δ) {A : Set 𝔼} {x : 𝔼} (h : x ∈ Metric.cthickening δ A) :
    f1 δ A x = δ := by
  unfold f1
  rw [Metric.infDist_zero_of_mem h, sub_zero]
  exact max_eq_right hδ

lemma mem_cthickening_iff_infDist' {A : Set 𝔼} (hA : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (x : 𝔼) :
    x ∈ Metric.cthickening r A ↔ Metric.infDist x A ≤ r := by
  rw [Metric.mem_cthickening_iff, Metric.infDist,
    ENNReal.le_ofReal_iff_toReal_le (Metric.infEDist_ne_top hA) hr]

/-- If `‖z‖ ≤ δ` and `f₁(x - z) ≠ 0`, then `x ∈ A^{3δ}`. -/
lemma mem_cthickening_of_f1_ne {δ : ℝ} (hδ : 0 < δ) {A : Set 𝔼} (hA : A.Nonempty) {x z : 𝔼}
    (hz : ‖z‖ ≤ δ) (h : f1 δ A (x - z) ≠ 0) : x ∈ Metric.cthickening (3 * δ) A := by
  have hpos : 0 < f1 δ A (x - z) := lt_of_le_of_ne (f1_nonneg _ _ _) (Ne.symm h)
  unfold f1 at hpos
  have hlt : Metric.infDist (x - z) (Metric.cthickening δ A) < δ := by
    rcases lt_max_iff.1 hpos with h0 | h0
    · exact absurd h0 (lt_irrefl _)
    · linarith
  obtain ⟨a, ha, hda⟩ := (Metric.infDist_lt_iff (hA.mono (Metric.self_subset_cthickening A))).1 hlt
  have h1 : Metric.infDist a A ≤ δ := (mem_cthickening_iff_infDist' hA hδ.le a).1 ha
  rw [mem_cthickening_iff_infDist' hA (by positivity)]
  have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := a) (s := A)
  have h3 : dist x a ≤ dist x (x - z) + dist (x - z) a := dist_triangle _ _ _
  have h4 : dist x (x - z) = ‖z‖ := by rw [dist_eq_norm]; simp
  linarith


/-- indicator of `{‖z‖ > δ}` -/
def tailInd (δ : ℝ) (z : 𝔼) : ℝ := if δ < ‖z‖ then 1 else 0

lemma tailInd_nonneg (δ : ℝ) (z : 𝔼) : 0 ≤ tailInd δ z := by unfold tailInd; split_ifs <;> norm_num

lemma tailInd_le_one (δ : ℝ) (z : 𝔼) : tailInd δ z ≤ 1 := by unfold tailInd; split_ifs <;> norm_num

lemma measurable_tailInd (δ : ℝ) : Measurable (tailInd (p := p) δ) := by
  unfold tailInd
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
    measurable_const

/-- the Gaussian tail mass `P(‖σ G‖ > δ)` -/
def tailMass (p : ℕ) (δ σ : ℝ) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin p), tailInd δ z * gaussKernel p (1 / (2 * σ ^ 2)) z

lemma integrable_tail_kernel {b : ℝ} (hb : 0 < b) (δ : ℝ) :
    Integrable (fun z : 𝔼 => tailInd δ z * gaussKernel p b z) := by
  refine (integrable_gaussKernel (p := p) hb).mono'
    ((measurable_tailInd δ).mul (continuous_gaussKernel b).measurable).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [norm_mul, Real.norm_of_nonneg (tailInd_nonneg δ z),
    Real.norm_of_nonneg (gaussKernel_pos hb z).le]
  exact mul_le_of_le_one_left (gaussKernel_pos hb z).le (tailInd_le_one δ z)

lemma tailMass_nonneg (δ σ : ℝ) (hσ : 0 < σ) : 0 ≤ tailMass p δ σ :=
  integral_nonneg fun z => mul_nonneg (tailInd_nonneg δ z) (gaussKernel_pos (by positivity) z).le

lemma gsmooth_eq (σ : ℝ) (f : 𝔼 → ℝ) (x : 𝔼) :
    gsmooth σ f x = ∫ z, f (x - z) * gaussKernel p (1 / (2 * σ ^ 2)) z := by
  unfold gsmooth; rw [conv_comm]; simp [smul_eq_mul]

lemma integrable_f1_kernel {δ σ : ℝ} (hδ : 0 ≤ δ) (hσ : 0 < σ) (A : Set 𝔼) (x : 𝔼) :
    Integrable (fun z => f1 δ A (x - z) * gaussKernel p (1 / (2 * σ ^ 2)) z) := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  simpa [smul_eq_mul] using integrable_bdd_smul (f := fun z => f1 δ A (x - z))
    ((continuous_f1 δ A).comp (continuous_const.sub continuous_id)) (fun z => abs_f1_le δ A hδ _)
    (continuous_gaussKernel _) (integrable_gaussKernel hb)

lemma F1_ge {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) {A : Set 𝔼} {x : 𝔼} (hx : x ∈ A) :
    δ * (1 - tailMass p δ σ) ≤ gsmooth σ (f1 δ A) x := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  rw [gsmooth_eq]
  have hi1 := integrable_f1_kernel (p := p) hδ.le hσ A x
  have hi2 := integrable_tail_kernel (p := p) hb δ
  have hi3 := integrable_gaussKernel (p := p) hb
  have hle : ∀ z : 𝔼, δ * gaussKernel p (1 / (2 * σ ^ 2)) z ≤
      f1 δ A (x - z) * gaussKernel p (1 / (2 * σ ^ 2)) z +
        δ * (tailInd δ z * gaussKernel p (1 / (2 * σ ^ 2)) z) := by
    intro z
    have hk := (gaussKernel_pos (p := p) hb z).le
    by_cases hz : δ < ‖z‖
    · have : tailInd δ z = 1 := by simp [tailInd, hz]
      rw [this]
      nlinarith [mul_nonneg (f1_nonneg δ A (x - z)) hk]
    · have : tailInd δ z = 0 := by simp [tailInd, hz]
      have h1 : f1 δ A (x - z) = δ := by
        refine f1_of_mem hδ.le (Metric.mem_cthickening_of_dist_le _ x δ A hx ?_)
        rw [dist_eq_norm]; simpa using not_lt.1 hz
      rw [this, h1]; simp
  have := integral_mono (hi3.const_mul δ) (hi1.add (hi2.const_mul δ)) hle
  rw [integral_const_mul, integral_gaussKernel hb] at this
  simp only [Pi.add_apply] at this
  rw [integral_add hi1 (hi2.const_mul δ), integral_const_mul] at this
  unfold tailMass
  linarith

lemma F1_le {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) {A : Set 𝔼} (hA : A.Nonempty) {x : 𝔼}
    (hx : x ∉ Metric.cthickening (3 * δ) A) :
    gsmooth σ (f1 δ A) x ≤ δ * tailMass p δ σ := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  rw [gsmooth_eq]
  have hi1 := integrable_f1_kernel (p := p) hδ.le hσ A x
  have hi2 := integrable_tail_kernel (p := p) hb δ
  have hle : ∀ z : 𝔼, f1 δ A (x - z) * gaussKernel p (1 / (2 * σ ^ 2)) z ≤
      δ * (tailInd δ z * gaussKernel p (1 / (2 * σ ^ 2)) z) := by
    intro z
    have hk := (gaussKernel_pos (p := p) hb z).le
    by_cases hz : δ < ‖z‖
    · have : tailInd δ z = 1 := by simp [tailInd, hz]
      rw [this, one_mul]
      exact mul_le_mul_of_nonneg_right (f1_le δ A _ hδ.le) hk
    · have : tailInd δ z = 0 := by simp [tailInd, hz]
      have h1 : f1 δ A (x - z) = 0 := by
        by_contra hne
        exact hx (mem_cthickening_of_f1_ne hδ hA (not_lt.1 hz) hne)
      rw [this, h1]; simp
  have := integral_mono hi1 (hi2.const_mul δ) hle
  rw [integral_const_mul] at this
  exact this

lemma testFn_F1 {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (A : Set 𝔼) :
    Yurinskii.TestFn (2 / σ ^ 2) (gsmooth σ (f1 δ A)) where
  contDiff := contDiff_gsmooth hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le)
  K_nonneg := by positivity
  bdd0 := ⟨δ, abs_gsmooth_le hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le)⟩
  bdd1 := ⟨1, norm_fderiv_gsmooth_le hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le)
    (f1_lipschitz δ A)⟩
  bdd2 := ⟨Real.sqrt p / σ, norm_fderiv_fderiv_gsmooth_le hσ (continuous_f1 δ A)
    (abs_f1_le δ A hδ.le) (f1_lipschitz δ A)⟩
  hess := fun x y v => by
    have := hess_gsmooth_lip hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le) zero_le_one
      (f1_lip δ A) x y v
    simpa [mul_assoc] using this


lemma gsmooth_nonneg {σ : ℝ} (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ) (A : Set 𝔼) (x : 𝔼) :
    0 ≤ gsmooth σ (f1 δ A) x := by
  rw [gsmooth_eq]
  exact integral_nonneg fun z => mul_nonneg (f1_nonneg δ A _)
    (gaussKernel_pos (by positivity) z).le

lemma integrable_gsmooth_f1 {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (A : Set 𝔼)
    (m : Measure 𝔼) [IsProbabilityMeasure m] : Integrable (gsmooth σ (f1 δ A)) m :=
  (integrable_const δ).mono'
    (contDiff_gsmooth hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le)).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact abs_gsmooth_le hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le) x)

lemma set_ineq {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (μ ν : Measure 𝔼)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set 𝔼} (hAc : IsClosed A) (hA : A.Nonempty) {D : ℝ}
    (hD : |∫ x, gsmooth σ (f1 δ A) x ∂μ - ∫ x, gsmooth σ (f1 δ A) x ∂ν| ≤ D) :
    μ.real A ≤ ν.real (Metric.cthickening (3 * δ) A) + 2 * tailMass p δ σ + D / δ := by
  set F := gsmooth σ (f1 δ A) with hF
  set τ := tailMass p δ σ with hτ
  have hτ0 : 0 ≤ τ := tailMass_nonneg δ σ hσ
  have hA3 : IsClosed (Metric.cthickening (3 * δ) A) := Metric.isClosed_cthickening
  have h1 : ∀ x, δ * A.indicator (1 : 𝔼 → ℝ) x ≤ F x + δ * τ := by
    intro x
    by_cases hx : x ∈ A
    · have := F1_ge hδ hσ hx
      simp [Set.indicator_of_mem hx]; nlinarith
    · simp [Set.indicator_of_notMem hx]
      have := gsmooth_nonneg hσ hδ A x
      positivity
  have h2 : ∀ x, F x ≤ δ * (Metric.cthickening (3 * δ) A).indicator (1 : 𝔼 → ℝ) x + δ * τ := by
    intro x
    by_cases hx : x ∈ Metric.cthickening (3 * δ) A
    · have := abs_gsmooth_le hσ (continuous_f1 δ A) (abs_f1_le δ A hδ.le) x
      have := (le_abs_self (F x)).trans this
      simp [Set.indicator_of_mem hx]; nlinarith
    · simp [Set.indicator_of_notMem hx]
      exact F1_le hδ hσ hA hx
  have hint : ∀ (m : Measure 𝔼) [IsProbabilityMeasure m] (S : Set 𝔼), MeasurableSet S →
      Integrable (fun x => δ * S.indicator (1 : 𝔼 → ℝ) x) m := by
    intro m _ S hS
    exact ((integrable_const (1 : ℝ)).indicator hS).const_mul δ
  have e1 : ∀ (m : Measure 𝔼) (S : Set 𝔼), MeasurableSet S →
      ∫ x, δ * S.indicator (1 : 𝔼 → ℝ) x ∂m = δ * m.real S := by
    intro m S hS
    rw [integral_const_mul, integral_indicator_one hS]
  have i1 := integral_mono (hint μ A hAc.measurableSet)
    ((integrable_gsmooth_f1 hδ hσ A μ).add (integrable_const (δ * τ))) h1
  have i2 := integral_mono (integrable_gsmooth_f1 hδ hσ A ν)
    ((hint ν _ hA3.measurableSet).add (integrable_const (δ * τ))) h2
  simp only [Pi.add_apply] at i1 i2
  rw [e1 μ A hAc.measurableSet, integral_add (integrable_gsmooth_f1 hδ hσ A μ) (integrable_const _)] at i1
  rw [integral_add (hint ν _ hA3.measurableSet) (integrable_const _), e1 ν _ hA3.measurableSet] at i2
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at i1 i2
  have hD' := (abs_le.1 hD).2
  have key : δ * μ.real A ≤ δ * (ν.real (Metric.cthickening (3 * δ) A) + 2 * τ + D / δ) := by
    rw [mul_add, mul_add, mul_div_cancel₀ _ hδ.ne']
    linarith
  exact le_of_mul_le_mul_left key hδ


lemma tailMass_le {δ σ : ℝ} (hδ : 0 ≤ δ) (hσ : 0 < σ) :
    tailMass p δ σ ≤ (2 : ℝ) ^ ((p : ℝ) / 2) * Real.exp (-(δ ^ 2 / (4 * σ ^ 2))) := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  set b := 1 / (2 * σ ^ 2) with hbd
  set c := (b / π) ^ ((p : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hbd2 : b / 2 = 1 / (4 * σ ^ 2) := by rw [hbd]; field_simp; ring
  have hi : Integrable (fun z : 𝔼 => Real.exp (-(b / 2) * ‖z‖ ^ 2)) :=
    integrable_exp_neg_norm_sq (by positivity)
  have hle : ∀ z : 𝔼, tailInd δ z * gaussKernel p b z ≤
      (Real.exp (-(b / 2) * δ ^ 2) * c) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
    intro z
    by_cases hz : δ < ‖z‖
    · have : tailInd δ z = 1 := by simp [tailInd, hz]
      rw [this, one_mul]
      unfold gaussKernel
      rw [← hc]
      have h1 : Real.exp (-b * ‖z‖ ^ 2) ≤ Real.exp (-(b / 2) * δ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have : δ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith
        nlinarith
      calc c * Real.exp (-b * ‖z‖ ^ 2) ≤ c * (Real.exp (-(b / 2) * δ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 hc0
        _ = _ := by ring
    · have : tailInd δ z = 0 := by simp [tailInd, hz]
      rw [this, zero_mul]; positivity
  have := integral_mono_of_nonneg (ae_of_all _ fun z => mul_nonneg (tailInd_nonneg δ z)
    (gaussKernel_pos hb z).le) (hi.const_mul (Real.exp (-(b / 2) * δ ^ 2) * c)) (ae_of_all _ hle)
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_norm_sq (by positivity : 0 < b / 2), hc, hbd2]
  have e : (b / π) ^ ((p : ℝ) / 2) * (π / (1 / (4 * σ ^ 2))) ^ ((p : ℝ) / 2) = (2 : ℝ) ^ ((p : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; rw [hbd]; field_simp; norm_num
  have e2 : -(1 / (4 * σ ^ 2)) * δ ^ 2 = -(δ ^ 2 / (4 * σ ^ 2)) := by ring
  rw [e2, mul_assoc, e]; ring


lemma exists_sigma {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hB1 : B < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ^ 2 = δ ^ 2 / (2 * p + 4 * Real.log (1 / B)) ∧ tailMass p δ σ ≤ B := by
  set ℓ := Real.log (1 / B) with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by rw [lt_div_iff₀ hB]; linarith)
  have hpos : 0 < 2 * (p : ℝ) + 4 * ℓ := by positivity
  refine ⟨δ / Real.sqrt (2 * p + 4 * ℓ), by positivity, ?_, ?_⟩
  · rw [div_pow, Real.sq_sqrt hpos.le]
  · set σ := δ / Real.sqrt (2 * p + 4 * ℓ) with hσd
    have hσ : 0 < σ := by positivity
    have hs2 : σ ^ 2 = δ ^ 2 / (2 * p + 4 * ℓ) := by rw [hσd, div_pow, Real.sq_sqrt hpos.le]
    refine (tailMass_le hδ.le hσ).trans ?_
    have e : δ ^ 2 / (4 * σ ^ 2) = p / 2 + ℓ := by
      rw [hs2]; field_simp; ring
    rw [e, neg_add, Real.exp_add]
    have e2 : Real.exp (-ℓ) = B := by
      rw [hℓ, Real.exp_neg, Real.exp_log (by positivity)]; simp
    rw [e2]
    have h2 : (2 : ℝ) ^ ((p : ℝ) / 2) ≤ Real.exp ((p : ℝ) / 2) := by
      calc (2 : ℝ) ^ ((p : ℝ) / 2) ≤ (Real.exp 1) ^ ((p : ℝ) / 2) :=
            Real.rpow_le_rpow (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by positivity)
        _ = Real.exp ((p : ℝ) / 2) := by rw [← Real.exp_mul]; simp
    have h3 : (2 : ℝ) ^ ((p : ℝ) / 2) * Real.exp (-((p : ℝ) / 2)) ≤ 1 := by
      calc (2 : ℝ) ^ ((p : ℝ) / 2) * Real.exp (-((p : ℝ) / 2)) ≤
          Real.exp ((p : ℝ) / 2) * Real.exp (-((p : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    calc (2 : ℝ) ^ ((p : ℝ) / 2) * (Real.exp (-((p : ℝ) / 2)) * B)
        = ((2 : ℝ) ^ ((p : ℝ) / 2) * Real.exp (-((p : ℝ) / 2))) * B := by ring
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right h3 hB.le
      _ = B := one_mul B


lemma coupling_set_ineq (μ ν : Measure 𝔼) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ B Λ : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hB1 : B < 1) (hΛ : 0 ≤ Λ)
    (H : ∀ (K : ℝ) (f : 𝔼 → ℝ), Yurinskii.TestFn K f →
      |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ K * Λ)
    {A : Set 𝔼} (hAc : IsClosed A) :
    μ.real A ≤ ν.real (Metric.cthickening (3 * δ) A) + 2 * B +
      2 * (2 * p + 4 * Real.log (1 / B)) / δ ^ 3 * Λ := by
  have hℓ0 : 0 < Real.log (1 / B) := Real.log_pos (by rw [lt_div_iff₀ hB]; linarith)
  have hc : 0 ≤ 2 * (2 * (p : ℝ) + 4 * Real.log (1 / B)) / δ ^ 3 * Λ := by positivity
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [measureReal_empty]
    have := measureReal_nonneg (μ := ν) (s := Metric.cthickening (3 * δ) (∅ : Set 𝔼))
    linarith
  obtain ⟨σ, hσ, hs2, hτ⟩ := exists_sigma (p := p) hδ hB hB1
  have h := set_ineq hδ hσ μ ν hAc hA (D := 2 / σ ^ 2 * Λ) (H _ _ (testFn_F1 hδ hσ A))
  have e : 2 / σ ^ 2 * Λ / δ = 2 * (2 * p + 4 * Real.log (1 / B)) / δ ^ 3 * Λ := by
    rw [hs2]; field_simp
  linarith


lemma strassen_real (μ ν : Measure 𝔼) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (h : ∀ A : Set 𝔼, IsClosed A → μ.real A ≤ ν.real (Metric.cthickening r A) + ε) :
    ∃ cp : Measure (𝔼 × 𝔼), IsProbabilityMeasure cp ∧ cp.map Prod.fst = μ ∧ cp.map Prod.snd = ν ∧
      (cp {q | r < dist q.1 q.2}).toReal ≤ ε := by
  obtain ⟨cp, h1, h2, h3, h4⟩ := Yurinskii.strassen_coupling μ ν r ε hr hε (fun A hA => by
    have := h A hA
    calc μ A = ENNReal.ofReal (μ.real A) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (ν.real (Metric.cthickening r A) + ε) := ENNReal.ofReal_le_ofReal this
      _ = ν (Metric.cthickening r A) + ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_add measureReal_nonneg hε, ofReal_measureReal (measure_ne_top _ _)])
  exact ⟨cp, h1, h2, h3, ENNReal.toReal_le_of_le_ofReal hε h4⟩

theorem yur_measure {N : ℕ} (ρ : Fin N → Measure 𝔼) [∀ i, IsProbabilityMeasure (ρ i)]
    (h0ρ : ∀ i c, ∫ x, x c ∂(ρ i) = 0) (h3ρ : ∀ i, Integrable (fun x : 𝔼 => ‖x‖ ^ 3) (ρ i))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cp : Measure (𝔼 × 𝔼), IsProbabilityMeasure cp ∧
      cp.map Prod.fst = (Measure.pi ρ).map (fun q => ∑ i, q i) ∧
      cp.map Prod.snd = multivariateGaussian (0 : 𝔼) (∑ i, Yurinskii.momentMatrix (ρ i)) ∧
      (cp {q | 3 * δ < dist q.1 q.2}).toReal ≤
        (18 + 4 * Yurinskii.c4) * ((∑ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i)) * p * δ ^ (-3 : ℝ)) *
          (1 + |Real.log (1 / ((∑ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i)) * p * δ ^ (-3 : ℝ)))| / p) := by
  set μ := (Measure.pi ρ).map (fun q : Fin N → 𝔼 => ∑ i, q i) with hμ
  set ν := multivariateGaussian (0 : 𝔼) (∑ i, Yurinskii.momentMatrix (ρ i)) with hν
  set L := ∑ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i) with hLd
  have hsm : Measurable (fun q : Fin N → 𝔼 => ∑ i, q i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hsm.aemeasurable).2 inferInstance
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => integral_nonneg fun x => by positivity
  set Λ := (2 + Yurinskii.c4 / 2) * L with hΛd
  have hc4 := Yurinskii.c4_nonneg
  have hΛ : 0 ≤ Λ := by positivity
  have hH : ∀ (K : ℝ) (f : 𝔼 → ℝ), Yurinskii.TestFn K f →
      |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ K * Λ := fun K f hf =>
    Yurinskii.lindeberg_gauss hf ρ h0ρ h3ρ
  have hδ3 : 0 < δ ^ (-3 : ℝ) := by positivity
  by_cases hz : L = 0 ∨ p = 0
  · have hL : L = 0 := by
      rcases hz with h | h
      · exact h
      · subst h
        refine Finset.sum_eq_zero fun i _ => ?_
        have : ∀ x : EuclideanSpace ℝ (Fin 0), ‖x‖ ^ 3 = 0 := fun x => by
          rw [Subsingleton.elim x 0]; simp
        simp [this]
    have hΛ0 : Λ = 0 := by rw [hΛd, hL]; ring
    have hset : ∀ A : Set 𝔼, IsClosed A →
        μ.real A ≤ ν.real (Metric.cthickening (3 * δ) A) + 0 := by
      intro A hA
      refine le_of_forall_pos_le_add fun η hη => ?_
      set B := min (η / 2) (1 / 2) with hB
      have hB0 : 0 < B := lt_min (by positivity) (by norm_num)
      have hB1 : B < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have h2B : 2 * B ≤ η := by
        have := min_le_left (η / 2) (1 / 2); linarith
      have := coupling_set_ineq μ ν hδ hB0 hB1 hΛ hH hA
      rw [hΛ0, mul_zero, add_zero] at this
      linarith
    obtain ⟨cp, h1, h2, h3, h4⟩ := strassen_real μ ν (3 * δ) 0 (by positivity) le_rfl hset
    refine ⟨cp, h1, h2, h3, ?_⟩
    have hB0 : L * p * δ ^ (-3 : ℝ) = 0 := by
      rcases hz with h | h
      · rw [h]; simp
      · rw [h]; simp
    rw [hB0]; simpa using h4
  · push Not at hz
    obtain ⟨hLne, hpne⟩ := hz
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLne)
    have hppos : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hpne
    set B := L * p * δ ^ (-3 : ℝ) with hBd
    have hBpos : 0 < B := by positivity
    have hC0 : 1 ≤ 18 + 4 * Yurinskii.c4 := by linarith
    by_cases hB1 : B < 1
    · set ℓ := Real.log (1 / B) with hℓ
      have hℓ0 : 0 < ℓ := Real.log_pos (by rw [lt_div_iff₀ hBpos]; linarith)
      have hset : ∀ A : Set 𝔼, IsClosed A → μ.real A ≤ ν.real (Metric.cthickening (3 * δ) A) +
          (2 * B + 2 * (2 * p + 4 * ℓ) / δ ^ 3 * Λ) := by
        intro A hA
        have := coupling_set_ineq μ ν hδ hBpos hB1 hΛ hH hA
        linarith
      have hε0 : 0 ≤ 2 * B + 2 * (2 * p + 4 * ℓ) / δ ^ 3 * Λ := by positivity
      obtain ⟨cp, h1, h2, h3, h4⟩ := strassen_real μ ν (3 * δ) _ (by positivity) hε0 hset
      refine ⟨cp, h1, h2, h3, h4.trans ?_⟩
      have hLd3 : L / δ ^ 3 = B / p := by
        rw [hBd, Real.rpow_neg hδ.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
      have e1 : 2 * (2 * (p : ℝ) + 4 * ℓ) / δ ^ 3 * Λ =
          2 * (2 + Yurinskii.c4 / 2) * ((2 * p + 4 * ℓ) * (B / p)) := by
        rw [← hLd3, hΛd]; ring
      have e2 : (2 * (p : ℝ) + 4 * ℓ) * (B / p) = B * (2 + 4 * (ℓ / p)) := by
        field_simp
      rw [e1, e2, abs_of_pos hℓ0]
      have hx : 0 ≤ ℓ / p := by positivity
      have hBx : 0 ≤ B * (ℓ / p) := by positivity
      have : 2 * (2 + Yurinskii.c4 / 2) * (B * (2 + 4 * (ℓ / p))) ≤
          (16 + 4 * Yurinskii.c4) * (B * (1 + ℓ / p)) := by
        nlinarith [mul_nonneg hc4 hBpos.le, mul_nonneg hc4 hBx]
      have e4 : (18 + 4 * Yurinskii.c4) * B * (1 + ℓ / p) =
          2 * B * (1 + ℓ / p) + (16 + 4 * Yurinskii.c4) * (B * (1 + ℓ / p)) := by ring
      nlinarith [e4, this, hBx]
    · push Not at hB1
      obtain ⟨cp, h1⟩ : ∃ cp : Measure (𝔼 × 𝔼), cp = μ.prod ν := ⟨_, rfl⟩
      haveI : IsProbabilityMeasure cp := by rw [h1]; infer_instance
      refine ⟨cp, inferInstance, ?_, ?_, ?_⟩
      · rw [h1, Measure.map_fst_prod]; simp
      · rw [h1, Measure.map_snd_prod]; simp
      · have hle : (cp {q | 3 * δ < dist q.1 q.2}).toReal ≤ 1 := by
          have := prob_le_one (μ := cp) (s := {q : 𝔼 × 𝔼 | 3 * δ < dist q.1 q.2})
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
        refine hle.trans ?_
        have hf : 1 ≤ 1 + |Real.log (1 / B)| / p := by
          have : 0 ≤ |Real.log (1 / B)| / p := by positivity
          linarith
        calc (1 : ℝ) ≤ B := hB1
          _ = 1 * B * 1 := by ring
          _ ≤ (18 + 4 * Yurinskii.c4) * B * (1 + |Real.log (1 / B)| / p) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hC0 hBpos.le) hf (by norm_num) (by positivity)


section Bridge

variable {Ω : Type*} [MeasurableSpace Ω]

lemma memLp_two_coord {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ^p}
    (hY : Measurable Y) (h3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) (c : Fin p) :
    MemLp (fun ω => Y ω c) 2 P := by
  have h2 := (Yurinskii.integrable_norm_of_pow3 (P := P) hY h3).2
  refine (memLp_two_iff_integrable_sq (by fun_prop : Measurable fun ω => Y ω c).aestronglyMeasurable).2 ?_
  refine h2.mono' (by fun_prop : Measurable fun ω => (Y ω c) ^ 2).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := PiLp.norm_apply_le (Y ω) c
  rw [Real.norm_eq_abs] at this
  nlinarith [abs_nonneg (Y ω c), sq_abs (Y ω c), norm_nonneg (Y ω)]

lemma integral_coord_zero' {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ^p}
    (hY : Measurable Y) (h3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) (h0 : ∫ ω, Y ω ∂P = 0)
    (c : Fin p) : ∫ ω, Y ω c ∂P = 0 := by
  have hi : Integrable Y P :=
    (integrable_norm_iff hY.aestronglyMeasurable).1 (Yurinskii.integrable_norm_of_pow3 hY h3).1
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj c : (ℝ^p) →L[ℝ] ℝ) hi
  simpa [h0] using this

lemma covMatrix_eq {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ} (ξ : Fin N → Ω → ℝ^p)
    (hmeas : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hL : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ 3) P) :
    covMatrix P (fun ω => ∑ i, ξ i ω) = ∑ i, Yurinskii.momentMatrix (P.map (ξ i)) := by
  ext c d
  have hm2 : ∀ i c, MemLp (fun ω => ξ i ω c) 2 P := fun i c => memLp_two_coord (hmeas i) (hL i) c
  have e : ∀ (ω : Ω) (c : Fin p), (∑ i, ξ i ω) c = ∑ i, ξ i ω c := fun ω c => by
    simp
  have hs : ∀ d, MemLp (fun ω => ∑ j, ξ j ω d) 2 P := fun d =>
    memLp_finsetSum _ (fun j _ => hm2 j d)
  simp only [covMatrix, Matrix.of_apply, Matrix.sum_apply, e]
  rw [covariance_fun_sum_left (X := fun i ω => ξ i ω c) (fun i => hm2 i c) (hs d)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covariance_fun_sum_right (X := fun j ω => ξ j ω d) (fun j => hm2 j d) (hm2 i c)]
  rw [Finset.sum_eq_single i]
  · rw [covariance_eq_sub (hm2 i c) (hm2 i d),
      integral_coord_zero' (hmeas i) (hL i) (hmean i) c, zero_mul, sub_zero]
    simp only [Yurinskii.momentMatrix, Matrix.of_apply]
    rw [integral_map (hmeas i).aemeasurable (by fun_prop : Measurable fun x : ℝ^p => x c * x d).aestronglyMeasurable]
    rfl
  · intro j _ hji
    have hI := (hind.indepFun (Ne.symm hji)).comp (φ := fun x : ℝ^p => x c) (ψ := fun x : ℝ^p => x d)
      (by fun_prop) (by fun_prop)
    exact hI.covariance_eq_zero (hm2 i c) (hm2 j d)
  · simp


end Bridge

end YurinskiiCoupling

/-- Lemma A.37 `M:B:lem:yurinskii` (source lines 11573-11579), Yurinskii's coupling
(external: Yurinskii 1977; Pollard 2002, Ch. 10): for independent mean-zero `ξ_1,…,ξ_N` in
`ℝ^n` with `L = ∑ E|ξ_i|³ < ∞` and `S = ∑ ξ_i`, for every `δ > 0` there is a probability
space carrying `S̃ =ᵈ S` and `Z ∼ N(0, Var S)` with
`P(|S̃ - Z| > 3δ) ≤ C₀ B (1 + |log(1/B)|/n)`, `B = L n δ^{-3}`, `C₀` universal. -/
theorem yurinskii_coupling : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n N : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Fin N → Ω → ℝ^n)
    (hmeas : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hL : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ 3) P)
    (δ : ℝ) (hδ : 0 < δ) (hS : (covMatrix P fun ω => ∑ i, ξ i ω).PosSemidef),
    let L := ∑ i, ∫ ω, ‖ξ i ω‖ ^ 3 ∂P
    let Bq := L * n * δ ^ (-3 : ℝ)
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (S' Z : Ω' → ℝ^n),
      law P' S' = law P (fun ω => ∑ i, ξ i ω) ∧
      law P' Z = ProbabilityTheory.multivariateGaussian 0 (covMatrix P fun ω => ∑ i, ξ i ω) ∧
      (P' {ω' | 3 * δ < ‖S' ω' - Z ω'‖}).toReal ≤ C₀ * Bq * (1 + |Real.log (1 / Bq)| / n) := by
  refine ⟨18 + 4 * Yurinskii.c4, by linarith [Yurinskii.c4_nonneg], ?_⟩
  intro n N Ω _ P _ ξ hmeas hind hmean hL δ hδ hS L Bq
  set ρ : Fin N → Measure (ℝ^n) := fun i => P.map (ξ i) with hρ
  have h0ρ : ∀ i c, ∫ x, x c ∂(ρ i) = 0 := fun i c => by
    simp only [hρ]
    rw [integral_map (hmeas i).aemeasurable (by fun_prop : Measurable fun x : ℝ^n => x c).aestronglyMeasurable]
    exact integral_coord_zero' (hmeas i) (hL i) (hmean i) c
  have h3ρ : ∀ i, Integrable (fun x : ℝ^n => ‖x‖ ^ 3) (ρ i) := fun i => by
    simp only [hρ]
    exact (integrable_map_measure (measurable_norm.pow_const 3).aestronglyMeasurable
      (hmeas i).aemeasurable).2 (hL i)
  have hLeq : ∑ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i) = L := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hρ]
    rw [integral_map (hmeas i).aemeasurable (measurable_norm.pow_const 3).aestronglyMeasurable]
  obtain ⟨cp, hcp, h1, h2, h3⟩ := yur_measure ρ h0ρ h3ρ hδ
  have hsm : Measurable (fun q : Fin N → ℝ^n => ∑ i, q i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hlaw : law P (fun ω => ∑ i, ξ i ω) = (Measure.pi ρ).map (fun q => ∑ i, q i) := by
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (hmeas i).aemeasurable)).1 hind
    have hm2 : Measurable (fun (ω : Ω) (i : Fin N) => ξ i ω) := Measurable.of_eval fun i => hmeas i
    show P.map (fun ω => ∑ i, ξ i ω) = _
    rw [show (fun ω => ∑ i, ξ i ω) = (fun q : Fin N → ℝ^n => ∑ i, q i) ∘ (fun (ω : Ω) (i : Fin N) => ξ i ω)
      from rfl, ← Measure.map_map hsm hm2, hmap]
  refine ⟨(EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)), inferInstance, cp, hcp, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
  · show cp.map Prod.fst = _
    rw [h1, hlaw]
  · show cp.map Prod.snd = _
    rw [h2, covMatrix_eq ξ hmeas hind hmean hL]
  · have e : {ω' : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) | 3 * δ < ‖ω'.1 - ω'.2‖} =
        {q | 3 * δ < dist q.1 q.2} := by
      ext q; simp [dist_eq_norm]
    have hBq : Bq = L * n * δ ^ (-3 : ℝ) := rfl
    rw [hBq]
    show (cp {ω' : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) | 3 * δ < ‖ω'.1 - ω'.2‖}).toReal ≤ _
    rw [e]
    rw [hLeq] at h3
    exact h3


end FiniteDim

end HRS
