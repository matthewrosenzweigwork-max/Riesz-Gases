/-
# HRS.External.WeakSpec -- weak specification and the Rebeschini-van Handel comparison (EXT-2, E3 + E4)

Abstract setting: a finite product `Fin n → E`, a probability measure `μ` on `E`.

* Part A (E4 core, `rvh_comparison`): for two one-site specifications `S, S'` on the same product
  space, `S` satisfying a Dobrushin condition with row sums `≤ r < 1`, and one-site kernels
  differing by at most `b` in total variation, every bounded measurable `f` with coordinate
  oscillations `Δ` satisfies `|P f - P' f| ≤ b (1 - r)⁻¹ ∑ⱼ Δⱼ` (RvH Cor. 2.6, trivial metric).
* Part B (E3): the weak specification (`WeakPotential`, `IsField`), the explicit pinned density
  (`pinnedLaw`), the one-site conditional densities (`siteKernel_fieldDensity`).
* Part C (E3): Jensen bound on the normalizer (`exp_le_integral_siteU`, `weak_normalizer_bounds`),
  `G_i ≤ C μ` (`weak_siteKernel_le`), Dobrushin coefficients `c_ij ≤ κ/N` (`weak_dobrushin`),
  `κ < 1/2` from smallness of `βγ` (`weakKappa_lt_half`), Wu's inequality for the pinned
  ensemble (`weak_resampling`, `weak_linear_variance`).
* Part D (E4): functional comparison for two ensembles (`rvh_field_comparison`), changed pin
  (`rvh_pin_changed`), deleted pin (`rvh_pin_deleted`), disintegration over a pin
  (`pinned_marginal_succ`), averaging over the pin (`rvh_pin_comparison`, `A:eq:weak-pin-comparison`)
  and one removed coordinate (`rvh_pin_removed`).
-/
import HRS.External.WuResampling

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.External

/-! ## Part A: functional comparison of two specifications -/

section Compare

open Spec

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- One-site averaging operators of two specifications whose kernels differ by at most `b` in total
variation differ by at most `b Δ_i` on functions with oscillation `Δ_i` in coordinate `i`. -/
lemma abs_site_sub_site_le (S S' : Spec E n) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i x A, MeasurableSet A → |(S.G i x).real A - (S'.G i x).real A| ≤ b)
    {g : (Fin n → E) → ℝ} (hg : Measurable g) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j)
    (hosc : OscBound g Δ) (i : Fin n) (x : Fin n → E) :
    |S.site i g x - S'.site i g x| ≤ b * Δ i := by
  exact abs_integral_sub_le_of_tv (S.G i x) (S'.G i x) (hΔ i) (fun A hA => hb i x A hA)
    (measurable_section g hg i x) (fun z z' => hosc i _ _ (update_agree' x i z z'))

lemma abs_scan_sub_scan_le [NeZero n] (S S' : Spec E n) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i x A, MeasurableSet A → |(S.G i x).real A - (S'.G i x).real A| ≤ b)
    {g : (Fin n → E) → ℝ} (hg : Measurable g) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j)
    (hosc : OscBound g Δ) (x : Fin n → E) :
    |S.scan g x - S'.scan g x| ≤ b / n * ∑ j, Δ j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold scan
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hn)]
  calc 1 / (n : ℝ) * |∑ i, (S.site i g x - S'.site i g x)|
      ≤ 1 / (n : ℝ) * ∑ i, b * Δ i := by
        refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hn).le
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => abs_site_sub_site_le S S' hb0 hb hg hΔ hosc i x)
    _ = b / n * ∑ j, Δ j := by rw [← Finset.mul_sum]; ring

lemma abs_integral_scan_sub_le [NeZero n] (S S' : Spec E n) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i x A, MeasurableSet A → |(S.G i x).real A - (S'.G i x).real A| ≤ b)
    {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g) (hbd : ∀ x, |g x| ≤ M)
    {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j) (hosc : OscBound g Δ) :
    |∫ x, S.scan g x ∂S'.P - ∫ x, g x ∂S'.P| ≤ b / n * ∑ j, Δ j := by
  have h1 : Integrable (S.scan g) S'.P := integrable_of_bdd (measurable_scan hg) (abs_scan_le hbd)
  have h2 : Integrable (S'.scan g) S'.P := integrable_of_bdd (measurable_scan hg) (abs_scan_le hbd)
  have e : ∫ x, S.scan g x ∂S'.P - ∫ x, g x ∂S'.P
      = ∫ x, (S.scan g x - S'.scan g x) ∂S'.P := by
    rw [integral_sub h1 h2, integral_scan (S := S') hg hbd]
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := S'.P) (f := fun x => S.scan g x - S'.scan g x)
    (C := b / n * ∑ j, Δ j) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_scan_sub_scan_le S S' hb0 hb hg hΔ hosc x)
  simpa using this

/-- **Single-site comparison** (Rebeschini-van Handel, Cor. 2.6 with the trivial metric; Dobrushin /
Foellmer comparison).  If `S` satisfies the Dobrushin condition with row sums `≤ r < 1`, and the
one-site kernels of `S` and `S'` differ by at most `b` in total variation (at every configuration),
then for bounded measurable `f` with oscillation `Δ_j` in coordinate `j`,
`|P f - P' f| ≤ b (1 - r)⁻¹ ∑ⱼ Δⱼ`. -/
theorem rvh_comparison [NeZero n] (S S' : Spec E n) {c : Fin n → Fin n → ℝ}
    (hc : IsDobrushin S c) {r : ℝ} (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) (hr : r < 1)
    {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i x A, MeasurableSet A → |(S.G i x).real A - (S'.G i x).real A| ≤ b)
    {M : ℝ} {f : (Fin n → E) → ℝ} (hf : Measurable f) (hbd : ∀ x, |f x| ≤ M)
    {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j) (hosc : OscBound f Δ) :
    |∫ x, f x ∂S.P - ∫ x, f x ∂S'.P| ≤ b / (1 - r) * ∑ j, Δ j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set ρ : ℝ := 1 - (1 - r) / n with hρ
  have hρ0 : 0 ≤ ρ := rho_nonneg hc hrow
  have h1r : 0 < 1 - r := by linarith
  have hρ1 : ρ < 1 := by
    have : 0 < (1 - r) / n := div_pos h1r hn
    linarith
  have hM : 0 ≤ M := by
    obtain ⟨x0⟩ := Measure.nonempty_of_neZero S.P
    exact (abs_nonneg _).trans (hbd x0)
  set T : ℝ := ∑ j, Δ j with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => hΔ j
  -- telescoping
  have hstep : ∀ m : ℕ, |∫ x, S.scan^[m + 1] f x ∂S'.P - ∫ x, S.scan^[m] f x ∂S'.P|
      ≤ b / n * (ρ ^ m * T) := by
    intro m
    obtain ⟨hm, hbm, Δ', hΔ', hosc', hsum⟩ := osc_scan_iterate hc hrow hf hbd hΔ hosc m
    have := abs_integral_scan_sub_le S S' hb0 hb hm hbm hΔ' hosc'
    rw [Function.iterate_succ_apply']
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left hsum (div_nonneg hb0 hn.le)
  have hgeo : ∀ k : ℕ, |∫ x, S.scan^[k] f x ∂S'.P - ∫ x, f x ∂S'.P|
      ≤ b / n * (T / (1 - ρ)) := by
    intro k
    have : ∀ k : ℕ, |∫ x, S.scan^[k] f x ∂S'.P - ∫ x, f x ∂S'.P|
        ≤ b / n * (∑ m ∈ Finset.range k, ρ ^ m * T) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, mul_add]
        have h3 := hstep k
        have h4 : |∫ x, S.scan^[k + 1] f x ∂S'.P - ∫ x, f x ∂S'.P|
            ≤ |∫ x, S.scan^[k + 1] f x ∂S'.P - ∫ x, S.scan^[k] f x ∂S'.P|
              + |∫ x, S.scan^[k] f x ∂S'.P - ∫ x, f x ∂S'.P| := by
          have := abs_add_le (∫ x, S.scan^[k + 1] f x ∂S'.P - ∫ x, S.scan^[k] f x ∂S'.P)
            (∫ x, S.scan^[k] f x ∂S'.P - ∫ x, f x ∂S'.P)
          simpa using this
        linarith
    refine (this k).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hb0 hn.le)
    rw [← Finset.sum_mul]
    have hs : ∑ m ∈ Finset.range k, ρ ^ m ≤ 1 / (1 - ρ) := by
      have h0 : 0 < 1 - ρ := by linarith
      rw [le_div_iff₀ h0, mul_comm, mul_neg_geom_sum]
      linarith [pow_nonneg hρ0 k]
    calc (∑ m ∈ Finset.range k, ρ ^ m) * T ≤ 1 / (1 - ρ) * T :=
          mul_le_mul_of_nonneg_right hs hT0
      _ = T / (1 - ρ) := by ring
  have hlim : ∀ k : ℕ, |∫ x, f x ∂S.P - ∫ x, f x ∂S'.P|
      ≤ b / n * (T / (1 - ρ)) + ρ ^ k * (n * (2 * M)) := by
    intro k
    have hx : ∀ x, |S.scan^[k] f x - ∫ y, f y ∂S.P| ≤ ρ ^ k * (n * (2 * M)) :=
      fun x => abs_scan_iterate_sub_integral_le hc hrow hf hbd k x
    have h2 : |∫ x, S.scan^[k] f x ∂S'.P - ∫ y, f y ∂S.P| ≤ ρ ^ k * (n * (2 * M)) := by
      have hi : Integrable (S.scan^[k] f) S'.P :=
        integrable_of_bdd (osc_scan_iterate hc hrow hf hbd hΔ hosc k).1
          (osc_scan_iterate hc hrow hf hbd hΔ hosc k).2.1
      have e : ∫ x, S.scan^[k] f x ∂S'.P - ∫ y, f y ∂S.P
          = ∫ x, (S.scan^[k] f x - ∫ y, f y ∂S.P) ∂S'.P := by
        rw [integral_sub hi (integrable_const _)]; simp
      rw [e]
      have := norm_integral_le_of_norm_le_const (μ := S'.P)
        (f := fun x => S.scan^[k] f x - ∫ y, f y ∂S.P) (C := ρ ^ k * (n * (2 * M)))
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hx x)
      simpa using this
    have h5 := hgeo k
    have h6 : |∫ x, f x ∂S.P - ∫ x, f x ∂S'.P|
        ≤ |∫ y, f y ∂S.P - ∫ x, S.scan^[k] f x ∂S'.P|
            + |∫ x, S.scan^[k] f x ∂S'.P - ∫ x, f x ∂S'.P| := by
      have := abs_add_le (∫ y, f y ∂S.P - ∫ x, S.scan^[k] f x ∂S'.P)
        (∫ x, S.scan^[k] f x ∂S'.P - ∫ x, f x ∂S'.P)
      simpa using this
    rw [abs_sub_comm] at h2
    linarith
  have hconst : b / n * (T / (1 - ρ)) = b / (1 - r) * T := by
    have : 1 - ρ = (1 - r) / n := by rw [hρ]; ring
    rw [this]; field_simp
  have htend : Filter.Tendsto (fun k : ℕ => b / (1 - r) * T + ρ ^ k * (n * (2 * M)))
      Filter.atTop (nhds (b / (1 - r) * T + 0 * (n * (2 * M)))) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _)
  rw [zero_mul, add_zero] at htend
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun k => ?_)
  rw [← hconst]; exact hlim k

end Compare

/-! ## Part B: the weak specification -/

section Weak

variable {E : Type*} [MeasurableSpace E]

/-- **Weak specification data** (`A:eq:weak-specification`): a probability space `(E, μ)`, a
single-site potential `φ` bounded above by `M` with `∫ φ dμ ≥ -M'`, and a nonnegative symmetric
pair kernel `q` with row bound `∫ q(x, y) μ(dy) ≤ γ`.  The coupling `λ = β/N`, the number `n` of
free coordinates and the pins are not part of the data. -/
structure WeakPotential (μ : Measure E) where
  φ : E → ℝ
  q : E → E → ℝ
  M : ℝ
  M' : ℝ
  γ : ℝ
  measurable_φ : Measurable φ
  measurable_q : Measurable (fun p : E × E => q p.1 p.2)
  q_nonneg : ∀ x y, 0 ≤ q x y
  q_symm : ∀ x y, q x y = q y x
  γ_nonneg : 0 ≤ γ
  φ_le : ∀ x, φ x ≤ M
  integrable_φ : Integrable φ μ
  neg_le_integral_φ : -M' ≤ ∫ x, φ x ∂μ
  integrable_q : ∀ x, Integrable (q x) μ
  row_le : ∀ x, ∫ y, q x y ∂μ ≤ γ

/-- A one-body field `ψ` (the single-site potential after pinning): measurable, bounded above by
`M`, with `∫ ψ dμ ≥ -M₁`. -/
structure IsField (μ : Measure E) (ψ : E → ℝ) (M M₁ : ℝ) : Prop where
  measurable : Measurable ψ
  le : ∀ z, ψ z ≤ M
  integrable : Integrable ψ μ
  ge : -M₁ ≤ ∫ z, ψ z ∂μ

variable {μ : Measure E}

/-- Pair energy `∑_{i<j} q(y_i, y_j)` of a configuration, written as `(1/2) ∑_{i ≠ j}`
(`q` is symmetric). -/
def pairEnergy (V : WeakPotential μ) {n : ℕ} (y : Fin n → E) : ℝ :=
  (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, V.q (y i) (y j)

/-- The one-body field of a pinned ensemble: `φ(z) - λ ∑_{b} q(z, a_b)` for the pin configuration
`a : B → E` and pair coefficient `λ`. -/
def pinField (V : WeakPotential μ) {B : Type*} [Fintype B] (lam : ℝ) (a : B → E) : E → ℝ :=
  fun z => V.φ z - lam * ∑ b, V.q z (a b)

/-- Unnormalized density (w.r.t. `μ^n`) of the ensemble with one-body field `ψ` and pair
coefficient `lam`:  `exp(∑ᵢ ψ(yᵢ) - lam ∑_{i<j} q(yᵢ, yⱼ))`. -/
def fieldWeight (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (y : Fin n → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ i, ψ (y i) - lam * pairEnergy V y))

/-- The normalizing constant `∫ fieldWeight dμ^n`. -/
def fieldNorm (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, fieldWeight V ψ lam y ∂(Measure.pi fun _ : Fin n => μ)

/-- The normalized density of the ensemble w.r.t. `μ^n`. -/
def fieldDensity (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) : (Fin n → E) → ℝ≥0∞ :=
  fun y => fieldWeight V ψ lam y * (fieldNorm V ψ lam n)⁻¹

/-- The law of the ensemble with one-body field `ψ`. -/
def fieldLaw (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) : Measure (Fin n → E) :=
  (Measure.pi fun _ : Fin n => μ).withDensity (fieldDensity V ψ lam n)

/-- **Pinned weak ensemble**: `n` free coordinates with density
`∝ exp(∑ᵢ φ(yᵢ) - lam ∑_{i<j} q(yᵢ,yⱼ) - lam ∑ᵢ ∑_{b ∈ B} q(yᵢ, a_b))` w.r.t. `μ^n`,
where `a : B → E` are the pins. -/
def pinnedLaw (V : WeakPotential μ) (lam : ℝ) (n : ℕ) {B : Type*} [Fintype B] (a : B → E) :
    Measure (Fin n → E) :=
  fieldLaw V (pinField V lam a) lam n

lemma pairEnergy_nonneg (V : WeakPotential μ) {n : ℕ} (y : Fin n → E) : 0 ≤ pairEnergy V y :=
  mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => V.q_nonneg _ _)

lemma measurable_pairEnergy (V : WeakPotential μ) {n : ℕ} : Measurable (pairEnergy V (n := n)) := by
  unfold pairEnergy
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
  have := V.measurable_q.comp ((measurable_pi_apply (X := fun _ : Fin n => E) i).prodMk (measurable_pi_apply j))
  exact this

/-- The part of the pair energy not involving coordinate `i`. -/
def pairRest (V : WeakPotential μ) {n : ℕ} (i : Fin n) (x : Fin n → E) : ℝ :=
  (1 / 2) * ∑ k ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase k, V.q (x k) (x l)

lemma pairEnergy_update (V : WeakPotential μ) {n : ℕ} (x : Fin n → E) (i : Fin n) (z : E) :
    pairEnergy V (update x i z)
      = ∑ l ∈ Finset.univ.erase i, V.q z (x l) + pairRest V i x := by
  unfold pairEnergy pairRest
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∑ j ∈ Finset.univ.erase i, V.q (update x i z i) (update x i z j)
      = ∑ l ∈ Finset.univ.erase i, V.q z (x l) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    simp [Finset.ne_of_mem_erase hl]
  have h2 : ∀ k ∈ Finset.univ.erase i,
      ∑ j ∈ Finset.univ.erase k, V.q (update x i z k) (update x i z j)
        = V.q (x k) z + ∑ l ∈ (Finset.univ.erase i).erase k, V.q (x k) (x l) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hmem : i ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hki.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase _ _ hmem, Finset.erase_right_comm]
    congr 1
    · simp [hki]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hli : l ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      simp [hki, hli]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  have h3 : ∑ k ∈ Finset.univ.erase i, V.q (x k) z = ∑ l ∈ Finset.univ.erase i, V.q z (x l) :=
    Finset.sum_congr rfl fun k _ => V.q_symm _ _
  rw [h3]
  ring

section WeakBasic

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ}

lemma measurable_fieldWeight (hψ : Measurable ψ) (V : WeakPotential μ) (lam : ℝ) {n : ℕ} :
    Measurable (fieldWeight V ψ lam (n := n)) := by
  unfold fieldWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  exact (Finset.measurable_sum _ fun i _ => hψ.comp (measurable_pi_apply i)).sub
    ((measurable_pairEnergy V).const_mul _)

lemma fieldWeight_pos (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (y : Fin n → E) :
    0 < fieldWeight V ψ lam y := by
  unfold fieldWeight
  exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

lemma fieldWeight_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (y : Fin n → E) :
    fieldWeight V ψ lam y ≤ ENNReal.ofReal (Real.exp (n * M)) := by
  unfold fieldWeight
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 : ∑ i, ψ (y i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hψ.le _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 := mul_nonneg hlam (pairEnergy_nonneg V y)
  linarith

lemma fieldNorm_pos (hψ : Measurable ψ) (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    0 < fieldNorm V ψ lam n := by
  rw [pos_iff_ne_zero]
  intro h
  unfold fieldNorm at h
  rw [lintegral_eq_zero_iff (measurable_fieldWeight hψ V lam)] at h
  obtain ⟨y, hy⟩ := h.exists
  exact (fieldWeight_pos V ψ lam y).ne' hy

lemma fieldNorm_lt_top (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    fieldNorm V ψ lam n < ∞ := by
  unfold fieldNorm
  calc ∫⁻ y, fieldWeight V ψ lam y ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (n * M)) ∂(Measure.pi fun _ : Fin n => μ) :=
        lintegral_mono fun y => fieldWeight_le hψ hlam y
    _ < ∞ := by simp

lemma measurable_fieldDensity (hψ : Measurable ψ) (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    Measurable (fieldDensity V ψ lam n) :=
  (measurable_fieldWeight hψ V lam).mul measurable_const

lemma fieldDensity_pos (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) (y : Fin n → E) :
    0 < fieldDensity V ψ lam n y :=
  ENNReal.mul_pos (fieldWeight_pos V ψ lam y).ne'
    (ENNReal.inv_ne_zero.2 (fieldNorm_lt_top hψ hlam n).ne)

lemma fieldDensity_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) (y : Fin n → E) :
    fieldDensity V ψ lam n y ≤ ((ENNReal.ofReal (Real.exp (n * M)) * (fieldNorm V ψ lam n)⁻¹).toNNReal : ℝ≥0) := by
  have hne : ENNReal.ofReal (Real.exp (n * M)) * (fieldNorm V ψ lam n)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (fieldNorm_pos hψ.measurable V lam n).ne')
  rw [ENNReal.coe_toNNReal hne]
  exact mul_le_mul_left (fieldWeight_le hψ hlam y) _

lemma lintegral_fieldDensity (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    ∫⁻ y, fieldDensity V ψ lam n y ∂(Measure.pi fun _ : Fin n => μ) = 1 := by
  unfold fieldDensity
  rw [lintegral_mul_const _ (measurable_fieldWeight hψ.measurable V lam)]
  exact ENNReal.mul_inv_cancel (fieldNorm_pos hψ.measurable V lam n).ne'
    (fieldNorm_lt_top hψ hlam n).ne

/-- The one-site specification (E0 data) of the weak ensemble. -/
def fieldSpec (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) : Spec E n :=
  Spec.ofDensity μ (fieldDensity V ψ lam n) (measurable_fieldDensity hψ.measurable V lam n)
    (fieldDensity_pos hψ hlam n) _ (fieldDensity_le hψ hlam n) (lintegral_fieldDensity hψ hlam n)

lemma fieldSpec_P (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    (fieldSpec (V := V) hψ hlam n).P = fieldLaw V ψ lam n := rfl

lemma fieldSpec_G (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) (i : Fin n) :
    (fieldSpec (V := V) hψ hlam n).G i = siteKernel μ (fieldDensity V ψ lam n) i := rfl

end WeakBasic

section SiteKernel

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ}

/-- Unnormalized one-site conditional density: given the other coordinates `x`, coordinate `i`
has density `∝ exp(ψ(z) - lam ∑_{l ≠ i} q(z, x_l))` w.r.t. `μ`. -/
def siteU (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i : Fin n) (x : Fin n → E)
    (z : E) : ℝ :=
  Real.exp (ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (x l))

lemma measurable_sumq (V : WeakPotential μ) {n : ℕ} (i : Fin n) (x : Fin n → E) :
    Measurable fun z => ∑ l ∈ Finset.univ.erase i, V.q z (x l) :=
  Finset.measurable_sum _ fun l _ => V.measurable_q.comp (measurable_id.prodMk measurable_const)

lemma measurable_siteU (hψ : Measurable ψ) (V : WeakPotential μ) (lam : ℝ) {n : ℕ} (i : Fin n)
    (x : Fin n → E) : Measurable (siteU V ψ lam i x) :=
  Real.measurable_exp.comp (hψ.sub ((measurable_sumq V i x).const_mul _))

lemma siteU_pos (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i : Fin n) (x : Fin n → E)
    (z : E) : 0 < siteU V ψ lam i x z := Real.exp_pos _

lemma sumq_nonneg (V : WeakPotential μ) {n : ℕ} (i : Fin n) (x : Fin n → E) (z : E) :
    0 ≤ ∑ l ∈ Finset.univ.erase i, V.q z (x l) :=
  Finset.sum_nonneg fun _ _ => V.q_nonneg _ _

lemma siteU_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n) (x : Fin n → E)
    (z : E) : siteU V ψ lam i x z ≤ Real.exp M := by
  unfold siteU
  refine Real.exp_le_exp.2 ?_
  have := mul_nonneg hlam (sumq_nonneg V i x z)
  linarith [hψ.le z]

lemma integrable_siteU (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x : Fin n → E) : Integrable (siteU V ψ lam i x) μ :=
  Integrable.of_bound (measurable_siteU hψ.measurable V lam i x).aestronglyMeasurable (Real.exp M)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (siteU_pos V ψ lam i x z).le]; exact siteU_le hψ hlam i x z)

lemma integral_siteU_pos (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x : Fin n → E) : 0 < ∫ z, siteU V ψ lam i x z ∂μ :=
  (integral_pos_iff_support_of_nonneg (fun z => (siteU_pos V ψ lam i x z).le)
    (integrable_siteU hψ hlam i x)).2 (by
      have : Function.support (siteU V ψ lam i x) = Set.univ :=
        Set.eq_univ_of_forall fun z => (siteU_pos V ψ lam i x z).ne'
      rw [this]; simp)

/-- A general factorization: if `W(x^{i ← z}) = κ U(z)` with `κ ∈ (0, ∞)`, then the one-site kernel
is the normalized `U`. -/
lemma siteKernel_of_factor {n : ℕ} {W : (Fin n → E) → ℝ≥0∞} (hW : Measurable W) (i : Fin n) (x : Fin n → E)
    {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ∞) {U : E → ℝ≥0∞} (hU : Measurable U)
    (hfac : ∀ z, W (update x i z) = κ * U z) :
    siteKernel μ W i x = μ.withDensity fun z => U z * (∫⁻ z', U z' ∂μ)⁻¹ := by
  rw [siteKernel_apply hW]
  have hZ : normalizer μ W i x = κ * ∫⁻ z, U z ∂μ := by
    unfold normalizer
    simp_rw [hfac]
    exact lintegral_const_mul _ hU
  rw [hZ]
  congr 1
  funext z
  rw [hfac z, ENNReal.mul_inv (Or.inl hκ0) (Or.inl hκt)]
  calc κ * U z * (κ⁻¹ * (∫⁻ z', U z' ∂μ)⁻¹)
      = (κ * κ⁻¹) * (U z * (∫⁻ z', U z' ∂μ)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hκ0 hκt, one_mul]

lemma sum_update_psi (ψ : E → ℝ) {n : ℕ} (x : Fin n → E) (i : Fin n) (z : E) :
    ∑ k, ψ (update x i z k) = ψ z + ∑ k ∈ Finset.univ.erase i, ψ (x k) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun k hk => by simp [Finset.ne_of_mem_erase hk]

lemma fieldDensity_update (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (x : Fin n → E)
    (i : Fin n) (z : E) :
    fieldDensity V ψ lam n (update x i z)
      = (ENNReal.ofReal (Real.exp (∑ k ∈ Finset.univ.erase i, ψ (x k) - lam * pairRest V i x))
          * (fieldNorm V ψ lam n)⁻¹) * ENNReal.ofReal (siteU V ψ lam i x z) := by
  unfold fieldDensity fieldWeight siteU
  rw [sum_update_psi, pairEnergy_update]
  have : ψ z + ∑ k ∈ Finset.univ.erase i, ψ (x k)
      - lam * (∑ l ∈ Finset.univ.erase i, V.q z (x l) + pairRest V i x)
      = (∑ k ∈ Finset.univ.erase i, ψ (x k) - lam * pairRest V i x)
        + (ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (x l)) := by ring
  rw [this, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

lemma siteKernel_fieldDensity (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x : Fin n → E) :
    siteKernel μ (fieldDensity V ψ lam n) i x
      = μ.withDensity fun z =>
          ENNReal.ofReal (siteU V ψ lam i x z / ∫ z', siteU V ψ lam i x z' ∂μ) := by
  have hne : (ENNReal.ofReal (Real.exp (∑ k ∈ Finset.univ.erase i, ψ (x k) - lam * pairRest V i x))
          * (fieldNorm V ψ lam n)⁻¹) ≠ 0 :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (ENNReal.inv_ne_zero.2 (fieldNorm_lt_top hψ hlam n).ne)).ne'
  have hnt : (ENNReal.ofReal (Real.exp (∑ k ∈ Finset.univ.erase i, ψ (x k) - lam * pairRest V i x))
          * (fieldNorm V ψ lam n)⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (fieldNorm_pos hψ.measurable V lam n).ne')
  rw [siteKernel_of_factor (measurable_fieldDensity hψ.measurable V lam n) i x hne hnt
    (U := fun z => ENNReal.ofReal (siteU V ψ lam i x z))
    (measurable_siteU hψ.measurable V lam i x).ennreal_ofReal
    (fun z => fieldDensity_update V ψ lam x i z)]
  congr 1
  funext z
  have h1 : ∫⁻ z', ENNReal.ofReal (siteU V ψ lam i x z') ∂μ
      = ENNReal.ofReal (∫ z', siteU V ψ lam i x z' ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_siteU hψ hlam i x)
      (Filter.Eventually.of_forall fun z => (siteU_pos V ψ lam i x z).le)).symm
  rw [h1, ← ENNReal.ofReal_inv_of_pos (integral_siteU_pos hψ hlam i x),
    ← ENNReal.ofReal_mul (siteU_pos V ψ lam i x z).le, div_eq_mul_inv]

end SiteKernel

section TVDensity

variable {μ : Measure E}

lemma real_withDensity_ofReal (g : E → ℝ) (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) {A : Set E}
    (hA : MeasurableSet A) :
    (μ.withDensity fun z => ENNReal.ofReal (g z)).real A = ∫ z in A, g z ∂μ := by
  rw [Measure.real, withDensity_apply _ hA,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
      hg.aestronglyMeasurable]

/-- Total variation between two normalized densities: for nonnegative integrable `u₁, u₂` with
positive integrals `Z₁, Z₂`, `|ν₁(A) - ν₂(A)| ≤ 2 ‖u₁ - u₂‖₁ / Z₁`, where `νₖ = (uₖ/Zₖ) μ`. -/
lemma abs_real_withDensity_sub_le (u₁ u₂ : E → ℝ) (m₁ : Measurable u₁) (m₂ : Measurable u₂)
    (n₁ : ∀ z, 0 ≤ u₁ z) (n₂ : ∀ z, 0 ≤ u₂ z) (i₁ : Integrable u₁ μ) (i₂ : Integrable u₂ μ)
    (Z₁ Z₂ : ℝ) (hZ₁ : Z₁ = ∫ z, u₁ z ∂μ) (hZ₂ : Z₂ = ∫ z, u₂ z ∂μ) (h₁ : 0 < Z₁) (h₂ : 0 < Z₂)
    {A : Set E} (hA : MeasurableSet A) :
    |(μ.withDensity fun z => ENNReal.ofReal (u₁ z / Z₁)).real A
        - (μ.withDensity fun z => ENNReal.ofReal (u₂ z / Z₂)).real A|
      ≤ 2 * (∫ z, |u₁ z - u₂ z| ∂μ) / Z₁ := by
  have hm1 : Measurable fun z => u₁ z / Z₁ := m₁.div_const _
  have hm2 : Measurable fun z => u₂ z / Z₂ := m₂.div_const _
  rw [real_withDensity_ofReal _ hm1 (fun z => div_nonneg (n₁ z) h₁.le) hA,
    real_withDensity_ofReal _ hm2 (fun z => div_nonneg (n₂ z) h₂.le) hA]
  set D : ℝ := ∫ z, |u₁ z - u₂ z| ∂μ with hD
  have hD0 : 0 ≤ D := integral_nonneg fun z => abs_nonneg _
  have e1 : ∫ z in A, u₁ z / Z₁ ∂μ = (∫ z in A, u₁ z ∂μ) / Z₁ := integral_div _ _
  have e2 : ∫ z in A, u₂ z / Z₂ ∂μ = (∫ z in A, u₂ z ∂μ) / Z₂ := integral_div _ _
  rw [e1, e2]
  set a₁ := ∫ z in A, u₁ z ∂μ
  set a₂ := ∫ z in A, u₂ z ∂μ
  have ha₂0 : 0 ≤ a₂ := setIntegral_nonneg hA fun z _ => n₂ z
  have ha₂ : a₂ ≤ Z₂ := hZ₂ ▸ setIntegral_le_integral i₂ (Filter.Eventually.of_forall n₂)
  have hdiff : |a₁ - a₂| ≤ D := by
    have : a₁ - a₂ = ∫ z in A, (u₁ z - u₂ z) ∂μ :=
      (integral_sub i₁.integrableOn i₂.integrableOn).symm
    rw [this]
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_le_integral (i₁.sub i₂).abs (Filter.Eventually.of_forall fun z => abs_nonneg _)
  have hZdiff : |Z₁ - Z₂| ≤ D := by
    have : Z₁ - Z₂ = ∫ z, (u₁ z - u₂ z) ∂μ := by rw [hZ₁, hZ₂, integral_sub i₁ i₂]
    rw [this]
    exact (abs_integral_le_integral_abs)
  have key : a₁ / Z₁ - a₂ / Z₂ = (a₁ - a₂) / Z₁ + a₂ * (Z₂ - Z₁) / (Z₁ * Z₂) := by
    field_simp; ring
  rw [key]
  have t1 : |(a₁ - a₂) / Z₁| ≤ D / Z₁ := by
    rw [abs_div, abs_of_pos h₁]; exact div_le_div_of_nonneg_right hdiff h₁.le
  have t2 : |a₂ * (Z₂ - Z₁) / (Z₁ * Z₂)| ≤ D / Z₁ := by
    rw [abs_div, abs_of_pos (mul_pos h₁ h₂), abs_mul, abs_of_nonneg ha₂0, div_le_div_iff₀ (mul_pos h₁ h₂) h₁]
    have : |Z₂ - Z₁| ≤ D := by rw [abs_sub_comm]; exact hZdiff
    calc a₂ * |Z₂ - Z₁| * Z₁ ≤ Z₂ * D * Z₁ := by
          gcongr
      _ = D * (Z₁ * Z₂) := by ring
  calc |(a₁ - a₂) / Z₁ + a₂ * (Z₂ - Z₁) / (Z₁ * Z₂)| ≤ D / Z₁ + D / Z₁ :=
        (abs_add_le _ _).trans (add_le_add t1 t2)
    _ = 2 * D / Z₁ := by ring

end TVDensity

section Bounds

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ}

lemma integrable_q_left (V : WeakPotential μ) (y : E) : Integrable (fun z => V.q z y) μ := by
  have := V.integrable_q y
  simpa [V.q_symm] using this

lemma integral_q_left_le (V : WeakPotential μ) (y : E) : ∫ z, V.q z y ∂μ ≤ V.γ := by
  have := V.row_le y
  simpa [V.q_symm] using this

/-- Jensen lower bound for the normalizer of the one-site conditional density. -/
lemma exp_le_integral_siteU (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x : Fin n → E) :
    Real.exp (-(M₁ + lam * n * V.γ)) ≤ ∫ z, siteU V ψ lam i x z ∂μ := by
  set h : E → ℝ := fun z => ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (x l) with hh
  have hint : Integrable h μ := by
    refine hψ.integrable.sub (Integrable.const_mul ?_ _)
    exact integrable_finset_sum _ fun l _ => integrable_q_left V (x l)
  have hjensen : Real.exp (∫ z, h z ∂μ) ≤ ∫ z, Real.exp (h z) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hint
      (integrable_siteU hψ hlam i x)
  have hI : ∫ z, h z ∂μ ≥ -(M₁ + lam * n * V.γ) := by
    have e : ∫ z, h z ∂μ = (∫ z, ψ z ∂μ)
        - lam * ∑ l ∈ Finset.univ.erase i, ∫ z, V.q z (x l) ∂μ := by
      rw [hh]
      simp only
      rw [integral_sub hψ.integrable (Integrable.const_mul
        (integrable_finset_sum _ fun l _ => integrable_q_left V (x l)) _), integral_const_mul,
        integral_finset_sum _ fun l _ => integrable_q_left V (x l)]
    rw [e]
    have h1 : ∑ l ∈ Finset.univ.erase i, ∫ z, V.q z (x l) ∂μ ≤ n * V.γ := by
      calc ∑ l ∈ Finset.univ.erase i, ∫ z, V.q z (x l) ∂μ ≤ ∑ _l ∈ Finset.univ.erase i, V.γ :=
            Finset.sum_le_sum fun l _ => integral_q_left_le V (x l)
        _ ≤ ∑ _l : Fin n, V.γ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => V.γ_nonneg
        _ = n * V.γ := by simp
    have := mul_le_mul_of_nonneg_left h1 hlam
    nlinarith [hψ.ge]
  refine le_trans (Real.exp_le_exp.2 hI) ?_
  exact hjensen

/-- Normalized one-site density bound: `G_i(x, ·) ≤ exp(M + Λ) μ`. -/
lemma siteU_div_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ}
    (hΛ : M₁ + lam * n * V.γ ≤ Λ) (i : Fin n) (x : Fin n → E) (z : E) :
    siteU V ψ lam i x z / ∫ z', siteU V ψ lam i x z' ∂μ ≤ Real.exp (M + Λ) := by
  have h1 := exp_le_integral_siteU (V := V) hψ hlam i x
  have h2 : Real.exp (-Λ) ≤ ∫ z', siteU V ψ lam i x z' ∂μ :=
    le_trans (Real.exp_le_exp.2 (by linarith)) h1
  rw [div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) h2)]
  calc siteU V ψ lam i x z ≤ Real.exp M := siteU_le hψ hlam i x z
    _ = Real.exp (M + Λ) * Real.exp (-Λ) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- `A:eq:weak-dobrushin`, first part: the one-site conditional laws are dominated by `C μ`
with `C = exp(M + Λ)`. -/
lemma siteKernel_le_smul (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ}
    (hΛ : M₁ + lam * n * V.γ ≤ Λ) (i : Fin n) (x : Fin n → E) :
    siteKernel μ (fieldDensity V ψ lam n) i x ≤ ENNReal.ofReal (Real.exp (M + Λ)) • μ := by
  rw [siteKernel_fieldDensity hψ hlam]
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ z in A, ENNReal.ofReal (siteU V ψ lam i x z / ∫ z', siteU V ψ lam i x z' ∂μ) ∂μ
      ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.exp (M + Λ)) ∂μ :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (siteU_div_le hψ hlam hΛ i x z)
    _ = _ := by rw [setLIntegral_const]

end Bounds

section Dobrushin

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

lemma abs_exp_sub_exp_le {u v M : ℝ} (hu : u ≤ M) (hv : v ≤ M) :
    |Real.exp u - Real.exp v| ≤ Real.exp M * |u - v| := by
  wlog h : v ≤ u generalizing u v
  · have := this hv hu (le_of_not_ge h)
    rwa [abs_sub_comm (Real.exp v), abs_sub_comm v u] at this
  rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
  have h1 : 1 - (u - v) ≤ Real.exp (-(u - v)) := by linarith [Real.add_one_le_exp (-(u - v))]
  have h2 : Real.exp u - Real.exp v ≤ Real.exp u * (u - v) := by
    have : Real.exp v = Real.exp u * Real.exp (-(u - v)) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    nlinarith [Real.exp_pos u]
  calc Real.exp u - Real.exp v ≤ Real.exp u * (u - v) := h2
    _ ≤ Real.exp M * (u - v) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hu) (sub_nonneg.2 h)

/-- Change of one other coordinate: the unnormalized conditional densities differ by at most
`2 e^M lam γ` in `L¹(μ)`. -/
lemma integral_abs_siteU_sub_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {x y : Fin n → E} (hxy : ∀ k, k ≠ j → x k = y k) :
    ∫ z, |siteU V ψ lam i x z - siteU V ψ lam i y z| ∂μ ≤ Real.exp M * (2 * lam * V.γ) := by
  have hpt : ∀ z, |siteU V ψ lam i x z - siteU V ψ lam i y z|
      ≤ Real.exp M * lam * (V.q z (x j) + V.q z (y j)) := by
    intro z
    unfold siteU
    refine (abs_exp_sub_exp_le (M := M) ?_ ?_).trans ?_
    · have := mul_nonneg hlam (sumq_nonneg V i x z); linarith [hψ.le z]
    · have := mul_nonneg hlam (sumq_nonneg V i y z); linarith [hψ.le z]
    · have hsum : ∑ l ∈ Finset.univ.erase i, V.q z (x l) - ∑ l ∈ Finset.univ.erase i, V.q z (y l)
          = V.q z (x j) - V.q z (y j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_eq_single_of_mem j (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩) ?_
        intro l _ hl
        rw [hxy l hl]; ring
      have : ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (x l)
          - (ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (y l))
          = -(lam * (V.q z (x j) - V.q z (y j))) := by rw [← hsum]; ring
      rw [this, abs_neg, abs_mul, abs_of_nonneg hlam]
      have h3 : |V.q z (x j) - V.q z (y j)| ≤ V.q z (x j) + V.q z (y j) := by
        rw [abs_le]; constructor <;> linarith [V.q_nonneg z (x j), V.q_nonneg z (y j)]
      calc Real.exp M * (lam * |V.q z (x j) - V.q z (y j)|)
          ≤ Real.exp M * (lam * (V.q z (x j) + V.q z (y j))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hlam) (Real.exp_pos _).le
        _ = _ := by ring
  have hi : Integrable (fun z => |siteU V ψ lam i x z - siteU V ψ lam i y z|) μ :=
    ((integrable_siteU hψ hlam i x).sub (integrable_siteU hψ hlam i y)).abs
  have hi2 : Integrable (fun z => Real.exp M * lam * (V.q z (x j) + V.q z (y j))) μ :=
    ((integrable_q_left V (x j)).add (integrable_q_left V (y j))).const_mul _
  calc ∫ z, |siteU V ψ lam i x z - siteU V ψ lam i y z| ∂μ
      ≤ ∫ z, Real.exp M * lam * (V.q z (x j) + V.q z (y j)) ∂μ := integral_mono hi hi2 hpt
    _ = Real.exp M * lam * (∫ z, V.q z (x j) ∂μ + ∫ z, V.q z (y j) ∂μ) := by
        rw [integral_const_mul, integral_add (integrable_q_left V _) (integrable_q_left V _)]
    _ ≤ Real.exp M * lam * (V.γ + V.γ) := by
        gcongr
        · exact integral_q_left_le V _
        · exact integral_q_left_le V _
    _ = _ := by ring

/-- **Dobrushin coefficients** (`A:eq:weak-dobrushin`, second part): changing one other coordinate
changes the one-site conditional law by at most `4 e^{M+Λ} lam γ` in total variation. -/
lemma abs_siteKernel_sub_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ}
    (hΛ : M₁ + lam * n * V.γ ≤ Λ) {i j : Fin n} (hij : i ≠ j) {x y : Fin n → E}
    (hxy : ∀ k, k ≠ j → x k = y k) {A : Set E} (hA : MeasurableSet A) :
    |(siteKernel μ (fieldDensity V ψ lam n) i x).real A
        - (siteKernel μ (fieldDensity V ψ lam n) i y).real A|
      ≤ 4 * Real.exp (M + Λ) * lam * V.γ := by
  rw [siteKernel_fieldDensity hψ hlam, siteKernel_fieldDensity hψ hlam]
  have h := abs_real_withDensity_sub_le (μ := μ) (siteU V ψ lam i x) (siteU V ψ lam i y)
    (measurable_siteU hψ.measurable V lam i x) (measurable_siteU hψ.measurable V lam i y)
    (fun z => (siteU_pos V ψ lam i x z).le) (fun z => (siteU_pos V ψ lam i y z).le)
    (integrable_siteU hψ hlam i x) (integrable_siteU hψ hlam i y) _ _ rfl rfl
    (integral_siteU_pos hψ hlam i x) (integral_siteU_pos hψ hlam i y) hA
  refine h.trans ?_
  have hD := integral_abs_siteU_sub_le (V := V) hψ hlam hij hxy
  have hZ : Real.exp (-Λ) ≤ ∫ z, siteU V ψ lam i x z ∂μ :=
    le_trans (Real.exp_le_exp.2 (by linarith)) (exp_le_integral_siteU (V := V) hψ hlam i x)
  have hZpos : 0 < ∫ z, siteU V ψ lam i x z ∂μ := integral_siteU_pos hψ hlam i x
  rw [div_le_iff₀ hZpos]
  have hexp : Real.exp (M + Λ) * Real.exp (-Λ) = Real.exp M := by rw [← Real.exp_add]; ring_nf
  have hc : 0 ≤ 2 * (Real.exp M * (2 * lam * V.γ)) := by
    have := V.γ_nonneg; positivity
  calc 2 * ∫ z, |siteU V ψ lam i x z - siteU V ψ lam i y z| ∂μ
      ≤ 2 * (Real.exp M * (2 * lam * V.γ)) := by linarith
    _ = (4 * Real.exp (M + Λ) * lam * V.γ) * Real.exp (-Λ) := by
        rw [show 4 * Real.exp (M + Λ) * lam * V.γ * Real.exp (-Λ)
          = 4 * (Real.exp (M + Λ) * Real.exp (-Λ)) * lam * V.γ by ring, hexp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by have := V.γ_nonneg; positivity)

/-- Comparison of the one-site conditional laws of two ensembles with different one-body fields
(same pair kernel, same coupling): total variation at most `2 e^{M+Λ} D`, where
`D ≥ ‖ψ - ψ'‖_{L¹(μ)}`. -/
lemma abs_siteKernel_sub_field_le (hψ : IsField μ ψ M M₁) (hψ' : IsField μ ψ' M M₁')
    (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ) {D : ℝ}
    (hD : ∫ z, |ψ z - ψ' z| ∂μ ≤ D) (i : Fin n) (x : Fin n → E) {A : Set E}
    (hA : MeasurableSet A) :
    |(siteKernel μ (fieldDensity V ψ lam n) i x).real A
        - (siteKernel μ (fieldDensity V ψ' lam n) i x).real A|
      ≤ 2 * Real.exp (M + Λ) * D := by
  rw [siteKernel_fieldDensity hψ hlam, siteKernel_fieldDensity hψ' hlam]
  have h := abs_real_withDensity_sub_le (μ := μ) (siteU V ψ lam i x) (siteU V ψ' lam i x)
    (measurable_siteU hψ.measurable V lam i x) (measurable_siteU hψ'.measurable V lam i x)
    (fun z => (siteU_pos V ψ lam i x z).le) (fun z => (siteU_pos V ψ' lam i x z).le)
    (integrable_siteU hψ hlam i x) (integrable_siteU hψ' hlam i x) _ _ rfl rfl
    (integral_siteU_pos hψ hlam i x) (integral_siteU_pos hψ' hlam i x) hA
  refine h.trans ?_
  have hD1 : ∫ z, |siteU V ψ lam i x z - siteU V ψ' lam i x z| ∂μ ≤ Real.exp M * D := by
    have hpt : ∀ z, |siteU V ψ lam i x z - siteU V ψ' lam i x z| ≤ Real.exp M * |ψ z - ψ' z| := by
      intro z
      unfold siteU
      refine (abs_exp_sub_exp_le (M := M) ?_ ?_).trans ?_
      · have := mul_nonneg hlam (sumq_nonneg V i x z); linarith [hψ.le z]
      · have := mul_nonneg hlam (sumq_nonneg V i x z); linarith [hψ'.le z]
      · apply le_of_eq; congr 2; ring
    have hi : Integrable (fun z => |siteU V ψ lam i x z - siteU V ψ' lam i x z|) μ :=
      ((integrable_siteU hψ hlam i x).sub (integrable_siteU hψ' hlam i x)).abs
    have hi2 : Integrable (fun z => Real.exp M * |ψ z - ψ' z|) μ :=
      (hψ.integrable.sub hψ'.integrable).abs.const_mul _
    calc _ ≤ ∫ z, Real.exp M * |ψ z - ψ' z| ∂μ := integral_mono hi hi2 hpt
      _ = Real.exp M * ∫ z, |ψ z - ψ' z| ∂μ := integral_const_mul _ _
      _ ≤ Real.exp M * D := mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le
  have hZ : Real.exp (-Λ) ≤ ∫ z, siteU V ψ lam i x z ∂μ :=
    le_trans (Real.exp_le_exp.2 (by linarith)) (exp_le_integral_siteU (V := V) hψ hlam i x)
  have hZpos : 0 < ∫ z, siteU V ψ lam i x z ∂μ := integral_siteU_pos hψ hlam i x
  rw [div_le_iff₀ hZpos]
  have hexp : Real.exp (M + Λ) * Real.exp (-Λ) = Real.exp M := by rw [← Real.exp_add]; ring_nf
  have hD0 : 0 ≤ D := le_trans (integral_nonneg fun z => abs_nonneg _) hD
  calc 2 * ∫ z, |siteU V ψ lam i x z - siteU V ψ' lam i x z| ∂μ
      ≤ 2 * (Real.exp M * D) := by linarith
    _ = (2 * Real.exp (M + Λ) * D) * Real.exp (-Λ) := by
        rw [show 2 * Real.exp (M + Λ) * D * Real.exp (-Λ)
          = 2 * (Real.exp (M + Λ) * Real.exp (-Λ)) * D by ring, hexp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by positivity)

end Dobrushin

section Pinned

variable [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- The normalized density of the pinned ensemble. -/
abbrev pinnedDensity (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (a : B → E) : (Fin n → E) → ℝ≥0∞ :=
  fieldDensity V (pinField V lam a) lam n

lemma pinnedLaw_eq (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (a : B → E) :
    pinnedLaw V lam n a = (Measure.pi fun _ : Fin n => μ).withDensity (pinnedDensity V lam n a) := rfl

lemma isField_pinField (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) :
    IsField μ (pinField V lam a) V.M (V.M' + lam * Fintype.card B * V.γ) where
  measurable := by
    unfold pinField
    refine V.measurable_φ.sub (Measurable.const_mul (Finset.measurable_sum _ fun b _ => ?_) _)
    exact V.measurable_q.comp (measurable_id.prodMk measurable_const)
  le z := by
    unfold pinField
    have : 0 ≤ lam * ∑ b, V.q z (a b) :=
      mul_nonneg hlam (Finset.sum_nonneg fun b _ => V.q_nonneg _ _)
    linarith [V.φ_le z]
  integrable := by
    unfold pinField
    exact V.integrable_φ.sub (Integrable.const_mul
      (integrable_finset_sum _ fun b _ => integrable_q_left V (a b)) _)
  ge := by
    unfold pinField
    rw [integral_sub V.integrable_φ (Integrable.const_mul
      (integrable_finset_sum _ fun b _ => integrable_q_left V (a b)) _), integral_const_mul,
      integral_finset_sum _ fun b _ => integrable_q_left V (a b)]
    have h1 : ∑ b, ∫ z, V.q z (a b) ∂μ ≤ Fintype.card B * V.γ := by
      calc ∑ b, ∫ z, V.q z (a b) ∂μ ≤ ∑ _b : B, V.γ :=
            Finset.sum_le_sum fun b _ => integral_q_left_le V (a b)
        _ = Fintype.card B * V.γ := by simp
    have := mul_le_mul_of_nonneg_left h1 hlam
    nlinarith [V.neg_le_integral_φ]

/-- The coefficient `κ = 4 e^{M + M' + βγ} β γ` of `A:eq:weak-dobrushin`. -/
def weakKappa (V : WeakPotential μ) (β : ℝ) : ℝ :=
  4 * Real.exp (V.M + V.M' + β * V.γ) * (β * V.γ)

lemma weakKappa_nonneg (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ weakKappa V β := by
  have := V.γ_nonneg
  unfold weakKappa; positivity

/-- **Smallness** (`κ < 1/2` from smallness of `γ`): if `βγ ≤ min(1, (16 e^{M+M'+1})⁻¹)`, then
`κ < 1/2`. -/
lemma weakKappa_lt_half (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β)
    (h : β * V.γ ≤ min 1 (1 / (16 * Real.exp (V.M + V.M' + 1)))) : weakKappa V β < 1 / 2 := by
  have hx : 0 ≤ β * V.γ := mul_nonneg hβ V.γ_nonneg
  have h1 : β * V.γ ≤ 1 := h.trans (min_le_left _ _)
  have h2 : β * V.γ ≤ 1 / (16 * Real.exp (V.M + V.M' + 1)) := h.trans (min_le_right _ _)
  have he : Real.exp (V.M + V.M' + β * V.γ) ≤ Real.exp (V.M + V.M' + 1) :=
    Real.exp_le_exp.2 (by linarith)
  have hE := Real.exp_pos (V.M + V.M' + 1)
  unfold weakKappa
  calc 4 * Real.exp (V.M + V.M' + β * V.γ) * (β * V.γ)
      ≤ 4 * Real.exp (V.M + V.M' + 1) * (1 / (16 * Real.exp (V.M + V.M' + 1))) := by gcongr
    _ = 1 / 4 := by field_simp; norm_num
    _ < 1 / 2 := by norm_num

/-- The smallness threshold exists for every `(M, M')`. -/
lemma exists_small_weakKappa (V : WeakPotential μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 ≤ β → β * V.γ ≤ δ → weakKappa V β < 1 / 2 :=
  ⟨_, lt_min one_pos (by positivity), fun β hβ h => weakKappa_lt_half V hβ h⟩

/-- Parameters of the weak ensemble: `lam = β/N`, `n` free coordinates and a pin set `B` with
`n + |B| ≤ N`. -/
lemma lam_bound {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) :
    β / N * Fintype.card B + β / N * n ≤ β := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have : ((n : ℝ) + Fintype.card B) ≤ N := by exact_mod_cast hN
  rw [← mul_add, mul_comm, ← mul_div_assoc, div_le_iff₀ hN']
  nlinarith

/-- **`A:eq:weak-dobrushin`**: for the pinned weak ensemble with `lam = β/N`, `n + |B| ≤ N`: the
one-site conditional laws are `≤ C μ`, `C = exp(M + M' + βγ)`. -/
theorem weak_siteKernel_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (i : Fin n) (x : Fin n → E) :
    siteKernel μ (pinnedDensity V (β / N) n a) i x
      ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) • μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have := siteKernel_le_smul (V := V) (isField_pinField V hlam a) hlam
    (Λ := V.M' + β * V.γ) (n := n) (by
      have := mul_le_mul_of_nonneg_right (lam_bound (B := B) hβ hN0 hN) V.γ_nonneg
      nlinarith) i x
  rwa [show V.M + (V.M' + β * V.γ) = V.M + V.M' + β * V.γ by ring] at this

/-- **`A:eq:weak-dobrushin`**: `c_ij ≤ κ/N` for the pinned weak ensemble. -/
theorem weak_dobrushin (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) :
    ∀ i j : Fin n, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
      MeasurableSet A →
      |(siteKernel μ (pinnedDensity V (β / N) n a) i x).real A
          - (siteKernel μ (pinnedDensity V (β / N) n a) i y).real A| ≤ weakKappa V β / N := by
  intro i j hij x y hxy A hA
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have := abs_siteKernel_sub_le (V := V) (isField_pinField V hlam a) hlam
    (Λ := V.M' + β * V.γ) (n := n) (by
      have := mul_le_mul_of_nonneg_right (lam_bound (B := B) hβ hN0 hN) V.γ_nonneg
      nlinarith) hij hxy hA
  refine this.trans (le_of_eq ?_)
  unfold weakKappa
  rw [show V.M + (V.M' + β * V.γ) = V.M + V.M' + β * V.γ by ring]
  ring

end Pinned

section Wu

variable [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- `A:eq:resampling` for the pinned weak ensemble: `Var_P(F) ≤ 2 ∑ᵢ E_P[Var_i F]`. -/
theorem weak_resampling (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    evariance F (pinnedLaw V (β / N) n a)
      ≤ 2 * ∑ i, ∫⁻ x, evariance (fun z => F (update x i z))
          (siteKernel μ (pinnedDensity V (β / N) n a) i x) ∂(pinnedLaw V (β / N) n a) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  exact wu_resampling_uniform μ (pinnedDensity V (β / N) n a)
    (measurable_fieldDensity hψ.measurable V _ n) (fieldDensity_pos hψ hlam n) _
    (fieldDensity_le hψ hlam n) (lintegral_fieldDensity hψ hlam n) N hN0
    (le_trans (Nat.le_add_right n _) hN) _ (weakKappa_nonneg V hβ) hκ
    (weak_dobrushin V hβ hN0 hN a) F hF

/-- **Linear form** (`A:eq:weak-linear`) for the pinned weak ensemble, with its own marginal:
if every one-coordinate marginal of the pinned law is `π`, then
`Var(∑ᵢ f(yᵢ)) ≤ 2 n Var_π(f)`. -/
theorem weak_linear_variance (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (π : Measure E)
    (hπ : ∀ i, (pinnedLaw V (β / N) n a).map (fun x => x i) = π)
    (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) (pinnedLaw V (β / N) n a)
      ≤ 2 * n * evariance f π := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  have hnN : n ≤ N := le_trans (Nat.le_add_right n _) hN
  exact wu_linear μ (pinnedDensity V (β / N) n a)
    (measurable_fieldDensity hψ.measurable V _ n) (fieldDensity_pos hψ hlam n) _
    (fieldDensity_le hψ hlam n) (lintegral_fieldDensity hψ hlam n) (fun _ _ => weakKappa V β / N)
    (fun _ _ => div_nonneg (weakKappa_nonneg V hβ) (Nat.cast_nonneg N))
    (weak_dobrushin V hβ hN0 hN a)
    (fun i => (row_sum_le_of_uniform hN0 hnN (weakKappa_nonneg V hβ) i).trans hκ) π hπ f hf

end Wu

section Compare2

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

/-- **Functional single-site comparison for two weak ensembles** with different one-body fields
(`ψ` versus `ψ'`; same `q`, `lam`, `n`).  If `Λ ≥ M₁ + lam n γ`, `D ≥ ‖ψ - ψ'‖_{L¹(μ)}` and the
Dobrushin row sums of the first ensemble are `≤ r < 1`, then for every bounded measurable `f` with
coordinate oscillations `Δ`:
`|E_ψ f - E_ψ' f| ≤ 2 e^{M+Λ} D (1 - r)⁻¹ ∑ⱼ Δⱼ`. -/
theorem rvh_field_comparison {n : ℕ} [NeZero n] (hψ : IsField μ ψ M M₁) (hψ' : IsField μ ψ' M M₁')
    (hlam : 0 ≤ lam) {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ) {D : ℝ}
    (hD : ∫ z, |ψ z - ψ' z| ∂μ ≤ D) {r : ℝ}
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M + Λ) * lam * V.γ ≤ r)
    (hr : r < 1) {B : ℝ} {f : (Fin n → E) → ℝ} (hf : Measurable f) (hbd : ∀ x, |f x| ≤ B)
    {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j) (hosc : OscBound f Δ) :
    |∫ x, f x ∂(fieldLaw V ψ lam n) - ∫ x, f x ∂(fieldLaw V ψ' lam n)|
      ≤ 2 * Real.exp (M + Λ) * D / (1 - r) * ∑ j, Δ j := by
  have hc0 : 0 ≤ 4 * Real.exp (M + Λ) * lam * V.γ := by have := V.γ_nonneg; positivity
  have hD0 : 0 ≤ D := le_trans (integral_nonneg fun z => abs_nonneg _) hD
  have hdob : IsDobrushin (fieldSpec (V := V) hψ hlam n) (fun _ _ => 4 * Real.exp (M + Λ) * lam * V.γ) :=
    ⟨fun _ _ => hc0, fun i j hij x y hxy A hA => by
      exact abs_siteKernel_sub_le (V := V) hψ hlam hΛ hij hxy hA⟩
  exact rvh_comparison (fieldSpec (V := V) hψ hlam n) (fieldSpec (V := V) hψ' hlam n) hdob hrow hr
    (b := 2 * Real.exp (M + Λ) * D) (by positivity)
    (fun i x A hA => abs_siteKernel_sub_field_le (V := V) hψ hψ' hlam hΛ hD i x hA) hf hbd hΔ hosc

end Compare2

section Event

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

lemma map_real_eval_eq {n : ℕ} (P : Measure (Fin n → E)) (j : Fin n) {A : Set E}
    (hA : MeasurableSet A) :
    (P.map (fun y => y j)).real A = P.real ((fun y : Fin n → E => y j) ⁻¹' A) := by
  rw [Measure.real, Measure.real, Measure.map_apply (measurable_pi_apply j) hA]

/-- The event version of `rvh_field_comparison` (`f = 1_A(y_j)`): marginals of coordinate `j`
differ by at most `2 e^{M+Λ} D (1 - r)⁻¹` in total variation. -/
theorem rvh_field_event {n : ℕ} (j : Fin n) (hψ : IsField μ ψ M M₁) (hψ' : IsField μ ψ' M M₁')
    (hlam : 0 ≤ lam) {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ) {D : ℝ}
    (hD : ∫ z, |ψ z - ψ' z| ∂μ ≤ D) {r : ℝ}
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M + Λ) * lam * V.γ ≤ r)
    (hr : r < 1) {A : Set E} (hA : MeasurableSet A) :
    |((fieldLaw V ψ lam n).map (fun y => y j)).real A
        - ((fieldLaw V ψ' lam n).map (fun y => y j)).real A|
      ≤ 2 * Real.exp (M + Λ) * D / (1 - r) := by
  haveI : NeZero n := NeZero.of_pos j.pos
  have hmeas : MeasurableSet ((fun y : Fin n → E => y j) ⁻¹' A) := measurable_pi_apply j hA
  have hP : ∀ (ψ'' : E → ℝ) (M₂ : ℝ) (h : IsField μ ψ'' M M₂),
      ∫ x, ((fun y : Fin n → E => y j) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ) x
        ∂(fieldLaw V ψ'' lam n) = ((fieldLaw V ψ'' lam n).map (fun y => y j)).real A := by
    intro ψ'' M₂ h
    haveI : IsProbabilityMeasure (fieldLaw V ψ'' lam n) := (fieldSpec (V := V) h hlam n).isProb
    rw [integral_indicator_one hmeas, map_real_eval_eq _ j hA]
  have h := rvh_field_comparison (V := V) hψ hψ' hlam hΛ hD hrow hr (B := 1)
    (f := ((fun y : Fin n → E => y j) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ))
    ((measurable_const.indicator hmeas)) (fun x => by
      by_cases hx : x ∈ (fun y : Fin n → E => y j) ⁻¹' A <;> simp [hx])
    (Δ := fun k => if k = j then 1 else 0) (fun k => by split_ifs <;> norm_num)
    (fun k x y hxy => by
      by_cases hk : k = j
      · subst hk
        simp only [if_true]
        by_cases hx : x ∈ (fun y : Fin n → E => y k) ⁻¹' A <;>
          by_cases hy : y ∈ (fun y : Fin n → E => y k) ⁻¹' A <;> simp [hx, hy]
      · simp only [hk, if_false]
        have : (x j ∈ A ↔ y j ∈ A) := by rw [hxy j (Ne.symm hk)]
        by_cases hx : x ∈ (fun y : Fin n → E => y j) ⁻¹' A
        · have hy : y ∈ (fun y : Fin n → E => y j) ⁻¹' A := this.1 hx
          simp [hx, hy]
        · have hy : y ∉ (fun y : Fin n → E => y j) ⁻¹' A := fun h' => hx (this.2 h')
          simp [hx, hy])
  rw [hP ψ M₁ hψ, hP ψ' M₁' hψ'] at h
  simpa using h

end Event

section PinComparison

variable [IsProbabilityMeasure μ] {B B₁ B₂ : Type*} [Fintype B] [Fintype B₁] [Fintype B₂]

lemma four_exp_eq (V : WeakPotential μ) (β : ℝ) (N : ℕ) :
    4 * Real.exp (V.M + (V.M' + β * V.γ)) * (β / N) * V.γ = weakKappa V β / N := by
  unfold weakKappa
  rw [show V.M + (V.M' + β * V.γ) = V.M + V.M' + β * V.γ by ring]
  ring

lemma weak_Lambda_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) :
    V.M' + β / N * Fintype.card B * V.γ + β / N * n * V.γ ≤ V.M' + β * V.γ := by
  have := mul_le_mul_of_nonneg_right (lam_bound (B := B) hβ hN0 hN) V.γ_nonneg
  nlinarith

/-- **Single-coordinate comparison of two pinned weak ensembles** (event form). If the pin fields
of `a₁ : B₁ → E` and `a₂ : B₂ → E` differ by `≤ D` in `L¹(μ)` and `κ ≤ 1/2`, then
`sup_A |P₁(y_j ∈ A) - P₂(y_j ∈ A)| ≤ 4 e^{M+M'+βγ} D`. -/
theorem rvh_pin_event (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B₁ ≤ N) (a₁ : B₁ → E) (a₂ : B₂ → E) (hκ : weakKappa V β ≤ 1 / 2)
    {D : ℝ} (hD : ∫ z, |pinField V (β / N) a₁ z - pinField V (β / N) a₂ z| ∂μ ≤ D)
    (j : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / N) n a₁).map (fun y => y j)).real A
        - ((pinnedLaw V (β / N) n a₂).map (fun y => y j)).real A|
      ≤ 4 * Real.exp (V.M + V.M' + β * V.γ) * D := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ₁ := isField_pinField V hlam a₁
  have hψ₂ : IsField μ (pinField V (β / N) a₂) V.M (V.M' + β / N * Fintype.card B₂ * V.γ) :=
    isField_pinField V hlam a₂
  have hD0 : 0 ≤ D := le_trans (integral_nonneg fun z => abs_nonneg _) hD
  have hnN : n ≤ N := le_trans (Nat.le_add_right n _) hN
  have h := rvh_field_event (V := V) j hψ₁ hψ₂ hlam (Λ := V.M' + β * V.γ)
    (weak_Lambda_le V hβ hN0 hN) hD (r := weakKappa V β) (fun i => by
      rw [four_exp_eq]
      exact row_sum_le_of_uniform hN0 hnN (weakKappa_nonneg V hβ) i) (by linarith) hA
  refine h.trans ?_
  have e : V.M + (V.M' + β * V.γ) = V.M + V.M' + β * V.γ := by ring
  rw [e]
  have h1 : (1 : ℝ) / 2 ≤ 1 - weakKappa V β := by linarith
  have h2 : 0 ≤ 2 * Real.exp (V.M + V.M' + β * V.γ) * D := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc 2 * Real.exp (V.M + V.M' + β * V.γ) * D
      = 4 * Real.exp (V.M + V.M' + β * V.γ) * D * (1 / 2) := by ring
    _ ≤ 4 * Real.exp (V.M + V.M' + β * V.γ) * D * (1 - weakKappa V β) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

end PinComparison

section PinCases

variable [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- Add one more pin at `x` to the pin configuration `a`. -/
def pinsWith (a : B → E) (x : E) : Option B → E := fun o => o.elim x a

lemma integral_abs_pinField_changed (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam)
    (a a' : B → E) (b₀ : B) (hb : ∀ b, b ≠ b₀ → a b = a' b) :
    ∫ z, |pinField V lam a z - pinField V lam a' z| ∂μ ≤ 2 * lam * V.γ := by
  classical
  have hpt : ∀ z, |pinField V lam a z - pinField V lam a' z|
      ≤ lam * (V.q z (a b₀) + V.q z (a' b₀)) := by
    intro z
    have hsum : ∑ b, V.q z (a b) - ∑ b, V.q z (a' b) = V.q z (a b₀) - V.q z (a' b₀) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_single_of_mem b₀ (Finset.mem_univ _) ?_
      intro l _ hl
      rw [hb l hl]; ring
    have : pinField V lam a z - pinField V lam a' z
        = -(lam * (V.q z (a b₀) - V.q z (a' b₀))) := by
      unfold pinField; rw [← hsum]; ring
    rw [this, abs_neg, abs_mul, abs_of_nonneg hlam]
    have h3 : |V.q z (a b₀) - V.q z (a' b₀)| ≤ V.q z (a b₀) + V.q z (a' b₀) := by
      rw [abs_le]; constructor <;> linarith [V.q_nonneg z (a b₀), V.q_nonneg z (a' b₀)]
    exact mul_le_mul_of_nonneg_left h3 hlam
  have hi : Integrable (fun z => |pinField V lam a z - pinField V lam a' z|) μ :=
    ((isField_pinField V hlam a).integrable.sub (isField_pinField V hlam a').integrable).abs
  have hi2 : Integrable (fun z => lam * (V.q z (a b₀) + V.q z (a' b₀))) μ :=
    ((integrable_q_left V (a b₀)).add (integrable_q_left V (a' b₀))).const_mul _
  calc ∫ z, |pinField V lam a z - pinField V lam a' z| ∂μ
      ≤ ∫ z, lam * (V.q z (a b₀) + V.q z (a' b₀)) ∂μ := integral_mono hi hi2 hpt
    _ = lam * (∫ z, V.q z (a b₀) ∂μ + ∫ z, V.q z (a' b₀) ∂μ) := by
        rw [integral_const_mul, integral_add (integrable_q_left V _) (integrable_q_left V _)]
    _ ≤ lam * (V.γ + V.γ) := by
        gcongr
        · exact integral_q_left_le V _
        · exact integral_q_left_le V _
    _ = _ := by ring

lemma integral_abs_pinField_deleted (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam)
    (a : B → E) (x : E) :
    ∫ z, |pinField V lam (pinsWith a x) z - pinField V lam a z| ∂μ ≤ lam * V.γ := by
  have hpt : ∀ z, |pinField V lam (pinsWith a x) z - pinField V lam a z| = lam * V.q z x := by
    intro z
    have : pinField V lam (pinsWith a x) z - pinField V lam a z = -(lam * V.q z x) := by
      unfold pinField pinsWith
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some]
      ring
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg hlam (V.q_nonneg _ _))]
  simp_rw [hpt]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_q_left_le V x) hlam

/-- **Changed pin** (RvH comparison, `b_j ≤ C/N`): two pin configurations differing in one pin give
`sup_A |P_a(y_j ∈ A) - P_{a'}(y_j ∈ A)| ≤ 2κ/N`. -/
theorem rvh_pin_changed (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a a' : B → E) (b₀ : B) (hb : ∀ b, b ≠ b₀ → a b = a' b)
    (hκ : weakKappa V β ≤ 1 / 2) (j : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / N) n a).map (fun y => y j)).real A
        - ((pinnedLaw V (β / N) n a').map (fun y => y j)).real A|
      ≤ 2 * weakKappa V β / N := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have h := rvh_pin_event V hβ hN0 hN a a' hκ
    (integral_abs_pinField_changed V hlam a a' b₀ hb) j hA
  refine h.trans (le_of_eq ?_)
  unfold weakKappa
  ring

/-- **Deleted pin**: adding the pin `x` to `a` changes the marginals by at most `κ/N`. -/
theorem rvh_pin_deleted (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + (Fintype.card B + 1) ≤ N) (a : B → E) (x : E)
    (hκ : weakKappa V β ≤ 1 / 2) (j : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / N) n (pinsWith a x)).map (fun y => y j)).real A
        - ((pinnedLaw V (β / N) n a).map (fun y => y j)).real A|
      ≤ weakKappa V β / N := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have h := rvh_pin_event V hβ hN0 (B₁ := Option B) (by simpa [Fintype.card_option] using hN)
    (pinsWith a x) a hκ (integral_abs_pinField_deleted V hlam a x) j hA
  refine h.trans (le_of_eq ?_)
  unfold weakKappa
  ring

end PinCases

section Mixture

variable [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- Insert the value `x` at position `i` into the configuration `y`. -/
def insertAt {n : ℕ} (i : Fin (n + 1)) (x : E) (y : Fin n → E) : Fin (n + 1) → E :=
  Fin.insertNth (α := fun _ => E) i x y

@[simp] lemma insertAt_same {n : ℕ} (i : Fin (n + 1)) (x : E) (y : Fin n → E) :
    insertAt i x y i = x := by simp [insertAt]

@[simp] lemma insertAt_succAbove {n : ℕ} (i : Fin (n + 1)) (x : E) (y : Fin n → E) (k : Fin n) :
    insertAt i x y (i.succAbove k) = y k := by simp [insertAt]

lemma sum_insertAt (ψ : E → ℝ) {n : ℕ} (i : Fin (n + 1)) (x : E) (y : Fin n → E) :
    ∑ k, ψ (insertAt i x y k) = ψ x + ∑ k, ψ (y k) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma pairEnergy_eq_sub (V : WeakPotential μ) {n : ℕ} (y : Fin n → E) :
    pairEnergy V y = (1 / 2) * (∑ k, ∑ l, V.q (y k) (y l) - ∑ k, V.q (y k) (y k)) := by
  unfold pairEnergy
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]

lemma pairEnergy_insertAt (V : WeakPotential μ) {n : ℕ} (i : Fin (n + 1)) (x : E) (y : Fin n → E) :
    pairEnergy V (insertAt i x y) = pairEnergy V y + ∑ k, V.q x (y k) := by
  rw [pairEnergy_eq_sub, pairEnergy_eq_sub]
  have h1 : ∑ k, ∑ l, V.q (insertAt i x y k) (insertAt i x y l)
      = V.q x x + ∑ l, V.q x (y l) + (∑ k, V.q (y k) x + ∑ k, ∑ l, V.q (y k) (y l)) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [insertAt_same, insertAt_succAbove]
    simp_rw [Fin.sum_univ_succAbove _ i, insertAt_same, insertAt_succAbove]
    rw [Finset.sum_add_distrib]
  have h2 : ∑ k, V.q (insertAt i x y k) (insertAt i x y k)
      = V.q x x + ∑ k, V.q (y k) (y k) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp
  have h3 : ∑ k, V.q (y k) x = ∑ k, V.q x (y k) :=
    Finset.sum_congr rfl fun k _ => V.q_symm _ _
  rw [h1, h2, h3]
  ring

lemma pinField_pinsWith (V : WeakPotential μ) (lam : ℝ) (a : B → E) (x z : E) :
    pinField V lam (pinsWith a x) z = pinField V lam a z - lam * V.q z x := by
  unfold pinField pinsWith
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some]
  ring

lemma fieldWeight_insertAt (V : WeakPotential μ) (lam : ℝ) (a : B → E) {n : ℕ} (i : Fin (n + 1))
    (x : E) (y : Fin n → E) :
    fieldWeight V (pinField V lam a) lam (insertAt i x y)
      = ENNReal.ofReal (Real.exp (pinField V lam a x))
          * fieldWeight V (pinField V lam (pinsWith a x)) lam y := by
  unfold fieldWeight
  rw [sum_insertAt, pairEnergy_insertAt, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp_rw [pinField_pinsWith, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h3 : ∑ k, V.q (y k) x = ∑ k, V.q x (y k) :=
    Finset.sum_congr rfl fun k _ => V.q_symm _ _
  rw [h3]
  ring

lemma lintegral_set_fieldWeight {ψ : E → ℝ} {M M₁ lam : ℝ} (V : WeakPotential μ)
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) {S : Set (Fin n → E)} (hS : MeasurableSet S) :
    ∫⁻ y in S, fieldWeight V ψ lam y ∂(Measure.pi fun _ : Fin n => μ)
      = fieldNorm V ψ lam n * fieldLaw V ψ lam n S := by
  unfold fieldLaw fieldDensity
  rw [withDensity_apply _ hS, lintegral_mul_const _ (measurable_fieldWeight hψ.measurable V lam),
    ← mul_assoc, mul_comm (fieldNorm V ψ lam n), mul_assoc,
    ENNReal.mul_inv_cancel (fieldNorm_pos hψ.measurable V lam n).ne'
      (fieldNorm_lt_top hψ hlam n).ne, mul_one]

/-- Mixing weight over the value `x` of coordinate `i`. -/
def pinWeight (V : WeakPotential μ) (lam : ℝ) (a : B → E) (n : ℕ) (x : E) : ℝ≥0∞ :=
  fieldNorm V (pinField V lam (pinsWith a x)) lam n * ENNReal.ofReal (Real.exp (pinField V lam a x))
    * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹

/-- **Disintegration of the pinned ensemble**: the law of coordinate `i.succAbove j` in the
`(n+1)`-particle ensemble with pins `a` is the mixture, over the value `x` of coordinate `i`
with weight `pinWeight`, of the marginals of the `n`-particle ensemble with the extra pin `x`
(the conditional law of the other coordinates given `y_i = x`). -/
theorem pinned_marginal_succ (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) {A : Set E} (hA : MeasurableSet A) :
    ((pinnedLaw V lam (n + 1) a).map (fun y => y (i.succAbove j))) A
      = ∫⁻ x, pinWeight V lam a n x * ((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)) A ∂μ := by
  have hψ := isField_pinField V hlam a
  have hψx : ∀ x, IsField μ (pinField V lam (pinsWith a x)) V.M
      (V.M' + lam * Fintype.card (Option B) * V.γ) := fun x => isField_pinField V hlam _
  have hS : MeasurableSet ((fun y : Fin (n + 1) → E => y (i.succAbove j)) ⁻¹' A) :=
    measurable_pi_apply _ hA
  have hS' : MeasurableSet ((fun y : Fin n → E => y j) ⁻¹' A) := measurable_pi_apply _ hA
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  change (fieldLaw V (pinField V lam a) lam (n + 1)) _ = _
  unfold fieldLaw
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  set h : (Fin (n + 1) → E) → ℝ≥0∞ := fun y =>
    ((fun y : Fin (n + 1) → E => y (i.succAbove j)) ⁻¹' A).indicator
      (fieldDensity V (pinField V lam a) lam (n + 1)) y with hh
  have hhm : Measurable h :=
    (measurable_fieldDensity hψ.measurable V lam (n + 1)).indicator hS
  have step1 : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, h (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => h (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  rw [step1, lintegral_prod (fun p => h (e.symm p)) (hhm.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [hsymm]
  have hx : ∀ y : Fin n → E, h (insertAt i x y)
      = ((fun y : Fin n → E => y j) ⁻¹' A).indicator
          (fun y => (ENNReal.ofReal (Real.exp (pinField V lam a x))
            * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹)
            * fieldWeight V (pinField V lam (pinsWith a x)) lam y) y := by
    intro y
    by_cases hm : y j ∈ A
    · have h1 : insertAt i x y ∈ (fun y : Fin (n + 1) → E => y (i.succAbove j)) ⁻¹' A := by
        simp [hm]
      have h2 : y ∈ (fun y : Fin n → E => y j) ⁻¹' A := hm
      simp only [hh]
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      unfold fieldDensity
      rw [fieldWeight_insertAt]; ring
    · have h1 : insertAt i x y ∉ (fun y : Fin (n + 1) → E => y (i.succAbove j)) ⁻¹' A := by
        simp [hm]
      have h2 : y ∉ (fun y : Fin n → E => y j) ⁻¹' A := hm
      simp only [hh]
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  simp_rw [hx]
  rw [lintegral_indicator hS', lintegral_const_mul' _ _ (by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (fieldNorm_pos hψ.measurable V lam (n + 1)).ne')),
    lintegral_set_fieldWeight V (hψx x) hlam n hS']
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  change _ = _ * (fieldLaw V (pinField V lam (pinsWith a x)) lam n _)
  unfold pinWeight
  ring

lemma isProb_pinnedLaw (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (a : B → E) :
    IsProbabilityMeasure (pinnedLaw V lam n a) :=
  (fieldSpec (V := V) (isField_pinField V hlam a) hlam n).isProb

lemma lintegral_pinWeight (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) :
    ∫⁻ x, pinWeight V lam a n x ∂μ = 1 := by
  have h := pinned_marginal_succ V hlam a i j (A := Set.univ) MeasurableSet.univ
  have := isProb_pinnedLaw V hlam (n + 1) a
  have : ∀ x, IsProbabilityMeasure (pinnedLaw V lam n (pinsWith a x)) :=
    fun x => isProb_pinnedLaw V hlam n _
  have e1 : ((pinnedLaw V lam (n + 1) a).map (fun y => y (i.succAbove j))) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  have e2 : ∀ x, ((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)) Set.univ = 1 := fun x => by
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  rw [e1] at h
  simp_rw [e2, mul_one] at h
  exact h.symm

/-- **Averaging over the pin** (`A:eq:weak-pin-comparison`): in the `(n+1)`-particle weak ensemble
with fixed pins `a` (`n + 1 + |B| ≤ N`, `lam = β/N`), the conditional law of `y_j` given
`y_i = x` (the explicit pinned `n`-particle ensemble with the extra pin `x`) differs from the
unconditioned marginal of `y_j` by at most `2κ/N` in total variation, uniformly in `x`:
`sup_A |Law(y_j | y_i = x)(A) - π(A)| ≤ 2 κ / N`, `κ = weakKappa V β`. -/
theorem rvh_pin_comparison (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + 1 + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (i : Fin (n + 1)) (j : Fin n) (x : E) {A : Set E} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / N) n (pinsWith a x)).map (fun y => y j)).real A
        - ((pinnedLaw V (β / N) (n + 1) a).map (fun y => y (i.succAbove j))).real A|
      ≤ 2 * weakKappa V β / N := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have := isProb_pinnedLaw V hlam (n + 1) a
  have : ∀ x, IsProbabilityMeasure (pinnedLaw V (β / N) n (pinsWith a x)) :=
    fun x => isProb_pinnedLaw V hlam n _
  set ε : ℝ := 2 * weakKappa V β / N with hε
  have hε0 : 0 ≤ ε := by
    have := weakKappa_nonneg V hβ
    positivity
  set r : E → ℝ := fun x' =>
    ((pinnedLaw V (β / N) n (pinsWith a x')).map (fun y => y j)).real A with hr
  have hcl : ∀ x', |r x - r x'| ≤ ε := fun x' => by
    have := rvh_pin_changed (B := Option B) V hβ hN0 (by rw [Fintype.card_option]; omega)
      (pinsWith a x) (pinsWith a x') none (fun b hb => by
        cases b with
        | none => exact absurd rfl hb
        | some b => rfl) hκ j hA
    exact this
  have hmix := pinned_marginal_succ V hlam a i j hA
  have hw := lintegral_pinWeight V hlam a i j
  set X := ((pinnedLaw V (β / N) (n + 1) a).map (fun y => y (i.succAbove j))) A with hX
  have hXt : X ≠ ∞ := by
    rw [hX, Measure.map_apply (measurable_pi_apply _) hA]
    exact measure_ne_top _ _
  have hp : ∀ x', ((pinnedLaw V (β / N) n (pinsWith a x')).map (fun y => y j)) A
      = ENNReal.ofReal (r x') := fun x' => by
    rw [hr]; simp only [Measure.real]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hr0 : ∀ x', 0 ≤ r x' := fun x' => measureReal_nonneg
  have hup : X ≤ ENNReal.ofReal (r x + ε) := by
    rw [hmix]
    calc ∫⁻ x', pinWeight V (β / N) a n x' * ((pinnedLaw V (β / N) n (pinsWith a x')).map (fun y => y j)) A ∂μ
        ≤ ∫⁻ x', pinWeight V (β / N) a n x' * ENNReal.ofReal (r x + ε) ∂μ := by
          refine lintegral_mono fun x' => mul_le_mul' le_rfl ?_
          rw [hp]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hcl x'
          rw [abs_le] at this
          linarith
      _ = ENNReal.ofReal (r x + ε) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hw, one_mul]
  have hlo : ENNReal.ofReal (r x - ε) ≤ X := by
    rw [hmix]
    calc ENNReal.ofReal (r x - ε) = ∫⁻ x', pinWeight V (β / N) a n x' * ENNReal.ofReal (r x - ε) ∂μ := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hw, one_mul]
      _ ≤ _ := by
          refine lintegral_mono fun x' => mul_le_mul' le_rfl ?_
          rw [hp]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hcl x'
          rw [abs_le] at this
          linarith
  have h1 : X.toReal ≤ r x + ε :=
    ENNReal.toReal_le_of_le_ofReal (by linarith [hr0 x]) hup
  have h2 : r x - ε ≤ X.toReal := (ENNReal.ofReal_le_iff_le_toReal hXt).1 hlo
  rw [abs_le]
  constructor
  · show -ε ≤ r x - X.toReal
    linarith
  · show r x - X.toReal ≤ ε
    linarith

/-- Averaging: if `ω` is a probability weight and `p x ∈ [0, 1]`-valued with `|p x - c| ≤ ε`,
then the mixture `∫ ω p` is within `ε` of `c`. -/
lemma abs_toReal_lintegral_sub_le {ω p : E → ℝ≥0∞} (hω : ∫⁻ x, ω x ∂μ = 1)
    (hp : ∀ x, p x ≠ ∞) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (h : ∀ x, |(p x).toReal - c| ≤ ε) :
    |(∫⁻ x, ω x * p x ∂μ).toReal - c| ≤ ε := by
  have hup : ∫⁻ x, ω x * p x ∂μ ≤ ENNReal.ofReal (c + ε) := by
    calc ∫⁻ x, ω x * p x ∂μ ≤ ∫⁻ x, ω x * ENNReal.ofReal (c + ε) ∂μ := by
          refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
          rw [← ENNReal.ofReal_toReal (hp x)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := h x; rw [abs_le] at this; linarith
      _ = ENNReal.ofReal (c + ε) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hω, one_mul]
  have hlo : ENNReal.ofReal (c - ε) ≤ ∫⁻ x, ω x * p x ∂μ := by
    calc ENNReal.ofReal (c - ε) = ∫⁻ x, ω x * ENNReal.ofReal (c - ε) ∂μ := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hω, one_mul]
      _ ≤ _ := by
          refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
          rw [← ENNReal.ofReal_toReal (hp x)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := h x; rw [abs_le] at this; linarith
  have hXt : ∫⁻ x, ω x * p x ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  have h1 := ENNReal.toReal_le_of_le_ofReal (by linarith) hup
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hXt).1 hlo
  rw [abs_le]; constructor <;> linarith

/-- **Removed coordinate** (`Q:lem:pin`, one removed coordinate): the marginal of the
`(n+1)`-particle ensemble (pins `a`, same `lam = β/N`) differs from the marginal of the
`n`-particle ensemble with the same pins by at most `κ/N` in total variation. -/
theorem rvh_pin_removed (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + 1 + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (i : Fin (n + 1)) (j : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / N) (n + 1) a).map (fun y => y (i.succAbove j))).real A
        - ((pinnedLaw V (β / N) n a).map (fun y => y j)).real A| ≤ weakKappa V β / N := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have := isProb_pinnedLaw V hlam (n + 1) a
  have : ∀ x, IsProbabilityMeasure (pinnedLaw V (β / N) n (pinsWith a x)) :=
    fun x => isProb_pinnedLaw V hlam n _
  have hmix := pinned_marginal_succ V hlam a i j hA
  have hw := lintegral_pinWeight V hlam a i j
  have hε0 : 0 ≤ weakKappa V β / N := div_nonneg (weakKappa_nonneg V hβ) (Nat.cast_nonneg N)
  have hc0 : 0 ≤ ((pinnedLaw V (β / N) n a).map (fun y => y j)).real A := measureReal_nonneg
  have h := abs_toReal_lintegral_sub_le (μ := μ) (ω := pinWeight V (β / N) a n)
    (p := fun x' => ((pinnedLaw V (β / N) n (pinsWith a x')).map (fun y => y j)) A) hw
    (fun x' => by
      rw [Measure.map_apply (measurable_pi_apply _) hA]; exact measure_ne_top _ _)
    hc0 hε0 (fun x' => rvh_pin_deleted V hβ hN0 (by omega) a x' hκ j hA)
  simp only [Measure.real]
  rw [hmix]
  exact h

end Mixture

section Symm

variable [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

lemma pairEnergy_comp_perm (V : WeakPotential μ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (y : Fin n → E) :
    pairEnergy V (y ∘ σ) = pairEnergy V y := by
  rw [pairEnergy_eq_sub, pairEnergy_eq_sub]
  congr 2
  · have h1 : ∀ k, ∑ l, V.q ((y ∘ σ) k) ((y ∘ σ) l) = ∑ l, V.q (y (σ k)) (y l) := fun k =>
      Equiv.sum_comp σ (fun l => V.q (y (σ k)) (y l))
    simp_rw [h1]
    exact Equiv.sum_comp σ (fun k => ∑ l, V.q (y k) (y l))
  · exact Equiv.sum_comp σ (fun k => V.q (y k) (y k))

lemma fieldDensity_comp_perm (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (y : Fin n → E) :
    fieldDensity V ψ lam n (y ∘ σ) = fieldDensity V ψ lam n y := by
  unfold fieldDensity fieldWeight
  rw [pairEnergy_comp_perm]
  have := Equiv.sum_comp σ (fun k => ψ (y k))
  simp only [Function.comp]
  rw [this]

/-- **Linear form for the exchangeable pinned ensemble**: with `π` the common one-point marginal
of the pinned law, `Var(∑ᵢ f(yᵢ)) ≤ 2 n Var_π(f)`. -/
theorem weak_linear_variance_symm (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} [NeZero n]
    (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) (pinnedLaw V (β / N) n a)
      ≤ 2 * n * evariance f ((pinnedLaw V (β / N) n a).map (fun x => x 0)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  have hnN : n ≤ N := le_trans (Nat.le_add_right n _) hN
  exact wu_linear_symm μ (pinnedDensity V (β / N) n a)
    (measurable_fieldDensity hψ.measurable V _ n) (fieldDensity_pos hψ hlam n) _
    (fieldDensity_le hψ hlam n) (lintegral_fieldDensity hψ hlam n) (fun _ _ => weakKappa V β / N)
    (fun _ _ => div_nonneg (weakKappa_nonneg V hβ) (Nat.cast_nonneg N))
    (weak_dobrushin V hβ hN0 hN a)
    (fun i => (row_sum_le_of_uniform hN0 hnN (weakKappa_nonneg V hβ) i).trans hκ)
    (fun σ y => fieldDensity_comp_perm V _ _ σ y) f hf

/-- Real form of `weak_linear_variance` for `f ∈ L²(π)`. -/
theorem weak_linear_variance_real (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ}
    (hN0 : 0 < N) (hN : n + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : ∀ i, (pinnedLaw V (β / N) n a).map (fun x => x i) = π)
    (f : E → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 π) :
    variance (fun y : Fin n → E => ∑ i, f (y i)) (pinnedLaw V (β / N) n a)
      ≤ 2 * n * variance f π := by
  have h := weak_linear_variance V hβ hN0 hN a hκ π hπ f hf
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hF : Measurable fun y : Fin n → E => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have := isProb_pinnedLaw V hlam n a
  rw [← ofReal_variance hf2] at h
  have hlt : evariance (fun y : Fin n → E => ∑ i, f (y i)) (pinnedLaw V (β / N) n a) < ⊤ := by
    refine lt_of_le_of_lt h ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) ENNReal.ofReal_lt_top
  have hmem : MemLp (fun y : Fin n → E => ∑ i, f (y i)) 2 (pinnedLaw V (β / N) n a) :=
    (evariance_lt_top_iff_memLp hF.aestronglyMeasurable).1 hlt
  rw [← ofReal_variance hmem] at h
  have h0 : 0 ≤ 2 * (n : ℝ) * variance f π := mul_nonneg (by positivity) (variance_nonneg _ _)
  have e : (2 : ℝ≥0∞) * n * ENNReal.ofReal (variance f π) = ENNReal.ofReal (2 * n * variance f π) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff h0] at h
  exact h

end Symm

section Extras

variable [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- `pairEnergy` is the energy `∑_{i<j} q(y_i, y_j)` of the manuscript. -/
lemma pairEnergy_eq_sum_lt (V : WeakPotential μ) {n : ℕ} (y : Fin n → E) :
    pairEnergy V y = ∑ i, ∑ j ∈ Finset.Ioi i, V.q (y i) (y j) := by
  have h1 : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, V.q (y i) (y j)
      = ∑ j ∈ Finset.Iio i, V.q (y i) (y j) + ∑ j ∈ Finset.Ioi i, V.q (y i) (y j) := by
    intro i
    rw [← Finset.sum_union (Finset.disjoint_left.2 fun j hj hj' => by
      simp at hj hj'; exact absurd (hj.trans hj') (lt_irrefl _))]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
      Finset.mem_univ, and_true]
    exact ⟨fun hne => lt_or_gt_of_ne hne, fun h => h.elim (fun h => h.ne) fun h => h.ne'⟩
  have h2 : ∑ i, ∑ j ∈ Finset.Iio i, V.q (y i) (y j)
      = ∑ j, ∑ i ∈ Finset.Ioi j, V.q (y j) (y i) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.Iio i) (t' := Finset.univ)
      (s' := fun j => Finset.Ioi j) (fun i j => by simp)]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => V.q_symm _ _
  unfold pairEnergy
  simp_rw [h1, Finset.sum_add_distrib, h2]
  ring

/-- Jensen lower bound for the normalizer of the pinned conditional density,
`∫ siteU ≥ exp(-(M' + βγ))`, and the trivial upper bound `≤ exp M`. -/
theorem weak_normalizer_bounds (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (i : Fin n) (x : Fin n → E) :
    Real.exp (-(V.M' + β * V.γ))
      ≤ ∫ z, siteU V (pinField V (β / N) a) (β / N) i x z ∂μ ∧
    ∫ z, siteU V (pinField V (β / N) a) (β / N) i x z ∂μ ≤ Real.exp V.M := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  refine ⟨le_trans (Real.exp_le_exp.2 ?_) (exp_le_integral_siteU (V := V) hψ hlam i x), ?_⟩
  · have := weak_Lambda_le V hβ hN0 hN
    linarith
  · calc ∫ z, siteU V (pinField V (β / N) a) (β / N) i x z ∂μ
        ≤ ∫ _z, Real.exp V.M ∂μ :=
          integral_mono (integrable_siteU hψ hlam i x) (integrable_const _)
            fun z => siteU_le hψ hlam i x z
      _ = Real.exp V.M := by simp

end Extras

end Weak

end HRS.External
