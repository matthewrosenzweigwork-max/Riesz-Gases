import Mathlib
import HRS.Stochastic.Filtration
import HRS.Stochastic.DDSCore
import HRS.Prob.HilbertMartingale

/-!
# Dimension-free Burkholder–Davis–Gundy inequality for Hilbert-valued martingales (HILBERT-BDG)

Main result `HRS.HilbertBDG.hilbert_bdg`: for every `p ≥ 2` (the proof works for every `p > 0`) there is
a constant `C = bdgConst p`, depending only on `p`, with
`E sup_{t ≤ T} ‖M_t‖^p ≤ C · E (∫_0^T ‖Σ_r‖_{𝔖₁} dr)^{p/2}` for every
`IsHilbertMartingaleWithCovariation P ℱ T M Sg` (no completeness or right-continuity of `ℱ`;
both sides are `lintegral`s in `ℝ≥0∞`).

Route (no stochastic integration, only continuous-time optional stopping from
`HRS/Stochastic/Filtration.lean`):
1. `goodLambda_moment`: the good-λ integration lemma (layer cake) `E U^p ≤ K E V^p` from
   `P(U ≥ βλ, V < δλ) ≤ ε P(U ≥ λ)` with `β^p ε < 1`.
2. `core_goodlambda`: for finitely many continuous martingales `X_i` with `X_i² - B_i` martingales,
   `B_i` continuous nondecreasing, the good-λ inequality for `U = sup_{[0,T]} |X|` and
   `V = (∑ B_i(T))^{1/2}`, by stopping at the hitting times of `|X|² ≥ λ²`, `|X|² ≥ (βλ)²`,
   `∑ B ≥ (δλ)²` (`core_identity`, `core_orth`: `E|X_ν|² = E∑B_ν` and orthogonality of increments).
3. Hilbert reduction: finite orthonormal families exhausting the norm (`exists_approx_family`),
   everywhere-clean versions of the coordinate martingales for the null-set completed filtration
   (`exists_clean_coord`, `clamp_martingale`), and Fatou's lemma.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS
namespace HilbertBDG

/-! ### Part 1: good-lambda integration -/

section GoodLambda

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Tail formula for the scaled moment `E (f/c)^p`. -/
lemma lintegral_rpow_div_eq_tail {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    ENNReal.ofReal ((c ^ p)⁻¹) * ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂P =
      ENNReal.ofReal p * ∫⁻ t in Ioi (0:ℝ), P {a | c * t ≤ f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h1 := lintegral_rpow_eq_lintegral_meas_le_mul P (f := fun ω => f ω / c)
    (Eventually.of_forall fun ω => div_nonneg (hf0 ω) hc.le) (hf.div_const c).aemeasurable hp
  have h2 : ∀ ω, ENNReal.ofReal ((f ω / c) ^ p) =
      ENNReal.ofReal ((c ^ p)⁻¹) * ENNReal.ofReal (f ω ^ p) := fun ω => by
    rw [Real.div_rpow (hf0 ω) hc.le, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 (Real.rpow_nonneg hc.le _))]
  have h3 : ∀ t : ℝ, {a | t ≤ f a / c} = {a | c * t ≤ f a} := fun t => by
    ext a; simp only [mem_setOf_eq]; rw [le_div_iff₀ hc, mul_comm]
  simp_rw [h2, h3] at h1
  rw [lintegral_const_mul _ (hf.pow_const p).ennreal_ofReal] at h1
  exact h1

lemma measurable_tail (g : Ω → ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    Measurable fun t : ℝ => P {a | t ≤ g a} * w t := by
  have : Antitone fun t : ℝ => P {a | t ≤ g a} := fun s t hst =>
    measure_mono (fun a ha => le_trans hst ha)
  exact this.measurable.mul hw

lemma goodLambda_moment_trunc {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hU0 : ∀ ω, 0 ≤ U ω) (hV0 : ∀ ω, 0 ≤ V ω) {p β δ ε : ℝ} (hp : 0 < p) (hβ : 1 < β)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hεβ : β ^ p * ε < 1) {N : ℝ} (hN : 0 < N)
    (hgl : ∀ l : ℝ, 0 < l → P {ω | β * l ≤ U ω ∧ V ω < δ * l} ≤
      ENNReal.ofReal ε * P {ω | l ≤ U ω}) :
    ∫⁻ ω, ENNReal.ofReal (min (U ω) N ^ p) ∂P ≤
      ENNReal.ofReal (β ^ p * (δ ^ p)⁻¹ / (1 - β ^ p * ε)) * ∫⁻ ω, ENNReal.ofReal (V ω ^ p) ∂P := by
  set Ut : Ω → ℝ := fun ω => min (U ω) N with hUt
  have hUtm : Measurable Ut := hU.min measurable_const
  have hUt0 : ∀ ω, 0 ≤ Ut ω := fun ω => le_min (hU0 ω) hN.le
  set a := ∫⁻ ω, ENNReal.ofReal (Ut ω ^ p) ∂P with ha
  set b := ∫⁻ ω, ENNReal.ofReal (V ω ^ p) ∂P with hb
  have hfin : a ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (b := ∫⁻ _ : Ω, ENNReal.ofReal (N ^ p) ∂P) (lintegral_mono fun ω => ?_) ?_)
    · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hUt0 ω) (min_le_right _ _) hp.le)
    · simp
  have wm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - 1)) :=
    (measurable_id.pow_const (p - 1)).ennreal_ofReal
  have hβ0 : 0 < β := by linarith
  have tB := lintegral_rpow_div_eq_tail P hUtm hUt0 hp hβ0
  have t1 := lintegral_rpow_div_eq_tail P hUtm hUt0 hp one_pos
  have tV := lintegral_rpow_div_eq_tail P hV hV0 hp hδ
  simp only [Real.one_rpow, inv_one, ENNReal.ofReal_one, one_mul] at t1
  rw [← ha] at tB t1
  rw [← hb] at tV
  have pw : ∀ t ∈ Ioi (0:ℝ), P {x | β * t ≤ Ut x} * ENNReal.ofReal (t ^ (p - 1)) ≤
      (ENNReal.ofReal ε * P {x | t ≤ Ut x} + P {x | δ * t ≤ V x}) *
        ENNReal.ofReal (t ^ (p - 1)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    gcongr
    by_cases h : β * t ≤ N
    · have e1 : {x | β * t ≤ Ut x} = {x | β * t ≤ U x} := by
        ext x; simp [hUt, le_min_iff, h]
      have e2 : {x | t ≤ Ut x} = {x | t ≤ U x} := by
        ext x
        have : t ≤ N := by nlinarith
        simp [hUt, le_min_iff, this]
      rw [e1, e2]
      calc P {x | β * t ≤ U x}
          ≤ P ({x | β * t ≤ U x ∧ V x < δ * t} ∪ {x | δ * t ≤ V x}) := by
            refine measure_mono fun x hx => ?_
            by_cases hv : V x < δ * t
            · exact Or.inl ⟨hx, hv⟩
            · exact Or.inr (not_lt.1 hv)
        _ ≤ P {x | β * t ≤ U x ∧ V x < δ * t} + P {x | δ * t ≤ V x} := measure_union_le _ _
        _ ≤ _ := add_le_add (hgl t ht0) le_rfl
    · have : {x | β * t ≤ Ut x} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
        exact lt_of_le_of_lt (min_le_right _ _) (not_le.1 h)
      rw [this]; simp
  have key : ENNReal.ofReal ((β ^ p)⁻¹) * a ≤
      ENNReal.ofReal ε * a + ENNReal.ofReal ((δ ^ p)⁻¹) * b := by
    calc ENNReal.ofReal ((β ^ p)⁻¹) * a
        = ENNReal.ofReal p * ∫⁻ t in Ioi (0:ℝ), P {x | β * t ≤ Ut x} * ENNReal.ofReal (t ^ (p - 1)) := tB
      _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0:ℝ),
            (ENNReal.ofReal ε * (P {x | t ≤ Ut x} * ENNReal.ofReal (t ^ (p - 1))) +
              P {x | δ * t ≤ V x} * ENNReal.ofReal (t ^ (p - 1))) := by
          refine mul_le_mul' le_rfl ?_
          refine setLIntegral_mono' (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ))) fun t ht => ?_
          calc _ ≤ _ := pw t ht
            _ = _ := by ring
      _ = ENNReal.ofReal p * (ENNReal.ofReal ε * (∫⁻ t in Ioi (0:ℝ), P {x | t ≤ Ut x} * ENNReal.ofReal (t ^ (p - 1))) +
            (∫⁻ t in Ioi (0:ℝ), P {x | δ * t ≤ V x} * ENNReal.ofReal (t ^ (p - 1)))) := by
          rw [lintegral_add_left ((measurable_tail P Ut _ wm).const_mul _),
            lintegral_const_mul _ (measurable_tail P Ut _ wm)]
      _ = ENNReal.ofReal ε * (ENNReal.ofReal p * (∫⁻ t in Ioi (0:ℝ), P {x | t ≤ Ut x} * ENNReal.ofReal (t ^ (p - 1)))) +
            ENNReal.ofReal p * (∫⁻ t in Ioi (0:ℝ), P {x | δ * t ≤ V x} * ENNReal.ofReal (t ^ (p - 1))) := by ring
      _ = _ := by rw [← t1, ← tV]
  have hbp : 0 < β ^ p := Real.rpow_pos_of_pos hβ0 p
  have hxeq : (β ^ p)⁻¹ - ε = (1 - β ^ p * ε) / β ^ p := by field_simp
  have hx : 0 < (β ^ p)⁻¹ - ε := by rw [hxeq]; exact div_pos (by linarith) hbp
  have hsplit : ENNReal.ofReal ((β ^ p)⁻¹) =
      ENNReal.ofReal ((β ^ p)⁻¹ - ε) + ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hx.le hε]; congr 1; ring
  have h2 : ENNReal.ofReal ((β ^ p)⁻¹ - ε) * a ≤ ENNReal.ofReal ((δ ^ p)⁻¹) * b := by
    have h := key
    rw [hsplit, add_mul, add_comm (ENNReal.ofReal ε * a)] at h
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
  have hK : ((β ^ p)⁻¹ - ε)⁻¹ * (δ ^ p)⁻¹ = β ^ p * (δ ^ p)⁻¹ / (1 - β ^ p * ε) := by
    have : (1 - β ^ p * ε) ≠ 0 := by linarith
    rw [hxeq]; field_simp
  calc a = ENNReal.ofReal (((β ^ p)⁻¹ - ε)⁻¹) * (ENNReal.ofReal ((β ^ p)⁻¹ - ε) * a) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hx.le), inv_mul_cancel₀ hx.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (((β ^ p)⁻¹ - ε)⁻¹) * (ENNReal.ofReal ((δ ^ p)⁻¹) * b) :=
        mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (((β ^ p)⁻¹ - ε)⁻¹ * (δ ^ p)⁻¹) * b := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hx.le)]
    _ = _ := by rw [hK]

lemma goodLambda_moment {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hU0 : ∀ ω, 0 ≤ U ω) (hV0 : ∀ ω, 0 ≤ V ω) {p β δ ε : ℝ} (hp : 0 < p) (hβ : 1 < β)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hεβ : β ^ p * ε < 1)
    (hgl : ∀ l : ℝ, 0 < l → P {ω | β * l ≤ U ω ∧ V ω < δ * l} ≤
      ENNReal.ofReal ε * P {ω | l ≤ U ω}) :
    ∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂P ≤
      ENNReal.ofReal (β ^ p * (δ ^ p)⁻¹ / (1 - β ^ p * ε)) * ∫⁻ ω, ENNReal.ofReal (V ω ^ p) ∂P := by
  have hmono : Monotone fun (N : ℕ) ω => ENNReal.ofReal (min (U ω) ((N : ℝ) + 1) ^ p) := by
    intro m n hmn ω
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_min (hU0 ω) (by positivity)) ?_ hp.le)
    exact min_le_min le_rfl (by exact_mod_cast Nat.add_le_add_right hmn 1 |>.trans' le_rfl)
  have hle : ∀ ω, ENNReal.ofReal (U ω ^ p) ≤ ⨆ N : ℕ, ENNReal.ofReal (min (U ω) ((N : ℝ) + 1) ^ p) := by
    intro ω
    obtain ⟨N, hN⟩ := exists_nat_ge (U ω)
    refine le_iSup_of_le N ?_
    have : min (U ω) ((N : ℝ) + 1) = U ω := min_eq_left (by linarith)
    rw [this]
  calc ∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂P
      ≤ ∫⁻ ω, ⨆ N : ℕ, ENNReal.ofReal (min (U ω) ((N : ℝ) + 1) ^ p) ∂P := lintegral_mono hle
    _ = ⨆ N : ℕ, ∫⁻ ω, ENNReal.ofReal (min (U ω) ((N : ℝ) + 1) ^ p) ∂P := by
        refine lintegral_iSup (fun N => ?_) hmono
        exact ((hU.min measurable_const).pow_const p).ennreal_ofReal
    _ ≤ _ := iSup_le fun N =>
        goodLambda_moment_trunc P hU hV hU0 hV0 hp hβ hδ hε hεβ (by positivity) hgl


end GoodLambda

/-! ### Part 2: finite-dimensional core (everything everywhere) -/

section Core

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  (ℱ : Filtration ℝ mΩ) {κ : Type*}

/-- The hypotheses of the finite-dimensional core: `X i` are continuous martingales started at
`0`, `B i` continuous nondecreasing adapted with `B i 0 = 0`, and `(X i)^2 - B i` is a martingale. -/
structure CoreData (s : Finset κ) (X B : κ → ℝ → Ω → ℝ) : Prop where
  mart : ∀ i ∈ s, Martingale (X i) ℱ P
  cont : ∀ i ∈ s, ∀ ω, Continuous fun t => X i t ω
  zero : ∀ i ∈ s, ∀ ω, X i 0 ω = 0
  mart2 : ∀ i ∈ s, Martingale (fun t ω => X i t ω ^ 2 - B i t ω) ℱ P
  bcont : ∀ i ∈ s, ∀ ω, Continuous fun t => B i t ω
  bmono : ∀ i ∈ s, ∀ ω, Monotone fun t => B i t ω
  bzero : ∀ i ∈ s, ∀ ω, B i 0 ω = 0
  badapt : ∀ i ∈ s, StronglyAdapted ℱ (B i)

variable {P ℱ} {s : Finset κ} {X B : κ → ℝ → Ω → ℝ}

/-- A continuous path started below `c` is `≤ c` up to (and at) its first hitting time of `[c, ∞)`. -/
lemma hit_value_le {u : ℝ → Ω → ℝ} {ω : Ω} (hc : Continuous fun t => u t ω) {c : ℝ}
    (h0 : u 0 ω < c) {ν : WithTop ℝ} (hν : ν ≤ hittingAfter u (Set.Ici c) 0 ω) {r : ℝ}
    (hr : ν = (r : WithTop ℝ)) (hr0 : 0 ≤ r) : u r ω ≤ c := by
  rcases lt_or_eq_of_le hν with hlt | heq
  · rw [hr] at hlt
    exact (not_le.1 (fun h => notMem_of_lt_hittingAfter hlt hr0 h)).le
  · rw [hr] at heq
    have hmem := mem_of_hittingAfter_eq_of_isClosed u ω hc isClosed_Ici 0 r heq.symm
    have hrpos : 0 < r := by
      rcases lt_or_eq_of_le hr0 with h | h
      · exact h
      · exfalso; subst h; exact absurd (Set.mem_Ici.1 hmem) (not_le.2 h0)
    have ht : Filter.Tendsto (fun t => u t ω) (𝓝[<] r) (𝓝 (u r ω)) :=
      (hc.tendsto r).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hrpos] with t ht'
    have hlt : (t : WithTop ℝ) < hittingAfter u (Set.Ici c) 0 ω := by
      rw [← heq]; exact_mod_cast ht'.2
    exact (not_le.1 (fun h => notMem_of_lt_hittingAfter hlt ht'.1.le h)).le

/-- At a finite hitting time of `[c, ∞)` the path equals `c`. -/
lemma hit_value_eq {u : ℝ → Ω → ℝ} {ω : Ω} (hc : Continuous fun t => u t ω) {c : ℝ}
    (h0 : u 0 ω < c) {r : ℝ} (hr : hittingAfter u (Set.Ici c) 0 ω = (r : WithTop ℝ)) :
    u r ω = c := by
  have hmem := mem_of_hittingAfter_eq_of_isClosed u ω hc isClosed_Ici 0 r hr
  have h0r : (0 : WithTop ℝ) ≤ (r : WithTop ℝ) := hr ▸ le_hittingAfter ω
  have hr0 : 0 ≤ r := by exact_mod_cast h0r
  exact le_antisymm (hit_value_le hc h0 (le_of_eq hr.symm) rfl hr0) (Set.mem_Ici.1 hmem)

lemma continuous_stoppedProcess {u : ℝ → Ω → ℝ} {ω : Ω} (hc : Continuous fun t => u t ω)
    (ν : Ω → WithTop ℝ) : Continuous fun t => stoppedProcess u ν t ω := by
  cases h : ν ω with
  | top => simpa [stoppedProcess_apply_top h] using hc
  | coe r =>
    simp_rw [stoppedProcess_apply_coe h]
    exact hc.comp (continuous_id.min continuous_const)

lemma stoppedValue_eq_stoppedProcess {u : ℝ → Ω → ℝ} {ν : Ω → WithTop ℝ} {T : ℝ}
    (hν : ∀ ω, ν ω ≤ (T : WithTop ℝ)) : stoppedValue u ν = stoppedProcess u ν T := by
  funext ω
  rw [stoppedProcess_eq_of_ge (hν ω)]
  rfl

lemma stoppedProcess_zero_apply {u : ℝ → Ω → ℝ} {ν : Ω → WithTop ℝ} (h0 : ∀ ω, 0 ≤ ν ω) (ω : Ω) :
    stoppedProcess u ν 0 ω = u 0 ω := by
  have : min ((0 : ℝ) : WithTop ℝ) (ν ω) = ((0 : ℝ) : WithTop ℝ) := by
    simpa using h0 ω
  show u (min ((0 : ℝ) : WithTop ℝ) (ν ω)).untopA ω = u 0 ω
  rw [this]
  simp [WithTop.untopA]

lemma untopA_nonneg {a : WithTop ℝ} {T : ℝ} (h0 : 0 ≤ a) (hle : a ≤ (T : WithTop ℝ)) :
    0 ≤ a.untopA := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
  simpa [WithTop.untopA] using h0

/-- Optional stopping at a bounded stopping time `ν ≤ T` below the level `c` of `∑ B`:
`E ∑ X_ν² = E ∑ B_ν`, all terms integrable. -/
lemma core_identity (hD : CoreData P ℱ s X B) {T c : ℝ} (hT : 0 ≤ T) {ν : Ω → WithTop ℝ}
    (hν : IsStoppingTime ℱ ν) (hle : ∀ ω, ν ω ≤ (T : WithTop ℝ)) (h0 : ∀ ω, 0 ≤ ν ω)
    (hA : ∀ ω, ∑ i ∈ s, stoppedValue (B i) ν ω ≤ c) :
    (∀ i ∈ s, Integrable (fun ω => stoppedValue (X i) ν ω ^ 2) P) ∧
      Integrable (fun ω => ∑ i ∈ s, stoppedValue (B i) ν ω) P ∧
      ∫ ω, ∑ i ∈ s, stoppedValue (X i) ν ω ^ 2 ∂P = ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν ω ∂P := by
  have hB0 : ∀ i ∈ s, ∀ ω, 0 ≤ stoppedValue (B i) ν ω := by
    intro i hi ω
    have h := hD.bmono i hi ω
    have hnn : (0:ℝ) ≤ (ν ω).untopA := untopA_nonneg (h0 ω) (hle ω)
    simpa [stoppedValue, hD.bzero i hi ω] using h hnn
  have hBle : ∀ i ∈ s, ∀ ω, stoppedValue (B i) ν ω ≤ c := by
    intro i hi ω
    refine le_trans ?_ (hA ω)
    exact Finset.single_le_sum (f := fun j => stoppedValue (B j) ν ω) (fun j hj => hB0 j hj ω) hi
  have key : ∀ i ∈ s, Integrable (fun ω => stoppedValue (X i) ν ω ^ 2) P ∧
      Integrable (stoppedValue (B i) ν) P ∧
      ∫ ω, stoppedValue (X i) ν ω ^ 2 ∂P = ∫ ω, stoppedValue (B i) ν ω ∂P := by
    intro i hi
    have hprogN : StronglyAdapted ℱ (fun t ω => X i t ω ^ 2 - B i t ω) :=
      (hD.mart2 i hi).1
    have hNc : ∀ ω, Continuous fun t => X i t ω ^ 2 - B i t ω := fun ω =>
      ((hD.cont i hi ω).pow 2).sub (hD.bcont i hi ω)
    have hint := Martingale.integral_stoppedProcess_of_continuous P ℱ _ (hD.mart2 i hi) hNc hν 0 T
      hT
    have hNint := ((Martingale.stoppedProcess_of_continuous P ℱ _ (hD.mart2 i hi) hNc hν).integrable T)
    have hBprog : IsStronglyProgressive ℱ (B i) :=
      (hD.badapt i hi).isStronglyProgressive_of_continuous (hD.bcont i hi)
    have hBmeas : StronglyMeasurable (stoppedValue (B i) ν) := by
      rw [stoppedValue_eq_stoppedProcess hle]
      exact hBprog.stronglyMeasurable_stoppedProcess hν T
    have hBint : Integrable (stoppedValue (B i) ν) P := by
      refine Integrable.of_bound hBmeas.aestronglyMeasurable c (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (hB0 i hi ω)]
      exact hBle i hi ω
    have e1 : stoppedProcess (fun t ω => X i t ω ^ 2 - B i t ω) ν T =
        fun ω => stoppedValue (X i) ν ω ^ 2 - stoppedValue (B i) ν ω := by
      rw [← stoppedValue_eq_stoppedProcess hle]; rfl
    have e0 : ∀ ω, stoppedProcess (fun t ω => X i t ω ^ 2 - B i t ω) ν 0 ω = 0 := by
      intro ω
      rw [stoppedProcess_zero_apply h0, hD.zero i hi, hD.bzero i hi]; simp
    rw [e1] at hint hNint
    simp_rw [e0] at hint
    simp only [integral_zero] at hint
    have hXint : Integrable (fun ω => stoppedValue (X i) ν ω ^ 2) P := by
      refine (hNint.add hBint).congr (Eventually.of_forall fun ω => ?_)
      simp
    refine ⟨hXint, hBint, ?_⟩
    rw [integral_sub hXint hBint] at hint
    linarith
  refine ⟨fun i hi => (key i hi).1, integrable_finsetSum _ (fun i hi => (key i hi).2.1), ?_⟩
  rw [integral_finsetSum _ (fun i hi => (key i hi).1), integral_finsetSum _ (fun i hi => (key i hi).2.1)]
  exact Finset.sum_congr rfl fun i hi => (key i hi).2.2

/-- If `A ∈ ℱ_{ν}` and `ν ≤ T`, then `ν` on `A` and `T` off `A` is a stopping time. -/
lemma isStoppingTime_piecewise_of_mem {ν : Ω → WithTop ℝ} (hν : IsStoppingTime ℱ ν) {T : ℝ}
    (hle : ∀ ω, ν ω ≤ (T : WithTop ℝ)) {A : Set Ω} (hA : MeasurableSet[hν.measurableSpace] A)
    [DecidablePred (· ∈ A)] :
    IsStoppingTime ℱ (A.piecewise ν fun _ => (T : WithTop ℝ)) := by
  intro t
  by_cases htT : T ≤ t
  · have : {ω | A.piecewise ν (fun _ => (T : WithTop ℝ)) ω ≤ (t : WithTop ℝ)} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases hx : ω ∈ A
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact (hle ω).trans (by exact_mod_cast htT)
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; exact_mod_cast htT
    rw [this]; exact @MeasurableSet.univ _ (ℱ t)
  · have : {ω | A.piecewise ν (fun _ => (T : WithTop ℝ)) ω ≤ (t : WithTop ℝ)} =
        A ∩ {ω | ν ω ≤ (t : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      by_cases hx : ω ∈ A
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]; simp [hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        simp only [hx, false_and, iff_false, not_le]
        exact_mod_cast not_le.1 htT
    rw [this]
    exact hA.2 t

/-- Orthogonality of increments at ordered bounded stopping times (optional sampling). -/
lemma core_orth (hD : CoreData P ℱ s X B) {T : ℝ} (hT : 0 ≤ T) {ν₁ ν₂ : Ω → WithTop ℝ}
    (h₁ : IsStoppingTime ℱ ν₁) (h₂ : IsStoppingTime ℱ ν₂) (h12 : ∀ ω, ν₁ ω ≤ ν₂ ω)
    (hle : ∀ ω, ν₂ ω ≤ (T : WithTop ℝ)) (h0 : ∀ ω, 0 ≤ ν₁ ω) {i : κ} (hi : i ∈ s)
    (hint1 : Integrable (fun ω => stoppedValue (X i) ν₁ ω ^ 2) P)
    (hint2 : Integrable (fun ω => stoppedValue (X i) ν₂ ω ^ 2) P) :
    Integrable (fun ω => stoppedValue (X i) ν₁ ω *
        (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω)) P ∧
      ∫ ω, stoppedValue (X i) ν₁ ω * (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ∂P = 0 := by
  classical
  have hle1 : ∀ ω, ν₁ ω ≤ (T : WithTop ℝ) := fun ω => (h12 ω).trans (hle ω)
  have h02 : ∀ ω, 0 ≤ ν₂ ω := fun ω => (h0 ω).trans (h12 ω)
  have hXm := hD.mart i hi
  have hprog : IsStronglyProgressive ℱ (X i) :=
    hXm.1.isStronglyProgressive_of_continuous (hD.cont i hi)
  have hI : ∀ {ν : Ω → WithTop ℝ}, IsStoppingTime ℱ ν → (∀ ω, ν ω ≤ (T : WithTop ℝ)) →
      Integrable (stoppedValue (X i) ν) P := by
    intro ν hν hνle
    rw [stoppedValue_eq_stoppedProcess hνle]
    exact (Martingale.stoppedProcess_of_continuous P ℱ _ hXm (hD.cont i hi) hν).integrable T
  have hI1 := hI h₁ hle1
  have hI2 := hI h₂ hle
  have step1 : ∀ A, MeasurableSet[h₁.measurableSpace] A →
      ∫ ω in A, (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ∂P = 0 := by
    intro A hA
    set ν : Ω → WithTop ℝ := A.piecewise ν₁ (fun _ => (T : WithTop ℝ)) with hνdef
    have hν : IsStoppingTime ℱ ν := isStoppingTime_piecewise_of_mem h₁ hle1 hA
    have hνle : ∀ ω, ν ω ≤ (T : WithTop ℝ) := by
      intro ω
      by_cases hx : ω ∈ A
      · simp only [hνdef, Set.piecewise_eq_of_mem _ _ _ hx]; exact hle1 ω
      · simp only [hνdef, Set.piecewise_eq_of_notMem _ _ _ hx]; exact le_rfl
    have hν0 : ∀ ω, 0 ≤ ν ω := by
      intro ω
      by_cases hx : ω ∈ A
      · simp only [hνdef, Set.piecewise_eq_of_mem _ _ _ hx]; exact h0 ω
      · simp only [hνdef, Set.piecewise_eq_of_notMem _ _ _ hx]; exact_mod_cast hT
    set Y := stoppedProcess (X i) ν₂ with hY
    have hYm : Martingale Y ℱ P :=
      Martingale.stoppedProcess_of_continuous P ℱ _ hXm (hD.cont i hi) h₂
    have hYc : ∀ ω, Continuous fun t => Y t ω := fun ω =>
      continuous_stoppedProcess (hD.cont i hi ω) ν₂
    have hZ := Martingale.integral_stoppedProcess_of_continuous P ℱ Y hYm hYc hν 0 T hT
    have hZm : Martingale (stoppedProcess Y ν) ℱ P :=
      Martingale.stoppedProcess_of_continuous P ℱ Y hYm hYc hν
    have hY0 : ∀ ω, stoppedProcess Y ν 0 ω = Y 0 ω := stoppedProcess_zero_apply hν0
    have hYT : ∀ ω, Y T ω = stoppedValue (X i) ν₂ ω := fun ω => by
      rw [hY, stoppedValue_eq_stoppedProcess hle]
    -- value of the doubly stopped process
    have hZT : ∀ ω, stoppedProcess Y ν T ω =
        A.piecewise (stoppedValue (X i) ν₁) (stoppedValue (X i) ν₂) ω := by
      intro ω
      rw [hY, stoppedProcess_stoppedProcess']
      have hmle : ∀ ω, min (ν ω) (ν₂ ω) ≤ (T : WithTop ℝ) := fun ω => (min_le_right _ _).trans (hle ω)
      rw [← stoppedValue_eq_stoppedProcess hmle]
      by_cases hx : ω ∈ A
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
        have : min (ν ω) (ν₂ ω) = ν₁ ω := by
          simp only [hνdef, Set.piecewise_eq_of_mem _ _ _ hx]; exact min_eq_left (h12 ω)
        simp only [stoppedValue, this]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        have : min (ν ω) (ν₂ ω) = ν₂ ω := by
          simp only [hνdef, Set.piecewise_eq_of_notMem _ _ _ hx]; exact min_eq_right (hle ω)
        simp only [stoppedValue, this]
    have hYint : ∫ ω, Y T ω ∂P = ∫ ω, Y 0 ω ∂P := by
      calc ∫ ω, Y T ω ∂P = ∫ ω, (P[Y T | ℱ 0]) ω ∂P := (integral_condExp (ℱ.le 0)).symm
        _ = ∫ ω, Y 0 ω ∂P := integral_congr_ae (hYm.2 0 T hT)
    have hAm : MeasurableSet A := h₁.measurableSpace_le A hA
    have e1 : ∫ ω, stoppedProcess Y ν T ω ∂P = ∫ ω, Y T ω ∂P := by
      rw [hZ]; simp_rw [hY0]; exact hYint.symm
    simp_rw [hZT, hYT] at e1
    have hsplit1 := integral_add_compl hAm hI1
    have hsplit2 := integral_add_compl hAm hI2
    have hpw : ∫ ω, A.piecewise (stoppedValue (X i) ν₁) (stoppedValue (X i) ν₂) ω ∂P =
        ∫ ω in A, stoppedValue (X i) ν₁ ω ∂P + ∫ ω in Aᶜ, stoppedValue (X i) ν₂ ω ∂P := by
      rw [← integral_add_compl hAm (f := fun ω => A.piecewise (stoppedValue (X i) ν₁)
        (stoppedValue (X i) ν₂) ω) ?_]
      · congr 1
        · exact setIntegral_congr_fun hAm fun ω hx => Set.piecewise_eq_of_mem _ _ _ hx
        · exact setIntegral_congr_fun hAm.compl fun ω hx => Set.piecewise_eq_of_notMem _ _ _ hx
      · exact Integrable.piecewise hAm hI1.integrableOn hI2.integrableOn
    rw [integral_sub hI2.integrableOn hI1.integrableOn]
    linarith
  have hmle : h₁.measurableSpace ≤ mΩ := h₁.measurableSpace_le
  have hg : StronglyMeasurable[h₁.measurableSpace] (stoppedValue (X i) ν₁) :=
    (measurable_stoppedValue hprog h₁).stronglyMeasurable
  have hint_h : Integrable (fun ω => stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) P :=
    hI2.sub hI1
  have hcond : (fun _ => (0:ℝ)) =ᵐ[P] P[fun ω => stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω | h₁.measurableSpace] :=
    ae_eq_condExp_of_forall_setIntegral_eq hmle hint_h (fun _ _ _ => integrableOn_zero)
      (fun t ht _ => by simp [step1 t ht]) aestronglyMeasurable_const
  have hg1 : MemLp (stoppedValue (X i) ν₁) 2 P :=
    (memLp_two_iff_integrable_sq (hg.mono hmle).aestronglyMeasurable).2 hint1
  have hg2 : MemLp (stoppedValue (X i) ν₂) 2 P :=
    (memLp_two_iff_integrable_sq hI2.aestronglyMeasurable).2 hint2
  have hprod : Integrable (stoppedValue (X i) ν₁ * fun ω => stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) P :=
    hg1.integrable_mul (hg2.sub hg1)
  refine ⟨hprod, ?_⟩
  calc ∫ ω, stoppedValue (X i) ν₁ ω * (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ∂P
      = ∫ ω, (P[stoppedValue (X i) ν₁ * fun ω => stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω | h₁.measurableSpace]) ω ∂P :=
        (integral_condExp hmle).symm
    _ = ∫ ω, (stoppedValue (X i) ν₁ * P[fun ω => stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω | h₁.measurableSpace]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg hprod hint_h)
    _ = 0 := by
        rw [← integral_zero (μ := P) (G := ℝ)]
        refine integral_congr_ae ?_
        filter_upwards [hcond] with ω hω
        simp [← hω]

/-- The quadratic increment between two ordered bounded stopping times, in expectation. -/
lemma core_diff (hD : CoreData P ℱ s X B) {T c : ℝ} (hT : 0 ≤ T) {ν₁ ν₂ : Ω → WithTop ℝ}
    (h₁ : IsStoppingTime ℱ ν₁) (h₂ : IsStoppingTime ℱ ν₂) (h12 : ∀ ω, ν₁ ω ≤ ν₂ ω)
    (hle : ∀ ω, ν₂ ω ≤ (T : WithTop ℝ)) (h0 : ∀ ω, 0 ≤ ν₁ ω)
    (hA₁ : ∀ ω, ∑ i ∈ s, stoppedValue (B i) ν₁ ω ≤ c)
    (hA₂ : ∀ ω, ∑ i ∈ s, stoppedValue (B i) ν₂ ω ≤ c) :
    Integrable (fun ω => ∑ i ∈ s, (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ^ 2) P ∧
    ∫ ω, ∑ i ∈ s, (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ^ 2 ∂P =
      ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν₂ ω ∂P - ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν₁ ω ∂P := by
  have hle1 : ∀ ω, ν₁ ω ≤ (T : WithTop ℝ) := fun ω => (h12 ω).trans (hle ω)
  have h02 : ∀ ω, 0 ≤ ν₂ ω := fun ω => (h0 ω).trans (h12 ω)
  obtain ⟨hi1, -, he1⟩ := core_identity hD hT h₁ hle1 h0 hA₁
  obtain ⟨hi2, -, he2⟩ := core_identity hD hT h₂ hle h02 hA₂
  have ho : ∀ i ∈ s, Integrable (fun ω => stoppedValue (X i) ν₁ ω *
        (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω)) P ∧
      ∫ ω, stoppedValue (X i) ν₁ ω * (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ∂P = 0 :=
    fun i hi => core_orth hD hT h₁ h₂ h12 hle h0 hi (hi1 i hi) (hi2 i hi)
  have hpt : ∀ ω, ∑ i ∈ s, (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ^ 2 =
      ∑ i ∈ s, stoppedValue (X i) ν₂ ω ^ 2 - ∑ i ∈ s, stoppedValue (X i) ν₁ ω ^ 2 -
        2 * ∑ i ∈ s, stoppedValue (X i) ν₁ ω *
          (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) := by
    intro ω
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs1 : Integrable (fun ω => ∑ i ∈ s, stoppedValue (X i) ν₁ ω ^ 2) P :=
    integrable_finsetSum _ hi1
  have hs2 : Integrable (fun ω => ∑ i ∈ s, stoppedValue (X i) ν₂ ω ^ 2) P :=
    integrable_finsetSum _ hi2
  have hs3 : Integrable (fun ω => ∑ i ∈ s, stoppedValue (X i) ν₁ ω *
          (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω)) P :=
    integrable_finsetSum _ (fun i hi => (ho i hi).1)
  have hs3z : ∫ ω, ∑ i ∈ s, stoppedValue (X i) ν₁ ω *
          (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i hi => (ho i hi).1)]
    exact Finset.sum_eq_zero fun i hi => (ho i hi).2
  simp_rw [hpt]
  refine ⟨(hs2.sub hs1).sub (hs3.const_mul 2), ?_⟩
  have A1 := integral_sub (hs2.sub hs1) (hs3.const_mul 2)
  have A2 := integral_sub hs2 hs1
  simp only [Pi.sub_apply] at A1 A2
  rw [A1, A2, integral_const_mul, hs3z, he1, he2]
  ring

/-- The running maximum of the Euclidean norm over `[0,T]`. -/
def coreU (s : Finset κ) (X : κ → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, Real.sqrt (∑ i ∈ s, X i t ω ^ 2)

lemma coreU_attained {ω : Ω} {T : ℝ} (hT : 0 ≤ T) (hc : ∀ i ∈ s, Continuous fun t => X i t ω) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt (∑ i ∈ s, X i t ω ^ 2) ≤ coreU s X T ω) ∧
      ∃ t ∈ Set.Icc (0 : ℝ) T, coreU s X T ω = Real.sqrt (∑ i ∈ s, X i t ω ^ 2) := by
  have hg : Continuous fun t : ℝ => Real.sqrt (∑ i ∈ s, X i t ω ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finset_sum _ fun i hi => (hc i hi).pow 2)
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hT) hg.continuousOn
  have hbdd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => Real.sqrt (∑ i ∈ s, X i t ω ^ 2)) :=
    ⟨Real.sqrt (∑ i ∈ s, X i t₀ ω ^ 2), by
      rintro _ ⟨t, rfl⟩; exact hmax t.2⟩
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt (∑ i ∈ s, X i t ω ^ 2) ≤ coreU s X T ω :=
    fun t ht => le_ciSup hbdd (⟨t, ht⟩ : Set.Icc (0 : ℝ) T)
  refine ⟨hle, t₀, ht₀, le_antisymm ?_ (hle t₀ ht₀)⟩
  exact ciSup_le fun t => hmax t.2

lemma le_coreU_iff {ω : Ω} {T : ℝ} (hT : 0 ≤ T) (hc : ∀ i ∈ s, Continuous fun t => X i t ω)
    {l : ℝ} (hl : 0 ≤ l) :
    l ≤ coreU s X T ω ↔ ∃ t ∈ Set.Icc (0 : ℝ) T, l ^ 2 ≤ ∑ i ∈ s, X i t ω ^ 2 := by
  obtain ⟨hle, t₀, ht₀, heq⟩ := coreU_attained (s := s) (X := X) hT hc
  constructor
  · intro h
    refine ⟨t₀, ht₀, ?_⟩
    rw [heq] at h
    exact (Real.le_sqrt hl (Finset.sum_nonneg fun i _ => sq_nonneg _)).1 h
  · rintro ⟨t, ht, h⟩
    exact ((Real.le_sqrt hl (Finset.sum_nonneg fun i _ => sq_nonneg _)).2 h).trans (hle t ht)

/-- First time the squared Euclidean norm reaches `a`. -/
def hitR (s : Finset κ) (X : κ → ℝ → Ω → ℝ) (a : ℝ) : Ω → WithTop ℝ :=
  hittingAfter (fun t ω => ∑ i ∈ s, X i t ω ^ 2) (Set.Ici a) 0

/-- First time the bracket `∑ B` reaches `c`. -/
def hitA (s : Finset κ) (B : κ → ℝ → Ω → ℝ) (c : ℝ) : Ω → WithTop ℝ :=
  hittingAfter (fun t ω => ∑ i ∈ s, B i t ω) (Set.Ici c) 0

/-- The stopping time `τ ∧ ρ ∧ T`. -/
def nuT (τ ρ : Ω → WithTop ℝ) (T : ℝ) : Ω → WithTop ℝ :=
  fun ω => min (min (τ ω) (ρ ω)) (T : WithTop ℝ)

lemma isStoppingTime_hitR (hD : CoreData P ℱ s X B) (a : ℝ) : IsStoppingTime ℱ (hitR s X a) := by
  refine isStoppingTime_hittingAfter_Ici ℱ _ ?_ ?_ a
  · intro t
    exact Finset.measurable_sum _ fun i hi => ((hD.mart i hi).1 t).measurable.pow_const 2
  · intro ω
    exact continuous_finset_sum _ fun i hi => (hD.cont i hi ω).pow 2

lemma isStoppingTime_hitA (hD : CoreData P ℱ s X B) (c : ℝ) : IsStoppingTime ℱ (hitA s B c) := by
  refine isStoppingTime_hittingAfter_Ici ℱ _ ?_ ?_ c
  · intro t
    exact Finset.measurable_sum _ fun i hi => ((hD.badapt i hi) t).measurable
  · intro ω
    exact continuous_finset_sum _ fun i hi => hD.bcont i hi ω

lemma isStoppingTime_nuT (hD : CoreData P ℱ s X B) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) (c T : ℝ) : IsStoppingTime ℱ (nuT τ (hitA s B c) T) :=
  (hτ.min (isStoppingTime_hitA hD c)).min (isStoppingTime_const ℱ T)

lemma nuT_le (τ ρ : Ω → WithTop ℝ) (T : ℝ) (ω : Ω) : nuT τ ρ T ω ≤ (T : WithTop ℝ) :=
  min_le_right _ _

lemma zero_le_hittingAfter {u : ℝ → Ω → ℝ} {S : Set ℝ} (ω : Ω) :
    (0 : WithTop ℝ) ≤ hittingAfter u S 0 ω := by
  have := le_hittingAfter (u := u) (s := S) (n := (0 : ℝ)) ω
  simpa using this

lemma nuT_nonneg {T : ℝ} (hT : 0 ≤ T) {τ ρ : Ω → WithTop ℝ} (h1 : ∀ ω, 0 ≤ τ ω)
    (h2 : ∀ ω, 0 ≤ ρ ω) (ω : Ω) : 0 ≤ nuT τ ρ T ω :=
  le_min (le_min (h1 ω) (h2 ω)) (by exact_mod_cast hT)

/-- Below the level: `∑ B` stopped at `τ ∧ ρ_c ∧ T` is at most `c`. -/
lemma core_stopped_B_le (hD : CoreData P ℱ s X B) {T c : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    {τ : Ω → WithTop ℝ} (hτ0 : ∀ ω, 0 ≤ τ ω) (ω : Ω) :
    ∑ i ∈ s, stoppedValue (B i) (nuT τ (hitA s B c) T) ω ≤ c := by
  have hle := nuT_le τ (hitA s B c) T ω
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
  have h0 := nuT_nonneg (ρ := hitA s B c) hT hτ0 (fun ω => zero_le_hittingAfter ω) ω
  have hr0 : (0 : ℝ) ≤ r := by
    rw [← hr] at h0; exact_mod_cast h0
  have hνρ : nuT τ (hitA s B c) T ω ≤ hittingAfter (fun t ω => ∑ i ∈ s, B i t ω) (Set.Ici c) 0 ω :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hbc := hit_value_le (u := fun t ω => ∑ i ∈ s, B i t ω) (ω := ω)
    (continuous_finset_sum _ fun i hi => hD.bcont i hi ω) (c := c)
    (by rw [Finset.sum_eq_zero fun i hi => hD.bzero i hi ω]; exact hc) hνρ hr.symm hr0
  have : ∀ i, stoppedValue (B i) (nuT τ (hitA s B c) T) ω = B i r ω := fun i => by
    simp [stoppedValue, ← hr, WithTop.untopA]
  simpa [this] using hbc

lemma hitR_le_iff (hD : CoreData P ℱ s X B) (ω : Ω) (a T : ℝ) :
    hitR s X a ω ≤ (T : WithTop ℝ) ↔ ∃ r, 0 ≤ r ∧ r ≤ T ∧ a ≤ ∑ i ∈ s, X i r ω ^ 2 := by
  unfold hitR
  rw [hittingAfter_le_iff_of_isClosed (fun t ω => ∑ i ∈ s, X i t ω ^ 2) ω
    (continuous_finset_sum _ fun i hi => (hD.cont i hi ω).pow 2) isClosed_Ici 0 T]
  simp [Set.mem_Ici]

lemma hitA_le_iff (hD : CoreData P ℱ s X B) (ω : Ω) (c T : ℝ) :
    hitA s B c ω ≤ (T : WithTop ℝ) ↔ ∃ r, 0 ≤ r ∧ r ≤ T ∧ c ≤ ∑ i ∈ s, B i r ω := by
  unfold hitA
  rw [hittingAfter_le_iff_of_isClosed (fun t ω => ∑ i ∈ s, B i t ω) ω
    (continuous_finset_sum _ fun i hi => hD.bcont i hi ω) isClosed_Ici 0 T]
  simp [Set.mem_Ici]

lemma hitR_value (hD : CoreData P ℱ s X B) (ω : Ω) {a : ℝ} (ha : 0 < a) {r : ℝ}
    (h : hitR s X a ω = (r : WithTop ℝ)) : ∑ i ∈ s, X i r ω ^ 2 = a := by
  refine hit_value_eq (u := fun t ω => ∑ i ∈ s, X i t ω ^ 2) (ω := ω)
    (continuous_finset_sum _ fun i hi => (hD.cont i hi ω).pow 2) ?_ h
  rw [Finset.sum_eq_zero fun i hi => by rw [hD.zero i hi ω]; ring]
  exact ha

lemma hitR_anti (a b : ℝ) (hab : a ≤ b) (ω : Ω) : hitR s X a ω ≤ hitR s X b ω :=
  hittingAfter_apply_anti (fun t ω => ∑ i ∈ s, X i t ω ^ 2) 0 ω (Set.Ici_subset_Ici.2 hab)

lemma core_B_nonneg (hD : CoreData P ℱ s X B) {T : ℝ} {ν : Ω → WithTop ℝ}
    (hle : ∀ ω, ν ω ≤ (T : WithTop ℝ)) (h0 : ∀ ω, 0 ≤ ν ω) {i : κ} (hi : i ∈ s) (ω : Ω) :
    0 ≤ stoppedValue (B i) ν ω := by
  have h := hD.bmono i hi ω
  have hnn : (0:ℝ) ≤ (ν ω).untopA := untopA_nonneg (h0 ω) (hle ω)
  simpa [stoppedValue, hD.bzero i hi ω] using h hnn

/-- Pathwise Cauchy–Schwarz step: two vectors of squared norms `a²` and `b²` with `a ≥ b ≥ 0`
are at squared distance `≥ (a-b)²`. -/
lemma sq_dist_ge {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (x y : κ → ℝ)
    (hx : ∑ i ∈ s, x i ^ 2 = a ^ 2) (hy : ∑ i ∈ s, y i ^ 2 = b ^ 2) :
    (a - b) ^ 2 ≤ ∑ i ∈ s, (x i - y i) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s x y
  rw [hx, hy] at hcs
  have h1 : ∑ i ∈ s, x i * y i ≤ a * b := by
    have := abs_le_of_sq_le_sq' (a := ∑ i ∈ s, x i * y i) (b := a * b)
      (by nlinarith) (mul_nonneg (hb.trans hab) hb)
    exact this.2
  have h2 : ∑ i ∈ s, (x i - y i) ^ 2 = ∑ i ∈ s, x i ^ 2 - 2 * ∑ i ∈ s, x i * y i + ∑ i ∈ s, y i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, hx, hy]
  nlinarith

lemma measurable_stoppedValue_core (hD : CoreData P ℱ s X B) {ν : Ω → WithTop ℝ}
    (hν : IsStoppingTime ℱ ν) {i : κ} (hi : i ∈ s) : Measurable (stoppedValue (X i) ν) := by
  have hprog : IsStronglyProgressive ℱ (X i) :=
    (hD.mart i hi).1.isStronglyProgressive_of_continuous (hD.cont i hi)
  exact (measurable_stoppedValue hprog hν).mono hν.measurableSpace_le le_rfl

/-- The good-lambda inequality for the finite-dimensional core. -/
lemma core_goodlambda (hD : CoreData P ℱ s X B) {T : ℝ} (hT : 0 ≤ T) {l β δ : ℝ} (hl : 0 < l)
    (hβ : 1 < β) (hδ : 0 < δ) :
    P {ω | β * l ≤ coreU s X T ω ∧ Real.sqrt (∑ i ∈ s, B i T ω) < δ * l} ≤
      ENNReal.ofReal (δ ^ 2 / (β - 1) ^ 2) * P {ω | l ≤ coreU s X T ω} := by
  classical
  have hβl : 0 < β * l := by positivity
  set c : ℝ := (δ * l) ^ 2 with hcdef
  have hc : 0 < c := by positivity
  set τ := hitR s X (l ^ 2) with hτdef
  set σ := hitR s X ((β * l) ^ 2) with hσdef
  have hτ : IsStoppingTime ℱ τ := isStoppingTime_hitR hD _
  have hσ : IsStoppingTime ℱ σ := isStoppingTime_hitR hD _
  have hτ0 : ∀ ω, 0 ≤ τ ω := fun ω => zero_le_hittingAfter ω
  have hσ0 : ∀ ω, 0 ≤ σ ω := fun ω => zero_le_hittingAfter ω
  have hτσ : ∀ ω, τ ω ≤ σ ω := fun ω =>
    hitR_anti _ _ (pow_le_pow_left₀ hl.le (le_mul_of_one_le_left hl.le hβ.le) 2) ω
  set ν₁ := nuT τ (hitA s B c) T with hν₁
  set ν₂ := nuT σ (hitA s B c) T with hν₂
  have h₁ : IsStoppingTime ℱ ν₁ := isStoppingTime_nuT hD hτ c T
  have h₂ : IsStoppingTime ℱ ν₂ := isStoppingTime_nuT hD hσ c T
  have h12 : ∀ ω, ν₁ ω ≤ ν₂ ω := fun ω =>
    min_le_min (min_le_min (hτσ ω) le_rfl) le_rfl
  have hle₁ : ∀ ω, ν₁ ω ≤ (T : WithTop ℝ) := nuT_le _ _ _
  have hle₂ : ∀ ω, ν₂ ω ≤ (T : WithTop ℝ) := nuT_le _ _ _
  have h0₁ : ∀ ω, 0 ≤ ν₁ ω := fun ω => nuT_nonneg hT hτ0 (fun ω => zero_le_hittingAfter ω) ω
  have h0₂ : ∀ ω, 0 ≤ ν₂ ω := fun ω => nuT_nonneg hT hσ0 (fun ω => zero_le_hittingAfter ω) ω
  have hA₁ := core_stopped_B_le hD hT hc hτ0
  have hA₂ := core_stopped_B_le hD hT hc hσ0
  obtain ⟨hDi, hDe⟩ := core_diff hD hT h₁ h₂ h12 hle₂ h0₁ hA₁ hA₂
  obtain ⟨-, hBi₁, -⟩ := core_identity hD hT h₁ hle₁ h0₁ hA₁
  obtain ⟨-, hBi₂, -⟩ := core_identity hD hT h₂ hle₂ h0₂ hA₂
  set S : Set Ω := {ω | τ ω ≤ (T : WithTop ℝ)} with hSdef
  have hSm : MeasurableSet S := ℱ.le T _ (hτ T)
  have hpath : ∀ ω, ∑ i ∈ s, stoppedValue (B i) ν₂ ω - ∑ i ∈ s, stoppedValue (B i) ν₁ ω ≤
      S.indicator (fun _ => c) ω := by
    intro ω
    by_cases hτT : τ ω ≤ (T : WithTop ℝ)
    · rw [Set.indicator_of_mem (show ω ∈ S from hτT)]
      have h1 := hA₂ ω
      have h2 : 0 ≤ ∑ i ∈ s, stoppedValue (B i) ν₁ ω :=
        Finset.sum_nonneg fun i hi => core_B_nonneg hD hle₁ h0₁ hi ω
      linarith
    · rw [Set.indicator_of_notMem (show ω ∉ S from hτT)]
      have hgt : (T : WithTop ℝ) < τ ω := not_le.1 hτT
      have heq : ν₁ ω = ν₂ ω := by
        simp only [hν₁, hν₂, nuT]
        rw [min_comm (τ ω), min_assoc, min_eq_right hgt.le, min_comm (σ ω), min_assoc,
          min_eq_right (hgt.trans_le (hτσ ω)).le]
      have : ∑ i ∈ s, stoppedValue (B i) ν₂ ω = ∑ i ∈ s, stoppedValue (B i) ν₁ ω :=
        Finset.sum_congr rfl fun i _ => by simp only [stoppedValue, heq]
      linarith
  have hint_ind : Integrable (S.indicator fun _ => c) P := (integrable_const c).indicator hSm
  have hI : ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν₂ ω ∂P - ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν₁ ω ∂P ≤
      P.real S * c := by
    rw [← integral_sub hBi₂ hBi₁]
    calc _ ≤ ∫ ω, S.indicator (fun _ => c) ω ∂P :=
          integral_mono (hBi₂.sub hBi₁) hint_ind hpath
      _ = P.real S * c := by rw [integral_indicator_const _ hSm]; simp
  -- the quadratic increment
  set Dsq : Ω → ℝ := fun ω => ∑ i ∈ s, (stoppedValue (X i) ν₂ ω - stoppedValue (X i) ν₁ ω) ^ 2
    with hDsq
  have hDm : Measurable Dsq :=
    Finset.measurable_sum _ fun i hi =>
      ((measurable_stoppedValue_core hD h₂ hi).sub (measurable_stoppedValue_core hD h₁ hi)).pow_const 2
  have hDnn : ∀ ω, 0 ≤ Dsq ω := fun ω => Finset.sum_nonneg fun i _ => sq_nonneg _
  set k : ℝ := (β - 1) ^ 2 * l ^ 2 with hk
  have hkpos : 0 < k := by
    have : 0 < β - 1 := by linarith
    positivity
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hDm.ennreal_ofReal.aemeasurable (ENNReal.ofReal k)
  have hlint : ∫⁻ ω, ENNReal.ofReal (Dsq ω) ∂P = ENNReal.ofReal (∫ ω, Dsq ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall hDnn)).symm
  have hEsub : {ω | β * l ≤ coreU s X T ω ∧ Real.sqrt (∑ i ∈ s, B i T ω) < δ * l} ⊆
      {ω | ENNReal.ofReal k ≤ ENNReal.ofReal (Dsq ω)} := by
    rintro ω ⟨hU, hV⟩
    have hcont : ∀ i ∈ s, Continuous fun t => X i t ω := fun i hi => hD.cont i hi ω
    obtain ⟨t₂, ht₂, hR₂⟩ := (le_coreU_iff hT hcont hβl.le).1 hU
    have hσT : σ ω ≤ (T : WithTop ℝ) := (hitR_le_iff hD ω _ T).2 ⟨t₂, ht₂.1, ht₂.2, hR₂⟩
    have hτT : τ ω ≤ (T : WithTop ℝ) := (hτσ ω).trans hσT
    have hAT : ∑ i ∈ s, B i T ω < c := by
      have := (Real.sqrt_lt' (by positivity : 0 < δ * l)).1 hV
      simpa [hcdef] using this
    have hρT : (T : WithTop ℝ) < hitA s B c ω := by
      by_contra hcon
      obtain ⟨r, hr0, hrT, hrc⟩ := (hitA_le_iff hD ω c T).1 (not_lt.1 hcon)
      have : ∑ i ∈ s, B i r ω ≤ ∑ i ∈ s, B i T ω :=
        Finset.sum_le_sum fun i hi => hD.bmono i hi ω hrT
      linarith
    have hν₁ω : ν₁ ω = τ ω := by
      simp only [hν₁, nuT]
      rw [min_eq_left (hτT.trans hρT.le), min_eq_left hτT]
    have hν₂ω : ν₂ ω = σ ω := by
      simp only [hν₂, nuT]
      rw [min_eq_left (hσT.trans hρT.le), min_eq_left hσT]
    obtain ⟨r₁, hr₁⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hτT)
    obtain ⟨r₂, hr₂⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hσT)
    have hv₁ := hitR_value hD ω (by positivity : 0 < l ^ 2) hr₁.symm
    have hv₂ := hitR_value hD ω (by positivity : 0 < (β * l) ^ 2) hr₂.symm
    have hs₁ : ∀ i, stoppedValue (X i) ν₁ ω = X i r₁ ω := fun i => by
      simp [stoppedValue, hν₁ω, ← hr₁, WithTop.untopA]
    have hs₂ : ∀ i, stoppedValue (X i) ν₂ ω = X i r₂ ω := fun i => by
      simp [stoppedValue, hν₂ω, ← hr₂, WithTop.untopA]
    have hge : k ≤ Dsq ω := by
      have := sq_dist_ge (s := s) (a := β * l) (b := l) hl.le (le_mul_of_one_le_left hl.le hβ.le)
        (fun i => X i r₂ ω) (fun i => X i r₁ ω) hv₂ hv₁
      have e : (β * l - l) ^ 2 = k := by rw [hk]; ring
      simp only [hDsq, hs₁, hs₂]
      linarith
    exact ENNReal.ofReal_le_ofReal hge
  have hSsub : S ⊆ {ω | l ≤ coreU s X T ω} := by
    intro ω hω
    have hcont : ∀ i ∈ s, Continuous fun t => X i t ω := fun i hi => hD.cont i hi ω
    obtain ⟨r, hr0, hrT, hrl⟩ := (hitR_le_iff hD ω _ T).1 hω
    exact (le_coreU_iff hT hcont hl.le).2 ⟨r, ⟨hr0, hrT⟩, hrl⟩
  have hDle : ∫ ω, Dsq ω ∂P ≤ P.real S * c := by
    have : ∫ ω, Dsq ω ∂P = ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν₂ ω ∂P -
        ∫ ω, ∑ i ∈ s, stoppedValue (B i) ν₁ ω ∂P := hDe
    linarith
  have hmain : ENNReal.ofReal k * P {ω | β * l ≤ coreU s X T ω ∧ Real.sqrt (∑ i ∈ s, B i T ω) < δ * l} ≤
      ENNReal.ofReal c * P {ω | l ≤ coreU s X T ω} := by
    calc ENNReal.ofReal k * P {ω | β * l ≤ coreU s X T ω ∧ Real.sqrt (∑ i ∈ s, B i T ω) < δ * l}
        ≤ ENNReal.ofReal k * P {ω | ENNReal.ofReal k ≤ ENNReal.ofReal (Dsq ω)} :=
          mul_le_mul' le_rfl (measure_mono hEsub)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Dsq ω) ∂P := hmk
      _ = ENNReal.ofReal (∫ ω, Dsq ω ∂P) := hlint
      _ ≤ ENNReal.ofReal (P.real S * c) := ENNReal.ofReal_le_ofReal hDle
      _ = ENNReal.ofReal c * P S := by
          rw [ENNReal.ofReal_mul measureReal_nonneg, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
      _ ≤ ENNReal.ofReal c * P {ω | l ≤ coreU s X T ω} := mul_le_mul' le_rfl (measure_mono hSsub)
  have hc' : c = k * (δ ^ 2 / (β - 1) ^ 2) := by
    have hb1 : β - 1 ≠ 0 := by linarith
    rw [hcdef, hk]
    field_simp
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hkpos
  have e : ENNReal.ofReal c = ENNReal.ofReal k * ENNReal.ofReal (δ ^ 2 / (β - 1) ^ 2) := by
    rw [hc']; exact ENNReal.ofReal_mul hkpos.le
  rw [e, mul_assoc] at hmain
  exact (ENNReal.mul_le_mul_iff_right hk0 ENNReal.ofReal_ne_top).1 hmain

lemma measurable_coreU (hD : CoreData P ℱ s X B) (T : ℝ) : Measurable (coreU s X T) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  haveI : Countable S := hSc.to_subtype
  have hmeas : ∀ q : Set.Icc (0 : ℝ) T, Measurable fun ω => Real.sqrt (∑ i ∈ s, X i q ω ^ 2) :=
    fun q => (Finset.measurable_sum _ fun i hi =>
      (ℱ.le q |> fun hle => ((hD.mart i hi).1 q).measurable.mono hle le_rfl).pow_const 2).sqrt
  have : coreU s X T = fun ω => ⨆ q : S, Real.sqrt (∑ i ∈ s, X i (q : Set.Icc (0 : ℝ) T) ω ^ 2) := by
    funext ω
    unfold coreU
    symm
    refine (hSd.ciSup' (f := fun t : Set.Icc (0 : ℝ) T => Real.sqrt (∑ i ∈ s, X i t ω ^ 2)) ?_)
    exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i hi =>
      ((hD.cont i hi ω).comp continuous_subtype_val).pow 2)
  rw [this]
  exact Measurable.iSup fun q => hmeas q

lemma coreU_nonneg (T : ℝ) (ω : Ω) : 0 ≤ coreU s X T ω :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _

end Core

/-! ### The constants -/

/-- The good-lambda threshold `δ_p` with `2^p δ_p² = 1/2`. -/
def bdgDelta (p : ℝ) : ℝ := Real.sqrt (1 / (2 : ℝ) ^ (p + 1))

/-- The explicit dimension-free BDG constant. -/
def bdgConst (p : ℝ) : ℝ := (2 : ℝ) ^ p * (bdgDelta p ^ p)⁻¹ / (1 - (2 : ℝ) ^ p * bdgDelta p ^ 2)

lemma bdgDelta_pos (p : ℝ) : 0 < bdgDelta p := Real.sqrt_pos.2 (by positivity)

lemma bdgDelta_sq (p : ℝ) : bdgDelta p ^ 2 = 1 / (2 : ℝ) ^ (p + 1) :=
  Real.sq_sqrt (by positivity)

lemma two_rpow_mul_bdgDelta_sq (p : ℝ) : (2 : ℝ) ^ p * bdgDelta p ^ 2 = 1 / 2 := by
  rw [bdgDelta_sq, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  field_simp

lemma bdgConst_nonneg (p : ℝ) : 0 ≤ bdgConst p := by
  unfold bdgConst
  rw [show (1 : ℝ) - (2 : ℝ) ^ p * bdgDelta p ^ 2 = 1 / 2 by rw [two_rpow_mul_bdgDelta_sq]; norm_num]
  have := bdgDelta_pos p
  positivity

section Core2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {κ : Type*} {s : Finset κ} {X B : κ → ℝ → Ω → ℝ}

/-- The finite-dimensional BDG inequality (everything everywhere). -/
theorem core_bdg (hD : CoreData P ℱ s X B) {T : ℝ} (hT : 0 ≤ T) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (coreU s X T ω ^ p) ∂P ≤
      ENNReal.ofReal (bdgConst p) *
        ∫⁻ ω, ENNReal.ofReal (Real.sqrt (∑ i ∈ s, B i T ω) ^ p) ∂P := by
  have hδ := bdgDelta_pos p
  have hV : Measurable fun ω => Real.sqrt (∑ i ∈ s, B i T ω) :=
    (Finset.measurable_sum _ fun i hi => (((hD.badapt i hi) T).measurable.mono (ℱ.le T) le_rfl)).sqrt
  have h := goodLambda_moment P (measurable_coreU hD T) hV (coreU_nonneg T)
    (fun ω => Real.sqrt_nonneg _) (p := p) (β := 2) (δ := bdgDelta p) (ε := bdgDelta p ^ 2)
    hp (by norm_num) hδ (by positivity)
    (by rw [two_rpow_mul_bdgDelta_sq]; norm_num)
    (fun l hl => by
      have := core_goodlambda hD hT hl (β := 2) (δ := bdgDelta p) (by norm_num) hδ
      have e : ((2 : ℝ) - 1) ^ 2 = 1 := by norm_num
      rw [e, div_one] at this
      exact this)
  exact h

end Core2


/-! ### Part 3: reduction of the Hilbert statement to the core -/

section Approx

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Finite orthonormal families that exhaust the norm: `∑_i ⟨e_n i, v⟩² → ‖v‖²` for all `v`. -/
lemma exists_approx_family :
    ∃ (d : ℕ → ℕ) (e : (n : ℕ) → Fin (d n) → H), (∀ n, Orthonormal ℝ (e n)) ∧
      ∀ v : H, Filter.Tendsto (fun n => ∑ i, inner ℝ (e n i) v ^ 2) Filter.atTop (𝓝 (‖v‖ ^ 2)) := by
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat ι
  have hfin : ∀ n : ℕ, {i : ι | g i < n}.Finite := fun n =>
    (Set.finite_Iio n).preimage (hg.injOn)
  let F : ℕ → Finset ι := fun n => (hfin n).toFinset
  have hFmono : Monotone F := by
    intro m n hmn i hi
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    omega
  have hFex : ∀ i, ∃ n, i ∈ F n := fun i => ⟨g i + 1, by simp [F]⟩
  have hFtend : Filter.Tendsto F Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_finset_of_monotone hFmono hFex
  refine ⟨fun n => (F n).card, fun n j => b (((F n).equivFin.symm j).val), fun n => ?_, fun v => ?_⟩
  · exact b.orthonormal.comp (fun j => (((F n).equivFin.symm j).val))
      (Subtype.val_injective.comp (F n).equivFin.symm.injective)
  · have h1 := (b.hasSum_inner_mul_inner v v).comp hFtend
    have h2 : ∀ n, ∑ i ∈ F n, inner ℝ v (b i) * inner ℝ (b i) v =
        ∑ j : Fin (F n).card, inner ℝ (b (((F n).equivFin.symm j).val)) v ^ 2 := by
      intro n
      calc ∑ i ∈ F n, inner ℝ v (b i) * inner ℝ (b i) v
          = ∑ i : ↥(F n), inner ℝ v (b i.val) * inner ℝ (b i.val) v :=
            (Finset.sum_coe_sort (F n) (fun i => inner ℝ v (b i) * inner ℝ (b i) v)).symm
        _ = ∑ j : Fin (F n).card, inner ℝ v (b (((F n).equivFin.symm j).val)) *
              inner ℝ (b (((F n).equivFin.symm j).val)) v :=
            (Equiv.sum_comp ((F n).equivFin.symm)
              (fun i : ↥(F n) => inner ℝ v (b i.val) * inner ℝ (b i.val) v)).symm
        _ = _ := Finset.sum_congr rfl fun j _ => by rw [real_inner_comm v, sq]
    simp_rw [Function.comp_def, h2, real_inner_self_eq_norm_sq] at h1
    exact h1

end Approx

section Clamp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Clamp a time into `[0, T]`. -/
def clampT (T t : ℝ) : ℝ := min (max t 0) T

lemma clampT_of_mem {T t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) T) : clampT T t = t := by
  unfold clampT; rw [max_eq_left h.1, min_eq_left h.2]

lemma clampT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT T t ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩

lemma continuous_clampT (T : ℝ) : Continuous (clampT T) :=
  (continuous_id.max continuous_const).min continuous_const

lemma monotone_clampT (T : ℝ) : Monotone (clampT T) := fun _ _ h =>
  min_le_min (max_le_max h le_rfl) le_rfl

lemma clampT_of_nonpos {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ 0) : clampT T t = 0 := by
  unfold clampT; rw [max_eq_right ht, min_eq_left hT]

/-- A martingale started at `0`, frozen outside `[0,T]`, is again a martingale. -/
lemma clamp_martingale {𝒢 : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ} (hZ : Martingale Z 𝒢 P)
    (hz0 : ∀ ω, Z 0 ω = 0) {T : ℝ} (hT : 0 ≤ T) :
    Martingale (fun t ω => Z (clampT T t) ω) 𝒢 P := by
  refine martingale_of_nonneg_times (fun t => ?_) (fun t ht ω => ?_) ?_
  · by_cases ht : 0 ≤ t
    · have : clampT T t ≤ t := (min_le_left _ _).trans (by rw [max_eq_left ht])
      exact (hZ.1 (clampT T t)).mono (𝒢.mono this)
    · have : (fun ω => Z (clampT T t) ω) = fun _ => (0 : ℝ) := by
        funext ω; rw [clampT_of_nonpos hT (not_le.1 ht).le]; exact hz0 ω
      rw [this]; exact stronglyMeasurable_const
  · simp [clampT_of_nonpos hT ht, hz0]
  · intro s t hs hst
    by_cases hsT : s ≤ T
    · have e1 : clampT T s = s := clampT_of_mem ⟨hs, hsT⟩
      have e2 : clampT T t = min t T := by
        unfold clampT; rw [max_eq_left (hs.trans hst)]
      simp only [e1, e2]
      exact hZ.2 s (min t T) (le_min hst hsT)
    · have e1 : clampT T s = T := by
        unfold clampT; rw [max_eq_left hs]; exact min_eq_right (not_le.1 hsT).le
      have e2 : clampT T t = T := by
        unfold clampT
        rw [max_eq_left (hs.trans hst)]; exact min_eq_right ((not_le.1 hsT).le.trans hst)
      simp only [e1, e2]
      exact (condExp_of_stronglyMeasurable (𝒢.le s) ((hZ.1 T).mono (𝒢.mono (not_le.1 hsT).le))
        (hZ.integrable T)).eventuallyEq

/-- Two processes continuous on `[0,T]` (a.e. for the second one) that agree a.e. at every fixed time
agree a.e. at all times of `[0,T]` simultaneously. -/
lemma ae_forall_eq_on_Icc {X Y : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hX : ∀ ω, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hY : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (h : ∀ s, X s =ᵐ[P] Y s) : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = Y t ω := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, X (clampT T (q : ℝ)) ω = Y (clampT T (q : ℝ)) ω :=
    ae_all_iff.2 fun q => h _
  filter_upwards [hq, hY] with ω hω hYω t ht
  have hXc : Continuous fun t => X (clampT T t) ω :=
    (hX ω).comp_continuous (continuous_clampT T) (fun t => clampT_mem hT t)
  have hYc : Continuous fun t => Y (clampT T t) ω :=
    hYω.comp_continuous (continuous_clampT T) (fun t => clampT_mem hT t)
  have heq : (fun t => X (clampT T t) ω) = fun t => Y (clampT T t) ω :=
    Rat.denseRange_cast.equalizer hXc hYc (funext hω)
  have := congrFun heq t
  simpa [clampT_of_mem ht] using this

end Clamp

section Coord

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}

lemma coord_isContSq (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (x : H) :
    IsContSqMartingale P ℱ T (fun t ω => inner ℝ (M t ω) x) where
  martingale := hM.martingale x
  zero := by filter_upwards [hM.zero] with ω h; simp [h]
  cont := by
    filter_upwards [hM.cont] with ω h
    exact (continuous_id.inner continuous_const).comp_continuousOn h
  sq_int := fun τ hτ => by
    have := (innerSL ℝ x).comp_memLp' (hM.sq_int τ hτ)
    have e : (fun ω => inner ℝ (M τ ω) x) = (innerSL ℝ x) ∘ M τ :=
      funext fun ω => real_inner_comm _ _
    rw [e]; exact this

/-- The bracket of a coordinate. -/
def coordBr (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (x : H) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ σ in Set.Icc 0 t, Sg σ ω x x

lemma coordBr_adapted (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (x : H) :
    Adapted ℱ (coordBr Sg x) := by
  intro t
  have h1 := (hM.martingale x).1 t
  have h2 := (hM.covariation x x).1 t
  have : coordBr Sg x t = fun ω => inner ℝ (M t ω) x * inner ℝ (M t ω) x -
      (inner ℝ (M t ω) x * inner ℝ (M t ω) x - ∫ σ in Set.Icc 0 t, Sg σ ω x x) := by
    funext ω; simp [coordBr]
  rw [this]
  exact (h1.measurable.mul h1.measurable).sub h2.measurable

lemma coordBr_zero (x : H) (ω : Ω) : coordBr Sg x 0 ω = 0 := by
  simp [coordBr]

lemma coordBr_cont (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hT : 0 ≤ T) (x : H) :
    ∀ᵐ ω ∂P, ContinuousOn (fun τ => coordBr Sg x τ ω) (Set.Icc 0 T) := by
  filter_upwards [hM.sigma_entry_int] with ω h
  have hint := h x x
  have h1 := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
    (μ := volume) (f := fun σ => Sg σ ω x x) (by rwa [Set.uIcc_of_le hT])
  rw [Set.uIcc_of_le hT] at h1
  refine h1.congr fun τ hτ => ?_
  simp only [coordBr]
  rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]

lemma coordBr_mono (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (x : H) :
    ∀ᵐ ω ∂P, MonotoneOn (fun τ => coordBr Sg x τ ω) (Set.Icc 0 T) := by
  filter_upwards [hM.sigma_entry_int, hM.sigma_traceClass] with ω h htc a ha b hb hab
  have hint := h x x
  simp only [coordBr]
  refine setIntegral_mono_set (hint.mono_set (Set.Icc_subset_Icc le_rfl hb.2)) ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    exact (htc σ ⟨hσ.1, hσ.2.trans hb.2⟩).nonneg x
  · exact Filter.Eventually.of_forall (Set.Icc_subset_Icc le_rfl hab)

lemma coordBr_compensator (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (x : H) :
    Martingale (fun τ ω => (inner ℝ (M τ ω) x) ^ 2 - coordBr Sg x τ ω) ℱ P := by
  have := hM.covariation x x
  simpa [coordBr, sq] using this

omit [MeasurableSpace H] [BorelSpace H] in
lemma sum_diag_le_traceNormForm {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {d : ℕ}
    {e : Fin d → H} (he : Orthonormal ℝ e) : ∑ i, C (e i) (e i) ≤ traceNormForm C := by
  have h := pairSum_le_traceNormForm (bddAbove_pairSum hC) ⟨⟨d, e, e⟩, he, he⟩
  refine le_trans ?_ h
  exact Finset.sum_le_sum fun i _ => le_abs_self _

lemma sum_coordBr_le (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {d : ℕ} {e : Fin d → H}
    (he : Orthonormal ℝ e) :
    ∀ᵐ ω ∂P, 0 ≤ ∑ i, coordBr Sg (e i) T ω ∧
      ∑ i, coordBr Sg (e i) T ω ≤ ∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω) := by
  filter_upwards [hM.sigma_traceClass, hM.sigma_entry_int, hM.sigma_pathint] with ω htc hent hpath
  have hsum : ∑ i, coordBr Sg (e i) T ω = ∫ σ in Set.Icc 0 T, ∑ i, Sg σ ω (e i) (e i) := by
    simp only [coordBr]
    rw [integral_finsetSum]
    exact fun i _ => hent (e i) (e i)
  rw [hsum]
  have hint : IntegrableOn (fun σ => ∑ i, Sg σ ω (e i) (e i)) (Set.Icc 0 T) :=
    integrable_finsetSum _ fun i _ => hent (e i) (e i)
  refine ⟨setIntegral_nonneg measurableSet_Icc fun σ hσ =>
    Finset.sum_nonneg fun i _ => (htc σ hσ).nonneg _, ?_⟩
  exact setIntegral_mono_on hint hpath measurableSet_Icc fun σ hσ =>
    sum_diag_le_traceNormForm (htc σ hσ) he

lemma coordBr_integrable (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {x : H}
    (hx : ‖x‖ = 1) : Integrable (coordBr Sg x T) P := by
  have he : Orthonormal ℝ (fun _ : Fin 1 => x) := orthonormal_subsingleton_iff.2 (fun _ => hx)
  have hmeas : AEStronglyMeasurable (coordBr Sg x T) P :=
    (((coordBr_adapted hM x T).mono (ℱ.le T) le_rfl)).aestronglyMeasurable
  refine Integrable.mono' hM.sigma_int hmeas ?_
  filter_upwards [sum_coordBr_le hM he] with ω h
  have := h.2
  simp only [Finset.univ_unique, Finset.sum_singleton] at this h
  rw [Real.norm_of_nonneg h.1]
  exact this

lemma exists_clean_coord (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hT : 0 ≤ T) {x : H}
    (hx : ‖x‖ = 1) :
    ∃ M₁ A₁ : ℝ → Ω → ℝ, CleanData P (augFiltration P ℱ) T M₁ A₁ ∧
      (∀ s, M₁ s =ᵐ[P] fun ω => inner ℝ (M s ω) x) ∧ ∀ s, A₁ s =ᵐ[P] coordBr Sg x s := by
  have hQ : IsQuadraticVariation P ℱ T (fun t ω => inner ℝ (M t ω) x) (coordBr Sg x) :=
    { adapted := coordBr_adapted hM x
      zero := Filter.Eventually.of_forall (coordBr_zero x)
      cont := coordBr_cont hM hT x
      mono := coordBr_mono hM x
      compensator := coordBr_compensator hM x }
  exact exists_clean (coord_isContSq hM x) hQ (coordBr_integrable hM hx)

end Coord

section FromClean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {κ : Type*}

lemma coreData_of_clean (s : Finset κ) {T : ℝ} (hT : 0 ≤ T) (M₁ A₁ : κ → ℝ → Ω → ℝ)
    (hC : ∀ i ∈ s, CleanData P ℱ T (M₁ i) (A₁ i)) :
    CoreData P ℱ s (fun i t ω => M₁ i (clampT T t) ω) (fun i t ω => A₁ i (clampT T t) ω) where
  mart i hi := clamp_martingale (hC i hi).mart (hC i hi).zeroM hT
  cont i hi ω := ((hC i hi).contM ω).comp_continuous (continuous_clampT T) (clampT_mem hT)
  zero i hi ω := by
    rw [clampT_of_mem ⟨le_rfl, hT⟩]; exact (hC i hi).zeroM ω
  mart2 i hi := clamp_martingale (𝒢 := ℱ) (Z := fun t ω => M₁ i t ω ^ 2 - A₁ i t ω)
    (hC i hi).qmart (fun ω => by simp [(hC i hi).zeroM ω, (hC i hi).zeroA ω]) hT
  bcont i hi ω := ((hC i hi).contA ω).comp_continuous (continuous_clampT T) (clampT_mem hT)
  bmono i hi ω a b hab :=
    (hC i hi).monoA ω (clampT_mem hT a) (clampT_mem hT b) (monotone_clampT T hab)
  bzero i hi ω := by
    rw [clampT_of_mem ⟨le_rfl, hT⟩]; exact (hC i hi).zeroA ω
  badapt i hi t := by
    by_cases ht : 0 ≤ t
    · have : clampT T t ≤ t := (min_le_left _ _).trans (by rw [max_eq_left ht])
      exact (((hC i hi).adaptedA (clampT T t)).mono (ℱ.mono this) le_rfl).stronglyMeasurable
    · have : (fun ω => A₁ i (clampT T t) ω) = fun _ => (0 : ℝ) := by
        funext ω; rw [clampT_of_nonpos hT (not_le.1 ht).le]; exact (hC i hi).zeroA ω
      change StronglyMeasurable[ℱ t] (fun ω => A₁ i (clampT T t) ω)
      rw [this]; exact stronglyMeasurable_const

end FromClean

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}

/-- The dimension-free Burkholder–Davis–Gundy upper inequality for Hilbert-valued continuous
martingales with operator covariation, with an explicit constant depending only on `p`. -/
theorem hilbert_bdg_aux {T : ℝ} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ p ∂P ≤
      ENNReal.ofReal (bdgConst p) *
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
  by_cases hT : 0 ≤ T
  swap
  · have : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (by simpa using hT)
    simp [this, ENNReal.zero_rpow_of_pos hp]
  obtain ⟨d, e, he, hconv⟩ := exists_approx_family (H := H)
  have hunit : ∀ n i, ‖e n i‖ = 1 := fun n i => (he n).norm_eq_one i
  have hcl : ∀ x : H, ‖x‖ = 1 → ∃ M₁ A₁ : ℝ → Ω → ℝ,
      CleanData P (augFiltration P ℱ) T M₁ A₁ ∧
        (∀ s, M₁ s =ᵐ[P] fun ω => inner ℝ (M s ω) x) ∧ ∀ s, A₁ s =ᵐ[P] coordBr Sg x s :=
    fun x hx => exists_clean_coord hM hT hx
  choose! M₁ A₁ hC hM1 hA1 using hcl
  set Xn : (n : ℕ) → Fin (d n) → ℝ → Ω → ℝ := fun n i t ω => M₁ (e n i) (clampT T t) ω with hXn
  set Bn : (n : ℕ) → Fin (d n) → ℝ → Ω → ℝ := fun n i t ω => A₁ (e n i) (clampT T t) ω with hBn
  have hDn : ∀ n, CoreData P (augFiltration P ℱ) (Finset.univ : Finset (Fin (d n))) (Xn n) (Bn n) :=
    fun n => coreData_of_clean _ hT (fun i => M₁ (e n i)) (fun i => A₁ (e n i))
      (fun i _ => hC _ (hunit n i))
  have hcore := fun n => core_bdg (hDn n) hT hp
  -- (E1)
  have hE1 : ∀ᵐ ω ∂P, ∀ n (i : Fin (d n)), ∀ t ∈ Set.Icc (0 : ℝ) T,
      Xn n i t ω = inner ℝ (M t ω) (e n i) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro i
    have h := ae_forall_eq_on_Icc (P := P) (X := M₁ (e n i)) (Y := fun t ω => inner ℝ (M t ω) (e n i)) hT
      (fun ω => (hC _ (hunit n i)).contM ω) (coord_isContSq hM (e n i)).cont
      (hM1 _ (hunit n i))
    filter_upwards [h] with ω hω t ht
    simp only [hXn, clampT_of_mem ht]
    exact hω t ht
  -- (E2)
  have hE2 : ∀ᵐ ω ∂P, ∀ n, ∑ i, Bn n i T ω ≤ ∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω) := by
    rw [ae_all_iff]; intro n
    have h1 : ∀ i : Fin (d n), ∀ᵐ ω ∂P, Bn n i T ω = coordBr Sg (e n i) T ω := fun i => by
      filter_upwards [hA1 (e n i) (hunit n i) T] with ω hω
      simp only [hBn, clampT_of_mem (⟨hT, le_rfl⟩ : T ∈ Set.Icc (0 : ℝ) T)]
      exact hω
    have h2 : ∀ᵐ ω ∂P, ∀ i, Bn n i T ω = coordBr Sg (e n i) T ω := ae_all_iff.2 h1
    filter_upwards [h2, sum_coordBr_le hM (he n)] with ω h2 h3
    calc ∑ i, Bn n i T ω = ∑ i, coordBr Sg (e n i) T ω := Finset.sum_congr rfl fun i _ => h2 i
      _ ≤ _ := h3.2
  have hτnn : ∀ ω, 0 ≤ ∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω) := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _
  have hG : ∀ᵐ ω ∂P, ∀ n, ENNReal.ofReal (Real.sqrt (∑ i, Bn n i T ω) ^ p) ≤
      (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) := by
    filter_upwards [hE2, hM.sigma_pathint] with ω h2 hpath n
    have hle : Real.sqrt (∑ i, Bn n i T ω) ^ p ≤ Real.sqrt (∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω)) ^ p :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (h2 n)) hp.le
    have hrw : Real.sqrt (∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω)) ^ p =
        (∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω)) ^ (p / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hτnn ω)]; congr 1; ring
    calc ENNReal.ofReal (Real.sqrt (∑ i, Bn n i T ω) ^ p)
        ≤ ENNReal.ofReal (Real.sqrt (∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω)) ^ p) :=
          ENNReal.ofReal_le_ofReal hle
      _ = (ENNReal.ofReal (∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω))) ^ (p / 2) := by
          rw [hrw, ENNReal.ofReal_rpow_of_nonneg (hτnn ω) (by positivity)]
      _ = _ := by
          rw [ofReal_integral_eq_lintegral_ofReal hpath
            (Filter.Eventually.of_forall fun _ => traceNormForm_nonneg _)]
  -- (E3)
  have hE3 : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ p ≤
      Filter.liminf (fun n => ENNReal.ofReal (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω ^ p))
        Filter.atTop := by
    filter_upwards [hE1] with ω h1
    have hlt : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ ≤
        Filter.liminf (fun n => ENNReal.ofReal (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω))
          Filter.atTop := by
      intro t ht
      have hsq : Filter.Tendsto (fun n => ∑ i, (Xn n i t ω) ^ 2) Filter.atTop (𝓝 (‖M t ω‖ ^ 2)) := by
        refine (hconv (M t ω)).congr fun n => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1 n i t ht, real_inner_comm]
      have hsqrt : Filter.Tendsto (fun n => Real.sqrt (∑ i, (Xn n i t ω) ^ 2)) Filter.atTop
          (𝓝 ‖M t ω‖) := by
        have := (Real.continuous_sqrt.tendsto _).comp hsq
        simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
      have hof := ENNReal.tendsto_ofReal hsqrt
      rw [← ofReal_norm_eq_enorm, ← hof.liminf_eq]
      refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
      exact ENNReal.ofReal_le_ofReal
        ((coreU_attained hT (fun i _ => (hDn n).cont i (Finset.mem_univ i) ω)).1 t ht)
    have hsup : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ≤
        Filter.liminf (fun n => ENNReal.ofReal (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω))
          Filter.atTop := iSup₂_le hlt
    calc (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ p
        ≤ (Filter.liminf (fun n => ENNReal.ofReal (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω))
            Filter.atTop) ^ p := ENNReal.rpow_le_rpow hsup hp.le
      _ = Filter.liminf ((fun x : ℝ≥0∞ => x ^ p) ∘ fun n => ENNReal.ofReal
            (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω)) Filter.atTop :=
          Monotone.map_liminf_of_continuousAt (ENNReal.monotone_rpow_of_nonneg hp.le) _
            (ENNReal.continuous_rpow_const.continuousAt)
      _ = _ := by
          congr 1; funext n
          simp only [Function.comp]
          rw [ENNReal.ofReal_rpow_of_nonneg (coreU_nonneg T ω) hp.le]
  -- assembly
  have hmeas : ∀ n, Measurable fun ω => ENNReal.ofReal (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω ^ p) :=
    fun n => ((measurable_coreU (hDn n) T).pow_const p).ennreal_ofReal
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω ^ p) ∂P ≤
      ENNReal.ofReal (bdgConst p) *
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
    intro n
    refine (hcore n).trans (mul_le_mul' le_rfl (lintegral_mono_ae ?_))
    filter_upwards [hG] with ω hω using hω n
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ p ∂P
      ≤ ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal
          (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω ^ p)) Filter.atTop ∂P :=
        lintegral_mono_ae hE3
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal
          (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω ^ p) ∂P) Filter.atTop :=
        lintegral_liminf_le hmeas
    _ ≤ Filter.limsup (fun n => ∫⁻ ω, ENNReal.ofReal
          (coreU (Finset.univ : Finset (Fin (d n))) (Xn n) T ω ^ p) ∂P) Filter.atTop :=
        Filter.liminf_le_limsup
    _ ≤ _ := Filter.limsup_le_of_le (h := Filter.Eventually.of_forall hbound)

end Main

/-- **Dimension-free Burkholder–Davis–Gundy upper inequality** for continuous square-integrable
Hilbert-valued martingales with operator covariation: for every `p ≥ 2` (in fact every `p > 0`)
there is a constant `C`, depending only on `p`, such that for every probability space, filtration,
separable Hilbert space and `IsHilbertMartingaleWithCovariation` on `[0,T]`,
`E sup_{t ≤ T} ‖M_t‖^p ≤ C · E (∫_0^T ‖Σ_r‖₁ dr)^{p/2}` (both sides `lintegral`s in `ℝ≥0∞`). -/
theorem hilbert_bdg (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        (T : ℝ) (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)),
        IsHilbertMartingaleWithCovariation P ℱ T M Sg →
        ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ p ∂P ≤
          ENNReal.ofReal C *
            ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P :=
  ⟨bdgConst p, bdgConst_nonneg p, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM =>
    hilbert_bdg_aux hM (by linarith)⟩


end HilbertBDG
end HRS
