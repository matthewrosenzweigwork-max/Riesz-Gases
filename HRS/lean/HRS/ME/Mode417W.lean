import HRS.ME.Est417
import HRS.ME.Stat417

/-!
# Row 4.17, packet M-mode: proof of `mode_window_bound`

Statement copied verbatim from `HRS/ME/Spec417Est.lean`.  Helper lemmas carry the prefix `mode417`.

Route (for `J(b) = ∫_0^b γ(b-r)(-G+E)(X^r) dr`, `b = a + t`): the integration-by-parts identity
`J(b) = -γ(0)F(X^b) + γ(b)F(X^0) + S(b) - ∫γ'(max(b-r) 0)F(X^r) + ∫γ(max(b-r) 0)E(X^r)` with
`S(b) = γ(0)M_b + ∫_0^b γ'(b-r)M_r dr`, five terms bounded by `(x1+...+x5)² ≤ 5 Σ xᵢ²`, and suprema
bounded by M4b (for `S`), M4c (for the two weighted integrals) and the Lyons-Zheng bound (for `F`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- Five-term Cauchy-Schwarz with the signs of the identity. -/
theorem mode417_sq5 (x1 x2 x3 x4 x5 : ℝ) :
    (-x1 + x2 + x3 - x4 + x5) ^ 2 ≤ 5 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2) := by
  nlinarith [sq_nonneg (x1 + x2), sq_nonneg (x1 + x3), sq_nonneg (x1 - x4), sq_nonneg (x1 + x5),
    sq_nonneg (x2 - x3), sq_nonneg (x2 + x4), sq_nonneg (x2 - x5), sq_nonneg (x3 + x4),
    sq_nonneg (x3 - x5), sq_nonneg (x4 + x5)]

/-- Deterministic integration by parts identity for one window `[0, b]`. -/
theorem mode417_ident (g e f γ γ' : ℝ → ℝ) (f0 b : ℝ) (hb : 0 ≤ b)
    (hg : IntervalIntegrable g volume 0 b) (he : IntervalIntegrable e volume 0 b)
    (hfc : ContinuousOn (fun r => f r - f0 - ∫ u in (0:ℝ)..r, g u) (Set.Icc 0 b))
    (hγ : ∀ x ∈ Set.Icc 0 b, HasDerivWithinAt γ (γ' x) (Set.Icc 0 b) x)
    (hγ' : ContinuousOn γ' (Set.Icc 0 b)) :
    ∫ r in (0:ℝ)..b, γ (b - r) * (-g r + e r) =
      -(γ 0 * f b) + γ b * f0 +
        (γ 0 * (f b - f0 - ∫ u in (0:ℝ)..b, g u) +
          ∫ r in (0:ℝ)..b, γ' (b - r) * (f r - f0 - ∫ u in (0:ℝ)..r, g u))
        - (∫ r in (0:ℝ)..b, γ' (max (b - r) 0) * f r) + ∫ r in (0:ℝ)..b, γ (max (b - r) 0) * e r := by
  have hu : Set.uIcc (0:ℝ) b = Set.Icc 0 b := Set.uIcc_of_le hb
  have hγc : ContinuousOn γ (Set.Icc 0 b) := fun x hx => (hγ x hx).continuousWithinAt
  have hmap : ∀ r ∈ Set.Icc (0:ℝ) b, b - r ∈ Set.Icc (0:ℝ) b := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hcont_sub : ContinuousOn (fun r : ℝ => b - r) (Set.Icc 0 b) :=
    (by fun_prop : Continuous fun r : ℝ => b - r).continuousOn
  have hcγ : ContinuousOn (fun r => γ (b - r)) (Set.Icc 0 b) := hγc.comp hcont_sub hmap
  have hcγ' : ContinuousOn (fun r => γ' (b - r)) (Set.Icc 0 b) := hγ'.comp hcont_sub hmap
  have hAc : ContinuousOn (fun r => ∫ u in (0:ℝ)..r, g u) (Set.Icc 0 b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hg Set.left_mem_uIcc
    rw [hu] at h
    exact h
  have hfcont : ContinuousOn f (Set.Icc 0 b) := by
    have h : ContinuousOn (fun r => (f r - f0 - ∫ u in (0:ℝ)..r, g u) + f0 + ∫ u in (0:ℝ)..r, g u)
        (Set.Icc 0 b) := (hfc.add continuousOn_const).add hAc
    exact h.congr (fun r _ => by dsimp only; ring)
  have hγ'I : IntervalIntegrable γ' volume 0 b := hγ'.intervalIntegrable_of_Icc hb
  -- splitting of the integrand
  have hgI : IntervalIntegrable (fun r => γ (b - r) * g r) volume 0 b :=
    hg.continuousOn_mul (by rw [hu]; exact hcγ)
  have heI : IntervalIntegrable (fun r => γ (b - r) * e r) volume 0 b :=
    he.continuousOn_mul (by rw [hu]; exact hcγ)
  have hsplit : ∫ r in (0:ℝ)..b, γ (b - r) * (-g r + e r) =
      -(∫ r in (0:ℝ)..b, γ (b - r) * g r) + ∫ r in (0:ℝ)..b, γ (b - r) * e r := by
    have h1 : (fun r => γ (b - r) * (-g r + e r)) =
        fun r => -(γ (b - r) * g r) + γ (b - r) * e r := by
      funext r; ring
    have hneg : IntervalIntegrable (fun r => -(γ (b - r) * g r)) volume 0 b := hgI.neg
    rw [h1, intervalIntegral.integral_add hneg heI, intervalIntegral.integral_neg]
  -- integration by parts (M3)
  have hibp := ibp_weighted_proof g γ γ' b hb hg hγ hγ'
  -- expansion of the primitive term
  have hI1 : IntervalIntegrable (fun r => γ' (b - r) * f r) volume 0 b :=
    (hcγ'.mul hfcont).intervalIntegrable_of_Icc hb
  have hI2 : IntervalIntegrable (fun r => f0 * γ' (b - r)) volume 0 b :=
    (continuousOn_const.mul hcγ').intervalIntegrable_of_Icc hb
  have hI3 : IntervalIntegrable (fun r => γ' (b - r) * (f r - f0 - ∫ u in (0:ℝ)..r, g u)) volume 0 b :=
    (hcγ'.mul hfc).intervalIntegrable_of_Icc hb
  have hAexp : ∫ r in (0:ℝ)..b, γ' (b - r) * ∫ u in (0:ℝ)..r, g u =
      (∫ r in (0:ℝ)..b, γ' (b - r) * f r) - f0 * (∫ r in (0:ℝ)..b, γ' (b - r)) -
        ∫ r in (0:ℝ)..b, γ' (b - r) * (f r - f0 - ∫ u in (0:ℝ)..r, g u) := by
    have h1 : (fun r => γ' (b - r) * ∫ u in (0:ℝ)..r, g u) = fun r =>
        (γ' (b - r) * f r - f0 * γ' (b - r)) - γ' (b - r) * (f r - f0 - ∫ u in (0:ℝ)..r, g u) := by
      funext r; ring
    rw [h1, intervalIntegral.integral_sub (hI1.sub hI2) hI3, intervalIntegral.integral_sub hI1 hI2,
      intervalIntegral.integral_const_mul]
  -- the weight integrates to `γ b - γ 0`
  have hJc : ∫ r in (0:ℝ)..b, γ' (b - r) = γ b - γ 0 := by
    have h1 := intervalIntegral.integral_comp_sub_left γ' b (a := 0) (b := b)
    rw [h1, sub_self, sub_zero]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hγc
      (fun x hx => (hγ x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hγ'I
  -- replacing `γ'(b-r)`, `γ(b-r)` by their `max` versions (equal for `r ≤ b`)
  have hmaxf : ∫ r in (0:ℝ)..b, γ' (max (b - r) 0) * f r = ∫ r in (0:ℝ)..b, γ' (b - r) * f r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [hu] at hr
    show γ' (max (b - r) 0) * f r = γ' (b - r) * f r
    rw [max_eq_left (by linarith [hr.2])]
  have hmaxe : ∫ r in (0:ℝ)..b, γ (max (b - r) 0) * e r = ∫ r in (0:ℝ)..b, γ (b - r) * e r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [hu] at hr
    show γ (max (b - r) 0) * e r = γ (b - r) * e r
    rw [max_eq_left (by linarith [hr.2])]
  rw [hmaxf, hmaxe, hsplit, hibp, hAexp, hJc]
  ring

/-- Measurable modification of a process which is a.s. continuous in the time variable on `[0, H]`. -/
theorem mode417_modify {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : ℝ → Ω → ℝ) (H : ℝ)
    (hH : 0 ≤ H) (hmeas : ∀ t, Measurable (M t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 H)) :
    ∃ Mt : ℝ → Ω → ℝ, (∀ t, Measurable (Mt t)) ∧ Measurable (fun p : ℝ × Ω => Mt p.1 p.2) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0:ℝ) H, Mt t ω = M t ω := by
  classical
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hgood : ∀ ω, ω ∉ N → ContinuousOn (fun t => M t ω) (Set.Icc 0 H) := by
    intro ω hω
    by_contra hc
    exact hω (hsub (show ω ∈ {ω | ¬ ContinuousOn (fun t => M t ω) (Set.Icc 0 H)} from hc))
  have hNm' : MeasurableSet {ω : Ω | ω ∈ N} := by rwa [Set.setOf_mem_eq]
  let Mt : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else M (max 0 (min t H)) ω
  have hMt_meas : ∀ t, Measurable (Mt t) := fun t =>
    Measurable.ite hNm' measurable_const (hmeas _)
  have hMt_cont : ∀ ω, Continuous (fun t => Mt t ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · have hfun : (fun t => Mt t ω) = fun _ => (0:ℝ) := funext fun t => if_pos hω
      rw [hfun]
      exact continuous_const
    · have hfun : (fun t => Mt t ω) = fun t => M (max 0 (min t H)) ω :=
        funext fun t => if_neg hω
      rw [hfun]
      exact (hgood ω hω).comp_continuous (continuous_const.max (continuous_id.min continuous_const))
        (fun t => ⟨le_max_left _ _, max_le hH (min_le_right _ _)⟩)
  refine ⟨Mt, hMt_meas, ?_, ?_⟩
  · exact measurable_uncurry_of_continuous_of_measurable hMt_cont hMt_meas
  · filter_upwards [hNae] with ω hω
    intro t ht
    simp only [Mt, if_neg hω]
    rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Density of the rational times in a window: the value at any point of the window is dominated by the
supremum over the rational times of the window (for a continuous function on the window). -/
theorem mode417_le_sup (g : ℝ → ℝ) (a T : ℝ) (hT : 0 < T)
    (hg : ContinuousOn g (Set.Icc a (a + T))) (x : ℝ) (hx : x ∈ Set.Icc a (a + T)) :
    ENNReal.ofReal (g x ^ 2) ≤ ⨆ s ∈ ratTimes a T, ENNReal.ofReal (g s ^ 2) := by
  have hq : ∀ δ : ℝ, 0 < δ → ∃ q : ℚ, (q : ℝ) ∈ Set.Icc a (a + T) ∧ |(q : ℝ) - x| < δ := by
    intro δ hδ
    have hlt : max a (x - δ) < min (a + T) (x + δ) :=
      lt_min (max_lt (by linarith [hx.1]) (by linarith [hx.2]))
        (max_lt (by linarith [hx.1]) (by linarith))
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn hlt
    refine ⟨q, ⟨le_trans (le_max_left _ _) h1.le, le_trans h2.le (min_le_left _ _)⟩, ?_⟩
    rw [abs_lt]
    constructor
    · linarith [le_max_right a (x - δ)]
    · linarith [min_le_right (a + T) (x + δ)]
  choose q hqI hqd using fun n : ℕ => hq (1 / ((n : ℝ) + 1)) (by positivity)
  have hmem : ∀ n, (q n : ℝ) ∈ ratTimes a T := fun n => ⟨hqI n, q n, rfl⟩
  have hlim : Tendsto (fun n => (q n : ℝ)) atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact (hqd n).le
  have hcw : ContinuousWithinAt g (Set.Icc a (a + T)) x := hg x hx
  have hcomp : Tendsto (fun n => g (q n)) atTop (nhds (g x)) :=
    hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hqI⟩)
  have hfin : Tendsto (fun n => ENNReal.ofReal (g (q n) ^ 2)) atTop
      (nhds (ENNReal.ofReal (g x ^ 2))) :=
    ENNReal.tendsto_ofReal (hcomp.pow 2)
  refine le_of_tendsto hfin (Filter.Eventually.of_forall fun n => ?_)
  exact le_iSup₂ (f := fun (s : ℝ) (_ : s ∈ ratTimes a T) => ENNReal.ofReal (g s ^ 2)) (q n : ℝ) (hmem n)

/-- One-time bound: the marginal of `Φ r` under `P` is `μ`, so the second moment is that of `μ`. -/
theorem mode417_onetime {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω)
    (μ : Measure Y) (Φ : ℝ≥0 → Ω → Y) (hΦ : ∀ t, Measurable (Φ t)) (H : ℝ)
    (hst : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (Φ t) = μ) (f : Y → ℝ) (hf : Measurable f) (κ : ℝ)
    (hκ : ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂μ ≤ ENNReal.ofReal κ) (r : ℝ) (hr : 0 ≤ r) (hrH : r ≤ H) :
    ∫⁻ ω, ENNReal.ofReal (f (Φ r.toNNReal ω) ^ 2) ∂P ≤ ENNReal.ofReal κ := by
  have hmeas : Measurable (fun y => ENNReal.ofReal (f y ^ 2)) := (hf.pow_const 2).ennreal_ofReal
  have hrH' : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by
    rw [Real.coe_toNNReal r hr]
    exact hrH
  calc ∫⁻ ω, ENNReal.ofReal (f (Φ r.toNNReal ω) ^ 2) ∂P
      = ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂(P.map (Φ r.toNNReal)) :=
        (lintegral_map hmeas (hΦ _)).symm
    _ = ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂μ := by rw [hst _ hrH']
    _ ≤ ENNReal.ofReal κ := hκ

/-- Joint measurability gives measurability of the interval integral in the parameter. -/
theorem mode417_intr_meas {Ω : Type*} [MeasurableSpace Ω] (h : ℝ × Ω → ℝ) (hh : Measurable h)
    (b : ℝ) : Measurable (fun ω => ∫ r in (0:ℝ)..b, h (r, ω)) := by
  have hm : ∀ (ν : Measure ℝ) [SFinite ν], Measurable (fun ω => ∫ r, h (r, ω) ∂ν) := by
    intro ν _
    have hf : StronglyMeasurable (fun q : Ω × ℝ => h (q.2, q.1)) :=
      (hh.comp measurable_swap).stronglyMeasurable
    exact (hf.integral_prod_right' (ν := ν)).measurable
  show Measurable (fun ω => (∫ r in Set.Ioc (0:ℝ) b, h (r, ω)) - ∫ r in Set.Ioc b 0, h (r, ω))
  exact (hm _).sub (hm _)

/-- Taking suprema over a set of a sum bounded by a sum of suprema. -/
theorem mode417_sup5 {ι : Type*} (S : Set ι) (c : ℝ≥0∞) (Φ A1 A2 A3 A4 A5 : ι → ℝ≥0∞)
    (h : ∀ t ∈ S, Φ t ≤ c * (A1 t + A2 t + A3 t + A4 t + A5 t)) :
    (⨆ t ∈ S, Φ t) ≤
      c * ((⨆ t ∈ S, A1 t) + (⨆ t ∈ S, A2 t) + (⨆ t ∈ S, A3 t) + (⨆ t ∈ S, A4 t) + (⨆ t ∈ S, A5 t)) := by
  refine iSup₂_le fun t ht => (h t ht).trans ?_
  have e1 : A1 t ≤ ⨆ t ∈ S, A1 t := le_iSup₂ (f := fun t (_ : t ∈ S) => A1 t) t ht
  have e2 : A2 t ≤ ⨆ t ∈ S, A2 t := le_iSup₂ (f := fun t (_ : t ∈ S) => A2 t) t ht
  have e3 : A3 t ≤ ⨆ t ∈ S, A3 t := le_iSup₂ (f := fun t (_ : t ∈ S) => A3 t) t ht
  have e4 : A4 t ≤ ⨆ t ∈ S, A4 t := le_iSup₂ (f := fun t (_ : t ∈ S) => A4 t) t ht
  have e5 : A5 t ≤ ⨆ t ∈ S, A5 t := le_iSup₂ (f := fun t (_ : t ∈ S) => A5 t) t ht
  gcongr
  all_goals first | exact e1 | exact e2 | exact e3 | exact e4 | exact e5 | skip

/-- Sub-additivity of `ofReal` on a sum of five terms. -/
theorem mode417_ofReal_sum5 (a b c e f : ℝ) :
    ENNReal.ofReal (a + b + c + e + f) ≤
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal e + ENNReal.ofReal f := by
  calc ENNReal.ofReal (a + b + c + e + f) ≤ ENNReal.ofReal (a + b + c + e) + ENNReal.ofReal f :=
        ENNReal.ofReal_add_le
    _ ≤ (ENNReal.ofReal (a + b + c) + ENNReal.ofReal e) + ENNReal.ofReal f :=
        add_le_add ENNReal.ofReal_add_le le_rfl
    _ ≤ ((ENNReal.ofReal (a + b) + ENNReal.ofReal c) + ENNReal.ofReal e) + ENNReal.ofReal f :=
        add_le_add (add_le_add ENNReal.ofReal_add_le le_rfl) le_rfl
    _ ≤ (((ENNReal.ofReal a + ENNReal.ofReal b) + ENNReal.ofReal c) + ENNReal.ofReal e)
          + ENNReal.ofReal f :=
        add_le_add (add_le_add (add_le_add ENNReal.ofReal_add_le le_rfl) le_rfl) le_rfl

/-- The five-term square bound in `ℝ≥0∞`. -/
theorem mode417_ofReal5 (x1 x2 x3 x4 x5 : ℝ) :
    ENNReal.ofReal ((-x1 + x2 + x3 - x4 + x5) ^ 2) ≤
      ENNReal.ofReal 5 * (ENNReal.ofReal (x1 ^ 2) + ENNReal.ofReal (x2 ^ 2) + ENNReal.ofReal (x3 ^ 2) +
        ENNReal.ofReal (x4 ^ 2) + ENNReal.ofReal (x5 ^ 2)) := by
  calc ENNReal.ofReal ((-x1 + x2 + x3 - x4 + x5) ^ 2)
      ≤ ENNReal.ofReal (5 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2)) :=
        ENNReal.ofReal_le_ofReal (mode417_sq5 x1 x2 x3 x4 x5)
    _ = ENNReal.ofReal 5 * ENNReal.ofReal (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2) :=
        ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 5 * (ENNReal.ofReal (x1 ^ 2) + ENNReal.ofReal (x2 ^ 2) + ENNReal.ofReal (x3 ^ 2) +
        ENNReal.ofReal (x4 ^ 2) + ENNReal.ofReal (x5 ^ 2)) :=
        by gcongr; exact mode417_ofReal_sum5 _ _ _ _ _


/-- Restriction of an interval integrable function to a smaller window `[0, x]`. -/
theorem mode417_ii_sub {f : ℝ → ℝ} {H x : ℝ} (hf : IntervalIntegrable f volume 0 H) (hx0 : 0 ≤ x)
    (hxH : x ≤ H) (hH : 0 ≤ H) : IntervalIntegrable f volume 0 x :=
  hf.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.uIcc_of_le hH]; exact ⟨hx0, hxH⟩))

/-- A path `f = c₀ + M + A` with `M` continuous and `A` a primitive of an integrable function is continuous. -/
theorem mode417_path_cont (f : ℝ → ℝ) (c0 : ℝ) (g : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hg : IntervalIntegrable g volume 0 H)
    (hc : ContinuousOn (fun t => f t - c0 - ∫ r in (0:ℝ)..t, g r) (Set.Icc 0 H)) :
    ContinuousOn f (Set.Icc 0 H) := by
  have hA : ContinuousOn (fun t => ∫ r in (0:ℝ)..t, g r) (Set.Icc 0 H) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hg Set.left_mem_uIcc
    rw [Set.uIcc_of_le hH] at h
    exact h
  have h2 : ContinuousOn (fun t => (f t - c0 - ∫ r in (0:ℝ)..t, g r) + c0 + ∫ r in (0:ℝ)..t, g r)
      (Set.Icc 0 H) := (hc.add continuousOn_const).add hA
  exact h2.congr (fun t _ => by dsimp only; ring)

/-- Square monotonicity from a bound on the absolute value. -/
theorem mode417_sq_le (x G : ℝ) (hG : 0 ≤ G) (h : |x| ≤ G) : x ^ 2 ≤ G ^ 2 := by
  have h2 := pow_le_pow_left₀ (abs_nonneg x) h 2
  rwa [sq_abs] at h2

/-- Tonelli: a.s. square integrability of `r ↦ f(Φ r ω)` on a finite window, from the one-time bounds. -/
theorem mode417_ii_of_sq {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω)
    [IsProbabilityMeasure P] (Φ : ℝ → Ω → Y) (hΦm : Measurable (fun p : ℝ × Ω => Φ p.1 p.2))
    (f : Y → ℝ) (hf : Measurable f) (H : ℝ) (hH : 0 ≤ H) (κ : ℝ)
    (hκ : ∀ r ∈ Set.Ioc (0:ℝ) H, ∫⁻ ω, ENNReal.ofReal (f (Φ r ω) ^ 2) ∂P ≤ ENNReal.ofReal κ) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun r => f (Φ r ω)) volume 0 H := by
  have hF2 : Measurable (fun p : ℝ × Ω => ENNReal.ofReal (f (Φ p.1 p.2) ^ 2)) :=
    ((hf.comp hΦm).pow_const 2).ennreal_ofReal
  have hF2' : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (f (Φ p.2 p.1) ^ 2)) :=
    hF2.comp measurable_swap
  have hq : Measurable (fun ω => ∫⁻ r in Set.Ioc (0:ℝ) H, ENNReal.ofReal (f (Φ r ω) ^ 2)) :=
    hF2'.lintegral_prod_right'
  have hswap : ∫⁻ ω, (∫⁻ r in Set.Ioc (0:ℝ) H, ENNReal.ofReal (f (Φ r ω) ^ 2)) ∂P =
      ∫⁻ r in Set.Ioc (0:ℝ) H, (∫⁻ ω, ENNReal.ofReal (f (Φ r ω) ^ 2) ∂P) :=
    lintegral_lintegral_swap hF2'.aemeasurable
  have hbound : ∫⁻ r in Set.Ioc (0:ℝ) H, (∫⁻ ω, ENNReal.ofReal (f (Φ r ω) ^ 2) ∂P) ≤
      ENNReal.ofReal κ * ENNReal.ofReal (H - 0) := by
    calc ∫⁻ r in Set.Ioc (0:ℝ) H, (∫⁻ ω, ENNReal.ofReal (f (Φ r ω) ^ 2) ∂P)
        ≤ ∫⁻ r in Set.Ioc (0:ℝ) H, ENNReal.ofReal κ :=
          setLIntegral_mono' measurableSet_Ioc (fun r hr => hκ r hr)
      _ = ENNReal.ofReal κ * ENNReal.ofReal (H - 0) := by
          rw [setLIntegral_const, Real.volume_Ioc]
  have hfin : ∫⁻ ω, (∫⁻ r in Set.Ioc (0:ℝ) H, ENNReal.ofReal (f (Φ r ω) ^ 2)) ∂P ≠ ⊤ := by
    rw [hswap]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hbound
  have hae := ae_lt_top hq hfin
  filter_upwards [hae] with ω hω
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) H)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hmeasω : Measurable (fun r => f (Φ r ω)) :=
    hf.comp (hΦm.comp (measurable_id.prodMk measurable_const))
  have hIO2 : IntegrableOn (fun r => f (Φ r ω) ^ 2) (Set.Ioc 0 H) := by
    refine ⟨((hmeasω.pow_const 2)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun r => sq_nonneg _)).mpr hω
  have hIf : IntegrableOn (fun r => f (Φ r ω)) (Set.Ioc 0 H) := by
    refine Integrable.mono' ((integrable_const (1:ℝ)).add hIO2) hmeasω.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs]
    show |f (Φ r ω)| ≤ 1 + f (Φ r ω) ^ 2
    nlinarith [sq_abs (f (Φ r ω)), abs_nonneg (f (Φ r ω)), sq_nonneg (|f (Φ r ω)| - 1),
      sq_nonneg (f (Φ r ω))]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hH).mpr hIf


/-- One window, pointwise: the integration-by-parts identity together with the five-term bound. -/
theorem mode417_pt (g e f γ γ' : ℝ → ℝ) (f0 b : ℝ) (hb : 0 ≤ b)
    (hg : IntervalIntegrable g volume 0 b) (he : IntervalIntegrable e volume 0 b)
    (hfc : ContinuousOn (fun r => f r - f0 - ∫ u in (0:ℝ)..r, g u) (Set.Icc 0 b))
    (hγ : ∀ x ∈ Set.Icc 0 b, HasDerivWithinAt γ (γ' x) (Set.Icc 0 b) x)
    (hγ' : ContinuousOn γ' (Set.Icc 0 b)) :
    ENNReal.ofReal ((∫ r in (0:ℝ)..b, γ (b - r) * (-g r + e r)) ^ 2) ≤
      ENNReal.ofReal 5 * (ENNReal.ofReal ((γ 0 * f b) ^ 2) + ENNReal.ofReal ((γ b * f0) ^ 2) +
        ENNReal.ofReal ((γ 0 * (f b - f0 - ∫ u in (0:ℝ)..b, g u) +
          ∫ r in (0:ℝ)..b, γ' (b - r) * (f r - f0 - ∫ u in (0:ℝ)..r, g u)) ^ 2) +
        ENNReal.ofReal ((∫ r in (0:ℝ)..b, γ' (max (b - r) 0) * f r) ^ 2) +
        ENNReal.ofReal ((∫ r in (0:ℝ)..b, γ (max (b - r) 0) * e r) ^ 2)) := by
  rw [mode417_ident g e f γ γ' f0 b hb hg he hfc hγ hγ']
  exact mode417_ofReal5 (γ 0 * f b) (γ b * f0)
    (γ 0 * (f b - f0 - ∫ u in (0:ℝ)..b, g u) + ∫ r in (0:ℝ)..b, γ' (b - r) * (f r - f0 - ∫ u in (0:ℝ)..r, g u))
    (∫ r in (0:ℝ)..b, γ' (max (b - r) 0) * f r) (∫ r in (0:ℝ)..b, γ (max (b - r) 0) * e r)


/-- Row 4.17, M-mode window estimate: the statement of `mode_window_bound`, proved from M3, M4b, M4c and the
Lyons-Zheng bound.  The constant is `C = 5 (2 + C₄b + 2 (1/c + T)²)` with `C₄b` the constant of `martingale_window_bound`. -/
theorem mode_window_bound_proof (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
      {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H₀ : ℝ)
      (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H₀ X₀ W X)
      (F G E : Config d N → ℝ) (hFm : Measurable F) (hGm : Measurable G) (hEm : Measurable E)
      (ς Γ : ℝ) (hς : 0 ≤ ς) (hΓ : 0 ≤ Γ)
      (hint : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => G (X r.toNNReal ω)) volume 0 H₀)
      (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => F (X t.toNNReal ω) - F (X 0 ω) -
        ∫ r in (0 : ℝ)..t, G (X r.toNNReal ω)) (Set.Icc 0 H₀))
      (hmax : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H₀ →
        ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
            ((F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω)) ^ 2) ∂P ≤
          ENNReal.ofReal (ς ^ 2 * (t - u)))
      (a : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ H₀)
      (hLZ : ∫⁻ ω, ⨆ t ∈ ratTimes a T, ENNReal.ofReal (F (X t.toNNReal ω) ^ 2) ∂P ≤
        ENNReal.ofReal (ς ^ 2))
      (hF : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (ς ^ 2))
      (hE : ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (ς ^ 2))
      (γ γ' : ℝ → ℝ) (hγ : ∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x)
      (hγ' : ContinuousOn γ' (Set.Ici 0))
      (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)),
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) * (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2) ∂P ≤
        ENNReal.ofReal (C * Γ ^ 2 * ς ^ 2) := by
  obtain ⟨C4b, hC4b0, hM4b⟩ := martingale_window_bound_proof c hc T hT
  have hT2 : 0 ≤ (1 / c + T) ^ 2 := sq_nonneg _
  refine ⟨5 * (2 + C4b + 2 * (1 / c + T) ^ 2), by linarith, ?_⟩
  intro hd s hs0 hsd V hV β hβ N hN Ω _ P _ X₀ W X H₀ hflow F G E hFm hGm hEm ς Γ hς hΓ hint hcont
    hmax a ha haT hLZ hF hE γ γ' hγ hγ' hbd
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hH0 : 0 ≤ H₀ := by linarith
  -- stationarity of the one-time marginals and path regularity
  have hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H₀ → P.map (X t) = canonicalGibbs (periodicRiesz d s) V N β :=
    HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H₀ hN P X₀ W X hflow
  have hpath : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.cont
    · omega
  have hadapt : ∀ t : ℝ≥0, Measurable (X t) := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.adapted
    · omega
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hpath)
  have hcont_bad : ∀ ω, ω ∉ Nn → ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    intro ω hω
    by_contra hne
    exact hω (hNsub hne)
  have hNae : ∀ᵐ ω ∂P, ω ∉ Nn := by
    rw [ae_iff]
    exact measure_mono_null (fun ω hω => not_not.mp hω) hN0
  -- a jointly measurable modification `Xs` of the path, equal to `X` off `Nn`
  obtain ⟨Xs, hXs_good, hXs_meas⟩ : ∃ Xs : ℝ → Ω → Config d N,
      (∀ ω, ω ∉ Nn → ∀ r : ℝ, Xs r ω = X r.toNNReal ω) ∧
        Measurable (fun p : ℝ × Ω => Xs p.1 p.2) := by
    refine ⟨fun r ω => if ω ∈ Nn then X 0 ω else X r.toNNReal ω, fun ω hω r => if_neg hω, ?_⟩
    refine measurable_uncurry_of_continuous_of_measurable (u := fun (r : ℝ) (ω : Ω) =>
      if ω ∈ Nn then X 0 ω else X r.toNNReal ω) (fun ω => ?_) (fun r => ?_)
    · by_cases hω : ω ∈ Nn
      · simp only [if_pos hω]
        exact continuous_const
      · simp only [if_neg hω]
        exact continuous_pi fun i => (hcont_bad ω hω i).comp continuous_real_toNNReal
    · exact Measurable.ite hNm (hadapt 0) (hadapt r.toNNReal)
  have hXs_t : ∀ t : ℝ, Measurable (fun ω => Xs t ω) := fun t =>
    hXs_meas.comp (measurable_const.prodMk measurable_id)
  -- the martingale-type process `M_t = F(X_t) - F(X_0) - ∫_0^t G(X_r)` (on `Xs`, jointly measurable version)
  obtain ⟨Mp, hMp⟩ : ∃ Mp : ℝ → Ω → ℝ, ∀ t ω, Mp t ω =
      F (Xs t ω) - F (Xs 0 ω) - ∫ r in (0:ℝ)..t, G (Xs r ω) := ⟨_, fun _ _ => rfl⟩
  have hMp_meas : ∀ t, Measurable (Mp t) := by
    intro t
    have hfun : Mp t = fun ω => F (Xs t ω) - F (Xs 0 ω) - ∫ r in (0:ℝ)..t, G (Xs r ω) :=
      funext fun ω => hMp t ω
    rw [hfun]
    exact ((hFm.comp (hXs_t t)).sub (hFm.comp (hXs_t 0))).sub
      (mode417_intr_meas (fun p : ℝ × Ω => G (Xs p.1 p.2)) (hGm.comp hXs_meas) t)
  have hMp_zero : ∀ ω, Mp 0 ω = 0 := by
    intro ω
    rw [hMp]
    simp
  have hMp_cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Mp t ω) (Set.Icc 0 H₀) := by
    filter_upwards [hcont, hNae] with ω hωc hωN
    have hfun : (fun t => Mp t ω) = fun t : ℝ => F (X t.toNNReal ω) - F (X 0 ω) -
        ∫ r in (0:ℝ)..t, G (X r.toNNReal ω) := by
      funext t
      rw [hMp]
      simp only [hXs_good ω hωN, Real.toNNReal_zero]
    rw [hfun]
    exact hωc
  have hMpX : ∀ ω, ω ∉ Nn → ∀ r : ℝ, Mp r ω =
      F (X r.toNNReal ω) - F (X 0 ω) - ∫ u in (0:ℝ)..r, G (X u.toNNReal ω) := by
    intro ω hωN r
    rw [hMp]
    simp only [hXs_good ω hωN, Real.toNNReal_zero]
  have hMp_max : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H₀ →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((Mp v ω - Mp u ω) ^ 2) ∂P ≤
        ENNReal.ofReal (ς ^ 2 * (t - u)) := by
    intro u t hu hut htH
    refine le_trans (le_of_eq ?_) (hmax u t hu hut htH)
    apply lintegral_congr_ae
    filter_upwards [hNae, hint] with ω hωN hωi
    apply iSup_congr
    intro v
    apply iSup_congr
    intro hv
    have hv' : v ∈ Set.Icc u (u + (t - u)) := hv.1
    have hu0 : 0 ≤ v := by linarith [hv'.1]
    have hvH : v ≤ H₀ := by linarith [hv'.2]
    have hii_v : IntervalIntegrable (fun r => G (X r.toNNReal ω)) volume 0 v :=
      mode417_ii_sub hωi hu0 hvH hH0
    have hii_u : IntervalIntegrable (fun r => G (X r.toNNReal ω)) volume 0 u :=
      mode417_ii_sub hωi hu (le_trans hut htH) hH0
    have key : Mp v ω - Mp u ω = F (X v.toNNReal ω) - F (X u.toNNReal ω) -
        ∫ r in u..v, G (X r.toNNReal ω) := by
      rw [hMpX ω hωN v, hMpX ω hωN u]
      have h := intervalIntegral.integral_interval_sub_left hii_v hii_u
      linarith
    rw [key]
  -- measurable modification of `Mp` and the M4b bound
  have hM4b' := hM4b P Mp H₀ (ς ^ 2) Γ (sq_nonneg ς) hΓ γ γ' hMp_meas (ae_of_all P hMp_zero)
    hMp_cont hMp_max hγ hγ' hbd a ha haT
  obtain ⟨Mt, hMt_meas, hMt_joint, hMt_eq⟩ := mode417_modify P Mp H₀ hH0 hMp_meas hMp_cont
  -- continuity and bounds of the weights
  have hγcI : ContinuousOn γ (Set.Ici 0) := fun x hx => (hγ x hx).continuousWithinAt
  have hc4c : Continuous (fun v : ℝ => γ' (max v 0)) :=
    hγ'.comp_continuous (continuous_id.max continuous_const)
      (fun x => Set.mem_Ici.mpr (le_max_right _ _))
  have hc5c : Continuous (fun v : ℝ => γ (max v 0)) :=
    hγcI.comp_continuous (continuous_id.max continuous_const)
      (fun x => Set.mem_Ici.mpr (le_max_right _ _))
  have hc4bd : ∀ v, 0 ≤ v → |(fun v : ℝ => γ' (max v 0)) v| ≤ Γ * Real.exp (-c * v) := by
    intro v hv
    show |γ' (max v 0)| ≤ _
    rw [max_eq_left hv]
    exact (hbd v hv).2
  have hc5bd : ∀ v, 0 ≤ v → |(fun v : ℝ => γ (max v 0)) v| ≤ Γ * Real.exp (-c * v) := by
    intro v hv
    show |γ (max v 0)| ≤ _
    rw [max_eq_left hv]
    exact (hbd v hv).1
  have hγle : ∀ v, 0 ≤ v → γ v ^ 2 ≤ Γ ^ 2 := by
    intro v hv
    have hexp : Real.exp (-c * v) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc.le hv])
    have h3 : |γ v| ≤ Γ := (hbd v hv).1.trans (mul_le_of_le_one_right hΓ hexp)
    exact mode417_sq_le (γ v) Γ hΓ h3
  have hγ0 : γ 0 ^ 2 ≤ Γ ^ 2 := hγle 0 le_rfl
  -- the two stationary weighted integrals (M4c)
  have hM4c4 := stationary_weighted_integral_proof hd hs0 hsd V hV β hβ hN P X₀ W X H₀ hflow F hFm
    (fun v : ℝ => γ' (max v 0)) hc4c.measurable c Γ hc hΓ hc4bd a T ha hT haT
  have hM4c5 := stationary_weighted_integral_proof hd hs0 hsd V hV β hβ hN P X₀ W X H₀ hflow E hEm
    (fun v : ℝ => γ (max v 0)) hc5c.measurable c Γ hc hΓ hc5bd a T ha hT haT
  -- the process `E(X_·)` is a.s. integrable on `[0, H₀]`
  have hEint : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => E (X r.toNNReal ω)) volume 0 H₀ := by
    have hEs := mode417_ii_of_sq P Xs hXs_meas E hEm H₀ hH0 (ς ^ 2)
      (fun r hr => by
        have h1 := mode417_onetime P (canonicalGibbs (periodicRiesz d s) V N β) X hadapt H₀ hstat
          E hEm (ς ^ 2) hE r hr.1.le hr.2
        refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h1
        filter_upwards [hNae] with ω hωN
        rw [hXs_good ω hωN r])
    filter_upwards [hEs, hNae] with ω hω hωN
    have hfun : (fun r : ℝ => E (X r.toNNReal ω)) = fun r => E (Xs r ω) :=
      funext fun r => by rw [hXs_good ω hωN r]
    rw [hfun]
    exact hω
  -- the five suprema
  obtain ⟨m1, hm1⟩ : ∃ m : Ω → ℝ≥0∞, ∀ ω, m ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ((γ 0 * F (X (a + t).toNNReal ω)) ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m : Ω → ℝ≥0∞, ∀ ω, m ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ((γ (a + t) * F (X 0 ω)) ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m : Ω → ℝ≥0∞, ∀ ω, m ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ((γ 0 * Mt (a + t) ω +
        ∫ r in (0:ℝ)..(a + t), γ' (max (a + t - r) 0) * Mt r ω) ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨m4, hm4⟩ : ∃ m : Ω → ℝ≥0∞, ∀ ω, m ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t), γ' (max (a + t - r) 0) * F (Xs r ω)) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨m5, hm5⟩ : ∃ m : Ω → ℝ≥0∞, ∀ ω, m ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t), γ (max (a + t - r) 0) * E (Xs r ω)) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hm1_meas : Measurable m1 := by
    have hfun : m1 = fun ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((γ 0 * F (X (a + t).toNNReal ω)) ^ 2) :=
      funext hm1
    rw [hfun]
    exact est4_meas_sup _ (est4_ratTimes_countable 0 T)
      (fun t ω => ENNReal.ofReal ((γ 0 * F (X (a + t).toNNReal ω)) ^ 2))
      (fun t => ((((hFm.comp (hadapt _)).const_mul (γ 0)).pow_const 2)).ennreal_ofReal)
  have hm2_meas : Measurable m2 := by
    have hfun : m2 = fun ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((γ (a + t) * F (X 0 ω)) ^ 2) :=
      funext hm2
    rw [hfun]
    exact est4_meas_sup _ (est4_ratTimes_countable 0 T)
      (fun t ω => ENNReal.ofReal ((γ (a + t) * F (X 0 ω)) ^ 2))
      (fun t => (((hFm.comp (hadapt 0)).const_mul (γ (a + t))).pow_const 2).ennreal_ofReal)
  have hm3_meas : Measurable m3 := by
    have hfun : m3 = fun ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((γ 0 * Mt (a + t) ω +
        ∫ r in (0:ℝ)..(a + t), γ' (max (a + t - r) 0) * Mt r ω) ^ 2) := funext hm3
    rw [hfun]
    refine est4_meas_sup _ (est4_ratTimes_countable 0 T)
      (fun t ω => ENNReal.ofReal ((γ 0 * Mt (a + t) ω +
        ∫ r in (0:ℝ)..(a + t), γ' (max (a + t - r) 0) * Mt r ω) ^ 2)) (fun t => ?_)
    have hh : Measurable (fun p : ℝ × Ω => γ' (max (a + t - p.1) 0) * Mt p.1 p.2) :=
      (hc4c.measurable.comp (measurable_const.sub measurable_fst : Measurable fun p : ℝ × Ω => a + t - p.1)).mul hMt_joint
    exact ((((hMt_meas (a + t)).const_mul (γ 0)).add (mode417_intr_meas _ hh (a + t))).pow_const 2).ennreal_ofReal
  have hm4_meas : Measurable m4 := by
    have hfun : m4 = fun ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ' (max (a + t - r) 0) * F (Xs r ω)) ^ 2) := funext hm4
    rw [hfun]
    refine est4_meas_sup _ (est4_ratTimes_countable 0 T)
      (fun t ω => ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ' (max (a + t - r) 0) * F (Xs r ω)) ^ 2)) (fun t => ?_)
    have hh : Measurable (fun p : ℝ × Ω => γ' (max (a + t - p.1) 0) * F (Xs p.1 p.2)) :=
      (hc4c.measurable.comp (measurable_const.sub measurable_fst : Measurable fun p : ℝ × Ω => a + t - p.1)).mul (hFm.comp hXs_meas)
    exact ((mode417_intr_meas _ hh (a + t)).pow_const 2).ennreal_ofReal
  have hm5_meas : Measurable m5 := by
    have hfun : m5 = fun ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ (max (a + t - r) 0) * E (Xs r ω)) ^ 2) := funext hm5
    rw [hfun]
    refine est4_meas_sup _ (est4_ratTimes_countable 0 T)
      (fun t ω => ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ (max (a + t - r) 0) * E (Xs r ω)) ^ 2)) (fun t => ?_)
    have hh : Measurable (fun p : ℝ × Ω => γ (max (a + t - p.1) 0) * E (Xs p.1 p.2)) :=
      (hc5c.measurable.comp (measurable_const.sub measurable_fst : Measurable fun p : ℝ × Ω => a + t - p.1)).mul (hEm.comp hXs_meas)
    exact ((mode417_intr_meas _ hh (a + t)).pow_const 2).ennreal_ofReal
  -- a.e. identifications of the suprema
  have hm3eq : ∀ᵐ ω ∂P, m3 ω = ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((γ 0 * Mp (a + t) ω +
      ∫ r in (0:ℝ)..(a + t), γ' (a + t - r) * Mp r ω) ^ 2) := by
    filter_upwards [hMt_eq] with ω hωMt
    rw [hm3 ω]
    apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    have hb0 : 0 ≤ a + t := by linarith [ht.1.1]
    have hbH : a + t ≤ H₀ := by linarith [ht.1.2]
    have hx : γ 0 * Mt (a + t) ω + ∫ r in (0:ℝ)..(a + t), γ' (max (a + t - r) 0) * Mt r ω =
        γ 0 * Mp (a + t) ω + ∫ r in (0:ℝ)..(a + t), γ' (a + t - r) * Mp r ω := by
      rw [hωMt (a + t) ⟨hb0, hbH⟩]
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le hb0] at hr
      show γ' (max (a + t - r) 0) * Mt r ω = γ' (a + t - r) * Mp r ω
      rw [hωMt r ⟨hr.1, by linarith [hr.2]⟩, max_eq_left (by linarith [hr.2])]
    rw [hx]
  have hm4X : ∀ᵐ ω ∂P, m4 ω = ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
      γ' (max (a + t - r) 0) * F (X r.toNNReal ω)) ^ 2) := by
    filter_upwards [hNae] with ω hωN
    rw [hm4 ω]
    simp only [hXs_good ω hωN]
  have hm5X : ∀ᵐ ω ∂P, m5 ω = ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
      γ (max (a + t - r) 0) * E (X r.toNNReal ω)) ^ 2) := by
    filter_upwards [hNae] with ω hωN
    rw [hm5 ω]
    simp only [hXs_good ω hωN]
  -- pointwise bound (sum of five squares)
  have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
      γ (a + t - r) * (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2)) ≤
      ENNReal.ofReal 5 * (m1 ω + m2 ω + m3 ω + m4 ω + m5 ω) := by
    filter_upwards [hint, hcont, hEint, hNae, hm3eq, hm4X, hm5X] with
      ω hωi hωc hωE hωN hωm3 hωm4 hωm5
    have hωm3X : m3 ω = ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((γ 0 * (F (X (a + t).toNNReal ω) - F (X 0 ω) -
        ∫ u in (0:ℝ)..(a + t), G (X u.toNNReal ω)) + ∫ r in (0:ℝ)..(a + t),
        γ' (a + t - r) * (F (X r.toNNReal ω) - F (X 0 ω) - ∫ u in (0:ℝ)..r, G (X u.toNNReal ω))) ^ 2) := by
      rw [hωm3]
      simp only [hMpX ω hωN]
    have hsup := mode417_sup5 (ratTimes 0 T) (ENNReal.ofReal 5)
      (fun t => ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ (a + t - r) * (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2))
      (fun t => ENNReal.ofReal ((γ 0 * F (X (a + t).toNNReal ω)) ^ 2))
      (fun t => ENNReal.ofReal ((γ (a + t) * F (X 0 ω)) ^ 2))
      (fun t => ENNReal.ofReal ((γ 0 * (F (X (a + t).toNNReal ω) - F (X 0 ω) -
        ∫ u in (0:ℝ)..(a + t), G (X u.toNNReal ω)) + ∫ r in (0:ℝ)..(a + t),
        γ' (a + t - r) * (F (X r.toNNReal ω) - F (X 0 ω) - ∫ u in (0:ℝ)..r, G (X u.toNNReal ω))) ^ 2))
      (fun t => ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ' (max (a + t - r) 0) * F (X r.toNNReal ω)) ^ 2))
      (fun t => ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ (max (a + t - r) 0) * E (X r.toNNReal ω)) ^ 2))
      (fun t ht => by
        have hb0 : 0 ≤ a + t := by linarith [ht.1.1]
        have hbH : a + t ≤ H₀ := by linarith [ht.1.2]
        exact mode417_pt (fun r => G (X r.toNNReal ω)) (fun r => E (X r.toNNReal ω))
          (fun r => F (X r.toNNReal ω)) γ γ' (F (X 0 ω)) (a + t) hb0
          (mode417_ii_sub hωi hb0 hbH hH0) (mode417_ii_sub hωE hb0 hbH hH0)
          (hωc.mono (Set.Icc_subset_Icc le_rfl hbH))
          (fun x hx => (hγ x hx.1).mono Set.Icc_subset_Ici_self)
          (hγ'.mono Set.Icc_subset_Ici_self))
    refine hsup.trans (le_of_eq ?_)
    rw [hm1 ω, hm2 ω, hωm3X, hωm4, hωm5]
  -- integrate
  have hsplit : ∫⁻ ω, ENNReal.ofReal 5 * (m1 ω + m2 ω + m3 ω + m4 ω + m5 ω) ∂P =
      ENNReal.ofReal 5 * (∫⁻ ω, m1 ω ∂P + ∫⁻ ω, m2 ω ∂P + ∫⁻ ω, m3 ω ∂P + ∫⁻ ω, m4 ω ∂P +
        ∫⁻ ω, m5 ω ∂P) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ hm5_meas,
      lintegral_add_right _ hm4_meas, lintegral_add_right _ hm3_meas, lintegral_add_right _ hm2_meas]
  have hbound : ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (ς ^ 2) = ENNReal.ofReal (Γ ^ 2 * ς ^ 2) :=
    (ENNReal.ofReal_mul (sq_nonneg Γ)).symm
  -- the first term (Lyons-Zheng, with the density of rational times, or one-time bound when T = 0)
  have hb1 : ∫⁻ ω, m1 ω ∂P ≤ ENNReal.ofReal (Γ ^ 2 * ς ^ 2) := by
    rw [← hbound]
    rcases eq_or_lt_of_le hT with hT0 | hTpos
    · have hone : ∫⁻ ω, ENNReal.ofReal (F (X a.toNNReal ω) ^ 2) ∂P ≤ ENNReal.ofReal (ς ^ 2) :=
        mode417_onetime P (canonicalGibbs (periodicRiesz d s) V N β) X hadapt H₀ hstat F hFm (ς ^ 2) hF
          a ha (by linarith)
      have hpt1 : ∀ ω, m1 ω ≤ ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (F (X a.toNNReal ω) ^ 2) := by
        intro ω
        rw [hm1 ω]
        refine iSup₂_le (fun t ht => ?_)
        have ht0 : t = 0 := le_antisymm (by linarith [ht.1.2, hT0]) ht.1.1
        subst ht0
        rw [add_zero, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hγ0) le_rfl
      calc ∫⁻ ω, m1 ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (F (X a.toNNReal ω) ^ 2) ∂P :=
            lintegral_mono hpt1
        _ = ENNReal.ofReal (Γ ^ 2) * ∫⁻ ω, ENNReal.ofReal (F (X a.toNNReal ω) ^ 2) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (ς ^ 2) := mul_le_mul' le_rfl hone
    · have hpt1 : ∀ᵐ ω ∂P, m1 ω ≤ ENNReal.ofReal (Γ ^ 2) *
          ⨆ s ∈ ratTimes a T, ENNReal.ofReal (F (X s.toNNReal ω) ^ 2) := by
        filter_upwards [hcont, hint] with ω hωc hωi
        rw [hm1 ω]
        have hgc : ContinuousOn (fun u : ℝ => F (X u.toNNReal ω)) (Set.Icc a (a + T)) :=
          (mode417_path_cont (fun u => F (X u.toNNReal ω)) (F (X 0 ω)) (fun r => G (X r.toNNReal ω))
            H₀ hH0 hωi hωc).mono (Set.Icc_subset_Icc ha haT)
        refine iSup₂_le (fun t ht => ?_)
        have hta : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1.1, by linarith [ht.1.2]⟩
        have hx : a + t ∈ Set.Icc a (a + T) := ⟨by linarith [hta.1], by linarith [hta.2]⟩
        calc ENNReal.ofReal ((γ 0 * F (X (a + t).toNNReal ω)) ^ 2)
            = ENNReal.ofReal (γ 0 ^ 2) * ENNReal.ofReal (F (X (a + t).toNNReal ω) ^ 2) := by
              rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
          _ ≤ ENNReal.ofReal (Γ ^ 2) * ⨆ s ∈ ratTimes a T, ENNReal.ofReal (F (X s.toNNReal ω) ^ 2) :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hγ0)
                (mode417_le_sup (fun u => F (X u.toNNReal ω)) a T hTpos hgc (a + t) hx)
      calc ∫⁻ ω, m1 ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal (Γ ^ 2) *
            ⨆ s ∈ ratTimes a T, ENNReal.ofReal (F (X s.toNNReal ω) ^ 2) ∂P := lintegral_mono_ae hpt1
        _ = ENNReal.ofReal (Γ ^ 2) * ∫⁻ ω, ⨆ s ∈ ratTimes a T, ENNReal.ofReal (F (X s.toNNReal ω) ^ 2) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (ς ^ 2) := mul_le_mul' le_rfl hLZ
  -- the second term (γ(b) F(X_0))
  have hone0 : ∫⁻ ω, ENNReal.ofReal (F (X 0 ω) ^ 2) ∂P ≤ ENNReal.ofReal (ς ^ 2) := by
    have h := mode417_onetime P (canonicalGibbs (periodicRiesz d s) V N β) X hadapt H₀ hstat F hFm
      (ς ^ 2) hF 0 le_rfl hH0
    rwa [Real.toNNReal_zero] at h
  have hb2 : ∫⁻ ω, m2 ω ∂P ≤ ENNReal.ofReal (Γ ^ 2 * ς ^ 2) := by
    rw [← hbound]
    calc ∫⁻ ω, m2 ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (F (X 0 ω) ^ 2) ∂P := by
          apply lintegral_mono
          intro ω
          rw [hm2 ω]
          refine iSup₂_le (fun t ht => ?_)
          rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hγle (a + t) (by linarith [ht.1.1]))) le_rfl
      _ = ENNReal.ofReal (Γ ^ 2) * ∫⁻ ω, ENNReal.ofReal (F (X 0 ω) ^ 2) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Γ ^ 2) * ENNReal.ofReal (ς ^ 2) := mul_le_mul' le_rfl hone0
  -- the martingale term (M4b)
  have hb3 : ∫⁻ ω, m3 ω ∂P ≤ ENNReal.ofReal (C4b * Γ ^ 2 * ς ^ 2) := by
    calc ∫⁻ ω, m3 ω ∂P = ∫⁻ ω, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((γ 0 * Mp (a + t) ω +
          ∫ r in (0:ℝ)..(a + t), γ' (a + t - r) * Mp r ω) ^ 2)) ∂P := lintegral_congr_ae hm3eq
      _ ≤ ENNReal.ofReal (C4b * Γ ^ 2 * ς ^ 2) := hM4b'
  -- the two weighted stationary integrals (M4c)
  have hb4 : ∫⁻ ω, m4 ω ∂P ≤ ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) := by
    calc ∫⁻ ω, m4 ω ∂P = ∫⁻ ω, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
          γ' (max (a + t - r) 0) * F (X r.toNNReal ω)) ^ 2)) ∂P := lintegral_congr_ae hm4X
      _ ≤ ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2) *
          ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) := hM4c4
      _ ≤ ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2) * ENNReal.ofReal (ς ^ 2) := mul_le_mul' le_rfl hF
      _ = ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hb5 : ∫⁻ ω, m5 ω ∂P ≤ ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) := by
    calc ∫⁻ ω, m5 ω ∂P = ∫⁻ ω, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
          γ (max (a + t - r) 0) * E (X r.toNNReal ω)) ^ 2)) ∂P := lintegral_congr_ae hm5X
      _ ≤ ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2) *
          ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) := hM4c5
      _ ≤ ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2) * ENNReal.ofReal (ς ^ 2) := mul_le_mul' le_rfl hE
      _ = ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  -- assembly
  have hR1 : 0 ≤ Γ ^ 2 * ς ^ 2 := by positivity
  have hR3 : 0 ≤ C4b * Γ ^ 2 * ς ^ 2 := mul_nonneg (mul_nonneg hC4b0 (sq_nonneg Γ)) (sq_nonneg ς)
  have hR4 : 0 ≤ Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2 := by positivity
  have hS2 : 0 ≤ Γ ^ 2 * ς ^ 2 + Γ ^ 2 * ς ^ 2 := by linarith
  have hS3 : 0 ≤ Γ ^ 2 * ς ^ 2 + Γ ^ 2 * ς ^ 2 + C4b * Γ ^ 2 * ς ^ 2 := by linarith
  have hS4 : 0 ≤ Γ ^ 2 * ς ^ 2 + Γ ^ 2 * ς ^ 2 + C4b * Γ ^ 2 * ς ^ 2 + Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2 := by
    linarith
  have hsum2 : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
      ENNReal.ofReal p + ENNReal.ofReal q = ENNReal.ofReal (p + q) :=
    fun p q hp hq => (ENNReal.ofReal_add hp hq).symm
  have hsum_eq : ENNReal.ofReal (Γ ^ 2 * ς ^ 2) + ENNReal.ofReal (Γ ^ 2 * ς ^ 2) +
      ENNReal.ofReal (C4b * Γ ^ 2 * ς ^ 2) + ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) +
      ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) =
      ENNReal.ofReal (Γ ^ 2 * ς ^ 2 + Γ ^ 2 * ς ^ 2 + C4b * Γ ^ 2 * ς ^ 2 +
        Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2 + Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) := by
    rw [hsum2 _ _ hR1 hR1, hsum2 _ _ hS2 hR3, hsum2 _ _ hS3 hR4, hsum2 _ _ hS4 hR4]
  calc ∫⁻ ω, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0:ℝ)..(a + t),
        γ (a + t - r) * (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal 5 * (m1 ω + m2 ω + m3 ω + m4 ω + m5 ω) ∂P := lintegral_mono_ae hpt
    _ = ENNReal.ofReal 5 * (∫⁻ ω, m1 ω ∂P + ∫⁻ ω, m2 ω ∂P + ∫⁻ ω, m3 ω ∂P + ∫⁻ ω, m4 ω ∂P +
        ∫⁻ ω, m5 ω ∂P) := hsplit
    _ ≤ ENNReal.ofReal 5 * (ENNReal.ofReal (Γ ^ 2 * ς ^ 2) + ENNReal.ofReal (Γ ^ 2 * ς ^ 2) +
        ENNReal.ofReal (C4b * Γ ^ 2 * ς ^ 2) + ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) +
        ENNReal.ofReal (Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2)) :=
        mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4) hb5)
    _ = ENNReal.ofReal 5 * ENNReal.ofReal (Γ ^ 2 * ς ^ 2 + Γ ^ 2 * ς ^ 2 + C4b * Γ ^ 2 * ς ^ 2 +
        Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2 + Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2) := by
        rw [hsum_eq]
    _ = ENNReal.ofReal (5 * (Γ ^ 2 * ς ^ 2 + Γ ^ 2 * ς ^ 2 + C4b * Γ ^ 2 * ς ^ 2 +
        Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2 + Γ ^ 2 * (1 / c + T) ^ 2 * ς ^ 2)) :=
        (ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)).symm
    _ ≤ ENNReal.ofReal (5 * (2 + C4b + 2 * (1 / c + T) ^ 2) * Γ ^ 2 * ς ^ 2) :=
        ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end HRS.ME

end
