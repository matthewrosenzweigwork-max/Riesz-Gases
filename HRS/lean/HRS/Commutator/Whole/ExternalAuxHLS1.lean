import Mathlib

/-!
# Hardy–Littlewood maximal theorem on `ℝ^d` (packet X-HLS, part 1)

The dyadic centred maximal function `cmxHLS_Md f (x) = sup_{j ∈ ℤ} ⨍_{B̄(x,2^j)} f`, its weak `(1,1)`
bound (Vitali covering, `Mathlib.MeasureTheory.Covering.Vitali`) and the strong `(p,p)` bound for
`1 < p < ∞` (layer cake).
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The dyadic centred maximal function. -/
def cmxHLS_Md (f : 𝔼 → ℝ≥0∞) (x : 𝔼) : ℝ≥0∞ :=
  ⨆ j : ℤ, (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y

lemma cmxHLS_vol_closedBall (x : 𝔼) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal (r ^ d) * volume (closedBall (0 : 𝔼) 1) := by
  rw [Measure.addHaar_closedBall' volume x hr, finrank_euclideanSpace_fin]

lemma cmxHLS_vol_closedBall_ne_zero (x : 𝔼) {r : ℝ} (hr : 0 < r) : volume (closedBall x r) ≠ 0 :=
  (measure_closedBall_pos volume x hr).ne'

lemma cmxHLS_vol_closedBall_ne_top (x : 𝔼) (r : ℝ) : volume (closedBall x r) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

lemma cmxHLS_vol_closedBall_mul4 (x : 𝔼) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x (4 * r)) = 4 ^ d * volume (closedBall x r) := by
  rw [cmxHLS_vol_closedBall x hr, cmxHLS_vol_closedBall x (by positivity), ← mul_assoc,
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

lemma cmxHLS_lintegral_le (f : 𝔼 → ℝ≥0∞) (x : 𝔼) (j : ℤ) :
    ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y ≤
      volume (closedBall x ((2 : ℝ) ^ j)) * cmxHLS_Md f x := by
  have h0 := cmxHLS_vol_closedBall_ne_zero x (zpow_pos (by norm_num : (0 : ℝ) < 2) j)
  have h1 := cmxHLS_vol_closedBall_ne_top x ((2 : ℝ) ^ j)
  rw [← ENNReal.inv_mul_le_iff h0 h1]
  exact le_iSup (fun j : ℤ => (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ *
    ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y) j

lemma cmxHLS_Md_measurable {f : 𝔼 → ℝ≥0∞} (hf : Measurable f) : Measurable (cmxHLS_Md f) := by
  unfold cmxHLS_Md
  refine Measurable.iSup fun j => ?_
  set r : ℝ := (2 : ℝ) ^ j with hr
  have hr0 : 0 ≤ r := (zpow_pos (by norm_num : (0 : ℝ) < 2) j).le
  have hint : Measurable fun x : 𝔼 => ∫⁻ y in closedBall x r, f y := by
    have hs : MeasurableSet {p : 𝔼 × 𝔼 | p.2 ∈ closedBall p.1 r} := by
      have : {p : 𝔼 × 𝔼 | p.2 ∈ closedBall p.1 r} = {p : 𝔼 × 𝔼 | dist p.2 p.1 ≤ r} := rfl
      rw [this]
      exact measurableSet_le (by fun_prop) measurable_const
    have hm : Measurable fun p : 𝔼 × 𝔼 =>
        {p : 𝔼 × 𝔼 | p.2 ∈ closedBall p.1 r}.indicator (fun p => f p.2) p :=
      (hf.comp measurable_snd).indicator hs
    have key : ∀ x : 𝔼, ∫⁻ y in closedBall x r, f y =
        ∫⁻ y, {p : 𝔼 × 𝔼 | p.2 ∈ closedBall p.1 r}.indicator (fun p => f p.2) (x, y) := by
      intro x
      rw [← lintegral_indicator measurableSet_closedBall]
      congr 1
    simp_rw [key]
    exact Measurable.lintegral_prod_right' hm
  have hv : ∀ x : 𝔼, volume (closedBall x r) = volume (closedBall (0 : 𝔼) r) := fun x => by
    rw [cmxHLS_vol_closedBall x hr0, cmxHLS_vol_closedBall 0 hr0]
  simp_rw [hv]
  exact hint.const_mul _


/-- Weak type `(1,1)`: `l · |{M f > l}| ≤ 4^d ∫ f` (Vitali, `τ = 4`). -/
lemma cmxHLS_weak (hd : 1 ≤ d) {f : 𝔼 → ℝ≥0∞} (hf : Measurable f) {l : ℝ≥0∞} (hl0 : l ≠ 0) :
    l * volume {x | l < cmxHLS_Md f x} ≤ 4 ^ d * ∫⁻ y, f y := by
  by_cases hF : ∫⁻ y, f y = ⊤
  · rw [hF, ENNReal.mul_top (by positivity)]; exact le_top
  by_cases hlt : l = ⊤
  · subst hlt
    have : {x | (⊤ : ℝ≥0∞) < cmxHLS_Md f x} = ∅ := by
      ext x; simp
    rw [this]; simp
  set S : Set 𝔼 := {x | l < cmxHLS_Md f x} with hS
  set ω : ℝ≥0∞ := volume (closedBall (0 : 𝔼) 1) with hω
  have hω0 : ω ≠ 0 := cmxHLS_vol_closedBall_ne_zero 0 one_pos
  have hωt : ω ≠ ⊤ := cmxHLS_vol_closedBall_ne_top 0 1
  have hex : ∀ x ∈ S, ∃ j : ℤ, l * volume (closedBall x ((2 : ℝ) ^ j)) <
      ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y := by
    intro x hx
    have hx' : l < cmxHLS_Md f x := hx
    unfold cmxHLS_Md at hx'
    obtain ⟨j, hj⟩ := lt_iSup_iff.1 hx'
    refine ⟨j, ?_⟩
    by_contra h
    have h := not_lt.1 h
    have h0 := cmxHLS_vol_closedBall_ne_zero x (zpow_pos (by norm_num : (0 : ℝ) < 2) j)
    have h1 := cmxHLS_vol_closedBall_ne_top x ((2 : ℝ) ^ j)
    have : (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y ≤ l :=
      (ENNReal.inv_mul_le_iff h0 h1).2 (by rw [mul_comm]; exact h)
    exact absurd hj (not_lt.2 this)
  choose! J hJ using hex
  set r : 𝔼 → ℝ := fun x => (2 : ℝ) ^ (J x) with hr
  have hrpos : ∀ x, 0 < r x := fun x => zpow_pos (by norm_num : (0 : ℝ) < 2) _
  set N : ℝ≥0∞ := (∫⁻ y, f y) / (l * ω) with hN
  have hlω0 : l * ω ≠ 0 := mul_ne_zero hl0 hω0
  have hlωt : l * ω ≠ ⊤ := ENNReal.mul_ne_top hlt hωt
  have hNt : N ≠ ⊤ := by
    rw [hN]; exact ENNReal.div_ne_top hF hlω0
  have hbound : ∀ x ∈ S, r x ≤ max 1 N.toReal := by
    intro x hx
    have h := hJ x hx
    have hle : ∫⁻ y in closedBall x (r x), f y ≤ ∫⁻ y, f y := setLIntegral_le_lintegral _ _
    have h2 : l * volume (closedBall x (r x)) < ∫⁻ y, f y := lt_of_lt_of_le h hle
    rw [cmxHLS_vol_closedBall x (hrpos x).le] at h2
    have h3 : ENNReal.ofReal (r x ^ d) < N := by
      rw [hN, ENNReal.lt_div_iff_mul_lt (Or.inl hlω0) (Or.inl hlωt)]
      calc ENNReal.ofReal (r x ^ d) * (l * ω) = l * (ENNReal.ofReal (r x ^ d) * ω) := by ring
        _ < _ := h2
    have h4 : r x ^ d < N.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hNt).1 h3
    by_cases h1 : r x ≤ 1
    · exact le_max_of_le_left h1
    · have h1 := not_le.1 h1
      refine le_max_of_le_right ?_
      calc r x ≤ r x ^ d := le_self_pow₀ h1.le (by omega)
        _ ≤ N.toReal := h4.le
  obtain ⟨u, huS, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    S id r (max 1 N.toReal) (fun a ha => hbound a ha) 4 (by norm_num)
  simp only [id] at hdisj hcov
  have hcount : u.Countable := by
    refine hdisj.countable_of_nonempty_interior (fun b hb => ?_)
    rw [interior_closedBall b (hrpos b).ne']
    exact nonempty_ball.2 (hrpos b)
  have hsub : S ⊆ ⋃ b ∈ u, closedBall b (4 * r b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    simp only [mem_iUnion]
    exact ⟨b, hb, hab (mem_closedBall_self (hrpos a).le)⟩
  have h1 : volume S ≤ ∑' b : u, 4 ^ d * volume (closedBall (b : 𝔼) (r b)) := by
    calc volume S ≤ volume (⋃ b ∈ u, closedBall b (4 * r b)) := measure_mono hsub
      _ ≤ ∑' b : u, volume (closedBall (b : 𝔼) (4 * r b)) := measure_biUnion_le _ hcount _
      _ = _ := by
        congr 1; ext b
        exact cmxHLS_vol_closedBall_mul4 _ (hrpos b).le
  calc l * volume S ≤ l * ∑' b : u, 4 ^ d * volume (closedBall (b : 𝔼) (r b)) :=
        mul_le_mul_right h1 _
    _ = 4 ^ d * ∑' b : u, l * volume (closedBall (b : 𝔼) (r b)) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1; ext b; ring
    _ ≤ 4 ^ d * ∑' b : u, ∫⁻ y in closedBall (b : 𝔼) (r b), f y := by
        gcongr with b
        exact (hJ b (huS b.2)).le
    _ = 4 ^ d * ∫⁻ y in ⋃ b ∈ u, closedBall b (r b), f y := by
        rw [lintegral_biUnion hcount (fun b _ => measurableSet_closedBall) hdisj]
    _ ≤ 4 ^ d * ∫⁻ y, f y := by
        exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _


lemma cmxHLS_Md_le_add {f g : 𝔼 → ℝ≥0∞} (hg : Measurable g) (c : ℝ≥0∞)
    (h : ∀ y, f y ≤ g y + c) (x : 𝔼) : cmxHLS_Md f x ≤ cmxHLS_Md g x + c := by
  unfold cmxHLS_Md
  refine iSup_le fun j => ?_
  have h0 := cmxHLS_vol_closedBall_ne_zero x (zpow_pos (by norm_num : (0 : ℝ) < 2) j)
  have h1 := cmxHLS_vol_closedBall_ne_top x ((2 : ℝ) ^ j)
  set B : Set 𝔼 := closedBall x ((2 : ℝ) ^ j) with hB
  have hstep : ∫⁻ y in B, f y ≤ (∫⁻ y in B, g y) + c * volume B := by
    calc ∫⁻ y in B, f y ≤ ∫⁻ y in B, (g y + c) := lintegral_mono h
      _ = (∫⁻ y in B, g y) + c * volume B := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  calc (volume B)⁻¹ * ∫⁻ y in B, f y ≤ (volume B)⁻¹ * ((∫⁻ y in B, g y) + c * volume B) :=
        mul_le_mul_right hstep _
    _ = (volume B)⁻¹ * (∫⁻ y in B, g y) + c := by
        rw [mul_add, mul_comm c (volume B), ← mul_assoc, ENNReal.inv_mul_cancel h0 h1, one_mul]
    _ ≤ _ := by
        refine add_le_add_left ?_ c
        exact le_iSup (fun j : ℤ => (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ *
          ∫⁻ y in closedBall x ((2 : ℝ) ^ j), g y) j

/-- The part of `f` above height `t/2`. -/
def cmxHLS_ft (f : 𝔼 → ℝ≥0) (t : ℝ) (y : 𝔼) : ℝ≥0∞ :=
  if t / 2 < (f y : ℝ) then (f y : ℝ≥0∞) else 0

lemma cmxHLS_ft_measurable {f : 𝔼 → ℝ≥0} (hf : Measurable f) (t : ℝ) :
    Measurable (cmxHLS_ft f t) := by
  unfold cmxHLS_ft
  refine Measurable.ite ?_ (hf.coe_nnreal_ennreal) measurable_const
  exact measurableSet_lt measurable_const (by fun_prop)

lemma cmxHLS_ft_le (f : 𝔼 → ℝ≥0) (t : ℝ) (y : 𝔼) :
    (f y : ℝ≥0∞) ≤ cmxHLS_ft f t y + ENNReal.ofReal (t / 2) := by
  unfold cmxHLS_ft
  split_ifs with h
  · exact le_self_add
  · have := not_lt.1 h
    rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal this

lemma cmxHLS_weak_t (hd : 1 ≤ d) {f : 𝔼 → ℝ≥0} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < cmxHLS_Md (fun y => (f y : ℝ≥0∞)) x} ≤
      2 * 4 ^ d * ∫⁻ y, cmxHLS_ft f t y := by
  set l : ℝ≥0∞ := ENNReal.ofReal (t / 2) with hl
  have hl0 : l ≠ 0 := by simp [hl, ht]
  have hlt : l ≠ ⊤ := ENNReal.ofReal_ne_top
  have hll : ENNReal.ofReal t = l + l := by
    rw [hl, ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hsub : {x | ENNReal.ofReal t < cmxHLS_Md (fun y => (f y : ℝ≥0∞)) x} ⊆
      {x | l < cmxHLS_Md (cmxHLS_ft f t) x} := by
    intro x hx
    have h1 : ENNReal.ofReal t < cmxHLS_Md (cmxHLS_ft f t) x + l :=
      lt_of_lt_of_le hx (cmxHLS_Md_le_add (cmxHLS_ft_measurable hf t) l (cmxHLS_ft_le f t) x)
    rw [hll] at h1
    exact (ENNReal.add_lt_add_iff_right hlt).1 h1
  have hw := cmxHLS_weak hd (cmxHLS_ft_measurable hf t) hl0
  refine (mul_le_mul_right (measure_mono (μ := volume) hsub) _).trans ?_
  rw [hll]
  calc (l + l) * volume {x | l < cmxHLS_Md (cmxHLS_ft f t) x}
      = 2 * (l * volume {x | l < cmxHLS_Md (cmxHLS_ft f t) x}) := by ring
    _ ≤ 2 * (4 ^ d * ∫⁻ y, cmxHLS_ft f t y) := by gcongr
    _ = 2 * 4 ^ d * ∫⁻ y, cmxHLS_ft f t y := by ring


lemma cmxHLS_int_rpow {b q : ℝ} (hb : 0 ≤ b) (hq : -1 < q) :
    ∫⁻ t in Ioo 0 b, ENNReal.ofReal (t ^ q) = ENNReal.ofReal (b ^ (q + 1) / (q + 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ q) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' hq
  rcases hb.eq_or_lt with h0 | hpos
  · subst h0
    simp [Real.zero_rpow (by linarith : q + 1 ≠ 0)]
  · rw [setLIntegral_congr Ioo_ae_eq_Ioc]
    have hI : IntegrableOn (fun t : ℝ => t ^ q) (Ioc 0 b) := 
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 hint
    rw [← ofReal_integral_eq_lintegral_ofReal hI]
    · rw [← intervalIntegral.integral_of_le hb, integral_rpow (Or.inl hq)]
      simp [Real.zero_rpow (by linarith : q + 1 ≠ 0)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le q

lemma cmxHLS_inner {p : ℝ} (hp : 1 < p) (a : ℝ≥0) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        (if t / 2 < (a : ℝ) then (a : ℝ≥0∞) else 0) =
      ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * (a : ℝ≥0∞) ^ p := by
  have h1 : ∀ t : ℝ, ENNReal.ofReal (t ^ (p - 2)) * (if t / 2 < (a : ℝ) then (a : ℝ≥0∞) else 0) =
      (Iio (2 * (a : ℝ))).indicator (fun t => (a : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 2))) t := by
    intro t
    by_cases h : t / 2 < (a : ℝ)
    · have : t < 2 * (a : ℝ) := by linarith
      rw [Set.indicator_of_mem (show t ∈ Iio (2 * (a : ℝ)) from this), mul_comm]
      simp [h]
    · have : ¬ t < 2 * (a : ℝ) := by intro h'; apply h; linarith
      simp [h, this]
  simp_rw [h1]
  rw [setLIntegral_indicator measurableSet_Iio, Iio_inter_Ioi, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    cmxHLS_int_rpow (by positivity) (by linarith)]
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have e1 : (a : ℝ≥0∞) ^ p = ENNReal.ofReal ((a : ℝ) ^ p) := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0]
  rw [e1, ← ENNReal.ofReal_coe_nnreal (p := a), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases (NNReal.coe_nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0]; simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · have e2 : (a : ℝ) ^ p = (a : ℝ) * (a : ℝ) ^ (p - 1) := by
      rw [← Real.rpow_one_add' hpos.le (by linarith)]; congr 1; ring
    rw [e2, show p - 2 + 1 = p - 1 by ring, Real.mul_rpow (by norm_num) hpos.le]
    ring


/-- **Hardy–Littlewood maximal theorem** (dyadic centred maximal function, `1 < p < ∞`). -/
theorem cmxHLS_strong (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝔼 → ℝ≥0, Measurable f →
      ∫⁻ x, cmxHLS_Md (fun y => (f y : ℝ≥0∞)) x ^ p ≤
        ENNReal.ofReal C * ∫⁻ y, (f y : ℝ≥0∞) ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set c : ℝ := 2 ^ (p - 1) / (p - 1) with hc
  have hcpos : 0 < c := div_pos (Real.rpow_pos_of_pos (by norm_num) _) hp1
  refine ⟨p * (2 * 4 ^ d) * c, by positivity, fun f hf => ?_⟩
  set F : 𝔼 → ℝ≥0∞ := fun y => (f y : ℝ≥0∞) with hF
  have hFm : Measurable F := hf.coe_nnreal_ennreal
  have hM := cmxHLS_Md_measurable hFm
  have hK : (2 : ℝ≥0∞) * 4 ^ d = ENNReal.ofReal (2 * 4 ^ d) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]; simp
  have key : ∀ N : ℕ, ∫⁻ x, (min (cmxHLS_Md F x) (N : ℝ≥0∞)) ^ p ≤
      ENNReal.ofReal (p * (2 * 4 ^ d) * c) * ∫⁻ y, F y ^ p := by
    intro N
    set gN : 𝔼 → ℝ := fun x => (min (cmxHLS_Md F x) (N : ℝ≥0∞)).toReal with hgN
    have hmeas : Measurable gN := (hM.min measurable_const).ennreal_toReal
    have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul volume (f := gN)
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hmeas.aemeasurable hp0
    have hfin : ∀ x, min (cmxHLS_Md F x) (N : ℝ≥0∞) ≠ ⊤ := fun x =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
    have hL : ∫⁻ x, (min (cmxHLS_Md F x) (N : ℝ≥0∞)) ^ p = ∫⁻ ω, ENNReal.ofReal (gN ω ^ p) := by
      refine lintegral_congr fun x => ?_
      rw [hgN]
      simp only
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le,
        ENNReal.ofReal_toReal (hfin x)]
    rw [hL, hlc]
    have hpt : ∀ t ∈ Ioi (0 : ℝ), volume {a | t < gN a} * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (t ^ (p - 2)) * (2 * 4 ^ d * ∫⁻ y, cmxHLS_ft f t y) := by
      intro t ht
      have ht' : 0 < t := ht
      have hw := cmxHLS_weak_t hd hf ht'
      have hsub : {a | t < gN a} ⊆ {a | ENNReal.ofReal t < cmxHLS_Md F a} := by
        intro a ha
        have ha' : t < gN a := ha
        have : ENNReal.ofReal t < min (cmxHLS_Md F a) (N : ℝ≥0∞) :=
          (ENNReal.ofReal_lt_iff_lt_toReal ht'.le (hfin a)).2 ha'
        exact lt_of_lt_of_le this (min_le_left _ _)
      have he : ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal t * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul ht'.le]
        congr 1
        rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ht', Real.rpow_one]
      calc volume {a | t < gN a} * ENNReal.ofReal (t ^ (p - 1))
          ≤ volume {a | ENNReal.ofReal t < cmxHLS_Md F a} * ENNReal.ofReal (t ^ (p - 1)) :=
            mul_le_mul_left (measure_mono (μ := volume) hsub) _
        _ = (ENNReal.ofReal t * volume {a | ENNReal.ofReal t < cmxHLS_Md F a}) *
              ENNReal.ofReal (t ^ (p - 2)) := by rw [he]; ring
        _ ≤ (2 * 4 ^ d * ∫⁻ y, cmxHLS_ft f t y) * ENNReal.ofReal (t ^ (p - 2)) :=
            mul_le_mul_left hw _
        _ = _ := by ring
    calc ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), volume {a | t < gN a} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (p - 2)) * (2 * 4 ^ d * ∫⁻ y, cmxHLS_ft f t y) :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hpt) _
      _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), (2 * 4 ^ d) * ∫⁻ y,
            ENNReal.ofReal (t ^ (p - 2)) * cmxHLS_ft f t y := by
          congr 1
          refine lintegral_congr fun t => ?_
          rw [lintegral_const_mul _ (cmxHLS_ft_measurable hf t), mul_left_comm]
      _ = ENNReal.ofReal p * ((2 * 4 ^ d) * ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y,
            ENNReal.ofReal (t ^ (p - 2)) * cmxHLS_ft f t y) := by
          rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])]
      _ = ENNReal.ofReal p * ((2 * 4 ^ d) * ∫⁻ y, ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (p - 2)) * cmxHLS_ft f t y) := by
          congr 2
          refine lintegral_lintegral_swap ?_
          refine Measurable.aemeasurable ?_
          have hm1 : Measurable fun q : ℝ × 𝔼 => ENNReal.ofReal (q.1 ^ (p - 2)) :=
            (measurable_fst.pow_const _).ennreal_ofReal
          have hm2 : Measurable fun q : ℝ × 𝔼 => cmxHLS_ft f q.1 q.2 := by
            unfold cmxHLS_ft
            refine Measurable.ite ?_ ((hf.comp measurable_snd).coe_nnreal_ennreal) measurable_const
            exact measurableSet_lt (measurable_fst.div_const 2)
              (by exact (measurable_subtype_coe.comp (hf.comp measurable_snd)))
          exact hm1.mul hm2
      _ = ENNReal.ofReal p * ((2 * 4 ^ d) * (ENNReal.ofReal c * ∫⁻ y, F y ^ p)) := by
          congr 2
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          exact cmxHLS_inner hp (f y)
      _ = ENNReal.ofReal (p * (2 * 4 ^ d) * c) * ∫⁻ y, F y ^ p := by
          have h3 : ENNReal.ofReal (p * (2 * 4 ^ d) * c) =
              ENNReal.ofReal p * ENNReal.ofReal (2 * 4 ^ d) * ENNReal.ofReal c := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          rw [hK, h3]
          ring
  -- monotone convergence
  have hsup : ∀ x, cmxHLS_Md F x ^ p = ⨆ N : ℕ, (min (cmxHLS_Md F x) (N : ℝ≥0∞)) ^ p := by
    intro x
    have h1 : (⨆ N : ℕ, min (cmxHLS_Md F x) (N : ℝ≥0∞)) = cmxHLS_Md F x := by
      have := inf_iSup_eq (cmxHLS_Md F x) (fun N : ℕ => (N : ℝ≥0∞))
      rw [ENNReal.iSup_natCast, inf_top_eq] at this
      exact this.symm
    conv_lhs => rw [← h1]
    refine Monotone.map_iSup_of_continuousAt (f := fun z : ℝ≥0∞ => z ^ p)
      ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hp0.le) ?_
    simp [ENNReal.zero_rpow_of_pos hp0]
  calc ∫⁻ x, cmxHLS_Md F x ^ p = ∫⁻ x, ⨆ N : ℕ, (min (cmxHLS_Md F x) (N : ℝ≥0∞)) ^ p :=
        lintegral_congr hsup
    _ = ⨆ N : ℕ, ∫⁻ x, (min (cmxHLS_Md F x) (N : ℝ≥0∞)) ^ p := by
        refine lintegral_iSup (fun N => ?_) (fun N M hNM x => ?_)
        · exact (hM.min measurable_const).pow_const _
        · exact ENNReal.monotone_rpow_of_nonneg hp0.le (min_le_min le_rfl (by exact_mod_cast hNM))
    _ ≤ _ := iSup_le key

end HRS.Commutator.Whole
