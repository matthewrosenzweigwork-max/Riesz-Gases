import Mathlib

/-!
# FC-G, part 1: the abstract moment transfer

`Pt << Q << Pi` with `L^p` density `Pt/Q`, `L^2` density `Q/Pi`, an exponential moment of `Z` under `Q` and a
small `L^2(Pi)` norm of `Z`.  Then all moments of `Z` under `Pt` are small:
`E_Pt |Z|^q <= C1 * ((A^{1/2} C2)^{1/2} M^{1/2})^{1/p'}` (Holder + Cauchy--Schwarz interpolation).
Packet prefix `fcg`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.Sec7.FCG

variable {E : Type*} [MeasurableSpace E]

/-- Cauchy--Schwarz for `ℝ≥0∞`-valued functions, with real exponents `2`. -/
theorem fcg_cs (μ : Measure E) {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, f x * g x ∂μ ≤ (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.aemeasurable hg.aemeasurable

/-- Unwinding `eLpNorm` into a lintegral for `ℝ≥0∞`-valued measurable functions. -/
theorem fcg_eLpNorm_eq (μ : Measure E) {h : E → ℝ≥0∞} (hh : Measurable h) {p : ℝ} (hp : 0 < p) :
    eLpNorm h (ENNReal.ofReal p) μ = (∫⁻ x, h x ^ p ∂μ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hh.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp

/-- Transfer by a density in `L^p`. -/
theorem fcg_holder_density (Pt Q : Measure E) [SigmaFinite Q] [SigmaFinite Pt] (hac : Pt ≪ Q) {p : ℝ}
    (hp : 1 < p) {C1 : ℝ}
    (hd : eLpNorm (Pt.rnDeriv Q) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C1)
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂Pt ≤ ENNReal.ofReal C1 *
      (∫⁻ x, F x ^ (Real.conjExponent p) ∂Q) ^ (1 / Real.conjExponent p) := by
  have hp0 : 0 < p := by linarith
  have h1 : ∫⁻ x, F x ∂Pt = ∫⁻ x, Pt.rnDeriv Q x * F x ∂Q :=
    (lintegral_rnDeriv_mul hac hF.aemeasurable).symm
  have hhm : Measurable (Pt.rnDeriv Q) := Measure.measurable_rnDeriv Pt Q
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq Q (Real.HolderConjugate.conjExponent hp).symm
    hF.aemeasurable hhm.aemeasurable
  rw [h1]
  calc ∫⁻ x, Pt.rnDeriv Q x * F x ∂Q = ∫⁻ x, (F * Pt.rnDeriv Q) x ∂Q := by
        refine lintegral_congr fun x => ?_
        simp [mul_comm]
    _ ≤ _ := h2
    _ = (∫⁻ x, F x ^ (Real.conjExponent p) ∂Q) ^ (1 / Real.conjExponent p) *
          eLpNorm (Pt.rnDeriv Q) (ENNReal.ofReal p) Q := by
        rw [fcg_eLpNorm_eq Q hhm hp0]
    _ ≤ (∫⁻ x, F x ^ (Real.conjExponent p) ∂Q) ^ (1 / Real.conjExponent p) * ENNReal.ofReal C1 :=
        mul_le_mul_right hd _
    _ = _ := mul_comm _ _

/-- Interpolation: `E|Z|^r <= (E|Z|)^{1/2} (E|Z|^{2r-1})^{1/2}`, `r >= 1/2`. -/
theorem fcg_interp (Q : Measure E) {Z : E → ℝ} (hZ : Measurable Z) {r : ℝ} (hr : 1 / 2 ≤ r) :
    ∫⁻ x, ENNReal.ofReal (|Z x| ^ r) ∂Q ≤
      (∫⁻ x, ENNReal.ofReal |Z x| ∂Q) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, ENNReal.ofReal (|Z x| ^ (2 * r - 1)) ∂Q) ^ (1 / (2 : ℝ)) := by
  have hfm : Measurable fun x => ENNReal.ofReal (|Z x| ^ (1 / (2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((hZ.abs).pow_const _)
  have hgm : Measurable fun x => ENNReal.ofReal (|Z x| ^ (r - 1 / 2)) :=
    ENNReal.measurable_ofReal.comp ((hZ.abs).pow_const _)
  have h := fcg_cs Q hfm hgm
  have e1 : ∀ x, ENNReal.ofReal (|Z x| ^ r) =
      ENNReal.ofReal (|Z x| ^ (1 / (2 : ℝ))) * ENNReal.ofReal (|Z x| ^ (r - 1 / 2)) := fun x => by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_add' (abs_nonneg _)
      (by linarith)]
    congr 2; ring
  have e2 : ∀ x, ENNReal.ofReal (|Z x| ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = ENNReal.ofReal |Z x| := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have e3 : ∀ x, ENNReal.ofReal (|Z x| ^ (r - 1 / 2)) ^ (2 : ℝ) =
      ENNReal.ofReal (|Z x| ^ (2 * r - 1)) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (abs_nonneg _)]
    congr 2; ring
  simp only [e1]
  simp only [e2, e3] at h
  exact h

/-- Pointwise comparison `u^m <= K exp(c u)`. -/
theorem fcg_pow_le_exp {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) (u : ℝ) (hu : 0 ≤ u) :
    u ^ m ≤ (1 + ((⌈m⌉₊).factorial : ℝ) / c ^ ⌈m⌉₊) * Real.exp (c * u) := by
  set n := ⌈m⌉₊ with hn
  have hmn : m ≤ n := Nat.le_ceil m
  have h1 : u ^ m ≤ 1 + u ^ n := by
    rcases le_total u 1 with h | h
    · have : u ^ m ≤ 1 := Real.rpow_le_one hu h hm
      have : 0 ≤ u ^ n := pow_nonneg hu n
      linarith
    · have : u ^ m ≤ u ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h hmn
      rw [Real.rpow_natCast] at this
      have : 0 ≤ (1 : ℝ) := zero_le_one
      linarith
  have h2 : (c * u) ^ n / (n.factorial : ℝ) ≤ Real.exp (c * u) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h3 : u ^ n ≤ ((n.factorial : ℝ) / c ^ n) * Real.exp (c * u) := by
    have hcn : 0 < c ^ n := pow_pos hc n
    rw [div_mul_eq_mul_div, le_div_iff₀ hcn]
    have := (div_le_iff₀ hfpos).1 h2
    calc u ^ n * c ^ n = (c * u) ^ n := by rw [mul_pow]; ring
      _ ≤ Real.exp (c * u) * n.factorial := this
      _ = _ := by ring
  have h4 : (1 : ℝ) ≤ Real.exp (c * u) := Real.one_le_exp (by positivity)
  have h5 : 0 ≤ ((n.factorial : ℝ) / c ^ n) := by positivity
  calc u ^ m ≤ 1 + u ^ n := h1
    _ ≤ 1 * Real.exp (c * u) + ((n.factorial : ℝ) / c ^ n) * Real.exp (c * u) := by linarith
    _ = _ := by ring

/-- The exponential moment bounds all moments. -/
theorem fcg_moment_of_exp (Q : Measure E) {Z : E → ℝ} (hZ : Measurable Z) {c CB : ℝ} (hc : 0 < c)
    (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Z x|)) ∂Q ≤ ENNReal.ofReal CB) {m : ℝ} (hm : 0 ≤ m) :
    ∫⁻ x, ENNReal.ofReal (|Z x| ^ m) ∂Q ≤
      ENNReal.ofReal ((1 + ((⌈m⌉₊).factorial : ℝ) / c ^ ⌈m⌉₊) * CB) := by
  set K : ℝ := 1 + ((⌈m⌉₊).factorial : ℝ) / c ^ ⌈m⌉₊ with hK
  have hK0 : 0 ≤ K := by positivity
  calc ∫⁻ x, ENNReal.ofReal (|Z x| ^ m) ∂Q
      ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal (Real.exp (c * |Z x|)) ∂Q := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (fcg_pow_le_exp hm hc _ (abs_nonneg _))
    _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Z x|)) ∂Q :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal CB := mul_le_mul_right hexp _
    _ = _ := (ENNReal.ofReal_mul hK0).symm

/-- First moment under `Q` from the `L^2(Pi)` size of `Z` and the `L^2` density `Q/Pi`. -/
theorem fcg_first_moment (Pi Q : Measure E) [SigmaFinite Pi] [SigmaFinite Q] (hac : Q ≪ Pi) {C2 : ℝ}
    (hd : eLpNorm (Q.rnDeriv Pi) (ENNReal.ofReal 2) Pi ≤ ENNReal.ofReal C2) {Z : E → ℝ}
    (hZ : Measurable Z) {A : ℝ}
    (hA : ∫⁻ x, ENNReal.ofReal (|Z x| ^ (2 : ℕ)) ∂Pi ≤ ENNReal.ofReal A) :
    ∫⁻ x, ENNReal.ofReal |Z x| ∂Q ≤ ENNReal.ofReal A ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2 := by
  have hhm : Measurable (Q.rnDeriv Pi) := Measure.measurable_rnDeriv Q Pi
  have hfm : Measurable fun x => ENNReal.ofReal |Z x| := ENNReal.measurable_ofReal.comp hZ.abs
  have h1 : ∫⁻ x, ENNReal.ofReal |Z x| ∂Q = ∫⁻ x, Q.rnDeriv Pi x * ENNReal.ofReal |Z x| ∂Pi :=
    (lintegral_rnDeriv_mul hac hfm.aemeasurable).symm
  have h2 := fcg_cs Pi hhm hfm
  rw [h1]
  have h3 : (∫⁻ x, Q.rnDeriv Pi x ^ (2 : ℝ) ∂Pi) ^ (1 / (2 : ℝ)) = eLpNorm (Q.rnDeriv Pi)
      (ENNReal.ofReal 2) Pi := (fcg_eLpNorm_eq Pi hhm (by norm_num)).symm
  have h4 : (∫⁻ x, ENNReal.ofReal |Z x| ^ (2 : ℝ) ∂Pi) ≤ ENNReal.ofReal A := by
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) hA
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    norm_cast
  calc ∫⁻ x, Q.rnDeriv Pi x * ENNReal.ofReal |Z x| ∂Pi
      ≤ _ := h2
    _ = eLpNorm (Q.rnDeriv Pi) (ENNReal.ofReal 2) Pi *
          (∫⁻ x, ENNReal.ofReal |Z x| ^ (2 : ℝ) ∂Pi) ^ (1 / (2 : ℝ)) := by rw [← h3]
    _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal A ^ (1 / (2 : ℝ)) :=
        mul_le_mul' hd (ENNReal.rpow_le_rpow h4 (by norm_num))
    _ = _ := mul_comm _ _


/-- The moment constant of the interpolation. -/
def fcgM (q p c CB : ℝ) : ℝ :=
  (1 + ((⌈2 * (q * Real.conjExponent p) - 1⌉₊).factorial : ℝ) / c ^ ⌈2 * (q * Real.conjExponent p) - 1⌉₊) * CB

/-- The transfer bound as an explicit function of `A`. -/
def fcgBound (C1 C2 M p : ℝ) (A : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal C1 * ((ENNReal.ofReal A ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
    ENNReal.ofReal M ^ (1 / (2 : ℝ))) ^ (1 / Real.conjExponent p)

/-- **The abstract moment transfer.** -/
theorem fcg_transfer (Pi Q Pt : Measure E) [SigmaFinite Pi] [SigmaFinite Q] [SigmaFinite Pt]
    (hQ : Q ≪ Pi) (hP : Pt ≪ Q) {p : ℝ} (hp : 1 < p) {C1 C2 c CB A : ℝ} (hc : 0 < c)
    (hd1 : eLpNorm (Pt.rnDeriv Q) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C1)
    (hd2 : eLpNorm (Q.rnDeriv Pi) (ENNReal.ofReal 2) Pi ≤ ENNReal.ofReal C2) {Z : E → ℝ}
    (hZ : Measurable Z)
    (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Z x|)) ∂Q ≤ ENNReal.ofReal CB)
    (hA : ∫⁻ x, ENNReal.ofReal (|Z x| ^ (2 : ℕ)) ∂Pi ≤ ENNReal.ofReal A) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x, ENNReal.ofReal (|Z x| ^ q) ∂Pt ≤ fcgBound C1 C2 (fcgM q p c CB) p A := by
  set p' := Real.conjExponent p with hp'
  have hp'1 : 1 < p' := (Real.HolderConjugate.conjExponent hp).symm.lt
  have hFm : Measurable fun x => ENNReal.ofReal (|Z x| ^ q) :=
    ENNReal.measurable_ofReal.comp (hZ.abs.pow_const _)
  have h1 := fcg_holder_density Pt Q hP hp hd1 hFm
  have e1 : ∀ x, ENNReal.ofReal (|Z x| ^ q) ^ p' = ENNReal.ofReal (|Z x| ^ (q * p')) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by linarith),
      ← Real.rpow_mul (abs_nonneg _)]
  set r := q * p' with hr
  have h1' : ∫⁻ x, ENNReal.ofReal (|Z x| ^ q) ^ p' ∂Q = ∫⁻ x, ENNReal.ofReal (|Z x| ^ r) ∂Q :=
    lintegral_congr e1
  rw [h1'] at h1
  have hr1 : 1 ≤ r := by nlinarith
  have h2 := fcg_interp Q hZ (r := r) (by linarith)
  have h3 := fcg_first_moment Pi Q hQ hd2 hZ hA
  have h4 := fcg_moment_of_exp Q hZ hc hexp (m := 2 * r - 1) (by linarith)
  have h5 : ∫⁻ x, ENNReal.ofReal (|Z x| ^ r) ∂Q ≤
      (ENNReal.ofReal A ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (fcgM q p c CB) ^ (1 / (2 : ℝ)) := by
    refine h2.trans (mul_le_mul' (ENNReal.rpow_le_rpow h3 (by norm_num))
      (ENNReal.rpow_le_rpow ?_ (by norm_num)))
    exact h4
  refine h1.trans ?_
  unfold fcgBound
  exact mul_le_mul_right (ENNReal.rpow_le_rpow h5 (by positivity)) _

/-- The transfer bound tends to `0` with `A`. -/
theorem fcg_bound_tendsto (C1 C2 M p : ℝ) (hp : 1 < p) {ι : Type*} {l : Filter ι} {A : ι → ℝ}
    (hA : Tendsto A l (𝓝 0)) : Tendsto (fun i => fcgBound C1 C2 M p (A i)) l (𝓝 0) := by
  have hp' : 0 < 1 / Real.conjExponent p := by
    have : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
    positivity
  have h0 : Tendsto (fun i => ENNReal.ofReal (A i)) l (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal hA)
  have h1 : Tendsto (fun i => ENNReal.ofReal (A i) ^ (1 / (2 : ℝ))) l (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.comp h0
  have h2 : Tendsto (fun i => ENNReal.ofReal (A i) ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.ofReal_ne_top)
  have h3 : Tendsto (fun i => (ENNReal.ofReal (A i) ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)))
      l (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.comp h2
  have h4 : Tendsto (fun i => (ENNReal.ofReal (A i) ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
      ENNReal.ofReal M ^ (1 / (2 : ℝ))) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h3 (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top))
  have h5 : Tendsto (fun i => ((ENNReal.ofReal (A i) ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
      ENNReal.ofReal M ^ (1 / (2 : ℝ))) ^ (1 / Real.conjExponent p)) l (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / Real.conjExponent p)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos hp'] at this
    exact this.comp h4
  unfold fcgBound
  simpa using ENNReal.Tendsto.const_mul h5 (Or.inr ENNReal.ofReal_ne_top)

end HRS.MC.Sec7.FCG

end
