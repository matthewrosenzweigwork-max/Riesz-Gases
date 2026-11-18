import HRS.MS.MovBridgeAux7

/-!
# MOVA3C, part 2: dilations on the oscillator scale (`mo_dilate`)

Namespace `HRS.MS.MovOsc`, helpers `mova3c_`.  Infrastructure for S6.1/S6.2 (the shifted oscillator `S_0`
is diagonal in the dilated Hermite basis; its scale `Σ^r` coincides with the scale of `𝓗`).

* `mova3c_dil l hl`: `w ↦ w(l ·)` on Schwartz functions (`SchwartzMap.compCLM`).
* `mova3c_W_dil`, `mova3c_dil_int`: integer endpoint, `‖w(l ·)‖_{Σ^n} ≤ C ‖w‖_{Σ^n}`, `l ∈ [a,b]`, by induction
  on the word norm: `(x_j + ∂_j)(w(l ·)) = (l⁻¹ x_j w + l ∂_j w)(l ·)` and `mo_xmul`, `mo_partial` (through
  `mova3c_W_XD`); the constant depends on `d, n, a, b` only.
* `mova3c_dil_span`: real index `σ ≥ 0` on the Hermite span (`mo_interp_osc` between `⌊σ⌋, ⌊σ⌋+1`).
* `mo_dilate`: for `0 < a ≤ b`, every real `s`, `l ∈ [a,b]`, `f ∈ Σ^s`: `f(l ·) ∈ Σ^s` and
  `‖f(l ·)‖_{Σ^s} ≤ C ‖f‖_{Σ^s}`, `C = C(d, s, a, b)`.  Negative indices and non-span `f` by
  `mova3c_dual_ext` with the adjoint `T'_l g = l^{-d} g(l⁻¹ ·)` (`∫ f(l x) g(x) dx = l^{-d} ∫ f(y) g(y/l) dy`);
  the compact set is made inversion invariant (`[μ, μ⁻¹]`, `μ = min a b⁻¹`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ContDiff

namespace HRS.MS.MovOsc

open HRS HRS.Whole HRS.MS.MovInterp

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ## The dilation operator on Schwartz functions -/

lemma mova3c_smul_tg (l : ℝ) : (fun x : Euc d => l • x).HasTemperateGrowth := by
  have : (fun x : Euc d => l • x) = ⇑(l • ContinuousLinearMap.id ℝ (Euc d)) := by
    funext x; simp
  rw [this]
  exact ContinuousLinearMap.hasTemperateGrowth _

/-- `w ↦ w(l ·)` on Schwartz functions, `l > 0`. -/
def mova3c_dil (l : ℝ) (hl : 0 < l) : 𝓢R →L[ℝ] 𝓢R :=
  SchwartzMap.compCLM ℝ (mova3c_smul_tg l) ⟨1, l⁻¹, fun x => by
    rw [norm_smul, Real.norm_of_nonneg hl.le, pow_one]
    have : l⁻¹ * (1 + l * ‖x‖) = l⁻¹ + ‖x‖ := by field_simp
    rw [this]; linarith [inv_pos.2 hl]⟩

lemma mova3c_dil_apply (l : ℝ) (hl : 0 < l) (w : 𝓢R) (x : Euc d) :
    mova3c_dil l hl w x = w (l • x) := rfl

/-- The ladder operator on a dilated function. -/
lemma mova3c_dil_G (l : ℝ) (hl : 0 < l) (j : Fin d) (w : 𝓢R) :
    mova1_X j (mova3c_dil l hl w) + mova1_D j (mova3c_dil l hl w) =
      mova3c_dil l hl (l⁻¹ • mova1_X j w + l • mova1_D j w) := by
  ext x
  have hfd : fderiv ℝ (fun y : Euc d => w (l • y)) x =
      (fderiv ℝ w (l • x)).comp (l • ContinuousLinearMap.id ℝ (Euc d)) := by
    have h1 : HasFDerivAt w (fderiv ℝ w (l • x)) (l • x) := w.differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun y : Euc d => l • y) (l • ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).const_smul l
    exact (h1.comp x h2).fderiv
  have hcoord : (l • x) j = l * x j := by simp
  simp only [SchwartzMap.add_apply, mova1_X_apply, mova1_D_apply, mova3c_dil_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  show x j * w (l • x) + fderiv ℝ (fun y : Euc d => w (l • y)) x (EuclideanSpace.single j 1) = _
  rw [hfd, hcoord]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  field_simp

/-- `L²` norm of a dilation. -/
lemma mova3c_dil_l2 (l : ℝ) (hl : 0 < l) (w : 𝓢R) :
    mova1_n2 (mova3c_dil l hl w) = Real.sqrt ((l ^ d)⁻¹) * mova1_n2 w := by
  rw [mova1_n2_eq, mova1_n2_eq]
  unfold mo_l2
  have h := Measure.integral_comp_smul (volume : Measure (Euc d)) (fun y => w y ^ 2) l
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
  have e : (fun x => (mova3c_dil l hl w) x ^ 2) = fun x => (fun y => w y ^ 2) (l • x) := rfl
  rw [e, h, abs_of_nonneg (by positivity), Real.sqrt_mul (by positivity)]

/-! ## Word norm of a dilation -/

lemma mova3c_W_XD (n : ℕ) : ∃ E : ℝ, 0 ≤ E ∧ ∀ (j : Fin d) (w : 𝓢R),
    mova1_W n (mova1_X j w) ≤ E * mova1_W (n + 1) w ∧ mova1_W n (mova1_D j w) ≤ E * mova1_W (n + 1) w := by
  obtain ⟨K, hK, hW⟩ := mova3c_W_le_osc (d := d) n
  obtain ⟨Cx, hCx, hx⟩ := mo_xmul (d := d) (n : ℝ)
  obtain ⟨Cp, hCp, hp⟩ := mo_partial (d := d) (n : ℝ)
  obtain ⟨Cl, hCl, hl⟩ := mova1_lower_W (d := d) (n + 1)
  refine ⟨K * (Cx + Cp) * Cl, by positivity, fun j w => ?_⟩
  have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hl' : oscNorm ((n : ℝ) + 1) w ≤ Cl * mova1_W (n + 1) w := by
    have := hl w; rwa [hn] at this
  have hW0 := mova1_W_nonneg (d := d) (n + 1) w
  constructor
  · have e : (⇑(mova1_X j w) : Euc d → ℝ) = fun x => x j * w x := funext (mova1_X_apply j w)
    calc mova1_W n (mova1_X j w) ≤ K * oscNorm (n : ℝ) (mova1_X j w) := hW _
      _ = K * oscNorm (n : ℝ) (fun x => x j * w x) := by rw [e]
      _ ≤ K * (Cx * oscNorm ((n : ℝ) + 1) w) :=
          mul_le_mul_of_nonneg_left (hx j w).2 hK
      _ ≤ K * (Cx * (Cl * mova1_W (n + 1) w)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl' hCx) hK
      _ ≤ K * (Cx + Cp) * Cl * mova1_W (n + 1) w := by
          have : 0 ≤ K * Cl * mova1_W (n + 1) w := by positivity
          nlinarith [mul_nonneg this hCp]
  · have e : (⇑(mova1_D j w) : Euc d → ℝ) =
        fun x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ)) := funext (mova1_D_apply j w)
    calc mova1_W n (mova1_D j w) ≤ K * oscNorm (n : ℝ) (mova1_D j w) := hW _
      _ = K * oscNorm (n : ℝ) (fun x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) := by rw [e]
      _ ≤ K * (Cp * oscNorm ((n : ℝ) + 1) w) :=
          mul_le_mul_of_nonneg_left (hp j w).2 hK
      _ ≤ K * (Cp * (Cl * mova1_W (n + 1) w)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl' hCp) hK
      _ ≤ K * (Cx + Cp) * Cl * mova1_W (n + 1) w := by
          have : 0 ≤ K * Cl * mova1_W (n + 1) w := by positivity
          nlinarith [mul_nonneg this hCx]

theorem mova3c_W_dil (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℝ) (hl : 0 < l), a ≤ l → l ≤ b → ∀ w : 𝓢R,
      mova1_W n (mova3c_dil l hl w) ≤ C * mova1_W n w := by
  induction n with
  | zero =>
    refine ⟨Real.sqrt ((a ^ d)⁻¹), Real.sqrt_nonneg _, fun l hl hal hlb w => ?_⟩
    show mova1_n2 (mova3c_dil l hl w) ≤ Real.sqrt ((a ^ d)⁻¹) * mova1_n2 w
    rw [mova3c_dil_l2]
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (mova1_n2_nonneg w)
    exact inv_anti₀ (pow_pos ha d) (pow_le_pow_left₀ ha.le hal d)
  | succ n ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    obtain ⟨E, hE, hEb⟩ := mova3c_W_XD (d := d) n
    have hb0 : 0 < b := ha.trans_le hab
    have hM0 : 0 ≤ (a⁻¹ + b) * E := mul_nonneg (add_nonneg (inv_nonneg.2 ha.le) hb0.le) hE
    refine ⟨C * (1 + (d : ℝ) * ((a⁻¹ + b) * E)), by positivity, fun l hl hal hlb w => ?_⟩
    have hWn := mova3c_W_mono n w
    have hW0 : 0 ≤ mova1_W n w := mova1_W_nonneg n w
    have hW1 : 0 ≤ mova1_W (n + 1) w := mova1_W_nonneg (n + 1) w
    have hlinv : l⁻¹ ≤ a⁻¹ := inv_anti₀ ha hal
    have T2 : ∀ j : Fin d, mova1_W n (mova1_X j (mova3c_dil l hl w) + mova1_D j (mova3c_dil l hl w)) ≤
        C * (((a⁻¹ + b) * E) * mova1_W (n + 1) w) := by
      intro j
      rw [mova3c_dil_G]
      refine (hCb l hl hal hlb _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC
      refine (mova3b2_W_add n _ _).trans ?_
      rw [mova3c_W_smul, mova3c_W_smul, abs_of_pos (inv_pos.2 hl), abs_of_pos hl]
      have h1 := (hEb j w).1
      have h2 := (hEb j w).2
      have hX0 : 0 ≤ mova1_W n (mova1_X j w) := mova1_W_nonneg n _
      have hD0 : 0 ≤ mova1_W n (mova1_D j w) := mova1_W_nonneg n _
      calc l⁻¹ * mova1_W n (mova1_X j w) + l * mova1_W n (mova1_D j w)
          ≤ a⁻¹ * (E * mova1_W (n + 1) w) + b * (E * mova1_W (n + 1) w) :=
            add_le_add (mul_le_mul hlinv h1 hX0 (inv_nonneg.2 ha.le))
              (mul_le_mul hlb h2 hD0 (ha.le.trans hab))
        _ = (a⁻¹ + b) * E * mova1_W (n + 1) w := by ring
        _ = _ := by ring
    show mova1_W n (mova3c_dil l hl w) + ∑ j : Fin d,
      mova1_W n (mova1_X j (mova3c_dil l hl w) + mova1_D j (mova3c_dil l hl w)) ≤
        C * (1 + (d : ℝ) * ((a⁻¹ + b) * E)) *
          (mova1_W n w + ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w))
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => T2 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have h1 : mova1_W n (mova3c_dil l hl w) ≤ C * mova1_W (n + 1) w :=
      (hCb l hl hal hlb w).trans (mul_le_mul_of_nonneg_left hWn hC)
    have hS : mova1_W (n + 1) w = mova1_W n w + ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w) := rfl
    rw [← hS]
    calc _ ≤ C * mova1_W (n + 1) w + (d : ℝ) * (C * (((a⁻¹ + b) * E) * mova1_W (n + 1) w)) := by
          linarith
      _ = _ := by ring

lemma mova3c_dil_memLp (l : ℝ) (hl : 0 < l) (w : 𝓢R) :
    MemLp (fun x => w (l • x)) 2 (volume : Measure (Euc d)) :=
  (mova3c_dil l hl w).memLp 2 volume

/-- **Integer endpoint of the dilation bound.** -/
theorem mova3c_dil_int (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℝ) (hl : 0 < l), a ≤ l → l ≤ b → ∀ w : 𝓢R,
      MemOsc (n : ℝ) (fun x => w (l • x)) ∧
        oscNorm (n : ℝ) (fun x => w (l • x)) ≤ C * oscNorm (n : ℝ) w := by
  obtain ⟨C1, hC1, h1⟩ := mova3c_W_dil n ha hab
  obtain ⟨C2, hC2, h2⟩ := mova1_lower_W (d := d) n
  obtain ⟨K, hK, h3⟩ := mova3c_W_le_osc (d := d) n
  refine ⟨C2 * C1 * K, by positivity, fun l hl hal hlb w => ?_⟩
  have hf : (fun x => w (l • x)) = ⇑(mova3c_dil l hl w) := rfl
  rw [hf]
  refine ⟨memOsc_schwartz _ _, ?_⟩
  calc oscNorm (n : ℝ) (⇑(mova3c_dil l hl w)) ≤ C2 * mova1_W n (mova3c_dil l hl w) := h2 _
    _ ≤ C2 * (C1 * mova1_W n w) := mul_le_mul_of_nonneg_left (h1 l hl hal hlb w) hC2
    _ ≤ C2 * (C1 * (K * oscNorm (n : ℝ) w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h3 w) hC1) hC2
    _ = _ := by ring

/-- **Dilation on the Hermite span**, real index `σ ≥ 0`. -/
theorem mova3c_dil_span (σ : ℝ) (hσ : 0 ≤ σ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℝ) (hl : 0 < l), a ≤ l → l ≤ b → ∀ f ∈ mo_Hspan d,
      MemOsc σ (fun x => f (l • x)) ∧ oscNorm σ (fun x => f (l • x)) ≤ C * oscNorm σ f := by
  set n0 : ℕ := ⌊σ⌋₊ with hn0
  have hn0s : (n0 : ℝ) ≤ σ := Nat.floor_le hσ
  have hs1 : σ < (n0 : ℝ) + 1 := Nat.lt_floor_add_one σ
  obtain ⟨C0, hC0, h0⟩ := mova3c_dil_int (d := d) n0 ha hab
  obtain ⟨C1, hC1, h1⟩ := mova3c_dil_int (d := d) (n0 + 1) ha hab
  refine ⟨max C0 C1, le_trans hC0 (le_max_left _ _), fun l hl hal hlb f hf => ?_⟩
  have hT := mova3c_interp_span (d := d) (T := fun f x => f (l • x))
    (fun f _ g _ c => by funext x; simp)
    (fun f hf => by
      obtain ⟨φ, rfl⟩ := mova3c_hspan_schwartz hf
      exact mova3c_dil_memLp l hl φ)
    (k := n0) (M0 := C0) (M1 := C1)
    (fun f hf => by
      obtain ⟨φ, rfl⟩ := mova3c_hspan_schwartz hf
      exact h0 l hl hal hlb φ)
    (fun f hf => by
      obtain ⟨φ, rfl⟩ := mova3c_hspan_schwartz hf
      exact h1 l hl hal hlb φ)
    hn0s hs1.le f hf
  exact hT

/-! ## Duality: the adjoint of a dilation -/

lemma mova3c_osc_const_mul (r c : ℝ) {f : Euc d → ℝ} (hf : MemOsc r f) :
    MemOsc r (fun x => c * f x) ∧ oscNorm r (fun x => c * f x) = |c| * oscNorm r f := by
  have hc : ∀ α, hermiteCoeff (fun x => c * f x) α = c * hermiteCoeff f α := by
    intro α
    unfold hermiteCoeff
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hs : Summable fun α => oscEigenvalue d α ^ r * hermiteCoeff (fun x => c * f x) α ^ 2 := by
    refine (hf.2.mul_left (c ^ 2)).congr fun α => ?_
    rw [hc]; ring
  refine ⟨⟨hf.1.const_mul c, hs⟩, ?_⟩
  unfold oscNorm
  have : ∑' α, oscEigenvalue d α ^ r * hermiteCoeff (fun x => c * f x) α ^ 2 =
      c ^ 2 * ∑' α, oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun α => by rw [hc]; ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma mova3c_comp_smul_memLp {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) {l : ℝ}
    (hl : 0 < l) : MemLp (fun x => f (l • x)) 2 (volume : Measure (Euc d)) := by
  have hmap : Measure.map (fun x : Euc d => l • x) (volume : Measure (Euc d)) =
      ENNReal.ofReal |(l ^ Module.finrank ℝ (Euc d))⁻¹| • (volume : Measure (Euc d)) :=
    Measure.map_addHaar_smul volume hl.ne'
  have hm : AEStronglyMeasurable (fun x => f (l • x)) (volume : Measure (Euc d)) := by
    have h1 : AEStronglyMeasurable f (Measure.map (fun x : Euc d => l • x) volume) := by
      rw [hmap]; exact hf.aestronglyMeasurable.smul_measure _
    exact h1.comp_aemeasurable (measurable_const_smul l).aemeasurable
  rw [memLp_two_iff_integrable_sq hm]
  exact (integrable_comp_smul_iff volume (fun y => f y ^ 2) hl.ne').2 hf.integrable_sq

lemma mova3c_dil_adj (l : ℝ) (hl : 0 < l) (f g : Euc d → ℝ) :
    ∫ x, f (l • x) * g x = ∫ x, f x * ((l ^ d)⁻¹ * g (l⁻¹ • x)) := by
  have h := Measure.integral_comp_smul (volume : Measure (Euc d)) (fun y => f y * g (l⁻¹ • y)) l
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
  have e : (fun x => f (l • x) * g x) = fun x => (fun y => f y * g (l⁻¹ • y)) (l • x) := by
    funext x; simp [smul_smul, inv_mul_cancel₀ hl.ne']
  have e2 : ∫ x, f x * ((l ^ d)⁻¹ * g (l⁻¹ • x)) = (l ^ d)⁻¹ * ∫ x, f x * g (l⁻¹ • x) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e, h, e2, abs_of_nonneg (by positivity)]

/-- **Dilation on the oscillator scale.**  For `0 < a ≤ b` and every real `s` there is `C = C(d, s, a, b)`
such that for all `l ∈ [a, b]` and `f ∈ Σ^s`: `f(l ·) ∈ Σ^s` and `‖f(l ·)‖_{Σ^s} ≤ C ‖f‖_{Σ^s}`. -/
theorem mo_dilate (s : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℝ), a ≤ l → l ≤ b → ∀ f : Euc d → ℝ, MemOsc s f →
      MemOsc s (fun x => f (l • x)) ∧ oscNorm s (fun x => f (l • x)) ≤ C * oscNorm s f := by
  have hb : 0 < b := ha.trans_le hab
  set μ : ℝ := min a b⁻¹ with hμ
  have hμpos : 0 < μ := lt_min ha (inv_pos.2 hb)
  have hμa : μ ≤ a := min_le_left _ _
  have hμb : μ ≤ b⁻¹ := min_le_right _ _
  have hbμ : b ≤ μ⁻¹ := by
    have := inv_anti₀ hμpos hμb
    rwa [inv_inv] at this
  have hμμ : μ ≤ μ⁻¹ := hμa.trans (hab.trans hbμ)
  obtain ⟨Cs, hCs, hspan⟩ := mova3c_dil_span (d := d) |s| (abs_nonneg s) hμpos hμμ
  have hq : 0 < (μ ^ d)⁻¹ := by positivity
  have hq1 : ∀ l : ℝ, μ ≤ l → (l ^ d)⁻¹ ≤ (μ ^ d)⁻¹ := fun l hl =>
    inv_anti₀ (pow_pos hμpos d) (pow_le_pow_left₀ hμpos.le hl d)
  -- inversion invariance of `[μ, μ⁻¹]`
  have hinv1 : ∀ l : ℝ, 0 < l → l ≤ μ⁻¹ → μ ≤ l⁻¹ := fun l hl h => by
    rw [le_inv_comm₀ hμpos hl]; exact h
  have hinv2 : ∀ l : ℝ, 0 < l → μ ≤ l → l⁻¹ ≤ μ⁻¹ := fun l hl h => inv_anti₀ hμpos h
  -- negative index, Hermite sums and all of `Σ^{-|s|}`
  have hneg : ∀ l : ℝ, 0 < l → μ ≤ l → l ≤ μ⁻¹ → ∀ f : Euc d → ℝ, MemOsc (-|s|) f →
      MemOsc (-|s|) (fun x => f (l • x)) ∧
        oscNorm (-|s|) (fun x => f (l • x)) ≤ ((μ ^ d)⁻¹ * Cs) * oscNorm (-|s|) f := by
    intro l hl hμl hlμ
    refine mova3c_dual_ext |s| (T := fun f x => f (l • x))
      (T' := fun g x => (l ^ d)⁻¹ * g (l⁻¹ • x)) (mul_nonneg hq.le hCs)
      (fun f hf => mova3c_comp_smul_memLp hf hl) (fun f g _ _ => mova3c_dil_adj l hl f g)
      (fun g hg => ?_)
    obtain ⟨h1, h2⟩ := hspan l⁻¹ (inv_pos.2 hl) (hinv1 l hl hlμ) (hinv2 l hl hμl) g hg
    obtain ⟨h3, h4⟩ := mova3c_osc_const_mul |s| ((l ^ d)⁻¹) h1
    refine ⟨h3, ?_⟩
    rw [h4, abs_of_pos (by positivity)]
    calc (l ^ d)⁻¹ * oscNorm |s| (fun x => g (l⁻¹ • x)) ≤ (μ ^ d)⁻¹ * (Cs * oscNorm |s| g) :=
          mul_le_mul (hq1 l hμl) h2 (Real.sqrt_nonneg _) hq.le
      _ = _ := by ring
  -- positive index
  have hpos : ∀ l : ℝ, 0 < l → μ ≤ l → l ≤ μ⁻¹ → ∀ f : Euc d → ℝ, MemOsc |s| f →
      MemOsc |s| (fun x => f (l • x)) ∧
        oscNorm |s| (fun x => f (l • x)) ≤ ((μ ^ d)⁻¹ * ((μ ^ d)⁻¹ * Cs)) * oscNorm |s| f := by
    intro l hl hμl hlμ f hf
    have := mova3c_dual_ext (-|s|) (T := fun f x => f (l • x))
      (T' := fun g x => (l ^ d)⁻¹ * g (l⁻¹ • x)) (B := (μ ^ d)⁻¹ * ((μ ^ d)⁻¹ * Cs))
      (mul_nonneg hq.le (mul_nonneg hq.le hCs))
      (fun f hf => mova3c_comp_smul_memLp hf hl) (fun f g _ _ => mova3c_dil_adj l hl f g)
      (fun g hg => by
        obtain ⟨h1, h2⟩ := hneg l⁻¹ (inv_pos.2 hl) (hinv1 l hl hlμ) (hinv2 l hl hμl) g
          (mova3b1_hspan_memOsc _ hg)
        obtain ⟨h3, h4⟩ := mova3c_osc_const_mul (-|s|) ((l ^ d)⁻¹) h1
        refine ⟨h3, ?_⟩
        rw [h4, abs_of_pos (by positivity)]
        calc (l ^ d)⁻¹ * oscNorm (-|s|) (fun x => g (l⁻¹ • x)) ≤
              (μ ^ d)⁻¹ * (((μ ^ d)⁻¹ * Cs) * oscNorm (-|s|) g) :=
              mul_le_mul (hq1 l hμl) h2 (Real.sqrt_nonneg _) hq.le
          _ = _ := by ring)
    rw [neg_neg] at this
    exact this f hf
  refine ⟨(μ ^ d)⁻¹ * ((μ ^ d)⁻¹ * Cs) + (μ ^ d)⁻¹ * Cs,
    add_nonneg (mul_nonneg hq.le (mul_nonneg hq.le hCs)) (mul_nonneg hq.le hCs), fun l hal hlb f hf => ?_⟩
  have hl : 0 < l := ha.trans_le hal
  have hμl : μ ≤ l := hμa.trans hal
  have hlμ : l ≤ μ⁻¹ := hlb.trans hbμ
  have hX := Real.sqrt_nonneg (∑' α, oscEigenvalue d α ^ s * hermiteCoeff f α ^ 2)
  rcases le_total 0 s with h | h
  · have hs' : |s| = s := abs_of_nonneg h
    rw [hs'] at hpos
    obtain ⟨h1, h2⟩ := hpos l hl hμl hlμ f hf
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
      (mul_nonneg hq.le hCs)) hX)⟩
  · have hs' : -|s| = s := by rw [abs_of_nonpos h]; ring
    rw [hs'] at hneg
    obtain ⟨h1, h2⟩ := hneg l hl hμl hlμ f hf
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left
      (mul_nonneg hq.le (mul_nonneg hq.le hCs))) hX)⟩

end HRS.MS.MovOsc
