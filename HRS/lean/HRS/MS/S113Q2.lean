import HRS.MS.S113Q1
import HRS.MS.S113X2C6

/-!
# S11.3 Q-regularity (worker S11Q), Q2: the chain inequality for a reference of class `C^{1,2}`

`s113q_Data` is `s113b_Data` with the joint `C²` regularity of the moving reference `q` replaced by the class `C^{1,2}`
(`s113q_C12`: continuous time derivative, continuous first and second SPATIAL derivatives, no mixed derivatives) and positivity on `[0,T+1]`.
`s113q_chain_ac`: the conclusion of `s113b_chain_ac` (and the interval integrability of `s113b_Gp`) for such data, by the Steklov
regularization `q_k = S_{1/(k+2)} q` (jointly `C²`), `s113b_chain_ac` for `q_k` and the passage `k → ∞` by dominated convergence.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral

namespace HRS.MS.S113Q

open HRS.MS.S113X2B HRS.MS.S113X2C

/-- Hypotheses of the chain inequality with a reference of class `C^{1,2}`. -/
structure s113q_Data {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (T : ℝ)
    (u : ℝ → s113b_E n → ℝ) (K G : Set (s113b_E n)) (B : ℝ) : Prop where
  hν : 0 < ν
  hb : ContDiff ℝ 2 b
  hq : s113q_C12 (fun z : ℝ × s113b_E n => q z.1 z.2)
  hq0 : ∀ t, t ∈ Icc 0 (T + 1) → ∀ x, 0 < q t x
  hKc : IsCompact K
  hG : IsOpen G
  hKG : K ⊆ G
  hKu : ∀ t x, x ∉ K → u t x = 0
  hu0 : ∀ t x, 0 ≤ u t x
  huB : ∀ t, t ∈ Icc 0 T → ∀ x, u t x ≤ B
  hum : Measurable (fun z : ℝ × s113b_E n => u z.1 z.2)
  sub : ∀ φ : s113b_E n → ℝ, s113b_Cinf φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) → tsupport φ ⊆ G →
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ x, φ x * u t x ≤ (∫ x, φ x * u s x) +
        ∫ τ in s..t, ∫ x, (ν * s113b_lap φ x + fderiv ℝ φ x (b x)) * u τ x

/-- The numerator `ν Δq - div(bq) - ∂_t q` expressed through the values `a0 = q`, `a1 = ∂_t q`, `a2 = D_x q`, `a3 = D_x² q`. -/
def s113q_Nf {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (a0 a1 : ℝ) (a2 : s113b_E n →L[ℝ] ℝ)
    (a3 : s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ) (x : s113b_E n) : ℝ :=
  ν * ∑ k : Fin n, a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) -
    ∑ k : Fin n, (a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) +
      b x k * a2 (EuclideanSpace.single k 1)) - a1

theorem s113q_N_eq {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 2 b) {q : ℝ → s113b_E n → ℝ}
    {d1 : ℝ × s113b_E n → ℝ} {d2 : ℝ × s113b_E n → s113b_E n →L[ℝ] ℝ}
    {d3 : ℝ × s113b_E n → s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ}
    (hd : s113q_C12Data (fun z : ℝ × s113b_E n => q z.1 z.2) d1 d2 d3) (τ : ℝ) (x : s113b_E n) :
    s113b_N ν b q τ x = s113q_Nf ν b (q τ x) (d1 (τ, x)) (d2 (τ, x)) (d3 (τ, x)) x := by
  have hf2 : fderiv ℝ (q τ) = fun y => d2 (τ, y) := funext fun y => (hd.h2 (τ, y)).fderiv
  have hlap : s113b_lap (q τ) x = ∑ k : Fin n, d3 (τ, x) (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
    simp only [s113b_lap, hf2, (hd.h3 (τ, x)).fderiv]
  have hbk : ∀ k : Fin n, DifferentiableAt ℝ (fun y => b y k) x := fun k =>
    (((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hb).differentiable (by norm_num)) x
  have hdiv : s113b_div (fun y => q τ y • b y) x = ∑ k : Fin n, (q τ x * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) +
      b x k * d2 (τ, x) (EuclideanSpace.single k 1)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hh : HasFDerivAt (fun y => q τ y * b y k) (q τ x • fderiv ℝ (fun y => b y k) x + b x k • d2 (τ, x)) x :=
      (hd.h2 (τ, x)).mul (hbk k).hasFDerivAt
    have : (fun y => (q τ y • b y) k) = fun y => q τ y * b y k := by ext y; simp
    rw [this, hh.fderiv]; simp
  have hdt : deriv (fun σ => q σ x) τ = d1 (τ, x) := (hd.h1 (τ, x)).deriv
  simp only [s113b_N, s113q_Nf, hlap, hdiv, hdt]

/-- Continuity of the numerator in its arguments. -/
theorem s113q_Nf_tendsto {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (x : s113b_E n) {a0 : ℕ → ℝ} {a1 : ℕ → ℝ}
    {a2 : ℕ → s113b_E n →L[ℝ] ℝ} {a3 : ℕ → s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ} {c0 c1 : ℝ}
    {c2 : s113b_E n →L[ℝ] ℝ} {c3 : s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ}
    (h0 : Tendsto a0 atTop (𝓝 c0)) (h1 : Tendsto a1 atTop (𝓝 c1)) (h2 : Tendsto a2 atTop (𝓝 c2))
    (h3 : Tendsto a3 atTop (𝓝 c3)) :
    Tendsto (fun k => s113q_Nf ν b (a0 k) (a1 k) (a2 k) (a3 k) x) atTop (𝓝 (s113q_Nf ν b c0 c1 c2 c3 x)) := by
  unfold s113q_Nf
  have ap : ∀ {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] {A : ℕ → s113b_E n →L[ℝ] F} {A0 : s113b_E n →L[ℝ] F},
      Tendsto A atTop (𝓝 A0) → ∀ v : s113b_E n, Tendsto (fun k => A k v) atTop (𝓝 (A0 v)) :=
    fun {F} _ _ {A} {A0} h v => ((ContinuousLinearMap.apply ℝ F v).continuous.tendsto A0).comp h
  refine ((tendsto_const_nhds.mul (tendsto_finsetSum _ fun k _ => ?_)).sub
    (tendsto_finsetSum _ fun k _ => ?_)).sub h1
  · exact ap (ap h3 (EuclideanSpace.single k 1)) (EuclideanSpace.single k 1)
  · exact (h0.mul_const _).add (tendsto_const_nhds.mul (ap h2 (EuclideanSpace.single k 1)))

/-- A bound for the numerator. -/
theorem s113q_Nf_bound {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (x : s113b_E n) {Cb Cb' : ℝ}
    (hCb : ∀ k : Fin n, |b x k| ≤ Cb) (hCb' : ∀ k : Fin n, |fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1)| ≤ Cb')
    (a0 a1 : ℝ) (a2 : s113b_E n →L[ℝ] ℝ) (a3 : s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ) :
    |s113q_Nf ν b a0 a1 a2 a3 x| ≤ |ν| * (n * ‖a3‖) + (n * (|a0| * Cb' + Cb * ‖a2‖)) + |a1| := by
  have e1 : ∀ k : Fin n, |a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| ≤ ‖a3‖ := fun k => by
    rw [← Real.norm_eq_abs]
    calc ‖a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)‖
        ≤ ‖a3 (EuclideanSpace.single k 1)‖ * ‖(EuclideanSpace.single k 1 : s113b_E n)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖a3‖ * ‖(EuclideanSpace.single k 1 : s113b_E n)‖) * ‖(EuclideanSpace.single k 1 : s113b_E n)‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖a3‖ := by simp
  have e2 : ∀ k : Fin n, |a2 (EuclideanSpace.single k 1)| ≤ ‖a2‖ := fun k => by
    rw [← Real.norm_eq_abs]
    calc ‖a2 (EuclideanSpace.single k 1)‖ ≤ ‖a2‖ * ‖(EuclideanSpace.single k 1 : s113b_E n)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖a2‖ := by simp
  unfold s113q_Nf
  have s1 : |∑ k : Fin n, a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| ≤ n * ‖a3‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ k : Fin n, |a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| ≤ ∑ _k : Fin n, ‖a3‖ :=
            Finset.sum_le_sum fun k _ => e1 k
        _ = n * ‖a3‖ := by simp)
  have s2 : |∑ k : Fin n, (a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) +
      b x k * a2 (EuclideanSpace.single k 1))| ≤ n * (|a0| * Cb' + Cb * ‖a2‖) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ k : Fin n, |a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) + b x k * a2 (EuclideanSpace.single k 1)|
          ≤ ∑ _k : Fin n, (|a0| * Cb' + Cb * ‖a2‖) := Finset.sum_le_sum fun k _ => by
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCb' k) (abs_nonneg _)
            · rw [abs_mul]
              exact mul_le_mul (hCb k) (e2 k) (abs_nonneg _) ((abs_nonneg _).trans (hCb k))
        _ = n * (|a0| * Cb' + Cb * ‖a2‖) := by simp; ring)
  calc |ν * ∑ k : Fin n, a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) -
        ∑ k : Fin n, (a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) + b x k * a2 (EuclideanSpace.single k 1)) - a1|
      ≤ |ν * ∑ k : Fin n, a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| +
        |∑ k : Fin n, (a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) + b x k * a2 (EuclideanSpace.single k 1))| + |a1| := by
        have h1 := abs_sub (ν * ∑ k : Fin n, a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) -
          ∑ k : Fin n, (a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) + b x k * a2 (EuclideanSpace.single k 1))) a1
        have h2 := abs_sub (ν * ∑ k : Fin n, a3 (EuclideanSpace.single k 1) (EuclideanSpace.single k 1))
          (∑ k : Fin n, (a0 * fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) + b x k * a2 (EuclideanSpace.single k 1)))
        linarith
    _ ≤ _ := by
        rw [abs_mul]
        gcongr

/-- Uniform bounds for the Steklov averages on a compact set. -/
theorem s113q_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {Q : ℝ × E → ℝ}
    {d1 : ℝ × E → ℝ} {d2 : ℝ × E → E →L[ℝ] ℝ} {d3 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hd : s113q_C12Data Q d1 d2 d3) {C : Set (ℝ × E)} (hC : IsCompact C) (hpos : ∀ z ∈ C, 0 < Q z) :
    ∃ (qmin CQ C1 C2 C3 : ℝ) (k0 : ℕ), 0 < qmin ∧ (∀ z ∈ C, qmin ≤ Q z) ∧ ∀ k, k0 ≤ k → ∀ z ∈ C,
      qmin / 2 ≤ s113q_S (s113q_eta k) Q z ∧ |s113q_S (s113q_eta k) Q z| ≤ CQ ∧ |s113q_S (s113q_eta k) d1 z| ≤ C1 ∧
      ‖s113q_S (s113q_eta k) d2 z‖ ≤ C2 ∧ ‖s113q_S (s113q_eta k) d3 z‖ ≤ C3 := by
  obtain ⟨qmin, hqmin, hle⟩ := hC.exists_forall_le' (a := 0) hd.cQ.continuousOn hpos
  obtain ⟨b0, hb0⟩ := hC.exists_bound_of_continuousOn hd.cQ.continuousOn
  obtain ⟨b1, hb1⟩ := hC.exists_bound_of_continuousOn hd.c1.continuousOn
  obtain ⟨b2, hb2⟩ := hC.exists_bound_of_continuousOn (f := d2) hd.c2.continuousOn
  obtain ⟨b3, hb3⟩ := hC.exists_bound_of_continuousOn (f := d3) hd.c3.continuousOn
  obtain ⟨k0, hk0⟩ := s113q_S_tendsto_unif' hd.cQ hC (qmin / 2) (half_pos hqmin)
  obtain ⟨k1, hk1⟩ := s113q_S_tendsto_unif' hd.c1 hC 1 one_pos
  obtain ⟨k2, hk2⟩ := s113q_S_tendsto_unif' (W := E →L[ℝ] ℝ) hd.c2 hC 1 one_pos
  obtain ⟨k3, hk3⟩ := s113q_S_tendsto_unif' (W := E →L[ℝ] E →L[ℝ] ℝ) hd.c3 hC 1 one_pos
  refine ⟨qmin, b0 + qmin / 2, b1 + 1, b2 + 1, b3 + 1, max (max k0 k1) (max k2 k3), hqmin, hle, fun k hk z hz => ?_⟩
  have e0 : k0 ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hk)
  have e1 : k1 ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hk)
  have e2 : k2 ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hk)
  have e3 : k3 ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hk)
  have h0 := hk0 k e0 z hz
  have h1 := hk1 k e1 z hz
  have h2 := hk2 k e2 z hz
  have h3 := hk3 k e3 z hz
  have n0 := norm_sub_norm_le (s113q_S (s113q_eta k) Q z) (Q z)
  have n1 := norm_sub_norm_le (s113q_S (s113q_eta k) d1 z) (d1 z)
  have n2 := norm_sub_norm_le (s113q_S (s113q_eta k) d2 z) (d2 z)
  have n3 := norm_sub_norm_le (s113q_S (s113q_eta k) d3 z) (d3 z)
  have c0 := hb0 z hz
  have c1 := hb1 z hz
  have c2 := hb2 z hz
  have c3 := hb3 z hz
  have m0 := hle z hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (abs_le.1 (by simpa [Real.norm_eq_abs] using h0 : |s113q_S (s113q_eta k) Q z - Q z| ≤ qmin / 2)).1
    linarith
  · simp only [Real.norm_eq_abs] at n0 c0 h0 ⊢
    linarith
  · simp only [Real.norm_eq_abs] at n1 c1 h1 ⊢
    linarith
  · linarith
  · linarith

/-- Dominated convergence for integrands supported in a compact set. -/
theorem s113q_dct_K {n : ℕ} {K : Set (s113b_E n)} (hK : IsCompact K) {F : ℕ → s113b_E n → ℝ} {f : s113b_E n → ℝ}
    {C : ℝ} {k0 : ℕ} (hm : ∀ k, AEStronglyMeasurable (F k) volume)
    (hb : ∀ k, k0 ≤ k → ∀ x, ‖F k x‖ ≤ K.indicator (fun _ => C) x)
    (hl : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (f x))) :
    Tendsto (fun k => ∫ x, F k x) atTop (𝓝 (∫ x, f x)) ∧ ∀ k, k0 ≤ k → |∫ x, F k x| ≤ C * (volume K).toReal := by
  have hi : Integrable (K.indicator fun _ => C) (volume : Measure (s113b_E n)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  refine ⟨?_, fun k hk => ?_⟩
  · have := tendsto_integral_of_dominated_convergence (μ := volume) (F := fun k x => F (k + k0) x) (f := f)
      (K.indicator fun _ => C) (fun k => hm _) hi (fun k => ae_of_all _ (hb (k + k0) (Nat.le_add_left _ _)))
      (ae_of_all _ fun x => (hl x).comp (tendsto_add_atTop_nat k0))
    exact (tendsto_add_atTop_iff_nat k0).1 this
  · have := norm_integral_le_of_norm_le hi (ae_of_all _ (hb k hk))
    rwa [integral_indicator_const _ hK.measurableSet, Real.norm_eq_abs, smul_eq_mul, mul_comm] at this

/-- Bounds on a compact set for the coefficients of the drift. -/
theorem s113q_bcoef {n : ℕ} {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 2 b) {K : Set (s113b_E n)} (hK : IsCompact K) :
    ∃ Cb Cb' : ℝ, (∀ x ∈ K, ∀ k : Fin n, |b x k| ≤ Cb) ∧
      ∀ x ∈ K, ∀ k : Fin n, |fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1)| ≤ Cb' := by
  have hbk : ∀ k : Fin n, ContDiff ℝ 2 (fun y : s113b_E n => b y k) := fun k =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hb
  have c1 : Continuous fun x => ∑ k : Fin n, |b x k| :=
    continuous_finsetSum _ fun k _ => ((hbk k).continuous).abs
  have c2 : Continuous fun x => ∑ k : Fin n, |fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1)| :=
    continuous_finsetSum _ fun k _ =>
      (((hbk k).continuous_fderiv (by norm_num)).clm_apply continuous_const).abs
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨Cb', hCb'⟩ := hK.exists_bound_of_continuousOn c2.continuousOn
  refine ⟨Cb, Cb', fun x hx k => ?_, fun x hx k => ?_⟩
  · refine le_trans (Finset.single_le_sum (f := fun k : Fin n => |b x k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)) ?_
    have := hCb x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at this
    exact this
  · refine le_trans (Finset.single_le_sum
      (f := fun k : Fin n => |fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1)|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k)) ?_
    have := hCb' x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at this
    exact this

section Main

variable {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
  {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ}

/-- The Steklov regularization `q_k = S_{1/(k+2)} q`. -/
def s113q_qk (q : ℝ → s113b_E n → ℝ) (k : ℕ) (t : ℝ) (x : s113b_E n) : ℝ :=
  s113q_S (s113q_eta k) (fun z : ℝ × s113b_E n => q z.1 z.2) (t, x)

theorem s113q_Data_k (hD : s113q_Data ν b q T u K G B) (k : ℕ) :
    s113b_Data ν b (s113q_qk q k) T u K G B := by
  obtain ⟨d1, d2, d3, hd⟩ := hD.hq
  refine ⟨hD.hν, hD.hb, (hd.steklov (s113q_eta k)).1, fun t ht x => ?_, hD.hKc, hD.hG, hD.hKG, hD.hKu,
    hD.hu0, hD.huB, hD.hum, hD.sub⟩
  exact s113q_S_pos hd.cQ (s113q_eta_pos k) (s113q_eta_le_one k) (fun t ht x => hD.hq0 t ht x) ht x

theorem s113q_qk_pos (hD : s113q_Data ν b q T u K G B) (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : s113b_E n) :
    0 < s113q_qk q k t x := (s113q_Data_k hD k).hq0 t ht x

theorem s113q_qk_tendsto (hD : s113q_Data ν b q T u K G B) (t : ℝ) (x : s113b_E n) :
    Tendsto (fun k => s113q_qk q k t x) atTop (𝓝 (q t x)) := by
  obtain ⟨d1, d2, d3, hd⟩ := hD.hq
  exact s113q_S_tendsto_pt hd.cQ (t, x)

theorem s113q_qk_cont (hD : s113q_Data ν b q T u K G B) (k : ℕ) (t : ℝ) :
    Continuous (s113q_qk q k t) := by
  obtain ⟨d1, d2, d3, hd⟩ := hD.hq
  exact (s113q_S_continuous hd.cQ _).comp (continuous_const.prodMk continuous_id)

/-- Convergence of the power mass `M_k(t) → M(t)`. -/
theorem s113q_M_tendsto (hD : s113q_Data ν b q T u K G B) {p : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hpt : 0 < p t) :
    Tendsto (fun k => s113b_M (s113q_qk q k) u p t) atTop (𝓝 (s113b_M q u p t)) := by
  obtain ⟨d1, d2, d3, hd⟩ := hD.hq
  have hS : IsCompact (({t} : Set ℝ) ×ˢ K) := isCompact_singleton.prod hD.hKc
  obtain ⟨qmin, hqmin, hle⟩ := hS.exists_forall_le' (a := 0) (f := fun z : ℝ × s113b_E n => q z.1 z.2)
    hd.cQ.continuousOn (fun z hz => by
      obtain ⟨h1, -⟩ := hz
      rw [mem_singleton_iff] at h1
      rw [h1]
      exact hD.hq0 t ⟨ht.1, by linarith [ht.2]⟩ z.2)
  obtain ⟨CQ0, hCQ0⟩ := hS.exists_bound_of_continuousOn hd.cQ.continuousOn
  obtain ⟨k0, hk0⟩ := s113q_S_tendsto_unif' hd.cQ hS (min (qmin / 2) 1) (lt_min (half_pos hqmin) one_pos)
  set Z : ℝ := B / (qmin / 2) with hZ
  set F : ℕ → s113b_E n → ℝ := fun k x => s113q_qk q k t x * (u t x / s113q_qk q k t x) ^ (p t) with hF
  have hmem : ∀ x ∈ K, (t, x) ∈ ({t} : Set ℝ) ×ˢ K := fun x hx => ⟨rfl, hx⟩
  have hlow : ∀ k, k0 ≤ k → ∀ x ∈ K, qmin / 2 ≤ s113q_qk q k t x ∧ s113q_qk q k t x ≤ max CQ0 0 + 1 := by
    intro k hk x hx
    have h1 := hk0 k hk (t, x) (hmem x hx)
    have h2 := hle (t, x) (hmem x hx)
    have h3 := hCQ0 (t, x) (hmem x hx)
    have h4 := abs_le.1 (h1.trans (min_le_right _ _) |> fun h => by simpa [Real.norm_eq_abs] using h)
    have h5 := (h1.trans (min_le_left _ _))
    simp only [Real.norm_eq_abs] at h5 h3
    have h6 := abs_le.1 h5
    simp only [s113q_qk]
    constructor
    · linarith [h6.1]
    · linarith [h4.2, le_abs_self (q t x), le_max_left CQ0 0]
  have hbd : ∀ k, k0 ≤ k → ∀ x, ‖F k x‖ ≤ K.indicator (fun _ => (max CQ0 0 + 1) * (Z + 1) ^ (p t)) x := by
    intro k hk x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      obtain ⟨hl, hu⟩ := hlow k hk x hx
      have hqp : 0 < s113q_qk q k t x := lt_of_lt_of_le (half_pos hqmin) hl
      have hr0 : 0 ≤ u t x / s113q_qk q k t x := div_nonneg (hD.hu0 t x) hqp.le
      have hr1 : u t x / s113q_qk q k t x ≤ Z := by
        refine (div_le_div₀ (by linarith [hD.hu0 t x, hD.huB t ht x]) (hD.huB t ht x) (half_pos hqmin) hl)
      simp only [hF]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hqp.le (Real.rpow_nonneg hr0 _))]
      exact mul_le_mul hu (Real.rpow_le_rpow hr0 (hr1.trans (by linarith)) hpt.le) (Real.rpow_nonneg hr0 _)
        (by positivity)
    · rw [indicator_of_notMem hx]
      simp [hF, hD.hKu t x hx, Real.zero_rpow hpt.ne']
  have hlim : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (q t x * (u t x / q t x) ^ (p t))) := by
    intro x
    have h1 := s113q_qk_tendsto hD t x
    have hq0 : q t x ≠ 0 := (hD.hq0 t ⟨ht.1, by linarith [ht.2]⟩ x).ne'
    exact h1.mul ((tendsto_const_nhds.div h1 hq0).rpow_const (Or.inr hpt.le))
  have hmeasF : ∀ k, AEStronglyMeasurable (F k) volume := by
    intro k
    have hu : Measurable (u t) := hD.hum.comp measurable_prodMk_left
    exact ((s113q_qk_cont hD k t).measurable.mul
      ((hu.div (s113q_qk_cont hD k t).measurable).pow_const _)).aestronglyMeasurable
  have hint : Integrable (K.indicator fun _ => (max CQ0 0 + 1) * (Z + 1) ^ (p t)) :=
    (integrableOn_const hD.hKc.measure_lt_top.ne).integrable_indicator hD.hKc.measurableSet
  have := tendsto_integral_of_dominated_convergence (μ := volume) (F := fun k x => F (k + k0) x)
    (f := fun x => q t x * (u t x / q t x) ^ (p t))
    (K.indicator fun _ => (max CQ0 0 + 1) * (Z + 1) ^ (p t)) (fun k => hmeasF _) hint
    (fun k => ae_of_all _ (hbd (k + k0) (Nat.le_add_left _ _)))
    (ae_of_all _ fun x => (hlim x).comp (tendsto_add_atTop_nat k0))
  exact (tendsto_add_atTop_iff_nat k0).1 this

end Main

end HRS.MS.S113Q

end
