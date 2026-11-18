import HRS.PDE.ForwardEq
import HRS.Analysis.Category

/-!
# Appendix C helper lemmas: quadratic forms of homogeneous symbols (Lemma C.3 (i), (v))

Auxiliary results for `HRS/PDE/Toolbox.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Coefficient form of the Sobolev norm (no upstream `sorry`) -/

/-- The complex coefficient `coeffOf` is the `fcoef` of `HRS/Torus/Sobolev.lean`. -/
theorem coeffOf_eq_fcoefC (φ : Torus d → ℝ) (k : Lattice d) : coeffOf φ k = Torus.fcoef φ k := by
  unfold coeffOf Torus.funFourierCoeff UnitAddTorus.mFourierCoeff Torus.fcoef
  have hm : (@volume (UnitAddTorus (Fin d))
      (@MeasureSpace.pi (Fin d) _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) =
      (volume : Measure (Torus d)) := by
    show Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hm]
  simp [smul_eq_mul, Torus.mode]

/-- For `u ∈ H^m`: `∑_k ⟨k⟩^{2m} |û(k)|²` converges and equals `‖u‖²_{H^m}`. -/
theorem memSobolev_coeff (m : ℝ) {u : Torus d → ℝ} (hu : MemSobolev m u) :
    Summable (fun k : Lattice d => Lattice.jp k ^ (2 * m) * ‖coeffOf u k‖ ^ 2) ∧
      ∑' k : Lattice d, Lattice.jp k ^ (2 * m) * ‖coeffOf u k‖ ^ 2 = sobolevNorm m u ^ 2 := by
  obtain ⟨hL2, hs⟩ := hu
  have hint : Integrable u := hL2.integrable one_le_two
  obtain ⟨h1, h2⟩ := Torus.weighted_fcoef_sq (2 * m) hint hs
  have hsum : Summable (fun k : Lattice d => Lattice.jp k ^ (2 * m) * ‖Torus.fcoef u k‖ ^ 2) :=
    (Torus.summable_lattice_iff _).mpr h1
  simp only [coeffOf_eq_fcoefC]
  refine ⟨hsum, ?_⟩
  rw [Torus.tsum_lattice _ hsum]
  have h0 : Lattice.jp (0 : Lattice d) ^ (2 * m) * ‖Torus.fcoef u 0‖ ^ 2 = Torus.mean u ^ 2 := by
    rw [Torus.jp_zero, Real.one_rpow, one_mul, Torus.fcoef_zero]
    simp
  show _ = Real.sqrt _ ^ 2
  rw [Real.sq_sqrt]
  · rw [h0, h2]
  · exact add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))

/-! ### The symbol bound `0 ≤ 𝔪(k) ≤ A ⟨k⟩^θ` -/

theorem toEuc_ne_zero {k : Lattice d} (hk : k ≠ 0) : Lattice.toEuc k ≠ 0 := by
  intro h
  apply hk
  funext i
  have := congrArg (fun x : Euc d => x i) h
  simpa [Lattice.toEuc] using this

theorem symbol_bound (θ : ℝ) (hθ : 0 < θ) (𝔪 : Lattice d → ℝ) (m₀ : Euc d → ℝ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ {ξ | ξ ≠ 0})
    (hnn : ∀ ξ, 0 ≤ m₀ ξ) (hhom : ∀ c : ℝ, 0 < c → ∀ ξ, m₀ (c • ξ) = c ^ θ * m₀ ξ)
    (hext : ∀ k : Lattice d, k ≠ 0 → 𝔪 k = m₀ (Lattice.toEuc k)) (hzero : 𝔪 0 = 0) :
    ∃ A : ℝ, ∀ k : Lattice d, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ := by
  have hcont : ContinuousOn m₀ (Metric.sphere (0 : Euc d) 1) := by
    refine hsm.continuousOn.mono ?_
    intro x hx h0
    simp [h0] at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euc d) 1).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    rw [hzero]
    exact ⟨le_rfl, mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (Torus.jp_pos _).le _)⟩
  · rw [hext k hk]
    refine ⟨hnn _, ?_⟩
    set ξ := Lattice.toEuc k with hξ
    have hξ0 : ξ ≠ 0 := toEuc_ne_zero hk
    have hc : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
    have hsph : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : Euc d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
    have h1 : m₀ ξ = ‖ξ‖ ^ θ * m₀ (‖ξ‖⁻¹ • ξ) := by
      rw [← hhom _ hc, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have h2 : m₀ (‖ξ‖⁻¹ • ξ) ≤ max C 0 :=
      (le_abs_self _).trans ((by simpa [abs_of_nonneg (hnn _)] using hC _ hsph : |m₀ _| ≤ C).trans (le_max_left _ _))
    have h3 : ‖ξ‖ ^ θ ≤ Lattice.jp k ^ θ :=
      Real.rpow_le_rpow hc.le (enorm_le_jp k) hθ.le
    calc m₀ ξ = ‖ξ‖ ^ θ * m₀ (‖ξ‖⁻¹ • ξ) := h1
      _ ≤ ‖ξ‖ ^ θ * max C 0 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hc.le _)
      _ ≤ Lattice.jp k ^ θ * max C 0 :=
          mul_le_mul_of_nonneg_right h3 (le_max_right _ _)
      _ = max C 0 * Lattice.jp k ^ θ := mul_comm _ _

/-! ### The form `∑ 𝔪 f \bar g` for a dominated symbol -/

section Form

variable (𝔪 : Lattice d → ℝ) (A θ : ℝ) (f g : Coeff d)

theorem form_summable_sq (hA : ∀ k, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ)
    (hf : Summable fun k => Lattice.jp k ^ θ * ‖f k‖ ^ 2) :
    Summable fun k => 𝔪 k * ‖f k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (hA k).1 (sq_nonneg _))
    (fun k => by
      calc 𝔪 k * ‖f k‖ ^ 2 ≤ (A * Lattice.jp k ^ θ) * ‖f k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hA k).2 (sq_nonneg _)
        _ = A * (Lattice.jp k ^ θ * ‖f k‖ ^ 2) := by ring)
    (hf.mul_left A)

theorem form_summable (hA : ∀ k, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ)
    (hf : Summable fun k => Lattice.jp k ^ θ * ‖f k‖ ^ 2)
    (hg : Summable fun k => Lattice.jp k ^ θ * ‖g k‖ ^ 2) :
    Summable fun k => ((𝔪 k : ℝ) : ℂ) * (f k * conj (g k)) := by
  have h1 := form_summable_sq 𝔪 A θ f hA hf
  have h2 := form_summable_sq 𝔪 A θ g hA hg
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun k => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hA k).1]
  have := (hA k).1
  nlinarith [sq_nonneg (‖f k‖ - ‖g k‖), mul_nonneg this (sq_nonneg (‖f k‖ - ‖g k‖))]

theorem form_symm :
    (bilinForm 𝔪 f g).re = (bilinForm 𝔪 g f).re := by
  have : bilinForm 𝔪 g f = conj (bilinForm 𝔪 f g) := by
    unfold bilinForm
    rw [Complex.conj_tsum]
    refine tsum_congr fun k => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [this, Complex.conj_re]

theorem form_self :
    bilinForm 𝔪 f f = ((∑' k, 𝔪 k * ‖f k‖ ^ 2 : ℝ) : ℂ) := by
  unfold bilinForm
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem form_self_nonneg (hA : ∀ k, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ) :
    0 ≤ (bilinForm 𝔪 f f).re := by
  rw [form_self 𝔪 f, Complex.ofReal_re]
  exact tsum_nonneg fun k => mul_nonneg (hA k).1 (sq_nonneg _)

theorem form_self_le (hA : ∀ k, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ)
    (hf : Summable fun k => Lattice.jp k ^ θ * ‖f k‖ ^ 2) :
    (bilinForm 𝔪 f f).re ≤ A * ∑' k, Lattice.jp k ^ θ * ‖f k‖ ^ 2 := by
  rw [form_self 𝔪 f, Complex.ofReal_re, ← tsum_mul_left]
  refine (form_summable_sq 𝔪 A θ f hA hf).tsum_le_tsum (fun k => ?_) (hf.mul_left A)
  calc 𝔪 k * ‖f k‖ ^ 2 ≤ (A * Lattice.jp k ^ θ) * ‖f k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hA k).2 (sq_nonneg _)
    _ = A * (Lattice.jp k ^ θ * ‖f k‖ ^ 2) := by ring

theorem form_cs (hA : ∀ k, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ)
    (hf : Summable fun k => Lattice.jp k ^ θ * ‖f k‖ ^ 2)
    (hg : Summable fun k => Lattice.jp k ^ θ * ‖g k‖ ^ 2) :
    |(bilinForm 𝔪 f g).re| ≤
      Real.sqrt (bilinForm 𝔪 f f).re * Real.sqrt (bilinForm 𝔪 g g).re := by
  have h1 := form_summable_sq 𝔪 A θ f hA hf
  have h2 := form_summable_sq 𝔪 A θ g hA hg
  set a : Lattice d → ℝ := fun k => Real.sqrt (𝔪 k) * ‖f k‖ with ha
  set b : Lattice d → ℝ := fun k => Real.sqrt (𝔪 k) * ‖g k‖ with hb
  have hsa : ∀ k, a k ^ 2 = 𝔪 k * ‖f k‖ ^ 2 := fun k => by
    simp only [ha, mul_pow, Real.sq_sqrt (hA k).1]
  have hsb : ∀ k, b k ^ 2 = 𝔪 k * ‖g k‖ ^ 2 := fun k => by
    simp only [hb, mul_pow, Real.sq_sqrt (hA k).1]
  have ha2 : Summable fun k => a k ^ 2 := by simpa only [hsa] using h1
  have hb2 : Summable fun k => b k ^ 2 := by simpa only [hsb] using h2
  obtain ⟨hab, hcs⟩ := Torus.cs_tsum a b (fun k => by positivity) (fun k => by positivity) ha2 hb2
  have hterm : ∀ k, ‖((𝔪 k : ℝ) : ℂ) * (f k * conj (g k))‖ = a k * b k := fun k => by
    simp only [ha, hb]
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hA k).1]
    rw [show √(𝔪 k) * ‖f k‖ * (√(𝔪 k) * ‖g k‖) = (√(𝔪 k) * √(𝔪 k)) * (‖f k‖ * ‖g k‖) by ring,
      Real.mul_self_sqrt (hA k).1]
  have hnorm : Summable fun k => ‖((𝔪 k : ℝ) : ℂ) * (f k * conj (g k))‖ := by
    simpa only [hterm] using hab
  have hlhs : |(bilinForm 𝔪 f g).re| ≤ ∑' k, a k * b k := by
    calc |(bilinForm 𝔪 f g).re| ≤ ‖bilinForm 𝔪 f g‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' k, ‖((𝔪 k : ℝ) : ℂ) * (f k * conj (g k))‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' k, a k * b k := tsum_congr hterm
  have e1 : (bilinForm 𝔪 f f).re = ∑' k, a k ^ 2 := by
    rw [form_self 𝔪 f, Complex.ofReal_re]; exact tsum_congr fun k => (hsa k).symm
  have e2 : (bilinForm 𝔪 g g).re = ∑' k, b k ^ 2 := by
    rw [form_self 𝔪 g, Complex.ofReal_re]; exact tsum_congr fun k => (hsb k).symm
  rw [e1, e2]
  exact hlhs.trans hcs

end Form

/-- The set of facts of Lemma C.3(i) and (v) for a symbol dominated by `A ⟨k⟩^θ`, `θ = 2 m`. -/
theorem quad_core (θ : ℝ) (𝔪 : Lattice d → ℝ) (A : ℝ)
    (hA : ∀ k, 0 ≤ 𝔪 k ∧ 𝔪 k ≤ A * Lattice.jp k ^ θ) (u v : Torus d → ℝ)
    (hu : MemSobolev (θ / 2) u) (hv : MemSobolev (θ / 2) v) :
    Summable (fun k => 𝔪 k * ‖coeffOf u k‖ ^ 2) ∧ Summable (fun k => 𝔪 k * ‖coeffOf v k‖ ^ 2) ∧
      Summable (fun k => ((𝔪 k : ℝ) : ℂ) * (coeffOf u k * conj (coeffOf v k))) ∧
      (bilinForm 𝔪 (coeffOf u) (coeffOf v)).re = (bilinForm 𝔪 (coeffOf v) (coeffOf u)).re ∧
      0 ≤ (bilinForm 𝔪 (coeffOf u) (coeffOf u)).re ∧
      (bilinForm 𝔪 (coeffOf u) (coeffOf u)).re ≤ A * sobolevNorm (θ / 2) u ^ 2 ∧
      |(bilinForm 𝔪 (coeffOf u) (coeffOf v)).re| ≤
        Real.sqrt (bilinForm 𝔪 (coeffOf u) (coeffOf u)).re *
          Real.sqrt (bilinForm 𝔪 (coeffOf v) (coeffOf v)).re := by
  have e : 2 * (θ / 2) = θ := by ring
  obtain ⟨hf, hfs⟩ := memSobolev_coeff (θ / 2) hu
  obtain ⟨hg, -⟩ := memSobolev_coeff (θ / 2) hv
  rw [e] at hf hfs hg
  refine ⟨form_summable_sq 𝔪 A θ _ hA hf, form_summable_sq 𝔪 A θ _ hA hg,
    form_summable 𝔪 A θ _ _ hA hf hg, form_symm 𝔪 _ _,
    form_self_nonneg 𝔪 A θ _ hA, ?_, form_cs 𝔪 A θ _ _ hA hf hg⟩
  rw [← hfs]
  exact form_self_le 𝔪 A θ _ hA hf

end HRS.PDE
