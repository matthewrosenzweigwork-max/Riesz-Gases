import HRS.PDE.ToolboxRd

/-!
# T1 of `UniqPlan.md`: two-multiplier symmetrization identity for a Lévy kernel

For `HRS.PDE.ToolboxRd.IsLevyKernel θ m 𝔨`, `F` Lipschitz with compact support and `p, q` bounded Lipschitz,
`B(p²F, q²F) = B(pqF, pqF) - ½ ∬ 𝔨(h) F(x) F(x-h) (p(x) q(x-h) - p(x-h) q(x))² dx dh`
with `B = symbolForm m`; the integral is over `(x, h) ∈ ℝ^d × ℝ^d`.  No sign or constant defect in
the printed identity.  Regularity assumed: `F` Lipschitz and compactly supported, `p, q` Lipschitz
and bounded (compact support of `p, q` is not needed).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.UniqT1

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.WeightAux HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- Lipschitz + compact support gives `H¹`. -/
theorem t1_memSobolev_one {L : ℝ} {F : Euc d → ℝ} (hF : HRS.PDE.ToolboxRd.IsLipschitz L F)
    (hc : HasCompactSupport F) : HRS.PDE.ToolboxRd.MemSobolev 1 F := by
  have hcont : Continuous F := isLipschitz_continuous hF
  have h2 : MemLp F 2 volume := hcont.memLp_of_hasCompactSupport hc
  set K : Set (Euc d) := tsupport F with hK
  have hKc : IsCompact K := hc
  set g : Euc d → ℝ := K.indicator (fun _ => (1 : ℝ)) with hg
  have hgi : Integrable g volume :=
    (integrable_indicator_iff hKc.measurableSet).2
      (integrableOn_const hKc.measure_lt_top.ne)
  have hgs : ∀ h : Euc d, Integrable (fun x => g (x - h)) volume := fun h =>
    hgi.comp_sub_right h
  refine memSobolev_one_of_diff_bound h2 (L ^ 2 * (2 * ∫ x, g x)) fun h => ?_
  have hpt : ∀ x, (F x - F (x - h)) ^ 2 ≤ (L * ‖h‖) ^ 2 * (g x + g (x - h)) := by
    intro x
    by_cases hx : x ∈ K
    · have hg1 : g x = 1 := by simp [hg, hx]
      have hg2 : 0 ≤ g (x - h) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have h1 : |F x - F (x - h)| ≤ L * ‖h‖ := by simpa using hF x (x - h)
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      rw [hg1]; nlinarith [sq_nonneg (L * ‖h‖)]
    · by_cases hy : x - h ∈ K
      · have hg1 : g (x - h) = 1 := by simp [hg, hy]
        have hg2 : 0 ≤ g x := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have h1 : |F x - F (x - h)| ≤ L * ‖h‖ := by simpa using hF x (x - h)
        have := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [sq_abs] at this
        rw [hg1]; nlinarith [sq_nonneg (L * ‖h‖)]
      · have e1 : F x = 0 := image_eq_zero_of_notMem_tsupport hx
        have e2 : F (x - h) = 0 := image_eq_zero_of_notMem_tsupport hy
        rw [e1, e2]
        have h1 : 0 ≤ g x := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have h2 : 0 ≤ g (x - h) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
  have hint : Integrable (fun x => (F x - F (x - h)) ^ 2) volume :=
    (h2.sub (memLp_translate h2 h)).integrable_sq
  calc ∫ x, (F x - F (x - h)) ^ 2
      ≤ ∫ x, (L * ‖h‖) ^ 2 * (g x + g (x - h)) :=
        integral_mono hint ((hgi.add (hgs h)).const_mul _) hpt
    _ = (L * ‖h‖) ^ 2 * (2 * ∫ x, g x) := by
        rw [integral_const_mul, integral_add hgi (hgs h), integral_sub_right_eq_self g h]; ring
    _ = L ^ 2 * (2 * ∫ x, g x) * ‖h‖ ^ 2 := by ring

/-- Product of a bounded Lipschitz function with `F` is Lipschitz and `H¹`. -/
theorem t1_good {LF Lb Bb : ℝ} {F b : Euc d → ℝ} (hF : HRS.PDE.ToolboxRd.IsLipschitz LF F)
    (hc : HasCompactSupport F) (hb : HRS.PDE.ToolboxRd.IsLipschitz Lb b) (hBb : ∀ x, |b x| ≤ Bb) :
    ∃ L, HRS.PDE.ToolboxRd.IsLipschitz L (fun x => b x * F x) ∧ HRS.PDE.ToolboxRd.MemSobolev 1 (fun x => b x * F x) := by
  obtain ⟨BF, hBF⟩ : ∃ B : ℝ, ∀ x, |F x| ≤ B := by
    obtain ⟨C, hC⟩ := (isLipschitz_continuous hF).bounded_above_of_compact_support hc
    exact ⟨C, hC⟩
  exact ⟨_, isLipschitz_mul hb hF hBb hBF,
    memSobolev_one_mul hb ⟨Bb, hBb⟩ (t1_memSobolev_one hF hc)⟩

/-- Product of two bounded Lipschitz functions. -/
theorem t1_prod {Lp Lq Bp Bq : ℝ} {p q : Euc d → ℝ} (hp : HRS.PDE.ToolboxRd.IsLipschitz Lp p)
    (hq : HRS.PDE.ToolboxRd.IsLipschitz Lq q) (hBp : ∀ x, |p x| ≤ Bp) (hBq : ∀ x, |q x| ≤ Bq) :
    ∃ L B, HRS.PDE.ToolboxRd.IsLipschitz L (fun x => p x * q x) ∧ ∀ x, |p x * q x| ≤ B :=
  ⟨_, Bp * Bq, isLipschitz_mul hp hq hBp hBq, fun x => by
    rw [abs_mul]; exact mul_le_mul (hBp x) (hBq x) (abs_nonneg _) ((abs_nonneg _).trans (hBp x))⟩

/-- **T1.** Two-multiplier symmetrization: for a Lévy kernel `𝔨` of the symbol `m`,
`F` Lipschitz with compact support and `p, q` bounded Lipschitz,
`B(p²F, q²F) = B(pqF, pqF) - ½ ∬ 𝔨(h) F(x) F(x-h) (p(x) q(x-h) - p(x-h) q(x))² d(x,h)`. -/
theorem symmetrization {θ : ℝ} {m 𝔨 : Euc d → ℝ} (h𝔨 : HRS.PDE.ToolboxRd.IsLevyKernel θ m 𝔨)
    {LF Lp Lq Bp Bq : ℝ} {F p q : Euc d → ℝ} (hF : HRS.PDE.ToolboxRd.IsLipschitz LF F)
    (hFc : HasCompactSupport F) (hp : HRS.PDE.ToolboxRd.IsLipschitz Lp p) (hq : HRS.PDE.ToolboxRd.IsLipschitz Lq q)
    (hBp : ∀ x, |p x| ≤ Bp) (hBq : ∀ x, |q x| ≤ Bq) :
    symbolForm m (fun x => p x ^ 2 * F x) (fun x => q x ^ 2 * F x) =
      symbolForm m (fun x => p x * q x * F x) (fun x => p x * q x * F x) -
        (1 / 2) * ∫ z : Euc d × Euc d, 𝔨 z.2 * F z.1 * F (z.1 - z.2) *
          (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2 := by
  obtain ⟨Lpp, Bpp, hpp, hBpp⟩ := t1_prod hp hp hBp hBp
  obtain ⟨Lqq, Bqq, hqq, hBqq⟩ := t1_prod hq hq hBq hBq
  obtain ⟨Lpq, Bpq, hpq, hBpq⟩ := t1_prod hp hq hBp hBq
  obtain ⟨La, hLa, hHa⟩ := t1_good hF hFc hpp hBpp
  obtain ⟨Lb, hLb, hHb⟩ := t1_good hF hFc hqq hBqq
  obtain ⟨Lc, hLc, hHc⟩ := t1_good hF hFc hpq hBpq
  have ea : (fun x => p x ^ 2 * F x) = fun x => p x * p x * F x := by funext x; ring
  have eb : (fun x => q x ^ 2 * F x) = fun x => q x * q x * F x := by funext x; ring
  rw [ea, eb]
  obtain ⟨I1, E1⟩ := h𝔨.bilinear La Lb _ _ hLa hLb hHa hHb
  obtain ⟨I2, E2⟩ := h𝔨.bilinear Lc Lc _ _ hLc hLc hHc hHc
  rw [E1, E2]
  have key : ∀ z : Euc d × Euc d,
      𝔨 z.2 * (p z.1 * p z.1 * F z.1 - p (z.1 - z.2) * p (z.1 - z.2) * F (z.1 - z.2)) *
          (q z.1 * q z.1 * F z.1 - q (z.1 - z.2) * q (z.1 - z.2) * F (z.1 - z.2)) -
        𝔨 z.2 * (p z.1 * q z.1 * F z.1 - p (z.1 - z.2) * q (z.1 - z.2) * F (z.1 - z.2)) *
          (p z.1 * q z.1 * F z.1 - p (z.1 - z.2) * q (z.1 - z.2) * F (z.1 - z.2)) =
      -(𝔨 z.2 * F z.1 * F (z.1 - z.2) *
          (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2) := fun z => by ring
  have hsub := integral_sub I1 I2
  simp only [key, integral_neg] at hsub
  linarith

end HRS.MS.UniqT1
