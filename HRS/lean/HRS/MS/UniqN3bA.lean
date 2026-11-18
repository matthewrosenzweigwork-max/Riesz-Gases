import HRS.MS.UniqT1

/-!
# N3b, part A: `H¹` membership of `p²F` and the two-multiplier identity without compact support of `p²F`

* `n3b_memSobolev_p2F`: `p` bounded Lipschitz with `p² ∈ L¹`, `F` bounded Lipschitz give `p²F ∈ H¹`.
* `n3b_symm`: the identity of `UniqT1.symmetrization` with the hypotheses `Lipschitz` and `MemSobolev 1`
  of the three functions `p²F`, `q²F`, `pqF` instead of compact support of `F`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.UniqN3b

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.WeightAux HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- Pointwise algebra for the difference of `a² f₁ - b² f₂`. -/
theorem n3b_diff_pt (a b f1 f2 D Lp LF P BF : ℝ) (hab : |a - b| ≤ Lp * D) (hb : |b| ≤ P)
    (hf1 : |f1| ≤ BF) (hf : |f1 - f2| ≤ LF * D) :
    (a ^ 2 * f1 - b ^ 2 * f2) ^ 2 ≤
      D ^ 2 * ((4 * Lp ^ 2 * BF ^ 2) * a ^ 2 + (4 * Lp ^ 2 * BF ^ 2 + 2 * P ^ 2 * LF ^ 2) * b ^ 2) := by
  have e : a ^ 2 * f1 - b ^ 2 * f2 = (a - b) * (a + b) * f1 + b ^ 2 * (f1 - f2) := by ring
  have hXY : ∀ X Y : ℝ, (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := fun X Y => by
    nlinarith [sq_nonneg (X - Y)]
  have hX : ((a - b) * (a + b) * f1) ^ 2 ≤ (Lp * D) ^ 2 * (2 * (a ^ 2 + b ^ 2)) * BF ^ 2 := by
    have h0 : ((a - b) * (a + b) * f1) ^ 2 = (a - b) ^ 2 * (a + b) ^ 2 * f1 ^ 2 := by ring
    have h1 : (a - b) ^ 2 ≤ (Lp * D) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    have h3 : f1 ^ 2 ≤ BF ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hf1 2
    rw [h0]
    gcongr
  have hY : (b ^ 2 * (f1 - f2)) ^ 2 ≤ P ^ 2 * b ^ 2 * (LF * D) ^ 2 := by
    have h0 : (b ^ 2 * (f1 - f2)) ^ 2 = b ^ 2 * b ^ 2 * (f1 - f2) ^ 2 := by ring
    have h1 : b ^ 2 ≤ P ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have h3 : (f1 - f2) ^ 2 ≤ (LF * D) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hf 2
    rw [h0]
    gcongr
  calc (a ^ 2 * f1 - b ^ 2 * f2) ^ 2
      = ((a - b) * (a + b) * f1 + b ^ 2 * (f1 - f2)) ^ 2 := by rw [e]
    _ ≤ 2 * ((a - b) * (a + b) * f1) ^ 2 + 2 * (b ^ 2 * (f1 - f2)) ^ 2 := hXY _ _
    _ ≤ 2 * ((Lp * D) ^ 2 * (2 * (a ^ 2 + b ^ 2)) * BF ^ 2) + 2 * (P ^ 2 * b ^ 2 * (LF * D) ^ 2) := by
        linarith
    _ = _ := by ring

/-- `p²F ∈ H¹` for `p, F` bounded Lipschitz with `p² ∈ L¹`. -/
theorem n3b_memSobolev_p2F {p F : Euc d → ℝ} {P Lp LF BF : ℝ} (hp : HRS.PDE.ToolboxRd.IsLipschitz Lp p)
    (hP : ∀ x, |p x| ≤ P) (hint : Integrable (fun x => p x ^ 2) volume)
    (hF : HRS.PDE.ToolboxRd.IsLipschitz LF F) (hFb : ∀ x, |F x| ≤ BF) :
    HRS.PDE.ToolboxRd.MemSobolev 1 (fun x => p x ^ 2 * F x) := by
  have hpc : Continuous p := isLipschitz_continuous hp
  have hFc : Continuous F := isLipschitz_continuous hF
  have hmeas : AEStronglyMeasurable (fun x => p x ^ 2 * F x) volume :=
    ((hpc.pow 2).mul hFc).aestronglyMeasurable
  have hL2 : MemLp (fun x => p x ^ 2 * F x) 2 volume := by
    rw [memLp_two_iff_integrable_sq hmeas]
    refine (hint.const_mul (P ^ 2 * BF ^ 2)).mono' (hmeas.pow 2) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : p x ^ 2 ≤ P ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hP x) 2
    have h2 : F x ^ 2 ≤ BF ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hFb x) 2
    calc (p x ^ 2 * F x) ^ 2 = p x ^ 2 * (p x ^ 2 * F x ^ 2) := by ring
      _ ≤ p x ^ 2 * (P ^ 2 * BF ^ 2) := by gcongr
      _ = _ := by ring
  set I : ℝ := ∫ x, p x ^ 2 with hI
  refine memSobolev_one_of_diff_bound hL2
    ((4 * Lp ^ 2 * BF ^ 2 + (4 * Lp ^ 2 * BF ^ 2 + 2 * P ^ 2 * LF ^ 2)) * I) fun h => ?_
  have hint2 : Integrable (fun x => (p x ^ 2 * F x - p (x - h) ^ 2 * F (x - h)) ^ 2) volume :=
    (hL2.sub (memLp_translate hL2 h)).integrable_sq
  have hgh : Integrable (fun x => p (x - h) ^ 2) volume := hint.comp_sub_right h
  have hpt : ∀ x, (p x ^ 2 * F x - p (x - h) ^ 2 * F (x - h)) ^ 2 ≤
      ‖h‖ ^ 2 * ((4 * Lp ^ 2 * BF ^ 2) * p x ^ 2 +
        (4 * Lp ^ 2 * BF ^ 2 + 2 * P ^ 2 * LF ^ 2) * p (x - h) ^ 2) := by
    intro x
    refine n3b_diff_pt _ _ _ _ _ Lp LF P BF ?_ (hP _) (hFb x) ?_
    · have := hp x (x - h); rwa [sub_sub_cancel] at this
    · have := hF x (x - h); rwa [sub_sub_cancel] at this
  have hdom : Integrable (fun x => ‖h‖ ^ 2 * ((4 * Lp ^ 2 * BF ^ 2) * p x ^ 2 +
        (4 * Lp ^ 2 * BF ^ 2 + 2 * P ^ 2 * LF ^ 2) * p (x - h) ^ 2)) volume :=
    ((hint.const_mul _).add (hgh.const_mul _)).const_mul _
  calc ∫ x, (p x ^ 2 * F x - p (x - h) ^ 2 * F (x - h)) ^ 2
      ≤ ∫ x, ‖h‖ ^ 2 * ((4 * Lp ^ 2 * BF ^ 2) * p x ^ 2 +
        (4 * Lp ^ 2 * BF ^ 2 + 2 * P ^ 2 * LF ^ 2) * p (x - h) ^ 2) :=
        integral_mono hint2 hdom hpt
    _ = ‖h‖ ^ 2 * ((4 * Lp ^ 2 * BF ^ 2) * I +
        (4 * Lp ^ 2 * BF ^ 2 + 2 * P ^ 2 * LF ^ 2) * I) := by
        rw [integral_const_mul, integral_add (hint.const_mul _) (hgh.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_sub_right_eq_self (fun x => p x ^ 2) h]
    _ = _ := by ring

/-- The two-multiplier identity (`UniqT1.symmetrization`) with membership hypotheses. -/
theorem n3b_symm {θ : ℝ} {m 𝔨 : Euc d → ℝ} (h𝔨 : IsLevyKernel θ m 𝔨)
    {La Lb Lc : ℝ} {F p q : Euc d → ℝ}
    (hLa : HRS.PDE.ToolboxRd.IsLipschitz La (fun x => p x ^ 2 * F x))
    (hLb : HRS.PDE.ToolboxRd.IsLipschitz Lb (fun x => q x ^ 2 * F x))
    (hLc : HRS.PDE.ToolboxRd.IsLipschitz Lc (fun x => p x * q x * F x))
    (hHa : HRS.PDE.ToolboxRd.MemSobolev 1 (fun x => p x ^ 2 * F x))
    (hHb : HRS.PDE.ToolboxRd.MemSobolev 1 (fun x => q x ^ 2 * F x))
    (hHc : HRS.PDE.ToolboxRd.MemSobolev 1 (fun x => p x * q x * F x)) :
    symbolForm m (fun x => p x ^ 2 * F x) (fun x => q x ^ 2 * F x) =
      symbolForm m (fun x => p x * q x * F x) (fun x => p x * q x * F x) -
        (1 / 2) * ∫ z : Euc d × Euc d, 𝔨 z.2 * F z.1 * F (z.1 - z.2) *
          (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2 := by
  obtain ⟨I1, E1⟩ := h𝔨.bilinear La Lb _ _ hLa hLb hHa hHb
  obtain ⟨I2, E2⟩ := h𝔨.bilinear Lc Lc _ _ hLc hLc hHc hHc
  rw [E1, E2]
  have key : ∀ z : Euc d × Euc d,
      𝔨 z.2 * (p z.1 ^ 2 * F z.1 - p (z.1 - z.2) ^ 2 * F (z.1 - z.2)) *
          (q z.1 ^ 2 * F z.1 - q (z.1 - z.2) ^ 2 * F (z.1 - z.2)) -
        𝔨 z.2 * (p z.1 * q z.1 * F z.1 - p (z.1 - z.2) * q (z.1 - z.2) * F (z.1 - z.2)) *
          (p z.1 * q z.1 * F z.1 - p (z.1 - z.2) * q (z.1 - z.2) * F (z.1 - z.2)) =
      -(𝔨 z.2 * F z.1 * F (z.1 - z.2) *
          (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2) := fun z => by ring
  have hsub := integral_sub I1 I2
  simp only [key, integral_neg] at hsub
  linarith

end HRS.MS.UniqN3b
