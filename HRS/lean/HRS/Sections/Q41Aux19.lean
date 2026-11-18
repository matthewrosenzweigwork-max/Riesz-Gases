import HRS.Sections.Q41Aux18
import HRS.PDE.MeanFieldAdjointFrozenB

/-!
# Packet Q41, helper 19: the increment of the stationary kernel is Lipschitz with constant `∝ ‖φ‖²_{C¹}`

For smooth `φ`, `C(φ,φ) - C(φ, S(h)φ) ≤ B ‖φ‖²_{C¹} h` (`q41_inc_bound`): the function
`J(v) = ⟨Pφ, R P S(v)φ⟩` has derivative `-β⁻¹ ∫ ρ ∇S(v)φ · ∇Pφ`, bounded by the energy
`β⁻¹ ∫ ρ |∇φ|²` (energy decay of the frozen semigroup).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

lemma q41_cont_grad {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) : Continuous (Torus.grad f) :=
  Torus.continuous_of_continuous_lift (isCk_grad 1 f hf).continuous

lemma q41_abs_B_le {ρ f g : Torus d → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hf : Continuous (Torus.grad f)) (hg : Continuous (Torus.grad g)) :
    |∫ x, ρ x * inner ℝ (Torus.grad f x) (Torus.grad g x)| ≤
      (Bform ρ f f + Bform ρ g g) / 2 := by
  have hint : ∀ {F : Torus d → ℝ}, Continuous F → Integrable F := fun hF =>
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e1 : Bform ρ f f = ∫ x, ρ x * ‖Torus.grad f x‖ ^ 2 := by
    unfold Bform; simp_rw [real_inner_self_eq_norm_sq]
  have e2 : Bform ρ g g = ∫ x, ρ x * ‖Torus.grad g x‖ ^ 2 := by
    unfold Bform; simp_rw [real_inner_self_eq_norm_sq]
  have i1 : Integrable fun x => ρ x * ‖Torus.grad f x‖ ^ 2 :=
    hint (hρc.mul (hf.norm.pow 2))
  have i2 : Integrable fun x => ρ x * ‖Torus.grad g x‖ ^ 2 :=
    hint (hρc.mul (hg.norm.pow 2))
  have hb : ∀ x, ‖ρ x * inner ℝ (Torus.grad f x) (Torus.grad g x)‖ ≤
      (ρ x * ‖Torus.grad f x‖ ^ 2 + ρ x * ‖Torus.grad g x‖ ^ 2) / 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
    have h1 := abs_real_inner_le_norm (Torus.grad f x) (Torus.grad g x)
    have h2 : ‖Torus.grad f x‖ * ‖Torus.grad g x‖ ≤
        (‖Torus.grad f x‖ ^ 2 + ‖Torus.grad g x‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖Torus.grad f x‖ - ‖Torus.grad g x‖)]
    have := hρ0 x
    nlinarith
  rw [e1, e2, ← Real.norm_eq_abs]
  calc ‖∫ x, ρ x * inner ℝ (Torus.grad f x) (Torus.grad g x)‖
      ≤ ∫ x, (ρ x * ‖Torus.grad f x‖ ^ 2 + ρ x * ‖Torus.grad g x‖ ^ 2) / 2 :=
        norm_integral_le_of_norm_le ((i1.add i2).div_const 2) (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_div, integral_add i1 i2]

lemma q41_B_nonneg {ρ f : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) : 0 ≤ Bform ρ f f := by
  unfold Bform
  refine integral_nonneg fun x => mul_nonneg (hρ0 x) ?_
  rw [real_inner_self_eq_norm_sq]; positivity

lemma q41_B_le_cb {ρ f : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρc : Continuous ρ)
    (hf : Torus.IsCk 2 f) :
    Bform ρ f f ≤ Torus.cbNorm 1 f ^ 2 := by
  have hint : ∀ {F : Torus d → ℝ}, Continuous F → Integrable F := fun hF =>
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf1 : Torus.IsCk 1 f := hf.of_le (by norm_num)
  have hg := q41_cont_grad hf
  have e1 : Bform ρ f f = ∫ x, ρ x * ‖Torus.grad f x‖ ^ 2 := by
    unfold Bform; simp_rw [real_inner_self_eq_norm_sq]
  rw [e1]
  have hi : Integrable fun x => ρ x * Torus.cbNorm 1 f ^ 2 := hint (hρc.mul continuous_const)
  calc ∫ x, ρ x * ‖Torus.grad f x‖ ^ 2 ≤ ∫ x, ρ x * Torus.cbNorm 1 f ^ 2 := by
        refine integral_mono (hint (hρc.mul (hg.norm.pow 2))) hi fun x => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg x)
        exact pow_le_pow_left₀ (norm_nonneg _) (MFApriori.norm_grad_le_cbNorm hf1 x) 2
    _ = Torus.cbNorm 1 f ^ 2 := by rw [integral_mul_const, hρ.integral_one, one_mul]

section Inc

variable {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}
  (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)

theorem q41_inc_bound (hd : 1 ≤ d) :
    ∀ {φ : Torus d → ℝ}, Torus.IsSmooth φ → ∀ {h : ℝ}, 0 ≤ h →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (Sg H h φ) ≤
      β⁻¹ * Torus.cbNorm 1 φ ^ 2 * h := by
  intro φ hφ h hh
  have h3 := ClassicalPart.three_le_mStar d
  have hKS := KS_of_frozen hd H
  have hρc : Continuous ρβ := H.cont (by omega)
  have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := 2 * mStar d + 4) (by omega) H.hρC
  have hpos : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le H.hc₀ (H.hlow x)
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := hKS.isProb
  obtain ⟨R, hRA, hAR, hRs, hRpos⟩ := exists_inverse hd s H.hs0 H.hsd hKS hρc β H.hβ.le
  have hφc := q41_cont_of_smooth hφ
  have hφck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) φ := isCk_of_smooth_ps hφ _
  have hφm : MemSobolev ((mStar d : ℝ) + 4) φ := (sob_of_isCk_ps hφck).2
  have cont1 : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Continuous f := fun hf =>
    MFAux.continuous_of_isCk (hf.of_le (by norm_num))
  set G : ℝ → Torus d → ℝ := fun v => Sg H v φ with hG
  have D : ∀ b : ℝ, 0 < b → _ := fun b hb => frozen_path_data hd H hφc hφm (T' := b) hb
  set y0 : Lp ℝ 2 (withDensityReal ρβ) := pL (withDensityReal ρβ) G 0 with hy0def
  set J : ℝ → ℝ := fun v => inner ℝ y0 (R (pL (withDensityReal ρβ) G v)) with hJ
  have hSdata : ∀ u : ℝ, 0 ≤ u → Continuous (G u) ∧ pair (withDensityReal ρβ) (G u) = 0 := by
    intro u hu
    obtain ⟨c2, pz, -⟩ := D (u + 1) (by linarith)
    exact ⟨cont1 (c2 u ⟨hu, by linarith⟩), pz u ⟨hu, by linarith⟩⟩
  have hy : ∀ u : ℝ, 0 ≤ u →
      ⇑(pL (withDensityReal ρβ) G u) =ᵐ[withDensityReal ρβ] projMean (withDensityReal ρβ) (G u) := by
    intro u hu
    rw [projMean_of_pair_zero (hSdata u hu).2]
    exact pL_ae (hSdata u hu).1
  have hy0 : ⇑y0 =ᵐ[withDensityReal ρβ] projMean (withDensityReal ρβ) φ := by
    have := pL_ae (μ := withDensityReal ρβ) (G := G) (v := 0) (hSdata 0 le_rfl).1
    have e0 : G 0 = projMean (withDensityReal ρβ) φ := frozen_zero hd H hφc hφm
    rw [e0] at this
    exact this
  -- (a) `J v = C(φ, S(v)φ)`
  have hJC : ∀ v : ℝ, 0 ≤ v →
      J v = susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (G v) := by
    intro v hv
    exact (susceptibilityCov_eq_inner hd s H.hs0 H.hsd hKS hρc β H.hβ R hAR φ (G v)
      (hSdata v hv).1 _ _ hy0 (hy v hv)).symm
  -- energy bound
  have hB : ∀ τ : ℝ, 0 ≤ τ → Torus.IsCk 2 (G τ) ∧ Bform ρβ (G τ) (G τ) ≤ Bform ρβ φ φ := by
    intro τ hτ
    have H5 : FrozenHyp d s (mStar d + 5) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := H.mono (by omega)
    obtain ⟨cP, hcP, hPoin⟩ := exists_weighted_poincare (d := d) c₀ Λ₀ H.hc₀
    have hP := hPoin ρβ H.thermal.1 hρc H.hlow H.le_Lam
    have hm2 : MemSobolev ((mStar d : ℝ) + 2) φ := memSobolev_mono_idx hφm (by linarith)
    obtain ⟨c2, -, hbd⟩ := frozen_energy_decay hd H5 hcP hP hφc hm2 hτ
    refine ⟨c2, hbd.trans ?_⟩
    have hB0 : 0 ≤ Bform ρβ φ φ := q41_B_nonneg (fun x => (hpos x).le)
    have : Real.exp (-(2 * (β⁻¹ * cP)) * τ) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have h1 : 0 < β⁻¹ * cP := mul_pos (inv_pos.2 H.hβ) hcP
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hτ)
    calc Real.exp (-(2 * (β⁻¹ * cP)) * τ) * Bform ρβ φ φ ≤ 1 * Bform ρβ φ φ :=
          mul_le_mul_of_nonneg_right this hB0
      _ = _ := one_mul _
  -- derivative on `(0, ∞)`
  have hder : ∀ v : ℝ, 0 < v → HasDerivAt J
      (-(β⁻¹ * ∫ x, ρβ x * inner ℝ (Torus.grad (G v) x) (Torus.grad (G 0) x))) v := by
    intro v hv
    obtain ⟨c2, pz, jc, jG, dd⟩ := D (v + 1) (by linarith)
    have cs : ∀ {Gt : ℝ → Torus d → ℝ},
        (Continuous fun p : Set.Icc (0 : ℝ) (v + 1) × Torus d => Gt p.1 p.2) →
        ∀ w ∈ Set.Icc (0 : ℝ) (v + 1), Continuous (Gt w) := fun h w hw =>
      h.comp (continuous_const.prodMk continuous_id
        (f := fun x : Torus d => (⟨w, hw⟩ : Set.Icc (0 : ℝ) (v + 1))))
    have h1 := hasDerivAt_pL (withDensityReal ρβ) (a := 0) (b := v + 1) (G := G)
      (G' := fun w => equilibriumGen d s ρβ β⁻¹ (G w)) (fun w hw => cont1 (c2 w hw))
      (cs (Gt := fun w => equilibriumGen d s ρβ β⁻¹ (G w)) jG) jG dd (v0 := v)
      ⟨hv, by linarith⟩
    have h2 := R.hasFDerivAt.comp_hasDerivAt v h1
    have h4 := (hasDerivAt_const v y0).inner ℝ h2
    refine h4.congr_deriv ?_
    have hvI : v ∈ Set.Icc (0 : ℝ) (v + 1) := ⟨hv.le, by linarith⟩
    have e' : ⇑(pL (withDensityReal ρβ) (fun w => equilibriumGen d s ρβ β⁻¹ (G w)) v)
        =ᵐ[withDensityReal ρβ] equilibriumGen d s ρβ β⁻¹ (G v) :=
      pL_ae (cs (Gt := fun w => equilibriumGen d s ρβ β⁻¹ (G w)) jG v hvI)
    have hG0 : Torus.IsCk 2 (G 0) := (hB 0 le_rfl).1
    have eg0 : ⇑y0 =ᵐ[withDensityReal ρβ] G 0 := pL_ae (hSdata 0 le_rfl).1
    have k := inner_R_eqGen s hKS β H.hβ hρ1 hpos R hRA (hB v hv.le).1 (hG0.of_le (by norm_num))
      (pL (withDensityReal ρβ) (fun w => equilibriumGen d s ρβ β⁻¹ (G w)) v) y0 e' eg0
    have hc : ((⇑R ∘ pL (withDensityReal ρβ) G) v) = R (pL (withDensityReal ρβ) G v) := rfl
    simp only [inner_zero_left, add_zero]
    rw [k]
    ring
  have hbound : ∀ v : ℝ, 0 < v →
      |∫ x, ρβ x * inner ℝ (Torus.grad (G v) x) (Torus.grad (G 0) x)| ≤ Bform ρβ φ φ := by
    intro v hv
    refine (q41_abs_B_le hρc (fun x => (hpos x).le) (q41_cont_grad (hB v hv.le).1)
      (q41_cont_grad (hB 0 le_rfl).1)).trans ?_
    have h1 := (hB v hv.le).2
    have h2 := (hB 0 le_rfl).2
    linarith
  have hcont : ContinuousOn J (Set.Icc 0 h) := by
    obtain ⟨c2, pz, jc, -⟩ := D (h + 1) (by linarith)
    have hc1 := continuousOn_pL (withDensityReal ρβ) (a := 0) (b := h + 1) (G := G)
      (fun w hw => cont1 (c2 w hw)) jc
    have hc : ContinuousOn J (Set.Icc 0 (h + 1)) :=
      ContinuousOn.inner (𝕜 := ℝ) continuousOn_const (R.continuous.comp_continuousOn hc1)
    exact hc.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hC := q41_covProps hd H
  have hG0 : G 0 = fun x => φ x + -pair (withDensityReal ρβ) φ := by
    funext x
    have := congrFun (frozen_zero hd H hφc hφm) x
    simp only [projMean] at this
    rw [show G 0 x = Sg H 0 φ x from rfl, this]
    ring
  have hCG0 : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (G 0) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ := by
    rw [hG0]
    exact hC.const2 φ φ _ hφc hφc
  have hJ0 : J 0 = susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ := by
    rw [hJC 0 le_rfl, hCG0]
  have hBφ : Bform ρβ φ φ ≤ Torus.cbNorm 1 φ ^ 2 :=
    q41_B_le_cb H.thermal.1 hρc (hB 0 le_rfl).1 |> fun h' => by
      have hφ2 : Torus.IsCk 2 φ := isCk_of_smooth_ps hφ 2
      exact q41_B_le_cb H.thermal.1 hρc hφ2
  have hνpos : 0 < β⁻¹ := inv_pos.2 H.hβ
  show _ - susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (G h) ≤ _
  rw [← hJC h hh, ← hJ0]
  rcases hh.eq_or_lt with h0 | hpos'
  · rw [← h0]
    have : 0 ≤ β⁻¹ * Torus.cbNorm 1 φ ^ 2 * 0 := by simp
    simp
  · obtain ⟨c, hc, hcc⟩ := exists_hasDerivAt_eq_slope J
      (fun v => -(β⁻¹ * ∫ x, ρβ x * inner ℝ (Torus.grad (G v) x) (Torus.grad (G 0) x))) hpos' hcont
      (fun v hv => hder v hv.1)
    have hslope : J h - J 0 = -(β⁻¹ * ∫ x, ρβ x * inner ℝ (Torus.grad (G c) x)
        (Torus.grad (G 0) x)) * h := by
      rw [hcc]
      field_simp
      ring
    have hb := hbound c hc.1
    have hbd : -(J h - J 0) ≤ β⁻¹ * Bform ρβ φ φ * h := by
      rw [hslope]
      have : β⁻¹ * ∫ x, ρβ x * inner ℝ (Torus.grad (G c) x) (Torus.grad (G 0) x) ≤
          β⁻¹ * Bform ρβ φ φ :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hνpos.le
      nlinarith
    calc J 0 - J h = -(J h - J 0) := by ring
      _ ≤ β⁻¹ * Bform ρβ φ φ * h := hbd
      _ ≤ β⁻¹ * Torus.cbNorm 1 φ ^ 2 * h := by
          have := mul_le_mul_of_nonneg_left hBφ hνpos.le
          nlinarith

end Inc

end HRS.Q41
