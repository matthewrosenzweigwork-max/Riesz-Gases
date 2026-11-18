import HRS.MS.SpecAux81

/-!
# S8L: the energy inequality of a positive subsolution from integration by parts with a cut-off (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_en_of_sub`: if `s ≥ s0 > 0` is `C²`, `L s ≤ a s + b h √s - |∇s|²/(2s)` pointwise and the
weighted integration by parts `∫ ρ ⟨∇s, ∇Ψ⟩ = ∫ ρ (L s) Ψ` holds for `C¹` compactly supported `Ψ`, then the integrated energy inequality
`∫ G'(s)|∇s|² + ∫ G(s)|∇s|²/(2s) ≤ ∫ (a s + b h √s) G(s)` (the `en` field of `S8pSubsol`) holds for the Herbst test functions `G`.
Proof: test with `ζ_R² G(s)` (`ζ_R = χ(x/R)`), absorb the cross term with `ε`, let `R → ∞` (Fatou, dominated convergence), then `ε → 0`.
Also `s8p_grad`, `s8p_pair` (pairing of differentials), `s8p_cross_le`, `s8p_fderiv_test`, `s8p_tr`, `s8p_trI`.
-/

noncomputable section

open MeasureTheory Real Filter Topology

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The gradient (Riesz vector) of a function. -/
def s8p_grad (f : V → ℝ) (x : V) : V := (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f x)

/-- Pairing of differentials. -/
def s8p_pair (f g : V → ℝ) (x : V) : ℝ := fderiv ℝ f x (s8p_grad g x)

theorem s8p_pair_self (f : V → ℝ) (x : V) : s8p_pair f f x = ‖fderiv ℝ f x‖ ^ 2 :=
  s8p_Pd_toDual _

theorem s8p_pair_smul_add (f g k : V → ℝ) (c1 c2 : ℝ) (x : V)
    (hΨ : fderiv ℝ f x = c1 • fderiv ℝ g x + c2 • fderiv ℝ k x) :
    s8p_pair k f x = c1 * s8p_pair k g x + c2 * ‖fderiv ℝ k x‖ ^ 2 := by
  unfold s8p_pair s8p_grad
  rw [hΨ]
  have : (InnerProductSpace.toDual ℝ V).symm (c1 • fderiv ℝ g x + c2 • fderiv ℝ k x) =
      c1 • (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ g x) +
        c2 • (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ k x) := by
    rw [map_add, map_smul, map_smul]
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← s8p_pair_self k x]
  rfl

theorem s8p_pair_abs_le (f g : V → ℝ) (x : V) : |s8p_pair f g x| ≤ ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
  unfold s8p_pair s8p_grad
  have := s8p_clm_le (fderiv ℝ f x) ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ g x))
  simpa using this


theorem s8p_cross_le {ζ G D s Q β ε : ℝ} (hζ : 0 ≤ ζ) (hG : 0 ≤ G) (hD : 0 ≤ D) (hs : 0 < s) (hε : 0 < ε)
    (hβ : 0 ≤ β) (hQ : |Q| ≤ Real.sqrt D * β) :
    -(2 * ζ * G * Q) ≤ ε * (ζ ^ 2 * G * D / (2 * s)) + (2 * β ^ 2 / ε) * (s * G) := by
  have h1 : -(2 * ζ * G * Q) ≤ 2 * ζ * G * (Real.sqrt D * β) := by
    have := neg_le_abs Q
    have h2 : 0 ≤ 2 * ζ * G := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (this.trans hQ) h2]
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  set r := Real.sqrt D with hr
  have hDr : D = r ^ 2 := hsq.symm
  have h3 : 2 * ζ * (r * β) ≤ ε * (ζ ^ 2 * D / (2 * s)) + (2 * β ^ 2 / ε) * s := by
    have h4 : 0 ≤ (ε * ζ * r - 2 * s * β) ^ 2 / (2 * s * ε) := by positivity
    have e : ε * (ζ ^ 2 * D / (2 * s)) + (2 * β ^ 2 / ε) * s - 2 * ζ * (r * β) =
        (ε * ζ * r - 2 * s * β) ^ 2 / (2 * s * ε) := by
      field_simp; rw [hDr]; ring
    linarith
  calc -(2 * ζ * G * Q) ≤ G * (2 * ζ * (r * β)) := by nlinarith
    _ ≤ G * (ε * (ζ ^ 2 * D / (2 * s)) + (2 * β ^ 2 / ε) * s) := mul_le_mul_of_nonneg_left h3 hG
    _ = _ := by ring

theorem s8p_fderiv_test {ζ s : V → ℝ} {G : ℝ → ℝ} (hζ : ContDiff ℝ 2 ζ) (hs : ContDiff ℝ 2 s)
    (hpos : ∀ x, 0 < s x) (hG : ContDiffOn ℝ 1 G (Set.Ioi 0)) (x : V) :
    fderiv ℝ (fun x => ζ x ^ 2 * G (s x)) x =
      (2 * ζ x * G (s x)) • fderiv ℝ ζ x + (ζ x ^ 2 * deriv G (s x)) • fderiv ℝ s x := by
  have hζd : HasFDerivAt ζ (fderiv ℝ ζ x) x := ((hζ.differentiable (by norm_num)) x).hasFDerivAt
  have hsd : HasFDerivAt s (fderiv ℝ s x) x := ((hs.differentiable (by norm_num)) x).hasFDerivAt
  have hGd : HasDerivAt G (deriv G (s x)) (s x) :=
    ((hG.contDiffAt (Ioi_mem_nhds (hpos x))).differentiableAt (by norm_num)).hasDerivAt
  have h1 := (hζd.pow 2).mul (hGd.comp_hasFDerivAt x hsd)
  have h2 : fderiv ℝ (fun x => ζ x ^ 2 * G (s x)) x = _ := h1.fderiv
  rw [h2]
  simp only [smul_add, smul_smul]
  ext v
  simp
  ring


theorem s8p_zeta {χ : V → ℝ} (hχ : ContDiff ℝ 2 χ) {R0 : ℝ} (hR0 : ∀ x, R0 < ‖x‖ → χ x = 0) {Bχ : ℝ}
    (hB : ∀ x, ‖fderiv ℝ χ x‖ ≤ Bχ) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (fun x => χ (R⁻¹ • x)) ∧ HasCompactSupport (fun x => χ (R⁻¹ • x)) ∧
      ∀ x, ‖fderiv ℝ (fun x => χ (R⁻¹ • x)) x‖ ≤ Bχ / R := by
  refine ⟨hχ.comp (contDiff_const.smul contDiff_id), ?_, fun x => ?_⟩
  · have := (s8p_cutoff_u (contDiff_const (c := (1 : ℝ))) hχ hR0 hR).2
    simpa using this
  · have h1 : HasFDerivAt (fun x : V => R⁻¹ • x) (R⁻¹ • ContinuousLinearMap.id ℝ V) x := by
      exact (hasFDerivAt_id x).const_smul R⁻¹
    have h2 : HasFDerivAt (fun x : V => χ (R⁻¹ • x)) (R⁻¹ • fderiv ℝ χ (R⁻¹ • x)) x := by
      have := (hχ.differentiable (by norm_num) (R⁻¹ • x)).hasFDerivAt.comp x h1
      refine this.congr_fderiv ?_
      ext v; simp
    rw [h2.fderiv, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
    calc R⁻¹ * ‖fderiv ℝ χ (R⁻¹ • x)‖ ≤ R⁻¹ * Bχ := mul_le_mul_of_nonneg_left (hB _) (by positivity)
      _ = Bχ / R := by ring

/-- Integral against the weighted measure. -/
theorem s8p_tr {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x) (h : V → ℝ) :
    ∫ x, h x ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) = ∫ x, ρ x * h x := by
  rw [integral_withDensity_eq_integral_toReal_smul (hρm.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 x).le]

theorem s8p_trI {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x) (h : V → ℝ) :
    Integrable h (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ↔
      Integrable (fun x => ρ x * h x) := by
  rw [integrable_withDensity_iff_integrable_smul' (hρm.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 x).le]

set_option maxHeartbeats 1600000 in
/-- The energy inequality of a subsolution, from the pointwise inequality and integration by parts
against compactly supported test functions (cut-off argument). -/
theorem s8p_en_of_sub {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x)
    {s h Ls : V → ℝ} {s0 a b : ℝ} (hs : ContDiff ℝ 2 s) (hs0 : 0 < s0) (hge : ∀ x, s0 ≤ s x)
    (hsint : Integrable s (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh0 : ∀ x, 0 ≤ h x) (hhm : Measurable h)
    (hh2 : Integrable (fun x => h x ^ 2) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    (hLsc : Continuous Ls)
    (hsub : ∀ x, Ls x ≤ a * s x + b * h x * Real.sqrt (s x) - ‖fderiv ℝ s x‖ ^ 2 / (2 * s x))
    (hibp : ∀ Ψ : V → ℝ, ContDiff ℝ 1 Ψ → HasCompactSupport Ψ →
      ∫ x, ρ x * s8p_pair s Ψ x = ∫ x, ρ x * (Ls x * Ψ x))
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, s0 ≤ t → |G t| ≤ B ∧ |deriv G t| ≤ B) (hG0 : ∀ t, 0 < t → 0 ≤ G t)
    (hGd0 : ∀ t, 0 < t → 0 ≤ deriv G t) :
    Integrable (fun x => deriv G (s x) * ‖fderiv ℝ s x‖ ^ 2) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ∧
      Integrable (fun x => G (s x) * ‖fderiv ℝ s x‖ ^ 2 / (2 * s x)) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ∧
      ∫ x, deriv G (s x) * ‖fderiv ℝ s x‖ ^ 2 ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) +
        ∫ x, G (s x) * ‖fderiv ℝ s x‖ ^ 2 / (2 * s x) ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ≤
      ∫ x, (a * s x + b * h x * Real.sqrt (s x)) * G (s x) ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  set μ := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ
  have tr := s8p_tr hρm hρ0
  have trI := s8p_trI hρm hρ0
  have hpos : ∀ x, 0 < s x := fun x => lt_of_lt_of_le hs0 (hge x)
  obtain ⟨χ, hχ, ⟨R0, hR0⟩, h01, h1, Bχ, hBχ0, hBχ⟩ := s8p_cutoff (V := V)
  have hDc : Continuous fun x => ‖fderiv ℝ s x‖ ^ 2 := ((hs.continuous_fderiv (by norm_num)).norm.pow 2)
  have hGc : Continuous fun x => G (s x) := hG.continuousOn.comp_continuous hs.continuous (fun x => hpos x)
  have hGdc : Continuous fun x => deriv G (s x) :=
    (hG.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp_continuous hs.continuous (fun x => hpos x)
  have hGB : ∀ x, |G (s x)| ≤ B ∧ |deriv G (s x)| ≤ B := fun x => hB _ (hge x)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hGB 0).1
  -- integrability of the "source" and the sG term
  have hsG : Integrable (fun x => s x * G (s x)) μ := by
    refine Integrable.mono' (hsint.const_mul B) ((hs.continuous.mul hGc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hpos x).le, Real.norm_eq_abs]
    calc s x * |G (s x)| ≤ s x * B := mul_le_mul_of_nonneg_left (hGB x).1 (hpos x).le
      _ = B * s x := mul_comm _ _
  have hsrc : Integrable (fun x => (a * s x + b * h x * Real.sqrt (s x)) * G (s x)) μ := by
    have h1 : Integrable (fun x => h x * Real.sqrt (s x)) μ := by
      refine Integrable.mono' (hh2.add hsint |>.const_mul (1 / 2 : ℝ))
        (hhm.mul (hs.continuous.sqrt.measurable)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (hh0 x), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have := Real.sq_sqrt (hpos x).le
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (h x - Real.sqrt (s x))]
    have h2 : Integrable (fun x => a * s x + b * (h x * Real.sqrt (s x))) μ :=
      (hsint.const_mul a).add (h1.const_mul b)
    have hm : Measurable fun x => (a * s x + b * h x * Real.sqrt (s x)) * G (s x) :=
      Measurable.mul (Measurable.add (hs.continuous.measurable.const_mul a)
        ((hhm.const_mul b).mul hs.continuous.sqrt.measurable)) hGc.measurable
    refine Integrable.mono' (h2.norm.mul_const B) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (G (s x))]
    have e : a * s x + b * h x * Real.sqrt (s x) = a * s x + b * (h x * Real.sqrt (s x)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hGB x).1 (norm_nonneg _)
  have cs_int : ∀ F : V → ℝ, Continuous F → HasCompactSupport F → Integrable F μ := fun F hc hcs =>
    hc.integrable_of_hasCompactSupport hcs
  set Rn : ℕ → ℝ := fun n => (n : ℝ) + 1 with hRn
  have hRpos : ∀ n, 0 < Rn n := fun n => by simp only [hRn]; positivity
  have hz := fun n => s8p_zeta hχ hR0 hBχ (hRpos n)
  set ζ : ℕ → V → ℝ := fun n x => χ ((Rn n)⁻¹ • x) with hζ
  set D : V → ℝ := fun x => ‖fderiv ℝ s x‖ ^ 2 with hD
  have hD0 : ∀ x, 0 ≤ D x := fun x => sq_nonneg _
  have hζ01 : ∀ n x, 0 ≤ ζ n x ∧ ζ n x ≤ 1 := fun n x => h01 _
  have key : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      Integrable (fun x => ζ n x ^ 2 * (deriv G (s x) * D x)) μ ∧
      Integrable (fun x => ζ n x ^ 2 * (G (s x) * D x / (2 * s x))) μ ∧
      ∫ x, ζ n x ^ 2 * (deriv G (s x) * D x) ∂μ + (1 - ε) * ∫ x, ζ n x ^ 2 * (G (s x) * D x / (2 * s x)) ∂μ ≤
        ∫ x, ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x)) ∂μ +
          (2 * (Bχ / Rn n) ^ 2 / ε) * ∫ x, s x * G (s x) ∂μ := by
    intro n ε hε
    set β := Bχ / Rn n with hβ
    have hβ0 : 0 ≤ β := by positivity
    set Ψ : V → ℝ := fun x => ζ n x ^ 2 * G (s x) with hΨ
    have hζcd : ContDiff ℝ 2 (ζ n) := (hz n).1
    have hΨcd : ContDiff ℝ 1 Ψ := by
      refine contDiff_iff_contDiffAt.2 fun x => ?_
      have h1 : ContDiffAt ℝ 1 (fun x => ζ n x ^ 2) x := ((hζcd.of_le (by norm_num)).pow 2).contDiffAt
      have h2 : ContDiffAt ℝ 1 (fun x => G (s x)) x :=
        (hG.contDiffAt (Ioi_mem_nhds (hpos x))).comp x (hs.contDiffAt.of_le (by norm_num))
      exact h1.mul h2
    have hζcs : HasCompactSupport (ζ n) := (hz n).2.1
    have hΨcs : HasCompactSupport Ψ := (hζcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
    have hI := hibp Ψ hΨcd hΨcs
    set Q : V → ℝ := fun x => s8p_pair s (ζ n) x with hQ
    have hpair : ∀ x, s8p_pair s Ψ x = (2 * ζ n x * G (s x)) * Q x + ζ n x ^ 2 * (deriv G (s x) * D x) := by
      intro x
      have := s8p_pair_smul_add Ψ (ζ n) s (2 * ζ n x * G (s x)) (ζ n x ^ 2 * deriv G (s x)) x
        (s8p_fderiv_test hζcd hs hpos hG x)
      rw [this]; simp only [hQ, hD]; ring
    have hQb : ∀ x, |Q x| ≤ Real.sqrt (D x) * β := fun x => by
      have h1 := s8p_pair_abs_le s (ζ n) x
      have h2 := (hz n).2.2 x
      have h3 : Real.sqrt (D x) = ‖fderiv ℝ s x‖ := by simp only [hD]; exact Real.sqrt_sq (norm_nonneg _)
      rw [h3]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    -- continuity and supports
    have hζc : Continuous (ζ n) := hζcd.continuous
    have hcsζ : ∀ F : V → ℝ, (∀ x, ζ n x = 0 → F x = 0) → HasCompactSupport F := fun F hF =>
      HasCompactSupport.intro hζcs (fun x hx => hF x (image_eq_zero_of_notMem_tsupport hx))
    have hQc : Continuous Q := by
      simp only [hQ, s8p_pair, s8p_grad]
      exact (hs.continuous_fderiv (by norm_num)).clm_apply
        ((InnerProductSpace.toDual ℝ V).symm.continuous.comp (hζcd.continuous_fderiv (by norm_num)))
    have hs1 : Continuous fun x => 2 * s x := continuous_const.mul hs.continuous
    have hA1c : Continuous fun x => ζ n x ^ 2 * (deriv G (s x) * D x) :=
      (hζc.pow 2).mul (hGdc.mul hDc)
    have hA2c : Continuous fun x => ζ n x ^ 2 * (G (s x) * D x / (2 * s x)) :=
      (hζc.pow 2).mul ((hGc.mul hDc).div hs1 (fun x => by have := hpos x; positivity))
    have hc1Q : Continuous fun x => (2 * ζ n x * G (s x)) * Q x := ((continuous_const.mul hζc).mul hGc).mul hQc
    have hΨc : Continuous Ψ := hΨcd.continuous
    have iA1 : Integrable (fun x => ζ n x ^ 2 * (deriv G (s x) * D x)) μ :=
      cs_int _ hA1c (hcsζ _ fun x hx => by simp [hx])
    have iA2 : Integrable (fun x => ζ n x ^ 2 * (G (s x) * D x / (2 * s x))) μ :=
      cs_int _ hA2c (hcsζ _ fun x hx => by simp [hx])
    have ic1Q : Integrable (fun x => (2 * ζ n x * G (s x)) * Q x) μ :=
      cs_int _ hc1Q (hcsζ _ fun x hx => by simp [hx])
    have iLsΨ : Integrable (fun x => Ls x * Ψ x) μ := cs_int _ (hLsc.mul hΨc) (hcsζ _ fun x hx => by simp [hΨ, hx])
    have iP4 : Integrable (fun x => ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x))) μ := by
      refine Integrable.mono' hsrc.norm ((hζc.pow 2).aestronglyMeasurable.mul hsrc.1) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := mul_le_mul_of_nonneg_right (pow_le_one₀ (hζ01 n x).1 (hζ01 n x).2 (n := 2)) (norm_nonneg ((a * s x + b * h x * Real.sqrt (s x)) * G (s x)))
      simpa using this
    have hpt : ∀ x, ζ n x ^ 2 * (deriv G (s x) * D x) + (1 - ε) * (ζ n x ^ 2 * (G (s x) * D x / (2 * s x))) ≤
        (s8p_pair s Ψ x - Ls x * Ψ x) + ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x)) +
          (2 * β ^ 2 / ε) * (s x * G (s x)) := fun x => by
      have hsx := hpos x
      have hz0 := (hζ01 n x).1
      have hG0x := hG0 _ hsx
      have hsub' := mul_le_mul_of_nonneg_right (hsub x) (by positivity : 0 ≤ ζ n x ^ 2 * G (s x))
      have hcross := s8p_cross_le hz0 hG0x (hD0 x) hsx hε hβ0 (hQb x)
      rw [hpair x]
      have e1 : (a * s x + b * h x * Real.sqrt (s x) - D x / (2 * s x)) * (ζ n x ^ 2 * G (s x)) =
          ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x)) -
            ζ n x ^ 2 * (G (s x) * D x / (2 * s x)) := by ring
      have e2 : ζ n x ^ 2 * G (s x) * D x / (2 * s x) = ζ n x ^ 2 * (G (s x) * D x / (2 * s x)) := by ring
      simp only [hΨ]
      rw [e1] at hsub'
      rw [e2] at hcross
      linarith [hsub', hcross]
    have iΦ : Integrable (fun x => s8p_pair s Ψ x - Ls x * Ψ x) μ := by
      have : Integrable (fun x => (2 * ζ n x * G (s x)) * Q x + ζ n x ^ 2 * (deriv G (s x) * D x)) μ := ic1Q.add iA1
      exact (this.congr (Filter.Eventually.of_forall fun x => (hpair x).symm)).sub iLsΨ
    have hΦ0 : ∫ x, (s8p_pair s Ψ x - Ls x * Ψ x) ∂μ = 0 := by
      have i1 : Integrable (fun x => s8p_pair s Ψ x) μ := by
        have : Integrable (fun x => (2 * ζ n x * G (s x)) * Q x + ζ n x ^ 2 * (deriv G (s x) * D x)) μ := ic1Q.add iA1
        exact this.congr (Filter.Eventually.of_forall fun x => (hpair x).symm)
      rw [integral_sub i1 iLsΨ, tr, tr (fun x => Ls x * Ψ x), hI]; ring
    have iP5 : Integrable (fun x => (2 * β ^ 2 / ε) * (s x * G (s x))) μ := hsG.const_mul _
    have hmono : ∫ x, (ζ n x ^ 2 * (deriv G (s x) * D x) + (1 - ε) * (ζ n x ^ 2 * (G (s x) * D x / (2 * s x)))) ∂μ ≤
        ∫ x, (((s8p_pair s Ψ x - Ls x * Ψ x) + ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x))) +
          (2 * β ^ 2 / ε) * (s x * G (s x))) ∂μ :=
      integral_mono ((iA1.add (iA2.const_mul (1 - ε)))) ((iΦ.add iP4).add iP5) hpt
    have iΦP4 : Integrable (fun x => (s8p_pair s Ψ x - Ls x * Ψ x) +
        ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x))) μ := iΦ.add iP4
    rw [integral_add iA1 (iA2.const_mul _), integral_const_mul, integral_add iΦP4 iP5,
      integral_add iΦ iP4, integral_const_mul, hΦ0, zero_add] at hmono
    exact ⟨iA1, iA2, hmono⟩
  -- limit n → ∞
  have hev : ∀ x, ∀ᶠ n in atTop, ζ n x = 1 := fun x => by
    have : ∀ᶠ n : ℕ in atTop, ‖x‖ ≤ Rn n := by
      filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      simp only [hRn]
      have := Nat.le_ceil ‖x‖
      have : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [this] with n hn
    exact h1 _ (by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (hRpos n).le, inv_mul_le_iff₀ (hRpos n)]
      simpa using hn)
  set Pf : V → ℝ := fun x => (a * s x + b * h x * Real.sqrt (s x)) * G (s x) with hPf
  set A1 : V → ℝ := fun x => deriv G (s x) * D x with hA1
  set A2 : V → ℝ := fun x => G (s x) * D x / (2 * s x) with hA2
  have hA10 : ∀ x, 0 ≤ A1 x := fun x => mul_nonneg (hGd0 _ (hpos x)) (hD0 x)
  have hA20 : ∀ x, 0 ≤ A2 x := fun x => by
    have := hG0 _ (hpos x); have := hpos x; have := hD0 x
    simp only [hA2]; positivity
  have hA1m : Measurable A1 := hGdc.measurable.mul hDc.measurable
  have hs1m : Measurable fun x => 2 * s x := (continuous_const.mul hs.continuous).measurable
  have hA2m : Measurable A2 := (hGc.measurable.mul hDc.measurable).div hs1m
  set Js : ℝ := ∫ x, s x * G (s x) ∂μ with hJs
  have hPint : Integrable Pf μ := hsrc
  -- the right-hand side converges
  have hRHS : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => ∫ x, ζ n x ^ 2 * Pf x ∂μ +
      (2 * (Bχ / Rn n) ^ 2 / ε) * Js) atTop (𝓝 (∫ x, Pf x ∂μ + 0)) := fun ε hε => by
    refine Tendsto.add ?_ ?_
    · refine tendsto_integral_of_dominated_convergence (fun x => ‖Pf x‖) ?_ hPint.norm ?_ ?_
      · intro n
        exact ((hz n).1.continuous.pow 2).aestronglyMeasurable.mul hPint.1
      · intro n
        refine Filter.Eventually.of_forall fun x => ?_
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := mul_le_mul_of_nonneg_right (pow_le_one₀ (hζ01 n x).1 (hζ01 n x).2 (n := 2)) (norm_nonneg (Pf x))
        simpa using this
      · refine Filter.Eventually.of_forall fun x => ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev x] with n hn
        simp [hζ] at hn ⊢
        rw [hn]; simp
    · have h0 : Tendsto (fun n : ℕ => Bχ / Rn n) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => (Rn n)⁻¹) atTop (𝓝 0) := by
          simpa [hRn, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa [div_eq_mul_inv] using this.const_mul Bχ
      have := (((h0.pow 2).const_mul 2).div_const ε).mul_const Js
      simpa using this
  have hε_ineq : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Integrable (fun x => A1 x + (1 - ε) * A2 x) μ ∧
        ∫ x, (A1 x + (1 - ε) * A2 x) ∂μ ≤ ∫ x, Pf x ∂μ := fun ε hε hε1 => by
    set f : ℕ → V → ENNReal := fun n x =>
      ENNReal.ofReal (ζ n x ^ 2 * A1 x + (1 - ε) * (ζ n x ^ 2 * A2 x)) with hf
    have hfm : ∀ n, Measurable (f n) := fun n => by
      simp only [hf]
      exact ENNReal.measurable_ofReal.comp (((hz n).1.continuous.pow 2).measurable.mul hA1m |>.add
        (((hz n).1.continuous.pow 2).measurable.mul hA2m |>.const_mul _))
    have hfl := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hfm
    have hlim_pt : ∀ x, Filter.liminf (fun n => f n x) (atTop : Filter ℕ) =
        ENNReal.ofReal (A1 x + (1 - ε) * A2 x) := fun x => by
      refine Filter.Tendsto.liminf_eq (f := (atTop : Filter ℕ)) ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      simp only [hf, hζ] at hn ⊢
      rw [hn]; simp
    have hint_n : ∀ n, ∫⁻ x, f n x ∂μ ≤ ENNReal.ofReal (∫ x, ζ n x ^ 2 * Pf x ∂μ +
        (2 * (Bχ / Rn n) ^ 2 / ε) * Js) := fun n => by
      obtain ⟨i1, i2, hk⟩ := key n ε hε
      have hnn : ∀ x, 0 ≤ ζ n x ^ 2 * A1 x + (1 - ε) * (ζ n x ^ 2 * A2 x) := fun x =>
        add_nonneg (mul_nonneg (sq_nonneg _) (hA10 x)) (mul_nonneg (by linarith) (mul_nonneg (sq_nonneg _) (hA20 x)))
      have iS : Integrable (fun x => ζ n x ^ 2 * A1 x + (1 - ε) * (ζ n x ^ 2 * A2 x)) μ :=
        i1.add (i2.const_mul (1 - ε))
      simp only [hf]
      rw [← ofReal_integral_eq_lintegral_ofReal iS (Filter.Eventually.of_forall hnn)]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_add i1 (i2.const_mul _), integral_const_mul]
      have : ∫ x, ζ n x ^ 2 * ((a * s x + b * h x * Real.sqrt (s x)) * G (s x)) ∂μ = ∫ x, ζ n x ^ 2 * Pf x ∂μ := rfl
      linarith [hk]
    have h3 : Filter.liminf (fun n => ∫⁻ x, f n x ∂μ) (atTop : Filter ℕ) ≤
        Filter.liminf (fun n => ENNReal.ofReal (∫ x, ζ n x ^ 2 * Pf x ∂μ +
          (2 * (Bχ / Rn n) ^ 2 / ε) * Js)) (atTop : Filter ℕ) :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hint_n)
    have hlimR := ENNReal.tendsto_ofReal (hRHS ε hε)
    rw [hlimR.liminf_eq] at h3
    simp_rw [hlim_pt] at hfl
    have hbound := hfl.trans h3
    have hF0 : ∀ x, 0 ≤ A1 x + (1 - ε) * A2 x := fun x =>
      add_nonneg (hA10 x) (mul_nonneg (by linarith) (hA20 x))
    have hFm : Measurable fun x => A1 x + (1 - ε) * A2 x := hA1m.add (hA2m.const_mul _)
    have hFint : Integrable (fun x => A1 x + (1 - ε) * A2 x) μ := by
      refine ⟨hFm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hF0)]
      exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
    refine ⟨hFint, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hFint (Filter.Eventually.of_forall hF0)] at hbound
    have hP0 : 0 ≤ ∫ x, Pf x ∂μ + 0 := by
      rw [add_zero]
      refine integral_nonneg fun x => ?_
      simp only [hPf]
      have := hh0 x; have := hG0 _ (hpos x); have := hpos x
      positivity
    have := (ENNReal.ofReal_le_ofReal_iff hP0).1 hbound
    linarith
  -- ε → 0
  have hF12 := (hε_ineq (1 / 2) (by norm_num) (by norm_num)).1
  have hA1int : Integrable A1 μ := by
    refine Integrable.mono' hF12 hA1m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hA10 x)]
    have := hA20 x
    linarith
  have hA2int : Integrable A2 μ := by
    refine Integrable.mono' (hF12.const_mul 2) hA2m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hA20 x)]
    have := hA10 x
    linarith
  refine ⟨hA1int, hA2int, ?_⟩
  have hlim : Tendsto (fun ε : ℝ => ∫ x, A1 x ∂μ + (1 - ε) * ∫ x, A2 x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, A1 x ∂μ + (1 - 0) * ∫ x, A2 x ∂μ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by fun_prop : Continuous fun ε : ℝ => ∫ x, A1 x ∂μ + (1 - ε) * ∫ x, A2 x ∂μ).continuousAt.tendsto
  have := le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    have := (hε_ineq ε hε.1 hε.2).2
    rw [integral_add hA1int (hA2int.const_mul _), integral_const_mul] at this
    exact this)
  simpa using this

end HRS.MS.Spec
