import HRS.MS.WlTrAux1
import HRS.MS.WlSmlAux2

/-!
# HRS.MS.WlTrAux2 -- the family ensembles `P` (kernel `K`) and `R0` (kernel `q_M`), `R_N` as a field law,
Wu's inequality with pole weights (WL-5, part 2)

Packet WL-5 of `docs/WR_LOG_PLAN.md` (Step 7).  Infrastructure lemmas, not manuscript rows.  Namespace
`HRS.MS.Wl`, helper prefix `wl5_`.  `K = sphericalLogKernel`, `q_M = wl_qm M`, `Ψ = wl_psi M`,
`μ = withDensityReal ρ`, `λ = β/N`, `b = nλ`; the field of the family is
`ψ_q = (nλ) rowIntE q μ + g` (`wl4b_psi`, `g = wl4b_g = h_N + v - λ ∑ t_a K(·, z_a)`).

* `wl5_fieldLaw_congr_q`: the field ensemble depends on the weak potential only through `V.q`.
* `wl5_RN_eq_fieldLaw`: the calibrated reference `wl4_RN` of a field ensemble `fieldLaw V ψ λ n` is the field
  ensemble of `ψ + ⟪t, Ξ⟫` (a bounded perturbation, `IsField` with the constants shifted by the bound).
* `wl5_P_eq_tilted`: the exact density of `P = fieldLaw V_K ψ_K λ n` against `R0 = fieldLaw V_q ψ_q λ n`:
  `P = R0` tilted by `-(b/2) ‖S_n‖²` (the energy of `K` is that of `q_M` plus that of the head `k_M`, a.e.,
  and `n 𝖥_n^{k_M} = ½‖S_n‖² - ½ k0`, `energy_identity_P`).
* `wl5_wu_linear`, `wl5_resampling_w`: Wu's inequality for a field ensemble with a pole weight: if
  `ψ ≤ M0 - w` then `Var(∑ f(y_i)) ≤ 2 n e^{M0 + Λ} ∫ |f|² e^{-w} dμ` (`evariance`, no integrability needed): the
  conditional density of one coordinate is `≤ e^{M0 + Λ} e^{-w}` (`siteKernel_fieldDensity`, Jensen
  `exp_le_integral_siteU`).

Adjustment with respect to the plan (documented, harmless): the poles with weights `t_a` are part of the field
(as in `WlFam`), the pole law of the TeX is a member of the family.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### The field ensemble depends on `V` only through `V.q` -/

section Congr

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

lemma wl5_fieldDensity_congr {V V' : WeakPotential μ} (h : V.q = V'.q) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) :
    fieldDensity V ψ lam n = fieldDensity V' ψ lam n := by
  have hp : ∀ {m : ℕ} (y : Fin m → E), HRS.External.pairEnergy V y = HRS.External.pairEnergy V' y := by
    intro m y
    unfold HRS.External.pairEnergy
    rw [h]
  funext y
  unfold fieldDensity fieldNorm fieldWeight
  simp only [hp]

lemma wl5_fieldLaw_congr_q {V V' : WeakPotential μ} (h : V.q = V'.q) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) :
    fieldLaw V ψ lam n = fieldLaw V' ψ lam n := by
  unfold fieldLaw
  rw [wl5_fieldDensity_congr h]

/-- The pinned law with no pins is the field law of `V.φ`. -/
lemma wl5_pinnedLaw_empty (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    pinnedLaw V lam n (fun e : Empty => e.elim) = fieldLaw V V.φ lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

lemma wl5_pinnedDensity_empty (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    pinnedDensity V lam n (fun e : Empty => e.elim) = fieldDensity V V.φ lam n := by
  unfold pinnedDensity
  congr 1
  funext z
  simp [pinField]

variable [IsProbabilityMeasure μ]

/-- `exp` of the field exponent is integrable against the product measure (bounded above, measurable). -/
lemma wl5_integrable_exp_field {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (n : ℕ) :
    Integrable (fun y : Fin n → E => Real.exp (∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y))
      (Measure.pi fun _ : Fin n => μ) := by
  have hfm : Measurable (fun y : Fin n → E => ∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y) :=
    (Finset.measurable_sum _ fun i _ => hψ.measurable.comp (measurable_pi_apply i)).sub
      ((measurable_pairEnergy V).const_mul _)
  refine Integrable.of_bound (Real.measurable_exp.comp hfm).aestronglyMeasurable (Real.exp (n * M))
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have h1 : ∑ i, ψ (y i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hψ.le _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 := mul_nonneg hlam (pairEnergy_nonneg V y)
  linarith

end Congr

/-! ### `R_N` as a field ensemble -/

section RNField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ}

/-- Tilting a field ensemble by `Yf t = ∑ ⟪t, Ξ(y_i)⟫` adds the bounded one-body field `⟪t, Ξ⟫`. -/
theorem wl5_tilt_Yf_eq_fieldLaw {V : WeakPotential μ} {ψ : Euc d → ℝ} {M M₁ lam : ℝ}
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hΨ : CalFeat Ψ B) (t : H) {c : ℝ}
    (hc : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ c) (n : ℕ) :
    (fieldLaw V ψ lam n).tilted (Yf μ Ψ t) =
      fieldLaw V (fun x => ψ x + inner ℝ t (Xi μ Ψ x)) lam n := by
  have hψ' : IsField μ (fun x => ψ x + inner ℝ t (Xi μ Ψ x)) (M + c) (M₁ + c) := by
    have := wl_isField_add hψ (wl_isField_bdd (μ := μ) (v := fun x => inner ℝ t (Xi μ Ψ x))
      (continuous_const.inner hΨ.continuous_Xi).measurable hc)
    exact this
  rw [wl4b_fieldLaw_eq_tilted hψ hlam n, wl4b_fieldLaw_eq_tilted hψ' hlam n,
    tilted_tilted (wl5_integrable_exp_field (V := V) hψ hlam n)]
  congr 1
  funext y
  simp only [Pi.add_apply, Yf, Finset.sum_add_distrib]
  ring

/-- `R_N = wl4_RN` of a field ensemble is the field ensemble with the calibration field added
(any bound `c` on `⟪t, Ξ⟫`). -/
theorem wl5_RN_eq_fieldLaw {V : WeakPotential μ} {ψ : Euc d → ℝ} {M M₁ lam : ℝ}
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hΨ : CalFeat Ψ B) (c β : ℝ) (n : ℕ)
    (hc : ∀ x, |inner ℝ (wl4_tN (1 / (n : ℝ)) β μ Ψ (fieldLaw V ψ lam n)) (Xi μ Ψ x)| ≤ c) :
    wl4_RN (1 / (n : ℝ)) β μ Ψ (fieldLaw V ψ lam n) =
      fieldLaw V (fun x => ψ x +
        inner ℝ (wl4_tN (1 / (n : ℝ)) β μ Ψ (fieldLaw V ψ lam n)) (Xi μ Ψ x)) lam n :=
  wl5_tilt_Yf_eq_fieldLaw hψ hlam hΨ _ hc n

end RNField

/-! ### The exact density of `P` against `R0` -/

section Density

open HRS.Whole

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

lemma wl5_wr8_km (M : ℕ) : Wr8Ok μ (wl_km (d := d) M) :=
  wl4b_wr8_of_bdd (wl_km_measurable M) (b := wl_k0 M) fun x y => by
    rw [abs_of_nonneg (wl_km_nonneg M x y)]
    exact wl_km_le_k0 M x y

/-- **`P` is `R0` tilted by `-(b/2)‖S_n‖²`.**  `P = fieldLaw V_K ((nλ) K*μ + g) λ n`,
`R0 = fieldLaw V_q ((nλ) q_M*μ + g) λ n`, `b = nλ`, `V_K.q = K`, `V_q.q = q_M`, `1 ≤ n`, `μ` atomless. -/
theorem wl5_P_eq_tilted (hat : ∀ x, μ {x} = 0) {aK aq : ℝ}
    (hK : EWeakKernel μ aK (fun x y : Euc d => sphericalLogKernel x y)) (haK : 0 ≤ aK) (M : ℕ)
    (hq : EWeakKernel μ aq (wl_qm (d := d) M)) (haq : 0 ≤ aq) {g : Euc d → ℝ} {G0 m : ℝ}
    (hg : IsField μ g G0 m) {lam : ℝ} (hlam : 0 ≤ lam) {n : ℕ} (hn : 1 ≤ n)
    (VK VQ : WeakPotential μ) (hVK : VK.q = fun x y => sphericalLogKernel x y)
    (hVQ : VQ.q = wl_qm (d := d) M) :
    fieldLaw VK (fun x => ((n : ℝ) * lam) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x + g x)
        lam n =
      (fieldLaw VQ (fun x => ((n : ℝ) * lam) * rowIntE (wl_qm (d := d) M) μ x + g x) lam n).tilted
        (fun X : Fin n → Euc d => -(((n : ℝ) * lam) / 2) * ‖wr11b_Sstat μ (wl_psi M) X‖ ^ 2) := by
  set π : Measure (Fin n → Euc d) := Measure.pi fun _ : Fin n => μ with hπ
  have hnl : 0 ≤ (n : ℝ) * lam := mul_nonneg (Nat.cast_nonneg n) hlam
  have hψK := wl_isField_add (wl_isField_rowInt hK haK hnl) hg
  have hψQ := wl_isField_add (wl_isField_rowInt hq haq hnl) hg
  have hn0 : 0 < n := hn
  rw [wl4b_fieldLaw_eq_tilted hψK hlam n, wl4b_fieldLaw_eq_tilted hψQ hlam n,
    tilted_tilted (wl5_integrable_exp_field (V := VQ) hψQ hlam n)]
  set IK : ℝ := ∫ x, ∫ z, sphericalLogKernel x z ∂μ ∂μ with hIK
  set Iq : ℝ := ∫ x, ∫ z, wl_qm (d := d) M x z ∂μ ∂μ with hIq
  set c₀ : ℝ := ((n : ℝ) * lam) * wl_k0 M / 2 + lam * (n : ℝ) ^ 2 / 2 * (IK - Iq) with hc₀
  refine (tilted_congr ?_).trans (wr11b_tilted_add_const π _ c₀)
  filter_upwards [ae_injective_pi_Euc (N := n) hat] with y hy
  have e1 := wl4b_exponent_eq VK hVK hn lam g y
  have e2 := wl4b_exponent_eq VQ hVQ hn lam g y
  have hoff := modEnergyE_congr_offdiag hat (k₁ := fun x z : Euc d => sphericalLogKernel x z)
    (k₂ := fun x z => wl_km (d := d) M x z + wl_qm M x z) (fun x z hxz => wl_K_eq M hxz) y hy
  have hadd := wr8_modEnergyE_add (N := n) (wl5_wr8_km (μ := μ) M) (hq.rowOKE haq).wr8_ok y
  have hid := energy_identity_P (wl_psi_hyp (d := d) M) μ hn y
  have hS : wr11b_Sstat μ (wl_psi M) y =
      (Real.sqrt n)⁻¹ • ∑ i, (wl_psi M (y i) - ∫ z, wl_psi M z ∂μ) := wr11b_Sstat_eq hn y
  rw [← hS] at hid
  have hkm : HRS.Whole.pairEnergy (wl_km (d := d) M) y μ = modEnergyE (wl_km (d := d) M) y μ := rfl
  rw [hkm] at hid
  have hE := hoff.trans hadd
  show ∑ i, (((n : ℝ) * lam) * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ (y i) + g (y i)) -
      lam * HRS.External.pairEnergy VK y =
    (∑ i, (((n : ℝ) * lam) * rowIntE (wl_qm (d := d) M) μ (y i) + g (y i)) -
      lam * HRS.External.pairEnergy VQ y) +
      (-(((n : ℝ) * lam) / 2) * ‖wr11b_Sstat μ (wl_psi M) y‖ ^ 2) + c₀
  rw [e1, e2, hc₀]
  linear_combination (-(lam * (n : ℝ) ^ 2)) * hE - (lam * n) * hid

end Density

/-! ### Wu's inequality for a field ensemble, with a pole weight -/

section Wu

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ}
  {q : E → E → ℝ} {φ : E → ℝ} {M M₁ β : ℝ} {N n : ℕ}

/-- **Wu's linear inequality for a field ensemble**: `Var(∑ f(y_i)) ≤ 2 n Var_π(f)`, `π` the one-point
marginal; `hκ` is the Dobrushin smallness of `wlPot hq ha hφ` (`V` is any weak potential with `V.q = q`). -/
theorem wl5_wu_linear [NeZero n] (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁)
    (hβ : 0 ≤ β) (hN0 : 0 < N) (hn : n ≤ N) (hκ : weakKappa (wlPot hq ha hφ) β ≤ 1 / 2)
    (V : WeakPotential μ) (hV : V.q = q) (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) (fieldLaw V φ (β / N) n) ≤
      2 * n * evariance f ((fieldLaw V φ (β / N) n).map (fun x => x 0)) := by
  have hVV : V.q = (wlPot hq ha hφ).q := hV
  rw [wl5_fieldLaw_congr_q hVV]
  have := weak_linear_variance_symm (B := Empty) (wlPot hq ha hφ) hβ hN0 (by simpa using hn)
    (fun e => e.elim) hκ f hf
  rw [wl5_pinnedLaw_empty] at this
  exact this

/-- **Resampling with a pole weight.**  If `φ ≤ M0 - w` (`w` the pole weight `λ ∑ t_a K(·, z_a)`) and
`Λ ≥ M₁ + (β/N) n a`, then `Var(∑ f(y_i)) ≤ 2 n e^{M0 + Λ} ∫ |f|² e^{-w} dμ` (`evariance`, no
integrability): each conditional density is `≤ e^{M0 + Λ} e^{-w} μ`. -/
theorem wl5_resampling_w [NeZero n] (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hφ : IsField μ φ M M₁)
    (hβ : 0 ≤ β) (hN0 : 0 < N) (hn : n ≤ N) (hκ : weakKappa (wlPot hq ha hφ) β ≤ 1 / 2)
    (V : WeakPotential μ) (hV : V.q = q) {M₀ Λ : ℝ} {w : E → ℝ} (hw : ∀ z, φ z ≤ M₀ - w z)
    (hΛ : M₁ + (β / N) * n * a ≤ Λ) (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) (fieldLaw V φ (β / N) n) ≤
      2 * n * (ENNReal.ofReal (Real.exp (M₀ + Λ)) *
        ∫⁻ z, ENNReal.ofReal (Real.exp (-w z)) * ‖f z‖ₑ ^ 2 ∂μ) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hVV : V.q = (wlPot hq ha hφ).q := hV
  rw [wl5_fieldLaw_congr_q hVV]
  set V' := wlPot hq ha hφ with hV'
  have hF : Measurable fun y : Fin n → E => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have key := weak_resampling V' hβ hN0 (by simpa using hn) (fun e : Empty => e.elim) hκ _ hF
  rw [wl5_pinnedLaw_empty] at key
  simp only [wl5_pinnedDensity_empty] at key
  simp only [show V'.φ = φ from rfl] at key
  haveI hP : IsProbabilityMeasure (fieldLaw V' φ (β / N) n) :=
    (fieldSpec (V := V') hφ hlam n).isProb
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (M₀ + Λ)) *
    ∫⁻ z, ENNReal.ofReal (Real.exp (-w z)) * ‖f z‖ₑ ^ 2 ∂μ with hC
  have hsite : ∀ (i : Fin n) (x : Fin n → E),
      evariance (fun z => ∑ k, f (Function.update x i z k)) (siteKernel μ (fieldDensity V' φ (β / N) n) i x)
        ≤ C := by
    intro i x
    haveI hν : IsProbabilityMeasure (siteKernel μ (fieldDensity V' φ (β / N) n) i x) :=
      ((fieldSpec (V := V') hφ hlam n).isMarkov i).isProbabilityMeasure x
    set c : ℝ := ∑ k ∈ Finset.univ.erase i, f (x k) with hc
    have hmeas : Measurable fun z => ∑ k, f (Function.update x i z k) :=
      Finset.measurable_sum _ fun k _ => hf.comp ((measurable_pi_apply k).comp
        (measurable_update x (a := i)))
    refine (evariance_le_lintegral_sub _ hmeas.aestronglyMeasurable c).trans ?_
    have hshift : ∀ z, (∑ k, f (Function.update x i z k)) - c = f z := by
      intro z
      rw [sum_update_psi f x i z, hc]
      ring
    simp_rw [hshift]
    rw [siteKernel_fieldDensity hφ hlam i x]
    have hmd : Measurable fun z => ENNReal.ofReal
        (siteU V' φ (β / N) i x z / ∫ z', siteU V' φ (β / N) i x z' ∂μ) :=
      ENNReal.measurable_ofReal.comp ((measurable_siteU hφ.measurable V' _ i x).div_const _)
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable μ hmd
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
    have hZ : Real.exp (-Λ) ≤ ∫ z', siteU V' φ (β / N) i x z' ∂μ :=
      le_trans (Real.exp_le_exp.2 (by
        have : V'.γ = a := rfl
        rw [this]; linarith)) (exp_le_integral_siteU (V := V') hφ hlam i x)
    have hZpos : 0 < ∫ z', siteU V' φ (β / N) i x z' ∂μ := lt_of_lt_of_le (Real.exp_pos _) hZ
    rw [hC, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hZpos]
    have h1 : siteU V' φ (β / N) i x z ≤ Real.exp (M₀ - w z) := by
      unfold siteU
      refine Real.exp_le_exp.2 ?_
      have := mul_nonneg hlam (sumq_nonneg V' i x z)
      have h2 : φ z ≤ M₀ - w z := hw z
      linarith
    calc siteU V' φ (β / N) i x z ≤ Real.exp (M₀ - w z) := h1
      _ = Real.exp (M₀ + Λ) * Real.exp (-w z) * Real.exp (-Λ) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by positivity)
  refine key.trans ?_
  have hbound : ∀ i : Fin n, ∫⁻ x, evariance (fun z => ∑ k, f (Function.update x i z k))
      (siteKernel μ (fieldDensity V' φ (β / N) n) i x) ∂(fieldLaw V' φ (β / N) n) ≤ C := by
    intro i
    calc _ ≤ ∫⁻ _x, C ∂(fieldLaw V' φ (β / N) n) := lintegral_mono fun x => hsite i x
      _ = C := by simp
  calc 2 * ∑ i, ∫⁻ x, evariance (fun z => ∑ k, f (Function.update x i z k))
        (siteKernel μ (fieldDensity V' φ (β / N) n) i x) ∂(fieldLaw V' φ (β / N) n)
      ≤ 2 * ∑ _i : Fin n, C := by gcongr with i; exact hbound i
    _ = 2 * n * C := by simp [mul_assoc]

end Wu

end HRS.MS.Wl
