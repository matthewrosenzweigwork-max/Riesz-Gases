import HRS.MS.ThCorrUDAux1

/-!
# TC-U2 (part 2): uniform `TcRef` / `TcDrift` for `0 < s < d - 1` and for `s = 0`

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu2_`.

* `tcu2_final`: generic assembly.  If every thermal density of the compact parameter set is a `TcuInst` for a potential
  operator `Uop` and `tcu2_boot` holds for `Uop`, then `TcRef` (for every `N`, one `S`) and `TcDrift` (for every `m`, one
  `Mb`) hold uniformly.
* `tcu_uniform_easy` (`0 < s < d - 1`) and `tcu_uniform_zero` (`s = 0`): the two main theorems of this file, from
  `tcu_apriori_pos` / `tcu_apriori_zero` (TCU1) and `tcu2_boot`.

Quantifier order of the main statements: `∃ c M₀ m₂, ∀ N, ∃ S, ∀ a β ∈ [am, ap] × [βm, βp], TcRef ...` and
`∀ m, ∃ Mb, ∀ a β, TcDrift d ρ (β * a) Mb m₂ m`.  The drift constant `q = β * a` is the Gaussian exponent
`ρ = exp (-(q/2) ‖x‖² + G)` of `gap_of_logDensity`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.TcU

open HRS HRS.Whole HRS.MS.LogReg HRS.MS.Thm HRS.MS.Can2

variable {d : ℕ}

/-- Generic assembly of `TcRef` and `TcDrift` from instances and the uniform bootstrap. -/
theorem tcu2_final {s : ℝ} {Uop : (Euc d → ℝ) → Euc d → ℝ} {am ap βm βp b C0 z₀ m₂ : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) (hz₀ : 0 < z₀) (hb : 0 < b)
    (hC0 : 0 < C0)
    (hinst : ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      TcuInst d Uop am ap βm βp b C0 z₀ a β (tcuZ d s a β) (thermalDensity d s a β) ∧
      HRS.Whole.IsProbDensity (thermalDensity d s a β) ∧
      Integrable (fun x => ‖x‖ ^ 2 * thermalDensity d s a β x) ∧
      (∫ x, ‖x‖ ^ 2 * thermalDensity d s a β x) ≤ m₂)
    (hboot : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ k M) :
    (∀ N : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      HRS.MS.TcDefs.TcRef d (thermalDensity d s a β) C0 b S N) ∧
    (∀ m : ℕ, ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      HRS.MS.TcDefs.TcDrift d (thermalDensity d s a β) (β * a) Mb m₂ m) := by
  refine ⟨fun N => ?_, fun m => ?_⟩
  · obtain ⟨S, hS0, hS⟩ := tcu2_ref_of_boot ham hβm hap hβp hz₀ hb hC0 hboot N
    refine ⟨S, hS0, fun a β h1 h2 h3 h4 => ?_⟩
    obtain ⟨hi, hp, -, -⟩ := hinst a β h1 h2 h3 h4
    exact hS a β _ _ hi hp
  · obtain ⟨Mb, hMb0, hMb⟩ := tcu2_drift_of_boot (b := b) (C0 := C0) (Uop := Uop) ham hβm hap hβp hz₀
      hboot m
    refine ⟨Mb, hMb0, fun a β h1 h2 h3 h4 => ?_⟩
    obtain ⟨hi, hp, hmom, hm₂⟩ := hinst a β h1 h2 h3 h4
    exact hMb a β _ _ m₂ hi (Integrable.of_integral_ne_zero (by rw [hp.integral_one]; norm_num))
      hp.integral_one hmom hm₂

/-! ### `0 < s < d - 1` -/

/-- The thermal equation of `thermalDensity` with the normaliser `tcuZ`, for `s > 0`. -/
lemma tcu2_data_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) :
    HRS.Whole.IsProbDensity (thermalDensity d s a β) ∧
    ∀ x, thermalDensity d s a β x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 +
      rege_U s (thermalDensity d s a β) x)) / tcuZ d s a β := by
  have hth := can2_isThermalDensity_pos hd hs0 hsd ha hβ
  obtain ⟨-, -, -, -, -, -, -, -, hU⟩ := rege_data hd hs0 hsd ha hβ
  refine ⟨hth.1, fun x => ?_⟩
  have h2 := hth.2 x
  have h3 : HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) x =
      rege_U s (thermalDensity d s a β) x := hU x
  rw [h2, h3]
  rfl

/-- The uniform bootstrap for `0 < s < d - 1`. -/
theorem tcu2_boot_easy (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs1 : s < (d : ℝ) - 1)
    {am ap βm βp b C0 z₀ : ℝ} (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀) (hb : 0 < b) (hC0 : 0 ≤ C0) :
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d (rege_U s) am ap βm βp b C0 z₀ k M := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨θ, hθ0, hθ1, hθd⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ s + 1 + θ < d := by
    refine ⟨min 1 (((d : ℝ) - s - 1) / 2), lt_min one_pos (by linarith), min_le_left _ _, ?_⟩
    have := min_le_right (1 : ℝ) (((d : ℝ) - s - 1) / 2)
    linarith
  exact tcu2_boot hd1 (σ := s + 1) (lam := s) (by linarith) (by linarith) hs0.le
    (rege_kap_measurable s).aestronglyMeasurable (rege_kap_norm_le s) (Lop := rege_L s)
    (rege_L_opnorm hs0.le) (fun F hm hF => rege_potential hd1 hs0 hθ0 hθ1 hθd hm hF)
    (rege_W_eq_conv s) ham hβm hap hβp hz₀ hb hC0

/-- **TC-U2 (`0 < s < d - 1`).**  `TcRef` and `TcDrift` for the thermal densities, uniformly over compact
`(a, β)`. -/
theorem tcu_uniform_easy (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs1 : s < (d : ℝ) - 1)
    {am ap βm βp : ℝ} (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ c M₀ m₂ : ℝ, 0 < c ∧ 0 < M₀ ∧
      (∀ N : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcRef d (thermalDensity d s a β) M₀ c S N) ∧
      (∀ m : ℕ, ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcDrift d (thermalDensity d s a β) (β * a) Mb m₂ m) := by
  have hd1 : 1 ≤ d := by omega
  have hsd : s < d := by linarith
  obtain ⟨c, M₀, z₀, m₂, UB, hc, hM₀, hz₀, hall⟩ :=
    tcu_apriori_pos hd1 hs0 hsd ham hβm hap hβp
  refine ⟨c, M₀, m₂, hc, hM₀, tcu2_final (s := s) (Uop := rege_U s) ham hβm hap hβp hz₀ hc hM₀ ?_
    (tcu2_boot_easy hd hs0 hs1 ham hβm hap hβp hz₀ hc hM₀.le)⟩
  intro a β h1 h2 h3 h4
  obtain ⟨hZ, hgauss, hint, hm2, -⟩ := hall a β h1 h2 h3 h4
  obtain ⟨hP, heq⟩ := tcu2_data_pos hd hs0 hsd (ham.trans_le h1) (hβm.trans_le h3)
  exact ⟨⟨h1, h2, h3, h4, hZ, hP.measurable, heq, hgauss⟩, hP, hint, hm2⟩

/-! ### `s = 0` -/

/-- The thermal equation of `thermalDensity` with the normaliser `tcuZ`, for `s = 0`. -/
lemma tcu2_data_zero (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    HRS.Whole.IsProbDensity (thermalDensity d 0 a β) ∧
    ∀ x, thermalDensity d 0 a β x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 +
      lreg_U (thermalDensity d 0 a β) x)) / tcuZ d 0 a β := by
  have hth := can2_isThermalDensity_log hd ha hβ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hU⟩ := lreg_data hd ha hβ
  refine ⟨hth.1, fun x => ?_⟩
  have h2 := hth.2 x
  have h3 : HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal (thermalDensity d 0 a β)) x =
      lreg_U (thermalDensity d 0 a β) x := hU x
  rw [h2, h3]
  rfl

/-- The uniform bootstrap for `s = 0`. -/
theorem tcu2_boot_zero (hd : 2 ≤ d) {am ap βm βp b C0 z₀ : ℝ} (ham : 0 < am) (hβm : 0 < βm)
    (hap : am ≤ ap) (hβp : βm ≤ βp) (hz₀ : 0 < z₀) (hb : 0 < b) (hC0 : 0 ≤ C0) :
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d lreg_U am ap βm βp b C0 z₀ k M := by
  have hd1 : 1 ≤ d := by omega
  have hσ : (1 : ℝ) < d := by exact_mod_cast hd
  exact tcu2_boot hd1 (σ := 1) (lam := 1) hσ zero_le_one zero_le_one
    lreg_kap_measurable.aestronglyMeasurable lreg_kap_le (Lop := innerSL ℝ) (norm_innerSL_le ℝ)
    (fun F hm hF => lreg_potential hd hm hF) lreg_W_eq_conv ham hβm hap hβp hz₀ hb hC0

/-- **TC-U2 (`s = 0`).**  `TcRef` and `TcDrift` for the logarithmic thermal densities, uniformly over compact
`(a, β)`. -/
theorem tcu_uniform_zero (hd : 2 ≤ d) {am ap βm βp : ℝ} (ham : 0 < am) (hβm : 0 < βm)
    (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ c M₀ m₂ : ℝ, 0 < c ∧ 0 < M₀ ∧
      (∀ N : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcRef d (thermalDensity d 0 a β) M₀ c S N) ∧
      (∀ m : ℕ, ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcDrift d (thermalDensity d 0 a β) (β * a) Mb m₂ m) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, M₀, z₀, m₂, L2, UB, hc, hM₀, hz₀, hall⟩ := tcu_apriori_zero hd1 ham hβm hap hβp
  refine ⟨c, M₀, m₂, hc, hM₀, tcu2_final (s := 0) (Uop := lreg_U) ham hβm hap hβp hz₀ hc hM₀ ?_
    (tcu2_boot_zero hd ham hβm hap hβp hz₀ hc hM₀.le)⟩
  intro a β h1 h2 h3 h4
  obtain ⟨hZ, hgauss, hint, hm2, -⟩ := hall a β h1 h2 h3 h4
  obtain ⟨hP, heq⟩ := tcu2_data_zero hd (ham.trans_le h1) (hβm.trans_le h3)
  exact ⟨⟨h1, h2, h3, h4, hZ, hP.measurable, heq, hgauss⟩, hP, hint, hm2⟩

end HRS.MS.TcU

end
