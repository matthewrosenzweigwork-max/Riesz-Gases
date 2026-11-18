import HRS.PDE.MovEAux3

/-!
# MOVE Aux4: comparison of `L^p` norms of densities for comparable reference measures (`movT_lp_init_limsup`)

`move_lp_upper`: if `Q = Pm.withDensity d`, `Qn = Pm.withDensity dn` (positive real densities) and `c d ≤ dn` a.e., then
`ν ≪ Q` implies `ν ≪ Qn` and `∫ (dν/dQn)^p dQn ≤ c^{1-p} ∫ (dν/dQ)^p dQ`.  Mathlib-only.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS

theorem move_pt {a b c γ p : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hγ : 0 ≤ γ) (hp : 1 < p) (h : c * a ≤ b) :
    b * (b⁻¹ * γ) ^ p ≤ c ^ (1 - p) * (a * (a⁻¹ * γ) ^ p) := by
  have e : ∀ t : ℝ, 0 < t → t * (t⁻¹ * γ) ^ p = t ^ (1 - p) * γ ^ p := by
    intro t ht
    rw [Real.mul_rpow (inv_nonneg.2 ht.le) hγ, Real.inv_rpow ht.le, ← mul_assoc,
      Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  rw [e b hb, e a ha]
  have h1 : b ^ (1 - p) ≤ (c * a) ^ (1 - p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
  rw [Real.mul_rpow hc.le ha.le] at h1
  have h2 : 0 ≤ γ ^ p := Real.rpow_nonneg hγ _
  calc b ^ (1 - p) * γ ^ p ≤ (c ^ (1 - p) * a ^ (1 - p)) * γ ^ p := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

theorem move_lp_upper {α : Type*} [MeasurableSpace α] (Pm : Measure α) [SigmaFinite Pm]
    {ν : Measure α} [IsFiniteMeasure ν] (dd dn : α → ℝ) (hm : Measurable dd) (hmn : Measurable dn)
    (hpos : ∀ x, 0 < dd x) (hposn : ∀ x, 0 < dn x)
    [IsFiniteMeasure (Pm.withDensity fun x => ENNReal.ofReal (dd x))]
    [IsFiniteMeasure (Pm.withDensity fun x => ENNReal.ofReal (dn x))]
    {c : ℝ} (hc : 0 < c) (hle : ∀ᵐ x ∂Pm, c * dd x ≤ dn x)
    (hac : ν ≪ Pm.withDensity fun x => ENNReal.ofReal (dd x)) {p : ℝ} (hp : 1 < p) :
    ν ≪ Pm.withDensity (fun x => ENNReal.ofReal (dn x)) ∧
      ∫⁻ x, (ν.rnDeriv (Pm.withDensity fun x => ENNReal.ofReal (dn x)) x) ^ p
          ∂(Pm.withDensity fun x => ENNReal.ofReal (dn x)) ≤
        ENNReal.ofReal (c ^ (1 - p)) *
          ∫⁻ x, (ν.rnDeriv (Pm.withDensity fun x => ENNReal.ofReal (dd x)) x) ^ p
            ∂(Pm.withDensity fun x => ENNReal.ofReal (dd x)) := by
  have hp0 : 0 < p := by linarith
  have hDm : Measurable fun x => ENNReal.ofReal (dd x) := ENNReal.measurable_ofReal.comp hm
  have hDnm : Measurable fun x => ENNReal.ofReal (dn x) := ENNReal.measurable_ofReal.comp hmn
  have hD0 : ∀ᵐ x ∂Pm, ENNReal.ofReal (dd x) ≠ 0 := ae_of_all _ fun x => (ENNReal.ofReal_pos.2 (hpos x)).ne'
  have hDn0 : ∀ᵐ x ∂Pm, ENNReal.ofReal (dn x) ≠ 0 := ae_of_all _ fun x => (ENNReal.ofReal_pos.2 (hposn x)).ne'
  have hDt : ∀ᵐ x ∂Pm, ENNReal.ofReal (dd x) ≠ ⊤ := ae_of_all _ fun x => ENNReal.ofReal_ne_top
  have hDnt : ∀ᵐ x ∂Pm, ENNReal.ofReal (dn x) ≠ ⊤ := ae_of_all _ fun x => ENNReal.ofReal_ne_top
  have hQPm : Pm.withDensity (fun x => ENNReal.ofReal (dd x)) ≪ Pm := withDensity_absolutelyContinuous _ _
  have hPmQn : Pm ≪ Pm.withDensity (fun x => ENNReal.ofReal (dn x)) :=
    withDensity_absolutelyContinuous' hDnm.aemeasurable hDn0
  have hQnPm : Pm.withDensity (fun x => ENNReal.ofReal (dn x)) ≪ Pm := withDensity_absolutelyContinuous _ _
  refine ⟨hac.trans (hQPm.trans hPmQn), ?_⟩
  have hgt : ∀ᵐ x ∂Pm, ν.rnDeriv Pm x < ⊤ := Measure.rnDeriv_lt_top _ _
  have h1 := Measure.rnDeriv_withDensity_right ν Pm hDm.aemeasurable hD0 hDt
  have h1n := Measure.rnDeriv_withDensity_right ν Pm hDnm.aemeasurable hDn0 hDnt
  rw [lintegral_withDensity_eq_lintegral_mul₀ hDm.aemeasurable
      ((Measure.measurable_rnDeriv _ _).pow_const _).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ hDnm.aemeasurable
      ((Measure.measurable_rnDeriv _ _).pow_const _).aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [h1, h1n, hgt, hle] with x hx hxn hgx hlex
  simp only [Pi.mul_apply]
  rw [hx, hxn]
  generalize ν.rnDeriv Pm x = G at hgx ⊢
  have hγ : G = ENNReal.ofReal G.toReal := (ENNReal.ofReal_toReal hgx.ne).symm
  have key := move_pt (hpos x) (hposn x) hc (ENNReal.toReal_nonneg (a := G)) hp hlex
  have e : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ((ENNReal.ofReal t)⁻¹ * G) ^ p =
      ENNReal.ofReal (t * (t⁻¹ * G.toReal) ^ p) := by
    intro t ht
    rw [hγ, ← ENNReal.ofReal_inv_of_pos ht, ← ENNReal.ofReal_mul (inv_nonneg.2 ht.le),
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (inv_nonneg.2 ht.le) ENNReal.toReal_nonneg) hp0.le,
      ← ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hgx.ne]
  rw [e _ (hposn x), e _ (hpos x), ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  exact ENNReal.ofReal_le_ofReal key

end HRS

end
