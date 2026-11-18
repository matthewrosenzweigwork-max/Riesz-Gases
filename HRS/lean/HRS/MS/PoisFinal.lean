import HRS.MS.PoisResAux2
import HRS.Whole.Thermal

/-!
# POIS-FINAL: the three Poisson rows from the master theorem `pois_resolvent`

* `affine_poisson_proof : type_of% @HRS.Whole.affine_poisson` (S4.2),
* `affine_poisson_higher_proof : type_of% @HRS.Whole.affine_poisson_higher` (S4.3),
* `affine_poisson_deriv_proof : type_of% @HRS.Whole.affine_poisson_deriv` (S4.8b).

All three are read off `HRS.MS.PoisRes.pois_resolvent` (the resolvent integral `χ = ∫_0^∞ P_t r dt`).
For S4.2/S4.3 the data `r ∈ C_b^m` is used with `D = cbNorm m r` (derivatives of order `1..m`) and
`D' = cbNorm 2 r` (orders `≤ 2`); the master theorem provides the low-order bounds for the same `χ`.
The hypothesis `Integrable r μ` of the frozen statements is not needed (it is automatic).
`d ≥ 1` is not needed either (the proof of the master theorem treats `d = 0` uniformly).
Helper lemmas carry the prefix `rf_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.PoisFinal

variable {d : ℕ}

theorem rf_cb_nonneg {k : ℕ} (r : Euc d → ℝ) : 0 ≤ cbNorm k r :=
  Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

theorem rf_cb_le {k : ℕ} {r : Euc d → ℝ} (h : MemCb k r) {j : ℕ} (hj : j ≤ k) (y : Euc d) :
    ‖iteratedFDeriv ℝ j r y‖ ≤ cbNorm k r := by
  unfold cbNorm
  calc ‖iteratedFDeriv ℝ j r y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j r z‖ := le_ciSup (h.2 j hj) y
    _ ≤ _ := Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j r z‖)
        (fun _ _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem rf_memCb_two {m : ℕ} (hm : 2 ≤ m) {r : Euc d → ℝ} (h : MemCb m r) : MemCb 2 r :=
  ⟨h.1.of_le (by exact_mod_cast hm), fun j hj => h.2 j (hj.trans hm)⟩

theorem rf_hasCb_two {m : ℕ} (hm : 2 ≤ m) {Mb : ℝ} {B : Euc d → Euc d} (h : HasCbBound m Mb B) :
    HasCbBound 2 Mb B :=
  ⟨h.1.of_le (by exact_mod_cast hm), fun j hj x => h.2 j (hj.trans hm) x⟩

/-- the `IsPoissonSolution` conclusions from the master theorem data at level `2`. -/
theorem rf_isSol {q : ℝ} {B : Euc d → Euc d} {μ : Measure (Euc d)} {r : Euc d → ℝ} {χ : Euc d → ℝ}
    {C2 Cl2 : ℝ} (hr : MemCb 2 r) (h2 : ContDiff ℝ 2 χ) (hint : Integrable χ μ)
    (hmean : ∫ x, χ x ∂μ = 0) (heq : ∀ x, poissonOp (fun x => -q • x + B x) χ x = r x)
    (hder : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ C2 * cbNorm 2 r)
    (hlog : ∀ x, |χ x| ≤ Cl2 * (cbNorm 2 r + cbNorm 2 r) * (1 + Real.log (2 + ‖x‖))) :
    IsPoissonSolution (fun x => -q • x + B x) μ r (2 * |Cl2| + 2 * |C2|) χ := by
  have hcb := rf_cb_nonneg (k := 2) r
  refine ⟨h2, hint, hmean, heq, fun x => ?_, fun x y => ?_⟩
  · refine (hlog x).trans ?_
    have hl : 0 ≤ 1 + Real.log (2 + ‖x‖) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + ‖x‖ by linarith [norm_nonneg x])
      linarith
    have : Cl2 * (cbNorm 2 r + cbNorm 2 r) ≤ (2 * |Cl2| + 2 * |C2|) * cbNorm 2 r := by
      nlinarith [le_abs_self Cl2, abs_nonneg C2, mul_nonneg hcb (abs_nonneg Cl2),
        mul_nonneg hcb (abs_nonneg C2)]
    nlinarith [mul_le_mul_of_nonneg_right this hl]
  · have h1 : ‖gradient χ x‖ = ‖iteratedFDeriv ℝ 1 χ x‖ := by
      rw [norm_iteratedFDeriv_one]
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _
    rw [h1]
    have a1 := hder 1 le_rfl (by norm_num) x
    have a2 := hder 2 (by norm_num) le_rfl y
    nlinarith [le_abs_self C2, abs_nonneg Cl2, mul_nonneg hcb (abs_nonneg Cl2),
      mul_nonneg hcb (abs_nonneg C2), mul_le_mul_of_nonneg_right (le_abs_self C2) hcb]

/-- **S4.2** `affine_poisson`. -/
theorem affine_poisson_proof : type_of% @HRS.Whole.affine_poisson := by
  intro d hd q Mb m₂ hq
  obtain ⟨Cm, Cl, C2, Cl2, h⟩ := HRS.MS.PoisRes.pois_resolvent (d := d) q Mb m₂ hq 2 le_rfl
  refine ⟨2 * |Cl2| + 2 * |C2|, fun B hB μ hμ hμ2 hm2 r hr _ hcen => ?_⟩
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ cbNorm 2 r :=
    fun j h1 h2 x => rf_cb_le hr h2 x
  obtain ⟨χ, h1, h2, h3, h4, -, -, h7⟩ := h B hB μ hμ hμ2 hm2 r hr.1 (cbNorm 2 r) hD hcen
  obtain ⟨g1, g2⟩ := h7 (cbNorm 2 r) hD
  exact ⟨χ, rf_isSol hr h1 h2 h3 h4 g1 (g2 (cbNorm 2 r) (fun x => rf_cb_le hr (Nat.zero_le _) x |>
    fun h => by simpa using h))⟩

/-- **S4.3** `affine_poisson_higher`. -/
theorem affine_poisson_higher_proof : type_of% @HRS.Whole.affine_poisson_higher := by
  intro d hd q Mb m₂ hq m hm
  obtain ⟨Cm, Cl, C2, Cl2, h⟩ := HRS.MS.PoisRes.pois_resolvent (d := d) q Mb m₂ hq m hm
  refine ⟨2 * |Cl2| + 2 * |C2|, (m : ℝ) * |Cm|, fun B hB μ hμ hμ2 hm2 r hr _ hcen => ?_⟩
  have hr2 := rf_memCb_two hm hr
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ cbNorm m r :=
    fun j h1 h2 x => rf_cb_le hr h2 x
  have hD2 : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ cbNorm 2 r :=
    fun j h1 h2 x => rf_cb_le hr2 h2 x
  obtain ⟨χ, h1, h2, h3, h4, h5, -, h7⟩ := h B hB μ hμ hμ2 hm2 r hr.1 (cbNorm m r) hD hcen
  obtain ⟨g1, g2⟩ := h7 (cbNorm 2 r) hD2
  have hM0 : ∀ x, ‖r x‖ ≤ cbNorm 2 r := fun x => by
    have := rf_cb_le hr2 (Nat.zero_le _) x
    simpa using this
  refine ⟨χ, rf_isSol hr2 (h1.of_le (by exact_mod_cast hm)) h2 h3 h4 g1 (g2 _ hM0), h1, fun x => ?_⟩
  have hcb := rf_cb_nonneg (k := m) r
  have hb : ∀ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ |Cm| * cbNorm m r := fun j =>
    (h5 ((j : ℕ) + 1) (by omega) (by omega) (x j)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) hcb)
  calc ∑ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ ∑ _j : Fin m, |Cm| * cbNorm m r :=
        Finset.sum_le_sum fun j _ => hb j
    _ = (m : ℝ) * |Cm| * cbNorm m r := by simp; ring

/-- **S4.8b** `affine_poisson_deriv`. -/
theorem affine_poisson_deriv_proof : type_of% @HRS.Whole.affine_poisson_deriv := by
  intro d hd q Mb m₂ hq m hm
  obtain ⟨Cm, Cl, C2, Cl2, h⟩ := HRS.MS.PoisRes.pois_resolvent (d := d) q Mb m₂ hq m hm
  refine ⟨Cm, fun B hB μ hμ hμ2 hm2 r hr D hD hcen => ?_⟩
  obtain ⟨χ, h1, h2, h3, h4, h5, -⟩ := h B hB μ hμ hμ2 hm2 r hr D hD hcen
  exact ⟨χ, h1, h2, h3, h4, h5⟩

end HRS.MS.PoisFinal
