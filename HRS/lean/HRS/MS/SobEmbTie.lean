import HRS.MS.SobEmbAux6
import HRS.MS.S1c2Tie

/-!
# SA1 tie: S.A.1 claims 1, 2, 3 (`sobolev_embeds_cb`, `commutatorNorm_le`, `h_embeds_sobolev`)

* `sobolev_embeds_cb_proof : type_of% @HRS.Whole.DecayingDensity.sobolev_embeds_cb`: `W^{m_c,p_c} ↪ C_b^{m_*}`.  The Sobolev
  ladder `sa1_reach_all` from `a₀ = p_c` with `j = ⌊d/p_c⌋` derivatives reaches some `q > d` (`q ≥ p_c`, `1/q ≥ 1/p_c - j/d`);
  Morrey's inequality `sa1_morrey` gives the sup bound with one more derivative, `m_c = m_* + j + 1`.  The real `iSup`s of
  `cbNorm` are bounded by the genuine pointwise bound (no junk value is used).
* `commutatorNorm_le_proof'`: claim 2, the tie of `HRS.S1C2` (`commutatorNorm_le_proof`, conditional on claim 1) with claim 1.
* `h_embeds_sobolev_proof`: claim 3, see below.

## Claim 3 (`HRS.Whole.DecayingDensity.h_embeds_sobolev`)

`h_embeds_sobolev_proof : type_of% @HRS.Whole.DecayingDensity.h_embeds_sobolev`: `H^{Γ_c} ↪ W^{m_c+2,p_c}`.  Route: the Sobolev
ladder `sa1_reach_all` from `a₀ = 2` through `ℓ = ⌊d(1/2-1/p_c)⌋+1` derivatives (`ℓ > d(1/2 - 1/p_c)`) reaches `L^{p_c}`,
`sa1_glue` converts it to `sobolevWNorm`; `Γ_c = m_c + 2 + ℓ`.  The statement is true as stated (hypothesis: integrability of
`‖D^j f‖²` for `j ≤ Γ_c`; the conclusion's integrals are then genuine since the proof shows `‖D^j f‖^{p_c}` integrable).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

open HRS.Whole

theorem h_embeds_sobolev_proof : type_of% @HRS.Whole.DecayingDensity.h_embeds_sobolev := by
  intro d s hs0 hsd c
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) < d := by linarith
    exact_mod_cast this.le
  have hp2 : 2 < c.integrability := HRS.Whole.DecayingDensity.two_lt_integrability hs0 hsd c
  set p := c.integrability with hp
  set ℓ : ℕ := ⌊(d : ℝ) * (1 / 2 - 1 / p)⌋₊ + 1 with hℓ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlt : (d : ℝ) * (1 / 2 - 1 / p) < ℓ := by
    rw [hℓ]; push_cast; exact Nat.lt_floor_add_one _
  have hge : 1 / (2 : ℝ) - (ℓ : ℝ) / d ≤ 1 / p := by
    have : (1 / 2 - 1 / p) < (ℓ : ℝ) / d := by
      rw [lt_div_iff₀ hdpos]; linarith
    linarith
  have hR : sa1_Reach d 2 ℓ p := sa1_reach_all hd2 (by norm_num) ℓ p hp2.le hge
  obtain ⟨C, hC0, hC⟩ := sa1_glue (d := d) (a0 := 2) (p := p) (by norm_num) (by linarith) hR (c.sobolevIndex + 2)
  refine ⟨C, fun f hf hint => ?_⟩
  have hΓ : c.gammaIndex = c.sobolevIndex + 2 + ℓ := rfl
  rw [hΓ] at hint ⊢
  exact (hC f hf hint).2


theorem sobolev_embeds_cb_proof : type_of% @HRS.Whole.DecayingDensity.sobolev_embeds_cb := by
  intro d s hs0 hsd c
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) < d := by linarith
    exact_mod_cast this.le
  have hp2 : 2 < c.integrability := HRS.Whole.DecayingDensity.two_lt_integrability hs0 hsd c
  set p := c.integrability with hp
  have hp0 : 0 < p := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set j : ℕ := ⌊(d : ℝ) / p⌋₊ with hj
  have hj1 : (j : ℝ) ≤ d / p := Nat.floor_le (by positivity)
  have hj2 : (d : ℝ) / p < j + 1 := Nat.lt_floor_add_one _
  set c0 : ℝ := 1 / p - (j : ℝ) / d with hc0
  have hc0' : c0 = ((d : ℝ) / p - j) / d := by rw [hc0]; field_simp
  have hc00 : 0 ≤ c0 := by rw [hc0']; exact div_nonneg (by linarith) hdpos.le
  have hc01 : c0 < 1 / d := by
    rw [hc0']; exact div_lt_div_of_pos_right (by linarith) hdpos
  set z : ℝ := min (1 / p) ((c0 + 1 / d) / 2) with hz
  have hz0 : 0 < z := lt_min (by positivity) (by have : 0 < 1 / (d : ℝ) := by positivity
                                                 linarith)
  have hzd : z < 1 / d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hzx : z ≤ 1 / p := min_le_left _ _
  have hzc : c0 ≤ z := le_min (by rw [hc0]; have : (0 : ℝ) ≤ (j : ℝ) / d := by positivity
                                  linarith) (by linarith)
  set q : ℝ := 1 / z with hq
  have hq1 : 1 / q = z := by rw [hq, one_div_one_div]
  have hqd : (d : ℝ) < q := by
    rw [hq, lt_one_div hdpos hz0]; exact hzd
  have hpq : p ≤ q := by
    have : 1 / q ≤ 1 / p := by rw [hq1]; exact hzx
    exact (one_div_le_one_div (by linarith) hp0).1 this
  have hR : sa1_Reach d p j q := sa1_reach_all hd2 (by linarith) j q hpq (by rw [hq1]; exact hzc)
  have hRI := sa1_reachInf_of_reach (by omega : 1 ≤ d) hqd hR
  obtain ⟨C, hC0, hC⟩ := sa1_glue_inf (d := d) (a0 := p) hp0 hRI (HRS.Whole.mStar d)
  refine ⟨C, fun f hf hint => ?_⟩
  have hm : c.sobolevIndex = HRS.Whole.mStar d + (j + 1) := rfl
  rw [hm] at hint ⊢
  exact hC f hf hint

/-- **S.A.1, claim 2** (`HRS.Whole.DecayingDensity.commutatorNorm_le`): the tie of `commutatorNorm_le_proof` (HRS/MS/S1c2Tie.lean,
conditional on claim 1) with `sobolev_embeds_cb_proof`. -/
theorem commutatorNorm_le_proof' : type_of% @HRS.Whole.DecayingDensity.commutatorNorm_le :=
  fun {_ _} hs0 hsd c M =>
    HRS.Whole.DecayingDensity.commutatorNorm_le_proof hs0 hsd c M (sobolev_embeds_cb_proof hs0 hsd c)

end HRS.SA1
