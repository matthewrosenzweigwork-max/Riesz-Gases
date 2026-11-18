import HRS.MS.ThmCoreAux3
import HRS.MS.ThmMinAux2

/-!
# THM-4 (first half): a minimiser of `G` on `C_M` is a fixed point of the Euler map

Abstract setting `ThmSetting K r B` of `HRS.MS.ThmDefs`.  Main statement:

* `fixedpoint_of_min` : if `0 < β`, `1 ≤ M`, `exp (β B) ≤ M`, and `μ ∈ Cset r M` minimises `Gfun K r β` over
  `Cset r M`, then `μ =ᵐ Tmap K r β μ`.

Route: the mixture `l_t = (1 - t) μ + t Tμ` lies in `Cset r M` (`Tμ ∈ Cset r M` by `Tmap_mem_Cset`); the identity
`fe_identity` together with `relEnt_mix` gives `0 ≤ G l_t - G μ ≤ -t β⁻¹ H(μ | Tμ) + ½ t² E_K(Tμ - μ)`, hence
`H(μ | Tμ) ≤ ½ β t E_K(Tμ - μ)` for all `t ∈ (0,1]`, so `H(μ | Tμ) = 0` and `μ =ᵐ Tμ`.

No statement is altered relative to the packet sketch except that the standing hypothesis `1 ≤ M` required by
`fe_identity` (binding review notes) is explicit; no junk-value trap: every integral used is accompanied by its
integrability proof inside `fe_identity` / `relEnt_mix`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- The mixture `(1 - t) μ + t ν`. -/
def t4_mix (μ ν : Euc d → ℝ) (t : ℝ) : Euc d → ℝ := fun x => (1 - t) * μ x + t * ν x

section Fix

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ}

lemma t4_mix_mem (hS : ThmSetting K r B) {M : ℝ} {μ ν : Euc d → ℝ} (hμ : μ ∈ Cset r M)
    (hν : ν ∈ Cset r M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t4_mix μ ν t ∈ Cset r M := by
  have hμi := t3_Cset_integrable hS hμ
  have hνi := t3_Cset_integrable hS hν
  refine ⟨⟨fun x => ?_, ?_, ?_⟩, fun x => ?_⟩
  · have := hμ.1.nonneg x
    have := hν.1.nonneg x
    unfold t4_mix
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (measurable_const.mul hμ.1.measurable).add (measurable_const.mul hν.1.measurable)
  · unfold t4_mix
    rw [integral_add (hμi.const_mul _) (hνi.const_mul _), integral_const_mul, integral_const_mul,
      hμ.1.integral_one, hν.1.integral_one]
    ring
  · unfold t4_mix
    have h1 := hμ.2 x
    have h2 := hν.2 x
    have : 0 ≤ 1 - t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 this, mul_le_mul_of_nonneg_left h2 ht0]

lemma t4_pairE_smul (K : Euc d → Euc d → ℝ) (f : Euc d → ℝ) (t : ℝ) :
    pairE K (fun x => t * f x) (fun x => t * f x) = t ^ 2 * pairE K f f := by
  unfold pairE
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  beta_reduce
  ring

/-- Key inequality along the mixing direction. -/
lemma t4_entropy_le (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    (hexp : Real.exp (β * B) ≤ M) {μ : Euc d → ℝ} (hμ : μ ∈ Cset r M)
    (hmin : ∀ l ∈ Cset r M, Gfun K r β μ ≤ Gfun K r β l) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    relEnt μ (Tmap K r β μ) ≤
      β * t * pairE K (Tmap K r β μ - μ) (Tmap K r β μ - μ) / 2 := by
  have hνC : Tmap K r β μ ∈ Cset r M := Tmap_mem_Cset hS hβ.le hexp hμ.1
  have hνpos := Tmap_pos hS hβ.le hμ.1
  obtain ⟨_, hμT, _, _⟩ := fe_identity hS hβ hM hμ hμ.1 (t3_ent_integrable hS hM hμ)
    (t3_pairE_integrable hS hμ hμ)
  have hlC := t4_mix_mem hS hμ hνC ht0.le ht1
  obtain ⟨_, _, _, hid⟩ := fe_identity hS hβ hM hμ hlC.1 (t3_ent_integrable hS hM hlC)
    (t3_pairE_integrable hS hlC hlC)
  have hmixle := (relEnt_mix hμ.1 hνC.1 hνpos hμT ht0.le ht1).2
  have hdiff : (t4_mix μ (Tmap K r β μ) t - μ) =
      fun x => t * (Tmap K r β μ - μ) x := by
    funext x
    simp only [t4_mix, Pi.sub_apply]
    ring
  have hE : pairE K (t4_mix μ (Tmap K r β μ) t - μ) (t4_mix μ (Tmap K r β μ) t - μ) =
      t ^ 2 * pairE K (Tmap K r β μ - μ) (Tmap K r β μ - μ) := by
    rw [hdiff]
    exact t4_pairE_smul K _ t
  rw [hE] at hid
  have hG := hmin _ hlC
  set H := relEnt μ (Tmap K r β μ) with hH
  set c := pairE K (Tmap K r β μ - μ) (Tmap K r β μ - μ) with hc
  set A := relEnt (t4_mix μ (Tmap K r β μ) t) (Tmap K r β μ) with hA
  have hA' : A ≤ (1 - t) * H := hmixle
  have h1 : 0 ≤ β⁻¹ * (A - H) + 1 / 2 * (t ^ 2 * c) := by linarith
  have h2 : β⁻¹ * (A - H) ≤ β⁻¹ * (-(t * H)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (inv_nonneg.2 hβ.le)
  have h3 : β⁻¹ * (t * H) ≤ t ^ 2 * c / 2 := by
    have : β⁻¹ * (-(t * H)) = -(β⁻¹ * (t * H)) := by ring
    linarith
  have h4 : t * H ≤ β * (t ^ 2 * c / 2) := by
    rw [inv_mul_le_iff₀ hβ] at h3
    exact h3
  have h5 : t * H ≤ t * (β * t * c / 2) := by nlinarith
  exact le_of_mul_le_mul_left h5 ht0

/-- THM-4 (first half): a minimiser of `G` on `C_M` is a fixed point of the Euler map (a.e.). -/
theorem fixedpoint_of_min (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    (hexp : Real.exp (β * B) ≤ M) {μ : Euc d → ℝ} (hμ : μ ∈ Cset r M)
    (hmin : ∀ l ∈ Cset r M, Gfun K r β μ ≤ Gfun K r β l) :
    μ =ᵐ[volume] Tmap K r β μ := by
  have hνC : Tmap K r β μ ∈ Cset r M := Tmap_mem_Cset hS hβ.le hexp hμ.1
  have hνpos := Tmap_pos hS hβ.le hμ.1
  obtain ⟨_, hμT, _, _⟩ := fe_identity hS hβ hM hμ hμ.1 (t3_ent_integrable hS hM hμ)
    (t3_pairE_integrable hS hμ hμ)
  have hH0 : 0 ≤ relEnt μ (Tmap K r β μ) := relEnt_nonneg hμ.1 hνC.1 hνpos hμT
  set H := relEnt μ (Tmap K r β μ) with hH
  set c := pairE K (Tmap K r β μ - μ) (Tmap K r β μ - μ) with hc
  have hkey : ∀ t : ℝ, 0 < t → t ≤ 1 → H ≤ β * t * c / 2 := fun t ht0 ht1 =>
    t4_entropy_le hS hβ hM hexp hμ hmin ht0 ht1
  have hHle : H ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set q := β * |c| with hq
    have hq0 : 0 ≤ q := mul_nonneg hβ.le (abs_nonneg c)
    have hden : 0 < H + q := by linarith
    set t := H / (H + q) with ht
    have ht0 : 0 < t := div_pos hpos hden
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hden]; linarith
    have htH : t * (H + q) = H := by rw [ht]; field_simp
    have h := hkey t ht0 ht1
    have h' : β * t * c ≤ q * t := by
      have : c ≤ |c| := le_abs_self c
      rw [hq]
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hβ.le ht0.le)]
    have h6 : 2 * H ≤ q * t := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h6 hden.le]
  have hH00 : H = 0 := le_antisymm hHle hH0
  exact (relEnt_eq_zero_iff hμ.1 hνC.1 hνpos hμT).1 hH00

end Fix

end HRS.MS.Thm

end
