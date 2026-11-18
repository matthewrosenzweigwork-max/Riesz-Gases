import HRS.Energy.KIDAux5

/-!
# KID helper file 6: boundedness and measurability of the modulated energy
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Energy

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.fK_cont (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {r : ℝ} (hr : r ∈ Icc 0 T) : Continuous (fK h ρ r) :=
  Torus.continuous_of_continuous_lift (c.contDiff_fK hsm hev hr).continuous

theorem MFctx.fK_bound (c : MFctx D T Λ ρ) {h : Torus d → ℝ} {Bh : ℝ} (hhc : Continuous h)
    (hBh : ∀ x, |h x| ≤ Bh) {r : ℝ} (hr : r ∈ Icc 0 T) (x : Torus d) : |fK h ρ r x| ≤ Bh := by
  unfold fK
  rw [pair_wDR (c.dens hr)]
  have : (fun y => psi h x y * ρ r y) = fun y => ρ r y * psi h x y := funext fun y => mul_comm _ _
  rw [this]
  exact c.abs_int_rho_le hr (hhc.comp (continuous_id.sub continuous_const)) (fun y => hBh _)

theorem MFctx.Dg_bound (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) {Bh : ℝ} (hhc : Continuous h) (hBh : ∀ x, |h x| ≤ Bh) {r : ℝ}
    (hr : r ∈ Icc 0 T) : |Dg h ρ r| ≤ Bh := by
  unfold Dg
  rw [pair_wDR (c.dens hr)]
  have : (fun y => fK h ρ r y * ρ r y) = fun y => ρ r y * fK h ρ r y := funext fun y => mul_comm _ _
  rw [this]
  exact c.abs_int_rho_le hr (c.fK_cont hsm hev hr) (fun y => c.fK_bound hhc hBh hr y)

theorem measurable_Fpp {h : Torus d → ℝ} (hhc : Continuous h) :
    Measurable (Fpp h : Config d N → ℝ) := by
  have hs : Measurable fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i - X j) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hhc.measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  unfold Fpp
  exact hs.const_mul _

theorem MFctx.energy_bound (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (hN : 0 < N) :
    ∃ C : ℝ, ∀ r ∈ Icc 0 T, ∀ X : Config d N,
      |modulatedEnergyKernel h X (withDensityReal (ρ r))| ≤ C := by
  have hhc : Continuous h := isCk_continuous (isCk1_of_smooth hsm |>.of_le (by norm_num) : Torus.IsCk 0 h)
  obtain ⟨Bh, hBh0, hBh⟩ := exists_norm_bound h hhc
  have hBh' : ∀ x, |h x| ≤ Bh := fun x => by simpa [Real.norm_eq_abs] using hBh x
  refine ⟨Bh + Bh + Bh, fun r hr X => ?_⟩
  rw [energy_eq hev hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : |Fpp h X| ≤ Bh := by
    unfold Fpp
    rw [abs_mul, abs_of_pos (by positivity)]
    have hs := abs_sum_le_card (Finset.univ : Finset (Fin N))
      (fun i => ∑ j ∈ Finset.univ.erase i, h (X i - X j)) (B := (N : ℝ) * Bh) (fun i => by
        refine (abs_sum_le_card _ _ (fun j => hBh' _)).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hBh0
        have : (Finset.univ.erase i).card ≤ N := by
          simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
        exact_mod_cast this)
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    calc 1 / (2 * (N : ℝ) ^ 2) * |∑ i, ∑ j ∈ Finset.univ.erase i, h (X i - X j)|
        ≤ 1 / (2 * (N : ℝ) ^ 2) * ((N : ℝ) * ((N : ℝ) * Bh)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Bh / 2 := by field_simp
      _ ≤ Bh := by linarith
  have h2 : |pair (empirical X) (fK h ρ r)| ≤ Bh := by
    rw [pair_empirical hN]
    have hs := abs_sum_le_card (Finset.univ : Finset (Fin N)) (fun i => fK h ρ r (X i)) (B := Bh)
      (fun i => c.fK_bound hhc hBh' hr _)
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    rw [abs_mul, abs_of_pos (by positivity)]
    calc ((N : ℝ))⁻¹ * |∑ i, fK h ρ r (X i)| ≤ ((N : ℝ))⁻¹ * ((N : ℝ) * Bh) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Bh := by field_simp
  have h3 := c.Dg_bound hsm hev hhc hBh' hr
  have := abs_add_le (Fpp h X - pair (empirical X) (fK h ρ r)) ((1 / 2) * Dg h ρ r)
  have := abs_sub (Fpp h X) (pair (empirical X) (fK h ρ r))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at *
  linarith

theorem MFctx.measurable_energy (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (hN : 0 < N) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Measurable fun X : Config d N => modulatedEnergyKernel h X (withDensityReal (ρ r)) := by
  have hhc : Continuous h := isCk_continuous (isCk1_of_smooth hsm |>.of_le (by norm_num) : Torus.IsCk 0 h)
  have e : (fun X : Config d N => modulatedEnergyKernel h X (withDensityReal (ρ r))) = fun X =>
      Fpp h X - (N : ℝ)⁻¹ * ∑ i, fK h ρ r (X i) + (1 / 2) * Dg h ρ r := by
    funext X
    rw [energy_eq hev hN, pair_empirical hN]
  rw [e]
  have hs : Measurable fun X : Config d N => ∑ i, fK h ρ r (X i) :=
    Finset.measurable_sum _ fun i _ => (c.fK_cont hsm hev hr).measurable.comp (measurable_pi_apply i)
  exact ((measurable_Fpp hhc).sub (hs.const_mul _)).add measurable_const

end Energy

end HRS.KID
