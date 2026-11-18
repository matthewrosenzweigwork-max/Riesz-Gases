import HRS.MS.MfeConfAux99
import HRS.MS.MfeConfAux17
import HRS.MS.MfeConfAux64

/-!
# S.B.1, packet F9 (part 3): the invariant Gibbs measure `Γ_k` of the regularised particle system

`Γ_k = Z_k⁻¹ exp(-H_k/θ) dX` with `H_k = sb1Hs D k N` (`θ = D.invβ`): a probability measure with a Gaussian majorant of the density
(`sb1_Hs_lower`, `sb1_gz_pos`, `sb1_gam_prob`), finite second moment (`sb1_gam_moment`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the lower bound of the regularised Hamiltonian -/
theorem sb1_Hs_lower (D : Whole.WholeDyn d) {k : Euc d → ℝ} (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) (N : ℕ)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (Z : Whole.EucConfig d N) :
    (cV / 2) * ‖Z‖ ^ 2 - N * CV - (N : ℝ) ^ 2 / cV ≤ sb1Hs D k N Z := by
  unfold sb1Hs
  have hA : cV * ‖Z‖ ^ 2 - N * CV ≤ ∑ i, D.V (Z i) := by
    calc cV * ‖Z‖ ^ 2 - N * CV ≤ cV * ∑ i, ‖Z i‖ ^ 2 - N * CV := by
          have := mul_le_mul_of_nonneg_left (sb1_pi_norm_sq_le Z) hcV.le
          linarith
      _ = ∑ i, (cV * ‖Z i‖ ^ 2 - CV) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
      _ ≤ ∑ i, D.V (Z i) := Finset.sum_le_sum fun i _ => hV (Z i)
  have hterm : ∀ i j : Fin N, -(2 * ‖Z‖) ≤ k (Z i - Z j) := by
    intro i j
    have h1 := hlow (Z i - Z j)
    have h2 : Real.log (1 + ‖Z i - Z j‖) ≤ ‖Z i - Z j‖ := by
      have := Real.log_le_sub_one_of_pos (by linarith [norm_nonneg (Z i - Z j)] : 0 < 1 + ‖Z i - Z j‖)
      linarith
    have h3 : ‖Z i - Z j‖ ≤ 2 * ‖Z‖ := by
      calc ‖Z i - Z j‖ ≤ ‖Z i‖ + ‖Z j‖ := norm_sub_le _ _
        _ ≤ ‖Z‖ + ‖Z‖ := add_le_add (norm_le_pi_norm Z i) (norm_le_pi_norm Z j)
        _ = 2 * ‖Z‖ := by ring
    linarith
  have hB : -(2 * (N : ℝ) ^ 2 * ‖Z‖) ≤ p4k_pairSum k N Z := by
    unfold p4k_pairSum
    calc -(2 * (N : ℝ) ^ 2 * ‖Z‖) = ∑ _i : Fin N, ∑ _j : Fin N, -(2 * ‖Z‖) := by simp; ring
      _ ≤ ∑ i : Fin N, ∑ _j ∈ Finset.univ.erase i, -(2 * ‖Z‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hnn : 0 ≤ ‖Z‖ := norm_nonneg _
          calc ∑ _j : Fin N, -(2 * ‖Z‖) = -(N * (2 * ‖Z‖)) := by simp
            _ ≤ -(((Finset.univ.erase i).card : ℝ) * (2 * ‖Z‖)) := by
                have : ((Finset.univ.erase i).card : ℝ) ≤ N := by
                  exact_mod_cast (Finset.card_erase_le).trans (by simp)
                nlinarith
            _ = ∑ _j ∈ Finset.univ.erase i, -(2 * ‖Z‖) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hB' : -((N : ℝ) * ‖Z‖) ≤ (1 / (2 * (N : ℝ))) * p4k_pairSum k N Z := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    have hN : (0 : ℝ) < N := by exact_mod_cast h
    calc -((N : ℝ) * ‖Z‖) = (1 / (2 * (N : ℝ))) * (-(2 * (N : ℝ) ^ 2 * ‖Z‖)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  have hC : -((N : ℝ) * ‖Z‖) ≥ -((cV / 2) * ‖Z‖ ^ 2) - (N : ℝ) ^ 2 / cV := by
    have e : (cV / 2) * ‖Z‖ ^ 2 - N * ‖Z‖ + (N : ℝ) ^ 2 / (2 * cV) =
        (cV * ‖Z‖ - N) ^ 2 / (2 * cV) := by field_simp; ring
    have hnn : 0 ≤ (cV * ‖Z‖ - N) ^ 2 / (2 * cV) := by positivity
    have hh : (N : ℝ) ^ 2 / (2 * cV) ≤ (N : ℝ) ^ 2 / cV := by
      rw [div_le_div_iff₀ (by positivity) hcV]
      nlinarith [sq_nonneg (N : ℝ), hcV]
    linarith
  linarith

/-- the partition function of the regularised Gibbs measure -/
def sb1Gz (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) : ℝ :=
  ∫ x : Whole.EucConfig d N, Real.exp (-D.invβ⁻¹ * sb1Hs D k N x)

/-- its Lebesgue density -/
def sb1Gq (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (x : Whole.EucConfig d N) : ℝ :=
  Real.exp (-D.invβ⁻¹ * sb1Hs D k N x) / sb1Gz D k N

/-- the regularised Gibbs measure `Γ_k` -/
def sb1Gam (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) : Measure (Whole.EucConfig d N) :=
  sb1Dm (sb1Gq D k N)

variable {D : Whole.WholeDyn d} {k : Euc d → ℝ}

theorem sb1_Gw_le (hθ : 0 < D.invβ) (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (Z : Whole.EucConfig d N) :
    Real.exp (-D.invβ⁻¹ * sb1Hs D k N Z) ≤
      Real.exp (D.invβ⁻¹ * (N * CV + (N : ℝ) ^ 2 / cV)) * Real.exp (-(D.invβ⁻¹ * cV / 2 * ‖Z‖ ^ 2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h := sb1_Hs_lower D hlow N hcV hV Z
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hθ
  nlinarith [mul_le_mul_of_nonneg_left h hβ.le]

theorem sb1_Gw_meas (hHc : Continuous (sb1Hs D k N)) :
    Measurable fun x : Whole.EucConfig d N => Real.exp (-D.invβ⁻¹ * sb1Hs D k N x) :=
  (Real.continuous_exp.comp (continuous_const.mul hHc)).measurable

theorem sb1_Gw_int (hθ : 0 < D.invβ) (hHc : Continuous (sb1Hs D k N)) (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    Integrable fun x : Whole.EucConfig d N => Real.exp (-D.invβ⁻¹ * sb1Hs D k N x) := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hθ
  have hg : Integrable (fun Ξ : Whole.EucConfig d N =>
      Real.exp (D.invβ⁻¹ * (N * CV + (N : ℝ) ^ 2 / cV)) * Real.exp (-(D.invβ⁻¹ * cV / 2 * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := D.invβ⁻¹ * cV / 2) (by positivity)).const_mul _
  refine hg.mono' (sb1_Gw_meas hHc).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact sb1_Gw_le hθ hlow hcV hV x

theorem sb1_gz_pos (hθ : 0 < D.invβ) (hHc : Continuous (sb1Hs D k N)) (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) : 0 < sb1Gz D k N := by
  unfold sb1Gz
  exact integral_exp_pos (sb1_Gw_int hθ hHc hlow hcV hV)

theorem sb1_Gq_pos (hθ : 0 < D.invβ) (hHc : Continuous (sb1Hs D k N)) (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (x : Whole.EucConfig d N) :
    0 < sb1Gq D k N x :=
  div_pos (Real.exp_pos _) (sb1_gz_pos hθ hHc hlow hcV hV)

theorem sb1_Gq_lintegral (hθ : 0 < D.invβ) (hHc : Continuous (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    ∫⁻ x, ENNReal.ofReal (sb1Gq D k N x) = 1 := by
  have hi := sb1_Gw_int hθ hHc hlow hcV hV
  have hz := sb1_gz_pos hθ hHc hlow hcV hV
  have hqi : Integrable (sb1Gq D k N) := hi.div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hqi (Eventually.of_forall fun x =>
    (sb1_Gq_pos hθ hHc hlow hcV hV x).le)]
  have : ∫ x, sb1Gq D k N x = 1 := by
    unfold sb1Gq
    rw [integral_div]
    exact div_self hz.ne'
  rw [this, ENNReal.ofReal_one]

theorem sb1_gam_prob (hθ : 0 < D.invβ) (hHc : Continuous (sb1Hs D k N)) (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    IsProbabilityMeasure (sb1Gam D k N) :=
  sb1Dm_prob (sb1_Gq_lintegral hθ hHc hlow hcV hV)

/-- the Gibbs measure has a finite second moment -/
theorem sb1_gam_moment (hθ : 0 < D.invβ) (hHc : Continuous (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(sb1Gam D k N) < ⊤ := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hθ
  have hz := sb1_gz_pos hθ hHc hlow hcV hV
  set a : ℝ := D.invβ⁻¹ * cV / 2 with ha
  have ha0 : 0 < a := by positivity
  set M : ℝ := Real.exp (D.invβ⁻¹ * (N * CV + (N : ℝ) ^ 2 / cV)) / sb1Gz D k N with hM
  have hqle : ∀ x, sb1Gq D k N x ≤ M * Real.exp (-(a * ‖x‖ ^ 2)) := fun x => by
    unfold sb1Gq
    rw [hM, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (sb1_Gw_le hθ hlow hcV hV x) hz.le
  unfold sb1Gam sb1Dm
  have hqm : Measurable (sb1Gq D k N) := (sb1_Gw_meas hHc).div_const _
  rw [lintegral_withDensity_eq_lintegral_mul₀ hqm.ennreal_ofReal.aemeasurable
    (measurable_norm.pow_const 2).ennreal_ofReal.aemeasurable]
  have hint : Integrable (fun Ξ : Whole.EucConfig d N => M * (2 / a) * Real.exp (-(a / 2 * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := a / 2) (by positivity)).const_mul _
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have hM0 : 0 ≤ M := by positivity
  have hq0 := (sb1_Gq_pos hθ hHc hlow hcV hV x).le
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hq0]
  refine ENNReal.ofReal_le_ofReal ?_
  set u : ℝ := a * ‖x‖ ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : u ≤ 2 * Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2)
    linarith
  have h2 : ‖x‖ ^ 2 * Real.exp (-u) ≤ (2 / a) * Real.exp (-(a / 2 * ‖x‖ ^ 2)) := by
    have e2 : -(a / 2 * ‖x‖ ^ 2) = -(u / 2) := by rw [hu]; ring
    rw [e2]
    have e3 : ‖x‖ ^ 2 = u / a := by rw [hu]; field_simp
    rw [e3]
    have : u / a * Real.exp (-u) = (u * Real.exp (-u)) / a := by ring
    rw [this, div_le_iff₀ ha0]
    have e4 : (2 / a) * Real.exp (-(u / 2)) * a = 2 * Real.exp (-(u / 2)) := by field_simp
    rw [e4]
    calc u * Real.exp (-u) ≤ 2 * Real.exp (u / 2) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 2 * Real.exp (-(u / 2)) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc sb1Gq D k N x * ‖x‖ ^ 2 ≤ (M * Real.exp (-(a * ‖x‖ ^ 2))) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hqle x) (by positivity)
    _ = M * (‖x‖ ^ 2 * Real.exp (-u)) := by rw [hu]; ring
    _ ≤ M * ((2 / a) * Real.exp (-(a / 2 * ‖x‖ ^ 2))) := mul_le_mul_of_nonneg_left h2 hM0
    _ = M * (2 / a) * Real.exp (-(a / 2 * ‖x‖ ^ 2)) := by ring

end HRS.MS.MfeConf
