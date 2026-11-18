import HRS.MS.ThCorrUAux1
import HRS.MS.LogBnd

/-!
# TC-U1 (part 2): uniform ingredients for the logarithmic case `s = 0`

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu2_`.

For `a ∈ [am, ap]`, `β ∈ [βm, βp]` (`0 < am`, `0 < βm`) the reference density `γ̄ = t67gammaBar d a β` of the
`s = 0` existence proof (`ThmLogAux1`) satisfies the UNIFORM Gaussian bound
`γ̄ x ≤ S₀ exp (-(βm am / 4) ‖x‖²)` with `S₀ = exp (βp C_{am} / 2) / c_min`, where
`t67w a β x ≤ exp (βp C_{am} / 2) exp (-(βm am/4) ‖x‖²)` (`t67l_le` with `ε = am/2`) and
`c̄ = ∫ t67w ≥ ∫ exp (-(βp ap / 2) ‖x‖²) = c_min`.

The (K1) bound `∫ K̃(x, y) γ̄(y) dy ≤ B` of `t67_k1` is re-proved with the EXPLICIT constant
`tcuB0 d S c₁ = S I + C + S J_g` for any `γ̄ ≤ S exp (-c₁ ‖·‖²)` (`I = ∫ 1_{B(0,1)} g`, `C = (log 3 + log 2)/2`,
`J_g = ∫ ‖y‖² exp (-c₁ ‖y‖²)`).  Then `ThmSetting (t67K d) γ̄ B` is assembled from `t67_setting` (other fields do not
depend on `B`) and the proof of `clb_thermalDensity_eq_rep` is repeated with this `B`.  No existing file is edited.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.TcU

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-- `C_{am} = am/2 - 1 - log (am/2)`, the constant of `l ≤ (am/2) ‖x‖² + C_{am}`. -/
def tcuCam (am : ℝ) : ℝ := am / 2 - 1 - Real.log (am / 2)

lemma tcu2_Cam_nonneg {am : ℝ} (ham : 0 < am) : 0 ≤ tcuCam am := by
  unfold tcuCam
  have := Real.log_le_sub_one_of_pos (x := am / 2) (by positivity)
  linarith

/-- `c_min = (π / (βp ap / 2))^{d/2}`. -/
def tcuCmin (d : ℕ) (ap βp : ℝ) : ℝ := (Real.pi / (βp * ap / 2)) ^ ((d : ℝ) / 2)

/-- The uniform constant `S₀ = exp (βp C_{am} / 2) / c_min` of the Gaussian bound for `γ̄`. -/
def tcuS0 (d : ℕ) (am ap βp : ℝ) : ℝ := Real.exp (βp * tcuCam am / 2) / tcuCmin d ap βp

lemma tcuCmin_pos {ap βp : ℝ} (hap : 0 < ap) (hβp : 0 < βp) : 0 < tcuCmin d ap βp := by
  unfold tcuCmin
  positivity

lemma tcuS0_pos {am ap βp : ℝ} (hap : 0 < ap) (hβp : 0 < βp) : 0 < tcuS0 d am ap βp := by
  unfold tcuS0
  have := tcuCmin_pos (d := d) hap hβp
  positivity

/-- `t67w ≤ exp (βp C_{am} / 2) exp (-(βm am / 4) ‖x‖²)` uniformly in the parameters. -/
lemma tcu2_w_le {am βm βp a β : ℝ} (ham : 0 < am) (hβ : 0 < β) (ha1 : am ≤ a) (hβ1 : βm ≤ β)
    (hβ2 : β ≤ βp) (x : Euc d) :
    t67w a β x ≤ Real.exp (βp * tcuCam am / 2) * Real.exp (-(βm * am / 4) * ‖x‖ ^ 2) := by
  unfold t67w
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := t67l_le (d := d) (ε := am / 2) (by positivity) x
  have hC := tcu2_Cam_nonneg ham
  unfold confinement
  have h1 : β / 2 * t67l x ≤ β / 2 * (am / 2 * ‖x‖ ^ 2 + tcuCam am) :=
    mul_le_mul_of_nonneg_left (by unfold tcuCam; linarith) (by positivity)
  have h2 : β * am ≤ β * a := mul_le_mul_of_nonneg_left ha1 hβ.le
  have h3 : βm * am ≤ β * am := mul_le_mul_of_nonneg_right hβ1 ham.le
  have h4 : β * tcuCam am ≤ βp * tcuCam am := mul_le_mul_of_nonneg_right hβ2 hC
  have P1 := mul_le_mul_of_nonneg_right (h3.trans h2) (sq_nonneg ‖x‖)
  have P2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x‖)
  nlinarith [P1, P2, h1, h4]

/-- Lower bound of the total mass `c̄`. -/
lemma tcu2_cbar_ge {ap βp a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (ha2 : a ≤ ap) (hβ2 : β ≤ βp) :
    tcuCmin d ap βp ≤ t67cbar d a β := by
  have hap : 0 < ap := ha.trans_le ha2
  have hβp : 0 < βp := hβ.trans_le hβ2
  unfold tcuCmin t67cbar
  rw [← t012_integral_exp_neg_sq (d := d) (b := βp * ap / 2) (by positivity)]
  refine integral_mono (t012_integrable_exp_neg_sq (by positivity)) (t67w_integrable ha hβ) fun x => ?_
  unfold t67w confinement
  apply Real.exp_le_exp.2
  have h1 : β * a ≤ βp * ap := mul_le_mul hβ2 ha2 ha.le hβp.le
  have P := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  nlinarith [t67l_nonneg x, P]

/-- **Uniform Gaussian bound for `γ̄`.** -/
lemma tcu2_gamma_le {am ap βm βp a β : ℝ} (ham : 0 < am) (hβm : 0 < βm) (ha1 : am ≤ a)
    (ha2 : a ≤ ap) (hβ1 : βm ≤ β) (hβ2 : β ≤ βp) (x : Euc d) :
    t67gammaBar d a β x ≤ tcuS0 d am ap βp * Real.exp (-(βm * am / 4) * ‖x‖ ^ 2) := by
  have ha : 0 < a := ham.trans_le ha1
  have hβ : 0 < β := hβm.trans_le hβ1
  have hap : 0 < ap := ha.trans_le ha2
  have hβp : 0 < βp := hβ.trans_le hβ2
  have hc := tcuCmin_pos (d := d) hap hβp
  have hcb := tcu2_cbar_ge (d := d) ha hβ ha2 hβ2
  unfold t67gammaBar tcuS0
  calc t67w a β x / t67cbar d a β
      ≤ (Real.exp (βp * tcuCam am / 2) * Real.exp (-(βm * am / 4) * ‖x‖ ^ 2)) / t67cbar d a β :=
        div_le_div_of_nonneg_right (tcu2_w_le ham hβ ha1 hβ1 hβ2 x) (t67cbar_pos ha hβ).le
    _ ≤ (Real.exp (βp * tcuCam am / 2) * Real.exp (-(βm * am / 4) * ‖x‖ ^ 2)) / tcuCmin d ap βp :=
        div_le_div_of_nonneg_left (by positivity) hc hcb
    _ = _ := by ring

/-- `(log (1+‖x‖²))² ≤ 4 (1 + ‖x‖²)`. -/
lemma tcu2_l_sq_le (x : Euc d) : t67l x ^ 2 ≤ 4 * (1 + ‖x‖ ^ 2) := by
  have hu : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have h1 : Real.log (Real.sqrt (1 + ‖x‖ ^ 2)) = t67l x / 2 := by
    rw [Real.log_sqrt hu.le]; rfl
  have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.2 hu
  have h2 := Real.log_le_sub_one_of_pos hs
  rw [h1] at h2
  have h3 := t67l_nonneg x
  have h4 : Real.sqrt (1 + ‖x‖ ^ 2) ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt hu.le
  nlinarith [Real.sqrt_nonneg (1 + ‖x‖ ^ 2)]

/-! ### (K1) with an explicit constant -/

/-- `I = ∫ 1_{B(0,1)} g`. -/
def tcuI (d : ℕ) : ℝ := ∫ z : Euc d, (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) z

/-- `J_g = ∫ ‖y‖² exp (-c₁ ‖y‖²)`. -/
def tcuJg (d : ℕ) (c₁ : ℝ) : ℝ := ∫ y : Euc d, ‖y‖ ^ 2 * Real.exp (-c₁ * ‖y‖ ^ 2)

/-- The explicit (K1) constant for `K̃` and `γ̄ ≤ S exp (-c₁ ‖·‖²)`. -/
def tcuB0 (d : ℕ) (S c₁ : ℝ) : ℝ :=
  S * tcuI d + ((1 / 2) * Real.log 3 + (1 / 2) * Real.log 2) + S * tcuJg d c₁

lemma tcuI_nonneg (d : ℕ) : 0 ≤ tcuI d := integral_nonneg fun z => t67_ind_nonneg z

lemma tcuJg_nonneg (d : ℕ) (c₁ : ℝ) : 0 ≤ tcuJg d c₁ :=
  integral_nonneg fun y => by positivity

lemma tcuB0_nonneg (d : ℕ) {S c₁ : ℝ} (hS : 0 ≤ S) : 0 ≤ tcuB0 d S c₁ := by
  have h1 := tcuI_nonneg d
  have h2 := tcuJg_nonneg d c₁
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold tcuB0
  positivity

theorem tcu2_k1 (hd : 1 ≤ d) {a β S c₁ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hS0 : 0 ≤ S) (hc₁ : 0 < c₁)
    (hγ : ∀ y, t67gammaBar d a β y ≤ S * Real.exp (-c₁ * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun y => t67K d x y * t67gammaBar d a β y) ∧
      ∫ y, t67K d x y * t67gammaBar d a β y ≤ tcuB0 d S c₁ := by
  set C : ℝ := (1 / 2) * Real.log 3 + (1 / 2) * Real.log 2 with hC
  have hint := t67_ind_integrable (d := d) hd
  have hγi := t67gammaBar_integrable (d := d) ha hβ
  have hγm := t67gammaBar_measurable (d := d) a β
  have hγp := t67gammaBar_pos (d := d) ha hβ
  have hSle : ∀ y, t67gammaBar d a β y ≤ S := fun y => by
    refine (hγ y).trans ?_
    have : Real.exp (-c₁ * ‖y‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c₁ * ‖y‖ ^ 2 := by positivity
      linarith
    calc S * Real.exp (-c₁ * ‖y‖ ^ 2) ≤ S * 1 := mul_le_mul_of_nonneg_left this hS0
      _ = S := mul_one _
  have hgi : Integrable fun y : Euc d => S * (‖y‖ ^ 2 * Real.exp (-c₁ * ‖y‖ ^ 2)) :=
    (t012_integrable_sq_mul_exp (d := d) hc₁).const_mul S
  have hlγ : Integrable fun y : Euc d => t67l y * t67gammaBar d a β y := by
    refine Integrable.mono' hgi (t67l_measurable.mul hγm).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (t67l_nonneg y) (hγp y).le)]
    calc t67l y * t67gammaBar d a β y ≤ ‖y‖ ^ 2 * (S * Real.exp (-c₁ * ‖y‖ ^ 2)) :=
          mul_le_mul (t67l_le_sq y) (hγ y) (hγp y).le (by positivity)
      _ = _ := by ring
  have hJ : ∫ y, t67l y * t67gammaBar d a β y ≤ S * tcuJg d c₁ := by
    unfold tcuJg
    rw [← integral_const_mul]
    refine integral_mono hlγ hgi fun y => ?_
    calc t67l y * t67gammaBar d a β y ≤ ‖y‖ ^ 2 * (S * Real.exp (-c₁ * ‖y‖ ^ 2)) :=
          mul_le_mul (t67l_le_sq y) (hγ y) (hγp y).le (by positivity)
      _ = _ := by ring
  have h1' : Integrable fun y : Euc d =>
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y := by
    have := (hint.comp_sub_left x)
    refine this.mul_bdd (c := S) hγm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hγp y)]
    exact hSle y
  have h2 : Integrable fun y : Euc d => C * t67gammaBar d a β y := hγi.const_mul C
  have hmaj : Integrable fun y : Euc d =>
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
        C * t67gammaBar d a β y + t67l y * t67gammaBar d a β y := (h1'.add h2).add hlγ
  have hmeasK : Measurable fun y : Euc d => t67K d x y * t67gammaBar d a β y :=
    ((t67K_measurable.comp (measurable_const.prodMk measurable_id))).mul hγm
  have hle : ∀ y, ‖t67K d x y * t67gammaBar d a β y‖ ≤
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
        C * t67gammaBar d a β y + t67l y * t67gammaBar d a β y := by
    intro y
    have hp := hγp y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (t67K_nonneg x y) hp.le)]
    have := t67K_le x y
    nlinarith [mul_le_mul_of_nonneg_right this hp.le]
  have hKint : Integrable fun y : Euc d => t67K d x y * t67gammaBar d a β y :=
    Integrable.mono' hmaj hmeasK.aestronglyMeasurable (ae_of_all _ hle)
  refine ⟨hKint, ?_⟩
  calc ∫ y, t67K d x y * t67gammaBar d a β y
      ≤ ∫ y, ((Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
        C * t67gammaBar d a β y + t67l y * t67gammaBar d a β y) := by
        refine integral_mono hKint hmaj fun y => ?_
        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hle y)
    _ = (∫ y, (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y) +
        C * (∫ y, t67gammaBar d a β y) + ∫ y, t67l y * t67gammaBar d a β y := by
        have hAB : Integrable fun y : Euc d =>
            (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
              C * t67gammaBar d a β y := h1'.add h2
        rw [integral_add hAB hlγ, integral_add h1' h2, integral_const_mul]
    _ ≤ tcuB0 d S c₁ := by
        have hb : ∫ y, (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) *
            t67gammaBar d a β y ≤ ∫ y, S * (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) := by
          refine integral_mono h1' ((hint.comp_sub_left x).const_mul S) fun y => ?_
          have := t67_ind_nonneg (d := d) (x - y)
          nlinarith [hSle y]
        have hc : ∫ y, S * (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) = S * tcuI d := by
          rw [integral_const_mul]
          congr 1
          exact integral_sub_left_eq_self (fun z => (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) z)
            volume x
        have hone : ∫ y, t67gammaBar d a β y = 1 := (t67gammaBar_isProbDensity (d := d) ha hβ).integral_one
        have e : C * (∫ y, t67gammaBar d a β y) = C := by rw [hone, mul_one]
        rw [e]
        have h3 := hb.trans hc.le
        unfold tcuB0
        linarith

/-- The abstract setting for `K̃`, `γ̄` with the explicit constant. -/
theorem tcu2_setting (hd : 1 ≤ d) {a β S c₁ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hS0 : 0 ≤ S)
    (hc₁ : 0 < c₁) (hγ : ∀ y, t67gammaBar d a β y ≤ S * Real.exp (-c₁ * ‖y‖ ^ 2)) :
    ThmSetting (t67K d) (t67gammaBar d a β) (tcuB0 d S c₁) := by
  obtain ⟨B, hS⟩ := t67_setting hd ha hβ
  exact { hS with k1 := fun x => tcu2_k1 hd ha hβ hS0 hc₁ hγ x }

/-- `thermalDensity d 0 a β` is a thermal equilibrium lying in `C_M` for `M = max 1 (exp (β B))`,
`B = tcuB0 d S c₁`. -/
theorem tcu2_rep (hd : 1 ≤ d) {a β S c₁ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hS0 : 0 ≤ S)
    (hc₁ : 0 < c₁) (hγ : ∀ y, t67gammaBar d a β y ≤ S * Real.exp (-c₁ * ‖y‖ ^ 2)) :
    HRS.Whole.IsThermalEquilibrium d 0 a β (thermalDensity d 0 a β) ∧
      thermalDensity d 0 a β ∈ Cset (t67gammaBar d a β) (max 1 (Real.exp (β * tcuB0 d S c₁))) := by
  have hS := tcu2_setting hd ha hβ hS0 hc₁ hγ
  have hM : 1 ≤ max 1 (Real.exp (β * tcuB0 d S c₁)) := le_max_left _ _
  have hexp : Real.exp (β * tcuB0 d S c₁) ≤ max 1 (Real.exp (β * tcuB0 d S c₁)) := le_max_right _ _
  obtain ⟨μ, hμ, hmin⟩ := exists_min_Cset hS hM hβ
  have hfix := fixedpoint_of_min hS hβ hM hexp hμ hmin
  have hρC := thermalRep_mem_Cset hS hβ.le hexp hμ.1
  have hρfix := thermalRep_fixed hfix
  have hEq := t67_equilibrium_of_fixed hS ha hβ hM hρC hρfix
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d 0 a β ρ := ⟨_, hEq⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d 0 a β (thermalDensity d 0 a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  have hae := t67_minimizer_ae_eq hS ha hβ hM hρC hρfix hτ.1
  have hpt : ∀ x, thermalDensity d 0 a β x =
      thermalRep (t67K d) (t67gammaBar d a β) β μ x :=
    thermalDensity_eq_pointwise hτ.2 hEq.2 hae
  refine ⟨hτ, hτ.1.1, fun x => ?_⟩
  rw [hpt x]
  exact hρC.2 x

end HRS.MS.TcU

end
