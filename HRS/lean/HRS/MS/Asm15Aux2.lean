import HRS.MS.Asm15Aux1
import HRS.MS.CzMikExtAux2
import HRS.MS.CzElemAux2
import HRS.MS.MovBridgeAux4

/-!
# ASM-15, part 2: clause 2 (ii-b) of `lp_positive_order_product`

For `1 < θ < 2`, `β = θ - 1 ∈ (0,1)`, `Z` real Schwartz let `G = 𝒥^{β} Z` (the complex Schwartz function with
`𝓕 G = (1+4π²|ξ|²)^{β/2} 𝓕 Z`, `HRS.MS.MovOsc.mova3b2_rot`); then `besselNormE d β p Z = ‖G‖_p`
(`asm15_besselNormE_eq`) and

* `Z = T_b G` with the plain Bessel symbol `b = (1+4π²|ξ|²)^{-β/2}` (Mikhlin, `asm15_isMikhlin_bessel`), hence
  `‖Z‖_p ≤ C ‖G‖_p` (`asm15_Z_bound`);
* `pvOdd d θ u_i Z = Re T_{s_i} G` with `s_i = K · ξ_i|ξ|^{β-1}(1+4π²|ξ|²)^{-β/2}` (Mikhlin, `isMikhlin_pvOdd_bessel`
  and `pvOdd_linear_fourier`), hence `‖pvOdd d θ u_i Z‖_p ≤ C ‖G‖_p` (`asm15_T_bound`).

`asm15_lp_positive_order_product` combines these with the commutator bound (ii-a)
(`HRS.CZ.ElemA.elema_positive_order_bound`) and `pvOdd (aZ) = [pvOdd,a]Z + a pvOdd Z`.  (`eLpNorm_add_le` needs no measurability here.)
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Asm15

open HRS.CZ.Sym HRS.CZ.Mik HRS.MS.MovOsc

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Mikhlin multipliers on `L^p` in `eLpNorm` form -/

theorem asm15_mik_Lp (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m → ∀ u : 𝓢(𝔼, ℂ),
      eLpNorm (mik2_T m u) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (Cm * A) * eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hCtop, hC⟩ := mikhlin_Lp_schwartz hd hp
  have hp0 : 0 < p := by linarith
  refine ⟨C.toReal ^ (1 / p), Real.rpow_nonneg ENNReal.toReal_nonneg _, fun A m hA hm u => ?_⟩
  have hpt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hp1 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hp2 : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2 (mik2_T_continuous hd hm u).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2 u.continuous.aestronglyMeasurable, hpt]
  have hpinv : 0 ≤ 1 / p := by positivity
  calc (∫⁻ x, ‖mik2_T m u x‖ₑ ^ p) ^ (1 / p)
      ≤ (C * ENNReal.ofReal A ^ p * ∫⁻ x, ‖u x‖ₑ ^ p) ^ (1 / p) := by
        gcongr
        exact hC A m hA hm u
    _ = ENNReal.ofReal (C.toReal ^ (1 / p) * A) * (∫⁻ x, ‖u x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hpinv, ENNReal.mul_rpow_of_nonneg _ _ hpinv,
          ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
          ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hpinv, ENNReal.ofReal_toReal hCtop]

theorem asm15_mikhlin_const_mul {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (K : ℂ) :
    mik1_IsMikhlin d (‖K‖ * A) (fun ξ => K * m ξ) := by
  refine ⟨fun ξ hξ => (hm.1 ξ hξ).const_smul K, fun i hi ξ hξ => ?_⟩
  have hat : ContDiffAt ℝ ∞ m ξ := hm.1 ξ hξ
  have e : (fun ξ => K * m ξ) = fun ξ => K • m ξ := rfl
  rw [e, iteratedFDeriv_const_smul_apply' (hat.of_le (by exact_mod_cast le_top)), norm_smul]
  have := hm.2 i hi ξ hξ
  calc ‖K‖ * ‖iteratedFDeriv ℝ i m ξ‖ ≤ ‖K‖ * (A * ‖ξ‖ ^ (-(i : ℝ))) := by gcongr
    _ = _ := by ring

/-! ### The Bessel potential `G` of a real Schwartz function -/

/-- the complexification of `Z` -/
abbrev asm15_Zc (Z : 𝓢(𝔼, ℝ)) : 𝓢(𝔼, ℂ) := mova3b2_cx Z

/-- `G = 𝒥^β Z`, `𝓕 G = (1+4π²|ξ|²)^{β/2} 𝓕 Z` -/
def asm15_G (β : ℝ) (Z : 𝓢(𝔼, ℝ)) : 𝓢(𝔼, ℂ) := mova3b2_rot (((β / 2 : ℝ)) : ℂ) (asm15_Zc Z)

lemma asm15_fourier_G (β : ℝ) (Z : 𝓢(𝔼, ℝ)) (ξ : 𝔼) :
    𝓕 (⇑(asm15_G β Z)) ξ =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) : ℝ) : ℂ) * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ := by
  have h := mova3b2_fourier_rot (((β / 2 : ℝ)) : ℂ) (asm15_Zc Z) ξ
  have hW : 0 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := (mova3b1_W_pos ξ).le
  have e1 : 𝓕 (⇑(asm15_G β Z)) ξ = (𝓕 (asm15_G β Z) : 𝓢(𝔼, ℂ)) ξ := rfl
  have e2 : (𝓕 (asm15_Zc Z) : 𝓢(𝔼, ℂ)) ξ = 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ := rfl
  rw [e1]
  unfold asm15_G
  rw [h, e2]
  unfold mova3b2_gm mova3b1_W
  rw [← Complex.ofReal_cpow hW]

lemma asm15_besselNormE_eq (β p : ℝ) (Z : 𝓢(𝔼, ℝ)) :
    HRS.Whole.AppendixA.besselNormE d β p Z = eLpNorm (⇑(asm15_G β Z)) (ENNReal.ofReal p) volume := by
  unfold HRS.Whole.AppendixA.besselNormE
  congr 1
  have e1 : (fun ξ : 𝔼 => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) : ℝ) : ℂ) *
      𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ) = ⇑(𝓕 (asm15_G β Z) : 𝓢(𝔼, ℂ)) :=
    funext fun ξ => (asm15_fourier_G β Z ξ).symm
  rw [e1, ← SchwartzMap.fourierInv_coe, FourierPair.fourierInv_fourier_eq]

/-! ### `Z = T_b G` with the plain Bessel symbol, and the bound `‖Z‖_p ≤ C ‖G‖_p` -/

lemma asm15_Z_eq (β : ℝ) (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ((Z x : ℝ) : ℂ) = mik2_T (symlin_R d β) (asm15_G β Z) x := by
  have h : (fun ξ : 𝔼 => symlin_R d β ξ * 𝓕 (⇑(asm15_G β Z)) ξ) =
      ⇑(𝓕 (asm15_Zc Z) : 𝓢(𝔼, ℂ)) := by
    funext ξ
    rw [asm15_fourier_G]
    have hpos : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := symlin_pos_base ξ
    have e2 : (𝓕 (asm15_Zc Z) : 𝓢(𝔼, ℂ)) ξ = 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ := rfl
    rw [e2, ← mul_assoc]
    unfold symlin_R
    rw [← Complex.ofReal_mul, ← Real.rpow_add hpos, show -β / 2 + β / 2 = 0 by ring, Real.rpow_zero]
    simp
  unfold mik2_T
  rw [h, ← SchwartzMap.fourierInv_coe, FourierPair.fourierInv_fourier_eq]
  rfl

theorem asm15_Z_bound (hd : 1 ≤ d) {β p : ℝ} (hβ : 0 < β) (hp : 1 < p) :
    ∃ CZ : ℝ, 0 ≤ CZ ∧ ∀ Z : 𝓢(𝔼, ℝ),
      eLpNorm (⇑Z) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CZ * HRS.Whole.AppendixA.besselNormE d β p Z := by
  obtain ⟨Cm, hCm, hM⟩ := asm15_mik_Lp (d := d) hd hp
  obtain ⟨A, hA, hmik⟩ := asm15_isMikhlin_bessel d hβ
  refine ⟨Cm * A, mul_nonneg hCm hA, fun Z => ?_⟩
  rw [asm15_besselNormE_eq]
  have e : eLpNorm (⇑Z) (ENNReal.ofReal p) volume =
      eLpNorm (mik2_T (symlin_R d β) (asm15_G β Z)) (ENNReal.ofReal p) volume := by
    refine eLpNorm_congr_norm_ae Z.continuous.aestronglyMeasurable
      (mik2_T_continuous hd hmik _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [← asm15_Z_eq β Z x, Complex.norm_real]
  rw [e]
  exact hM A _ hA hmik _

/-! ### `pvOdd d θ u_i Z = Re T_{s_i} G` -/

/-- the constant `K = c_θ · (-2πi) · (2π)^{θ-2}` -/
def asm15_K (d : ℕ) (θ : ℝ) : ℂ :=
  ((symlin_c d θ : ℝ) : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I)) * (((2 * Real.pi) ^ (θ - 2) : ℝ) : ℂ)

/-- the symbol `symlin_mult · (1+4π²|ξ|²)^{-(θ-1)/2}` of `pvOdd_θ ∘ 𝒥^{-(θ-1)}` -/
def asm15_sI (d : ℕ) (θ : ℝ) (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  symlin_mult d θ i ξ * (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(θ - 1) / 2) : ℝ) : ℂ)

lemma asm15_sI_eq (θ : ℝ) (i : Fin d) :
    asm15_sI d θ i = fun ξ : 𝔼 => asm15_K d θ *
      (((ξ i * ‖ξ‖ ^ ((θ - 1) - 1) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(θ - 1) / 2) : ℝ)) : ℂ) := by
  funext ξ
  by_cases hξ : ξ = 0
  · subst hξ; simp [asm15_sI, symlin_mult]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    unfold asm15_sI symlin_mult asm15_K
    rw [Real.mul_rpow (by positivity) hn.le, show θ - 1 - 1 = θ - 2 by ring]
    push_cast
    ring

theorem asm15_sI_mikhlin (d : ℕ) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i : Fin d, mik1_IsMikhlin d A (asm15_sI d θ i) := by
  obtain ⟨A0, hA0, h⟩ := isMikhlin_pvOdd_bessel d (β := θ - 1) (by linarith) (by linarith)
  refine ⟨‖asm15_K d θ‖ * A0, mul_nonneg (norm_nonneg _) hA0, fun i => ?_⟩
  rw [asm15_sI_eq]
  exact asm15_mikhlin_const_mul (h i) (asm15_K d θ)

lemma asm15_pvOdd_eq (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) (i : Fin d) (Z : 𝓢(𝔼, ℝ))
    (x : 𝔼) :
    ((HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (⇑Z) x : ℝ) : ℂ) =
      mik2_T (asm15_sI d θ i) (asm15_G (θ - 1) Z) x := by
  have h1 := (pvOdd_linear_fourier hd (θ := θ) (by linarith) hθ2 i Z).1 x
  rw [h1]
  unfold mik2_T
  have hf : (fun ξ : 𝔼 => symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ) =
      fun ξ : 𝔼 => asm15_sI d θ i ξ * 𝓕 (⇑(asm15_G (θ - 1) Z)) ξ := by
    funext ξ
    rw [asm15_fourier_G]
    unfold asm15_sI
    have hpos : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := symlin_pos_base ξ
    rw [mul_assoc, ← mul_assoc (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(θ - 1) / 2) : ℝ) : ℂ),
      ← Complex.ofReal_mul, ← Real.rpow_add hpos, show -(θ - 1) / 2 + (θ - 1) / 2 = 0 by ring,
      Real.rpow_zero]
    simp
  rw [hf]

lemma asm15_pvOdd_re (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) (i : Fin d) (Z : 𝓢(𝔼, ℝ)) :
    HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (⇑Z) =
      fun x => (mik2_T (asm15_sI d θ i) (asm15_G (θ - 1) Z) x).re := by
  funext x
  rw [← asm15_pvOdd_eq hd hθ1 hθ2 i Z x, Complex.ofReal_re]

lemma asm15_pvOdd_continuous (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) : Continuous (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (⇑Z)) := by
  obtain ⟨A, hA, hm⟩ := asm15_sI_mikhlin d hθ1 hθ2
  rw [asm15_pvOdd_re hd hθ1 hθ2 i Z]
  exact Complex.continuous_re.comp (mik2_T_continuous hd (hm i) _)

theorem asm15_T_bound (hd : 1 ≤ d) {θ p : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 1 < p) (i : Fin d) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ Z : 𝓢(𝔼, ℝ),
      eLpNorm (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (⇑Z)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CT * HRS.Whole.AppendixA.besselNormE d (θ - 1) p Z := by
  obtain ⟨Cm, hCm, hM⟩ := asm15_mik_Lp (d := d) hd hp
  obtain ⟨A, hA, hm⟩ := asm15_sI_mikhlin d hθ1 hθ2
  refine ⟨Cm * A, mul_nonneg hCm hA, fun Z => ?_⟩
  rw [asm15_besselNormE_eq]
  have e : eLpNorm (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (⇑Z)) (ENNReal.ofReal p) volume =
      eLpNorm (mik2_T (asm15_sI d θ i) (asm15_G (θ - 1) Z)) (ENNReal.ofReal p) volume := by
    refine eLpNorm_congr_norm_ae (asm15_pvOdd_continuous hd hθ1 hθ2 i Z).aestronglyMeasurable
      (mik2_T_continuous hd (hm i) _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [← asm15_pvOdd_eq hd hθ1 hθ2 i Z x, Complex.norm_real]
  rw [e]
  exact hM A _ hA (hm i) _

/-! ### Assembly -/

open HRS.CZ.Pv HRS.CZ.ElemA in
/-- **`lp_positive_order_product` for `Ω(u) = u_i`** (clause 1 = (ii-a) `elema_positive_order_bound`, clause 2 = (ii-b)) -/
theorem asm15_lp_positive_order_product (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p)
    (i : Fin d) :
    ∃ C : ℝ, ∀ a : 𝔼 → ℝ, HRS.MemCb 1 a →
      (∀ W : SchwartzMap 𝔼 ℝ,
        eLpNorm (fun x => HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (fun y => a y * W y) x -
            a x * HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) W x)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * HRS.cbNorm 1 a) * eLpNorm W (ENNReal.ofReal p) volume) ∧
      ∀ Z : SchwartzMap 𝔼 ℝ,
        eLpNorm (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) fun y => a y * Z y)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * HRS.cbNorm 1 a) * HRS.Whole.AppendixA.besselNormE d (θ - 1) p Z := by
  have hp1 : 1 < p := by linarith
  have hK := isPvKernel_coord (d := d) i
  obtain ⟨C0, hC0, hb⟩ := elema_positive_order_bound hd hθ1 hθ2 hK
  obtain ⟨CZ, hCZ, hZ⟩ := asm15_Z_bound hd (β := θ - 1) (p := p) (by linarith) hp1
  obtain ⟨CT, hCT, hT⟩ := asm15_T_bound hd hθ1 hθ2 hp1 i
  have hCnn : 0 ≤ C0 * (1 + CZ) + CT := add_nonneg (mul_nonneg hC0 (by linarith)) hCT
  refine ⟨C0 * (1 + CZ) + CT, fun a ha => ?_⟩
  obtain ⟨Ba, La, hBa, hLa, hcb, hab, hal⟩ := elema_cb1_data ha
  have hac : Continuous a := ha.1.continuous
  rw [hcb]
  have hBL : 0 ≤ Ba + La := add_nonneg hBa hLa
  have hcomm : ∀ W : SchwartzMap 𝔼 ℝ,
      eLpNorm (fun x => HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (fun y => a y * W y) x -
          a x * HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C0 * (Ba + La)) * eLpNorm W (ENNReal.ofReal p) volume :=
    fun W => hb p hp1.le a Ba La hBa hLa hac hab hal W
  refine ⟨fun W => (hcomm W).trans (mul_le_mul_left ?_ _), fun Z => ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_nonneg hC0 (mul_nonneg hCZ hBL), mul_nonneg hCT hBL]
  set T : 𝔼 → ℝ := HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (⇑Z) with hTdef
  have hsplit : (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) fun y => a y * Z y) =
      (fun x => HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (fun y => a y * Z y) x - a x * T x) +
        (fun x => a x * T x) := by
    funext x; simp
  have hp1' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1.le
  have h1 := eLpNorm_add_le (f := fun x => HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) (fun y => a y * Z y) x - a x * T x) (g := fun x => a x * T x) (μ := volume) hp1'
  have hTc : Continuous T := asm15_pvOdd_continuous hd hθ1 hθ2 i Z
  have hpt : ∀ᵐ x ∂(volume : Measure 𝔼), ‖a x * T x‖₊ ≤ Real.toNNReal Ba * ‖T x‖₊ := by
    refine ae_of_all _ fun x => ?_
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_mul, Real.coe_toNNReal _ hBa, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hab x) (abs_nonneg _)
  have hg : eLpNorm (fun x => a x * T x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal Ba * eLpNorm T (ENNReal.ofReal p) volume := by
    have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (g := T) (c := Real.toNNReal Ba)
      (hac.mul hTc).aestronglyMeasurable hpt (ENNReal.ofReal p)
    rw [ENNReal.smul_def, smul_eq_mul] at h
    exact h
  have hZb := hZ Z
  have hTb := hT Z
  rw [hsplit]
  refine h1.trans ?_
  calc _ ≤ ENNReal.ofReal (C0 * (Ba + La)) * eLpNorm (⇑Z) (ENNReal.ofReal p) volume +
        ENNReal.ofReal Ba * eLpNorm T (ENNReal.ofReal p) volume := add_le_add (hcomm Z) hg
    _ ≤ ENNReal.ofReal (C0 * (Ba + La)) * (ENNReal.ofReal CZ *
          HRS.Whole.AppendixA.besselNormE d (θ - 1) p Z) +
        ENNReal.ofReal Ba * (ENNReal.ofReal CT * HRS.Whole.AppendixA.besselNormE d (θ - 1) p Z) :=
        add_le_add (mul_le_mul' le_rfl hZb) (mul_le_mul' le_rfl hTb)
    _ = ENNReal.ofReal (C0 * (Ba + La) * CZ + Ba * CT) *
          HRS.Whole.AppendixA.besselNormE d (θ - 1) p Z := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hC0 hBL),
          ← ENNReal.ofReal_mul hBa, ← add_mul,
          ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC0 hBL) hCZ) (mul_nonneg hBa hCT)]
    _ ≤ _ := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_nonneg hC0 hBL, mul_nonneg hCT hLa]

end HRS.CZ.Asm15
