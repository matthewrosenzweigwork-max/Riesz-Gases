import HRS.Energy.Commutator.RenormStjIntE

/-!
# Route S, packet STJ: the `μ`-term inside the ball and the `J_l` term (uniform and `l`-integrated bounds)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-! ### Radial integrals on the torus -/

theorem lintegral_torus_rpow (hd : 1 ≤ d) {α ρ : ℝ} (hα : -(d : ℝ) < α) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∫⁻ z : Torus d, (if KernelGrad.tdist z 0 ≤ ρ then ENNReal.ofReal (KernelGrad.tdist z 0 ^ α) else 0) =
      (volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal (ρ ^ ((d : ℝ) + α) / ((d : ℝ) + α)) := by
  set F : ℝ → ℝ≥0∞ := fun t => if t ≤ ρ then ENNReal.ofReal (t ^ α) else 0 with hF
  have hFm : Measurable F :=
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)) measurable_const
  have hF0 : ∀ r, 1 / 3 ≤ r → F r = 0 := fun r hr => by
    simp only [hF]; rw [if_neg (by linarith)]
  have h := lintegral_torus_radial hd (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) F hFm hF0
  have e : ∀ z : Torus d, (if KernelGrad.tdist z 0 ≤ ρ then ENNReal.ofReal (KernelGrad.tdist z 0 ^ α) else 0) =
      F (KernelGrad.tdist z 0) := fun z => rfl
  simp_rw [e]
  rw [h, radial_Ioc_integral hd hα hρ]

theorem integral_torus_rpow (hd : 1 ≤ d) {α ρ : ℝ} (hα : -(d : ℝ) < α) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    Integrable (fun z : Torus d => if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ α else 0) ∧
    ∫ z : Torus d, (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ α else 0) =
      (volume : Measure (Euc d)).toSphere.real univ * (ρ ^ ((d : ℝ) + α) / ((d : ℝ) + α)) := by
  have hdα : 0 < (d : ℝ) + α := by linarith
  have hm : Measurable fun z : Torus d => if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ α else 0 :=
    Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const)
      (EnergyAux.measurable_tdist_zero.pow_const _) measurable_const
  have hnn : ∀ z : Torus d, 0 ≤ (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ α else 0) := fun z => by
    split_ifs
    · exact Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) _
    · exact le_rfl
  have hl := lintegral_torus_rpow hd hα hρ hρ4
  have e : ∀ z : Torus d, ENNReal.ofReal (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ α else 0) =
      (if KernelGrad.tdist z 0 ≤ ρ then ENNReal.ofReal (KernelGrad.tdist z 0 ^ α) else 0) := fun z => by
    split_ifs <;> simp
  have hfin : ∫⁻ z : Torus d, ENNReal.ofReal (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ α else 0) ≠ ⊤ := by
    simp_rw [e]; rw [hl]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hint := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hnn)).mp hfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hm.aestronglyMeasurable]
  simp_rw [e]
  rw [hl, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- uniform (in `l`) bounds for the integrals of the force over small balls -/
theorem Wb_unif (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 0 ≤ l → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 →
    Wb d l ρ ≤ K * ρ := by
  obtain ⟨K0, hK0, hK⟩ := sgv_unif_bound hd
  have hS := sphere_real_pos hd
  refine ⟨K0 * (2 * (volume : Measure (Euc d)).toSphere.real univ), by positivity, fun l hl ρ hρ hρ4 => ?_⟩
  obtain ⟨hi1, hv1⟩ := integral_torus_rpow hd (α := 1 - (d : ℝ)) (ρ := ρ) (by linarith) hρ hρ4
  obtain ⟨hi0, hv0⟩ := integral_torus_rpow hd (α := 0) (ρ := ρ) (by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith) hρ hρ4
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  set S := (volume : Measure (Euc d)).toSphere.real univ with hSdef
  have hbound : ∀ᵐ z : Torus d ∂volume, (if KernelGrad.tdist z 0 ≤ ρ then ‖SliceAux.sgv l z‖ else 0) ≤
      K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) else 0) +
        K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (0 : ℝ) else 0) := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
    by_cases h : KernelGrad.tdist z 0 ≤ ρ
    · simp only [if_pos h]
      have := hK l hl z hz
      rw [Real.rpow_zero]
      nlinarith
    · simp only [if_neg h]; norm_num
  have hnn : 0 ≤ᵐ[volume] fun z : Torus d => if KernelGrad.tdist z 0 ≤ ρ then ‖SliceAux.sgv l z‖ else 0 :=
    Filter.Eventually.of_forall fun z => by simp only [Pi.zero_apply]; split_ifs <;> positivity
  have hrhs : Integrable (fun z : Torus d => K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) else 0) +
        K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (0 : ℝ) else 0)) :=
    (hi1.const_mul K0).add (hi0.const_mul K0)
  unfold Wb
  refine (integral_mono_of_nonneg hnn hrhs hbound).trans ?_
  rw [integral_add (hi1.const_mul K0) (hi0.const_mul K0), integral_const_mul, integral_const_mul, hv1, hv0]
  have e1 : (d : ℝ) + (1 - (d : ℝ)) = 1 := by ring
  have e0 : (d : ℝ) + 0 = d := by ring
  rw [e1, e0, Real.rpow_one, Real.rpow_natCast, div_one]
  have hρd : ρ ^ d ≤ ρ := by
    have : ρ ^ d ≤ ρ ^ 1 := pow_le_pow_of_le_one hρ.le (by linarith) hd
    simpa using this
  have h1 : ρ ^ d / (d : ℝ) ≤ ρ := by
    rw [div_le_iff₀ hdr]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  nlinarith [mul_nonneg hS.le hρ.le, mul_nonneg hK0 (mul_nonneg hS.le hρ.le), mul_nonneg hK0 hS.le,
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hK0 hS.le)]

theorem Wt_unif (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 0 ≤ l → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 →
    Wt d l ρ ≤ K * ρ ^ 2 := by
  obtain ⟨K0, hK0, hK⟩ := sgv_unif_bound hd
  have hS := sphere_real_pos hd
  refine ⟨K0 * (volume : Measure (Euc d)).toSphere.real univ, by positivity, fun l hl ρ hρ hρ4 => ?_⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hi1, hv1⟩ := integral_torus_rpow hd (α := 2 - (d : ℝ)) (ρ := ρ) (by linarith) hρ hρ4
  obtain ⟨hi0, hv0⟩ := integral_torus_rpow hd (α := 1) (ρ := ρ) (by linarith) hρ hρ4
  set S := (volume : Measure (Euc d)).toSphere.real univ with hSdef
  have hbound : ∀ᵐ z : Torus d ∂volume, (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0) ≤
      K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (2 - (d : ℝ)) else 0) +
        K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (1 : ℝ) else 0) := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
    by_cases h : KernelGrad.tdist z 0 ≤ ρ
    · simp only [if_pos h]
      have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
      have h1 := hK l hl z hz
      have e : KernelGrad.tdist z 0 ^ (2 - (d : ℝ)) = KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) * KernelGrad.tdist z 0 := by
        rw [← Real.rpow_add_one ht.ne']; congr 1; ring
      rw [e, Real.rpow_one]
      nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
    · simp only [if_neg h]; norm_num
  have hnn : 0 ≤ᵐ[volume] fun z : Torus d => if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0 :=
    Filter.Eventually.of_forall fun z => by
      simp only [Pi.zero_apply]; split_ifs
      · exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)
      · exact le_rfl
  have hrhs : Integrable (fun z : Torus d => K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (2 - (d : ℝ)) else 0) +
        K0 * (if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 ^ (1 : ℝ) else 0)) :=
    (hi1.const_mul K0).add (hi0.const_mul K0)
  unfold Wt
  refine (integral_mono_of_nonneg hnn hrhs hbound).trans ?_
  rw [integral_add (hi1.const_mul K0) (hi0.const_mul K0), integral_const_mul, integral_const_mul, hv1, hv0]
  have e1 : (d : ℝ) + (2 - (d : ℝ)) = 2 := by ring
  have e0 : (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e0, Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hρd : ρ ^ (d + 1) ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ.le (by linarith) (by omega)
  have h1 : ρ ^ (d + 1) / (((d + 1 : ℕ) : ℝ)) ≤ ρ ^ 2 / 2 := by
    have hd1 : (2 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      push_cast; linarith
    calc ρ ^ (d + 1) / (((d + 1 : ℕ) : ℝ)) ≤ ρ ^ (d + 1) / 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hd1
      _ ≤ ρ ^ 2 / 2 := by linarith
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK0 hS.le)
  push_cast at h2 ⊢
  nlinarith [mul_nonneg hK0 (mul_nonneg hS.le hρ2)]

/-! ### `l`-integrals of the force -/

theorem grad_l_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z : Torus d, z ≠ 0 →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal ‖SliceAux.sgv l z‖ ≤
        ENNReal.ofReal (Cg * (KernelGrad.tdist z 0 ^ (-s - 1) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := SliceAux.slice_abs_bound hs0 hs hsd
  refine ⟨d * C, by positivity, fun z hz => ?_⟩
  have hpt : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal ‖SliceAux.sgv l z‖ ≤
      ∑ j : Fin d, ENNReal.ofReal (l ^ (-bexp d s) * |SliceAux.sgc j l z|) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have hp : 0 ≤ l ^ (-bexp d s) := Real.rpow_nonneg hl'.le _
    rw [← ENNReal.ofReal_mul hp]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hp (abs_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (SliceAux.norm_sgv_le l z) hp
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  rw [lintegral_finset_sum']
  · have hj : ∀ j : Fin d, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s) * |SliceAux.sgc j l z|) ≤
        ENNReal.ofReal (C * (KernelGrad.tdist z 0 ^ (-s - 1) + 1)) := by
      intro j
      obtain ⟨hI, hJ⟩ := hC j z hz
      exact (ofReal_integral_eq_lintegral_ofReal hI
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl =>
          mul_nonneg (Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < l from hl)) _) (abs_nonneg _)))).symm.le.trans
        (ENNReal.ofReal_le_ofReal hJ)
    calc ∑ j : Fin d, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s) * |SliceAux.sgc j l z|)
        ≤ ∑ _j : Fin d, ENNReal.ofReal (C * (KernelGrad.tdist z 0 ^ (-s - 1) + 1)) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = ENNReal.ofReal (d * C * (KernelGrad.tdist z 0 ^ (-s - 1) + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hnn : 0 ≤ C * (KernelGrad.tdist z 0 ^ (-s - 1) + 1) := by
            have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-s - 1); positivity
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  · intro j _
    have h1 : Measurable fun l : ℝ => SliceAux.sgc j l z :=
      (SliceAux.measurable_sgc j).comp (measurable_id.prodMk measurable_const)
    exact (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul h1.abs)).aemeasurable

theorem Jl_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ KJ : ℝ, 0 ≤ KJ ∧
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Jl d l) ≤ ENNReal.ofReal KJ := by
  obtain ⟨Cg, hCg0, hCg⟩ := grad_l_lintegral hd hs0 hs hsd
  set g : Torus d → ℝ := fun z => Cg * (KernelGrad.tdist z 0 ^ (-s) + KernelGrad.tdist z 0) with hg
  have hgi : Integrable g := by
    have h1 := SliceAux.integrable_tdist_rpow (by omega : 0 < d) hs0 hsd
    have h2 : Integrable (fun z : Torus d => KernelGrad.tdist z 0) :=
      (continuous_id.comp CoercAux.continuous_tdist_zero).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact (h1.add h2).const_mul Cg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by
    simp only [hg]
    have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-s)
    have := KernelGrad.tdist_nonneg z 0
    positivity
  have hfin : ∫⁻ z, ENNReal.ofReal (g z) < ⊤ := hgi.lintegral_lt_top
  refine ⟨(∫⁻ z, ENNReal.ofReal (g z)).toReal, ENNReal.toReal_nonneg, ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  have hK : Measurable (Function.uncurry fun (l : ℝ) (z : Torus d) =>
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖)) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp
        (EnergyAux.measurable_tdist_zero.comp measurable_snd |>.mul
          ((SliceAux.measurable_sgv.comp (measurable_fst.prodMk measurable_snd)).norm)))
  have e1 : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Jl d l) =
      ∫⁻ z : Torus d, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    unfold Jl
    exact ofReal_integral_eq_lintegral_ofReal (integrable_tdist_sgv hd hl'.le)
      (Filter.Eventually.of_forall fun z => mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _))
  rw [setLIntegral_congr_fun measurableSet_Ioi e1]
  have hK' : AEMeasurable (Function.uncurry fun (l : ℝ) (z : Torus d) =>
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Torus d))) := hK.aemeasurable
  rw [lintegral_lintegral_swap hK']
  refine lintegral_mono_ae ?_
  filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
  have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
  have e2 : ∀ l : ℝ, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖) =
      ENNReal.ofReal (KernelGrad.tdist z 0) * (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal ‖SliceAux.sgv l z‖) := by
    intro l
    rw [ENNReal.ofReal_mul ht.le]; ring
  simp_rw [e2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (KernelGrad.tdist z 0) * ∫⁻ l in Ioi (0 : ℝ),
        ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal ‖SliceAux.sgv l z‖
      ≤ ENNReal.ofReal (KernelGrad.tdist z 0) * ENNReal.ofReal (Cg * (KernelGrad.tdist z 0 ^ (-s - 1) + 1)) :=
        mul_le_mul' le_rfl (hCg z hz)
    _ = ENNReal.ofReal (g z) := by
        rw [← ENNReal.ofReal_mul ht.le]
        congr 1
        simp only [hg]
        have : KernelGrad.tdist z 0 ^ (-s) = KernelGrad.tdist z 0 ^ (-s - 1) * KernelGrad.tdist z 0 := by
          rw [← Real.rpow_add_one ht.ne']; congr 1; ring
        rw [this]; ring

theorem measurable_Wt_l (d : ℕ) (ρ : ℝ) : Measurable fun l : ℝ => Wt d l ρ := by
  unfold Wt
  have h : Measurable fun q : ℝ × Torus d => if KernelGrad.tdist q.2 0 ≤ ρ then
      KernelGrad.tdist q.2 0 * ‖SliceAux.sgv q.1 q.2‖ else 0 :=
    Measurable.ite (measurableSet_le (EnergyAux.measurable_tdist_zero.comp measurable_snd) measurable_const)
      ((EnergyAux.measurable_tdist_zero.comp measurable_snd).mul SliceAux.measurable_sgv.norm) measurable_const
  exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable

theorem Wt_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Wt d l η) ≤
        ENNReal.ofReal (K1 * η ^ ((d : ℝ) - s)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := grad_l_lintegral hd hs0 hs hsd
  have hS := sphere_real_pos hd
  have hds : 0 < (d : ℝ) - s := by linarith
  set S := (volume : Measure (Euc d)).toSphere.real univ with hSdef
  refine ⟨Cg * S * (1 / ((d : ℝ) - s) + 1), by positivity, fun η hη hη8 => ?_⟩
  have hη4 : η ≤ 1 / 4 := by linarith
  have hK : Measurable (Function.uncurry fun (l : ℝ) (z : Torus d) =>
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal
        (if KernelGrad.tdist z 0 ≤ η then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0)) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul (ENNReal.measurable_ofReal.comp ?_)
    exact Measurable.ite (measurableSet_le (EnergyAux.measurable_tdist_zero.comp measurable_snd) measurable_const)
      ((EnergyAux.measurable_tdist_zero.comp measurable_snd).mul
        ((SliceAux.measurable_sgv.comp (measurable_fst.prodMk measurable_snd)).norm)) measurable_const
  have e1 : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Wt d l η) =
      ∫⁻ z : Torus d, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal
        (if KernelGrad.tdist z 0 ≤ η then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    unfold Wt
    exact ofReal_integral_eq_lintegral_ofReal (integrable_Wt hd hl'.le η)
      (Filter.Eventually.of_forall fun z => by
        simp only [Pi.zero_apply]; split_ifs
        · exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)
        · exact le_rfl)
  rw [setLIntegral_congr_fun measurableSet_Ioi e1]
  rw [lintegral_lintegral_swap hK.aemeasurable]
  -- pointwise bound
  have hpt : ∀ z : Torus d, z ≠ 0 →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal
        (if KernelGrad.tdist z 0 ≤ η then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0) ≤
      (if KernelGrad.tdist z 0 ≤ η then ENNReal.ofReal (Cg * (KernelGrad.tdist z 0 ^ (-s) + KernelGrad.tdist z 0)) else 0) := by
    intro z hz
    have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
    by_cases h : KernelGrad.tdist z 0 ≤ η
    · simp only [if_pos h]
      have e2 : ∀ l : ℝ, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖) =
          ENNReal.ofReal (KernelGrad.tdist z 0) * (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal ‖SliceAux.sgv l z‖) := by
        intro l
        rw [ENNReal.ofReal_mul ht.le]; ring
      simp_rw [e2]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (KernelGrad.tdist z 0) * ∫⁻ l in Ioi (0 : ℝ),
            ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal ‖SliceAux.sgv l z‖
          ≤ ENNReal.ofReal (KernelGrad.tdist z 0) * ENNReal.ofReal (Cg * (KernelGrad.tdist z 0 ^ (-s - 1) + 1)) :=
            mul_le_mul' le_rfl (hCg z hz)
        _ = ENNReal.ofReal (Cg * (KernelGrad.tdist z 0 ^ (-s) + KernelGrad.tdist z 0)) := by
            rw [← ENNReal.ofReal_mul ht.le]
            congr 1
            have : KernelGrad.tdist z 0 ^ (-s) = KernelGrad.tdist z 0 ^ (-s - 1) * KernelGrad.tdist z 0 := by
              rw [← Real.rpow_add_one ht.ne']; congr 1; ring
            rw [this]; ring
    · simp only [if_neg h, ENNReal.ofReal_zero, mul_zero, lintegral_zero]; exact le_rfl
  have hae : ∀ᵐ z : Torus d, z ≠ 0 := KernelAux.torus_ae_ne (by omega)
  refine (lintegral_mono_ae (hae.mono fun z hz => hpt z hz)).trans ?_
  -- radial integrals
  have hsplit : ∀ z : Torus d, (if KernelGrad.tdist z 0 ≤ η then
        ENNReal.ofReal (Cg * (KernelGrad.tdist z 0 ^ (-s) + KernelGrad.tdist z 0)) else 0) =
      ENNReal.ofReal Cg * ((if KernelGrad.tdist z 0 ≤ η then ENNReal.ofReal (KernelGrad.tdist z 0 ^ (-s)) else 0) +
        (if KernelGrad.tdist z 0 ≤ η then ENNReal.ofReal (KernelGrad.tdist z 0 ^ (1 : ℝ)) else 0)) := by
    intro z
    split_ifs
    · rw [ENNReal.ofReal_mul hCg0, ENNReal.ofReal_add (Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) _)
        (KernelGrad.tdist_nonneg z 0), Real.rpow_one]
    · simp
  simp_rw [hsplit]
  have hm1 : Measurable fun z : Torus d => (if KernelGrad.tdist z 0 ≤ η then ENNReal.ofReal (KernelGrad.tdist z 0 ^ (-s)) else 0) :=
    Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const)
      (ENNReal.measurable_ofReal.comp (EnergyAux.measurable_tdist_zero.pow_const _)) measurable_const
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1,
    lintegral_torus_rpow hd (by linarith) hη hη4, lintegral_torus_rpow hd (α := 1) (by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      linarith) hη hη4]
  have hSE : (volume : Measure (Euc d)).toSphere univ = ENNReal.ofReal S := by
    rw [hSdef, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hSE]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 0 < η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s) := by
    have : 0 < (d : ℝ) + -s := by linarith
    positivity
  have hp2 : 0 < η ^ ((d : ℝ) + 1) / ((d : ℝ) + 1) := by positivity
  rw [← ENNReal.ofReal_mul hS.le, ← ENNReal.ofReal_mul hS.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hCg0]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : η ^ ((d : ℝ) + -s) = η ^ ((d : ℝ) - s) := by congr 1
  have h2 : η ^ ((d : ℝ) + 1) / ((d : ℝ) + 1) ≤ η ^ ((d : ℝ) - s) := by
    have hle : η ^ ((d : ℝ) + 1) ≤ η ^ ((d : ℝ) - s) :=
      Real.rpow_le_rpow_of_exponent_ge hη (by linarith) (by linarith)
    calc η ^ ((d : ℝ) + 1) / ((d : ℝ) + 1) ≤ η ^ ((d : ℝ) + 1) := by
          rw [div_le_iff₀ (by positivity)]
          have := Real.rpow_nonneg hη.le ((d : ℝ) + 1)
          nlinarith
      _ ≤ _ := hle
  have h3 : η ^ ((d : ℝ) + -s) / ((d : ℝ) + -s) = η ^ ((d : ℝ) - s) / ((d : ℝ) - s) := by
    rw [h1]; congr 1
  rw [h3]
  have hpw : 0 ≤ η ^ ((d : ℝ) - s) := Real.rpow_nonneg hη.le _
  have e3 : η ^ ((d : ℝ) - s) / ((d : ℝ) - s) = (1 / ((d : ℝ) - s)) * η ^ ((d : ℝ) - s) := by ring
  rw [e3]
  have h4 := mul_le_mul_of_nonneg_left h2 hS.le
  nlinarith [mul_nonneg hCg0 hS.le, mul_nonneg (mul_nonneg hCg0 hS.le) hpw]

theorem muMaj_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Wt d l η + mass d l η * (Wt d l (2 * η) + η * Wb d l (2 * η))) ≤
        ENNReal.ofReal (KM * η ^ ((d : ℝ) - s)) := by
  obtain ⟨K1, hK10, hK1⟩ := Wt_lintegral hd hs0 hs hsd
  obtain ⟨Kb, hKb0, hKb⟩ := Wb_unif hd
  obtain ⟨Kt, hKt0, hKt⟩ := Wt_unif hd
  obtain ⟨Cm, hCm0, hCm⟩ := mass_integral hd hs0 hs hsd
  set K2 : ℝ := 4 * Kt + 2 * Kb with hK2
  have hK20 : 0 ≤ K2 := by positivity
  refine ⟨K1 + K2 * Cm, by positivity, fun η hη hη8 => ?_⟩
  have hη2 : η < 1 / 2 := by linarith
  obtain ⟨hmI, hmJ⟩ := hCm η hη hη2
  have hpt : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (Wt d l η + mass d l η * (Wt d l (2 * η) + η * Wb d l (2 * η))) ≤
      ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Wt d l η) +
        ENNReal.ofReal (K2 * η ^ 2) * ENNReal.ofReal (l ^ (-bexp d s) * mass d l η) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have hp : 0 ≤ l ^ (-bexp d s) := Real.rpow_nonneg hl'.le _
    have h1 := hKt l hl'.le (2 * η) (by linarith) (by linarith)
    have h2 := hKb l hl'.le (2 * η) (by linarith) (by linarith)
    have hm0 := mass_nonneg d l η
    have hB : mass d l η * (Wt d l (2 * η) + η * Wb d l (2 * η)) ≤ mass d l η * (K2 * η ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hm0
      have : η * Wb d l (2 * η) ≤ η * (Kb * (2 * η)) := mul_le_mul_of_nonneg_left h2 hη.le
      simp only [hK2]
      nlinarith
    calc ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Wt d l η + mass d l η * (Wt d l (2 * η) + η * Wb d l (2 * η)))
        ≤ ENNReal.ofReal (l ^ (-bexp d s)) * (ENNReal.ofReal (Wt d l η) + ENNReal.ofReal (mass d l η * (K2 * η ^ 2))) := by
          refine mul_le_mul' le_rfl ?_
          refine (ENNReal.ofReal_le_ofReal (add_le_add le_rfl hB)).trans ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Wt d l η) +
          ENNReal.ofReal (K2 * η ^ 2) * ENNReal.ofReal (l ^ (-bexp d s) * mass d l η) := by
          rw [mul_add]
          congr 1
          rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K2 * η ^ 2)]
          congr 1; ring
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  have hmeas1 : AEMeasurable (fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (Wt d l η))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_Wt_l d η))).aemeasurable
  rw [lintegral_add_left' hmeas1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hB : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s) * mass d l η) ≤
      ENNReal.ofReal (Cm * η ^ ((d : ℝ) - 2 - s)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmI
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < l from hl)) _) (mass_nonneg d l η)))]
    exact ENNReal.ofReal_le_ofReal hmJ
  calc _ ≤ ENNReal.ofReal (K1 * η ^ ((d : ℝ) - s)) +
        ENNReal.ofReal (K2 * η ^ 2) * ENNReal.ofReal (Cm * η ^ ((d : ℝ) - 2 - s)) :=
        add_le_add (hK1 η hη hη8) (mul_le_mul' le_rfl hB)
    _ = ENNReal.ofReal ((K1 + K2 * Cm) * η ^ ((d : ℝ) - s)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have : η ^ ((d : ℝ) - s) = η ^ 2 * η ^ ((d : ℝ) - 2 - s) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hη]; congr 1; push_cast; ring
        rw [this]; ring

end HRS.Commutator.Stj
