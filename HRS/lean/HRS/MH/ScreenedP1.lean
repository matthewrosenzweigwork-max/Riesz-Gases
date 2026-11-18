import HRS.MH.ScreenedP1Aux3

/-!
# Packet P1 of `B:lem:screened` (S.B.4): proof of `screened_pairing_lt` (`ScreenedSpec.lean`).

Route (`ScreenedPlan.md` 3.4): `v = aψ` is `L¹` (`|a| ≤ Λ⟨x⟩^{-(d+3)}`), a.e. measurable (from the
representation, `p1_aesm_of_rep`); `u = ∂_i g * v` a.e. (`gk_rep_L1`, `gk_unique`); the kernel is split at
radius 1 and Young (`young_l1_l2`) bounds the near part in `L²` by `‖v‖₂` and the far part by `‖v‖₁`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Cauchy-Schwarz for lower Lebesgue integrals, a.e.-measurable version. -/
lemma p1_cs_aemeas {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two hf hg
  simp only [ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, a2_sq_sqrt, a2_sq_sqrt]

/-- Square roots in `ℝ≥0∞`: `x² ≤ y²` implies `x ≤ y`. -/
lemma p1_le_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  have e : ∀ z : ℝ≥0∞, (z ^ 2) ^ (1 / 2 : ℝ) = z := by
    intro z
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc x = (x ^ 2) ^ (1 / 2 : ℝ) := (e x).symm
    _ ≤ (y ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = y := e y

/-- The core `L²` estimate: `‖u‖₂² ≤ Λ² ‖ψ‖₂² Q` for the representative `u` of `∂_i g * (aψ)`. -/
lemma p1_core {s : ℝ} (hd2 : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 1) (h2 : (d : ℝ) < 2 * (s + 1))
    (i : Fin d) {Λ : ℝ} (hΛ : 0 ≤ Λ) {a : Euc d → ℝ} (hA : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ)
    {ψ u : Euc d → ℝ} (hψ : MemLp ψ 2 volume) (hu : MemLp u 2 volume)
    (hrep : IsGradKernelRep d s i (fun y => a y * ψ y) u) :
    ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal Λ ^ 2 * (eLpNorm ψ 2 volume) ^ 2 * p1_Q d s := by
  set v : Euc d → ℝ := fun y => a y * ψ y with hvdef
  have hav : ∀ y, ‖v y‖ₑ ≤ ENNReal.ofReal Λ * (p1_G d y * ‖ψ y‖ₑ) := by
    intro y
    have hjb1 : 1 ≤ jbracket y := p1_one_le_jbracket y
    have hjbpos : 0 < jbracket y ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (by linarith) _
    have habs : |a y| ≤ Λ * jbracket y ^ (-((d : ℝ) + 3)) := by
      rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hjbpos]
      linarith [hA y, mul_comm (|a y|) (jbracket y ^ ((d : ℝ) + 3))]
    have e1 : ‖v y‖ₑ = ENNReal.ofReal |a y| * ‖ψ y‖ₑ := by
      simp only [hvdef]
      rw [enorm_mul, Real.enorm_eq_ofReal_abs]
    rw [e1, p1_G, ← mul_assoc, ← ENNReal.ofReal_mul hΛ]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal habs) le_rfl
  have hvm : AEStronglyMeasurable v volume := p1_aesm_of_rep hd2 hs0 hsd i hrep
  set v' : Euc d → ℝ := hvm.mk v with hv'def
  have hv'm : Measurable v' := hvm.stronglyMeasurable_mk.measurable
  have hvv' : v =ᵐ[volume] v' := hvm.ae_eq_mk
  have hψm : AEStronglyMeasurable ψ volume := hψ.aestronglyMeasurable
  set ψ' : Euc d → ℝ := hψm.mk ψ with hψ'def
  have hψ'm : Measurable ψ' := hψm.stronglyMeasurable_mk.measurable
  have hψψ' : ψ =ᵐ[volume] ψ' := hψm.ae_eq_mk
  have hv'bd : ∀ᵐ y ∂(volume : Measure (Euc d)),
      ‖v' y‖ₑ ≤ ENNReal.ofReal Λ * (p1_G d y * ‖ψ' y‖ₑ) := by
    filter_upwards [hvv', hψψ'] with y h1 h2
    rw [← h1, ← h2]
    exact hav y
  have hCS : (∫⁻ y, p1_G d y * ‖ψ' y‖ₑ) ^ 2 ≤ (∫⁻ y, p1_G d y ^ 2) * ∫⁻ y, ‖ψ' y‖ₑ ^ 2 :=
    p1_cs_aemeas volume (p1_G d) (fun y => ‖ψ' y‖ₑ) p1_G_measurable.aemeasurable
      hψ'm.enorm.aemeasurable
  have hNψ : ∫⁻ y, ‖ψ' y‖ₑ ^ 2 = (eLpNorm ψ 2 volume) ^ 2 := by
    rw [eLpNorm_congr_ae hψψ', l1_sq_eLpNorm_ae ψ' hψ'm.aestronglyMeasurable]
  have hPfin : (eLpNorm ψ 2 volume) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hψ.eLpNorm_ne_top
  have hXfin : (∫⁻ y, p1_G d y * ‖ψ' y‖ₑ) < ⊤ := by
    have h1 : (∫⁻ y, p1_G d y * ‖ψ' y‖ₑ) ^ 2 < ⊤ :=
      lt_of_le_of_lt hCS (ENNReal.mul_lt_top p1_G_sq_lintegral_lt_top
        (by rw [hNψ]; exact lt_top_iff_ne_top.2 hPfin))
    exact lt_top_iff_ne_top.2 (fun h => by rw [h] at h1; simp at h1)
  have hL1 : ∫⁻ y, ‖v' y‖ₑ ≤ ENNReal.ofReal Λ * ∫⁻ y, p1_G d y * ‖ψ' y‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae hv'bd
  have hv1fin : ∫⁻ y, ‖v' y‖ₑ < ⊤ :=
    lt_of_le_of_lt hL1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hXfin)
  have hv'int : Integrable v' volume := ⟨hv'm.aestronglyMeasurable, hv1fin⟩
  have hrep0 := gk_rep_L1_proof hd2 hs0 hsd i v' hv'int
  have hrepu : IsGradKernelRep d s i v' u := p1_gkRep_congr hrep hvv'
  have huw0 : u =ᵐ[volume] (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v' y) :=
    (gk_unique_proof i hrep0 hrepu).symm
  have hv'enm : Measurable (fun y => ‖v' y‖ₑ) := hv'm.enorm
  have hD0m : Measurable (p1_D0 d s) := p1_D0_measurable s
  have hDim : Measurable (p1_Dinf d s) := p1_Dinf_measurable s
  have hAm : Measurable (p1_A d s v') :=
    Measurable.lintegral_prod_right'
      (f := fun p : Euc d × Euc d => p1_D0 d s (p.1 - p.2) * ‖v' p.2‖ₑ)
      ((hD0m.comp (measurable_fst.sub measurable_snd)).mul (hv'enm.comp measurable_snd))
  have hpt : ∀ x, ‖∫ y, rieszKernelGrad d s (x - y) i * v' y‖ₑ ≤ p1_A d s v' x + p1_B d s v' x := by
    intro x
    have hae : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by
      have hne : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      have hnt : Nontrivial (Euc d) := inferInstance
      rw [ae_iff]
      have hset : {y : Euc d | ¬ y ≠ x} = {x} := by
        ext y
        simp
      rw [hset]
      exact measure_singleton x
    have hmeas : Measurable (fun y => p1_D0 d s (x - y) * ‖v' y‖ₑ) :=
      (hD0m.comp (measurable_const.sub measurable_id)).mul hv'enm
    calc ‖∫ y, rieszKernelGrad d s (x - y) i * v' y‖ₑ
        ≤ ∫⁻ y, ‖rieszKernelGrad d s (x - y) i * v' y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, (p1_D0 d s (x - y) + p1_Dinf d s (x - y)) * ‖v' y‖ₑ := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          rw [enorm_mul]
          exact mul_le_mul' (p1_kernel_le hs0 i (sub_ne_zero.2 (Ne.symm hy))) le_rfl
      _ = p1_A d s v' x + p1_B d s v' x := by
          unfold p1_A p1_B
          simp_rw [add_mul]
          exact lintegral_add_left hmeas _
  have hYA : ∫⁻ x, (p1_A d s v' x) ^ 2 ≤ (∫⁻ z, p1_D0 d s z) ^ 2 * ∫⁻ y, ‖v' y‖ₑ ^ 2 :=
    young_l1_l2_proof (p1_D0 d s) (fun y => ‖v' y‖ₑ) hD0m hv'enm
      (p1_D0_lintegral_lt_top (by omega) hs0 hsd).ne
  have hBeq : ∀ x, p1_B d s v' x = ∫⁻ y, ‖v' (x - y)‖ₑ * p1_Dinf d s y := by
    intro x
    have := lintegral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun y => p1_Dinf d s y * ‖v' (x - y)‖ₑ) x
    simp only [sub_sub_cancel] at this
    unfold p1_B
    rw [this]
    exact lintegral_congr fun y => mul_comm _ _
  have hYB : ∫⁻ x, (p1_B d s v' x) ^ 2 ≤ (∫⁻ y, ‖v' y‖ₑ) ^ 2 * ∫⁻ y, p1_Dinf d s y ^ 2 := by
    calc ∫⁻ x, (p1_B d s v' x) ^ 2
        = ∫⁻ x, (∫⁻ y, ‖v' (x - y)‖ₑ * p1_Dinf d s y) ^ 2 := lintegral_congr fun x => by rw [hBeq x]
      _ ≤ (∫⁻ y, ‖v' y‖ₑ) ^ 2 * ∫⁻ y, p1_Dinf d s y ^ 2 :=
          young_l1_l2_proof (fun y => ‖v' y‖ₑ) (p1_Dinf d s) hv'enm (p1_Dinf_measurable s) hv1fin.ne
  have hsq_w0 : ∫⁻ x, ‖∫ y, rieszKernelGrad d s (x - y) i * v' y‖ₑ ^ 2
      ≤ 2 * (∫⁻ x, (p1_A d s v' x) ^ 2) + 2 * (∫⁻ x, (p1_B d s v' x) ^ 2) := by
    calc ∫⁻ x, ‖∫ y, rieszKernelGrad d s (x - y) i * v' y‖ₑ ^ 2
        ≤ ∫⁻ x, (2 * (p1_A d s v' x) ^ 2 + 2 * (p1_B d s v' x) ^ 2) := by
          apply lintegral_mono
          intro x
          calc ‖∫ y, rieszKernelGrad d s (x - y) i * v' y‖ₑ ^ 2
              ≤ (p1_A d s v' x + p1_B d s v' x) ^ 2 := by
                gcongr
                exact hpt x
            _ ≤ 2 * (p1_A d s v' x) ^ 2 + 2 * (p1_B d s v' x) ^ 2 := p1_add_sq_le _ _
      _ = 2 * (∫⁻ x, (p1_A d s v' x) ^ 2) + 2 * (∫⁻ x, (p1_B d s v' x) ^ 2) := by
          rw [lintegral_add_left ((hAm.pow_const 2).const_mul 2),
            lintegral_const_mul' (2 : ℝ≥0∞) (fun x => (p1_A d s v' x) ^ 2) (by norm_num),
            lintegral_const_mul' (2 : ℝ≥0∞) (fun x => (p1_B d s v' x) ^ 2) (by norm_num)]
          try rfl
  have hN : ∫⁻ y, ‖v' y‖ₑ ^ 2 ≤ ENNReal.ofReal Λ ^ 2 * ∫⁻ y, ‖ψ' y‖ₑ ^ 2 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hv'bd] with y hy
    have hle : ‖v' y‖ₑ ≤ ENNReal.ofReal Λ * ‖ψ' y‖ₑ :=
      le_trans hy (mul_le_mul' le_rfl (mul_le_of_le_one_left (by positivity) (p1_G_le_one y)))
    calc ‖v' y‖ₑ ^ 2 ≤ (ENNReal.ofReal Λ * ‖ψ' y‖ₑ) ^ 2 := by gcongr
      _ = ENNReal.ofReal Λ ^ 2 * ‖ψ' y‖ₑ ^ 2 := mul_pow _ _ _
  have hX2 : (∫⁻ y, ‖v' y‖ₑ) ^ 2 ≤ ENNReal.ofReal Λ ^ 2 * ((∫⁻ y, p1_G d y ^ 2) * ∫⁻ y, ‖ψ' y‖ₑ ^ 2) := by
    calc (∫⁻ y, ‖v' y‖ₑ) ^ 2 ≤ (ENNReal.ofReal Λ * ∫⁻ y, p1_G d y * ‖ψ' y‖ₑ) ^ 2 := by gcongr
      _ = ENNReal.ofReal Λ ^ 2 * (∫⁻ y, p1_G d y * ‖ψ' y‖ₑ) ^ 2 := mul_pow _ _ _
      _ ≤ ENNReal.ofReal Λ ^ 2 * ((∫⁻ y, p1_G d y ^ 2) * ∫⁻ y, ‖ψ' y‖ₑ ^ 2) := by gcongr
  rw [hNψ] at hN hX2
  have hA' : ∫⁻ x, (p1_A d s v' x) ^ 2 ≤
      (∫⁻ z, p1_D0 d s z) ^ 2 * (ENNReal.ofReal Λ ^ 2 * (eLpNorm ψ 2 volume) ^ 2) :=
    hYA.trans (by gcongr)
  have hB' : ∫⁻ x, (p1_B d s v' x) ^ 2 ≤
      (ENNReal.ofReal Λ ^ 2 * ((∫⁻ y, p1_G d y ^ 2) * (eLpNorm ψ 2 volume) ^ 2)) *
        ∫⁻ y, p1_Dinf d s y ^ 2 :=
    hYB.trans (by gcongr)
  have hfin1 : 2 * (∫⁻ x, (p1_A d s v' x) ^ 2) ≤
      2 * ((∫⁻ z, p1_D0 d s z) ^ 2 * (ENNReal.ofReal Λ ^ 2 * (eLpNorm ψ 2 volume) ^ 2)) :=
    mul_le_mul_of_nonneg_left hA' (by positivity)
  have hfin2 : 2 * (∫⁻ x, (p1_B d s v' x) ^ 2) ≤
      2 * ((ENNReal.ofReal Λ ^ 2 * ((∫⁻ y, p1_G d y ^ 2) * (eLpNorm ψ 2 volume) ^ 2)) *
        ∫⁻ y, p1_Dinf d s y ^ 2) :=
    mul_le_mul_of_nonneg_left hB' (by positivity)
  calc ∫⁻ x, ‖u x‖ₑ ^ 2
      = ∫⁻ x, ‖∫ y, rieszKernelGrad d s (x - y) i * v' y‖ₑ ^ 2 :=
        lintegral_congr_ae (huw0.mono fun x hx => by simp only [hx])
    _ ≤ 2 * (∫⁻ x, (p1_A d s v' x) ^ 2) + 2 * (∫⁻ x, (p1_B d s v' x) ^ 2) := hsq_w0
    _ ≤ 2 * ((∫⁻ z, p1_D0 d s z) ^ 2 * (ENNReal.ofReal Λ ^ 2 * (eLpNorm ψ 2 volume) ^ 2)) +
          2 * ((ENNReal.ofReal Λ ^ 2 * ((∫⁻ y, p1_G d y ^ 2) * (eLpNorm ψ 2 volume) ^ 2)) *
            ∫⁻ y, p1_Dinf d s y ^ 2) :=
        add_le_add hfin1 hfin2
    _ = ENNReal.ofReal Λ ^ 2 * (eLpNorm ψ 2 volume) ^ 2 * p1_Q d s := by
        unfold p1_Q
        ring

/-- Packet P1: `screened_pairing_lt` (`s < d-1`, `d < 2(s+1)`). -/
theorem screened_pairing_lt_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 1)
    (h2 : (d : ℝ) < 2 * (s + 1)) :
    ∃ C : ℝ, ∀ (Λ : ℝ) (a : Euc d → ℝ), (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      ∀ (i : Fin d) (ψ w u : Euc d → ℝ), MemLp ψ 2 volume → MemLp w 2 volume →
      sobolevNormE (kgOrder d s) ψ < ⊤ → MemLp u 2 volume →
      IsGradKernelRep d s i (fun y => a y * ψ y) u →
        ENNReal.ofReal |∫ x, u x * w x| ≤
          ENNReal.ofReal (C * Λ) * sobolevNormE (kgOrder d s) ψ * eLpNorm w 2 volume := by
  have hd2 : 2 ≤ d := by
    have h1 : (1 : ℝ) < d := by linarith
    have h3 : 1 < d := by exact_mod_cast h1
    omega
  have hk0 : kgOrder d s = 0 := by
    unfold kgOrder
    exact max_eq_right (by linarith)
  have hD0 := p1_D0_lintegral_lt_top hd hs0 hsd
  have hDi := p1_Dinf_sq_lintegral_lt_top hs0 h2
  have hG := p1_G_sq_lintegral_lt_top (d := d)
  have hQfin : p1_Q d s < ⊤ := by
    unfold p1_Q
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hD0),
      ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top hG hDi)⟩
  have hCsq : ENNReal.ofReal (Real.sqrt (p1_Q d s).toReal) ^ 2 = p1_Q d s := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hQfin.ne]
  refine ⟨Real.sqrt (p1_Q d s).toReal, ?_⟩
  set C : ℝ := Real.sqrt (p1_Q d s).toReal with hCdef
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  intro Λ a hA i ψ w u hψ hw hψfin hu hrep
  have hΛ : 0 ≤ Λ := by
    have h00 : 0 ≤ jbracket (0 : Euc d) ^ ((d : ℝ) + 3) * |a 0| :=
      mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (p1_one_le_jbracket 0)) _) (abs_nonneg _)
    linarith [hA 0]
  have hcore := p1_core hd2 hs0 hsd h2 i hΛ hA hψ hu hrep
  have hCS2 : (∫⁻ x, ‖u x‖ₑ * ‖w x‖ₑ) ^ 2 ≤ (∫⁻ x, ‖u x‖ₑ ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 :=
    p1_cs_aemeas volume (fun x => ‖u x‖ₑ) (fun x => ‖w x‖ₑ)
      hu.aestronglyMeasurable.enorm hw.aestronglyMeasurable.enorm
  have hwsq : ∫⁻ x, ‖w x‖ₑ ^ 2 = (eLpNorm w 2 volume) ^ 2 :=
    (l1_sq_eLpNorm_ae w hw.aestronglyMeasurable).symm
  have hkey : (∫⁻ x, ‖u x‖ₑ * ‖w x‖ₑ) ^ 2 ≤
      (ENNReal.ofReal C * ENNReal.ofReal Λ * eLpNorm ψ 2 volume * eLpNorm w 2 volume) ^ 2 := by
    calc (∫⁻ x, ‖u x‖ₑ * ‖w x‖ₑ) ^ 2 ≤ (∫⁻ x, ‖u x‖ₑ ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 := hCS2
      _ ≤ (ENNReal.ofReal Λ ^ 2 * (eLpNorm ψ 2 volume) ^ 2 * p1_Q d s) * (eLpNorm w 2 volume) ^ 2 := by
          rw [hwsq]
          gcongr
      _ = (ENNReal.ofReal C * ENNReal.ofReal Λ * eLpNorm ψ 2 volume * eLpNorm w 2 volume) ^ 2 := by
          rw [← hCsq]
          ring
  have hint : ‖∫ x, u x * w x‖ₑ ≤ ∫⁻ x, ‖u x‖ₑ * ‖w x‖ₑ :=
    (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun x => enorm_mul _ _))
  have hY : ‖∫ x, u x * w x‖ₑ ≤
      ENNReal.ofReal C * ENNReal.ofReal Λ * eLpNorm ψ 2 volume * eLpNorm w 2 volume :=
    p1_le_of_sq_le (le_trans (pow_le_pow_left₀ (by positivity) hint 2) hkey)
  rw [hk0, l1_sobolev_zero_eq hψ, ENNReal.ofReal_mul hC0, ← Real.norm_eq_abs, ofReal_norm_eq_enorm]
  exact hY

end HRS.MH.Screened
