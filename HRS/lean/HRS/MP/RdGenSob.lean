import HRS.PDE.ToolboxRd.Fourier
import HRS.Whole.SobolevDual

/-!
# Packet MPRGEN, stage 1: the Sobolev embedding `H^q(ℝ^d) ↪ C_b^j` (`j + d/2 < q`)

Fourier inversion for `φ ∈ L²` continuous with `φ̂ ∈ L¹` (`rg_inversion`, by duality against Schwartz test
functions: `∫ s φ̂ = ∫ ŝ φ` for the `L²` transform, `∫ ŝ ψ̂' = ∫ s ψ` for the pointwise transform, then
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), the Cauchy-Schwarz bound
`∫ |ξ|^l |φ̂| ≤ C_l ‖φ‖_{H^q}` (`rg_moment_bound`), and differentiation of the Fourier integral
(`rg_norm_iteratedFDeriv_fourier_le`).  Result: `rg_sobolev_embedding`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform SchwartzMap

namespace HRS.MP.RdGen
open HRS HRS.Whole HRS.PDE HRS.PDE.ToolboxRd

variable {d : ℕ}

lemma rg_fourierL2_dual {φ : Euc d → ℝ} (hφ : MemLp φ 2 volume) (s : 𝓢(Euc d, ℂ)) :
    ∫ x, s x * fourierL2 φ x = ∫ x, 𝓕 s x * ((φ x : ℝ) : ℂ) := by
  set Fl := FourierAux.ofRealLp hφ with hFldef
  have hFl := FourierAux.fourierL2_eq hφ
  have h1 : ∫ x, s x • fourierL2 φ x =
      ∫ x, s x • ((FourierAux.FT d Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show s x • fourierL2 φ x = _
    rw [congrFun hFl x]
  have h2 : (𝓕 (MeasureTheory.Lp.toTemperedDistribution Fl)) s =
      ∫ x, s x • ((𝓕 Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := by
    rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
      MeasureTheory.Lp.toTemperedDistribution_apply]
  have h3 : (𝓕 (MeasureTheory.Lp.toTemperedDistribution Fl)) s =
      (MeasureTheory.Lp.toTemperedDistribution Fl) (𝓕 s) := rfl
  have h4 : (MeasureTheory.Lp.toTemperedDistribution Fl) (𝓕 s) = ∫ x, (𝓕 s) x • Fl x :=
    MeasureTheory.Lp.toTemperedDistribution_apply _ _
  have h5 : ∫ x, s x • ((FourierAux.FT d Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x =
      ∫ x, s x • ((𝓕 Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := rfl
  have := h1.trans (h5.trans (h2.symm.trans (h3.trans h4)))
  simp only [smul_eq_mul] at this
  rw [this]
  refine integral_congr_ae ?_
  filter_upwards [FourierAux.ofRealLp_coe hφ] with x hx
  rw [hx]


lemma rg_inversion {φ : Euc d → ℝ} (hφ : MemLp φ 2 volume) (hc : Continuous φ)
    (hF1 : Integrable (fun ξ : Euc d => fourierL2 φ (-ξ))) (x : Euc d) :
    𝓕 (fun ξ : Euc d => fourierL2 φ (-ξ)) x = ((φ x : ℝ) : ℂ) := by
  set F' : Euc d → ℂ := fun ξ => fourierL2 φ (-ξ) with hF'
  set ψ : Euc d → ℂ := 𝓕 F' with hψ
  have hψc : Continuous ψ :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hF1
  have hφc : Continuous (fun x => ((φ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hc
  have hψloc : LocallyIntegrable ψ volume := hψc.locallyIntegrable
  have hφloc : LocallyIntegrable (fun x => ((φ x : ℝ) : ℂ)) volume := hφc.locallyIntegrable
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (ψ x - ((φ x : ℝ) : ℂ)) = 0 := by
    intro g hg hsupp
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hsC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set s : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hgC with hsdef
    have hs : ⇑s = fun x => ((g x : ℝ) : ℂ) := rfl
    set t : SchwartzMap (Euc d) ℂ := 𝓕⁻ s with htdef
    have ht : 𝓕 t = s := FourierInvPair.fourier_fourierInv_eq s
    have htapply : ∀ ξ, t ξ = 𝓕 (⇑s) (-ξ) := by
      intro ξ
      rw [htdef, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    have h1 : ∫ x, g x • ψ x = ∫ ξ, 𝓕 (⇑s) (-ξ) * fourierL2 φ ξ := by
      have hflip : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
        ext x y
        simp
      have e0 := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        (L := innerₗ (Euc d)) (f := F') (g := ⇑s)
        Real.continuous_fourierChar continuous_inner hF1 s.integrable
      rw [hflip] at e0
      simp only [smul_eq_mul] at e0
      have e1 : ∫ x, g x • ψ x = ∫ ξ, ψ ξ * s ξ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hs, Complex.real_smul]
        ring
      rw [e1]
      have e2 : (∫ ξ, ψ ξ * s ξ) = ∫ ξ, F' ξ * 𝓕 (⇑s) ξ := e0
      rw [e2]
      have e3 := integral_neg_eq_self (fun ξ : Euc d => F' ξ * 𝓕 (⇑s) ξ) (volume : Measure (Euc d))
      rw [← e3]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      simp only [hF', neg_neg]
      ring
    have h2 : ∫ x, g x • ((φ x : ℝ) : ℂ) = ∫ ξ, 𝓕 (⇑s) (-ξ) * fourierL2 φ ξ := by
      have e0 := rg_fourierL2_dual hφ t
      rw [ht] at e0
      have e1 : ∫ x, g x • ((φ x : ℝ) : ℂ) = ∫ x, s x * ((φ x : ℝ) : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hs, Complex.real_smul]
      rw [e1, ← e0]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      show t ξ * fourierL2 φ ξ = _
      rw [htapply ξ]
    have hsplit : ∫ x, g x • (ψ x - ((φ x : ℝ) : ℂ)) =
        (∫ x, g x • ψ x) - ∫ x, g x • ((φ x : ℝ) : ℂ) := by
      rw [← integral_sub]
      · simp only [smul_sub]
      · exact Continuous.integrable_of_hasCompactSupport (hg.continuous.smul hψc) hsupp.smul_right
      · exact Continuous.integrable_of_hasCompactSupport (hg.continuous.smul hφc) hsupp.smul_right
    rw [hsplit, h1, h2, sub_self]
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hψloc.sub hφloc) key
  have hae : ψ =ᵐ[volume] fun x => ((φ x : ℝ) : ℂ) := by
    filter_upwards [hzero] with x hx
    simpa [sub_eq_zero] using hx
  exact congrFun ((Continuous.ae_eq_iff_eq volume hψc hφc).1 hae) x


lemma rg_wt_ge (ξ : Euc d) : (1 + ‖ξ‖) ^ 2 / 2 ≤ FourierAux.wt ξ := by
  unfold FourierAux.wt
  have h1 : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (1 - ‖ξ‖), sq_nonneg ‖ξ‖]

lemma rg_integrable_a {l : ℕ} {q : ℝ} (hlq : (l : ℝ) + d / 2 < q) :
    Integrable (fun ξ : Euc d => (‖ξ‖ ^ l * FourierAux.wt ξ ^ (-q / 2)) ^ 2) := by
  have hq0 : 0 < q := by
    have : (0 : ℝ) ≤ l + d / 2 := by positivity
    linarith
  have hint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-(2 * q - 2 * l))) := by
    apply integrable_one_add_norm
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  refine (hint.const_mul (2 ^ q)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_norm.pow l).mul (FourierAux.continuous_wt_rpow (-q / 2))).pow 2
      |>.aestronglyMeasurable
  · have hw := FourierAux.wt_pos ξ
    have h1 : 0 < 1 + ‖ξ‖ := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    have e1 : (‖ξ‖ ^ l * FourierAux.wt ξ ^ (-q / 2)) ^ 2 = ‖ξ‖ ^ (2 * l) * FourierAux.wt ξ ^ (-q) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (FourierAux.wt ξ ^ (-q / 2)) 2,
        ← Real.rpow_mul hw.le]
      congr 2
      · ring
      · push_cast; ring
    rw [e1]
    have e2 : FourierAux.wt ξ ^ (-q) ≤ 2 ^ q * (1 + ‖ξ‖) ^ (-(2 * q)) := by
      have h2 := rg_wt_ge ξ
      have h3 : 0 < (1 + ‖ξ‖) ^ 2 / 2 := by positivity
      have h4 : (((1 + ‖ξ‖) ^ 2 : ℝ)) ^ (-q) = (1 + ‖ξ‖) ^ (-(2 * q)) := by
        rw [← Real.rpow_natCast (1 + ‖ξ‖) 2, ← Real.rpow_mul h1.le]
        congr 1
        push_cast; ring
      have h5 : (((1 + ‖ξ‖) ^ 2 / 2 : ℝ)) ^ (-q) = 2 ^ q * (1 + ‖ξ‖) ^ (-(2 * q)) := by
        have h6 : ((2 : ℝ)⁻¹) ^ (-q) = 2 ^ q := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [div_eq_mul_inv, Real.mul_rpow (sq_nonneg _) (by norm_num), h4, h6, mul_comm]
      calc FourierAux.wt ξ ^ (-q) ≤ ((1 + ‖ξ‖) ^ 2 / 2) ^ (-q) :=
            Real.rpow_le_rpow_of_nonpos h3 h2 (by linarith)
        _ = _ := h5
    have e3 : ‖ξ‖ ^ (2 * l) ≤ (1 + ‖ξ‖) ^ (2 * l) :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have e4 : (1 + ‖ξ‖) ^ (2 * l) * (1 + ‖ξ‖) ^ (-(2 * q)) = (1 + ‖ξ‖) ^ (-(2 * q - 2 * l)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add h1]
      congr 1
      push_cast; ring
    calc ‖ξ‖ ^ (2 * l) * FourierAux.wt ξ ^ (-q)
        ≤ (1 + ‖ξ‖) ^ (2 * l) * (2 ^ q * (1 + ‖ξ‖) ^ (-(2 * q))) :=
          mul_le_mul e3 e2 (by positivity) (by positivity)
      _ = 2 ^ q * ((1 + ‖ξ‖) ^ (2 * l) * (1 + ‖ξ‖) ^ (-(2 * q))) := by ring
      _ = _ := by rw [e4]


lemma rg_moment_bound (l : ℕ) {q : ℝ} (hlq : (l : ℝ) + d / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ToolboxRd.MemSobolev q u →
      Integrable (fun ξ : Euc d => ‖ξ‖ ^ l * ‖fourierL2 u ξ‖) ∧
      ∫ ξ, ‖ξ‖ ^ l * ‖fourierL2 u ξ‖ ≤ C * Real.sqrt (sobolevNormSq q u) := by
  refine ⟨Real.sqrt (∫ ξ : Euc d, (‖ξ‖ ^ l * FourierAux.wt ξ ^ (-q / 2)) ^ 2), Real.sqrt_nonneg _,
    fun u hu => ?_⟩
  have hIa := rg_integrable_a (d := d) hlq
  set a : Euc d → ℝ := fun ξ => ‖ξ‖ ^ l * FourierAux.wt ξ ^ (-q / 2) with ha
  set b : Euc d → ℝ := fun ξ => FourierAux.wt ξ ^ (q / 2) * ‖fourierL2 u ξ‖ with hb
  have hFm := FourierAux.aestronglyMeasurable_fourierL2 hu.1
  have hab : ∀ ξ : Euc d, ‖ξ‖ ^ l * ‖fourierL2 u ξ‖ = a ξ * b ξ := by
    intro ξ
    have hw := FourierAux.wt_pos ξ
    simp only [ha, hb]
    have : FourierAux.wt ξ ^ (-q / 2) * FourierAux.wt ξ ^ (q / 2) = 1 := by
      rw [← Real.rpow_add hw]; norm_num [show -q / 2 + q / 2 = 0 by ring]
    calc ‖ξ‖ ^ l * ‖fourierL2 u ξ‖ = ‖ξ‖ ^ l * ‖fourierL2 u ξ‖ * (FourierAux.wt ξ ^ (-q / 2) * FourierAux.wt ξ ^ (q / 2)) := by rw [this, mul_one]
      _ = _ := by ring
  have ha_nn : ∀ ξ, 0 ≤ a ξ := fun ξ => by
    have := FourierAux.wt_pos ξ
    simp only [ha]; positivity
  have hb_nn : ∀ ξ, 0 ≤ b ξ := fun ξ => by
    have := FourierAux.wt_pos ξ
    simp only [hb]; positivity
  have hacont : Continuous a := (continuous_norm.pow l).mul (FourierAux.continuous_wt_rpow (-q / 2))
  have hbm : AEStronglyMeasurable b volume :=
    ((FourierAux.continuous_wt_rpow (q / 2)).aestronglyMeasurable).mul hFm.norm
  have hbsq : ∀ ξ, b ξ ^ 2 = FourierAux.wt ξ ^ q * ‖fourierL2 u ξ‖ ^ 2 := by
    intro ξ
    have hw := FourierAux.wt_pos ξ
    simp only [hb]
    rw [mul_pow, ← Real.rpow_natCast (FourierAux.wt ξ ^ (q / 2)) 2, ← Real.rpow_mul hw.le]
    congr 2
    push_cast; ring
  have hIb : Integrable (fun ξ => b ξ ^ 2) := by
    have := hu.2
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    show _ = b ξ ^ 2
    rw [hbsq]; rfl
  have hMa : MemLp a 2 volume :=
    (memLp_two_iff_integrable_sq hacont.aestronglyMeasurable).2 hIa
  have hMb : MemLp b 2 volume := (memLp_two_iff_integrable_sq hbm).2 hIb
  have hint : Integrable (fun ξ => a ξ * b ξ) := hMa.integrable_mul hMb
  have hfun : (fun ξ : Euc d => ‖ξ‖ ^ l * ‖fourierL2 u ξ‖) = fun ξ => a ξ * b ξ := funext hab
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hfun]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure (Euc d)))
    (p := 2) (q := 2) (by exact Real.HolderConjugate.two_two) (Eventually.of_forall ha_nn)
    (Eventually.of_forall hb_nn) (by simpa using hMa) (by simpa using hMb)
  have e1 : ∫ ξ, a ξ ^ (2 : ℝ) = ∫ ξ, a ξ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp
  have e2 : ∫ ξ, b ξ ^ (2 : ℝ) = ToolboxRd.sobolevNormSq q u := by
    unfold ToolboxRd.sobolevNormSq
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Real.rpow_two]
    rw [hbsq]; rfl
  rw [e1, e2] at hH
  simpa [Real.sqrt_eq_rpow] using hH


lemma rg_norm_iteratedFDeriv_fourier_le {f : Euc d → ℂ} {j : ℕ}
    (hf : ∀ n : ℕ, n ≤ j → Integrable (fun v : Euc d => ‖v‖ ^ n * ‖f v‖))
    (hm : AEStronglyMeasurable f volume) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (𝓕 f) x‖ ≤ (2 * Real.pi) ^ j * ∫ v, ‖v‖ ^ j * ‖f v‖ := by
  have h1 := Real.iteratedFDeriv_fourier (N := (j : ℕ∞)) (fun n hn => hf n (by exact_mod_cast hn)) hm
    (n := j) le_rfl
  rw [h1]
  set g : Euc d → (Euc d [×j]→L[ℝ] ℂ) := fun v => VectorFourier.fourierPowSMulRight (innerSL ℝ) f v j
    with hg
  have hpt : ∀ v, ‖g v‖ ≤ (2 * Real.pi) ^ j * (‖v‖ ^ j * ‖f v‖) := by
    intro v
    have := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) f v j
    refine this.trans ?_
    have h2 : (2 * Real.pi * ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖) ^ j ≤ (2 * Real.pi) ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      have := norm_innerSL_le (𝕜 := ℝ) (E := Euc d)
      nlinarith [Real.pi_pos]
    calc (2 * Real.pi * ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖) ^ j * ‖v‖ ^ j * ‖f v‖
        ≤ (2 * Real.pi) ^ j * ‖v‖ ^ j * ‖f v‖ := by gcongr
      _ = _ := by ring
  have hint : Integrable (fun v : Euc d => (2 * Real.pi) ^ j * (‖v‖ ^ j * ‖f v‖)) :=
    (hf j le_rfl).const_mul _
  rw [Real.fourier_eq]
  calc ‖∫ v, 𝐞 (-inner ℝ v x) • g v‖ ≤ ∫ v, ‖𝐞 (-inner ℝ v x) • g v‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v, (2 * Real.pi) ^ j * (‖v‖ ^ j * ‖f v‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) hint
          (Eventually.of_forall fun v => ?_)
        show ‖𝐞 (-inner ℝ v x) • g v‖ ≤ _
        exact (le_of_eq (Circle.norm_smul _ _)).trans (hpt v)
    _ = _ := by rw [integral_const_mul]


/-- Sobolev embedding on `ℝ^d`: for `φ` smooth with `φ ∈ H^q`, `j + d/2 < q`, the `j`-th derivative is bounded by
the `H^q` norm. -/
theorem rg_sobolev_embedding (j : ℕ) {q : ℝ} (hq : (j : ℝ) + d / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → ToolboxRd.MemSobolev q φ →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j φ x‖ ≤ C * HRS.Whole.sobolevNorm q φ := by
  obtain ⟨Cj, hCj0, hCj⟩ := rg_moment_bound (d := d) j hq
  refine ⟨(2 * Real.pi) ^ j * Cj, by positivity, fun φ hφ hmem x => ?_⟩
  have hF := FourierAux.aestronglyMeasurable_fourierL2 hmem.1
  have hmom : ∀ n : ℕ, n ≤ j → Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖fourierL2 φ ξ‖) := by
    intro n hn
    have hnq : (n : ℝ) + d / 2 < q := by
      have : (n : ℝ) ≤ j := by exact_mod_cast hn
      linarith
    obtain ⟨Cn, -, hCn⟩ := rg_moment_bound (d := d) n hnq
    exact (hCn φ hmem).1
  set F' : Euc d → ℂ := fun ξ => fourierL2 φ (-ξ) with hF'
  have hF'm : AEStronglyMeasurable F' volume :=
    hF.comp_quasiMeasurePreserving (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have hF'int : ∀ n : ℕ, n ≤ j → Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖F' ξ‖) := by
    intro n hn
    have := (hmom n hn).comp_neg
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [hF']
  have hcont : Continuous φ := hφ.continuous
  have hF1 : Integrable F' := by
    have := hF'int 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hF'm).1 this
  have hinv : (fun y : Euc d => ((φ y : ℝ) : ℂ)) = 𝓕 F' := by
    funext y
    exact (rg_inversion hmem.1 hcont hF1 y).symm
  have hcd : ContDiff ℝ ∞ (fun y : Euc d => ((φ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have e1 : ‖iteratedFDeriv ℝ j φ x‖ = ‖iteratedFDeriv ℝ j (fun y : Euc d => ((φ y : ℝ) : ℂ)) x‖ := by
    have := LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.ofRealLI
      (hφ.contDiffAt (x := x)) (i := j) (by exact_mod_cast le_top)
    exact this.symm
  rw [e1, hinv]
  refine (rg_norm_iteratedFDeriv_fourier_le hF'int hF'm x).trans ?_
  have e2 : ∫ v : Euc d, ‖v‖ ^ j * ‖F' v‖ = ∫ v : Euc d, ‖v‖ ^ j * ‖fourierL2 φ v‖ := by
    have := integral_neg_eq_self (fun ξ : Euc d => ‖ξ‖ ^ j * ‖fourierL2 φ ξ‖) (volume : Measure (Euc d))
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [hF']
  rw [e2]
  have := (hCj φ hmem).2
  calc (2 * Real.pi) ^ j * ∫ v : Euc d, ‖v‖ ^ j * ‖fourierL2 φ v‖
      ≤ (2 * Real.pi) ^ j * (Cj * Real.sqrt (ToolboxRd.sobolevNormSq q φ)) := by gcongr
    _ = _ := by unfold HRS.Whole.sobolevNorm; ring

end HRS.MP.RdGen
