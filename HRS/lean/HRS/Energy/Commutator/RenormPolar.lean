import HRS.Energy.Commutator.RenormMu

/-!
# Route S, packet S4: polar coordinates (lintegral form) and the choice of a good radius
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- Polar coordinates in `ℝ^d` for nonnegative measurable functions. -/
theorem lintegral_polar_euc (hd : 1 ≤ d) (g : Euc d → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(volume : Measure (Euc d)) =
      ∫⁻ ω : sphere (0 : Euc d) 1, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * g (t • (ω : Euc d)))
        ∂(volume : Measure (Euc d)).toSphere := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  calc ∫⁻ y, g y ∂(volume : Measure (Euc d))
      = ∫⁻ x : ({(0 : Euc d)}ᶜ : Set (Euc d)), g x.1 ∂((volume : Measure (Euc d)).comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0 : Euc d) 1 × Ioi (0 : ℝ), g (p.2.1 • (p.1 : Euc d))
          ∂((volume : Measure (Euc d)).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ (Euc d) - 1))) := by
        have := (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (Euc d))).lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (fun p : sphere (0 : Euc d) 1 × Ioi (0 : ℝ) => g (p.2.1 • (p.1 : Euc d)))
        rw [← this]
        refine lintegral_congr fun x => ?_
        simp only [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
        have hn : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    _ = _ := by
        rw [lintegral_prod]
        · refine lintegral_congr fun ω => ?_
          simp only [Measure.volumeIoiPow, hfr]
          rw [lintegral_withDensity_eq_lintegral_mul]
          · exact lintegral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
              (fun r : ℝ => ENNReal.ofReal (r ^ (d - 1)) * g (r • (ω : Euc d)))
          · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
          · exact hg.comp (measurable_subtype_coe.smul_const _)
        · exact (hg.comp ((measurable_subtype_coe.comp measurable_snd).smul
            (measurable_subtype_coe.comp measurable_fst))).aemeasurable

theorem lintegral_torus_ball {δ : ℝ} (hδ2 : δ ≤ 1 / 2) (f : Torus d → ℝ≥0∞)
    (hf : ∀ z, δ ≤ KernelGrad.tdist z 0 → f z = 0) :
    ∫⁻ z, f z = ∫⁻ w in ball (0 : Euc d) δ, f (Torus.mk w) := by
  rw [KernelAux.lintegral_torus_box]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h2 := hmp.setLIntegral_comp_preimage_emb hemb (fun y : Fin d → ℝ => f (KernelAux.boxPt y))
    (KernelAux.Box d)
  rw [← h2]
  have hA : MeasurableSet ((@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d)) :=
    (KernelAux.measurableSet_Box d).preimage hmp.measurable
  have hBA : ball (0 : Euc d) δ ⊆ (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d) := by
    intro w hw i
    have h1 := PiLp.norm_apply_le w i
    have h2 : ‖w‖ < δ := by simpa using hw
    have := abs_lt.1 (lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using h1) (h2.trans_le hδ2))
    simp only [mem_Ioc]
    constructor <;> linarith [this.1, this.2]
  rw [← lintegral_indicator hA, ← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun w => ?_
  by_cases hw : w ∈ ball (0 : Euc d) δ
  · rw [indicator_of_mem hw, indicator_of_mem (hBA hw)]; rfl
  · rw [indicator_of_notMem hw]
    by_cases hwA : w ∈ (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d)
    · rw [indicator_of_mem hwA]
      apply hf
      have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
        have := hwA i
        simp only [mem_Ioc] at this
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      have := KernelGrad.tdist_mk (d := d) hy
      have e : KernelGrad.tdist (KernelAux.boxPt (@WithLp.ofLp 2 (Fin d → ℝ) w)) 0 = KernelGrad.tdist (Torus.mk w) 0 := rfl
      rw [e, this]
      simpa [mem_ball, dist_zero_right] using hw
    · rw [indicator_of_notMem hwA]

theorem lintegral_chC (G : Torus d → ℝ≥0∞) (hG : Measurable G) (t : ℝ) (a : Torus d) :
    ∫⁻ x, G x ∂(chC d t a) =
      ((volume : Measure (Euc d)).toSphere univ)⁻¹ *
        ∫⁻ ω : sphere (0 : Euc d) 1, G (Torus.mk (t • (ω : Euc d)) + a) ∂(volume : Measure (Euc d)).toSphere := by
  unfold chC sphereT
  have hadd : Measurable (fun y : Torus d => y + a) := measurable_id.add_const a
  have hsc : Measurable (fun ω : sphere (0 : Euc d) 1 => t • (ω : Euc d)) :=
    measurable_subtype_coe.const_smul t
  have hGa : Measurable (fun y : Torus d => G (y + a)) := hG.comp hadd
  rw [lintegral_map hG hadd, lintegral_map hGa Torus.continuous_mk.measurable,
    lintegral_smul_measure]
  have hGb : Measurable (fun y : Euc d => G (Torus.mk y + a)) := hGa.comp Torus.continuous_mk.measurable
  rw [lintegral_map hGb hsc]
  rfl

/-- the mean of the sphere integrals over `t ∈ (r/2, r)` is the integral over the annulus -/
theorem annulus_polar (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (a : Torus d) (G : Torus d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y : Euc d, (if r / 2 < ‖y‖ ∧ ‖y‖ < r then G (Torus.mk y + a) else 0) =
      ∫⁻ t in Ioo (r / 2) r, ENNReal.ofReal (t ^ (d - 1)) *
        ∫⁻ ω : sphere (0 : Euc d) 1, G (Torus.mk (t • (ω : Euc d)) + a) ∂(volume : Measure (Euc d)).toSphere := by
  have hGa : Measurable (fun y : Euc d => G (Torus.mk y + a)) :=
    (hG.comp (measurable_id.add_const a)).comp Torus.continuous_mk.measurable
  have hgm : Measurable (fun y : Euc d => if r / 2 < ‖y‖ ∧ ‖y‖ < r then G (Torus.mk y + a) else 0) := by
    refine Measurable.ite ?_ hGa measurable_const
    exact (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  rw [lintegral_polar_euc hd _ hgm]
  have e1 : ∀ ω : sphere (0 : Euc d) 1,
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) *
        (if r / 2 < ‖t • (ω : Euc d)‖ ∧ ‖t • (ω : Euc d)‖ < r then G (Torus.mk (t • (ω : Euc d)) + a) else 0)) =
      ∫⁻ t in Ioo (r / 2) r, ENNReal.ofReal (t ^ (d - 1)) * G (Torus.mk (t • (ω : Euc d)) + a) := by
    intro ω
    have hω : ‖(ω : Euc d)‖ = 1 := by simp
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Ioo (r / 2) r
    · have ht0 : 0 < t := by linarith [ht.1]
      rw [indicator_of_mem ht, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0)]
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos ht0, if_pos ⟨ht.1, ht.2⟩]
    · rw [indicator_of_notMem ht]
      by_cases ht0 : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht0]
        have ht0' : 0 < t := ht0
        rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos ht0', if_neg (fun h => ht ⟨h.1, h.2⟩), mul_zero]
      · rw [indicator_of_notMem ht0]
  simp_rw [e1]
  have hmeas : Measurable (Function.uncurry fun (ω : sphere (0 : Euc d) 1) (t : ℝ) =>
      ENNReal.ofReal (t ^ (d - 1)) * G (Torus.mk (t • (ω : Euc d)) + a)) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_snd.pow_const _).ennreal_ofReal
    · exact hGa.comp ((measurable_snd).smul (measurable_subtype_coe.comp measurable_fst))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [lintegral_const_mul]
  exact hGa.comp (measurable_const_smul t |>.comp measurable_subtype_coe)

theorem annulus_le_torus (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) (a : Torus d)
    (G : Torus d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y : Euc d, (if r / 2 < ‖y‖ ∧ ‖y‖ < r then G (Torus.mk y + a) else 0) ≤
      ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then G x else 0) := by
  have hGa : Measurable (fun y : Euc d => G (Torus.mk y + a)) :=
    (hG.comp (measurable_id.add_const a)).comp Torus.continuous_mk.measurable
  have h1 : ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then G x else 0) =
      ∫⁻ z : Torus d, (if r / 2 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < r then G (z + a) else 0) := by
    rw [← lintegral_add_right_eq_self (fun x : Torus d =>
      if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then G x else 0) a]
    refine lintegral_congr fun z => ?_
    simp only [EnergyAux.tdist_def (z + a) a, add_sub_cancel_right]
  rw [h1, lintegral_torus_ball hr2 _ (fun z hz => by simp [not_lt.mpr hz])]
  calc ∫⁻ y : Euc d, (if r / 2 < ‖y‖ ∧ ‖y‖ < r then G (Torus.mk y + a) else 0)
      = ∫⁻ y : Euc d, (ball (0 : Euc d) r).indicator
          (fun y => if r / 2 < ‖y‖ ∧ ‖y‖ < r then G (Torus.mk y + a) else 0) y := by
        refine lintegral_congr fun y => ?_
        by_cases h : r / 2 < ‖y‖ ∧ ‖y‖ < r
        · rw [indicator_of_mem (by simpa using h.2)]
        · rw [if_neg h]
          by_cases hb : y ∈ ball (0 : Euc d) r
          · rw [indicator_of_mem hb, if_neg h]
          · rw [indicator_of_notMem hb]
    _ = ∫⁻ w in ball (0 : Euc d) r, (if r / 2 < ‖w‖ ∧ ‖w‖ < r then G (Torus.mk w + a) else 0) :=
        lintegral_indicator measurableSet_ball _
    _ ≤ ∫⁻ w in ball (0 : Euc d) r, (if r / 2 < KernelGrad.tdist (Torus.mk w) 0 ∧ KernelGrad.tdist (Torus.mk w) 0 < r
          then G (Torus.mk w + a) else 0) := by
        refine le_of_eq (setLIntegral_congr_fun measurableSet_ball fun w hw => ?_)
        have hw' : ‖w‖ < r := by simpa using hw
        have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
          have h1 := PiLp.norm_apply_le w i
          have := (le_of_eq (by simp [Real.norm_eq_abs] : |w i| = ‖w i‖)).trans h1
          linarith
        rw [KernelGrad.tdist_mk hy]

theorem sphere_pick (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) (a : Torus d)
    (G : Torus d → ℝ≥0∞) (hG : Measurable G) :
    ∃ t ∈ Ioo (r / 2) r, (∫⁻ x, G x ∂(chC d t a)) *
        ((volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal ((r / 2) ^ d)) ≤
      ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then G x else 0) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  set S : ℝ≥0∞ := (volume : Measure (Euc d)).toSphere univ with hS
  have hS0 : S ≠ 0 := fun h => Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.mp h)
  have hSt : S ≠ ⊤ := measure_ne_top _ _
  have hGa : Measurable (fun y : Euc d => G (Torus.mk y + a)) :=
    (hG.comp (measurable_id.add_const a)).comp Torus.continuous_mk.measurable
  set Ψ : ℝ → ℝ≥0∞ := fun t => ∫⁻ ω : sphere (0 : Euc d) 1, G (Torus.mk (t • (ω : Euc d)) + a)
    ∂(volume : Measure (Euc d)).toSphere with hΨ
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (d - 1)) * Ψ t with hf
  have hΨm : Measurable Ψ := by
    have : Measurable (fun p : ℝ × sphere (0 : Euc d) 1 => G (Torus.mk (p.1 • (p.2 : Euc d)) + a)) :=
      hGa.comp (measurable_fst.smul (measurable_subtype_coe.comp measurable_snd))
    exact this.lintegral_prod_right'
  have hfm : Measurable f := (measurable_id.pow_const _).ennreal_ofReal.mul hΨm
  have hs0 : (volume : Measure ℝ) (Ioo (r / 2) r) ≠ 0 := by
    rw [Real.volume_Ioo]; simp; linarith
  have hst : (volume : Measure ℝ) (Ioo (r / 2) r) ≠ ⊤ := by
    rw [Real.volume_Ioo]; simp
  obtain ⟨t, ht, hft⟩ := exists_le_setLAverage (μ := (volume : Measure ℝ)) hs0 hst hfm.aemeasurable
  refine ⟨t, ht, ?_⟩
  rw [setLAverage_eq] at hft
  have hft' : f t * (volume : Measure ℝ) (Ioo (r / 2) r) ≤ ∫⁻ t in Ioo (r / 2) r, f t :=
    (ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl hst)).mp hft
  have hann := annulus_polar hd hr a G hG
  have hle := annulus_le_torus hd hr hr2 a G hG
  rw [Real.volume_Ioo] at hft'
  refine le_trans ?_ hle
  rw [hann]
  refine le_trans ?_ hft'
  rw [lintegral_chC G hG t a]
  have e1 : (S⁻¹ * Ψ t) * (S * ENNReal.ofReal ((r / 2) ^ d)) = Ψ t * ENNReal.ofReal ((r / 2) ^ d) := by
    have : (S⁻¹ * Ψ t) * (S * ENNReal.ofReal ((r / 2) ^ d)) = (S⁻¹ * S) * (Ψ t * ENNReal.ofReal ((r / 2) ^ d)) := by ring
    rw [this, ENNReal.inv_mul_cancel hS0 hSt, one_mul]
  rw [e1]
  have hpow : (r / 2) ^ d = (r / 2) ^ (d - 1) * (r / 2) := by
    rw [← pow_succ]; congr 1; omega
  have hr20 : 0 ≤ r / 2 := by linarith
  have h2 : ENNReal.ofReal ((r / 2) ^ (d - 1)) ≤ ENNReal.ofReal (t ^ (d - 1)) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr20 ht.1.le _)
  calc Ψ t * ENNReal.ofReal ((r / 2) ^ d)
      = Ψ t * ENNReal.ofReal ((r / 2) ^ (d - 1)) * ENNReal.ofReal (r / 2) := by
        rw [hpow, ENNReal.ofReal_mul (pow_nonneg hr20 _), mul_assoc]
    _ ≤ Ψ t * ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (r / 2) := by gcongr
    _ = f t * ENNReal.ofReal (r - r / 2) := by
        rw [hf]; dsimp only; rw [mul_comm (Ψ t), show r - r / 2 = r / 2 by ring]

theorem ball_ratio (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) (a : Torus d) :
    (∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0)) =
      ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (ball 0 1) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have h1 : ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0) =
      ∫⁻ z : Torus d, (if KernelGrad.tdist z 0 < r then (1 : ℝ≥0∞) else 0) := by
    rw [← lintegral_add_right_eq_self (fun x : Torus d => if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0) a]
    refine lintegral_congr fun z => ?_
    simp only [EnergyAux.tdist_def (z + a) a, add_sub_cancel_right]
  rw [h1, lintegral_torus_ball hr2 _ (fun z hz => by simp [not_lt.mpr hz])]
  have h2 : ∀ w ∈ ball (0 : Euc d) r, (if KernelGrad.tdist (Torus.mk w) 0 < r then (1 : ℝ≥0∞) else 0) = 1 := by
    intro w hw
    have hw' : ‖w‖ < r := by simpa using hw
    have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
      have h1 := PiLp.norm_apply_le w i
      have := (le_of_eq (by simp [Real.norm_eq_abs] : |w i| = ‖w i‖)).trans h1
      linarith
    rw [KernelGrad.tdist_mk hy, if_pos hw']
  rw [setLIntegral_congr_fun measurableSet_ball h2, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, one_mul, Measure.addHaar_ball_of_pos _ _ hr, hfr]

theorem T_pick (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) (a : Torus d)
    {F : Torus d → Euc d} (hFm : Measurable F)
    (hF2 : Integrable (fun x : Torus d =>
      if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ‖F x‖ ^ 2 else 0) volume)
    {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v) :
    ∃ η : ℝ, r / 2 < η ∧ η < r ∧
      |∫ x, inner ℝ (v a - v x) (F x) ∂(chC d η a)| ≤
        L * r * (2 ^ d / (2 * d) * ε + 2 ^ d / (2 * ε * d * ((volume : Measure (Euc d)) (ball 0 1)).toReal * r ^ d) *
          ∫ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ‖F x‖ ^ 2 else 0)) := by
  have hvc := lipschitzVF_continuous hL hv
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  set ω' : ℝ≥0∞ := (volume : Measure (Euc d)) (ball 0 1) with hω'
  have hω'top : ω' ≠ ⊤ := measure_ball_lt_top.ne
  have hω'pos : 0 < ω'.toReal := ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hω'top
  obtain ⟨Gr, hGr⟩ : ∃ Gr : Torus d → ℝ, Gr = fun x => (ε + ‖F x‖ ^ 2 / ε) / 2 := ⟨_, rfl⟩
  have hGr0 : ∀ x, 0 ≤ Gr x := fun x => by rw [hGr]; positivity
  have hGrm : Measurable Gr := by
    rw [hGr]; exact (measurable_const.add ((hFm.norm.pow_const 2).div_const ε)).div_const 2
  have hFle : ∀ x, ‖F x‖ ≤ Gr x := fun x => by
    rw [hGr]; dsimp only
    have h : ‖F x‖ * 2 ≤ ε + ‖F x‖ ^ 2 / ε := by
      rw [← sub_nonneg]
      have : ε + ‖F x‖ ^ 2 / ε - ‖F x‖ * 2 = (ε - ‖F x‖) ^ 2 / ε := by field_simp; ring
      rw [this]; positivity
    linarith
  obtain ⟨η, hη, hineq⟩ := sphere_pick hd hr hr2 a (fun x => ENNReal.ofReal (Gr x)) hGrm.ennreal_ofReal
  set e : ℝ := ∫ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ‖F x‖ ^ 2 else 0) with he
  have he0 : 0 ≤ e := integral_nonneg fun x => by split_ifs <;> positivity
  have hB : MeasurableSet {x : Torus d | KernelGrad.tdist x a < r} := by
    have : Measurable fun x : Torus d => KernelGrad.tdist x a := by
      have h := EnergyAux.measurable_tdist_zero (d := d)
      have e1 : (fun x : Torus d => KernelGrad.tdist x a) = fun x => KernelGrad.tdist (x - a) 0 := by
        funext x; exact EnergyAux.tdist_def x a
      rw [e1]; exact h.comp (measurable_id.sub_const a)
    exact measurableSet_lt this measurable_const
  have hAm : MeasurableSet {x : Torus d | r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r} := by
    have : Measurable fun x : Torus d => KernelGrad.tdist x a := by
      have h := EnergyAux.measurable_tdist_zero (d := d)
      have e1 : (fun x : Torus d => KernelGrad.tdist x a) = fun x => KernelGrad.tdist (x - a) 0 := by
        funext x; exact EnergyAux.tdist_def x a
      rw [e1]; exact h.comp (measurable_id.sub_const a)
    exact (measurableSet_lt measurable_const this).inter (measurableSet_lt this measurable_const)
  have hR : ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ENNReal.ofReal (Gr x) else 0) ≤
      ENNReal.ofReal (ε / 2) * (ENNReal.ofReal (r ^ d) * ω') + ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal e := by
    have h1 : ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ENNReal.ofReal (Gr x) else 0) ≤
        ∫⁻ x : Torus d, (ENNReal.ofReal (ε / 2) * (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0) +
          ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal
            (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ‖F x‖ ^ 2 else 0)) := by
      refine lintegral_mono fun x => ?_
      by_cases hx : r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r
      · simp only [if_pos hx, if_pos hx.2, mul_one]
        rw [hGr]; dsimp only
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        field_simp
      · simp only [if_neg hx]; exact zero_le
    refine h1.trans (le_of_eq ?_)
    have hB : MeasurableSet {x : Torus d | KernelGrad.tdist x a < r} := by
      have : Measurable fun x : Torus d => KernelGrad.tdist x a := by
        have h := EnergyAux.measurable_tdist_zero (d := d)
        have e1 : (fun x : Torus d => KernelGrad.tdist x a) = fun x => KernelGrad.tdist (x - a) 0 := by
          funext x; exact EnergyAux.tdist_def x a
        rw [e1]; exact h.comp (measurable_id.sub_const a)
      exact measurableSet_lt this measurable_const
    have hm1 : Measurable fun x : Torus d => (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite hB measurable_const measurable_const
    have hm2 : Measurable fun x : Torus d =>
        ENNReal.ofReal (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then ‖F x‖ ^ 2 else 0) :=
      (Measurable.ite hAm (hFm.norm.pow_const 2) measurable_const).ennreal_ofReal
    rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1, lintegral_const_mul _ hm2,
      ball_ratio hd hr hr2 a, he, ← ofReal_integral_eq_lintegral_ofReal hF2 (Filter.Eventually.of_forall fun x => by
        simp only [Pi.zero_apply]; split_ifs <;> positivity)]
  have hη0 : 0 < η := by linarith [hη.1]
  have hS0 : (volume : Measure (Euc d)).toSphere univ ≠ 0 := fun h => Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.mp h)
  have hSeq : (volume : Measure (Euc d)).toSphere univ = (d : ℝ≥0∞) * ω' := by
    rw [Measure.toSphere_apply_univ, hfr]
  have hSreal : ((volume : Measure (Euc d)).toSphere univ).toReal = d * ω'.toReal := by
    rw [hSeq, ENNReal.toReal_mul]; simp
  have hRtop : ENNReal.ofReal (ε / 2) * (ENNReal.ofReal (r ^ d) * ω') + ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal e ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω'top),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hr20 : 0 < r / 2 := by linarith
  have hc0 : (volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal ((r / 2) ^ d) ≠ 0 :=
    mul_ne_zero hS0 (ENNReal.ofReal_pos.mpr (pow_pos hr20 _)).ne'
  set Φ : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Gr x) ∂(chC d η a) with hΦ
  have hΦtop : Φ ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_mul hc0] at hineq
    exact absurd (hineq.trans hR) (not_le.mpr (lt_top_iff_ne_top.mpr hRtop))
  have h3 : Φ.toReal * (d * ω'.toReal * (r / 2) ^ d) ≤ ε / 2 * (r ^ d * ω'.toReal) + 1 / (2 * ε) * e := by
    have := ENNReal.toReal_mono hRtop (hineq.trans hR)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr20.le _), hSreal,
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω'top))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (pow_nonneg hr.le _), ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal he0] at this
    exact this
  have hint : Integrable Gr (chC d η a) := by
    haveI := isFiniteMeasure_chC hd η a
    exact (lintegral_ofReal_ne_top_iff_integrable hGrm.aestronglyMeasurable
      (Filter.Eventually.of_forall hGr0)).mp hΦtop
  have hΦ' : ∫ x, Gr x ∂(chC d η a) = Φ.toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hGr0) hGrm.aestronglyMeasurable
  have hT : ‖∫ x, inner ℝ (v a - v x) (F x) ∂(chC d η a)‖ ≤ ∫ x, L * η * Gr x ∂(chC d η a) := by
    refine norm_integral_le_of_norm_le (hint.const_mul (L * η)) ?_
    filter_upwards [chC_supp hd hη0 (by linarith [hη.2]) a] with x hx
    have h5 := hv a x
    have h6 : KernelGrad.tdist a x ≤ η := by rw [tdist_symm']; exact hx
    calc ‖inner ℝ (v a - v x) (F x)‖ ≤ ‖v a - v x‖ * ‖F x‖ := norm_inner_le_norm _ _
      _ ≤ (L * η) * Gr x := by
          refine mul_le_mul ?_ (hFle x) (norm_nonneg _) (by positivity)
          exact h5.trans (mul_le_mul_of_nonneg_left h6 hL)
  rw [integral_const_mul, hΦ'] at hT
  refine ⟨η, hη.1, hη.2, ?_⟩
  rw [Real.norm_eq_abs] at hT
  have hc : 0 < (d : ℝ) * ω'.toReal * (r / 2) ^ d := by positivity
  have hΦle : Φ.toReal ≤ 2 ^ d / (2 * d) * ε + 2 ^ d / (2 * ε * d * ω'.toReal * r ^ d) * e := by
    rw [← le_div_iff₀ hc] at h3
    refine h3.trans (le_of_eq ?_)
    rw [div_pow]
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp
  calc |∫ x, inner ℝ (v a - v x) (F x) ∂(chC d η a)| ≤ L * η * Φ.toReal := hT
    _ ≤ L * r * Φ.toReal := by
        have hΦ0 : 0 ≤ Φ.toReal := ENNReal.toReal_nonneg
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη.2.le hL) hΦ0
    _ ≤ _ := mul_le_mul_of_nonneg_left hΦle (by positivity)

/-- radial integrals on the torus (nonnegative, supported near the origin) -/
theorem lintegral_torus_radial (hd : 1 ≤ d) {δ : ℝ} (hδ2 : δ ≤ 1 / 2) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hF0 : ∀ r, δ ≤ r → F r = 0) :
    ∫⁻ z : Torus d, F (KernelGrad.tdist z 0) =
      (volume : Measure (Euc d)).toSphere univ * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t := by
  rw [lintegral_torus_ball hδ2 _ (fun z hz => by simp [hF0 _ hz])]
  have h1 : ∀ w ∈ ball (0 : Euc d) δ, F (KernelGrad.tdist (Torus.mk w) 0) = F ‖w‖ := by
    intro w hw
    have hw' : ‖w‖ < δ := by simpa using hw
    have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
      have h1 := PiLp.norm_apply_le w i
      have := (le_of_eq (by simp [Real.norm_eq_abs] : |w i| = ‖w i‖)).trans h1
      linarith
    rw [KernelGrad.tdist_mk hy]
  rw [setLIntegral_congr_fun measurableSet_ball h1, ← lintegral_indicator measurableSet_ball]
  have hm : Measurable (fun w : Euc d => (ball (0 : Euc d) δ).indicator (fun w => F ‖w‖) w) :=
    (hF.comp measurable_norm).indicator measurableSet_ball
  rw [lintegral_polar_euc hd _ hm]
  have e1 : ∀ ω : sphere (0 : Euc d) 1,
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) *
        (ball (0 : Euc d) δ).indicator (fun w => F ‖w‖) (t • (ω : Euc d))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t := by
    intro ω
    have hω : ‖(ω : Euc d)‖ = 1 := by simp
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hn : ‖t • (ω : Euc d)‖ = t := by rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    by_cases htδ : t < δ
    · rw [indicator_of_mem (by simpa [hn] using htδ), hn]
    · rw [indicator_of_notMem (by simpa [hn] using htδ), hF0 t (not_lt.mp htδ)]
  simp_rw [e1]
  rw [lintegral_const]
  simp [mul_comm]

end HRS.Commutator.Renorm
