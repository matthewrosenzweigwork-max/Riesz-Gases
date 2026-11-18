import HRS.MC.S7FCBConv

/-!
# FC-B, part 8: `L^p` convergence of the averaging operator
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

local instance fcb_borel_prod2'' : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4'' : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

theorem fcbT_stronglyMeasurable (n : ℕ) {f : Torus d × Torus d → ℝ} (hfm : Measurable f) :
    StronglyMeasurable (fcbT d n f) := by
  have : Measurable fun p : (Torus d × Torus d) × (Torus d × Torus d) =>
      fcbKap d n (p.1 - p.2) * f p.2 :=
    (((fcbKap_continuous n).comp (continuous_fst.sub continuous_snd)).measurable).mul (hfm.comp measurable_snd)
  exact this.stronglyMeasurable.integral_prod_right'

theorem fcb_integrable_kmul (n : ℕ) {f : Torus d × Torus d → ℝ} (hf : Integrable f (volume.prod volume))
    (x : Torus d × Torus d) :
    Integrable (fun q => fcbKap d n (x - q) * f q) (volume.prod volume) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (fcbKap_continuous (d := d) n).continuousOn
  exact hf.bdd_mul ((fcbKap_continuous n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (c := C) (Eventually.of_forall fun q => by
      have := hC (x - q) (mem_univ _); simpa using this)

theorem fcbT_sub (n : ℕ) {f g : Torus d × Torus d → ℝ} (hf : Integrable f (volume.prod volume))
    (hg : Integrable g (volume.prod volume)) (x : Torus d × Torus d) :
    fcbT d n (fun q => f q - g q) x = fcbT d n f x - fcbT d n g x := by
  unfold fcbT
  simp_rw [mul_sub]
  exact integral_sub (fcb_integrable_kmul n hf x) (fcb_integrable_kmul n hg x)

theorem fcb_eLpNorm_T_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 < p)
    {f : Torus d × Torus d → ℝ} (hfm : Measurable f) :
    eLpNorm (fcbT d n f) (ENNReal.ofReal p) (volume.prod volume) ≤
      eLpNorm f (ENNReal.ofReal p) (volume.prod volume) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using (by linarith : 0 < p)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (fcbT_stronglyMeasurable n hfm).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hfm.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by linarith)]
  exact ENNReal.rpow_le_rpow (fcbT_lintegral_le hd hn hp hfm) (by positivity)

theorem fcb_Lp_conv (hd : 0 < d) {p : ℝ} (hp : 1 < p) {f : Torus d × Torus d → ℝ} (hfm : Measurable f)
    (hf : MemLp f (ENNReal.ofReal p) (volume.prod volume)) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => fcbT d (n + 1) f x - f x) (ENNReal.ofReal p)
      (volume.prod volume)) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfi : Integrable f (volume.prod volume) := hf.integrable hp1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun n => hεt ▸ le_top
  have hε3 : ε / 3 ≠ 0 := by
    intro h
    rw [ENNReal.div_eq_zero_iff] at h
    rcases h with h | h
    · exact hε.ne' h
    · simp at h
  have hε3t : ε / 3 ≠ ⊤ := ENNReal.div_ne_top hεt (by norm_num)
  obtain ⟨g, hgf, hgm⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hptop hε3
  have hgi : Integrable g (volume.prod volume) := hgm.integrable hp1
  have hηpos : 0 < (ε / 3).toReal := ENNReal.toReal_pos hε3 hε3t
  obtain ⟨N, hN⟩ := fcbT_unif_conv hd g.continuous hηpos
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
  -- decomposition
  have hdec : (fun x => fcbT d (n + 1) f x - f x) =
      (fun x => fcbT d (n + 1) (fun q => f q - g q) x) + (fun x => fcbT d (n + 1) g x - g x) +
        (fun x => g x - f x) := by
    funext x
    simp only [Pi.add_apply]
    rw [fcbT_sub (n + 1) hfi hgi]
    ring
  rw [hdec]
  have hfg : Measurable fun q => f q - g q := hfm.sub g.continuous.measurable
  have t1 : eLpNorm (fun x => fcbT d (n + 1) (fun q => f q - g q) x) (ENNReal.ofReal p) (volume.prod volume)
      ≤ ε / 3 := by
    refine (fcb_eLpNorm_T_le hd hn1 hp hfg).trans ?_
    have : (fun q => f q - g q) = f - ⇑g := rfl
    rw [this]; exact hgf
  have t2 : eLpNorm (fun x => fcbT d (n + 1) g x - g x) (ENNReal.ofReal p) (volume.prod volume) ≤ ε / 3 := by
    have hmeas : AEStronglyMeasurable (fun x => fcbT d (n + 1) g x - g x) (volume.prod volume) :=
      ((fcbT_stronglyMeasurable (n + 1) g.continuous.measurable).sub
        g.continuous.measurable.stronglyMeasurable).aestronglyMeasurable
    refine (eLpNorm_le_of_ae_bound (C := (ε / 3).toReal) hmeas
      (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hN (n + 1) (by omega) hn1 x
    · rw [measure_univ, ENNReal.one_rpow, one_mul, ENNReal.ofReal_toReal hε3t]
  have t3 : eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) (volume.prod volume) ≤ ε / 3 := by
    have : (fun x => g x - f x) = ⇑g - f := rfl
    rw [this, eLpNorm_sub_comm]; exact hgf
  calc _ ≤ eLpNorm (fun x => fcbT d (n + 1) (fun q => f q - g q) x + (fun x => fcbT d (n + 1) g x - g x) x)
          (ENNReal.ofReal p) (volume.prod volume) + eLpNorm (fun x => g x - f x) (ENNReal.ofReal p)
          (volume.prod volume) := eLpNorm_add_le hp1
    _ ≤ (eLpNorm (fun x => fcbT d (n + 1) (fun q => f q - g q) x) (ENNReal.ofReal p) (volume.prod volume) +
          eLpNorm (fun x => fcbT d (n + 1) g x - g x) (ENNReal.ofReal p) (volume.prod volume)) +
          eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) (volume.prod volume) := by
        gcongr; exact eLpNorm_add_le hp1
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := ENNReal.add_thirds ε

end HRS.MC.Sec7.FCB
