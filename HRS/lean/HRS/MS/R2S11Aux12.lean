import HRS.MS.R2S11Aux11

/-!
# S11.4 item (5): the window time integral, given the uniform `L^{rr}` bounds of items (2), (3) and the joint measurability of the class
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole HRS.MS.R2Mt
open HRS (Euc)

variable {d : ℕ}

/-- Item (5) of `r2_moving_moment_transfer` for the data `(B, rr)`. -/
def S11Item5 (d : ℕ) (s q β γ : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ B rr : ℝ) : Prop :=
  2 ≤ rr → ∀ T : ℝ, 0 < T → ∃ CT : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
      [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → EucConfig d N)
      (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N),
      (∀ N, 2 ≤ N → MovParticleSetup (P N) d s q β N (X₀ N) (W N) (X N) ∧
        MovPrepared d s N γ (HRS.Whole.withDensityReal (ρ 0)) ((P N).map (X₀ N))) →
      ∀ h : ℝ → Euc d → Euc d → ℝ,
        (Measurable fun p : ℝ × Euc d × Euc d => h p.1 p.2.1 p.2.2) →
        (∀ t, 0 ≤ t → IsBoundedPairKernel s B (h t)) → ∀ b : ℝ, 0 ≤ b → ∀ N : ℕ, 2 ≤ N →
          ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), ENNReal.ofReal
              (((N : ℝ) * pairEnergy (h t) (X N t.toNNReal ζ) (HRS.Whole.withDensityReal (ρ t))) ^ 2)) ^ (rr / 2)
            ∂(P N) ≤ ENNReal.ofReal CT

/-- The time-slice bound: `∫ (f∘X_t)^{2·(rr/2)} dP ≤ C^{rr}` from the `L^{rr}` bound of `f` under the law of `X_t`. -/
theorem s11_slice {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) (Xt : Ω → E)
    (hXt : Measurable Xt) (f : E → ℝ) (hf : Measurable f) {rr C : ℝ} (hrr : 2 ≤ rr)
    (hb : eLpNorm f (ENNReal.ofReal rr) (P.map Xt) ≤ ENNReal.ofReal C) :
    ∫⁻ ζ, ENNReal.ofReal ((f (Xt ζ)) ^ 2) ^ (rr / 2) ∂P ≤ ENNReal.ofReal C ^ rr := by
  have hrr0 : 0 < rr := by linarith
  have h2 := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := P.map Xt)
    (p := ENNReal.ofReal rr) (by simpa using hrr0) ENNReal.ofReal_ne_top hf.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal hrr0.le] at h2
  have h3 : (∫⁻ x, ‖f x‖ₑ ^ rr ∂(P.map Xt)) = (eLpNorm f (ENNReal.ofReal rr) (P.map Xt)) ^ rr := by
    rw [h2, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hrr0.ne', ENNReal.rpow_one]
  have hmap := lintegral_map (μ := P) (f := fun x => ‖f x‖ₑ ^ rr) (g := Xt) (hf.enorm.pow_const rr) hXt
  calc ∫⁻ ζ, ENNReal.ofReal ((f (Xt ζ)) ^ 2) ^ (rr / 2) ∂P = ∫⁻ ζ, ‖f (Xt ζ)‖ₑ ^ rr ∂P := by
        refine lintegral_congr fun ζ => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by linarith), Real.enorm_eq_ofReal_abs,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hrr0.le]
        congr 1
        rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        ring
    _ = ∫⁻ x, ‖f x‖ₑ ^ rr ∂(P.map Xt) := hmap.symm
    _ = (eLpNorm f (ENNReal.ofReal rr) (P.map Xt)) ^ rr := h3
    _ ≤ ENNReal.ofReal C ^ rr := ENNReal.rpow_le_rpow hb hrr0.le

/-- Hölder in time and Tonelli: from slice bounds to the window bound. -/
theorem s11_time_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (G : ℝ × Ω → ℝ≥0∞)
    (hG : Measurable G) {q T b : ℝ} (hq : 1 ≤ q) (hT : 0 ≤ T) {K : ℝ≥0∞}
    (hK : ∀ t ∈ Set.Icc b (b + T), ∫⁻ ζ, G (t, ζ) ^ q ∂P ≤ K) :
    ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), G (t, ζ)) ^ q ∂P ≤ ENNReal.ofReal T ^ q * K := by
  have hvol : volume (Set.Icc b (b + T)) = ENNReal.ofReal T := by
    rw [Real.volume_Icc]; congr 1; ring
  have hHolder : ∀ ζ, (∫⁻ t in Set.Icc b (b + T), G (t, ζ)) ^ q ≤
      ENNReal.ofReal T ^ (q - 1) * (∫⁻ t in Set.Icc b (b + T), G (t, ζ) ^ q) := fun ζ =>
    s11_holder_time hq _ hvol ((hG.comp (measurable_id.prodMk measurable_const)).aemeasurable)
  have hne : ENNReal.ofReal T ^ (q - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  calc ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), G (t, ζ)) ^ q ∂P
      ≤ ∫⁻ ζ, (ENNReal.ofReal T ^ (q - 1) * ∫⁻ t in Set.Icc b (b + T), G (t, ζ) ^ q) ∂P :=
        lintegral_mono hHolder
    _ = ENNReal.ofReal T ^ (q - 1) * ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), G (t, ζ) ^ q) ∂P :=
        lintegral_const_mul' _ _ hne
    _ = ENNReal.ofReal T ^ (q - 1) * ∫⁻ t in Set.Icc b (b + T), (∫⁻ ζ, G (t, ζ) ^ q ∂P) := by
        rw [lintegral_lintegral_swap]
        exact ((hG.pow_const q).comp measurable_swap).aemeasurable
    _ ≤ ENNReal.ofReal T ^ (q - 1) * ∫⁻ t in Set.Icc b (b + T), K :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Icc hK) _
    _ = ENNReal.ofReal T ^ (q - 1) * (K * ENNReal.ofReal T) := by rw [setLIntegral_const, hvol]
    _ = ENNReal.ofReal T ^ q * K := by
        have : ENNReal.ofReal T ^ q = ENNReal.ofReal T ^ (q - 1) * ENNReal.ofReal T := by
          have := ENNReal.rpow_add_of_nonneg (x := ENNReal.ofReal T) (q - 1) 1 (by linarith) zero_le_one
          rw [sub_add_cancel, ENNReal.rpow_one] at this
          exact this
        rw [this]; ring

theorem s11_G_meas {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (h : ℝ → Euc d → Euc d → ℝ)
    (hhm : Measurable fun p : ℝ × Euc d × Euc d => h p.1 p.2.1 p.2.2) (ρ' : ℝ → Euc d → ℝ)
    (hρ' : Measurable fun p : ℝ × Euc d => ρ' p.1 p.2) (X' : ℝ × Ω → EucConfig d N) (hX' : Measurable X') :
    Measurable fun p : ℝ × Ω => ENNReal.ofReal (((N : ℝ) * pairEnergy (h p.1) (X' p)
      (HRS.Whole.withDensityReal (ρ' p.1))) ^ 2) := by
  have h1 := s11_pairEnergy_meas (N := N) h hhm ρ' hρ'
  have h2 : Measurable fun p : ℝ × Ω => pairEnergy (h p.1) (X' p) (HRS.Whole.withDensityReal (ρ' p.1)) :=
    Measurable.comp (g := fun q : ℝ × EucConfig d N => pairEnergy (h q.1) q.2 (HRS.Whole.withDensityReal (ρ' q.1)))
      (f := fun p : ℝ × Ω => (p.1, X' p)) h1 (measurable_fst.prodMk hX')
  have h3 : Measurable fun p : ℝ × Ω => (N : ℝ) * pairEnergy (h p.1) (X' p) (HRS.Whole.withDensityReal (ρ' p.1)) :=
    h2.const_mul (N : ℝ)
  have h4 : Measurable fun p : ℝ × Ω => ((N : ℝ) * pairEnergy (h p.1) (X' p)
      (HRS.Whole.withDensityReal (ρ' p.1))) ^ 2 := h3.pow_const 2
  exact ENNReal.measurable_ofReal.comp h4

theorem s11_item5 {s q β γ : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ B rr : ℝ}
    (hmeas : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 → ∀ ρ : ℝ → Euc d → ℝ,
      MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → Measurable fun p : ℝ≥0 × Euc d => ρ p.1 p.2)
    (hI : S11Items23 d s q β γ ρ₀ j m εstar r c₀ B rr) :
    S11Item5 d s q β γ ρ₀ j m εstar r c₀ B rr := by
  intro hrr T hT
  obtain ⟨C, hC⟩ := hI
  refine ⟨T ^ (rr / 2) * (max C 0) ^ rr, ?_⟩
  intro f0 hf0 ρ hρ' Ω _ P _ X₀ W X hsetup h hhm hhb b hb N hN
  have hq1 : 1 ≤ rr / 2 := by linarith
  have hrr0 : 0 < rr := by linarith
  have hfb := (hC f0 hf0 ρ hρ' Ω P X₀ W X hsetup).1
  obtain ⟨X', hX'm, hX'e⟩ := s11_X_joint (P := P N) (X := X N)
    (fun t => (((hsetup N hN).1.sol 0).adapted t)) ((hsetup N hN).1.sol 0).cont
  have hρtm : Measurable fun p : ℝ × Euc d => ρ p.1.toNNReal p.2 :=
    (hmeas f0 hf0 ρ hρ').comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hGm := s11_G_meas (N := N) h hhm (fun t => ρ t.toNNReal) hρtm X' hX'm
  have hLHS : ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), ENNReal.ofReal
      (((N : ℝ) * pairEnergy (h t) (X N t.toNNReal ζ) (HRS.Whole.withDensityReal (ρ t))) ^ 2)) ^ (rr / 2) ∂(P N) =
      ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), ENNReal.ofReal (((N : ℝ) * pairEnergy (h t) (X' (t, ζ))
        (HRS.Whole.withDensityReal (ρ t.toNNReal))) ^ 2)) ^ (rr / 2) ∂(P N) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hX'e] with ζ hζ
    congr 1
    refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have ht0 : 0 ≤ t := hb.trans ht.1
    rw [hζ t, Real.coe_toNNReal t ht0]
  have hslice : ∀ t ∈ Set.Icc b (b + T), ∫⁻ ζ, ENNReal.ofReal (((N : ℝ) * pairEnergy (h t) (X' (t, ζ))
      (HRS.Whole.withDensityReal (ρ t.toNNReal))) ^ 2) ^ (rr / 2) ∂(P N) ≤ ENNReal.ofReal (max C 0) ^ rr := by
    intro t ht
    have ht0 : 0 ≤ t := hb.trans ht.1
    have e : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0
    have hk := hhb t ht0
    haveI : SFinite (HRS.Whole.withDensityReal (ρ t)) := by
      unfold HRS.Whole.withDensityReal; infer_instance
    have hfm : Measurable (fun Z : EucConfig d N => (N : ℝ) *
        pairEnergy (h t) Z (HRS.Whole.withDensityReal (ρ t))) :=
      measurable_const.mul (HRS.MS.Wr.wr9_measurable_pairEnergy hk.measurable)
    obtain ⟨h1, -⟩ := hfb (h t) hk t.toNNReal N hN
    simp only [r2MovFamily, e] at h1
    have hXm : Measurable (X N t.toNNReal) := ((hsetup N hN).1.sol 0).adapted _
    have := s11_slice (P N) (X N t.toNNReal) hXm _ hfm hrr (rr := rr) (C := C) h1
    calc _ = ∫⁻ ζ, ENNReal.ofReal (((N : ℝ) * pairEnergy (h t) (X N t.toNNReal ζ)
          (HRS.Whole.withDensityReal (ρ t))) ^ 2) ^ (rr / 2) ∂(P N) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hX'e] with ζ hζ
          rw [hζ t, e]
      _ ≤ ENNReal.ofReal C ^ rr := this
      _ ≤ ENNReal.ofReal (max C 0) ^ rr :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hrr0.le
  rw [hLHS]
  refine (s11_time_integral (P N) _ hGm hq1 hT.le hslice).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg hT.le (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hrr0.le]

end HRS.MS.R2S11
