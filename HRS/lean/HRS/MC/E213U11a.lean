import HRS.MC.E213U5a
import HRS.MC.E213U4
import HRS.MC.S7FCW1W
import HRS.MC.S7FCF5RE3b
import HRS.MC.S7FCF5NF6c
import HRS.MC.S7FCF5E
import HRS.MC.S7UCAE
import HRS.MC.S7FCHA1

/-!
# Packet e213u11, file a: uniform moments of the canonical Gaussian data

For the canonical `GaussData` `gd`, every `Rw > 0` and `q ≥ 1`, the moments `∫ ‖(η^{a+·}, ℬ^{a+·})‖^q` of the pair
(path in `C([0,Rw];E_r)`, quadratic field in `L²([0,Rw];E_r)`) are bounded uniformly in `a ≥ 0`.  Route: the
particle moments (`fcf5_E3b`, `fcf5_F6c`, uniform in `a`, `N ≥ 2`), the `W_1` convergence of `chaos_conv`, Fatou (`D7b`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}


theorem u11_prod_enorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (p : E × F) :
    ‖p‖ₑ = max ‖p.1‖ₑ ‖p.2‖ₑ := by
  simp only [← ofReal_norm, Prod.norm_def, ENNReal.ofReal_max]

/-- Real moment from a `lintegral` bound (the inverse of `S7FCDA_lintegral_le`). -/
theorem u11_real_moment {X : Type*} [NormedAddCommGroup X] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → X} (hf : AEMeasurable (fun ω => ‖f ω‖) P) {q : ℝ} (hq : 0 ≤ q) {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ‖f ω‖ ^ q) P ∧ ∫ ω, ‖f ω‖ ^ q ∂P ≤ C := by
  have hnn : 0 ≤ᵐ[P] fun ω => ‖f ω‖ ^ q := Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hmeas : AEStronglyMeasurable (fun ω => ‖f ω‖ ^ q) P :=
    (hf.pow_const q).aestronglyMeasurable
  have hof : ∀ ω, ‖f ω‖ₑ ^ q = ENNReal.ofReal (‖f ω‖ ^ q) := fun ω => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq]
  simp only [hof] at h
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    exact ENNReal.toReal_le_of_le_ofReal hC0 h

theorem u11_enorm_fst_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (p : E × F) :
    ‖p.1‖ₑ ≤ ‖p‖ₑ := by
  rw [u11_prod_enorm]; exact le_max_left _ _

theorem u11_enorm_snd_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (p : E × F) :
    ‖p.2‖ₑ ≤ ‖p‖ₑ := by
  rw [u11_prod_enorm]; exact le_max_right _ _

section Moments

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- A family of prepared realisations (for all `N`), as in `exists_gaussData_proof`. -/
theorem u11_exists_fam (hE : EdgeworthHyp S β₀ m) : Nonempty (PrepFamily S β₀ hE) := by
  choose Ω mΩ P hP X₀ W X hreal using HRS.MC.E213U4.u4_exists_realizations (regime S β₀ hE)
  exact ⟨{ Ω := Ω, mΩ := mΩ, P := P, pP := hP, X₀ := X₀, W := W, X := X, hreal := hreal }⟩

theorem u11_pair_aemeasurable (Rw : ℝ) (hRw : 0 < Rw) (a : ℝ) (ha : 0 ≤ a) :
    AEMeasurable (pairLim (rLvl d) Rw a gd.η gd.B) gd.P₀ := by
  obtain ⟨ε₂, c, K, hK⟩ := HRS.MC.Sec7.S7FCH.S7FCHA_kernelData (regime S β₀ hE)
  exact (HRS.MC.Sec7.S7UCA.s7_UC_E4_limit_measurable_proof (regime S β₀ hE) (rLvl d) rfl Rw hRw gd.P₀ gd.η
    gd.limit gd.B gd.B_meas a ha ∅ (fun k => K k 0)).1

theorem u11_pair_moment (Rw : ℝ) (hRw : 0 < Rw) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a →
      ∫⁻ ω, ‖pairLim (rLvl d) Rw a gd.η gd.B ω‖ₑ ^ q ∂gd.P₀ ≤ ENNReal.ofReal C := by
  obtain ⟨fam⟩ := u11_exists_fam hE
  set R := regime S β₀ hE with hR
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨C1, hC1⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof R (rLvl d) rfl Rw hRw q hq
  obtain ⟨C2, hC2⟩ := HRS.MC.Sec7.S7FCF5N.fcf5_F6c_B_moments_proof R (rLvl d) rfl Rw hRw q hq
  refine ⟨C1 + C2, fun a ha => ?_⟩
  have hW := (HRS.MC.E213U5.chaos_conv_proof gd fam).1 Rw hRw 1 le_rfl
  have hpN : ∀ N : ℕ, 2 ≤ N → AEMeasurable (pairN (rLvl d) Rw a R.D.s R.ρ (fam.P N) (fam.X N)) (fam.P N) :=
    fun N hN => HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof R (rLvl d) rfl Rw hRw (fam.P N) (by omega)
      (fam.X₀ N) (fam.W N) (fam.X N) (fam.hreal N (by omega)) a ha
  have hpL := u11_pair_aemeasurable gd Rw hRw a ha
  haveI : IsProbabilityMeasure (law gd.P₀ (pairLim (rLvl d) Rw a gd.η gd.B)) :=
    (Measure.isProbabilityMeasure_map_iff hpL).2 inferInstance
  haveI : ∀ n : ℕ, IsProbabilityMeasure (law (fam.P (n + 2))
      (pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)))) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hpN (n + 2) (by omega))).2 inferInstance
  have hW' : Tendsto (fun n : ℕ => wassersteinE 1 (law (fam.P (n + 2))
      (pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2))))
      (law gd.P₀ (pairLim (rLvl d) Rw a gd.η gd.B))) atTop (𝓝 0) := by
    have h2 := (tendsto_add_atTop_iff_nat (f := fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
        wassersteinE 1 (law (fam.P N) (pairN (rLvl d) Rw a.1 R.D.s R.ρ (fam.P N) (fam.X N)))
          (law gd.P₀ (pairLim (rLvl d) Rw a.1 gd.η gd.B))) 2).2 hW
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
      (fun n => le_iSup (fun a : {a : ℝ // 0 ≤ a} => wassersteinE 1
        (law (fam.P (n + 2)) (pairN (rLvl d) Rw a.1 R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2))))
        (law gd.P₀ (pairLim (rLvl d) Rw a.1 gd.η gd.B))) ⟨a, ha⟩)
  have h7 := HRS.MC.Sec7.S7FCW1.s7_FC_D7b_fatou_proof
    (fun n => law (fam.P (n + 2)) (pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2))))
    (law gd.P₀ (pairLim (rLvl d) Rw a gd.η gd.B)) hW' q hq0
  rw [HRS.MC.Sec7.S7FCDA.S7FCDA_lintegral_law _ _ hpL] at h7
  refine h7.trans ?_
  have hpart : ∀ n : ℕ, ∫⁻ x, ‖x‖ₑ ^ q ∂(law (fam.P (n + 2))
      (pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)))) ≤ ENNReal.ofReal (C1 + C2) := by
    intro n
    have hN : 2 ≤ n + 2 := by omega
    rw [HRS.MC.Sec7.S7FCDA.S7FCDA_lintegral_law _ _ (hpN (n + 2) hN)]
    obtain ⟨⟨hI1, hb1⟩, -⟩ := hC1 a ha (n + 2) hN (fam.P (n + 2)) (fam.X₀ (n + 2)) (fam.W (n + 2))
      (fam.X (n + 2)) (fam.hreal (n + 2) (by omega))
    obtain ⟨hI2, hb2⟩ := hC2 a ha (n + 2) hN (fam.P (n + 2)) (fam.X₀ (n + 2)) (fam.W (n + 2))
      (fam.X (n + 2)) (fam.hreal (n + 2) (by omega))
    have l1 := HRS.MC.Sec7.S7FCDA.S7FCDA_lintegral_le (fam.P (n + 2))
      (zetaWin (rLvl d) Rw a (fam.P (n + 2)) (fam.X (n + 2))) q C1 hq0 hI1 hb1
    have l2 := HRS.MC.Sec7.S7FCDA.S7FCDA_lintegral_le (fam.P (n + 2))
      (fun ω => (pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).2) q C2 hq0 hI2 hb2
    have hC1' : 0 ≤ C1 := le_trans (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hb1
    have hC2' : 0 ≤ C2 := le_trans (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hb2
    have hm1 : AEMeasurable (fun ω => ‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).1‖ₑ ^ q)
        (fam.P (n + 2)) :=
      ((hpN (n + 2) hN).fst.enorm).pow_const q
    calc ∫⁻ ω, ‖pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω‖ₑ ^ q ∂(fam.P (n + 2))
        ≤ ∫⁻ ω, (‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).1‖ₑ ^ q +
            ‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).2‖ₑ ^ q) ∂(fam.P (n + 2)) := by
          refine lintegral_mono fun ω => ?_
          rw [u11_prod_enorm]
          rcases le_total ‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).1‖ₑ
              ‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).2‖ₑ with h | h
          · rw [max_eq_right h]; exact le_add_self
          · rw [max_eq_left h]; exact le_self_add
      _ = ∫⁻ ω, ‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).1‖ₑ ^ q ∂(fam.P (n + 2)) +
          ∫⁻ ω, ‖(pairN (rLvl d) Rw a R.D.s R.ρ (fam.P (n + 2)) (fam.X (n + 2)) ω).2‖ₑ ^ q ∂(fam.P (n + 2)) :=
          lintegral_add_left' hm1 _
      _ ≤ ENNReal.ofReal C1 + ENNReal.ofReal C2 := add_le_add l1 l2
      _ = ENNReal.ofReal (C1 + C2) := (ENNReal.ofReal_add hC1' hC2').symm
  calc liminf _ atTop ≤ liminf (fun _ : ℕ => ENNReal.ofReal (C1 + C2)) atTop :=
        liminf_le_liminf (Eventually.of_forall hpart)
    _ = _ := liminf_const _

end Moments


section Components

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u11_eta_moment (Rw : ℝ) (hRw : 0 < Rw) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      AEMeasurable (procWin (rLvl d) Rw a gd.η) gd.P₀ ∧
      Integrable (fun ω => ‖procWin (rLvl d) Rw a gd.η ω‖ ^ q) gd.P₀ ∧
      ∫ ω, ‖procWin (rLvl d) Rw a gd.η ω‖ ^ q ∂gd.P₀ ≤ C := by
  obtain ⟨C, hC⟩ := u11_pair_moment gd Rw hRw q hq
  refine ⟨max C 0, le_max_right _ _, fun a ha => ?_⟩
  have hpL := u11_pair_aemeasurable gd Rw hRw a ha
  have hm : AEMeasurable (procWin (rLvl d) Rw a gd.η) gd.P₀ := hpL.fst
  refine ⟨hm, u11_real_moment (f := procWin (rLvl d) Rw a gd.η) hm.norm (by linarith) (le_max_right _ _) ?_⟩
  refine le_trans (lintegral_mono fun ω => ?_) ((hC a ha).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  exact ENNReal.rpow_le_rpow (u11_enorm_fst_le (pairLim (rLvl d) Rw a gd.η gd.B ω)) (by linarith)

theorem u11_B_moment (Rw : ℝ) (hRw : 0 < Rw) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      AEMeasurable (fun ω => toL2 (rLvl d) Rw (fun t => gd.B (a + t) ω)) gd.P₀ ∧
      Integrable (fun ω => ‖toL2 (rLvl d) Rw (fun t => gd.B (a + t) ω)‖ ^ q) gd.P₀ ∧
      ∫ ω, ‖toL2 (rLvl d) Rw (fun t => gd.B (a + t) ω)‖ ^ q ∂gd.P₀ ≤ C := by
  obtain ⟨C, hC⟩ := u11_pair_moment gd Rw hRw q hq
  refine ⟨max C 0, le_max_right _ _, fun a ha => ?_⟩
  have hpL := u11_pair_aemeasurable gd Rw hRw a ha
  have hm : AEMeasurable (fun ω => toL2 (rLvl d) Rw (fun t => gd.B (a + t) ω)) gd.P₀ := hpL.snd
  refine ⟨hm, u11_real_moment (f := fun ω => toL2 (rLvl d) Rw (fun t => gd.B (a + t) ω)) hm.norm (by linarith)
    (le_max_right _ _) ?_⟩
  refine le_trans (lintegral_mono fun ω => ?_) ((hC a ha).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  exact ENNReal.rpow_le_rpow (u11_enorm_snd_le (pairLim (rLvl d) Rw a gd.η gd.B ω)) (by linarith)

theorem u11_norm_epath_le {m₁ : ℝ} (hmm : rLvl d ≤ m₁) (T : ℝ) (w : PathSpace d (rLvl d) T) :
    ‖HRS.MD.EQInterp.epath hmm T w‖ ≤ ‖w‖ := by
  refine HRS.MC.Sec7.S7FCH4.S7FCH4_norm_le_of _ (norm_nonneg _) fun s => ?_
  rw [HRS.MD.EQInterp.epath_at']
  exact (NegSobolev.norm_embed_le m₁ hmm _).trans (HRS.MC.Sec7.S7FCH4.S7FCH4_norm_at_le w s)

theorem u11_Z_moment (T : ℝ) (hT : 0 < T) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      AEStronglyMeasurable (gd.Zwin T a) gd.P₀ ∧
      Integrable (fun ω => ‖gd.Zwin T a ω‖ ^ q) gd.P₀ ∧
      ∫ ω, ‖gd.Zwin T a ω‖ ^ q ∂gd.P₀ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := u11_eta_moment gd T hT q hq
  refine ⟨C, hC0, fun a ha => ?_⟩
  obtain ⟨hm, hI, hb⟩ := hC a ha
  have hZ : AEStronglyMeasurable (gd.Zwin T a) gd.P₀ := by
    have : AEMeasurable (gd.Zwin T a) gd.P₀ :=
      (HRS.MD.EQInterp.epath (rLvl_le hE) T).continuous.aemeasurable.comp_aemeasurable hm
    exact this.aestronglyMeasurable
  refine ⟨hZ, ?_, ?_⟩
  · refine hI.mono' (hZ.norm.aemeasurable.pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (u11_norm_epath_le _ _ _) (by linarith)
  · refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)
      hI (Eventually.of_forall fun ω => ?_)) hb
    exact Real.rpow_le_rpow (norm_nonneg _) (u11_norm_epath_le _ _ _) (by linarith)

end Components

end HRS.MC.E213U11

end
