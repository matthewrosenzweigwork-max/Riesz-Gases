import HRS.MC.E213U16k
import HRS.MC.E213U11g

/-!
# Packet e213u16, file l: integrability of the noise coefficient `ℬ` and its past-measurability
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section BInt

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The block sums dominating `∫_0^H ‖ℬ^v‖ dv`. -/
def Gblk (H : ℝ) (ω : gd.Ω₀) : ℝ :=
  ∑ k ∈ Finset.range ⌈H⌉₊, ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖

theorem u16_Gblk_integrable (H : ℝ) : Integrable (Gblk gd H) gd.P₀ := by
  refine integrable_finsetSum _ fun k _ => ?_
  obtain ⟨C, -, hC⟩ := HRS.MC.E213U11.u11_B_moment gd 1 one_pos 1 le_rfl
  have := (hC k (Nat.cast_nonneg k)).2.1
  simpa using this

theorem u16_B_int_bound (H : ℝ) (hH : 0 < H) :
    ∀ᵐ ω ∂gd.P₀, ∫ v in Set.Ioc 0 H, ‖gd.B v ω‖ ≤ Gblk gd H ω := by
  have hn : (0 : ℝ) < (⌈H⌉₊ : ℝ) := by
    have : 0 < ⌈H⌉₊ := Nat.ceil_pos.2 hH
    exact_mod_cast this
  have hHn : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil _
  filter_upwards [HRS.MC.E213U11.u11_B_integrable gd (⌈H⌉₊ : ℝ) hn, HRS.MC.E213U11.u11_B_blocks gd] with ω hint hblk
  have h1 := HRS.MC.E213U11.u11_weighted_block (fun v => ‖gd.B v ω‖) (fun v => norm_nonneg _) ⌈H⌉₊ hint 0 0 H le_rfl hHn
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h1
  refine h1.trans ?_
  unfold Gblk
  refine Finset.sum_le_sum fun k _ => ?_
  exact HRS.MC.E213U11.u11_block_integral_le (fun v => gd.B v ω) k (hblk k)

theorem u16_B_joint (H : ℝ) (hH : 0 < H) :
    Integrable (fun p : ℝ × gd.Ω₀ => ‖gd.B p.1 p.2‖) ((volume.restrict (Set.Icc 0 H)).prod gd.P₀) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × gd.Ω₀ => ‖gd.B p.1 p.2‖) ((volume.restrict (Set.Icc 0 H)).prod gd.P₀) :=
    (gd.B_meas.norm).aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨HRS.MC.E213U11.u11_B_integrable gd H hH, ?_⟩
  have h0 : StronglyMeasurable (fun p : ℝ × gd.Ω₀ => ‖gd.B p.1 p.2‖) := (gd.B_meas.norm).stronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun ω => ∫ v in Set.Icc 0 H, ‖‖gd.B v ω‖‖ ∂volume) gd.P₀ := by
    have := h0.integral_prod_left' (μ := volume.restrict (Set.Icc 0 H))
    simpa using this.aestronglyMeasurable
  refine (u16_Gblk_integrable gd H).mono' hmeas ?_
  filter_upwards [u16_B_int_bound gd H hH] with ω hω
  simp only [norm_norm]
  rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun v _ => norm_nonneg _),
    integral_Icc_eq_integral_Ioc]
  exact hω

end BInt


section BPast

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_fc_le {r : ℝ} (F : NegSobolev d r) (k : NonzeroLattice d) :
    |NegSobolev.fourierCoeff F k| ≤ Lattice.jp k.1 ^ r * ‖F‖ := by
  unfold NegSobolev.fourierCoeff NegSobolev.coord
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos _) _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos _) _).le
  have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k
  calc |(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k| = ‖(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖F‖ := this

theorem u16_fc_cont {r : ℝ} (k : NonzeroLattice d) : Continuous fun F : NegSobolev d r => NegSobolev.fourierCoeff F k :=
  continuous_const.mul (HRS.Uniform.Q54c.continuous_coord r k)

/-- `NegSobolev`-valued transfer using only the Fourier modes. -/
theorem u16_neg_meas_modes {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} (m : MeasurableSpace Ω) {r : ℝ}
    {F : Ω → NegSobolev d r}
    (h : ∀ k : NonzeroLattice d, ∃ g : Ω → ℝ, Measurable[m] g ∧ ∀ᵐ ω ∂μ, NegSobolev.eval (F ω) (Torus.realMode k) = g ω) :
    ∃ F' : Ω → NegSobolev d r, Measurable[m] F' ∧ F =ᵐ[μ] F' := by
  letI : MeasurableSpace Ω := m0
  refine u16_meas_of_coords (μ := μ) (J := NonzeroLattice d) m (fun k F => NegSobolev.coord F k)
    (fun k => HRS.Uniform.Q54c.continuous_coord r k) ?_ ?_
  · intro F G hFG
    have : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) = (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G) :=
      lp.ext (funext fun k => congrFun hFG k)
    exact this
  · intro k
    obtain ⟨g, hg, hae⟩ := h k
    refine ⟨fun ω => Lattice.jp k.1 ^ (-r) * g ω, hg.const_mul _, ?_⟩
    filter_upwards [hae] with ω hω
    rw [u16_coord_eq, hω]

/-- For a.e. `v ≤ τ`, the Wick field `ℬ^v` is a.s. equal to a `pastSig τ`-measurable `E_r`-valued map. -/
theorem u16_B_past {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    ∀ᵐ v ∂(volume.restrict (Set.Icc 0 τ)), ∃ B' : gd.Ω₀ → NegSobolev d (rLvl d),
      Measurable[pastSig gd τ] B' ∧ (fun ω => gd.B v ω) =ᵐ[gd.P₀] B' := by
  have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 H := Set.Icc_subset_Icc le_rfl hτ.2
  have hj := (u16_B_joint gd H hH)
  have hj' : Integrable (fun p : ℝ × gd.Ω₀ => ‖gd.B p.1 p.2‖) ((volume.restrict (Set.Icc 0 τ)).prod gd.P₀) :=
    hj.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hw : ∀ᵐ v ∂(volume.restrict (Set.Icc 0 τ)),
      IsWickQuadraticField S.s gd.P₀ (fun ω => gd.η v ω) (withDensityReal (S.ρ v)) (gd.B v) :=
    ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Ici_self) gd.B_wick
  filter_upwards [hj'.prod_right_ae, hw, ae_restrict_mem measurableSet_Icc] with v hvi hvw hv
  refine u16_neg_meas_modes (μ := gd.P₀) (pastSig gd τ) fun k => ?_
  have hQm : Measurable fun ω => NegSobolev.fourierCoeff (gd.B v ω) k :=
    (u16_fc_cont k).measurable.comp (gd.B_meas.comp (measurable_const.prodMk measurable_id))
  have hQi : Integrable (fun ω => NegSobolev.fourierCoeff (gd.B v ω) k) gd.P₀ := by
    refine (hvi.const_mul (Lattice.jp k.1 ^ (rLvl d))).mono' hQm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact u16_fc_le _ k
  have e : (fun ω => NegSobolev.eval (gd.B v ω) (Torus.realMode k)) =
      fun ω => NegSobolev.fourierCoeff (gd.B v ω) k :=
    funext fun ω => HRS.MD.EQGaussWindow.eqgw_eval_realMode _ _
  have hq := u16_wick_past gd hτ hv (hvw k) (by rw [e]; exact hQi) (by rw [e]; exact hQm.aestronglyMeasurable)
  obtain ⟨g, hg, hae⟩ := hq
  exact ⟨g, hg.measurable, hae⟩

end BPast

end HRS.MC.E213U16

end
