import HRS.MS.Fp81S21ShiftedMildAssembly3
import HRS.MS.S21E_Zeta

/-! Extend the simultaneous shifted mild identity from rational to all times. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MP.RdRem HRS.MS.CovMeas

/-- The simultaneous shifted mild identity holds at every terminal time in
one full-measure event. The source certificate is the all-mode output of the
compiled drift construction; its interval-integrability clause feeds the
rational identity, and its continuity clause supplies the extension. -/
theorem fp81s21_shifted_mild_coord_all_times
    (p : Parameters) {δ b H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hb : 0 ≤ b) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A (b + H))
    (G : A.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H)
    (hNoise : fp81s21_NoiseMatch p R A F hH b G)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hData : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (b + H) r c)
    (hcert : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d,
      (∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable
          (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) ∧
      ContinuousOn
        (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H))) :
    ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ t ∈ Icc b (b + H),
      OscDual.coord
          (fp81s21_particleZeta p R A t ω -
            fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)) α =
        fp81s21_shiftedModeInitial p R A α b t ω -
          (Real.sqrt (N : ℝ))⁻¹ *
            fp81s21_shiftedModeDrift p R A α b t ω := by
  have hsource : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ a t : ℝ,
      0 ≤ a → a ≤ t → t ≤ b + H →
      IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t := by
    filter_upwards [hcert] with ω hω
    intro α a t ha hat ht
    exact (hω α).1 a t ha hat ht
  have hrat := fp81s21_shifted_mild_coord_rational p R hδ hδh hb hH hN A F
    hphys G hNoise hsource
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hmindex : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by
      unfold wholeSpaceIndex
      omega)
  have hXmeas : ∀ t : ℝ≥0, Measurable (A.X t) :=
    (A.strong (b + H)).adapted
  have hXb : Measurable (A.X b.toNNReal) := hXmeas b.toNNReal
  have hinit : ∀ α : MultiIndex p.d, ∀ ω, ContinuousOn
      (fun t => fp81s21_shiftedModeInitial p R A α b t ω)
      (Icc b (b + H)) := by
    intro α ω
    have hμb : IsProbabilityMeasure (r26t3_mu R b) := by
      have href := r26t3_reference_data p δ hδ hδh R
      exact HRS.Whole.Q34.isProbabilityMeasure_nu (href.2.2.1 b hb).1
    exact fp81s21_shiftedModeInitial_continuous p R A hN α hb hH hData hXb hμb ω
  have hzeta := HRS.Whole.s21e_zeta_cont_time hd1 hNpos hmindex
    A.P A.X hXmeas (A.strong (b + H)).cont
  have htranslated : Dense (Set.range (fun q : ℚ => b + (q : ℝ))) := by
    have himageSet : (fun y : ℝ => b + y) '' Set.range ((↑) : ℚ → ℝ) =
        Set.range (fun q : ℚ => b + (q : ℝ)) := by
      ext z
      constructor
      · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
        exact ⟨q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨(q : ℝ), ⟨q, rfl⟩, rfl⟩
    intro x
    have hxcast : x - b ∈ closure (Set.range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast (x - b)
    have htranslateCont : Continuous (fun y : ℝ => b + y) :=
      continuous_const.add continuous_id
    have hximage := mem_closure_image (f := fun y : ℝ => b + y)
      htranslateCont.continuousAt hxcast
    have hcancel : b + (x - b) = x := by ring
    simpa only [himageSet, hcancel] using hximage
  filter_upwards [hrat, hzeta, hcert] with ω hratω hζ hcertω
  intro α
  let lhs : ℝ → ℝ := fun t => OscDual.coord
    (fp81s21_particleZeta p R A t ω -
      fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)) α
  let rhs : ℝ → ℝ := fun t =>
    fp81s21_shiftedModeInitial p R A α b t ω -
      (Real.sqrt (N : ℝ))⁻¹ *
        fp81s21_shiftedModeDrift p R A α b t ω
  have hNoiseCont : Continuous fun t : ℝ =>
      fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b) := by
    let cl : ℝ → Icc (0 : ℝ) H := fun t =>
      ⟨mrrClamp H (t - b), mrrClamp_mem hH.le (t - b)⟩
    have hcl : Continuous cl :=
      ((continuous_mrrClamp H).comp (continuous_id.sub continuous_const)).subtype_mk
        (fun t => mrrClamp_mem hH.le (t - b))
    have hEval : Continuous (fun u : Icc (0 : ℝ) H => OscPath.at' (G ω) u) :=
      (G ω).continuous
    change Continuous fun t : ℝ => OscPath.at' (G ω) (cl t)
    exact hEval.comp hcl
  have hζ' : Continuous (fun t : ℝ => fp81s21_particleZeta p R A t ω) := by
    simpa [fp81s21_particleZeta] using hζ
  have hcoord : Continuous (fun z : OscDual p.d (wholeSpaceIndex p.d : ℝ) =>
      OscDual.coord z α) := (HRS.MS.R2Interp.s102_coordCLM α).continuous
  have hlhs : ContinuousOn lhs (Icc b (b + H)) := by
    apply hcoord.comp_continuousOn
    exact (hζ'.sub hNoiseCont).continuousOn
  have hinitω : ContinuousOn
      (fun t => fp81s21_shiftedModeInitial p R A α b t ω)
      (Icc b (b + H)) := hinit α ω
  have hdriftω := (hcertω α).2
  have hrhs : ContinuousOn rhs (Icc b (b + H)) := by
    dsimp [rhs]
    exact hinitω.sub (continuousOn_const.mul hdriftω)
  let S : Set ℝ := Ioo b (b + H) ∩ Set.range (fun q : ℚ => b + (q : ℝ))
  have hEqS : Set.EqOn lhs rhs S := by
    rintro x ⟨hxI, q, rfl⟩
    have hq : (q : ℝ) ∈ Icc (0 : ℝ) H := by
      change b < b + (q : ℝ) ∧ b + (q : ℝ) < b + H at hxI
      constructor
      · linarith [hxI.1]
      · linarith [hxI.2]
    simpa [lhs, rhs, fp81s21_shiftedNoiseValue,
      HRS.MP.RdRem.mrrClamp_of_mem hq] using hratω α q hq
  have hSsub : S ⊆ Icc b (b + H) := by
    rintro x ⟨hx, -⟩
    exact ⟨hx.1.le, hx.2.le⟩
  have hInterior : Ioo b (b + H) ⊆ closure S := by
    simpa [S] using
      htranslated.open_subset_closure_inter (isOpen_Ioo (a := b) (b := b + H))
  have hIooClosure : closure (Ioo b (b + H)) = Icc b (b + H) :=
    closure_Ioo (a := b) (b := b + H) (by linarith)
  have hWindowClosure : Icc b (b + H) ⊆ closure S := by
    rw [← hIooClosure]
    simpa [closure_closure] using closure_mono hInterior
  have hEq := Set.EqOn.of_subset_closure hEqS hlhs hrhs hSsub hWindowClosure
  intro t ht
  have hclamp : mrrClamp H (t - b) = t - b := by
    apply mrrClamp_of_mem
    constructor <;> linarith [ht.1, ht.2]
  simpa [lhs, rhs, fp81s21_shiftedNoiseValue, hclamp] using hEq ht

#print axioms HRS.Fp81.S21.fp81s21_shifted_mild_coord_all_times

end HRS.Fp81.S21

end
