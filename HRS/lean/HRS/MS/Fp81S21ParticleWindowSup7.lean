import HRS.MS.Fp81S21ParticleWindowSup6
import HRS.MS.Fp81S21WindowSupMeas6

/-! The physical shifted-mild residual inherits the modewise sixth-moment
bounds and the simultaneous all-time coordinate identity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MS.R2WinErr
open HRS.MP.RdRem

/-- Physical residual window bound from the staged 10d moments, 10f identity,
and explicit moving-data certificate. -/
theorem fp81s21_particle_residual_window_sup_moment6
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    {H : ℝ} (hH : 0 < H) (b : ℝ) (hb : 0 ≤ b)
    (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A (b + H))
    (G : A.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H)
    (hGmeas : AEMeasurable G A.P)
    (hNoise : fp81s21_NoiseMatch p R A F hH b G)
    {r : ℕ} {c0 : MultiIndex p.d → ℝ}
    (hData : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (b + H) r c0)
    (CI CD : ℝ) (hCI : 0 ≤ CI) (hCD : 0 ≤ CD)
    (hI : ∀ α : MultiIndex p.d,
      fp81s21_Moment6 A.P
        (fun ω => ⨆ t : Icc b (b + H),
          |fp81s21_shiftedModeInitial p R A α b t ω|)
        ((CI * (1 + H) * s104_b p.d α) ^ 6))
    (hD : ∀ α : MultiIndex p.d,
      fp81s21_Moment6 A.P
        (fun ω => ⨆ t : Icc b (b + H),
          |fp81s21_shiftedModeDrift p R A α b t ω|)
        ((CD * (H + H ^ 2) * s104_b p.d α) ^ 6))
    (hcert : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d,
      (∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable
          (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) ∧
      ContinuousOn
        (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H)))
    (hwsq : Summable fun α : MultiIndex p.d => (s104_b p.d α) ^ 2) :
    fp81s21_Moment6 A.P
      (fun ω => ⨆ t : Icc b (b + H),
        ‖fp81s21_particleZeta p R A t ω -
          fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)‖)
      (((CI * (1 + H) + (Real.sqrt (N : ℝ))⁻¹ * CD * (H + H ^ 2)) *
        Real.sqrt (∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2)) ^ 6) := by
  classical
  letI : Nonempty (Icc b (b + H)) := ⟨⟨b, ⟨le_rfl, by linarith⟩⟩⟩
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hmindex : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by
      unfold wholeSpaceIndex
      omega)
  have hXmeas : ∀ t : ℝ≥0, Measurable (A.X t) :=
    (A.strong (b + H)).adapted
  have hZetaMeas (t : ℝ) : AEMeasurable
      (fun ω => fp81s21_particleZeta p R A t ω) A.P := by
    dsimp [fp81s21_particleZeta]
    exact (s102_zetaB_meas hmindex hNpos A.P A.X hXmeas t).aemeasurable
  have hZetaCont : ∀ᵐ ω ∂A.P,
      Continuous (fun t : ℝ => fp81s21_particleZeta p R A t ω) := by
    have h := HRS.Whole.s21e_zeta_cont_time hd1 hNpos hmindex
      A.P A.X hXmeas (A.strong (b + H)).cont
    filter_upwards [h] with ω hω
    simpa [fp81s21_particleZeta] using hω
  have hNoiseCont (ω : A.Ω) : Continuous (fun t : ℝ =>
      fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)) := by
    let cl : ℝ → Icc (0 : ℝ) H := fun t =>
      ⟨mrrClamp H (t - b), mrrClamp_mem hH.le (t - b)⟩
    have hcl : Continuous cl :=
      ((continuous_mrrClamp H).comp (continuous_id.sub continuous_const)).subtype_mk
        (fun t => mrrClamp_mem hH.le (t - b))
    have hEval : Continuous (fun u : Icc (0 : ℝ) H => OscPath.at' (G ω) u) :=
      (G ω).continuous
    change Continuous fun t : ℝ => OscPath.at' (G ω) (cl t)
    exact hEval.comp hcl
  let L : ℝ → A.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ) := fun t ω =>
    fp81s21_particleZeta p R A t ω -
      fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)
  have hLmeas : ∀ t ∈ Icc b (b + H), AEMeasurable (L t) A.P := by
    intro t ht
    dsimp [L]
    exact (hZetaMeas t).sub (by
      let τ : Icc (0 : ℝ) H :=
        ⟨mrrClamp H (t - b), mrrClamp_mem hH.le (t - b)⟩
      change AEMeasurable (fun ω => OscPath.at' (G ω) τ) A.P
      exact (ContinuousMap.evalCLM ℝ τ).continuous.measurable.comp_aemeasurable hGmeas)
  have hLcont : ∀ᵐ ω ∂A.P, ContinuousOn (fun t => L t ω) (Icc b (b + H)) := by
    filter_upwards [hZetaCont] with ω hω
    exact (hω.sub (hNoiseCont ω)).continuousOn
  have hcertMode : ∀ α : MultiIndex p.d, ∀ᵐ ω ∂A.P,
      (∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable
          (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) ∧
      ContinuousOn (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H)) := by
    exact (ae_all_iff).1 hcert
  have hcoord := fp81s21_shifted_mild_coord_all_times_of_per_mode_certificate
    p R hδ hδh hb hH hN A F hphys G hNoise hData hcertMode
  have hcoordL : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ t ∈ Icc b (b + H),
      OscDual.coord (L t ω) α =
        fp81s21_shiftedModeInitial p R A α b t ω -
          (Real.sqrt (N : ℝ))⁻¹ * fp81s21_shiftedModeDrift p R A α b t ω := by
    simpa [L] using hcoord
  have hmodeCont : ∀ α : MultiIndex p.d, ∀ᵐ ω ∂A.P,
      ContinuousOn (fun t => fp81s21_shiftedModeInitial p R A α b t ω)
        (Icc b (b + H)) ∧
      ContinuousOn (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H)) := by
    intro α
    have hbT : b ∈ Icc (0 : ℝ) (b + H) := by constructor <;> linarith
    have hXb : Measurable (A.X b.toNNReal) := hXmeas b.toNNReal
    obtain ⟨hIcont, _⟩ := fp81s21_initial_coordinate_regular
      A.P A.X hData hbT hXb hNpos α
    filter_upwards [hcertMode α] with ω hω
    exact ⟨hIcont ω, hω.2⟩
  let BadSet : Set A.Ω := {ω | ¬ ContinuousOn (fun t => L t ω) (Icc b (b + H))}
  have hBadNull : A.P BadSet = 0 := by exact (ae_iff.mp hLcont)
  obtain ⟨Bad, hBadSub, hBadMeas, hBadNull'⟩ :=
    exists_measurable_superset_of_null hBadNull
  have hNotBad : ∀ᵐ ω ∂A.P, ω ∉ Bad := by
    rw [ae_iff]
    simpa using hBadNull'
  have hGood (ω : A.Ω) (hω : ω ∉ Bad) :
      ContinuousOn (fun t => L t ω) (Icc b (b + H)) := by
    by_contra hn
    exact hω (hBadSub hn)
  let L' : ℝ → A.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
    fun t ω => if ω ∈ Bad then 0 else L t ω
  have hL'eq (t : ℝ) : (fun ω => L' t ω) =ᵐ[A.P] L t := by
    filter_upwards [hNotBad] with ω hω
    simp [L', hω]
  have hL'meas : ∀ t ∈ Icc b (b + H), AEMeasurable (L' t) A.P := by
    intro t ht
    exact (hLmeas t ht).congr (hL'eq t).symm
  have hL'cont : ∀ ω, ContinuousOn (fun t => L' t ω) (Icc b (b + H)) := by
    intro ω
    by_cases hω : ω ∈ Bad
    · simp [L', hω]
      exact continuousOn_const
    · simpa [L', hω] using hGood ω hω
  have hcoord' : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ t ∈ Icc b (b + H),
      OscDual.coord (L' t ω) α =
        fp81s21_shiftedModeInitial p R A α b t ω -
          (Real.sqrt (N : ℝ))⁻¹ * fp81s21_shiftedModeDrift p R A α b t ω := by
    filter_upwards [hcoordL, hNotBad] with ω hω hgood α t ht
    simpa [L', hgood] using hω α t ht
  have hres := fp81s21_residual_path_sup_moment6_of_shifted_mild
    A.P (by omega : 0 < p.d) (wholeSpaceIndex p.d : ℝ) b H hH N hN L'
    (fun α t ω => fp81s21_shiftedModeInitial p R A α b t ω)
    (fun α t ω => fp81s21_shiftedModeDrift p R A α b t ω)
    (s104_b p.d) CI CD
    hCI hCD s104_b_nonneg hwsq hI hD hmodeCont hcoord' hL'meas hL'cont
  let U : A.Ω → ℝ := fun ω => ⨆ t : Icc b (b + H), ‖L t ω‖
  let U' : A.Ω → ℝ := fun ω => ⨆ t : Icc b (b + H), ‖L' t ω‖
  have hUeq : U =ᵐ[A.P] U' := by
    filter_upwards [hNotBad] with ω hω
    apply iSup_congr
    intro t
    congr 1
    simp [L', hω]
  have hUpow : (fun ω => ‖U' ω‖ ^ (6 : ℕ)) =ᵐ[A.P]
      (fun ω => ‖U ω‖ ^ (6 : ℕ)) := by
    filter_upwards [hUeq] with ω hω
    rw [hω.symm]
  refine ⟨?_, hres.2.1.congr hUpow, ?_⟩
  · simpa [U, U'] using hres.1.congr hUeq.symm
  · calc
      (∫ ω, ‖U ω‖ ^ 6 ∂A.P) = ∫ ω, ‖U' ω‖ ^ 6 ∂A.P := integral_congr_ae hUpow.symm
      _ ≤ _ := hres.2.2

#print axioms HRS.Fp81.S21.fp81s21_particle_residual_window_sup_moment6
end HRS.Fp81.S21
end
