import HRS.MS.Fp81S21ShiftedMildAssembly2
import HRS.MS.Fp81S21WindowSup11
import HRS.MS.Fp81S21WindowSup13
import HRS.MS.Fp81S21WindowSup9

/-! Continuity of the propagated initial coordinate from the centered FTC. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The propagated centered initial mode is continuous in terminal time. The
proof uses the compiled centered FTC and integrability of its derivative
coordinate on the full shifted window. -/
theorem fp81s21_shiftedModeInitial_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (hN : 2 ≤ N) (α : MultiIndex p.d) {b H : ℝ}
    (hb : 0 ≤ b) (hH : 0 < H)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hData : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (b + H) r c)
    (hX : Measurable (A.X b.toNNReal))
    (hμ : IsProbabilityMeasure (r26t3_mu R b)) :
    ∀ ω, ContinuousOn
      (fun t => fp81s21_shiftedModeInitial p R A α b t ω)
      (Icc b (b + H)) := by
  letI : IsProbabilityMeasure (r26t3_mu R b) := hμ
  have hNpos : 0 < N := by omega
  have hbT : b ∈ Icc (0 : ℝ) (b + H) := by
    constructor <;> linarith
  let q : ℝ → Euc p.d → ℝ := fun s x =>
    s101Th (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (b + H) b s α x
  have hqjoint : Measurable (Function.uncurry q) := by
    exact fp81s21_s101Th_joint_measurable hData hbT α
  let g : ℝ → A.Ω → ℝ := fun s ω =>
    s102_zf A.P A.X ω b (q s)
  have hgjoint : Measurable (Function.uncurry g) := by
    dsimp [g]
    exact fp81s21_s102_zf_family_measurable A.P A.X b hX hNpos q hqjoint
  have hqmeas (s : ℝ) : Measurable (q s) :=
    hqjoint.comp (measurable_const.prodMk measurable_id)
  have hqbound (s : ℝ) (x : Euc p.d) :
      |q s x| ≤ c α :=
    s101_th_bound hData hbT s α x
  have hgbound (s : ℝ) (ω : A.Ω) :
      |g s ω| ≤ 4 * Real.sqrt N * c α :=
    fp81s21_window_s102_zf_abs_bound A.P A.X b hX hNpos
      (r26t3_mu R b) (hqmeas s) (hData.nonneg α) (hqbound s) ω
  have hgint (ω : A.Ω) :
      IntervalIntegrable (fun s => g s ω) volume b (b + H) := by
    have he : Measurable (fun s : ℝ => (s, ω)) :=
      measurable_id.prodMk measurable_const
    have hsec : Measurable (fun s : ℝ => g s ω) := by
      change Measurable ((Function.uncurry g) ∘ fun s : ℝ => (s, ω))
      exact hgjoint.comp he
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := 4 * Real.sqrt N * c α)
      measure_Ioc_lt_top.ne hsec.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact hgbound s ω
  let f0 : Euc p.d → ℝ :=
    propagatorW (r26t3_coeff R) b b
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
  let f0c : A.Ω → ℝ := fun ω =>
    s102_zf A.P A.X ω b f0
  intro ω
  have hFTC (t : ℝ) (ht : t ∈ Icc b (b + H)) :
      s102_zf A.P A.X ω b
          (propagatorW (r26t3_coeff R) b t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) =
        f0c ω + ∫ s in b..t, g s ω := by
    have h := fp81s21_window_s102_zf_ftc A.P A.X hData hbT ht
      hX hNpos α ω
    simpa [f0c, f0, g, q] using h
  have hbH : b ≤ b + H := le_add_of_nonneg_right hH.le
  have hgiIcc : IntegrableOn (fun s => g s ω) (Icc b (b + H)) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hbH).mp (hgint ω)
  have hgi : IntegrableOn (fun s => g s ω) (uIcc b (b + H)) volume := by
    simpa [uIcc_of_le hbH] using hgiIcc
  have hprimU : ContinuousOn
      (fun t => f0c ω + ∫ s in b..t, g s ω)
      (uIcc b (b + H)) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval hgi)
  have hprim : ContinuousOn
      (fun t => f0c ω + ∫ s in b..t, g s ω)
      (Icc b (b + H)) := by
    simpa [uIcc_of_le hbH] using hprimU
  have hcont : ContinuousOn
      (fun t => s102_zf A.P A.X ω b
        (propagatorW (r26t3_coeff R) b t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))
      (Icc b (b + H)) :=
    hprim.congr fun t ht => hFTC t ht
  simpa [fp81s21_shiftedModeInitial] using hcont

#print axioms HRS.Fp81.S21.fp81s21_shiftedModeInitial_continuous

end HRS.Fp81.S21

end
