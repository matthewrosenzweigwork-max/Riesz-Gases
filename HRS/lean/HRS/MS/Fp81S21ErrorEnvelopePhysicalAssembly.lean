import HRS.MS.Fp81S21ErrorEnvelopePhysicalSelection
import HRS.MS.Fp81S21RecentRSPhysical14
import HRS.MS.Fp81S21MovingInterpolation
import HRS.MS.Fp81S21RemotePhysical

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
attribute [local instance] fp81s21_initialMeasure_isProbability
local instance (p : Parameters) : CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

theorem fp81s21_errorEnvelope_physical (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∃ Q : fp81s21_Physical35 p R,
      ∃ O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ,
      fp81s21_Compatκ Q O1 ∧
      ∃ future, fp81s21_moving_heat_full_clause p R future ∧
      ∃ α : ℕ → ℝ, fp81s21_Profile α ∧ fp81s21_Init R future α ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ fp81s21_Dec R O1 α C c) := by
  classical
  obtain ⟨Es, E, εAvg, hεAvg, hεAvgT, r34, hr34, h34half, h34all⟩ := fp81s21_recent_rs_physical p
  obtain ⟨rsel, hrsel, _, hsel⟩ := fp81s21_gaussian_physical_package_selected p Es E
  obtain ⟨rsrc, hrsrc, _, hsrc⟩ := fp81s21_gaussian_source_retained p
  obtain ⟨r20, hr20, _, h20all⟩ := fp81s21_moving_path_interpolation p
  obtain ⟨r28, hr28, _, h28all⟩ := fp81s21_initial_uniform_in_shift p
  obtain ⟨r38, hr38, _, h38⟩ := fp81s21_remote_physical p
  obtain ⟨r36, hr36, _, h36⟩ := fp81s21_gaussian_packet36 p
  obtain ⟨rM, hrM, _, hMom⟩ := fp81s21_gaussian35_O1_moment_bound p
  obtain ⟨rW, hrW, _, hWick⟩ := fp81s21_gaussian_wick_input p
  let δ0 := min r34 (min rsel (min rsrc (min r20 (min r28 (min r38 (min r36 (min rM rW)))))))
  refine ⟨δ0, by dsimp [δ0]; positivity, (min_le_left _ _).trans h34half, ?_⟩
  intro δ hδ hδle R
  have ⟨l34, lsel, lsrc, l20, l28, l38, l36, lM, lW⟩ :
      δ ≤ r34 ∧ δ ≤ rsel ∧ δ ≤ rsrc ∧ δ ≤ r20 ∧ δ ≤ r28 ∧ δ ≤ r38 ∧
        δ ≤ r36 ∧ δ ≤ rM ∧ δ ≤ rW := by simpa only [δ0, le_min_iff] using hδle
  obtain ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnT, hg, hgT, hb, hbT,
    S31, c33, hc33, K33, hK33, Kpred, hKpred, O, h33, _, hrecent⟩ := h34all δ hδ l34 R
  obtain ⟨src⟩ := hsrc δ hδ lsrc R
  let Q0 := fp81s21_gaussian35_selection_of_selected Es E src εAvg εB hεAvg hεAvgT hb hbT MUG hMUG canon S31.gaussian.quadratic
  obtain ⟨Q, hparent⟩ := hsel δ hδ lsel R Q0 rfl rfl
  obtain ⟨hEs, hE, hM, hAvg, hB, hcanon, hquad⟩ := fp81s21_recentRS13_compatible p R Es E src εAvg εB hεAvg hεAvgT hb hbT MUG hMUG canon S31.gaussian.quadratic Q hparent
  obtain ⟨future, hf, Cmix, cdec, K20, h20⟩ := h20all δ hδ l20 R
  obtain ⟨Kresponse, _, hresp, hbound⟩ := hMom δ hδ lM R
  obtain ⟨O1, hκ⟩ := fp81s21_errorEnvelope_select_O1 Q Kresponse hresp (hWick δ hδ lW R Q) (hbound Q)
  have hv : ValidFuture R future := ⟨hf.1, hf.2.1⟩
  obtain ⟨α, hα, hαT, hinit⟩ := h28all δ hδ l28 R future hv
  obtain ⟨C, c, hC, hc, hremote⟩ := h38 δ hδ l38 R Q
  have hsup : fp81s21_physical_supplied_data p R Q future C c (Window p) (projTensor (Window p) 2) := by
    intro L hL
    obtain ⟨eL, heL, heLT, _, hrecentGRS⟩ := hrecent Q hEs hE hM hAvg hB hcanon hquad future hf L hL
    refine ⟨eL, heL, heLT, ?_⟩
    intro N hN A a ha Φ hΦ
    obtain ⟨F⟩ := HRS.MS.R26T3.r26t3_filtered_particle A
    obtain ⟨D20, hcov, hPhi⟩ := h20 a ha N hN A F
    obtain ⟨WN, hI⟩ := hPhi Φ ⟨hΦ.1, hΦ.2.1⟩
    obtain ⟨Wg, hD36, hJ36⟩ := h36 δ hδ l36 R Q future hf a ha Φ hΦ
    have hcontract := fp81s21_errorEnvelope_packet36_contract Q future a ha Φ hΦ Wg hD36 hJ36
    refine ⟨_, _, _, _, WN, Wg, hI, hcontract, ?_, ?_⟩
    · exact hrecentGRS N hN A F a ha D20 Cmix cdec K20 hcov Φ hΦ WN Wg
    · exact hremote future hf N hN A F a ha D20 Cmix cdec K20 hcov Φ hΦ WN Q.src.G0 (Q.UG a ha) (Q.UB a ha) (Q.hUG a ha) (Q.hUB a ha) (fp81s21_remote_G_extend Q.src.G0 a ha Wg.Y) Wg.WG L hL
  refine ⟨Q, O1, hκ, future, hf, α, ⟨hα, hαT⟩, hinit, C, c, hC, hc, ?_⟩
  simpa only [fp81s21_Dec, fp81s21_Profile, and_assoc] using
    fp81s21_errorEnvelope_physical_supplied p R Q O1 future α C c (Window p) (projTensor (Window p) 2) hκ ⟨hα, hαT⟩ hinit hC.le hc hsup

#print axioms fp81s21_errorEnvelope_physical
end HRS.Fp81.S21
end
