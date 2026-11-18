import HRS.MS.SA16SEn13
import HRS.MS.SA16Y3EnD12

/-!
# S.A.16 (SA16Y3) EnD13: Gronwall energy bound for the Duhamel solution, derivative-only constants

Copy of `sa16sz_energy_solution` (SA16SEn13).  The exponent `p * cTr(B) + p * CJ * CG` involves only the
derivative bound `B` (`SA16DerCoef`).  The hypothesis `hbo` (`SA16BddCoef` with an arbitrary constant `B'`)
and `hKb` (a qualitative bound of `K`) are used only to identify the operators and to run the mild theory.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section EnD13
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the constant `C_J` of the energy chain: depends only on `d, m, p` (not on the data) -/
def sa16y3_CJ (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] : ℝ := Classical.choose (sa16y3_gen_energyD (d := d) (p := p) m)

lemma sa16y3_CJ_pos (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] : 0 < sa16y3_CJ d m p :=
  (Classical.choose_spec (sa16y3_gen_energyD (d := d) (p := p) m)).1

lemma sa16y3_gen_energyD_CJ (m : ℕ) {ν B B' CG : ℝ} (hν : 0 ≤ ν) {bc : Fin d → Euc d → ℝ}
    (hb : SA16DerCoef (m + 1) B bc) (hbo : SA16BddCoef (m + 1) B' bc)
    (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p) (hT0 : ‖T0‖ ≤ CG) (G : WmpSpace d (m + 1 + 1) p) :
    fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
      (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) -
        T0 (sa16sz_iota2 d m p G)) ≤
      (p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) * jetEnergy d m p (sa16sz_iota2 d m p G) :=
  (Classical.choose_spec (sa16y3_gen_energyD (d := d) (p := p) m)).2 hν hb hbo T0 hT0 G

set_option maxHeartbeats 1600000 in
/-- **Energy bound for the Duhamel solution** (packet P7, sub case). -/
theorem sa16y3_energy_solutionD {m : ℕ} {ν T B B' Bk CG : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16DerCoef (m + 1) B (bc r))
    (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ r ∈ Icc (0 : ℝ) T, (sa16r_iota d m p).comp (T1 r) = (T0 r).comp (sa16r_iota d m p))
    (hT0 : ∀ r ∈ Icc (0 : ℝ) T, ‖T0 r‖ ≤ CG)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - (T1 r).comp (sa16r_iota d (m + 1) p))
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk) (hBk : 0 ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
        jetEnergy d m p (sa16sz_iota2 d m p φ) *
          Real.exp ((p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) * τ) := by
  set c : ℝ := p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG with hc
  set e : ℝ → ℝ := fun τ => jetEnergy d m p (sa16sz_iota2 d m p (u τ)) with he
  have hcont : ContinuousOn e (Icc 0 T) :=
    (sa16sz_jetEnergy_cont m).comp_continuousOn ((sa16sz_iota2 d m p).continuous.comp_continuousOn hu)
  have hderiv : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧ e' ≤ c * e τ := by
    intro τ hτ
    have hτI : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
    have hdu := sa16sx_hasDerivAt hν hT K hKb hBk hKc φ hu hsol hτ
    have hE := (sa16v2_jetEnergy_hasFDerivAt d m p (sa16sz_iota2 d m p (u τ))).comp_hasDerivAt τ hdu
    refine ⟨sa16v2_Dj d m p (sa16r_iota d m p (sa16r_iota d (m + 1) p (u τ))) (sa16sx_f m ν K u τ), hE, ?_⟩
    have hf : sa16sx_f m ν K u τ = ν • sa16so_Lap d m p (u τ) +
        sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) - T0 τ (sa16sz_iota2 d m p (u τ)) := by
      unfold sa16sx_f
      rw [hK τ]
      have h1 := congrArg (fun L => L (sa16r_iota d (m + 1) p (u τ))) (hcomp τ hτI)
      simp only [ContinuousLinearMap.comp_apply] at h1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub, h1]
      unfold sa16sz_iota2
      simp only [ContinuousLinearMap.comp_apply]
      abel
    have hder : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p (u τ)) =
        sa16v2_Dj d m p (sa16sz_iota2 d m p (u τ)) :=
      (sa16v2_jetEnergy_hasFDerivAt d m p _).fderiv
    have := sa16y3_gen_energyD_CJ m hν.le (hbc τ hτI) (hbo τ hτI) (T0 τ) (hT0 τ hτI) (u τ)
    rw [hder, ← hf] at this
    exact this
  have hmain := sa16sz_gronwall hcont hderiv
  have h0 : e 0 = jetEnergy d m p (sa16sz_iota2 d m p φ) := by
    have := sa16sx_strong hν hT K hKb hBk hKc φ hu hsol 0 ⟨le_rfl, hT.le⟩
    simp only [he, intervalIntegral.integral_same, add_zero] at this ⊢
    unfold sa16sz_iota2
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
  intro τ hτ
  have := hmain τ hτ
  rw [h0] at this
  exact this

end EnD13

end HRS.Whole.AppendixA.Phase2SA16R
