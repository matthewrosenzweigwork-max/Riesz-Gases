import HRS.MS.R2GenInitAux34
import HRS.MS.R2WinErrStat
import HRS.MS.R2GenInitAux29

/-!
# S10.5 window comparison, packet E1: the stationary data `S105Stat` from S10.3

`s105_stat_of_thermal`: for the quadratic gradient dynamics and a thermal equilibrium `ρ`, `S105Stat d s a β T b ρ` holds for every window start
`b ≥ 0` (with `T > 0`): the orbit data of `s103_stationary`, the oscillator test bounds `s104_hphi`, the classical adjoint solutions
`s104_stat_orbit`, the `u`-measurability `s104_hobs_stat`, `OscAdjointInput` at horizon `b + T` (`s21_oscAdjointInput`) and the regularity of the slice.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr HRS.MS.S21 HRS.MS.GenPath HRS.MH.DualityRd

variable {d : ℕ}

theorem s105_oscAdj_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {τ₀ : ℝ} (hτ : 0 < τ₀) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    OscAdjointInput ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) τ₀ ∧
    Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x) := by
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, hthr0, hSetup⟩ := s21_setup_family hd hs0 hsd ha hβ hτ hρ
  obtain ⟨S, hρ', hinv', hκ', hCadj⟩ := hSetup C₀thr le_rfl
  have hcoeff : S.coeff 2 = (quadraticGradientDyn d s a β).coeff (fun _ => ρ) := by
    rw [s21_coeff_setup S hρ' hinv' 2, ← s21_dyn_eq]
  refine ⟨?_, ?_⟩
  · have := hCadj 2
    rw [hcoeff] at this
    exact this
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (s21Bounds d s a β τ₀ θ Λ K C₀thr).T := ⟨le_rfl, hτ.le⟩
    have := (S.mf 2).second_moment 0 h0
    rwa [hρ' 2 0] at this

theorem s105_stat_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {b : ℝ} (hb : 0 ≤ b) :
    S105Stat d s a β T b ρ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cs0, cdec, hcdec, hsum, hmain⟩ := HRS.MS.R2WinOrb.s103_stationary hd s hs0 hsd a β ha hβ T hT
  obtain ⟨Cphi, hCphi0, hphi'⟩ := s104_hphi hd1
  set Cs : ℝ := max Cs0 Cphi with hCs
  have hCs0 : 0 ≤ Cs := hCphi0.trans (le_max_right _ _)
  set k : ℕ := 4 * d + 42 with hk
  set C : WholeCoeff d := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hCdef
  have hτ : 0 < b + T := by linarith
  have horb : ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) (Cs * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
        (Cs * s104_b d α) cdec) := by
    intro α
    have hm' := hmain ρ hρ α
    dsimp only at hm'
    have hle : Cs0 * s104_b d α ≤ Cs * s104_b d α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s104_b_nonneg α)
    exact ⟨fun t ht => s104_R2OrbitGrad_mono _ (hm'.1 t ht).2.1 hle,
      fun t ht => s104_R2OrbitGrad_mono _ (hm'.1 t ht).2.2.2.1 hle⟩
  have hφ : ∀ α a', ContDiff ℝ k (fun x => gradComp a' (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a' (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) x‖ ≤
        Cs * s104_b d α := fun α a' =>
    ⟨(hphi' α a').1, fun j hj x => ((hphi' α a').2 j hj x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (s104_b_nonneg α))⟩
  have hex : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      (∃ f, IsClassicalAdjointW C t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f) ∧
      (∃ f, IsClassicalAdjointW C t (generatorW C t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) f) := by
    intro α t ht
    obtain ⟨G0, G1, G2, hG⟩ := s104_stat_orbit hd hs0 hsd ha hβ hρ α ht
    exact ⟨hG.ex0 t ⟨ht, le_rfl⟩, hG.ex1 t ⟨ht, le_rfl⟩⟩
  have hmeasU : ∀ r : ℝ, 0 ≤ r → ∀ (a' : Fin d) α x, AEStronglyMeasurable (fun u => if r < b + u then
      gradComp a' (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) x
      else 0) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun r hr a' α x => s104_hobs_stat hd hs0 hsd ha hβ hρ T b r hT.le hb hr a' α x
  have hbS : Summable (s104_b d) := hsum
  have hF := s105_win_feat hd1 C k ((wholeSpaceIndex d : ℕ) : ℝ) T b cdec Cs hb hT.le hcdec.le hCs0 hbS
    (fun α => (horb α).1) (fun α => (horb α).2) hφ (fun α t ht => (hex α t ht).1) (fun α t ht => (hex α t ht).2) hmeasU
  obtain ⟨hC, hρ2⟩ := s105_oscAdj_stat hd hs0 hsd ha hβ hτ hρ
  refine ⟨hC, ?_, hF, ?_, hρ.2.1, hρ2, s105_regSlice hd hs0 hsd ha hβ hτ hρ⟩
  · intro a' r hr x
    exact s105_winK C k ((wholeSpaceIndex d : ℕ) : ℝ) T cdec Cs hcdec.le hCs0 hbS (fun α => (horb α).1)
      (fun α => (horb α).2) hφ hb hr.1 a' (hmeasU r hr.1 a') x
  · intro α t ht
    exact HRS.MS.Fcau.propagatorW_isClassical (hex α t ht).1

end HRS.MS.R2GenInit
