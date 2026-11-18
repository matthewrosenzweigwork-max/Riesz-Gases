import HRS.MS.SA16Y5Ex1f
import HRS.MS.SA16Y5Ex2
import HRS.MS.SA16Y3Hk6
import HRS.MS.SA16Y3En1

/-!
# S.A.16 (SA16Y5) Ex2f: `adjoint_lp` for `LpCase.iso` and `LpCase.hilbert` in the fractional range `d-1 < s < d`

`sa16y5f_Hex_iso`, `sa16y5f_Hex_hilb`: node operators `N : W^{m+2} → W^m` with `SA16FOp`, norm and dissipativity, from `sa16y3_extend(A)`, `sa16y3_diss`,
`sa16y3_hilb_energy_gen`.  `sa16y5_adjoint_lp_iso_hi`, `sa16y5_adjoint_lp_hilbert_hi`: the statements of `adjoint_lp` for `κc := LpCase.iso / LpCase.hilbert`
under the extra hypothesis `d - 1 < s` (uniqueness from `bounded_lp_uniqueness_bridge`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16V2

section Ex2f
variable {d : ℕ}

lemma sa16y5f_wrep_of_jets {m : ℕ} {p : ℝ} [Fact (2 ≤ p)] (G : WmpSpace d m p) {f : Euc d → ℝ}
    (h : (((G : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m f) :
    wrep d m p G =ᵐ[volume] f := by
  filter_upwards [h] with x hx
  show (((G : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = f x
  rw [hx]
  exact sa16j_pd_zero _ _ _

theorem sa16y5f_Hex_iso (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    {p : ℝ} [Fact (2 ≤ p)] (m : ℕ) (MB : ℝ) :
    ∀ Wd : ℝ, 0 ≤ Wd → ∃ Cg cN : ℝ, 0 ≤ Cg ∧ 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ},
      (∃ lam : ℝ, 0 ≤ lam ∧ M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ))) →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb (m + 3) Wd μ → ∃ N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p,
        SA16FOp d m p s M μ N ∧ ‖N‖ ≤ Cg ∧ ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N G)) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hθ1 : 1 < s + 2 - d := by linarith
  intro Wd hWd
  obtain ⟨K, hK0, hK⟩ := sa16y3_extend (s := s) (p := p) hd hs0 hsd hθ1 m
  obtain ⟨C, hC0, hC⟩ := sa16y3_diss (s := s) (p := p) hd hs0 hsd hθ1 m Wd hWd
  refine ⟨max MB 0 * (K * Wd), p * max MB 0 * C, by positivity, by positivity, ?_⟩
  intro M hMC hM μ hμ hpos hCb
  obtain ⟨lam, hlam, hMl⟩ := hMC
  have hlamMB : lam ≤ max MB 0 := by
    have h := hM ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [hMl] at h
    have h' : lam ≤ MB := by simpa [abs_of_nonneg hlam] using h
    exact h'.trans (le_max_left _ _)
  obtain ⟨T, hT, hTc⟩ := hK hμ.1 hWd (sa16z_Cb_mono (by omega) hCb)
  have hTj := fun φ => (hTc φ).2
  refine ⟨(-lam) • T, ?_, ?_, fun G => ?_⟩
  · intro φ
    filter_upwards [sa16r_wrep_smul d m p (-lam) (T (sa16r_Jcc d (m + 1 + 1) p φ)),
      (hTc φ).1] with x e1 e2
    rw [ContinuousLinearMap.smul_apply, e1, e2]
    have := sa16y3_eucNonlocal_split (s := s) lam 0 μ φ.1 x
    rw [add_zero] at this
    rw [hMl, this]
    have hPA : sa16y3_PA s (0 : Matrix (Fin d) (Fin d) ℝ) μ φ.1 x = 0 := by simp [sa16y3_PA]
    rw [hPA]
    ring
  · calc ‖(-lam) • T‖ ≤ ‖-lam‖ * ‖T‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = lam * ‖T‖ := by rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hlam]
      _ ≤ max MB 0 * (K * Wd) :=
          mul_le_mul hlamMB hT (ContinuousLinearMap.opNorm_nonneg _) (le_max_right _ _)
  · have e : -(((-lam) • T) G) = lam • T G := by
      rw [ContinuousLinearMap.smul_apply, neg_smul, neg_neg]
    rw [e]
    refine (hC hμ hpos hCb T hTj hlam G).trans ?_
    have hE := sa16v2c_E_nonneg d m p (sa16sz_iota2 d m p G)
    refine mul_le_mul_of_nonneg_right ?_ hE
    calc p * lam * C ≤ p * max MB 0 * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamMB hp0.le) hC0
      _ = _ := by ring

theorem sa16y5f_Hex_hilb (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    {p : ℝ} [Fact (2 ≤ p)] (hp2 : p = 2) (m : ℕ) (MB : ℝ) :
    ∀ Wd : ℝ, 0 ≤ Wd → ∃ Cg cN : ℝ, 0 ≤ Cg ∧ 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ},
      (∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
        M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb (m + 3) Wd μ → ∃ N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p,
        SA16FOp d m p s M μ N ∧ ‖N‖ ≤ Cg ∧ ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N G)) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2' : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hθ1 : 1 < s + 2 - d := by linarith
  intro Wd hWd
  obtain ⟨K, C, CA, hK0, hC0, hCA0, H⟩ :=
    sa16y3_hilb_energy_gen (s := s) (p := p) hd hs0 hsd hθ1 hp2 m Wd hWd (max MB 0) (le_max_right _ _)
  refine ⟨max MB 0 * (K * Wd) + K * (max MB 0 * Wd), p * max MB 0 * C + p * CA * (max MB 0 * Wd),
    by positivity, by positivity, ?_⟩
  intro M hMC hM μ hμ hpos hCb
  obtain ⟨lam, hlam, A, hskew, hMl⟩ := hMC
  have hAii : ∀ i, A i i = 0 := fun i => by
    have := congrFun (congrFun hskew i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hlamMB : lam ≤ max MB 0 := by
    have h := hM ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [hMl] at h
    have h' : lam ≤ MB := by simpa [hAii, abs_of_nonneg hlam] using h
    exact h'.trans (le_max_left _ _)
  have hA : ∀ i j, |A i j| ≤ max MB 0 := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hAii]; simp
    · have h1 := hM i j
      rw [hMl] at h1
      have : |A i j| ≤ MB := by simpa [Matrix.one_apply, h] using h1
      exact this.trans (le_max_left _ _)
  obtain ⟨T, TA, hT, hTA, hTj, hTAj, hN, -⟩ := H hlam hA hskew hμ hpos hCb
  refine ⟨(-lam) • T + TA, ?_, ?_, fun G => ?_⟩
  · intro φ
    filter_upwards [sa16r_wrep_add d m p (((-lam) • T) (sa16r_Jcc d (m + 1 + 1) p φ))
        (TA (sa16r_Jcc d (m + 1 + 1) p φ)),
      sa16r_wrep_smul d m p (-lam) (T (sa16r_Jcc d (m + 1 + 1) p φ)),
      sa16y5f_wrep_of_jets _ (hTj φ), sa16y5f_wrep_of_jets _ (hTAj φ)] with x e1 e2 e3 e4
    rw [ContinuousLinearMap.add_apply, e1]
    have e2' : wrep d m p (((-lam) • T) (sa16r_Jcc d (m + 1 + 1) p φ)) x =
        -lam * wrep d m p (T (sa16r_Jcc d (m + 1 + 1) p φ)) x := by
      rw [ContinuousLinearMap.smul_apply]; exact e2
    rw [e2', e3, e4, hMl, sa16y3_eucNonlocal_split (s := s) lam A μ φ.1 x]
    ring
  · calc ‖(-lam) • T + TA‖ ≤ ‖(-lam) • T‖ + ‖TA‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ max MB 0 * (K * Wd) + K * (max MB 0 * Wd) := by
          refine add_le_add ?_ hTA
          calc ‖(-lam) • T‖ ≤ ‖-lam‖ * ‖T‖ := ContinuousLinearMap.opNorm_smul_le _ _
            _ = lam * ‖T‖ := by rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hlam]
            _ ≤ max MB 0 * (K * Wd) :=
                mul_le_mul hlamMB hT (ContinuousLinearMap.opNorm_nonneg _) (le_max_right _ _)
  · have e : (((-lam) • T + TA) G) = -(lam • T G) + TA G := by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, neg_smul]
    rw [e]
    refine (hN G).trans ?_
    have hE := sa16v2c_E_nonneg d m p (sa16sz_iota2 d m p G)
    refine mul_le_mul_of_nonneg_right ?_ hE
    have h1 : p * lam * C ≤ p * max MB 0 * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamMB hp0.le) hC0
    linarith

end Ex2f

end HRS.Whole.AppendixA.Phase2SA16R
