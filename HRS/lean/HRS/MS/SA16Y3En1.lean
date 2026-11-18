import HRS.MS.SA16Y3Diss1
import HRS.MS.SA16ZEn1

/-!
# S.A.16 (SA16Y3) En1: the P7 isotropic energy theorem, unconditional (`d-1 < s < d`, `M = -λ I`, `λ ≥ 0`, `p ≥ 2`)

The nonlocal operator is `𝒢 = N = -λ T`, `T : W^{m+2,p} →L W^{m,p}` the extension of `φ ↦ P_μ φ` (`sa16y3_extend`).
`sa16y3_iso_energy_gen`: for `μ ≥ 0` in `C_b^∞` with `‖D^kμ‖ ≤ Λ` (`k ≤ m+3`) there is such a `T` (`‖T‖ ≤ KΛ`), and for all
`ν ≥ 0`, `b` with `SA16BddCoef (m+1) B b`, every `G ∈ W^{m+2,p}`:
`d(jetEnergy_m)_{ι²G}(νΔG + ι(b·∇G) - N G) ≤ (p cTr + p λ C) jetEnergy_m(ι²G)`, `C = C(d,s,p,Λ,m)`.
`sa16y3_iso_energy_strong`: the Gronwall energy bound for a strong solution with time-dependent `μ_τ`, `T_τ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section En1
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1000000 in
theorem sa16y3_iso_energy_gen (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb (m + 3) Λ μ →
      ∃ T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ K * Λ ∧
        (∀ φ : ccSub d, (((T (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16z_P s μ φ.1)) ∧
        (∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (-(-(lam • T G))) ≤ p * lam * C * jetEnergy d m p (sa16sz_iota2 d m p G)) ∧
        ∀ {ν B : ℝ}, 0 ≤ ν → ∀ {bc : Fin d → Euc d → ℝ}, SA16BddCoef (m + 1) B bc →
          ∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
            (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) - (-(lam • T G))) ≤
            (p * sa16sz_cTr d m p B + p * lam * C) * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  obtain ⟨K, hK0, hK⟩ := sa16y3_extend (s := s) (p := p) hd hs0 hsd hθ1 m
  obtain ⟨C, hC0, hC⟩ := sa16y3_diss (s := s) (p := p) hd hs0 hsd hθ1 m Λ hΛ
  refine ⟨K, C, hK0, hC0, fun {μ} hμ hpos hCb => ?_⟩
  obtain ⟨T, hT, hTc⟩ := hK hμ.1 hΛ (sa16z_Cb_mono (by omega) hCb)
  have hTj := fun φ => (hTc φ).2
  have hN : ∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
      (-(-(lam • T G))) ≤ p * lam * C * jetEnergy d m p (sa16sz_iota2 d m p G) := fun G => by
    rw [neg_neg]; exact hC hμ hpos hCb T hTj hlam G
  refine ⟨T, hT, hTj, hN, fun {ν B} hν {bc} hb G => ?_⟩
  exact sa16zz_gen_energy_diss m hν hb (fun G => -(lam • T G)) hN G

set_option maxHeartbeats 1000000 in
theorem sa16y3_iso_energy_strong (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ν Tt B : ℝ}, 0 ≤ ν → ∀ (bc : ℝ → Fin d → Euc d → ℝ),
      (∀ r ∈ Ioo (0 : ℝ) Tt, SA16BddCoef (m + 1) B (bc r)) →
      ∀ (μ : ℝ → Euc d → ℝ), (∀ r ∈ Ioo (0 : ℝ) Tt, HRS.S16Frac.S16FracCb (μ r) ∧ (∀ x, 0 ≤ μ r x) ∧
        sa16z_Cb (m + 3) Λ (μ r)) →
      ∀ (T : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p),
        (∀ r ∈ Ioo (0 : ℝ) Tt, ∀ φ : ccSub d, (((T r (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16z_P s (μ r) φ.1)) →
        ∀ {u : ℝ → WmpSpace d (m + 1 + 1) p}, ContinuousOn u (Icc 0 Tt) →
          (∀ τ ∈ Ioo (0 : ℝ) Tt, HasDerivAt (fun r => sa16sz_iota2 d m p (u r))
            (ν • sa16so_Lap d m p (u τ) + sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) -
              (-(lam • T τ (u τ)))) τ) →
          ∀ τ ∈ Icc (0 : ℝ) Tt, jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
            jetEnergy d m p (sa16sz_iota2 d m p (u 0)) *
              Real.exp ((p * sa16sz_cTr d m p B + p * lam * C) * τ) := by
  obtain ⟨C, hC0, hC⟩ := sa16y3_diss (s := s) (p := p) hd hs0 hsd hθ1 m Λ hΛ
  refine ⟨C, hC0, fun {ν Tt B} hν bc hbc μ hμ T hT {u} hu hder => ?_⟩
  refine sa16zz_energy_strong (m := m) (ν := ν) (T := Tt) (B := B) (cNl := p * lam * C) hν bc hbc
    (fun r G => -(lam • T r G)) (fun r hr G => ?_) hu hder
  rw [neg_neg]
  exact hC (hμ r hr).1 (hμ r hr).2.1 (hμ r hr).2.2 (T r) (hT r hr) hlam G

end En1

end HRS.Whole.AppendixA.Phase2SA16R
