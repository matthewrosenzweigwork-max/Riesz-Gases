import HRS.MS.SA16Y3Hk5
import HRS.MS.SA16Y3En1

/-!
# S.A.16 (SA16Y3) Hk6: the P7 Hilbert-corner energy theorem (`d-1 < s < d`, `p = 2`, `M = -λ I + A`, `λ ≥ 0`, `A^T = -A`)

The nonlocal operator is `𝒢 = N = -λ T + T^A`, `T`, `T^A : W^{m+2,2} →L W^{m,2}` the extensions of `φ ↦ P_μ φ`, `φ ↦ P^A_μ φ`.
`sa16y3_hdissA`: `d(jetEnergy_m)_{ι²G}(-T^A G) ≤ p C AB Λ jetEnergy_m(ι²G)`.
`sa16y3_hilb_energy_gen`: the energy bound for `ν Δ + ι(b·∇) - N` (gen form) and `sa16y3_hilb_energy_strong` (Gronwall bound for a strong solution).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section Hk6
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_hdissA (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (hp2 : p = 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ}, 0 ≤ AB → (∀ a b, |A a b| ≤ AB) →
      A.transpose = -A → ∀ {μ : Euc d → ℝ}, ContDiff ℝ ∞ μ → ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (m + 2) Λ μ →
      ∀ (TA : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p),
        (∀ φ : ccSub d, (((TA (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16y3_PA s A μ φ.1)) →
        ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(TA G)) ≤
            p * C * (AB * Λ) * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  subst hp2
  obtain ⟨C, hC0, hC⟩ := sa16y3_hpair hd hs0 hsd hθ1 m (s := s)
  refine ⟨C, hC0, fun {A AB} hAB hAab hA {μ} hμ {Λ} hΛ hCb TA hT G => ?_⟩
  have hder : fderiv ℝ (jetEnergy d m 2) = sa16v2_Dj d m 2 :=
    funext fun G => (sa16v2_jetEnergy_hasFDerivAt d m 2 G).fderiv
  have hDc : Continuous (sa16v2_Dj d m 2) := sa16v2_Dj_continuous d m 2
  have hι2 := (sa16sz_iota2 d m 2).continuous
  refine (sa16r_Jcc_dense d (m + 1 + 1) 2).induction_on G (isClosed_le ?_ ?_) (fun φ => ?_)
  · rw [hder]
    exact (hDc.comp hι2).clm_apply TA.continuous.neg
  · exact continuous_const.mul ((sa16sz_jetEnergy_cont m).comp hι2)
  · rw [sa16sz_iota2_Jcc, map_neg, sa16y3_fderiv_pair m φ (TA (sa16r_Jcc d (m + 1 + 1) 2 φ)) (hT φ),
      sa16sz_energy_cc]
    have h1 := hC hAB hAab hA hμ φ.2 hΛ hCb
    have h2 := (abs_le.1 h1).1
    linarith

set_option maxHeartbeats 1000000 in
theorem sa16y3_hilb_energy_gen (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (hp2 : p = 2)
    (m : ℕ) (Λ : ℝ) (hΛ : 0 ≤ Λ) (AB : ℝ) (hAB : 0 ≤ AB) :
    ∃ K C CA : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ CA ∧ ∀ {lam : ℝ}, 0 ≤ lam → ∀ {A : Matrix (Fin d) (Fin d) ℝ},
      (∀ a b, |A a b| ≤ AB) → A.transpose = -A →
      ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → sa16z_Cb (m + 3) Λ μ →
      ∃ (T TA : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p), ‖T‖ ≤ K * Λ ∧ ‖TA‖ ≤ K * (AB * Λ) ∧
        (∀ φ : ccSub d, (((T (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16z_P s μ φ.1)) ∧
        (∀ φ : ccSub d, (((TA (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16y3_PA s A μ φ.1)) ∧
        (∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (-(-(lam • T G) + TA G)) ≤ (p * lam * C + p * CA * (AB * Λ)) * jetEnergy d m p (sa16sz_iota2 d m p G)) ∧
        ∀ {ν B : ℝ}, 0 ≤ ν → ∀ {bc : Fin d → Euc d → ℝ}, SA16BddCoef (m + 1) B bc →
          ∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
            (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) - (-(lam • T G) + TA G)) ≤
            (p * sa16sz_cTr d m p B + (p * lam * C + p * CA * (AB * Λ))) *
              jetEnergy d m p (sa16sz_iota2 d m p G) := by
  obtain ⟨K1, hK1, hK1'⟩ := sa16y3_extend (s := s) (p := p) hd hs0 hsd hθ1 m
  obtain ⟨K2, hK2, hK2'⟩ := sa16y3_extendA (s := s) (p := p) hd hs0 hsd hθ1 m
  obtain ⟨C, hC0, hC⟩ := sa16y3_diss (s := s) (p := p) hd hs0 hsd hθ1 m Λ hΛ
  obtain ⟨CA, hCA0, hCA⟩ := sa16y3_hdissA (s := s) (p := p) hd hs0 hsd hθ1 hp2 m
  refine ⟨max K1 K2, C, CA, le_max_of_le_left hK1, hC0, hCA0, fun {lam} hlam {A} hAab hA {μ} hμ hpos hCb => ?_⟩
  obtain ⟨T, hT, hTc⟩ := hK1' hμ.1 hΛ (sa16z_Cb_mono (by omega) hCb)
  obtain ⟨TA, hTA, hTAc⟩ := hK2' hAB hAab hA hμ.1 hΛ (sa16z_Cb_mono (by omega) hCb)
  have hTj := fun φ => (hTc φ).2
  have hN : ∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
      (-(-(lam • T G) + TA G)) ≤ (p * lam * C + p * CA * (AB * Λ)) * jetEnergy d m p (sa16sz_iota2 d m p G) :=
    fun G => by
      have e1 := hC hμ hpos hCb T hTj hlam G
      have e2 := hCA hAB hAab hA hμ.1 hΛ (sa16z_Cb_mono (by omega) hCb) TA hTAc G
      have : -(-(lam • T G) + TA G) = lam • T G + -(TA G) := by abel
      rw [this, map_add]
      nlinarith
  refine ⟨T, TA, hT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ),
    hTA.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hAB hΛ)), hTj, hTAc, hN,
    fun {ν B} hν {bc} hb G => ?_⟩
  exact sa16zz_gen_energy_diss m hν hb (fun G => -(lam • T G) + TA G) hN G

set_option maxHeartbeats 1000000 in
theorem sa16y3_hilb_energy_strong (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (hp2 : p = 2)
    (m : ℕ) (Λ : ℝ) (hΛ : 0 ≤ Λ) (AB : ℝ) (hAB : 0 ≤ AB) :
    ∃ C CA : ℝ, 0 ≤ C ∧ 0 ≤ CA ∧ ∀ {lam : ℝ}, 0 ≤ lam → ∀ {A : Matrix (Fin d) (Fin d) ℝ},
      (∀ a b, |A a b| ≤ AB) → A.transpose = -A →
      ∀ {ν Tt B : ℝ}, 0 ≤ ν → ∀ (bc : ℝ → Fin d → Euc d → ℝ),
      (∀ r ∈ Ioo (0 : ℝ) Tt, SA16BddCoef (m + 1) B (bc r)) →
      ∀ (μ : ℝ → Euc d → ℝ), (∀ r ∈ Ioo (0 : ℝ) Tt, HRS.S16Frac.S16FracCb (μ r) ∧ (∀ x, 0 ≤ μ r x) ∧
        sa16z_Cb (m + 3) Λ (μ r)) →
      ∀ (T TA : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p),
        (∀ r ∈ Ioo (0 : ℝ) Tt, ∀ φ : ccSub d, (((T r (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16z_P s (μ r) φ.1)) →
        (∀ r ∈ Ioo (0 : ℝ) Tt, ∀ φ : ccSub d, (((TA r (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16y3_PA s A (μ r) φ.1)) →
        ∀ {u : ℝ → WmpSpace d (m + 1 + 1) p}, ContinuousOn u (Icc 0 Tt) →
          (∀ τ ∈ Ioo (0 : ℝ) Tt, HasDerivAt (fun r => sa16sz_iota2 d m p (u r))
            (ν • sa16so_Lap d m p (u τ) + sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) -
              (-(lam • T τ (u τ)) + TA τ (u τ))) τ) →
          ∀ τ ∈ Icc (0 : ℝ) Tt, jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
            jetEnergy d m p (sa16sz_iota2 d m p (u 0)) *
              Real.exp ((p * sa16sz_cTr d m p B + (p * lam * C + p * CA * (AB * Λ))) * τ) := by
  obtain ⟨C, hC0, hC⟩ := sa16y3_diss (s := s) (p := p) hd hs0 hsd hθ1 m Λ hΛ
  obtain ⟨CA, hCA0, hCA⟩ := sa16y3_hdissA (s := s) (p := p) hd hs0 hsd hθ1 hp2 m
  refine ⟨C, CA, hC0, hCA0, fun {lam} hlam {A} hAab hA {ν Tt B} hν bc hbc μ hμ T TA hT hTA {u} hu hder => ?_⟩
  refine sa16zz_energy_strong (m := m) (ν := ν) (T := Tt) (B := B)
    (cNl := p * lam * C + p * CA * (AB * Λ)) hν bc hbc
    (fun r G => -(lam • T r G) + TA r G) (fun r hr G => ?_) hu hder
  have e1 := hC (hμ r hr).1 (hμ r hr).2.1 (hμ r hr).2.2 (T r) (hT r hr) hlam G
  have e2 := hCA hAB hAab hA (hμ r hr).1.1 hΛ (sa16z_Cb_mono (by omega) (hμ r hr).2.2) (TA r) (hTA r hr) G
  have : -(-(lam • T r G) + TA r G) = lam • T r G + -(TA r G) := by abel
  rw [this, map_add]
  nlinarith

end Hk6

end HRS.Whole.AppendixA.Phase2SA16R
