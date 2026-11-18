import HRS.MS.FixEqP3Aux26

/-!
# S5.7 `fixed_equation` (worker S57P), part 39: the Hölder bound of `κ^N_{t₂} - κ_{t₂} - (κ^N_{t₁} - κ_{t₁})`
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ}
  {Ca CaN Cd CdN Cp1 Cp2 Dt : ℝ}

/-- generic Hölder bound of the kernel element for one family with an arbitrary weight -/
theorem s57p_el_holder_fam {C : WholeCoeff d} {w : ℝ × Euc d → ℝ} {Wm : ℝ} (K' : S57pKd T w Wm)
    (hbd : S57pOrbBd C T n m J Ca Cd) (α : MultiIndex d) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2T : t₂ ≤ T) (hn : 1 ≤ n) :
    ‖s57pel T w (s57pA C t₂ (oscTestFun m α)) t₂ - s57pel T w (s57pA C t₁ (oscTestFun m α)) t₁‖ ^ 2 ≤
      Wm * ((Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 * (t₂ - t₁) ^ 2 * T +
        (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 * (t₂ - t₁)) := by
  have ht1 : t₁ ∈ Set.Icc (0 : ℝ) T := ⟨h0, h12.trans h2T⟩
  have ht2 : t₂ ∈ Set.Icc (0 : ℝ) T := ⟨h0.trans h12, h2T⟩
  obtain ⟨h1a, h1b⟩ := (hbd α).1 t₁ ht1
  obtain ⟨h2a, h2b⟩ := (hbd α).1 t₂ ht2
  have hB1 : ∀ p, ‖s57pA C t₁ (oscTestFun m α) p‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    s57p_A_bound ht1.1 (fun r hr x => (h1b r hr).2 1 (by omega) x)
  have hB2 : ∀ p, ‖s57pA C t₂ (oscTestFun m α) p‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    s57p_A_bound ht2.1 (fun r hr x => (h2b r hr).2 1 (by omega) x)
  exact s57p_el_holder K' (s57p_A_cont ht2.1 h2a).aestronglyMeasurable
    (s57p_A_cont ht1.1 h1a).aestronglyMeasurable (s := t₁) (t := t₂)
    (Ba := Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) (Bd := Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) h12
    (fun p _ => hB2 p) (fun p _ => hB1 p)
    (fun p hp => s57p_A_holder h0 h12 (fun r hr => (h1b r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)))
      (fun r hr => (h2b r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)))
      (fun r hr x => (hbd α).2 t₁ t₂ h0 h12 h2T r hr 1 hn x) p hp)

theorem S57pPairBd.kdiff_decomp (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (hT : 0 ≤ T) {q qN τ : ℝ} (hq : 0 ≤ q) (hqN : 0 ≤ qN) (hτ0 : 0 ≤ τ)
    (hτ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ)
    (α : MultiIndex d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t (oscTestFun m α) - s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α) =
      s57pel T (fun p => s57pw T qN ρN p - s57pw T q ρN p) (s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α)) t +
      s57pel T (fun p => s57pw T q ρN p - s57pw T q ρ p) (s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α)) t +
      s57pel T (s57pw T q ρ) (fun p => s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α) p -
        s57pA (fixedEqCoeff s M Q ν c ρ) t (oscTestFun m α) p) t := by
  have K1 := s57p_w1_data P.FxN.fe hT hq hqN P.FxN.prob
  have K2 := s57p_w2_data P.Fx.fe P.FxN.fe hT hq P.Fx.prob P.FxN.prob hτ0 hτ
  have K3 := s57p_wdata P.Fx.fe hT hq P.Fx.prob
  have KN' := s57p_wdata P.FxN.fe hT hqN P.FxN.prob
  obtain ⟨hAd1, hAd2⟩ := P.Adiff α ht
  have hAN := s57p_A_cont ht.1 ((P.hbdN α).1 t ht).1
  have hA := s57p_A_cont ht.1 ((P.hbd α).1 t ht).1
  have bN : ∀ p, ‖s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α) p‖ ≤ CaN * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    s57p_A_bound ht.1 (fun r hr x => ((((P.hbdN α).1 t ht).2 r hr).2 1 (by have := P.Fx.hn4; omega) x))
  have bC : ∀ p, ‖s57pA (fixedEqCoeff s M Q ν c ρ) t (oscTestFun m α) p‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    s57p_A_bound ht.1 (fun r hr x => ((((P.hbd α).1 t ht).2 r hr).2 1 (by have := P.Fx.hn4; omega) x))
  unfold s57pκ
  exact s57p_el_decomp (wm := s57pw T q ρN)
    (s57p_kf_memLp KN' hAN.aestronglyMeasurable (Ba := _) (fun p _ => bN p))
    (s57p_kf_memLp K3 hA.aestronglyMeasurable (Ba := _) (fun p _ => bC p))
    (s57p_kf_memLp K1 hAN.aestronglyMeasurable (Ba := _) (fun p _ => bN p))
    (s57p_kf_memLp K2 hAN.aestronglyMeasurable (Ba := _) (fun p _ => bN p))
    (s57p_kf_memLp K3 (hAN.sub hA).aestronglyMeasurable (Ba := _) (fun p _ => hAd2 p))

end HRS.MS.FixEq
