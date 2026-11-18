import HRS.MS.R26T8AP15p

/-!
# S8.2 T8A P15q: the centring terms `∫ Lop Q(.,y) dμ` and `∫ Lop Q(x,.) dμ`
For `Q` conormal `(k+2) 1 M (σ-2) A` (`σ < d`): both `L`-rows are `μ`-integrable and the centring functions
`y ↦ ∫ Lop Q(.,y) dμ`, `x ↦ ∫ Lop Q(x,.) dμ` give `Conormal k 1 (M+1) (σ-2) (C A)` pair functions (row lemma).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p15_ell_one {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (C : WholeCoeff d)
    (α : Fin d → Euc d → ℝ) (hb : ∀ i x, C.drift 0 x i = α i x) (k : ℕ) (a beta M sigma B : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) (hB : 0 ≤ B)
    (hα : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ (Q : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 2) 1 M (sigma - 2) A Q →
      (∀ y, Integrable (fun x => r26t8a_Lop C (fun w => Q w y) x) (HRS.Whole.withDensityReal rho)) ∧
      Conormal k 1 (M + 1) (sigma - 2) (Cl * A)
        (fun _ y => ∫ x', r26t8a_Lop C (fun w => Q w y) x' ∂(HRS.Whole.withDensityReal rho)) := by
  obtain ⟨c, hc, hK⟩ := r26t8a_Kx_conormal hchi C α hb k 1 M (sigma - 2) B hB hα hαb
  obtain ⟨Cr, hCr, hr⟩ := r26t8a_p15_rowy hchi hd k 1 a beta (M + 1) sigma ha hbeta (by linarith) hsd hrho
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  refine ⟨2 ^ k * (Cr * c), by positivity, fun Q A hA hQ => ?_⟩
  have hK' : Conormal k 1 (M + 1) sigma (c * A) (fun x y => r26t8a_Lop C (fun w => Q w y) x) :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (le_of_eq (by ring)) (hK Q A hA hQ)
  obtain ⟨hint, hsm, hj⟩ := hr _ _ (by positivity) hK'
  refine ⟨fun y => (r26t8a_f25_wd_integrable hprob _).2 (hint y), ?_⟩
  have h := r26t8a_conormal_of_snd (k := k) (b := 1) (σ := sigma - 2) (by linarith : (0 : ℝ) ≤ M + 1)
    (by positivity : 0 ≤ Cr * (c * A)) hsm (fun j hjk y => by
      have := hj j hjk y
      exact this)
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) le_rfl h

theorem r26t8a_p15_ell {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (C : WholeCoeff d)
    (α : Fin d → Euc d → ℝ) (hb : ∀ i x, C.drift 0 x i = α i x) (k : ℕ) (a beta M sigma B : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) (hB : 0 ≤ B)
    (hα : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ (Q : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 2) 1 M (sigma - 2) A Q →
      (∀ y, Integrable (fun x => r26t8a_Lop C (fun w => Q w y) x) (HRS.Whole.withDensityReal rho)) ∧
      (∀ x, Integrable (fun y => r26t8a_Lop C (Q x) y) (HRS.Whole.withDensityReal rho)) ∧
      Conormal k 1 (M + 1) (sigma - 2) (Cl * A)
        (fun _ y => ∫ x', r26t8a_Lop C (fun w => Q w y) x' ∂(HRS.Whole.withDensityReal rho)) ∧
      Conormal k 1 (M + 1) (sigma - 2) (Cl * A)
        (fun x _ => ∫ y', r26t8a_Lop C (Q x) y' ∂(HRS.Whole.withDensityReal rho)) := by
  obtain ⟨Cl, hCl, h⟩ := r26t8a_p15_ell_one hchi hd C α hb k a beta M sigma B ha hbeta hM hsd hB hα hαb hrho
  refine ⟨Cl, hCl, fun Q A hA hQ => ?_⟩
  obtain ⟨h1, h2⟩ := h Q A hA hQ
  obtain ⟨h3, h4⟩ := h (fun x y => Q y x) A hA (r26t8a_f24_conormal_swap hchi hQ)
  exact ⟨h1, h3, h2, r26t8a_f24_conormal_swap hchi h4⟩

end HRS.MS.R26T8A
