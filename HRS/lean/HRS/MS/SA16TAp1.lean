import HRS.MS.SA16TCo6
import HRS.MS.SA16TCo5
import HRS.MS.SA16TMo3

/-!
# S.A.16 (SA16T) Ap1: the smoothed drift family `bc_n^σ` of the approximating problems

For `AdjointRdData`, `t ∈ (0,T]` and `σ ∈ [0,t]`, `b^σ = M∇g*μ^{t-σ} - ∇V` is `C^{m+2}` with uniform bounds
(`sa16p_drift_bounds`), `bc_n^σ = χ_{n+1} (ρ_n ⋆ b^σ)` are `SA16BddCoef (m+1) Bn` with uniform derivative bound `B`, `bc_n^σ` is
continuous in `σ` in the `SA16BddCoef` sense, and `|bc_n^σ(x)| ≤ C0 + L (|x|+1)`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P

section Ap1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the reversed-time drift -/
def sa16t_b (D : WholeDyn d) (μ : ℝ → Euc d → ℝ) (t σ : ℝ) : Euc d → Euc d := meanFieldDriftW D (μ (t - σ))

/-- the smoothed, cut-off reversed-time drift -/
def sa16t_bcs (d n : ℕ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ) (t σ : ℝ) : Fin d → Euc d → ℝ :=
  sa16t_bcv d n (sa16t_b D μ t σ)

/-- bounds of the drift at the origin and of its derivatives -/
def sa16t_C0 (d m : ℕ) (s MB Λ G₀ : ℝ) : ℝ :=
  ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s *
    ((d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)))) + G₀

def sa16t_L (d m : ℕ) (s MB Λ ΛV : ℝ) : ℝ :=
  ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s *
    ((d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)))) + ΛV

lemma sa16t_drift_facts (hd : 1 ≤ d) {s MB Λ ΛV G₀ νbar T : ℝ} {m : ℕ} {D : WholeDyn d} {μ : ℝ → Euc d → ℝ}
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) :
    ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (sa16t_b D μ t σ) ∧ ‖sa16t_b D μ t σ 0‖ ≤ sa16t_C0 d m s MB Λ G₀ ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (sa16t_b D μ t σ) x‖ ≤ sa16t_L d m s MB Λ ΛV := by
  obtain ⟨hDs, hs0, hsd⟩ := hD.hs
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  exact sa16p_drift_bounds hd hs0 hsd m hDs hD.hM hD.hV (sa16so_regDensity_of_MF hD.hμ.regular hr)

lemma sa16t_C0_nonneg (hd : 1 ≤ d) {s MB Λ ΛV G₀ νbar T : ℝ} {m : ℕ} {D : WholeDyn d} {μ : ℝ → Euc d → ℝ}
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    0 ≤ sa16t_C0 d m s MB Λ G₀ ∧ 0 ≤ sa16t_L d m s MB Λ ΛV := by
  have h := sa16t_drift_facts hd hD ht (σ := 0) ⟨le_rfl, ht.1.le⟩
  exact ⟨(norm_nonneg _).trans h.2.1, (norm_nonneg _).trans (h.2.2 1 le_rfl (by omega) 0)⟩

theorem sa16t_coefs (hd : 1 ≤ d) (m : ℕ) :
    ∃ Bχ : ℝ, 0 ≤ Bχ ∧ ∀ {s MB Λ ΛV G₀ νbar T : ℝ} {D : WholeDyn d} {μ : ℝ → Euc d → ℝ},
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ {t : ℝ}, t ∈ Ioc (0 : ℝ) T → ∀ n : ℕ,
      (∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (max (sa16t_C0 d m s MB Λ G₀ + sa16t_L d m s MB Λ ΛV *
          (2 * sa16t_R n + 1)) (sa16t_Bu Bχ d (m + 1) (sa16t_C0 d m s MB Λ G₀) (sa16t_L d m s MB Λ ΛV)))
          (sa16t_bcs d n D μ t σ)) ∧
      (∀ σ ∈ Icc (0 : ℝ) t, ∀ l : Fin d, ∀ i, 1 ≤ i → i ≤ m + 1 → ∀ x,
        ‖iteratedFDeriv ℝ i (sa16t_bcs d n D μ t σ l) x‖ ≤
          sa16t_Bu Bχ d (m + 1) (sa16t_C0 d m s MB Λ G₀) (sa16t_L d m s MB Λ ΛV)) ∧
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ l x, |sa16t_bcs d n D μ t σ l x| ≤
        sa16t_C0 d m s MB Λ G₀ + sa16t_L d m s MB Λ ΛV * (‖x‖ + 1) := by
  obtain ⟨Bχ, hB0, H⟩ := sa16t_coef_vec d (m + 1) (by omega)
  refine ⟨Bχ, hB0, fun {s MB Λ ΛV G₀ νbar T D μ} hD {t} ht n => ?_⟩
  obtain ⟨hC0, hL0⟩ := sa16t_C0_nonneg hd hD ht
  have hmain : ∀ σ ∈ Icc (0 : ℝ) t, _ := fun σ hσ => by
    have hf := sa16t_drift_facts hd hD ht hσ
    exact H (sa16t_b D μ t σ) _ _ hC0 hL0 (hf.1.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))) hf.2.1
      (fun j hj1 hjk => hf.2.2 j hj1 (by omega)) n
  exact ⟨fun σ hσ => (hmain σ hσ).1, fun σ hσ l i hi1 hi2 x => (hmain σ hσ).2.1 l i hi1 hi2 x,
    fun σ hσ l x => (hmain σ hσ).2.2 l x⟩

end Ap1

end HRS.Whole.AppendixA.Phase2SA16R
