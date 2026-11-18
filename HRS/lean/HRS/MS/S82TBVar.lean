import HRS.MS.S82TBRow
import HRS.MS.S82TJVar

/-!
# S8.2 (S82T): variance of `N^{-5/2} sum_{i != j} K(X_i, X_j)` for a repeated-pair kernel
Pair template under the unpinned reference law (uncentered rows), then domination transfer to `canonicalP`:
`Var_{P_N} <= C A^2 / N`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82Q

lemma s82t_cN5_sq {N : ℕ} (hN : 0 < N) :
    (((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / ((N : ℕ) : ℝ) ^ 5 := by
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  have : (-(5 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((5 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg hNr.le, Real.rpow_natCast, one_div]

theorem s82t_B_variance {d : ℕ} (hd : 2 ≤ d) {a beta M C0 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      ∀ A : ℝ, 0 ≤ A → ∀ K : Euc d → Euc d → ℝ,
      Measurable (Function.uncurry K) → (∀ x y, K x y = K y x) →
      (∀ x y, x ≠ y → |K x y| ≤ A * Phase2S82.pairWeight M x y * pole x y ^ 2) →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum K X) 2
          (canonicalP d N a beta) ∧
        evariance (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum K X)
          (canonicalP d N a beta) ≤ ENNReal.ofReal (CB * A ^ 2 / N) := by
  obtain ⟨DB, hDB, hrowB⟩ := s82t_B_row hd (a := a) (C0 := C0) hM hbeta q hq G c hG hc hρ hρG
  have hMom0 : 0 ≤ HRS.MS.S82N.s82n_Mom d (4 * M) G c :=
    HRS.MS.S82N.s82n_Mom_nonneg (by omega) _ _ _ (by linarith) hG.le hc
  set Mom := HRS.MS.S82N.s82n_Mom d (4 * M) G c with hMom
  refine ⟨|C0| * (16 * C0 ^ 2 * DB * Mom), by positivity, ?_⟩
  intro h hW A hA K hKm hKs hKb N hN
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hC0 := hW.positive
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  set N := m + 2 with hNdef
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  set Ψ : Euc d → ℝ := fun x => DB * A ^ 2 * jbracket x ^ (4 * M) * ((N : ℕ) : ℝ) ^ 3 with hΨ
  have hrow : ∀ᵐ x ∂mu, ∫⁻ X', ENNReal.ofReal ((∑ j, K x (X' j)) ^ 2)
      ∂referenceLaw q h mu beta N (m + 1) (Fin.cons x pins0 : Fin (0 + 1) → Euc d) ≤
      ENNReal.ofReal (Ψ x) := ae_of_all _ fun x => hrowB h hW A hA K hKm hKb m x
  set J : ℝ := DB * A ^ 2 * ((N : ℕ) : ℝ) ^ 3 * Mom with hJ
  have hc0 : 0 ≤ DB * A ^ 2 * ((N : ℕ) : ℝ) ^ 3 := by positivity
  have hJle : ∫⁻ x, ENNReal.ofReal (Ψ x) ∂s82q_nu q mu beta N pins0 ≤ ENNReal.ofReal J := by
    calc ∫⁻ x, ENNReal.ofReal (Ψ x) ∂s82q_nu q mu beta N pins0
        ≤ ∫⁻ x, ENNReal.ofReal (Ψ x) ∂mu :=
          lintegral_mono' (s82q_nu_le q hW.short.nonneg mu beta hbeta N pins0) le_rfl
      _ ≤ ENNReal.ofReal (DB * A ^ 2 * ((N : ℕ) : ℝ) ^ 3) *
            ∫⁻ x, ENNReal.ofReal (jbracket x ^ (4 * M)) ∂mu := by
          refine s82q_lint_scale _ _ _ _ hc0 (ae_of_all _ fun x => le_of_eq ?_)
          simp only [hΨ]; ring
      _ ≤ ENNReal.ofReal (DB * A ^ 2 * ((N : ℕ) : ℝ) ^ 3) * ENNReal.ofReal Mom :=
          mul_le_mul_of_nonneg_left (s82p2_jb_moment hd (4 * M) (by linarith) G c hG hc _ hρ hρG) bot_le
      _ = ENNReal.ofReal J := (ENNReal.ofReal_mul hc0).symm
  obtain ⟨-, hFL, hvar⟩ := s82q_pair_template hW hbeta (N := N) hN (p := 0) (m := m + 1)
    (by omega) (by omega) (by omega) pins0 K hKs hKm (((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) Ψ J hrow hJle
  have hFm : Measurable (fun X : EucConfig d N =>
      ((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum K X) :=
    measurable_const.mul (s82t_pairSum_measurable hKm)
  have hV : evariance (fun X : EucConfig d N => ((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum K X)
      (unpinnedReference q h mu beta N) ≤
      ENNReal.ofReal (16 * C0 ^ 2 * DB * Mom * A ^ 2 / ((N : ℕ) : ℝ)) := by
    refine hvar.trans (le_of_eq ?_)
    congr 1
    rw [s82t_cN5_sq (by omega), hJ]
    have : ((m + 1 + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) := by rw [hNdef]
    rw [this]
    field_simp
  obtain ⟨hFc, hVc⟩ := s82q_transfer hW hN _ hFm hFL _ hV
  refine ⟨hFc, hVc.trans (le_of_eq ?_)⟩
  rw [← ENNReal.ofReal_mul hC0.le, abs_of_pos hC0]
  congr 1
  ring

end HRS.MS.S82T
