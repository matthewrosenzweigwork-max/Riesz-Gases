import HRS.MS.S82TJRow

/-!
# S8.2 (S82T): variance of `N^{-3/2} sum_{i != j} K(X_i, X_j)` for a canonical `J`-type kernel
Pair template under the unpinned reference law, then domination transfer to `canonicalP`:
`Var_{P_N} <= C A^2 log(eN) / N`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82Q

lemma s82t_pairSum_measurable {d N : ℕ} {K : Euc d → Euc d → ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable (fun X : EucConfig d N => Phase2S82.pairSum K X) := by
  have : (fun X : EucConfig d N => Phase2S82.pairSum K X) = fun X => ∑ i, s82q_prow K i X := rfl
  rw [this]
  exact Finset.measurable_sum _ fun i _ => s82q_prow_measurable hK i

lemma s82t_cN_sq {N : ℕ} (hN : 0 < N) :
    (((N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / ((N : ℕ) : ℝ) ^ 3 := by
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  have : (-(3 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg hNr.le, Real.rpow_natCast, one_div]

theorem s82t_J_variance {d : ℕ} (hd : 2 ≤ d) {a beta M C0 C1 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 → ∀ A : ℝ, 0 ≤ A → ∀ K : Euc d → Euc d → ℝ,
      Measurable (Function.uncurry K) → (∀ x y, K x y = K y x) →
      (∀ x y, x ≠ y → |K x y| ≤ A * Phase2S82.pairWeight M x y * pole x y) →
      (∀ x, Integrable (K x) (HRS.Whole.withDensityReal rho)) →
      (∀ x, ∫ y, K x y ∂HRS.Whole.withDensityReal rho = 0) →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum K X) 2
          (canonicalP d N a beta) ∧
        evariance (fun X : EucConfig d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum K X)
          (canonicalP d N a beta) ≤ ENNReal.ofReal (CJ * A ^ 2 * logN N / N) := by
  obtain ⟨DJ, hDJ, hrowJ⟩ := s82t_J_row hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq G c hG hc hρ hρG
  have hMom0 : 0 ≤ HRS.MS.S82N.s82n_Mom d (4 * M) G c :=
    HRS.MS.S82N.s82n_Mom_nonneg (by omega) _ _ _ (by linarith) hG.le hc
  set Mom := HRS.MS.S82N.s82n_Mom d (4 * M) G c with hMom
  refine ⟨|C0| * (16 * C0 ^ 2 * DJ * Mom), by positivity, ?_⟩
  intro h hW hP A hA K hKm hKs hKb hKi hK0 N hN
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hC0 := hW.positive
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  set N := m + 2 with hNdef
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  set Ψ : Euc d → ℝ := fun x => DJ * A ^ 2 * jbracket x ^ (4 * M) * ((N : ℕ) : ℝ) * logN N with hΨ
  have hrow : ∀ᵐ x ∂mu, ∫⁻ X', ENNReal.ofReal ((∑ j, K x (X' j)) ^ 2)
      ∂referenceLaw q h mu beta N (m + 1) (Fin.cons x pins0 : Fin (0 + 1) → Euc d) ≤
      ENNReal.ofReal (Ψ x) := ae_of_all _ fun x => hrowJ h hW hP A hA K hKm hKb hKi hK0 m x
  set J : ℝ := DJ * A ^ 2 * ((N : ℕ) : ℝ) * logN N * Mom with hJ
  have hc0 : 0 ≤ DJ * A ^ 2 * ((N : ℕ) : ℝ) * logN N := by positivity
  have hJle : ∫⁻ x, ENNReal.ofReal (Ψ x) ∂s82q_nu q mu beta N pins0 ≤ ENNReal.ofReal J := by
    calc ∫⁻ x, ENNReal.ofReal (Ψ x) ∂s82q_nu q mu beta N pins0
        ≤ ∫⁻ x, ENNReal.ofReal (Ψ x) ∂mu :=
          lintegral_mono' (s82q_nu_le q hW.short.nonneg mu beta hbeta N pins0) le_rfl
      _ ≤ ENNReal.ofReal (DJ * A ^ 2 * ((N : ℕ) : ℝ) * logN N) *
            ∫⁻ x, ENNReal.ofReal (jbracket x ^ (4 * M)) ∂mu := by
          refine s82q_lint_scale _ _ _ _ hc0 (ae_of_all _ fun x => le_of_eq ?_)
          simp only [hΨ]; ring
      _ ≤ ENNReal.ofReal (DJ * A ^ 2 * ((N : ℕ) : ℝ) * logN N) * ENNReal.ofReal Mom :=
          mul_le_mul_of_nonneg_left (s82p2_jb_moment hd (4 * M) (by linarith) G c hG hc _ hρ hρG) bot_le
      _ = ENNReal.ofReal J := (ENNReal.ofReal_mul hc0).symm
  obtain ⟨-, hFL, hvar⟩ := s82q_pair_template hW hbeta (N := N) hN (p := 0) (m := m + 1)
    (by omega) (by omega) (by omega) pins0 K hKs hKm (((N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) Ψ J hrow hJle
  have hFm : Measurable (fun X : EucConfig d N =>
      ((N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum K X) :=
    measurable_const.mul (s82t_pairSum_measurable hKm)
  have hV : evariance (fun X : EucConfig d N => ((N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum K X)
      (unpinnedReference q h mu beta N) ≤
      ENNReal.ofReal (16 * C0 ^ 2 * DJ * Mom * A ^ 2 * logN N / ((N : ℕ) : ℝ)) := by
    refine hvar.trans (le_of_eq ?_)
    congr 1
    rw [s82t_cN_sq (by omega), hJ]
    have : ((m + 1 + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) := by rw [hNdef]
    rw [this]
    field_simp
  obtain ⟨hFc, hVc⟩ := s82q_transfer hW hN _ hFm hFL _ hV
  refine ⟨hFc, hVc.trans (le_of_eq ?_)⟩
  rw [← ENNReal.ofReal_mul hC0.le, abs_of_pos hC0]
  congr 1
  ring

end HRS.MS.S82T
