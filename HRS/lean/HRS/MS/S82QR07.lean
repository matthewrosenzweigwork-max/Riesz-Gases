import HRS.MS.S82QT5
import HRS.MS.QsfCorr2

/-!
# S8.2 R07: weighted triple moments (frozen statement of the Pro skeleton `S82.R07`)
Twice-pinned inner row, once-pinned outer row (both conditional means retained), full resampling under the
reference law, one-way domination to the physical canonical law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- Twice-pinned inner row, then one-pin outer row, with both conditional means retained. -/
theorem weighted_triple_moments (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ G : Euc d → Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Measurable (fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2) →
      CanonicalTriple (HRS.Whole.withDensityReal rho) G →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        |G x y z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z) →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum G X) 2 (canonicalP d N a beta) ∧
        evariance (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum G X) (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 * logN N ^ 2 / (N : ℝ) ^ 2) := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  have hρ0 : HRS.Whole.IsProbDensity (HRS.Whole.thermalDensity d (criticalS d) a beta) := hT.prob
  have hρG : HRS.Whole.HasR2GaussianUpper (Cth + 1) cth
      (HRS.Whole.thermalDensity d (criticalS d) a beta) := by
    refine ⟨hT.hc, fun x => ?_⟩
    have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : 0 ≤ Real.exp (-cth * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith
  have hG : 0 < Cth + 1 := by linarith [hT.C0]
  obtain ⟨Cout, hCout, hout⟩ := HRS.MS.S82Q.s82q_outer hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq
    (rho := HRS.Whole.thermalDensity d (criticalS d) a beta) (Cth + 1) cth hG hT.hc hρ0 hρG
  set Mom := HRS.MS.S82N.s82n_Mom d (8 * M) (Cth + 1) cth with hMom
  have hMom0 : 0 ≤ Mom := HRS.MS.S82N.s82n_Mom_nonneg (by omega) _ _ _ (by linarith) hG.le hT.hc
  refine ⟨|C0| * (36 * C0 ^ 2 * Cout * Mom), by positivity, ?_⟩
  intro rho hrho h hW hP Gt A hA hGm hGc hGb N hN
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  have hC0 := hW.positive
  obtain rfl | ⟨m, rfl⟩ : N = 2 ∨ ∃ m, N = m + 3 := by
    rcases Nat.lt_or_ge N 3 with h3 | h3
    · left; omega
    · right; exact ⟨N - 3, by omega⟩
  · -- N = 2: the triple sum vanishes
    have hz : ∀ X : EucConfig d 2, tripleSum Gt X = 0 := by
      intro X
      rw [HRS.MS.S82Q.s82q_tripleSum_ite]
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b _ =>
        Finset.sum_eq_zero fun c' _ => if_neg ?_
      have key : ∀ a' b c' : Fin 2, ¬(b ≠ a' ∧ c' ≠ a' ∧ c' ≠ b) := by decide
      exact key a' b c'
    have hF0 : (fun X : EucConfig d 2 => ((2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X) =
        fun _ => 0 := by
      funext X; rw [hz X, mul_zero]
    rw [hF0]
    haveI := HRS.MS.S82P2.s82p2_canonicalP_prob hW hN
    refine ⟨memLp_const (0 : ℝ), ?_⟩
    simp [evariance]
  · -- N = m + 3
    haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal
        (HRS.Whole.thermalDensity d (criticalS d) a beta)) := HRS.Whole.Q09A.measure_isProb hρ0
    set mu := HRS.Whole.withDensityReal (HRS.Whole.thermalDensity d (criticalS d) a beta) with hmudef
    set N := m + 3 with hNdef
    have hN3 : 2 ≤ N := by omega
    have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hL1 := HRS.MS.S82Q.s82q_logN_nonneg (N := N) (by omega)
    let pins0 : Fin 0 → Euc d := fun i => i.elim0
    set Ψ : Euc d → ℝ := fun x => Cout * A ^ 2 * jbracket x ^ (8 * M) * ((N : ℕ) : ℝ) ^ 2 *
      logN N ^ 2 with hΨ
    have hrow : ∀ᵐ x ∂mu, ∫⁻ X', ENNReal.ofReal ((pairSum (fun y w => Gt x y w) X') ^ 2)
        ∂referenceLaw q h mu beta N (m + 2) (Fin.cons x pins0 : Fin (0 + 1) → Euc d) ≤
        ENNReal.ofReal (Ψ x) := ae_of_all _ fun x => hout h hW hP A hA Gt hGm hGc hGb m x
    set J : ℝ := Cout * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * logN N ^ 2 * Mom with hJ
    have hJle : ∫⁻ x, ENNReal.ofReal (Ψ x) ∂HRS.MS.S82Q.s82q_nu q mu beta N pins0 ≤
        ENNReal.ofReal J := by
      have hc0 : 0 ≤ Cout * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * logN N ^ 2 := by positivity
      calc ∫⁻ x, ENNReal.ofReal (Ψ x) ∂HRS.MS.S82Q.s82q_nu q mu beta N pins0
          ≤ ∫⁻ x, ENNReal.ofReal (Ψ x) ∂mu :=
            lintegral_mono' (HRS.MS.S82Q.s82q_nu_le q hW.short.nonneg mu beta hbeta N pins0) le_rfl
        _ ≤ ENNReal.ofReal (Cout * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * logN N ^ 2) *
              ∫⁻ x, ENNReal.ofReal (jbracket x ^ (8 * M)) ∂mu := by
            refine HRS.MS.S82Q.s82q_lint_scale _ _ _ _ hc0 (ae_of_all _ fun x => le_of_eq ?_)
            simp only [hΨ]; ring
        _ ≤ ENNReal.ofReal (Cout * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * logN N ^ 2) * ENNReal.ofReal Mom :=
            mul_le_mul_of_nonneg_left (HRS.MS.S82P2.s82p2_jb_moment hd (8 * M) (by linarith)
              (Cth + 1) cth hG hT.hc _ hρ0 hρG) bot_le
        _ = ENNReal.ofReal J := (ENNReal.ofReal_mul hc0).symm
    have hG1 : ∀ x y z, Gt x y z = Gt y x z := fun x y z => (hGc.1 x y z).1
    have hG2 : ∀ x y z, Gt x y z = Gt x z y := fun x y z => (hGc.1 x y z).2
    obtain ⟨-, hFL, hvar⟩ := HRS.MS.S82Q.s82q_triple_template hW hbeta hN3 (p := 0) (m := m + 2)
      (by omega) (by omega) (by omega) pins0 Gt hG1 hG2 hGm (((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) Ψ J
      hrow hJle
    have hFm : Measurable (fun X : EucConfig d N =>
        ((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X) := by
      refine measurable_const.mul ?_
      show Measurable (fun X : EucConfig d N => ∑ i, HRS.MS.S82Q.s82q_trow Gt i X)
      exact Finset.measurable_sum _ fun i _ => HRS.MS.S82Q.s82q_trow_measurable hGm i
    have hcN : (((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / ((N : ℕ) : ℝ) ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
      have : (-(5 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((5 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_neg hNr.le, Real.rpow_natCast, one_div]
    have hV : evariance (fun X : EucConfig d N => ((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X)
        (unpinnedReference q h mu beta N) ≤
        ENNReal.ofReal (36 * C0 ^ 2 * Cout * Mom * A ^ 2 * logN N ^ 2 / ((N : ℕ) : ℝ) ^ 2) := by
      refine hvar.trans (le_of_eq ?_)
      congr 1
      rw [hcN, hJ]
      have : ((m + 2 + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) := by rw [hNdef]
      rw [this]
      field_simp
    obtain ⟨hFc, hVc⟩ := HRS.MS.S82Q.s82q_transfer hW hN3 _ hFm hFL _ hV
    refine ⟨hFc, hVc.trans (le_of_eq ?_)⟩
    rw [← ENNReal.ofReal_mul hC0.le, abs_of_pos hC0]
    congr 1
    ring

end HRS.MS.Phase2S82
