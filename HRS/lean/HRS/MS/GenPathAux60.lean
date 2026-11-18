import HRS.MS.GenPathAux59

/-!
# S5.6 packet P7k: the distance between the particle initial path `A(k₀)` and the prescribed path, pointwise
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_sigma_nonneg (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) : 0 ≤ S.σ N := by
  unfold WholeSetup.σ sigmaScale
  have := S.hκ N
  have := (S.hinvβ N).1
  split_ifs
  · exact (S.hκ N).le
  · exact le_min (S.hκ N).le (Real.sqrt_nonneg _)

theorem s56_sigma_eq (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) : S.σ N = S.A N * S.κ N := by
  unfold WholeSetup.σ WholeSetup.A Ascale
  have hκ := S.hκ N
  by_cases h : S.invβ N = 0
  · simp [h, sigmaScale]
  · simp only [h, if_false]
    field_simp

theorem s56_eps_pointwise (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (s : ℕ → Set.Icc (0 : ℝ) b.T) (hs : DenseRange s)
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d b.m b.T) (x : EucConfig d N)
    (η : (Euc d → ℝ) → ℝ) (c : ℕ × MultiIndex d → ℝ)
    (hcη : ∀ i : ℕ × MultiIndex d, c i = S.A N * η (propagatorW (S.coeff N) 0 (s i.1) (oscTestFun b.m i.2)))
    (hgc : s56PathCoords (d := d) b.m b.T s (g c) = c) :
    ‖s56EvalPath hbv.hT.le (s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical x)
        (HRS.Whole.withDensityReal (S.ρ N 0))) - g c‖ₑ ≤
      ENNReal.ofReal (S.A N) * ⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE fun α : MultiIndex d =>
        S.κ N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
          η (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  set k := s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical x)
    (HRS.Whole.withDensityReal (S.ρ N 0)) with hk
  set F : OscPath d b.m b.T := s56EvalPath hT k - g c with hF
  set L : ℝ≥0∞ := ENNReal.ofReal (S.A N) * ⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE fun α : MultiIndex d =>
        S.κ N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
          η (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) with hL
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) b.T =>
      (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F) t := (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F).continuous
  have hclosed : IsClosed {t : Set.Icc (0 : ℝ) b.T | ‖(show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F) t‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  have key : ∀ t0 : Set.Icc (0 : ℝ) b.T, ‖(show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F) t0‖ₑ ≤ L :=
    fun t0 => hs.induction_on t0 hclosed (fun n => by
      show ‖(show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F) (s n)‖ₑ ≤ L
      rw [s56_enorm_eq_l2NormE]
      have hco : ∀ α : MultiIndex d, OscDual.coord ((show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F) (s n)) α =
          S.A N * (S.κ N * (HRS.Whole.pair (HRS.Whole.empirical x)
              (propagatorW (S.coeff N) 0 (s n) (oscTestFun b.m α)) -
            HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0))
              (propagatorW (S.coeff N) 0 (s n) (oscTestFun b.m α))) -
            η (propagatorW (S.coeff N) 0 (s n) (oscTestFun b.m α))) := by
        intro α
        show OscDual.coord (((show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from s56EvalPath hT k) - 
          (show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from g c)) (s n)) α = _
        rw [ContinuousMap.sub_apply, s56_coord_sub, s56EvalPath_apply]
        rw [s56_k0_eval b hbv S N hN hC (S.σ N) x (s n).2 α]
        have h2 := congrFun hgc (n, α)
        simp only [s56PathCoords, OscPath.at'] at h2
        rw [h2, hcη (n, α), s56_sigma_eq b S N]
        ring
      have : (fun α => OscDual.coord ((show C(Set.Icc (0 : ℝ) b.T, OscDual d b.m) from F) (s n)) α) =
          fun α => S.A N * (S.κ N * (HRS.Whole.pair (HRS.Whole.empirical x)
              (propagatorW (S.coeff N) 0 (s n) (oscTestFun b.m α)) -
            HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0))
              (propagatorW (S.coeff N) 0 (s n) (oscTestFun b.m α))) -
            η (propagatorW (S.coeff N) 0 (s n) (oscTestFun b.m α))) := funext hco
      rw [this, s56_l2NormE_mul]
      have hA : 0 ≤ S.A N := by
        unfold WholeSetup.A Ascale
        split_ifs
        · exact zero_le_one
        · exact div_nonneg (s56_sigma_nonneg b S N) (S.hκ N).le
      rw [abs_of_nonneg hA]
      exact mul_le_mul' le_rfl (le_iSup (fun t : Set.Icc (0 : ℝ) b.T => l2NormE fun α : MultiIndex d =>
        S.κ N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
          η (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) (s n)))
  by_cases hLtop : L = ⊤
  · rw [hLtop]; exact le_top
  have hb : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hLtop]
  refine ENNReal.ofReal_le_ofReal ((ContinuousMap.norm_le _ hb).2 fun t => ?_)
  have := key t
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hLtop, ENNReal.ofReal_le_ofReal_iff hb] at this
  exact this

end HRS.MS.GenPath
