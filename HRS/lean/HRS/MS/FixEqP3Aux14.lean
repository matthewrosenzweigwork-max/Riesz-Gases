import HRS.MS.FixEqP3Aux13

/-!
# S5.7 `fixed_equation` (worker S57P), part 26: the Gaussian noise field of a family

`s57p_fam_noise`: given an isonormal process `W` on `L²([0,T]×ℝ^d;ℝ^d)`, the noise field `X` of the family `(ν,c,ρ)` with noise level `q`:
a process in `B_m`, measurable, continuous in `t ∈ [0,T]` for every sample point, with coordinates `W(κ_t φ_α)` a.s., whose
finite-dimensional pairings with test functions of `Σ^m` are centered Gaussian with covariance `noiseCovW`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau HRS.MS.U10

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ}
  {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca Cd : ℝ}

/-- the gradient field of a test function of `Σ^m` is continuous and bounded -/
theorem s57p_osc_A (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hm : (J : ℝ) + d < m) {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (s57pA (fixedEqCoeff s M Q ν c ρ) t φ) ∧
      ∃ B : ℝ, ∀ p, ‖s57pA (fixedEqCoeff s M Q ν c ρ) t φ p‖ ≤ B := by
  obtain ⟨hsum, hexp, htail⟩ := s57p_hermite_series hd hm hCj hjets hφ
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  set g : MultiIndex d → ℝ := fun α => |s57pb d m φ α| * (Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) with hg
  have hg0 : ∀ α, 0 ≤ g α := fun α => mul_nonneg (abs_nonneg _) (mul_nonneg hCj (Real.rpow_nonneg (oscEv_pos α).le _))
  have hφR : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hBφ : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ ∑' α, g α := by
    intro l hl x
    have := htail ∅ l hl x
    have e : (fun y => φ y - s57pP d m φ ∅ y) = φ := by funext y; simp [s57pP]
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    refine tsum_congr fun α => ?_
    simp [hg]
  obtain ⟨hcl, hO⟩ := hCu Fx.fam.adj (tsum_nonneg hg0) hφR hBφ t ht
  exact ⟨s57p_A_cont ht.1 hcl, _, s57p_A_bound ht.1 (fun r hr x => (hO r hr).2 1 (by omega) x)⟩

theorem s57p_fam_noise (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hJ : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (hm : (J : ℝ) + d < m) {q : ℝ} (hq : 0 ≤ q) (hT0 : 0 < T)
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Qm : Measure Ω₀} [IsProbabilityMeasure Qm]
    {W : Lp (Euc d) 2 (s57pμ d T) → Ω₀ → ℝ} (hI : Sb7Iso Qm W)
    (hlaw : ∀ g, Qm.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2)))
    (hjoint : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (h : κ → Lp (Euc d) 2 (s57pμ d T)),
      Qm.map (fun w => (WithLp.toLp 2 (fun a => W (h a) w) : EuclideanSpace ℝ κ)) =
        multivariateGaussian 0 (Matrix.of fun a b => inner ℝ (h a) (h b))) :
    ∃ X : ℝ → Ω₀ → OscDual d m, (∀ t, Measurable (X t)) ∧ (∀ w, ContinuousOn (fun t => X t w) (Set.Icc 0 T)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Qm, OscDual.coord (X t w) α =
        W (s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)) w) ∧
      ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        (∀ a, IsOscTest m (φ a)) →
        Qm.map (fun w => (WithLp.toLp 2 (fun a => OscDual.eval (X (ts a) w) (φ a)) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun a b =>
            noiseCovW (fixedEqCoeff s M Q ν c ρ) q (ts a) (ts b) (φ a) (φ b)) := by
  obtain ⟨hs0, hs1⟩ := s57p_kappa_hs Fx hbd hCa hCd hq (s57p_summable_J hd hm)
  obtain ⟨X, hXm, hXc, hXa⟩ := s57p_noise_exists hI hlaw hT0 m
    (fun t α => s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)) hs0 hs1
  refine ⟨X, hXm, hXc, hXa, fun p ts φ hts hφ => ?_⟩
  have hlaw2 := s57p_noise_law hI hjoint (fun t α => s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)) hXa
    (kφ := fun t φ => s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t φ)
    (fun t ht φ hφ ε hε => s57p_kappa_expand hθ hd Fx hbd hCj hjets hJ hm hCa hq hφ ht hε) p ts φ hts hφ
  rw [hlaw2]
  congr 2
  funext a b
  obtain ⟨hA1, B1, hB1⟩ := s57p_osc_A hθ hd Fx hCj hjets hm (hφ a) (hts a)
  obtain ⟨hA2, B2, hB2⟩ := s57p_osc_A hθ hd Fx hCj hjets hm (hφ b) (hts b)
  exact s57p_gram Fx.fe Fx.hT hq Fx.prob (hts a) (hts b) hA1 hA2 hB1 hB2

end HRS.MS.FixEq
