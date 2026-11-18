import HRS.MS.Fp81S21WickApprox36

/-! Simultaneous time approximation with one selected rank family. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- After selecting the physical quadratic Gaussian data, one rank family and
profiles work for every supplied physical particle and Gaussian time section. -/
theorem fp81s21_quadraticPhysical31_both_time (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∀ ε : ℕ → ℝ, ∀ S : fp81s21_QuadraticPhysical31 p R Es E ε,
    ∀ m : ℕ, ∃ Λ : ℝ, ∃ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    0 ≤ Λ ∧ (∀ j, (θ j).1 = gradient (E.test j)) ∧
    ∃ τN τG : ℕ → ℝ, (∀ k, 0 ≤ τN k) ∧ (∀ k, 0 ≤ τG k) ∧
    Tendsto τN atTop (𝓝 0) ∧ Tendsto τG atTop (𝓝 0) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ (r : ℝ → A.Ω → r26t6_Coeff) (Mr a H : ℝ), 0 ≤ a → 0 ≤ H →
      fp81s21_MomentRep E A.P (fp81s21_particleQuadField R N A) r Mr →
      ∀ V : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep A.P r Mr a H V → ∀ k : ℕ,
      ∃ Mq : ℝ, ∃ q : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry q) ∧
        (∀ᵐ ω ∂A.P, ∀ u, 0 ≤ u → q u ω = ∑ j : Fin m,
          fp81s21_particleQuad A u (D (θ j) k).kernel ω • fp81s21_coeffBasis j) ∧
        ∃ U : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
          fp81s21_TimeL2Rep A.P q Mq a H U ∧
          fp81s21_SqErr A.P U (fun ω => fp81s21_timeProject H m (V ω))
            (Real.sqrt (H * (m : ℝ)) * τN k)) ∧
    (∀ G : GaussianRealization R, ∀ (a H : ℝ), 0 ≤ a → 0 ≤ H →
      ∀ V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep G.P (S.qe G) (S.Kstar ^ 4 * S.B / 2) a H V →
      ∀ k : ℕ, ∃ Mq : ℝ, ∃ q : ℝ → G.Ω → r26t6_Coeff,
        Measurable (Function.uncurry q) ∧
        (∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P, ∀ j : ℕ,
          q u ω j = if hj : j < m then
            (S.W G u (fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k)) : G.Ω → ℝ) ω
          else 0) ∧
        ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
          fp81s21_TimeL2Rep G.P q Mq a H U ∧
          fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (V ω))
            (Real.sqrt (H * (m : ℝ)) * τG k)) := by
  obtain ⟨δn, hδn, hδnh, hn⟩ := fp81s21_quadraticPhysical31_shared_rankKernel p
  obtain ⟨δg, hδg, hδgh, hg⟩ := fp81s21_quadraticPhysical31_time_lift p
  let δ0 := min δn δg
  refine ⟨δ0, lt_min hδn hδg, (min_le_left _ _).trans hδnh, ?_⟩
  intro δ hδ hδle R Es E ε S m
  have hδn' : δ ≤ δn := hδle.trans (min_le_left _ _)
  have hδg' : δ ≤ δg := hδle.trans (min_le_right _ _)
  obtain ⟨Λ, θ, D, hΛ, hθ, B, C, hB, hC, happrox,
    τN, τG, hτN, hτG, hτNlim, hτGlim, herrG, herrN⟩ :=
    hn δ hδ hδn' R Es E ε S m
  refine ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, herrN, ?_⟩
  exact hg δ hδ hδg' R Es E ε S m Λ θ hθ D τG herrG

#print axioms fp81s21_quadraticPhysical31_both_time
end HRS.Fp81.S21
end
