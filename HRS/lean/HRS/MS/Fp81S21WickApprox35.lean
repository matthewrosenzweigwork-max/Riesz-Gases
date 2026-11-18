import HRS.MS.Fp81S21WickApprox34
import HRS.MS.Fp81S21WickApprox28
import HRS.MS.Fp81S21RankKernel4

/-! Shared physical rank-kernel certificates and particle time errors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Select a common rank family after the physical Gaussian selection. Its
certificate and both fixed-time profiles are retained, and every supplied
particle time representative has the corresponding time error. -/
theorem fp81s21_quadraticPhysical31_shared_rankKernel (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∀ ε : ℕ → ℝ, ∀ S : fp81s21_QuadraticPhysical31 p R Es E ε,
    ∀ m : ℕ, ∃ Λ : ℝ, ∃ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    0 ≤ Λ ∧ (∀ j, (θ j).1 = gradient (E.test j)) ∧
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
    IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
      (fun θ => commutatorKernel p.d p.s θ.1) (fun θ k => (D θ k).kernel) ∧
    ∃ τN τG : ℕ → ℝ, (∀ k, 0 ≤ τN k) ∧ (∀ k, 0 ≤ τG k) ∧
    Tendsto τN atTop (𝓝 0) ∧ Tendsto τG atTop (𝓝 0) ∧
    (∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
      ∀ f : Euc p.d → ℝ, IsR2Test f →
      ∀ θ' : HRS.MS.R2S11.s11V p.d Λ, θ'.1 = gradient f → ∀ k : ℕ,
      ∃ hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ' k).kernel xy.1 xy.2)
        2 ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
      fp81s21_SqErr G.P
        (fun ω => S.W G u (hf.toLp (fun xy => (D θ' k).kernel xy.1 xy.2)) ω)
        (fun ω => fp81s21_wickChartField Es (S.qs G) u ω f) (τG k)) ∧
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
            (Real.sqrt (H * (m : ℝ)) * τN k)) := by
  obtain ⟨δn, hδn, hδnh, hn⟩ := fp81s21_rankKernel_particle_sqerr p
  obtain ⟨δt, hδt, hδth, ht⟩ := fp81s21_particle_rankKernel_time_sqerr2 p
  let δ0 := min δn δt
  refine ⟨δ0, lt_min hδn hδt, (min_le_left _ _).trans hδnh, ?_⟩
  intro δ hδ hδle R Es E ε S m
  have hδn' : δ ≤ δn := hδle.trans (min_le_left _ _)
  have hδt' : δ ≤ δt := hδle.trans (min_le_right _ _)
  obtain ⟨Λ, hΛ, θ, hθ⟩ := fp81s21_chart_gradient_velocities2 E m
  obtain ⟨D, B, C, κ, hB, hC, hκ, hκlim, happrox, hprod⟩ :=
    fp81s21_rankKernel_moving_product_profile p R Λ hΛ
  obtain ⟨τN, hτN, hτNlim, herrN⟩ :=
    hn δ hδ hδn' R Λ hΛ D B C hB hC happrox κ hκ hκlim hprod
  obtain ⟨τG, hτG, hτGlim, herrG⟩ :=
    fp81s21_quadraticPhysical31_rankKernel_profile p R Es E ε S Λ hΛ D B C hB hC happrox
  refine ⟨Λ, θ, D, hΛ, hθ, B, C, hB, hC, happrox,
    τN, τG, hτN, hτG, hτNlim, hτGlim, herrG, ?_⟩
  intro N hN A r Mr a H ha hH hr V hV k
  apply ht δ hδ hδt' R N hN A E m k Λ θ hθ D r Mr a H (τN k) ha hH hr V hV
  intro u hu j
  exact (herrN k N hN A u hu (θ j)).2

#print axioms fp81s21_quadraticPhysical31_shared_rankKernel
end HRS.Fp81.S21
end
