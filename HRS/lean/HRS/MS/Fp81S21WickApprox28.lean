import HRS.MS.Fp81S21WickApprox27

/-! Particle physical finite-rank time-error assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_wickApprox28_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_wickApprox28_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A particle fixed-time rank-kernel profile, the physical chart representative,
and its genuine time section yield the physical finite-rank time-L² error. -/
theorem fp81s21_particle_rankKernel_time_sqerr2 (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ (m k : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ),
      (∀ j, (θ j).1 = gradient (E.test j)) →
      ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      ∀ (r : ℝ → A.Ω → r26t6_Coeff) (Mr a H ε : ℝ),
      0 ≤ a → 0 ≤ H →
      fp81s21_MomentRep E A.P (fp81s21_particleQuadField R N A) r Mr →
      ∀ V : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep A.P r Mr a H V →
      (∀ u, 0 ≤ u → ∀ j : Fin m, fp81s21_SqErr A.P
        (fp81s21_particleQuad A u (D (θ j) k).kernel)
        (fp81s21_particleQuad A u (commutatorKernel p.d p.s (θ j).1)) ε) →
      ∃ Mq : ℝ, ∃ q : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry q) ∧
        (∀ᵐ ω ∂A.P, ∀ u, 0 ≤ u → q u ω = ∑ j : Fin m,
          fp81s21_particleQuad A u (D (θ j) k).kernel ω • fp81s21_coeffBasis j) ∧
        ∃ U : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
          fp81s21_TimeL2Rep A.P q Mq a H U ∧
          fp81s21_SqErr A.P U (fun ω => fp81s21_timeProject H m (V ω))
            (Real.sqrt (H * (m : ℝ)) * ε) := by
  obtain ⟨δ₀, hδ₀, hhalf, hfields⟩ := fp81s21_particle_rankKernel_time_fields2 p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R N hN A E m k Λ θ hθ D r Mr a H ε ha hH hrep V hV hfixed
  obtain ⟨Mq, q, hqm, hqe, hqsec, hqtime⟩ :=
    hfields δ hδ hδle R N hN A m (fun j => D (θ j) k)
  obtain ⟨U, hU⟩ := hqtime a ha H hH
  let rproj : ℝ → A.Ω → r26t6_Coeff := fun u ω => fp81s21_projectField m (r u ω)
  have hrm : Measurable (Function.uncurry rproj) :=
    (fp81s21_projectField m).continuous.measurable.comp hrep.1
  have hVp : fp81s21_TimeL2Rep A.P rproj Mr a H
      (fun ω => fp81s21_timeProject H m (V ω)) :=
    fp81s21_TimeL2Rep_project2 A.P r Mr a H m V hV
  have hsupport : ∀ u, 0 ≤ u → ∀ᵐ ω ∂A.P,
      fp81s21_projectField m (q u ω - rproj u ω) = q u ω - rproj u ω := by
    intro u hu
    filter_upwards [hqe] with ω hω
    rw [hω u hu]
    exact fp81s21_finite_basis_sub_project_supported2 m _ _
  have hcoord : ∀ u, 0 ≤ u → ∀ j ∈ Finset.range m,
      fp81s21_SqErr A.P (fun ω => q u ω j) (fun ω => rproj u ω j) ε := by
    intro u hu j hj
    let i : Fin m := ⟨j, Finset.mem_range.mp hj⟩
    have hfixed' := hfixed u hu i
    have he : (fun ω => ‖fp81s21_particleQuad A u (D (θ i) k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s (θ i).1) ω‖ ^ 2) =ᵐ[A.P]
        (fun ω => ‖q u ω j - rproj u ω j‖ ^ 2) := by
      filter_upwards [hqe, (hrep.2 u hu).2.2] with ω hqω hrω
      have hqcoord : q u ω j = fp81s21_particleQuad A u (D (θ i) k).kernel ω := by
        rw [hqω u hu]
        exact fp81s21_finite_basis_coordinate2 m _ i
      have hrcoord : rproj u ω j =
          fp81s21_particleQuad A u (commutatorKernel p.d p.s (θ i).1) ω := by
        rw [show rproj u ω j = r u ω j by simp [rproj, fp81s21_projectField_coordinate2,
          Finset.mem_range.mp hj]]
        rw [← fp81s21_chartAction_test_coordinate2 E (r u ω) j,
          hrω.1 (E.test j) (E.test_smooth j)]
        rw [hθ i, fp81s21_particleQuad_commutator_eq]
        rfl
      rw [hqcoord, hrcoord]
    exact ⟨hfixed'.1.congr he, by rw [← integral_congr_ae he]; exact hfixed'.2⟩
  refine ⟨Mq, q, hqm, hqe, U, hU, ?_⟩
  exact fp81s21_time_finite_coordinate_sqerr A.P q rproj Mq Mr a H U
    (fun ω => fp81s21_timeProject H m (V ω)) hqm hrm hU hVp ha hH m ε hsupport hcoord

#print axioms fp81s21_particle_rankKernel_time_sqerr2
end HRS.Fp81.S21
end
