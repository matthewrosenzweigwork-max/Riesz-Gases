import HRS.Sections.Sec5
import HRS.PDE.MeanField

/-!
# Packet Q40b, part 2: analytic inputs extracted from `IsSmoothPositiveTrajectory`

From `htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ` (Proposition 5.1 for every `K`) we extract
the smooth uniform bounds on `ρ^t`, the weak-solution and regularity hypotheses of the duality
identity (Proposition 3.7), joint continuity, and (Proposition 3.9 / 5.2, via
`HRS.PDE.MFLinear.loss_facts`) the existence of classical adjoint solutions with the exponential
gradient bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem q40b_finiteRegHyp (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {K : ℕ}
    (hK : (d : ℝ) / 2 + 6 < K) : PDE.FiniteRegHyp d s β β K V ρ₀ := by
  have hcont : Continuous ρ₀ := by
    have := htr.init.smooth
    exact PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ₀) from this) (by exact_mod_cast le_top))
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  refine ⟨htr.hs0, htr.hsd, htr.hβ, le_rfl, hK, ?_, htr.init.density, ?_, ⟨ρ₀ x0, htr.init.pos x0, fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)⟩⟩
  · exact ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from htr.V_smooth)
      (WithTop.coe_le_coe.2 le_top)
  · exact PDE.MFSemigroup.memSobolev_of_isSmooth htr.init.smooth _


theorem q40b_sol (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {K : ℕ}
    (hK : (d : ℝ) / 2 + 6 < K) :
    ∃ ρc : ℝ → PDE.Coeff d, PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
      ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t := htr.global K hK

theorem q40b_rho_bounds (hd : 1 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ Λ : ℕ → ℝ, ∀ t, 0 ≤ t →
      IsProbDensity (ρ t) ∧ Torus.IsSmooth (ρ t) ∧ (∀ x, c₀ ≤ ρ t x) ∧
        ∀ k : ℕ, Torus.cbNorm k (ρ t) ≤ Λ k := by
  -- constants at level `K n = n + d + 7`
  have hKn : ∀ n : ℕ, (d : ℝ) / 2 + 6 < ((n + d + 7 : ℕ) : ℝ) := by
    intro n; push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hcont : ∀ n : ℕ, ∃ C : ℝ, ∀ t, 0 ≤ t → Torus.IsCk n (ρ t) ∧ Torus.cbNorm n (ρ t) ≤ C := by
    intro n
    have H := q40b_finiteRegHyp htr (hKn n)
    obtain ⟨c, C, hc, hU⟩ := PDE.finite_reg_uniform_bounds hd s β β (n + d + 7) V ρ₀ H
    obtain ⟨ρc, hρc, hρ⟩ := q40b_sol htr (hKn n)
    have hdn : (d : ℝ) / 2 + n < ((n + d + 7 : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    obtain ⟨C', hC'⟩ := PDE.toFun_isCk_le (d := d) n ((n + d + 7 : ℕ) : ℝ) hdn
    refine ⟨|C'| * C, fun t ht => ?_⟩
    have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd s β β (n + d + 7) V ρ₀ H β
      ⟨le_rfl, le_rfl⟩ ρc hρc t ht
    have h1 := hC' (ρc t) (hρc.cont.1 t ht) hreal
    rw [← hρ t ht]
    refine ⟨h1.1, h1.2.trans ?_⟩
    have h2 := (hU β ⟨le_rfl, le_rfl⟩ ρc hρc t ht).2
    have h3 : 0 ≤ PDE.hsNorm (((n + d + 7 : ℕ) : ℝ)) (ρc t) :=
      PDE.MFApriori.Aux.hsNorm_nonneg _ _
    calc C' * PDE.hsNorm (((n + d + 7 : ℕ) : ℝ)) (ρc t) ≤ |C'| * PDE.hsNorm (((n + d + 7 : ℕ) : ℝ)) (ρc t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |C'| * C := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  choose Λ hΛ using hcont
  have H0 := q40b_finiteRegHyp htr (hKn 0)
  obtain ⟨c, C, hc, hU⟩ := PDE.finite_reg_uniform_bounds hd s β β (0 + d + 7) V ρ₀ H0
  obtain ⟨ρc, hρc, hρ⟩ := q40b_sol htr (hKn 0)
  refine ⟨c, hc, Λ, fun t ht => ⟨?_, ?_, ?_, fun k => (hΛ k t ht).2⟩⟩
  · rw [← hρ t ht]
    exact PDE.MFWeak.isProbDensity_mfPath hd s β β (0 + d + 7) V ρ₀ H0 β ⟨le_rfl, le_rfl⟩ ρc hρc t ht
  · have : ∀ n : ℕ, ContDiff ℝ n (Torus.lift (ρ t)) := fun n => (hΛ n t ht).1
    exact contDiff_infty.2 this
  · intro x
    rw [← hρ t ht]
    exact ((hU β ⟨le_rfl, le_rfl⟩ ρc hρc t ht).1 x).1


theorem q40b_classical_congr {D : DynData d} {ρ ρ' : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (h : ∀ r ∈ Set.Icc 0 t, ρ r = ρ' r)
    (hF : IsClassicalAdjointSolution D ρ t φ F) : IsClassicalAdjointSolution D ρ' t φ F where
  c2 := hF.c2
  cont_c2 := hF.cont_c2
  terminal := hF.terminal
  time_deriv := fun x r hr => by
    have := hF.time_deriv x r hr
    rwa [h r ⟨hr.1.le, hr.2.le⟩] at this
  cont_time_deriv := by
    refine hF.cont_time_deriv.congr fun p => ?_
    simp only [h p.1.1 p.1.2]

theorem q40b_classical_iff {D : DynData d} {ρ ρ' : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (h : ∀ r ∈ Set.Icc 0 t, ρ r = ρ' r) :
    IsClassicalAdjointSolution D ρ t φ F ↔ IsClassicalAdjointSolution D ρ' t φ F :=
  ⟨q40b_classical_congr h, q40b_classical_congr fun r hr => (h r hr).symm⟩

open Classical in
theorem q40b_dite_aux (P P' : (ℝ → Torus d → ℝ) → Prop) (hP : P = P') (r : ℝ) :
    (if h : ∃ f, P f then h.choose r else (0 : Torus d → ℝ)) =
      if h : ∃ f, P' f then h.choose r else 0 := by
  subst hP; rfl

theorem q40b_propagator_congr {D : DynData d} {ρ ρ' : ℝ → Torus d → ℝ} {t : ℝ}
    (h : ∀ r ∈ Set.Icc 0 t, ρ r = ρ' r) (r : ℝ) (φ : Torus d → ℝ) :
    propagator D ρ r t φ = propagator D ρ' r t φ := by
  have hP : (fun f => IsClassicalAdjointSolution D ρ t φ f) =
      (fun f => IsClassicalAdjointSolution D ρ' t φ f) :=
    funext fun f => propext (q40b_classical_iff h)
  unfold propagator
  exact q40b_dite_aux _ _ hP r

theorem q40b_meanField_congr {D : DynData d} {T : ℝ} {ρ ρ' : ℝ → Torus d → ℝ}
    (h : ∀ r ∈ Set.Icc 0 T, ρ r = ρ' r) (hρ : IsMeanFieldSolution D T ρ') :
    IsMeanFieldSolution D T ρ where
  density := fun t ht => by rw [h t ht]; exact hρ.density t ht
  weak := fun ψ hψ t ht => by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    rw [h t ht, h 0 h0]
    rw [hρ.weak ψ hψ t ht]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    simp only [h r hrT]


theorem q40b_hK0 (d : ℕ) : (d : ℝ) / 2 + 6 < ((0 + d + 7 : ℕ) : ℝ) := by
  push_cast
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem q40b_meanField (hd : 1 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ}
    (hT : 0 < T) : IsMeanFieldSolution htr.dyn T ρ := by
  have H := q40b_finiteRegHyp htr (q40b_hK0 d)
  obtain ⟨ρc, hρc, hρ⟩ := q40b_sol htr (q40b_hK0 d)
  have := PDE.finite_reg_isMeanFieldSolution hd s β β (0 + d + 7) V ρ₀ H β ⟨le_rfl, le_rfl⟩ ρc hρc T hT
  exact q40b_meanField_congr (fun r hr => (hρ r hr.1).symm) this

theorem q40b_regular (hd : 1 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) :
    ∃ Λ : ℝ, IsRegularMF 3 Λ T ρ := by
  obtain ⟨c₀, hc₀, Λ, hΛ⟩ := q40b_rho_bounds hd htr
  refine ⟨Λ 3, fun t ht => ⟨?_, (hΛ t ht.1).2.2.2 3⟩⟩
  exact PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) (hΛ t ht.1).2.1

theorem q40b_jointCont (hd : 1 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  have H := q40b_finiteRegHyp htr (q40b_hK0 d)
  obtain ⟨ρc, hρc, hρ⟩ := q40b_sol htr (q40b_hK0 d)
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd s β β (0 + d + 7) V ρ₀ H β
    ⟨le_rfl, le_rfl⟩ ρc hρc
  have hSol : PDE.MFApriori.MFSolRealOn d s V β⁻¹ ((0 + d + 7 : ℕ) : ℝ) ρ₀ ρc T :=
    ⟨PDE.MFApriori.IsMFSolutionHK.toSolOn hρc T, fun τ hτ => hreal τ hτ.1⟩
  have hK2 : (d : ℝ) / 2 + 2 < ((0 + d + 7 : ℕ) : ℝ) := by
    have := q40b_hK0 d; linarith
  have := (PDE.MFApriori.continuousOn_mfPath_prod_on hd s htr.hs0 htr.hsd (0 + d + 7) hK2 V ρ₀ H.hV β⁻¹ ρc hSol).1
  refine this.congr fun p hp => ?_
  show ρ p.1 p.2 = PDE.mfPath ρc p.1 p.2
  rw [hρ p.1 hp.1.1]


theorem q40b_K_ok (d j : ℕ) : (d : ℝ) / 2 + 6 < ((2 * j + 4 * d + 20 : ℕ) : ℝ) := by
  push_cast
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem q40b_adjoint (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {j : ℕ} (hj : Even j) (hjd : (d : ℝ) / 2 + 4 < j)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    (∀ t, 0 ≤ t → ∃ F : ℝ → Torus d → ℝ, IsClassicalAdjointSolution htr.dyn ρ t φ F ∧
      ∀ r ∈ Set.Icc 0 t, propagator htr.dyn ρ r t φ = F r) ∧
    ∃ C m : ℝ, 0 ≤ C ∧ 0 < m ∧ ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator htr.dyn ρ r t φ) x‖ ≤ C * Real.exp (-m * (t - r)) := by
  have hd1 : 1 ≤ d := by omega
  have hK := q40b_K_ok d j
  have H := q40b_finiteRegHyp htr hK
  obtain ⟨ρc, hρc, hρ⟩ := q40b_sol htr hK
  have hρβc : Continuous ρβ := PDE.MFLinear.continuous_of_isSmooth hρS
  obtain ⟨m, Cρ, c₀, Λ₀, hF, -⟩ := PDE.MFLinear.loss_facts hd1 s β β (2 * j + 4 * d + 20) V ρ₀ H j hj hjd
    le_rfl β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ hρβ hρβc hρpos
  have hcongr : ∀ t : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ρ r = PDE.mfPath ρc r :=
    fun t r hr => (hρ r hr.1).symm
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      have hDK := PDE.ClassicalAux.convKernelFacts_of_two_le hd htr.dyn.hs0 htr.dyn.hsd
      have hV1 : Torus.IsCk 1 htr.dyn.V :=
        PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) htr.V_smooth
      have hρ1 : Torus.IsCk 1 (ρ 0) :=
        PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top)
          ((q40b_rho_bounds hd1 htr).choose_spec.2.choose_spec 0 le_rfl).2.1
      have hφ2 : Torus.IsCk 2 φ := PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) hφ
      refine ⟨fun _ => φ, PDE.MFSemigroup.isClassical_zero htr.dyn hDK hV1 ρ hρ1 hφ2, fun r hr => ?_⟩
      have : r = 0 := le_antisymm hr.2 hr.1
      subst this
      exact PDE.MFSemigroup.propagator_zero htr.dyn hDK hV1 ρ hρ1 hφ2
    · obtain ⟨F, hFc, hFp⟩ := hF.classical φ hφ t hpos
      refine ⟨F, (q40b_classical_iff (hcongr t)).2 hFc, fun r hr => ?_⟩
      rw [q40b_propagator_congr (hcongr t) r φ]
      exact hFp r hr
  · obtain ⟨C, hC0, -, -, -, hbd⟩ := hF.grad φ hφ
    refine ⟨C, m, hC0, hF.m_pos, fun t ht r hr x => ?_⟩
    rw [q40b_propagator_congr (hcongr t) r φ]
    exact hbd t ht r hr x

end HRS.Q40b
