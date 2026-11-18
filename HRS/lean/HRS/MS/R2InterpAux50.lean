import HRS.MS.R2InterpAux49

/-!
# S10.2 (worker S102), part 50 (packet F9): the covariance Riemann--Stieltjes integral of a cylindrical functional
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIL HRS.MC.Sec7.S7PIF6 HRS.MC.Sec7.S7PIG6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

/-- The density of the pair `(i,j)` of observations for the `𝒥` term: `u ↦ 1_{u ≤ τ_i ∧ τ_j} z^u(∇U^{u,τ_i}φ_i·∇U^{u,τ_j}φ_j)`. -/
def s102_hh2 (C : WholeCoeff d) (m : ℝ) {q : ℕ} {T : ℝ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (z : ℝ → (Euc d → ℝ) → ℝ) (i j : Fin q) (u : ℝ) : ℝ :=
  (Iic (min (τ i : ℝ) (τ j : ℝ))).indicator (fun u => z u (fun x =>
      inner ℝ (gradient (propagatorW C u (τ i) (oscTestFun m (α i))) x)
        (gradient (propagatorW C u (τ j) (oscTestFun m (α j))) x))) u

theorem s102_hh2_integral (C : WholeCoeff d) (m : ℝ) {q : ℕ} {T : ℝ} (τ : Fin q → Icc (0 : ℝ) T)
    (α : Fin q → MultiIndex d) (z : ℝ → (Euc d → ℝ) → ℝ) (i j : Fin q) {a a' : ℝ} (ha : 0 ≤ a) :
    ∫ u in Ioc a a', s102_hh2 C m τ α z i j u =
      ∫ u in Ioc a a' ∩ Icc (0 : ℝ) (min (τ i : ℝ) (τ j : ℝ)), z u (fun x =>
        inner ℝ (gradient (propagatorW C u (τ i) (oscTestFun m (α i))) x)
          (gradient (propagatorW C u (τ j) (oscTestFun m (α j))) x)) := by
  unfold s102_hh2
  rw [setIntegral_indicator measurableSet_Iic]
  have : Ioc a a' ∩ Iic (min (τ i : ℝ) (τ j : ℝ)) = Ioc a a' ∩ Icc (0 : ℝ) (min (τ i : ℝ) (τ j : ℝ)) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [h1.1], h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  rw [this]

/-- **F9**: the sums `∑ r2JPair(D²u_{G∘obs}(τ,Y_τ))` converge to `∫_{(0,T]} ∑_{ij} ∂_{ij}F(r,obs Y_r) 2ν z^r(∇obsTest_i·∇obsTest_j) dr`. -/
theorem s102_F9 (hT : 0 < T)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (hcov : ∀ k k', ContinuousOn (fun u => s102_obsCov C m τ α u k k') (Icc 0 T))
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (Y : ℝ → OscPath d m T)
    (hY : ContinuousOn Y (Icc 0 T)) (z : ℝ → (Euc d → ℝ) → ℝ)
    (Jc : ℝ → TensorDual (OscPath d m T) 2)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T z (Ioc a b) (Jc b - Jc a))
    (hzi : ∀ i j, IntegrableOn (s102_hh2 C m τ α z i j) (Icc 0 T)) :
    IsR2RS T (fun t a a' => r2JPair C m T z (Ioc a a')
        (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun w => G (s102_obs τ α w)) t) (Y t)))
      (∫ u in Ioc 0 T, ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α (Y u))
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] * (2 * C.ν * s102_hh2 C m τ α z i j u)) := by
  set g : Fin q × Fin q → ℝ → ℝ := fun p t => iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G t)
    (s102_obs τ α (Y t)) ![EuclideanSpace.single p.1 1, EuclideanSpace.single p.2 1] with hgdef
  have hcont := HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof T _ hcov
    (fun u hu => (s102_obs_law C (hγ u hu) τ α).1) G 2 hG 2 le_rfl
  have hg : ∀ p, ContinuousOn (g p) (Icc 0 T) := by
    intro p
    have h1 : ContinuousOn (fun t : ℝ => (t, s102_obs τ α (Y t))) (Icc 0 T) :=
      continuousOn_id.prodMk ((s102_obs τ α).continuous.comp_continuousOn hY)
    have h2 := hcont.comp h1 (fun t ht => ⟨ht, mem_univ _⟩)
    exact (S7PIL_ev (![EuclideanSpace.single p.1 (1 : ℝ), EuclideanSpace.single p.2 1] :
      Fin 2 → EuclideanSpace ℝ (Fin q))).continuous.comp_continuousOn h2
  have hI := HRS.MC.Sec7.S7PIS2.S7PIS2_RS_density T hT g
    (fun p u => 2 * C.ν * s102_hh2 C m τ α z p.1 p.2 u) hg (fun p => (hzi p.1 p.2).const_mul _)
  have hI' : IsR2RS T (fun t a a' => ∑ p, g p t * ∫ u in Ioc a a', 2 * C.ν * s102_hh2 C m τ α z p.1 p.2 u)
      (∫ u in Ioc 0 T, ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α (Y u))
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] * (2 * C.ν * s102_hh2 C m τ α z i j u)) := by
    rw [s102_isR2RS_iff]
    simpa only [Fintype.sum_prod_type] using hI
  refine (s102_isR2RS_iff _ _ _).2 (S7PIG6_IsRS_congr ((s102_isR2RS_iff _ _ _).1 hI') fun t a a' ht ha haa' ha'T => ?_)
  rw [s102_jPair_eq C hT z Jc hJ a a' ha haa' ha'T, (s102_heat_obs_deriv C γ hγ τ α G hG t ht _).2,
    s102_cyl_expand]
  simp only [map_sum, map_smul, smul_eq_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [s102_J_gen (hJ a a' ha haa' ha'T), integral_const_mul, s102_hh2_integral C m τ α z i j ha]

end HRS.MS.R2Interp

end
