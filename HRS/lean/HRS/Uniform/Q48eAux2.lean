import HRS.PDE.MeanFieldSemigroup

/-!
# Q48e, part 2: the frozen adjoint propagator at the thermal density

For the stationary frozen coefficient `ρ^t ≡ ρβ` (smooth, positive, probability density) and smooth `V`, the classical
adjoint propagator `U^{u,t} = propagator (mfData ...) (fun _ => ρβ) u t` on smooth test functions satisfies:

* `frozen_bound`: `‖U^{u,t}φ‖_{H^j} ≤ e^{c_j (t-u)} ‖φ‖_{H^j}` for every integer `j ≥ m_*` (Prop 3.9(a));
* `frozen_self`: `U^{t,t}φ = φ`;
* `frozen_smooth`: `U^{u,t}φ` is smooth;
* `frozen_semigroup`: `U^{r,t}φ = U^{r,σ}U^{σ,t}φ`;
* `frozen_coeff_cont`: `(t,u) ↦ ∫ e_k U^{u,t}φ` is continuous on the simplex `0 ≤ u ≤ t ≤ T`
  (time-homogeneity and joint continuity of the classical solution).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q48e

open HRS HRS.PDE HRS.PDE.MFSemigroup

variable {d : ℕ}

theorem frozen_self_pos (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (t : ℝ) (ht : 0 ≤ t) :
    propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) t t φ = φ := by
  set D := mfData d s hs0 hsd V β hβ with hD
  rcases ht.eq_or_lt with h0 | ht0
  · rw [← h0]
    have hK : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
    exact propagator_zero D hK (isCk_nat_of_isSmooth hV 1) (fun _ => ρβ) (isCk_nat_of_isSmooth hρ 1)
      (isCk_nat_of_isSmooth hφ 2)
  · obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρ hpos (mStar d)
    obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd (mStar d) le_rfl R MB Λ VB
    have hφc : Continuous φ := ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hφ 1)
    obtain ⟨h1, -⟩ := hmain D 0 t (fun _ => ρβ) (hA 0 t ht0) t ⟨ht0, le_rfl⟩ φ hφc
      (memSobolev_of_isSmooth hφ _)
    have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => ρβ) t φ f := ⟨_, h1⟩
    simp only [propagator, hex, dite_true]
    exact hex.choose_spec.terminal

theorem frozen_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (j : ℕ) (hj : mStar d ≤ j) :
    ∃ c : ℝ, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      MemSobolev (j : ℝ) (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ) ∧
      sobolevNorm (j : ℝ) (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ) ≤
        Real.exp (c * (t - u)) * sobolevNorm (j : ℝ) φ := by
  have hj3 : 3 ≤ j := le_trans (ClassicalPart.three_le_mStar d) hj
  obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρ hpos j
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd j hj R MB Λ VB
  refine ⟨R.lambdaM (Cs j) 0 (thetaOrder d s), fun φ hφ u t hu hut => ?_⟩
  have hφc : Continuous φ := ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hφ 1)
  have hφS : MemSobolev (j : ℝ) φ := memSobolev_of_isSmooth hφ _
  by_cases ht : 0 < t
  · obtain ⟨-, -, h3, -⟩ := hmain (mfData d s hs0 hsd V β hβ) 0 t (fun _ => ρβ) (hA 0 t ht) t
      ⟨ht, le_rfl⟩ φ hφc hφS
    exact h3 j (by omega) le_rfl u ⟨hu, hut⟩
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) (hu.trans hut)
    have hu0 : u = 0 := le_antisymm (ht0 ▸ hut) hu
    subst ht0; subst hu0
    rw [frozen_self_pos hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos φ hφ 0 le_rfl]
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul]
    exact ⟨hφS, le_rfl⟩


theorem frozen_smooth (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (u t : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) :
    Torus.IsSmooth (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ) := by
  set D := mfData d s hs0 hsd V β hβ with hD
  by_cases ht : 0 < t
  · have hφc : Continuous φ := ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hφ 1)
    have hn : ∀ n : ℕ, Torus.IsCk (n : WithTop ℕ∞)
        (propagator D (fun _ => ρβ) u t φ) := by
      intro n
      obtain ⟨j, hj⟩ : ∃ j : ℕ, j = mStar d + n + d := ⟨_, rfl⟩
      have hjm : mStar d ≤ j := by omega
      have hm1 : 1 ≤ j := by have := ClassicalPart.three_le_mStar d; omega
      have hφS : MemSobolev (j : ℝ) φ := memSobolev_of_isSmooth hφ _
      obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρ hpos j
      obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd j hjm R MB Λ VB
      obtain ⟨-, hpe, -, -⟩ := hmain D 0 t (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ φ hφc hφS
      rw [hpe u ⟨hu, hut⟩]
      obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (j : ℝ) φ hφS
      have hre : IsRealCoeff (coeffOf φ) :=
        isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφc)
      have hreal := ClassicalPart.propagatorCoeff_real hd s hs0 hsd j hm1 R MB Λ VB D 0 t
        (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ (coeffOf φ) hcm hre
      obtain ⟨C0, hC0, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd j hm1 R MB Λ VB
      obtain ⟨hsol, hw, -⟩ := hspec D 0 t (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ (coeffOf φ) hcm
      have hτ := ClassicalAux.mem_Icc_sub t (show u ∈ Set.Icc 0 t from ⟨hu, hut⟩)
      have hdj : (d : ℝ) / 2 + n < j := by
        rw [hj]; push_cast
        have h1 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have h2 : (0 : ℝ) < mStar d := by have := ClassicalPart.three_le_mStar d; exact_mod_cast (by omega)
        have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      obtain ⟨Cn, hCn⟩ := toFun_isCk_le n (j : ℝ) hdj
      exact (hCn _ (hw.1 _ hτ) (hreal _ hτ)).1
    exact contDiff_infty.2 hn
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) (hu.trans hut)
    have hu0 : u = 0 := le_antisymm (ht0 ▸ hut) hu
    subst ht0; subst hu0
    rw [frozen_self_pos hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos φ hφ 0 le_rfl]
    exact hφ

theorem frozen_semigroup (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (r σ t : ℝ) (hr : 0 ≤ r) (hrσ : r ≤ σ) (hσt : σ ≤ t) :
    propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r t φ =
      propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r σ
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) σ t φ) := by
  rcases hσt.eq_or_lt with h | h
  · subst h
    rw [frozen_self_pos hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos φ hφ σ (hr.trans hrσ)]
  · have ht : 0 < t := lt_of_le_of_lt (hr.trans hrσ) h
    have hφc : Continuous φ := ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hφ 1)
    obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρ hpos (mStar d)
    exact propagator_semigroup hd s hs0 hsd (mStar d) le_rfl R MB Λ VB (mfData d s hs0 hsd V β hβ) 0 t
      (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ φ hφc (memSobolev_of_isSmooth hφ _) r σ hr hrσ h


theorem frozen_coeff_cont (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (k : NonzeroLattice d) (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => Torus.funRealCoeff
      (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) p.2 p.1 ψ) k)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
  set D := mfData d s hs0 hsd V β hβ with hD
  obtain ⟨T', hT'def⟩ : ∃ T' : ℝ, T' = T + 1 := ⟨_, rfl⟩
  have hT' : 0 < T' := by rw [hT'def]; linarith
  obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρ hpos (mStar d)
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd (mStar d) le_rfl R MB Λ VB
  have hψc : Continuous ψ := ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hψ 1)
  obtain ⟨hF, -⟩ := hmain D 0 T' (fun _ => ρβ) (hA 0 T' hT') T' ⟨hT', le_rfl⟩ ψ hψc
    (memSobolev_of_isSmooth hψ _)
  set F : ℝ → Torus d → ℝ := fun r x =>
    toFun (propagatorCoeff D (fun _ => ρβ) (mStar d) T' (coeffOf ψ) (T' - r)) x with hFdef
  -- time-homogeneity
  have hid : ∀ p ∈ {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T},
      propagator D (fun _ => ρβ) p.2 p.1 ψ = F (p.2 + (T' - p.1)) := by
    rintro ⟨t, u⟩ ⟨hu, hut, htT⟩
    simp only at hu hut htT ⊢
    by_cases ht : 0 < t
    · have htT' : t ≤ T' := by linarith
      have hG := shift_classical D ρβ htT' hF
      have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => ρβ) t ψ f := ⟨_, hG⟩
      have hu' := classical_adjoint_unique hd s hs0 hsd (mStar d) (by have := ClassicalPart.three_le_mStar d; omega)
        R MB Λ VB D 0 t (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ ψ _ _ hex.choose_spec hG u ⟨hu, hut⟩
      simp only [propagator, hex, dite_true]
      rw [hu']
    · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) (hu.trans hut)
      have hu0 : u = 0 := le_antisymm (ht0 ▸ hut) hu
      subst ht0; subst hu0
      rw [frozen_self_pos hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos ψ hψ 0 le_rfl]
      have := hF.terminal
      simp only [zero_add, sub_zero]
      exact this.symm
  -- continuity of the coefficient of the classical solution in the time variable
  have hFc := continuous_F hF
  have hcontF : Continuous fun r : Set.Icc (0 : ℝ) T' => Torus.funRealCoeff (F r) k := by
    have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
      (f := fun (r : Set.Icc (0 : ℝ) T') (y : Torus d) => Torus.realMode k y * F r y)
      (((Torus.continuous_realMode k).comp continuous_snd).mul hFc) isCompact_univ
    simp only [MeasureTheory.Measure.restrict_univ] at this
    exact this
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ => Torus.funRealCoeff (F (p.2 + (T' - p.1))) k) ?_
    (fun p hp => by rw [hid p hp])
  rw [continuousOn_iff_continuous_domRestrict]
  have hmem : ∀ p : {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T},
      p.1.2 + (T' - p.1.1) ∈ Set.Icc (0 : ℝ) T' := fun p =>
    ⟨by linarith [p.2.1, p.2.2.2, hT'def], by linarith [p.2.1, p.2.2.1, p.2.2.2, hT'def]⟩
  exact hcontF.comp (Continuous.subtype_mk
    ((continuous_snd.comp continuous_subtype_val).add
      (continuous_const.sub (continuous_fst.comp continuous_subtype_val))) hmem)

end HRS.Uniform.Q48e
