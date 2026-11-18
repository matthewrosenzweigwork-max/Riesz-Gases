import HRS.PDE.MeanFieldAprioriClassical
import HRS.PDE.MeanFieldAprioriClassicalOn
import HRS.PDE.Galerkin
import HRS.PDE.TorusCalculus

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP1b
(the `Φ`-identity; package MF-01, plan `MeanFieldAprioriPlan.md`)

Section 1: differentiation of a parameter integral on the torus (generic in the family).
Section 2: calculus on the torus for compositions `Φ ∘ ρ`.
Section 3: the integration-by-parts identities for a fixed `ρ ∈ C²` (`integral_deriv_mul_rhs`,
`integral_pow_rhs`).  These two need the extra hypothesis `hVK : MemHs K (coeffOf V)` (see the
correction `toFun_mfRhsCoeff_eq'` of AP1a).
Section 4: time derivatives along a solution (`*_global` for global solutions on `[0,∞)`, the
unsuffixed names are the time-local versions of the amendment, §2.2, at the end of the file).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-! ### Section 1: differentiation of a parameter integral -/

theorem hasDerivAt_integral_param (f f' : ℝ → Torus d → ℝ) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hf : ContinuousOn (fun p : ℝ × Torus d => f p.1 p.2) (Icc a b ×ˢ univ))
    (hf' : ContinuousOn (fun p : ℝ × Torus d => f' p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ τ ∈ Ioo a b, ∀ x, HasDerivAt (fun σ => f σ x) (f' τ x) τ) :
    HasDerivAt (fun τ => ∫ x, f τ x) (∫ x, f' t x) t := by
  have hK : IsCompact (Icc a b ×ˢ (univ : Set (Torus d))) := isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf'
  have hmemK : ∀ τ ∈ Icc a b, ∀ x : Torus d, (τ, x) ∈ Icc a b ×ˢ (univ : Set (Torus d)) :=
    fun τ hτ x => ⟨hτ, mem_univ _⟩
  have hcf : ∀ τ ∈ Icc a b, Continuous fun x : Torus d => f τ x := fun τ hτ =>
    hf.comp_continuous (Continuous.prodMk_right τ) (hmemK τ hτ)
  have hcf' : ∀ τ ∈ Icc a b, Continuous fun x : Torus d => f' τ x := fun τ hτ =>
    hf'.comp_continuous (Continuous.prodMk_right τ) (hmemK τ hτ)
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
    (𝕜 := ℝ) (x₀ := t) (s := Ioo a b) (F := f) (F' := f') (bound := fun _ => C)
    (Ioo_mem_nhds ht.1 ht.2)
    (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
      exact (hcf τ (Ioo_subset_Icc_self hτ)).aestronglyMeasurable)
    ((hcf t htI).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hcf' t htI).aestronglyMeasurable
    (Eventually.of_forall fun x τ hτ => by
      have := hC (τ, x) ⟨Ioo_subset_Icc_self hτ, mem_univ _⟩
      simpa using this)
    (integrable_const C)
    (Eventually.of_forall fun x τ hτ => hd τ hτ x)
  exact key.2

/-! ### Section 2: calculus on the torus for compositions -/

theorem isCk_comp {k : ℕ} (Φ : ℝ → ℝ) (I : Set ℝ) (hΦ : ContDiffOn ℝ k Φ I) (u : Torus d → ℝ)
    (hu : Torus.IsCk k u) (hrange : ∀ x, u x ∈ I) : Torus.IsCk k (fun x => Φ (u x)) := by
  unfold Torus.IsCk at *
  have e : Torus.lift (fun x => Φ (u x)) = Φ ∘ Torus.lift u := rfl
  rw [e]
  have := hΦ.comp hu.contDiffOn (s := univ) (fun y _ => hrange (Torus.mk y))
  exact contDiffOn_univ.mp this

theorem partialDeriv_comp (j : Fin d) (Φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ 1 Φ I) (u : Torus d → ℝ) (hu : Torus.IsCk 1 u) (hrange : ∀ x, u x ∈ I)
    (x : Torus d) :
    Torus.partialDeriv j (fun y => Φ (u y)) x = deriv Φ (u x) * Torus.partialDeriv j u x := by
  have hΦd : DifferentiableAt ℝ Φ (Torus.lift u (Torus.rep x)) := by
    have : Torus.lift u (Torus.rep x) = u x := by simp [Torus.lift, Torus.mk_rep]
    rw [this]
    exact (hΦ.differentiableOn one_ne_zero).differentiableAt (hI.mem_nhds (hrange x))
  have e : Torus.lift (fun y => Φ (u y)) = Φ ∘ Torus.lift u := rfl
  unfold Torus.partialDeriv
  rw [e, fderiv_comp _ hΦd (hu.differentiable one_ne_zero _)]
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : ∀ w : ℝ, fderiv ℝ Φ (Torus.lift u (Torus.rep x)) w =
      deriv Φ (Torus.lift u (Torus.rep x)) * w := fun w => by
    conv_lhs => rw [show w = w • (1 : ℝ) by simp]
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [h1]
  simp [Torus.lift, Torus.mk_rep]

theorem norm_grad_sq (u : Torus d → ℝ) (x : Torus d) :
    ‖Torus.grad u x‖ ^ 2 = ∑ j, (Torus.partialDeriv j u x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [MFAux.grad_apply]

theorem inner_grad_grad (u w : Torus d → ℝ) (x : Torus d) :
    inner ℝ (Torus.grad u x) (Torus.grad w x) =
      ∑ j, Torus.partialDeriv j u x * Torus.partialDeriv j w x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [MFAux.grad_apply, mul_comm]

theorem continuous_of_isCk' {j : ℕ} {u : Torus d → ℝ} (hu : Torus.IsCk j u) (hj : 1 ≤ j) :
    Continuous u := MFAux.continuous_of_isCk (hu.of_le (by exact_mod_cast hj))

/-- `W = V + g ⋆ ρ` is `C²`. -/
theorem isCk_two_Wpot (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (c : Coeff d)
    (hc : MemHs K c) (hreal : IsRealCoeff c) : Torus.IsCk 2 (Wpot d s V c) :=
  isCk_add V _ hV (riesz_isCk hd s hs0 hsd 2 K (by simpa using hK) c hc hreal).1

/-- Integration by parts: `∫ Φ'(ρ)(νΔρ + Div(ρ∇W)) = -ν ∫ Φ''(ρ)|∇ρ|² - ∫ Φ''(ρ) ρ ∇ρ·∇W`.
**Corrected variant** of the plan statement `integral_deriv_mul_rhs`: (1) extra hypothesis
`hVK : MemHs K (coeffOf V)` (needed for `toFun_mfRhsCoeff_eq'`); (2) the first integral is
parenthesised: in the plan statement `-ν * ∫ x, A x - ∫ x, B x` parses as `-ν * ∫ x, (A x - ∫ B)`,
which is false. -/
theorem integral_deriv_mul_rhs' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V)
    (hVK : MemHs K (coeffOf V)) (ν : ℝ)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (Φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ 2 Φ I) (hrange : ∀ x, toFun c x ∈ I) :
    ∫ x, deriv Φ (toFun c x) * toFun (mfRhsCoeff d s V ν c) x =
      -ν * (∫ x, deriv (deriv Φ) (toFun c x) * ‖Torus.grad (toFun c) x‖ ^ 2) -
        ∫ x, deriv (deriv Φ) (toFun c x) * toFun c x *
          inner ℝ (Torus.grad (toFun c) x) (Torus.grad (Wpot d s V c) x) := by
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hW1 : Torus.IsCk 1 (Wpot d s V c) := hW2.of_le (by norm_num)
  set ρ := toFun c with hρdef
  set W := Wpot d s V c with hWdef
  set G := deriv Φ with hG
  have hG1 : ContDiffOn ℝ 1 G I := hΦ.deriv_of_isOpen hI (by norm_num)
  have hGc : ContinuousOn (deriv G) I := hG1.continuousOn_deriv_of_isOpen hI le_rfl
  have hG0 : ContinuousOn G I := hG1.continuousOn
  have hρc : Continuous ρ := continuous_of_isCk' hρ1 le_rfl
  have hA : Torus.IsCk 1 (fun x => G (ρ x)) := isCk_comp G I hG1 ρ hρ1 hrange
  have hAc : Continuous fun x => G (ρ x) := hG0.comp_continuous hρc hrange
  have hBc : Continuous fun x => deriv G (ρ x) := hGc.comp_continuous hρc hrange
  have hdA : ∀ j x, Torus.partialDeriv j (fun y => G (ρ y)) x =
      deriv G (ρ x) * Torus.partialDeriv j ρ x := fun j x =>
    partialDeriv_comp j G I hI hG1 ρ hρ1 hrange x
  have hpρ : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => continuous_partialDeriv j _ hρ1
  have hpW : ∀ j, Continuous (Torus.partialDeriv j W) := fun j => continuous_partialDeriv j _ hW1
  have hpρ1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ρ) := fun j => isCk_one_partialDeriv j _ hρ2
  have hP1 : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j W y) := fun j =>
    MFAux.isCk_mul_partialDeriv _ _ hρ1 hW2 j
  have hpP : ∀ j, Continuous (Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y)) :=
    fun j => continuous_partialDeriv j _ (hP1 j)
  have hpp : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j ρ)) := fun j =>
    continuous_partialDeriv j _ (hpρ1 j)
  have hlap : ∀ x, Torus.laplacian ρ x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) x :=
    fun x => laplacian_eq_sum _ hρ2 x
  -- the two integrations by parts
  have ibp1 : ∀ j, ∫ x, G (ρ x) * Torus.partialDeriv j (Torus.partialDeriv j ρ) x =
      -∫ x, deriv G (ρ x) * (Torus.partialDeriv j ρ x) ^ 2 := by
    intro j
    have := integral_partialDeriv_mul j (Torus.partialDeriv j ρ) (fun y => G (ρ y)) (hpρ1 j) hA
    simp_rw [hdA] at this
    have e1 : ∀ x, G (ρ x) * Torus.partialDeriv j (Torus.partialDeriv j ρ) x =
        Torus.partialDeriv j (Torus.partialDeriv j ρ) x * G (ρ x) := fun x => mul_comm _ _
    simp_rw [e1, this]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have ibp2 : ∀ j, ∫ x, G (ρ x) * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x =
      -∫ x, deriv G (ρ x) * ρ x * (Torus.partialDeriv j ρ x * Torus.partialDeriv j W x) := by
    intro j
    have := integral_partialDeriv_mul j (fun y => ρ y * Torus.partialDeriv j W y) (fun y => G (ρ y))
      (hP1 j) hA
    simp_rw [hdA] at this
    have e1 : ∀ x, G (ρ x) * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x =
        Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x * G (ρ x) :=
      fun x => mul_comm _ _
    simp_rw [e1, this]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hF : ∀ x, toFun (mfRhsCoeff d s V ν c) x = ν * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) x +
      ∑ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x := by
    intro x
    rw [toFun_mfRhsCoeff_eq' hd s hs0 hsd K hK V hV hVK ν c hc hreal x, hlap x]
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ x, G (ρ x) * toFun (mfRhsCoeff d s V ν c) x
      = ∫ x, (ν * (∑ j, G (ρ x) * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) +
          ∑ j, G (ρ x) * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hF, mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ν * (∑ j, ∫ x, G (ρ x) * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) +
          ∑ j, ∫ x, G (ρ x) * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x := by
        have c1 : ∀ j, Continuous fun x => G (ρ x) * Torus.partialDeriv j (Torus.partialDeriv j ρ) x :=
          fun j => hAc.mul (hpp j)
        have c2 : ∀ j, Continuous fun x => G (ρ x) *
            Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x :=
          fun j => hAc.mul (hpP j)
        have i1 : Integrable fun x => ν * (∑ j, G (ρ x) * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) :=
          hint _ (continuous_const.mul (continuous_finsetSum _ fun j _ => c1 j))
        have i2 : Integrable fun x => ∑ j, G (ρ x) *
            Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x :=
          hint _ (continuous_finsetSum _ fun j _ => c2 j)
        rw [integral_add i1 i2, integral_const_mul, integral_finsetSum _ (fun j _ => hint _ (c1 j)),
          integral_finsetSum _ (fun j _ => hint _ (c2 j))]
    _ = _ := by
        have e1 : ∫ x, deriv G (ρ x) * ‖Torus.grad ρ x‖ ^ 2 =
            ∑ j, ∫ x, deriv G (ρ x) * (Torus.partialDeriv j ρ x) ^ 2 := by
          simp_rw [norm_grad_sq, Finset.mul_sum]
          exact integral_finsetSum _ (fun j _ => hint _ (hBc.mul ((hpρ j).pow 2)))
        have e2 : ∫ x, deriv G (ρ x) * ρ x * inner ℝ (Torus.grad ρ x) (Torus.grad W x) =
            ∑ j, ∫ x, deriv G (ρ x) * ρ x * (Torus.partialDeriv j ρ x * Torus.partialDeriv j W x) := by
          simp_rw [inner_grad_grad, Finset.mul_sum]
          exact integral_finsetSum _ (fun j _ => hint _ ((hBc.mul hρc).mul ((hpρ j).mul (hpW j))))
        rw [e1, e2]
        simp_rw [ibp1, ibp2]
        simp only [Finset.sum_neg_distrib, Finset.mul_sum, mul_neg, neg_mul]
        rw [sub_eq_add_neg]

/-- The power identity used for the upper bound: for `p ≥ 2`,
`∫ ρ^{p-1}(νΔρ + Div(ρ∇W)) = -ν(p-1) ∫ ρ^{p-2}|∇ρ|² + ((p-1)/p) ∫ ρ^p ΔW`.
**Corrected variant** of the plan statement `integral_pow_rhs` (extra hypothesis `hVK` and
parenthesisation of the first integral; as printed in the plan, the first `∫ x, …  + …` swallows
the second summand). -/
theorem integral_pow_rhs' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V)
    (hVK : MemHs K (coeffOf V)) (ν : ℝ)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (p : ℕ) (hp : 2 ≤ p) :
    ∫ x, toFun c x ^ (p - 1) * toFun (mfRhsCoeff d s V ν c) x =
      -ν * (p - 1) * (∫ x, toFun c x ^ (p - 2) * ‖Torus.grad (toFun c) x‖ ^ 2) +
        ((p : ℝ) - 1) / p * ∫ x, toFun c x ^ p * Torus.laplacian (Wpot d s V c) x := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hqq : (q + 2 - 1 : ℕ) = q + 1 := by omega
  have hq2 : (q + 2 - 2 : ℕ) = q := by omega
  rw [hqq, hq2]
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hW1 : Torus.IsCk 1 (Wpot d s V c) := hW2.of_le (by norm_num)
  set ρ := toFun c with hρdef
  set W := Wpot d s V c with hWdef
  have hρc : Continuous ρ := continuous_of_isCk' hρ1 le_rfl
  have hpρ : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => continuous_partialDeriv j _ hρ1
  have hpW : ∀ j, Continuous (Torus.partialDeriv j W) := fun j => continuous_partialDeriv j _ hW1
  have hpW1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j W) := fun j => isCk_one_partialDeriv j _ hW2
  have hpp : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j W)) := fun j =>
    continuous_partialDeriv j _ (hpW1 j)
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Φ = r ^ (q+2)
  set P : ℝ → ℝ := fun r => r ^ (q + 2) with hP
  have hPcd : ContDiff ℝ 2 P := by rw [hP]; fun_prop
  have hP2 : ContDiffOn ℝ 2 P univ := hPcd.contDiffOn
  have hP1 : deriv P = fun r => ((q + 2 : ℕ) : ℝ) * r ^ (q + 1) := by
    funext r; simp [hP]
  have hP2' : deriv (deriv P) = fun r => ((q + 2 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) * r ^ q) := by
    funext r
    rw [hP1]
    simp
  have key := integral_deriv_mul_rhs' hd s hs0 hsd K hK V hV hVK ν c hc hreal P univ isOpen_univ hP2
    (fun x => mem_univ _)
  rw [hP2', hP1] at key
  simp only at key
  -- the extra integration by parts
  have hPow1 : Torus.IsCk 1 (fun x => ρ x ^ (q + 2)) :=
    isCk_comp (k := 1) P univ (hPcd.of_le (by norm_num)).contDiffOn ρ hρ1 (fun x => mem_univ _)
  have hdP : ∀ j x, Torus.partialDeriv j (fun y => ρ y ^ (q + 2)) x =
      ((q + 2 : ℕ) : ℝ) * ρ x ^ (q + 1) * Torus.partialDeriv j ρ x := by
    intro j x
    have := partialDeriv_comp j P univ isOpen_univ (hPcd.of_le (by norm_num)).contDiffOn ρ hρ1
      (fun x => mem_univ _) x
    rw [hP1] at this
    exact this
  have ibp : ∀ j, ∫ x, ((q + 2 : ℕ) : ℝ) * ρ x ^ (q + 1) * Torus.partialDeriv j ρ x *
      Torus.partialDeriv j W x = -∫ x, ρ x ^ (q + 2) * Torus.partialDeriv j (Torus.partialDeriv j W) x := by
    intro j
    have := integral_partialDeriv_mul j (fun x => ρ x ^ (q + 2)) (Torus.partialDeriv j W) hPow1 (hpW1 j)
    simp_rw [hdP] at this
    exact this
  have hlapW : ∀ x, Torus.laplacian W x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j W) x :=
    fun x => laplacian_eq_sum _ hW2 x
  have A1 : ∫ x, ((q + 2 : ℕ) : ℝ) * ρ x ^ (q + 1) * toFun (mfRhsCoeff d s V ν c) x =
      ((q + 2 : ℕ) : ℝ) * ∫ x, ρ x ^ (q + 1) * toFun (mfRhsCoeff d s V ν c) x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have A2 : ∫ x, ((q + 2 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) * ρ x ^ q) * ‖Torus.grad ρ x‖ ^ 2 =
      ((q + 2 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) * ∫ x, ρ x ^ q * ‖Torus.grad ρ x‖ ^ 2 := by
    rw [mul_assoc, ← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have A3 : ∫ x, ((q + 2 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) * ρ x ^ q) * ρ x *
        inner ℝ (Torus.grad ρ x) (Torus.grad W x) =
      -(((q + 1 : ℕ) : ℝ) * ∫ x, ρ x ^ (q + 2) * Torus.laplacian W x) := by
    have e1 : ∀ x, ((q + 2 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) * ρ x ^ q) * ρ x *
        inner ℝ (Torus.grad ρ x) (Torus.grad W x) =
        ((q + 1 : ℕ) : ℝ) * ∑ j, (((q + 2 : ℕ) : ℝ) * ρ x ^ (q + 1) * Torus.partialDeriv j ρ x *
          Torus.partialDeriv j W x) := by
      intro x
      rw [inner_grad_grad, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e1]
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint _ ?_)]
    · simp_rw [ibp]
      simp_rw [hlapW, Finset.mul_sum]
      rw [integral_finsetSum _ (fun j _ => hint _ ?_)]
      · simp [Finset.sum_neg_distrib, Finset.mul_sum]
      · exact (hρc.pow _).mul (hpp j)
    · exact (((continuous_const.mul (hρc.pow _)).mul (hpρ j)).mul (hpW j))
  rw [A1, A2, A3] at key
  have hq0 : ((q + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at key ⊢
  field_simp
  linarith

/-! ### Section 4: time derivatives along a solution -/

/-- Generic form of `hasDerivAt_integral_comp`: `t ↦ ∫ Φ(u(t,x)) dx` for a family `u` that is
differentiable in time pointwise with jointly continuous `u`, `∂_t u` on `[a,b] × 𝕋^d`. -/
theorem hasDerivAt_integral_comp_gen (u u' : ℝ → Torus d → ℝ) (Φ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hΦ : ContDiffOn ℝ 1 Φ I) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hu : ContinuousOn (fun p : ℝ × Torus d => u p.1 p.2) (Icc a b ×ˢ univ))
    (hu' : ContinuousOn (fun p : ℝ × Torus d => u' p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ τ ∈ Ioo a b, ∀ x, HasDerivAt (fun σ => u σ x) (u' τ x) τ)
    (hrange : ∀ τ ∈ Icc a b, ∀ x, u τ x ∈ I) :
    HasDerivAt (fun τ => ∫ x, Φ (u τ x)) (∫ x, deriv Φ (u t x) * u' t x) t := by
  have hmaps : MapsTo (fun p : ℝ × Torus d => u p.1 p.2) (Icc a b ×ˢ univ) I :=
    fun p hp => hrange p.1 hp.1 p.2
  refine hasDerivAt_integral_param (fun τ x => Φ (u τ x)) (fun τ x => deriv Φ (u τ x) * u' τ x) ht
    (hΦ.continuousOn.comp hu hmaps)
    ((hΦ.continuousOn_deriv_of_isOpen hI le_rfl |>.comp hu hmaps).mul hu') ?_
  intro τ hτ x
  have hΦd : DifferentiableAt ℝ Φ (u τ x) :=
    (hΦ.differentiableOn one_ne_zero).differentiableAt (hI.mem_nhds (hrange τ (Ioo_subset_Icc_self hτ) x))
  exact hΦd.hasDerivAt.comp τ (hd τ hτ x)

theorem hasDerivAt_integral_comp_global (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : MFSolReal d s V ν K ρ₀ ρc) (Φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ 2 Φ I) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hrange : ∀ t ∈ Set.Icc a b, ∀ x, mfPath ρc t x ∈ I) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun τ => ∫ x, Φ (mfPath ρc τ x))
      (∫ x, deriv Φ (mfPath ρc t x) * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  have _ := hab
  obtain ⟨h1, h2⟩ := continuousOn_mfPath_prod hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hsub : Icc a b ×ˢ (univ : Set (Torus d)) ⊆ Ici 0 ×ˢ univ :=
    prod_mono (fun τ hτ => le_trans ha hτ.1) subset_rfl
  exact hasDerivAt_integral_comp_gen (mfPath ρc) (fun τ => toFun (mfRhsCoeff d s V ν (ρc τ))) Φ I hI
    (hΦ.of_le (by norm_num)) ht (h1.mono hsub) (h2.mono hsub)
    (fun τ hτ x => hasDerivAt_mfPath hd s hs0 hsd K hK V ρ₀ hV ν ρc H x
      (lt_of_le_of_lt ha hτ.1)) hrange

/-- Derivative of `∫ V ρ`. -/
theorem hasDerivAt_integral_V_global (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : MFSolReal d s V ν K ρ₀ ρc) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => ∫ x, V x * mfPath ρc τ x)
      (∫ x, V x * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  obtain ⟨h1, h2⟩ := continuousOn_mfPath_prod hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  have hVc : Continuous V := continuous_of_isCk' hV1 le_rfl
  have hsub : Icc (t / 2) (2 * t) ×ˢ (univ : Set (Torus d)) ⊆ Ici 0 ×ˢ univ :=
    prod_mono (fun τ hτ => le_trans (by linarith) hτ.1) subset_rfl
  have htm : t ∈ Ioo (t / 2) (2 * t) := ⟨by linarith, by linarith⟩
  refine hasDerivAt_integral_param (fun τ x => V x * mfPath ρc τ x)
    (fun τ x => V x * toFun (mfRhsCoeff d s V ν (ρc τ)) x) htm ?_ ?_ ?_
  · exact (hVc.comp_continuousOn (continuous_snd.continuousOn)).mul (h1.mono hsub)
  · exact (hVc.comp_continuousOn (continuous_snd.continuousOn)).mul (h2.mono hsub)
  · intro τ hτ x
    exact (hasDerivAt_mfPath hd s hs0 hsd K hK V ρ₀ hV ν ρc H x
      (lt_of_le_of_lt (by linarith) hτ.1)).const_mul (V x)

/-! ### Section 5: the interaction energy -/

/-- Parseval for continuous real functions: `∑_j û(-j) v̂(j) = ∫ u v`. -/
theorem hasSum_pairing' {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v) :
    HasSum (fun j : Lattice d => coeffOf u (-j) * coeffOf v j) (((∫ x, u x * v x : ℝ)) : ℂ) := by
  have hmem : ∀ w : Torus d → ℝ, Continuous w → MemLp (fun x => ((w x : ℝ) : ℂ)) 2 volume :=
    fun w hw => (Complex.continuous_ofReal.comp hw).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := hasSum_parseval (fun x => ((u x : ℝ) : ℂ)) (fun x => ((v x : ℝ) : ℂ)) (hmem u hu) (hmem v hv)
  have hr := isRealCoeff_coeffOf u (hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have e1 : ∀ n : Lattice d, conj (Torus.funFourierCoeff (fun x => ((u x : ℝ) : ℂ)) n) *
      Torus.funFourierCoeff (fun x => ((v x : ℝ) : ℂ)) n = coeffOf u (-n) * coeffOf v n := fun n => by
    show conj (coeffOf u n) * coeffOf v n = _
    rw [hr n]
  have e2 : ∫ t, conj (((u t : ℝ) : ℂ)) * ((v t : ℝ) : ℂ) = (((∫ x, u x * v x : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  simp_rw [e1, e2] at h
  exact h

/-- `∑' k, 1/⟨k⟩^{2m}` converges for `m > d/2`. -/
theorem summable_sobWeight_neg (m : ℝ) (hm : (d : ℝ) / 2 < m) :
    Summable fun k : Lattice d => sobWeight (-m) k := by
  rw [Torus.summable_lattice_iff]
  refine (summable_jp_rpow (d := d) m (by linarith)).congr fun k => ?_
  rw [sobWeight_eq_jp]; ring_nf

theorem sobWeight_le_of_le {m n : ℝ} (hmn : m ≤ n) (k : Lattice d) : sobWeight m k ≤ sobWeight n k := by
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Lattice.enorm k), Real.pi_pos]) hmn

/-- Generic form of `hasDerivAt_interaction`: the interaction energy `½ ∑ ĝ(k)|ρ̂_τ(k)|²` of a
family of real coefficient sequences, modewise differentiable on `(a,b)` with derivatives `F τ`
and uniform `H^K`/`H^{K-2}` bounds. -/
theorem hasDerivAt_interaction_gen (s : ℝ) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (ρc F : ℝ → Coeff d) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hmem : ∀ τ ∈ Ioo a b, MemHs K (ρc τ)) (hreal : ∀ τ ∈ Ioo a b, IsRealCoeff (ρc τ))
    (hFmem : ∀ τ ∈ Ioo a b, MemHs (K - 2) (F τ)) (hFreal : ∀ τ ∈ Ioo a b, IsRealCoeff (F τ))
    (hder : ∀ τ ∈ Ioo a b, ∀ k, HasDerivAt (fun σ => ρc σ k) (F τ k) τ)
    (B : ℝ) (hB : ∀ τ ∈ Ioo a b, hsNorm K (ρc τ) ≤ B ∧ hsNorm (K - 2) (F τ) ≤ B) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖ρc τ k‖ ^ 2).re)
      (∫ x, riesz d s (ρc t) x * toFun (F t) x) t := by
  have hKd : (d : ℝ) / 2 < K - 2 := by linarith
  set Rc : ℝ := |rieszConst d s| with hRc
  have hRc0 : 0 ≤ Rc := abs_nonneg _
  have hgR : ∀ k, |rieszCoeff d s k| ≤ Rc := fun k => abs_rieszCoeff_leU hsd k
  set g : Lattice d → ℝ → ℝ := fun k τ => rieszCoeff d s k * ‖ρc τ k‖ ^ 2 with hg
  set g' : Lattice d → ℝ → ℝ := fun k τ => rieszCoeff d s k * (2 * inner ℝ (ρc τ k) (F τ k))
    with hg'
  have hgd : ∀ k, ∀ τ ∈ Ioo a b, HasDerivAt (g k) (g' k τ) τ := fun k τ hτ =>
    ((hder τ hτ k).norm_sq).const_mul _
  set u : Lattice d → ℝ := fun k => 2 * Rc * B ^ 2 * sobWeight (-(K - 2)) k with hu
  have hus : Summable u := (summable_sobWeight_neg (K - 2) hKd).mul_left _
  have hmode : ∀ τ ∈ Ioo a b, ∀ k, ‖ρc τ k‖ * ‖F τ k‖ ≤ B ^ 2 * sobWeight (-(K - 2)) k := by
    intro τ hτ k
    obtain ⟨hB1, hB2⟩ := hB τ hτ
    have hw : 0 < sobWeight (K - 2) k := sobWeight_pos _ k
    have hwK : sobWeight (K - 2) k ≤ sobWeight K k := sobWeight_le_of_le (by linarith) k
    have h1 : ‖ρc τ k‖ * Real.sqrt (sobWeight (K - 2) k) ≤ B :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hwK) (norm_nonneg _)).trans
        ((Aux.norm_coeff_mul_sqrt_le K (hmem τ hτ) k).trans hB1)
    have h2 : ‖F τ k‖ * Real.sqrt (sobWeight (K - 2) k) ≤ B :=
      (Aux.norm_coeff_mul_sqrt_le (K - 2) (hFmem τ hτ) k).trans hB2
    have h3 : (‖ρc τ k‖ * Real.sqrt (sobWeight (K - 2) k)) * (‖F τ k‖ * Real.sqrt (sobWeight (K - 2) k))
        ≤ B * B :=
      mul_le_mul h1 h2 (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
        ((mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)).trans h1)
    have h4 : (‖ρc τ k‖ * Real.sqrt (sobWeight (K - 2) k)) * (‖F τ k‖ * Real.sqrt (sobWeight (K - 2) k))
        = ‖ρc τ k‖ * ‖F τ k‖ * sobWeight (K - 2) k := by
      have := Real.mul_self_sqrt hw.le
      calc _ = ‖ρc τ k‖ * ‖F τ k‖ * (Real.sqrt (sobWeight (K - 2) k) * Real.sqrt (sobWeight (K - 2) k)) := by ring
        _ = _ := by rw [this]
    have hneg : sobWeight (-(K - 2)) k = (sobWeight (K - 2) k)⁻¹ := by
      unfold sobWeight
      rw [Real.rpow_neg (by positivity)]
    rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hw]
    nlinarith
  have hbound : ∀ k, ∀ τ ∈ Ioo a b, ‖g' k τ‖ ≤ u k := by
    intro k τ hτ
    have hin : |inner ℝ (ρc τ k) (F τ k)| ≤ ‖ρc τ k‖ * ‖F τ k‖ := abs_real_inner_le_norm _ _
    calc ‖g' k τ‖ = |rieszCoeff d s k| * (2 * |inner ℝ (ρc τ k) (F τ k)|) := by
          simp only [hg', Real.norm_eq_abs, abs_mul]
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ Rc * (2 * (B ^ 2 * sobWeight (-(K - 2)) k)) := by
          gcongr
          · exact hgR k
          · exact hin.trans (hmode τ hτ k)
      _ = u k := by simp only [hu]; ring
  have hg0 : Summable fun k => g k t := by
    have hm0 : MemHs 0 (ρc t) := Aux.memHs_mono (by linarith) (hmem t ht)
    have : Summable fun k => Rc * ‖ρc t k‖ ^ 2 := by
      simpa [MemHs, Aux.sobWeight_zero_aux] using hm0.mul_left Rc
    refine Summable.of_norm_bounded this fun k => ?_
    simp only [hg, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    exact mul_le_mul_of_nonneg_right (hgR k) (sq_nonneg _)
  have key := hasDerivAt_tsum_of_isPreconnected hus isOpen_Ioo isPreconnected_Ioo hgd hbound ht hg0 ht
  have key2 := key.const_mul (1 / 2 : ℝ)
  have hfun : (fun τ => (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖ρc τ k‖ ^ 2).re) =
      fun τ => (1 / 2 : ℝ) * ∑' k, g k τ := by
    funext τ
    congr 1
    have : (∑' k, (rieszCoeff d s k : ℂ) * ‖ρc τ k‖ ^ 2) = ((∑' k, g k τ : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun k => ?_
      simp [hg]
    rw [this, Complex.ofReal_re]
  rw [hfun]
  convert key2 using 1
  -- the value of the derivative
  have hsF : Summable fun k => ‖F t k‖ := summable_norm_of_memHs (K - 2) hKd _ (hFmem t ht)
  have hrm := hs_rieszMult s hsd K (ρc t) (hmem t ht)
  have hsR : Summable fun k => ‖rieszMult d s (ρc t) k‖ :=
    summable_norm_of_memHs K (by linarith) _ hrm.1
  have hrr := isRealCoeff_rieszMult s (ρc t) (hreal t ht)
  have hcoR : coeffOf (riesz d s (ρc t)) = rieszMult d s (ρc t) := coeffOf_toFun _ hrr hsR
  have hcoF : coeffOf (toFun (F t)) = F t := coeffOf_toFun _ (hFreal t ht) hsF
  have hcu : Continuous (riesz d s (ρc t)) := HRS.PDE.MFProduct.continuous_toFun _ hsR
  have hcv : Continuous (toFun (F t)) := HRS.PDE.MFProduct.continuous_toFun _ hsF
  have hP := hasSum_pairing' hcu hcv
  rw [hcoR, hcoF] at hP
  have hRe := Complex.reCLM.hasSum hP
  have hterm : ∀ j : Lattice d, (Complex.reCLM ∘ fun j : Lattice d =>
      rieszMult d s (ρc t) (-j) * F t j) j = rieszCoeff d s j * inner ℝ (ρc t j) (F t j) := by
    intro j
    show ((rieszCoeff d s (-j) : ℝ) * ρc t (-j) * F t j : ℂ).re = _
    rw [rieszCoeff_neg, hreal t ht j, mul_assoc, Complex.re_ofReal_mul, Complex.inner,
      mul_comm (F t j)]
  have hRe' : HasSum (fun j : Lattice d => rieszCoeff d s j * inner ℝ (ρc t j) (F t j))
      (∫ x, riesz d s (ρc t) x * toFun (F t) x) := by
    have e : (fun j : Lattice d => rieszCoeff d s j * inner ℝ (ρc t j) (F t j)) =
        Complex.reCLM ∘ fun j : Lattice d => rieszMult d s (ρc t) (-j) * F t j :=
      funext fun j => (hterm j).symm
    rw [e]
    rwa [Complex.reCLM_apply, Complex.ofReal_re] at hRe
  rw [← hRe'.tsum_eq]
  have : ∑' n, g' n t = 2 * ∑' n, rieszCoeff d s n * inner ℝ (ρc t n) (F t n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by simp only [hg']; ring
  rw [this]; ring

/-- The mean-field right-hand side maps real coefficient sequences to real ones
(`V` integrable, e.g. continuous). -/
theorem isRealCoeff_mfRhsCoeff (s : ℝ) (V : Torus d → ℝ) (hV : Integrable V) (ν : ℝ) (c : Coeff d)
    (hc : IsRealCoeff c) : IsRealCoeff (mfRhsCoeff d s V ν c) := by
  have hVr : IsRealCoeff (coeffOf V) := isRealCoeff_coeffOf V hV
  have hm : ∀ j : Fin d, IsRealCoeff (fun k' => derivCoeff j (coeffOf V) k' +
      gradRieszCoeff d s j c k') := by
    intro j k
    have h1 := isRealCoeff_derivCoeff j _ hVr k
    have h2 : gradRieszCoeff d s j c (-k) = conj (gradRieszCoeff d s j c k) :=
      isRealCoeff_derivCoeff j _ (isRealCoeff_rieszMult s c hc) k
    show derivCoeff j (coeffOf V) (-k) + gradRieszCoeff d s j c (-k) =
      conj (derivCoeff j (coeffOf V) k + gradRieszCoeff d s j c k)
    rw [h1, h2, map_add]
  have hmul : ∀ j : Fin d, IsRealCoeff (derivCoeff j (mulCoeff c (fun k' => derivCoeff j (coeffOf V) k' +
      gradRieszCoeff d s j c k'))) := by
    intro j
    refine isRealCoeff_derivCoeff j _ ?_
    have hmj := hm j
    rw [HRS.PDE.isRealCoeff_iff_reflConj] at hmj ⊢
    rw [← HRS.PDE.mulCoeff_reflConj _ _ hc, hmj]
  intro k
  have h1 := isRealCoeff_laplaceCoeff c hc k
  simp only [mfRhsCoeff, map_add, map_mul, Complex.conj_ofReal, h1, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (hmul j k)

/-- Derivative of the interaction energy `½ ∑ ĝ(k)|ρ̂(k)|²`: `∫ (g⋆ρ) ∂_tρ`. -/
theorem hasDerivAt_interaction_global (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : MFSolReal d s V ν K ρ₀ ρc) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖ρc τ k‖ ^ 2).re)
      (∫ x, riesz d s (ρc t) x * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  have hVi : Integrable V :=
    (continuous_of_isCk' hV1 le_rfl).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr := rhs_continuousInHsOn hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol
  obtain ⟨B1, hB1⟩ := exists_bound_of_continuousInHsOn (K : ℝ) ρc (2 * t) H.sol.cont
  obtain ⟨B2, hB2⟩ := exists_bound_of_continuousInHsOn ((K : ℝ) - 2)
    (fun σ => mfRhsCoeff d s V ν (ρc σ)) (2 * t) hr
  have hpos : ∀ τ ∈ Ioo (t / 2) (2 * t), 0 < τ := fun τ hτ => by linarith [hτ.1]
  refine hasDerivAt_interaction_gen s hsd K hK ρc (fun σ => mfRhsCoeff d s V ν (ρc σ))
    (a := t / 2) (b := 2 * t) ⟨by linarith, by linarith⟩
    (fun τ hτ => H.sol.cont.1 τ (hpos τ hτ).le) (fun τ hτ => H.real τ (hpos τ hτ).le)
    (fun τ hτ => hr.1 τ (hpos τ hτ).le)
    (fun τ hτ => isRealCoeff_mfRhsCoeff s V hVi ν _ (H.real τ (hpos τ hτ).le))
    (fun τ hτ k => hasDerivAt_coeff hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol k (hpos τ hτ))
    (max B1 B2) (fun τ hτ => ⟨(hB1 τ ⟨(hpos τ hτ).le, hτ.2.le⟩).trans (le_max_left _ _),
      (hB2 τ ⟨(hpos τ hτ).le, hτ.2.le⟩).trans (le_max_right _ _)⟩)

/-! ### Section 6: time-local versions (amendment §2.2) -/

/-- `hasDerivAt_integral_comp` for a real solution on `[0,T]`, `[a,b] ⊆ [0,T]`. -/
theorem hasDerivAt_integral_comp (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) (Φ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hΦ : ContDiffOn ℝ 2 Φ I) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbT : b ≤ T)
    (hrange : ∀ t ∈ Set.Icc a b, ∀ x, mfPath ρc t x ∈ I) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun τ => ∫ x, Φ (mfPath ρc τ x))
      (∫ x, deriv Φ (mfPath ρc t x) * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  have _ := hab
  obtain ⟨h1, h2⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hsub : Icc a b ×ˢ (univ : Set (Torus d)) ⊆ Icc 0 T ×ˢ univ :=
    prod_mono (fun τ hτ => ⟨le_trans ha hτ.1, hτ.2.trans hbT⟩) subset_rfl
  exact hasDerivAt_integral_comp_gen (mfPath ρc) (fun τ => toFun (mfRhsCoeff d s V ν (ρc τ))) Φ I hI
    (hΦ.of_le (by norm_num)) ht (h1.mono hsub) (h2.mono hsub)
    (fun τ hτ x => hasDerivAt_mfPath_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H x
      ⟨lt_of_le_of_lt ha hτ.1, hτ.2.trans_le hbT⟩) hrange

/-- `hasDerivAt_interaction` for a real solution on `[0,T]`, `t ∈ (0,T)`. -/
theorem hasDerivAt_interaction (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖ρc τ k‖ ^ 2).re)
      (∫ x, riesz d s (ρc t) x * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  have hVi : Integrable V :=
    (continuous_of_isCk' hV1 le_rfl).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr := rhs_continuousInHsOn' hd s hs0 hsd K hK1 V hV ν ρc _ H.sol.cont
  obtain ⟨B1, hB1⟩ := exists_bound_of_continuousInHsOn_Icc (K : ℝ) ρc T H.sol.cont
  obtain ⟨B2, hB2⟩ := exists_bound_of_continuousInHsOn_Icc ((K : ℝ) - 2)
    (fun σ => mfRhsCoeff d s V ν (ρc σ)) T hr
  have hmemI : ∀ τ ∈ Ioo (t / 2) T, τ ∈ Icc 0 T := fun τ hτ =>
    ⟨by linarith [hτ.1, ht.1], hτ.2.le⟩
  refine hasDerivAt_interaction_gen s hsd K hK ρc (fun σ => mfRhsCoeff d s V ν (ρc σ))
    (a := t / 2) (b := T) ⟨by linarith [ht.1], ht.2⟩
    (fun τ hτ => H.sol.cont.1 τ (hmemI τ hτ)) (fun τ hτ => H.real τ (hmemI τ hτ))
    (fun τ hτ => hr.1 τ (hmemI τ hτ))
    (fun τ hτ => isRealCoeff_mfRhsCoeff s V hVi ν _ (H.real τ (hmemI τ hτ)))
    (fun τ hτ k => hasDerivAt_coeff_on hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol k
      ⟨by linarith [hτ.1, ht.1], hτ.2⟩)
    (max B1 B2) (fun τ hτ => ⟨(hB1 τ (hmemI τ hτ)).trans (le_max_left _ _),
      (hB2 τ (hmemI τ hτ)).trans (le_max_right _ _)⟩)

/-- Derivative of `∫ V ρ`, time-local version. -/
theorem hasDerivAt_integral_V (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun τ => ∫ x, V x * mfPath ρc τ x)
      (∫ x, V x * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  obtain ⟨h1, h2⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  have hVc : Continuous V := continuous_of_isCk' hV1 le_rfl
  have hsub : Icc (t / 2) T ×ˢ (univ : Set (Torus d)) ⊆ Icc 0 T ×ˢ univ :=
    prod_mono (fun τ hτ => ⟨by linarith [hτ.1, ht.1], hτ.2⟩) subset_rfl
  have htm : t ∈ Ioo (t / 2) T := ⟨by linarith [ht.1], ht.2⟩
  refine hasDerivAt_integral_param (fun τ x => V x * mfPath ρc τ x)
    (fun τ x => V x * toFun (mfRhsCoeff d s V ν (ρc τ)) x) htm ?_ ?_ ?_
  · exact (hVc.comp_continuousOn (continuous_snd.continuousOn)).mul (h1.mono hsub)
  · exact (hVc.comp_continuousOn (continuous_snd.continuousOn)).mul (h2.mono hsub)
  · intro τ hτ x
    exact (hasDerivAt_mfPath_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H x
      ⟨by linarith [hτ.1, ht.1], hτ.2⟩).const_mul (V x)
