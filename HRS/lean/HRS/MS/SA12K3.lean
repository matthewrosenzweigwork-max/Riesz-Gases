import HRS.MS.SA12K2
import HRS.MS.ToriConv

/-!
# S.A.12 C1, joint continuity of the jets of a weakly continuous regular density path

For `CoeffHypRd s m Λ T ρ` every jet `D^i ρ(τ)(x)`, `i ≤ m+2`, is jointly continuous on `[0,T] × ℝ^d`:
mollify (kernel form: weak continuity), and use the uniform bound of the next derivative.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA

variable {d : ℕ}

theorem sa12k_fd (i : ℕ) : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ) := by
  induction i with
  | zero =>
    exact LinearEquiv.finiteDimensional
      (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toLinearEquiv
  | succ i ih =>
    have := ih
    exact LinearEquiv.finiteDimensional
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).toLinearEquiv.symm

theorem sa12k_cont_of_functionals {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {φ : X → V} {S : Set X}
    (h : ∀ ℓ : V →L[ℝ] ℝ, ContinuousOn (fun x => ℓ (φ x)) S) : ContinuousOn φ S := by
  let b := Module.finBasis ℝ V
  have hφ : φ = fun x => ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)) (φ x) • b j := by
    funext x
    simp only [LinearMap.coe_toContinuousLinearMap']
    exact (b.sum_repr (φ x)).symm
  rw [hφ]
  exact continuousOn_finsetSum _ fun j _ => (h _).smul continuousOn_const

theorem sa12k_den_facts {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (ρ t) ∧
    (∀ k ≤ m + 3, ∀ w : Euc d, jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k (ρ t) w‖ ≤
      (d : ℝ) ^ k * |Λ|) ∧ HRS.Whole.IsProbDensity (ρ t) := by
  obtain ⟨hMC, hWfin, hWle⟩ := hρ.regular.1 t ht
  have hWle' : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ t)).toReal ≤ |Λ| := by
    have hcb0 : 0 ≤ cbNorm (m + 3) (ρ t) :=
      Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _
    have := le_abs_self Λ
    linarith
  exact ⟨hMC.1, fun k hk w =>
    (tca_weight_le (m + 3) ((d : ℝ) + 3) (ρ t) hWfin.ne k hk w).trans
      (mul_le_mul_of_nonneg_left hWle' (pow_nonneg (Nat.cast_nonneg d) _)), hρ.prob t ht⟩

/-- A uniform bound of the jets up to order `m+3`. -/
theorem sa12k_den_bound {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k ≤ m + 3, ∀ w : Euc d,
      ‖iteratedFDeriv ℝ k (ρ t) w‖ ≤ Bd := by
  refine ⟨∑ i ∈ Finset.range (m + 4), (d : ℝ) ^ i * |Λ|, Finset.sum_nonneg fun i _ => by positivity,
    fun t ht k hk w => ?_⟩
  obtain ⟨-, hW, -⟩ := sa12k_den_facts hρ ht
  have hjb1 : 1 ≤ jbracket w ^ ((d : ℝ) + 3) :=
    Real.one_le_rpow (tca_one_le_jbracket w) (by positivity)
  have h1 : ‖iteratedFDeriv ℝ k (ρ t) w‖ ≤ (d : ℝ) ^ k * |Λ| :=
    (le_mul_of_one_le_left (norm_nonneg _) hjb1).trans (hW k hk w)
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun i : ℕ => (d : ℝ) ^ i * |Λ|)
    (fun i _ => by positivity) (Finset.mem_range.2 (by omega))

/-- Joint continuity of the kernel convolution against a weakly continuous probability path. -/
theorem sa12k_kconv_joint {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hρc : ∀ τ ∈ Icc (0 : ℝ) T, Continuous (ρ τ))
    (hprob : ∀ τ ∈ Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ τ))
    (hweak : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Icc (0 : ℝ) T))
    {i : ℕ} {κ : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ}
    (hκ : Continuous κ) (hc : HasCompactSupport κ) :
    ContinuousOn (fun q : ℝ × Euc d => sa12k_kconv (ρ q.1) κ q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have := sa12k_fd (d := d) i
  have hint : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, Integrable (fun y => ρ τ y • κ (x - y)) := fun τ hτ x =>
    sa12k_kconv_integrable (hρc τ hτ) hκ hc x
  -- time continuity at a fixed point
  have hA : ∀ x₀ : Euc d, ContinuousOn (fun τ => sa12k_kconv (ρ τ) κ x₀) (Icc (0 : ℝ) T) := by
    intro x₀
    refine sa12k_cont_of_functionals fun ℓ => ?_
    have hψ : Continuous (fun y => ℓ (κ (x₀ - y))) :=
      ℓ.continuous.comp (hκ.comp (continuous_const.sub continuous_id))
    have hψc : HasCompactSupport (fun y : Euc d => ℓ (κ (x₀ - y))) := by
      have h1 : HasCompactSupport (fun y : Euc d => κ (x₀ - y)) :=
        hc.comp_homeomorph (Homeomorph.subLeft x₀)
      exact h1.comp_left (by simp)
    obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ
    have h := hweak _ hψ ⟨B, fun x => by simpa using hB x⟩
    refine h.congr fun τ hτ => ?_
    show ℓ (sa12k_kconv (ρ τ) κ x₀) = ∫ y, ℓ (κ (x₀ - y)) * ρ τ y
    unfold sa12k_kconv
    rw [← ℓ.integral_comp_comm (hint τ hτ x₀)]
    congr 1
    funext y
    rw [map_smul, smul_eq_mul, mul_comm]
  -- uniform continuity in space
  have hB : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ x x' : Euc d, ‖x - x'‖ < r → ∀ τ ∈ Icc (0 : ℝ) T,
      ‖sa12k_kconv (ρ τ) κ x - sa12k_kconv (ρ τ) κ x'‖ ≤ ε := by
    intro ε hε
    have huc := hc.uniformContinuous_of_continuous hκ
    obtain ⟨r, hr, hr'⟩ := Metric.uniformContinuous_iff.1 huc ε hε
    refine ⟨r, hr, fun x x' hxx τ hτ => ?_⟩
    unfold sa12k_kconv
    rw [← integral_sub (hint τ hτ x) (hint τ hτ x')]
    have hρ0 := (hprob τ hτ).nonneg
    have hρi : Integrable (ρ τ) := by
      by_contra hni
      have := (hprob τ hτ).integral_one
      rw [integral_undef hni] at this
      exact zero_ne_one this
    calc ‖∫ y, (ρ τ y • κ (x - y) - ρ τ y • κ (x' - y))‖
        ≤ ∫ y, ‖ρ τ y • κ (x - y) - ρ τ y • κ (x' - y)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ρ τ y * ε := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            (hρi.mul_const ε) (Filter.Eventually.of_forall fun y => ?_)
          show ‖ρ τ y • κ (x - y) - ρ τ y • κ (x' - y)‖ ≤ ρ τ y * ε
          have hs : ρ τ y • κ (x - y) - ρ τ y • κ (x' - y) = ρ τ y • (κ (x - y) - κ (x' - y)) :=
            (smul_sub _ _ _).symm
          rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 y)]
          refine mul_le_mul_of_nonneg_left ?_ (hρ0 y)
          have := hr' (a := x - y) (b := x' - y) (by
            rw [dist_eq_norm]; simpa using hxx)
          rw [dist_eq_norm] at this
          exact this.le
      _ = ε := by rw [integral_mul_const, (hprob τ hτ).integral_one, one_mul]
  rw [Metric.continuousOn_iff]
  rintro ⟨τ₀, x₀⟩ hq ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousOn_iff.1 (hA x₀) τ₀ hq.1 (ε / 2) (by linarith)
  obtain ⟨r, hr, h2⟩ := hB (ε / 4) (by linarith)
  refine ⟨min δ₁ r, lt_min hδ₁ hr, ?_⟩
  rintro ⟨τ, x⟩ hqq hd
  have hd' := hd
  rw [Prod.dist_eq, max_lt_iff] at hd'
  have hτd : dist τ τ₀ < δ₁ := lt_of_lt_of_le hd'.1 (min_le_left _ _)
  have hxd : ‖x - x₀‖ < r := by
    have := lt_of_lt_of_le hd'.2 (min_le_right _ _)
    rwa [dist_eq_norm] at this
  have e1 := h1 τ hqq.1 hτd
  have e2 := h2 x x₀ hxd τ hqq.1
  rw [dist_eq_norm] at e1 ⊢
  show ‖sa12k_kconv (ρ τ) κ x - sa12k_kconv (ρ τ₀) κ x₀‖ < ε
  calc ‖sa12k_kconv (ρ τ) κ x - sa12k_kconv (ρ τ₀) κ x₀‖
      = ‖(sa12k_kconv (ρ τ) κ x - sa12k_kconv (ρ τ) κ x₀) +
          (sa12k_kconv (ρ τ) κ x₀ - sa12k_kconv (ρ τ₀) κ x₀)‖ := by congr 1; abel
    _ ≤ ‖sa12k_kconv (ρ τ) κ x - sa12k_kconv (ρ τ) κ x₀‖ +
          ‖sa12k_kconv (ρ τ) κ x₀ - sa12k_kconv (ρ τ₀) κ x₀‖ := norm_add_le _ _
    _ < ε := by linarith

/-- Joint continuity of the jets `D^i ρ(τ)(x)`, `i ≤ m+2`, on `[0,T] × ℝ^d`. -/
theorem sa12k_joint_jets {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    (i : ℕ) (hi : i ≤ m + 2) :
    ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ i (ρ q.1) q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  obtain ⟨Bd, hBd0, hBd⟩ := sa12k_den_bound hρ
  have hcd : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (ρ τ) :=
    fun τ hτ => (sa12k_den_facts hρ hτ).1
  have hρc : ∀ τ ∈ Icc (0 : ℝ) T, Continuous (ρ τ) := fun τ hτ =>
    (hcd τ hτ).continuous
  have hprob := fun τ (hτ : τ ∈ Icc (0 : ℝ) T) => (sa12k_den_facts hρ hτ).2.2
  -- the mollified jets
  set F : ℕ → ℝ × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ := fun n q =>
    sa12k_kconv (ρ q.1) (iteratedFDeriv ℝ i (sa12k_eta (1 / ((n : ℝ) + 1)) (by positivity))) q.2 with hF
  have hFc : ∀ n, ContinuousOn (F n) (Icc (0 : ℝ) T ×ˢ univ) := by
    intro n
    have hη := sa12k_eta_moll (d := d) (1 / ((n : ℝ) + 1)) (by positivity)
    exact sa12k_kconv_joint hρc hprob hρ.cont
      (hη.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top))
      (hη.compact.iteratedFDeriv i)
  have hFeq : ∀ n, ∀ q ∈ Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)),
      F n q = sa12k_moll (sa12k_eta (1 / ((n : ℝ) + 1)) (by positivity)) (iteratedFDeriv ℝ i (ρ q.1)) q.2 := by
    intro n q hq
    have hη := sa12k_eta_moll (d := d) (1 / ((n : ℝ) + 1)) (by positivity)
    have h1 := sa12k_moll_iter hη (hcd q.1 hq.1) (B := Bd) (fun k hk y => hBd q.1 hq.1 k hk y) i
      (by omega)
    have h2 := sa12k_kconv_iter (hρc q.1 hq.1) hη.smooth hη.compact i
    have h3 : sa12k_moll (sa12k_eta (1 / ((n : ℝ) + 1)) (by positivity)) (ρ q.1) =
        sa12k_kconv (ρ q.1) (sa12k_eta (1 / ((n : ℝ) + 1)) (by positivity)) :=
      sa12k_moll_eq_kconv _ _
    rw [h3] at h1
    show sa12k_kconv (ρ q.1) (iteratedFDeriv ℝ i _) q.2 = _
    rw [← congrFun h2 q.2, h1]
  have hconv : TendstoUniformlyOn F (fun q : ℝ × Euc d => iteratedFDeriv ℝ i (ρ q.1) q.2) atTop
      (Icc (0 : ℝ) T ×ˢ univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (Bd / ε)
    filter_upwards [eventually_ge_atTop N] with n hn q hq
    have hη := sa12k_eta_moll (d := d) (1 / ((n : ℝ) + 1)) (by positivity)
    have hfc : Continuous (iteratedFDeriv ℝ i (ρ q.1)) :=
      (hcd q.1 hq.1).continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))
    have herr := sa12k_moll_err hη hfc q.2 (E := Bd * (1 / ((n : ℝ) + 1))) (fun u hu => by
      have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i (ρ q.1)) :=
        (hcd q.1 hq.1).differentiable_iteratedFDeriv (by exact_mod_cast (by omega : i < m + 3))
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ i (ρ q.1))
        (C := Bd) (s := univ) (x := q.2) (y := q.2 - u) (fun z _ => hdiff z)
        (fun z _ => by
          rw [norm_fderiv_iteratedFDeriv]
          exact hBd q.1 hq.1 (i + 1) (by omega) z)
        convex_univ (mem_univ _) (mem_univ _)
      calc _ ≤ Bd * ‖q.2 - u - q.2‖ := this
        _ = Bd * ‖u‖ := by rw [sub_sub_cancel_left, norm_neg]
        _ ≤ Bd * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hu hBd0)
    rw [dist_eq_norm, norm_sub_rev, hFeq n q hq]
    refine lt_of_le_of_lt herr ?_
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_one_div, div_lt_iff₀ hpos]
    have := (div_lt_iff₀ hε).1 hN
    nlinarith
  exact hconv.continuousOn (Filter.Eventually.of_forall hFc).frequently

end HRS.MH.AdjointRd.Phase2SA12Construction
