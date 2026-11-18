import HRS.MS.R2ChaosAux6

/-!
# HRS.MS.R2ChaosAux7 -- Parseval for the orthonormal basis `(P_μ a_i)` of `L²_0(μ)`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Parseval

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s94_memLp_projMean {a : Euc d → ℝ} (ha : IsR2Test a) : MemLp (Whole.projMean μ a) 2 μ := by
  obtain ⟨C, hC⟩ := s94_projMean_bounded μ ha
  exact MemLp.of_bound (s94_projMean_continuous μ ha).aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa using hC x)

theorem s94_integral_projMean {a : Euc d → ℝ} (ha : IsR2Test a) : ∫ x, Whole.projMean μ a x ∂μ = 0 := by
  unfold Whole.projMean
  rw [integral_sub (s94_test_integrable ha μ) (integrable_const _)]
  simp [Whole.pair]

/-- Parseval: for `f ∈ L²_0(μ)`, `∑_{i<n} ⟨f, P a_i⟩² → ‖f‖²`. -/
theorem s94_parseval {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    (hcomplete : ∀ f : Euc d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 → (∀ i, ∫ x, f x * a i x ∂μ = 0) → f =ᵐ[μ] 0)
    {f : Euc d → ℝ} (hf : MemLp f 2 μ) (hf0 : ∫ x, f x ∂μ = 0) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (∫ x, f x * Whole.projMean μ (a i) x ∂μ) ^ 2) atTop
      (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
  classical
  let eL : ℕ → Lp ℝ 2 μ := fun i => (s94_memLp_projMean (μ := μ) (ha i)).toLp _
  let oneL : Lp ℝ 2 μ := (memLp_const (1 : ℝ) : MemLp (fun _ : Euc d => (1 : ℝ)) 2 μ).toLp _
  let v : Option ℕ → Lp ℝ 2 μ := fun p => p.elim oneL eL
  have hinner : ∀ (g g' : Euc d → ℝ) (hg : MemLp g 2 μ) (hg' : MemLp g' 2 μ),
      inner ℝ (hg.toLp g) (hg'.toLp g') = ∫ x, g x * g' x ∂μ := by
    intro g g' hg hg'
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hg'.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hinner' : ∀ (g : Euc d → ℝ) (hg : MemLp g 2 μ) (G : Lp ℝ 2 μ),
      inner ℝ (hg.toLp g) G = ∫ x, g x * G x ∂μ := by
    intro g hg G
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x h1
    rw [h1]
    simp [mul_comm]
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro p q
    rcases p with _ | i <;> rcases q with _ | j
    · show inner ℝ oneL oneL = _
      rw [show oneL = (memLp_const (1 : ℝ) : MemLp (fun _ : Euc d => (1 : ℝ)) 2 μ).toLp _ from rfl, hinner]
      simp
    · show inner ℝ oneL (eL j) = _
      rw [hinner]
      simpa using s94_integral_projMean (μ := μ) (ha j)
    · show inner ℝ (eL i) oneL = _
      rw [hinner]
      simpa using s94_integral_projMean (μ := μ) (ha i)
    · show inner ℝ (eL i) (eL j) = _
      rw [hinner, hon]
      simp [Option.some_inj]
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro G hG
    have h0 : ∀ p, inner ℝ (v p) G = 0 := fun p =>
      (Submodule.mem_orthogonal _ _).1 hG _ (Submodule.subset_span ⟨p, rfl⟩)
    have hG2 : MemLp (fun x => G x) 2 μ := Lp.memLp G
    have hm : ∫ x, G x ∂μ = 0 := by
      have this : inner ℝ oneL G = 0 := h0 none
      rw [show oneL = (memLp_const (1 : ℝ) : MemLp (fun _ : Euc d => (1 : ℝ)) 2 μ).toLp _ from rfl,
        hinner'] at this
      simpa using this
    have hi : ∀ i, ∫ x, G x * Whole.projMean μ (a i) x ∂μ = 0 := by
      intro i
      have this : inner ℝ (eL i) G = 0 := h0 (some i)
      rw [show eL i = (s94_memLp_projMean (μ := μ) (ha i)).toLp _ from rfl, hinner'] at this
      simpa [mul_comm] using this
    have hGa : ∀ i, ∫ x, G x * a i x ∂μ = 0 := by
      intro i
      have e : ∀ x, G x * a i x = G x * Whole.projMean μ (a i) x + Whole.pair μ (a i) * G x := fun x => by
        unfold Whole.projMean; ring
      simp_rw [e]
      rw [integral_add, integral_const_mul, hm, hi]
      · simp
      · exact (hG2.integrable_mul (s94_memLp_projMean (μ := μ) (ha i))).congr (ae_of_all _ fun x => by simp [mul_comm])
      · exact hG2.integrable (by norm_num) |>.const_mul _
    have hae := hcomplete _ hG2 hm hGa
    exact (Lp.eq_zero_iff_ae_eq_zero).2 hae
  let b := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  have hb : ⇑b = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp
  set fL : Lp ℝ 2 μ := hf.toLp f with hfL
  have hsum := b.hasSum_inner_mul_inner fL fL
  rw [hb, hfL, hinner f f hf hf] at hsum
  have hterm : ∀ p : Option ℕ, inner ℝ fL (v p) * inner ℝ (v p) fL =
      (p.elim 0 (fun i => ∫ x, f x * Whole.projMean μ (a i) x ∂μ)) ^ 2 := by
    intro p
    rcases p with _ | i
    · show inner ℝ fL oneL * inner ℝ oneL fL = _
      rw [hfL, show oneL = (memLp_const (1 : ℝ) : MemLp (fun _ : Euc d => (1 : ℝ)) 2 μ).toLp _ from rfl, hinner]
      simp [hf0]
    · show inner ℝ fL (eL i) * inner ℝ (eL i) fL = _
      rw [hfL, show eL i = (s94_memLp_projMean (μ := μ) (ha i)).toLp _ from rfl, hinner, hinner]
      simp only [Option.elim]
      rw [sq]
      congr 1
      exact integral_congr_ae (ae_of_all _ fun x => by simp [mul_comm])
  have hsum' : HasSum (fun p : Option ℕ =>
      (p.elim 0 (fun i => ∫ x, f x * Whole.projMean μ (a i) x ∂μ)) ^ 2) (∫ x, f x * f x ∂μ) := by
    have h2 : (fun p : Option ℕ => (p.elim 0 (fun i => ∫ x, f x * Whole.projMean μ (a i) x ∂μ)) ^ 2) =
        fun p => inner ℝ fL (v p) * inner ℝ (v p) fL := funext fun p => (hterm p).symm
    rw [h2]
    exact hsum
  have hsum2 : HasSum (fun i : ℕ => (∫ x, f x * Whole.projMean μ (a i) x ∂μ) ^ 2) (∫ x, f x * f x ∂μ) := by
    have := (Function.Injective.hasSum_iff (Option.some_injective ℕ)
      (f := fun p : Option ℕ => (p.elim 0 (fun i => ∫ x, f x * Whole.projMean μ (a i) x ∂μ)) ^ 2) (a := ∫ x, f x * f x ∂μ)
      (fun p hp => by
        rcases p with _ | i
        · simp
        · exact absurd ⟨i, rfl⟩ hp)).2 hsum'
    exact this
  have := hsum2.tendsto_sum_nat
  simpa [sq] using this

end Parseval

section Remainder

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- The coefficients `γ_i = ⟨P u, P a_i⟩`. -/
def s94gam (μ : Measure (Euc d)) (u : Euc d → ℝ) (a : ℕ → Euc d → ℝ) (i : ℕ) : ℝ :=
  ∫ x, Whole.projMean μ u x * Whole.projMean μ (a i) x ∂μ

theorem s94_remainder_sq {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {u : Euc d → ℝ} (hu : IsR2Test u) (n : ℕ) :
    ∫ x, (Whole.projMean μ u x - ∑ i : Fin n, s94gam μ u a i * Whole.projMean μ (a i) x) ^ 2 ∂μ =
      ∫ x, (Whole.projMean μ u x) ^ 2 ∂μ - ∑ i : Fin n, s94gam μ u a i ^ 2 := by
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ℝ, ∀ i, γ i = s94gam μ u a i := ⟨fun i => s94gam μ u a i, fun _ => rfl⟩
  simp only [← hγ]
  have e : ∀ x, (Whole.projMean μ u x - ∑ i : Fin n, γ i * Whole.projMean μ (a i) x) ^ 2 =
      (Whole.projMean μ u x) ^ 2 - 2 * ∑ i : Fin n, γ i * (Whole.projMean μ u x * Whole.projMean μ (a i) x) +
        ∑ i : Fin n, ∑ j : Fin n, (γ i * γ j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x) := fun x => by
    have h1 : (∑ i : Fin n, γ i * Whole.projMean μ (a i) x) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, (γ i * γ j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 : Whole.projMean μ u x * ∑ i : Fin n, γ i * Whole.projMean μ (a i) x =
        ∑ i : Fin n, γ i * (Whole.projMean μ u x * Whole.projMean μ (a i) x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    linear_combination (-2) * h2 + h1
  have hi1 : Integrable (fun x => (Whole.projMean μ u x) ^ 2) μ := by
    have := s94_integrable_projMean_mul μ hu hu
    exact this.congr (ae_of_all _ fun x => by simp [sq])
  have hi2 : ∀ i : Fin n, Integrable (fun x => γ i * (Whole.projMean μ u x * Whole.projMean μ (a i) x)) μ :=
    fun i => (s94_integrable_projMean_mul μ hu (ha i)).const_mul _
  have hi3 : ∀ i j : Fin n, Integrable (fun x => (γ i * γ j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x)) μ :=
    fun i j => (s94_integrable_projMean_mul μ (ha i) (ha j)).const_mul _
  have hi2' : Integrable (fun x => 2 * ∑ i : Fin n, γ i * (Whole.projMean μ u x * Whole.projMean μ (a i) x)) μ :=
    (integrable_finset_sum _ fun i _ => hi2 i).const_mul 2
  have hi3' : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n, (γ i * γ j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x)) μ :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi3 i j
  simp_rw [e]
  have hi12 : Integrable (fun x => (Whole.projMean μ u x) ^ 2 -
      2 * ∑ i : Fin n, γ i * (Whole.projMean μ u x * Whole.projMean μ (a i) x)) μ := hi1.sub hi2'
  rw [integral_add hi12 hi3', integral_sub hi1 hi2', integral_const_mul,
    integral_finset_sum _ fun i _ => hi2 i]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi3 i j]
  have h2 : ∑ i : Fin n, ∫ x, γ i * (Whole.projMean μ u x * Whole.projMean μ (a i) x) ∂μ = ∑ i : Fin n, γ i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hγ]
    simp only [s94gam]
    ring
  have h3 : ∑ i : Fin n, ∫ x, ∑ j : Fin n, (γ i * γ j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x) ∂μ =
      ∑ i : Fin n, γ i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hi3 i j]
    simp_rw [integral_const_mul, hon]
    rw [Finset.sum_eq_single i (fun j _ hj => by
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h).symm
      simp [hne]) (fun h => absurd (Finset.mem_univ i) h)]
    simp [sq]
  rw [h2, h3]
  ring

end Remainder

section RemainderField

variable {s T b p K : ℝ} {μ : Measure (Euc d)} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

/-- The remainder `ξ(u)(t) - ∑_{i<n} γ_i ξ(a_i)(t)` has second moment at most `Λ (‖Pu‖² - ∑_{i<n} γ_i²)`. -/
theorem s94_remainder_le (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) [IsProbabilityMeasure μ] {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ a x) ^ 2 ∂μ)
    {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {u : Euc d → ℝ} (hu : IsR2Test u) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    ∫ ζ, (r2PathEval T (ξ u ζ) t - ∑ i : Fin n, s94gam μ u a i * r2PathEval T (ξ (a i) ζ) t) ^ 2 ∂P' ≤
      Λ * (∫ x, (Whole.projMean μ u x) ^ 2 ∂μ - ∑ i : Fin n, s94gam μ u a i ^ 2) := by
  set γ : Fin n → ℝ := fun i => s94gam μ u a i with hγ
  set bb : Fin (n + 1) → Euc d → ℝ := Fin.cons (α := fun _ => Euc d → ℝ) u (fun i : Fin n => a i) with hbb
  set c : Fin (n + 1) → ℝ := Fin.cons (α := fun _ => ℝ) 1 (fun i : Fin n => -γ i) with hc
  have hbbt : ∀ j, IsR2Test (bb j) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [hbb] using hu
    · simpa [hbb] using ha i
  have hfun : (fun x => ∑ j, c j * bb j x) = fun x => u x - ∑ i : Fin n, γ i * a i x := by
    funext x
    rw [Fin.sum_univ_succ]
    simp [hbb, hc, sub_eq_add_neg, Finset.sum_neg_distrib]
  have hlin := s94_xi_lincomb hset hbbt c
  rw [hfun] at hlin
  have hw : IsR2Test (fun x => u x - ∑ i : Fin n, γ i * a i x) := by
    rw [← hfun]; exact s94_test_lincomb hbbt c
  have h1 : ∀ ζ, ξ (fun x => u x - ∑ i : Fin n, γ i * a i x) ζ = ∑ j, c j • ξ (bb j) ζ →
      r2PathEval T (ξ (fun x => u x - ∑ i : Fin n, γ i * a i x) ζ) t =
        r2PathEval T (ξ u ζ) t - ∑ i : Fin n, γ i * r2PathEval T (ξ (a i) ζ) t := by
    intro ζ hζ
    rw [hζ, s94_pathEval_lincomb, Fin.sum_univ_succ]
    simp [hbb, hc, sub_eq_add_neg, Finset.sum_neg_distrib]
  have hint : ∫ ζ, (r2PathEval T (ξ u ζ) t - ∑ i : Fin n, γ i * r2PathEval T (ξ (a i) ζ) t) ^ 2 ∂P' =
      ∫ ζ, (r2PathEval T (ξ (fun x => u x - ∑ i : Fin n, γ i * a i x) ζ) t) ^ 2 ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [hlin] with ζ hζ
    rw [h1 ζ hζ]
  have hP : ∀ x, Whole.projMean μ (fun x => u x - ∑ i : Fin n, γ i * a i x) x =
      Whole.projMean μ u x - ∑ i : Fin n, γ i * Whole.projMean μ (a i) x := by
    intro x
    have := s94_projMean_lincomb μ hbbt c x
    rw [hfun] at this
    rw [this, Fin.sum_univ_succ]
    simp [hbb, hc, sub_eq_add_neg, Finset.sum_neg_distrib]
  show ∫ ζ, (r2PathEval T (ξ u ζ) t - ∑ i : Fin n, γ i * r2PathEval T (ξ (a i) ζ) t) ^ 2 ∂P' ≤ _
  rw [hint]
  refine (hcov t ht _ hw).trans ?_
  simp_rw [hP]
  rw [s94_remainder_sq ha hon hu n]

end RemainderField

end HRS.MS.R2Chaos
