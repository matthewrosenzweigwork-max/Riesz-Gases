import HRS.MS.FixEqP3Aux11

/-!
# S5.7 `fixed_equation` (worker S57P), part 24: linearity of the kernel elements and the expansion of `κ_t(φ)`

`s57p_el_lin`, `s57p_el_finsum`: `el` is linear on kernels with `L²` truncation; `s57p_kappa_expand`: for `φ ∈ Σ^m`,
`κ_t(φ) = lim_F ∑_{α ∈ F} b_α κ_t(φ_α)` in `L²([0,T]×ℝ^d;ℝ^d)` (from `s57p_prop_expand`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

section Lin

variable {T : ℝ} {w : ℝ × Euc d → ℝ}

theorem s57p_kf_lin (A₁ A₂ : ℝ × Euc d → Euc d) (t a b : ℝ) :
    s57pkf w (fun p => a • A₁ p + b • A₂ p) t = fun p => a • s57pkf w A₁ t p + b • s57pkf w A₂ t p := by
  funext p; simp only [s57pkf]
  split_ifs
  · rw [smul_add, smul_comm (w p) a, smul_comm (w p) b]
  · simp

theorem s57p_el_lin {A₁ A₂ : ℝ × Euc d → Euc d} {t : ℝ} (h1 : MemLp (s57pkf w A₁ t) 2 (s57pμ d T))
    (h2 : MemLp (s57pkf w A₂ t) 2 (s57pμ d T)) (a b : ℝ) :
    ∃ h : MemLp (s57pkf w (fun p => a • A₁ p + b • A₂ p) t) 2 (s57pμ d T),
      s57pel T w (fun p => a • A₁ p + b • A₂ p) t = a • s57pel T w A₁ t + b • s57pel T w A₂ t := by
  have e : s57pkf w (fun p => a • A₁ p + b • A₂ p) t = a • s57pkf w A₁ t + b • s57pkf w A₂ t := by
    rw [s57p_kf_lin]; rfl
  have h' : MemLp (a • s57pkf w A₁ t + b • s57pkf w A₂ t) 2 (s57pμ d T) := (h1.const_smul a).add (h2.const_smul b)
  have h : MemLp (s57pkf w (fun p => a • A₁ p + b • A₂ p) t) 2 (s57pμ d T) := by rw [e]; exact h'
  refine ⟨h, ?_⟩
  have hc : h.toLp (s57pkf w (fun p => a • A₁ p + b • A₂ p) t) = h'.toLp (a • s57pkf w A₁ t + b • s57pkf w A₂ t) :=
    MemLp.toLp_congr h h' (by rw [e])
  rw [s57p_el_eq h, s57p_el_eq h1, s57p_el_eq h2, hc, MemLp.toLp_add (h1.const_smul a) (h2.const_smul b),
    MemLp.toLp_const_smul, MemLp.toLp_const_smul]

theorem s57p_el_finsum {ι : Type*} {A : ι → ℝ × Euc d → Euc d} {t : ℝ}
    (hA : ∀ α, MemLp (s57pkf w (A α) t) 2 (s57pμ d T)) (b : ι → ℝ) (F : Finset ι) :
    ∃ h : MemLp (s57pkf w (fun p => ∑ α ∈ F, b α • A α p) t) 2 (s57pμ d T),
      s57pel T w (fun p => ∑ α ∈ F, b α • A α p) t = ∑ α ∈ F, b α • s57pel T w (A α) t := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have e : s57pkf w (fun p => ∑ α ∈ (∅ : Finset ι), b α • A α p) t = 0 := by funext p; simp [s57pkf]
    have h : MemLp (s57pkf w (fun p => ∑ α ∈ (∅ : Finset ι), b α • A α p) t) 2 (s57pμ d T) := by
      rw [e]; exact MemLp.zero
    refine ⟨h, ?_⟩
    rw [s57p_el_eq h, MemLp.toLp_congr h MemLp.zero (by rw [e]), MemLp.toLp_zero]
    simp
  | insert β F hβ ih =>
    obtain ⟨hF, eF⟩ := ih
    have e : (fun p => ∑ α ∈ insert β F, b α • A α p) =
        fun p => (1 : ℝ) • (∑ α ∈ F, b α • A α p) + b β • A β p := by
      funext p; rw [Finset.sum_insert hβ, one_smul, add_comm]
    obtain ⟨h, el⟩ := s57p_el_lin hF (hA β) 1 (b β)
    rw [e]
    refine ⟨h, ?_⟩
    rw [el, eF, Finset.sum_insert hβ, one_smul, add_comm]

end Lin

theorem s57p_gradient_finsum {ι : Type*} (F : Finset ι) (g : ι → Euc d → ℝ) (b : ι → ℝ)
    (hg : ∀ α, ContDiff ℝ 1 (g α)) (x : Euc d) :
    gradient (fun y => ∑ α ∈ F, b α * g α y) x = ∑ α ∈ F, b α • gradient (g α) x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have : (fun y : Euc d => ∑ α ∈ (∅ : Finset ι), b α * g α y) = fun _ => 0 := by funext y; simp
    rw [this]
    ext i
    rw [movtr_gradient_apply]
    simp
  | insert β F hβ ih =>
    have e : (fun y => ∑ α ∈ insert β F, b α * g α y) = fun y => (1 : ℝ) * (∑ α ∈ F, b α * g α y) + b β * g β y := by
      funext y; rw [Finset.sum_insert hβ, one_mul, add_comm]
    rw [e, s57p_gradient_lin2 (ContDiff.sum fun α _ => contDiff_const.mul (hg α)) (hg β), ih, Finset.sum_insert hβ,
      one_smul, add_comm]

variable {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ}
  {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca Cd : ℝ}

theorem s57p_kappa_expand (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hJ : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (hm : (J : ℝ) + d < m) (hCa : 0 ≤ Ca)
    {q : ℝ} (hq : 0 ≤ q) {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F₀ : Finset (MultiIndex d), ∀ F : Finset (MultiIndex d), F₀ ⊆ F →
      ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t φ - ∑ α ∈ F, s57pb d m φ α • s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t
        (oscTestFun m α)‖ ≤ ε := by
  set C := fixedEqCoeff s M Q ν c ρ with hC
  set R := n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ with hR
  have hT := Fx.hT
  obtain ⟨hsum, hexp, htail⟩ := s57p_hermite_series hd hm hCj hjets hφ
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  have hwd := s57p_wdata Fx.fe hT hq Fx.prob
  set g : MultiIndex d → ℝ := fun α => |s57pb d m φ α| * (Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) with hg
  have hg0 : ∀ α, 0 ≤ g α := fun α => mul_nonneg (abs_nonneg _) (mul_nonneg hCj (Real.rpow_nonneg (oscEv_pos α).le _))
  have hφR : ContDiff ℝ (R : WithTop ℕ∞) φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hBφ : ∀ l ≤ R, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ ∑' α, g α := by
    intro l hl x
    have := htail ∅ l hl x
    have e : (fun y => φ y - s57pP d m φ ∅ y) = φ := by funext y; simp [s57pP]
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    refine tsum_congr fun α => ?_
    simp [hg]
  have hBφ0 : 0 ≤ ∑' α, g α := tsum_nonneg hg0
  obtain ⟨hclφ, hOφ⟩ := hCu Fx.fam.adj hBφ0 hφR hBφ t ht
  have hFam : ∀ F : Finset (MultiIndex d), True := fun _ => trivial
  -- the expansion in sup norm
  set ε' : ℝ := ε / (T * (2 * q) + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨F₀, hF₀⟩ := s57p_prop_expand hθ hd Fx.fam (m := m) (J := J) (by omega) hm hφ hε'0
  refine ⟨F₀, fun F hF => ?_⟩
  -- kernels
  have hAα : ∀ α, Continuous (s57pA C t (oscTestFun m α)) := fun α => s57p_A_cont ht.1 ((hbd α).1 t ht).1
  have hAbα : ∀ α (p : ℝ × Euc d), ‖s57pA C t (oscTestFun m α) p‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    fun α => s57p_A_bound ht.1 (fun r hr x => (((hbd α).1 t ht).2 r hr).2 1 (by omega) x)
  have hAφ : Continuous (s57pA C t φ) := s57p_A_cont ht.1 hclφ
  have hAbφ : ∀ p : ℝ × Euc d, ‖s57pA C t φ p‖ ≤ |K| * (s57pCu θ hθ (n + 1) * ∑' α, g α) :=
    s57p_A_bound ht.1 (fun r hr x => (hOφ r hr).2 1 (by omega) x)
  have hMα : ∀ α, MemLp (s57pkf (s57pw T q ρ) (s57pA C t (oscTestFun m α)) t) 2 (s57pμ d T) := fun α =>
    s57p_kf_memLp hwd (hAα α).aestronglyMeasurable (Ba := Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
      (fun p _ => hAbα α p)
  have hMφ : MemLp (s57pkf (s57pw T q ρ) (s57pA C t φ) t) 2 (s57pμ d T) :=
    s57p_kf_memLp hwd hAφ.aestronglyMeasurable (Ba := |K| * (s57pCu θ hθ (n + 1) * ∑' α, g α)) (fun p _ => hAbφ p)
  obtain ⟨hS, eS⟩ := s57p_el_finsum hMα (s57pb d m φ) F
  obtain ⟨hD, eD⟩ := s57p_el_lin hMφ hS 1 (-1)
  -- the pointwise bound of the difference
  have hdiff : ∀ p : ℝ × Euc d, ‖(1 : ℝ) • s57pA C t φ p + (-1 : ℝ) • ∑ α ∈ F, s57pb d m φ α • s57pA C t (oscTestFun m α) p‖ ≤ ε' := by
    intro p
    set r' : ℝ := max 0 (min p.1 t) with hr'
    have hr'mem : r' ∈ Set.Icc (0 : ℝ) t := ⟨le_max_left _ _, max_le ht.1 (min_le_right _ _)⟩
    have hcα : ∀ α, ContDiff ℝ 1 (propagatorW C r' t (oscTestFun m α)) := fun α =>
      (((hbd α).1 t ht).2 r' hr'mem).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
    have hcφ : ContDiff ℝ 1 (propagatorW C r' t φ) := (hOφ r' hr'mem).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
    have e1 : (1 : ℝ) • s57pA C t φ p + (-1 : ℝ) • ∑ α ∈ F, s57pb d m φ α • s57pA C t (oscTestFun m α) p =
        gradient (fun y => propagatorW C r' t φ y -
          ∑ α ∈ F, s57pb d m φ α * propagatorW C r' t (oscTestFun m α) y) p.2 := by
      rw [HRS.MS.Fcau.fcau_gradient_sub hcφ (ContDiff.sum fun α _ => contDiff_const.mul (hcα α)),
        s57p_gradient_finsum F (fun α => propagatorW C r' t (oscTestFun m α)) (s57pb d m φ) hcα]
      simp only [s57pA, one_smul, neg_smul, ← sub_eq_add_neg, hr']
    rw [e1, s57p_norm_gradient]
    exact hF₀ F hF t ht r' hr'mem 1 (by omega) p.2
  have hAD : Continuous (fun p : ℝ × Euc d => (1 : ℝ) • s57pA C t φ p + (-1 : ℝ) • ∑ α ∈ F, s57pb d m φ α • s57pA C t (oscTestFun m α) p) := by
    exact (hAφ.const_smul (1 : ℝ)).add ((continuous_finset_sum _ fun α _ => (hAα α).const_smul (s57pb d m φ α)).const_smul (-1 : ℝ))
  have hnorm := s57p_el_norm hwd hAD.aestronglyMeasurable (t := t) (Ba := ε') (fun p _ => hdiff p)
  have hrw : s57pκ C T q ρ t φ - ∑ α ∈ F, s57pb d m φ α • s57pκ C T q ρ t (oscTestFun m α) =
      s57pel T (s57pw T q ρ) (fun p => (1 : ℝ) • s57pA C t φ p + (-1 : ℝ) • ∑ α ∈ F, s57pb d m φ α • s57pA C t (oscTestFun m α) p) t := by
    rw [eD, eS]
    simp only [s57pκ, one_smul, neg_smul, ← sub_eq_add_neg]
  rw [hrw]
  refine le_of_sq_le_sq ?_ hε.le
  refine hnorm.trans ?_
  have hT0 : 0 ≤ T * (2 * q) := by positivity
  rw [hε', div_pow]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ε, mul_nonneg hT0 (sq_nonneg ε), sq_nonneg (T * (2 * q))]

end HRS.MS.FixEq
