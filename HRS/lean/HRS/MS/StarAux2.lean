import HRS.MS.StarAux1

/-!
# STAR-2: the corner `R2c*` core estimate

`UlocStarRegime d s M` : `d - 2 < s` and `Sym M ≤ 0` (contains `R2a`-with-sign, `R2c`, and the corner
`d - 1 < s < d`, `invβ = 0`, `M = -λI + A`).  `n3c_r2c_core_star` is `n3c_r2c_core` with the hypothesis
`s ≤ d - 1` replaced by `s < d` (already a standing hypothesis): the first-order sum is bounded by `n3c_key`
(`s ≤ d - 1`) or `star_key_high` (`s > d - 1`), and the symmetric order-`θ` term by `n3b_sign`
(`0 < θ < 2`).  The hypotheses `hχ hb hΨ` are added (needed by `star_key_high`); `ν₀` is dropped.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Star

/-- The corner regime for uniqueness in the uniformly local class. -/
def UlocStarRegime (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (d : ℝ) - 2 < s ∧ Torus.SymNonpos M

end HRS.MS.Star

namespace HRS.MS.UniqN3c

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqC3 HRS.MS.UniqN2b HRS.PDE.ToolboxRd HRS.MS.Star

variable {d : ℕ}

/-- **STAR-2: the corner/`R2c` core estimate (one-sided), regime `UlocStarRegime`.** -/
theorem n3c_r2c_core_star (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hR : UlocStarRegime d D.s D.M)
    (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ) (hcoef : CoeffHypRd D.s m Λ T ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : HRS.Whole.IsAdvectingDrift m Cb t b) (hΨ : HRS.Whole.IsNegDriftFlow t b Ψ)
    (K : ℝ) (hK : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A LF BF : ℝ) (f : Euc d → ℝ),
      0 ≤ A → ContDiff ℝ ∞ f → LocMass A f → IsLipschitz LF f → (∀ x, |f x| ≤ BF) →
      -(nMain D (ρ (t - σ)) f (fun x => varsigma χ Ψ σ c x * f x)) ≤ C * A ^ 2 := by
  have hR' : (d : ℝ) - 2 < D.s ∧ Torus.SymNonpos D.M := hR
  obtain ⟨lam, q, hsdg⟩ := HRS.PDE.exists_symDiag hR'.2
  obtain ⟨c0, hc0, hbr⟩ := HRS.MS.UniqN3a.n3a_bridge hd hs0 (by linarith [hR'.1]) hsd
  obtain ⟨C0, hC0, hkey⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ)
      (i j : Fin d), 0 ≤ A → ContDiff ℝ ∞ f → LocMass A f →
      |∫ y, f y * (D1 j (ρ (t - σ)) y *
        kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)| ≤ C0 * A ^ 2 := by
    by_cases hs1 : D.s ≤ (d : ℝ) - 1
    · exact n3c_key hd D hs0 hsd hs1 m Cb Λ T t ρ hcoef ht χ χh b Ψ K hK
    · exact star_key_high hd D hsd (not_le.1 hs1) m Cb Λ T t ρ hcoef ht χ χh hχ b Ψ hb hΨ K hK
  obtain ⟨Lχ0, hLχ0, hLχ⟩ := n2b_advCutoff_lip hK.flow hχ.1.1 hχ.1.2.1
  set A0 : ℝ := HRS.MS.UniqC1.c1A d m Λ with hA0def
  have hA00 : 0 ≤ A0 := HRS.MS.UniqE1.e1_A_nonneg m Λ
  have hr : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hθ0 : 0 < D.s + 2 - d := by linarith [hR'.1]
  have hθ2 : D.s + 2 - d < 2 := by linarith
  -- the sign constants, one per direction `q l`
  have hl : ∀ l : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Euc d) (p q' F : Euc d → ℝ) (A LF BF : ℝ), 0 ≤ A →
      (∀ x, 0 ≤ p x ∧ p x ≤ Real.sqrt A0 * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2))) →
      IsLipschitz (Real.sqrt ((A0 + 1) / 2)) p →
      (∀ x, 0 ≤ q' x ∧ q' x ≤ 1) → IsLipschitz Lχ0 q' →
      Function.support q' ⊆ closedBall a (2 * Real.exp (Cb * t)) →
      IsLipschitz LF F → (∀ x, |F x| ≤ BF) → LocMass A F →
      -C * A ^ 2 ≤ symbolForm (fun ξ : Euc d => c0 * (2 * Real.pi * inner ℝ ξ (q l)) ^ 2 *
        ‖ξ‖ ^ (D.s - d)) (fun x => p x ^ 2 * F x) (fun x => q' x ^ 2 * F x) := by
    intro l
    have hm := n3c_mq_homog hd hs0 hR'.1 hsd hc0 (q l)
    obtain ⟨k, hk⟩ := quadratic_toolbox_kernel hd _ hθ0 hθ2 _ hm
    exact HRS.MS.UniqN3b.n3b_sign hd hθ0 hθ2 hm hk (Real.sqrt A0) (Real.sqrt ((A0 + 1) / 2)) Lχ0
      (2 * Real.exp (Cb * t))
  choose Cl hCl0 hCl using hl
  have hlam : ∀ l, 0 ≤ lam l := hsdg.nonneg
  refine ⟨(∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * C0 + ∑ l, lam l * Cl l,
    add_nonneg (by positivity) (Finset.sum_nonneg fun l _ => mul_nonneg (hlam l) (hCl0 l)), ?_⟩
  intro σ hσ c A LF BF f hA hf hfm hfL hfb
  obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
  obtain ⟨hψ2, hψc, hψs, hψf⟩ := n2b_psi_facts hK hσ c hf
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hfb 0)
  have hnn : ∀ x, 0 ≤ ρ (t - σ) x := (hcoef.prob (t - σ) (hr σ hσ)).nonneg
  have hfc : Continuous f := hf.continuous
  -- `u = ρ' f ∈ L²`
  have hu : MemLp (fun x => ρ (t - σ) x * f x) 2 volume := by
    refine n3c_memLp (hρ1.continuous.mul hfc).aestronglyMeasurable (C := A0 * BF) fun x => ?_
    rw [abs_mul]
    have h1 := hρ0 x
    calc |ρ (t - σ) x| * |f x| ≤ (A0 * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) * BF :=
          mul_le_mul h1 (hfb x) (abs_nonneg _) (by positivity)
      _ = A0 * BF * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by ring
  -- the splitting
  have hsplit := n3c_nMain_split (D := D) hs0 hsd hρ1 hρ0 hρ1' hfm hψ2 hψc
  have hbridge : ∀ l, Integrable (fun x => ρ (t - σ) x * f x * HRS.Whole.convFun
        (rieszKernel d D.s) (fun y => fderiv ℝ (fun z => fderiv ℝ
          (fun x => varsigma χ Ψ σ c x * f x) z (q l)) y (q l)) x) volume ∧
      symbolForm (fun ξ : Euc d => c0 * (2 * Real.pi * inner ℝ ξ (q l)) ^ 2 * ‖ξ‖ ^ (D.s - d))
        (fun x => ρ (t - σ) x * f x) (fun x => varsigma χ Ψ σ c x * f x) =
      - ∫ x, ρ (t - σ) x * f x * HRS.Whole.convFun (rieszKernel d D.s) (fun y => fderiv ℝ (fun z =>
          fderiv ℝ (fun x => varsigma χ Ψ σ c x * f x) z (q l)) y (q l)) x := fun l => by
    obtain ⟨h1, _, h3⟩ := hbr (q l) _ _ hu hψ2 hψc
    exact ⟨h1, h3⟩
  -- the second term
  have hG : ∫ y, f y * (ρ (t - σ) y * ∑ i, ∑ j, D.M j i *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i (fun x => varsigma χ Ψ σ c x * f x))) y) =
      ∑ l, lam l * symbolForm (fun ξ : Euc d => c0 * (2 * Real.pi * inner ℝ ξ (q l)) ^ 2 *
        ‖ξ‖ ^ (D.s - d)) (fun x => ρ (t - σ) x * f x) (fun x => varsigma χ Ψ σ c x * f x) := by
    have hpt : ∀ y, f y * (ρ (t - σ) y * ∑ i, ∑ j, D.M j i *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i (fun x => varsigma χ Ψ σ c x * f x))) y) =
        -∑ l, lam l * (ρ (t - σ) y * f y * HRS.Whole.convFun (rieszKernel d D.s) (fun z => fderiv ℝ
          (fun w => fderiv ℝ (fun x => varsigma χ Ψ σ c x * f x) w (q l)) z (q l)) y) := by
      intro y
      rw [n3c_G_sum hs0 hsd hψ2 hψc hsdg.diag y]
      simp only [mul_neg, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hpt]
    rw [integral_neg, integral_finsetSum _ fun l _ => (hbridge l).1.const_mul (lam l)]
    simp_rw [integral_const_mul, (hbridge _).2]
    simp [Finset.sum_neg_distrib]
  -- the sign
  have hq' : ∀ l, -(Cl l) * A ^ 2 ≤ symbolForm (fun ξ : Euc d => c0 *
      (2 * Real.pi * inner ℝ ξ (q l)) ^ 2 * ‖ξ‖ ^ (D.s - d)) (fun x => ρ (t - σ) x * f x)
        (fun x => varsigma χ Ψ σ c x * f x) := by
    intro l
    have hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ (ρ (t - σ))) y‖ ≤ A0 := by
      intro y
      refine (n2b_rho_decay2 hd hcoef (hr σ hσ) y).trans ?_
      have : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)
      calc A0 * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ A0 * 1 := by gcongr
        _ = A0 := mul_one _
    have hpL := n3c_sqrt_lip hρ2 hnn hB2
    have hqsupp : Function.support (advCutoff χ Ψ σ c) ⊆
        closedBall (Ψ σ c) (2 * Real.exp (Cb * t)) := by
      intro x hx
      have hx' : varsigma χ Ψ σ c x ≠ 0 := pow_ne_zero 2 (Function.mem_support.1 hx)
      exact hK.supp σ hσ c (subset_tsupport _ (Function.mem_support.2 hx'))
    have := hCl l (Ψ σ c) (fun x => Real.sqrt (ρ (t - σ) x)) (advCutoff χ Ψ σ c) f A LF BF hA
      (fun x => ⟨Real.sqrt_nonneg _, n3c_p_decay hnn hρ0 x⟩) hpL
      (fun x => by
        have := hχ.1.2.2.2.1 (Function.invFun (Ψ σ) x - c)
        exact ⟨this.1, this.2⟩)
      (hLχ σ hσ c) hqsupp hfL hfb hfm
    have e1 : (fun x => Real.sqrt (ρ (t - σ) x) ^ 2 * f x) = fun x => ρ (t - σ) x * f x := by
      funext x; rw [Real.sq_sqrt (hnn x)]
    have e2 : (fun x => advCutoff χ Ψ σ c x ^ 2 * f x) = fun x => varsigma χ Ψ σ c x * f x := rfl
    rw [e1, e2] at this
    exact this
  -- first-order sum
  have hS1 : |∑ i, ∑ j, D.M j i * ∫ y, f y * (D1 j (ρ (t - σ)) y *
      kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)| ≤
      (∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * C0 * A ^ 2 := by
    calc _ ≤ ∑ i, ∑ j, |D.M j i| * (C0 * A ^ 2) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hkey σ hσ c A f i j hA hf hfm) (abs_nonneg _)
      _ = (∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * C0 * A ^ 2 := by
          simp only [← Finset.sum_mul]
          ring
  -- assemble
  rw [hsplit, hG]
  have hsum : -(∑ l, lam l * symbolForm (fun ξ : Euc d => c0 * (2 * Real.pi * inner ℝ ξ (q l)) ^ 2 *
        ‖ξ‖ ^ (D.s - d)) (fun x => ρ (t - σ) x * f x) (fun x => varsigma χ Ψ σ c x * f x)) ≤
      ∑ l, lam l * Cl l * A ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    have := mul_le_mul_of_nonneg_left (hq' l) (hlam l)
    nlinarith [this]
  have hneg := neg_abs_le (∑ i, ∑ j, D.M j i * ∫ y, f y * (D1 j (ρ (t - σ)) y *
      kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y))
  have hsumA : ∑ l, lam l * Cl l * A ^ 2 = (∑ l, lam l * Cl l) * A ^ 2 := by
    rw [Finset.sum_mul]
  nlinarith [hS1, hneg, hsum, hsumA, abs_nonneg (∑ i, ∑ j, D.M j i * ∫ y, f y * (D1 j (ρ (t - σ)) y *
      kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y))]

end HRS.MS.UniqN3c
