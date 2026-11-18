import HRS.MS.UniqN4bG

/-!
# N4b of `UniqPlan.md`, part H: the near-field bound for one index pair

* `N4bCut`: the packaged facts on the cutoff `ς` and the partner cutoff `θ`.
* `n4b_pair_near`: `|∫ θ f ∂_j(ρ' H_i)| ≤ ε ∫_{B̄(p,8L)} |∇f|² + C A²`
  (integration by parts, `n4b_near`; interpolation, `n4b_H_interp`, `n4b_norms`; Young step, `n4b_young`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqN2b HRS.MS.UniqN0

variable {d : ℕ}

/-- Facts on the cutoff `ς` and the partner cutoff `θ` (supports in balls around `p`, values in `[0,1]`,
Lipschitz bounds, and the separation of `tsupport ς` from `tsupport (1 - θ)`). -/
structure N4bCut (d : ℕ) (p : Euc d) (L K Lθ δ : ℝ) (ς θ : Euc d → ℝ) : Prop where
  ς2 : ContDiff ℝ 2 ς
  ς01 : ∀ y, 0 ≤ ς y ∧ ς y ≤ 1
  ςK : ∀ y, ‖fderiv ℝ ς y‖ ≤ K
  ςs : tsupport ς ⊆ closedBall p (2 * L)
  θ1 : ContDiff ℝ 1 θ
  θ01 : ∀ y, 0 ≤ θ y ∧ θ y ≤ 1
  θs : tsupport θ ⊆ closedBall p (8 * L)
  θL : ∀ (j : Fin d) y, |D1 j θ y| ≤ Lθ
  sep : ∀ x y, x ∈ tsupport ς → y ∈ tsupport (fun y => 1 - θ y) → δ ≤ ‖x - y‖

/-- Facts on the density `ρ'`: `C¹` with `⟨y⟩^{-(d+3)}` decay of `ρ'` and its partial derivatives. -/
structure N4bRho (d : ℕ) (Cρ : ℝ) (ρ' : Euc d → ℝ) : Prop where
  c1 : ContDiff ℝ 1 ρ'
  dec0 : ∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))
  dec1 : ∀ (j : Fin d) y, |D1 j ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))

theorem n4b_pair_near (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L K Lθ Cρ δ : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hLθ : 0 ≤ Lθ) (hCρ : 0 ≤ Cρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin d) (p : Euc d) (ς θ ρ' f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      N4bCut d p L K Lθ δ ς θ → N4bRho d Cρ ρ' → ContDiff ℝ ∞ f → LocMass A f →
      |∫ y, θ y * f y * (D1 j ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y +
          ρ' y * D1 j (kernelConvDeriv d s i (fun x => ς x * f x)) y)| ≤
        ε * (∫ y in closedBall p (8 * L), ‖fderiv ℝ f y‖ ^ 2) + C * A ^ 2 := by
  have hL0 : 0 < L := by linarith
  have h8 : 1 ≤ 8 * L := by linarith
  obtain ⟨N, hN⟩ := n2b_ball_eLpNorm d (8 * L + 1)
  obtain ⟨C₂, hC₂, hH⟩ := n4b_H_interp hd hs0 hsd h8
  set κ : ℝ := kgOrder d s with hκ
  have hκ0 : 0 ≤ κ := n4b_kgOrder_nonneg d s
  have hκ1 : κ < 1 := n4b_kgOrder_lt_one hsd
  set cb : ℝ := Real.sqrt N + Real.sqrt d + Real.sqrt d * K * Real.sqrt N with hcb
  have hcb0 : 0 ≤ cb := by positivity
  set Q0 : ℝ := Cρ * C₂ * cb * max 1 (Lθ * Real.sqrt N) with hQ0def
  have hQ0 : 0 ≤ Q0 := by positivity
  obtain ⟨Cy, hCy0, hy⟩ := n4b_young hκ0 hκ1 (ε := ε / (Q0 + 1)) (by positivity)
  refine ⟨Q0 * Cy, by positivity, ?_⟩
  intro i j p ς θ ρ' f A hA hc hr hf hfm
  set E : Set (Euc d) := closedBall p (8 * L) with hE
  have hEm : MeasurableSet E := measurableSet_closedBall
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  set ψ : Euc d → ℝ := fun x => ς x * f x with hψdef
  have hςc : HasCompactSupport ς :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hc.ςs
  have hψ2 : ContDiff ℝ 2 ψ := hc.ς2.mul (hf.of_le (by simp))
  have hψc : HasCompactSupport ψ := hςc.mul_right
  have hψsupp : Function.support ψ ⊆ closedBall p (8 * L) :=
    (Function.support_mul_subset_left ς f).trans ((subset_tsupport ς).trans
      (hc.ςs.trans (closedBall_subset_closedBall (by linarith))))
  -- gradient and local masses
  set G : ℝ := Real.sqrt (∫ y in E, ‖fderiv ℝ f y‖ ^ 2) with hGdef
  have hI0 : 0 ≤ ∫ y in E, ‖fderiv ℝ f y‖ ^ 2 := setIntegral_nonneg hEm fun y _ => by positivity
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hGsq : G ^ 2 = ∫ y in E, ‖fderiv ℝ f y‖ ^ 2 := Real.sq_sqrt hI0
  set m : ℝ := Real.sqrt N * A with hmdef
  have hm0 : 0 ≤ m := by positivity
  have hfmE : eLpNorm (E.indicator f) 2 volume ≤ ENNReal.ofReal m := by
    have h1 := hN A f hfm p
    rw [abs_of_nonneg hA] at h1
    refine le_trans (eLpNorm_mono_enorm (hf1.continuous.aestronglyMeasurable.indicator hEm)
      (g := (ball p (8 * L + 1)).indicator f) (fun y => ?_)) h1
    by_cases hy : y ∈ E
    · have hy' : y ∈ ball p (8 * L + 1) := by
        rw [mem_ball]; have := mem_closedBall.1 hy; linarith
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy']
    · rw [Set.indicator_of_notMem hy]; simp
  obtain ⟨hΓψ, hψ0, hG'⟩ := n4b_norms hK hc.ς2 hc.ς01 hc.ςK hc.ςs hL0.le hf1 hm0 hG0 hfmE hGsq.ge
  -- interpolated bound on `H_i`
  have hHi : eLpNorm (E.indicator (kernelConvDeriv d s i ψ)) 2 volume ≤
      ENNReal.ofReal (C₂ * (cb * (A ^ (1 - κ) * (A + G) ^ κ))) := by
    refine (hH i p ψ (hψ2.of_le (by norm_num)) hψc hψsupp hm0 (by positivity) hψ0 hΓψ).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have ha : m ≤ cb * A := by
      have : Real.sqrt N ≤ cb := by
        have := Real.sqrt_nonneg (d : ℝ)
        have h2 : 0 ≤ Real.sqrt d * K * Real.sqrt N := by positivity
        rw [hcb]; linarith
      rw [hmdef]; exact mul_le_mul_of_nonneg_right this hA
    have hb : m + Real.sqrt d * (G + K * m) ≤ cb * (A + G) := by
      have h1 : m + Real.sqrt d * (G + K * m) =
          (Real.sqrt N + Real.sqrt d * K * Real.sqrt N) * A + Real.sqrt d * G := by
        rw [hmdef]; ring
      rw [h1]
      have h2 : 0 ≤ Real.sqrt d * K * Real.sqrt N := by positivity
      have h3 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      have h4 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
      rw [hcb]
      nlinarith [mul_nonneg h3 hG0, mul_nonneg (add_nonneg h4 h2) hA, mul_nonneg hA h3,
        mul_nonneg hG0 h4, mul_nonneg hG0 h2]
    exact mul_le_mul_of_nonneg_left
      (n4b_prod_bound hκ0 hκ1.le hcb0 hA hG0 hm0 ha hb (by positivity)) hC₂
  -- the near field
  have hρb : ∀ y, |ρ' y| ≤ Cρ := fun y => by
    refine (hr.dec0 y).trans ?_
    have : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
        (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
    calc Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ Cρ * 1 := by gcongr
      _ = Cρ := mul_one _
  have hθc : HasCompactSupport θ :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hc.θs
  have hh0 : 0 ≤ C₂ * (cb * (A ^ (1 - κ) * (A + G) ^ κ)) := by positivity
  have hnear := n4b_near hs0 hsd i j hr.c1 hCρ hρb hψ2 hψc hf1 hc.θ1 hθc hEm hc.θs hLθ
    (fun y => by rw [abs_of_nonneg (hc.θ01 y).1]; exact (hc.θ01 y).2) (hc.θL j) hh0 hG0 hm0 hHi
    (hG' j) hfmE
  refine hnear.trans ?_
  rw [← hGsq]
  exact n4b_near_final hκ1 hCρ hC₂ hcb0 hLθ (Real.sqrt_nonneg _) hA hG0 hε (hy G A hG0 hA)

end HRS.MS.UniqN4b
