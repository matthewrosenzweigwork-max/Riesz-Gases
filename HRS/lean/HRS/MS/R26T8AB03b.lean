import HRS.MS.R26T8AB03a

/-!
# S8.2 T8A B03 (part b): age FTC for the coordinates of the configuration gradient at a fixed collision-free configuration
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b03_ftc_gen (φ φ' : ℝ → ℝ) (s0 T : ℝ) (hs0 : 0 ≤ s0)
    (hder : ∀ v : ℝ, 0 ≤ v → HasDerivWithinAt φ (φ' v) (Set.Ici 0) v)
    (hcont' : ContinuousOn (fun t : ℝ => φ' (s0 + t)) (Set.Icc 0 T)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, φ (s0 + t) = φ (s0 + 0) + ∫ s in Set.Icc 0 t, φ' (s0 + s) := by
  intro t ht
  have hlin : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun u : ℝ => φ (s0 + u)) (φ' (s0 + s)) (Set.Ici 0) s := by
    intro s hs
    have hl : HasDerivWithinAt (fun u : ℝ => s0 + u) 1 (Set.Ici 0) s :=
      ((hasDerivAt_id s).const_add s0).hasDerivWithinAt
    have h2 := (hder (s0 + s) (by linarith)).scomp s hl (fun u hu => by simp only [Set.mem_Ici] at *; linarith)
    have e : (1 : ℝ) • φ' (s0 + s) = φ' (s0 + s) := one_smul _ _
    rw [e] at h2
    exact h2
  have hcontφ : ContinuousOn (fun u : ℝ => φ (s0 + u)) (Set.Icc 0 t) :=
    fun u hu => ((hlin u hu.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun u : ℝ => φ' (s0 + u)) volume 0 t :=
    (hcont'.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcontφ
    (fun u hu => (hlin u hu.1.le).mono (fun y hy => Set.mem_Ici.2 (le_trans hu.1.le (le_of_lt hy)))) hint
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1, hftc]
  ring

set_option maxHeartbeats 12800000 in
theorem r26t8a_b03_cg_ftc (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    (x : EucConfig d N) (hx : x ∉ eucCollisionSet d N) (s0 T : ℝ) (hs0 : 0 ≤ s0) (i : Fin N) (k : Fin d) :
    ContinuousOn (fun t : ℝ => Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (s0 + t)) x i k)
      (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (s0 + t)) x i k =
      Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (s0 + 0)) x i k +
        ∫ s in Set.Icc 0 t, Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (s0 + s)) x i k := by
  obtain ⟨hQc, hQd, -, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 0 (by norm_num)
  have hH := r26t8a_o04_H_contOn d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
    (by norm_num) i k
  have hpath : ContinuousOn (fun t : ℝ => (s0 + t, x)) (Set.Icc 0 T) :=
    ((continuous_const.add continuous_id).prodMk continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun t : ℝ => (s0 + t, x)) (Set.Icc 0 T) (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) :=
    fun t ht => ⟨by simp only [Set.mem_Ici]; linarith [ht.1], hx⟩
  have hcont' : ContinuousOn (fun t : ℝ => Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (s0 + t)) x i k)
      (Set.Icc 0 T) :=
    ContinuousOn.comp (g := fun q : ℝ × EucConfig d N =>
      Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 q.1) q.2 i k)
      (f := fun t : ℝ => (s0 + t, x)) hH hpath hmaps
  refine ⟨hcont', ?_⟩
  -- the derivative in age
  let e : EucConfig d N := r26t8a_o03b_iota d N i (EuclideanSpace.single k (1 : ℝ))
  let m1 : Fin 1 → EucConfig d N := fun _ => e
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => EucConfig d N) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun A => A m1
        map_add' := fun A B => rfl
        map_smul' := fun r A => rfl }
      (∏ i, ‖m1 i‖) (fun A => by simpa [mul_comm] using A.le_opNorm m1)
  have hev : ∀ (g : EucConfig d N → ℝ), DifferentiableAt ℝ g x →
      ev (iteratedFDeriv ℝ 1 g x) = Phase2S82.configGrad g x i k := by
    intro g hg
    rw [r26t8a_o04_cg_coord hg i k]
    show iteratedFDeriv ℝ 1 g x m1 = _
    rw [iteratedFDeriv_one_apply]
  have hdiff : ∀ v : ℝ, 0 ≤ v → ∀ jj : ℕ, jj ≤ 1 →
      DifferentiableAt ℝ (r26t8a_QAge (N := N) a beta m rho Psi alpha jj v) x := by
    intro v hv jj hjj
    obtain ⟨A, hA⟩ : ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha jj v) :=
      ⟨_, horb.bound alpha v hv jj (by omega)⟩
    exact (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hA hx).differentiableAt (by norm_num)
  have hder : ∀ v : ℝ, 0 ≤ v → HasDerivWithinAt
      (fun u => Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 u) x i k)
      (Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 v) x i k) (Set.Ici 0) v := by
    intro v hv
    have h0 := hQd x hx v hv 1 (by norm_num)
    have h1 := ev.hasFDerivAt.comp_hasDerivWithinAt v h0
    refine (h1.congr (fun u hu => ?_) ?_).congr_deriv ?_
    · exact (hev _ (hdiff u hu 0 (by norm_num))).symm
    · exact (hev _ (hdiff v hv 0 (by norm_num))).symm
    · exact hev _ (hdiff v hv 1 le_rfl)
  exact r26t8a_b03_ftc_gen _ _ s0 T hs0 hder hcont'

end HRS.MS.R26T8A

end
