import HRS.Energy.KIDAux2
import HRS.Stochastic.SelectedLawFKE

/-!
# KID helper file 3: the pair term `Fpp` and its Itô calculus (part C of the plan)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Pair

/-- The pair sum on the covering space, for a kernel `H` on `ℝ^d`. -/
def pairSum (N : ℕ) (H : Euc d → ℝ) (Y : Fin N → Euc d) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, H (Y i - Y j)

/-- The coordinate-difference map `Y ↦ Y_i - Y_j`. -/
def diffCLM (d N : ℕ) (i j : Fin N) : (Fin N → Euc d) →L[ℝ] Euc d :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j

theorem diffCLM_apply (i j : Fin N) (Y : Fin N → Euc d) : diffCLM d N i j Y = Y i - Y j := rfl

theorem iteratedFDeriv_pairSum {H : Euc d → ℝ} {n : ℕ} (hH : ContDiff ℝ n H) (Y : Fin N → Euc d)
    (m : Fin n → (Fin N → Euc d)) :
    iteratedFDeriv ℝ n (pairSum N H) Y m =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        iteratedFDeriv ℝ n H (Y i - Y j) (fun a => m a i - m a j) := by
  have hc : ∀ i j : Fin N, ContDiff ℝ n (H ∘ ⇑(diffCLM d N i j)) := fun i j =>
    hH.comp (diffCLM d N i j).contDiff
  have e : pairSum N H = fun Z => (1 / (2 * (N : ℝ) ^ 2)) • ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
      (H ∘ ⇑(diffCLM d N i j)) Z := by
    funext Z; simp [pairSum, diffCLM_apply]
  rw [e, iteratedFDeriv_const_smul_apply' (hf := ?_), iteratedFDeriv_fun_sum_apply]
  · simp only [smul_apply, sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_fun_sum_apply]
    · simp only [sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hH Y le_rfl]
      rfl
    · exact fun j _ => (hc i j).contDiffAt
  · exact fun i _ => (ContDiff.sum fun j _ => hc i j).contDiffAt
  · exact (ContDiff.sum fun i _ => ContDiff.sum fun j _ => hc i j).contDiffAt

theorem fderiv_pairSum {H : Euc d → ℝ} (hH : ContDiff ℝ 1 H) (Y v : Fin N → Euc d) :
    fderiv ℝ (pairSum N H) Y v = (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      fderiv ℝ H (Y i - Y j) (v i - v j) := by
  have := iteratedFDeriv_pairSum (N := N) hH Y (fun _ : Fin 1 => v)
  simpa [iteratedFDeriv_one_apply] using this

theorem fderiv2_pairSum {H : Euc d → ℝ} (hH : ContDiff ℝ 2 H) (Y u v : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (pairSum N H)) Y u v = (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      fderiv ℝ (fderiv ℝ H) (Y i - Y j) (u i - u j) (v i - v j) := by
  have := iteratedFDeriv_pairSum (N := N) hH Y ![u, v]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this

theorem fderiv_odd_of_even {H : Euc d → ℝ} (hH : Differentiable ℝ H) (hev : ∀ w, H (-w) = H w)
    (w : Euc d) : fderiv ℝ H (-w) = -fderiv ℝ H w := by
  have h1 : HasFDerivAt (fun w => H (-w)) ((fderiv ℝ H (-w)).comp (-ContinuousLinearMap.id ℝ (Euc d))) w :=
    (hH (-w)).hasFDerivAt.comp w (hasFDerivAt_id w).neg
  have e : (fun w => H (-w)) = H := funext hev
  rw [e] at h1
  rw [h1.fderiv]
  ext u
  simp

theorem grad_odd {h : Torus d → ℝ} (h1 : Torus.IsCk 1 h) (hev : ∀ x, h (-x) = h x) (x : Torus d) :
    Torus.grad h (-x) = -Torus.grad h x := by
  have hx : x = Torus.mk (Torus.rep x) := (Torus.mk_rep x).symm
  have hd : Differentiable ℝ (Torus.lift h) := (show ContDiff ℝ 1 (Torus.lift h) from h1).differentiable one_ne_zero
  rw [hx, ← HRS.KernelGrad.mk_neg, grad_mk, grad_mk]
  apply ext_inner_right ℝ
  intro v
  rw [inner_neg_left, inner_gradient', inner_gradient', fderiv_odd_of_even hd (lift_even hev)]
  simp

theorem inner_grad_mk {h : Torus d → ℝ} (w u : Euc d) :
    fderiv ℝ (Torus.lift h) w u = inner ℝ (Torus.grad h (Torus.mk w)) u := by
  rw [grad_mk, inner_gradient']

/-- The mean pair force `P_i = N⁻¹ ∑_{j ≠ i} ∇h(x_i - x_j)`. -/
def Pvec (h : Torus d → ℝ) (X : Config d N) (i : Fin N) : Euc d :=
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, Torus.grad h (X i - X j)

theorem isCk1_of_smooth {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) : Torus.IsCk 1 h :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))

theorem isCk2_of_smooth {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) : Torus.IsCk 2 h :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm) two_le_top

theorem fderiv_ppLift {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (Y v : Fin N → Euc d) :
    fderiv ℝ (pairSum N (Torus.lift h)) Y v =
      (1 / (N : ℝ)) * ∑ i, inner ℝ (Pvec h (fun i => Torus.mk (Y i)) i) (v i) := by
  have h1 := isCk1_of_smooth hsm
  rw [fderiv_pairSum (show ContDiff ℝ 1 (Torus.lift h) from h1)]
  set g : Fin N → Fin N → Euc d := fun i j => Torus.grad h (Torus.mk (Y i) - Torus.mk (Y j)) with hg
  have e1 : ∀ i j, fderiv ℝ (Torus.lift h) (Y i - Y j) (v i - v j) = inner ℝ (v i - v j) (g i j) := by
    intro i j
    rw [inner_grad_mk, HRS.KernelGrad.mk_sub, real_inner_comm]
  have hodd : ∀ i j, g j i = -g i j := by
    intro i j
    simp only [hg]
    rw [← grad_odd h1 hev, neg_sub]
  simp_rw [e1]
  have hs := sum_inner_offdiag_symm v g hodd
  have hS : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i - v j) (g i j) =
      2 * ∑ i, inner ℝ (v i) (∑ j ∈ Finset.univ.erase i, g i j) := by
    simp_rw [inner_sum]
    linarith
  rw [hS]
  unfold Pvec
  simp only [inner_smul_left, RCLike.conj_to_real, ← Finset.mul_sum, real_inner_comm (v _)]
  have hN : (N : ℝ) ≠ 0 ∨ N = 0 := by
    by_cases h : N = 0
    · exact Or.inr h
    · exact Or.inl (by exact_mod_cast h)
  rcases hN with hN | hN
  · simp only [inner_smul_right, ← Finset.mul_sum]
    field_simp
    rfl
  · subst hN; simp

theorem sum_noise_pair (D : DynData d) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {i j : Fin N} (hij : i ≠ j) :
    ∑ k : Fin N × Fin d, B (liftedNoise D k i - liftedNoise D k j) (liftedNoise D k i - liftedNoise D k j)
      = 2 * (2 * D.invβ) * ∑ a : Fin d, B (EuclideanSpace.single a 1) (EuclideanSpace.single a 1) := by
  have hc : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ :=
    Real.sq_sqrt (by have := D.hβ; positivity)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_add i j hij]
  · simp only [liftedNoise_apply, if_true, if_neg hij, if_neg hij.symm, sub_zero, zero_sub,
      map_neg, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.neg_apply, neg_neg, neg_mul, mul_neg]
    linear_combination (B (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)) * hc +
      (B (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)) * hc
  · intro l _ hl
    simp [liftedNoise_apply, hl.1.symm, hl.2.symm]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_fderiv2_pairSum (D : DynData d) {H : Euc d → ℝ} (hH : ContDiff ℝ 2 H)
    (Y : Fin N → Euc d) :
    ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (pairSum N H)) Y (liftedNoise D k) (liftedNoise D k)
      = (2 * D.invβ) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          Laplacian.laplacian H (Y i - Y j)) := by
  simp_rw [fderiv2_pairSum hH, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ y : Fin N, ∑ x : Fin N × Fin d, ∑ j ∈ Finset.univ.erase y,
      ((fderiv ℝ (fderiv ℝ H) (Y y - Y j)) (liftedNoise D x y - liftedNoise D x j))
        (liftedNoise D x y - liftedNoise D x j) = ∑ j ∈ Finset.univ.erase y,
      2 * (2 * D.invβ) * Laplacian.laplacian H (Y y - Y j) := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [sum_noise_pair D (fderiv ℝ (fderiv ℝ H) (Y y - Y j)) (Finset.ne_of_mem_erase hj).symm,
      laplacian_eq_sum_fderiv]
  simp_rw [e]
  simp only [← Finset.mul_sum]
  ring

end Pair

section ItoPath

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}

/-- Pathwise Itô formula for a `C^{1,2}` configuration functional `Φ` along a filtered strong solution,
on the horizon `t ≤ T`, with the martingale part as an `L²` Itô integral of the reference integrand. -/
theorem kid_ito_pathwise (hV : Torus.IsCk 2 D.V) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hC : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (Φ : ℝ → Config d N → ℝ) (hΦc : IsC12On t Set.univ (configLift Φ))
    {C1 : ℝ} (hC1 : ∀ s ∈ Set.Icc 0 t, ∀ Y, ‖fderiv ℝ (configLift Φ s) Y‖ ≤ C1) :
    IsProgressiveL2 P ℱ (fun s ω k => fkeRef D t Φ X s ω k) ∧
    ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => fkeSample D t Φ X s ω) (Set.Icc 0 t) ∧
      ∀ τ : ℝ≥0, (τ : ℝ) ≤ t →
        Φ (τ : ℝ) (X τ ω) = Φ 0 (X 0 ω) + (∫ s in Set.Icc (0:ℝ) τ, fkeSample D t Φ X s ω)
          + itoIntegral P ℱ W' (fun s ω k => fkeRef D t Φ X s ω k) (τ : ℝ) ω := by
  have hΨprog := isProgressive_fkeRef hF.progressive ht0 D Φ hΦc
  have hΨL2 : IsProgressiveL2 P ℱ (fun s ω k => fkeRef D t Φ X s ω k) :=
    IsProgressiveL2.of_bounded P hΨprog (max C1 0 * ∑ j : Fin N × Fin d, ‖liftedNoise D j‖)
      (fun s ω k => fkeRef_bound ht0 D Φ hC1 s ω k)
  refine ⟨hΨL2, ?_⟩
  have hlift := hC.ae_lift_eq hF
  have hI0 : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 t) :=
    hC.ae_integrableOn_drift ht0 htT
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t →
      intPart D X τ ω = ∫ s in Set.Icc (0 : ℝ) (τ : ℝ), driftProc D X (Real.toNNReal s) ω := by
    filter_upwards [hI0] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ (hτ.trans htT)]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  have hZint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t →
      liftProcM D W' X τ ω = liftProcM D W' X 0 ω
        + (∫ s in Set.Icc (0 : ℝ) τ, driftProc D X (Real.toNNReal s) ω)
        + ∑ k, (W' τ ω k - W' 0 ω k) • liftedNoise D k := by
    filter_upwards [hint] with ω hω τ hτ
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hω τ hτ]
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (liftProcM D W' X 0) := by
    intro s
    have e : liftProcM D W' X 0 = fun ω => fun i => Torus.rep (X 0 ω i) :=
      funext fun ω => liftProcM_zero ω
    rw [e]
    have hg : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
      measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
    exact hg.comp (hF.measurable_init s)
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := t) ht0 (configLift Φ) hΦc
    (liftedNoise D) (liftProcM D W' X) (measurable_liftProcM hV hF) hX₀ (driftProc D X)
    (isProgressive_driftProc hV hF) hI0 hZint
  obtain ⟨N0, hN0m, hN0P, hN0⟩ := exists_null_of_ae (P := P)
    (p := fun ω => ∀ τ : ℝ≥0, (τ : ℝ) ≤ t → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i)) hlift'
  have hcongr := localItoIntegral_congr_null hF.brownian hΨL2.locL2 hN0m hN0P
    (Ψ := itoIntegrand t Set.univ (configLift Φ) (ofNNRealTime (liftProcM D W' X))
      (fun _ _ => liftedNoise D))
    (fun s ω hω => by
      funext k
      exact itoIntegrand_eq_fkeRef D Φ W' X ω (hN0 ω hω) s k)
    (fun s hs ω => by
      have hn : s ∉ Set.Icc (0:ℝ) t := fun h => absurd h.1 (not_le.2 hs)
      funext k
      simp [itoIntegrand, hn])
    (fun s hs ω => by
      have hn : s ∉ Set.Icc (0:ℝ) t := fun h => absurd h.1 (not_le.2 hs)
      funext k
      simp [fkeRef, hn])
  have hloc := localItoIntegral_eq_itoIntegral hF.brownian hΨL2
  filter_upwards [hito, hlift', hcongr, hloc] with ω hωito hω h1 h2
  refine ⟨?_, fun τ hτ => ?_⟩
  · refine hωito.1.congr_fun (fun s hs => ?_) measurableSet_Icc
    have hsτ : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ t := by
      rw [Real.coe_toNNReal _ hs.1]; exact hs.2
    have hx := hω _ hsτ
    dsimp only
    rw [itoDrift_eq_fkeIto D t Φ (liftProcM D W' X) X ω s hx]
    unfold fkeSample
    rw [clampTI_of_mem hs]
    have hmk : ∀ i, Torus.mk (repC (X (Real.toNNReal s) ω) i)
        = Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i) := by
      intro i
      show Torus.mk (Torus.rep (X (Real.toNNReal s) ω i)) = _
      rw [Torus.mk_rep]
      exact congrFun hx i
    exact (fkeIto_eq_of_mk D t Φ s hmk).symm
  · have h := hωito.2 τ hτ
    have hL : configLift Φ (τ : ℝ) (liftProcM D W' X τ ω) = Φ (τ : ℝ) (X τ ω) := by
      show Φ (τ : ℝ) (fun i => Torus.mk (liftProcM D W' X τ ω i)) = Φ (τ : ℝ) (X τ ω)
      rw [← hω τ hτ]
    have hcol0 : configLift Φ 0 (liftProcM D W' X 0 ω) = Φ 0 (X 0 ω) := by
      have h0 := hω 0 (by simpa using ht0)
      show Φ 0 (fun i => Torus.mk (liftProcM D W' X 0 ω i)) = Φ 0 (X 0 ω)
      rw [h0]
    have hint2 : ∫ s in Set.Icc (0:ℝ) τ, itoDrift t (configLift Φ)
        (ofNNRealTime (liftProcM D W' X)) (ofNNRealTime (driftProc D X))
        (fun _ _ => liftedNoise D) s ω = ∫ s in Set.Icc (0:ℝ) τ, fkeSample D t Φ X s ω := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hsτ : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ t := by
        rw [Real.coe_toNNReal _ hs.1]
        exact hs.2.trans hτ
      have hx := hω _ hsτ
      rw [itoDrift_eq_fkeIto D t Φ (liftProcM D W' X) X ω s hx]
      unfold fkeSample
      rw [clampTI_of_mem ⟨hs.1, hs.2.trans hτ⟩]
      have hmk : ∀ i, Torus.mk (repC (X (Real.toNNReal s) ω) i)
          = Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i) := by
        intro i
        show Torus.mk (Torus.rep (X (Real.toNNReal s) ω i)) = _
        rw [Torus.mk_rep]
        exact congrFun hx i
      exact (fkeIto_eq_of_mk D t Φ s hmk).symm
    rw [hL, hcol0, hint2, h1 (τ : ℝ), h2 (τ : ℝ)] at h
    exact h

end ItoPath

section PairIto

/-- The torus pair term `(2N²)⁻¹ ∑_{i≠j} h(x_i - x_j)`. -/
def Fpp (h : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i - X j)

/-- The time-independent configuration functional of the pair term. -/
def Φpp (h : Torus d → ℝ) : ℝ → Config d N → ℝ := fun _ X => Fpp h X

theorem configLift_Φpp (h : Torus d → ℝ) (s : ℝ) :
    configLift (Φpp (N := N) h) s = pairSum N (Torus.lift h) := by
  funext Y
  simp only [configLift, Φpp, Fpp, pairSum, Torus.lift, Function.comp]
  simp only [HRS.KernelGrad.mk_sub]

theorem contDiff_pairSum {H : Euc d → ℝ} {n : WithTop ℕ∞} (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (pairSum N H) := by
  unfold pairSum
  refine contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_)
  exact hH.comp (diffCLM d N i j).contDiff

/-- The pair-term part of the Itô drift. -/
def ppDrift (D : DynData d) (h : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, inner ℝ (Pvec h X i) (particleDrift D X i) +
    D.invβ * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j))

theorem fkeIto_pp (D : DynData d) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (t s : ℝ) (Y : Fin N → Euc d) :
    fkeIto D t (Φpp h) s Y = ppDrift D h (fun i => Torus.mk (Y i)) := by
  have hc : configLift (Φpp (N := N) h) = fun _ => pairSum N (Torus.lift h) :=
    funext (configLift_Φpp h)
  have hH2 : ContDiff ℝ 2 (Torus.lift h) := isCk2_of_smooth hsm
  unfold fkeIto
  simp only [hc, derivWithin_const]
  rw [fderiv_ppLift hsm hev, sum_fderiv2_pairSum D hH2]
  unfold ppDrift driftVec
  simp_rw [← HRS.KernelGrad.mk_sub, laplacian_mk h]
  have h0 : derivWithin (fun _ : ℝ => pairSum N (Torus.lift h) Y) (Icc 0 t) s = 0 := by simp
  rw [h0]
  ring

theorem fkeSample_pp (D : DynData d) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (t : ℝ) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (s : ℝ) (ω : Ω) :
    fkeSample D t (Φpp h) X s ω = ppDrift D h (X (Real.toNNReal s) ω) := by
  unfold fkeSample
  rw [fkeIto_pp D hsm hev, mk_repC]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}

theorem kid_pp_ito (hV : Torus.IsCk 2 D.V) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hC : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    IsProgressiveL2 P ℱ (fun s ω k => fkeRef D t (Φpp h) X s ω k) ∧
    ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => ppDrift D h (X (Real.toNNReal s) ω)) (Set.Icc 0 t) ∧
      ∀ τ : ℝ≥0, (τ : ℝ) ≤ t →
        Fpp h (X τ ω) = Fpp h (X 0 ω) + (∫ s in Set.Icc (0:ℝ) τ, ppDrift D h (X (Real.toNNReal s) ω))
          + itoIntegral P ℱ W' (fun s ω k => fkeRef D t (Φpp h) X s ω k) (τ : ℝ) ω := by
  have hH2 : ContDiff ℝ 2 (Torus.lift h) := isCk2_of_smooth hsm
  have hc : configLift (Φpp (N := N) h) = fun _ => pairSum N (Torus.lift h) :=
    funext (configLift_Φpp h)
  have hΦc : IsC12On t Set.univ (configLift (Φpp (N := N) h)) := by
    rw [hc]
    exact isC12On_of_contDiff t Set.univ (pairSum N (Torus.lift h)) (contDiff_pairSum hH2)
  obtain ⟨C1, hC1⟩ := bounded_of_periodic (T := t) (fun s Y => fderiv ℝ (configLift (Φpp (N := N) h) s) Y)
    hΦc.cont_fderiv (fun s Y v hv => fderiv_configLift_add_lattice (Φpp (N := N) h) s hv Y)
  obtain ⟨h1, h2⟩ := kid_ito_pathwise hV ht0 htT hC hF (Φpp h) hΦc (C1 := C1)
    (fun s hs Y => hC1 s hs Y)
  refine ⟨h1, ?_⟩
  filter_upwards [h2] with ω hω
  simp only [fkeSample_pp D hsm hev] at hω
  refine ⟨hω.1, fun τ hτ => ?_⟩
  have := hω.2 τ hτ
  simpa [Φpp, Fpp] using this

end PairIto

section FIto

/-- The time derivative of `f_r = h * ρ_r`: `ft r x = wkG(ρ, ψ_x)(r)`. -/
def ftK (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ :=
  wkG D ρ (psi h x) r

/-- The drift of `⟨empirical X, f_r⟩` as an explicit finite sum (for configurations, at time `r`). -/
def fDrift (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (ftK D h ρ r (X i) + D.invβ * Torus.laplacian (fK h ρ r) (X i) +
    inner ℝ (Torus.grad (fK h ρ r) (X i)) (particleDrift D X i))

theorem drift_f_eq (D : DynData d) {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {r : ℝ} (hr : r ∈ Set.Icc 0 t) (X : Config d N)
    (hcol : X ∉ collisionSet d N ∨ D.M = 0) :
    pair (empirical X) (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
          - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
      + interactionPairing D (f r) (empirical X) (empirical X)
    = (1 / (N : ℝ)) * ∑ i, (ft r (X i) + D.invβ * Torus.laplacian (f r) (X i) +
        inner ℝ (Torus.grad (f r) (X i)) (particleDrift D X i)) := by
  have hc2 : ContDiff ℝ 2 (Torus.lift (f r)) := hf.c2 r hr
  have hN0 : 0 < N := by omega
  have hY : ∀ i, Torus.mk (repC X i) = X i := fun i => by
    show Torus.mk (Torus.rep (X i)) = X i
    exact Torus.mk_rep _
  have h := drift_pointwise (D := D) hN ht hf hr X (repC X) hY hcol
  rw [← h, derivWithin_empiricalLift ht hf hr, empiricalLift_eq, fderiv_sumLift_lift_apply hc2,
    sum_fderiv_fderiv_sumLift_liftedNoise D hc2]
  simp only [sum_lap_eq, hY]
  rw [show ∑ i, (ft r (X i) + D.invβ * Torus.laplacian (f r) (X i) +
      inner ℝ (Torus.grad (f r) (X i)) (particleDrift D X i)) =
      ∑ i, ft r (X i) + D.invβ * ∑ i, Torus.laplacian (f r) (X i) +
        ∑ i, inner ℝ (Torus.grad (f r) (X i)) (particleDrift D X i) by
    simp [Finset.sum_add_distrib, Finset.mul_sum]]
  ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem nullContact_of_strong (hsol : IsStrongSolution P D T X₀ W X) : NullContactOccupation P T X := by
  filter_upwards [hsol.no_collision] with ω hω
  have : {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ω ∈ collisionSet d N} = ∅ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hs
    exact hω _ (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  rw [this]
  exact measure_empty

theorem kid_f_ito (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t (fK h ρ) X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r : ℝ => fDrift D h ρ r (X (Real.toNNReal r) ω)) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) (fK h ρ τ)
        = pair (empirical (X 0 ω)) (fK h ρ 0)
          + (∫ r in (0:ℝ)..τ, fDrift D h ρ r (X (Real.toNNReal r) ω))
          + empiricalMartingale P ℱ W' D t (fK h ρ) X (Real.toNNReal τ) ω := by
  have htI : t ∈ Set.Icc 0 T := ⟨ht0.le, htT⟩
  have hf := c.isC12Test hsm hev htI
  obtain ⟨hprog, hmain⟩ := empirical_ito_of_contact hN c.hV hsol.toContact hF
    (Or.inr (nullContact_of_strong hsol)) htI hf
  refine ⟨hprog, ?_⟩
  filter_upwards [hmain, hsol.no_collision] with ω hω hcol
  intro τ hτ
  obtain ⟨hint, hid⟩ := hω τ hτ
  have hpt : ∀ r ∈ Set.Icc (0:ℝ) τ, pair (empirical (X (Real.toNNReal r) ω))
      (fun x => ftK D h ρ r x + D.invβ * Torus.laplacian (fK h ρ r) x
        - inner ℝ (Torus.grad D.V x) (Torus.grad (fK h ρ r) x))
      + interactionPairing D (fK h ρ r) (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω)) = fDrift D h ρ r (X (Real.toNNReal r) ω) := by
    intro r hr
    have hrt : r ∈ Set.Icc 0 t := ⟨hr.1, hr.2.trans hτ.2⟩
    exact drift_f_eq D hN ht0 hf hrt _ (Or.inl (hcol _ (by
      rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans (hτ.2.trans htT))))
  refine ⟨hint.congr_fun (fun r hr => hpt r hr) measurableSet_Icc, ?_⟩
  rw [hid]
  congr 2
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le hτ.1] at hr
  exact hpt r hr

end FIto

end HRS.KID
