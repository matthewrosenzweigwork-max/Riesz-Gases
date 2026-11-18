import HRS.Sections.AdjKEAux3

/-!
# ADJKE part 4: the integrated forcing is locally Lipschitz in the terminal time

Along a collision-free continuous path with the forcing integrand interval integrable for every terminal time `t ∈ [0,T]`,
`t ↦ evolvingForcingCoord k t` is Lipschitz on `[0,T]` (locally in `t`, unit-length windows):
`D_t - D_{t'} = -∫_{t'}^t g_t - ∫_0^{t'} (g_t - g_{t'})`, with `|g_t| ≤ B` and `|g_t - g_{t'}| ≤ B' (t - t')`
(`adjke_E_bound`, `adjke_E_sub`, `adjke_prop_stab`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The forcing integrand `r ↦ √N F_N^{h_{∇U^{r,t}e_k}}(X_r, ρ_r)` along a path. -/
def adjkeG (D : DynData d) (ρ : ℝ → Torus d → ℝ) {N : ℕ} (Xp : ℝ≥0 → Config d N) (k : NonzeroLattice d)
    (t r : ℝ) : ℝ :=
  Real.sqrt N * modulatedEnergy
    (commKernel (periodicRieszGrad d D.s) (Torus.grad (propagator D ρ r t (Torus.realMode k))))
    (Xp r.toNNReal) (withDensityReal (ρ r))

/-- The forcing coordinate along a path (`evolvingForcingCoord` with the path of one sample point). -/
def adjkeD (D : DynData d) (ρ : ℝ → Torus d → ℝ) {N : ℕ} (Xp : ℝ≥0 → Config d N) (k : NonzeroLattice d)
    (t : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..t, -(adjkeG D ρ Xp k t r)

theorem adjkeD_eq {Ω : Type*} {N : ℕ} (D : DynData d) (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (k : NonzeroLattice d) (t : ℝ) (ω : Ω) :
    evolvingForcingCoord D ρ X k t ω = adjkeD D ρ (fun u => X u ω) k t := rfl

theorem adjke_forcing_lipschitz (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {N : ℕ}
    (hN : 0 < N) (T : ℝ) (hT : 0 < T) (k : NonzeroLattice d) (Xp : ℝ≥0 → Config d N)
    (hXc : ∀ i, Continuous fun u : ℝ≥0 => Xp u i)
    (hcol : ∀ u : ℝ≥0, (u : ℝ) ≤ T → Xp u ∉ collisionSet d N)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) T, IntervalIntegrable (adjkeG htr.dyn ρ Xp k t) volume 0 t) :
    ∃ Lc : ℝ, ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ T → t - t' ≤ 1 →
      |adjkeD htr.dyn ρ Xp k t - adjkeD htr.dyn ρ Xp k t'| ≤ Lc * (t - t') := by
  have hd1 : 1 ≤ d := by omega
  have hφ : Torus.IsSmooth (Torus.realMode k) := HRS.FieldSingAux.isSmooth_realMode k
  set φ : Torus d → ℝ := Torus.realMode k with hφdef
  obtain ⟨cstar, A, I, hA, hI0, hEb⟩ := adjke_E_bound hd htr.dyn.hs0 htr.dyn.hsd hN
  obtain ⟨c₀, hc₀, Λρ, hρbd⟩ := Q40b.q40b_rho_bounds hd1 htr
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
    (Q40b.q40b_jointCont hd1 htr T)
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hρle : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ρ r y ≤ Λ' := fun r hr y =>
    ((le_abs_self _).trans (by simpa using hΛ (r, y) ⟨hr, mem_univ _⟩)).trans (le_max_left _ _)
  obtain ⟨Λ₂, -, -, hpack⟩ := dyncmp_adjoint_package hd htr T
  obtain ⟨Cφ, hCφ⟩ := hpack φ hφ
  obtain ⟨K, hK0, hK⟩ := adjke_prop_stab hd htr T hT hφ
  -- the pair sum is bounded along the path
  have hcont : ContinuousOn (fun r : ℝ => adjkePairSum d htr.dyn.s cstar (Xp r.toNNReal)) (Set.Icc 0 T) := by
    unfold adjkePairSum
    refine continuousOn_const.mul (continuousOn_finset_sum _ fun i _ =>
      continuousOn_finset_sum _ fun j hj => ?_)
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    refine ContinuousOn.add ?_ continuousOn_const
    intro r hr
    have hz : Xp r.toNNReal i - Xp r.toNNReal j ≠ 0 := sub_ne_zero.2 (fun h =>
      hcol r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2) ⟨i, j, hij, h⟩)
    have hXi : Continuous fun r : ℝ => Xp r.toNNReal i := (hXc i).comp continuous_real_toNNReal
    have hXj : Continuous fun r : ℝ => Xp r.toNNReal j := (hXc j).comp continuous_real_toNNReal
    exact ((adjke_riesz_continuousAt hd htr.dyn.hs0 htr.dyn.hsd hz).comp
      (f := fun r : ℝ => Xp r.toNNReal i - Xp r.toNNReal j) (hXi.sub hXj).continuousAt).continuousWithinAt
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C0' : ℝ := max C0 0 with hC0'
  have hpair : ∀ r ∈ Set.Icc (0 : ℝ) T, adjkePairSum d htr.dyn.s cstar (Xp r.toNNReal) ≤ C0' := fun r hr =>
    ((le_abs_self _).trans (by simpa using hC0 r hr)).trans (le_max_left _ _)
  set Cc : ℝ := A * (C0' + 3 / 2 * Λ' * I) with hCc
  have hCc0 : 0 ≤ Cc := by
    refine mul_nonneg hA ?_
    have : 0 ≤ Λ' := le_max_right _ _
    have : 0 ≤ C0' := le_max_right _ _
    positivity
  -- energy bounds for gradients of `C²` functions
  have hEg : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f →
      RowOK (withDensityReal (ρ r)) (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad f)) ∧
      |modulatedEnergy (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad f)) (Xp r.toNNReal)
          (withDensityReal (ρ r))| ≤ Torus.cbNorm 2 f * Cc := by
    intro r hr f hf
    have hf1 : Torus.IsCk 1 f := PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hf
    have hlip : IsLipschitzVF (Torus.cbNorm 2 f) (Torus.grad f) :=
      Q40b.q40b_grad_lip hf fun y => PDE.ET.norm_iteratedFDeriv_le_cbNorm (le_refl 2) hf y
    have hcb : 0 ≤ Torus.cbNorm 2 f := PDE.cbNorm_nonneg' 2 f
    obtain ⟨h1, h2⟩ := hEb (hρbd r hr.1).1 (hρle r hr) (PDE.MFLinear.continuous_grad hf1) hcb hlip
      (Xp r.toNNReal)
    refine ⟨h1, h2.trans ?_⟩
    refine mul_le_mul_of_nonneg_left ?_ hcb
    exact mul_le_mul_of_nonneg_left (by linarith [hpair r hr]) hA
  have hEd : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ {f f' : Torus d → ℝ}, Torus.IsCk 2 f → Torus.IsCk 2 f' →
      Torus.IsCk 2 (fun x => f x - f' x) →
      |modulatedEnergy (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad f)) (Xp r.toNNReal)
          (withDensityReal (ρ r)) -
        modulatedEnergy (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad f')) (Xp r.toNNReal)
          (withDensityReal (ρ r))| ≤ Torus.cbNorm 2 (fun x => f x - f' x) * Cc := by
    intro r hr f f' hf hf' hff'
    have hf1 : Torus.IsCk 1 f := PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hf
    have hf1' : Torus.IsCk 1 f' := PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hf'
    obtain ⟨hr1, -⟩ := hEg r hr hf
    obtain ⟨hr2, -⟩ := hEg r hr hf'
    have hsub := adjke_E_sub (ρ := ρ r) (hρbd r hr.1).1 (N := N) hr1 hr2 (Xp r.toNNReal)
    have hgrad : (fun x => Torus.grad f x - Torus.grad f' x) = Torus.grad (fun x => f x - f' x) := by
      funext x; exact (PDE.MFLinear.grad_sub hf1 hf1' x).symm
    rw [hgrad] at hsub
    rw [← hsub]
    exact (hEg r hr hff').2
  -- pointwise bounds on the forcing integrand
  have hg1 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc (0 : ℝ) t,
      |adjkeG htr.dyn ρ Xp k t r| ≤ Real.sqrt N * (Cφ * Cc) := by
    intro t ht r hr
    obtain ⟨hcls, hcb⟩ := hCφ t ht
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    have hf2 := (hcls.c2 r hr)
    have hf2' : Torus.IsCk 2 (propagator htr.dyn ρ r t φ) := hf2
    have := (hEg r hrT hf2').2
    unfold adjkeG
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine mul_le_mul_of_nonneg_left (this.trans ?_) (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (hcb r hr) hCc0
  have hg2 : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ T → t - t' ≤ 1 → ∀ r ∈ Set.Icc (0 : ℝ) t',
      |adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r| ≤ Real.sqrt N * (K * Cc) * (t - t') := by
    intro t' t ht' ht't htT htt' r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans (ht't.trans htT)⟩
    obtain ⟨hCk, hcb⟩ := hK r t' t hr.1 hr.2 ht't htT htt'
    have hclst := (hCφ t ⟨ht'.trans ht't, htT⟩).1
    have hclst' := (hCφ t' ⟨ht', ht't.trans htT⟩).1
    have hf : Torus.IsCk 2 (propagator htr.dyn ρ r t φ) := hclst.c2 r ⟨hr.1, hr.2.trans ht't⟩
    have hf' : Torus.IsCk 2 (propagator htr.dyn ρ r t' φ) := hclst'.c2 r hr
    have := hEd r hrT hf hf' hCk
    unfold adjkeG
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt N * |modulatedEnergy _ _ _ - modulatedEnergy _ _ _|
        ≤ Real.sqrt N * (Torus.cbNorm 2 (fun x => propagator htr.dyn ρ r t φ x -
            propagator htr.dyn ρ r t' φ x) * Cc) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * ((K * (t - t')) * Cc) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcb hCc0) (Real.sqrt_nonneg _)
      _ = Real.sqrt N * (K * Cc) * (t - t') := by ring
  refine ⟨Real.sqrt N * (Cφ * Cc) + T * (Real.sqrt N * (K * Cc)), ?_⟩
  intro t' t ht' ht't htT htt'
  have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨ht'.trans ht't, htT⟩
  have ht'm : t' ∈ Set.Icc (0 : ℝ) T := ⟨ht', ht't.trans htT⟩
  have hI1 := hint t ht
  have hI2 := hint t' ht'm
  have hI1a : IntervalIntegrable (adjkeG htr.dyn ρ Xp k t) volume 0 t' :=
    hI1.mono_set (by
      rw [uIcc_of_le ht', uIcc_of_le (ht'.trans ht't)]
      exact Icc_subset_Icc le_rfl ht't)
  have hI1b : IntervalIntegrable (adjkeG htr.dyn ρ Xp k t) volume t' t :=
    hI1.mono_set (by
      rw [uIcc_of_le ht't, uIcc_of_le (ht'.trans ht't)]
      exact Icc_subset_Icc ht' le_rfl)
  unfold adjkeD
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg]
  have hadd : ∫ r in (0 : ℝ)..t, adjkeG htr.dyn ρ Xp k t r =
      (∫ r in (0 : ℝ)..t', adjkeG htr.dyn ρ Xp k t r) + ∫ r in t'..t, adjkeG htr.dyn ρ Xp k t r :=
    (intervalIntegral.integral_add_adjacent_intervals hI1a hI1b).symm
  have hdiff : ∫ r in (0 : ℝ)..t', (adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r) =
      (∫ r in (0 : ℝ)..t', adjkeG htr.dyn ρ Xp k t r) - ∫ r in (0 : ℝ)..t', adjkeG htr.dyn ρ Xp k t' r :=
    intervalIntegral.integral_sub hI1a hI2
  have hsplit : -(∫ r in (0 : ℝ)..t, adjkeG htr.dyn ρ Xp k t r) -
      -(∫ r in (0 : ℝ)..t', adjkeG htr.dyn ρ Xp k t' r) =
      -(∫ r in t'..t, adjkeG htr.dyn ρ Xp k t r) -
        ∫ r in (0 : ℝ)..t', (adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r) := by
    rw [hadd, hdiff]
    ring
  rw [hsplit]
  have b1 : |∫ r in t'..t, adjkeG htr.dyn ρ Xp k t r| ≤ Real.sqrt N * (Cφ * Cc) * (t - t') := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t') (b := t)
      (f := adjkeG htr.dyn ρ Xp k t) (C := Real.sqrt N * (Cφ * Cc)) (fun r hr => by
        rw [uIoc_of_le ht't] at hr
        rw [Real.norm_eq_abs]
        exact hg1 t ht r ⟨(ht'.trans hr.1.le), hr.2⟩)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht't)] at this
  have b2 : |∫ r in (0 : ℝ)..t', (adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r)| ≤
      Real.sqrt N * (K * Cc) * (t - t') * t' := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t')
      (f := fun r => adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r)
      (C := Real.sqrt N * (K * Cc) * (t - t')) (fun r hr => by
        rw [uIoc_of_le ht'] at hr
        rw [Real.norm_eq_abs]
        exact hg2 t' t ht' ht't htT htt' r ⟨hr.1.le, hr.2⟩)
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht'] at this
  have hts : 0 ≤ t - t' := sub_nonneg.2 ht't
  have hB : 0 ≤ Real.sqrt N * (K * Cc) := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hK0 hCc0)
  calc |-(∫ r in t'..t, adjkeG htr.dyn ρ Xp k t r) -
          ∫ r in (0 : ℝ)..t', (adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r)|
      ≤ |∫ r in t'..t, adjkeG htr.dyn ρ Xp k t r| +
          |∫ r in (0 : ℝ)..t', (adjkeG htr.dyn ρ Xp k t r - adjkeG htr.dyn ρ Xp k t' r)| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
    _ ≤ Real.sqrt N * (Cφ * Cc) * (t - t') + Real.sqrt N * (K * Cc) * (t - t') * t' := add_le_add b1 b2
    _ ≤ (Real.sqrt N * (Cφ * Cc) + T * (Real.sqrt N * (K * Cc))) * (t - t') := by
        have : Real.sqrt N * (K * Cc) * (t - t') * t' ≤ T * (Real.sqrt N * (K * Cc)) * (t - t') := by
          have h1 : t' ≤ T := ht't.trans htT
          have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hB hts)
          nlinarith [this]
        nlinarith [this]

end HRS.AdjK
