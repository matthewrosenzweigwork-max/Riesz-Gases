import HRS.PDE.Toolbox
import HRS.PDE.GalerkinLimit
import HRS.PDE.Galerkin
import HRS.PDE.EnergyLeib

/-!
# The drift of the forward equation as a `C^{m+1}` function (input of `transport_form_bound`)

For `d ≥ 2` the components of `M ∇g*μ - ∇V` (Lemma C.1, `coefficient_bounds`) have the Fourier
coefficients `driftCoeff` (`convGradConv_coeff`).  For `d = 1` the drift coefficients lie in
`H^{m+2}` and the function is obtained from the Fourier series (`toFun_isCk_le`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### `C^n` functions have coefficients in `H^n` -/

theorem memHs_coeffOf_cbNorm (n : ℕ) (b : Torus d → ℝ) (hb : Torus.IsCk n b) :
    MemHs (n : ℝ) (coeffOf b) ∧ hsNormSq (n : ℝ) (coeffOf b) ≤
      ((d : ℝ) + 1) ^ n * ((multiIndices d n).card : ℝ) * Torus.cbNorm n b ^ 2 := by
  classical
  have hb' : ContDiff ℝ (n : WithTop ℕ∞) (Torus.lift b) := hb
  have hφ : ∀ α ∈ multiIndices d n, ∃ φ : Torus d → ℝ, Continuous φ ∧
      coeffOf φ = multiDerivCoeff α (coeffOf b) ∧ ∀ x, |φ x| ≤ Torus.cbNorm n b := fun α hα =>
    exists_derivFun b n hb' α (Finset.mem_filter.mp hα).2
  have hbound : ∀ α ∈ multiIndices d n, ∀ S : Finset (Lattice d),
      ∑ k ∈ S, ‖multiDerivCoeff α (coeffOf b) k‖ ^ 2 ≤ Torus.cbNorm n b ^ 2 := by
    intro α hα S
    obtain ⟨φ, hc, he, hx⟩ := hφ α hα
    obtain ⟨hm0, hn0⟩ := coeffOf_memHs_zero hc
    have hsup : Torus.supNorm φ ≤ Torus.cbNorm n b := ciSup_le fun x => by simpa using hx x
    have hs0 : 0 ≤ Torus.supNorm φ := supNorm_nonneg φ
    have h1 := sum_le_hsNormSq hm0 S
    simp only [sobWeight_zero, one_mul] at h1
    rw [he] at h1 hn0
    exact h1.trans (hn0.trans (pow_le_pow_left₀ hs0 hsup 2))
  have hS : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight (n : ℝ) k * ‖coeffOf b k‖ ^ 2 ≤
      ((d : ℝ) + 1) ^ n * ((multiIndices d n).card : ℝ) * Torus.cbNorm n b ^ 2 := by
    intro S
    calc ∑ k ∈ S, sobWeight (n : ℝ) k * ‖coeffOf b k‖ ^ 2
        ≤ ∑ k ∈ S, ((d : ℝ) + 1) ^ n *
            ∑ α ∈ multiIndices d n, ‖multiDerivCoeff α (coeffOf b) k‖ ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [sobWeight_natCast]
          simp_rw [norm_sq_multiDerivCoeff]
          rw [← Finset.sum_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (pow_le_sum_weight n k) (sq_nonneg _)
      _ = ((d : ℝ) + 1) ^ n * ∑ α ∈ multiIndices d n,
            ∑ k ∈ S, ‖multiDerivCoeff α (coeffOf b) k‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ ((d : ℝ) + 1) ^ n * ∑ _α ∈ multiIndices d n, Torus.cbNorm n b ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α hα => hbound α hα S) (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  exact memHs_of_sum_le hS

/-! ### Linearity of `coeffOf` -/

theorem coeffOf_lin {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Torus d → ℝ)
    (g : Torus d → ℝ) (hf : ∀ i, Continuous (f i)) (hg : Continuous g) :
    coeffOf (fun x => ∑ i ∈ s, c i * f i x - g x) =
      fun k => ∑ i ∈ s, ((c i : ℝ) : ℂ) * coeffOf (f i) k - coeffOf g k := by
  funext k
  rw [coeffOf_eq, coeffOf_eq, Finset.sum_congr rfl fun i _ => by rw [coeffOf_eq]]
  have hi : ∀ i, Integrable fun x : Torus d => Torus.mode (-k) x * (f i x : ℂ) := fun i =>
    integrable_of_continuous' ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp (hf i)))
  have hg' : Integrable fun x : Torus d => Torus.mode (-k) x * (g x : ℂ) :=
    integrable_of_continuous' ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp hg))
  have e : ∀ x : Torus d, Torus.mode (-k) x * ((∑ i ∈ s, c i * f i x - g x : ℝ) : ℂ) =
      ∑ i ∈ s, ((c i : ℝ) : ℂ) * (Torus.mode (-k) x * (f i x : ℂ)) -
        Torus.mode (-k) x * (g x : ℂ) := by
    intro x
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_sub (integrable_finsetSum _ fun i _ => (hi i).const_mul _) hg',
    integral_finsetSum _ fun i _ => (hi i).const_mul _]
  simp_rw [integral_const_mul]

theorem grad_apply_eq_partialDeriv (V : Torus d → ℝ) (j : Fin d) (x : Torus d) :
    Torus.grad V x j = Torus.partialDeriv j V x := by
  unfold Torus.grad Torus.partialDeriv
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := fderiv ℝ (Torus.lift V) (Torus.rep x))
  show (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (Torus.lift V) (Torus.rep x)) j = _
  rw [EuclideanSpace.inner_single_right] at h
  simpa using h

theorem matVec_apply (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) (j : Fin d) :
    Torus.matVec M v j = ∑ i, M j i * v i := by
  simp [Torus.matVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-! ### `d ≥ 2`: from Lemma C.1 -/

theorem exists_driftFuns_ge2 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ B : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ μ : Torus d → ℝ, IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∃ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk (m + 1) (b j)) ∧
        (∀ j, Torus.cbNorm (m + 1) (b j) ≤ B) ∧ ∀ j, coeffOf (b j) = driftCoeff D μ j := by
  obtain ⟨C, hC⟩ := coefficient_bounds (by omega) s hs0 hsd m MB Λ VB
  refine ⟨C, ?_⟩
  intro D hDs hM hV μ hprob hCk hΛ
  obtain ⟨hf, hfb⟩ := hC D.M hM D.V hV μ hprob hCk hΛ
  set f : Torus d → Euc d := fun x => Torus.matVec D.M (convGradConv (periodicRieszGrad d s) μ x) -
    Torus.grad D.V x with hfdef
  have hnn1 : 0 ≤ ⨆ q : {q : Euc d // ‖q‖ = 1},
      Torus.cbNorm (m + 1) (fun x => inner ℝ q.1 (Torus.grad μ x)) :=
    Real.iSup_nonneg fun q => cbNorm_nonneg _ _
  have hnn2 := cbNorm_nonneg (d := d) (m + 3) μ
  have hfC : Torus.cbNorm (m + 1) f ≤ C := by linarith
  have hμ1 : Torus.IsCk 1 μ := hCk.of_le (by norm_cast; omega)
  have hVk : Torus.IsCk 1 D.V := hV.1.of_le (by norm_cast; omega)
  have hcont : ∀ i, Continuous fun x => convGradConv (periodicRieszGrad d s) μ x i := fun i =>
    (EuclideanSpace.proj i).continuous.comp (convGradConv_continuous hd hs0 hsd μ hμ1)
  have hVc : ∀ j, Continuous (Torus.partialDeriv j D.V) := fun j => continuous_partialDeriv j _ hVk
  refine ⟨fun j x => f x j, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have : (fun x => f x j) = fun x => (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (f x) := rfl
    unfold Torus.IsCk
    have e : Torus.lift (fun x => f x j) = (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) ∘ Torus.lift f := rfl
    rw [e]
    exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.comp (by
      have := hf
      unfold Torus.IsCk at this
      exact this)
  · have h1 := cbNorm_clm_comp_le (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (m + 1) f (by
      have := hf
      unfold Torus.IsCk at this ⊢
      exact this)
    have hn : ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa using PiLp.norm_apply_le v j
    calc Torus.cbNorm (m + 1) (fun x => f x j)
        ≤ ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖ * Torus.cbNorm (m + 1) f := h1
      _ ≤ 1 * Torus.cbNorm (m + 1) f :=
          mul_le_mul_of_nonneg_right hn (cbNorm_nonneg _ _)
      _ ≤ C := by linarith
  · have hfj : (fun x => f x j) = fun x => ∑ i, D.M j i * convGradConv (periodicRieszGrad d s) μ x i -
        Torus.partialDeriv j D.V x := by
      funext x
      simp only [hfdef, PiLp.sub_apply, matVec_apply, grad_apply_eq_partialDeriv]
    show coeffOf (fun x => f x j) = _
    rw [hfj, coeffOf_lin Finset.univ (fun i => D.M j i)
      (fun i x => convGradConv (periodicRieszGrad d s) μ x i) _ hcont (hVc j)]
    funext k
    simp only [driftCoeff]
    rw [coeffOf_partialDeriv j D.V hVk]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [convGradConv_coeff hd hs0 hsd μ hμ1 i, hDs]

/-! ### `d = 1`: from the Fourier series -/

theorem driftCoeff_memHs (D : DynData d) (ρ : Torus d → ℝ) (r : ℝ) (hρ : MemHs (r + 1) (coeffOf ρ))
    (hV : MemHs (r + 1) (coeffOf D.V)) (j : Fin d) :
    MemHs r (driftCoeff D ρ j) ∧ hsNormSq r (driftCoeff D ρ j) ≤
      2 * ((|rieszConst d D.s| * ∑ i, |D.M j i|) ^ 2 * hsNormSq (r + 1) (coeffOf ρ) +
        hsNormSq (r + 1) (coeffOf D.V)) := by
  set a : ℝ := |rieszConst d D.s| * ∑ i, |D.M j i| with ha
  have hpt : ∀ k, sobWeight r k * ‖driftCoeff D ρ j k‖ ^ 2 ≤
      2 * (a ^ 2 * (sobWeight (r + 1) k * ‖coeffOf ρ k‖ ^ 2) +
        sobWeight (r + 1) k * ‖coeffOf D.V k‖ ^ 2) := by
    intro k
    have h := norm_driftCoeff_le D ρ j k
    have hn := norm_nonneg (driftCoeff D ρ j k)
    have h2 : ‖driftCoeff D ρ j k‖ ^ 2 ≤ (Lattice.jp k *
        (a * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖)) ^ 2 := pow_le_pow_left₀ hn h 2
    have hw := (sobWeight_pos (d := d) r k).le
    have hw1 : sobWeight (r + 1) k = sobWeight r k * Lattice.jp k ^ 2 := by
      rw [sobWeight_add, jp_sq]
    have h3 : (a * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖) ^ 2 ≤
        2 * (a ^ 2 * ‖coeffOf ρ k‖ ^ 2 + ‖coeffOf D.V k‖ ^ 2) := by
      nlinarith [sq_nonneg (a * ‖coeffOf ρ k‖ - ‖coeffOf D.V k‖)]
    calc sobWeight r k * ‖driftCoeff D ρ j k‖ ^ 2
        ≤ sobWeight r k * (Lattice.jp k *
        (a * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖)) ^ 2 := mul_le_mul_of_nonneg_left h2 hw
      _ = sobWeight r k * Lattice.jp k ^ 2 *
          (a * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖) ^ 2 := by ring
      _ ≤ sobWeight r k * Lattice.jp k ^ 2 *
          (2 * (a ^ 2 * ‖coeffOf ρ k‖ ^ 2 + ‖coeffOf D.V k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by rw [hw1]; ring
  have hS : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight r k * ‖driftCoeff D ρ j k‖ ^ 2 ≤
      2 * (a ^ 2 * hsNormSq (r + 1) (coeffOf ρ) + hsNormSq (r + 1) (coeffOf D.V)) := by
    intro S
    calc _ ≤ ∑ k ∈ S, 2 * (a ^ 2 * (sobWeight (r + 1) k * ‖coeffOf ρ k‖ ^ 2) +
          sobWeight (r + 1) k * ‖coeffOf D.V k‖ ^ 2) := Finset.sum_le_sum fun k _ => hpt k
      _ = 2 * (a ^ 2 * ∑ k ∈ S, sobWeight (r + 1) k * ‖coeffOf ρ k‖ ^ 2 +
          ∑ k ∈ S, sobWeight (r + 1) k * ‖coeffOf D.V k‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ _ := by
          have h1 := sum_le_hsNormSq hρ S
          have h2 := sum_le_hsNormSq hV S
          have : 0 ≤ a ^ 2 := sq_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left h1 this]
  exact memHs_of_sum_le hS

theorem exists_driftFuns_one (hd : d < 2) (s : ℝ) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ B : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ μ : Torus d → ℝ, IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∃ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk (m + 1) (b j)) ∧
        (∀ j, Torus.cbNorm (m + 1) (b j) ≤ B) ∧ ∀ j, coeffOf (b j) = driftCoeff D μ j := by
  have hdr : (d : ℝ) < 2 := by exact_mod_cast hd
  obtain ⟨Ct, hCt⟩ := toFun_isCk_le (d := d) (m + 1) ((m + 2 : ℕ) : ℝ) (by push_cast; linarith)
  set Kn : ℝ := ((d : ℝ) + 1) ^ (m + 3) * ((multiIndices d (m + 3)).card : ℝ) with hKn
  have hKn0 : 0 ≤ Kn := by positivity
  set A : ℝ := |MB| * d with hA
  refine ⟨max Ct 0 * Real.sqrt (2 * ((|rieszConst d s| * A) ^ 2 * (Kn * Λ ^ 2) + Kn * VB ^ 2)), ?_⟩
  intro D hDs hM hV μ hprob hCk hΛ
  have hμ1 : Torus.IsCk 1 μ := hCk.of_le (by norm_cast; omega)
  have hμc : Continuous μ := continuous_of_isCk hμ1
  have hVc : Continuous D.V := continuous_of_isCk (hV.1.of_le (by norm_cast; omega))
  have hμr : IsRealCoeff (coeffOf μ) := isRealCoeff_coeffOf _ (integrable_of_continuous' hμc)
  have hVr : IsRealCoeff (coeffOf D.V) := isRealCoeff_coeffOf _ (integrable_of_continuous' hVc)
  have hμ3 : Torus.IsCk ((m + 3 : ℕ) : WithTop ℕ∞) μ := by
    unfold Torus.IsCk at *; push_cast; exact hCk
  have hV3 : Torus.IsCk ((m + 3 : ℕ) : WithTop ℕ∞) D.V := by
    have := hV.1; unfold Torus.IsCk at *; push_cast; exact this
  obtain ⟨hμH, hμN⟩ := memHs_coeffOf_cbNorm (m + 3) μ hμ3
  obtain ⟨hVH, hVN⟩ := memHs_coeffOf_cbNorm (m + 3) D.V hV3
  have hΛ2 : Torus.cbNorm (m + 3) μ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (cbNorm_nonneg _ _) hΛ 2
  have hVB2 : Torus.cbNorm (m + 3) D.V ^ 2 ≤ VB ^ 2 :=
    pow_le_pow_left₀ (cbNorm_nonneg _ _) hV.2 2
  have hcast : ((m + 3 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hμH hμN hVH hVN
  have hμN' : hsNormSq (((m + 2 : ℕ) : ℝ) + 1) (coeffOf μ) ≤ Kn * Λ ^ 2 :=
    hμN.trans (mul_le_mul_of_nonneg_left hΛ2 hKn0)
  have hVN' : hsNormSq (((m + 2 : ℕ) : ℝ) + 1) (coeffOf D.V) ≤ Kn * VB ^ 2 :=
    hVN.trans (mul_le_mul_of_nonneg_left hVB2 hKn0)
  have hrowM : ∀ j, ∑ i, |D.M j i| ≤ A := by
    intro j
    calc ∑ i, |D.M j i| ≤ ∑ _i : Fin d, |MB| :=
          Finset.sum_le_sum fun i _ => (hM j i).trans (le_abs_self _)
      _ = A := by rw [hA]; simp; ring
  have hmem : ∀ j, MemHs (((m + 2 : ℕ) : ℝ)) (driftCoeff D μ j) ∧
      hsNormSq (((m + 2 : ℕ) : ℝ)) (driftCoeff D μ j) ≤
        2 * ((|rieszConst d s| * A) ^ 2 * (Kn * Λ ^ 2) + Kn * VB ^ 2) := by
    intro j
    obtain ⟨h1, h2⟩ := driftCoeff_memHs D μ _ hμH hVH j
    refine ⟨h1, h2.trans ?_⟩
    rw [hDs]
    have hr0 : 0 ≤ |rieszConst d s| := abs_nonneg _
    have ha1 : |rieszConst d s| * ∑ i, |D.M j i| ≤ |rieszConst d s| * A :=
      mul_le_mul_of_nonneg_left (hrowM j) hr0
    have ha0 : 0 ≤ |rieszConst d s| * ∑ i, |D.M j i| :=
      mul_nonneg hr0 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hsq : (|rieszConst d s| * ∑ i, |D.M j i|) ^ 2 ≤ (|rieszConst d s| * A) ^ 2 :=
      pow_le_pow_left₀ ha0 ha1 2
    rw [hDs] at h2
    have hn0 := hsNormSq_nonneg (((m + 2 : ℕ) : ℝ) + 1) (coeffOf μ)
    have := mul_le_mul hsq hμN' hn0 (sq_nonneg _)
    linarith
  refine ⟨fun j => toFun (driftCoeff D μ j), fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have := (hCt _ (hmem j).1 (isRealCoeff_driftCoeff D μ hμr hVr j)).1
    unfold Torus.IsCk at this ⊢
    push_cast at this
    exact this
  · obtain ⟨_, hcb⟩ := hCt _ (hmem j).1 (isRealCoeff_driftCoeff D μ hμr hVr j)
    refine hcb.trans ?_
    have hnn : 0 ≤ hsNorm (((m + 2 : ℕ) : ℝ)) (driftCoeff D μ j) := Real.sqrt_nonneg _
    have hle : hsNorm (((m + 2 : ℕ) : ℝ)) (driftCoeff D μ j) ≤
        Real.sqrt (2 * ((|rieszConst d s| * A) ^ 2 * (Kn * Λ ^ 2) + Kn * VB ^ 2)) :=
      Real.sqrt_le_sqrt (hmem j).2
    calc Ct * hsNorm (((m + 2 : ℕ) : ℝ)) (driftCoeff D μ j)
        ≤ max Ct 0 * hsNorm (((m + 2 : ℕ) : ℝ)) (driftCoeff D μ j) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (le_max_right _ _)
  · refine coeffOf_toFun _ (isRealCoeff_driftCoeff D μ hμr hVr j)
      (summable_norm_of_memHs (((m + 2 : ℕ) : ℝ)) (by push_cast; linarith) _ (hmem j).1)

/-- The drift of the forward equation as `C^{m+1}` functions with a uniform bound (input of
`transport_form_bound`; `B:eq:coeff-bounds`). -/
theorem exists_driftFuns (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ B : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ μ : Torus d → ℝ, IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∃ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk (m + 1) (b j)) ∧
        (∀ j, Torus.cbNorm (m + 1) (b j) ≤ B) ∧ ∀ j, coeffOf (b j) = driftCoeff D μ j := by
  by_cases h2 : 2 ≤ d
  · exact exists_driftFuns_ge2 h2 s hs0 hsd m MB Λ VB
  · exact exists_driftFuns_one (by omega) s m MB Λ VB

end HRS.PDE
