import HRS.Whole.AppendixALemmas2
import HRS.MP.PropIncr

/-!
# Packet MPKERN: the kernel increment bounds S.A.22(ii) on the torus

Proof of `HRS.Whole.AppendixALemmas.path_kernel_increment_torus` (statement:
`HRS/Whole/AppendixALemmas2.lean`).  Route: the functional `ℓ(φ) = ∂_j U^{r,t}φ(x)` is bounded by
`C ‖φ‖_{H^{q_T}}` on smooth mean-zero `φ` (Sobolev embedding and the adjoint estimate), linear
(`HRS.A33.prop_lin`), hence represented by a unique element of `NegSobolev d q_T` (a Riesz argument in
Fourier coordinates, Stage 1); the increment `ℓ_t - ℓ_{s'}` is bounded by `C |t-s'| ‖φ‖_{H^{q_T}}`
through `HRS.MP.PropIncr.mpi_main`, and the dual norm is controlled by the trigonometric
polynomial tests (Stage 1, `mpk_norm_le_of_eval`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MP.KernIncr

open HRS

variable {d : ℕ}

/-! ### Stage 1: duality in Fourier coordinates -/

/-- a smooth mean-zero test function -/
def MPKTest (φ : Torus d → ℝ) : Prop := Torus.IsSmooth φ ∧ Torus.mean φ = 0

theorem mpk_cont_of_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  PDE.ClassicalAux.continuous_of_isCk (PDE.ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hφ)

theorem mpk_test_comb {φ ψ : Torus d → ℝ} (hφ : MPKTest φ) (hψ : MPKTest ψ) (α β : ℝ) :
    MPKTest (fun x => α * φ x + β * ψ x) := by
  refine ⟨?_, ?_⟩
  · have h1 := hφ.1
    have h2 := hψ.1
    unfold Torus.IsSmooth Torus.IsCk at h1 h2 ⊢
    exact (contDiff_const.mul h1).add (contDiff_const.mul h2)
  · have i1 : Integrable φ := PDE.ClassicalAux.integrable_of_continuous (mpk_cont_of_smooth hφ.1)
    have i2 : Integrable ψ := PDE.ClassicalAux.integrable_of_continuous (mpk_cont_of_smooth hψ.1)
    have h1 := hφ.2
    have h2 := hψ.2
    unfold Torus.mean at h1 h2 ⊢
    rw [integral_add (i1.const_mul α) (i2.const_mul β), integral_const_mul, integral_const_mul, h1, h2]
    ring

theorem mpk_test_zero : MPKTest (fun _ : Torus d => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · unfold Torus.IsSmooth Torus.IsCk
    exact contDiff_const
  · simp [Torus.mean]

theorem mpk_test_realMode (k : NonzeroLattice d) : MPKTest (Torus.realMode k : Torus d → ℝ) :=
  ⟨FieldSingAux.isSmooth_realMode k, Torus.integral_realMode k⟩

theorem mpk_test_trigPoly (S : Finset (NonzeroLattice d)) (b : NonzeroLattice d → ℝ) :
    MPKTest (FieldSingAux.trigPoly S b) :=
  ⟨FieldSingAux.isSmooth_trigPoly S b, FieldSingAux.mean_trigPoly S b⟩

theorem mpk_eval_trigPoly {m : ℝ} (F : NegSobolev d m) (S : Finset (NonzeroLattice d))
    (b : NonzeroLattice d → ℝ) :
    NegSobolev.eval F (FieldSingAux.trigPoly S b) =
      ∑ k ∈ S, NegSobolev.fourierCoeff F k * b k := by
  unfold NegSobolev.eval
  simp_rw [FieldSingAux.funRealCoeff_trigPoly]
  rw [tsum_eq_sum (s := S) (fun k hk => by simp [hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [hk]

theorem mpk_sobolevNorm_trigPoly (m : ℝ) (S : Finset (NonzeroLattice d))
    (b : NonzeroLattice d → ℝ) :
    sobolevNorm m (FieldSingAux.trigPoly S b) =
      Real.sqrt (∑ k ∈ S, Lattice.jp k.1 ^ (2 * m) * b k ^ 2) := by
  unfold sobolevNorm
  rw [FieldSingAux.mean_trigPoly]
  simp_rw [FieldSingAux.funRealCoeff_trigPoly]
  rw [tsum_eq_sum (s := S) (fun k hk => by simp [hk])]
  rw [zero_pow two_ne_zero, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by simp [hk]

/-- the weighted coefficient `⟨k⟩^{-m} e(k)` -/
def mpkWt (m : ℝ) (e : NonzeroLattice d → ℝ) (k : NonzeroLattice d) : ℝ :=
  Lattice.jp k.1 ^ (-m) * e k

theorem mpkWt_mul (m : ℝ) (e : NonzeroLattice d → ℝ) (k : NonzeroLattice d) :
    Lattice.jp k.1 ^ m * mpkWt m e k = e k := by
  have hj := Torus.jp_pos k.1
  unfold mpkWt
  rw [← mul_assoc, ← Real.rpow_add hj]
  simp

theorem mpkWt_sq (m : ℝ) (e : NonzeroLattice d → ℝ) (k : NonzeroLattice d) :
    Lattice.jp k.1 ^ (2 * m) * mpkWt m e k ^ 2 = e k ^ 2 := by
  rw [← mpkWt_mul m e k, mul_pow, Torus.jp_rpow_sq]

theorem mpk_eval_sub_trig {m : ℝ} (F G : NegSobolev d m) (S : Finset (NonzeroLattice d))
    (b : NonzeroLattice d → ℝ) :
    NegSobolev.eval (F - G) (FieldSingAux.trigPoly S b) =
      NegSobolev.eval F (FieldSingAux.trigPoly S b) - NegSobolev.eval G (FieldSingAux.trigPoly S b) := by
  rw [mpk_eval_trigPoly, mpk_eval_trigPoly, mpk_eval_trigPoly, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : NegSobolev.fourierCoeff (F - G) k =
      NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
    have hc : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
    unfold NegSobolev.fourierCoeff
    rw [hc, mul_sub]
  rw [this]; ring

/-- the norm of `F ∈ NegSobolev` is at most `B` once the trigonometric tests satisfy
`|F(φ)| ≤ B ‖φ‖_{H^m}`. -/
theorem mpk_norm_le_of_eval {m : ℝ} (F : NegSobolev d m) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ (S : Finset (NonzeroLattice d)) (b : NonzeroLattice d → ℝ),
      |NegSobolev.eval F (FieldSingAux.trigPoly S b)| ≤
        B * sobolevNorm m (FieldSingAux.trigPoly S b)) :
    ‖F‖ ≤ B := by
  classical
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have hS : ∀ S : Finset (NonzeroLattice d), ∑ k ∈ S, NegSobolev.coord F k ^ 2 ≤ B ^ 2 := by
    intro S
    have h1 : ∀ k, NegSobolev.fourierCoeff F k * mpkWt m (NegSobolev.coord F) k =
        NegSobolev.coord F k ^ 2 := by
      intro k
      unfold NegSobolev.fourierCoeff
      calc Lattice.jp k.1 ^ m * NegSobolev.coord F k * mpkWt m (NegSobolev.coord F) k
          = NegSobolev.coord F k * (Lattice.jp k.1 ^ m * mpkWt m (NegSobolev.coord F) k) := by ring
        _ = _ := by rw [mpkWt_mul]; ring
    have hev := h S (mpkWt m (NegSobolev.coord F))
    rw [mpk_eval_trigPoly, mpk_sobolevNorm_trigPoly] at hev
    simp only [h1, mpkWt_sq] at hev
    set Q := ∑ k ∈ S, NegSobolev.coord F k ^ 2 with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => sq_nonneg _
    rw [abs_of_nonneg hQ0] at hev
    have hq0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
    have hqq : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0
    by_cases hz : Real.sqrt Q = 0
    · have hQz : Q = 0 := by
        have := hqq
        rw [hz] at this
        linarith
      rw [hQz]; positivity
    · have hpos : 0 < Real.sqrt Q := lt_of_le_of_ne hq0 (Ne.symm hz)
      have : Real.sqrt Q ≤ B := by
        by_contra hc
        have hc := not_le.mp hc
        nlinarith
      rw [← hqq]
      nlinarith
  have hle : ∑' k, NegSobolev.coord F k ^ 2 ≤ B ^ 2 := hs.tsum_le_of_sum_le hS
  rw [← hn] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp hle

/-- Riesz representation: a linear functional on smooth mean-zero tests, bounded by the `H^m` norm, is
the pairing with an element of `NegSobolev d m`. -/
theorem mpk_exists_rep {m : ℝ} (L : (Torus d → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hlin : ∀ φ ψ : Torus d → ℝ, MPKTest φ → MPKTest ψ → ∀ α β : ℝ,
      L (fun x => α * φ x + β * ψ x) = α * L φ + β * L ψ)
    (hbd : ∀ φ : Torus d → ℝ, MPKTest φ → |L φ| ≤ B * sobolevNorm m φ) :
    ∃ F : NegSobolev d m, ∀ φ : Torus d → ℝ, MPKTest φ → NegSobolev.eval F φ = L φ := by
  classical
  set a : NonzeroLattice d → ℝ := fun k => L (Torus.realMode k) with ha
  set c : NonzeroLattice d → ℝ := mpkWt m a with hc
  set b : NonzeroLattice d → ℝ := mpkWt m c with hb
  have hL0 : L (fun _ => 0) = 0 := by
    have := hlin _ _ mpk_test_zero mpk_test_zero 0 0
    simpa using this
  have hLtrig : ∀ (S : Finset (NonzeroLattice d)) (β : NonzeroLattice d → ℝ),
      L (FieldSingAux.trigPoly S β) = ∑ k ∈ S, β k * a k := by
    intro S β
    induction S using Finset.induction_on with
    | empty =>
      have : FieldSingAux.trigPoly (∅ : Finset (NonzeroLattice d)) β = fun _ => 0 := by
        funext x; simp [FieldSingAux.trigPoly]
      rw [this, hL0]; simp
    | insert k S hk ih =>
      have e : FieldSingAux.trigPoly (insert k S) β =
          fun x => β k * Torus.realMode k x + 1 * FieldSingAux.trigPoly S β x := by
        funext x; simp [FieldSingAux.trigPoly, Finset.sum_insert hk]
      rw [e, hlin _ _ (mpk_test_realMode k) (mpk_test_trigPoly S β), ih, Finset.sum_insert hk]
      simp [ha]
  have hQ : ∀ S : Finset (NonzeroLattice d), ∑ k ∈ S, c k ^ 2 ≤ B ^ 2 := by
    intro S
    have h1 : ∀ k, b k * a k = c k ^ 2 := by
      intro k
      have := mpkWt_mul m c k
      have h2 := mpkWt_mul m a k
      have hj := Torus.jp_pos k.1
      have e1 : c k = Lattice.jp k.1 ^ (-m) * a k := rfl
      have e2 : b k = Lattice.jp k.1 ^ (-m) * c k := rfl
      rw [e2, sq]
      nth_rewrite 2 [e1]
      ring
    have hev := hbd _ (mpk_test_trigPoly S b)
    rw [hLtrig, mpk_sobolevNorm_trigPoly] at hev
    simp only [h1] at hev
    simp only [hb, mpkWt_sq] at hev
    set Q := ∑ k ∈ S, c k ^ 2 with hQdef
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => sq_nonneg _
    rw [abs_of_nonneg hQ0] at hev
    have hq0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
    have hqq : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0
    by_cases hz : Real.sqrt Q = 0
    · have hQz : Q = 0 := by
        have := hqq
        rw [hz] at this
        linarith
      rw [hQz]; positivity
    · have hpos : 0 < Real.sqrt Q := lt_of_le_of_ne hq0 (Ne.symm hz)
      have : Real.sqrt Q ≤ B := by
        by_contra hcon
        have hcon := not_le.mp hcon
        nlinarith
      rw [← hqq]
      nlinarith
  have hsum : Summable fun k => c k ^ 2 :=
    summable_of_sum_le (fun k => sq_nonneg _) hQ
  have hmem : Memℓp c 2 := (Torus.memℓp_two_iff c).2 hsum
  let F : NegSobolev d m := (⟨c, hmem⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)
  have hcoord : ∀ k, NegSobolev.coord F k = c k := fun k => rfl
  have hfc : ∀ k, NegSobolev.fourierCoeff F k = a k := by
    intro k
    unfold NegSobolev.fourierCoeff
    rw [hcoord, hc, mpkWt_mul]
  refine ⟨F, fun φ hφ => ?_⟩
  -- the Fourier series of `φ`
  have hS := (A33.a33_memSob m hφ.1).2
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2
    with hw
  have hcontφ : Continuous φ := mpk_cont_of_smooth hφ.1
  have hcomb : ∀ T : Finset (NonzeroLattice d),
      MPKTest (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T (Torus.funRealCoeff φ) x) :=
    fun T => mpk_test_comb hφ (mpk_test_trigPoly T _) 1 (-1)
  have hdiff : ∀ T : Finset (NonzeroLattice d),
      |L φ - ∑ k ∈ T, a k * Torus.funRealCoeff φ k| ≤
        B * Real.sqrt (∑' k, (if k ∈ T then 0 else w k)) := by
    intro T
    have hl := hlin φ _ hφ (mpk_test_trigPoly T (Torus.funRealCoeff φ)) 1 (-1)
    rw [hLtrig] at hl
    have e1 : L φ - ∑ k ∈ T, a k * Torus.funRealCoeff φ k =
        L (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T (Torus.funRealCoeff φ) x) := by
      rw [hl]
      have : ∑ k ∈ T, a k * Torus.funRealCoeff φ k = ∑ k ∈ T, Torus.funRealCoeff φ k * a k :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [this]; ring
    rw [e1]
    refine (hbd _ (hcomb T)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB
    unfold sobolevNorm
    rw [(hcomb T).2, zero_pow two_ne_zero, zero_add]
    refine Real.sqrt_le_sqrt (le_of_eq (tsum_congr fun k => ?_))
    rw [A33.a33_funRealCoeff_lin hcontφ (PDE.ClassicalAux.continuous_of_isCk
      (PDE.ClassicalAux.isCk_of_le (by exact_mod_cast le_top) (FieldSingAux.isSmooth_trigPoly T _)))
      1 (-1) k, FieldSingAux.funRealCoeff_trigPoly]
    by_cases hk : k ∈ T
    · simp [hk]
    · simp [hk, hw]
  have htail : Tendsto (fun T : Finset (NonzeroLattice d) => ∑' k, (if k ∈ T then 0 else w k))
      atTop (𝓝 0) := by
    have e : ∀ T : Finset (NonzeroLattice d),
        ∑' k, (if k ∈ T then 0 else w k) = (∑' k, w k) - ∑ k ∈ T, w k := by
      intro T
      have hsF : Summable (fun k => if k ∈ T then w k else 0) :=
        summable_of_ne_finset_zero (s := T) fun k hk => by simp [hk]
      have : (fun k => if k ∈ T then (0 : ℝ) else w k) =
          fun k => w k - (if k ∈ T then w k else 0) := by
        funext k; split_ifs <;> simp
      have hind : ∑' k, (if k ∈ T then w k else 0) = ∑ k ∈ T, w k := by
        rw [tsum_eq_sum (s := T) (fun k hk => by simp [hk])]
        exact Finset.sum_congr rfl fun k hk => by simp [hk]
      rw [this, hS.tsum_sub hsF, hind]
    simp_rw [e]
    have h2 : Tendsto (fun T : Finset (NonzeroLattice d) => (∑' k, w k) - ∑ k ∈ T, w k) atTop
        (𝓝 ((∑' k, w k) - ∑' k, w k)) := tendsto_const_nhds.sub hS.hasSum
    simpa using h2
  have hlim : HasSum (fun k => a k * Torus.funRealCoeff φ k) (L φ) := by
    have h3 : Tendsto (fun T : Finset (NonzeroLattice d) =>
        B * Real.sqrt (∑' k, (if k ∈ T then 0 else w k))) atTop (𝓝 0) := by
      have := (htail.sqrt).const_mul B
      simpa using this
    have h4 : Tendsto (fun T : Finset (NonzeroLattice d) =>
        ‖(∑ k ∈ T, a k * Torus.funRealCoeff φ k) - L φ‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun T => norm_nonneg _) (fun T => ?_) h3
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hdiff T
    exact tendsto_iff_norm_sub_tendsto_zero.2 h4
  unfold NegSobolev.eval
  simp_rw [hfc]
  exact hlim.tsum_eq

/-! ### Stage 2: the functional `φ ↦ ∂_j U^{r,t}φ(x)` -/

open HRS.PDE
open HRS.Whole.AppendixALemmas (qT)

theorem mpk_isCk_comb {f g : Torus d → ℝ} {k : WithTop ℕ∞} (hf : Torus.IsCk k f)
    (hg : Torus.IsCk k g) (α β : ℝ) : Torus.IsCk k (fun y => α * f y + β * g y) := by
  unfold Torus.IsCk at hf hg ⊢
  exact (contDiff_const.mul hf).add (contDiff_const.mul hg)

theorem mpk_grad_comb {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (α β : ℝ)
    (x : Torus d) (j : Fin d) :
    Torus.grad (fun y => α * f y + β * g y) x j = α * Torus.grad f x j + β * Torus.grad g x j := by
  rw [MFAux.grad_apply, MFAux.grad_apply, MFAux.grad_apply]
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => α * f y + β * g y) =
      fun z => α * Torus.lift f z + β * Torus.lift g z := rfl
  have hf' : DifferentiableAt ℝ (Torus.lift f) (Torus.rep x) :=
    (ContDiff.differentiable hf (by norm_num)).differentiableAt
  have hg' : DifferentiableAt ℝ (Torus.lift g) (Torus.rep x) :=
    (ContDiff.differentiable hg (by norm_num)).differentiableAt
  have hD : HasFDerivAt (fun z => α * Torus.lift f z + β * Torus.lift g z)
      (α • fderiv ℝ (Torus.lift f) (Torus.rep x) + β • fderiv ℝ (Torus.lift g) (Torus.rep x))
      (Torus.rep x) := (hf'.hasFDerivAt.const_mul α).add (hg'.hasFDerivAt.const_mul β)
  rw [e, hD.fderiv]
  simp

/-- Sup bound of the gradient by a high Sobolev norm. -/
theorem mpk_grad_sup_le (j : ℕ) (hj : (d : ℝ) / 2 + 1 < j) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ f : Torus d → ℝ, MemSobolev (j : ℝ) f → Torus.IsCk 1 f →
      ∀ x, ‖Torus.grad f x‖ ≤ Cs * sobolevNorm (j : ℝ) f := by
  obtain ⟨C, hC⟩ := cbNorm_le_sobolevNorm (d := d) 1 (j : ℝ) (by simpa using hj)
  refine ⟨max C 0, le_max_right _ _, fun f hf hf1 x => ?_⟩
  have h0 : 0 ≤ sobolevNorm (j : ℝ) f := Real.sqrt_nonneg _
  calc ‖Torus.grad f x‖ ≤ Torus.cbNorm 1 f := MFApriori.norm_grad_le_cbNorm hf1 x
    _ ≤ C * sobolevNorm (j : ℝ) f := hC f hf (by simpa using hf1)
    _ ≤ max C 0 * sobolevNorm (j : ℝ) f := mul_le_mul_of_nonneg_right (le_max_left _ _) h0

theorem mpk_isCk_one {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) : Torus.IsCk 1 f :=
  ContDiff.of_le hf (by norm_num)

theorem mpk_abs_grad_le (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    |Torus.grad f x j| ≤ ‖Torus.grad f x‖ := by
  have := PiLp.norm_apply_le (Torus.grad f x) j
  rwa [Real.norm_eq_abs] at this

theorem mpk_prop_zero (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d}
    {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {χ : Torus d → ℝ}
    (hχ : Torus.IsCk 2 χ) : propagator D μ 0 0 χ = χ := by
  have hV1 : Torus.IsCk 1 D.V :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
  have hμ1 : Torus.IsCk 1 (μ 0) :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
      (hA.hμ.smooth 0 ⟨le_rfl, hA.hT.le⟩)
  exact PropIncr.mpi_propagator_zero D (ClassicalAux.convKernelFacts hd D) hV1 μ hμ1 hχ

/-- the propagator on smooth data: `C²`, in `H^m`, with an `H^m` bound uniform in `D` -/
theorem mpk_prop_facts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB ν₀ T : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ),
      AdjointData s m R MB Λ VB D ν₀ T μ → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
      ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        Torus.IsCk 2 (propagator D μ r t φ) ∧ MemSobolev (m : ℝ) (propagator D μ r t φ) ∧
        sobolevNorm (m : ℝ) (propagator D μ r t φ) ≤ K * sobolevNorm (m : ℝ) φ := by
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd s hs0 hsd m hm R MB Λ VB
  refine ⟨Real.exp (|R.lambdaM (Cs m) ν₀ (thetaOrder d s)| * |T|),
    Real.one_le_exp (by positivity), ?_⟩
  intro D μ hA r t hr hrt htT φ hφ
  have hm3 := ClassicalPart.one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have hT0 : 0 < T := hA.hT
  have hφCk : Torus.IsCk 2 φ := MFSemigroup.isCk_nat_of_isSmooth hφ 2
  have hdom : A33.Dom m φ := A33.dom_smooth hφ
  by_cases ht0 : t = 0
  · subst ht0
    obtain rfl : r = 0 := le_antisymm hrt hr
    have hU0 : propagator D μ 0 0 φ = φ := mpk_prop_zero hd hA hφCk
    rw [hU0]
    refine ⟨hφCk, hdom.2, ?_⟩
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_exp (by positivity))
  · have ht : t ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne (hr.trans hrt) (Ne.symm ht0), htT⟩
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr, hrt⟩
    obtain ⟨hcls, hpe, h3, -⟩ := hmain D ν₀ T μ hA t ht φ hdom.1 hdom.2
    refine ⟨?_, ?_⟩
    · rw [hpe r hr']
      exact hcls.c2 r hr'
    · obtain ⟨hmem, hbd⟩ := h3 m hm1 le_rfl r hr'
      refine ⟨hmem, hbd.trans ?_⟩
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
      have h1 : R.lambdaM (Cs m) ν₀ (thetaOrder d s) * (t - r) ≤
          |R.lambdaM (Cs m) ν₀ (thetaOrder d s)| * (t - r) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      have h2 : |R.lambdaM (Cs m) ν₀ (thetaOrder d s)| * (t - r) ≤
          |R.lambdaM (Cs m) ν₀ (thetaOrder d s)| * |T| :=
        mul_le_mul_of_nonneg_left (by linarith [le_abs_self T]) (abs_nonneg _)
      linarith

theorem mpk_qT_cast (d : ℕ) : ((qT d : ℕ) : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + d + 8 := by
  unfold qT Main.gammaIdx mStar
  push_cast
  ring

theorem mpk_pde (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C₂ C₃ : ℝ, 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ),
      AdjointData s (qT d) Rg MB Λ VB D ν₀ T μ → D.invβ ≤ νbar → ∀ (j : Fin d) (x : Torus d),
      (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        |Torus.grad (propagator D μ r t φ) x j| ≤ C₂ * sobolevNorm ((qT d : ℕ) : ℝ) φ) ∧
      (∀ r s' t : ℝ, 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        |Torus.grad (propagator D μ r t φ) x j - Torus.grad (propagator D μ r s' φ) x j| ≤
          C₃ * |t - s'| * sobolevNorm ((qT d : ℕ) : ℝ) φ) ∧
      (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ ψ : Torus d → ℝ, ∀ α β : ℝ,
        Torus.IsSmooth φ → Torus.IsSmooth ψ →
        Torus.grad (propagator D μ r t (fun y => α * φ y + β * ψ y)) x j =
          α * Torus.grad (propagator D μ r t φ) x j + β * Torus.grad (propagator D μ r t ψ) x j) := by
  have hm : mStar d ≤ qT d := by unfold qT Main.gammaIdx; omega
  obtain ⟨K, hK1, hKf⟩ := mpk_prop_facts hd s hs0 hsd (qT d) hm Rg MB Λ VB ν₀ T
  have hq1 : (d : ℝ) / 2 + 1 < ((qT d : ℕ) : ℝ) := by
    rw [mpk_qT_cast]
    have := Nat.cast_nonneg (α := ℝ) ⌊(d : ℝ) / 2⌋₊
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hq2 : (d : ℝ) / 2 + 1 < ((Main.gammaIdx d : ℕ) : ℝ) := by
    have : ((Main.gammaIdx d : ℕ) : ℝ) = ((qT d : ℕ) : ℝ) - 2 := by
      unfold qT; push_cast; ring
    rw [this, mpk_qT_cast]
    have := Nat.cast_nonneg (α := ℝ) ⌊(d : ℝ) / 2⌋₊
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  obtain ⟨Cs1, hCs1, hgq⟩ := mpk_grad_sup_le (d := d) (qT d) hq1
  obtain ⟨Cs2, hCs2, hgg⟩ := mpk_grad_sup_le (d := d) (Main.gammaIdx d) hq2
  obtain ⟨C1, hC1⟩ := PropIncr.mpi_main hd s hs0 hsd (Main.gammaIdx d)
    (by unfold Main.gammaIdx; omega) Rg MB Λ VB νbar ν₀ T
  refine ⟨Cs1 * K, Cs2 * |C1|, by positivity, by positivity, ?_⟩
  intro D μ hA hν j x
  refine ⟨?_, ?_, ?_⟩
  · intro r t hr hrt htT φ hφ
    obtain ⟨hck, hmem, hn⟩ := hKf D μ hA r t hr hrt htT φ hφ
    refine (mpk_abs_grad_le _ x j).trans ((hgq _ hmem (mpk_isCk_one hck) x).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hn hCs1
  · intro r s' t hr hrs hst htT φ hφ
    obtain ⟨hckt, hmemt, -⟩ := hKf D μ hA r t hr (hrs.trans hst) htT φ hφ
    obtain ⟨hcks, hmems, -⟩ := hKf D μ hA r s' hr hrs (hst.trans htT) φ hφ
    have hφS : MemSobolev ((qT d : ℕ) : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
    have hφc : Continuous φ := mpk_cont_of_smooth hφ
    obtain ⟨hmemd, hnd⟩ := hC1 D μ hA hν r s' t hr hrs hst htT φ hφS hφc
    have hfe : (fun y => propagator D μ r t φ y - propagator D μ r s' φ y) =
        fun y => 1 * propagator D μ r t φ y + (-1) * propagator D μ r s' φ y := by
      funext y; ring
    have hck1 : Torus.IsCk 1 (fun y => propagator D μ r t φ y - propagator D μ r s' φ y) := by
      rw [hfe]
      exact mpk_isCk_comb (mpk_isCk_one hckt) (mpk_isCk_one hcks) 1 (-1)
    have hg := mpk_grad_comb (mpk_isCk_one hckt) (mpk_isCk_one hcks) 1 (-1) x j
    have hdiff : Torus.grad (propagator D μ r t φ) x j - Torus.grad (propagator D μ r s' φ) x j =
        Torus.grad (fun y => propagator D μ r t φ y - propagator D μ r s' φ y) x j := by
      rw [hfe, hg]; ring
    rw [hdiff]
    refine (mpk_abs_grad_le _ x j).trans ((hgg _ hmemd hck1 x).trans ?_)
    have h0 : 0 ≤ |t - s'| * sobolevNorm ((qT d : ℕ) : ℝ) φ :=
      mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    calc Cs2 * sobolevNorm ((Main.gammaIdx d : ℕ) : ℝ)
          (fun y => propagator D μ r t φ y - propagator D μ r s' φ y)
        ≤ Cs2 * (C1 * |t - s'| * sobolevNorm ((qT d : ℕ) : ℝ) φ) :=
          mul_le_mul_of_nonneg_left hnd hCs2
      _ ≤ Cs2 * (|C1| * (|t - s'| * sobolevNorm ((qT d : ℕ) : ℝ) φ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCs2
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ = Cs2 * |C1| * |t - s'| * sobolevNorm ((qT d : ℕ) : ℝ) φ := by ring
  · intro r t hr hrt htT φ ψ α β hφ hψ
    have hcomb : Torus.IsSmooth (fun y => α * φ y + β * ψ y) := mpk_isCk_comb hφ hψ α β
    obtain ⟨hckφ, -, -⟩ := hKf D μ hA r t hr hrt htT φ hφ
    obtain ⟨hckψ, -, -⟩ := hKf D μ hA r t hr hrt htT ψ hψ
    have hlin : propagator D μ r t (fun y => α * φ y + β * ψ y) =
        fun y => α * propagator D μ r t φ y + β * propagator D μ r t ψ y := by
      by_cases ht0 : t = 0
      · subst ht0
        obtain rfl : r = 0 := le_antisymm hrt hr
        have hz : ∀ χ : Torus d → ℝ, Torus.IsSmooth χ → propagator D μ 0 0 χ = χ := fun χ hχ =>
          mpk_prop_zero hd hA (MFSemigroup.isCk_nat_of_isSmooth hχ 2)
        rw [hz _ hcomb, hz _ hφ, hz _ hψ]
      · have ht : t ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne (hr.trans hrt) (Ne.symm ht0), htT⟩
        exact A33.prop_lin hd s hs0 hsd (qT d) hm Rg MB Λ VB D ν₀ T μ hA ht (A33.dom_smooth hφ)
          (A33.dom_smooth hψ) α β ⟨hr, hrt⟩
    rw [hlin]
    exact mpk_grad_comb (mpk_isCk_one hckφ) (mpk_isCk_one hckψ) α β x j

/-! ### The theorem -/

theorem path_kernel_increment_torus_proof (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, ∀ {ι : Type} (D : ι → DynData d) (ρ : ι → ℝ → Torus d → ℝ),
      (∀ i, PDE.AdjointData s (Main.gammaIdx d + 2) Rg MB Λ VB (D i) ν₀ T (ρ i)) →
      (∀ i, (D i).invβ ≤ νbar) →
      (∀ i : ι, ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Torus d,
        ∃! k : NegSobolev d ((qT d : ℕ) : ℝ), ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
          Torus.mean φ = 0 → NegSobolev.eval k φ = (Torus.grad (propagator (D i) (ρ i) r t φ) x) j) ∧
      ∀ Kern : ι → Fin d → ℝ → ℝ → Torus d → NegSobolev d ((qT d : ℕ) : ℝ),
        (∀ i : ι, ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Torus d,
          ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
            NegSobolev.eval (Kern i j r t x) φ = (Torus.grad (propagator (D i) (ρ i) r t φ) x) j) →
        ∀ i : ι, ∀ (j : Fin d) (r s' t : ℝ), 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ x : Torus d,
          ‖Kern i j r t x - Kern i j r s' x‖ ≤ C * |t - s'| ∧ ‖Kern i j r t x‖ ≤ C := by
  by_cases hcase : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  · obtain ⟨hd, hs0, hsd⟩ := hcase
    obtain ⟨C₂, C₃, hC₂, hC₃, hP⟩ := mpk_pde hd s hs0 hsd Rg ν₀ MB Λ T VB νbar
    have hC2m : C₂ ≤ max C₂ C₃ := le_max_left _ _
    have hC3m : C₃ ≤ max C₂ C₃ := le_max_right _ _
    refine ⟨max C₂ C₃, fun {ι} D ρ hA hν => ⟨?_, ?_⟩⟩
    · intro i j r t hr hrt htT x
      obtain ⟨hbd, -, hlinp⟩ := hP (D i) (ρ i) (hA i) (hν i) j x
      obtain ⟨F, hF⟩ := mpk_exists_rep (m := ((qT d : ℕ) : ℝ))
        (fun φ => Torus.grad (propagator (D i) (ρ i) r t φ) x j) C₂ hC₂
        (fun φ ψ hφ hψ α β => hlinp r t hr hrt htT φ ψ α β hφ.1 hψ.1)
        (fun φ hφ => hbd r t hr hrt htT φ hφ.1)
      refine ⟨F, fun φ hφs hφm => hF φ ⟨hφs, hφm⟩, fun F' hF' => ?_⟩
      have hn : ‖F' - F‖ ≤ 0 := by
        refine mpk_norm_le_of_eval (F' - F) 0 le_rfl fun S b => ?_
        rw [mpk_eval_sub_trig, hF' _ (FieldSingAux.isSmooth_trigPoly S b)
          (FieldSingAux.mean_trigPoly S b), hF _ (mpk_test_trigPoly S b)]
        simp
      have : F' - F = 0 := norm_le_zero_iff.1 hn
      exact sub_eq_zero.1 this
    · intro Kern hK i j r s' t hr hrs hst htT x
      obtain ⟨hbd, hinc, -⟩ := hP (D i) (ρ i) (hA i) (hν i) j x
      have hrt : r ≤ t := hrs.trans hst
      have hrs' : r ≤ s' := hrs
      have hs'T : s' ≤ T := hst.trans htT
      refine ⟨?_, ?_⟩
      · have hn : ‖Kern i j r t x - Kern i j r s' x‖ ≤ C₃ * |t - s'| := by
          refine mpk_norm_le_of_eval _ _ (mul_nonneg hC₃ (abs_nonneg _)) fun S b => ?_
          rw [mpk_eval_sub_trig, hK i j r t hr hrt htT x _ (FieldSingAux.isSmooth_trigPoly S b)
            (FieldSingAux.mean_trigPoly S b), hK i j r s' hr hrs' hs'T x _
            (FieldSingAux.isSmooth_trigPoly S b) (FieldSingAux.mean_trigPoly S b)]
          exact hinc r s' t hr hrs hst htT _ (FieldSingAux.isSmooth_trigPoly S b)
        exact hn.trans (mul_le_mul_of_nonneg_right hC3m (abs_nonneg _))
      · have hn : ‖Kern i j r t x‖ ≤ C₂ := by
          refine mpk_norm_le_of_eval _ _ hC₂ fun S b => ?_
          rw [hK i j r t hr hrt htT x _ (FieldSingAux.isSmooth_trigPoly S b)
            (FieldSingAux.mean_trigPoly S b)]
          exact hbd r t hr hrt htT _ (FieldSingAux.isSmooth_trigPoly S b)
        exact hn.trans hC2m
  · have hbad : ∀ (D₀ : DynData d) (ρ₀ : ℝ → Torus d → ℝ),
        PDE.AdjointData s (Main.gammaIdx d + 2) Rg MB Λ VB D₀ ν₀ T ρ₀ → False := by
      intro D₀ ρ₀ hA₀
      apply hcase
      have h0 := D₀.hs0
      have h1 := D₀.hsd
      have hs := hA₀.hs
      rw [hs] at h0 h1
      refine ⟨?_, h0, h1⟩
      have : (0 : ℝ) < d := lt_of_le_of_lt h0 h1
      exact_mod_cast this
    refine ⟨0, fun {ι} D ρ hA hν => ⟨fun i => ?_, fun Kern hK i => ?_⟩⟩
    · exact (hbad _ _ (hA i)).elim
    · exact (hbad _ _ (hA i)).elim

example := (@path_kernel_increment_torus_proof :
  type_of% @HRS.Whole.AppendixALemmas.path_kernel_increment_torus)

end HRS.MP.KernIncr
