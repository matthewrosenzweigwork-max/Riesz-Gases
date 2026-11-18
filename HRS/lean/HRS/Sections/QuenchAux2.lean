import HRS.Sections.QuenchAux1

/-!
# Packet QUENCH (Q27), part 2: the homogeneous propagator on modes, mode inner products of gradients

* `D = mfData` for gradient data `IsGradientData D s β (fun _ => 0)`;
* `U^{r,t}(c e_j) = e^{-λ_j (t-r)} c e_j` for `0 ≤ r ≤ t`;
* `∫ ∇(α e_j)·∇(α' e_{j'}) dx = αα'(2π|j|)² δ_{jj'}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

lemma dyn_eq {s β : ℝ} (hβ : 0 < β) (hs0 : 0 ≤ s) (hsd : s < d) (D : DynData d)
    (hD : IsGradientData D s β (fun _ => 0)) :
    D = PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ := by
  obtain ⟨h1, h2, h3, h4⟩ := hD
  cases D
  simp only at h1 h2 h3 h4
  subst h1 h2 h3
  simp only [PDE.mfData]
  congr

/-- `r ↦ exp(-λ(T-r)) c e_k` is a classical adjoint solution on `[0,T]` with terminal datum `c e_k`. -/
theorem isClassical_mode (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (c T : ℝ) :
    IsClassicalAdjointSolution (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
      (fun _ => (fun _ : Torus d => (1 : ℝ))) T (fun y => c * Torus.realMode k y)
      (fun r y => Real.exp (-(q38b_rate d s β k) * (T - r)) * (c * Torus.realMode k y)) := by
  have he2 : Torus.IsCk 2 (fun y => c * Torus.realMode k y) :=
    q38b_isCk_const_mul (by simpa using q38b_isCk_realMode k 2) c
  refine ⟨fun r _ => q38b_isCk_const_mul he2 _, fun j hj => ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous fun y : Euc d =>
        iteratedFDeriv ℝ j (Torus.lift (fun y => c * Torus.realMode k y)) y :=
      he2.continuous_iteratedFDeriv (by exact_mod_cast hj)
    have hfun : ∀ r : ℝ, Torus.lift (fun y => Real.exp (-(q38b_rate d s β k) * (T - r)) *
        (c * Torus.realMode k y)) =
        fun z => Real.exp (-(q38b_rate d s β k) * (T - r)) •
          Torus.lift (fun y => c * Torus.realMode k y) z :=
      fun r => rfl
    have hcd : ContDiff ℝ 2 (Torus.lift (fun y => c * Torus.realMode k y)) := he2
    have hcdn : ∀ z, ContDiffAt ℝ j (Torus.lift (fun y => c * Torus.realMode k y)) z := fun z =>
      (hcd.of_le (by exact_mod_cast hj)).contDiffAt
    have hexp : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
        Real.exp (-(q38b_rate d s β k) * (T - p.1.1)) := by fun_prop
    refine (hexp.smul (hcont.comp continuous_snd)).congr fun p => ?_
    rw [hfun, iteratedFDeriv_const_smul_apply' (hcdn p.2)]
    rfl
  · funext y
    simp
  · intro x r hr
    have h1 : HasDerivAt (fun r' : ℝ => -(q38b_rate d s β k) * (T - r')) (q38b_rate d s β k) r := by
      have := ((hasDerivAt_id r).const_sub T).const_mul (-(q38b_rate d s β k))
      simpa using this
    have h2 := (h1.exp).mul_const (c * Torus.realMode k x)
    convert h2 using 1
    have e : (fun y => Real.exp (-(q38b_rate d s β k) * (T - r)) * (c * Torus.realMode k y)) =
        fun y => (Real.exp (-(q38b_rate d s β k) * (T - r)) * c) * Torus.realMode k y := by
      funext y; ring
    rw [e, q38b_bg hd hs0 hsd hβ k]
    ring
  · have hc : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d =>
        -(q38b_rate d s β k * (Real.exp (-(q38b_rate d s β k) * (T - p.1.1)) *
          (c * Torus.realMode k p.2))) := by
      have := q38b_continuous_realMode k
      fun_prop
    refine hc.congr fun p => ?_
    have e : (fun y => Real.exp (-(q38b_rate d s β k) * (T - p.1.1)) * (c * Torus.realMode k y)) =
        fun y => (Real.exp (-(q38b_rate d s β k) * (T - p.1.1)) * c) * Torus.realMode k y := by
      funext y; ring
    rw [e, q38b_bg hd hs0 hsd hβ k]
    ring

/-- `U^{r,τ}(c e_k) = e^{-λ_k(τ-r)} c e_k` for the homogeneous frozen dynamics, `0 ≤ r ≤ τ`. -/
theorem propagator_mode (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (c : ℝ) {r τ : ℝ} (hr : 0 ≤ r) (hrτ : r ≤ τ) :
    propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) (fun _ => (fun _ : Torus d => (1 : ℝ)))
      r τ (fun y => c * Torus.realMode k y) =
      fun y => Real.exp (-(q38b_rate d s β k) * (τ - r)) * (c * Torus.realMode k y) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ with hD
  rcases eq_or_lt_of_le (hr.trans hrτ) with h0 | hpos
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hrτ) hr
    subst hr0
    rw [← h0]
    have hK : PDE.ClassicalAux.ConvKernelFacts d D.s :=
      PDE.ClassicalAux.convKernelFacts_of_two_le hd D.hs0 D.hsd
    have hV1 : Torus.IsCk 1 D.V := contDiff_const
    have hρ1 : Torus.IsCk 1 ((fun _ => (fun _ : Torus d => (1 : ℝ))) (0 : ℝ)) := contDiff_const
    have he2 : Torus.IsCk 2 (fun y => c * Torus.realMode k y) :=
      q38b_isCk_const_mul (by simpa using q38b_isCk_realMode k 2) c
    rw [PDE.MFSemigroup.propagator_zero D hK hV1 _ hρ1 he2]
    funext y
    simp
  · have hprob : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
      ⟨fun _ => zero_le_one, measurable_const, by simp⟩
    have hsm : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
      unfold Torus.IsSmooth Torus.IsCk; exact contDiff_const
    have hsm0 : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := by
      unfold Torus.IsSmooth Torus.IsCk; exact contDiff_const
    obtain ⟨R, MB, Λ, VB, hA⟩ := PDE.MFSemigroup.adjointData_frozen s hs0 hsd β hβ
      (fun _ => (0 : ℝ)) hsm0 (fun _ => (1 : ℝ)) hprob hsm (fun _ => one_pos) (PDE.mStar d)
    have hF := isClassical_mode hd hs0 hsd hβ k c τ
    have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => (fun _ : Torus d => (1 : ℝ))) τ
        (fun y => c * Torus.realMode k y) f := ⟨_, hF⟩
    have hu := PDE.MFSemigroup.classical_adjoint_unique_of_two hd s hs0 hsd (PDE.mStar d)
      (by unfold PDE.mStar; omega) R MB Λ VB D 0 τ (fun _ => (fun _ : Torus d => (1 : ℝ)))
      (hA 0 τ hpos) τ ⟨hpos, le_rfl⟩ _ _ _ hex.choose_spec hF r ⟨hr, hrτ⟩
    simp only [propagator, hex, dite_true]
    rw [hu]

/-- The negated index. -/
def negIdx (j : NonzeroLattice d) : NonzeroLattice d := ⟨-j.1, neg_ne_zero.2 j.2⟩

lemma negIdx_inj {j j' : NonzeroLattice d} : negIdx j = negIdx j' ↔ j = j' := by
  constructor
  · intro h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [negIdx] using this
  · intro h; rw [h]

lemma grad_apply' (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad f x j = Torus.partialDeriv j f x := by
  unfold Torus.grad Torus.partialDeriv
  have h1 := EuclideanSpace.inner_single_right j (1 : ℝ) (gradient (Torus.lift f) (Torus.rep x))
  have h2 := InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift f) (Torus.rep x))
  simp only [one_mul, RCLike.conj_to_real] at h1
  rw [← h1]
  exact h2

lemma inner_grad' (f g : Torus d → ℝ) (x : Torus d) :
    inner ℝ (Torus.grad f x) (Torus.grad g x) =
      ∑ i, Torus.partialDeriv i f x * Torus.partialDeriv i g x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [grad_apply', grad_apply']
  simp [mul_comm]

lemma inner_grad_modes (j j' : NonzeroLattice d) (α α' : ℝ) (x : Torus d) :
    inner ℝ (Torus.grad (fun y => α * Torus.realMode j y) x) (Torus.grad (fun y => α' * Torus.realMode j' y) x) =
      (α * α' * (2 * Real.pi) ^ 2 * ∑ i, ((j.1 i : ℝ) * (j'.1 i : ℝ))) *
        (Torus.realMode (negIdx j) x * Torus.realMode (negIdx j') x) := by
  rw [inner_grad']
  simp_rw [q38b_partialDeriv_c_realMode]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [negIdx]
  ring

lemma int_grad_modes (j j' : NonzeroLattice d) (α α' : ℝ) :
    ∫ x : Torus d, inner ℝ (Torus.grad (fun y => α * Torus.realMode j y) x)
        (Torus.grad (fun y => α' * Torus.realMode j' y) x) =
      if j = j' then α * α' * (2 * Real.pi * Lattice.enorm j.1) ^ 2 else 0 := by
  simp_rw [inner_grad_modes]
  rw [integral_const_mul, Torus.realMode_orthonormal]
  simp only [negIdx_inj]
  by_cases h : j = j'
  · subst h
    have hn : Lattice.enorm j.1 ^ 2 = ∑ i, (j.1 i : ℝ) ^ 2 := by
      unfold Lattice.enorm
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    simp only [ite_true, mul_one]
    have : (2 * Real.pi * Lattice.enorm j.1) ^ 2 = (2 * Real.pi) ^ 2 * ∑ i, (j.1 i : ℝ) * (j.1 i : ℝ) := by
      rw [mul_pow, hn]
      simp_rw [sq]
    rw [this]
    ring
  · simp [h]

/-! ### The OU kernel -/

/-- The covariance kernel `K_λ(t,r) = e^{-λ|t-r|} - e^{-λ(t+r)}` of the OU process started at zero
(up to the factor `v = σ²/(2λ)`). -/
def ouK (lam t r : ℝ) : ℝ := Real.exp (-lam * |t - r|) - Real.exp (-lam * (t + r))

lemma int_exp_Icc {lam : ℝ} (hl : 0 < lam) {ta tb : ℝ} (ha : 0 ≤ ta) (hb : 0 ≤ tb) :
    ∫ r in Set.Icc (0 : ℝ) (min ta tb), Real.exp (-lam * (ta - r)) * Real.exp (-lam * (tb - r)) =
      ouK lam ta tb / (2 * lam) := by
  have hm : 0 ≤ min ta tb := le_min ha hb
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (min ta tb),
      HasDerivAt (fun r => Real.exp (-lam * (ta + tb - 2 * r)) / (2 * lam))
        (Real.exp (-lam * (ta - x)) * Real.exp (-lam * (tb - x))) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -lam * (ta + tb - 2 * r)) (2 * lam) x := by
      have := (((hasDerivAt_id x).const_mul 2).const_sub (ta + tb)).const_mul (-lam)
      convert this using 1
      simp
      ring
    have h2 := (h1.exp).div_const (2 * lam)
    convert h2 using 1
    rw [← Real.exp_add]
    field_simp
    congr 1
    ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp only [mul_zero, sub_zero]
    unfold ouK
    have e1 : -lam * (ta + tb - 2 * min ta tb) = -lam * |ta - tb| := by
      rcases le_total ta tb with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    rw [e1]
    ring_nf
  · apply Continuous.intervalIntegrable
    fun_prop

lemma ouK_comm (lam t r : ℝ) : ouK lam t r = ouK lam r t := by
  unfold ouK
  rw [abs_sub_comm, add_comm]

/-- The block-diagonal OU covariance matrix on the pairs `(js a, ts a)`. -/
def covMat {p : ℕ} (v lam : NonzeroLattice d → ℝ) (js : Fin p → NonzeroLattice d) (ts : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => if js a = js b then v (js a) * ouK (lam (js a)) (ts a) (ts b) else 0

lemma blocks_nonneg {p : ℕ} (W : NonzeroLattice d → ℝ) (hW : ∀ j, 0 ≤ W j)
    (js : Fin p → NonzeroLattice d) (y : Fin p → ℝ) :
    0 ≤ ∑ a, ∑ b, (if js a = js b then W (js a) * y a * y b else 0) := by
  classical
  have key : ∑ a, ∑ b, (if js a = js b then W (js a) * y a * y b else 0) =
      ∑ j ∈ Finset.univ.image js, W j * (∑ a, if js a = j then y a else 0) ^ 2 := by
    have h1 : ∀ j : NonzeroLattice d, W j * (∑ a, if js a = j then y a else 0) ^ 2 =
        ∑ a, ∑ b, (if js a = j ∧ js b = j then W j * y a * y b else 0) := by
      intro j
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases ha : js a = j <;> by_cases hb : js b = j <;> simp [ha, hb] <;> ring
    simp_rw [h1]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : js a = js b
    · rw [if_pos hab]
      have hmem : js a ∈ Finset.univ.image js := Finset.mem_image_of_mem _ (Finset.mem_univ a)
      rw [Finset.sum_eq_single_of_mem (js a) hmem]
      · simp [hab]
      · intro j _ hj
        have : ¬ (js a = j ∧ js b = j) := fun h => hj (h.1.symm)
        simp [this]
    · rw [if_neg hab]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ¬ (js a = j ∧ js b = j) := fun h => hab (h.1.trans h.2.symm)
      simp [this]
  rw [key]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hW j) (sq_nonneg _)

lemma covMat_posSemidef {p : ℕ} (v lam : NonzeroLattice d → ℝ) (hv : ∀ j, 0 ≤ v j)
    (hl : ∀ j, 0 < lam j) (js : Fin p → NonzeroLattice d) (ts : Fin p → ℝ) (ht : ∀ a, 0 ≤ ts a) :
    (covMat v lam js ts).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, covMat, Matrix.of_apply, star_trivial]
    by_cases h : js a = js b
    · rw [if_pos h, if_pos h.symm, ouK_comm, h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ a, ts a ≤ T := ⟨∑ a, |ts a|, fun a => by
      calc ts a ≤ |ts a| := le_abs_self _
        _ ≤ ∑ a, |ts a| := Finset.single_le_sum (f := fun a => |ts a|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ a)⟩
    set g : Fin p → ℝ → ℝ := fun a r => Real.exp (-lam (js a) * (ts a - r)) with hg
    set h : Fin p → ℝ → ℝ := fun a r => x a * Set.indicator (Set.Icc (0 : ℝ) (ts a)) (g a) r with hh
    have hgc : ∀ a, Continuous (g a) := fun a => by simp only [hg]; fun_prop
    have hint : ∀ a b, Integrable (fun r => h a r * h b r) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
      intro a b
      have e : (fun r => h a r * h b r) = fun r => (x a * x b) *
          Set.indicator (Set.Icc (0 : ℝ) (min (ts a) (ts b))) (fun r => g a r * g b r) r := by
        funext r
        simp only [hh]
        by_cases h1 : r ∈ Set.Icc (0 : ℝ) (ts a) <;> by_cases h2 : r ∈ Set.Icc (0 : ℝ) (ts b)
        · have h3 : r ∈ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := ⟨h1.1, le_min h1.2 h2.2⟩
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h3]; ring
        · have h3 : r ∉ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := fun hr => h2 ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
          simp [Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
        · have h3 : r ∉ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := fun hr => h1 ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
          simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
        · have h3 : r ∉ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := fun hr => h1 ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
          simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
      rw [e]
      refine Integrable.const_mul ?_ _
      refine Integrable.indicator ?_ measurableSet_Icc
      exact (Continuous.integrableOn_Icc (by have := hgc a; have := hgc b; fun_prop))
    have hprod : ∀ a b, ∫ r in Set.Icc (0 : ℝ) T, h a r * h b r =
        x a * x b * ∫ r in Set.Icc (0 : ℝ) (min (ts a) (ts b)), g a r * g b r := by
      intro a b
      have e : (fun r => h a r * h b r) = fun r => (x a * x b) *
          Set.indicator (Set.Icc (0 : ℝ) (min (ts a) (ts b))) (fun r => g a r * g b r) r := by
        funext r
        simp only [hh]
        by_cases h1 : r ∈ Set.Icc (0 : ℝ) (ts a) <;> by_cases h2 : r ∈ Set.Icc (0 : ℝ) (ts b)
        · have h3 : r ∈ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := ⟨h1.1, le_min h1.2 h2.2⟩
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h3]; ring
        · have h3 : r ∉ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := fun hr => h2 ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
          simp [Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
        · have h3 : r ∉ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := fun hr => h1 ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
          simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
        · have h3 : r ∉ Set.Icc (0 : ℝ) (min (ts a) (ts b)) := fun hr => h1 ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
          simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
      rw [e, integral_const_mul]
      congr 1
      rw [integral_indicator measurableSet_Icc]
      have hsub : Set.Icc (0 : ℝ) (min (ts a) (ts b)) ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl ((min_le_left _ _).trans (hT a))
      rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 hsub]
    set W : NonzeroLattice d → ℝ := fun j => 2 * lam j * v j with hW
    have step : ∀ a b, x a * (covMat v lam js ts a b * x b) =
        (if js a = js b then W (js a) * ∫ r in Set.Icc (0 : ℝ) T, h a r * h b r else 0) := by
      intro a b
      by_cases hab : js a = js b
      · rw [if_pos hab, hprod]
        simp only [covMat, Matrix.of_apply, if_pos hab, hW, hg]
        have hl' := hl (js a)
        have hta := ht a
        have htb := ht b
        have := int_exp_Icc hl' hta htb
        rw [show (fun r => Real.exp (-lam (js a) * (ts a - r)) * Real.exp (-lam (js b) * (ts b - r))) =
          fun r => Real.exp (-lam (js a) * (ts a - r)) * Real.exp (-lam (js a) * (ts b - r)) by
            funext r; rw [hab]]
        simp only [hab] at this ⊢
        rw [this]
        have hl0 := (hl (js b)).ne'
        field_simp
      · simp [covMat, hab]
    have hsum : dotProduct (star x) (Matrix.mulVec (covMat v lam js ts) x) =
        ∫ r in Set.Icc (0 : ℝ) T, ∑ a, ∑ b, (if js a = js b then W (js a) * h a r * h b r else 0) := by
      simp only [dotProduct, Matrix.mulVec, star_trivial]
      have hint' : ∀ a b, Integrable (fun r => if js a = js b then W (js a) * h a r * h b r else 0)
          (volume.restrict (Set.Icc (0 : ℝ) T)) := by
        intro a b
        by_cases hab : js a = js b
        · simp only [if_pos hab]
          have := (hint a b).const_mul (W (js a))
          refine this.congr (Eventually.of_forall fun r => ?_)
          simp only [mul_assoc]
        · simp only [if_neg hab]
          exact integrable_zero _ _ _
      have hterm : ∀ a b, (if js a = js b then W (js a) * ∫ r in Set.Icc (0 : ℝ) T, h a r * h b r else 0) =
          ∫ r in Set.Icc (0 : ℝ) T, (if js a = js b then W (js a) * h a r * h b r else 0) := by
        intro a b
        by_cases hab : js a = js b
        · simp only [if_pos hab]
          rw [← integral_const_mul]
          simp only [mul_assoc]
        · simp only [if_neg hab, integral_zero]
      calc ∑ a, x a * ∑ b, covMat v lam js ts a b * x b
          = ∑ a, ∑ b, x a * (covMat v lam js ts a b * x b) := by simp_rw [Finset.mul_sum]
        _ = ∑ a, ∑ b, ∫ r in Set.Icc (0 : ℝ) T, (if js a = js b then W (js a) * h a r * h b r else 0) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [step, hterm]
        _ = _ := by
            rw [integral_finset_sum]
            · refine Finset.sum_congr rfl fun a _ => ?_
              rw [integral_finset_sum]
              intro b _
              exact hint' a b
            · intro a _
              exact integrable_finset_sum _ fun b _ => hint' a b
    rw [hsum]
    refine setIntegral_nonneg measurableSet_Icc fun r _ => ?_
    exact blocks_nonneg W (fun j => by simp only [hW]; have := hv j; have := hl j; positivity) js
      (fun a => h a r)

end Qch

end HRS
