import HRS.Torus.Basic

/-!
# NRS-T, part 1: the algebra `ℂ[ℤ^d]` of trigonometric polynomials (sequence form of the torus argument)

Torus analogue of `XNRSAux1`-`XNRSAux3`.  A trigonometric polynomial is a finitely supported coefficient
function `f : ℤ^d → ℂ`, i.e. an element of the group algebra `TPA d = ℂ[ℤ^d]`; the product of functions is
the convolution product, `∫ f g = (f * g)(0)`, `∂_a` is the multiplier `2πi k_a` (a derivation), `Λ^σ`
the multiplier `(2π|k|)^σ` (`0` at `k = 0`).  `J(σ,h) = ∫ (Λ^σ h)(v·∇h)` and the recursion/induction of
`XNRSAux2/3` are then pure algebra.
-/

noncomputable section

open scoped BigOperators

namespace HRS.Commutator.TorusNote.NRST

open HRS

variable {d : ℕ}

/-- Trigonometric polynomials with complex coefficients: `ℂ[ℤ^d]`. -/
abbrev TPA (d : ℕ) := AddMonoidAlgebra ℂ (Lattice d)

/-- Coefficientwise multiplier. -/
def mulSeq (m : Lattice d → ℂ) (f : TPA d) : TPA d :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support (fun k => m k * f.coeff k) (fun k hk => by
    rw [Finsupp.mem_support_iff]; intro h; apply hk; simp [h]))

@[simp] lemma coeff_mulSeq (m : Lattice d → ℂ) (f : TPA d) (k : Lattice d) :
    (mulSeq m f).coeff k = m k * f.coeff k := by
  simp [mulSeq]

lemma mulSeq_add (m : Lattice d → ℂ) (f g : TPA d) : mulSeq m (f + g) = mulSeq m f + mulSeq m g := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp [mul_add]

lemma mulSeq_zero (m : Lattice d → ℂ) : mulSeq m (0 : TPA d) = 0 := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp

lemma mulSeq_single (m : Lattice d → ℂ) (k : Lattice d) (x : ℂ) :
    mulSeq m (AddMonoidAlgebra.single k x) = AddMonoidAlgebra.single k (m k * x) := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext l
  by_cases h : l = k
  · subst h; simp
  · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm h]

/-- `∂_a`: the multiplier `2πi k_a`. -/
def dd (a : Fin d) (f : TPA d) : TPA d :=
  mulSeq (fun k => 2 * Real.pi * Complex.I * ((k a : ℤ) : ℂ)) f

lemma coeff_dd (a : Fin d) (f : TPA d) (k : Lattice d) :
    (dd a f).coeff k = (2 * Real.pi * Complex.I * ((k a : ℤ) : ℂ)) * f.coeff k := by
  simp [dd]

lemma dd_add (a : Fin d) (f g : TPA d) : dd a (f + g) = dd a f + dd a g := mulSeq_add _ _ _

lemma dd_zero (a : Fin d) : dd a (0 : TPA d) = 0 := mulSeq_zero _

lemma dd_single (a : Fin d) (k : Lattice d) (x : ℂ) :
    dd a (AddMonoidAlgebra.single k x) =
      AddMonoidAlgebra.single k ((2 * Real.pi * Complex.I * ((k a : ℤ) : ℂ)) * x) :=
  mulSeq_single _ _ _

/-- Leibniz rule for `∂_a` (the convolution product is the product of functions). -/
lemma dd_mul (a : Fin d) (f g : TPA d) : dd a (f * g) = dd a f * g + f * dd a g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [dd_zero]
  | add f1 f2 h1 h2 => simp only [add_mul, dd_add, h1, h2]; abel
  | single k x =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp [dd_zero]
    | add g1 g2 h1 h2 => simp only [mul_add, dd_add, h1, h2]; abel
    | single l y =>
      rw [AddMonoidAlgebra.single_mul_single, dd_single, dd_single, dd_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
        ← AddMonoidAlgebra.single_add]
      congr 1
      simp only [Pi.add_apply, Int.cast_add]
      ring

lemma dd_comm (a c : Fin d) (f : TPA d) : dd a (dd c f) = dd c (dd a f) := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp only [coeff_dd]
  ring

lemma dd_coeff_zero (a : Fin d) (f : TPA d) : (dd a f).coeff 0 = 0 := by
  simp [coeff_dd]

/-- Real-valued trigonometric polynomial: `f(-k) = conj f(k)`. -/
def IsRealT (f : TPA d) : Prop := ∀ k, f.coeff (-k) = (starRingEnd ℂ) (f.coeff k)

lemma IsRealT.dd {f : TPA d} (hf : IsRealT f) (a : Fin d) : IsRealT (dd a f) := by
  intro k
  rw [coeff_dd, coeff_dd, hf k]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat,
    Pi.neg_apply, Int.cast_neg]
  ring

/-- `Λ^σ` multiplier (real part of the symbol; `0` at `k = 0`). -/
def lw (σ : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else (2 * Real.pi * Lattice.enorm k) ^ σ

lemma enorm_nonneg (k : Lattice d) : 0 ≤ Lattice.enorm k := norm_nonneg _

lemma enorm_zero : Lattice.enorm (0 : Lattice d) = 0 := by
  unfold Lattice.enorm
  have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  rw [this, norm_zero]

lemma lw_zero (σ : ℝ) : lw σ (0 : Lattice d) = 0 := by simp [lw]

lemma lw_nonneg (σ : ℝ) (k : Lattice d) : 0 ≤ lw σ k := by
  unfold lw
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (mul_nonneg (by positivity) (enorm_nonneg k)) _

lemma lw_neg (σ : ℝ) (k : Lattice d) : lw σ (-k) = lw σ k := by
  unfold lw
  by_cases h : k = 0
  · simp [h]
  · have h' : -k ≠ 0 := neg_ne_zero.2 h
    have : Lattice.enorm (-k) = Lattice.enorm k := by
      unfold Lattice.enorm
      have : Lattice.toEuc (-k) = -Lattice.toEuc k := by
        ext i; simp [Lattice.toEuc]
      rw [this, norm_neg]
    simp [h, h', this]

lemma enorm_pos {k : Lattice d} (hk : k ≠ 0) : 0 < Lattice.enorm k := by
  unfold Lattice.enorm
  apply norm_pos_iff.2
  intro h
  apply hk
  ext i
  have := congrArg (fun x : Euc d => x i) h
  simpa [Lattice.toEuc] using this

lemma lw_pos {σ : ℝ} {k : Lattice d} (hk : k ≠ 0) : 0 < lw σ k := by
  unfold lw
  rw [if_neg hk]
  have := enorm_pos hk
  positivity

lemma lw_mul (σ τ : ℝ) (k : Lattice d) : lw (σ + τ) k = lw σ k * lw τ k := by
  by_cases h : k = 0
  · simp [h, lw_zero]
  · unfold lw
    rw [if_neg h, if_neg h, if_neg h, Real.rpow_add]
    have := enorm_pos h
    positivity

lemma lw_sq (σ : ℝ) (k : Lattice d) : lw σ k ^ 2 = lw (2 * σ) k := by
  have : 2 * σ = σ + σ := by ring
  rw [this, lw_mul, sq]

lemma lw_two (k : Lattice d) : lw 2 k = 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  by_cases h : k = 0
  · simp [h, lw_zero, enorm_zero]
  · unfold lw
    rw [if_neg h]
    have := enorm_pos h
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring

lemma sum_sq_eq_enorm (k : Lattice d) : ∑ a : Fin d, ((k a : ℤ) : ℝ) ^ 2 = Lattice.enorm k ^ 2 := by
  unfold Lattice.enorm Lattice.toEuc
  rw [EuclideanSpace.real_norm_sq_eq]

/-- `Λ^σ`. -/
def lam (σ : ℝ) (f : TPA d) : TPA d := mulSeq (fun k => ((lw σ k : ℝ) : ℂ)) f

lemma coeff_lam (σ : ℝ) (f : TPA d) (k : Lattice d) :
    (lam σ f).coeff k = ((lw σ k : ℝ) : ℂ) * f.coeff k := by
  simp [lam]

lemma lam_dd (σ : ℝ) (a : Fin d) (f : TPA d) : lam σ (dd a f) = dd a (lam σ f) := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp only [coeff_lam, coeff_dd]
  ring

lemma lam_comp (σ τ : ℝ) (f : TPA d) : lam σ (lam τ f) = lam (σ + τ) f := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp only [coeff_lam, lw_mul]
  push_cast
  ring

/-- `Λ^{γ+2} = -∑_a ∂_a∂_a Λ^γ`. -/
lemma lam_add_two (γ : ℝ) (f : TPA d) :
    lam (γ + 2) f = -∑ a, dd a (dd a (lam γ f)) := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  have hs : ∑ a : Fin d, (2 * (Real.pi : ℂ) * Complex.I * ((k a : ℤ) : ℂ)) *
      ((2 * (Real.pi : ℂ) * Complex.I * ((k a : ℤ) : ℂ)) * ((lw γ k : ℝ) : ℂ) * f.coeff k)
      = (-(4 * (Real.pi : ℂ) ^ 2) * ((∑ a : Fin d, ((k a : ℤ) : ℝ) ^ 2 : ℝ) : ℂ)) *
        ((lw γ k : ℝ) : ℂ) * f.coeff k := by
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (4 * (Real.pi : ℂ) ^ 2 * ((k a : ℤ) : ℂ) ^ 2 * ((lw γ k : ℝ) : ℂ) * f.coeff k) * this
  have e : (-∑ a, dd a (dd a (lam γ f))).coeff k =
      -∑ a : Fin d, (2 * (Real.pi : ℂ) * Complex.I * ((k a : ℤ) : ℂ)) *
        ((2 * (Real.pi : ℂ) * Complex.I * ((k a : ℤ) : ℂ)) * ((lw γ k : ℝ) : ℂ) * f.coeff k) := by
    rw [AddMonoidAlgebra.coeff_neg]
    congr 1
    rw [AddMonoidAlgebra.coeff_sum]
    simp [Finsupp.finset_sum_apply, coeff_dd, coeff_lam, mul_assoc]
  rw [e, hs, sum_sq_eq_enorm, coeff_lam, lw_mul, lw_two]
  push_cast
  ring

/-! ### Pairing, `J`, recursion -/

/-- `∫ f g = (f g)(0)`. -/
def pr (f g : TPA d) : ℂ := (f * g).coeff 0

lemma pr_eq_sum (f g : TPA d) : pr f g = ∑ k ∈ f.coeff.support, f.coeff k * g.coeff (-k) := by
  unfold pr
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp [Finsupp.sum]

lemma pr_dd (a : Fin d) (f g : TPA d) : pr (dd a f) g = - pr f (dd a g) := by
  have h := dd_coeff_zero a (f * g)
  rw [dd_mul, AddMonoidAlgebra.coeff_add] at h
  have h2 : pr (dd a f) g + pr f (dd a g) = 0 := h
  exact eq_neg_of_add_eq_zero_left h2

lemma pr_add_left (f g h : TPA d) : pr (f + g) h = pr f h + pr g h := by
  unfold pr; rw [add_mul]; rfl

lemma pr_add_right (f g h : TPA d) : pr f (g + h) = pr f g + pr f h := by
  unfold pr; rw [mul_add]; rfl

lemma pr_neg_left (f g : TPA d) : pr (-f) g = - pr f g := by
  unfold pr; rw [neg_mul]; rfl

lemma pr_sum_left {ι : Type*} (s : Finset ι) (f : ι → TPA d) (g : TPA d) :
    pr (∑ i ∈ s, f i) g = ∑ i ∈ s, pr (f i) g := by
  unfold pr; rw [Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

lemma pr_sum_right {ι : Type*} (s : Finset ι) (f : TPA d) (g : ι → TPA d) :
    pr f (∑ i ∈ s, g i) = ∑ i ∈ s, pr f (g i) := by
  unfold pr; rw [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

/-- `v·∇h = ∑_c v_c ∂_c h`. -/
def adv (V : Fin d → TPA d) (h : TPA d) : TPA d := ∑ c, V c * dd c h

/-- `J(σ,h) = ∫ (Λ^σ h)(v·∇h)`. -/
def Jf (V : Fin d → TPA d) (σ : ℝ) (h : TPA d) : ℂ := pr (lam σ h) (adv V h)

lemma dd_adv (V : Fin d → TPA d) (a : Fin d) (h : TPA d) :
    dd a (adv V h) = ∑ c, dd a (V c) * dd c h + adv V (dd a h) := by
  unfold adv
  have hsum : ∀ (s : Finset (Fin d)) (F : Fin d → TPA d), dd a (∑ c ∈ s, F c) = ∑ c ∈ s, dd a (F c) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp [dd_zero]
    | insert x s hx ih => rw [Finset.sum_insert hx, dd_add, ih, Finset.sum_insert hx]
  rw [hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dd_mul, dd_comm]

lemma Jf_rec (V : Fin d → TPA d) (γ : ℝ) (h : TPA d) :
    Jf V (γ + 2) h = ∑ a, Jf V γ (dd a h) +
      ∑ a, ∑ c, pr (lam γ (dd a h)) (dd a (V c) * dd c h) := by
  unfold Jf
  rw [lam_add_two, pr_neg_left, pr_sum_left, ← Finset.sum_neg_distrib]
  have step : ∀ a : Fin d, - pr (dd a (dd a (lam γ h))) (adv V h) =
      pr (lam γ (dd a h)) (dd a (adv V h)) := by
    intro a
    rw [pr_dd, neg_neg, lam_dd]
  simp_rw [step, dd_adv, pr_add_right, Finset.sum_add_distrib, pr_sum_right]
  rw [add_comm]

/-! ### The homogeneous seminorm, the pairing bound and the induction -/

/-- `‖f‖²_{Ḣ^β} = ∑_{k≠0} (2π|k|)^{2β}|f(k)|²`. -/
def hom (β : ℝ) (f : TPA d) : ℝ := ∑ k ∈ f.coeff.support, lw β k ^ 2 * ‖f.coeff k‖ ^ 2

lemma hom_nonneg (β : ℝ) (f : TPA d) : 0 ≤ hom β f :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma hom_eq_sum (β : ℝ) (f : TPA d) {T : Finset (Lattice d)} (hT : f.coeff.support ⊆ T) :
    hom β f = ∑ k ∈ T, lw β k ^ 2 * ‖f.coeff k‖ ^ 2 := by
  unfold hom
  refine Finset.sum_subset hT fun k _ hk => ?_
  have : f.coeff k = 0 := by simpa using hk
  simp [this]

lemma supp_mulSeq_subset (m : Lattice d → ℂ) (f : TPA d) :
    (mulSeq m f).coeff.support ⊆ f.coeff.support := by
  intro k hk
  rw [Finsupp.mem_support_iff] at hk ⊢
  intro h
  apply hk
  simp [h]

lemma sq_le_enorm_sq (a : Fin d) (k : Lattice d) : ((k a : ℤ) : ℝ) ^ 2 ≤ Lattice.enorm k ^ 2 := by
  rw [← sum_sq_eq_enorm]
  exact Finset.single_le_sum (f := fun i : Fin d => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ a)

lemma hom_dd_le (β : ℝ) (a : Fin d) (f : TPA d) : hom β (dd a f) ≤ hom (β + 1) f := by
  rw [hom_eq_sum β (dd a f) (supp_mulSeq_subset _ f), hom_eq_sum (β + 1) f (T := f.coeff.support) le_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [coeff_dd, norm_mul]
  have h1 : lw (β + 1) k ^ 2 = lw β k ^ 2 * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) := by
    rw [lw_sq, show 2 * (β + 1) = 2 * β + 2 by ring, lw_mul, lw_two, ← lw_sq]
  have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k a : ℤ) : ℂ))‖ ^ 2 =
      4 * Real.pi ^ 2 * ((k a : ℤ) : ℝ) ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le, mul_one, Complex.norm_intCast]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  rw [h1, mul_pow, h2]
  have := sq_le_enorm_sq a k
  have h0 : 0 ≤ lw β k ^ 2 * ‖f.coeff k‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2),
    mul_nonneg h0 (le_of_lt (by positivity : (0 : ℝ) < 1))]

lemma sum_neg_le (β : ℝ) (T : Finset (Lattice d)) (g : TPA d) :
    ∑ k ∈ T, (lw β k * ‖g.coeff (-k)‖) ^ 2 ≤ hom β g := by
  classical
  have h1 : ∑ k ∈ T, (lw β k * ‖g.coeff (-k)‖) ^ 2 =
      ∑ k ∈ T.image Neg.neg, lw β k ^ 2 * ‖g.coeff k‖ ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ h => neg_injective h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lw_neg, mul_pow]
  rw [h1]
  calc ∑ k ∈ T.image Neg.neg, lw β k ^ 2 * ‖g.coeff k‖ ^ 2
      ≤ ∑ k ∈ T.image Neg.neg ∪ g.coeff.support, lw β k ^ 2 * ‖g.coeff k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => by positivity)
    _ = hom β g := (hom_eq_sum β g Finset.subset_union_right).symm

lemma norm_pr_lam_le (β : ℝ) (f g : TPA d) :
    ‖pr (lam (2 * β) f) g‖ ≤ Real.sqrt (hom β f) * Real.sqrt (hom β g) := by
  classical
  set T : Finset (Lattice d) := f.coeff.support with hT
  have h1 : pr (lam (2 * β) f) g =
      ∑ k ∈ T, (lam (2 * β) f).coeff k * g.coeff (-k) := by
    rw [pr_eq_sum]
    refine Finset.sum_subset (supp_mulSeq_subset _ f) fun k _ hk => ?_
    have : (lam (2 * β) f).coeff k = 0 := by simpa using hk
    simp [this]
  calc ‖pr (lam (2 * β) f) g‖ = ‖∑ k ∈ T, (lam (2 * β) f).coeff k * g.coeff (-k)‖ := by rw [h1]
    _ ≤ ∑ k ∈ T, ‖(lam (2 * β) f).coeff k * g.coeff (-k)‖ := norm_sum_le _ _
    _ = ∑ k ∈ T, (lw β k * ‖f.coeff k‖) * (lw β k * ‖g.coeff (-k)‖) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coeff_lam, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (lw_nonneg _ _), two_mul, lw_mul]
        ring
    _ ≤ Real.sqrt (∑ k ∈ T, (lw β k * ‖f.coeff k‖) ^ 2) *
          Real.sqrt (∑ k ∈ T, (lw β k * ‖g.coeff (-k)‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (hom β f) * Real.sqrt (hom β g) := by
        have e : ∑ k ∈ T, (lw β k * ‖f.coeff k‖) ^ 2 = hom β f := by
          rw [hom_eq_sum β f (T := T) le_rfl]
          exact Finset.sum_congr rfl fun k _ => by rw [mul_pow]
        rw [e]
        gcongr
        exact sum_neg_le β T g

/-- `C_0 = C₀`, `C_{m+1} = d C_m + d² C_B`. -/
def Cm (d : ℕ) (C0 CB : ℝ) : ℕ → ℝ
  | 0 => C0
  | m + 1 => d * Cm d C0 CB m + (d : ℝ) ^ 2 * CB

lemma Cm_nonneg {C0 CB : ℝ} (h0 : 0 ≤ C0) (hB : 0 ≤ CB) (m : ℕ) : 0 ≤ Cm d C0 CB m := by
  induction m with
  | zero => exact h0
  | succ m ih => simp only [Cm]; positivity

/-- Induction on `m`: `‖J(2α'+2m,h)‖ ≤ C_m K ‖Λ^{α'+m}h‖²` (torus `xind`). -/
theorem ind (V : Fin d → TPA d) {K C0 CB α' : ℝ} (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hCB : 0 ≤ CB)
    (hα' : 0 ≤ α')
    (hbase : ∀ h : TPA d, IsRealT h → ‖Jf V (2 * α') h‖ ≤ C0 * K * hom α' h) {N : ℕ}
    (hmul : ∀ m : ℕ, 1 ≤ m → m ≤ N → ∀ (a c : Fin d) (Γ : TPA d), IsRealT Γ → Γ.coeff 0 = 0 →
      hom (α' + m - 1) (dd a (V c) * Γ) ≤ (CB * K) ^ 2 * hom (α' + m - 1) Γ) :
    ∀ (m : ℕ), m ≤ N → ∀ (h : TPA d), IsRealT h →
      ‖Jf V (2 * α' + 2 * m) h‖ ≤ Cm d C0 CB m * K * hom (α' + m) h := by
  intro m
  induction m with
  | zero =>
    intro _ h hh
    simpa [Cm] using hbase h hh
  | succ m ih =>
    intro hmN h hh
    have hrec := Jf_rec V (2 * α' + 2 * m) h
    have e1 : 2 * α' + 2 * (m : ℝ) + 2 = 2 * α' + 2 * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at hrec
    rw [hrec]
    set X := hom (α' + ((m + 1 : ℕ) : ℝ)) h with hX
    have hX0 : 0 ≤ X := hom_nonneg _ _
    have e2 : α' + ((m + 1 : ℕ) : ℝ) = α' + m + 1 := by push_cast; ring
    have hdd : ∀ a : Fin d, hom (α' + m) (dd a h) ≤ X := fun a => by
      rw [hX, e2]; exact hom_dd_le _ a h
    have hA : ∀ a : Fin d, ‖Jf V (2 * α' + 2 * m) (dd a h)‖ ≤ Cm d C0 CB m * K * X := by
      intro a
      refine (ih (by omega) (dd a h) (hh.dd a)).trans ?_
      exact mul_le_mul_of_nonneg_left (hdd a) (mul_nonneg (Cm_nonneg hC0 hCB m) hK)
    have hR : ∀ a c : Fin d, ‖pr (lam (2 * α' + 2 * m) (dd a h)) (dd a (V c) * dd c h)‖ ≤ CB * K * X := by
      intro a c
      have e3 : 2 * α' + 2 * (m : ℝ) = 2 * (α' + m) := by ring
      rw [e3]
      refine (norm_pr_lam_le _ _ _).trans ?_
      have h2 : hom (α' + m) (dd a (V c) * dd c h) ≤ (CB * K) ^ 2 * X := by
        have := hmul (m + 1) (by omega) hmN a c (dd c h) (hh.dd c) (dd_coeff_zero c h)
        have e4 : α' + ((m + 1 : ℕ) : ℝ) - 1 = α' + m := by push_cast; ring
        rw [e4] at this
        exact this.trans (mul_le_mul_of_nonneg_left (hdd c) (sq_nonneg _))
      calc Real.sqrt (hom (α' + m) (dd a h)) * Real.sqrt (hom (α' + m) (dd a (V c) * dd c h))
          ≤ Real.sqrt X * Real.sqrt ((CB * K) ^ 2 * X) := by
            gcongr
            exact hdd a
        _ = CB * K * X := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hCB hK)]
            have := Real.mul_self_sqrt hX0
            rw [show Real.sqrt X * (CB * K * Real.sqrt X) = CB * K * (Real.sqrt X * Real.sqrt X) by ring, this]
    calc ‖∑ a, Jf V (2 * α' + 2 * m) (dd a h) +
          ∑ a, ∑ c, pr (lam (2 * α' + 2 * m) (dd a h)) (dd a (V c) * dd c h)‖
        ≤ ∑ a, ‖Jf V (2 * α' + 2 * m) (dd a h)‖ +
          ∑ a, ∑ c, ‖pr (lam (2 * α' + 2 * m) (dd a h)) (dd a (V c) * dd c h)‖ := by
          refine (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Fin d, Cm d C0 CB m * K * X + ∑ a : Fin d, ∑ c : Fin d, CB * K * X :=
          add_le_add (Finset.sum_le_sum fun a _ => hA a)
            (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => hR a c)
      _ = Cm d C0 CB (m + 1) * K * X := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Cm]
          ring

end HRS.Commutator.TorusNote.NRST
