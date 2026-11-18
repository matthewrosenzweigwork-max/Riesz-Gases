import HRS.Uniform.Q48bAux5
import HRS.Uniform.Q48eAux3

/-!
# Q54, part 10: the dual operator on `E_r` of a bounded linear map on test functions

`exists_dual_op`: let `Up` be a map on functions which is additive, homogeneous and constant-preserving on smooth
functions and satisfies `‖Up φ‖_{H^r} ≤ M ‖φ‖_{H^r}` for smooth `φ`.  Then there is a bounded operator `V` on `E_r` with
`⟨V z, φ⟩ = ⟨z, Up φ⟩` for every smooth `φ`, and `‖V‖ ≤ M`.

(`V` is the Hilbert-space adjoint of the extension to `ℓ²` of `Up` acting on weighted real Fourier coefficients of
finite trigonometric polynomials.)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

/-- weighted real Fourier coefficients `⟨k⟩^r φ̂(k)`. -/
def wseqF (r : ℝ) (φ : Torus d → ℝ) : NonzeroLattice d → ℝ :=
  fun k => Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k

theorem memℓp_wseqF {r : ℝ} {φ : Torus d → ℝ} (h : MemSobolev r φ) : Memℓp (wseqF r φ) 2 := by
  rw [Torus.memℓp_two_iff]
  refine h.2.congr fun k => ?_
  simp only [wseqF]
  rw [mul_pow, Torus.jp_rpow_sq]

/-- the element of `E_r` with coordinates `⟨k⟩^r φ̂(k)`. -/
def lpOf (r : ℝ) {φ : Torus d → ℝ} (h : MemSobolev r φ) : NegSobolev d r :=
  (⟨wseqF r φ, memℓp_wseqF h⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem coord_lpOf (r : ℝ) {φ : Torus d → ℝ} (h : MemSobolev r φ) (k : NonzeroLattice d) :
    NegSobolev.coord (lpOf r h) k = Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k := rfl

theorem norm_sq_lpOf (r : ℝ) {φ : Torus d → ℝ} (h : MemSobolev r φ) :
    ‖lpOf r h‖ ^ 2 = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2 := by
  rw [q48b_norm_sq]
  refine tsum_congr fun k => ?_
  rw [coord_lpOf, mul_pow, Torus.jp_rpow_sq]

theorem inner_eq_tsum_coord (r : ℝ) (F G : NegSobolev d r) :
    inner ℝ F G = ∑' k : NonzeroLattice d, NegSobolev.coord F k * NegSobolev.coord G k := by
  show (inner ℝ (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G)) = _
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp [NegSobolev.coord, mul_comm]

theorem eval_eq_inner (r : ℝ) (F : NegSobolev d r) {φ : Torus d → ℝ} (h : MemSobolev r φ) :
    NegSobolev.eval F φ = inner ℝ F (lpOf r h) := by
  unfold NegSobolev.eval
  rw [inner_eq_tsum_coord]
  refine tsum_congr fun k => ?_
  rw [coord_lpOf]
  simp only [NegSobolev.fourierCoeff]
  ring

section Dual

variable (r : ℝ) (Up : (Torus d → ℝ) → Torus d → ℝ) (M : ℝ)

abbrev L2 (d : ℕ) := lp (fun _ : NonzeroLattice d => ℝ) 2

/-- inclusion of finitely supported sequences. -/
def eFin (d : ℕ) : (NonzeroLattice d →₀ ℝ) →ₗ[ℝ] L2 d :=
  Finsupp.linearCombination ℝ (fun k => lp.single 2 k (1 : ℝ))

theorem eFin_apply (c : NonzeroLattice d →₀ ℝ) (k : NonzeroLattice d) : (eFin d c) k = c k := by
  classical
  unfold eFin
  rw [Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single, smul_eq_mul]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hk : k ∈ c.support
  · simp [hk]
  · simp only [hk, if_false]
    exact (Finsupp.notMem_support_iff.1 hk).symm

theorem funRealCoeff_finset_sum {ι' : Type*} (T : Finset ι') (α : ι' → ℝ) (g : ι' → Torus d → ℝ)
    (hg : ∀ l ∈ T, MemLp (g l) 2 (volume : Measure (Torus d))) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => ∑ l ∈ T, α l * g l x) k = ∑ l ∈ T, α l * Torus.funRealCoeff (g l) k := by
  classical
  unfold Torus.funRealCoeff
  have hr : MemLp (Torus.realMode k) 2 (volume : Measure (Torus d)) :=
    (Torus.continuous_realMode k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint : ∀ l ∈ T, Integrable (fun x => α l * (Torus.realMode k x * g l x)) := by
    intro l hl
    exact (hr.integrable_mul (hg l hl)).const_mul (α l)
  have e : ∀ x, Torus.realMode k x * ∑ l ∈ T, α l * g l x =
      ∑ l ∈ T, α l * (Torus.realMode k x * g l x) := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ hint]
  exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul]

theorem eFin_single (d : ℕ) (k : NonzeroLattice d) (a : ℝ) :
    eFin d (Finsupp.single k a) = lp.single 2 k a := by
  classical
  unfold eFin
  rw [Finsupp.linearCombination_single]
  ext j
  simp [lp.coeFn_single, Pi.single_apply]

theorem denseRange_eFin (d : ℕ) : DenseRange (eFin d) := by
  classical
  intro y
  have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num) y
  refine mem_closure_of_tendsto hs (Filter.Eventually.of_forall fun F => ?_)
  refine ⟨∑ i ∈ F, Finsupp.single i (y i), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => eFin_single d i (y i)

/-- hypotheses on `Up` on the domain `P` (a space of functions containing the smooth ones). -/
structure DualHyp (P : (Torus d → ℝ) → Prop) (r : ℝ) (Up : (Torus d → ℝ) → Torus d → ℝ) (M : ℝ) : Prop where
  hM : 0 ≤ M
  smooth : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → P φ
  memS : ∀ φ : Torus d → ℝ, P φ → MemSobolev r φ
  closed : ∀ φ ψ : Torus d → ℝ, P φ → P ψ → ∀ α β : ℝ, P (fun x => α * φ x + β * ψ x)
  lin : ∀ φ ψ : Torus d → ℝ, P φ → P ψ → ∀ α β : ℝ,
    Up (fun x => α * φ x + β * ψ x) = fun x => α * Up φ x + β * Up ψ x
  const : ∀ c : ℝ, Up (fun _ => c) = fun _ => c
  bd : ∀ φ : Torus d → ℝ, P φ → MemSobolev r (Up φ) ∧ sobolevNorm r (Up φ) ≤ M * sobolevNorm r φ

theorem DualHyp.finsum {r : ℝ} {Up : (Torus d → ℝ) → Torus d → ℝ} {M : ℝ} {P : (Torus d → ℝ) → Prop} (h : DualHyp P r Up M)
    (T : Finset (NonzeroLattice d)) (α : NonzeroLattice d → ℝ) :
    Up (fun x => ∑ l ∈ T, α l * Torus.realMode l x) =
      fun x => ∑ l ∈ T, α l * Up (Torus.realMode l) x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact h.const 0
  | insert a T ha ih =>
    have e1 : (fun x => ∑ l ∈ insert a T, α l * Torus.realMode l x) =
        fun x => α a * Torus.realMode a x + 1 * ∑ l ∈ T, α l * Torus.realMode l x := by
      funext x; rw [Finset.sum_insert ha]; ring
    have hs : Torus.IsSmooth (fun x => ∑ l ∈ T, α l * Torus.realMode l x) := q48bTest_smooth T α
    rw [e1, h.lin (Torus.realMode a) (fun x => ∑ l ∈ T, α l * Torus.realMode l x)
      (h.smooth _ (q48b_isSmooth_realMode a)) (h.smooth _ hs) (α a) 1, ih]
    funext x
    rw [Finset.sum_insert ha]; ring

variable {r : ℝ} {Up : (Torus d → ℝ) → Torus d → ℝ} {M : ℝ} {P : (Torus d → ℝ) → Prop}

/-- the image of the basis vector `l` (in weighted coordinates). -/
def colSeq (h : DualHyp P r Up M) (l : NonzeroLattice d) : L2 d :=
  (Lattice.jp l.1 ^ (-r)) • (show L2 d from
    lpOf r (h.bd (Torus.realMode l) (h.smooth _ (q48b_isSmooth_realMode l))).1)

/-- the operator on finitely supported weighted sequences. -/
def fMap (h : DualHyp P r Up M) : (NonzeroLattice d →₀ ℝ) →ₗ[ℝ] L2 d :=
  Finsupp.linearCombination ℝ (colSeq h)

/-- the trigonometric polynomial with weighted coefficients `c`. -/
def phiOf (r : ℝ) (c : NonzeroLattice d →₀ ℝ) : Torus d → ℝ :=
  q48bTest c.support (fun l => c l / Lattice.jp l.1 ^ r)

theorem phiOf_smooth (r : ℝ) (c : NonzeroLattice d →₀ ℝ) : Torus.IsSmooth (phiOf r c) :=
  q48bTest_smooth _ _

theorem fMap_eq (h : DualHyp P r Up M) (c : NonzeroLattice d →₀ ℝ) :
    fMap h c = (show L2 d from lpOf r (h.bd (phiOf r c) (h.smooth _ (phiOf_smooth r c))).1) := by
  classical
  ext k
  show (fMap h c) k = Lattice.jp k.1 ^ r * Torus.funRealCoeff (Up (phiOf r c)) k
  unfold fMap
  rw [Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  have hU : Up (phiOf r c) = fun x => ∑ l ∈ c.support, (c l / Lattice.jp l.1 ^ r) * Up (Torus.realMode l) x :=
    h.finsum c.support (fun l => c l / Lattice.jp l.1 ^ r)
  rw [hU, funRealCoeff_finset_sum c.support _ _ (fun l _ => (h.bd _ (h.smooth _ (q48b_isSmooth_realMode l))).1.1) k,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show c l * (Lattice.jp l.1 ^ (-r) * (Lattice.jp k.1 ^ r * Torus.funRealCoeff (Up (Torus.realMode l)) k)) =
    Lattice.jp k.1 ^ r * (c l / Lattice.jp l.1 ^ r * Torus.funRealCoeff (Up (Torus.realMode l)) k)
  have : Lattice.jp l.1 ^ (-r) = (Lattice.jp l.1 ^ r)⁻¹ := Real.rpow_neg (Torus.jp_pos _).le r
  rw [this]
  ring

theorem norm_eFin (c : NonzeroLattice d →₀ ℝ) :
    ‖eFin d c‖ = Real.sqrt (∑ l ∈ c.support, c l ^ 2) := by
  classical
  have h := (Torus.lp_two_sq (eFin d c)).2
  have h2 : ‖eFin d c‖ ^ 2 = ∑ l ∈ c.support, c l ^ 2 := by
    rw [h, tsum_eq_sum (s := c.support)]
    · exact Finset.sum_congr rfl fun l _ => by rw [eFin_apply]
    · intro k hk
      rw [eFin_apply, Finsupp.notMem_support_iff.1 hk]; simp
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

theorem fMap_norm_le (h : DualHyp P r Up M) (c : NonzeroLattice d →₀ ℝ) :
    ‖fMap h c‖ ≤ M * ‖eFin d c‖ := by
  classical
  have hbd := h.bd (phiOf r c) (h.smooth _ (phiOf_smooth r c))
  have e1 : ‖fMap h c‖ = ‖lpOf r hbd.1‖ := by rw [fMap_eq]; rfl
  have e2 : ‖lpOf r hbd.1‖ ≤ sobolevNorm r (Up (phiOf r c)) := by
    have hsq := norm_sq_lpOf r hbd.1
    unfold sobolevNorm
    refine Real.le_sqrt_of_sq_le ?_
    rw [hsq]
    have := sq_nonneg (Torus.mean (Up (phiOf r c)))
    linarith
  have e3 : sobolevNorm r (phiOf r c) = ‖eFin d c‖ := by
    unfold phiOf
    rw [q48bTest_sobolevNorm, norm_eFin]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have hj := Torus.jp_pos l.1
    show Lattice.jp l.1 ^ (2 * r) * (c l / Lattice.jp l.1 ^ r) ^ 2 = c l ^ 2
    rw [div_pow, Torus.jp_rpow_sq]
    field_simp
  rw [e1]
  calc ‖lpOf r hbd.1‖ ≤ sobolevNorm r (Up (phiOf r c)) := e2
    _ ≤ M * sobolevNorm r (phiOf r c) := hbd.2
    _ = M * ‖eFin d c‖ := by rw [e3]

/-- the finite section of a weighted sequence. -/
def secFin (y : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) : NonzeroLattice d →₀ ℝ :=
  ∑ i ∈ F, Finsupp.single i (y i)

theorem secFin_apply (y : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) (k : NonzeroLattice d) :
    secFin y F k = if k ∈ F then y k else 0 := by
  classical
  unfold secFin
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem secFin_support (y : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) :
    (secFin y F).support ⊆ F := by
  intro k hk
  by_contra hF
  have := secFin_apply y F k
  rw [if_neg hF] at this
  exact (Finsupp.mem_support_iff.1 hk) this

theorem eFin_secFin (y : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) :
    eFin d (secFin y F) = ∑ i ∈ F, lp.single 2 i (y i) := by
  unfold secFin
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => eFin_single d i (y i)

theorem coeff_phiOf_sec (r : ℝ) (φ : Torus d → ℝ) (F : Finset (NonzeroLattice d))
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (phiOf r (secFin (wseqF r φ) F)) k = if k ∈ F then Torus.funRealCoeff φ k else 0 := by
  classical
  unfold phiOf
  rw [q48bTest_coeff]
  have hj : Lattice.jp k.1 ^ r ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
  by_cases hkF : k ∈ F
  · rw [if_pos hkF]
    by_cases hks : k ∈ (secFin (wseqF r φ) F).support
    · rw [if_pos hks, secFin_apply, if_pos hkF]
      simp only [wseqF]
      field_simp
    · rw [if_neg hks]
      have h0 : secFin (wseqF r φ) F k = 0 := Finsupp.notMem_support_iff.1 hks
      rw [secFin_apply, if_pos hkF] at h0
      simp only [wseqF] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hj
      · exact h.symm
  · rw [if_neg hkF]
    have : k ∉ (secFin (wseqF r φ) F).support := fun hk => hkF (secFin_support _ F hk)
    rw [if_neg this]

theorem isSmooth_sub' {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x - g x) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.sub hg

theorem isSmooth_add_const' {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) :
    Torus.IsSmooth (fun x => f x + c) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.add contDiff_const

theorem isSmooth_const' (c : ℝ) : Torus.IsSmooth (fun _ : Torus d => c) := by
  unfold Torus.IsSmooth Torus.IsCk
  exact contDiff_const

theorem mean_const' (c : ℝ) : Torus.mean (fun _ : Torus d => c) = c := by
  unfold Torus.mean
  simp

theorem mean_sub_add_const' {f g : Torus d → ℝ} (hf : Integrable f) (hg : Integrable g) (c : ℝ) :
    Torus.mean (fun x => f x - g x + c) = Torus.mean f - Torus.mean g + c := by
  unfold Torus.mean
  have h1 : Integrable (fun x => f x - g x) := hf.sub hg
  have := integral_add (μ := (volume : Measure (Torus d))) h1 (integrable_const c)
  simp only [] at this ⊢
  rw [this, integral_sub hf hg]
  simp

theorem funRealCoeff_sub' {f g : Torus d → ℝ} (hf : MemLp f 2 (volume : Measure (Torus d)))
    (hg : MemLp g 2 (volume : Measure (Torus d))) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => f x - g x) k = Torus.funRealCoeff f k - Torus.funRealCoeff g k := by
  have h := funRealCoeff_finset_sum (Finset.univ : Finset (Fin 2)) (fun i => if i = 0 then (1 : ℝ) else -1)
    (fun i => if i = 0 then f else g) (fun l _ => by split_ifs <;> assumption) k
  simp [Fin.sum_univ_two, sub_eq_add_neg] at h
  simpa [sub_eq_add_neg] using h

theorem norm_lpOf_le_sobolev (r : ℝ) {u : Torus d → ℝ} (hu : MemSobolev r u) :
    ‖lpOf r hu‖ ≤ sobolevNorm r u := by
  have hsq := norm_sq_lpOf r hu
  unfold sobolevNorm
  refine Real.le_sqrt_of_sq_le ?_
  rw [hsq]
  have := sq_nonneg (Torus.mean u)
  linarith

theorem tail_tendsto (s : NonzeroLattice d → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hs : Summable s) :
    Tendsto (fun F : Finset (NonzeroLattice d) => ∑' k, (if k ∈ F then 0 else s k)) atTop (𝓝 0) := by
  classical
  have e : ∀ F : Finset (NonzeroLattice d),
      ∑' k, (if k ∈ F then 0 else s k) = (∑' k, s k) - ∑ k ∈ F, s k := by
    intro F
    have hsF : Summable (fun k => if k ∈ F then s k else 0) :=
      summable_of_ne_finset_zero (s := F) fun k hk => by simp [hk]
    have : (fun k => if k ∈ F then (0 : ℝ) else s k) = fun k => s k - (if k ∈ F then s k else 0) := by
      funext k; split_ifs <;> simp
    have hind : ∑' k, (if k ∈ F then s k else 0) = ∑ k ∈ F, s k := by
      rw [tsum_eq_sum (s := F) (fun k hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [this, hs.tsum_sub hsF, hind]
  simp_rw [e]
  have := hs.hasSum
  have h2 : Tendsto (fun F : Finset (NonzeroLattice d) => (∑' k, s k) - ∑ k ∈ F, s k) atTop
      (𝓝 ((∑' k, s k) - ∑' k, s k)) := tendsto_const_nhds.sub this
  simpa using h2

theorem fMap_sec_bound (h : DualHyp P r Up M) {φ : Torus d → ℝ} (hφ : P φ)
    (F : Finset (NonzeroLattice d)) :
    ‖fMap h (secFin (wseqF r φ) F) - (show L2 d from lpOf r (h.bd φ hφ).1)‖ ≤
      M * Real.sqrt (∑' k : NonzeroLattice d, (if k ∈ F then 0 else
        Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2)) := by
  classical
  have hφS : MemSobolev r φ := h.memS φ hφ
  set c := secFin (wseqF r φ) F with hc
  set φF := phiOf r c with hφF
  have hFsm : Torus.IsSmooth φF := phiOf_smooth r c
  have hFS : MemSobolev r φF := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hFsm r
  set m := Torus.mean φ with hm
  set ψ : Torus d → ℝ := fun x => φF x - φ x + m with hψ
  have hFP : P φF := h.smooth _ hFsm
  have e1 : (fun x => φF x - φ x) = fun x => 1 * φF x + (-1) * φ x := by funext x; ring
  have e2 : ψ = fun x => 1 * (φF x - φ x) + m * 1 := by funext x; simp only [hψ]; ring
  have hPd : P (fun x => φF x - φ x) := by rw [e1]; exact h.closed φF φ hFP hφ 1 (-1)
  have hP1 : P (fun _ : Torus d => (1 : ℝ)) := h.smooth _ (isSmooth_const' 1)
  have hψP : P ψ := by rw [e2]; exact h.closed _ _ hPd hP1 1 m
  have hbF := h.bd φF hFP
  have hb := h.bd φ hφ
  have hbψ := h.bd ψ hψP
  -- Up ψ = Up φF - Up φ + m
  have hC1 : ∀ x, Up ψ x = Up φF x - Up φ x + m := by
    have s1 := h.lin φF φ hFP hφ 1 (-1)
    have s2 := h.lin (fun x => φF x - φ x) (fun _ => (1 : ℝ)) hPd hP1 1 m
    intro x
    have s2' := congrFun s2 x
    have s1' := congrFun s1 x
    have c1 := congrFun (h.const 1) x
    rw [e2, s2']
    rw [e1, s1', c1]
    ring
  have hC2 : ∀ k, Torus.funRealCoeff (Up φF) k - Torus.funRealCoeff (Up φ) k =
      Torus.funRealCoeff (Up ψ) k := by
    intro k
    have : Up ψ = fun x => (Up φF x - Up φ x) + m := funext hC1
    have hg : MemLp (fun x => Up φF x - Up φ x) 2 (volume : Measure (Torus d)) := hbF.1.1.sub hb.1.1
    rw [this, q48b_funRealCoeff_add_const hg m k, funRealCoeff_sub' hbF.1.1 hb.1.1]
  -- the difference of the two elements
  have hdiff : fMap h c - (show L2 d from lpOf r hb.1) = (show L2 d from lpOf r hbψ.1) := by
    rw [fMap_eq]
    ext k
    show Lattice.jp k.1 ^ r * Torus.funRealCoeff (Up φF) k - Lattice.jp k.1 ^ r * Torus.funRealCoeff (Up φ) k =
      Lattice.jp k.1 ^ r * Torus.funRealCoeff (Up ψ) k
    rw [← hC2 k]; ring
  rw [hdiff]
  refine (norm_lpOf_le_sobolev r hbψ.1).trans (hbψ.2.trans ?_)
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) h.hM
  -- sobolevNorm of ψ
  have hint : Integrable φ := hφS.1.integrable one_le_two
  have hmean : Torus.mean ψ = 0 := by
    have hFint : Integrable φF := q48b_integrable_cont (q48bTest_continuous _ _)
    rw [hψ, mean_sub_add_const' (f := φF) (g := φ) hFint hint m]
    rw [show Torus.mean φF = 0 from q48bTest_mean _ _]
    simp [hm]
  have hcoef : ∀ k, Torus.funRealCoeff ψ k = - (if k ∈ F then 0 else Torus.funRealCoeff φ k) := by
    intro k
    have h1 : Torus.funRealCoeff ψ k = Torus.funRealCoeff (fun x => φF x - φ x) k :=
      q48b_funRealCoeff_add_const (hFS.1.sub hφS.1) m k
    rw [h1, funRealCoeff_sub' hFS.1 hφS.1, hφF, coeff_phiOf_sec]
    by_cases hk : k ∈ F <;> simp [hk]
  unfold sobolevNorm
  rw [hmean]
  congr 1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  refine tsum_congr fun k => ?_
  rw [hcoef k]
  by_cases hk : k ∈ F <;> simp [hk]

theorem fMap_sec_tendsto (h : DualHyp P r Up M) {φ : Torus d → ℝ} (hφ : P φ) :
    Tendsto (fun F : Finset (NonzeroLattice d) => fMap h (secFin (wseqF r φ) F)) atTop
      (𝓝 (show L2 d from lpOf r (h.bd φ hφ).1)) := by
  classical
  have hφS : MemSobolev r φ := h.memS φ hφ
  have ht := tail_tendsto (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2)
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)) hφS.2
  have hs : Tendsto (fun F : Finset (NonzeroLattice d) => M * Real.sqrt (∑' k : NonzeroLattice d,
      (if k ∈ F then 0 else Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp ht
    simpa using this.const_mul M
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun F => norm_nonneg _) (fun F => fMap_sec_bound h hφ F) hs

theorem exists_dual_op (h : DualHyp P r Up M) :
    ∃ V : NegSobolev d r →L[ℝ] NegSobolev d r, ‖V‖ ≤ M ∧
      ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), P φ →
        NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ) := by
  classical
  set T : L2 d →L[ℝ] L2 d := (fMap h).extendOfNorm (eFin d) with hT
  have hTe : ∀ c, T (eFin d c) = fMap h c := fun c =>
    LinearMap.extendOfNorm_eq (denseRange_eFin d) ⟨M, fMap_norm_le h⟩ c
  have hTn : ‖T‖ ≤ M := LinearMap.opNorm_extendOfNorm_le (denseRange_eFin d) h.hM (fMap_norm_le h)
  let T' : NegSobolev d r →L[ℝ] NegSobolev d r := T
  let V : NegSobolev d r →L[ℝ] NegSobolev d r := ContinuousLinearMap.adjoint T'
  refine ⟨V, ?_, fun z φ hφ => ?_⟩
  · have : ‖V‖ = ‖T'‖ := ContinuousLinearMap.adjoint.norm_map T'
    rw [this]
    exact hTn
  · have hφS : MemSobolev r φ := h.memS φ hφ
    have hb := h.bd φ hφ
    have hkey : T' (lpOf r hφS) = lpOf r hb.1 := by
      have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num)
        (show L2 d from lpOf r hφS)
      have h1 : Tendsto (fun F : Finset (NonzeroLattice d) => eFin d (secFin (wseqF r φ) F)) atTop
          (𝓝 (show L2 d from lpOf r hφS)) :=
        Tendsto.congr (fun F => (eFin_secFin (wseqF r φ) F).symm) hs
      have h2 : Tendsto (fun F : Finset (NonzeroLattice d) => T (eFin d (secFin (wseqF r φ) F))) atTop
          (𝓝 (T (show L2 d from lpOf r hφS))) := (T.continuous.tendsto _).comp h1
      have h3 : Tendsto (fun F : Finset (NonzeroLattice d) => fMap h (secFin (wseqF r φ) F)) atTop
          (𝓝 (T (show L2 d from lpOf r hφS))) :=
        Tendsto.congr (fun F => hTe _) h2
      have heq : T (show L2 d from lpOf r hφS) = (show L2 d from lpOf r hb.1) :=
        tendsto_nhds_unique h3 (fMap_sec_tendsto h hφ)
      exact heq
    rw [eval_eq_inner r (V z) hφS, eval_eq_inner r z hb.1, ContinuousLinearMap.adjoint_inner_left, hkey]

end Dual

end HRS.Uniform.Q54
