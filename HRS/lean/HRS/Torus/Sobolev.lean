import HRS.Torus.Basic

/-!
# HRS foundations II: Sobolev spaces on the torus and path spaces

Source: HRS periodic main paper, display `H:eq:path-spaces` (source lines 521-528):
`E_m = H^{-m}_0(𝕋^d)`, `𝒳_{m,T} = C([0,T]; E_m)`, `‖w‖_{𝒳_{m,T}} = sup_{0≤t≤T} ‖w^t‖_{H^{-m}}`.
Norm conventions: `⟨k⟩ = (1+4π²|k|²)^{1/2}`, `‖e_k‖_{H^m} = ⟨k⟩^m`
(source lines 1976, 8129, 8274-8275): `E_r` has the real orthonormal basis
`ε_k = ⟨k⟩^r e_k`, zero frequency excluded.

## Representation

`H^{-m}_0(𝕋^d)` is represented by the *weighted coefficient sequence*
`F ↦ (⟨k⟩^{-m} F̂(k))_{k ≠ 0} ∈ ℓ²(ℤ^d∖{0}; ℝ)`, where `F̂(k) = F(e_k)` are the
coefficients in the real basis `e_k` of `HRS.Torus.realMode`.  This map is an
isometric isomorphism `H^{-m}_0 ≅ ℓ²`, so we *define* `NegSobolev d m` to be
`lp (fun _ : NonzeroLattice d => ℝ) 2` (a real Hilbert space in Mathlib) and
record the dictionary:

* the coordinate `F k` of `F : NegSobolev d m` is `⟨k⟩^{-m} F̂(k)`;
* `‖F‖ = (∑_{k≠0} ⟨k⟩^{-2m} |F̂(k)|²)^{1/2} = ‖F‖_{H^{-m}}`;
* the pairing with a smooth test function is `F(φ) = ∑_{k≠0} F̂(k) φ̂(k)`.

Embedding a finite signed measure (or a function) into `NegSobolev d m` requires
square-summability of the weighted coefficients, which holds for every finite
measure iff `2m > d`.  To keep the embedding a genuine definition, it is defined
by cases on `Memℓp`, returning `0` in the (never attained, for `2m > d`) bad case;
`ofSeq_coe_of_mem` and `memℓp_of_bounded` (FOUND-02) remove the case split.

Different `m` give *different* types `NegSobolev d m` (it is a `def`, not an
`abbrev`), because the identification of a distribution with its weighted
sequence depends on `m`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

/-! ### Helper lemmas (FOUND-02): Fourier decay, series representation, Sobolev bounds -/

namespace Torus
variable {d : ℕ}

theorem mk_add (x y : Euc d) : mk (x + y) = mk x + mk y := by
  funext i; simp [mk]

theorem mk_toEuc (n : Lattice d) : mk (Lattice.toEuc n) = 0 := by
  funext i; simp [mk, Lattice.toEuc]

theorem continuous_mk : Continuous (mk : Euc d → Torus d) := by
  unfold mk
  refine continuous_pi fun i => ?_
  exact (AddCircle.continuous_mk' _).comp (by fun_prop)

theorem rep_mk (y : Euc d) : ∃ n : Lattice d, rep (mk y) = y + Lattice.toEuc n := by
  have h : ∀ i, ∃ n : ℤ, (rep (mk y)) i = y i + n := by
    intro i
    have h1 : ((rep (mk y) i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := by
      have := congrFun (mk_rep (mk y)) i
      simpa [mk] using this
    have h2 := (QuotientAddGroup.eq).mp h1
    rw [AddSubgroup.mem_zmultiples_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨-n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    push_cast
    linarith
  choose n hn using h
  refine ⟨n, ?_⟩
  ext i
  simp [hn i, Lattice.toEuc]

theorem lift_descend {E : Type*} (G : Euc d → E)
    (hG : ∀ (y : Euc d) (n : Lattice d), G (y + Lattice.toEuc n) = G y) :
    lift (fun x => G (rep x)) = G := by
  funext y
  obtain ⟨n, hn⟩ := rep_mk y
  simp [lift, hn, hG]

theorem continuous_of_continuous_lift {E : Type*} [TopologicalSpace E] {φ : Torus d → E}
    (h : Continuous (lift φ)) : Continuous φ := by
  let K : Set (Euc d) := (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  let f : K → Torus d := fun x => mk x.1
  have hf : Continuous f := continuous_mk.comp continuous_subtype_val
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨⟨rep x, ?_⟩, mk_rep x⟩
    refine ⟨fun i => rep x i, fun i _ => ?_, rfl⟩
    have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  have hq : Topology.IsQuotientMap f := hf.isClosedMap.isQuotientMap hf hsurj
  rw [hq.continuous_iff]
  exact h.comp continuous_subtype_val


/-- complex Fourier coefficient `∫ e^{-2πi k·x} ψ(x) dx` of a real function -/
def fcoef (ψ : Torus d → ℝ) (k : Lattice d) : ℂ := ∫ x, mode (-k) x * (ψ x : ℂ)

theorem dot_add (k : Lattice d) (x y : Euc d) : Lattice.dot k (x + y) = Lattice.dot k x + Lattice.dot k y := by
  simp [Lattice.dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul (k : Lattice d) (h : ℝ) (x : Euc d) : Lattice.dot k (h • x) = h * Lattice.dot k x := by
  simp [Lattice.dot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem mode_add_arg (k : Lattice d) (x y : Torus d) : mode k (x + y) = mode k x * mode k y := by
  rw [← mk_rep x, ← mk_rep y, ← mk_add, mode_mk, mode_mk, mode_mk, ← Complex.exp_add, dot_add]
  congr 1
  push_cast
  ring

theorem mode_neg_lattice (k : Lattice d) (x : Torus d) : mode (-k) x * mode k x = 1 := by
  rw [mode_neg, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mode]
  simp

theorem fcoef_translate (ψ : Torus d → ℝ) (k : Lattice d) (a : Torus d) :
    ∫ x, mode (-k) x * (ψ (x + a) : ℂ) = mode k a * fcoef ψ k := by
  have h := integral_add_right_eq_self (μ := (volume : Measure (Torus d)))
    (fun y => mode (-k) (y - a) * (ψ y : ℂ)) a
  have e1 : ∀ y, mode (-k) (y - a) = mode (-k) y * mode k a := by
    intro y
    have h1 : mode (-k) y = mode (-k) (y - a) * mode (-k) a := by
      rw [← mode_add_arg]; simp
    calc mode (-k) (y - a) = mode (-k) (y - a) * (mode (-k) a * mode k a) := by
          rw [mode_neg_lattice, mul_one]
      _ = _ := by rw [← mul_assoc, ← h1]
  simp only [add_sub_cancel_right] at h
  rw [h, fcoef, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [e1]
  ring


/-- periodic functions on `ℝ^d` -/
def Per {E : Type*} (G : Euc d → E) : Prop := ∀ (y : Euc d) (n : Lattice d), G (y + Lattice.toEuc n) = G y

/-- the torus function with lift `G` -/
def descend {E : Type*} (G : Euc d → E) : Torus d → E := fun x => G (rep x)

theorem lift_descend' {E : Type*} {G : Euc d → E} (hG : Per G) : lift (descend G) = G :=
  lift_descend G hG

theorem continuous_descend {E : Type*} [TopologicalSpace E] {G : Euc d → E} (hG : Per G)
    (hc : Continuous G) : Continuous (descend G) :=
  continuous_of_continuous_lift (by rw [lift_descend' hG]; exact hc)

theorem descend_mk {E : Type*} {G : Euc d → E} (hG : Per G) (y : Euc d) : descend G (mk y) = G y :=
  congrFun (lift_descend' hG) y

theorem Per.bound {G : Euc d → ℝ} (hG : Per G) (hc : Continuous G) : ∃ B, ∀ y, |G y| ≤ B := by
  have hcd := continuous_descend hG hc
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hcd.continuousOn
  refine ⟨B, fun y => ?_⟩
  have := hB (mk y) (Set.mem_univ _)
  rwa [descend_mk hG, Real.norm_eq_abs] at this

theorem Per.fderiv {G : Euc d → ℝ} (hG : Per G) (v : Euc d) : Per (fun y => fderiv ℝ G y v) := by
  intro y n
  have : (fun x => G (x + Lattice.toEuc n)) = G := funext fun x => hG x n
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := y) (Lattice.toEuc n)
  rw [this] at h2
  show _root_.fderiv ℝ G (y + Lattice.toEuc n) v = _root_.fderiv ℝ G y v
  rw [← h2]


theorem mode_mk_smul (k : Lattice d) (h : ℝ) (v : Euc d) :
    mode k (mk (h • v)) = Complex.exp ((h : ℂ) * (2 * Real.pi * Complex.I * (Lattice.dot k v : ℝ))) := by
  rw [mode_mk, dot_smul]
  congr 1
  push_cast
  ring

theorem fcoef_fderiv {G : Euc d → ℝ} (hG : Per G) (hd : ContDiff ℝ 1 G) (v : Euc d) (k : Lattice d) :
    fcoef (descend (fun y => _root_.fderiv ℝ G y v)) k =
      (2 * Real.pi * Complex.I * (Lattice.dot k v : ℝ)) * fcoef (descend G) k := by
  set g := descend G with hg
  have hgc : Continuous g := continuous_descend hG hd.continuous
  have hper' := hG.fderiv v
  have hcont' : Continuous (fun y => _root_.fderiv ℝ G y v) :=
    (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgc' : Continuous (descend fun y => _root_.fderiv ℝ G y v) := continuous_descend hper' hcont'
  obtain ⟨B, hB⟩ := hper'.bound hcont'
  let F : ℝ → Torus d → ℂ := fun h x => mode (-k) x * (G (rep x + h • v) : ℂ)
  let F' : ℝ → Torus d → ℂ := fun h x => mode (-k) x * (_root_.fderiv ℝ G (rep x + h • v) v : ℂ)
  have hFg : ∀ h x, F h x = mode (-k) x * (g (x + mk (h • v)) : ℂ) := by
    intro h x
    have : g (x + mk (h • v)) = G (rep x + h • v) := by
      have e : x + mk (h • v) = mk (rep x + h • v) := by rw [mk_add, mk_rep]
      rw [e, hg, descend_mk hG]
    simp only [F, this]
  have hFint : ∀ h, ∫ x, F h x = mode k (mk (h • v)) * fcoef g k := by
    intro h
    simp_rw [hFg]
    exact fcoef_translate g k _
  have hmodec : Continuous (mode (-k) : Torus d → ℂ) := continuous_mode _
  have hFc : ∀ h, Continuous (F h) := by
    intro h
    have : F h = fun x => mode (-k) x * (g (x + mk (h • v)) : ℂ) := funext (hFg h)
    rw [this]
    exact hmodec.mul (Complex.continuous_ofReal.comp (hgc.comp (continuous_id.add continuous_const)))
  have hderiv : HasDerivAt (fun h => ∫ x, F h x) (∫ x, F' 0 x) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
      (F := F) (F' := F') (bound := fun _ => B * 1) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun h => (hFc h).aestronglyMeasurable) 
      ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ?_ ?_
      (integrable_const _) ?_).2
    · have : F' 0 = fun x => mode (-k) x *
          ((descend (fun y => _root_.fderiv ℝ G y v) x : ℝ) : ℂ) := by
        funext x; simp [F', descend]
      rw [this]
      exact (hmodec.mul (Complex.continuous_ofReal.comp hgc')).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x h _ => ?_
      simp only [F', norm_mul, norm_mode, one_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hB _
    · refine Filter.Eventually.of_forall fun x h _ => ?_
      have h1 : HasDerivAt (fun h : ℝ => rep x + h • v) v h := by
        simpa using ((hasDerivAt_id h).smul_const v).const_add (rep x)
      have h2 := (hd.differentiable one_ne_zero (rep x + h • v)).hasFDerivAt.comp_hasDerivAt h h1
      exact (h2.ofReal_comp.const_mul (mode (-k) x))
  have hexp : HasDerivAt (fun h : ℝ => mode k (mk (h • v)) * fcoef g k)
      ((2 * Real.pi * Complex.I * (Lattice.dot k v : ℝ)) * fcoef g k) 0 := by
    simp_rw [mode_mk_smul]
    have := (((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const
      (2 * Real.pi * Complex.I * (Lattice.dot k v : ℝ))).cexp.mul_const (fcoef g k))
    simpa using this
  have hfun : (fun h => ∫ x, F h x) = fun h : ℝ => mode k (mk (h • v)) * fcoef g k := funext hFint
  rw [hfun] at hderiv
  have := hderiv.unique hexp
  rw [← this]
  simp [fcoef, F', descend]


theorem Per.iteratedFDeriv {G : Euc d → ℝ} (hG : Per G) (i : ℕ) :
    Per (fun y => _root_.iteratedFDeriv ℝ i G y) := by
  intro y n
  have : (fun x => G (x + Lattice.toEuc n)) = G := funext fun x => hG x n
  have h2 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := G) i (x := y) (Lattice.toEuc n)
  rw [this] at h2
  show _root_.iteratedFDeriv ℝ i G (y + Lattice.toEuc n) = _root_.iteratedFDeriv ℝ i G y
  rw [← h2]

theorem Per.iteratedFDeriv_apply {G : Euc d → ℝ} (hG : Per G) {i : ℕ} (m : Fin i → Euc d) :
    Per (fun y => _root_.iteratedFDeriv ℝ i G y m) := by
  intro y n
  show _root_.iteratedFDeriv ℝ i G (y + Lattice.toEuc n) m = _root_.iteratedFDeriv ℝ i G y m
  exact congrArg (fun F => F m) (hG.iteratedFDeriv i y n)

theorem continuous_iteratedFDeriv_apply {G : Euc d → ℝ} {n : ℕ} (hd : ContDiff ℝ n G) {i : ℕ}
    (hi : i ≤ n) (m : Fin i → Euc d) : Continuous (fun y => _root_.iteratedFDeriv ℝ i G y m) :=
  (continuous_eval_const m).comp
    (hd.continuous_iteratedFDeriv (by exact_mod_cast hi))

theorem fcoef_iteratedFDeriv {G : Euc d → ℝ} (hG : Per G) {n : ℕ} (hd : ContDiff ℝ n G) (k : Lattice d) :
    ∀ (i : ℕ) (hi : i ≤ n) (m : Fin i → Euc d),
    fcoef (descend (fun y => _root_.iteratedFDeriv ℝ i G y m)) k =
      (2 * Real.pi * Complex.I) ^ i * (∏ s, ((Lattice.dot k (m s) : ℝ) : ℂ)) * fcoef (descend G) k := by
  intro i
  induction i with
  | zero => intro hi m; simp [iteratedFDeriv_zero_apply]
  | succ i ih =>
    intro hi m
    have hdiff : Differentiable ℝ (_root_.iteratedFDeriv ℝ i G) :=
      hd.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_of_succ_le hi)
    have e : (fun y => _root_.iteratedFDeriv ℝ (i + 1) G y m) =
        fun y => _root_.fderiv ℝ (fun z => _root_.iteratedFDeriv ℝ i G z (Fin.tail m)) y (m 0) := by
      funext y
      exact (hdiff y).iteratedFDeriv_succ_apply_left'
    rw [e]
    have hH : ContDiff ℝ 1 (fun z => _root_.iteratedFDeriv ℝ i G z (Fin.tail m)) := by
      have := hd.iteratedFDeriv_right (i := i) (m := 1) (by exact_mod_cast (by omega : 1 + i ≤ n))
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Euc d) ℝ (Fin.tail m)).contDiff.comp this
    rw [fcoef_fderiv (hG.iteratedFDeriv_apply _) hH, ih (Nat.le_of_succ_le hi), Fin.prod_univ_succ]
    simp only [Fin.tail, pow_succ]
    ring


theorem summable_lattice_iff (f : Lattice d → ℝ) :
    Summable f ↔ Summable (fun k : NonzeroLattice d => f k.1) := by
  classical
  have h1 : Summable f ↔ Summable (Function.update f 0 0) := by
    constructor
    · intro h; exact h.update 0 0
    · intro h; have := h.update 0 (f 0); simpa using this
  have h2 : Function.update f 0 0 = ({0}ᶜ : Set (Lattice d)).indicator f := by
    funext k
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, Function.update_of_ne hk]
  rw [h1, h2, ← summable_subtype_iff_indicator]
  rfl

theorem tsum_lattice (f : Lattice d → ℝ) (hf : Summable f) :
    ∑' k, f k = f 0 + ∑' k : NonzeroLattice d, f k.1 := by
  classical
  rw [hf.tsum_eq_add_tsum_ite 0]
  congr 1
  have h2 : (fun n => if n = 0 then 0 else f n) = ({0}ᶜ : Set (Lattice d)).indicator f := by
    funext k
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]
  rw [h2, ← tsum_subtype]
  rfl


theorem toEuc_neg (k : Lattice d) : Lattice.toEuc (-k) = - Lattice.toEuc k := by
  ext i; simp [Lattice.toEuc]

theorem jp_neg (k : Lattice d) : Lattice.jp (-k) = Lattice.jp k := by
  simp [Lattice.jp, Lattice.enorm, toEuc_neg]

theorem jp_zero : Lattice.jp (0 : Lattice d) = 1 := by
  have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  simp [Lattice.jp, Lattice.enorm, this]

theorem jp_pos (k : Lattice d) : 0 < Lattice.jp k := lt_of_lt_of_le one_pos (jp_ge_one k)

theorem fcoef_zero (φ : Torus d → ℝ) : fcoef φ 0 = (mean φ : ℂ) := by
  simp [fcoef, mean, mode_zero, integral_complex_ofReal]

theorem two_mul_norm_fcoef_sq {φ : Torus d → ℝ} (hφ : Integrable φ) (k : NonzeroLattice d) :
    2 * ‖fcoef φ k.1‖ ^ 2 = funRealCoeff φ k ^ 2 + funRealCoeff φ (negNZ d k) ^ 2 := by
  have h := funRealCoeff_sq_add_neg (φ := φ) k
  have h2 := norm_sq_coeff hφ k.1
  show _ = funRealCoeff φ k ^ 2 + funRealCoeff φ ⟨-k.1, neg_ne_zero.mpr k.2⟩ ^ 2
  rw [h]
  unfold fcoef
  rw [h2]

theorem weighted_fcoef_sq (s : ℝ) {φ : Torus d → ℝ} (hφ : Integrable φ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ s * funRealCoeff φ k ^ 2) :
    Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ s * ‖fcoef φ k.1‖ ^ 2) ∧
    ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ s * ‖fcoef φ k.1‖ ^ 2 =
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ s * funRealCoeff φ k ^ 2 := by
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ s * funRealCoeff φ k ^ 2 with ha
  have hneg : Summable fun k => a (negNZ d k) := (negNZ d).summable_iff.mpr hs
  have e : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ s * ‖fcoef φ k.1‖ ^ 2 = (a k + a (negNZ d k)) / 2 := by
    intro k
    have h := two_mul_norm_fcoef_sq hφ k
    have hj : Lattice.jp (negNZ d k).1 = Lattice.jp k.1 := jp_neg k.1
    simp only [ha, hj]
    have : ‖fcoef φ k.1‖ ^ 2 = (funRealCoeff φ k ^ 2 + funRealCoeff φ (negNZ d k) ^ 2) / 2 := by
      linarith
    rw [this]; ring
  simp_rw [e]
  refine ⟨(hs.add hneg).div_const 2, ?_⟩
  rw [tsum_div_const, hs.tsum_add hneg, Equiv.tsum_eq (negNZ d) a]
  ring


theorem cs_tsum {ι : Type*} (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ha2 : Summable fun i => a i ^ 2) (hb2 : Summable fun i => b i ^ 2) :
    Summable (fun i => a i * b i) ∧
      ∑' i, a i * b i ≤ Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) := by
  have := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
    Real.HolderConjugate.two_two ha hb (by simpa using ha2) (by simpa using hb2)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using this

theorem jp_rpow_sq (s : ℝ) (k : Lattice d) : (Lattice.jp k ^ s) ^ 2 = Lattice.jp k ^ (2 * s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (jp_pos k).le]
  push_cast; ring_nf

theorem sobolev_coeff_bound {m : ℝ} {i : ℕ} (hm : (d : ℝ) / 2 + i < m) {φ : Torus d → ℝ}
    (hφ : Integrable φ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * funRealCoeff φ k ^ 2) :
    Summable (fun k : Lattice d => Lattice.jp k ^ i * ‖fcoef φ k‖) ∧
    ∑' k : Lattice d, Lattice.jp k ^ i * ‖fcoef φ k‖ ≤ |mean φ| +
      Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - i)))) *
      Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * funRealCoeff φ k ^ 2) := by
  obtain ⟨hs2, he⟩ := weighted_fcoef_sq (2 * m) hφ hs
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(m - i)) with ha
  set b : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * ‖fcoef φ k.1‖ with hb
  have hd : (d : ℝ) < 2 * (m - i) := by linarith
  have ha2 : Summable fun k => a k ^ 2 := by
    have := summable_jp_rpow (d := d) (m - i) hd
    refine this.congr fun k => ?_
    simp only [ha]; rw [jp_rpow_sq]; ring_nf
  have hb2 : Summable fun k => b k ^ 2 := by
    refine hs2.congr fun k => ?_
    simp only [hb]; rw [mul_pow, jp_rpow_sq]
  have hcs := cs_tsum a b (fun k => Real.rpow_nonneg (jp_pos _).le _)
    (fun k => mul_nonneg (Real.rpow_nonneg (jp_pos _).le _) (norm_nonneg _)) ha2 hb2
  have hprod : ∀ k : NonzeroLattice d, a k * b k = Lattice.jp k.1 ^ i * ‖fcoef φ k.1‖ := by
    intro k
    simp only [ha, hb]
    rw [← mul_assoc, ← Real.rpow_add (jp_pos k.1)]
    have : -(m - (i : ℝ)) + m = i := by ring
    rw [this, Real.rpow_natCast]
  have hsum : Summable (fun k : Lattice d => Lattice.jp k ^ i * ‖fcoef φ k‖) := by
    rw [summable_lattice_iff]
    exact hcs.1.congr hprod
  refine ⟨hsum, ?_⟩
  rw [tsum_lattice _ hsum]
  have h0 : Lattice.jp (0 : Lattice d) ^ i * ‖fcoef φ 0‖ = |mean φ| := by
    rw [jp_zero, fcoef_zero]; simp
  rw [h0]
  gcongr
  have e1 : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ i * ‖fcoef φ k.1‖ = ∑' k, a k * b k :=
    tsum_congr fun k => (hprod k).symm
  rw [e1]
  refine hcs.2.trans ?_
  have e2 : ∑' k, a k ^ 2 = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - i))) := by
    refine tsum_congr fun k => ?_
    simp only [ha]; rw [jp_rpow_sq]; ring_nf
  have e3 : ∑' k, b k ^ 2 = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * funRealCoeff φ k ^ 2 := by
    rw [← he]
    refine tsum_congr fun k => ?_
    simp only [hb]; rw [mul_pow, jp_rpow_sq]
  rw [e2, e3]


theorem hasSum_fcoef_series {g : Torus d → ℝ} (hc : Continuous g)
    (hs : Summable fun k : Lattice d => ‖fcoef g k‖) (x : Torus d) :
    HasSum (fun k : Lattice d => fcoef g k * mode k x) (g x : ℂ) := by
  let f : C(UnitAddTorus (Fin d), ℂ) := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp hc⟩
  have hco : ∀ k, UnitAddTorus.mFourierCoeff f k = fcoef g k := by
    intro k
    simp only [UnitAddTorus.mFourierCoeff, fcoef, smul_eq_mul]
    rw [volume_eq_pi_haar]
    rfl
  have hsum : Summable (UnitAddTorus.mFourierCoeff f) := by
    refine Summable.of_norm (hs.congr fun k => ?_)
    rw [hco]
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum x
  simp only [hco, smul_eq_mul] at this
  exact this

theorem abs_le_tsum_fcoef {g : Torus d → ℝ} (hc : Continuous g)
    (hs : Summable fun k : Lattice d => ‖fcoef g k‖) (x : Torus d) :
    |g x| ≤ ∑' k : Lattice d, ‖fcoef g k‖ := by
  have h := hasSum_fcoef_series hc hs x
  have h1 : ‖(g x : ℂ)‖ ≤ ∑' k : Lattice d, ‖fcoef g k * mode k x‖ := by
    rw [← h.tsum_eq]
    exact norm_tsum_le_tsum_norm h.summable.norm
  simpa [norm_mul, norm_mode] using h1


theorem dot_eq_inner (k : Lattice d) (v : Euc d) : Lattice.dot k v = inner ℝ (Lattice.toEuc k) v := by
  simp [Lattice.dot, PiLp.inner_apply, Lattice.toEuc, mul_comm]

theorem abs_dot_le (k : Lattice d) (v : Euc d) : |Lattice.dot k v| ≤ Lattice.enorm k * ‖v‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm _ _

theorem descend_lift (φ : Torus d → ℝ) : descend (lift φ) = φ := by
  funext x; simp [descend, lift, mk_rep]

theorem norm_iteratedFDeriv_le_tsum {φ : Torus d → ℝ} {n : ℕ} (hd : ContDiff ℝ n (lift φ))
    {i : ℕ} (hi : i ≤ n)
    (hs : Summable fun k : Lattice d => Lattice.jp k ^ i * ‖fcoef φ k‖) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (lift φ) y‖ ≤ ∑' k : Lattice d, Lattice.jp k ^ i * ‖fcoef φ k‖ := by
  have hG : Per (lift φ) := fun y n => lift_periodic φ y n
  refine ContinuousMultilinearMap.opNorm_le_bound (tsum_nonneg fun k => mul_nonneg
    (pow_nonneg (jp_pos k).le _) (norm_nonneg _)) fun m => ?_
  set g := descend (fun z => iteratedFDeriv ℝ i (lift φ) z m) with hg
  have hper : Per (fun z => iteratedFDeriv ℝ i (lift φ) z m) := hG.iteratedFDeriv_apply m
  have hgc : Continuous g := continuous_descend hper (continuous_iteratedFDeriv_apply hd hi m)
  set P : ℝ := ∏ s, ‖m s‖ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun s _ => norm_nonneg _
  have hco : ∀ k, ‖fcoef g k‖ ≤ P * (Lattice.jp k ^ i * ‖fcoef φ k‖) := by
    intro k
    rw [hg, fcoef_iteratedFDeriv hG hd k i hi m, descend_lift, norm_mul, norm_mul, norm_pow, norm_prod]
    have h1 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [Complex.norm_I]
    rw [h1]
    have h2 : ∏ s, ‖((Lattice.dot k (m s) : ℝ) : ℂ)‖ ≤ ∏ s, (Lattice.enorm k * ‖m s‖) :=
      Finset.prod_le_prod₀ (fun s _ => norm_nonneg _) (fun s _ => by
        simpa [Real.norm_eq_abs] using abs_dot_le k (m s))
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (2 * Real.pi) ^ i * (Lattice.enorm k ^ i * P) ≤ Lattice.jp k ^ i * P := by
      rw [← mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg Real.two_pi_pos.le (norm_nonneg (Lattice.toEuc k))) (two_pi_enorm_le_jp k) i) hP0
    have h4 := mul_le_mul_of_nonneg_left h2 (pow_nonneg Real.two_pi_pos.le i)
    have h5 : (2 * Real.pi) ^ i * ∏ s, ‖((Lattice.dot k (m s) : ℝ) : ℂ)‖ ≤ Lattice.jp k ^ i * P :=
      h4.trans h3
    calc (2 * Real.pi) ^ i * (∏ s, ‖((Lattice.dot k (m s) : ℝ) : ℂ)‖) * ‖fcoef φ k‖
        = ((2 * Real.pi) ^ i * ∏ s, ‖((Lattice.dot k (m s) : ℝ) : ℂ)‖) * ‖fcoef φ k‖ := rfl
      _ ≤ (Lattice.jp k ^ i * P) * ‖fcoef φ k‖ := mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
      _ = P * (Lattice.jp k ^ i * ‖fcoef φ k‖) := by ring
  have hsg : Summable fun k : Lattice d => ‖fcoef g k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hco (hs.mul_left P)
  have := abs_le_tsum_fcoef hgc hsg (mk y)
  rw [hg, descend_mk hper] at this
  refine this.trans ?_
  calc ∑' k : Lattice d, ‖fcoef g k‖ ≤ ∑' k : Lattice d, P * (Lattice.jp k ^ i * ‖fcoef φ k‖) :=
        hsg.tsum_le_tsum hco (hs.mul_left P)
    _ = _ := by rw [tsum_mul_left]; ring


theorem abs_realMode_le (k : NonzeroLattice d) (x : Torus d) : |realMode k x| ≤ Real.sqrt 2 := by
  unfold realMode
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by simpa using norm_cosMode_le k.1 x)
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by simpa using norm_sinMode_le k.1 x)

theorem abs_funRealCoeff_le {φ : Torus d → ℝ} (hφ : Integrable φ) (k : NonzeroLattice d) :
    |funRealCoeff φ k| ≤ Real.sqrt 2 * ‖fcoef φ k.1‖ := by
  have h := two_mul_norm_fcoef_sq hφ k
  rw [← Real.sqrt_sq_eq_abs, show ‖fcoef φ k.1‖ = Real.sqrt (‖fcoef φ k.1‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm, ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (funRealCoeff φ (negNZ d k))]

theorem real_pair_eq {g : Torus d → ℝ} (hg : Integrable g) (k : NonzeroLattice d) (x : Torus d) :
    (fcoef g k.1 * mode k.1 x).re =
      (funRealCoeff g k * realMode k x +
        funRealCoeff g (negNZ d k) * realMode (negNZ d k) x) / 2 := by
  have hc : fcoef g k.1 = ((cosCoeff g k.1 : ℝ) : ℂ) + ((-sinCoeff g k.1 : ℝ) : ℂ) * Complex.I :=
    integral_mode_mul_real hg k.1
  have hre : (fcoef g k.1 * mode k.1 x).re = cosCoeff g k.1 * cosMode k.1 x + sinCoeff g k.1 * sinMode k.1 x := by
    rw [hc]
    simp [Complex.mul_re, Complex.mul_im, cosMode, sinMode]
  rw [hre]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hneg := isPosHalf_neg k.1 k.2
  have e1 : (negNZ d k).1 = -k.1 := rfl
  by_cases hp : Lattice.IsPosHalf k.1
  · have hq : ¬ Lattice.IsPosHalf (-k.1) := fun h => (hneg.mp h) hp
    rw [funRealCoeff_eq, funRealCoeff_eq, e1]
    unfold realMode
    simp only [e1, hp, hq, ite_true, ite_false, sinCoeff_neg, sinMode_neg]
    linear_combination (-(cosCoeff g k.1 * cosMode k.1 x + sinCoeff g k.1 * sinMode k.1 x) / 2) * h2
  · have hq : Lattice.IsPosHalf (-k.1) := hneg.mpr hp
    rw [funRealCoeff_eq, funRealCoeff_eq, e1]
    unfold realMode
    simp only [e1, hp, hq, ite_true, ite_false, cosCoeff_neg, cosMode_neg]
    linear_combination (-(cosCoeff g k.1 * cosMode k.1 x + sinCoeff g k.1 * sinMode k.1 x) / 2) * h2


theorem summable_norm_funRealCoeff {g : Torus d → ℝ} (hg : Integrable g)
    (hs : Summable fun k : Lattice d => ‖fcoef g k‖) :
    Summable fun k : NonzeroLattice d => |funRealCoeff g k| := by
  have hs' := (summable_lattice_iff _).mp hs
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) (abs_funRealCoeff_le hg) (hs'.mul_left _)

theorem hasSum_realExpansion {g : Torus d → ℝ} (hc : Continuous g)
    (hs : Summable fun k : Lattice d => ‖fcoef g k‖) (x : Torus d) :
    HasSum (fun k : NonzeroLattice d => funRealCoeff g k * realMode k x) (g x - mean g) := by
  have hg : Integrable g := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set t : NonzeroLattice d → ℝ := fun k => funRealCoeff g k * realMode k x with ht
  have hts : Summable t := by
    have h1 := (summable_norm_funRealCoeff hg hs).mul_left (Real.sqrt 2)
    refine Summable.of_norm_bounded h1 fun k => ?_
    rw [ht, Real.norm_eq_abs, abs_mul]
    calc |funRealCoeff g k| * |realMode k x| ≤ |funRealCoeff g k| * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left (abs_realMode_le k x) (abs_nonneg _)
      _ = _ := mul_comm _ _
  set r : Lattice d → ℝ := fun k => (fcoef g k * mode k x).re with hr
  have hrsum : HasSum r (g x) := by
    have := Complex.reCLM.hasSum (hasSum_fcoef_series hc hs x)
    simpa [hr] using this
  have hr0 : r 0 = mean g := by
    simp [hr, fcoef_zero, mode_zero]
  have hrN := (summable_lattice_iff r).mp hrsum.summable
  have htot := tsum_lattice r hrsum.summable
  rw [hrsum.tsum_eq, hr0] at htot
  have hpair : ∀ k : NonzeroLattice d, r k.1 = (t k + t (negNZ d k)) / 2 := fun k =>
    real_pair_eq hg k x
  have htn : Summable fun k => t (negNZ d k) := (negNZ d).summable_iff.mpr hts
  have : ∑' k : NonzeroLattice d, t k = g x - mean g := by
    have h1 : ∑' k : NonzeroLattice d, r k.1 = ∑' k : NonzeroLattice d, t k := by
      simp_rw [hpair]
      rw [tsum_div_const, hts.tsum_add htn, Equiv.tsum_eq (negNZ d) t]
      ring
    linarith
  rw [← this]
  exact hts.hasSum


theorem continuous_realMode (k : NonzeroLattice d) : Continuous (realMode k) := by
  unfold realMode
  split_ifs
  · exact continuous_const.mul (continuous_cosMode _)
  · exact continuous_const.mul (continuous_sinMode _)

theorem pair_eq_mean_add_tsum (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    (hc : Continuous g) (hs : Summable fun k : Lattice d => ‖fcoef g k‖) :
    pair μ g = mean g + ∑' k : NonzeroLattice d, funRealCoeff g k * measureRealCoeff μ k := by
  have hg : Integrable g := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set F : NonzeroLattice d → Torus d → ℝ := fun k x => funRealCoeff g k * realMode k x with hF
  have hFc : ∀ k, Continuous (F k) := fun k => continuous_const.mul (continuous_realMode k)
  have hFi : ∀ k, Integrable (F k) μ := fun k =>
    (hFc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ k, ∫ a, ‖F k a‖ ∂μ ≤ Real.sqrt 2 * |funRealCoeff g k| := by
    intro k
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => ‖F k a‖)
      (C := Real.sqrt 2 * |funRealCoeff g k|) (Filter.Eventually.of_forall fun a => by
        rw [norm_norm, hF]
        simp only [Real.norm_eq_abs, abs_mul]
        calc |funRealCoeff g k| * |realMode k a| ≤ |funRealCoeff g k| * Real.sqrt 2 :=
              mul_le_mul_of_nonneg_left (abs_realMode_le k a) (abs_nonneg _)
          _ = _ := mul_comm _ _)
    simp only [probReal_univ, mul_one] at h
    exact (le_abs_self _).trans (by simpa using h)
  have hsum : Summable fun k => ∫ a, ‖F k a‖ ∂μ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun a => norm_nonneg _) hbd
      ((summable_norm_funRealCoeff hg hs).mul_left _)
  have h := hasSum_integral_of_summable_integral_norm hFi hsum
  have e1 : ∀ a, ∑' k, F k a = g a - mean g := fun a => (hasSum_realExpansion hc hs a).tsum_eq
  simp_rw [e1] at h
  have e2 : ∫ a, (g a - mean g) ∂μ = pair μ g - mean g := by
    have hgμ : Integrable g μ :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hgμ (integrable_const _)]
    simp [pair]
  have e3 : ∀ k, ∫ a, F k a ∂μ = funRealCoeff g k * measureRealCoeff μ k := by
    intro k
    simp only [hF]
    rw [integral_const_mul]
    rfl
  simp_rw [e3] at h
  rw [e2] at h
  rw [h.tsum_eq]
  ring


theorem abs_measureRealCoeff_le (μ : Measure (Torus d)) [IsFiniteMeasure μ] (k : NonzeroLattice d) :
    |Torus.measureRealCoeff μ k| ≤ Real.sqrt 2 * (μ Set.univ).toReal := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := realMode k) (C := Real.sqrt 2)
    (Filter.Eventually.of_forall fun x => by simpa using abs_realMode_le k x)
  simpa [measureRealCoeff, Measure.real] using h

theorem norm_fcoef_le_of_bound {g : Torus d → ℝ} {B : ℝ} (hB : ∀ x, |g x| ≤ B) (k : Lattice d) :
    ‖fcoef g k‖ ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
    (f := fun x => mode (-k) x * (g x : ℂ)) (C := B)
    (Filter.Eventually.of_forall fun x => by simp [norm_mul, norm_mode, hB x])
  simpa [fcoef] using this

theorem fcoef_pow_decay {φ : Torus d → ℝ} {n : ℕ} (hd : ContDiff ℝ n (lift φ)) :
    ∃ B : ℝ, ∀ k : NonzeroLattice d, ‖fcoef φ k.1‖ * Lattice.jp k.1 ^ n ≤ B := by
  have hG : Per (lift φ) := fun y n => lift_periodic φ y n
  obtain ⟨B₀, hB₀⟩ := bddAbove_norm_iteratedFDeriv_lift n φ hd
  refine ⟨B₀ * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n, fun k => ?_⟩
  have hpi := Real.pi_pos
  have hk0 : 0 < Lattice.enorm k.1 := by
    have := (jp_le_enorm k)
    have h1 := jp_ge_one k.1
    by_contra h
    have : Lattice.enorm k.1 ≤ 0 := not_lt.mp h
    nlinarith
  set e : Euc d := (Lattice.enorm k.1)⁻¹ • Lattice.toEuc k.1 with he
  have hne : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hk0]
    exact inv_mul_cancel₀ hk0.ne'
  have hdot : Lattice.dot k.1 e = Lattice.enorm k.1 := by
    rw [dot_eq_inner, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
    unfold Lattice.enorm
    field_simp
  let m : Fin n → Euc d := fun _ => e
  set g := descend (fun z => iteratedFDeriv ℝ n (lift φ) z m) with hg
  have hper : Per (fun z => iteratedFDeriv ℝ n (lift φ) z m) := hG.iteratedFDeriv_apply m
  have hbd : ∀ x, |g x| ≤ B₀ := by
    intro x
    rw [hg, ← mk_rep x, descend_mk hper]
    have h1 := (iteratedFDeriv ℝ n (lift φ) (rep x)).le_opNorm m
    have h2 : ∏ i, ‖m i‖ = 1 := by simp [m, hne]
    rw [h2, mul_one] at h1
    exact (Real.norm_eq_abs _ ▸ h1).trans (hB₀ ⟨rep x, rfl⟩)
  have h1 := norm_fcoef_le_of_bound hbd k.1
  rw [hg, fcoef_iteratedFDeriv hG hd k.1 n le_rfl m, descend_lift] at h1
  have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by simp [Complex.norm_I]
  rw [norm_mul, norm_mul, norm_pow, h2, norm_prod] at h1
  simp only [m, hdot, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0] at h1
  have h3 : Lattice.jp k.1 ^ n ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * (2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n := by
    rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (jp_pos _).le ?_ n
    have := jp_le_enorm k
    calc Lattice.jp k.1 ≤ (1 + 2 * Real.pi) * Lattice.enorm k.1 := this
      _ = _ := by field_simp
  calc ‖fcoef φ k.1‖ * Lattice.jp k.1 ^ n
      ≤ ‖fcoef φ k.1‖ * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * (2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * ((2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n * ‖fcoef φ k.1‖) := by ring
    _ ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * B₀ := by gcongr
    _ = _ := by ring


theorem summable_fcoef_of_contDiff {φ : Torus d → ℝ} (hd : ∀ n : ℕ, ContDiff ℝ n (lift φ)) :
    Summable fun k : Lattice d => ‖fcoef φ k‖ := by
  obtain ⟨B, hB⟩ := fcoef_pow_decay (hd (d + 1))
  rw [summable_lattice_iff]
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2) (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hs.mul_left B)
  have hj := jp_pos k.1
  have e : Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) / 2))) = (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
      Real.rpow_natCast]
  rw [e]
  have := hB k
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hj _)]
  exact this

theorem pair_sub_eq_tsum (μ ν : Measure (Torus d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : Torus d → ℝ} (hc : Continuous g) (hs : Summable fun k : Lattice d => ‖fcoef g k‖) :
    pair μ g - pair ν g = ∑' k : NonzeroLattice d,
      (measureRealCoeff μ k - measureRealCoeff ν k) * funRealCoeff g k := by
  have hg : Integrable g := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsm : ∀ (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ],
      Summable fun k : NonzeroLattice d => funRealCoeff g k * measureRealCoeff ρ k := by
    intro ρ _
    refine Summable.of_norm_bounded ((summable_norm_funRealCoeff hg hs).mul_left (Real.sqrt 2)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have := abs_measureRealCoeff_le ρ k
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at this
    calc |funRealCoeff g k| * |measureRealCoeff ρ k| ≤ |funRealCoeff g k| * Real.sqrt 2 := by
          gcongr
      _ = _ := mul_comm _ _
  rw [pair_eq_mean_add_tsum μ hc hs, pair_eq_mean_add_tsum ν hc hs, add_sub_add_left_eq_sub,
    ← (hsm μ).tsum_sub (hsm ν)]
  refine tsum_congr fun k => ?_
  ring


theorem memℓp_two_iff {ι : Type*} (f : ι → ℝ) : Memℓp f 2 ↔ Summable fun i => f i ^ 2 := by
  rw [memℓp_gen_iff (by simp)]
  simp [Real.rpow_two, sq_abs]

theorem lp_two_sq {ι : Type*} (F : lp (fun _ : ι => ℝ) 2) :
    Summable (fun i => F i ^ 2) ∧ ‖F‖ ^ 2 = ∑' i, F i ^ 2 := by
  refine ⟨(memℓp_two_iff _).mp F.2, ?_⟩
  have := lp.norm_rpow_eq_tsum (by simp) F
  simpa [Real.rpow_two, sq_abs] using this

end Torus

/-- `E_m = H^{-m}_0(𝕋^d)`, realised as `ℓ²(ℤ^d ∖ {0}; ℝ)` through the weighted
coefficients `⟨k⟩^{-m} F̂(k)`. -/
def NegSobolev (d : ℕ) (_m : ℝ) : Type := lp (fun _ : NonzeroLattice d => ℝ) 2

namespace NegSobolev

variable {d : ℕ} {m : ℝ}

instance : NormedAddCommGroup (NegSobolev d m) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : NonzeroLattice d => ℝ) 2))

instance : InnerProductSpace ℝ (NegSobolev d m) :=
  inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : NonzeroLattice d => ℝ) 2))

instance : CompleteSpace (NegSobolev d m) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : NonzeroLattice d => ℝ) 2))

instance : MeasurableSpace (NegSobolev d m) := borel _

instance : BorelSpace (NegSobolev d m) := ⟨rfl⟩

/-- The weighted coordinate `⟨k⟩^{-m} F̂(k)`. -/
def coord (F : NegSobolev d m) (k : NonzeroLattice d) : ℝ :=
  (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k

/-- The unweighted real Fourier coefficient `F̂(k) = F(e_k)`. -/
def fourierCoeff (F : NegSobolev d m) (k : NonzeroLattice d) : ℝ :=
  Lattice.jp k.1 ^ m * coord F k

open Classical in
/-- The element of `E_m` with prescribed (unweighted) coefficients `c k = F̂(k)`;
`0` if the weighted sequence is not square-summable. -/
def ofSeq (m : ℝ) (c : NonzeroLattice d → ℝ) : NegSobolev d m :=
  if h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2 then
    (⟨fun k => Lattice.jp k.1 ^ (-m) * c k, h⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)
  else 0

theorem ofSeq_of_mem (c : NonzeroLattice d → ℝ)
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) :
    (ofSeq m c : lp (fun _ : NonzeroLattice d => ℝ) 2) =
      (⟨fun k => Lattice.jp k.1 ^ (-m) * c k, h⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2) := by
  unfold ofSeq
  simp [h] <;> rfl

theorem coord_sq (F : NegSobolev d m) :
    Summable (fun k => coord F k ^ 2) ∧ ‖F‖ ^ 2 = ∑' k, coord F k ^ 2 :=
  Torus.lp_two_sq (F : lp (fun _ : NonzeroLattice d => ℝ) 2)

/-- Pairing `F(φ) = ∑_{k≠0} F̂(k) φ̂(k)` of `F ∈ H^{-m}_0` with a test function `φ`
(sum taken as `tsum`, which is the value whenever the series converges). -/
def eval (F : NegSobolev d m) (φ : Torus d → ℝ) : ℝ :=
  ∑' k : NonzeroLattice d, fourierCoeff F k * Torus.funRealCoeff φ k

/-- The embedding of a finite signed measure `μ - ν` into `E_m` (zero frequency dropped,
so only the zero-mass part is recorded; for `μ(𝕋^d) = ν(𝕋^d)` nothing is lost). -/
def ofMeasureDiff (m : ℝ) (μ ν : Measure (Torus d)) : NegSobolev d m :=
  ofSeq m fun k => Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k

/-- The embedding of a single finite measure modulo constants (zero frequency dropped). -/
def ofMeasure (m : ℝ) (μ : Measure (Torus d)) : NegSobolev d m :=
  ofSeq m fun k => Torus.measureRealCoeff μ k

/-- The embedding of an integrable function modulo constants. -/
def ofFun (m : ℝ) (f : Torus d → ℝ) : NegSobolev d m :=
  ofSeq m fun k => Torus.funRealCoeff f k

/-- The scaled empirical error `κ (μ_N - μ)` as an element of `E_m`. -/
def scaledFluc (m : ℝ) (κ : ℝ) {N : ℕ} (X : Config d N) (μ : Measure (Torus d)) :
    NegSobolev d m :=
  κ • ofMeasureDiff m (empirical X) μ

/-- Centered continuous linear "evaluation at `φ`" is bounded by the `H^m` norm of `φ`
(work package FOUND-02). -/
theorem abs_eval_le (F : NegSobolev d m) (φ : Torus d → ℝ)
    (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    |eval F φ| ≤ ‖F‖ * Real.sqrt (∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) := by
  classical
  set y : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k with hy
  have hy2 : Summable fun k => y k ^ 2 := by
    refine hφ.congr fun k => ?_
    simp only [hy]; rw [mul_pow, Torus.jp_rpow_sq]
  obtain ⟨hF2, hFn⟩ := coord_sq F
  have e : eval F φ = ∑' k, coord F k * y k := by
    unfold eval fourierCoeff
    refine tsum_congr fun k => ?_
    simp only [hy]; ring
  have hcs := Torus.cs_tsum (fun k => |coord F k|) (fun k => |y k|) (fun _ => abs_nonneg _)
    (fun _ => abs_nonneg _) (by simpa [sq_abs] using hF2) (by simpa [sq_abs] using hy2)
  rw [e]
  have h1 : |∑' k, coord F k * y k| ≤ ∑' k, |coord F k| * |y k| := by
    have hs : Summable fun k => ‖coord F k * y k‖ := by simpa [abs_mul] using hcs.1
    simpa [abs_mul] using norm_tsum_le_tsum_norm hs
  refine h1.trans (hcs.2.trans ?_)
  simp only [sq_abs]
  have : Real.sqrt (∑' k, coord F k ^ 2) = ‖F‖ := by
    rw [← hFn]
    exact Real.sqrt_sq (norm_nonneg _)
  rw [this]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_of_eq (tsum_congr fun k => ?_)))
    (norm_nonneg _)
  simp only [hy]; rw [mul_pow, Torus.jp_rpow_sq]

/-- Weighted coefficients of a bounded coefficient sequence are square-summable
when `2m > d` (FOUND-02). -/
theorem memℓp_of_bounded (hm : (d : ℝ) < 2 * m) (c : NonzeroLattice d → ℝ)
    (hc : ∃ C, ∀ k, |c k| ≤ C) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2 := by
  obtain ⟨C, hC⟩ := hc
  rw [Torus.memℓp_two_iff]
  have hs := summable_jp_rpow (d := d) m hm
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hs.mul_left (C ^ 2))
  have hj := Torus.jp_pos k.1
  rw [mul_pow, Torus.jp_rpow_sq, show -(2 * m) = 2 * (-m) by ring, mul_comm (C ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hj.le _)
  rw [← sq_abs (c k)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC k) 2

theorem coord_ofSeq_of_mem (c : NonzeroLattice d → ℝ)
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) (k) :
    coord (ofSeq m c) k = Lattice.jp k.1 ^ (-m) * c k := by
  unfold coord
  rw [ofSeq_of_mem c h]

/-- Fourier coefficients of a finite measure are bounded by its mass. -/
theorem abs_measureRealCoeff_le (μ : Measure (Torus d)) [IsFiniteMeasure μ] (k : NonzeroLattice d) :
    |Torus.measureRealCoeff μ k| ≤ Real.sqrt 2 * (μ Set.univ).toReal := by
  exact Torus.abs_measureRealCoeff_le μ k

/-- For `2m > d` the embedding of a finite signed measure is the honest weighted sequence. -/
theorem fourierCoeff_ofMeasureDiff (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : NonzeroLattice d) :
    fourierCoeff (ofMeasureDiff m μ ν) k =
      Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k := by
  have hb : ∃ C, ∀ k, |Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k| ≤ C := by
    refine ⟨Real.sqrt 2 * (μ Set.univ).toReal + Real.sqrt 2 * (ν Set.univ).toReal, fun k => ?_⟩
    refine (abs_sub _ _).trans (add_le_add (Torus.abs_measureRealCoeff_le μ k)
      (Torus.abs_measureRealCoeff_le ν k))
  have hmem := memℓp_of_bounded hm _ hb
  unfold fourierCoeff ofMeasureDiff
  rw [coord_ofSeq_of_mem _ hmem, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

/-- Version of `eval_ofMeasureDiff` for continuous test functions with absolutely summable
Fourier coefficients (helper). -/
theorem eval_ofMeasureDiff_of_summable (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (φ : Torus d → ℝ) (hc : Continuous φ)
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef φ k‖) :
    eval (ofMeasureDiff m μ ν) φ = pair μ φ - pair ν φ := by
  rw [Torus.pair_sub_eq_tsum μ ν hc hs]
  unfold eval
  exact tsum_congr fun k => by rw [fourierCoeff_ofMeasureDiff hm μ ν k]

/-- The pairing of an embedded signed measure with a smooth test function is the
integral: `(μ - ν)(φ) = ∫ φ d(μ - ν)` for mean-zero-corrected `φ` (FOUND-02). -/
theorem eval_ofMeasureDiff (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (φ : Torus d → ℝ)
    (hφ : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    eval (ofMeasureDiff m μ ν) φ = pair μ φ - pair ν φ := by
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n => hφ.of_le (by exact_mod_cast le_top)
  exact eval_ofMeasureDiff_of_summable hm μ ν φ
    (Torus.continuous_of_continuous_lift (hd 0).continuous)
    (Torus.summable_fcoef_of_contDiff hd)

/-- The embedding `E_{m} ↪ E_{m'}` for `m ≤ m'` is a contraction (identity on `F̂`). -/
def embed (m' : ℝ) (F : NegSobolev d m) : NegSobolev d m' := ofSeq m' (fourierCoeff F)

theorem norm_embed_le (m' : ℝ) (hmm' : m ≤ m') (F : NegSobolev d m) :
    ‖embed m' F‖ ≤ ‖F‖ := by
  have hcoord : ∀ k, |Lattice.jp k.1 ^ (-m') * fourierCoeff F k| ≤ |coord F k| := by
    intro k
    have hj := Torus.jp_pos k.1
    have : Lattice.jp k.1 ^ (-m') * fourierCoeff F k = Lattice.jp k.1 ^ (m - m') * coord F k := by
      unfold fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add hj]
      ring_nf
    rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
    have h1 : Lattice.jp k.1 ^ (m - m') ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by linarith)
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  obtain ⟨h3, h4⟩ := coord_sq F
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m') * fourierCoeff F k) 2 := by
    rw [Torus.memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h3
    calc _ = |Lattice.jp k.1 ^ (-m') * fourierCoeff F k| ^ 2 := (sq_abs _).symm
      _ ≤ |coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
      _ = _ := sq_abs _
  have hc : ∀ k, coord (embed m' F) k = Lattice.jp k.1 ^ (-m') * fourierCoeff F k :=
    fun k => coord_ofSeq_of_mem _ hmem k
  obtain ⟨h1, h2⟩ := coord_sq (embed m' F)
  have hsq : ‖embed m' F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [h2, h4]
    refine h1.tsum_le_tsum (fun k => ?_) h3
    rw [hc k]
    calc _ = |Lattice.jp k.1 ^ (-m') * fourierCoeff F k| ^ 2 := (sq_abs _).symm
      _ ≤ |coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
      _ = _ := sq_abs _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end NegSobolev

/-- The positive Sobolev norm `‖φ‖_{H^m} = (|φ̂(0)|² + ∑_{k≠0} ⟨k⟩^{2m} |φ̂(k)|²)^{1/2}`
of a real function (`⟨k⟩ = (1+4π²|k|²)^{1/2}`, source line 1976). -/
def sobolevNorm {d : ℕ} (m : ℝ) (φ : Torus d → ℝ) : ℝ :=
  Real.sqrt ((Torus.mean φ) ^ 2 +
    ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)

/-- Membership in `H^m(𝕋^d)`: square-integrable with finite weighted coefficient sum. -/
def MemSobolev {d : ℕ} (m : ℝ) (φ : Torus d → ℝ) : Prop :=
  MemLp φ 2 volume ∧
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2

/-- `H^m(𝕋^d) ↪ C^j(𝕋^d)` for `m > d/2 + j` (used at source line 1976 with `j = 2`;
FOUND-02). -/
theorem cbNorm_le_sobolevNorm {d : ℕ} (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j < m) :
    ∃ C : ℝ, ∀ φ : Torus d → ℝ, MemSobolev m φ → Torus.IsCk j φ →
      Torus.cbNorm j φ ≤ C * sobolevNorm m φ := by
  refine ⟨∑ i ∈ Finset.range (j + 1),
    (1 + Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - i))))), ?_⟩
  rintro φ ⟨hL2, hs⟩ hCk
  have hint : Integrable φ := hL2.integrable one_le_two
  unfold Torus.cbNorm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hmi : (d : ℝ) / 2 + i < m := by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  obtain ⟨hsum, hbound⟩ := Torus.sobolev_coeff_bound hmi hint hs
  have hd : ContDiff ℝ j (Torus.lift φ) := hCk
  have hT : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hS1 : |Torus.mean φ| ≤ sobolevNorm m φ :=
    (by unfold sobolevNorm; exact Real.abs_le_sqrt (by linarith))
  have hS2 : Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)
      ≤ sobolevNorm m φ := Real.sqrt_le_sqrt (by linarith [sq_nonneg (Torus.mean φ)])
  refine ciSup_le fun y => ?_
  calc ‖iteratedFDeriv ℝ i (Torus.lift φ) y‖
      ≤ ∑' k : Lattice d, Lattice.jp k ^ i * ‖Torus.fcoef φ k‖ :=
        Torus.norm_iteratedFDeriv_le_tsum hd hij hsum y
    _ ≤ _ := hbound
    _ ≤ sobolevNorm m φ + Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - i)))) *
          sobolevNorm m φ := add_le_add hS1 (mul_le_mul_of_nonneg_left hS2 (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Duality: `|∫ φ d(μ-ν)| ≤ ‖μ-ν‖_{H^{-m}} ‖φ‖_{H^m}` for zero-mass differences (FOUND-02). -/
theorem abs_pair_sub_le {d : ℕ} (m : ℝ) (hm : (d : ℝ) < 2 * m)
    (μ ν : Measure (Torus d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (φ : Torus d → ℝ) (hφ : MemSobolev m φ) (hc : Continuous φ) :
    |pair μ φ - pair ν φ| ≤ ‖NegSobolev.ofMeasureDiff m μ ν‖ * sobolevNorm m φ := by
  obtain ⟨hL2, hs⟩ := hφ
  have hint : Integrable φ := hL2.integrable one_le_two
  have hmi : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) < m := by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  obtain ⟨hsum, -⟩ := Torus.sobolev_coeff_bound hmi hint hs
  have hsum' : Summable fun k : Lattice d => ‖Torus.fcoef φ k‖ := by simpa using hsum
  rw [← NegSobolev.eval_ofMeasureDiff_of_summable hm μ ν φ hc hsum']
  refine (NegSobolev.abs_eval_le _ φ hs).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold sobolevNorm
  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (Torus.mean φ)])

/-! ### Path spaces -/

/-- `𝒳_{m,T} = C([0,T]; E_m)` with the sup norm `‖w‖ = sup_{0≤t≤T} ‖w^t‖_{H^{-m}}`
(source lines 521-528). Mathlib's `ContinuousMap` norm on a compact domain is exactly
this sup norm. -/
def PathSpace (d : ℕ) (m T : ℝ) : Type := C(Set.Icc (0 : ℝ) T, NegSobolev d m)

namespace PathSpace

variable {d : ℕ} {m T : ℝ}

instance : NormedAddCommGroup (PathSpace d m T) :=
  inferInstanceAs (NormedAddCommGroup C(Set.Icc (0 : ℝ) T, NegSobolev d m))

instance : NormedSpace ℝ (PathSpace d m T) :=
  inferInstanceAs (NormedSpace ℝ C(Set.Icc (0 : ℝ) T, NegSobolev d m))

instance : MeasurableSpace (PathSpace d m T) := borel _

instance : BorelSpace (PathSpace d m T) := ⟨rfl⟩

/-- Evaluation of a path at time `t ∈ [0,T]`. -/
def at' (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) : NegSobolev d m :=
  (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) t

/-- The shifted window `w^{a+·}` restricted to `[0,T]` of a path defined on all of `[0,∞)`
(source lines 526-528). -/
def window (a : ℝ) (w : ℝ → NegSobolev d m) (hw : Continuous w) : PathSpace d m T :=
  (⟨fun t => w (a + t), by fun_prop⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- Sup-norm characterisation `‖w‖_{𝒳_{m,T}} = sup_{t} ‖w^t‖` (FOUND-02). -/
theorem norm_eq_iSup (w : PathSpace d m T) (hT : 0 ≤ T) :
    ‖w‖ = ⨆ t : Set.Icc (0 : ℝ) T, ‖at' w t‖ := by
  exact ContinuousMap.norm_eq_iSup_norm w

end PathSpace

end HRS
