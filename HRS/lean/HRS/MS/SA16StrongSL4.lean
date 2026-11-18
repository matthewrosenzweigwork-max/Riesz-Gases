import HRS.MS.SA16StrongDefs

/-!
# S.A.16 SL4: `wmp_zero_injective`

An element of the closed-jet space `WmpSpace` is determined by its zeroth component.  The proof passes
the integration by parts identity `∫ ∂^α φ ψ = ± ∫ φ ∂^{α'} ψ` of compact smooth jets to the
`L^p` closure (Hölder pairing against compactly supported smooth tests), and applies the fundamental
lemma of the calculus of variations.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

/-! ### calculus: integration by parts for the iterated partial derivatives -/

lemma sa16s_cc_fderiv {d : ℕ} {f : Euc d → ℝ} (hf : IsCcInfty f) (v : Euc d) :
    IsCcInfty (fun x => fderiv ℝ f x v) :=
  ⟨(hf.1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, hf.2.fderiv_apply ℝ v⟩

lemma sa16s_cc_partialDeriv {d : ℕ} {f : Euc d → ℝ} (hf : IsCcInfty f) {j : ℕ}
    (idx : Fin j → Fin d) : IsCcInfty (partialDeriv idx f) := by
  have e : partialDeriv idx f = fun x => iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (idx l) 1) :=
    rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (iteratedFDeriv ℝ j f) :=
      hf.1.iteratedFDeriv_right (m := ∞) (by exact_mod_cast le_top)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (idx l) 1)).contDiff.comp h1
  · have h2 := hf.2.iteratedFDeriv (𝕜 := ℝ) j
    exact h2.comp_left (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ =>
      A (fun l => EuclideanSpace.single (idx l) 1)) (by simp)

lemma sa16s_integrable_of_cc {d : ℕ} {f : Euc d → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable f := hf.integrable_of_hasCompactSupport hs

/-- integration by parts in one direction -/
lemma sa16s_ibp1 {d : ℕ} {f g : Euc d → ℝ} (hf : IsCcInfty f) (hg : IsCcInfty g) (v : Euc d) :
    ∫ x, fderiv ℝ f x v * g x = -∫ x, f x * fderiv ℝ g x v := by
  have hdf := sa16s_cc_fderiv hf v
  have hdg := sa16s_cc_fderiv hg v
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have h1 : Integrable (fun x => fderiv ℝ f x v * g x) :=
    (hdf.1.continuous.mul hgc).integrable_of_hasCompactSupport (hdf.2.mul_right)
  have h2 : Integrable (fun x => f x * fderiv ℝ g x v) :=
    (hfc.mul hdg.1.continuous).integrable_of_hasCompactSupport (hf.2.mul_right)
  have h3 : Integrable (fun x => f x * g x) :=
    (hfc.mul hgc).integrable_of_hasCompactSupport (hf.2.mul_right)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v) h1 h2 h3
    (fun x _ => (hf.1.differentiable (by simp)) x) (fun x _ => (hg.1.differentiable (by simp)) x)
  linarith

/-- the left-hand recursion for `partialDeriv` -/
lemma sa16s_pd_cons {d : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (i : Fin d)
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv (Fin.cons i idx : Fin (j + 1) → Fin d) f x =
      fderiv ℝ (partialDeriv idx f) x (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    ((hf.iteratedFDeriv_right (m := ∞) (i := j) (by exact_mod_cast le_top)).differentiable
      (by simp)) x
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have hL : HasFDerivAt (fun y => iteratedFDeriv ℝ j f y (fun l => EuclideanSpace.single (idx l) 1))
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l => EuclideanSpace.single (idx l) 1)).comp (fderiv ℝ (iteratedFDeriv ℝ j f) x)) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (idx l) 1)).hasFDerivAt.comp x hd.hasFDerivAt
  rw [hL.fderiv]
  have htail : (Fin.tail fun l : Fin (j + 1) => (EuclideanSpace.single
      ((Fin.cons i idx : Fin (j + 1) → Fin d) l) (1 : ℝ) : Euc d)) =
      fun l => EuclideanSpace.single (idx l) 1 := by
    funext l
    simp [Fin.tail]
  simp [htail]

/-- the right-hand recursion for `partialDeriv` -/
lemma sa16s_pd_snoc {d : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (i : Fin d)
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) f x =
      partialDeriv idx (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x := by
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_right]
  have hcd : ContDiffAt ℝ j (fun y => fderiv ℝ f y) x :=
    ((hf.fderiv_right (m := ∞) le_rfl).of_le (by exact_mod_cast le_top)).contDiffAt
  have h := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).iteratedFDeriv_comp_left
    (f := fun y => fderiv ℝ f y) hcd (i := j) le_rfl
  have h' := congrArg (fun A => A (fun l => EuclideanSpace.single (idx l) 1)) h
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp] at h'
  have hinit : Fin.init (fun l : Fin (j + 1) => (EuclideanSpace.single
      ((Fin.snoc idx i : Fin (j + 1) → Fin d) l) (1 : ℝ) : Euc d)) =
      fun l => EuclideanSpace.single (idx l) 1 := by
    funext l
    simp [Fin.init, Fin.snoc_castSucc]
  have hlast : (EuclideanSpace.single ((Fin.snoc idx i : Fin (j + 1) → Fin d) (Fin.last j))
      (1 : ℝ) : Euc d) = EuclideanSpace.single i 1 := by simp
  rw [hinit, hlast]
  exact h'.symm


/-- integration by parts for an iterated partial derivative of compactly supported smooth functions -/
lemma sa16s_ibp_tuple {d : ℕ} : ∀ (j : ℕ) (idx : Fin j → Fin d), ∃ idx' : Fin j → Fin d,
    ∀ φ ψ : Euc d → ℝ, IsCcInfty φ → IsCcInfty ψ →
      ∫ x, partialDeriv idx φ x * ψ x = (-1) ^ j * ∫ x, φ x * partialDeriv idx' ψ x := by
  intro j
  induction j with
  | zero =>
    intro idx
    refine ⟨idx, fun φ ψ hφ hψ => ?_⟩
    simp [partialDeriv]
  | succ j ih =>
    intro idx
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons i idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    obtain ⟨idx'', h''⟩ := ih idx'
    refine ⟨Fin.snoc idx'' i, fun φ ψ hφ hψ => ?_⟩
    have e1 : ∀ x, partialDeriv (Fin.cons i idx' : Fin (j + 1) → Fin d) φ x =
        fderiv ℝ (partialDeriv idx' φ) x (EuclideanSpace.single i 1) :=
      fun x => sa16s_pd_cons hφ.1 i idx' x
    have e2 : ∀ x, partialDeriv (Fin.snoc idx'' i : Fin (j + 1) → Fin d) ψ x =
        partialDeriv idx'' (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) x :=
      fun x => sa16s_pd_snoc hψ.1 i idx'' x
    simp_rw [e1, e2]
    rw [sa16s_ibp1 (sa16s_cc_partialDeriv hφ idx') hψ]
    rw [h'' φ _ hφ (sa16s_cc_fderiv hψ _)]
    ring


/-! ### the pairing functionals on `L^p` -/

section Pairing

variable (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)]

instance sa16s_fact_conj : Fact (1 ≤ ENNReal.conjExponent (ENNReal.ofReal p)) :=
  ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent (ENNReal.ofReal p)) (ENNReal.ofReal p)⟩

/-- `G ↦ ∫ G(x)(τ) ψ(x) dx`, a continuous linear functional on `L^p` (Hölder pairing) -/
def sa16s_pair (τ : WIndex d m) {ψ : Euc d → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    WLp d m p →L[ℝ] ℝ :=
  ((((ContinuousLinearMap.mul ℝ ℝ).comp
      (ContinuousLinearMap.proj τ : (WIndex d m → ℝ) →L[ℝ] ℝ)).lpPairing
      (volume : Measure (Euc d)) (ENNReal.ofReal p)
      (ENNReal.conjExponent (ENNReal.ofReal p))).flip
    ((hψc.memLp_of_hasCompactSupport (p := ENNReal.conjExponent (ENNReal.ofReal p))
      (μ := (volume : Measure (Euc d))) hψs).toLp ψ))

lemma sa16s_pair_apply (τ : WIndex d m) {ψ : Euc d → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (G : WLp d m p) :
    sa16s_pair d m p τ hψc hψs G =
      ∫ x, ((G : Euc d → (WIndex d m → ℝ)) x τ) * ψ x := by
  unfold sa16s_pair
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hψc.memLp_of_hasCompactSupport
    (p := ENNReal.conjExponent (ENNReal.ofReal p)) (μ := (volume : Measure (Euc d))) hψs)] with x hx
  simp [hx]

end Pairing


/-- the weak-derivative identity survives in the closure `WmpSpace` -/
lemma sa16s_wmp_ibp (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (τ : WIndex d m) :
    ∃ idx' : Fin (τ.1 : ℕ) → Fin d, ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ G ∈ WmpSpace d m p,
      ∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x =
        (-1) ^ (τ.1 : ℕ) * ∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) *
          partialDeriv idx' ψ x := by
  obtain ⟨idx', hidx'⟩ := sa16s_ibp_tuple (τ.1 : ℕ) τ.2
  refine ⟨idx', fun ψ hψ G hG => ?_⟩
  have hψ' : IsCcInfty (partialDeriv idx' ψ) := sa16s_cc_partialDeriv hψ idx'
  set Lf : WLp d m p →L[ℝ] ℝ :=
    sa16s_pair d m p τ hψ.1.continuous hψ.2 -
      ((-1 : ℝ) ^ (τ.1 : ℕ)) • sa16s_pair d m p (wZero d m) hψ'.1.continuous hψ'.2 with hLf
  have hLfapp : ∀ F : WLp d m p, Lf F =
      (∫ x, ((F : Euc d → (WIndex d m → ℝ)) x τ) * ψ x) -
        (-1) ^ (τ.1 : ℕ) * ∫ x, ((F : Euc d → (WIndex d m → ℝ)) x (wZero d m)) *
          partialDeriv idx' ψ x := by
    intro F
    simp only [hLf, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      sa16s_pair_apply]
  have hspan : Submodule.span ℝ {F : WLp d m p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
      (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ} ≤ LinearMap.ker (Lf : WLp d m p →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    rintro F ⟨φ, hφ, hF⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show Lf F = 0
    rw [hLfapp]
    have e1 : ∫ x, ((F : Euc d → (WIndex d m → ℝ)) x τ) * ψ x =
        ∫ x, partialDeriv τ.2 φ x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hx
      rw [hx]
      rfl
    have e2 : ∫ x, ((F : Euc d → (WIndex d m → ℝ)) x (wZero d m)) * partialDeriv idx' ψ x =
        ∫ x, φ x * partialDeriv idx' ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hx
      have hz0 : wJet m φ x (wZero d m) = φ x := by
        simp only [wJet, wZero, partialDeriv]
        exact iteratedFDeriv_zero_apply _
      rw [hx, hz0]
    rw [e1, e2, hidx' φ ψ hφ hψ]
    ring
  have hclosed : IsClosed ((LinearMap.ker (Lf : WLp d m p →ₗ[ℝ] ℝ) : Submodule ℝ (WLp d m p)) :
      Set (WLp d m p)) := by
    have : ((LinearMap.ker (Lf : WLp d m p →ₗ[ℝ] ℝ) : Submodule ℝ (WLp d m p)) :
        Set (WLp d m p)) = Lf ⁻¹' {0} := by
      ext F; simp
    rw [this]
    exact isClosed_singleton.preimage Lf.continuous
  have hG' : G ∈ LinearMap.ker (Lf : WLp d m p →ₗ[ℝ] ℝ) :=
    Submodule.topologicalClosure_minimal _ hspan hclosed hG
  have hz : Lf G = 0 := hG'
  rw [hLfapp] at hz
  linarith

theorem wmp_zero_injective (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (G H : WmpSpace d m p)
    (h : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) =
      ((H : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m)) : G=H := by
  set D : WLp d m p := (G : WLp d m p) - (H : WLp d m p) with hDdef
  have hD : D ∈ WmpSpace d m p := (WmpSpace d m p).sub_mem G.2 H.2
  have hD0 : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = 0 := by
    filter_upwards [Lp.coeFn_sub (G : WLp d m p) (H : WLp d m p), h] with x hx hxh
    rw [hDdef, hx]
    simp [hxh]
  have hDτ : ∀ τ : WIndex d m, ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ = 0 := by
    intro τ
    obtain ⟨idx', hidx'⟩ := sa16s_wmp_ibp d m p τ
    have hP : MemLp (fun x => ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ)
        (ENNReal.ofReal p) (volume : Measure (Euc d)) :=
      by
        have hD' := Lp.memLp D
        exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) τ).comp_memLp' hD'
    have hloc : LocallyIntegrable (fun x => ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ)
        (volume : Measure (Euc d)) :=
      hP.locallyIntegrable (by
        have : (1 : ℝ) ≤ p := by linarith [Fact.out (p := 2 ≤ p)]
        simpa using ENNReal.ofReal_le_ofReal this)
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψs => ?_
    have := hidx' ψ ⟨hψ, hψs⟩ D hD
    have e0 : ∫ x, ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) *
        partialDeriv idx' ψ x = 0 := by
      have h0 : (fun x => ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) *
          partialDeriv idx' ψ x) =ᵐ[volume] fun _ => (0 : ℝ) := by
        filter_upwards [hD0] with x hx
        simp [hx]
      rw [integral_congr_ae h0]
      simp
    rw [e0, mul_zero] at this
    simpa [mul_comm] using this
  have hall : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ τ : WIndex d m,
      ((D : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ = 0 := by
    rw [ae_all_iff]
    exact hDτ
  have hDz : D = 0 := by
    refine Lp.ext ?_
    filter_upwards [hall, Lp.coeFn_zero (WIndex d m → ℝ) (ENNReal.ofReal p) (volume : Measure (Euc d))]
      with x hx hx0
    rw [hx0]
    funext τ
    exact hx τ
  exact Subtype.ext (sub_eq_zero.1 hDz)

end HRS.Whole.AppendixA.Phase2SA16
