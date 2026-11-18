import HRS.MS.ThCorrSAux1
import HRS.Whole.Thermal

/-!
# TC-S, part 2: `H^J` Fourier norm versus classical derivatives (statement S2)

Namespace `HRS.MS.TcS`.  For `φ ∈ C^J(ℝ^d)` with `D^jφ ∈ L²` (`j ≤ J`; this is `HRS.Whole.MemHSmooth J φ`)
the classical coordinate derivatives are the distributional ones:
`fourierL2 (∂_k f) = 2πi ξ_k fourierL2 f` a.e. for `f ∈ L²` of class `C¹` with `∂_k f ∈ L²`
(`tcs_fourier_partial`, by duality against `C_c^∞` test functions and integration by parts).  Iterating,
`fourierL2 (D^nφ(e_{i_1}, …, e_{i_n})) = ∏ (2πi ξ_{i_t}) fourierL2 φ`, and Plancherel gives

* `tcs_sobolev_of_hsmooth` (S2): `MemHSmooth J φ → MemSobolev J φ ∧ sobolevNormSq J φ ≤ C (sobolevWNorm J 2 φ)²`
  with `C = 2^J (d+1)^J`;
* `tcs_sobolevNorm_le_hsmooth`: the same for the norm, `‖φ‖_{H^J} ≤ √C ∑_{j ≤ J} ‖D^jφ‖_{L²}`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.TcS
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MP.RdGen

variable {d : ℕ}

/-! ### Derivative of the Fourier transform of a `C_c^∞` function -/

theorem tcs_fderiv_fourier {h : Euc d → ℂ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (k : Fin d) (x : Euc d) :
    fderiv ℝ (𝓕 h) x (EuclideanSpace.single k (1 : ℝ)) =
      𝓕 (fun v : Euc d => (-(2 * Real.pi * Complex.I * ((v k : ℝ) : ℂ))) * h v) x := by
  have hint1 : Integrable h := hh.continuous.integrable_of_hasCompactSupport hc
  have hint2 : Integrable (fun v : Euc d => ‖v‖ * ‖h v‖) :=
    (continuous_norm.mul hh.continuous.norm).integrable_of_hasCompactSupport hc.norm.mul_left
  have hint3 : Integrable (fun v : Euc d => VectorFourier.fourierSMulRight (innerSL ℝ) h v) := by
    refine (hint2.const_mul (2 * Real.pi * ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖)).mono'
      hh.continuous.aestronglyMeasurable.fourierSMulRight (Eventually.of_forall fun v => ?_)
    have := VectorFourier.norm_fourierSMulRight_le (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) h v
    calc _ ≤ _ := this
      _ = _ := by ring
  rw [Real.fderiv_fourier hint1 hint2, Real.fourier_continuousLinearMap_apply hint3]
  have hfun : (fun v : Euc d => (VectorFourier.fourierSMulRight (innerSL ℝ) h v)
      (EuclideanSpace.single k (1 : ℝ))) =
      fun v : Euc d => (-(2 * Real.pi * Complex.I * ((v k : ℝ) : ℂ))) * h v := by
    funext v
    have e : ((innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) v) (EuclideanSpace.single k (1 : ℝ)) = v k := by
      rw [innerSL_apply_apply, EuclideanSpace.inner_single_right]; simp
    simp only [VectorFourier.fourierSMulRight_apply, e]
    simp [Complex.real_smul, smul_eq_mul]
    ring
  rw [hfun]


/-! ### The Fourier transform of a coordinate derivative -/

/-- the `C_c^∞` function `ξ ↦ 2πi ξ_k g(ξ)`, as a Schwartz function. -/
def tcs_mulSchwartz (k : Fin d) {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    SchwartzMap (Euc d) ℂ :=
  (show HasCompactSupport (fun ξ : Euc d => (2 * Real.pi * Complex.I * ((ξ k : ℝ) : ℂ)) *
      ((g ξ : ℝ) : ℂ)) from
    (hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_left).toSchwartzMap
    (by
      have h1 : ContDiff ℝ ∞ (fun ξ : Euc d => ((ξ k : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp
          ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff)
      exact (contDiff_const.mul h1).mul (Complex.ofRealCLM.contDiff.comp hg))

theorem tcs_mulSchwartz_apply (k : Fin d) {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (ξ : Euc d) :
    tcs_mulSchwartz k hg hc ξ = (2 * Real.pi * Complex.I * ((ξ k : ℝ) : ℂ)) * ((g ξ : ℝ) : ℂ) := rfl

theorem tcs_fourier_partial {f : Euc d → ℝ} (k : Fin d) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume)
    (hdf2 : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))) 2 volume) :
    fourierL2 (fun x => fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))) =ᵐ[volume]
      fun ξ => (2 * Real.pi * Complex.I * ((ξ k : ℝ) : ℂ)) * fourierL2 f ξ := by
  generalize he : EuclideanSpace.single k (1 : ℝ) = e at hdf2 ⊢
  set G : Euc d → ℂ := fourierL2 (fun x => fderiv ℝ f x e) with hG
  set H : Euc d → ℂ := fun ξ => (2 * Real.pi * Complex.I * ((ξ k : ℝ) : ℂ)) * fourierL2 f ξ
    with hH
  have hGl : LocallyIntegrable G volume := (memLp_fourierL2 hdf2).locallyIntegrable (by norm_num)
  have hFl : LocallyIntegrable (fourierL2 f) volume :=
    (memLp_fourierL2 hf2).locallyIntegrable (by norm_num)
  have hcoef : Continuous (fun ξ : Euc d => (2 * Real.pi * Complex.I * ((ξ k : ℝ) : ℂ))) := by
    have h1 : Continuous (fun ξ : Euc d => ((ξ k : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous
    exact continuous_const.mul h1
  have hHl : LocallyIntegrable H volume := by
    have := (locallyIntegrableOn_univ.2 hFl).continuousOn_mul hcoef.continuousOn
      isClosed_univ.isLocallyClosed
    exact locallyIntegrableOn_univ.1 this
  have hdiff : ∀ x, DifferentiableAt ℝ f x := fun x => hf.differentiable (by norm_num) x
  have hdf_ofReal : ∀ x, fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x e = ((fderiv ℝ f x e : ℝ) : ℂ) := by
    intro x
    have := (Complex.ofRealCLM.hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
    have h2 : fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x = Complex.ofRealCLM ∘L fderiv ℝ f x := this
    rw [h2]; rfl
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (G x - H x) = 0 := by
    intro g hg hsupp
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hsC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set s : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hgC with hsdef
    have hs : ⇑s = fun x => ((g x : ℝ) : ℂ) := rfl
    set s3 : SchwartzMap (Euc d) ℂ := tcs_mulSchwartz k hg hsupp with hs3
    have hs3a : ∀ ξ, s3 ξ = (2 * Real.pi * Complex.I * ((ξ k : ℝ) : ℂ)) * s ξ := fun ξ => rfl
    -- derivative of `𝓕 s`
    have hder : ∀ x, fderiv ℝ (𝓕 ⇑s) x e = -(𝓕 ⇑s3 x) := by
      intro x
      subst he
      rw [hs, tcs_fderiv_fourier hgC hsC k x]
      have : (fun v : Euc d => (-(2 * Real.pi * Complex.I * ((v k : ℝ) : ℂ))) * ((g v : ℝ) : ℂ)) =
          ⇑(-s3) := by
        funext v
        rw [SchwartzMap.neg_apply, hs3a, hs]; ring
      rw [this, ← SchwartzMap.fourier_coe]
      have hn : (𝓕 (-s3) : SchwartzMap (Euc d) ℂ) = -(𝓕 s3 : SchwartzMap (Euc d) ℂ) := by
        simpa using (map_neg (SchwartzMap.fourierTransformCLM ℂ) s3)
      rw [hn]
      rfl
    have hFs : ∀ x, 𝓕 ⇑s x = ((𝓕 s : SchwartzMap (Euc d) ℂ) x) := fun x => rfl
    have hFs3 : ∀ x, 𝓕 ⇑s3 x = ((𝓕 s3 : SchwartzMap (Euc d) ℂ) x) := fun x => rfl
    have hfC : MemLp (fun x => ((f x : ℝ) : ℂ)) 2 volume := hf2.ofReal (K := ℂ)
    have hdfC : MemLp (fun x => ((fderiv ℝ f x e : ℝ) : ℂ)) 2 volume := hdf2.ofReal (K := ℂ)
    have hFsL : MemLp (𝓕 ⇑s) 2 volume := (𝓕 s : SchwartzMap (Euc d) ℂ).memLp 2 volume
    have hFs3L : MemLp (𝓕 ⇑s3) 2 volume := (𝓕 s3 : SchwartzMap (Euc d) ℂ).memLp 2 volume
    -- integration by parts
    have hibp : ∫ x, 𝓕 ⇑s x * ((fderiv ℝ f x e : ℝ) : ℂ) =
        -∫ x, fderiv ℝ (𝓕 ⇑s) x e * ((f x : ℝ) : ℂ) := by
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
        (f := 𝓕 ⇑s) (g := fun x => ((f x : ℝ) : ℂ)) (v := e)
        ?_ ?_ ?_ ?_ ?_
      · simp only [hdf_ofReal] at this
        exact this
      · simp only [hder]
        exact (hFs3L.integrable_mul hfC).neg.congr (Eventually.of_forall fun x => by simp)
      · simp only [hdf_ofReal]
        exact hFsL.integrable_mul hdfC
      · exact hFsL.integrable_mul hfC
      · intro x _
        exact ((𝓕 s : SchwartzMap (Euc d) ℂ).differentiableAt (x := x))
      · intro x _
        exact Complex.ofRealCLM.differentiable.differentiableAt.comp x (hdiff x)
    have h1 : ∫ x, g x • G x = ∫ x, 𝓕 ⇑s x * ((fderiv ℝ f x e : ℝ) : ℂ) := by
      have := rg_fourierL2_dual hdf2 s
      refine Eq.trans ?_ this
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hs, Complex.real_smul, hG]
    have h2 : ∫ x, g x • H x = ∫ x, s3 x * fourierL2 f x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hH, hs3a, hs, Complex.real_smul]
      ring
    have h3 := rg_fourierL2_dual hf2 s3
    have h4 : ∫ x, fderiv ℝ (𝓕 ⇑s) x e * ((f x : ℝ) : ℂ) = -∫ x, 𝓕 s3 x * ((f x : ℝ) : ℂ) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [hder, hFs3 x]; ring
    have hint1 : Integrable (fun x => g x • G x) volume :=
      hGl.integrable_smul_left_of_hasCompactSupport hg.continuous hsupp
    have hint2 : Integrable (fun x => g x • H x) volume :=
      hHl.integrable_smul_left_of_hasCompactSupport hg.continuous hsupp
    have hsplit : ∫ x, g x • (G x - H x) = (∫ x, g x • G x) - ∫ x, g x • H x := by
      rw [← integral_sub hint1 hint2]
      simp only [smul_sub]
    rw [hsplit, h1, h2, hibp, h4, ← h3]
    simp
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hGl.sub hHl) key
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx


/-! ### Iterated coordinate derivatives -/

/-- `D^nφ(x)(e_{i_1}, …, e_{i_n})`. -/
def tcs_pd {n : ℕ} (i : Fin n → Fin d) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  iteratedFDeriv ℝ n φ x (fun t => EuclideanSpace.single (i t) (1 : ℝ))

theorem tcs_pd_zero (i : Fin 0 → Fin d) (φ : Euc d → ℝ) : tcs_pd i φ = φ := by
  funext x
  simp [tcs_pd, iteratedFDeriv_zero_apply]

theorem tcs_abs_pd_le {n : ℕ} (i : Fin n → Fin d) (φ : Euc d → ℝ) (x : Euc d) :
    |tcs_pd i φ x| ≤ ‖iteratedFDeriv ℝ n φ x‖ := by
  unfold tcs_pd
  have h := (iteratedFDeriv ℝ n φ x).le_opNorm (fun t => EuclideanSpace.single (i t) (1 : ℝ))
  have h1 : ∏ t : Fin n, ‖(EuclideanSpace.single (i t) (1 : ℝ) : Euc d)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  simpa using h

theorem tcs_pd_eq_comp {n : ℕ} (i : Fin n → Fin d) (φ : Euc d → ℝ) :
    tcs_pd i φ = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
      (fun t => EuclideanSpace.single (i t) (1 : ℝ))) ∘ iteratedFDeriv ℝ n φ := rfl

theorem tcs_contDiff_pd {n m : ℕ} (i : Fin n → Fin d) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ((m + n : ℕ) : ℕ∞) φ) :
    ContDiff ℝ m (tcs_pd i φ) := by
  rw [tcs_pd_eq_comp]
  refine (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ _).contDiff.comp ?_
  exact hφ.iteratedFDeriv_right (by norm_cast)

theorem tcs_fderiv_pd {n : ℕ} (i : Fin n → Fin d) (k : Fin d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) φ) (x : Euc d) :
    fderiv ℝ (tcs_pd i φ) x (EuclideanSpace.single k (1 : ℝ)) =
      tcs_pd (Fin.cons k i : Fin (n + 1) → Fin d) φ x := by
  have hdiff : Differentiable ℝ (fun y => iteratedFDeriv ℝ n φ y) :=
    hφ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  rw [tcs_pd_eq_comp]
  have h1 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
      (fun t => EuclideanSpace.single (i t) (1 : ℝ))).hasFDerivAt.comp x (hdiff x).hasFDerivAt
  rw [h1.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
  unfold tcs_pd
  rw [iteratedFDeriv_succ_apply_left]
  have e1 : ((Fin.cons k i : Fin (n + 1) → Fin d) 0) = k := rfl
  simp only [e1]
  congr 1

theorem tcs_memLp_pd {n : ℕ} (i : Fin n → Fin d) {φ : Euc d → ℝ} (hφ : ContDiff ℝ n φ)
    (hL : MemLp (fun x => iteratedFDeriv ℝ n φ x) 2 volume) : MemLp (tcs_pd i φ) 2 volume := by
  refine hL.of_le ?_ (Eventually.of_forall fun x => ?_)
  · have := tcs_contDiff_pd (m := 0) i (φ := φ) (by simpa using hφ)
    exact this.continuous.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact tcs_abs_pd_le i φ x

/-- derivative law for iterated coordinate derivatives -/
theorem tcs_fourier_pd {φ : Euc d → ℝ} {J : ℕ} (hφ : ContDiff ℝ J φ)
    (hL : ∀ j ≤ J, MemLp (fun x => iteratedFDeriv ℝ j φ x) 2 volume) :
    ∀ n ≤ J, ∀ i : Fin n → Fin d, fourierL2 (tcs_pd i φ) =ᵐ[volume]
      fun ξ => (∏ t, (2 * Real.pi * Complex.I * ((ξ (i t) : ℝ) : ℂ))) * fourierL2 φ ξ := by
  intro n
  induction n with
  | zero =>
    intro _ i
    rw [tcs_pd_zero]
    exact Eventually.of_forall fun ξ => by simp
  | succ n ih =>
    intro hn i
    have hnJ : n ≤ J := Nat.le_of_succ_le hn
    have hi : i = (Fin.cons (i 0) (Fin.tail i) : Fin (n + 1) → Fin d) := (Fin.cons_self_tail i).symm
    set i' : Fin n → Fin d := Fin.tail i with hi'
    set k : Fin d := i 0 with hk
    have hφ' : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) φ := by
      exact hφ.of_le (by exact_mod_cast hn)
    have hf1 : ContDiff ℝ 1 (tcs_pd i' φ) := by
      refine tcs_contDiff_pd (m := 1) i' ?_
      rw [Nat.add_comm]; exact hφ'
    have hf2 : MemLp (tcs_pd i' φ) 2 volume :=
      tcs_memLp_pd i' (hφ.of_le (by exact_mod_cast hnJ)) (hL n hnJ)
    have hdf : (fun x => fderiv ℝ (tcs_pd i' φ) x (EuclideanSpace.single k (1 : ℝ))) =
        tcs_pd (Fin.cons k i' : Fin (n + 1) → Fin d) φ :=
      funext fun x => tcs_fderiv_pd i' k hφ' x
    have hdf2 : MemLp (fun x => fderiv ℝ (tcs_pd i' φ) x (EuclideanSpace.single k (1 : ℝ))) 2
        volume := by
      rw [hdf]
      exact tcs_memLp_pd _ (hφ.of_le (by exact_mod_cast hn)) (hL (n + 1) hn)
    have hA := tcs_fourier_partial k hf1 hf2 hdf2
    rw [hdf] at hA
    have hB := ih hnJ i'
    rw [hi]
    filter_upwards [hA, hB] with ξ h1 h2
    rw [h1, h2, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring


/-! ### The main estimate (S2) -/

theorem tcs_norm_prod_coord {n : ℕ} (i : Fin n → Fin d) (ξ : Euc d) :
    ‖∏ t, (2 * Real.pi * Complex.I * ((ξ (i t) : ℝ) : ℂ))‖ = (2 * Real.pi) ^ n * ∏ t, |ξ (i t)| := by
  rw [norm_prod]
  have : ∀ t, ‖(2 * Real.pi * Complex.I * ((ξ (i t) : ℝ) : ℂ))‖ = (2 * Real.pi) * |ξ (i t)| := by
    intro t
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    simp [abs_of_pos Real.pi_pos]
  simp_rw [this]
  rw [Finset.prod_mul_distrib]
  simp

theorem tcs_sum_norm_sq_pd {φ : Euc d → ℝ} {J : ℕ} (hφ : ContDiff ℝ J φ)
    (hL : ∀ j ≤ J, MemLp (fun x => iteratedFDeriv ℝ j φ x) 2 volume) :
    ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ n ∈ Finset.range (J + 1),
      ∑ i : Fin n → Fin d, ‖fourierL2 (tcs_pd i φ) ξ‖ ^ 2 =
        (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n * ‖fourierL2 φ ξ‖ ^ 2 := by
  refine ae_all_iff.2 fun n => ?_
  by_cases hn : n ∈ Finset.range (J + 1)
  swap
  · exact Eventually.of_forall fun ξ h => absurd h hn
  have hn' : n ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ i : Fin n → Fin d,
      fourierL2 (tcs_pd i φ) ξ =
        (∏ t, (2 * Real.pi * Complex.I * ((ξ (i t) : ℝ) : ℂ))) * fourierL2 φ ξ :=
    ae_all_iff.2 fun i => tcs_fourier_pd hφ hL n hn' i
  filter_upwards [hall] with ξ hξ _
  calc ∑ i : Fin n → Fin d, ‖fourierL2 (tcs_pd i φ) ξ‖ ^ 2
      = ∑ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 φ ξ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hξ i, norm_mul, tcs_norm_prod_coord, mul_pow]
    _ = (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n * ‖fourierL2 φ ξ‖ ^ 2 := by
        rw [← Finset.sum_mul, HRS.MS.QMul.qm_sum_sq]

theorem tcs_sobolev_of_hsmooth (d J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, HRS.Whole.MemHSmooth J φ →
      HRS.PDE.ToolboxRd.MemSobolev (J : ℝ) φ ∧
        sobolevNormSq (J : ℝ) φ ≤ C * (HRS.Whole.sobolevWNorm J 2 φ) ^ 2 := by
  refine ⟨2 ^ J * ((d : ℝ) + 1) ^ J, by positivity, fun φ hφ => ?_⟩
  obtain ⟨hcd, hL⟩ := hφ
  have hM : ∀ n ≤ J, ∀ i : Fin n → Fin d, MemLp (tcs_pd i φ) 2 volume := fun n hn i =>
    tcs_memLp_pd i (hcd.of_le (by exact_mod_cast hn)) (hL n hn)
  have hφ2 : MemLp φ 2 volume := by
    have := hM 0 (Nat.zero_le _) (fun t => t.elim0)
    rwa [tcs_pd_zero] at this
  have hae := tcs_sum_norm_sq_pd hcd hL
  set Φ : Euc d → ℝ := fun ξ => 2 ^ J * ∑ n ∈ Finset.range (J + 1),
    ∑ i : Fin n → Fin d, ‖fourierL2 (tcs_pd i φ) ξ‖ ^ 2 with hΦ
  have hΦint : Integrable Φ volume := by
    refine Integrable.const_mul (integrable_finset_sum _ fun n hn => integrable_finset_sum _
      fun i _ => ?_) _
    exact integrable_norm_sq_fourierL2 (hM n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) i)
  have hbound : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      wt ξ ^ (J : ℝ) * ‖fourierL2 φ ξ‖ ^ 2 ≤ Φ ξ := by
    filter_upwards [hae] with ξ hξ
    have h1 := HRS.MS.QMul.qm_wt_pow_le J ξ
    rw [Real.rpow_natCast]
    have h2 : Φ ξ = 2 ^ J * ((∑ n ∈ Finset.range (J + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n) *
        ‖fourierL2 φ ξ‖ ^ 2) := by
      simp only [hΦ]
      rw [Finset.sum_congr rfl hξ, Finset.sum_mul]
    rw [h2]
    calc wt ξ ^ J * ‖fourierL2 φ ξ‖ ^ 2
        ≤ (2 ^ J * ∑ n ∈ Finset.range (J + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n) *
          ‖fourierL2 φ ξ‖ ^ 2 := by gcongr
      _ = _ := by ring
  have hmem : Integrable (fun ξ : Euc d => wt ξ ^ (J : ℝ) * ‖fourierL2 φ ξ‖ ^ 2) volume := by
    refine hΦint.mono' (aesm_wt_mul (aestronglyMeasurable_fourierL2 hφ2) _) ?_
    filter_upwards [hbound] with ξ hξ
    have : 0 ≤ wt ξ ^ (J : ℝ) * ‖fourierL2 φ ξ‖ ^ 2 := by
      have := wt_pos (d := d) ξ
      positivity
    rwa [Real.norm_of_nonneg this]
  refine ⟨⟨hφ2, hmem⟩, ?_⟩
  rw [sobolevNormSq_eq]
  have step1 : ∫ ξ, wt ξ ^ (J : ℝ) * ‖fourierL2 φ ξ‖ ^ 2 ≤ ∫ ξ, Φ ξ :=
    integral_mono_ae hmem hΦint hbound
  -- the integral of `Φ`
  set X : ℕ → ℝ := fun n => ∫ x, ‖iteratedFDeriv ℝ n φ x‖ ^ 2 with hX
  have step2 : ∫ ξ, Φ ξ ≤ 2 ^ J * ∑ n ∈ Finset.range (J + 1), ((d : ℝ) + 1) ^ J * X n := by
    simp only [hΦ]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [integral_finset_sum _ fun n hn => integrable_finset_sum _ fun i _ =>
      integrable_norm_sq_fourierL2 (hM n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) i)]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [integral_finset_sum _ fun i _ => integrable_norm_sq_fourierL2 (hM n hn' i)]
    have hi : ∀ i : Fin n → Fin d, ∫ ξ, ‖fourierL2 (tcs_pd i φ) ξ‖ ^ 2 ≤ X n := by
      intro i
      rw [integral_norm_sq_fourierL2 (hM n hn' i)]
      refine integral_mono (hM n hn' i).integrable_sq ((hL n hn').norm.integrable_sq) fun x => ?_
      have h1 := tcs_abs_pd_le i φ x
      have h2 : |tcs_pd i φ x| ^ 2 ≤ ‖iteratedFDeriv ℝ n φ x‖ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      simpa [sq_abs] using h2
    calc ∑ i : Fin n → Fin d, ∫ ξ, ‖fourierL2 (tcs_pd i φ) ξ‖ ^ 2
        ≤ ∑ _i : Fin n → Fin d, X n := Finset.sum_le_sum fun i _ => hi i
      _ = (d : ℝ) ^ n * X n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ ((d : ℝ) + 1) ^ J * X n := by
          have hXn : 0 ≤ X n := integral_nonneg fun x => by positivity
          refine mul_le_mul_of_nonneg_right ?_ hXn
          calc (d : ℝ) ^ n ≤ ((d : ℝ) + 1) ^ n :=
                pow_le_pow_left₀ (by positivity) (by linarith) n
            _ ≤ ((d : ℝ) + 1) ^ J :=
                pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := by positivity
                                      linarith) hn'
  -- the `W^{J,2}` norm
  set tn : ℕ → ℝ := fun n => (∫ x, ‖iteratedFDeriv ℝ n φ x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) with htn
  have hXn0 : ∀ n, 0 ≤ X n := fun n => integral_nonneg fun x => by positivity
  have htn0 : ∀ n, 0 ≤ tn n := fun n => by
    refine Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  have htn2 : ∀ n, tn n ^ 2 = X n := by
    intro n
    have e : (∫ x, ‖iteratedFDeriv ℝ n φ x‖ ^ (2 : ℝ)) = X n := by
      simp only [hX]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Real.rpow_two]
    simp only [htn]
    rw [e, ← Real.rpow_natCast, ← Real.rpow_mul (hXn0 n)]
    norm_num
  have hW : HRS.Whole.sobolevWNorm J 2 φ = ∑ n ∈ Finset.range (J + 1), tn n := rfl
  calc ∫ ξ, wt ξ ^ (J : ℝ) * ‖fourierL2 φ ξ‖ ^ 2
      ≤ 2 ^ J * ∑ n ∈ Finset.range (J + 1), ((d : ℝ) + 1) ^ J * X n := step1.trans step2
    _ = 2 ^ J * ((d : ℝ) + 1) ^ J * ∑ n ∈ Finset.range (J + 1), tn n ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]
        simp only [htn2]
    _ ≤ 2 ^ J * ((d : ℝ) + 1) ^ J * (∑ n ∈ Finset.range (J + 1), tn n) ^ 2 := by
        gcongr
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun n _ => htn0 n
    _ = _ := by rw [hW]

/-- the norm form of `tcs_sobolev_of_hsmooth` -/
theorem tcs_sobolevNorm_le_hsmooth (d J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, HRS.Whole.MemHSmooth J φ →
      HRS.Whole.sobolevNorm (J : ℝ) φ ≤ C * HRS.Whole.sobolevWNorm J 2 φ := by
  obtain ⟨C, hC, h⟩ := tcs_sobolev_of_hsmooth d J
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun φ hφ => ?_⟩
  have h1 := (h φ hφ).2
  unfold HRS.Whole.sobolevNorm
  have hW : 0 ≤ HRS.Whole.sobolevWNorm J 2 φ := by
    unfold HRS.Whole.sobolevWNorm
    exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  calc Real.sqrt (sobolevNormSq (J : ℝ) φ)
      ≤ Real.sqrt (C * HRS.Whole.sobolevWNorm J 2 φ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt C * HRS.Whole.sobolevWNorm J 2 φ := by
        rw [Real.sqrt_mul hC, Real.sqrt_sq hW]

end HRS.MS.TcS
