import HRS.MP.SelfSimP5Init

/-!
# MPP5D (10a): transport from chamber coordinates to configuration space

Namespace `HRS.MP.SelfSimP5Impl`, helpers `ss5l_`.  Part of the proof of `HRS.MP.SelfSimP5.ss5_limit`
(`ss5_limit_proof` is in `HRS/MP/SelfSimP5LimC.lean`).

* `ss5l_equiv σ`: `ss5_toCh σ` as a measurable equivalence `EucConfig 1 N ≃ᵐ Ch5 N`, with the continuous linear maps
  `ss5l_toChL`, `ss5l_unrankL`.
* Fisher information: the integrand `ss5l_fiC` of `fisherInfoW (selfSimWeight 1 0 θ N 0)` for a configuration test field
  `ζ` equals the integrand `ss5l_fiU` of `ss5_fish θ U_ε` for the chamber field `χ · (toCh ∘ ζ ∘ unrank)` at every
  point of the closed chamber, once `χ` is a cut-off equal to `1` near the chamber image of the support of `ζ` and
  `ε` is below the minimal gap there (`ss5l_integrand_eq`, `ss5l_choose`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.MP.SelfSimP5 HRS.MP.SelfSim HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff
open Metric

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-- Inverse of the chamber coordinates `ss5_toCh σ`. -/
def ss5l_unrank {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : Ch5 N) : EucConfig 1 N :=
  fun i => WithLp.toLp 2 (fun _ : Fin 1 => z (σ.symm i))

theorem ss5l_toCh_unrank {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : Ch5 N) :
    ss5_toCh σ (ss5l_unrank σ z) = z := by
  ext k
  simp [ss5_toCh, ss5l_unrank]

theorem ss5l_unrank_toCh {N : ℕ} (σ : Equiv.Perm (Fin N)) (ξ : EucConfig 1 N) :
    ss5l_unrank σ (ss5_toCh σ ξ) = ξ := by
  funext i
  ext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  simp [ss5_toCh, ss5l_unrank]

/-- `ss5_toCh σ` as a continuous linear map. -/
def ss5l_toChL {N : ℕ} (σ : Equiv.Perm (Fin N)) : EucConfig 1 N →L[ℝ] Ch5 N :=
  LinearMap.toContinuousLinearMap
    { toFun := ss5_toCh σ
      map_add' := fun x y => by ext k; simp [ss5_toCh]
      map_smul' := fun c x => by ext k; simp [ss5_toCh] }

/-- `ss5l_unrank σ` as a continuous linear map. -/
def ss5l_unrankL {N : ℕ} (σ : Equiv.Perm (Fin N)) : Ch5 N →L[ℝ] EucConfig 1 N :=
  LinearMap.toContinuousLinearMap
    { toFun := ss5l_unrank σ
      map_add' := fun x y => by funext i; ext j; simp [ss5l_unrank]
      map_smul' := fun c x => by funext i; ext j; simp [ss5l_unrank] }

theorem ss5l_toChL_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (ξ : EucConfig 1 N) :
    ss5l_toChL σ ξ = ss5_toCh σ ξ := rfl

theorem ss5l_unrankL_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : Ch5 N) :
    ss5l_unrankL σ z = ss5l_unrank σ z := rfl

theorem ss5l_unrank_continuous {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (ss5l_unrank σ) := (ss5l_unrankL σ).continuous

/-- The chamber map as a measurable equivalence. -/
def ss5l_equiv {N : ℕ} (σ : Equiv.Perm (Fin N)) : EucConfig 1 N ≃ᵐ Ch5 N where
  toFun := ss5_toCh σ
  invFun := ss5l_unrank σ
  left_inv := ss5l_unrank_toCh σ
  right_inv := ss5l_toCh_unrank σ
  measurable_toFun := (ss5h_toCh_continuous σ).measurable
  measurable_invFun := (ss5l_unrank_continuous σ).measurable

theorem ss5l_equiv_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (ξ : EucConfig 1 N) :
    ss5l_equiv σ ξ = ss5_toCh σ ξ := rfl

theorem ss5l_unrank_single {N : ℕ} (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    ss5l_unrank σ (EuclideanSpace.single k 1) = configBasis 1 N (σ k, 0) := by
  funext i
  ext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  by_cases h : i = σ k
  · subst h; simp [ss5l_unrank, configBasis]
  · have h' : σ.symm i ≠ k := fun h2 => h (by rw [← h2]; simp)
    simp [ss5l_unrank, configBasis, h, h']

theorem ss5l_div_transport {N : ℕ} (σ : Equiv.Perm (Fin N)) {ζ : EucConfig 1 N → EucConfig 1 N}
    (hζ : Differentiable ℝ ζ) (z : Ch5 N) :
    ss5_div (fun w => ss5_toCh σ (ζ (ss5l_unrank σ w))) z = configDivW ζ (ss5l_unrank σ z) := by
  unfold ss5_div configDivW
  have hterm : ∀ k : Fin N, fderiv ℝ (fun w : Ch5 N => (ss5_toCh σ (ζ (ss5l_unrank σ w))) k) z
        (EuclideanSpace.single k 1) =
      fderiv ℝ (fun Z : EucConfig 1 N => ζ Z (σ k) 0) (ss5l_unrank σ z) (configBasis 1 N (σ k, 0)) := by
    intro k
    have hd : DifferentiableAt ℝ (fun Z : EucConfig 1 N => ζ Z (σ k) 0) (ss5l_unrank σ z) := by
      have h1 := differentiableAt_pi.1 (hζ (ss5l_unrank σ z)) (σ k)
      exact (differentiableAt_euclidean.1 h1) 0
    have hc : (fun w : Ch5 N => (ss5_toCh σ (ζ (ss5l_unrank σ w))) k) =
        (fun Z : EucConfig 1 N => ζ Z (σ k) 0) ∘ (ss5l_unrankL σ) := by
      funext w; simp [ss5_toCh, ss5l_unrankL_apply]
    rw [hc, fderiv_comp z (by simpa [ss5l_unrankL_apply] using hd) (ss5l_unrankL σ).differentiableAt]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.fderiv]
    rw [show (ss5l_unrankL σ) (EuclideanSpace.single k 1) = configBasis 1 N (σ k, 0) from
      ss5l_unrank_single σ k]
    rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  exact Equiv.sum_comp σ (fun i => fderiv ℝ (fun Z : EucConfig 1 N => ζ Z i 0) (ss5l_unrank σ z)
    (configBasis 1 N (i, 0)))


theorem ss5l_inner_gradient {N : ℕ} (U : Ch5 N → ℝ) (z w : Ch5 N) :
    inner ℝ (gradient U z) w = fderiv ℝ U z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem ss5l_norm_transport {N : ℕ} (σ : Equiv.Perm (Fin N)) (ξ : EucConfig 1 N) :
    ‖ss5_toCh σ ξ‖ ^ 2 = ∑ i, ‖ξ i‖ ^ 2 := ss5h_toCh_norm_sq σ ξ

theorem ss5l_PhiTr_eq {N : ℕ} {ε : ℝ} {z : Ch5 N} (hz : ∀ k l : Fin N, k < l → ε ≤ z l - z k) :
    ss5_PhiTr N ε z = ss5_Phi N z := by
  unfold ss5_PhiTr ss5_Phi
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    unfold ss5_phiTr
    rw [if_pos (hz k l hkl)]
  · simp [hkl]

theorem ss5l_dlogG {N : ℕ} (σ : Equiv.Perm (Fin N)) (θ : ℝ) {ε : ℝ} (hε : 0 < ε) {ξ : EucConfig 1 N}
    (hgap : ∀ k l : Fin N, k < l → ε < ss5_toCh σ ξ l - ss5_toCh σ ξ k) (v : EucConfig 1 N) :
    fderiv ℝ (fun Z : EucConfig 1 N => Real.log (selfSimWeight 1 0 θ N 0 Z)) ξ v =
      -θ⁻¹ * fderiv ℝ (ss5_U N ε) (ss5_toCh σ ξ) (ss5_toCh σ v) := by
  have hev : ∀ᶠ Z in 𝓝 ξ, ∀ k l : Fin N, k < l → ε < ss5_toCh σ Z l - ss5_toCh σ Z k := by
    refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ?_
    by_cases hkl : k < l
    · have hc : Continuous fun Z : EucConfig 1 N => ss5_toCh σ Z l - ss5_toCh σ Z k :=
        ((EuclideanSpace.proj l : Ch5 N →L[ℝ] ℝ).continuous.comp (ss5h_toCh_continuous σ)).sub
          ((EuclideanSpace.proj k : Ch5 N →L[ℝ] ℝ).continuous.comp (ss5h_toCh_continuous σ))
      have := hc.continuousAt.eventually (lt_mem_nhds (hgap k l hkl))
      filter_upwards [this] with Z hZ _ using hZ
    · exact Filter.Eventually.of_forall fun _ h => absurd h hkl
  have hceq : (fun Z : EucConfig 1 N => Real.log (selfSimWeight 1 0 θ N 0 Z)) =ᶠ[𝓝 ξ]
      fun Z => -θ⁻¹ * ss5_U N ε (ss5l_toChL σ Z) := by
    filter_upwards [hev] with Z hZ
    have hcone : Z ∈ ss5_cone σ := fun k l hkl => by
      have := hZ k l hkl
      have h2 : ss5_toCh σ Z l - ss5_toCh σ Z k > 0 := lt_trans hε this
      exact sub_pos.1 h2
    rw [ss5i_weight_cone σ hcone, Real.log_exp]
    have := ss5l_PhiTr_eq (N := N) (ε := ε) (z := ss5_toCh σ Z) (fun k l hkl => (hZ k l hkl).le)
    rw [ss5l_toChL_apply]
    unfold ss5_U
    rw [this]
    ring
  rw [hceq.fderiv_eq]
  have hU : DifferentiableAt ℝ (ss5_U N ε) (ss5l_toChL σ ξ) :=
    ((ss5t_contDiff_U hε).differentiable (by norm_num)) _
  have h1 := ((hU.hasFDerivAt).comp ξ (ss5l_toChL σ).hasFDerivAt).const_mul (-θ⁻¹)
  have h2 : fderiv ℝ (fun Z : EucConfig 1 N => -θ⁻¹ * ss5_U N ε (ss5l_toChL σ Z)) ξ =
      -θ⁻¹ • (fderiv ℝ (ss5_U N ε) (ss5l_toChL σ ξ)).comp (ss5l_toChL σ) := h1.fderiv
  rw [h2]
  simp [ss5l_toChL_apply]


/-! ### Cutoff functions and the closed chamber -/

theorem ss5l_cutoff {N : ℕ} {K O : Set (Ch5 N)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ χ : Ch5 N → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      ∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1 := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hO hKO
  have hst : cthickening (δ / 4) K ⊆ thickening (δ / 2) K :=
    cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨f, hf, -, hfs, hft⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := δ / 2) (E := K)) isClosed_cthickening hst
  have hts : tsupport f ⊆ cthickening δ K := by
    unfold tsupport
    rw [hfs]
    exact (closure_thickening_subset_cthickening _ _).trans (cthickening_mono (by linarith) K)
  refine ⟨f, hf, ?_, hts.trans hsub, fun z hz => ?_⟩
  · exact (hK.cthickening).of_isClosed_subset isClosed_closure hts
  · have hn : thickening (δ / 4) K ∈ 𝓝 z :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by positivity) K hz)
    filter_upwards [hn] with y hy
    exact (hft y).1 (thickening_subset_cthickening _ _ hy)

/-- The closed chamber. -/
def ss5l_cch (N : ℕ) : Set (Ch5 N) := {z | ∀ k l : Fin N, k < l → z k ≤ z l}

theorem ss5l_cch_closed (N : ℕ) : IsClosed (ss5l_cch N) := by
  have hm : ∀ i : Fin N, Continuous fun z : Ch5 N => z i := fun i =>
    (EuclideanSpace.proj i : Ch5 N →L[ℝ] ℝ).continuous
  have : ss5l_cch N = ⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l), {z : Ch5 N | z k ≤ z l} := by
    ext z; simp [ss5l_cch]
  rw [this]
  exact isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_le (hm k) (hm l)

theorem ss5l_chamber_open (N : ℕ) : IsOpen (ss5_chamber N) := by
  have hm : ∀ i : Fin N, Continuous fun z : Ch5 N => z i := fun i =>
    (EuclideanSpace.proj i : Ch5 N →L[ℝ] ℝ).continuous
  have : ss5_chamber N = ⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l), {z : Ch5 N | z k < z l} := by
    ext z; simp [ss5_chamber]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (hm k) (hm l)

/-- A compact subset of the open chamber has uniformly positive gaps. -/
theorem ss5l_sep {N : ℕ} {A : Set (Ch5 N)} (hA : IsCompact A) (hAC : A ⊆ ss5_chamber N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ A, ∀ k l : Fin N, k < l → δ ≤ z l - z k := by
  have hp : ∀ p : Fin N × Fin N, ∃ c : ℝ, 0 < c ∧ (p.1 < p.2 → ∀ z ∈ A, c ≤ z p.2 - z p.1) := by
    intro p
    by_cases hp : p.1 < p.2
    · obtain ⟨c, hc0, hc⟩ := hA.exists_forall_le' (f := fun z : Ch5 N => z p.2 - z p.1)
        (a := 0) (by
          exact ((EuclideanSpace.proj p.2 : Ch5 N →L[ℝ] ℝ).continuous.sub
            (EuclideanSpace.proj p.1 : Ch5 N →L[ℝ] ℝ).continuous).continuousOn)
        (fun z hz => sub_pos.2 (hAC hz p.1 p.2 hp))
      exact ⟨c, hc0, fun _ z hz => hc z hz⟩
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  choose c hc0 hc using hp
  have hsum0 : 0 ≤ ∑ p, 1 / c p := Finset.sum_nonneg fun p _ => (one_div_pos.2 (hc0 p)).le
  refine ⟨1 / (1 + ∑ p, 1 / c p), by positivity, fun z hz k l hkl => ?_⟩
  have h1 : 1 / c (k, l) ≤ 1 + ∑ p, 1 / c p := by
    have := Finset.single_le_sum (f := fun p => 1 / c p) (fun p _ => (one_div_pos.2 (hc0 p)).le)
      (Finset.mem_univ (k, l))
    linarith
  calc 1 / (1 + ∑ p, 1 / c p) ≤ 1 / (1 / c (k, l)) :=
        one_div_le_one_div_of_le (one_div_pos.2 (hc0 _)) h1
    _ = c (k, l) := by rw [one_div_one_div]
    _ ≤ z l - z k := hc (k, l) hkl z hz

/-- The cut-off adapted to a compact set of non-colliding configurations. -/
theorem ss5l_choose {N : ℕ} (σ : Equiv.Perm (Fin N)) {K : Set (EucConfig 1 N)} (hK : IsCompact K)
    (hKd : Disjoint K (eucCollisionSet 1 N)) :
    ∃ χ : Ch5 N → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ ss5_chamber N ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport χ, ∀ k l : Fin N, k < l → δ ≤ z l - z k) ∧
      ∀ ξ ∈ K, ss5_toCh σ ξ ∈ ss5l_cch N → χ =ᶠ[𝓝 (ss5_toCh σ ξ)] fun _ => 1 := by
  set K2 : Set (Ch5 N) := (ss5_toCh σ '' K) ∩ ss5l_cch N with hK2
  have hK2c : IsCompact K2 :=
    (hK.image (ss5h_toCh_continuous σ)).inter_right (ss5l_cch_closed N)
  have hK2C : K2 ⊆ ss5_chamber N := by
    rintro z ⟨⟨ξ, hξK, rfl⟩, hz⟩ k l hkl
    refine lt_of_le_of_ne (hz k l hkl) fun h => ?_
    have h0 : ξ (σ k) 0 = ξ (σ l) 0 := h
    have hne : σ k ≠ σ l := fun h' => (ne_of_lt hkl) (σ.injective h')
    refine Set.disjoint_left.1 hKd hξK ⟨σ k, σ l, hne, ?_⟩
    ext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    exact h0
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := ss5l_cutoff hK2c (ss5l_chamber_open N) hK2C
  refine ⟨χ, hχ, hχc, hχs, ?_, fun ξ hξ hz => hχ1 _ ⟨⟨ξ, hξ, rfl⟩, hz⟩⟩
  exact ss5l_sep hχc hχs


/-! ### The Fisher integrands in the two coordinate systems -/

/-- The integrand of `fisherInfoW (selfSimWeight 1 0 θ N 0)`. -/
def ss5l_fiC (N : ℕ) (θ : ℝ) (ζ : EucConfig 1 N → EucConfig 1 N) (ξ : EucConfig 1 N) : ℝ :=
  -2 * configDivW ζ ξ -
    2 * fderiv ℝ (fun Z : EucConfig 1 N => Real.log (selfSimWeight 1 0 θ N 0 Z)) ξ (ζ ξ) -
    ∑ i, ‖ζ ξ i‖ ^ 2

/-- The integrand of `ss5_fish θ U`. -/
def ss5l_fiU {N : ℕ} (θ : ℝ) (U : Ch5 N → ℝ) (η : Ch5 N → Ch5 N) (z : Ch5 N) : ℝ :=
  -2 * ss5_div η z + 2 * θ⁻¹ * inner ℝ (gradient U z) (η z) - ‖η z‖ ^ 2

theorem ss5l_toCh_zero {N : ℕ} (σ : Equiv.Perm (Fin N)) : ss5_toCh σ (0 : EucConfig 1 N) = 0 := by
  ext k; simp [ss5_toCh]

theorem ss5l_div_zero {N : ℕ} {η : Ch5 N → Ch5 N} {z : Ch5 N} (h : η =ᶠ[𝓝 z] fun _ => 0) :
    ss5_div η z = 0 := by
  unfold ss5_div
  refine Finset.sum_eq_zero fun k _ => ?_
  have hev : (fun w => η w k) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [h] with w hw
    simp [hw]
  rw [hev.fderiv_eq]
  simp

theorem ss5l_cfgdiv_zero {N : ℕ} {ζ : EucConfig 1 N → EucConfig 1 N} {ξ : EucConfig 1 N}
    (h : ζ =ᶠ[𝓝 ξ] fun _ => 0) : configDivW ζ ξ = 0 := by
  unfold configDivW
  refine Finset.sum_eq_zero fun k _ => ?_
  have hev : (fun Z : EucConfig 1 N => ζ Z k.1 k.2) =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
    filter_upwards [h] with w hw
    simp [hw]
  rw [hev.fderiv_eq]
  simp

theorem ss5l_integrand_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) (θ : ℝ) {ζ : EucConfig 1 N → EucConfig 1 N}
    (hζ : ContDiff ℝ ∞ ζ) {K : Set (EucConfig 1 N)} (hKc : IsClosed K)
    (hKz : ∀ ξ, ξ ∉ K → ζ ξ = 0) {χ : Ch5 N → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hK1 : ∀ ξ ∈ K, ss5_toCh σ ξ ∈ ss5l_cch N → (χ =ᶠ[𝓝 (ss5_toCh σ ξ)] fun _ => 1) ∧
      ∀ k l : Fin N, k < l → ε < ss5_toCh σ ξ l - ss5_toCh σ ξ k)
    (ξ : EucConfig 1 N) (hξ : ss5_toCh σ ξ ∈ ss5l_cch N) :
    ss5l_fiC N θ ζ ξ = ss5l_fiU θ (ss5_U N ε)
      (fun z => χ z • ss5_toCh σ (ζ (ss5l_unrank σ z))) (ss5_toCh σ ξ) := by
  unfold ss5l_fiC ss5l_fiU
  by_cases hK : ξ ∈ K
  · obtain ⟨hχ1, hgap⟩ := hK1 ξ hK hξ
    set z := ss5_toCh σ ξ with hz
    have hzu : ss5l_unrank σ z = ξ := ss5l_unrank_toCh σ ξ
    have hχz : χ z = 1 := hχ1.self_of_nhds
    have hηeq : (fun w => χ w • ss5_toCh σ (ζ (ss5l_unrank σ w))) =ᶠ[𝓝 z]
        fun w => ss5_toCh σ (ζ (ss5l_unrank σ w)) := by
      filter_upwards [hχ1] with w hw
      simp [hw]
    have hdiv : ss5_div (fun w => χ w • ss5_toCh σ (ζ (ss5l_unrank σ w))) z = configDivW ζ ξ := by
      rw [← hzu, ← ss5l_div_transport σ (hζ.differentiable (by simp)) z]
      unfold ss5_div
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (fun w => (χ w • ss5_toCh σ (ζ (ss5l_unrank σ w))) k) =ᶠ[𝓝 z]
          fun w => (ss5_toCh σ (ζ (ss5l_unrank σ w))) k := by
        filter_upwards [hηeq] with w hw
        rw [hw]
      rw [hk.fderiv_eq]
    have hηz : χ z • ss5_toCh σ (ζ (ss5l_unrank σ z)) = ss5_toCh σ (ζ ξ) := by
      rw [hχz, one_smul, hzu]
    beta_reduce
    rw [hdiv, hηz, ss5l_inner_gradient, ss5l_dlogG σ θ hε hgap (ζ ξ), ss5l_norm_transport]
    ring
  · have hz0 : ζ ξ = 0 := hKz ξ hK
    have hζ0 : ζ =ᶠ[𝓝 ξ] fun _ => 0 := by
      filter_upwards [hKc.isOpen_compl.mem_nhds hK] with Z hZ
      exact hKz Z hZ
    set z := ss5_toCh σ ξ with hz
    have hzu : ss5l_unrank σ z = ξ := ss5l_unrank_toCh σ ξ
    have hηeq : (fun w => χ w • ss5_toCh σ (ζ (ss5l_unrank σ w))) =ᶠ[𝓝 z] fun _ => 0 := by
      have h1 : ζ =ᶠ[𝓝 (ss5l_unrank σ z)] fun _ => 0 := by rw [hzu]; exact hζ0
      have h2 := (ss5l_unrank_continuous σ).continuousAt.eventually h1
      filter_upwards [h2] with w hw
      simp [hw, ss5l_toCh_zero]
    rw [ss5l_div_zero hηeq, ss5l_cfgdiv_zero hζ0, hz0, hηeq.self_of_nhds]
    simp

end HRS.MP.SelfSimP5Impl
