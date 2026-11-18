import HRS.Equilibrium.StaticLimits
import HRS.Dynamics.InitialData

/-!
# Lemma 7.5 `quadratic_limit`: spectral layer (packet Q08, sub-packet `Spectral`)

Skeleton file (statements only, `sorry`-ed; every statement is TRUE as written, see the notes on junk
values below). Everything here lives in `HRS.Q08`, helpers are prefixed `q08_`.

`Q08Data` bundles the standing hypotheses of `HRS.quadratic_limit` (Lemma 7.5, `M:N:lem:quadratic-limit`).
With `μ = ρ dx`, `g = periodicRiesz d s` and the orthonormal basis `(e_i)` of `L²_0(μ)`:

* `q08Kmat i j = ∬ g(x-y) e_i(x) e_j(y) dμ dμ` is the matrix of the (Hilbert-Schmidt, nonnegative) operator
  `K_μ` on `L²_0(μ)`; `q08Hmat i j = ∬ h e_i e_j` that of `H_μ`;
* `q08Cmat i j = susceptibilityCov g μ β (e_i) (e_j) = ⟨e_i, (I+βK_μ)^{-1} e_j⟩`;
* `q08Coef a i = ⟨φ_a, e_i⟩_{L²(μ)}`.

Junk values: all Bochner integrals here are of integrable functions (`g ∈ L²(μ⊗μ)` because `2s < d`
and `ρ` is bounded; `h ∈ L²(μ⊗μ)` by the envelope), `tsum`s are not used (only `HasSum`/`Summable`), and
`responseInverse` is the genuine solution because the response equation is uniquely solvable by Lax-Milgram
(`K_μ ≥ 0`); only `l2Inner` against it is used, which does not see the a.e.-ambiguity.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

variable {d : ℕ}

/-- The standing data and hypotheses of Lemma 7.5, bundled. -/
structure Q08Data (d : ℕ) where
  s : ℝ
  β : ℝ
  ρ : Torus d → ℝ
  c : ℝ
  B : ℝ
  h : Torus d → Torus d → ℝ
  e : ℕ → Torus d → ℝ
  p : ℕ
  φ : Fin p → Torus d → ℝ
  hd : 2 ≤ d
  hs0 : 0 ≤ s
  hs : s < (d : ℝ) / 2
  hβ : 0 < β
  hρ : SmoothPosDensity ρ
  hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c
  hmeas : Measurable (Function.uncurry h)
  hsymm : ∀ x y, h x y = h y x
  hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c)
  he : IsONBL2Zero (withDensityReal ρ) e
  hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M

namespace Q08Data

variable (D : Q08Data d)

/-- The background measure `μ = ρ dx` (a probability measure). -/
def μ : Measure (Torus d) := withDensityReal D.ρ

/-- The kernel `g = periodicRiesz d s`. -/
def g : Torus d → ℝ := periodicRiesz d D.s

/-- The Gibbs law `Q_{N,β}(μ)`. -/
def Gibbs (N : ℕ) : Measure (Config d N) := modulatedGibbs (periodicRiesz d D.s) N D.β D.μ

/-- The reference product law `μ^{⊗N}`. -/
def prodLaw (N : ℕ) : Measure (Config d N) := Measure.pi fun _ => D.μ

/-- Matrix of `K_μ`: `∬ g(x-y) e_i(x) e_j(y) dμ dμ`. -/
def Kmat (i j : ℕ) : ℝ :=
  ∫ x, ∫ y, periodicRiesz d D.s (x - y) * D.e i x * D.e j y ∂D.μ ∂D.μ

/-- Matrix of `H_μ`: `∬ h(x,y) e_i(x) e_j(y) dμ dμ` (the expression of the statement). -/
def Hmat (i j : ℕ) : ℝ :=
  ∫ x, ∫ y, D.h x y * D.e i x * D.e j y ∂D.μ ∂D.μ

/-- `C_{β,μ}(e_i, e_j)`. -/
def Cmat (i j : ℕ) : ℝ :=
  susceptibilityCov (periodicRiesz d D.s) D.μ D.β (D.e i) (D.e j)

/-- `⟨φ_a, e_i⟩_{L²(μ)}`. -/
def coef (a : Fin D.p) (i : ℕ) : ℝ := l2Inner D.μ (D.φ a) (D.e i)

end Q08Data

variable (D : Q08Data d)

instance q08_isProb_μ : IsProbabilityMeasure D.μ := isProb_withDensityReal D.hρ.density

/-! ### Helpers for the spectral layer (prefix `q08s_`) -/

theorem q08s_inner_toLp {X : Type*} [MeasurableSpace X] (ν : Measure X) {f g : X → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp [h1, h2, mul_comm]

theorem q08s_bessel {X : Type*} [MeasurableSpace X] (ν : Measure X) {ι : Type*} [DecidableEq ι] (f : ι → X → ℝ)
    (hf : ∀ i, MemLp (f i) 2 ν)
    (ho : ∀ i j, ∫ x, f i x * f j x ∂ν = if i = j then 1 else 0) (G : X → ℝ) (hG : MemLp G 2 ν) :
    Summable (fun i => (∫ x, G x * f i x ∂ν) ^ 2) ∧
      ∑' i, (∫ x, G x * f i x ∂ν) ^ 2 ≤ ∫ x, G x ^ 2 ∂ν := by
  set v : ι → MeasureTheory.Lp ℝ 2 ν := fun i => (hf i).toLp (f i) with hv
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hv]
    simp only
    rw [q08s_inner_toLp ν (hf i) (hf j), ho]
  set Gl := hG.toLp G with hGl
  have hin : ∀ i, inner ℝ (v i) Gl = ∫ x, G x * f i x ∂ν := by
    intro i
    rw [hv, hGl]
    simp only
    rw [q08s_inner_toLp ν (hf i) hG]
    refine integral_congr_ae (Eventually.of_forall fun x => by ring)
  have h1 := hon.inner_products_summable Gl
  have h2 := hon.tsum_inner_products_le Gl
  have hn : ‖Gl‖ ^ 2 = ∫ x, G x ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, hGl, q08s_inner_toLp ν hG hG]
    refine integral_congr_ae (Eventually.of_forall fun x => by ring)
  simp only [hin, Real.norm_eq_abs, sq_abs] at h1 h2
  rw [hn] at h2
  exact ⟨h1, h2⟩


section Q08sHelpers

open ResponseAux InnerProductSpace

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Abstract hypotheses for the response matrix. -/
structure q08s_Abs (one : H) (K : H →L[ℝ] H) (β : ℝ) (E U : ℕ → H) : Prop where
  hone : ‖one‖ = 1
  hKsa : ∀ u w, inner ℝ (K u) w = inner ℝ (K w) u
  hKnn : ∀ u, 0 ≤ inner ℝ (K u) u
  hβ : 0 ≤ β
  hEon : Orthonormal ℝ E
  hE0 : ∀ i, inner ℝ one (E i) = 0
  hEcomp : ∀ f, inner ℝ one f = 0 → (∀ i, inner ℝ (E i) f = 0) → f = 0
  hU0 : ∀ j, inner ℝ one (U j) = 0
  hUeq : ∀ j, U j + β • projL one (K (U j)) = E j

variable {one : H} {K : H →L[ℝ] H} {β : ℝ} {E U : ℕ → H}

theorem q08s_PU (A : q08s_Abs one K β E U) (j : ℕ) : projL one (U j) = U j :=
  (projL_eq_self_iff A.hone).2 (A.hU0 j)

theorem q08s_C_symm (A : q08s_Abs one K β E U) (i j : ℕ) :
    inner ℝ (E i) (U j) = inner ℝ (E j) (U i) := by
  have key : ∀ i j, inner ℝ (E i) (U j) = inner ℝ (U i) (U j) + β * inner ℝ (K (U i)) (U j) := by
    intro i j
    conv_lhs => rw [← A.hUeq i]
    rw [inner_add_left, real_inner_smul_left, inner_projL_left, q08s_PU A j]
  rw [key i j, key j i, real_inner_comm (U i) (U j), A.hKsa (U i) (U j)]

theorem q08s_sum_inner (v : ℕ → ℝ) (n : ℕ) (X Y : ℕ → H) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * inner ℝ (X i) (Y j) =
      inner ℝ (∑ i ∈ Finset.range n, v i • X i) (∑ j ∈ Finset.range n, v j • Y j) := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem q08s_Uv (A : q08s_Abs one K β E U) (v : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, v i • U i) + β • projL one (K (∑ i ∈ Finset.range n, v i • U i)) =
      ∑ i ∈ Finset.range n, v i • E i := by
  simp only [map_sum, map_smul, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← A.hUeq i, smul_add, smul_comm β (v i)]

theorem q08s_PUv (A : q08s_Abs one K β E U) (v : ℕ → ℝ) (n : ℕ) :
    projL one (∑ i ∈ Finset.range n, v i • U i) = ∑ i ∈ Finset.range n, v i • U i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, q08s_PU A i]

theorem q08s_C_psd (A : q08s_Abs one K β E U) (n : ℕ) (v : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * inner ℝ (E i) (U j) := by
  rw [q08s_sum_inner]
  set Uv := ∑ i ∈ Finset.range n, v i • U i
  set Ev := ∑ i ∈ Finset.range n, v i • E i
  have h1 : Ev = Uv + β • projL one (K Uv) := (q08s_Uv A v n).symm
  have h2 : projL one Uv = Uv := q08s_PUv A v n
  rw [h1, inner_add_left, real_inner_smul_left, inner_projL_left, h2]
  exact add_nonneg real_inner_self_nonneg (mul_nonneg A.hβ (A.hKnn Uv))

theorem q08s_E_sq (A : q08s_Abs one K β E U) (n : ℕ) (v : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, v i ^ 2 =
      inner ℝ (∑ i ∈ Finset.range n, v i • E i) (∑ i ∈ Finset.range n, v i • E i) := by
  rw [← q08s_sum_inner]
  have := orthonormal_iff_ite.1 A.hEon
  simp only [this, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_ite_eq, if_pos hi, sq]

theorem q08s_C_le (A : q08s_Abs one K β E U) (n : ℕ) (v : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * inner ℝ (E i) (U j) ≤
      ∑ i ∈ Finset.range n, v i ^ 2 := by
  rw [q08s_sum_inner, q08s_E_sq A]
  set Uv := ∑ i ∈ Finset.range n, v i • U i
  set Ev := ∑ i ∈ Finset.range n, v i • E i
  have h1 : Ev = Uv + β • projL one (K Uv) := (q08s_Uv A v n).symm
  have h2 : projL one Uv = Uv := q08s_PUv A v n
  have hb : 0 ≤ inner ℝ (K Uv) Uv := A.hKnn Uv
  have hc : 0 ≤ inner ℝ (projL one (K Uv)) (projL one (K Uv)) := real_inner_self_nonneg
  have e1 : inner ℝ Ev Uv = inner ℝ Uv Uv + β * inner ℝ (K Uv) Uv := by
    rw [h1, inner_add_left, real_inner_smul_left, inner_projL_left, h2]
  have e2 : inner ℝ Ev Ev = inner ℝ Uv Uv + 2 * β * inner ℝ (K Uv) Uv +
      β ^ 2 * inner ℝ (projL one (K Uv)) (projL one (K Uv)) := by
    conv_lhs => rw [h1]
    have p1 : inner ℝ (projL one (K Uv)) Uv = inner ℝ (K Uv) Uv := by rw [inner_projL_left, h2]
    have p2 : inner ℝ Uv (projL one (K Uv)) = inner ℝ (K Uv) Uv :=
      (real_inner_comm (projL one (K Uv)) Uv).trans p1
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, p1, p2]
    ring
  rw [e1, e2]
  have := A.hβ
  nlinarith [mul_nonneg this hb, mul_nonneg (sq_nonneg β) hc]

theorem q08s_expand (A : q08s_Abs one K β E U) (x : H) (hx : inner ℝ one x = 0) :
    HasSum (fun k => inner ℝ (E k) x • E k) x := by
  classical
  set v : Option ℕ → H := fun o => o.elim one E with hv
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with _ | i <;> rcases j with _ | j
    · simp [hv, real_inner_self_eq_norm_sq, A.hone]
    · simp [hv, A.hE0 j]
    · simp [hv, real_inner_comm one (E i), A.hE0 i]
    · simp only [hv, Option.elim, Option.some.injEq]
      exact orthonormal_iff_ite.1 A.hEon i j
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have h0 : inner ℝ one y = 0 := hy one (Submodule.subset_span ⟨none, rfl⟩)
    refine A.hEcomp y h0 fun i => hy (E i) (Submodule.subset_span ⟨some i, rfl⟩)
  set b := HilbertBasis.mkOfOrthogonalEqBot hon hsp with hb
  have hbv : ⇑b = v := HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp
  have h1 := b.hasSum_repr x
  simp only [HilbertBasis.repr_apply_apply, hbv] at h1
  have hinj : Function.Injective (some : ℕ → Option ℕ) := Option.some_injective ℕ
  have h2 := (hinj.hasSum_iff (f := fun o => inner ℝ (v o) x • v o) (a := x) ?_).2 h1
  · exact h2
  · intro o ho
    rcases o with _ | o
    · simp [hv, hx]
    · exact absurd ⟨o, rfl⟩ ho

theorem q08s_resolvent (A : q08s_Abs one K β E U) (i j : ℕ) :
    HasSum (fun k => ((if i = k then (1 : ℝ) else 0) + β * inner ℝ (K (E k)) (E i)) *
      inner ℝ (E k) (U j)) (if i = j then 1 else 0) := by
  classical
  have h := q08s_expand A (U j) (A.hU0 j)
  set Φ : H →L[ℝ] ℝ := (innerSL ℝ (E i)).comp (ContinuousLinearMap.id ℝ H + β • K) with hΦ
  have h2 := h.mapL Φ
  have hPE : projL one (E i) = E i := (projL_eq_self_iff A.hone).2 (A.hE0 i)
  have hval : Φ (U j) = if i = j then 1 else 0 := by
    have e1 : Φ (U j) = inner ℝ (E i) (U j + β • K (U j)) := by
      simp [hΦ, inner_add_right, real_inner_smul_right]
    have e2 : inner ℝ (E i) (K (U j)) = inner ℝ (E i) (projL one (K (U j))) := by
      rw [← inner_projL_left, hPE]
    rw [e1, inner_add_right, real_inner_smul_right, e2, ← real_inner_smul_right, ← inner_add_right,
      A.hUeq j]
    exact orthonormal_iff_ite.1 A.hEon i j
  rw [hval] at h2
  convert h2 using 2 with k
  simp only [hΦ, ContinuousLinearMap.comp_apply, innerSL_apply_apply, add_apply,
    ContinuousLinearMap.id_apply, smul_apply, map_smul, inner_add_right,
    real_inner_smul_right, smul_eq_mul]
  rw [orthonormal_iff_ite.1 A.hEon i k, real_inner_comm (E i) (K (E k))]
  ring

end Abstract


section Concrete


theorem q08s_hsd : D.s < (d : ℝ) := by
  have := D.hs
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

include D in
theorem q08s_hd1 : 1 ≤ d := le_trans (by norm_num) D.hd

theorem q08s_g_meas : Measurable (periodicRiesz d D.s) :=
  CoercAux.measurable_periodicRiesz_one (q08s_hd1 D) D.hs0 (q08s_hsd D)

theorem q08s_g_int : Integrable (periodicRiesz d D.s) :=
  (integral_periodicRiesz D.hd D.hs0 (q08s_hsd D)).1

theorem q08s_exists_bound : ∃ Λ : ℝ, 0 < Λ ∧ ∀ x, D.ρ x ≤ Λ :=
  PoleCavityAux.exists_density_bound D.hρ

/-- A bound on the density. -/
def q08s_Λ : ℝ := (q08s_exists_bound D).choose

theorem q08s_Λ_bound (x : Torus d) : D.ρ x ≤ q08s_Λ D := (q08s_exists_bound D).choose_spec.2 x

theorem q08s_ghat_nonneg (n : Lattice d) : 0 ≤ rieszCoeff d D.s n := by
  by_cases hn : n = 0
  · simp [rieszCoeff, hn]
  · exact (rieszCoeff_pos D.hd D.hs0 (q08s_hsd D) n hn).le

theorem q08s_setup : Setup (periodicRiesz d D.s) D.ρ (q08s_Λ D) :=
  ⟨D.hρ.density, q08s_Λ_bound D, q08s_g_meas D, q08s_g_int D, rieszCoeff d D.s, q08s_ghat_nonneg D,
    hcoef_of_funFourierCoeff (periodicRiesz_fourierCoeff D.hd D.hs0 (q08s_hsd D))⟩

end Concrete

section General

variable {g ρ : Torus d → ℝ} {Λ : ℝ}

theorem q08s_inner_KL (S : Setup g ρ Λ) (u w : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (KL S u) w = ∫ x, Kt g (withDensityReal ρ) u x * w x ∂(withDensityReal ρ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [KLfun_coe S u] with x hx
  rw [KL_apply, hx]
  simp [mul_comm]

theorem q08s_KL_symm (S : Setup g ρ Λ) (u w : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (KL S u) w = inner ℝ (KL S w) u := by
  obtain ⟨ĝ, hĝ, hcoef⟩ := S.hĝ
  rw [q08s_inner_KL, q08s_inner_KL]
  exact Kt_form_symm S.hρ S.hΛ S.hg S.hgi ĝ hcoef (Lp.memLp u) (Lp.memLp w)

end General


section Bridge


/-- `e_i` as an element of `L²(μ)`. -/
def q08s_E (i : ℕ) : Lp ℝ 2 (withDensityReal D.ρ) := (D.he.memLp i).toLp (D.e i)

theorem q08s_E_coe (i : ℕ) : (q08s_E D i : Torus d → ℝ) =ᵐ[withDensityReal D.ρ] D.e i :=
  (D.he.memLp i).coeFn_toLp

theorem q08s_inner_E (i : ℕ) (f : Lp ℝ 2 (withDensityReal D.ρ)) :
    inner ℝ (q08s_E D i) f = ∫ x, f x * D.e i x ∂(withDensityReal D.ρ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [q08s_E_coe D i] with x hx
  simp [hx, mul_comm]

theorem q08s_resp_exists (j : ℕ) :
    IsResponse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.e j)
      (responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.e j)) := by
  obtain ⟨h, hh, _⟩ := exists_unique_respEq (q08s_setup D) D.hβ.le (D.he.memLp j)
  have hex' : ∃ h, IsResponse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.e j) h := ⟨h, hh⟩
  unfold responseInverse
  rw [dif_pos hex']
  exact hex'.choose_spec

/-- The response `R_{β,μ} e_j` as an element of `L²(μ)`. -/
def q08s_U (j : ℕ) : Lp ℝ 2 (withDensityReal D.ρ) :=
  (q08s_resp_exists D j).1.toLp (responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.e j))

theorem q08s_U_coe (j : ℕ) : (q08s_U D j : Torus d → ℝ) =ᵐ[withDensityReal D.ρ]
    responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.e j) :=
  (q08s_resp_exists D j).1.coeFn_toLp

theorem q08s_abs : q08s_Abs (oneL D.hρ.density) (KL (q08s_setup D)) D.β (q08s_E D) (q08s_U D) := by
  have hρ := D.hρ.density
  haveI : IsProbabilityMeasure (withDensityReal D.ρ) := isProbabilityMeasure_dens hρ
  refine ⟨norm_oneL hρ, q08s_KL_symm (q08s_setup D), inner_KL_nonneg (q08s_setup D), D.hβ.le, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    rw [q08s_inner_E D i (q08s_E D j)]
    rw [integral_congr_ae (g := fun x => D.e j x * D.e i x)
      (by filter_upwards [q08s_E_coe D j] with x hx; rw [hx])]
    have := D.he.orthonormal j i
    unfold l2Inner at this
    rw [this]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro i
    rw [inner_oneL hρ]
    rw [integral_congr_ae (q08s_E_coe D i)]
    exact D.he.centered i
  · intro f h0 hf
    rw [inner_oneL hρ] at h0
    have := D.he.complete f (Lp.memLp f) h0 (fun i => by
      have := hf i
      rw [q08s_inner_E D i f] at this
      exact this)
    exact Lp.eq_zero_iff_ae_eq_zero.2 this
  · intro j
    rw [inner_oneL hρ]
    rw [integral_congr_ae (q08s_U_coe D j)]
    exact (q08s_resp_exists D j).2.1
  · intro j
    have hresp := q08s_resp_exists D j
    obtain ⟨hP, hT⟩ := (respEq_iff (q08s_setup D) D.β (D.he.memLp j) hresp.1).1 hresp
    have hPE : projL (oneL hρ) (q08s_E D j) = q08s_E D j := by
      refine (projL_eq_self_iff (norm_oneL hρ)).2 ?_
      rw [inner_oneL hρ, integral_congr_ae (q08s_E_coe D j)]
      exact D.he.centered j
    rw [Top_apply, hP] at hT
    exact hT.trans hPE

theorem q08s_Cmat_eq (i j : ℕ) : D.Cmat i j = inner ℝ (q08s_E D i) (q08s_U D j) := by
  rw [q08s_inner_E D i (q08s_U D j)]
  unfold Q08Data.Cmat Q08Data.μ susceptibilityCov l2Inner projMean pair
  have h0 : ∫ x, D.e i x ∂(withDensityReal D.ρ) = 0 := D.he.centered i
  simp only [h0, sub_zero]
  refine integral_congr_ae ?_
  filter_upwards [q08s_U_coe D j] with x hx
  rw [hx, mul_comm]

theorem q08s_Kmat_eq (i j : ℕ) :
    D.Kmat i j = inner ℝ (KL (q08s_setup D) (q08s_E D j)) (q08s_E D i) := by
  rw [q08s_inner_KL]
  have h1 : Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (q08s_E D j) =
      Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (D.e j) := Kt_congr _ (q08s_E_coe D j)
  rw [h1]
  unfold Q08Data.Kmat
  have h2 : ∀ x, ∫ y, periodicRiesz d D.s (x - y) * D.e i x * D.e j y ∂D.μ =
      Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (D.e j) x * D.e i x := by
    intro x
    unfold Kt
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  simp_rw [h2]
  refine integral_congr_ae ?_
  filter_upwards [q08s_E_coe D i] with x hx
  rw [hx]

end Bridge

theorem q08s_memLp_tensor {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} [SFinite μ] [SFinite ν] {a : X → ℝ} {b : Y → ℝ} (ha : MemLp a 2 μ)
    (hb : MemLp b 2 ν) : MemLp (fun z : X × Y => a z.1 * b z.2) 2 (μ.prod ν) := by
  have h1 : AEStronglyMeasurable (fun z : X × Y => a z.1 * b z.2) (μ.prod ν) :=
    (ha.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hb.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  rw [memLp_two_iff_integrable_sq h1]
  have := (ha.integrable_sq).mul_prod (hb.integrable_sq)
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp [mul_pow]

theorem q08s_hs_summable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (e : ℕ → X → ℝ) (he : ∀ i, MemLp (e i) 2 μ)
    (ho : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0) (k : X → X → ℝ)
    (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ)) :
    Summable (fun ij : ℕ × ℕ => (∫ x, ∫ y, k x y * e ij.1 x * e ij.2 y ∂μ ∂μ) ^ 2) := by
  set f : ℕ × ℕ → X × X → ℝ := fun ij z => e ij.1 z.1 * e ij.2 z.2 with hf
  have hfm : ∀ ij, MemLp (f ij) 2 (μ.prod μ) := fun ij => q08s_memLp_tensor (he _) (he _)
  have hfo : ∀ ij kl, ∫ z, f ij z * f kl z ∂(μ.prod μ) = if ij = kl then 1 else 0 := by
    intro ij kl
    have : ∀ z : X × X, f ij z * f kl z = (e ij.1 z.1 * e kl.1 z.1) * (e ij.2 z.2 * e kl.2 z.2) := by
      intro z; simp only [hf]; ring
    simp_rw [this]
    rw [integral_prod_mul (fun x => e ij.1 x * e kl.1 x) (fun y => e ij.2 y * e kl.2 y), ho, ho]
    rcases ij with ⟨a, b⟩
    rcases kl with ⟨c, d⟩
    by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]
  obtain ⟨hs, _⟩ := q08s_bessel (μ.prod μ) f hfm hfo _ hk
  refine hs.congr fun ij => ?_
  have hint : Integrable (fun z : X × X => k z.1 z.2 * f ij z) (μ.prod μ) :=
    hk.integrable_mul (hfm ij)
  rw [integral_prod _ hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hf]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring_nf



section Facts


theorem q08s_g_sq_int :
    Integrable (fun p : Torus d × Torus d => periodicRiesz d D.s (p.1 - p.2) ^ 2) (D.μ.prod D.μ) :=
  periodicRiesz_sq_integrable D.hd D.hs0 D.hs D.ρ D.hρ.density (q08s_Λ D) (q08s_Λ_bound D)

theorem q08s_g_memLp :
    MemLp (fun p : Torus d × Torus d => periodicRiesz d D.s (p.1 - p.2)) 2 (D.μ.prod D.μ) := by
  have hm : AEStronglyMeasurable (fun p : Torus d × Torus d => periodicRiesz d D.s (p.1 - p.2))
      (D.μ.prod D.μ) := ((q08s_g_meas D).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  exact q08s_g_sq_int D

theorem q08s_diag_ae : ∀ᵐ z ∂(D.μ.prod D.μ), z.1 ≠ z.2 := by
  have hm : MeasurableSet {z : Torus d × Torus d | z.1 ≠ z.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [Measure.ae_prod_iff_ae_ae hm]
  refine Eventually.of_forall fun x => ?_
  have h0 : D.μ {x} = 0 := withDensity_absolutelyContinuous _ _ (volume_singleton_torus (q08s_hd1 D) x)
  rw [ae_iff]
  have : {y | ¬ x ≠ y} = {x} := by
    ext y; simp [eq_comm]
  rw [this]
  exact h0

theorem q08s_h_memLp :
    MemLp (fun z : Torus d × Torus d => D.h z.1 z.2) 2 (D.μ.prod D.μ) := by
  have hm : AEStronglyMeasurable (fun z : Torus d × Torus d => D.h z.1 z.2) (D.μ.prod D.μ) :=
    D.hmeas.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  have hb : Integrable (fun z : Torus d × Torus d =>
      2 * D.B ^ 2 * (periodicRiesz d D.s (z.1 - z.2) ^ 2 + D.c ^ 2)) (D.μ.prod D.μ) :=
    ((q08s_g_sq_int D).add (integrable_const _)).const_mul _
  refine hb.mono' (hm.pow 2) ?_
  filter_upwards [q08s_diag_ae D] with z hz
  have h1 := D.hB z.1 z.2 hz
  have h0 : 0 ≤ |D.h z.1 z.2| := abs_nonneg _
  have h2 : D.h z.1 z.2 ^ 2 ≤ (D.B * (periodicRiesz d D.s (z.1 - z.2) + D.c)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ h0 h1 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine h2.trans ?_
  nlinarith [sq_nonneg (D.B * (periodicRiesz d D.s (z.1 - z.2) - D.c))]

theorem q08s_e_ortho (i j : ℕ) : ∫ x, D.e i x * D.e j x ∂D.μ = if i = j then 1 else 0 :=
  D.he.orthonormal i j

theorem q08s_kernel_tensor_int (k : Torus d → Torus d → ℝ)
    (hk : MemLp (fun z : Torus d × Torus d => k z.1 z.2) 2 (D.μ.prod D.μ)) (i j : ℕ) :
    Integrable (fun z : Torus d × Torus d => k z.1 z.2 * D.e i z.1 * D.e j z.2) (D.μ.prod D.μ) := by
  have := hk.integrable_mul (q08s_memLp_tensor (D.he.memLp i) (D.he.memLp j))
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.mul_apply]
  ring


end Facts

end Q08sHelpers


/-! ### Hilbert-Schmidt structure of `K` and `H` -/

/-- `K` is symmetric, Hilbert-Schmidt (`∑ K_ij² ≤ ‖g‖²_{L²(μ⊗μ)} < ∞`, Bessel for the orthonormal family
`e_i ⊗ e_j`) and nonnegative (`ĝ_k ≥ 0`, `ĝ_0 = 0`, Parseval for `f ρ ∈ L²(dx)`). -/
theorem q08_Kmat_spec :
    (∀ i j, D.Kmat i j = D.Kmat j i) ∧
    Summable (fun ij : ℕ × ℕ => D.Kmat ij.1 ij.2 ^ 2) ∧
    ∀ (n : ℕ) (v : ℕ → ℝ),
      0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * D.Kmat i j := by
  refine ⟨fun i j => ?_, ?_, fun n v => ?_⟩
  · rw [q08s_Kmat_eq, q08s_Kmat_eq]
    exact q08s_KL_symm (q08s_setup D) _ _
  · exact q08s_hs_summable D.μ D.e D.he.memLp (q08s_e_ortho D) (fun x y => periodicRiesz d D.s (x - y))
      (q08s_g_memLp D)
  · have h1 : ∀ i j, D.Kmat i j = inner ℝ (q08s_E D i) (ResponseAux.KL (q08s_setup D) (q08s_E D j)) := fun i j => by
      rw [q08s_Kmat_eq, real_inner_comm]
    simp_rw [h1]
    rw [q08s_sum_inner v n (q08s_E D) (fun j => ResponseAux.KL (q08s_setup D) (q08s_E D j))]
    have : ∑ j ∈ Finset.range n, v j • ResponseAux.KL (q08s_setup D) (q08s_E D j) =
        ResponseAux.KL (q08s_setup D) (∑ j ∈ Finset.range n, v j • q08s_E D j) := by
      simp [map_sum, map_smul]
    rw [this, real_inner_comm]
    exact ResponseAux.inner_KL_nonneg (q08s_setup D) _

/-- `H` is symmetric and Hilbert-Schmidt (`h ∈ L²(μ⊗μ)` by the envelope `|h| ≤ B(g + c)` and `2s < d`). -/
theorem q08_Hmat_spec :
    (∀ i j, D.Hmat i j = D.Hmat j i) ∧
    Summable (fun ij : ℕ × ℕ => D.Hmat ij.1 ij.2 ^ 2) := by
  refine ⟨fun i j => ?_, ?_⟩
  · unfold Q08Data.Hmat
    have hint := q08s_kernel_tensor_int D D.h (q08s_h_memLp D) j i
    rw [integral_integral_swap (f := fun x y => D.h x y * D.e j x * D.e i y) hint]
    refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae (Eventually.of_forall fun b => ?_))
    simp only
    rw [D.hsymm b a]
    ring
  · exact q08s_hs_summable D.μ D.e D.he.memLp (q08s_e_ortho D) D.h (q08s_h_memLp D)

/-- The coefficients of the tests: `∑_i ⟨φ_a, e_i⟩² ≤ ‖φ_a‖²_{L²(μ)}` (Bessel). -/
theorem q08_coef_summable (a : Fin D.p) : Summable (fun i => D.coef a i ^ 2) := by
  obtain ⟨hm, M, hM⟩ := D.hφ a
  have hmem : MemLp (D.φ a) 2 D.μ :=
    MemLp.of_bound hm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hM x)
  exact (q08s_bessel D.μ D.e D.he.memLp (q08s_e_ortho D) (D.φ a) hmem).1

/-! ### The response matrix `C = (I + βK)^{-1}` -/

/-- `C_ij = ⟨e_i, (I+βK_μ)^{-1} e_j⟩` is a symmetric matrix with `0 ≤ C ≤ I` (as a form on finitely
supported vectors), and it is the inverse of `I + βK` in the basis `(e_i)`: row `i` of `K` and column `j`
of `C` are in `ℓ²`, and `∑_k (δ_ik + β K_ik) C_kj = δ_ij`. -/
theorem q08_Cmat_spec :
    (∀ i j, D.Cmat i j = D.Cmat j i) ∧
    (∀ (n : ℕ) (v : ℕ → ℝ),
      0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * D.Cmat i j) ∧
    (∀ (n : ℕ) (v : ℕ → ℝ),
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * D.Cmat i j ≤
        ∑ i ∈ Finset.range n, v i ^ 2) ∧
    ∀ i j, HasSum (fun k => ((if i = k then (1 : ℝ) else 0) + D.β * D.Kmat i k) * D.Cmat k j)
      (if i = j then 1 else 0) := by
  have A := q08s_abs D
  refine ⟨fun i j => ?_, fun n v => ?_, fun n v => ?_, fun i j => ?_⟩
  · rw [q08s_Cmat_eq, q08s_Cmat_eq]; exact q08s_C_symm A i j
  · simp_rw [q08s_Cmat_eq]; exact q08s_C_psd A n v
  · simp_rw [q08s_Cmat_eq]; exact q08s_C_le A n v
  · have := q08s_resolvent A i j
    simp_rw [q08s_Kmat_eq, q08s_Cmat_eq]
    exact this

/-! ### Helpers for the bounded orthonormal family (prefix `q08s_`) -/

section Q08sBounded


section S5


theorem q08s_memLp_of_bdd {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : MemLp f 2 μ :=
  MemLp.of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)

theorem q08s_integrable_of_bdd {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  (q08s_memLp_of_bdd hm M hM).integrable one_le_two

theorem q08s_orthonormalize {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} [Finite ι] (g : ι → X → ℝ) (hg : ∀ s, Measurable (g s) ∧ ∃ M, ∀ x, |g s x| ≤ M)
    (hg0 : ∀ s, ∫ x, g s x ∂μ = 0) :
    ∃ (L : ℕ) (u : Fin L → X → ℝ), (∀ i, Measurable (u i) ∧ ∃ M, ∀ x, |u i x| ≤ M) ∧
      (∀ i, ∫ x, u i x ∂μ = 0) ∧
      (∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0) ∧
      ∀ s, g s =ᵐ[μ] fun x => ∑ i, (∫ y, g s y * u i y ∂μ) * u i x := by
  classical
  have hmem : ∀ s, MemLp (g s) 2 μ := fun s =>
    q08s_memLp_of_bdd (hg s).1 (hg s).2.choose (hg s).2.choose_spec
  set v : ι → MeasureTheory.Lp ℝ 2 μ := fun s => (hmem s).toLp (g s) with hv
  set W : Submodule ℝ (MeasureTheory.Lp ℝ 2 μ) := Submodule.span ℝ (Set.range v) with hW
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  set b := stdOrthonormalBasis ℝ W with hb
  have hrep : ∀ w ∈ W, ∃ f : X → ℝ, Measurable f ∧ (∃ M, ∀ x, |f x| ≤ M) ∧ (∫ x, f x ∂μ = 0) ∧
      (w : X → ℝ) =ᵐ[μ] f := by
    intro w hw
    refine Submodule.span_induction (p := fun (w : MeasureTheory.Lp ℝ 2 μ) _ => ∃ f : X → ℝ, Measurable f ∧
      (∃ M, ∀ x, |f x| ≤ M) ∧ (∫ x, f x ∂μ = 0) ∧ (w : X → ℝ) =ᵐ[μ] f) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨s, rfl⟩
      exact ⟨g s, (hg s).1, (hg s).2, hg0 s, (hmem s).coeFn_toLp⟩
    · exact ⟨0, measurable_const, ⟨0, by simp⟩, by simp, Lp.coeFn_zero _ _ _⟩
    · rintro x y - - ⟨f1, m1, ⟨M1, hM1⟩, i1, e1⟩ ⟨f2, m2, ⟨M2, hM2⟩, i2, e2⟩
      refine ⟨fun t => f1 t + f2 t, m1.add m2, ⟨M1 + M2, fun t => (abs_add_le _ _).trans
        (add_le_add (hM1 t) (hM2 t))⟩, ?_, (Lp.coeFn_add x y).trans (e1.add e2)⟩
      rw [integral_add (q08s_integrable_of_bdd m1 M1 hM1) (q08s_integrable_of_bdd m2 M2 hM2), i1, i2,
        add_zero]
    · rintro a x - ⟨f, m, ⟨M, hM⟩, i, e⟩
      refine ⟨fun t => a * f t, m.const_mul a, ⟨|a| * M, fun t => ?_⟩, ?_,
        (Lp.coeFn_smul a x).trans (e.mono fun t ht => by simp [ht])⟩
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)
      · rw [integral_const_mul, i, mul_zero]
  choose F hFm hFb hF0 hFae using fun i : Fin (Module.finrank ℝ W) => hrep (b i : MeasureTheory.Lp ℝ 2 μ) (b i).2
  have hinner : ∀ i j, inner ℝ (b i : MeasureTheory.Lp ℝ 2 μ) (b j : MeasureTheory.Lp ℝ 2 μ) =
      ∫ x, F i x * F j x ∂μ := by
    intro i j
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hFae i, hFae j] with x h1 h2
    simp [h1, h2, mul_comm]
  refine ⟨Module.finrank ℝ W, F, fun i => ⟨hFm i, hFb i⟩, hF0, ?_, ?_⟩
  · intro i j
    rw [← hinner]
    have := orthonormal_iff_ite.1 b.orthonormal i j
    rw [Submodule.coe_inner] at this
    rw [this]
  · intro s
    set x : W := ⟨v s, Submodule.subset_span ⟨s, rfl⟩⟩ with hx
    have h1 : v s = ∑ i, (inner ℝ (b i) x) • (b i : MeasureTheory.Lp ℝ 2 μ) := by
      have := Subtype.ext_iff.1 (b.sum_repr' x).symm
      simpa [Submodule.coe_sum, hx] using this
    have h3 : ((v s : MeasureTheory.Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
        ∑ i, ⇑((inner ℝ (b i) x) • (b i : MeasureTheory.Lp ℝ 2 μ)) := by
      have := (Lp.coeFn_finsetSum Finset.univ
        (fun i => (inner ℝ (b i) x) • (b i : MeasureTheory.Lp ℝ 2 μ)))
      rw [← h1] at this
      exact this
    have h4 : ∀ i, ⇑((inner ℝ (b i) x) • (b i : MeasureTheory.Lp ℝ 2 μ)) =ᵐ[μ]
        fun t => (inner ℝ (b i) x) * F i t := fun i =>
      (Lp.coeFn_smul _ _).trans ((hFae i).mono fun t ht => by simp [ht])
    have h5 := h3.trans (eventuallyEq_sum (fun i _ => h4 i))
    have h6 : (g s) =ᵐ[μ] (v s : X → ℝ) := ((hmem s).coeFn_toLp).symm
    have hcoef : ∀ i, inner ℝ (b i) x = ∫ y, g s y * F i y ∂μ := by
      intro i
      rw [Submodule.coe_inner, hx]
      simp only
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hFae i, (hmem s).coeFn_toLp] with t h1 h2
      have h2' : ((v s : MeasureTheory.Lp ℝ 2 μ) : X → ℝ) t = g s t := h2
      simp [h1, h2', mul_comm]
    refine h6.trans (h5.trans (Eventually.of_forall fun t => ?_))
    simp only [Finset.sum_apply, hcoef]


theorem q08s_sq_integral {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {G : Y → ℝ}
    (hG : MemLp G 2 ν) : ‖hG.toLp G‖ ^ 2 = ∫ y, G y ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hG.coeFn_toLp] with y hy
  simp [hy, sq]

theorem q08s_proj_min_abs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (hv : Orthonormal ℝ v) (f : E) (d : ι → ℝ) :
    ‖f - ∑ i, inner ℝ (v i) f • v i‖ ≤ ‖f - ∑ i, d i • v i‖ := by
  set B := ∑ i, inner ℝ (v i) f • v i with hB
  set A := ∑ i, d i • v i with hA
  have horth : ∀ i, inner ℝ (v i) (f - B) = 0 := by
    intro i
    rw [inner_sub_right, hB, inner_sum]
    simp only [inner_smul_right]
    have := orthonormal_iff_ite.1 hv
    simp [this]
  have h0 : inner ℝ (f - B) (B - A) = 0 := by
    have : B - A = ∑ i, (inner ℝ (v i) f - d i) • v i := by
      rw [hB, hA, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_smul]
    rw [this, inner_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_right, real_inner_comm (v i) (f - B), horth i, mul_zero]
  have : ‖f - A‖ ^ 2 = ‖f - B‖ ^ 2 + ‖B - A‖ ^ 2 := by
    have e : f - A = (f - B) + (B - A) := by abel
    rw [e, norm_add_sq_real, h0]; ring
  have h1 : ‖f - B‖ ^ 2 ≤ ‖f - A‖ ^ 2 := by nlinarith [sq_nonneg ‖B - A‖]
  exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _)


theorem q08s_memLp_comb {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {ι : Type*} [Fintype ι]
    (w : ι → Y → ℝ) (hw : ∀ i, MemLp (w i) 2 ν) {F : Y → ℝ} (hF : MemLp F 2 ν) (d : ι → ℝ) :
    MemLp (fun y => F y - ∑ i, d i * w i y) 2 ν :=
  hF.sub (memLp_finset_sum _ fun i _ => (hw i).const_mul (d i))

theorem q08s_toLp_comb {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {ι : Type*} [Fintype ι]
    (w : ι → Y → ℝ) (hw : ∀ i, MemLp (w i) 2 ν) {F : Y → ℝ} (hF : MemLp F 2 ν) (d : ι → ℝ) :
    (q08s_memLp_comb w hw hF d).toLp (fun y => F y - ∑ i, d i * w i y) =
      hF.toLp F - ∑ i, d i • (hw i).toLp (w i) := by
  refine (Lp.ext ?_)
  have h1 := (q08s_memLp_comb w hw hF d).coeFn_toLp
  have h2 := Lp.coeFn_sub (hF.toLp F) (∑ i, d i • (hw i).toLp (w i))
  have h3 := Lp.coeFn_finsetSum Finset.univ (fun i => d i • (hw i).toLp (w i))
  have h4 : ∀ᵐ y ∂ν, ∀ i, ((d i • (hw i).toLp (w i) : Lp ℝ 2 ν) : Y → ℝ) y = d i * w i y := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (d i) ((hw i).toLp (w i)), (hw i).coeFn_toLp] with y a b
    rw [a]; simp [b]
  filter_upwards [h1, h2, h3, h4, hF.coeFn_toLp] with y a b c e f
  rw [a, b]
  simp only [Pi.sub_apply, c, Finset.sum_apply, f]
  rw [Finset.sum_congr rfl fun i _ => e i]

theorem q08s_proj_min {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (w : ι → Y → ℝ) (hw : ∀ i, MemLp (w i) 2 ν)
    (ho : ∀ i j, ∫ y, w i y * w j y ∂ν = if i = j then 1 else 0) {F : Y → ℝ} (hF : MemLp F 2 ν)
    (d : ι → ℝ) :
    ∫ y, (F y - ∑ i, (∫ z, F z * w i z ∂ν) * w i y) ^ 2 ∂ν ≤
      ∫ y, (F y - ∑ i, d i * w i y) ^ 2 ∂ν := by
  set c : ι → ℝ := fun i => ∫ z, F z * w i z ∂ν with hc
  have hon : Orthonormal ℝ (fun i => (hw i).toLp (w i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [q08s_inner_toLp ν (hw i) (hw j), ho]
  have hci : ∀ i, inner ℝ ((hw i).toLp (w i)) (hF.toLp F) = c i := by
    intro i
    rw [q08s_inner_toLp ν (hw i) hF]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only [hc]; ring)
  have h := q08s_proj_min_abs (fun i => (hw i).toLp (w i)) hon (hF.toLp F) d
  simp only [hci] at h
  rw [← q08s_toLp_comb w hw hF c, ← q08s_toLp_comb w hw hF d] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [q08s_sq_integral, q08s_sq_integral] at h2


end S5

section S6



/-- Subalgebra of finite sums of tensors of continuous functions. -/
def q08s_tensorAlg (d : ℕ) : Subalgebra ℝ C(Torus d × Torus d, ℝ) :=
  Algebra.adjoin ℝ (Set.range (fun f : C(Torus d, ℝ) => f.comp (ContinuousMap.fst : C(Torus d × Torus d, Torus d))) ∪
    Set.range (fun f : C(Torus d, ℝ) => f.comp (ContinuousMap.snd : C(Torus d × Torus d, Torus d))))

theorem q08s_tensorAlg_form (T : C(Torus d × Torus d, ℝ)) (hT : T ∈ q08s_tensorAlg d) :
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → C(Torus d, ℝ)), ∀ z, T z = ∑ i, a i z.1 * b i z.2 := by
  classical
  unfold q08s_tensorAlg at hT
  refine Algebra.adjoin_induction (p := fun T _ => ∃ (ι : Type) (_ : Fintype ι) (a b : ι → C(Torus d, ℝ)),
    ∀ z, T z = ∑ i, a i z.1 * b i z.2) ?_ ?_ ?_ ?_ hT
  · rintro T (⟨f, rfl⟩ | ⟨f, rfl⟩)
    · exact ⟨Unit, inferInstance, fun _ => f, fun _ => 1, fun z => by simp⟩
    · exact ⟨Unit, inferInstance, fun _ => 1, fun _ => f, fun z => by simp⟩
  · intro r
    exact ⟨Unit, inferInstance, fun _ => ContinuousMap.const _ r, fun _ => 1, fun z => by simp [Algebra.algebraMap_eq_smul_one]⟩
  · rintro T S - - ⟨ι1, _, a1, b1, h1⟩ ⟨ι2, _, a2, b2, h2⟩
    refine ⟨ι1 ⊕ ι2, inferInstance, Sum.elim a1 a2, Sum.elim b1 b2, fun z => ?_⟩
    simp [h1, h2, Fintype.sum_sum_type]
  · rintro T S - - ⟨ι1, _, a1, b1, h1⟩ ⟨ι2, _, a2, b2, h2⟩
    refine ⟨ι1 × ι2, inferInstance, fun p => a1 p.1 * a2 p.2, fun p => b1 p.1 * b2 p.2, fun z => ?_⟩
    simp only [ContinuousMap.mul_apply, h1, h2, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem q08s_tensorAlg_sep : (q08s_tensorAlg d).SeparatesPoints := by
  intro z w hzw
  by_cases h1 : z.1 = w.1
  · have h2 : z.2 ≠ w.2 := fun h => hzw (Prod.ext h1 h)
    refine ⟨_, ⟨(ContinuousMap.mk (fun x : Torus d => dist x z.2) (continuous_id.dist continuous_const)).comp
      (ContinuousMap.snd : C(Torus d × Torus d, Torus d)), ?_, rfl⟩, ?_⟩
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
    · intro h
      have h' : dist z.2 z.2 = dist w.2 z.2 := h
      rw [dist_self] at h'
      exact h2 (dist_eq_zero.1 h'.symm).symm
  · refine ⟨_, ⟨(ContinuousMap.mk (fun x : Torus d => dist x z.1) (continuous_id.dist continuous_const)).comp
      (ContinuousMap.fst : C(Torus d × Torus d, Torus d)), ?_, rfl⟩, ?_⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
    · intro h
      have h' : dist z.1 z.1 = dist w.1 z.1 := h
      rw [dist_self] at h'
      exact h1 (dist_eq_zero.1 h'.symm).symm


theorem q08s_norm_sq_lp {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} (h : Lp ℝ 2 ν) :
    ‖h‖ ^ 2 = ∫ y, (h y) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [sq]

theorem q08s_tensor_dense (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {F : Torus d × Torus d → ℝ} (hF : MemLp F 2 (μ.prod μ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → Torus d → ℝ), (∀ i, Continuous (a i) ∧ Continuous (b i)) ∧
      ∫ z, (F z - ∑ i, a i z.1 * b i z.2) ^ 2 ∂(μ.prod μ) ≤ ε ^ 2 := by
  haveI : BorelSpace (Torus d × Torus d) := Prod.borelSpace
  set ν := μ.prod μ with hν
  have hden := ContinuousMap.toLp_denseRange ℝ ν ℝ (p := 2) (by norm_num)
  obtain ⟨G, hG⟩ := (Metric.denseRange_iff.1 hden) (hF.toLp F) (ε / 2) (by positivity)
  have hcl := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints (q08s_tensorAlg d)
    q08s_tensorAlg_sep
  have hGmem : G ∈ (q08s_tensorAlg d).topologicalClosure := by rw [hcl]; trivial
  have hGmem' : G ∈ closure ((q08s_tensorAlg d : Subalgebra ℝ C(Torus d × Torus d, ℝ)) : Set C(Torus d × Torus d, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe]; exact hGmem
  obtain ⟨T, hTA, hGT⟩ := Metric.mem_closure_iff.1 hGmem' (ε / 2) (by positivity)
  obtain ⟨ι, hι, a, b, hT⟩ := q08s_tensorAlg_form T hTA
  refine ⟨ι, hι, fun i => a i, fun i => b i, fun i => ⟨(a i).continuous, (b i).continuous⟩, ?_⟩
  -- L² closeness of F and G
  have h1 : ∫ z, (F z - G z) ^ 2 ∂ν ≤ (ε / 2) ^ 2 := by
    have hn := q08s_norm_sq_lp (hF.toLp F - ContinuousMap.toLp 2 ν ℝ G)
    rw [dist_eq_norm] at hG
    have hle : ‖hF.toLp F - ContinuousMap.toLp 2 ν ℝ G‖ ^ 2 ≤ (ε / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hG.le 2
    rw [hn] at hle
    refine le_trans (le_of_eq ?_) hle
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (hF.toLp F) (ContinuousMap.toLp 2 ν ℝ G),
      ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℝ) G, hF.coeFn_toLp] with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have h2 : ∀ z, (G z - T z) ^ 2 ≤ (ε / 2) ^ 2 := by
    intro z
    have := ContinuousMap.dist_apply_le_dist (f := G) (g := T) z
    rw [Real.dist_eq] at this
    have h0 : |G z - T z| ≤ ε / 2 := this.trans hGT.le
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hGm : MemLp (fun z => G z) 2 ν :=
    (Lp.memLp (ContinuousMap.toLp 2 ν ℝ G)).ae_eq (ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℝ) G)
  have hTm : MemLp (fun z => T z) 2 ν :=
    (Lp.memLp (ContinuousMap.toLp 2 ν ℝ T)).ae_eq (ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℝ) T)
  have i1 : Integrable (fun z => (F z - G z) ^ 2) ν := (hF.sub hGm).integrable_sq
  have i2 : Integrable (fun z => (G z - T z) ^ 2) ν := (hGm.sub hTm).integrable_sq
  have i3 : Integrable (fun z => (F z - T z) ^ 2) ν := (hF.sub hTm).integrable_sq
  have h3 : ∫ z, (G z - T z) ^ 2 ∂ν ≤ (ε / 2) ^ 2 := by
    calc ∫ z, (G z - T z) ^ 2 ∂ν ≤ ∫ z, (ε / 2) ^ 2 ∂ν := integral_mono i2 (integrable_const _) h2
      _ = (ε / 2) ^ 2 := by simp
  have h4 : ∫ z, (F z - T z) ^ 2 ∂ν ≤ ∫ z, (2 * (F z - G z) ^ 2 + 2 * (G z - T z) ^ 2) ∂ν := by
    refine integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun z => ?_
    simp only
    nlinarith [sq_nonneg (F z - G z - (G z - T z))]
  rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul] at h4
  have h5 : ∀ z, (F z - ∑ i, a i z.1 * b i z.2) = F z - T z := fun z => by rw [hT z]
  simp_rw [h5]
  nlinarith [h1, h3, h4]


end S6

section S7


theorem q08s_sq_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : MemLp f 2 μ) : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  set c := ∫ x, f x ∂μ with hc
  have h1 : Integrable f μ := hf.integrable one_le_two
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have h0 : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have e : ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - c ^ 2 := by
    have : ∀ x, (f x - c) ^ 2 = f x ^ 2 - 2 * c * f x + c ^ 2 := fun x => by ring
    simp_rw [this]
    have i2 : Integrable (fun x => f x ^ 2 - 2 * c * f x) μ := h2.sub (h1.const_mul _)
    rw [integral_add i2 (integrable_const _), integral_sub h2 (h1.const_mul _),
      integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, ← hc]
    ring
  linarith

section Cen

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem q08s_a_memLp {F : X → X → ℝ} (hF : MemLp (fun z : X × X => F z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun x => ∫ y, F x y ∂μ) 2 μ := by
  have hF2 : Integrable (fun z : X × X => F z.1 z.2 ^ 2) (μ.prod μ) := hF.integrable_sq
  have hm : AEStronglyMeasurable (fun x => ∫ y, F x y ∂μ) μ :=
    hF.aestronglyMeasurable.integral_prod_right'
  rw [memLp_two_iff_integrable_sq hm]
  refine (hF2.integral_prod_left).mono' (hm.pow 2) ?_
  have hs := hF.aestronglyMeasurable.prodMk_left
  filter_upwards [hs, hF2.prod_right_ae] with x h1 h2
  have hmem : MemLp (fun y => F x y) 2 μ := (memLp_two_iff_integrable_sq h1).2 h2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact q08s_sq_integral_le μ hmem

theorem q08s_swap_memLp {F : X → X → ℝ} (hF : MemLp (fun z : X × X => F z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun z : X × X => F z.2 z.1) 2 (μ.prod μ) :=
  hF.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))

theorem q08s_b_memLp {F : X → X → ℝ} (hF : MemLp (fun z : X × X => F z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun y => ∫ x, F x y ∂μ) 2 μ :=
  q08s_a_memLp μ (F := fun x y => F y x) (q08s_swap_memLp μ hF)

theorem q08s_int_b {F : X → X → ℝ} (hF : MemLp (fun z : X × X => F z.1 z.2) 2 (μ.prod μ)) :
    ∫ y, (∫ x, F x y ∂μ) ∂μ = ∫ x, ∫ y, F x y ∂μ ∂μ :=
  (integral_integral_swap (f := F) (hF.integrable one_le_two)).symm

theorem q08s_slice_zero {F : X → X → ℝ} (hF : MemLp (fun z : X × X => F z.1 z.2) 2 (μ.prod μ))
    (P : X → X → ℝ) (hP1 : ∀ x, Integrable (P x) μ) (hP0 : ∀ x, ∫ y, P x y ∂μ = 0) :
    ∀ᵐ x ∂μ, ∫ y, (F x y - (∫ y', F x y' ∂μ) - (∫ x', F x' y ∂μ) +
      (∫ x', ∫ y', F x' y' ∂μ ∂μ) - P x y) ∂μ = 0 := by
  have hFi : Integrable (fun z : X × X => F z.1 z.2) (μ.prod μ) := hF.integrable one_le_two
  have hb : Integrable (fun y => ∫ x, F x y ∂μ) μ := hFi.integral_prod_right
  filter_upwards [hFi.prod_right_ae] with x hx
  set c1 := ∫ y', F x y' ∂μ with hc1
  set m := ∫ x', ∫ y', F x' y' ∂μ ∂μ with hm
  have i1 : Integrable (fun y => F x y - c1) μ := hx.sub (integrable_const _)
  have i2 : Integrable (fun y => F x y - c1 - ∫ x', F x' y ∂μ) μ := i1.sub hb
  have i3 : Integrable (fun y => F x y - c1 - ∫ x', F x' y ∂μ + m) μ := i2.add (integrable_const _)
  rw [integral_sub i3 (hP1 x), integral_add i2 (integrable_const _), integral_sub i1 hb,
    integral_sub hx (integrable_const _), q08s_int_b μ hF, hP0 x]
  simp only [integral_const, probReal_univ, one_smul, sub_zero]
  rw [← hc1, ← hm]; ring

theorem q08s_fst_memLp {α : X → ℝ} (hα : MemLp α 2 μ) :
    MemLp (fun z : X × X => α z.1) 2 (μ.prod μ) := by
  have := q08s_memLp_tensor (μ := μ) (ν := μ) hα (memLp_const (1 : ℝ))
  simpa using this

theorem q08s_snd_memLp {α : X → ℝ} (hα : MemLp α 2 μ) :
    MemLp (fun z : X × X => α z.2) 2 (μ.prod μ) := by
  have := q08s_memLp_tensor (μ := μ) (ν := μ) (memLp_const (1 : ℝ)) hα
  simpa using this

theorem q08s_orth_x {R : X → X → ℝ} (hR : MemLp (fun z : X × X => R z.1 z.2) 2 (μ.prod μ))
    {α : X → ℝ} (hα : MemLp α 2 μ) (hs : ∀ᵐ x ∂μ, ∫ y, R x y ∂μ = 0) :
    ∫ z, R z.1 z.2 * α z.1 ∂(μ.prod μ) = 0 := by
  have hint : Integrable (fun z : X × X => R z.1 z.2 * α z.1) (μ.prod μ) :=
    hR.integrable_mul (q08s_fst_memLp μ hα)
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hs] with x hx
  simp only [Pi.zero_apply]
  rw [integral_mul_const, hx, zero_mul]

theorem q08s_orth_y {R : X → X → ℝ} (hR : MemLp (fun z : X × X => R z.1 z.2) 2 (μ.prod μ))
    {β : X → ℝ} (hβ : MemLp β 2 μ) (hs : ∀ᵐ y ∂μ, ∫ x, R x y ∂μ = 0) :
    ∫ z, R z.1 z.2 * β z.2 ∂(μ.prod μ) = 0 := by
  have hint : Integrable (fun z : X × X => R z.1 z.2 * β z.2) (μ.prod μ) :=
    hR.integrable_mul (q08s_snd_memLp μ hβ)
  rw [integral_prod_symm _ hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hs] with y hy
  simp only [Pi.zero_apply]
  rw [integral_mul_const, hy, zero_mul]

theorem q08s_pyth {R : X → X → ℝ} (hR : MemLp (fun z : X × X => R z.1 z.2) 2 (μ.prod μ))
    {α β : X → ℝ} (hα : MemLp α 2 μ) (hβ : MemLp β 2 μ) (hsx : ∀ᵐ x ∂μ, ∫ y, R x y ∂μ = 0)
    (hsy : ∀ᵐ y ∂μ, ∫ x, R x y ∂μ = 0) :
    ∫ z, R z.1 z.2 ^ 2 ∂(μ.prod μ) ≤ ∫ z, (R z.1 z.2 + α z.1 + β z.2) ^ 2 ∂(μ.prod μ) := by
  have hS : MemLp (fun z : X × X => α z.1 + β z.2) 2 (μ.prod μ) :=
    (q08s_fst_memLp μ hα).add (q08s_snd_memLp μ hβ)
  have i1 : Integrable (fun z : X × X => R z.1 z.2 ^ 2) (μ.prod μ) := hR.integrable_sq
  have i2 : Integrable (fun z : X × X => R z.1 z.2 * α z.1) (μ.prod μ) :=
    hR.integrable_mul (q08s_fst_memLp μ hα)
  have i3 : Integrable (fun z : X × X => R z.1 z.2 * β z.2) (μ.prod μ) :=
    hR.integrable_mul (q08s_snd_memLp μ hβ)
  have i4 : Integrable (fun z : X × X => (α z.1 + β z.2) ^ 2) (μ.prod μ) := hS.integrable_sq
  have e : ∀ z : X × X, (R z.1 z.2 + α z.1 + β z.2) ^ 2 =
      R z.1 z.2 ^ 2 + 2 * (R z.1 z.2 * α z.1) + 2 * (R z.1 z.2 * β z.2) + (α z.1 + β z.2) ^ 2 :=
    fun z => by ring
  simp_rw [e]
  have i23 : Integrable (fun z : X × X => R z.1 z.2 ^ 2 + 2 * (R z.1 z.2 * α z.1)) (μ.prod μ) :=
    i1.add (i2.const_mul 2)
  have i234 : Integrable (fun z : X × X => R z.1 z.2 ^ 2 + 2 * (R z.1 z.2 * α z.1) +
      2 * (R z.1 z.2 * β z.2)) (μ.prod μ) := i23.add (i3.const_mul 2)
  rw [integral_add i234 i4, integral_add i23 (i3.const_mul 2), integral_add i1 (i2.const_mul 2),
    integral_const_mul, integral_const_mul, q08s_orth_x μ hR hα hsx, q08s_orth_y μ hR hβ hsy]
  have : 0 ≤ ∫ z, (α z.1 + β z.2) ^ 2 ∂(μ.prod μ) := integral_nonneg fun _ => sq_nonneg _
  linarith

end Cen


end S7

section S8


variable {X : Type*} [MeasurableSpace X]

/-- `u` extended by the constant function `1` in position `0`. -/
def q08s_ext {L : ℕ} (u : Fin L → X → ℝ) : Fin (L + 1) → X → ℝ :=
  Fin.cons (α := fun _ => X → ℝ) (fun _ => (1 : ℝ)) u

@[simp] theorem q08s_ext_zero {L : ℕ} (u : Fin L → X → ℝ) : q08s_ext u 0 = fun _ => 1 := by
  simp [q08s_ext]

@[simp] theorem q08s_ext_succ {L : ℕ} (u : Fin L → X → ℝ) (i : Fin L) : q08s_ext u i.succ = u i := by
  simp [q08s_ext]

theorem q08s_ext_ortho (μ : Measure X) [IsProbabilityMeasure μ] {L : ℕ} (u : Fin L → X → ℝ)
    (hu : ∀ i, MemLp (u i) 2 μ) (hu0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (huo : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0) (i j : Fin (L + 1)) :
    ∫ x, q08s_ext u i x * q08s_ext u j x ∂μ = if i = j then 1 else 0 := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hu0, (Fin.succ_ne_zero j).symm]
  · simp [hu0, Fin.succ_ne_zero i]
  · simp [huo, Fin.succ_inj]

theorem q08s_ext_memLp (μ : Measure X) [IsProbabilityMeasure μ] {L : ℕ} (u : Fin L → X → ℝ)
    (hu : ∀ i, MemLp (u i) 2 μ) (i : Fin (L + 1)) : MemLp (q08s_ext u i) 2 μ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : X => (1 : ℝ)) 2 μ)
  · simpa using hu i

theorem q08s_sum_split {L : ℕ} (c : Fin (L + 1) × Fin (L + 1) → ℝ) (u : Fin L → X → ℝ) (x y : X) :
    ∑ p : Fin (L + 1) × Fin (L + 1), c p * (q08s_ext u p.1 x * q08s_ext u p.2 y) =
      c (0, 0) + ∑ l : Fin L, c (0, l.succ) * u l y + ∑ j : Fin L, c (j.succ, 0) * u j x +
        ∑ j : Fin L, ∑ l : Fin L, c (j.succ, l.succ) * (u j x * u l y) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, q08s_ext_zero, q08s_ext_succ, mul_one, one_mul, Finset.sum_add_distrib]
  ring


end S8


theorem q08s_sum_tensor {ι κ : Type*} [Fintype ι] [Fintype κ] (f g : ι → κ → ℝ) (x y : κ → ℝ) :
    ∑ i, (∑ j, f i j * x j) * (∑ l, g i l * y l) =
      ∑ j, ∑ l, (∑ i, f i j * g i l) * (x j * y l) := by
  calc ∑ i, (∑ j, f i j * x j) * (∑ l, g i l * y l)
      = ∑ i, ∑ j, ∑ l, (f i j * x j) * (g i l * y l) := by simp_rw [Finset.sum_mul_sum]
    _ = ∑ j, ∑ i, ∑ l, (f i j * x j) * (g i l * y l) := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, (f i j * x j) * (g i l * y l) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ l, (∑ i, f i j * g i l) * (x j * y l) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

section Core

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {L : ℕ} (u : Fin L → X → ℝ)

/-- The finite-rank part `∑ c_ij u_i(x) u_j(y)`. -/
def q08s_P (c : Fin L → Fin L → ℝ) (x y : X) : ℝ := ∑ i, ∑ j, c i j * u i x * u j y

theorem q08s_P_memLp (hu : ∀ i, MemLp (u i) 2 μ) (c : Fin L → Fin L → ℝ) :
    MemLp (fun z : X × X => q08s_P u c z.1 z.2) 2 (μ.prod μ) :=
  memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => by
    have := (q08s_memLp_tensor (hu i) (hu j)).const_mul (c i j)
    simpa [mul_assoc] using this

theorem q08s_P_slice1 (hui : ∀ i, Integrable (u i) μ) (hu0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (c : Fin L → Fin L → ℝ) (x : X) :
    Integrable (fun y => q08s_P u c x y) μ ∧ ∫ y, q08s_P u c x y ∂μ = 0 := by
  constructor
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      have := (hui j).const_mul (c i j * u i x)
      simpa [mul_assoc] using this
  · unfold q08s_P
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      have := (hui j).const_mul (c i j * u i x)
      simpa [mul_assoc] using this]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => by
      have := (hui j).const_mul (c i j * u i x)
      simpa [mul_assoc] using this]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∀ y, c i j * u i x * u j y = (c i j * u i x) * u j y := fun y => rfl
    rw [integral_const_mul, hu0 j, mul_zero]

theorem q08s_P_slice2 (hui : ∀ i, Integrable (u i) μ) (hu0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (c : Fin L → Fin L → ℝ) (x : X) :
    Integrable (fun y => q08s_P u c y x) μ ∧ ∫ y, q08s_P u c y x ∂μ = 0 := by
  constructor
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      have := (hui i).const_mul (c i j * u j x)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · unfold q08s_P
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      have := (hui i).const_mul (c i j * u j x)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => by
      have := (hui i).const_mul (c i j * u j x)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∀ y, c i j * u i y * u j x = (c i j * u j x) * u i y := fun y => by ring
    simp_rw [this]
    rw [integral_const_mul, hu0 i, mul_zero]


theorem q08s_kernel_core (k : X → X → ℝ) (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ))
    (hum : ∀ i, Measurable (u i)) (hub : ∀ i, ∃ M, ∀ x, |u i x| ≤ M)
    (hu0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (huo : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0)
    {ι : Type} [Fintype ι] (a b : ι → X → ℝ)
    (hspa : ∀ i, a i =ᵐ[μ] fun x => (∫ y, a i y ∂μ) + ∑ j, (∫ y, a i y * u j y ∂μ) * u j x)
    (hspb : ∀ i, b i =ᵐ[μ] fun x => (∫ y, b i y ∂μ) + ∑ j, (∫ y, b i y * u j y ∂μ) * u j x)
    {ε : ℝ} (hT : ∫ z, (k z.1 z.2 - ∑ i, a i z.1 * b i z.2) ^ 2 ∂(μ.prod μ) ≤ ε ^ 2) :
    ∫ x, ∫ y, (k x y - ∫ y', k x y' ∂μ - ∫ x', k x' y ∂μ + ∫ x', ∫ y', k x' y' ∂μ ∂μ
        - ∑ i, ∑ j, (∫ x', ∫ y', k x' y' * u i x' * u j y' ∂μ ∂μ) * u i x * u j y) ^ 2 ∂μ ∂μ
      ≤ ε ^ 2 := by
  classical
  set ν := μ.prod μ with hν
  have hu2 : ∀ i, MemLp (u i) 2 μ := fun i => q08s_memLp_of_bdd (hum i) _ (hub i).choose_spec
  have hui : ∀ i, Integrable (u i) μ := fun i => (hu2 i).integrable one_le_two
  set A : X → ℝ := fun x => ∫ y, k x y ∂μ with hA
  set B : X → ℝ := fun y => ∫ x, k x y ∂μ with hB
  set m : ℝ := ∫ x, ∫ y, k x y ∂μ ∂μ with hm
  set c : Fin L → Fin L → ℝ := fun i j => ∫ x', ∫ y', k x' y' * u i x' * u j y' ∂μ ∂μ with hc
  set P := q08s_P u c with hP
  set R : X → X → ℝ := fun x y => k x y - A x - B y + m - P x y with hR
  have hAmem : MemLp A 2 μ := q08s_a_memLp μ hk
  have hBmem : MemLp B 2 μ := q08s_b_memLp μ hk
  set cA : Fin L → ℝ := fun j => ∫ x, A x * u j x ∂μ with hcA
  set cB : Fin L → ℝ := fun l => ∫ y, B y * u l y ∂μ with hcB
  set α : X → ℝ := fun x => A x - m - ∑ j, cA j * u j x with hα
  set β : X → ℝ := fun y => B y - m - ∑ l, cB l * u l y with hβ
  have hαmem : MemLp α 2 μ :=
    (hAmem.sub (memLp_const m)).sub (memLp_finsetSum _ fun j _ => (hu2 j).const_mul _)
  have hβmem : MemLp β 2 μ :=
    (hBmem.sub (memLp_const m)).sub (memLp_finsetSum _ fun j _ => (hu2 j).const_mul _)
  have hRmem : MemLp (fun z : X × X => R z.1 z.2) 2 ν :=
    ((((hk.sub (q08s_fst_memLp μ hAmem)).sub (q08s_snd_memLp μ hBmem)).add
      (memLp_const m)).sub (q08s_P_memLp μ u hu2 c))
  have hsx : ∀ᵐ x ∂μ, ∫ y, R x y ∂μ = 0 :=
    q08s_slice_zero μ hk P (fun x => (q08s_P_slice1 μ u hui hu0 c x).1)
      (fun x => (q08s_P_slice1 μ u hui hu0 c x).2)
  have hsy : ∀ᵐ y ∂μ, ∫ x, R x y ∂μ = 0 := by
    have h1 := q08s_slice_zero μ (F := fun x y => k y x) (q08s_swap_memLp μ hk) (fun x y => P y x)
      (fun x => (q08s_P_slice2 μ u hui hu0 c x).1) (fun x => (q08s_P_slice2 μ u hui hu0 c x).2)
    have hmm : (∫ x', ∫ y', k y' x' ∂μ ∂μ) = m :=
      (integral_integral_swap (f := fun x y => k y x) ((q08s_swap_memLp μ hk).integrable one_le_two)).trans
        rfl
    filter_upwards [h1] with x hx
    beta_reduce at hx
    rw [hmm] at hx
    rw [← hx]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hR, hA, hB]
    ring
  have hpy := q08s_pyth μ hRmem hαmem hβmem hsx hsy
  set e := q08s_ext u with he
  have hext2 : ∀ p, MemLp (e p) 2 μ := q08s_ext_memLp μ u hu2
  have heo := q08s_ext_ortho μ u hu2 hu0 huo
  set w : Fin (L + 1) × Fin (L + 1) → X × X → ℝ := fun p z => e p.1 z.1 * e p.2 z.2 with hw
  have hwm : ∀ p, MemLp (w p) 2 ν := fun p => q08s_memLp_tensor (hext2 p.1) (hext2 p.2)
  have hwo : ∀ p q, ∫ z, w p z * w q z ∂ν = if p = q then 1 else 0 := by
    intro p q
    have : ∀ z : X × X, w p z * w q z = (e p.1 z.1 * e q.1 z.1) * (e p.2 z.2 * e q.2 z.2) :=
      fun z => by simp only [hw]; ring
    simp_rw [this]
    rw [integral_prod_mul (fun x => e p.1 x * e q.1 x) (fun y => e p.2 y * e q.2 y), heo, heo]
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp [h1, h2]
  set αc : ι → Fin (L + 1) → ℝ := fun i j => ∫ y, a i y * e j y ∂μ with hαc
  set βc : ι → Fin (L + 1) → ℝ := fun i j => ∫ y, b i y * e j y ∂μ with hβc
  set d : Fin (L + 1) × Fin (L + 1) → ℝ := fun p => ∑ i, αc i p.1 * βc i p.2 with hd
  have hspa' : ∀ i, a i =ᵐ[μ] fun x => ∑ j, αc i j * e j x := by
    intro i
    refine (hspa i).mono fun x hx => ?_
    show a i x = ∑ j, αc i j * e j x
    rw [hx, Fin.sum_univ_succ]
    simp [hαc, he]
  have hspb' : ∀ i, b i =ᵐ[μ] fun x => ∑ j, βc i j * e j x := by
    intro i
    refine (hspb i).mono fun x hx => ?_
    show b i x = ∑ j, βc i j * e j x
    rw [hx, Fin.sum_univ_succ]
    simp [hβc, he]
  have hae : ∀ᵐ z ∂ν, ∑ i, a i z.1 * b i z.2 = ∑ p, d p * w p z := by
    have h1 : ∀ᵐ z ∂ν, ∀ i, a i z.1 = ∑ j, αc i j * e j z.1 :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun x => ∀ i, a i x = ∑ j, αc i j * e j x)
        (ae_all_iff.2 hspa')
    have h2 : ∀ᵐ z ∂ν, ∀ i, b i z.2 = ∑ j, βc i j * e j z.2 :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun x => ∀ i, b i x = ∑ j, βc i j * e j x)
        (ae_all_iff.2 hspb')
    filter_upwards [h1, h2] with z h1 h2
    calc ∑ i, a i z.1 * b i z.2 = ∑ i, (∑ j, αc i j * e j z.1) * (∑ l, βc i l * e l z.2) :=
          Finset.sum_congr rfl fun i _ => by rw [h1 i, h2 i]
      _ = ∑ p, d p * w p z := by
          rw [q08s_sum_tensor αc βc (fun j => e j z.1) (fun l => e l z.2)]
          simp only [hd, hw, Fintype.sum_prod_type]
  have hint : ∀ p, Integrable (fun z : X × X => k z.1 z.2 * w p z) ν :=
    fun p => hk.integrable_mul (hwm p)
  have hccg : ∀ p, ∫ z, k z.1 z.2 * w p z ∂ν = ∫ x, ∫ y, k x y * (e p.1 x * e p.2 y) ∂μ ∂μ :=
    fun p => integral_prod _ (hint p)
  have hcc00 : ∫ z, k z.1 z.2 * w (0, 0) z ∂ν = m := by
    rw [hccg]; simp [he, hm]
  have hccA : ∀ j : Fin L, ∫ z, k z.1 z.2 * w (j.succ, 0) z ∂ν = cA j := by
    intro j
    rw [hccg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [he, q08s_ext_succ, q08s_ext_zero, mul_one, hcA, hA]
    rw [integral_mul_const]
  have hccB : ∀ l : Fin L, ∫ z, k z.1 z.2 * w (0, l.succ) z ∂ν = cB l := by
    intro l
    rw [hccg]
    simp only [he, q08s_ext_succ, q08s_ext_zero, one_mul]
    have hi : Integrable (Function.uncurry fun x y => k x y * u l y) ν :=
      hk.integrable_mul (q08s_snd_memLp μ (hu2 l))
    rw [integral_integral_swap hi]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hcB, hB]
    rw [integral_mul_const]
  have hccC : ∀ j l : Fin L, ∫ z, k z.1 z.2 * w (j.succ, l.succ) z ∂ν = c j l := by
    intro j l
    rw [hccg]
    simp only [he, q08s_ext_succ, hc]
    refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))
    ring
  have hfull : ∀ z : X × X, ∑ p, (∫ z', k z'.1 z'.2 * w p z' ∂ν) * w p z =
      m + ∑ l, cB l * u l z.2 + ∑ j, cA j * u j z.1 + P z.1 z.2 := by
    intro z
    have h := q08s_sum_split (fun p => ∫ z', k z'.1 z'.2 * w p z' ∂ν) u z.1 z.2
    simp only [hcc00, hccA, hccB, hccC] at h
    have hP' : ∑ x, ∑ x_1, c x x_1 * (u x z.1 * u x_1 z.2) = P z.1 z.2 := by
      simp only [hP, q08s_P]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hP'] at h
    exact h
  have hpm := q08s_proj_min ν w hwm hwo hk d
  have hid : ∀ z : X × X, R z.1 z.2 + α z.1 + β z.2 =
      k z.1 z.2 - ∑ p, (∫ z', k z'.1 z'.2 * w p z' ∂ν) * w p z := by
    intro z
    rw [hfull z]
    simp only [hR, hα, hβ]
    ring
  calc ∫ x, ∫ y, R x y ^ 2 ∂μ ∂μ = ∫ z, R z.1 z.2 ^ 2 ∂ν :=
        (integral_prod (fun z : X × X => R z.1 z.2 ^ 2) hRmem.integrable_sq).symm
    _ ≤ ∫ z, (R z.1 z.2 + α z.1 + β z.2) ^ 2 ∂ν := hpy
    _ = ∫ z, (k z.1 z.2 - ∑ p, (∫ z', k z'.1 z'.2 * w p z' ∂ν) * w p z) ^ 2 ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only
        rw [hid z]
    _ ≤ ∫ z, (k z.1 z.2 - ∑ p, d p * w p z) ^ 2 ∂ν := hpm
    _ = ∫ z, (k z.1 z.2 - ∑ i, a i z.1 * b i z.2) ^ 2 ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with z hz
        rw [hz]
    _ ≤ ε ^ 2 := hT

end Core

theorem q08s_orthonormalize' {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} [Finite ι] (g : ι → X → ℝ) (hg : ∀ s, Measurable (g s) ∧ ∃ M, ∀ x, |g s x| ≤ M) :
    ∃ (L : ℕ) (u : Fin L → X → ℝ), (∀ i, Measurable (u i) ∧ ∃ M, ∀ x, |u i x| ≤ M) ∧
      (∀ i, ∫ x, u i x ∂μ = 0) ∧
      (∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0) ∧
      ∀ s, g s =ᵐ[μ] fun x => (∫ y, g s y ∂μ) + ∑ i, (∫ y, g s y * u i y ∂μ) * u i x := by
  have hint : ∀ s, Integrable (g s) μ := fun s => q08s_integrable_of_bdd (hg s).1 _ (hg s).2.choose_spec
  obtain ⟨L, u, hu, hu0, huo, hspan⟩ := q08s_orthonormalize μ (fun s x => g s x - ∫ y, g s y ∂μ)
    (fun s => ⟨(hg s).1.sub measurable_const, (hg s).2.choose + |∫ y, g s y ∂μ|, fun x => by
      have := (hg s).2.choose_spec x
      calc |g s x - ∫ y, g s y ∂μ| ≤ |g s x| + |∫ y, g s y ∂μ| := abs_sub _ _
        _ ≤ _ := by linarith⟩)
    (fun s => by simp [integral_sub (hint s) (integrable_const _)])
  refine ⟨L, u, hu, hu0, huo, fun s => ?_⟩
  have hui : ∀ i, Integrable (u i) μ := fun i => q08s_integrable_of_bdd (hu i).1 _ (hu i).2.choose_spec
  have hcoef : ∀ i, ∫ y, (g s y - ∫ y', g s y' ∂μ) * u i y ∂μ = ∫ y, g s y * u i y ∂μ := by
    intro i
    have : ∀ y, (g s y - ∫ y', g s y' ∂μ) * u i y = g s y * u i y - (∫ y', g s y' ∂μ) * u i y :=
      fun y => by ring
    simp_rw [this]
    rw [integral_sub, integral_const_mul, hu0 i, mul_zero, sub_zero]
    · exact (q08s_memLp_of_bdd (hg s).1 _ (hg s).2.choose_spec).integrable_mul
        (q08s_memLp_of_bdd (hu i).1 _ (hu i).2.choose_spec)
    · exact (hui i).const_mul _
  filter_upwards [hspan s] with x hx
  simp only [hcoef] at hx
  linarith


theorem q08s_kernel_gens {d : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (k : Torus d → Torus d → ℝ) (hk : MemLp (fun z : Torus d × Torus d => k z.1 z.2) 2 (μ.prod μ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → Torus d → ℝ),
      (∀ i, Measurable (a i) ∧ ∃ M, ∀ x, |a i x| ≤ M) ∧ (∀ i, Measurable (b i) ∧ ∃ M, ∀ x, |b i x| ≤ M) ∧
      ∫ z, (k z.1 z.2 - ∑ i, a i z.1 * b i z.2) ^ 2 ∂(μ.prod μ) ≤ ε ^ 2 := by
  obtain ⟨ι, hι, a, b, hc, hT⟩ := q08s_tensor_dense μ hk hε
  have hbdd : ∀ f : Torus d → ℝ, Continuous f → ∃ M, ∀ x, |f x| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x trivial⟩
  exact ⟨ι, hι, a, b, fun i => ⟨(hc i).1.measurable, hbdd _ (hc i).1⟩,
    fun i => ⟨(hc i).2.measurable, hbdd _ (hc i).2⟩, hT⟩


end Q08sBounded

/-! ### Approximation by bounded orthonormal families

(used by the assembly: the finite-rank approximants must be BOUNDED, because the `e_i` are only
`L²`, and a finite-rank kernel `∑ K_ij e_i ⊗ e_j` with unbounded `e_i` has no uniform exponential
moment for its diagonal term.) -/

/-- For every `ε > 0` there are `L` and bounded measurable, centred, orthonormal (in `L²(μ)`) functions
`u_0, …, u_{L-1}` such that the orthogonal projection `Π` onto their span satisfies
`‖g_c - (Π⊗Π) g_c‖_{L²(μ⊗μ)} ≤ ε`, `‖h_c - (Π⊗Π) h_c‖ ≤ ε` and `‖(φ_a - μ φ_a) - Π(φ_a - μ φ_a)‖ ≤ ε`,
where `k_c(x,y) = k(x,y) - ∫k(x,y')dμ(y') - ∫k(x',y)dμ(x') + ∬k` is the doubly centred kernel and
`(Π⊗Π)k = ∑_{i,j<L} (∬ k u_i u_j) u_i ⊗ u_j`. (Completeness of `(e_i)` in `L²_0`, density of bounded
functions, Gram-Schmidt; the doubly centred kernels lie in `L²(μ⊗μ)` and their coefficient squares
are summable, which is `q08_Kmat_spec`/`q08_Hmat_spec`.) -/
theorem q08_bounded_family (ε : ℝ) (hε : 0 < ε) :
    ∃ (L : ℕ) (u : Fin L → Torus d → ℝ),
      (∀ i, Measurable (u i) ∧ ∃ M, ∀ x, |u i x| ≤ M) ∧
      (∀ i, ∫ x, u i x ∂D.μ = 0) ∧
      (∀ i j, ∫ x, u i x * u j x ∂D.μ = if i = j then 1 else 0) ∧
      (∀ k : Torus d → Torus d → ℝ, (k = (fun x y => periodicRiesz d D.s (x - y)) ∨ k = D.h) →
        ∫ x, ∫ y, (k x y - ∫ y', k x y' ∂D.μ - ∫ x', k x' y ∂D.μ + ∫ x', ∫ y', k x' y' ∂D.μ ∂D.μ
            - ∑ i, ∑ j, (∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) * u i x * u j y) ^ 2
          ∂D.μ ∂D.μ ≤ ε ^ 2) ∧
      (∀ a : Fin D.p,
        ∫ x, (D.φ a x - ∫ x', D.φ a x' ∂D.μ -
          ∑ i, l2Inner D.μ (D.φ a) (u i) * u i x) ^ 2 ∂D.μ ≤ ε ^ 2) := by
  obtain ⟨ι1, h1, a1, b1, ha1, hb1, hT1⟩ := q08s_kernel_gens D.μ
    (fun x y => periodicRiesz d D.s (x - y)) (q08s_g_memLp D) hε
  obtain ⟨ι2, h2, a2, b2, ha2, hb2, hT2⟩ := q08s_kernel_gens D.μ D.h (q08s_h_memLp D) hε
  let G : (((ι1 ⊕ ι1) ⊕ (ι2 ⊕ ι2)) ⊕ Fin D.p) → Torus d → ℝ :=
    Sum.elim (Sum.elim (Sum.elim a1 b1) (Sum.elim a2 b2)) D.φ
  have hG : ∀ s, Measurable (G s) ∧ ∃ M, ∀ x, |G s x| ≤ M := by
    rintro ((( i | i) | (i | i)) | i)
    · exact ha1 i
    · exact hb1 i
    · exact ha2 i
    · exact hb2 i
    · exact D.hφ i
  obtain ⟨L, u, hu, hu0, huo, hspan⟩ := q08s_orthonormalize' D.μ G hG
  refine ⟨L, u, hu, hu0, huo, ?_, ?_⟩
  · intro k hk
    rcases hk with rfl | rfl
    · exact q08s_kernel_core D.μ u _ (q08s_g_memLp D) (fun i => (hu i).1) (fun i => (hu i).2) hu0 huo a1 b1
        (fun i => hspan (Sum.inl (Sum.inl (Sum.inl i))))
        (fun i => hspan (Sum.inl (Sum.inl (Sum.inr i)))) hT1
    · exact q08s_kernel_core D.μ u _ (q08s_h_memLp D) (fun i => (hu i).1) (fun i => (hu i).2) hu0 huo a2 b2
        (fun i => hspan (Sum.inl (Sum.inr (Sum.inl i))))
        (fun i => hspan (Sum.inl (Sum.inr (Sum.inr i)))) hT2
  · intro a
    have := hspan (Sum.inr a)
    have h0 : ∫ x, (D.φ a x - ∫ x', D.φ a x' ∂D.μ -
          ∑ i, l2Inner D.μ (D.φ a) (u i) * u i x) ^ 2 ∂D.μ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [this] with x hx
      simp only [Pi.zero_apply]
      have : D.φ a x - ∫ x', D.φ a x' ∂D.μ - ∑ i, l2Inner D.μ (D.φ a) (u i) * u i x = 0 := by
        have hx' : D.φ a x = (∫ y, D.φ a y ∂D.μ) + ∑ i, (∫ y, D.φ a y * u i y ∂D.μ) * u i x := hx
        unfold l2Inner
        rw [hx']
        ring
      rw [this]; norm_num
    rw [h0]; positivity

end HRS.Q08

end
