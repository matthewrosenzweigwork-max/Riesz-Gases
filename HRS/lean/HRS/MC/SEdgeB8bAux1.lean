import HRS.MC.SEdgeVocab
import HRS.Equilibrium.QuadraticLimit.Spectral

/-!
# Packet B8b, helper file 1: the abstract Hilbert-space part

Prefix `b8b_`.  For the abstract response data `q08s_Abs one K β E U` and a pair `(w, u)` with
`u + β P K u = P w`, `⟨one, u⟩ = 0`, we prove the truncation statements needed for the Wick IBP limit.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS.Q08 HRS.ResponseAux InnerProductSpace

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {one : H} {K : H →L[ℝ] H} {β : ℝ} {E U : ℕ → H}

/-- finite Fourier projection onto `E 0, ..., E (L-1)`. -/
def b8b_Pi (E : ℕ → H) (L : ℕ) (v : H) : H :=
  ∑ i ∈ Finset.range L, inner ℝ (E i) v • E i

/-- `Y_L = ∑_{k<L} ⟨E k, w⟩ U k`. -/
def b8b_Y (E U : ℕ → H) (w : H) (L : ℕ) : H :=
  ∑ k ∈ Finset.range L, inner ℝ (E k) w • U k

theorem b8b_sa (A : q08s_Abs one K β E U) {y u a b : H} (hy : inner ℝ one y = 0)
    (hu : inner ℝ one u = 0) (ha : y + β • projL one (K y) = a)
    (hb : u + β • projL one (K u) = b) : inner ℝ a u = inner ℝ y b := by
  have hPy : projL one y = y := (projL_eq_self_iff A.hone).2 hy
  have hPu : projL one u = u := (projL_eq_self_iff A.hone).2 hu
  subst ha hb
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_projL_left, hPu, ← inner_projL_left, hPy]
  have h1 : inner ℝ (K y) u = inner ℝ y (K u) := by
    rw [A.hKsa y u, real_inner_comm]
  rw [h1]

theorem b8b_stab (A : q08s_Abs one K β E U) {z δ : H} (hz : inner ℝ one z = 0)
    (hzd : z + β • projL one (K z) = δ) : ‖z‖ ≤ ‖δ‖ := by
  have hPz : projL one z = z := (projL_eq_self_iff A.hone).2 hz
  have h1 : inner ℝ δ z = inner ℝ z z + β * inner ℝ (K z) z := by
    rw [← hzd, inner_add_left, real_inner_smul_left, inner_projL_left, hPz]
  have h2 : ‖z‖ * ‖z‖ ≤ ‖δ‖ * ‖z‖ := by
    have h3 : ‖z‖ * ‖z‖ ≤ inner ℝ δ z := by
      rw [h1, real_inner_self_eq_norm_sq]
      nlinarith [mul_nonneg A.hβ (A.hKnn z)]
    exact h3.trans ((real_inner_le_norm δ z))
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h2 h0

theorem b8b_Pi_sub (L : ℕ) (x y : H) : b8b_Pi E L (x - y) = b8b_Pi E L x - b8b_Pi E L y := by
  unfold b8b_Pi
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right, sub_smul]

theorem b8b_Pi_norm_le (A : q08s_Abs one K β E U) (L : ℕ) (x : H) : ‖b8b_Pi E L x‖ ≤ ‖x‖ := by
  have h1 := q08s_E_sq A L (fun i => inner ℝ (E i) x)
  have h2 := A.hEon.sum_inner_products_le (s := Finset.range L) x
  have h3 : ‖b8b_Pi E L x‖ ^ 2 = ∑ i ∈ Finset.range L, inner ℝ (E i) x ^ 2 := by
    rw [h1, b8b_Pi, real_inner_self_eq_norm_sq]
  have h4 : ∑ i ∈ Finset.range L, inner ℝ (E i) x ^ 2 ≤ ‖x‖ ^ 2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) h2
    simp [Real.norm_eq_abs, sq_abs]
  have : ‖b8b_Pi E L x‖ ^ 2 ≤ ‖x‖ ^ 2 := h3 ▸ h4
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem b8b_Pi_tendsto (A : q08s_Abs one K β E U) {x : H} (hx : inner ℝ one x = 0) :
    Tendsto (fun L => b8b_Pi E L x) atTop (𝓝 x) :=
  (q08s_expand A x hx).tendsto_sum_nat

theorem b8b_Pi_proj_tendsto (A : q08s_Abs one K β E U) (w : H) :
    Tendsto (fun L => b8b_Pi E L w) atTop (𝓝 (projL one w)) := by
  have h := b8b_Pi_tendsto A (inner_one_projL A.hone w)
  have hE : ∀ i, inner ℝ (E i) (projL one w) = inner ℝ (E i) w := by
    intro i
    have hPE : projL one (E i) = E i := (projL_eq_self_iff A.hone).2 (A.hE0 i)
    rw [← inner_projL_left, hPE]
  simpa [b8b_Pi, hE] using h

theorem b8b_Y_eq (A : q08s_Abs one K β E U) (w : H) (L : ℕ) :
    b8b_Y E U w L + β • projL one (K (b8b_Y E U w L)) = b8b_Pi E L w := by
  exact q08s_Uv A (fun k => inner ℝ (E k) w) L

theorem b8b_Y_inner_one (A : q08s_Abs one K β E U) (w : H) (L : ℕ) :
    inner ℝ one (b8b_Y E U w L) = 0 := by
  have := q08s_PUv A (fun k => inner ℝ (E k) w) L
  have h2 : projL one (b8b_Y E U w L) = b8b_Y E U w L := this
  rw [← h2]
  exact inner_one_projL A.hone _

theorem b8b_Y_tendsto (A : q08s_Abs one K β E U) {w u : H} (hu0 : inner ℝ one u = 0)
    (hueq : u + β • projL one (K u) = projL one w) :
    Tendsto (fun L => b8b_Y E U w L) atTop (𝓝 u) := by
  have hX := b8b_Pi_proj_tendsto A (E := E) (U := U) (K := K) (β := β) w
  have hbound : ∀ L, ‖b8b_Y E U w L - u‖ ≤ ‖b8b_Pi E L w - projL one w‖ := by
    intro L
    refine b8b_stab A (z := b8b_Y E U w L - u) (δ := b8b_Pi E L w - projL one w) ?_ ?_
    · rw [inner_sub_right, b8b_Y_inner_one A, hu0]; simp
    · rw [map_sub, map_sub, smul_sub, ← b8b_Y_eq A w L, ← hueq]; abel
  rw [tendsto_iff_norm_sub_tendsto_zero] at hX ⊢
  exact squeeze_zero (fun L => norm_nonneg _) hbound hX

theorem b8b_inner_E_Y (A : q08s_Abs one K β E U) (w : H) (L i : ℕ) :
    inner ℝ (b8b_Pi E L w) (U i) = inner ℝ (b8b_Y E U w L) (E i) := by
  refine b8b_sa A (y := b8b_Y E U w L) (u := U i) (b := E i) ?_ (A.hU0 i) (b8b_Y_eq A w L)
    (A.hUeq i)
  exact b8b_Y_inner_one A w L

theorem b8b_inner_E_u (A : q08s_Abs one K β E U) {w u : H} (hu0 : inner ℝ one u = 0)
    (hueq : u + β • projL one (K u) = projL one w) (i : ℕ) :
    inner ℝ (projL one w) (U i) = inner ℝ u (E i) :=
  b8b_sa A hu0 (A.hU0 i) hueq (A.hUeq i)

/-- the vector `∑_{i<L} t_i E_i` with `t_i = ⟨X_L, U_i⟩` converges to `u`. -/
theorem b8b_PiY_tendsto (A : q08s_Abs one K β E U) {w u : H} (hu0 : inner ℝ one u = 0)
    (hueq : u + β • projL one (K u) = projL one w) :
    Tendsto (fun L => ∑ i ∈ Finset.range L, inner ℝ (b8b_Pi E L w) (U i) • E i) atTop (𝓝 u) := by
  have hY := b8b_Y_tendsto A hu0 hueq (E := E) (U := U) (w := w)
  have hP := b8b_Pi_tendsto A hu0 (E := E) (U := U) (K := K) (β := β)
  have e1 : ∀ L, ∑ i ∈ Finset.range L, inner ℝ (b8b_Pi E L w) (U i) • E i =
      b8b_Pi E L (b8b_Y E U w L) := by
    intro L
    conv_rhs => rw [b8b_Pi]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [b8b_inner_E_Y A w L i, real_inner_comm]
  simp_rw [e1]
  rw [tendsto_iff_norm_sub_tendsto_zero] at hY hP ⊢
  have hb : ∀ L, ‖b8b_Pi E L (b8b_Y E U w L) - u‖ ≤
      ‖b8b_Y E U w L - u‖ + ‖b8b_Pi E L u - u‖ := by
    intro L
    have : b8b_Pi E L (b8b_Y E U w L) - u =
        b8b_Pi E L (b8b_Y E U w L - u) + (b8b_Pi E L u - u) := by
      rw [b8b_Pi_sub]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    exact add_le_add (b8b_Pi_norm_le A L _) le_rfl
  refine squeeze_zero (fun L => norm_nonneg _) hb ?_
  simpa using hY.add hP

end Abstract


section Concrete

variable {d : ℕ} (D : Q08Data d)

/-- `L²` inner product as an integral -/
theorem b8b_inner_eq {X : Type*} [MeasurableSpace X] {ν : Measure X} (f g : Lp ℝ 2 ν) :
    inner ℝ f g = ∫ x, f x * g x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-- the response to a square-integrable source -/
theorem b8b_resp {ψ : Torus d → ℝ} (hψ : MemLp ψ 2 (withDensityReal D.ρ)) :
    IsResponse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β ψ
      (responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β ψ) := by
  obtain ⟨h, hh, _⟩ := exists_unique_respEq (q08s_setup D) D.hβ.le hψ
  have hex' : ∃ h, IsResponse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β ψ h := ⟨h, hh⟩
  unfold responseInverse
  rw [dif_pos hex']
  exact hex'.choose_spec

theorem b8b_resp_hyp {ψ : Torus d → ℝ} (hψ : MemLp ψ 2 (withDensityReal D.ρ)) :
    inner ℝ (oneL D.hρ.density) ((b8b_resp D hψ).1.toLp _) = 0 ∧
    (b8b_resp D hψ).1.toLp _ + D.β • projL (oneL D.hρ.density)
        (KL (q08s_setup D) ((b8b_resp D hψ).1.toLp _)) =
      projL (oneL D.hρ.density) (hψ.toLp ψ) := by
  have hρ := D.hρ.density
  haveI : IsProbabilityMeasure (withDensityReal D.ρ) := isProbabilityMeasure_dens hρ
  have hresp := b8b_resp D hψ
  set u := hresp.1.toLp (responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β ψ) with hu
  obtain ⟨hP, hT⟩ := (respEq_iff (q08s_setup D) D.β hψ hresp.1).1 hresp
  refine ⟨?_, ?_⟩
  · rw [inner_oneL hρ, integral_congr_ae hresp.1.coeFn_toLp]
    exact hresp.2.1
  · rw [Top_apply, hP] at hT
    exact hT

/-- `C(φ,ψ) = ⟨P φ, R ψ⟩` in `L²(μ)` -/
theorem b8b_cov_eq {φ ψ : Torus d → ℝ} (hφ : MemLp φ 2 (withDensityReal D.ρ))
    (hψ : MemLp ψ 2 (withDensityReal D.ρ)) :
    susceptibilityCov (periodicRiesz d D.s) (withDensityReal D.ρ) D.β φ ψ =
      inner ℝ (projL (oneL D.hρ.density) (hφ.toLp φ)) ((b8b_resp D hψ).1.toLp _) := by
  have hρ := D.hρ.density
  rw [b8b_inner_eq]
  unfold susceptibilityCov l2Inner projMean pair
  have hr := (b8b_resp D hψ).1.coeFn_toLp
  have hw := projL_coe hρ (hφ.toLp φ)
  have hwint : ∫ y, (hφ.toLp φ : Torus d → ℝ) y ∂(withDensityReal D.ρ) =
      ∫ y, φ y ∂(withDensityReal D.ρ) := integral_congr_ae hφ.coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [hr, hw, hφ.coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, hwint, h3]

/-- `⟨e_k, φ⟩ = ∫ φ e_k` -/
theorem b8b_coef_eq {φ : Torus d → ℝ} (hφ : MemLp φ 2 (withDensityReal D.ρ)) (k : ℕ) :
    l2Inner (withDensityReal D.ρ) φ (D.e k) = inner ℝ (q08s_E D k) (hφ.toLp φ) := by
  rw [q08s_inner_E D k]
  unfold l2Inner
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]

end Concrete

end HRS.MC.SEdge.B8b
