import HRS.MC.IID2
import HRS.MC.S7ChaosIIDVocab
import HRS.Equilibrium.ResponseVariance
import HRS.PDE.MeanFieldLinearResponse

/-!
# iid bridge, packet iid2, part B: a covariance factor is a contraction

For `S` with `s7_IsCovFactor d s β ρ e S` (`∑_k S_ik S_jk = C(e_i,e_j)`, `C = susceptibilityCov`) and
`e` an orthonormal basis of `L²_0(ρ dx)`:

* `covFactor_row`: `∀ i, Summable fun k => S i k ^ 2`;
* `covFactor_bound`: `ContrBound S`, that is, for every `L` and `x`, `k ↦ (∑_{i<L} x_i S_ik)²` is summable
  with sum `≤ ∑_{i<L} x_i²`.

Route: `responseInverse` is linear on finite combinations of the `e_i` (`isResponse_sum`, from
`Kop_add_ae`, `Kop_smul` and uniqueness `exists_unique_response`), so `∑_{i,j<L} x_i x_j C(e_i,e_j) =
C(f,f)` for `f = ∑_{i<L} x_i e_i`; then `susceptibilityCov_le_variance` and orthonormality.
-/

open MeasureTheory Filter Topology Finset

noncomputable section

namespace HRS.MC.IID

open HRS

section Linear

variable {d : ℕ} {s β : ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

open HRS.PDE.MFLinear in
/-- The response equation is linear: a combination of responses is the response of the combination. -/
theorem isResponse_comb (H : KS (periodicRiesz d s) ρ Λ) {ψ1 ψ2 h1 h2 : Torus d → ℝ}
    (hψ1 : MemLp ψ1 2 (withDensityReal ρ)) (hψ2 : MemLp ψ2 2 (withDensityReal ρ))
    (hr1 : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ1 h1)
    (hr2 : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ2 h2) (c : ℝ) :
    IsResponse (periodicRiesz d s) (withDensityReal ρ) β (fun x => ψ1 x + c * ψ2 x)
      (fun x => h1 x + c * h2 x) := by
  haveI := H.isProb
  obtain ⟨m1, p1, q1⟩ := hr1
  obtain ⟨m2, p2, q2⟩ := hr2
  have i1 := m1.integrable one_le_two
  have i2 := m2.integrable one_le_two
  have j1 := hψ1.integrable one_le_two
  have j2 := hψ2.integrable one_le_two
  refine ⟨m1.add (m2.const_mul c), ?_, ?_⟩
  · unfold pair at p1 p2 ⊢
    rw [integral_add i1 (i2.const_mul c), integral_const_mul, p1, p2]
    ring
  · have hK := Kop_add_ae H i1 (i2.const_mul c)
    have hs := Kop_smul (g := periodicRiesz d s) (ρ := ρ) c h2
    have hp : ∀ x, projMean (withDensityReal ρ) (fun y => ψ1 y + c * ψ2 y) x =
        projMean (withDensityReal ρ) ψ1 x + c * projMean (withDensityReal ρ) ψ2 x := by
      intro x
      unfold projMean pair
      rw [integral_add j1 (j2.const_mul c), integral_const_mul]
      ring
    filter_upwards [hK, q1, q2] with x hKx e1 e2
    rw [hp x]
    have hsx := congrFun hs x
    linear_combination e1 + c * e2 + β * hKx + β * hsx

open HRS.PDE.MFLinear in
/-- Finite combinations: if `r i` is a response for `e i`, then `∑_{i<L} x_i r_i` is a response for
`∑_{i<L} x_i e_i`. -/
theorem isResponse_sum (H : KS (periodicRiesz d s) ρ Λ) {e r : ℕ → Torus d → ℝ}
    (he : ∀ i, MemLp (e i) 2 (withDensityReal ρ))
    (hr : ∀ i, IsResponse (periodicRiesz d s) (withDensityReal ρ) β (e i) (r i)) (x : ℕ → ℝ)
    (L : ℕ) :
    MemLp (fun t => ∑ i ∈ range L, x i * e i t) 2 (withDensityReal ρ) ∧
      IsResponse (periodicRiesz d s) (withDensityReal ρ) β (fun t => ∑ i ∈ range L, x i * e i t)
        (fun t => ∑ i ∈ range L, x i * r i t) := by
  haveI := H.isProb
  induction L with
  | zero =>
    simp only [range_zero, sum_empty]
    refine ⟨MemLp.zero, MemLp.zero, ?_, ?_⟩
    · simp [pair]
    · refine Filter.Eventually.of_forall fun t => ?_
      simp [Kop, projMean, pair]
  | succ L ih =>
    have e1 : (fun t => ∑ i ∈ range (L + 1), x i * e i t) =
        fun t => (∑ i ∈ range L, x i * e i t) + x L * e L t := by
      funext t; rw [sum_range_succ]
    have e2 : (fun t => ∑ i ∈ range (L + 1), x i * r i t) =
        fun t => (∑ i ∈ range L, x i * r i t) + x L * r L t := by
      funext t; rw [sum_range_succ]
    rw [e1, e2]
    exact ⟨ih.1.add ((he L).const_mul (x L)),
      isResponse_comb H ih.1 (he L) ih.2 (hr L) (x L)⟩

end Linear

section Main

variable {d : ℕ} {s β : ℝ}

/-- `responseInverse` is a.e. any response. -/
theorem responseInverse_ae_of_isResponse (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (hβ : 0 ≤ β)
    (ψ h : Torus d → ℝ) (hψ : MemLp ψ 2 (withDensityReal ρ))
    (hh : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h) :
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ =ᵐ[withDensityReal ρ] h := by
  obtain ⟨h0, hh0, huniq⟩ := exists_unique_response hd hs0 hsd ρ hρ Λ hΛ β hβ ψ hψ
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := ⟨h0, hh0⟩
  have hr : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ) := by
    unfold responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  exact (huniq _ hr).trans (huniq _ hh).symm

/-- `responseInverse ψ` is a response (it exists) -/
theorem isResponse_responseInverse (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (hβ : 0 ≤ β)
    (ψ : Torus d → ℝ) (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ) := by
  obtain ⟨h0, hh0, -⟩ := exists_unique_response hd hs0 hsd ρ hρ Λ hΛ β hβ ψ hψ
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := ⟨h0, hh0⟩
  unfold responseInverse
  rw [dif_pos hex]
  exact hex.choose_spec

/-- `∫ (∑_{i<L} x_i u_i)(∑_{j<L} x_j v_j) = ∑_{i,j<L} x_i x_j ∫ u_i v_j`. -/
theorem integral_comb_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : ℕ → α → ℝ}
    (hu : ∀ i, MemLp (u i) 2 μ) (hv : ∀ i, MemLp (v i) 2 μ) (x : ℕ → ℝ) (L : ℕ) :
    ∫ t, (∑ i ∈ range L, x i * u i t) * (∑ j ∈ range L, x j * v j t) ∂μ =
      ∑ i ∈ range L, ∑ j ∈ range L, x i * x j * ∫ t, u i t * v j t ∂μ := by
  have hint : ∀ i j, Integrable (fun t => u i t * v j t) μ := fun i j => (hu i).integrable_mul (hv j)
  have e1 : ∀ t, (∑ i ∈ range L, x i * u i t) * (∑ j ∈ range L, x j * v j t) =
      ∑ i ∈ range L, ∑ j ∈ range L, x i * x j * (u i t * v j t) := by
    intro t
    rw [sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  simp_rw [e1]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _)]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]
  exact sum_congr rfl fun j _ => integral_const_mul _ _

/-- **The covariance factor has `ℓ²` rows.** -/
theorem covFactor_row {d : ℕ} {s β : ℝ} {ρ : Torus d → ℝ} {e : ℕ → Torus d → ℝ}
    {S : ℕ → ℕ → ℝ} (hS : s7_IsCovFactor d s β ρ e S) (i : ℕ) :
    Summable fun k => S i k ^ 2 :=
  (hS i i).summable.congr fun k => (sq _).symm

/-- **The covariance factor is a contraction** (`‖Sᵀx‖ ≤ ‖x‖`), from `C ≤ I`
(`susceptibilityCov_le_variance`) and orthonormality of `e`. -/
theorem covFactor_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S) :
    ContrBound S := by
  intro L x
  obtain ⟨Λ, -, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hρc : Continuous ρ := PoleCavityAux.continuous_of_smoothPos hρ
  have hprob := hρ.density
  have hgi := (integral_periodicRiesz hd hs0 hsd).1
  have H : PDE.MFLinear.KS (periodicRiesz d s) ρ Λ :=
    ⟨hgi, fun y => periodicRiesz_neg y, hprob, hΛ⟩
  haveI := H.isProb
  set μ := withDensityReal ρ with hμ
  set g := periodicRiesz d s with hg
  -- the responses of the basis
  set r : ℕ → Torus d → ℝ := fun j => responseInverse g μ β (e j) with hr
  have hrr : ∀ j, IsResponse g μ β (e j) (r j) := fun j =>
    isResponse_responseInverse hd hs0 hsd ρ hprob Λ hΛ hβ.le (e j) (he.memLp j)
  have hrm : ∀ j, MemLp (r j) 2 μ := fun j => (hrr j).1
  -- the covariance matrix entries
  have hP : ∀ i, projMean μ (e i) = e i := fun i => by
    funext t; simp [projMean, pair, he.centered i]
  have hC : ∀ i j, susceptibilityCov g μ β (e i) (e j) = ∫ t, e i t * r j t ∂μ := by
    intro i j
    unfold susceptibilityCov l2Inner
    rw [hP i]
  -- the combination
  set f : Torus d → ℝ := fun t => ∑ i ∈ range L, x i * e i t with hf
  set h : Torus d → ℝ := fun t => ∑ i ∈ range L, x i * r i t with hh
  obtain ⟨hfm, hfr⟩ := isResponse_sum H he.memLp hrr x L
  have hfP : projMean μ f = f := by
    funext t
    have : pair μ f = 0 := by
      unfold pair
      rw [hf]
      rw [integral_finset_sum _ (fun i _ => ((he.memLp i).integrable one_le_two).const_mul _)]
      refine sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, he.centered i, mul_zero]
    simp [projMean, this]
  have hae : responseInverse g μ β f =ᵐ[μ] h :=
    responseInverse_ae_of_isResponse hd hs0 hsd ρ hprob Λ hΛ hβ.le f h hfm hfr
  -- the quadratic form
  have hQ1 : susceptibilityCov g μ β f f = ∫ t, f t * h t ∂μ := by
    unfold susceptibilityCov l2Inner
    rw [hfP]
    exact integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  have hQ : susceptibilityCov g μ β f f =
      ∑ i ∈ range L, ∑ j ∈ range L, x i * x j * susceptibilityCov g μ β (e i) (e j) := by
    rw [hQ1, hf, hh, integral_comb_mul he.memLp hrm x L]
    simp_rw [hC]
  have hV : l2Inner μ (projMean μ f) (projMean μ f) = ∑ i ∈ range L, x i ^ 2 := by
    unfold l2Inner
    rw [hfP, hf]
    rw [integral_comb_mul he.memLp he.memLp x L]
    have := he.orthonormal
    unfold l2Inner at this
    simp_rw [this]
    refine sum_congr rfl fun i hi => ?_
    have hi := mem_range.1 hi
    simp [sq, mul_ite, hi]
  have hle := susceptibilityCov_le_variance hd hs0 hsd ρ hprob Λ hΛ β hβ.le f hfm
  -- the series identity
  have hser : HasSum (fun k => (∑ i ∈ range L, x i * S i k) ^ 2)
      (∑ i ∈ range L, ∑ j ∈ range L, x i * x j * susceptibilityCov g μ β (e i) (e j)) := by
    have : (fun k => (∑ i ∈ range L, x i * S i k) ^ 2) =
        fun k => ∑ i ∈ range L, ∑ j ∈ range L, x i * x j * (S i k * S j k) := by
      funext k
      rw [sq, sum_mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [this]
    exact hasSum_sum fun i _ => hasSum_sum fun j _ => (hS i j).mul_left (x i * x j)
  refine ⟨hser.summable, ?_⟩
  rw [hser.tsum_eq, ← hQ, ← hV]
  exact hle

end Main

end HRS.MC.IID
