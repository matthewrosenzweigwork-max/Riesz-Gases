import HRS.MS.WlCavAux1

/-!
# HRS.MS.WlCavAux2 -- cavity ensemble of `Q_N`, exact first marginal, weighted sup bound, pole densities (WL-6, part 2)

Packet WL-6 of `docs/WR_LOG_PLAN.md` (Step 8 of the proof of `r2_log_static`).  Infrastructure lemmas, not manuscript
rows.  Namespace `HRS.MS.Wl`, helper prefix `wl6_`.  Builds on `WlCavAux1` (generic layer) and `WlEnsAux1-2`
(`wl_Q_eq_fieldLaw`, `wlFamField`, `wl_isField_family`).

Standing notation: `μ = withDensityReal ρ`, `K = sphericalLogKernel`, `ℓ = logWeight`, `λ = β/N`,
`ψ = wl_Qfield μ β N = β rowIntE K μ + h_N`, `h_N = wl_hN β N = -(β/N) ℓ`.

* **Cavity and pole ensembles** (`V`-free): `wl_cavLaw μ β N n = wl6_law μ K ψ λ n` (the cavity law `P_n^0`, `n = N-1`
  free particles) and `wl_poleLaw μ β N n t x = wl6_law μ K (ψ - t λ K(·,x)) λ n` (the pole ensemble `P_n^{x,t}`, the
  tilt of `P_n^0` by `exp(-tλ ∑ K(x,y_i))`).  `wl_pole_eq_fam`: a pole ensemble is a member of the family
  `wlFamField` of `WlEnsAux2` (one pole, weight `t`, `v = 0`).
* `wl_theta μ β N x = e^{β Kμ(x)} e^{h_N(x)} Φ_x / Z` with `Φ_x = wl_cavPhi ≤ 1` and `Z = wl_cavZ`.
* `wl_density_sup` (bundle): `firstMarginal Q = μ.withDensity θ` (exact), `0 ≤ Φ_x ≤ 1`, `Z ≥ C⁻¹`, `θ` measurable and
  `θ x ≤ C (1+‖x‖²)^{-(β/(2N))}` for every `x`, uniformly in `ρ, β ∈ [0, βp], N ≥ 2` (the new weighted third clause of
  `HasLogMarginalDensityBounds`), and `firstMarginal Q ≤ C • μ`.
* `wl_cavity_disintegration`: `∫ F(X 0, tail X) dQ_N = ∫ ∫ F(x, Y) d(P_n^{x,1}) dπ_N(x)`;
  `wl_cavity_mixture`: the identity for one-point marginals obtained from `pinned_marginal_succ`, with the exact
  mixing weight `θ`.
* `wl_pole_bundle`: for the whole family `ψ_fam = β Kμ - λℓ + v - λ ∑ t_b K(·, z_b)` (`t_b ≥ 0`, `∑ t_b ≤ T`,
  `|v| ≤ b0`): the one-particle marginal of `m+1 ≤ N` particles is `≤ C μ` with the retained factors `e^{h_N(x)}` and
  `e^{-λ ∑ t_b K(x,z_b)}`, and the two-particle marginal of `m+2 ≤ N` particles is `≤ C μ ⊗ μ` with the retained factors
  `e^{h_N(x)+h_N(y)}`, the pole factors and the pair factor `e^{-λ K(x,y)}`.

Statement adjustments (all harmless, documented): `β` ranges over `[0, βp]` (the proofs only use `β ≥ 0`); the
bound `Z ≥ e^{-C}` of the sketch is stated as `C⁻¹ ≤ Z` with the same `C` as the sup bound; the pole constants
depend on the additional parameters `T, b0` (total pole weight, size of `v`); the weights `t_b` need only be
nonnegative.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.External HRS.MS.Wr

/-! ### Generic comparison lemmas for measures -/

section Comp

variable {α : Type*} [MeasurableSpace α]

/-- `f ≤ c g` pointwise gives `ν.withDensity f ≤ c • ν.withDensity g`. -/
lemma wl6_withDensity_le_smul {ν : Measure α} {f g : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ x, f x ≤ c * g x) : ν.withDensity f ≤ c • ν.withDensity g := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA,
    ← lintegral_const_mul' _ _ hc]
  exact lintegral_mono fun x => h x

/-- Transitivity of domination by multiples. -/
lemma wl6_le_smul_trans {ν₁ ν₂ ν₃ : Measure α} {c₁ c₂ c : ℝ≥0∞} (h1 : ν₁ ≤ c₁ • ν₂)
    (h2 : ν₂ ≤ c₂ • ν₃) (hc : c₁ * c₂ ≤ c) : ν₁ ≤ c • ν₃ := by
  refine Measure.le_iff'.2 fun s => ?_
  have a1 := Measure.le_iff'.1 h1 s
  have a2 := Measure.le_iff'.1 h2 s
  simp only [Measure.smul_apply, smul_eq_mul] at a1 a2 ⊢
  calc ν₁ s ≤ c₁ * ν₂ s := a1
    _ ≤ c₁ * (c₂ * ν₃ s) := mul_le_mul' le_rfl a2
    _ = (c₁ * c₂) * ν₃ s := (mul_assoc _ _ _).symm
    _ ≤ c * ν₃ s := mul_le_mul' hc le_rfl

end Comp

/-! ### The ensembles of `Q_N` -/

section Rho

variable {d : ℕ}

/-- The kernel `K = sphericalLogKernel` as a function of two points. -/
abbrev wl6_K : Euc d → Euc d → ℝ := fun x y => sphericalLogKernel x y

/-- The one-body field `h_N = -(β/N) ℓ`. -/
def wl_hN (β : ℝ) (N : ℕ) (x : Euc d) : ℝ := -(β / (N : ℝ)) * logWeight x

lemma wl_Qfield_eq (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) (x : Euc d) :
    wl_Qfield μ β N x = β * rowIntE wl6_K μ x + wl_hN β N x := by
  unfold wl_Qfield wl_hN
  ring

/-- `Φ_x = N_{N-1}(pole at x) / N_{N-1}`. -/
def wl_cavPhi (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) (x : Euc d) : ℝ :=
  wl6_Phi μ wl6_K (wl_Qfield μ β N) (β / N) (N - 1) x

/-- `Z = N_N / N_{N-1}`. -/
def wl_cavZ (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) : ℝ :=
  wl6_Z μ wl6_K (wl_Qfield μ β N) (β / N) (N - 1)

/-- `θ(x) = e^{β Kμ(x)} e^{h_N(x)} Φ_x / Z`. -/
def wl_theta (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) (x : Euc d) : ℝ :=
  Real.exp (β * rowIntE wl6_K μ x) * Real.exp (wl_hN β N x) * wl_cavPhi μ β N x / wl_cavZ μ β N

/-- The cavity law `P_n^0` (`n` free particles, coupling `β/N`). -/
def wl_cavLaw (μ : Measure (Euc d)) (β : ℝ) (N n : ℕ) : Measure (Fin n → Euc d) :=
  wl6_law μ wl6_K (wl_Qfield μ β N) (β / N) n

/-- The pole ensemble `P_n^{x,t}`: the cavity law tilted by `exp(-t (β/N) ∑ K(x, y_i))`. -/
def wl_poleLaw (μ : Measure (Euc d)) (β : ℝ) (N n : ℕ) (t : ℝ) (x : Euc d) : Measure (Fin n → Euc d) :=
  wl6_law μ wl6_K (wl6_pole wl6_K (wl_Qfield μ β N) (t * (β / N)) x) (β / N) n

lemma wl_theta_eq (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) (x : Euc d) :
    wl_theta μ β N x = wl6_theta μ wl6_K (wl_Qfield μ β N) (β / N) (N - 1) x := by
  unfold wl_theta wl6_theta wl_cavPhi wl_cavZ
  rw [wl_Qfield_eq, Real.exp_add]

/-- A pole ensemble is a member of the family `wlFamField` (one pole at `x` of weight `t`, `v = 0`). -/
lemma wl_pole_eq_fam (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) (t : ℝ) (x : Euc d) :
    wl6_pole wl6_K (wl_Qfield μ β N) (t * (β / N)) x =
      wlFamField μ wl6_K β N logWeight (fun _ => 0) (fun _ : Unit => t) (fun _ => x) := by
  funext z
  simp only [wl6_pole, wl_Qfield, wlFamField, Finset.univ_unique, Finset.sum_singleton]
  ring

lemma wl6_exp_neg_logWeight (β : ℝ) (N : ℕ) (x : Euc d) :
    Real.exp (-(β / (N : ℝ)) * logWeight x) = (1 + ‖x‖ ^ 2) ^ (-(β / (2 * (N : ℝ)))) := by
  unfold logWeight
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

lemma wl6_firstMarginal_def (n : ℕ) (Q : Measure (HRS.Whole.EucConfig d (n + 1))) :
    HRS.Whole.firstMarginal Q = Q.map (fun X : HRS.Whole.EucConfig d (n + 1) => X 0) := by
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (Nat.succ_pos n)]
  rfl

/-! ### The exact first marginal and the weighted sup bound -/

/-- **`wl_density_sup`** (bundle).  For `d ≥ 2`, `βp ≥ 0`, `A` there is one constant `C ≥ 1` (quantified before
`ρ, β, N`) such that for every probability density `ρ` with `HasSphericalBound A ρ`, every `β ∈ [0, βp]` and every
`N ≥ 2`, with `μ = ρ dx` and `Q = HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ`:
`HRS.Whole.firstMarginal Q = μ.withDensity θ` with `θ = wl_theta` measurable, `θ(x) = e^{β Kμ(x)} e^{h_N(x)} Φ_x / Z`,
`0 ≤ Φ_x ≤ 1`, `Z ≥ C⁻¹`, and `0 ≤ θ(x) ≤ C (1+‖x‖²)^{-(β/(2N))}` for every `x`; in particular
`HRS.Whole.firstMarginal Q ≤ C • μ`. -/
theorem wl_density_sup (hd : 2 ≤ d) (βp A : ℝ) (hβp : 0 ≤ βp) : ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 ≤ β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
      Measurable (wl_theta (HRS.Whole.withDensityReal ρ) β N) ∧
      HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) =
        (HRS.Whole.withDensityReal ρ).withDensity
          (fun x => ENNReal.ofReal (wl_theta (HRS.Whole.withDensityReal ρ) β N x)) ∧
      (∀ x, 0 ≤ wl_cavPhi (HRS.Whole.withDensityReal ρ) β N x ∧ wl_cavPhi (HRS.Whole.withDensityReal ρ) β N x ≤ 1) ∧
      C⁻¹ ≤ wl_cavZ (HRS.Whole.withDensityReal ρ) β N ∧
      (∀ x, 0 ≤ wl_theta (HRS.Whole.withDensityReal ρ) β N x ∧
        wl_theta (HRS.Whole.withDensityReal ρ) β N x ≤ C * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * (N : ℝ))))) ∧
      HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal C • HRS.Whole.withDensityReal ρ := by
  obtain ⟨C0, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  set Clp : ℝ := max Cl 0 with hClp
  have hClp0 : 0 ≤ Clp := le_max_right _ _
  set Λ : ℝ := βp * (2 * C0 + Clp) with hΛ
  have hΛ0 : 0 ≤ Λ := mul_nonneg hβp (by linarith)
  refine ⟨Real.exp Λ, Real.one_le_exp hΛ0, fun ρ hρ hA β hβ hβp' N hN => ?_⟩
  have := wl_isProb hρ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨hK, hℓ, hℓle, hfield, hQ⟩ := h ρ hρ hA β hβ (n + 1) (by omega)
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set V : WeakPotential μ := wlPot hK hC0 hfield with hV
  have hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ C0 := fun x => hK.wr1_rowInt_le hC0 x
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hQeq := hQ V rfl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hE : β * Cl / ((n + 1 : ℕ) : ℝ) + β / ((n + 1 : ℕ) : ℝ) * n * C0 ≤ βp * (C0 + Clp) := by
    have h1 : β * Cl / ((n + 1 : ℕ) : ℝ) ≤ β * Clp := by
      rw [div_le_iff₀ hnn]
      push_cast
      have a : β * Cl ≤ β * Clp := mul_le_mul_of_nonneg_left (le_max_left _ _) hβ
      have b : 0 ≤ β * Clp := mul_nonneg hβ hClp0
      nlinarith [mul_nonneg b hn0]
    have h2 : β / ((n + 1 : ℕ) : ℝ) * n ≤ β := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hnn]
      push_cast
      nlinarith
    have h3 : β / ((n + 1 : ℕ) : ℝ) * n * C0 ≤ β * C0 := mul_le_mul_of_nonneg_right h2 hC0
    have h4 : β * Clp + β * C0 ≤ βp * (C0 + Clp) := by
      nlinarith [mul_le_mul_of_nonneg_right hβp' (add_nonneg hC0 hClp0)]
    linarith
  have hθfun : wl_theta μ β (n + 1) = wl6_theta μ V.q (wl_Qfield μ β (n + 1))
      (β / ((n + 1 : ℕ) : ℝ)) n := funext fun x => wl_theta_eq μ β (n + 1) x
  have hZ := wl6_Z_ge V hfield hlam hrow n
  have hZ' : Real.exp (-(βp * (C0 + Clp))) ≤ wl_cavZ μ β (n + 1) :=
    le_trans (Real.exp_le_exp.2 (by linarith)) hZ
  have hfm : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ) =
      (fieldLaw V (wl_Qfield μ β (n + 1)) (β / ((n + 1 : ℕ) : ℝ)) (n + 1)).map (fun X => X 0) := by
    rw [hQeq, wl6_firstMarginal_def]
  have hdens : wl6_dens μ V.q (wl_Qfield μ β (n + 1)) (β / ((n + 1 : ℕ) : ℝ)) n =
      fun x => ENNReal.ofReal (wl_theta μ β (n + 1) x) :=
    funext fun x => by rw [wl6_dens_eq_theta V hfield hlam, hθfun]
  have hfm2 : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ) =
      μ.withDensity (fun x => ENNReal.ofReal (wl_theta μ β (n + 1) x)) := by
    rw [hfm, wl6_marginal_zero V hfield hlam hrow n, hdens]
  have hsup : ∀ x, 0 ≤ wl_theta μ β (n + 1) x ∧
      wl_theta μ β (n + 1) x ≤ Real.exp Λ * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * ((n + 1 : ℕ) : ℝ)))) := by
    intro x
    refine ⟨by rw [hθfun]; exact wl6_theta_nonneg V hfield hlam n x, ?_⟩
    rw [hθfun, ← wl6_exp_neg_logWeight β (n + 1) x]
    refine (wl6_theta_le V hfield hlam hrow n x).trans ?_
    have hψx : wl_Qfield μ β (n + 1) x ≤ β * C0 + (-(β / ((n + 1 : ℕ) : ℝ)) * logWeight x) := by
      rw [wl_Qfield_eq]
      unfold wl_hN
      have := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le hC0 x) hβ
      linarith
    rw [← Real.exp_add, ← Real.exp_add]
    have : β * C0 + -(β / ((n + 1 : ℕ) : ℝ)) * logWeight x +
        (β * Cl / ((n + 1 : ℕ) : ℝ) + β / ((n + 1 : ℕ) : ℝ) * n * C0) ≤ Λ + -(β / ((n + 1 : ℕ) : ℝ)) * logWeight x := by
      have := mul_le_mul_of_nonneg_right hβp' hC0
      rw [hΛ]
      nlinarith
    calc Real.exp (wl_Qfield μ β (n + 1) x + (β * Cl / ((n + 1 : ℕ) : ℝ) + β / ((n + 1 : ℕ) : ℝ) * n * C0))
        ≤ Real.exp (Λ + -(β / ((n + 1 : ℕ) : ℝ)) * logWeight x) :=
          Real.exp_le_exp.2 (by linarith)
      _ = _ := by rw [Real.exp_add]
  have hmeas : Measurable (wl_theta μ β (n + 1)) := by
    rw [hθfun]; exact wl6_measurable_theta V hfield.measurable _ n
  have hCinv : (Real.exp Λ)⁻¹ ≤ wl_cavZ μ β (n + 1) := by
    rw [← Real.exp_neg]
    refine le_trans (Real.exp_le_exp.2 ?_) hZ'
    rw [hΛ]
    nlinarith
  have hle : HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β μ) ≤
      ENNReal.ofReal (Real.exp Λ) • μ := by
    rw [hfm2]
    refine Measure.le_iff.2 fun A hA => ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    refine (hsup x).2.trans ?_
    have hr : (1 + ‖x‖ ^ 2) ^ (-(β / (2 * ((n + 1 : ℕ) : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
        (neg_nonpos.2 (div_nonneg hβ (by positivity)))
    nlinarith [Real.exp_pos Λ]
  refine ⟨hmeas, hfm2, fun x => ⟨?_, ?_⟩, hCinv, hsup, hle⟩
  · exact wl6_Phi_nonneg V n x
  · exact wl6_Phi_le_one V hfield hlam n x

/-! ### Exact cavity identity for `Q_N` -/

/-- **Exact cavity identity** (`wl_cavity_disintegration`).  `Q_N = HRS.Whole.modulatedGibbs (rieszKernel d 0) (n+1) β μ`
disintegrated over the first particle: `∫ F(X 0, tail X) dQ = ∫ ∫ F(x, Y) d(P_n^{x,1})(Y) dπ_N(x)`, where `P_n^{x,1}` is
`wl_poleLaw` (the cavity law tilted by `exp(-λ ∑ K(x, y_i))`) and `π_N = HRS.Whole.firstMarginal Q`. -/
theorem wl_cavity_disintegration (hd : 2 ≤ d) {A : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hA : HasSphericalBound A ρ) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (F : Euc d × (Fin n → Euc d) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ X : Fin (n + 1) → Euc d, F (X 0, Fin.tail X)
        ∂(HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β (HRS.Whole.withDensityReal ρ)) =
      ∫⁻ x, ∫⁻ Y, F (x, Y) ∂(wl_poleLaw (HRS.Whole.withDensityReal ρ) β (n + 1) n 1 x)
        ∂(HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β (HRS.Whole.withDensityReal ρ))) := by
  obtain ⟨C0, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  have := wl_isProb hρ
  obtain ⟨hK, hℓ, hℓle, hfield, hQ⟩ := h ρ hρ hA β hβ (n + 1) (by omega)
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set V : WeakPotential μ := wlPot hK hC0 hfield with hV
  have hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ C0 := fun x => hK.wr1_rowInt_le hC0 x
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hQeq := hQ V rfl
  rw [hQeq, wl6_firstMarginal_def, wl6_disintegration V hfield hlam hrow n F hF]
  refine lintegral_congr fun x => ?_
  simp only [wl_poleLaw, one_mul]
  rfl

/-- **Mixture form** (from `pinned_marginal_succ`).  Every one-point marginal of `Q_N` (`N = n+1`) is the mixture,
with the exact weight `θ(x)` (the density of `π_N`), of the one-point marginals of the pole ensembles `P_n^{x,1}`. -/
theorem wl_cavity_mixture (hd : 2 ≤ d) {A : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hA : HasSphericalBound A ρ) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin (n + 1)) (j : Fin n)
    {S : Set (Euc d)} (hS : MeasurableSet S) :
    ((HRS.Whole.modulatedGibbs (rieszKernel d 0) (n + 1) β (HRS.Whole.withDensityReal ρ)).map
        (fun X => X (i.succAbove j))) S =
      ∫⁻ x, ENNReal.ofReal (wl_theta (HRS.Whole.withDensityReal ρ) β (n + 1) x) *
        ((wl_poleLaw (HRS.Whole.withDensityReal ρ) β (n + 1) n 1 x).map (fun Y => Y j)) S
          ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C0, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  have := wl_isProb hρ
  obtain ⟨hK, hℓ, hℓle, hfield, hQ⟩ := h ρ hρ hA β hβ (n + 1) (by omega)
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hF := wl_isField_Qfield hK hC0 hℓ hβ (n + 1)
  set V : WeakPotential μ := wlPot hK hC0 hF with hV
  have hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ C0 := fun x => hK.wr1_rowInt_le hC0 x
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  set a : Empty → Euc d := fun e => e.elim with ha
  have hpin := wl_Q_eq_pinnedLaw hK hC0 hℓ hβ (N := n + 1) (by omega)
  rw [hpin, pinned_marginal_succ V hlam a i j hS]
  have hpf0 : pinField V (β / ((n + 1 : ℕ) : ℝ)) a = wl_Qfield μ β (n + 1) := by
    funext z
    simp [pinField, hV, wlPot]
  refine lintegral_congr fun x => ?_
  have hpf1 : pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith a x) =
      wl6_pole V.q (wl_Qfield μ β (n + 1)) (β / ((n + 1 : ℕ) : ℝ)) x := by
    funext z
    rw [pinField_pinsWith, hpf0]
    rfl
  have hw : pinWeight V (β / ((n + 1 : ℕ) : ℝ)) a n x = ENNReal.ofReal (wl_theta μ β (n + 1) x) := by
    have hθ' : wl_theta μ β (n + 1) x = wl6_theta μ V.q (wl_Qfield μ β (n + 1))
        (β / ((n + 1 : ℕ) : ℝ)) n x := wl_theta_eq μ β (n + 1) x
    rw [hθ', ← wl6_dens_eq_theta V hF hlam]
    unfold pinWeight wl6_dens
    rw [hpf1, hpf0]
    simp only [wl6_fieldNorm_eq]
    ring
  rw [hw]
  congr 2
  unfold pinnedLaw wl_poleLaw
  rw [hpf1, one_mul]
  rfl

/-! ### Pole densities for the whole family -/

lemma wl6_fam_le (μ : Measure (Euc d)) {C0 : ℝ} (hrowK : ∀ x, rowIntE wl6_K μ x ≤ C0) {β : ℝ}
    (hβ : 0 ≤ β) (N : ℕ) {B : Type} [Fintype B] (t : B → ℝ) (z : B → Euc d) {v : Euc d → ℝ} {b0 : ℝ}
    (hb : ∀ x, |v x| ≤ b0) (x : Euc d) :
    wlFamField μ wl6_K β N logWeight v t z x ≤
      β * C0 + b0 + (-(β / (N : ℝ)) * logWeight x +
        -(β / (N : ℝ)) * ∑ i, t i * sphericalLogKernel x (z i)) := by
  unfold wlFamField
  have h1 := mul_le_mul_of_nonneg_left (hrowK x) hβ
  have h2 := (le_abs_self (v x)).trans (hb x)
  show β * rowIntE wl6_K μ x - β / (N : ℝ) * logWeight x + v x -
      β / (N : ℝ) * ∑ i, t i * wl6_K x (z i) ≤ _
  linarith

/-- **Pole densities** (`wl_pole_bundle`).  `d ≥ 2`, `βp, T, b0 ≥ 0`, `A`: there is `C ≥ 1` (before `ρ, β, N, B, t, z, v`)
such that for every probability density `ρ` with `HasSphericalBound A ρ`, `β ∈ [0, βp]`, `N ≥ 1`, every finite pole set
with weights `t_b ≥ 0`, `∑ t_b ≤ T`, and every measurable `v` with `|v| ≤ b0`, the field ensembles
`P = wl6_law μ K ψ_fam (β/N) n` with `ψ_fam = wlFamField` (`β Kμ - (β/N) ℓ + v - (β/N) ∑ t_b K(·, z_b)`) satisfy:
* the first marginal of `n = m+1 ≤ N` particles is `≤ C • μ.withDensity (e^{h_N(x)} e^{-(β/N) ∑ t_b K(x,z_b)})`;
* the marginal of the first two of `n = m+2 ≤ N` particles is `≤ C • (μ⊗μ).withDensity (e^{h_N(x)+h_N(y)}
  e^{-(β/N) ∑ t_b (K(x,z_b)+K(y,z_b))} e^{-(β/N) K(x,y)})`: field, pole and pair factors are retained. -/
theorem wl_pole_bundle (hd : 2 ≤ d) (βp A T b0 : ℝ) (hβp : 0 ≤ βp) (hT : 0 ≤ T) (hb0 : 0 ≤ b0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 ≤ β → β ≤ βp → ∀ N : ℕ, 1 ≤ N → ∀ (B : Type) [Fintype B] (t : B → ℝ) (z : B → Euc d)
        (v : Euc d → ℝ), (∀ i, 0 ≤ t i) → ∑ i, t i ≤ T → Measurable v → (∀ x, |v x| ≤ b0) →
        (∀ m : ℕ, m + 1 ≤ N →
          (wl6_law (HRS.Whole.withDensityReal ρ) wl6_K
              (wlFamField (HRS.Whole.withDensityReal ρ) wl6_K β N logWeight v t z) (β / N) (m + 1)).map
              (fun X => X 0) ≤
            ENNReal.ofReal C • (HRS.Whole.withDensityReal ρ).withDensity (fun x => ENNReal.ofReal
              (Real.exp (-(β / (N : ℝ)) * logWeight x) *
                Real.exp (-(β / (N : ℝ)) * ∑ i, t i * sphericalLogKernel x (z i))))) ∧
        (∀ m : ℕ, m + 2 ≤ N →
          (wl6_law (HRS.Whole.withDensityReal ρ) wl6_K
              (wlFamField (HRS.Whole.withDensityReal ρ) wl6_K β N logWeight v t z) (β / N) (m + 2)).map
              (fun X => (X 0, X (Fin.succ 0))) ≤
            ENNReal.ofReal C • ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)).withDensity
              (fun p => ENNReal.ofReal
                (Real.exp (-(β / (N : ℝ)) * (logWeight p.1 + logWeight p.2)) *
                  Real.exp (-(β / (N : ℝ)) * ∑ i, t i *
                    (sphericalLogKernel p.1 (z i) + sphericalLogKernel p.2 (z i))) *
                  Real.exp (-(β / (N : ℝ)) * sphericalLogKernel p.1 p.2)))) := by
  obtain ⟨C0, Cl, hC0, h⟩ := wl_Q_eq_fieldLaw hd A
  set Clp : ℝ := max Cl 0 with hClp
  have hClp0 : 0 ≤ Clp := le_max_right _ _
  set Λ : ℝ := βp * (Clp + T * C0 + 2 * C0) + 2 * b0 with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ βp * (Clp + T * C0 + 2 * C0) :=
      mul_nonneg hβp (by have := mul_nonneg hT hC0; linarith)
    linarith
  refine ⟨Real.exp (2 * Λ), Real.one_le_exp (by linarith), fun ρ hρ hA β hβ hβp' N hN B _ t z v ht hT'
    hvm hvb => ?_⟩
  have := wl_isProb hρ
  obtain ⟨hK, hℓ, hℓle, -, -⟩ := h ρ hρ hA β hβ N hN
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam : 0 ≤ β / (N : ℝ) := div_nonneg hβ hNpos.le
  have hlamβ : β / (N : ℝ) ≤ β := div_le_self hβ (by exact_mod_cast hN)
  have hfam := wl_isField_family hK hC0 hβ N (ℓ := logWeight) wl2_logWeight_measurable
    wl2_logWeight_nonneg hℓ (m := Clp) (hℓle.trans (le_max_left _ _)) hvm hvb t ht z
  set ψ : Euc d → ℝ := wlFamField μ wl6_K β N logWeight v t z with hψ
  set V : WeakPotential μ := wlPot hK hC0 hfam with hV
  have hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ C0 := fun x => hK.wr1_rowInt_le hC0 x
  have hrowK : ∀ x, rowIntE wl6_K μ x ≤ C0 := fun x => hK.wr1_rowInt_le hC0 x
  -- field constant
  have hM₁ : β / (N : ℝ) * Clp + b0 + β / (N : ℝ) * ((∑ i, t i) * C0) ≤
      βp * Clp + b0 + βp * (T * C0) := by
    have a1 : β / (N : ℝ) * Clp ≤ βp * Clp :=
      mul_le_mul_of_nonneg_right (hlamβ.trans hβp') hClp0
    have a2 : β / (N : ℝ) * ((∑ i, t i) * C0) ≤ βp * (T * C0) :=
      mul_le_mul (hlamβ.trans hβp') (mul_le_mul_of_nonneg_right hT' hC0)
        (mul_nonneg (Finset.sum_nonneg fun i _ => ht i) hC0) hβp
    linarith
  -- pointwise exponent bound for the field
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (ψ x)) ≤ ENNReal.ofReal (Real.exp (β * C0 + b0)) *
      ENNReal.ofReal (Real.exp (-(β / (N : ℝ)) * logWeight x) *
        Real.exp (-(β / (N : ℝ)) * ∑ i, t i * sphericalLogKernel x (z i))) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := wl6_fam_le μ hrowK hβ N t z hvb x
    rw [hψ]
    linarith
  have hlimit : β * C0 + b0 ≤ βp * C0 + b0 := by
    have := mul_le_mul_of_nonneg_right hβp' hC0
    linarith
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · -- one particle
    have h1 := wl6_one_le V hfam hlam hrow m
    have hlm : β / (N : ℝ) * (m : ℝ) ≤ β := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
      have : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ N)
      nlinarith
    refine wl6_le_smul_trans h1 (wl6_withDensity_le_smul (ENNReal.ofReal_ne_top) hpt) ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hm1 : β / (N : ℝ) * (m : ℝ) * C0 ≤ β * C0 := mul_le_mul_of_nonneg_right hlm hC0
    have hm2 : β * C0 ≤ βp * C0 := mul_le_mul_of_nonneg_right hβp' hC0
    have hΛ' : Λ ≤ 2 * Λ := by linarith
    rw [hΛ] at hΛ' ⊢
    nlinarith
  · -- two particles
    have h2 := wl6_two_le V hfam hlam hrow m
    have hlm : β / (N : ℝ) * ((m : ℝ) + 1) ≤ β := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
      have : (m : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : m + 1 ≤ N)
      nlinarith
    have hpt2 : ∀ p : Euc d × Euc d, ENNReal.ofReal (Real.exp (ψ p.1 + ψ p.2 - β / (N : ℝ) * V.q p.1 p.2)) ≤
        ENNReal.ofReal (Real.exp (2 * (β * C0 + b0))) * ENNReal.ofReal
          (Real.exp (-(β / (N : ℝ)) * (logWeight p.1 + logWeight p.2)) *
            Real.exp (-(β / (N : ℝ)) * ∑ i, t i *
              (sphericalLogKernel p.1 (z i) + sphericalLogKernel p.2 (z i))) *
            Real.exp (-(β / (N : ℝ)) * sphericalLogKernel p.1 p.2)) := by
      intro p
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have e1 := wl6_fam_le μ hrowK hβ N t z hvb p.1
      have e2 := wl6_fam_le μ hrowK hβ N t z hvb p.2
      have e3 : ∑ i, t i * (sphericalLogKernel p.1 (z i) + sphericalLogKernel p.2 (z i)) =
          ∑ i, t i * sphericalLogKernel p.1 (z i) + ∑ i, t i * sphericalLogKernel p.2 (z i) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e3]
      show ψ p.1 + ψ p.2 - β / (N : ℝ) * sphericalLogKernel p.1 p.2 ≤ _
      rw [hψ]
      nlinarith
    refine wl6_le_smul_trans h2 (wl6_withDensity_le_smul (ENNReal.ofReal_ne_top) hpt2) ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hm1 : β / (N : ℝ) * ((m : ℝ) + 1) * C0 ≤ β * C0 := mul_le_mul_of_nonneg_right hlm hC0
    have hm2 : β * C0 ≤ βp * C0 := mul_le_mul_of_nonneg_right hβp' hC0
    rw [hΛ]
    nlinarith

end Rho

end HRS.MS.Wl
