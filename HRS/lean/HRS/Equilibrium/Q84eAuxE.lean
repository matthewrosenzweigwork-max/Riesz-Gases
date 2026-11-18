/-
# HRS.Equilibrium.Q84eAuxE — packet Q84e: `μ(B ψ(·,y)) = 0` (source line 4954, "Here, `μ(Bf)=0`")

The integration by parts `∫ ρ B(ψ(·,y)) dx = 0` for the kernel `ψ(·,y)`, smooth off `{y}` with
`|∇ψ|, |D²ψ| ≲ w`: along coordinate lines avoiding `y` (almost every line for `d ≥ 2`) via the
Gibbs relation `∇ρ = -βρ(∇V + F_μ)`.
-/
import HRS.Equilibrium.Q84dStationary
import HRS.PDE.MeanFieldAux
import HRS.Equilibrium.Q84eAuxD

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ}

/-- The Gibbs relation `∇V + F_μ = -β⁻¹ ∇ρ / ρ`, componentwise. -/
theorem q84e_drift {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (hβ : 0 < β)
    (hV : Torus.IsSmooth V) (hρ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρs : SmoothPosDensity ρ) (x : Torus d) (j : Fin d) :
    (Torus.grad V x) j + (forceField d s ρ x) j = -β⁻¹ * ((Torus.grad ρ x) j / ρ x) := by
  have hρ1 : Torus.IsCk 1 ρ := Q84a.q84a_contDiff_one hρs.smooth
  have hV1 : Torus.IsCk 1 V := Q84a.q84a_contDiff_one hV
  obtain ⟨-, hdiff⟩ := HRS.PDE.MFAux.gibbs_partialDeriv V ρ (convFun (periodicRiesz d s) ρ) β hβ.ne'
    (∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y))) hρ1 hV1 hρs.pos hρ.2
  unfold forceField
  rw [Q84a.q84a_conv_eq hρs]
  simp only [HRS.PDE.MFAux.grad_apply]
  rw [hdiff j x]
  ring

/-- Derivative of a smooth function along a coordinate line. -/
theorem q84e_line_deriv {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (x : Torus d) (k : Fin d) :
    HasDerivAt (fun τ : ℝ => f (x + Torus.mk (τ • ek k))) ((Torus.grad f x) k) 0 := by
  have hVd : DifferentiableAt ℝ (fun u : Euc d => f (x + Torus.mk u)) 0 := by
    rw [q84d_slice_eq]
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
    exact ((hc.differentiable (by norm_num)) _).comp 0 (differentiableAt_id.const_add _)
  have h1 : HasDerivAt (fun τ : ℝ => τ • ek k) (ek k) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (ek k)
  have hF0 : HasFDerivAt (fun u : Euc d => f (x + Torus.mk u))
      (fderiv ℝ (fun u : Euc d => f (x + Torus.mk u)) 0) ((fun τ : ℝ => τ • ek k) 0) := by
    simpa using hVd.hasFDerivAt
  have h2 := hF0.comp_hasDerivAt (0 : ℝ) h1
  have e : (fun τ : ℝ => f (x + Torus.mk (τ • ek k))) =
      (fun u : Euc d => f (x + Torus.mk u)) ∘ fun τ : ℝ => τ • ek k := by
    funext τ; simp
  rw [e]
  convert h2 using 1
  rw [q84d_slice_grad_comp]

/-- Integration by parts along closed coordinate lines on the torus. -/
theorem q84e_ibp_torus (k : Fin d) {v w : Torus d → ℝ} (hvm : Measurable v)
    (hvi : Integrable v)
    (hline : ∀ᵐ x : Torus d, ∀ t : ℝ,
      HasDerivAt (fun τ : ℝ => w (x + Torus.mk (τ • ek k))) (v (x + Torus.mk (t • ek k))) t) :
    ∫ x, v x = 0 := by
  have hmp : MeasurePreserving (fun Y : Config d 1 => Y 0) volume (volume : Measure (Torus d)) :=
    measurePreserving_eval (fun _ : Fin 1 => (volume : Measure (Torus d))) 0
  have hl : ∀ Y : Config d 1, ∀ τ : ℝ, (lineCfg (0 : Fin 1) k Y τ) 0 = Y 0 + Torus.mk (τ • ek k) := by
    intro Y τ; simp [lineCfg]
  have h := q84d_ibp (0 : Fin 1) k (v := fun Y : Config d 1 => v (Y 0)) (w := fun Y => w (Y 0))
    (hvm.comp (measurable_pi_apply 0)) (hmp.integrable_comp_of_integrable hvi) (by
      filter_upwards [hmp.quasiMeasurePreserving.ae hline] with Y hY t
      simp only [hl]
      exact hY t)
  have := integral_map (μ := (volume : Measure (Config d 1))) hmp.measurable.aemeasurable
    (f := v) hvm.aestronglyMeasurable
  rw [hmp.map_eq] at this
  rw [this]
  exact h

/-- Integrability against `μ = ρ dx` in terms of `ρ g`. -/
theorem q84e_integrable_mu_iff {ρ : Torus d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {g : Torus d → ℝ} :
    Integrable g (withDensityReal ρ) ↔ Integrable (fun z => ρ z * g z) := by
  unfold withDensityReal
  rw [integrable_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρm)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun z => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 z), mul_comm]

/-- Almost every coordinate line in direction `k` avoids a given point (`d ≥ 2`). -/
theorem q84e_ae_line_avoid (hd : 2 ≤ d) (k : Fin d) (y : Torus d) :
    ∀ᵐ x : Torus d, ∀ t : ℝ, x + Torus.mk (t • ek k) ≠ y := by
  obtain ⟨m, hmk⟩ : ∃ m : Fin d, m ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
    · exact ⟨⟨0, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
  have hmp : MeasurePreserving (fun x : Torus d => x m) volume (volume : Measure UnitAddCircle) :=
    measurePreserving_eval (fun _ : Fin d => (volume : Measure UnitAddCircle)) m
  have hy : ∀ᵐ u ∂(volume : Measure UnitAddCircle), u ≠ y m := by
    rw [ae_iff]
    have : {u : UnitAddCircle | ¬u ≠ y m} = {y m} := by ext u; simp
    rw [this]; exact volume_singleton_circle _
  filter_upwards [hmp.quasiMeasurePreserving.ae hy] with x hx t hxt
  have := congrFun hxt m
  simp [Torus.mk, ek, hmk] at this
  exact hx this

/-- The flux `w_k = ρ ∂_{x_k}ψ(·,y)` has derivative `v_k` along lines avoiding `y`. -/
theorem q84e_flux_line_deriv {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (hβ : 0 < β)
    (hV : Torus.IsSmooth V) (hρ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρs : SmoothPosDensity ρ) {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (k : Fin d) (y x : Torus d)
    (hxy : x ≠ y) :
    HasDerivAt (fun τ : ℝ => ρ (x + Torus.mk (τ • ek k)) * gK ψ k (x + Torus.mk (τ • ek k)) y)
      (ρ x * (hK ψ k x y - β * ((Torus.grad V x) k + (forceField d s ρ x) k) * gK ψ k x y)) 0 := by
  have h1 := q84e_line_deriv hρs.smooth x k
  have h2 := q84d_gK_line_deriv hsm hxy k
  have h3 := h1.mul h2
  simp only [zero_smul, q84d_mk_zero, add_zero] at h3
  convert h3 using 1
  have hdr := q84e_drift hβ hV hρ hρs x k
  have hpos := hρs.pos x
  have : (Torus.grad ρ x) k = -(β * ρ x * ((Torus.grad V x) k + (forceField d s ρ x) k)) := by
    rw [hdr]; field_simp
  rw [this]; ring

/-- **`μ(B ψ(·,y)) = 0`** (source line 4954): `B(ψ(·,y))` is `μ`-integrable with mean zero. -/
theorem q84e_Bop_mean (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hβ : 0 < β) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ)
    (y : Torus d) :
    Integrable (fun x => Bop d s V β ρ (fun z => ψ z y) x) (withDensityReal ρ) ∧
      ∫ x, Bop d s V β ρ (fun z => ψ z y) x ∂(withDensityReal ρ) = 0 := by
  have hPs := hψ.size
  have hsm := hPs.smooth
  have hK0 := q84d_K_nonneg hd hcrit hψ
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift
    (Q84a.q84a_contDiff_one hρs.smooth).continuous
  have hρm : Measurable ρ := hρc.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρs.pos x).le
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  obtain ⟨Gv, hGv⟩ := q84d_exists_grad_bound hV
  obtain ⟨M, hM0, hM⟩ := Q84a.q84a_force_bound hβ hV hρ hρs
  have hF : ∀ x k, |(forceField d s ρ x) k| ≤ M := fun x k =>
    (q84d_comp_le_norm _ k).trans (hM x)
  set vk : Fin d → Torus d → ℝ := fun k x =>
    ρ x * (hK ψ k x y - β * ((Torus.grad V x) k + (forceField d s ρ x) k) * gK ψ k x y) with hvk
  -- measurability
  have hvm : ∀ k, Measurable (vk k) := by
    intro k
    have h1 : Measurable (fun x : Torus d => hK ψ k x y) :=
      (q84d_measurable_hK ψ k).comp (measurable_id.prodMk measurable_const)
    have h2 : Measurable (fun x : Torus d => gK ψ k x y) :=
      (q84d_measurable_gK ψ k).comp (measurable_id.prodMk measurable_const)
    have h3 : Measurable (fun x : Torus d => (Torus.grad V x) k) :=
      (EuclideanSpace.proj k).continuous.measurable.comp (q84d_measurable_grad V)
    have h4 : Measurable (fun x : Torus d => (forceField d s ρ x) k) :=
      (EuclideanSpace.proj k).continuous.measurable.comp (q84d_measurable_grad _)
    exact hρm.mul (h1.sub ((measurable_const.mul (h3.add h4)).mul h2))
  -- integrability
  have hvi : ∀ k, Integrable (vk k) := by
    intro k
    set C : ℝ := Λ * (K₁ + β * (Gv + M) * K₁) with hC
    refine Integrable.mono' ((q84d_integrable_wEnv hd hcrit y).const_mul C)
      (hvm k).aestronglyMeasurable ?_
    have hy : ∀ᵐ x : Torus d, x ≠ y := by
      rw [ae_iff]
      have : {x : Torus d | ¬x ≠ y} = {y} := by ext x; simp
      rw [this]; exact volume_singleton_torus (by omega) y
    filter_upwards [hy] with x hxy
    have hw := PairCorrAux.one_le_wEnv s x y
    have hwy : wEnv s x y = wEnv s y x := PairCorrAux.wEnv_symm s x y
    have g1 := q84d_gK_bound hPs hxy k
    have h1 := q84d_hK_bound hPs hxy k
    have hgv : |(Torus.grad V x) k + (forceField d s ρ x) k| ≤ Gv + M :=
      (abs_add_le _ _).trans (add_le_add (hGv x k) (hF x k))
    have hb : |hK ψ k x y - β * ((Torus.grad V x) k + (forceField d s ρ x) k) * gK ψ k x y| ≤
        (K₁ + β * (Gv + M) * K₁) * wEnv s x y := by
      calc |hK ψ k x y - β * ((Torus.grad V x) k + (forceField d s ρ x) k) * gK ψ k x y|
          ≤ |hK ψ k x y| + |β * ((Torus.grad V x) k + (forceField d s ρ x) k) * gK ψ k x y| :=
            abs_sub _ _
        _ ≤ K₁ * wEnv s x y + β * (Gv + M) * (K₁ * wEnv s x y) := by
            refine add_le_add h1 ?_
            rw [abs_mul, abs_mul, abs_of_pos hβ]
            refine mul_le_mul (mul_le_mul_of_nonneg_left hgv hβ.le) g1 (abs_nonneg _)
              (mul_nonneg hβ.le ((abs_nonneg _).trans hgv))
        _ = (K₁ + β * (Gv + M) * K₁) * wEnv s x y := by ring
    have hz : |ρ x * (hK ψ k x y - β * ((Torus.grad V x) k + (forceField d s ρ x) k) * gK ψ k x y)| ≤
        Λ * ((K₁ + β * (Gv + M) * K₁) * wEnv s x y) := by
      rw [abs_mul, abs_of_nonneg (hρ0 x)]
      exact mul_le_mul (hΛ x) hb (abs_nonneg _) hΛ0.le
    calc ‖vk k x‖ = |ρ x * (hK ψ k x y - β * ((Torus.grad V x) k + (forceField d s ρ x) k) *
          gK ψ k x y)| := Real.norm_eq_abs _
      _ ≤ Λ * ((K₁ + β * (Gv + M) * K₁) * wEnv s x y) := hz
      _ = C * wEnv s y x := by rw [hC, hwy]; ring
  -- zero mean of each flux divergence
  have hv0 : ∀ k, ∫ x, vk k x = 0 := by
    intro k
    refine q84e_ibp_torus k (w := fun x => ρ x * gK ψ k x y) (hvm k) (hvi k) ?_
    filter_upwards [q84e_ae_line_avoid hd k y] with x hx t
    have hxt := hx t
    have h0 := q84e_flux_line_deriv hβ hV hρ hρs hsm k y _ hxt
    have h1 : HasDerivAt (fun σ : ℝ => ρ (x + Torus.mk (t • ek k) + Torus.mk (σ • ek k)) *
        gK ψ k (x + Torus.mk (t • ek k) + Torus.mk (σ • ek k)) y) (vk k (x + Torus.mk (t • ek k)))
        (t - t) := by rw [sub_self]; exact h0
    have h2 := h1.comp_sub_const t t
    have e : (fun σ : ℝ => ρ (x + Torus.mk (t • ek k) + Torus.mk ((σ - t) • ek k)) *
        gK ψ k (x + Torus.mk (t • ek k) + Torus.mk ((σ - t) • ek k)) y) =
        fun τ => ρ (x + Torus.mk (τ • ek k)) * gK ψ k (x + Torus.mk (τ • ek k)) y := by
      funext τ
      rw [add_assoc, ← Q84a.q84a_mk_add, ← add_smul, add_sub_cancel]
    rw [e] at h2
    exact h2
  -- the identity `ρ B = β⁻¹ ∑ v_k` off `{y}`
  have hid : ∀ᵐ x : Torus d, ρ x * Bop d s V β ρ (fun z => ψ z y) x = β⁻¹ * ∑ k, vk k x := by
    have hy : ∀ᵐ x : Torus d, x ≠ y := by
      rw [ae_iff]
      have : {x : Torus d | ¬x ≠ y} = {y} := by ext x; simp
      rw [this]; exact volume_singleton_torus (by omega) y
    filter_upwards [hy] with x hxy
    rw [q84d_Bop_eq hsm hxy]
    unfold Bsur
    simp only [hvk, ← Finset.mul_sum, Finset.sum_sub_distrib, PiLp.add_apply, add_mul,
      Finset.sum_add_distrib, mul_add]
    field_simp
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  have hsum : Integrable (fun x => β⁻¹ * ∑ k, vk k x) :=
    (integrable_finsetSum _ fun k _ => hvi k).const_mul _
  have hρB : Integrable (fun x => ρ x * Bop d s V β ρ (fun z => ψ z y) x) :=
    hsum.congr (hid.mono fun x hx => hx.symm)
  refine ⟨(q84e_integrable_mu_iff hρm hρ0).2 hρB, ?_⟩
  rw [integral_withDensityReal_eq ρ hρm hρ0, integral_congr_ae hid, integral_const_mul,
    integral_finsetSum _ fun k _ => hvi k]
  simp [hv0]

end HRS.Q84e

end
