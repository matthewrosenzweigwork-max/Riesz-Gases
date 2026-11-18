import HRS.PDE.MeanFieldVelocityTools
import HRS.PDE.MeanFieldDecayHr
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldThermal

/-!
# Velocity identity and exponential decay of the effective velocity, packet P8b of MF-01
(plan `MeanFieldDecayPlan.md`, §1 P8b)

* `effVelocity_thermal_eq_zero`: the thermal density has zero effective velocity (Gibbs relation).
* `effVelocity_eq_inv_smul_flux`: `u = ρ⁻¹ J` with the flux `J` *linear* in `z = ρ - ρ_β`.
* `finite_reg_velocity_decay`: Proposition 5.1, last sentence of the first paragraph; the statement is
  *exactly* the type of `HRS.PDE.finite_reg_velocity_decay` (`HRS/PDE/MeanField.lean`), so the
  integrator closes the target by `exact HRS.PDE.MFVelocity.finite_reg_velocity_decay hd s βm βp K V ρ₀ H`.

Route (flux form): no composition estimate for `log` of a decaying quantity; `ρ⁻¹` is a bounded
`C^j` quantity (P8a, `exists_cbNorm_inv_le`) and the flux is bilinear/linear in `z`, which decays in
`H^r ↪ C^{j+1}` for `r = (j + 1 + d/2 + K)/2`.

Statement check (`pp.parens`): none of the three statements contains an integral, so the
`∫`-precedence trap does not occur.

Dependence on the scaffold: `finite_reg_velocity_decay` uses `MFDecay.finite_reg_decay` and
`MFGlobal.finite_reg_uniform_bounds`, hence is conditional on `MFApriori.mf_apriori_bound_real_on`
(AP7); `effVelocity_thermal_eq_zero` and `effVelocity_eq_inv_smul_flux` are unconditional.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFVelocity

open MFApriori MFDecay

variable {d : ℕ}

/-! ### Section 1: the velocity identity -/

/-- `∂_j (f - g) = ∂_j f - ∂_j g` for `C¹` functions. -/
theorem partialDeriv_sub' (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.partialDeriv j (fun y => f y - g y) x =
      Torus.partialDeriv j f x - Torus.partialDeriv j g x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => f y - g y) = fun y => Torus.lift f y - Torus.lift g y := rfl
  rw [e, fderiv_fun_sub ((hf.differentiable one_ne_zero) _) ((hg.differentiable one_ne_zero) _)]
  rfl

/-- `C¹` regularity of a function with `H^K` coefficients, `K > d/2 + 1`. -/
theorem isCk_one_of_memHs (K : ℝ) (hK : (d : ℝ) / 2 + 1 < K) (ρ : Torus d → ℝ)
    (hc : Continuous ρ) (hmem : MemHs K (coeffOf ρ)) : Torus.IsCk 1 ρ := by
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hsum := summable_norm_of_memHs K hK0 _ hmem
  have hreal := isRealCoeff_coeffOf ρ (MFThermalReg.integrable_of_cont hc)
  obtain ⟨C, hC⟩ := toFun_isCk_le 1 K (by simpa using hK)
  have := (hC _ hmem hreal).1
  rwa [MFThermalReg.toFun_coeffOf hc hsum] at this

/-- (E2) The thermal density has zero effective velocity. -/
theorem effVelocity_thermal_eq_zero (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 1 V) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hc : Continuous ρβ)
    (hp : ∀ x, 0 < ρβ x) (hmem : MemHs K (coeffOf ρβ)) (x : Torus d) :
    effVelocity d s V β ρβ x = 0 := by
  have hρ1 : Torus.IsCk 1 ρβ := isCk_one_of_memHs K hK ρβ hc hmem
  obtain ⟨hφ1, hder⟩ := MFAux.gibbs_partialDeriv V ρβ (convFun (periodicRiesz d s) ρβ) β hβ.ne'
    _ hρ1 hV hp hρβ.2
  obtain ⟨-, hlog⟩ := grad_log_eq ρβ hρ1 hp
  ext j
  unfold effVelocity
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
  rw [hlog x, MFOneLe.convGradConv_eq_partialDeriv hd s hs0 hsd hρ1 hφ1 j x, hder j x]
  simp only [PiLp.smul_apply, smul_eq_mul, MFAux.grad_apply]
  field_simp
  ring


/-- (E3) The velocity is `ρ⁻¹` times the flux `J = β⁻¹∇ρ + ρ∇W`, and the flux is linear in
`z = ρ - ρ_β` (because `J_β = 0`):
`J = β⁻¹∇z + z ∇W_ρ + ρ_β ∇(g⋆z)`. -/
theorem effVelocity_eq_inv_smul_flux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 1 V) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) (hmem : MemHs K (coeffOf ρ))
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρβ1 : Torus.IsCk 1 ρβ)
    (hp : ∀ x, 0 < ρβ x) (hmemβ : MemHs K (coeffOf ρβ)) (x : Torus d) :
    effVelocity d s V β ρ x = (ρ x)⁻¹ •
      (β⁻¹ • Torus.grad (fun y => ρ y - ρβ y) x +
        (ρ x - ρβ x) • Torus.grad (Wpot d s V (coeffOf ρ)) x +
        ρβ x • Torus.grad (riesz d s (coeffOf ρ - coeffOf ρβ)) x) := by
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hcρ : Continuous ρ := MFAux.continuous_of_isCk hρ
  have hcβ : Continuous ρβ := MFAux.continuous_of_isCk hρβ1
  have hrealρ : IsRealCoeff (coeffOf ρ) := isRealCoeff_coeffOf ρ (MFThermalReg.integrable_of_cont hcρ)
  have hrealβ : IsRealCoeff (coeffOf ρβ) :=
    isRealCoeff_coeffOf ρβ (MFThermalReg.integrable_of_cont hcβ)
  have hsumρ := summable_norm_of_memHs K hK0 _ hmem
  have hsumβ := summable_norm_of_memHs K hK0 _ hmemβ
  have hR1 : Torus.IsCk 1 (riesz d s (coeffOf ρ)) :=
    (riesz_isCk hd s hs0 hsd 1 K (by simpa using hK) _ hmem hrealρ).1
  have hRβ1 : Torus.IsCk 1 (riesz d s (coeffOf ρβ)) :=
    (riesz_isCk hd s hs0 hsd 1 K (by simpa using hK) _ hmemβ hrealβ).1
  have hdiff : riesz d s (coeffOf ρ - coeffOf ρβ) =
      fun y => riesz d s (coeffOf ρ) y - riesz d s (coeffOf ρβ) y := by
    funext y
    unfold riesz
    have hs1 : Summable fun k => ‖rieszMult d s (coeffOf ρ) k‖ :=
      summable_norm_of_memHs K hK0 _ (hs_rieszMult s hsd K _ hmem).1
    have hs2 : Summable fun k => ‖rieszMult d s (coeffOf ρβ) k‖ :=
      summable_norm_of_memHs K hK0 _ (hs_rieszMult s hsd K _ hmemβ).1
    rw [← Aux.toFun_sub _ _ hs1 hs2]
    congr 1
    funext k
    simp [rieszMult, mul_sub]
  have h0 := effVelocity_thermal_eq_zero hd s hs0 hsd K hK V hV β hβ ρβ hρβ hcβ hp hmemβ x
  have hcgβ := convGradConv_eq_grad_riesz hd s hs0 hsd K hK ρβ hρβ1 hmemβ x
  have hcg := convGradConv_eq_grad_riesz hd s hs0 hsd K hK ρ hρ hmem x
  obtain ⟨-, hlogρ⟩ := grad_log_eq ρ hρ hpos
  obtain ⟨-, hlogβ⟩ := grad_log_eq ρβ hρβ1 hp
  have hW : ∀ j, Torus.partialDeriv j (Wpot d s V (coeffOf ρ)) x =
      Torus.partialDeriv j V x + Torus.partialDeriv j (riesz d s (coeffOf ρ)) x := fun j =>
    partialDeriv_add j V (riesz d s (coeffOf ρ)) hV hR1 x
  have hρρβ : ∀ j, Torus.partialDeriv j (fun y => ρ y - ρβ y) x =
      Torus.partialDeriv j ρ x - Torus.partialDeriv j ρβ x := fun j =>
    partialDeriv_sub' j hρ hρβ1 x
  have hRR : ∀ j, Torus.partialDeriv j (riesz d s (coeffOf ρ - coeffOf ρβ)) x =
      Torus.partialDeriv j (riesz d s (coeffOf ρ)) x -
        Torus.partialDeriv j (riesz d s (coeffOf ρβ)) x := fun j => by
    rw [hdiff]; exact partialDeriv_sub' j hR1 hRβ1 x
  unfold effVelocity at h0 ⊢
  rw [hlogβ x, hcgβ] at h0
  rw [hlogρ x, hcg]
  ext j
  have h0j := congrArg (fun v => v j) h0
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply, MFAux.grad_apply] at h0j ⊢
  rw [hW j, hρρβ j, hRR j]
  have hρx := (hpos x).ne'
  have hρβx := (hp x).ne'
  field_simp at h0j ⊢
  linear_combination h0j


/-! ### Section 2: the `C^j` bound of the flux form -/

theorem isCk_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ} (hab : a ≤ b)
    {φ : Torus d → E} (h : Torus.IsCk b φ) : Torus.IsCk a φ := by
  unfold Torus.IsCk at h ⊢
  exact h.of_le (by exact_mod_cast hab)

/-- Deterministic `C^j` bound of `ρ⁻¹ • (ν ∇z + z ∇W + ρβ ∇R)` in terms of `C^{j+1}` norms. -/
theorem exists_flux_bound (j : ℕ) (cL cU : ℝ) (hcL : 0 < cL) (hcU : cL ≤ cU) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : ℝ) (ρ ρβ z W R : Torus d → ℝ),
      Torus.IsCk (j + 1 : ℕ) ρ → (∀ x, cL ≤ ρ x ∧ ρ x ≤ cU) → Torus.IsCk (j + 1 : ℕ) ρβ →
      Torus.IsCk (j + 1 : ℕ) z → Torus.IsCk (j + 1 : ℕ) W → Torus.IsCk (j + 1 : ℕ) R →
      Torus.IsCk j (fun x => (ρ x)⁻¹ • (ν • Torus.grad z x + z x • Torus.grad W x +
          ρβ x • Torus.grad R x)) ∧
      Torus.cbNorm j (fun x => (ρ x)⁻¹ • (ν • Torus.grad z x + z x • Torus.grad W x +
          ρβ x • Torus.grad R x)) ≤
        A * (1 + Torus.cbNorm (j + 1) ρ) ^ j *
          (|ν| * Torus.cbNorm (j + 1) z + Torus.cbNorm (j + 1) z * Torus.cbNorm (j + 1) W +
            Torus.cbNorm (j + 1) ρβ * Torus.cbNorm (j + 1) R) := by
  obtain ⟨Ci, hCi0, hCi⟩ := exists_cbNorm_inv_le (d := d) j cL cU hcL hcU
  obtain ⟨Cs, hCs0, hCs⟩ := exists_cbNorm_smul_le (d := d) j
  refine ⟨Cs * Ci * (Cs + 1), by positivity, fun ν ρ ρβ z W R hρ hb hρβ hz hW hR => ?_⟩
  have hρj : Torus.IsCk j ρ := isCk_of_le (Nat.le_succ j) hρ
  have hzj : Torus.IsCk j z := isCk_of_le (Nat.le_succ j) hz
  have hρβj : Torus.IsCk j ρβ := isCk_of_le (Nat.le_succ j) hρβ
  have hgz : Torus.IsCk j (Torus.grad z) := isCk_grad j z hz
  have hgW : Torus.IsCk j (Torus.grad W) := isCk_grad j W hW
  have hgR : Torus.IsCk j (Torus.grad R) := isCk_grad j R hR
  have hgz' : Torus.cbNorm j (Torus.grad z) ≤ Torus.cbNorm (j + 1) z := cbNorm_grad_le j z hz
  have hgW' : Torus.cbNorm j (Torus.grad W) ≤ Torus.cbNorm (j + 1) W := cbNorm_grad_le j W hW
  have hgR' : Torus.cbNorm j (Torus.grad R) ≤ Torus.cbNorm (j + 1) R := cbNorm_grad_le j R hR
  have mz : Torus.cbNorm j z ≤ Torus.cbNorm (j + 1) z := HRS.KernelGrad.cbNorm_mono (Nat.le_succ j)
  have mρβ : Torus.cbNorm j ρβ ≤ Torus.cbNorm (j + 1) ρβ :=
    HRS.KernelGrad.cbNorm_mono (Nat.le_succ j)
  have mρ : Torus.cbNorm j ρ ≤ Torus.cbNorm (j + 1) ρ := HRS.KernelGrad.cbNorm_mono (Nat.le_succ j)
  have n0 : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : Torus d → E) (k : ℕ),
      0 ≤ Torus.cbNorm k φ := fun φ k => HRS.KernelGrad.cbNorm_nonneg' φ k
  -- the three flux terms
  obtain ⟨hT1, hT1b⟩ := cbNorm_const_smul_le_vec j ν (Torus.grad z) hgz
  obtain ⟨hT2, hT2b⟩ := hCs z (Torus.grad W) hzj hgW
  obtain ⟨hT3, hT3b⟩ := hCs ρβ (Torus.grad R) hρβj hgR
  have hT12 := isCk_add_vec j _ _ hT1 hT2
  have hJ : Torus.IsCk j (fun x => ν • Torus.grad z x + z x • Torus.grad W x +
      ρβ x • Torus.grad R x) := isCk_add_vec j _ _ hT12 hT3
  have hJb : Torus.cbNorm j (fun x => ν • Torus.grad z x + z x • Torus.grad W x +
      ρβ x • Torus.grad R x) ≤ (Cs + 1) * (|ν| * Torus.cbNorm (j + 1) z +
        Torus.cbNorm (j + 1) z * Torus.cbNorm (j + 1) W +
        Torus.cbNorm (j + 1) ρβ * Torus.cbNorm (j + 1) R) := by
    have h12 := cbNorm_add_le_vec j _ _ hT1 hT2
    have h123 := cbNorm_add_le_vec j _ _ hT12 hT3
    have e : (fun x => ν • Torus.grad z x + z x • Torus.grad W x + ρβ x • Torus.grad R x) =
        ((fun x => ν • Torus.grad z x) + (fun x => z x • Torus.grad W x)) +
          (fun x => ρβ x • Torus.grad R x) := rfl
    rw [e]
    have b1 : |ν| * Torus.cbNorm j (Torus.grad z) ≤ |ν| * Torus.cbNorm (j + 1) z :=
      mul_le_mul_of_nonneg_left hgz' (abs_nonneg _)
    have b2 : Cs * Torus.cbNorm j z * Torus.cbNorm j (Torus.grad W) ≤
        Cs * (Torus.cbNorm (j + 1) z * Torus.cbNorm (j + 1) W) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul mz hgW' (n0 _ _) (n0 _ _)) hCs0
    have b3 : Cs * Torus.cbNorm j ρβ * Torus.cbNorm j (Torus.grad R) ≤
        Cs * (Torus.cbNorm (j + 1) ρβ * Torus.cbNorm (j + 1) R) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul mρβ hgR' (n0 _ _) (n0 _ _)) hCs0
    have p1 : 0 ≤ |ν| * Torus.cbNorm (j + 1) z := mul_nonneg (abs_nonneg _) (n0 _ _)
    have p2 : 0 ≤ Torus.cbNorm (j + 1) z * Torus.cbNorm (j + 1) W := mul_nonneg (n0 _ _) (n0 _ _)
    have p3 : 0 ≤ Torus.cbNorm (j + 1) ρβ * Torus.cbNorm (j + 1) R :=
      mul_nonneg (n0 _ _) (n0 _ _)
    nlinarith [mul_nonneg hCs0 p2, mul_nonneg hCs0 p3]
  obtain ⟨hi, hib⟩ := hCi ρ hρj hb
  obtain ⟨hu, hub⟩ := hCs (fun x => (ρ x)⁻¹) _ hi hJ
  refine ⟨hu, hub.trans ?_⟩
  have hpow : (1 + Torus.cbNorm j ρ) ^ j ≤ (1 + Torus.cbNorm (j + 1) ρ) ^ j :=
    pow_le_pow_left₀ (by linarith [n0 ρ j]) (by linarith) j
  have hib' : Torus.cbNorm j (fun x => (ρ x)⁻¹) ≤ Ci * (1 + Torus.cbNorm (j + 1) ρ) ^ j :=
    hib.trans (mul_le_mul_of_nonneg_left hpow hCi0)
  have hnn : 0 ≤ Torus.cbNorm j (fun x => (ρ x)⁻¹) := n0 _ _
  calc Cs * Torus.cbNorm j (fun x => (ρ x)⁻¹) * Torus.cbNorm j (fun x => ν • Torus.grad z x +
          z x • Torus.grad W x + ρβ x • Torus.grad R x)
      ≤ Cs * (Ci * (1 + Torus.cbNorm (j + 1) ρ) ^ j) * ((Cs + 1) * (|ν| * Torus.cbNorm (j + 1) z +
        Torus.cbNorm (j + 1) z * Torus.cbNorm (j + 1) W +
        Torus.cbNorm (j + 1) ρβ * Torus.cbNorm (j + 1) R)) := by
        gcongr <;> first
          | exact mul_nonneg hCs0 (mul_nonneg hCi0
              (pow_nonneg (add_nonneg zero_le_one (n0 ρ (j + 1))) _))
          | exact n0 _ _
    _ = _ := by ring


/-! ### Section 3: the decay -/

theorem isRealCoeff_sub' {a b : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    IsRealCoeff (a - b) := fun j => by
  simp only [Pi.sub_apply, map_sub]; rw [ha j, hb j]

/-- (E4) = the body of `finite_reg_velocity_decay` (verbatim conclusion). -/
theorem finite_reg_velocity_decay (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∀ j : ℕ, (j : ℝ) + 1 + (d : ℝ) / 2 < K → ∃ C c : ℝ, 0 < c ∧
      ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∀ t, 0 ≤ t → Torus.IsCk j (effVelocity d s V β (mfPath ρc t)) ∧
        Torus.cbNorm j (effVelocity d s V β (mfPath ρc t)) ≤ C * Real.exp (-c * t) := by
  intro j hj
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set r : ℝ := ((j : ℝ) + 1 + (d : ℝ) / 2 + K) / 2 with hr
  have hr1 : (d : ℝ) / 2 + ((j + 1 : ℕ) : ℝ) < r := by
    rw [hr]; push_cast; linarith
  have hrK : r < K := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hK1 : (d : ℝ) / 2 + ((j + 1 : ℕ) : ℝ) < K := by push_cast; linarith
  have hKd : (d : ℝ) / 2 + 1 < K := by linarith
  have hjK : j + 1 ≤ K + 2 := by
    have : ((j + 1 : ℕ) : ℝ) ≤ ((K + 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨c, C, hc, hunif⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  obtain ⟨B, hB0, hB⟩ := exists_thermal_hK_bound hd s βm βp K V ρ₀ H
  obtain ⟨Cr, cr, hCr, hcr, hdec⟩ := finite_reg_decay hd s βm βp K V ρ₀ H r hr0 hrK
  obtain ⟨A, hA0, hA⟩ := exists_flux_bound (d := d) j c (max C c) hc (le_max_right _ _)
  obtain ⟨E1, hE1⟩ := toFun_isCk_le (d := d) (j + 1) r hr1
  obtain ⟨E2, hE2⟩ := toFun_isCk_le (d := d) (j + 1) K hK1
  have hV1 : Torus.IsCk (j + 1 : ℕ) V := isCk_of_le hjK H.hV
  have hV1' : Torus.IsCk 1 V := isCk_of_le (Nat.le_add_left 1 j) hV1
  have hVc : Continuous V := MFAux.continuous_of_isCk hV1'
  set G : ℝ := |rieszConst d s| with hG
  set Vn : ℝ := Torus.cbNorm (j + 1) V with hVn
  set Wb : ℝ := Vn + |E2| * (G * C) with hWb
  set Eβ : ℝ := |E2| * Real.sqrt B with hEβ
  set Eρ : ℝ := |E2| * C with hEρ
  refine ⟨A * (1 + Eρ) ^ j * (|E1| * Cr * (βm⁻¹ + Wb + Eβ * G)), cr, hcr, ?_⟩
  intro β hβ ρc hsol t ht
  have hβpos : 0 < β := lt_of_lt_of_le H.hβm hβ.1
  have hb := hunif β hβ ρc hsol t ht
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hsol t ht
  have hmt : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht)
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hsumt := summable_norm_of_memHs (K : ℝ) hK0 _ hmt
  obtain ⟨ρβ, hρβ, hcont, hpos⟩ :=
    MFThermalAssembly.thermal_exists_continuous hd s H.hs0 H.hsd V hVc β hβpos
  have hSob := MFThermalAssembly.thermal_memSobolev_all hd s H.hs0 H.hsd K V H.hV β hβpos ρβ hρβ
    hcont hpos
  have hmβ : MemHs (K : ℝ) (coeffOf ρβ) := (ProdAux.memHs_of_memSobolev (K : ℝ) hSob).1
  have hsumβ := summable_norm_of_memHs (K : ℝ) hK0 _ hmβ
  have hrealβ : IsRealCoeff (coeffOf ρβ) :=
    isRealCoeff_coeffOf ρβ (MFThermalReg.integrable_of_cont hcont)
  have hBβ := hB β hβ ρβ hρβ hcont hpos hSob
  obtain ⟨hmz, hzn⟩ := hdec β hβ ρc hsol ρβ hρβ hcont hpos hSob t ht
  have hrealz : IsRealCoeff (ρc t - coeffOf ρβ) := isRealCoeff_sub' hreal hrealβ
  -- regularity and bounds of the ingredients
  have hρK : hsNorm (K : ℝ) (ρc t) ≤ C := hb.2
  have hnn1 : 0 ≤ hsNorm (K : ℝ) (ρc t) := Real.sqrt_nonneg _
  obtain ⟨hρC, hρCb⟩ := hE2 _ hmt hreal
  have hρCb' : Torus.cbNorm (j + 1) (toFun (ρc t)) ≤ Eρ :=
    hρCb.trans ((mul_le_mul_of_nonneg_right (le_abs_self E2) hnn1).trans
      (mul_le_mul_of_nonneg_left hρK (abs_nonneg _)))
  have hcoeff : coeffOf (mfPath ρc t) = ρc t := coeffOf_toFun (ρc t) hreal hsumt
  have hρβeq : toFun (coeffOf ρβ) = ρβ := MFThermalReg.toFun_coeffOf hcont hsumβ
  obtain ⟨hβC, hβCb⟩ := hE2 _ hmβ hrealβ
  rw [hρβeq] at hβC hβCb
  have hβCb' : Torus.cbNorm (j + 1) ρβ ≤ Eβ := by
    refine hβCb.trans ((mul_le_mul_of_nonneg_right (le_abs_self E2) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)))
    exact Real.sqrt_le_sqrt hBβ
  -- the difference
  have hzeq : (fun y => mfPath ρc t y - ρβ y) = toFun (ρc t - coeffOf ρβ) := by
    funext y
    rw [Aux.toFun_sub _ _ hsumt hsumβ, hρβeq]
    rfl
  obtain ⟨hzC, hzCb⟩ := hE1 _ hmz hrealz
  have hexp : 0 ≤ Real.exp (-cr * t) := (Real.exp_pos _).le
  have hD : hsNorm r (ρc t - coeffOf ρβ) ≤ Cr * Real.exp (-cr * t) := hzn
  have hDnn : 0 ≤ hsNorm r (ρc t - coeffOf ρβ) := Real.sqrt_nonneg _
  have hzCb' : Torus.cbNorm (j + 1) (fun y => mfPath ρc t y - ρβ y) ≤
      |E1| * (Cr * Real.exp (-cr * t)) := by
    rw [hzeq]
    exact hzCb.trans ((mul_le_mul_of_nonneg_right (le_abs_self E1) hDnn).trans
      (mul_le_mul_of_nonneg_left hD (abs_nonneg _)))
  rw [← hzeq] at hzC
  -- the interaction part of the difference
  have hRm := hs_rieszMult s H.hsd r _ hmz
  obtain ⟨hRC, hRCb⟩ := hE1 _ hRm.1 (isRealCoeff_rieszMult s _ hrealz)
  have hRCb' : Torus.cbNorm (j + 1) (riesz d s (ρc t - coeffOf ρβ)) ≤
      |E1| * (G * (Cr * Real.exp (-cr * t))) := by
    have h1 : hsNorm r (rieszMult d s (ρc t - coeffOf ρβ)) ≤ G * (Cr * Real.exp (-cr * t)) :=
      hRm.2.trans (mul_le_mul_of_nonneg_left hD (abs_nonneg _))
    exact hRCb.trans ((mul_le_mul_of_nonneg_right (le_abs_self E1) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
  -- the potential
  have hRtm := hs_rieszMult s H.hsd (K : ℝ) _ hmt
  obtain ⟨hRtC, hRtCb⟩ := hE2 _ hRtm.1 (isRealCoeff_rieszMult s _ hreal)
  have hRtCb' : Torus.cbNorm (j + 1) (riesz d s (ρc t)) ≤ |E2| * (G * C) := by
    have h1 : hsNorm (K : ℝ) (rieszMult d s (ρc t)) ≤ G * C :=
      hRtm.2.trans (mul_le_mul_of_nonneg_left hρK (abs_nonneg _))
    exact hRtCb.trans ((mul_le_mul_of_nonneg_right (le_abs_self E2) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
  have hWC : Torus.IsCk (j + 1 : ℕ) (Wpot d s V (ρc t)) := isCk_add V _ hV1 hRtC
  have hWCb : Torus.cbNorm (j + 1) (Wpot d s V (ρc t)) ≤ Wb :=
    (Torus.cbNorm_add_le (j + 1) V (riesz d s (ρc t)) hV1 hRtC).trans
      (by rw [hWb]; linarith)
  -- the velocity identity
  have hlow : ∀ x, c ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ max C c := fun x =>
    ⟨(hb.1 x).1, (hb.1 x).2.trans (le_max_left _ _)⟩
  have hρ1 : Torus.IsCk 1 (mfPath ρc t) := isCk_of_le (Nat.le_add_left 1 j) hρC
  have hρβ1 : Torus.IsCk 1 ρβ := isCk_of_le (Nat.le_add_left 1 j) hβC
  have hmem : MemHs (K : ℝ) (coeffOf (mfPath ρc t)) := by rw [hcoeff]; exact hmt
  have hfun : effVelocity d s V β (mfPath ρc t) = fun x =>
      ((mfPath ρc t) x)⁻¹ • (β⁻¹ • Torus.grad (fun y => mfPath ρc t y - ρβ y) x +
        (fun y => mfPath ρc t y - ρβ y) x • Torus.grad (Wpot d s V (ρc t)) x +
        ρβ x • Torus.grad (riesz d s (ρc t - coeffOf ρβ)) x) := by
    funext x
    have := effVelocity_eq_inv_smul_flux hd s H.hs0 H.hsd (K : ℝ) hKd V hV1' β hβpos
      (mfPath ρc t) hρ1 (fun x => lt_of_lt_of_le hc (hlow x).1) hmem ρβ hρβ hρβ1 hpos
      hmβ x
    rw [hcoeff] at this
    exact this
  rw [hfun]
  obtain ⟨hu, hub⟩ := hA β⁻¹ (mfPath ρc t) ρβ _ _ _ hρC hlow hβC hzC hWC hRC
  refine ⟨hu, hub.trans ?_⟩
  have n0 : ∀ (φ : Torus d → ℝ) (k : ℕ), 0 ≤ Torus.cbNorm k φ :=
    fun φ k => HRS.KernelGrad.cbNorm_nonneg' φ k
  have hν : |β⁻¹| ≤ βm⁻¹ := by
    rw [abs_of_pos (inv_pos.2 hβpos)]
    exact inv_anti₀ H.hβm hβ.1
  have hGnn : 0 ≤ G := abs_nonneg _
  have hC0 : 0 ≤ C := le_trans hnn1 hρK
  have hρCb'' : Torus.cbNorm (j + 1) (mfPath ρc t) ≤ Eρ := hρCb'
  have hpow : (1 + Torus.cbNorm (j + 1) (mfPath ρc t)) ^ j ≤ (1 + Eρ) ^ j :=
    pow_le_pow_left₀ (add_nonneg zero_le_one (n0 _ _)) (by linarith) j
  have hz0 := n0 (fun y => mfPath ρc t y - ρβ y) (j + 1)
  have hexpC : 0 ≤ Cr * Real.exp (-cr * t) := mul_nonneg hCr.le hexp
  calc A * (1 + Torus.cbNorm (j + 1) (mfPath ρc t)) ^ j *
        (|β⁻¹| * Torus.cbNorm (j + 1) (fun y => mfPath ρc t y - ρβ y) +
          Torus.cbNorm (j + 1) (fun y => mfPath ρc t y - ρβ y) *
            Torus.cbNorm (j + 1) (Wpot d s V (ρc t)) +
          Torus.cbNorm (j + 1) ρβ * Torus.cbNorm (j + 1) (riesz d s (ρc t - coeffOf ρβ)))
      ≤ A * (1 + Eρ) ^ j *
        (βm⁻¹ * (|E1| * (Cr * Real.exp (-cr * t))) +
          (|E1| * (Cr * Real.exp (-cr * t))) * Wb +
          Eβ * (|E1| * (G * (Cr * Real.exp (-cr * t))))) := by
        gcongr
        all_goals first
          | exact n0 _ _
          | exact (inv_pos.2 H.hβm).le
          | exact add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (n0 _ _))
              (mul_nonneg (n0 _ _) (n0 _ _))) (mul_nonneg (n0 _ _) (n0 _ _))
    _ = _ := by ring

end HRS.PDE.MFVelocity
