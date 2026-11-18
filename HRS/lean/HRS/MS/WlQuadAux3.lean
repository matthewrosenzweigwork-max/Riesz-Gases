import HRS.MS.WlQuadAux2
import HRS.MS.WrQuadAux3

/-!
# HRS.MS.WlQuadAux3 -- change of centering and the calibrated reference as a pinned law (WL-11, part 1)

Packet WL-11 of `docs/WR_LOG_PLAN.md` (Step 12 of the proof of `r2_log_static`).  Infrastructure lemmas, not
manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl11_`.  Notation: `μ = withDensityReal ρ`,
`K = sphericalLogKernel`, `H_ν(x) = ∫ h(x,y) dν(y)` (`wr14a_Hc`).

Contents.
* `wl11_withDensity_le`: `μ.withDensity θ ≤ C_p μ` for `θ ≤ C_p`;
* `wl11_schur_L2`: the Schur test for the symmetric kernel `|h| ≤ B (1 + K)` in `L²(μ)` (from `wl_schur`);
* `wl11_change_term_le`: the **change term** `∫ |H_ν - H_π|² dπ ≤ c C_p B² ‖φ - θ‖²_{L²(μ)}` for
  `ν = φ μ`, `π = θ μ`, `0 ≤ φ, θ ≤ C_p` (the logarithmic port of `wr14a_change_term_le`; densities are used
  instead of Radon-Nikodym derivatives, no junk values);
* `wl11_qvb_integrable`: the first two conjuncts of `QuadraticVarianceBound` for `ν ≤ C_p μ`;
* `wl11_ref_pinned`: for `M ≥ M₀`, `N ≥ N₀` the calibrated reference `wl9_RN` is the pinned law of a weak potential
  `V'` with Dobrushin coefficient `κ(V', β) ≤ 1/2` (the set-up of `wl_quad_ref`, exported).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-- A density bounded by `C_p` gives a measure dominated by `C_p μ`. -/
theorem wl11_withDensity_le {μ : Measure (Euc d)} {θ : Euc d → ℝ} {Cp : ℝ} (hθ : ∀ x, θ x ≤ Cp) :
    μ.withDensity (fun x => ENNReal.ofReal (θ x)) ≤ ENNReal.ofReal Cp • μ := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hθ x)

/-! ### The Schur test in `L²(μ)` -/

/-- **Schur test.**  For a symmetric measurable `h` with `|h| ≤ B (1 + K)` off the diagonal,
`∫ (∫ |h(x,y)| F(y) dμ(y))² dμ(x) ≤ (C B)² ∫ F² dμ`, `C` depending on `d, A` only. -/
theorem wl11_schur_L2 (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ (B : ℝ) (h : Euc d → Euc d → ℝ),
      Measurable (fun p : Euc d × Euc d => h p.1 p.2) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      ∀ F : Euc d → ℝ≥0∞, Measurable F →
        ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * F y ∂(HRS.Whole.withDensityReal ρ)) ^ 2
            ∂(HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (C * B) ^ 2 * ∫⁻ y, F y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC0, hC⟩ := wl_schur hd A
  refine ⟨C, hC0, fun ρ hρ hA B h hm hsym hbd F hF => ?_⟩
  haveI := wl_isProb hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  obtain ⟨hB0, hrows, -⟩ := hC ρ hρ hA B h hm hbd
  have hhx : ∀ x, Measurable (h x) := fun x => Measurable.of_uncurry_left (f := h) hm
  set K : Euc d → Euc d → ℝ≥0∞ := fun x y => ENNReal.ofReal |h x y| with hK
  have hKm : Measurable (fun p : Euc d × Euc d => K p.1 p.2) := hm.abs.ennreal_ofReal
  have hKx : ∀ x, Measurable (K x) := fun x => (hhx x).abs.ennreal_ofReal
  have hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ ENNReal.ofReal (C * B) := by
    intro x
    obtain ⟨hi, -, hle, -⟩ := hrows x
    have := ofReal_integral_eq_lintegral_ofReal (f := fun y => |h x y|) hi.abs
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
    simp only [hK]
    rw [← this]
    exact ENNReal.ofReal_le_ofReal hle
  have hcol : ∀ y, ∫⁻ x, K x y ∂ν ≤ ENNReal.ofReal (C * B) := by
    intro y
    calc ∫⁻ x, K x y ∂ν = ∫⁻ x, K y x ∂ν := lintegral_congr fun x => by simp only [hK, hsym x y]
      _ ≤ _ := hrow y
  have h1 : ∀ x, (∫⁻ y, K x y * F y ∂ν) ^ 2 ≤
      ENNReal.ofReal (C * B) * ∫⁻ y, K x y * F y ^ 2 ∂ν := fun x =>
    (HRS.Whole.Q34.weighted_cs ν (K x) F (hKx x) hF).trans (mul_le_mul' (hrow x) le_rfl)
  have hjoint : Measurable (fun p : Euc d × Euc d => K p.1 p.2 * F p.2 ^ 2) :=
    hKm.mul ((hF.comp measurable_snd).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, K x y * F y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (C * B) * ∫⁻ y, K x y * F y ^ 2 ∂ν ∂ν := lintegral_mono h1
    _ = ENNReal.ofReal (C * B) * ∫⁻ x, ∫⁻ y, K x y * F y ^ 2 ∂ν ∂ν := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d => K p.1 p.2 * F p.2 ^ 2) hjoint
    _ = ENNReal.ofReal (C * B) * ∫⁻ y, ∫⁻ x, K x y * F y ^ 2 ∂ν ∂ν := by
        congr 1
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ENNReal.ofReal (C * B) * ∫⁻ y, ENNReal.ofReal (C * B) * F y ^ 2 ∂ν := by
        refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
        have hm' : Measurable (fun x : Euc d => K x y) :=
          Measurable.of_uncurry_right (f := K) hKm (y := y)
        rw [lintegral_mul_const _ hm']
        exact mul_le_mul' (hcol y) le_rfl
    _ = ENNReal.ofReal (C * B) ^ 2 * ∫⁻ y, F y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hF.pow_const 2)]
        ring

/-! ### The change term -/

/-- `H_ν` for `ν = φ μ` is the pairing against `φ`. -/
theorem wl11_Hc_withDensity {μ : Measure (Euc d)} {Cp : ℝ} {h : Euc d → Euc d → ℝ} {φ : Euc d → ℝ}
    (hφm : Measurable φ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ Cp) (x : Euc d) (hix : Integrable (h x) μ) :
    wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (φ y)) x = ∫ y, φ y * h x y ∂μ ∧
      Integrable (fun y => φ y * h x y) μ := by
  have hint : Integrable (fun y => φ y * h x y) μ := by
    refine (hix.norm.const_mul Cp).mono' (hφm.aestronglyMeasurable.mul hix.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs (φ y), abs_of_nonneg (hφ y).1]
    exact mul_le_mul_of_nonneg_right (hφ y).2 (norm_nonneg _)
  refine ⟨?_, hint⟩
  unfold wr14a_Hc
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (φ y))
    (ENNReal.measurable_ofReal.comp hφm)
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφ y).1]

/-- **The change term** (Schur test with the kernel `1 + K`): for `ν = φ μ`, `π = θ μ`, `0 ≤ φ, θ ≤ C_p`,
`∫ |H_ν - H_π|² dπ ≤ c C_p B² ‖φ - θ‖²_{L²(μ)}`. -/
theorem wl11_change_term_le (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ {B : ℝ} {h : Euc d → Euc d → ℝ},
      Measurable (fun p : Euc d × Euc d => h p.1 p.2) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      ∀ {φ θ : Euc d → ℝ}, Measurable φ → Measurable θ → (∀ x, 0 ≤ φ x ∧ φ x ≤ Cp) →
      (∀ x, 0 ≤ θ x ∧ θ x ≤ Cp) →
      ∫⁻ x, ‖wr14a_Hc h ((HRS.Whole.withDensityReal ρ).withDensity fun y => ENNReal.ofReal (φ y)) x -
          wr14a_Hc h ((HRS.Whole.withDensityReal ρ).withDensity fun y => ENNReal.ofReal (θ y)) x‖ₑ ^ 2
        ∂((HRS.Whole.withDensityReal ρ).withDensity fun y => ENNReal.ofReal (θ y)) ≤
        ENNReal.ofReal (c * Cp * B ^ 2) * (eLpNorm (fun y => φ y - θ y) 2 (HRS.Whole.withDensityReal ρ)) ^ 2 := by
  obtain ⟨CS, hCS0, hCS⟩ := wl11_schur_L2 hd A
  obtain ⟨C1, hC10, hC1⟩ := wl_schur hd A
  refine ⟨CS ^ 2, by positivity, fun ρ hρ hA {Cp} hCp {B} {h} hm hsym hh {φ θ} hφm hθm hφ hθ => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hB0, hrows, -⟩ := hC1 ρ hρ hA B h hm hh
  set g : Euc d → ℝ := fun y => φ y - θ y with hg
  have hgm : Measurable g := hφm.sub hθm
  have hΔ : ∀ x, ‖wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (φ y)) x -
      wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (θ y)) x‖ₑ ≤
        ∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ := by
    intro x
    obtain ⟨e1, i1⟩ := wl11_Hc_withDensity hφm hφ x (hrows x).1
    obtain ⟨e2, i2⟩ := wl11_Hc_withDensity hθm hθ x (hrows x).1
    have e : wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (φ y)) x -
        wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (θ y)) x = ∫ y, g y * h x y ∂μ := by
      rw [e1, e2, ← integral_sub i1 i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg]; ring
    rw [e]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal_abs (h x y), mul_comm]
  have hschur := hCS ρ hρ hA B h hm hsym hh (fun y => ‖g y‖ₑ) hgm.enorm
  calc ∫⁻ x, ‖wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (φ y)) x -
          wr14a_Hc h (μ.withDensity fun y => ENNReal.ofReal (θ y)) x‖ₑ ^ 2
        ∂(μ.withDensity fun y => ENNReal.ofReal (θ y))
      ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ) ^ 2
          ∂(μ.withDensity fun y => ENNReal.ofReal (θ y)) :=
        lintegral_mono fun x => pow_le_pow_left' (hΔ x) 2
    _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ) ^ 2 ∂(ENNReal.ofReal Cp • μ) :=
        lintegral_mono' (wl11_withDensity_le fun x => (hθ x).2) le_rfl
    _ = ENNReal.ofReal Cp * ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ) ^ 2 ∂μ := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal (CS * B) ^ 2 * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ) :=
        mul_le_mul' le_rfl hschur
    _ = ENNReal.ofReal (CS ^ 2 * Cp * B ^ 2) * (eLpNorm g 2 μ) ^ 2 := by
        rw [HRS.Quad.lintegral_enorm_sq_eq_eLpNorm_sq hgm.aestronglyMeasurable]
        have e : ENNReal.ofReal (CS ^ 2 * Cp * B ^ 2) =
            ENNReal.ofReal Cp * ENNReal.ofReal (CS * B) ^ 2 := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hCp]
          congr 1; ring
        rw [e]; ring

/-! ### Integrability conjuncts of `QuadraticVarianceBound` -/

/-- For `ν ≤ C_p μ` a probability measure and `|h| ≤ B (1 + K)`: `h(x, ·) ∈ L¹(ν)` for every `x`, and
`h ∈ L¹(ν ⊗ ν)`. -/
theorem wl11_qvb_integrable (hd : 2 ≤ d) (A : ℝ) : ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      IsProbabilityMeasure ν → ∀ {B : ℝ} {h : Euc d → Euc d → ℝ},
      Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      (∀ x, Integrable (fun y => h x y) ν) ∧ Integrable (fun p : Euc d × Euc d => h p.1 p.2) (ν.prod ν) := by
  obtain ⟨c, hc0, hHc⟩ := wl10_Hc_bound hd A
  intro ρ hρ hA ν Cp hν hCp hνp B h hm hh
  have hB : 0 ≤ B := wl2_B_nonneg (by omega) hh
  have h1 : ∀ x, Integrable (fun y => h x y) ν := fun x =>
    wl10_integrable_of_env_bound hd A ρ hρ hA hν hCp hB (wr14a_measurable_h_x hm x)
      (fun y hy => hh x y (Ne.symm hy))
  refine ⟨h1, ?_⟩
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall h1, ?_⟩
  have hbd : ∀ x, |∫ y, ‖h x y‖ ∂ν| ≤ c * Cp * B := by
    intro x
    have := hHc ρ hρ hA hν hCp hB (h := fun x y => |h x y|) (fun x y hxy => by
      rw [abs_abs]; exact hh x y hxy) x
    simpa [wr14a_Hc, Real.norm_eq_abs] using this
  have hmeas : Measurable (fun x : Euc d => ∫ y, ‖h x y‖ ∂ν) :=
    (hm.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable (c * Cp * B)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hbd x

/-! ### The calibrated reference as a pinned law -/

/-- **`R_N` is a pinned law with `κ ≤ 1/2`** (the set-up of `wl_quad_ref`): for `M ≥ M₀` there is `N₀ ≥ 2` such that
for every `ρ, β ∈ (0, β₊], N ≥ N₀` and weak potential `V` with `V.q = q_M` there is a weak potential `V'` (kernel `q_M`,
field `ψ_R`) with `κ(V', β) ≤ 1/2` and `wl9_RN μ M V β N = pinnedLaw V' (β/N) N ∅`. -/
theorem wl11_ref_pinned (hd : 2 ≤ d) (A βp : ℝ) (hβp : 0 ≤ βp) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M → ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm (d := d) M →
      ∃ V' : WeakPotential (HRS.Whole.withDensityReal ρ), weakKappa V' β ≤ 1 / 2 ∧
        wl9_RN (HRS.Whole.withDensityReal ρ) M V β N =
          pinnedLaw V' (β / (N : ℝ)) N (fun e : Empty => e.elim) := by
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨hCq0, hCqspec⟩ := wl4b_Cq_spec hd A
  set Cq := wl4b_Cq d A with hCq
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Mf : ℝ := βp * Cq + 1 with hMf
  set M1f : ℝ := βp * Cl' + 1 + βp * Cq with hM1f
  have hMf0 : 0 ≤ Mf := by positivity
  have hM1f0 : 0 ≤ M1f := by positivity
  obtain ⟨M0, hM0, hhead⟩ := wl9_head (d := d) (by omega) Cq βp Mf M1f
  refine ⟨M0, hM0, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans hM0 hM
  obtain ⟨N0, hN0⟩ := wl_field_small hd A βp 0 M hM1
  refine ⟨max N0 2, le_max_right _ _, fun ρ hρ hA β hβ hββp N hN V hV => ?_⟩
  have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  haveI := wl_isProb hρ
  obtain ⟨-, hℓ, hℓle, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  have hq := hCqspec ρ hρ hA M hM1
  set a : ℝ := Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) with hadef
  have ha : 0 ≤ a := mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have haC : a ≤ Cq := by
    calc a ≤ Cq * 1 := mul_le_mul_of_nonneg_left (wl9_rpow_le_one M hM1) hCq0
      _ = Cq := mul_one _
  have hm' : ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ Cl' := hℓle.trans (le_max_left _ _)
  have hF : WlFam 0 β N N (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : Euc d)) (fun _ => (0 : ℝ)) :=
    { one_le := by omega
      n_le := le_rfl
      β_nonneg := hβ.le
      p_le := by norm_num
      t_nonneg := fun a => a.elim0
      t_le := fun a => a.elim0
      v_meas := measurable_const
      v_bdd := fun x => by simp }
  have hc : ∀ x, |inner ℝ (wl9_tN (HRS.Whole.withDensityReal ρ) M V β N)
      (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x)| ≤ 1 := fun x =>
    hN0 ρ hρ hA β hβ hββp N N hNN0 (by omega) 0 (fun _ => (0 : ℝ)) (fun _ => (0 : Euc d)) (fun _ => 0) hF V hV x
  have hN0pos : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0pos
  set lam : ℝ := β / (N : ℝ) with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le hNpos.le
  have hlam_le : lam ≤ β := by
    rw [hlamdef, div_le_iff₀ hNpos]
    exact le_mul_of_one_le_right hβ.le (by exact_mod_cast hN0pos)
  have hψ : IsField (HRS.Whole.withDensityReal ρ) (wl9_psiR (HRS.Whole.withDensityReal ρ) M V β N)
      (β * a + 1) (lam * Cl' + 1) :=
    wl9_isField_psiR hq ha hℓ hm' hβ.le hN0pos V hc
  set V' : WeakPotential (HRS.Whole.withDensityReal ρ) := wlPot hq ha hψ with hV'
  have hV'γ : V'.γ = a := rfl
  have hβaC : β * a ≤ βp * Cq := mul_le_mul hββp haC ha hβp
  have hMle : β * a + 1 ≤ Mf := by linarith
  have h1 : lam * Cl' ≤ βp * Cl' := mul_le_mul (hlam_le.trans hββp) le_rfl hCl'0 hβp
  have hM1le : lam * Cl' + 1 ≤ M1f := by linarith [mul_nonneg hβp hCq0]
  have hs : β * a ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1))) :=
    (mul_le_mul_of_nonneg_right hββp ha).trans (hhead M hM)
  have hsψ : β * a ≤ min 1 (1 / (16 * Real.exp ((β * a + 1) + (lam * Cl' + 1) + 1))) :=
    wl9_hs_mono hMle hM1le hs
  have hκ : weakKappa V' β ≤ 1 / 2 := (wl_kappa_lt_half hq ha hψ hβ.le hsψ).le
  refine ⟨V', hκ, ?_⟩
  rw [wl9_RN_eq hq ha hℓ hm' hβ.le hN0pos V hc,
    wl5_fieldLaw_congr_q (V' := V') (by rw [hV]; rfl) _ _ _, wl5_pinnedLaw_empty V' lam N]
  rfl

end HRS.MS.Wl
