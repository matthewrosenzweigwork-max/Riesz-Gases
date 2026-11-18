import HRS.MS.R26T8AP10a15

/-!
# S8.2 T8A P10a (part 16): the vector field `h = ρ ∇Q(·,y)` satisfies `R26P10Hyp`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The Riesz map as a real continuous linear map. -/
def r26t8a_Rz (d : ℕ) : (Euc d →L[ℝ] ℝ) →L[ℝ] Euc d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ => WithLp.toLp 2 (fun j => φ (EuclideanSpace.single j 1))
      map_add' := fun φ ψ => by ext j; simp
      map_smul' := fun c φ => by ext j; simp }

theorem r26t8a_gradient_eq_Rz (f : Euc d → ℝ) :
    gradient f = fun w => r26t8a_Rz d (fderiv ℝ f w) := by
  funext w; ext j
  rw [r26t8a_gradient_coord]
  simp [r26t8a_Rz]

theorem r26t8a_fderiv_gradient_le (f : Euc d → ℝ) (u : Euc d)
    (hu : DifferentiableAt ℝ (fderiv ℝ f) u) :
    ‖fderiv ℝ (gradient f) u‖ ≤ ‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖ := by
  have : gradient f = (r26t8a_Rz d) ∘ fderiv ℝ f := r26t8a_gradient_eq_Rz f
  rw [this, ((r26t8a_Rz d).hasFDerivAt.comp u hu.hasFDerivAt).fderiv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem r26t8a_norm_gradient (f : Euc d → ℝ) (u : Euc d) : ‖gradient f u‖ = ‖fderiv ℝ f u‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

theorem r26t8a_p10a_gp_of_poly {y : Euc d} {e M c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D) {φ : Euc d → ℝ}
    (h : ∀ u, u ≠ y → |φ u| ≤ D * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-e))) :
    R26P10GP y e φ := by
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
  refine ⟨D * Cp, c / 2, mul_nonneg hD hCp0, by positivity, fun u hu => (h u hu).trans ?_⟩
  have hp : 0 ≤ 1 + ‖u - y‖ ^ (-e) := by positivity
  have := hCp ‖u‖ (norm_nonneg _)
  calc D * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-e))
      = D * ((1 + ‖u‖) ^ M * Real.exp (-c * ‖u‖ ^ 2)) * (1 + ‖u - y‖ ^ (-e)) := by ring
    _ ≤ D * (Cp * Real.exp (-(c / 2) * ‖u‖ ^ 2)) * (1 + ‖u - y‖ ^ (-e)) := by
        gcongr
    _ = _ := by ring

theorem r26t8a_p10a_hyp (hd : 2 ≤ d) {k b : ℕ} {M σ A : ℝ} (hM : 0 ≤ M) (hσ : σ < d) (hA : 0 ≤ A)
    {Q : Euc d → Euc d → ℝ} (hQ : Conormal (k + 2) b M (σ - 2) A Q) {ρ : Euc d → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) {Cρ c : ℝ} (hCρ : 0 ≤ Cρ) (hc : 0 < c)
    (hb1 : ∀ x, |ρ x| ≤ Cρ * Real.exp (-c * ‖x‖ ^ 2))
    (hb2 : ∀ x, ‖fderiv ℝ ρ x‖ ≤ Cρ * Real.exp (-c * ‖x‖ ^ 2)) (y : Euc d) :
    ∃ τ : ℝ, R26P10Hyp d y τ (fun u => ρ u • gradient (fun v => Q v y) u) := by
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max (σ - 1) 0 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact le_max_right _ _
  have hm1 : σ - 1 ≤ m := by rw [hm]; exact le_max_left _ _
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmd : m < d - 1 := by
    rw [hm]; exact max_lt (by linarith) (by linarith)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (d - 1 - m) / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  refine ⟨m + η, ?_⟩
  have hτ0 : 0 < m + η := by linarith
  have hτd : m + η + 1 < d := by rw [hη] at *; linarith
  set τ := m + η with hτ
  set f : Euc d → ℝ := fun v => Q v y with hf
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 f {y}ᶜ := by
    have hg : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun v : Euc d => (v, y)) :=
      contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    have := hQ.1.comp hg.contDiffOn hmaps
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) {y}ᶜ :=
    hf2.fderiv_of_isOpen hopen (by rw [one_add_one_eq_two])
  have hgrad : ContDiffOn ℝ 1 (gradient f) {y}ᶜ := by
    rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).contDiff.comp_contDiffOn hDf
  have hC1 : ContDiffOn ℝ 1 (fun u => ρ u • gradient f u) {y}ᶜ :=
    (hρ.of_le (by exact_mod_cast le_top)).contDiffOn.smul hgrad
  -- jet bounds
  obtain ⟨K1, hK10, hK1⟩ := r26t8a_p10a_Tj_bound hchi (k := k) (b := b) (M := M) (σ := σ - 2) hM
    (j := 1) (by omega) (e := τ) (by rw [hτ]; push_cast; linarith) hτ0
  obtain ⟨K2, hK20, hK2⟩ := r26t8a_p10a_Tj_bound hchi (k := k) (b := b) (M := M) (σ := σ - 2) hM
    (j := 2) (by omega) (e := τ + 1) (by rw [hτ]; push_cast; linarith) (by linarith)
  have hT1 : ∀ u, u ≠ y → ‖fderiv ℝ f u‖ ≤
      K1 * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ)) := fun u hu => by
    have := hK1 A hA hQ y u hu
    rwa [norm_iteratedFDeriv_one] at this
  have hT2 : ∀ u, u ≠ y → ‖fderiv ℝ (fderiv ℝ f) u‖ ≤
      K2 * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-(τ + 1))) := fun u hu => by
    have := hK2 A hA hQ y u hu
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  have hNR := norm_nonneg (r26t8a_Rz d)
  refine ⟨hd, hτ0, hτd, hC1, ?_, ?_⟩
  · refine r26t8a_p10a_gp_of_poly (M := M) (D := Cρ * (K1 * A * jbracket y ^ M)) hc
      (by positivity) fun u hu => ?_
    rw [abs_of_nonneg (norm_nonneg _), norm_smul, Real.norm_eq_abs, r26t8a_norm_gradient]
    have h1 := hT1 u hu
    have hp : 0 ≤ (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ)) := by positivity
    calc |ρ u| * ‖fderiv ℝ f u‖ ≤ (Cρ * Real.exp (-c * ‖u‖ ^ 2)) *
          (K1 * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ))) :=
          mul_le_mul (hb1 u) h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have g1 : R26P10GP y (τ + 1) (fun u => |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖)) := by
      refine r26t8a_p10a_gp_of_poly (M := M) (D := Cρ * (‖r26t8a_Rz d‖ * (K2 * A * jbracket y ^ M))) hc
        (by positivity) fun u hu => ?_
      rw [abs_of_nonneg (by positivity)]
      have h2 := hT2 u hu
      calc |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖) ≤ (Cρ * Real.exp (-c * ‖u‖ ^ 2)) *
            (‖r26t8a_Rz d‖ * (K2 * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-(τ + 1))))) :=
            mul_le_mul (hb1 u) (mul_le_mul_of_nonneg_left h2 hNR) (by positivity) (by positivity)
        _ = _ := by ring
    have g2 : R26P10GP y τ (fun u => ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖) := by
      refine r26t8a_p10a_gp_of_poly (M := M) (D := Cρ * (K1 * A * jbracket y ^ M)) hc
        (by positivity) fun u hu => ?_
      rw [abs_of_nonneg (by positivity)]
      have h1 := hT1 u hu
      calc ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖ ≤ (Cρ * Real.exp (-c * ‖u‖ ^ 2)) *
            (K1 * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-τ))) :=
            mul_le_mul (hb2 u) h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have g12 := r26t8a_p10a_gp_add g1 (r26t8a_p10a_gp_mono g2 hτ0.le (by linarith))
    refine r26t8a_p10a_gp_of_bound g12 zero_le_one fun u hu => ?_
    have hdf : DifferentiableAt ℝ (gradient f) u :=
      (hgrad.contDiffAt (hopen.mem_nhds (by simpa using hu))).differentiableAt (by simp)
    have hdρ : DifferentiableAt ℝ ρ u := (hρ.differentiable (by simp)) u
    have hDD : DifferentiableAt ℝ (fderiv ℝ f) u :=
      (hDf.contDiffAt (hopen.mem_nhds (by simpa using hu))).differentiableAt (by simp)
    have hnn : 0 ≤ |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖) + ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖ := by
      positivity
    rw [fderiv_fun_smul hdρ hdf, one_mul, abs_of_nonneg hnn, abs_norm]
    refine (norm_add_le (ρ u • fderiv ℝ (gradient f) u) ((fderiv ℝ ρ u).smulRight (gradient f u))).trans ?_
    have e1 : ‖ρ u • fderiv ℝ (gradient f) u‖ ≤ |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (r26t8a_fderiv_gradient_le f u hDD) (abs_nonneg _)
    have e2 : ‖(fderiv ℝ ρ u).smulRight (gradient f u)‖ ≤ ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply, r26t8a_norm_gradient]
    linarith

end HRS.MS.R26T8A
