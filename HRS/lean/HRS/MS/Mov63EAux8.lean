import HRS.MS.Mov63EAux7

/-!
# S6.3, packet N6 (part 8): mass, probability density, and the weak formulation for all `C_b²` tests

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.

* `mne_mass_zero`, `mne_isProb`: `MovMassZero` gives `∫ ρ_u = 1`; with `ρ_u ≥ 0` it is an `IsProbDensity`.
* `mneP` (`ρ_t = ρ + √ρ V_{v(max t 0)}`), `mne_fubini_glob`, `mne_integrand`, **`mne_weak`**: the `weak` field of `IsWholeMeanFieldSolution` for every `ψ` with `MemCb 2 ψ`
  and every `t ≥ 0`, under the hypothesis `hnn : ∀ t ≥ 0, ∀ x, 0 ≤ ρ_t x`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Weak

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ)

include H in
/-- The mass condition says `∫ √ρ V_u = 0`. -/
lemma mne_mass_zero (u : OscSpace d (m : ℝ)) (hu : MovMassZero ρ (mnd_m_nonneg hm) u) :
    ∫ x, mnc_hu ρ (mne_hn hm) u x = 0 := by
  have hmem := mneV_memOsc hm u
  have hL2 : MemLp (mneV hm u) 2 (volume : Measure (Euc d)) := (mo_mono (mnd_m_nonneg hm) hmem).1.1
  have hj : mov2d_j (mnd_m_nonneg hm) u = OscSpace.ofFun 0 (mneV hm u) := by
    have := mov2d_j_ofFun (mnd_m_nonneg hm) hmem
    rwa [mneV_ofFun hm u] at this
  unfold MovMassZero at hu
  rw [hj, mov2d_Phi_ofFun hL2, mnb_inner_sqrt H hL2] at hu
  exact hu

include H in
lemma mne_isProb (u : OscSpace d (m : ℝ)) (hu : MovMassZero ρ (mnd_m_nonneg hm) u)
    (hnn : ∀ x, 0 ≤ mneRho ρ hm u x) : Whole.IsProbDensity (mneRho ρ hm u) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H (mne_hn hm)
  obtain ⟨Kρ, hKρ, hρW⟩ := mnc_rgW_rho H
  have hch : 0 ≤ K1 * ‖u‖ := mul_nonneg hK1 (norm_nonneg _)
  have iρ : Integrable ρ := mnc_rgW_integrable hd1 hKρ hρW
  have ih : Integrable (mnc_hu ρ (mne_hn hm) u) := mnc_rgW_integrable hd1 hch (hW u)
  refine ⟨hnn, (mne_rho_cd hm H u).continuous.measurable, ?_⟩
  show ∫ x, (ρ x + mnc_hu ρ (mne_hn hm) u x) = 1
  rw [integral_add iρ ih, mne_mass_zero hm H u hu, add_zero]
  exact H.hρ.2.1.integral_one


variable {v : ℝ → OscSpace d (m : ℝ)}

/-- The density family `ρ_t = ρ + √ρ V_{v(max t 0)}` (constant for `t < 0`). -/
def mneP (d : ℕ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (v : ℝ → OscSpace d (m : ℝ)) (t : ℝ) :
    Euc d → ℝ :=
  fun y => ρ y + mnc_hu ρ (mne_hn hm) (v (max t 0)) y

lemma mneP_eq {t : ℝ} (ht : 0 ≤ t) : mneP d ρ hm v t = mneRho ρ hm (v t) := by
  funext y
  simp only [mneP, max_eq_left ht]

include H in
/-- Global Fubini for the tested primitive (`C_b²` tests). -/
lemma mne_fubini_glob (hmild : MneMild H hm v) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) =
      ∫ τ in (0 : ℝ)..t, ∫ x, ψ x * mneEc d s q β ρ hm v (τ, x) := by
  have hc := mne_Ec_cont hm H hmild
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (hmild.cont.mono Icc_subset_Ici_self)
  obtain ⟨KG, hKG0, hKG⟩ := mne_flux_bound hm H M
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, b0, b1, b2⟩ := mne_cb2_bounds hψ
  have hψc : Continuous ψ := hψ.1.continuous
  set F : ℝ × Euc d → ℝ := fun p => ψ p.2 * mneEc d s q β ρ hm v p with hF
  have hFc : Continuous F := (hψc.comp continuous_snd).mul hc
  have hmeas : (volume.restrict (Ioc (0 : ℝ) t)).prod (volume : Measure (Euc d)) =
      (volume : Measure (ℝ × Euc d)).restrict (Ioc 0 t ×ˢ univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hg : Integrable (fun p : ℝ × Euc d => (B0 * KG) * (1 * (1 + ‖p.2‖) ^ (-((d : ℝ) + 1))))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod (volume : Measure (Euc d))) := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc (0 : ℝ) t)) :=
      integrableOn_const (by simp)
    exact (h1.mul_prod (mne_integrableG (d := d))).const_mul _
  have hint : Integrable (Function.uncurry fun (τ : ℝ) (x : Euc d) => ψ x * mneEc d s q β ρ hm v (τ, x))
      ((volume.restrict (uIoc (0 : ℝ) t)).prod (volume : Measure (Euc d))) := by
    rw [uIoc_of_le ht, hmeas]
    rw [hmeas] at hg
    refine hg.mono' hFc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)).2 (Eventually.of_forall fun p hp => ?_)
    have hτ : p.1 ∈ Icc (0 : ℝ) t := ⟨hp.1.1.le, hp.1.2⟩
    have hv : ‖v p.1‖ ≤ M := hM p.1 hτ
    have := (hKG (v p.1) hv p.2).2.2.2.2.2.2
    rw [Real.norm_eq_abs]
    show |ψ p.2 * mneEc d s q β ρ hm v p| ≤ _
    have e : mneEc d s q β ρ hm v p = movDiv (mneY d s q β ρ hm (v p.1)) p.2 := mneEc_eq hm hp.1.1.le p.2
    rw [e, abs_mul]
    calc |ψ p.2| * |movDiv (mneY d s q β ρ hm (v p.1)) p.2| ≤ B0 * (KG * (1 + ‖p.2‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul (b0 _) this (abs_nonneg _) hB0
      _ = _ := by ring
  have e : ∀ x : Euc d, ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) =
      ∫ τ in (0 : ℝ)..t, ψ x * mneEc d s q β ρ hm v (τ, x) := fun x => by
    rw [intervalIntegral.integral_const_mul]
  simp_rw [e]
  exact (intervalIntegral_integral_swap hint).symm


include H in
/-- The weak-form integrand at `ρ_u` (a probability density) is the integral of the flux divergence against `ψ`. -/
lemma mne_integrand (u : OscSpace d (m : ℝ)) (hp : Whole.IsProbDensity (mneRho ρ hm u)) {ψ : Euc d → ℝ}
    (hψ : MemCb 2 ψ) :
    Whole.pair (Whole.withDensityReal (mneRho ρ hm u))
        (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian ψ x -
          inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient ψ x)) +
      interactionPairingW (quadraticGradientDyn d s q β) ψ (Whole.withDensityReal (mneRho ρ hm u))
        (Whole.withDensityReal (mneRho ρ hm u)) =
    ∫ x, movDiv (mneY d s q β ρ hm u) x * ψ x := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hreg : RegSliceRd (mneRho ρ hm u) := mnc_regSlice_hu H (mne_hn hm) u hp
  set D := quadraticGradientDyn d s q β with hD
  have hM : ∀ y : Euc d, Torus.matVec D.M y = -y := fun y => by simp [hD, quadraticGradientDyn, Torus.matVec]
  have hI := (self_pairing_rd_proof D hd1 H.hs0 H.hsd hreg hψ).1
  have hI' : interactionPairingW D ψ (Whole.withDensityReal (mneRho ρ hm u)) (Whole.withDensityReal (mneRho ρ hm u)) =
      ∫ x, -(mneRho ρ hm u x * inner ℝ (gradient ψ x) (movForce d s (mneRho ρ hm u) x)) := by
    rw [hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : convGradConvW (rieszKernelGrad d D.s) (mneRho ρ hm u) x = movForce d s (mneRho ρ hm u) x := rfl
    simp only [this, hM, inner_neg_right, mul_neg]
  have hpair : Whole.pair (Whole.withDensityReal (mneRho ρ hm u))
      (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) =
      ∫ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (q • x : Euc d) (gradient ψ x)) := by
    rw [Whole.pair, dc1a_integral_withDensity hp.measurable hp.nonneg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (gradient (confinement q) x) (gradient ψ x)) = _
    rw [movtr_gradient_confinement q x]
  rw [hpair, hI', mne_J hm H hψ u]

include H in
lemma mne_int_Rpsi (u : OscSpace d (m : ℝ)) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    Integrable (fun x => mneRho ρ hm u x * ψ x) := by
  obtain ⟨KG, hKG0, hKG⟩ := mne_flux_bound hm H ‖u‖
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, b0, b1, b2⟩ := mne_cb2_bounds hψ
  refine mne_int_of_bound (K := KG * B0) ((mne_rho_cd hm H u).continuous.mul hψ.1.continuous) (fun x => ?_)
  calc _ ≤ (KG * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) * B0 :=
        mne_abs_mul_le (hKG u le_rfl x).1 (b0 x) (mul_nonneg hKG0 (by positivity))
    _ = _ := by ring

include H in
/-- **N6a: the weak formulation for all `C_b²` test functions** (given nonnegativity of `ρ_t`, `t ≥ 0`, which N7 provides): the
conclusion is exactly the `weak` field of `IsWholeMeanFieldSolution` for the family `ρ_t = mneP`. -/
theorem mne_weak (hmild : MneMild H hm v) (hnn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ mneP d ρ hm v t x)
    {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) {t : ℝ} (ht : 0 ≤ t) :
    Whole.pair (Whole.withDensityReal (mneP d ρ hm v t)) ψ -
        Whole.pair (Whole.withDensityReal (mneP d ρ hm v 0)) ψ =
      ∫ r in Icc 0 t,
        (Whole.pair (Whole.withDensityReal (mneP d ρ hm v r))
            (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian ψ x -
              inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient ψ x)) +
          interactionPairingW (quadraticGradientDyn d s q β) ψ (Whole.withDensityReal (mneP d ρ hm v r))
            (Whole.withDensityReal (mneP d ρ hm v r))) := by
  have hprob : ∀ r, 0 ≤ r → Whole.IsProbDensity (mneRho ρ hm (v r)) := fun r hr =>
    mne_isProb hm H (v r) (hmild.mass r hr) (fun x => by
      have := hnn r hr x
      rwa [mneP_eq hm hr] at this)
  -- the right-hand side
  have hR : ∫ r in Icc (0 : ℝ) t,
        (Whole.pair (Whole.withDensityReal (mneP d ρ hm v r))
            (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian ψ x -
              inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient ψ x)) +
          interactionPairingW (quadraticGradientDyn d s q β) ψ (Whole.withDensityReal (mneP d ρ hm v r))
            (Whole.withDensityReal (mneP d ρ hm v r))) =
      ∫ r in Icc (0 : ℝ) t, ∫ x, ψ x * mneEc d s q β ρ hm v (r, x) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    have h1 := mne_integrand hm H (v r) (hprob r hr.1) hψ
    simp only [mneP_eq hm hr.1]
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show movDiv (mneY d s q β ρ hm (v r)) x * ψ x = ψ x * mneEc d s q β ρ hm v (r, x)
    rw [mneEc_eq hm hr.1 x, mul_comm]
  rw [hR]
  -- the left-hand side
  have hL : ∀ r, 0 ≤ r → Whole.pair (Whole.withDensityReal (mneP d ρ hm v r)) ψ =
      ∫ x, mneRho ρ hm (v r) x * ψ x := fun r hr => by
    rw [mneP_eq hm hr, Whole.pair, dc1a_integral_withDensity (hprob r hr).measurable (hprob r hr).nonneg]
  rw [hL t ht, hL 0 le_rfl, ← integral_sub (mne_int_Rpsi hm H (v t) hψ) (mne_int_Rpsi hm H (v 0) hψ)]
  have e1 : ∀ x, mneRho ρ hm (v t) x * ψ x - mneRho ρ hm (v 0) x * ψ x =
      ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) := fun x => by
    rw [← mne_pointwise hm H hmild ht x]
    simp only [mneRho]
    ring
  simp_rw [e1]
  rw [mne_fubini_glob hm H hmild hψ ht, intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]

end Weak

end HRS.MS.Mov63

end
