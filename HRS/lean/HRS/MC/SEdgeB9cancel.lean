import HRS.MC.SEdgeVocab

/-!
# Packet B9cancel: the cubic cancellation (relocation of `sed_B9cancel`)

Proof of the statement `HRS.MC.SEdge.sed_B9cancel` (SEdgeSpec.lean) in its own file.  The spec theorem
stays `sorry`; the `example` at the end ties this proof to it by `type_of%`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B9cancel

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

/-- The `k`-th component of `∇g`. -/
abbrev b9c_G (d : ℕ) (s : ℝ) (k : Fin d) (z : Torus d) : ℝ := (periodicRieszGrad d s z) k

theorem b9c_G_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (k : Fin d) :
    Integrable (b9c_G d s k) := by
  have h := HRS.Q66.q66_gradKernel_integrable hd hs0 (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  exact (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).integrable_comp h

theorem b9c_G_meas (hs : s < (d : ℝ) / 2) (hd : 2 ≤ d) (k : Fin d) : Measurable (b9c_G d s k) := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous.measurable).comp
    (HRS.KernelGrad.measurable_periodicRieszGrad hsd)

theorem b9c_G_odd (hd : 2 ≤ d) (hs : s < (d : ℝ) / 2) (k : Fin d) (z : Torus d) :
    b9c_G d s k (-z) = - b9c_G d s k z := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact HRS.Q66.q66_gradKernel_odd hsd z k

theorem b9c_bdd {u : Torus d → ℝ} (hu : Continuous u) : ∃ C, ∀ x, ‖u x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

theorem b9c_prod_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (k : Fin d)
    {u w : Torus d → ℝ} (hu : Continuous u) (hw : Continuous w) :
    Integrable (fun p : Torus d × Torus d => u p.1 * (w p.2 * b9c_G d s k (p.1 - p.2))) := by
  have h1 : Integrable (fun p : Torus d × Torus d => (1 : ℝ) * b9c_G d s k (p.1 - p.2))
      ((volume : Measure (Torus d)).prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (f := fun _ : Torus d => (1 : ℝ))
      (integrable_const _) (b9c_G_integrable hd hs0 hs k)
  have h2 : Integrable (fun p : Torus d × Torus d => (u p.1 * w p.2) * b9c_G d s k (p.1 - p.2)) := by
    have h1' : Integrable (fun p : Torus d × Torus d => b9c_G d s k (p.1 - p.2))
        ((volume : Measure (Torus d)).prod volume) := by simpa using h1
    obtain ⟨C1, hC1⟩ := b9c_bdd hu
    obtain ⟨C2, hC2⟩ := b9c_bdd hw
    refine h1'.bdd_mul (f := fun p : Torus d × Torus d => u p.1 * w p.2) (c := C1 * C2) ?_ ?_
    · exact ((hu.comp continuous_fst).mul (hw.comp continuous_snd)).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul]
      exact mul_le_mul (hC1 _) (hC2 _) (norm_nonneg _) ((norm_nonneg _).trans (hC1 p.1))
  refine h2.congr (Eventually.of_forall fun p => ?_)
  simp only
  ring

/-- Antisymmetry of the bilinear form `(u,w) ↦ ∬ u(x) w(y) ∇g(x-y)`. -/
theorem b9c_antisymm (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (k : Fin d)
    {u w : Torus d → ℝ} (hu : Continuous u) (hw : Continuous w) :
    ∫ x, u x * ∫ y, w y * b9c_G d s k (x - y) =
      - ∫ x, w x * ∫ y, u y * b9c_G d s k (x - y) := by
  have hint := b9c_prod_integrable hd hs0 hs k hu hw
  have e1 : ∫ x, u x * ∫ y, w y * b9c_G d s k (x - y) =
      ∫ x, ∫ y, u x * (w y * b9c_G d s k (x - y)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_const_mul]
  rw [e1, integral_integral_swap hint]
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  have e2 : ∀ x : Torus d, u x * (w y * b9c_G d s k (x - y)) =
      -(w y * (u x * b9c_G d s k (y - x))) := by
    intro x
    have : y - x = -(x - y) := by abel
    rw [this, b9c_G_odd hd hs]
    ring
  simp_rw [e2]
  rw [integral_neg, integral_const_mul]

theorem b9c_hs1 (hd : 2 ≤ d) (hs : s < (d : ℝ) / 2) : s < (d : ℝ) - 1 := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder in
theorem b9c_conv_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {w : Torus d → ℝ}
    (hw : Torus.IsSmooth w) (k : Fin d) (x : Torus d) :
    ∫ y, w y * b9c_G d s k (x - y) = Torus.partialDeriv k (convFun (periodicRiesz d s) w) x :=
  HRS.Q66.q66_grad_conv hd hs0 (b9c_hs1 hd hs) (HRS.Q66.q66_isCk_of_smooth hw 1) k x

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder in
theorem b9c_conv_cont (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {w : Torus d → ℝ}
    (hw : Torus.IsSmooth w) (k : Fin d) :
    Continuous (fun x => ∫ y, w y * b9c_G d s k (x - y)) := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have h1 : Torus.IsCk 1 (convFun (periodicRiesz d s) w) :=
    convFun_isCk_one F.integrable (HRS.Q66.q66_isCk_of_smooth hw 1)
  have : (fun x => ∫ y, w y * b9c_G d s k (x - y)) =
      Torus.partialDeriv k (convFun (periodicRiesz d s) w) :=
    funext (b9c_conv_eq hd hs0 hs hw k)
  rw [this]
  exact HRS.PDE.continuous_partialDeriv k _ h1

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder in
theorem b9c_grad_phi (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r φ : Torus d → ℝ}
    (hr : Torus.IsSmooth r)
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) φ x) (k : Fin d) (x : Torus d) :
    Torus.partialDeriv k φ x = Torus.partialDeriv k r x +
      β * ∫ y, (ρ y * r y) * b9c_G d s k (x - y) := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have hHs : Torus.IsSmooth (fun y => ρ y * r y) := HRS.Q66.q66_isSmooth_mul hρ.smooth hr
  have h1 : Torus.IsCk 1 (convFun (periodicRiesz d s) (fun y => ρ y * r y)) :=
    convFun_isCk_one F.integrable (HRS.Q66.q66_isCk_of_smooth hHs 1)
  have hconv : ∀ x, ∫ y, periodicRiesz d s (x - y) * r y ∂(withDensityReal ρ) =
      convFun (periodicRiesz d s) (fun y => ρ y * r y) x := by
    intro x
    rw [integral_withDensityReal_eq ρ hρ.density.measurable (fun y => (hρ.pos y).le)]
    unfold convFun
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  obtain ⟨c, hc⟩ : ∃ c : ℝ, φ = fun y => (r y + β * convFun (periodicRiesz d s) (fun y => ρ y * r y) y) + c := by
    refine ⟨pair (withDensityReal ρ) φ - β * pair (withDensityReal ρ)
      (fun x => ∫ y, periodicRiesz d s (x - y) * r y ∂(withDensityReal ρ)) , funext fun y => ?_⟩
    have := hresp y
    simp only [Kop, projMean] at this
    rw [hconv y] at this
    linarith
  have hr1 : Torus.IsCk 1 r := HRS.Q66.q66_isCk_of_smooth hr 1
  have hb1 : Torus.IsCk 1 (fun y => β * convFun (periodicRiesz d s) (fun y => ρ y * r y) y) :=
    (contDiff_const.mul h1 :
      ContDiff ℝ 1 (fun z => β * Torus.lift (convFun (periodicRiesz d s) (fun y => ρ y * r y)) z))
  have hs1 : Torus.IsCk 1 (fun y => r y + β * convFun (periodicRiesz d s) (fun y => ρ y * r y) y) :=
    (ContDiff.add hr1 hb1 :
      ContDiff ℝ 1 (fun z => Torus.lift r z + (fun z => β * Torus.lift
        (convFun (periodicRiesz d s) (fun y => ρ y * r y)) z) z))
  have hcc : Torus.IsCk 1 (fun _ : Torus d => c) := contDiff_const
  rw [hc, HRS.PDE.MFHolder.partialDeriv_add k hs1 hcc, HRS.PDE.MFHolder.partialDeriv_add k hr1 hb1,
    HRS.PDE.MFAux.partialDeriv_const, HRS.PDE.MFHolder.partialDeriv_const_mul k h1, add_zero,
    ← b9c_conv_eq hd hs0 hs hHs k x]

theorem b9c_int_of_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The convolution `C_k w (x) = ∫ w(y) ∂_k g(x-y) dy`. -/
abbrev b9c_C (d : ℕ) (s : ℝ) (k : Fin d) (w : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, w y * b9c_G d s k (x - y)

theorem b9c_A_term (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {rb rc φb : Torus d → ℝ}
    (hrb : Torus.IsSmooth rb) (hrc : Torus.IsSmooth rc) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j))
    (hrespb : ∀ x, rb x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rb x =
      projMean (withDensityReal ρ) φb x) :
    ∫ x, sed_drift v φb x * rc x ∂(withDensityReal ρ) =
      ∑ k, ((∫ x, (ρ x * (v k x * rc x)) * Torus.partialDeriv k rb x) +
        β * ∫ x, (ρ x * (v k x * rc x)) * b9c_C d s k (fun y => ρ y * rb y) x) := by
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  have hvc : ∀ k, Continuous (v k) := fun k => HRS.Q66.q66_cont_of_smooth (hv k)
  have hrcc : Continuous rc := HRS.Q66.q66_cont_of_smooth hrc
  have hpd : ∀ k, Continuous (Torus.partialDeriv k rb) := fun k =>
    HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hrb k)
  have hHs : Torus.IsSmooth (fun y => ρ y * rb y) := HRS.Q66.q66_isSmooth_mul hρ.smooth hrb
  have hCc : ∀ k, Continuous (b9c_C d s k (fun y => ρ y * rb y)) := fun k =>
    b9c_conv_cont hd hs0 hs hHs k
  have hcoef : ∀ k, Continuous (fun x => ρ x * (v k x * rc x)) := fun k =>
    hρc.mul ((hvc k).mul hrcc)
  rw [integral_withDensityReal_eq ρ hρ.density.measurable (fun y => (hρ.pos y).le)]
  have e1 : ∀ x, ρ x * (sed_drift v φb x * rc x) =
      ∑ k, ((ρ x * (v k x * rc x)) * Torus.partialDeriv k rb x +
        β * ((ρ x * (v k x * rc x)) * b9c_C d s k (fun y => ρ y * rb y) x)) := by
    intro x
    unfold sed_drift
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [b9c_grad_phi hd hs0 hs hρ hrb hrespb k x]
    simp only [b9c_C]
    ring
  simp_rw [e1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add, integral_const_mul]
    · exact b9c_int_of_cont ((hcoef k).mul (hpd k))
    · exact (b9c_int_of_cont ((hcoef k).mul (hCc k))).const_mul _
  · intro k _
    exact (b9c_int_of_cont ((hcoef k).mul (hpd k))).add
      ((b9c_int_of_cont ((hcoef k).mul (hCc k))).const_mul _)

theorem b9c_Qt_term (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {rb rc : Torus d → ℝ}
    (hrb : Torus.IsSmooth rb) (hrc : Torus.IsSmooth rc) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j)) :
    sed_Qt d s ρ v rb rc =
      ∑ k, ((∫ x, (ρ x * (v k x * rb x)) * b9c_C d s k (fun y => ρ y * rc y) x) +
        ∫ x, (ρ x * (v k x * rc x)) * b9c_C d s k (fun y => ρ y * rb y) x) := by
  have hs1 := b9c_hs1 hd hs
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  have hvc : ∀ k, Continuous (v k) := fun k => HRS.Q66.q66_cont_of_smooth (hv k)
  have hrbc : Continuous rb := HRS.Q66.q66_cont_of_smooth hrb
  have hrcc : Continuous rc := HRS.Q66.q66_cont_of_smooth hrc
  have hS1 : Torus.IsSmooth (fun y => ρ y * rb y) := HRS.Q66.q66_isSmooth_mul hρ.smooth hrb
  have hS2 : Torus.IsSmooth (fun y => ρ y * rc y) := HRS.Q66.q66_isSmooth_mul hρ.smooth hrc
  have hS3 : ∀ k, Torus.IsSmooth (fun y => ρ y * (v k y * rc y)) := fun k =>
    HRS.Q66.q66_isSmooth_mul hρ.smooth (HRS.Q66.q66_isSmooth_mul (hv k) hrc)
  have hC1 : ∀ k, Continuous (b9c_C d s k (fun y => ρ y * rb y)) := fun k =>
    b9c_conv_cont hd hs0 hs hS1 k
  have hC2 : ∀ k, Continuous (b9c_C d s k (fun y => ρ y * rc y)) := fun k =>
    b9c_conv_cont hd hs0 hs hS2 k
  have hC3 : ∀ k, Continuous (b9c_C d s k (fun y => ρ y * (v k y * rc y))) := fun k =>
    b9c_conv_cont hd hs0 hs (hS3 k) k
  have hm := fun (k : Fin d) => b9c_antisymm hd hs0 hs k
    (u := fun y => ρ y * rb y) (w := fun y => ρ y * (v k y * rc y))
    (hρc.mul hrbc) (HRS.Q66.q66_cont_of_smooth (hS3 k))
  -- inner integral
  have inner : ∀ x : Torus d, ∫ y, HRS.Q66.q66_hv d s v x y * rb x * rc y ∂(withDensityReal ρ) =
      ∑ k, ((v k x * rb x) * b9c_C d s k (fun y => ρ y * rc y) x -
        rb x * b9c_C d s k (fun y => ρ y * (v k y * rc y)) x) := by
    intro x
    rw [integral_withDensityReal_eq ρ hρ.density.measurable (fun y => (hρ.pos y).le)]
    have e1 : ∀ y, ρ y * (HRS.Q66.q66_hv d s v x y * rb x * rc y) =
        ∑ k, ((v k x * rb x) * ((ρ y * rc y) * b9c_G d s k (x - y)) -
          rb x * ((ρ y * (v k y * rc y)) * b9c_G d s k (x - y))) := by
      intro y
      unfold HRS.Q66.q66_hv
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [b9c_G]
      ring
    simp_rw [e1]
    have i1 : ∀ k : Fin d, Integrable (fun y : Torus d =>
        (v k x * rb x) * ((ρ y * rc y) * b9c_G d s k (x - y))) := fun k =>
      (HRS.Q66.q66_integrable_mulG hd hs0 hs1 x k (hρc.mul hrcc)).const_mul _
    have i2 : ∀ k : Fin d, Integrable (fun y : Torus d =>
        rb x * ((ρ y * (v k y * rc y)) * b9c_G d s k (x - y))) := fun k =>
      (HRS.Q66.q66_integrable_mulG hd hs0 hs1 x k (hρc.mul ((hvc k).mul hrcc))).const_mul _
    have i3 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun y : Torus d =>
        (v k x * rb x) * ((ρ y * rc y) * b9c_G d s k (x - y)) -
          rb x * ((ρ y * (v k y * rc y)) * b9c_G d s k (x - y))) := fun k _ => (i1 k).sub (i2 k)
    rw [integral_finsetSum _ i3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_sub (i1 k) (i2 k), integral_const_mul, integral_const_mul]
  unfold sed_Qt
  simp_rw [inner]
  rw [integral_withDensityReal_eq ρ hρ.density.measurable (fun y => (hρ.pos y).le)]
  have e2 : ∀ x : Torus d, ρ x * ∑ k, ((v k x * rb x) * b9c_C d s k (fun y => ρ y * rc y) x -
        rb x * b9c_C d s k (fun y => ρ y * (v k y * rc y)) x) =
      ∑ k, ((ρ x * (v k x * rb x)) * b9c_C d s k (fun y => ρ y * rc y) x -
        (ρ x * rb x) * b9c_C d s k (fun y => ρ y * (v k y * rc y)) x) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e2]
  have j1 : ∀ k : Fin d, Continuous (fun x => (ρ x * (v k x * rb x)) *
      b9c_C d s k (fun y => ρ y * rc y) x) := fun k =>
    (hρc.mul ((hvc k).mul hrbc)).mul (hC2 k)
  have j2 : ∀ k : Fin d, Continuous (fun x => (ρ x * rb x) *
      b9c_C d s k (fun y => ρ y * (v k y * rc y)) x) := fun k =>
    (hρc.mul hrbc).mul (hC3 k)
  have i3 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x : Torus d =>
      (ρ x * (v k x * rb x)) * b9c_C d s k (fun y => ρ y * rc y) x -
        (ρ x * rb x) * b9c_C d s k (fun y => ρ y * (v k y * rc y)) x) :=
    fun k _ => (b9c_int_of_cont (j1 k)).sub (b9c_int_of_cont (j2 k))
  rw [integral_finsetSum _ i3]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_sub (b9c_int_of_cont (j1 k)) (b9c_int_of_cont (j2 k)), hm k]
  ring

theorem b9c_div_term (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {ra rb rc : Torus d → ℝ} (hra : Torus.IsSmooth ra) (hrb : Torus.IsSmooth rb)
    (hrc : Torus.IsSmooth rc) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * ra x)) :
    ∑ k, ((∫ x, (ρ x * (v k x * rc x)) * Torus.partialDeriv k rb x) +
        ∫ x, (ρ x * (v k x * rb x)) * Torus.partialDeriv k rc x) =
      ∫ x, ρ x * (ra x * rb x * rc x) := by
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  have hvc : ∀ k, Continuous (v k) := fun k => HRS.Q66.q66_cont_of_smooth (hv k)
  have hrbc : Continuous rb := HRS.Q66.q66_cont_of_smooth hrb
  have hrcc : Continuous rc := HRS.Q66.q66_cont_of_smooth hrc
  have hpb : ∀ k, Continuous (Torus.partialDeriv k rb) := fun k =>
    HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hrb k)
  have hpc : ∀ k, Continuous (Torus.partialDeriv k rc) := fun k =>
    HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hrc k)
  have hbc : Torus.IsSmooth (fun y => rb y * rc y) := HRS.Q66.q66_isSmooth_mul hrb hrc
  have hpv : ∀ k, Torus.IsSmooth (fun y => ρ y * v k y) := fun k =>
    HRS.Q66.q66_isSmooth_mul hρ.smooth (hv k)
  have hpvc : ∀ k, Continuous (Torus.partialDeriv k (fun y => ρ y * v k y)) := fun k =>
    HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv (hpv k) k)
  have hk : ∀ k : Fin d, ((∫ x, (ρ x * (v k x * rc x)) * Torus.partialDeriv k rb x) +
        ∫ x, (ρ x * (v k x * rb x)) * Torus.partialDeriv k rc x) =
      -∫ x, Torus.partialDeriv k (fun y => ρ y * v k y) x * (rb x * rc x) := by
    intro k
    have hadd : ∫ x, ((ρ x * (v k x * rc x)) * Torus.partialDeriv k rb x +
        (ρ x * (v k x * rb x)) * Torus.partialDeriv k rc x) =
        (∫ x, (ρ x * (v k x * rc x)) * Torus.partialDeriv k rb x) +
        ∫ x, (ρ x * (v k x * rb x)) * Torus.partialDeriv k rc x :=
      integral_add (b9c_int_of_cont ((hρc.mul ((hvc k).mul hrcc)).mul (hpb k)))
        (b9c_int_of_cont ((hρc.mul ((hvc k).mul hrbc)).mul (hpc k)))
    rw [← hadd]
    rw [HRS.PDE.integral_partialDeriv_mul k (fun y => ρ y * v k y) (fun y => rb y * rc y)
      (HRS.Q66.q66_isCk_of_smooth (hpv k) 1) (HRS.Q66.q66_isCk_of_smooth hbc 1)]
    rw [neg_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [HRS.PDE.MFAux.partialDeriv_mul k rb rc (HRS.Q66.q66_isCk_of_smooth hrb 1)
      (HRS.Q66.q66_isCk_of_smooth hrc 1)]
    ring
  simp_rw [hk]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Finset.sum_mul, hdiv x]
    ring
  · intro k _
    exact b9c_int_of_cont ((hpvc k).mul (hrbc.mul hrcc))

theorem sed_B9cancel_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ra rb rc φb φc : Torus d → ℝ}
    (hra : Torus.IsSmooth ra) (hrb : Torus.IsSmooth rb) (hrc : Torus.IsSmooth rc)
    (hφb : Torus.IsSmooth φb) (hφc : Torus.IsSmooth φc) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * ra x))
    (hrespb : ∀ x, rb x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rb x =
      projMean (withDensityReal ρ) φb x)
    (hrespc : ∀ x, rc x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rc x =
      projMean (withDensityReal ρ) φc x) :
    ∫ x, sed_drift v φb x * rc x ∂(withDensityReal ρ) +
        ∫ x, sed_drift v φc x * rb x ∂(withDensityReal ρ) -
        β * sed_Qt d s ρ v rb rc =
      ∫ x, ra x * rb x * rc x ∂(withDensityReal ρ) := by
  rw [b9c_A_term hd hs0 hs hρ hrb hrc hv hrespb, b9c_A_term hd hs0 hs hρ hrc hrb hv hrespc,
    b9c_Qt_term hd hs0 hs hρ hrb hrc hv,
    integral_withDensityReal_eq ρ hρ.density.measurable (fun y => (hρ.pos y).le),
    ← b9c_div_term hd hρ hra hrb hrc hv hdiv, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end HRS.MC.SEdge.B9cancel


end
