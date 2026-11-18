import HRS.Sections.Sec6
import HRS.Sections.ScrnAux3

/-!
# Packet SCRN, part 4: the mesoscopic test as a periodisation, smoothness, Fourier coefficients

`mesoTest d ℓ x₀ φ = descend (scrnP d ℓ x₀ φ)` with `scrnP = ∑_z g(· + z)`, `g(ξ) = ℓ^{-d/2} φ((ξ - x₀)/ℓ)`.
For `φ ∈ C_c^∞` the periodisation is a locally finite sum (so `mesoTest` is smooth) and
`ψ̂(k) = ℓ^{d/2} e^{-2πi k·x₀} φ̂(ℓk)` (`scrn_fcoef_mesoTest`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform

namespace HRS

variable {d : ℕ}

/-- `g(ξ) = ℓ^{-d/2} φ(ℓ⁻¹ (ξ - x₀))`. -/
def scrnG (d : ℕ) (ℓ : ℝ) (x₀ : Euc d) (φ : Euc d → ℝ) (ξ : Euc d) : ℝ :=
  ℓ ^ (-(d : ℝ) / 2) * φ (ℓ⁻¹ • (ξ - x₀))

/-- The periodisation `∑_z g(ξ + z)`. -/
def scrnP (d : ℕ) (ℓ : ℝ) (x₀ : Euc d) (φ : Euc d → ℝ) (ξ : Euc d) : ℝ :=
  ∑' z : Lattice d, scrnG d ℓ x₀ φ (ξ + Lattice.toEuc z)

lemma mesoTest_eq_descend (ℓ : ℝ) (x₀ : Euc d) (φ : Euc d → ℝ) :
    mesoTest d ℓ x₀ φ = Torus.descend (scrnP d ℓ x₀ φ) := by
  funext x
  simp only [mesoTest, Torus.descend, scrnP, scrnG]
  rw [tsum_mul_left]
  congr 2
  funext z
  congr 2
  abel

lemma scrnP_per (ℓ : ℝ) (x₀ : Euc d) (φ : Euc d → ℝ) : Torus.Per (scrnP d ℓ x₀ φ) := by
  intro y n
  unfold scrnP
  have : ∀ z : Lattice d, scrnG d ℓ x₀ φ (y + Lattice.toEuc n + Lattice.toEuc z) =
      scrnG d ℓ x₀ φ (y + Lattice.toEuc (n + z)) := by
    intro z
    congr 1
    have : Lattice.toEuc (n + z) = Lattice.toEuc n + Lattice.toEuc z := by
      ext i; simp [Lattice.toEuc]
    rw [this]; abel
  simp_rw [this]
  exact (Equiv.addLeft n).tsum_eq (fun z => scrnG d ℓ x₀ φ (y + Lattice.toEuc z))

/-- A finite set of lattice points containing all `z` with `‖toEuc z‖ ≤ ρ`. -/
lemma finite_lattice_ball (ρ : ℝ) : {z : Lattice d | ‖Lattice.toEuc z‖ ≤ ρ}.Finite := by
  have hsub : {z : Lattice d | ‖Lattice.toEuc z‖ ≤ ρ} ⊆
      (Set.Icc (fun _ : Fin d => -⌈ρ⌉) (fun _ : Fin d => ⌈ρ⌉) : Set (Lattice d)) := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := abs_le_enorm z i
      have h2 : |(z i : ℝ)| ≤ ρ := h1.trans hz
      have h3 : (-(⌈ρ⌉ : ℝ)) ≤ (z i : ℝ) := by
        have := Int.le_ceil ρ
        linarith [neg_abs_le (z i : ℝ)]
      exact_mod_cast h3
    · have h1 := abs_le_enorm z i
      have h2 : |(z i : ℝ)| ≤ ρ := h1.trans hz
      have h3 : (z i : ℝ) ≤ (⌈ρ⌉ : ℝ) := by
        have := Int.le_ceil ρ
        linarith [le_abs_self (z i : ℝ)]
      exact_mod_cast h3
  exact (Set.finite_Icc _ _).subset hsub


lemma contDiff_scrnG {ℓ : ℝ} (x₀ : Euc d) {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (scrnG d ℓ x₀ φ) := by
  unfold scrnG
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Euc d => ℓ⁻¹ • (ξ - x₀)) :=
    (contDiff_id.sub contDiff_const).const_smul ℓ⁻¹
  exact contDiff_const.mul (hφ.comp h)

lemma scrnP_local {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ} {R : ℝ}
    (hR : ∀ x, φ x ≠ 0 → ‖x‖ ≤ R) (y₀ : Euc d) :
    ∃ F : Finset (Lattice d), ∀ y ∈ Metric.ball y₀ 1,
      scrnP d ℓ x₀ φ y = ∑ z ∈ F, scrnG d ℓ x₀ φ (y + Lattice.toEuc z) := by
  set ρ : ℝ := ℓ * R + ‖y₀ - x₀‖ + 1 with hρ
  refine ⟨(finite_lattice_ball (d := d) ρ).toFinset, fun y hy => ?_⟩
  unfold scrnP
  refine tsum_eq_sum (fun z hz => ?_)
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hz
  by_contra hne
  have hφz : φ (ℓ⁻¹ • (y + Lattice.toEuc z - x₀)) ≠ 0 := by
    intro h0
    apply hne
    simp [scrnG, h0]
  have h1 := hR _ hφz
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hℓ] at h1
  have h2 : ‖y + Lattice.toEuc z - x₀‖ ≤ ℓ * R := by
    have : ℓ⁻¹ * ‖y + Lattice.toEuc z - x₀‖ ≤ R := h1
    rw [inv_mul_le_iff₀ hℓ] at this
    linarith
  have h3 : ‖Lattice.toEuc z‖ ≤ ‖y + Lattice.toEuc z - x₀‖ + ‖y - x₀‖ := by
    calc ‖Lattice.toEuc z‖ = ‖(y + Lattice.toEuc z - x₀) - (y - x₀)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h4 : ‖y - x₀‖ ≤ ‖y₀ - x₀‖ + 1 := by
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    calc ‖y - x₀‖ = ‖(y - y₀) + (y₀ - x₀)‖ := by congr 1; abel
      _ ≤ ‖y - y₀‖ + ‖y₀ - x₀‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  linarith

theorem contDiff_scrnP {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (scrnP d ℓ x₀ φ) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x, φ x ≠ 0 → ‖x‖ ≤ R := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => ?_⟩
    have : x ∈ tsupport φ := subset_tsupport _ hx
    simpa using hR this
  rw [contDiff_iff_contDiffAt]
  intro y₀
  obtain ⟨F, hF⟩ := scrnP_local hℓ x₀ hR y₀
  have hev : scrnP d ℓ x₀ φ =ᶠ[𝓝 y₀] fun y => ∑ z ∈ F, scrnG d ℓ x₀ φ (y + Lattice.toEuc z) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ one_pos) (fun y hy => hF y hy)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine (ContDiff.sum (fun z _ => ?_)).contDiffAt
  exact (contDiff_scrnG x₀ hφ).comp (contDiff_id.add contDiff_const)

theorem isCk_mesoTest {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (n : WithTop ℕ∞) (hn : n ≤ (⊤ : ℕ∞)) :
    Torus.IsCk n (mesoTest d ℓ x₀ φ) := by
  unfold Torus.IsCk
  rw [mesoTest_eq_descend, Torus.lift_descend' (scrnP_per ℓ x₀ φ)]
  exact (contDiff_scrnP hℓ x₀ hφ hc).of_le hn


/-- The torus integral as an integral over the unit cube `[-1/2,1/2)^d ⊂ ℝ^d`. -/
lemma scrn_integral_torus_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus d → E) : ∫ x, f x = ∫ ξ in scrnCube d 1 0, f (Torus.mk ξ) := by
  rw [KernelAux.integral_torus_box f]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb (fun y => f (KernelAux.boxPt y)) (KernelAux.Box d)
  rw [← h1]
  have hae : (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d) =ᵐ[volume] scrnCube d 1 0 := by
    have e1 : KernelAux.Box d = Set.pi Set.univ fun _ : Fin d => Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
      ext x; simp [KernelAux.Box]
    have e2 : (Set.pi Set.univ fun _ : Fin d => Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) =ᵐ[volume]
        Set.pi Set.univ fun i : Fin d => Set.Ico (1 * (((0 : Lattice d) i : ℝ) - 1 / 2))
          (1 * (((0 : Lattice d) i : ℝ) + 1 / 2)) := by
      refine (Measure.univ_pi_Ioc_ae_eq_Icc).trans ?_
      refine Filter.EventuallyEq.trans ?_ (Measure.univ_pi_Ico_ae_eq_Icc).symm
      have : ∀ i : Fin d, (-1 / 2 + 1 : ℝ) = 1 * (((0 : Lattice d) i : ℝ) + 1 / 2) := fun i => by
        simp; norm_num
      have h2 : ∀ i : Fin d, (-1 / 2 : ℝ) = 1 * (((0 : Lattice d) i : ℝ) - 1 / 2) := fun i => by
        simp; norm_num
      simp_rw [← this, ← h2]
      exact Filter.EventuallyEq.rfl
    rw [e1]
    exact hmp.quasiMeasurePreserving.preimage_ae_eq e2
  rw [setIntegral_congr_set hae]
  rfl


lemma mem_scrnCube_one_add (n : Lattice d) (ξ : Euc d) :
    ξ + Lattice.toEuc n ∈ scrnCube d 1 n ↔ ξ ∈ scrnCube d 1 0 := by
  rw [mem_scrnCube, mem_scrnCube]
  refine forall_congr' fun i => ?_
  simp only [PiLp.add_apply, Lattice.toEuc, Pi.zero_apply, Int.cast_zero, one_mul, zero_sub,
    zero_add]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

lemma setIntegral_scrnCube_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : Lattice d) (f : Euc d → E) :
    ∫ ξ in scrnCube d 1 n, f ξ = ∫ ξ in scrnCube d 1 0, f (ξ + Lattice.toEuc n) := by
  have hemb : MeasurableEmbedding (fun ξ : Euc d => ξ + Lattice.toEuc n) :=
    (MeasurableEquiv.addRight (Lattice.toEuc n)).measurableEmbedding
  have hmp : MeasurePreserving (fun ξ : Euc d => ξ + Lattice.toEuc n) volume volume :=
    measurePreserving_add_right volume (Lattice.toEuc n)
  have hpre : (fun ξ : Euc d => ξ + Lattice.toEuc n) ⁻¹' (scrnCube d 1 n) = scrnCube d 1 0 := by
    ext ξ; exact mem_scrnCube_one_add n ξ
  have := hmp.setIntegral_preimage_emb hemb f (scrnCube d 1 n)
  rw [hpre] at this
  exact this.symm

/-- Unfolding the periodisation: `∫_{Q_0} H ∑_z g(·+z) = ∫_{ℝ^d} H g` for periodic bounded `H`. -/
theorem scrn_unfold {g : Euc d → ℂ} (hg : Integrable g) {H : Euc d → ℂ} (hH : Measurable H)
    {B : ℝ} (hHb : ∀ ξ, ‖H ξ‖ ≤ B) (hHper : ∀ (ξ : Euc d) (n : Lattice d),
      H (ξ + Lattice.toEuc n) = H ξ) :
    ∫ ξ in scrnCube d 1 0, H ξ * (∑' z : Lattice d, g (ξ + Lattice.toEuc z)) =
      ∫ ξ, H ξ * g ξ := by
  have hone : (0 : ℝ) < 1 := one_pos
  have hHg : Integrable (fun ξ => H ξ * g ξ) := by
    refine Integrable.mono' (hg.norm.const_mul B)
      (hH.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hHb ξ) (norm_nonneg _)
  have hcube : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}, Integrable f →
      HasSum (fun n : Lattice d => ∫ ξ in scrnCube d 1 n, f ξ) (∫ ξ, f ξ) := by
    intro E _ _ f hf
    have := hasSum_integral_iUnion (μ := volume) (f := f) (fun k => measurableSet_scrnCube 1 k)
      (scrnCube_disjoint hone) (by rw [iUnion_scrnCube hone]; exact hf.integrableOn)
    rwa [iUnion_scrnCube hone, Measure.restrict_univ] at this
  have hcubeR : Summable (fun n : Lattice d => ∫ ξ in scrnCube d 1 0, ‖g (ξ + Lattice.toEuc n)‖) := by
    refine (hcube (f := fun ξ => ‖g ξ‖) hg.norm).summable.congr (fun n => ?_)
    exact setIntegral_scrnCube_shift n (fun ξ => ‖g ξ‖)
  have hFint : ∀ n : Lattice d, Integrable (fun ξ => H ξ * g (ξ + Lattice.toEuc n))
      (volume.restrict (scrnCube d 1 0)) := by
    intro n
    have h1 : Integrable (fun ξ => g (ξ + Lattice.toEuc n)) :=
      hg.comp_add_right (Lattice.toEuc n)
    refine Integrable.mono' ((h1.norm.const_mul B).restrict)
      (hH.aestronglyMeasurable.mul h1.aestronglyMeasurable).restrict
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hHb ξ) (norm_nonneg _)
  have hgn : ∀ n : Lattice d, Integrable (fun ξ => ‖g (ξ + Lattice.toEuc n)‖)
      (volume.restrict (scrnCube d 1 0)) := fun n =>
    ((hg.comp_add_right (Lattice.toEuc n)).norm).restrict
  have hsumF : Summable (fun n : Lattice d => ∫ ξ in scrnCube d 1 0, ‖H ξ * g (ξ + Lattice.toEuc n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun ξ => norm_nonneg _)
      (fun n => ?_) (hcubeR.mul_left B)
    rw [← integral_const_mul]
    refine integral_mono (hFint n).norm ((hgn n).const_mul B) (fun ξ => ?_)
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (hHb ξ) (norm_nonneg _)
  have e1 := integral_tsum_of_summable_integral_norm hFint hsumF
  have e2 : ∀ n : Lattice d, ∫ ξ in scrnCube d 1 n, H ξ * g ξ =
      ∫ ξ in scrnCube d 1 0, H ξ * g (ξ + Lattice.toEuc n) := by
    intro n
    rw [setIntegral_scrnCube_shift n (fun ξ => H ξ * g ξ)]
    refine setIntegral_congr_fun (measurableSet_scrnCube 1 0) (fun ξ _ => ?_)
    simp only [hHper]
  calc ∫ ξ in scrnCube d 1 0, H ξ * (∑' z : Lattice d, g (ξ + Lattice.toEuc z))
      = ∫ ξ in scrnCube d 1 0, ∑' n : Lattice d, H ξ * g (ξ + Lattice.toEuc n) := by
        refine setIntegral_congr_fun (measurableSet_scrnCube 1 0) (fun ξ _ => ?_)
        rw [tsum_mul_left]
    _ = ∑' n : Lattice d, ∫ ξ in scrnCube d 1 0, H ξ * g (ξ + Lattice.toEuc n) := e1.symm
    _ = ∑' n : Lattice d, ∫ ξ in scrnCube d 1 n, H ξ * g ξ := by
        simp_rw [e2]
    _ = ∫ ξ, H ξ * g ξ := (hcube hHg).tsum_eq


lemma scrn_inner_toEuc (u : Euc d) (k : Lattice d) (ℓ : ℝ) :
    inner ℝ u (ℓ • Lattice.toEuc k) = ℓ * Lattice.dot k u := by
  simp only [PiLp.inner_apply, PiLp.smul_apply, Lattice.toEuc, smul_eq_mul, Lattice.dot,
    RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma scrn_dot_add_smul (k : Lattice d) (x u : Euc d) (ℓ : ℝ) :
    Lattice.dot k (x + ℓ • u) = Lattice.dot k x + ℓ * Lattice.dot k u := by
  simp only [Lattice.dot, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem scrn_fourier_g {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) (φ : Euc d → ℝ) (k : Lattice d) :
    ∫ ξ : Euc d, Complex.exp (((-(2 * Real.pi * Lattice.dot k ξ) : ℝ) : ℂ) * Complex.I) *
        ((scrnG d ℓ x₀ φ ξ : ℝ) : ℂ) =
      ((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (((-(2 * Real.pi * Lattice.dot k x₀) : ℝ) : ℂ) * Complex.I) *
          𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) (ℓ • Lattice.toEuc k) := by
  have e1 := integral_add_left_eq_self (μ := (volume : Measure (Euc d)))
    (fun ξ : Euc d => Complex.exp (((-(2 * Real.pi * Lattice.dot k ξ) : ℝ) : ℂ) * Complex.I) *
        ((scrnG d ℓ x₀ φ ξ : ℝ) : ℂ)) x₀
  rw [← e1]
  set Ψ : Euc d → ℂ := fun u => Complex.exp (((-(2 * Real.pi * Lattice.dot k (x₀ + ℓ • u)) : ℝ) : ℂ) * Complex.I) *
        ((ℓ ^ (-(d : ℝ) / 2) * φ u : ℝ) : ℂ) with hΨ
  have e2 : (fun w : Euc d => Complex.exp (((-(2 * Real.pi * Lattice.dot k (x₀ + w)) : ℝ) : ℂ) * Complex.I) *
        ((scrnG d ℓ x₀ φ (x₀ + w) : ℝ) : ℂ)) = fun w => Ψ (ℓ⁻¹ • w) := by
    funext w
    simp only [hΨ, scrnG, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  rw [e2, Measure.integral_comp_smul (volume : Measure (Euc d)) Ψ ℓ⁻¹]
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  rw [hfr]
  have hpw : |((ℓ⁻¹) ^ d)⁻¹| = ℓ ^ d := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [hpw]
  have hF : 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) (ℓ • Lattice.toEuc k) =
      ∫ u : Euc d, Complex.exp (((-(2 * Real.pi * (ℓ * Lattice.dot k u)) : ℝ) : ℂ) * Complex.I) *
        ((φ u : ℝ) : ℂ) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul, Circle.coe_exp]
    rw [scrn_inner_toEuc]
    congr 3
    push_cast
    ring
  rw [hF]
  have hΨ2 : ∀ u : Euc d, Ψ u = (((ℓ ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp (((-(2 * Real.pi * Lattice.dot k x₀) : ℝ) : ℂ) * Complex.I)) *
      (Complex.exp (((-(2 * Real.pi * (ℓ * Lattice.dot k u)) : ℝ) : ℂ) * Complex.I) *
        ((φ u : ℝ) : ℂ)) := by
    intro u
    simp only [hΨ, scrn_dot_add_smul]
    rw [show (((-(2 * Real.pi * (Lattice.dot k x₀ + ℓ * Lattice.dot k u))) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * Lattice.dot k x₀) : ℝ) : ℂ) * Complex.I +
        ((-(2 * Real.pi * (ℓ * Lattice.dot k u)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add]
    push_cast
    ring
  simp_rw [hΨ2]
  rw [integral_const_mul, Complex.real_smul]
  have hpow : ℓ ^ d * ℓ ^ (-(d : ℝ) / 2) = ℓ ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hℓ]
    congr 1; ring
  have hpow' : ((ℓ ^ d : ℝ) : ℂ) * ((ℓ ^ (-(d : ℝ) / 2) : ℝ) : ℂ) = ((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hpow]
  calc ((ℓ ^ d : ℝ) : ℂ) * (((ℓ ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (((-(2 * Real.pi * Lattice.dot k x₀) : ℝ) : ℂ) * Complex.I) *
        ∫ u : Euc d, Complex.exp (((-(2 * Real.pi * (ℓ * Lattice.dot k u)) : ℝ) : ℂ) * Complex.I) *
          ((φ u : ℝ) : ℂ))
      = (((ℓ ^ d : ℝ) : ℂ) * ((ℓ ^ (-(d : ℝ) / 2) : ℝ) : ℂ)) *
        Complex.exp (((-(2 * Real.pi * Lattice.dot k x₀) : ℝ) : ℂ) * Complex.I) *
        ∫ u : Euc d, Complex.exp (((-(2 * Real.pi * (ℓ * Lattice.dot k u)) : ℝ) : ℂ) * Complex.I) *
          ((φ u : ℝ) : ℂ) := by ring
    _ = _ := by rw [hpow']


lemma hasCompactSupport_scrnG {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (scrnG d ℓ x₀ φ) := by
  unfold scrnG
  have h : HasCompactSupport (fun ξ : Euc d => φ (ℓ⁻¹ • (ξ - x₀))) := by
    have := hc.comp_homeomorph ((Homeomorph.subRight x₀).trans
      (Homeomorph.smulOfNeZero ℓ⁻¹ (inv_ne_zero hℓ.ne')))
    exact this
  exact h.mul_left

lemma integrable_scrnG {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun ξ => ((scrnG d ℓ x₀ φ ξ : ℝ) : ℂ)) := by
  have h1 : Continuous (fun ξ => ((scrnG d ℓ x₀ φ ξ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (contDiff_scrnG x₀ hφ).continuous
  refine h1.integrable_of_hasCompactSupport ?_
  exact (hasCompactSupport_scrnG hℓ x₀ hc).comp_left Complex.ofReal_zero

theorem scrn_fcoef_mesoTest {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (k : Lattice d) :
    Torus.fcoef (mesoTest d ℓ x₀ φ) k =
      ((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (((-(2 * Real.pi * Lattice.dot k x₀) : ℝ) : ℂ) * Complex.I) *
          𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) (ℓ • Lattice.toEuc k) := by
  rw [← scrn_fourier_g hℓ x₀ φ k]
  unfold Torus.fcoef
  rw [scrn_integral_torus_cube]
  set H : Euc d → ℂ := fun ξ => Complex.exp (((-(2 * Real.pi * Lattice.dot k ξ) : ℝ) : ℂ) * Complex.I)
    with hH
  have hHeq : ∀ ξ : Euc d, Torus.mode (-k) (Torus.mk ξ) = H ξ := by
    intro ξ
    rw [Torus.mode_mk]
    simp only [hH, Lattice.dot, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    congr 2
    push_cast
    ring
  have hHc : Continuous H := by
    simp only [hH, Lattice.dot]; fun_prop
  have hHb : ∀ ξ, ‖H ξ‖ ≤ 1 := fun ξ => by
    simp only [hH]
    rw [Complex.norm_exp_ofReal_mul_I]
  have hHper : ∀ (ξ : Euc d) (n : Lattice d), H (ξ + Lattice.toEuc n) = H ξ := by
    intro ξ n
    rw [← hHeq, ← hHeq, Torus.mk_add, Torus.mk_toEuc, add_zero]
  have hmesoc : ∀ ξ : Euc d, (mesoTest d ℓ x₀ φ (Torus.mk ξ) : ℝ) = scrnP d ℓ x₀ φ ξ := by
    intro ξ
    rw [mesoTest_eq_descend, Torus.descend_mk (scrnP_per ℓ x₀ φ)]
  have hunf := scrn_unfold (integrable_scrnG hℓ x₀ hφ hc) hHc.measurable hHb hHper
  have hlhs : ∫ ξ in scrnCube d 1 0, Torus.mode (-k) (Torus.mk ξ) *
      ((mesoTest d ℓ x₀ φ (Torus.mk ξ) : ℝ) : ℂ) =
      ∫ ξ in scrnCube d 1 0, H ξ * ∑' z : Lattice d, ((scrnG d ℓ x₀ φ (ξ + Lattice.toEuc z) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun (measurableSet_scrnCube 1 0) (fun ξ _ => ?_)
    rw [hHeq, hmesoc]
    unfold scrnP
    rw [Complex.ofReal_tsum]
  rw [hlhs, hunf]

end HRS
