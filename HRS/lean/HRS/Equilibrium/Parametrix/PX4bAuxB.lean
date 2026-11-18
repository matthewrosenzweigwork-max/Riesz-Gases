import HRS.Equilibrium.Parametrix.PX4bAuxA
import HRS.Equilibrium.Parametrix.PXSAuxGlue
import HRS.Equilibrium.PairCorrection

/-!
# Packet PX4b auxiliaries B: linearity of `Jop` on slices that are `C²` off a point
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- A slice `f` of a kernel with a singular point `y`: `C²` away from `y`, and the weighted
gradient components are integrable. -/
structure Nice (ρ : Torus d → ℝ) (y : Torus d) (f : Torus d → ℝ) : Prop where
  c2 : ∀ v : Euc d, Torus.mk v ≠ y → ContDiffAt ℝ 2 (Torus.lift f) v
  hint : ∀ j : Fin d, Integrable (fun u => ρ u * Torus.partialDeriv j f u)

lemma px4b_fderiv_lift_periodic (f : Torus d → ℝ) {k : Euc d} (hk : IsLat k) (v : Euc d) :
    fderiv ℝ (Torus.lift f) (v + k) = fderiv ℝ (Torus.lift f) v := by
  have e : (fun x => Torus.lift f (x + k)) = Torus.lift f := funext fun x => by
    simp [Torus.lift, mk_add_eq, mk_isLat hk]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := Torus.lift f) (x := v) k
  rw [e] at this
  exact this.symm

lemma px4b_lift_partialDeriv (f : Torus d → ℝ) (j : Fin d) (v : Euc d) :
    Torus.lift (Torus.partialDeriv j f) v = fderiv ℝ (Torus.lift f) v (EuclideanSpace.single j 1) := by
  obtain ⟨k, hk, hrep⟩ := rep_exists_lat v
  show fderiv ℝ (Torus.lift f) (Torus.rep (Torus.mk v)) (EuclideanSpace.single j 1) = _
  rw [hrep, px4b_fderiv_lift_periodic f hk]

lemma px4b_partialDeriv_eq (f : Torus d → ℝ) (j : Fin d) (u : Torus d) :
    Torus.partialDeriv j f u = fderiv ℝ (Torus.lift f) (Torus.rep u) (EuclideanSpace.single j 1) := rfl

lemma px4b_D_pos_of_ne {x y : Torus d} (hxy : x ≠ y) : 0 < px4b_D (Torus.rep x - Torus.rep y) := by
  unfold px4b_D
  rw [norm_pos_iff]
  intro h0
  have h1 := px3a_mk_cR (Torus.mk (Torus.rep x - Torus.rep y))
  rw [h0, show Torus.mk (0 : Euc d) = 0 from mk_isLat isLat_zero] at h1
  apply hxy
  have : Torus.mk (Torus.rep x - Torus.rep y) = x - y := by rw [mk_sub_eq, Torus.mk_rep, Torus.mk_rep]
  rw [this] at h1
  exact sub_eq_zero.mp h1.symm

/-- Local `C¹` regularity of the weighted derivative components of a `Nice` slice. -/
lemma px4b_Nice_hloc {ρ : Torus d → ℝ} (hρ : ContDiff ℝ ∞' (Torus.lift ρ)) {y : Torus d}
    {f : Torus d → ℝ} (hf : Nice ρ y f) (j : Fin d) {v : Euc d} (hv : Torus.mk v ≠ y) :
    ContDiffAt ℝ 1 (Torus.lift (fun u => ρ u * Torus.partialDeriv j f u)) v := by
  have h1 : Torus.lift (fun u => ρ u * Torus.partialDeriv j f u) =
      fun w => Torus.lift ρ w * fderiv ℝ (Torus.lift f) w (EuclideanSpace.single j 1) := by
    funext w
    simp only [Torus.lift, Function.comp]
    exact congrArg (fun t => ρ (Torus.mk w) * t) (px4b_lift_partialDeriv f j w)
  rw [h1]
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ (Torus.lift f)) v :=
    (hf.c2 v hv).fderiv_right (m := 1) (by norm_num)
  exact (hρ.contDiffAt.of_le (by exact_mod_cast le_top)).mul (h2.clm_apply contDiffAt_const)


lemma px4b_D_eq_cR (v : Euc d) (x : Torus d) :
    px4b_D (v - Torus.rep x) = ‖Torus.centeredRep (Torus.mk v - x)‖ := by
  unfold px4b_D
  rw [mk_sub_eq, Torus.mk_rep]

lemma px4b_delta {x y : Torus d} (hxy : x ≠ y) :
    ∃ δ : ℝ, 0 < δ ∧ 6 * δ ≤ 1 / 8 ∧
      ∀ v : Euc d, px4b_D (v - Torus.rep x) < 8 * δ → Torus.mk v ≠ y := by
  set t : ℝ := ‖Torus.centeredRep (y - x)‖ with ht
  have htpos : 0 < t := by
    rw [ht, norm_pos_iff]
    intro h0
    have h1 := px3a_mk_cR (y - x)
    rw [h0, show Torus.mk (0 : Euc d) = 0 from mk_isLat isLat_zero] at h1
    exact hxy (sub_eq_zero.mp h1.symm).symm
  refine ⟨min (t / 8) (1 / 48), lt_min (by positivity) (by norm_num), ?_, ?_⟩
  · have := min_le_right (t / 8) (1 / 48)
    linarith
  · intro v hv hmk
    rw [px4b_D_eq_cR, hmk] at hv
    have := min_le_left (t / 8) (1 / 48)
    rw [← ht] at hv
    linarith

lemma px4b_Nice_lin {ρ : Torus d → ℝ} (hd : 1 ≤ d) {y : Torus d} {f₁ f₂ : Torus d → ℝ}
    (h₁ : Nice ρ y f₁) (h₂ : Nice ρ y f₂) (a c : ℝ) :
    Nice ρ y (fun u => a * f₁ u + c * f₂ u) := by
  have hpd : ∀ (j : Fin d) (w : Torus d), w ≠ y →
      Torus.partialDeriv j (fun u => a * f₁ u + c * f₂ u) w =
        a * Torus.partialDeriv j f₁ w + c * Torus.partialDeriv j f₂ w := by
    intro j w hw
    have hw1 : ContDiffAt ℝ 2 (Torus.lift f₁) (Torus.rep w) := h₁.c2 _ (by rwa [Torus.mk_rep])
    have hw2 : ContDiffAt ℝ 2 (Torus.lift f₂) (Torus.rep w) := h₂.c2 _ (by rwa [Torus.mk_rep])
    have hd1 := (hw1.differentiableAt (by norm_num)).hasFDerivAt
    have hd2 := (hw2.differentiableAt (by norm_num)).hasFDerivAt
    have hs : HasFDerivAt (fun v => a * Torus.lift f₁ v + c * Torus.lift f₂ v)
        (a • fderiv ℝ (Torus.lift f₁) (Torus.rep w) + c • fderiv ℝ (Torus.lift f₂) (Torus.rep w))
        (Torus.rep w) := (hd1.const_mul a).add (hd2.const_mul c)
    rw [px4b_partialDeriv_eq, px4b_partialDeriv_eq, px4b_partialDeriv_eq]
    have e : Torus.lift (fun u => a * f₁ u + c * f₂ u) =
        fun v => a * Torus.lift f₁ v + c * Torus.lift f₂ v := rfl
    rw [e, hs.fderiv]
    simp
  refine ⟨fun v hv => ?_, fun j => ?_⟩
  · exact (contDiffAt_const.mul (h₁.c2 v hv)).add (contDiffAt_const.mul (h₂.c2 v hv))
  · have hae : ∀ᵐ w ∂(volume : Measure (Torus d)), w ≠ y := by
      rw [ae_iff]; simpa using volume_singleton_torus hd y
    have := ((h₁.hint j).const_mul a).add ((h₂.hint j).const_mul c)
    refine this.congr ?_
    filter_upwards [hae] with w hw
    simp only [Pi.add_apply]
    rw [hpd j w hw]; ring

/-- Coordinates of the derivative of a vector-valued function. -/
lemma px4b_fderiv_coord {v : Euc d → Euc d} {p : Euc d} (hv : DifferentiableAt ℝ v p) (u : Euc d)
    (i : Fin d) : (fderiv ℝ v p u) i = fderiv ℝ (fun w => v w i) p u := by
  have h1 : HasFDerivAt (fun y => v y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
      (fderiv ℝ v p)) p :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp _ hv.hasFDerivAt
  rw [h1.fderiv]
  rfl

lemma px4b_Jop_eq_sum {s : ℝ} {ρ : Torus d → ℝ} {f : Torus d → ℝ} {x : Torus d}
    (hdiff : ∀ i, DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i f u))) (Torus.rep x)) :
    Jop d s ρ f x = ∑ i, fderiv ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i f u))) (Torus.rep x) (EuclideanSpace.single i 1) := by
  unfold Jop Torus.div
  refine Finset.sum_congr rfl fun i _ => ?_
  set v : Torus d → Euc d := fun z => (WithLp.toLp 2 fun j =>
      convFun (periodicRiesz d s) (fun y => ρ y * Torus.partialDeriv j f y) z : Euc d) with hv
  have hvd : DifferentiableAt ℝ (Torus.lift v) (Torus.rep x) := by
    rw [differentiableAt_euclidean]
    exact hdiff
  rw [px4b_fderiv_coord hvd]
  rfl

/-- Local facts for the weighted gradient convolutions of a `Nice` slice. -/
lemma px4b_Jop_facts {s : ℝ} {ρ : Torus d → ℝ} (hg : Integrable (periodicRiesz d s))
    (hgs : Torus.IsSmoothOffZero (periodicRiesz d s)) (hρ : ContDiff ℝ ∞' (Torus.lift ρ))
    {y x : Torus d} (hxy : x ≠ y) {f : Torus d → ℝ} (hf : Nice ρ y f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euc d, px4b_D (z - Torus.rep x) < δ → ∀ i : Fin d,
      Integrable (fun w => periodicRiesz d s (Torus.mk z - w) * (ρ w * Torus.partialDeriv i f w)) ∧
      DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s)
        (fun u => ρ u * Torus.partialDeriv i f u))) z := by
  obtain ⟨δ, hδ, hδ6, hnot⟩ := px4b_delta hxy
  refine ⟨δ, hδ, fun z hz i => ?_⟩
  exact px4b_convFun_local hg hgs (hf.hint i) (Torus.rep x) hδ hδ6
    (fun v hv => px4b_Nice_hloc hρ hf i (hnot v hv)) z hz

/-- Linearity of `Jop` on `Nice` slices at a regular point. -/
theorem px4b_Jop_lin {s : ℝ} {ρ : Torus d → ℝ} (hd : 1 ≤ d) (hg : Integrable (periodicRiesz d s))
    (hgs : Torus.IsSmoothOffZero (periodicRiesz d s)) (hρ : ContDiff ℝ ∞' (Torus.lift ρ))
    {y x : Torus d} (hxy : x ≠ y) {f₁ f₂ : Torus d → ℝ} (h₁ : Nice ρ y f₁) (h₂ : Nice ρ y f₂)
    (a c : ℝ) :
    Jop d s ρ (fun u => a * f₁ u + c * f₂ u) x = a * Jop d s ρ f₁ x + c * Jop d s ρ f₂ x := by
  have h₃ := px4b_Nice_lin hd h₁ h₂ a c
  obtain ⟨δ₁, hδ₁, F₁⟩ := px4b_Jop_facts hg hgs hρ hxy h₁
  obtain ⟨δ₂, hδ₂, F₂⟩ := px4b_Jop_facts hg hgs hρ hxy h₂
  obtain ⟨δ₃, hδ₃, F₃⟩ := px4b_Jop_facts hg hgs hρ hxy h₃
  set δ := min δ₁ (min δ₂ δ₃) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hae : ∀ᵐ w ∂(volume : Measure (Torus d)), w ≠ y := by
    rw [ae_iff]; simpa using volume_singleton_torus hd y
  have hpd : ∀ (j : Fin d) (w : Torus d), w ≠ y →
      Torus.partialDeriv j (fun u => a * f₁ u + c * f₂ u) w =
        a * Torus.partialDeriv j f₁ w + c * Torus.partialDeriv j f₂ w := by
    intro j w hw
    have hw1 : ContDiffAt ℝ 2 (Torus.lift f₁) (Torus.rep w) := h₁.c2 _ (by rwa [Torus.mk_rep])
    have hw2 : ContDiffAt ℝ 2 (Torus.lift f₂) (Torus.rep w) := h₂.c2 _ (by rwa [Torus.mk_rep])
    have hd1 := (hw1.differentiableAt (by norm_num)).hasFDerivAt
    have hd2 := (hw2.differentiableAt (by norm_num)).hasFDerivAt
    have hs : HasFDerivAt (fun v => a * Torus.lift f₁ v + c * Torus.lift f₂ v)
        (a • fderiv ℝ (Torus.lift f₁) (Torus.rep w) + c • fderiv ℝ (Torus.lift f₂) (Torus.rep w))
        (Torus.rep w) := (hd1.const_mul a).add (hd2.const_mul c)
    rw [px4b_partialDeriv_eq, px4b_partialDeriv_eq, px4b_partialDeriv_eq]
    have e : Torus.lift (fun u => a * f₁ u + c * f₂ u) =
        fun v => a * Torus.lift f₁ v + c * Torus.lift f₂ v := rfl
    rw [e, hs.fderiv]
    simp
  have hopen := px4b_isOpen_D_lt (Torus.rep x) δ
  have hx : px4b_D (Torus.rep x - Torus.rep x) < δ := by
    rw [sub_self, px4b_D_mk_zero (mk_isLat isLat_zero)]
    exact hδ0
  have hδ₁' : δ ≤ δ₁ := min_le_left _ _
  have hδ₂' : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃' : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hconv : ∀ i : Fin d, ∀ z : Euc d, px4b_D (z - Torus.rep x) < δ →
      Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i
        (fun u => a * f₁ u + c * f₂ u) u)) z =
      a * Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i f₁ u)) z +
      c * Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i f₂ u)) z := by
    intro i z hz
    have i1 := (F₁ z (lt_of_lt_of_le hz hδ₁') i).1
    have i2 := (F₂ z (lt_of_lt_of_le hz hδ₂') i).1
    show convFun _ _ (Torus.mk z) = a * convFun _ _ (Torus.mk z) + c * convFun _ _ (Torus.mk z)
    unfold convFun
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a) (i2.const_mul c)]
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [hpd i w hw]; ring
  have hd1 : ∀ i, DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i f₁ u))) (Torus.rep x) := fun i =>
    (F₁ _ (lt_of_lt_of_le hx hδ₁') i).2
  have hd2 : ∀ i, DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i f₂ u))) (Torus.rep x) := fun i =>
    (F₂ _ (lt_of_lt_of_le hx hδ₂') i).2
  have hd3 : ∀ i, DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i (fun u => a * f₁ u + c * f₂ u) u))) (Torus.rep x) :=
    fun i => (F₃ _ (lt_of_lt_of_le hx hδ₃') i).2
  rw [px4b_Jop_eq_sum hd3, px4b_Jop_eq_sum hd1, px4b_Jop_eq_sum hd2, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hev : Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i
        (fun u => a * f₁ u + c * f₂ u) u)) =ᶠ[𝓝 (Torus.rep x)]
      fun z => a * Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i f₁ u)) z +
        c * Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i f₂ u)) z := by
    filter_upwards [hopen.mem_nhds hx] with z hz using hconv i z hz
  rw [hev.fderiv_eq]
  have hs : HasFDerivAt (fun z => a * Torus.lift (convFun (periodicRiesz d s)
        (fun u => ρ u * Torus.partialDeriv i f₁ u)) z +
        c * Torus.lift (convFun (periodicRiesz d s) (fun u => ρ u * Torus.partialDeriv i f₂ u)) z)
      (a • fderiv ℝ (Torus.lift (convFun (periodicRiesz d s)
        (fun u => ρ u * Torus.partialDeriv i f₁ u))) (Torus.rep x) +
       c • fderiv ℝ (Torus.lift (convFun (periodicRiesz d s)
        (fun u => ρ u * Torus.partialDeriv i f₂ u))) (Torus.rep x)) (Torus.rep x) :=
    ((hd1 i).hasFDerivAt.const_mul a).add ((hd2 i).hasFDerivAt.const_mul c)
  rw [hs.fderiv]
  simp


lemma px4b_inner_grad (b : Euc d) (φ : Euc d → ℝ) (p : Euc d) :
    inner ℝ b (gradient φ p) = fderiv ℝ φ p b := by
  rw [real_inner_comm]
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

/-- Linearity of `Bop` at a regular point of two slices. -/
lemma px4b_Bop_lin {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} {y u : Torus d}
    (hu : u ≠ y) {f₁ f₂ : Torus d → ℝ} (h₁ : Nice ρ y f₁) (h₂ : Nice ρ y f₂) (a c : ℝ) :
    Bop d s V β ρ (fun w => a * f₁ w + c * f₂ w) u =
      a * Bop d s V β ρ f₁ u + c * Bop d s V β ρ f₂ u := by
  have hw1 : ContDiffAt ℝ 2 (Torus.lift f₁) (Torus.rep u) := h₁.c2 _ (by rwa [Torus.mk_rep])
  have hw2 : ContDiffAt ℝ 2 (Torus.lift f₂) (Torus.rep u) := h₂.c2 _ (by rwa [Torus.mk_rep])
  have hd1 := (hw1.differentiableAt (by norm_num)).hasFDerivAt
  have hd2 := (hw2.differentiableAt (by norm_num)).hasFDerivAt
  have hs : HasFDerivAt (fun v => a * Torus.lift f₁ v + c * Torus.lift f₂ v)
      (a • fderiv ℝ (Torus.lift f₁) (Torus.rep u) + c • fderiv ℝ (Torus.lift f₂) (Torus.rep u))
      (Torus.rep u) := (hd1.const_mul a).add (hd2.const_mul c)
  have e : Torus.lift (fun w => a * f₁ w + c * f₂ w) =
      (a • Torus.lift f₁) + (c • Torus.lift f₂) := rfl
  have hlap : Torus.laplacian (fun w => a * f₁ w + c * f₂ w) u =
      a * Torus.laplacian f₁ u + c * Torus.laplacian f₂ u := by
    unfold Torus.laplacian
    rw [e]
    have := (hw1.const_smul a).laplacian_add (hw2.const_smul c)
    rw [show (a • Torus.lift f₁ + c • Torus.lift f₂) =
      ((fun y => a • Torus.lift f₁ y) + fun y => c • Torus.lift f₂ y) from rfl, this]
    erw [InnerProductSpace.laplacian_smul a hw1, InnerProductSpace.laplacian_smul c hw2]
    simp
  unfold Bop Torus.grad
  rw [hlap, px4b_inner_grad, px4b_inner_grad, px4b_inner_grad]
  have e2 : (Torus.lift fun w => a * f₁ w + c * f₂ w) =
      fun v => a * Torus.lift f₁ v + c * Torus.lift f₂ v := rfl
  rw [e2, hs.fderiv]
  simp
  ring


lemma px4b_ae_ne_mu (hd : 1 ≤ d) (ρ : Torus d → ℝ) (y : Torus d) :
    ∀ᵐ u ∂(withDensityReal ρ), u ≠ y := by
  have h : ∀ᵐ u ∂(volume : Measure (Torus d)), u ≠ y := by
    rw [ae_iff]; simpa using volume_singleton_torus hd y
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- Pointwise linearity of `Bop + Jop` away from the singular point. -/
theorem px4b_G_lin {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (hd : 1 ≤ d)
    (hg : Integrable (periodicRiesz d s)) (hgs : Torus.IsSmoothOffZero (periodicRiesz d s))
    (hρ : ContDiff ℝ ∞' (Torus.lift ρ)) {y u : Torus d} (hu : u ≠ y) {f₁ f₂ : Torus d → ℝ}
    (h₁ : Nice ρ y f₁) (h₂ : Nice ρ y f₂) (a c : ℝ) :
    Bop d s V β ρ (fun w => a * f₁ w + c * f₂ w) u + Jop d s ρ (fun w => a * f₁ w + c * f₂ w) u =
      a * (Bop d s V β ρ f₁ u + Jop d s ρ f₁ u) + c * (Bop d s V β ρ f₂ u + Jop d s ρ f₂ u) := by
  rw [px4b_Bop_lin hu h₁ h₂ a c, px4b_Jop_lin hd hg hgs hρ hu h₁ h₂ a c]
  ring

/-- Linearity of `projGen` on `Nice` slices with integrable `Bop + Jop`. -/
theorem px4b_projGen_lin {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (hd : 1 ≤ d)
    (hg : Integrable (periodicRiesz d s)) (hgs : Torus.IsSmoothOffZero (periodicRiesz d s))
    (hρ : ContDiff ℝ ∞' (Torus.lift ρ)) {y x : Torus d} (hxy : x ≠ y) {f₁ f₂ : Torus d → ℝ}
    (h₁ : Nice ρ y f₁) (h₂ : Nice ρ y f₂)
    (I₁ : Integrable (fun u => Bop d s V β ρ f₁ u + Jop d s ρ f₁ u) (withDensityReal ρ))
    (I₂ : Integrable (fun u => Bop d s V β ρ f₂ u + Jop d s ρ f₂ u) (withDensityReal ρ)) (a c : ℝ) :
    projGen d s V β ρ (fun w => a * f₁ w + c * f₂ w) x =
      a * projGen d s V β ρ f₁ x + c * projGen d s V β ρ f₂ x := by
  unfold projGen projMean pair
  have hpt := fun u (hu : u ≠ y) => px4b_G_lin (s := s) (V := V) (β := β) hd hg hgs hρ hu h₁ h₂ a c
  have hint : ∫ u, (Bop d s V β ρ (fun w => a * f₁ w + c * f₂ w) u +
        Jop d s ρ (fun w => a * f₁ w + c * f₂ w) u) ∂(withDensityReal ρ) =
      a * ∫ u, (Bop d s V β ρ f₁ u + Jop d s ρ f₁ u) ∂(withDensityReal ρ) +
        c * ∫ u, (Bop d s V β ρ f₂ u + Jop d s ρ f₂ u) ∂(withDensityReal ρ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (I₁.const_mul a) (I₂.const_mul c)]
    refine integral_congr_ae ?_
    filter_upwards [px4b_ae_ne_mu hd ρ y] with u hu using hpt u hu
  beta_reduce
  rw [hint, hpt x hxy]
  ring

end HRS.Parx
end
