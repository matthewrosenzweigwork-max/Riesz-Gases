import HRS.MC.CepH3D2

/-!
# Packet CEPH3, part E1: Gaussian integrability, null boundary of the alcove, quadratic bounds
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3e_gauss_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Ch N => Real.exp (-b * ‖z‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace (ι := Fin N) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [Complex.norm_exp, zero_mul, add_zero]
  congr 1
  rw [show (-(b:ℂ) * ((‖z‖:ℝ):ℂ) ^ 2) = (((-b * ‖z‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- The hyperplane `{z | z l - z k = c}` is Lebesgue-null for `k ≠ l`. -/
lemma h3e_hyperplane_null {k l : Fin N} (hkl : k ≠ l) (c : ℝ) :
    volume {z : Ch N | z l - z k = c} = 0 := by
  let f : Ch N →ₗ[ℝ] ℝ := (EuclideanSpace.proj l : Ch N →L[ℝ] ℝ).toLinearMap - (EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).toLinearMap
  let x₀ : Ch N := c • EuclideanSpace.single l 1
  have hf : ∀ z, f z = z l - z k := fun z => by simp [f]
  have hx₀ : f x₀ = c := by simp [hf, x₀, hkl.symm, PiLp.single_apply]
  let s : AffineSubspace ℝ (Ch N) := AffineSubspace.mk' x₀ (LinearMap.ker f)
  have hs : (s : Set (Ch N)) = {z | z l - z k = c} := by
    ext z
    have h1 : z ∈ (s : Set (Ch N)) ↔ f (z - x₀) = 0 := by
      simp only [s, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker]
    rw [h1, map_sub, hx₀, hf z, sub_eq_zero]
    rfl
  rw [← hs]
  refine Measure.addHaar_affineSubspace _ s fun htop => ?_
  have hdir : s.direction = LinearMap.ker f := by simp [s]
  rw [htop, AffineSubspace.direction_top] at hdir
  have : f (EuclideanSpace.single l 1) = 1 := by simp [hf, hkl.symm, PiLp.single_apply]
  have hmem : EuclideanSpace.single l (1:ℝ) ∈ (⊤ : Submodule ℝ (Ch N)) := trivial
  rw [hdir] at hmem
  simp [this] at hmem

lemma h3e_boundary_null : volume (closure (cep_Alcove N) \ cep_Alcove N) = 0 := by
  classical
  set Cl : Set (Ch N) := {z | (∀ k l : Fin N, k < l → z k ≤ z l) ∧ ∀ k l : Fin N, z l ≤ z k + 1} with hCl
  have hclosed : IsClosed Cl := by
    have e : Cl = (⋂ k, ⋂ l, ⋂ (_ : k < l), {z : Ch N | z k ≤ z l}) ∩ ⋂ k, ⋂ l, {z : Ch N | z l ≤ z k + 1} := by
      ext z; simp [hCl]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ => ?_)
      (isClosed_iInter fun k => isClosed_iInter fun l => ?_)
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · exact isClosed_le (by fun_prop) (by fun_prop)
  have hsub : cep_Alcove N ⊆ Cl := fun z hz => ⟨fun k l hkl => (hz.1 k l hkl).le, fun k l => (hz.2 k l).le⟩
  have hcl : closure (cep_Alcove N) ⊆ Cl := closure_minimal hsub hclosed
  have hcov : closure (cep_Alcove N) \ cep_Alcove N ⊆
      ⋃ k, ⋃ l, ⋃ (_ : k ≠ l), ({z : Ch N | z l - z k = 0} ∪ {z : Ch N | z l - z k = 1}) := by
    rintro z ⟨hz, hzA⟩
    obtain ⟨h1, h2⟩ := hcl hz
    by_contra hcon
    apply hzA
    refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
    · refine lt_of_le_of_ne (h1 k l hkl) fun heq => hcon ?_
      simp only [mem_iUnion, mem_union, mem_setOf_eq]
      exact ⟨k, l, hkl.ne, Or.inl (by linarith)⟩
    · refine lt_of_le_of_ne (h2 k l) fun heq => hcon ?_
      simp only [mem_iUnion, mem_union, mem_setOf_eq]
      refine ⟨k, l, fun hkl => ?_, Or.inr (by linarith)⟩
      subst hkl; linarith
  refine measure_mono_null hcov ?_
  refine measure_iUnion_null fun k => measure_iUnion_null fun l => measure_iUnion_null fun hkl => ?_
  exact measure_union_null (h3e_hyperplane_null hkl _) (h3e_hyperplane_null hkl _)

lemma h3e_alcove_point [NeZero N] : ∃ w : Ch N, w ∈ cep_Alcove N ∧ w 0 = 1 / 2 := by
  refine ⟨WithLp.toLp 2 fun k => 1 / 2 + (k : ℝ) / (2 * N), ?_, by simp⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hk : ∀ k : Fin N, (k : ℝ) < N := fun k => by exact_mod_cast k.2
  refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
  · have : (k : ℝ) < l := by exact_mod_cast hkl
    simp only
    have : (k : ℝ) / (2 * N) < l / (2 * N) := by gcongr
    linarith
  · simp only
    have h1 : (l : ℝ) / (2 * N) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hk l]
    have h2 : 0 ≤ (k : ℝ) / (2 * N) := by positivity
    linarith

lemma h3e_Psi_bound {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    (z : Ch N) : |Ψ z - Ψ 0| ≤ ‖gradient Ψ 0‖ * ‖z‖ + L * ‖z‖ ^ 2 := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  set g : ℝ → ℝ := fun s => Ψ (s • z) with hg
  have hder : ∀ s : ℝ, HasDerivAt g (fderiv ℝ Ψ (s • z) z) s := by
    intro s
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (s • z)) (s • z) := (hd _).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • z) z s := by
      simpa using (hasDerivAt_id s).smul_const z
    exact h1.comp_hasDerivAt s h2
  have hbound : ∀ s ∈ Ico (0:ℝ) 1, ‖fderiv ℝ Ψ (s • z) z‖ ≤ (‖gradient Ψ 0‖ + L * ‖z‖) * ‖z‖ := by
    intro s hs
    have e : fderiv ℝ Ψ (s • z) z = inner ℝ (gradient Ψ (s • z)) z := by
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    rw [e]
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have := hΨL.dist_le_mul (s • z) 0
    rw [dist_eq_norm, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg hs.1] at this
    calc ‖gradient Ψ (s • z)‖ ≤ ‖gradient Ψ 0‖ + ‖gradient Ψ (s • z) - gradient Ψ 0‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖gradient Ψ 0‖ + L * (s * ‖z‖) := by gcongr
      _ ≤ ‖gradient Ψ 0‖ + L * ‖z‖ := by
        gcongr
        nlinarith [hs.2, norm_nonneg z]
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := 0) (b := 1)
    (fun x _ => (hder x).hasDerivWithinAt) hbound 1 (by simp)
  simp only [hg, one_smul, zero_smul, sub_zero, Real.norm_eq_abs] at this
  calc |Ψ z - Ψ 0| ≤ _ := this
    _ = _ := by ring

lemma h3e_real_ineq {N a L n s d B : ℝ} (hN : 0 < N) (ha : 0 ≤ a) (hL : 0 ≤ L) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hsd : s ≤ 2 * Real.sqrt N * (1 + d)) (hn : 32 * N * (L + 1) ≤ n) :
    B + a * s + L * s ^ 2 - n / 2 * d ^ 2 ≤ B + a ^ 2 / 2 + 4 * a * Real.sqrt N + 16 * N * L + 8 * N - s ^ 2 / 2 := by
  set r := Real.sqrt N with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hN
  have hr2 : r ^ 2 = N := Real.sq_sqrt hN.le
  have has : a * s ≤ a ^ 2 / 2 + s ^ 2 / 2 := by nlinarith [sq_nonneg (a - s)]
  by_cases hcase : 4 * r ≤ s
  · have hd1 : s / (4 * r) ≤ d := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hd2 : s ^ 2 / (16 * N) ≤ d ^ 2 := by
      have : (s / (4 * r)) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hd1 2
      calc s ^ 2 / (16 * N) = (s / (4 * r)) ^ 2 := by rw [div_pow, mul_pow, hr2]; ring
        _ ≤ d ^ 2 := this
    have hd3 : (L + 1) * s ^ 2 ≤ n / 2 * d ^ 2 := by
      have h1 : s ^ 2 ≤ 16 * N * d ^ 2 := by
        rwa [div_le_iff₀ (by positivity), mul_comm] at hd2
      have h2 : (L + 1) * s ^ 2 ≤ (L + 1) * (16 * N * d ^ 2) := mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : (L + 1) * (16 * N * d ^ 2) = 16 * N * (L + 1) * d ^ 2 := by ring
      have h4 : 16 * N * (L + 1) * d ^ 2 ≤ n / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg d)
      linarith
    have : 0 ≤ 4 * a * r := by positivity
    have : 0 ≤ 16 * N * L := by positivity
    nlinarith
  · push_neg at hcase
    have hs2 : s ^ 2 ≤ 16 * N := by nlinarith
    have h1 : a * s ≤ a * (4 * r) := mul_le_mul_of_nonneg_left hcase.le ha
    have h2 : L * s ^ 2 ≤ L * (16 * N) := mul_le_mul_of_nonneg_left hs2 hL
    have h3 : 0 ≤ n / 2 * d ^ 2 := by
      have : 0 ≤ n := by nlinarith [mul_pos hN hN, hL]
      positivity
    nlinarith [sq_nonneg a]

lemma h3e_norm_le_infDist [NeZero N] {z : Ch N} (hz : z ∈ cep_cell N) :
    ‖z‖ ≤ 2 * Real.sqrt N * (1 + Metric.infDist z (cep_Alcove N)) := by
  obtain ⟨w, hw, -⟩ := h3e_alcove_point (N := N)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ a ∈ cep_Alcove N, ‖z‖ ≤ 2 * Real.sqrt N * (1 + dist z a) := by
    intro a ha
    set r := dist z a with hr
    have hk : ∀ k : Fin N, |z k| ≤ 2 + 2 * r := by
      intro k
      have hlt : a 0 ≤ a k ∧ a k < a 0 + 1 := ⟨by
        by_cases hk0 : (0 : Fin N) = k
        · rw [hk0]
        · exact (ha.1 0 k (lt_of_le_of_ne (Fin.zero_le _) hk0)).le, ha.2 0 k⟩
      have e1 : |z k - a k| ≤ r := by
        have := PiLp.norm_apply_le (z - a) k
        rwa [← dist_eq_norm] at this
      have e0 : |z 0 - a 0| ≤ r := by
        have := PiLp.norm_apply_le (z - a) 0
        rwa [← dist_eq_norm] at this
      rw [abs_le] at e1 e0 ⊢
      have := hz.1; have := hz.2
      constructor <;> linarith [e1.1, e1.2, e0.1, e0.2]
    have hsq : ‖z‖ ^ 2 ≤ N * (2 + 2 * r) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ k, ‖z k‖ ^ 2 ≤ ∑ _k : Fin N, (2 + 2 * r) ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hk k) 2
        _ = N * (2 + 2 * r) ^ 2 := by simp
    have hr0 : 0 ≤ r := dist_nonneg
    have : ‖z‖ ≤ Real.sqrt (N * (2 + 2 * r) ^ 2) := Real.le_sqrt_of_sq_le hsq
    rw [Real.sqrt_mul hN.le, Real.sqrt_sq (by positivity)] at this
    linarith
  have hpos : 0 < 2 * Real.sqrt N := by have := Real.sqrt_pos.mpr hN; positivity
  have h2 : ‖z‖ / (2 * Real.sqrt N) - 1 ≤ Metric.infDist z (cep_Alcove N) :=
    (Metric.le_infDist ⟨w, hw⟩).mpr fun a ha => by
      have := key a ha
      rw [sub_le_iff_le_add', div_le_iff₀ hpos]
      linarith
  rw [sub_le_iff_le_add', div_le_iff₀ hpos] at h2
  linarith
end
end HRS.MC.CepH3
