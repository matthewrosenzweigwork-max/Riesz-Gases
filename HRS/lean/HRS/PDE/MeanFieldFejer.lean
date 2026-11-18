import HRS.PDE.MeanFieldInputs
import HRS.PDE.MeanFieldThermalUnique

/-!
# Fejér kernel on the torus and convolution facts (package MF-01, packet P2a)

The product Fejér kernel `F_N(x) = ∏_i |∑_{j<N} e^{2πi j x_i}|²/N` is nonnegative, has mean one and
Fourier coefficients `∏_i (1 - |k_i|/N)_+`; convolution with `F_N` is an approximate identity on
continuous functions (`fejer_tendsto_uniformly`).  Further: `L¹`-continuity of translations
(`l1_modulus`) and the elementary convolution bounds.  Plan: `HRS/PDE/MeanFieldPlan.md`, §3.1.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFThermalExist

variable {d : ℕ}

/-! ### One-dimensional layer -/

/-- `fourier j` as a power of `fourier 1`. -/
theorem fourier_natCast_eq_pow (j : ℕ) (t : UnitAddCircle) :
    fourier (j : ℤ) t = (fourier 1 t) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [this, fourier_add, ih, pow_succ]

/-- The one-dimensional Fejér kernel. -/
def fej1 (N : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖∑ j ∈ Finset.range N, fourier (j : ℤ) t‖ ^ 2 / N

theorem fej1_nonneg (N : ℕ) (t : UnitAddCircle) : 0 ≤ fej1 N t := by
  unfold fej1; positivity

theorem fej1_continuous (N : ℕ) : Continuous (fej1 N) := by
  unfold fej1
  have : ∀ j : ℤ, Continuous (fun t : UnitAddCircle => fourier j t) := fun j => (fourier j).continuous
  fun_prop

/-- The key algebraic identity (Fejér): `|∑_{j<N} e_j|² = ∑_{j,l<N} e_{j-l}`. -/
theorem fej1_mul_eq (N : ℕ) (t : UnitAddCircle) :
    ((fej1 N t : ℝ) : ℂ) * N =
      ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, fourier ((j : ℤ) - l) t := by
  unfold fej1
  by_cases hN : N = 0
  · subst hN; simp
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [Complex.ofReal_div]
  push_cast
  rw [div_mul_cancel₀ _ hN', ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← fourier_neg, ← fourier_add, sub_eq_add_neg]

theorem volume_circle_eq_haar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]; simp

theorem integral_fourier_mul (m n : ℤ) :
    ∫ t : UnitAddCircle, fourier (-m) t * fourier n t = if m = n then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) m
  unfold fourierCoeff at h
  rw [volume_circle_eq_haar]
  simp only [smul_eq_mul] at h
  rw [h, Pi.single_apply]

/-- Counting the pairs `(j,l)` with `j - l = m`. -/
theorem card_pairs (N : ℕ) (m : ℤ) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = m)).card =
      N - m.natAbs := by
  rcases le_total 0 m with hm | hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have : (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = n) =
        (Finset.range (N - n)).image (fun l => (l + n, l)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
        Prod.ext_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨b, by omega, by omega, rfl⟩
      · rintro ⟨l, h1, h2, h3⟩
        subst h2 h3
        omega
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.snd h),
      Finset.card_range]
    simp
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hm
    subst hn
    have : (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = -(n : ℤ)) =
        (Finset.range (N - n)).image (fun l => (l, l + n)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
        Prod.ext_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨a, by omega, rfl, by omega⟩
      · rintro ⟨l, h1, h2, h3⟩
        subst h2 h3
        omega
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h),
      Finset.card_range]
    simp

theorem fej1_coeff (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∫ t : UnitAddCircle, fourier (-m) t * ((fej1 N t : ℝ) : ℂ) =
      ((max (1 - |(m : ℝ)| / N) 0 : ℝ) : ℂ) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hF : ∀ t : UnitAddCircle, ((fej1 N t : ℝ) : ℂ) = (1 / (N : ℂ)) *
      ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, fourier ((j : ℤ) - l) t := by
    intro t
    rw [← fej1_mul_eq]; field_simp
  have hc : ∀ j l : ℕ, Continuous fun t : UnitAddCircle => fourier (-m) t * fourier ((j : ℤ) - l) t :=
    fun j l => (fourier (-m)).continuous.mul (fourier _).continuous
  have hi : ∀ j l : ℕ, Integrable fun t : UnitAddCircle => fourier (-m) t * fourier ((j : ℤ) - l) t :=
    fun j l => (hc j l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : (fun t : UnitAddCircle => fourier (-m) t * ((fej1 N t : ℝ) : ℂ)) = fun t =>
      (1 / (N : ℂ)) * ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        fourier (-m) t * fourier ((j : ℤ) - l) t := by
    funext t
    rw [hF, mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [e, integral_const_mul, integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hi j l))]
  simp_rw [integral_finsetSum _ (fun l _ => hi _ l), integral_fourier_mul]
  have hsum : (∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, (if m = (x : ℤ) - y then (1 : ℂ) else 0)) =
      ((N - m.natAbs : ℕ) : ℂ) := by
    rw [← card_pairs N m, ← Finset.sum_product' (f := fun (x y : ℕ) => if m = (x : ℤ) - y then (1 : ℂ) else 0),
      Finset.sum_boole]
    congr 3
    ext p
    simp [eq_comm]
  rw [hsum]
  have hr : (((N - m.natAbs : ℕ) : ℝ)) / N = max (1 - |(m : ℝ)| / N) 0 := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have habs : |(m : ℝ)| = (m.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs]
    by_cases h : m.natAbs ≤ N
    · rw [Nat.cast_sub h, max_eq_left]
      · field_simp
      · rw [sub_nonneg, div_le_one hNr]; exact_mod_cast h
    · push Not at h
      rw [Nat.sub_eq_zero_of_le h.le, max_eq_right]
      · simp
      · rw [sub_nonpos, one_le_div hNr]; exact_mod_cast h.le
  rw [← hr]
  push_cast
  field_simp

theorem exists_fourier_sub_one_lower (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : UnitAddCircle, δ ≤ ‖t‖ → c ≤ ‖fourier 1 t - 1‖ := by
  set S : Set UnitAddCircle := {t | δ ≤ ‖t‖} with hSdef
  have hS : IsCompact S := (isClosed_le continuous_const continuous_norm).isCompact
  by_cases hne : S.Nonempty
  · have hc : Continuous fun t : UnitAddCircle => ‖fourier 1 t - 1‖ :=
      (((fourier 1).continuous).sub continuous_const).norm
    obtain ⟨t0, ht0, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
    refine ⟨‖fourier 1 t0 - 1‖, ?_, fun t ht => hmin ht⟩
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    rw [fourier_one] at h
    have h0 : AddCircle.toCircle t0 = AddCircle.toCircle (0 : UnitAddCircle) :=
      Subtype.ext (by simpa using h)
    have := (AddCircle.injective_toCircle one_ne_zero) h0
    have h1 : δ ≤ ‖t0‖ := ht0
    rw [this, norm_zero] at h1
    linarith
  · exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne⟩

theorem fej1_tail_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ t : UnitAddCircle, δ ≤ ‖t‖ → fej1 N t ≤ C / N := by
  obtain ⟨c, hc, hct⟩ := exists_fourier_sub_one_lower δ hδ
  refine ⟨4 / c ^ 2, by positivity, fun N hN t ht => ?_⟩
  unfold fej1
  have hz : ‖fourier 1 t‖ = 1 := by rw [fourier_one]; exact Circle.norm_coe _
  set z := fourier (1 : ℤ) t with hzdef
  have hS : ∑ j ∈ Finset.range N, fourier (j : ℤ) t = ∑ j ∈ Finset.range N, z ^ j :=
    Finset.sum_congr rfl fun j _ => fourier_natCast_eq_pow j t
  rw [hS]
  have hgeom : (z - 1) * ∑ j ∈ Finset.range N, z ^ j = z ^ N - 1 := mul_geom_sum z N
  have h2 : ‖z - 1‖ * ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have h3 : c * ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_right (hct t ht) (norm_nonneg _)) h2
  have h4 : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / c := by
    rw [le_div_iff₀ hc]; linarith
  have h5 : ‖∑ j ∈ Finset.range N, z ^ j‖ ^ 2 ≤ 4 / c ^ 2 := by
    calc _ ≤ (2 / c) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = 4 / c ^ 2 := by field_simp; norm_num
  exact div_le_div_of_nonneg_right h5 (Nat.cast_nonneg N)

/-! ### The product Fejér kernel -/

/-- Fejér (product) kernel of order `N`: nonnegative, mean one, coefficients `∏_i (1 - |k_i|/N)_+`. -/
noncomputable def fejer (N : ℕ) (x : Torus d) : ℝ :=
  ∏ i : Fin d, (‖∑ j ∈ Finset.range N, Torus.mode (Pi.single i (j : ℤ)) x‖ ^ 2 / N)

theorem mode_single (i : Fin d) (j : ℤ) (x : Torus d) :
    Torus.mode (Pi.single i j) x = fourier j (x i) := by
  unfold Torus.mode UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · simp
  · intro i' _ hi'
    simp [hi']
  · simp

theorem fejer_eq_prod (N : ℕ) (x : Torus d) : fejer N x = ∏ i, fej1 N (x i) := by
  unfold fejer fej1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp_rw [mode_single]

theorem fejer_nonneg (N : ℕ) (x : Torus d) : 0 ≤ fejer N x := by
  rw [fejer_eq_prod]
  exact Finset.prod_nonneg fun i _ => fej1_nonneg N _

theorem fejer_continuous (N : ℕ) : Continuous (fejer (d := d) N) := by
  have : (fejer (d := d) N) = fun x => ∏ i, fej1 N (x i) := funext (fejer_eq_prod N)
  rw [this]
  exact continuous_finsetProd _ fun i _ => (fej1_continuous N).comp (continuous_apply i)

theorem integral_fej1 (N : ℕ) (hN : 0 < N) : ∫ t, fej1 N t = 1 := by
  have h := fej1_coeff N hN 0
  simp only [neg_zero, fourier_zero, one_mul, Int.cast_zero, abs_zero, zero_div, sub_zero] at h
  rw [integral_complex_ofReal] at h
  simpa using h

theorem integral_fejer (N : ℕ) (hN : 0 < N) : ∫ x, fejer (d := d) N x = 1 := by
  simp_rw [fejer_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun _ t => fej1 N t)]
  simp [integral_fej1 N hN]

theorem coeffOf_fejer (N : ℕ) (hN : 0 < N) (k : Lattice d) :
    coeffOf (fejer N) k = ∏ i : Fin d, ((max (1 - |(k i : ℝ)| / N) 0 : ℝ) : ℂ) := by
  unfold coeffOf Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  have : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x • ((fejer N x : ℝ) : ℂ) =
      ∏ i, (fourier (-(k i)) (x i) * ((fej1 N (x i) : ℝ) : ℂ)) := by
    intro x
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, smul_eq_mul,
      fejer_eq_prod, Complex.ofReal_prod]
    rw [Finset.prod_mul_distrib]
  simp_rw [this]
  have key := integral_fintype_prod_eq_prod (𝕜 := ℂ) (E := fun _ : Fin d => UnitAddCircle)
    (μ := fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (fun i (t : UnitAddCircle) => fourier (-(k i)) t * ((fej1 N t : ℝ) : ℂ))
  refine Eq.trans key ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← volume_circle_eq_haar]
  exact fej1_coeff N hN (k i)

/-! ### Approximate identity -/

/-- The mass of the `i`-th coordinate tail `{δ ≤ ‖x_i‖}` under `F_N` is the one-dimensional tail. -/
theorem integral_fejer_tail (N : ℕ) (hN : 0 < N) (δ : ℝ) (i : Fin d) :
    ∫ z : Torus d, Set.indicator {z : Torus d | δ ≤ ‖z i‖} (fejer N) z =
      ∫ t : UnitAddCircle, Set.indicator {t : UnitAddCircle | δ ≤ ‖t‖} (fej1 N) t := by
  classical
  have hpt : ∀ z : Torus d, Set.indicator {z : Torus d | δ ≤ ‖z i‖} (fejer N) z =
      ∏ i', (if i' = i then Set.indicator {t : UnitAddCircle | δ ≤ ‖t‖} (fej1 N)
        else fej1 N) (z i') := by
    intro z
    by_cases h : δ ≤ ‖z i‖
    · rw [Set.indicator_of_mem (by exact h), fejer_eq_prod]
      refine Finset.prod_congr rfl fun i' _ => ?_
      by_cases hi : i' = i
      · subst hi; simp [Set.indicator_of_mem, h]
      · simp [hi]
    · rw [Set.indicator_of_notMem (by exact h)]
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [Set.indicator_of_notMem, h]
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i' (t : UnitAddCircle) => (if i' = i then Set.indicator {t : UnitAddCircle | δ ≤ ‖t‖}
      (fej1 N) else fej1 N) t)]
  rw [Finset.prod_eq_single i]
  · simp
  · intro i' _ hi'
    simp [hi', integral_fej1 N hN]
  · simp

theorem integral_fej1_tail_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      ∫ t : UnitAddCircle, Set.indicator {t : UnitAddCircle | δ ≤ ‖t‖} (fej1 N) t ≤ C / N := by
  obtain ⟨C, hC, hCt⟩ := fej1_tail_le δ hδ
  refine ⟨C, hC, fun N hN => ?_⟩
  have hnn : 0 ≤ᵐ[volume] Set.indicator {t : UnitAddCircle | δ ≤ ‖t‖} (fej1 N) :=
    Filter.Eventually.of_forall fun t => Set.indicator_nonneg (fun t _ => fej1_nonneg N t) t
  calc _ ≤ ∫ t : UnitAddCircle, C / N :=
        integral_mono_of_nonneg hnn (integrable_const _) (Filter.Eventually.of_forall fun t => by
          by_cases h : δ ≤ ‖t‖
          · rw [Set.indicator_of_mem (by exact h)]; exact hCt N hN t h
          · rw [Set.indicator_of_notMem (by exact h)]; positivity)
    _ = C / N := by simp

/-- `g ⋆ h (x) = ∫ g(z) h(x - z) dz`. -/
theorem convFun_eq (g h : Torus d → ℝ) (x : Torus d) :
    convFun g h x = ∫ z, g z * h (x - z) := by
  unfold convFun
  rw [← integral_sub_left_eq_self (fun y => g (x - y) * h y) volume x]
  simp

theorem integrable_of_continuous' {g : Torus d → ℝ} (hg : Continuous g) : Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Fejér means converge uniformly for continuous functions (approximate identity). -/
theorem fejer_tendsto_uniformly (v : Torus d → ℝ) (hv : Continuous v) :
    TendstoUniformly (fun N x => convFun (fejer N) v x) v atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hv.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Set.mem_univ _))
  obtain ⟨δ, hδ, hδv⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hv) (ε / 2) (by positivity)
  obtain ⟨C, hC, hCt⟩ := integral_fej1_tail_le δ hδ
  have hlim : Tendsto (fun N : ℕ => (ε / 2)⁻¹ * (2 * M * d * C) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 0] with N hNlt hN x
  have hF := fejer_continuous (d := d) N
  have hFnn := fejer_nonneg (d := d) N
  have hFint := integral_fejer (d := d) N hN
  set F := fejer (d := d) N with hFdef
  -- the difference as a single integral
  have hvx : ∫ z, F z * v x = v x := by rw [integral_mul_const, hFint, one_mul]
  have hi1 : Integrable fun z => F z * v (x - z) :=
    integrable_of_continuous' (hF.mul (hv.comp (continuous_const.sub continuous_id)))
  have hi2 : Integrable fun z => F z * v x := integrable_of_continuous' (hF.mul continuous_const)
  have hdiff : ∫ z, F z * (v x - v (x - z)) = v x - convFun F v x := by
    calc ∫ z, F z * (v x - v (x - z)) = ∫ z, (F z * v x - F z * v (x - z)) := by
          simp_rw [mul_sub]
      _ = (∫ z, F z * v x) - ∫ z, F z * v (x - z) := integral_sub hi2 hi1
      _ = v x - convFun F v x := by rw [hvx, convFun_eq]
  -- pointwise bound
  set g : Fin d → Torus d → ℝ := fun i => Set.indicator {z : Torus d | δ ≤ ‖z i‖} F with hg
  have hgint : ∀ i, Integrable (g i) := fun i =>
    (integrable_of_continuous' hF).indicator
      (isClosed_le continuous_const ((continuous_apply i).norm)).measurableSet
  have hpt : ∀ z, F z * |v x - v (x - z)| ≤ F z * (ε / 2) + 2 * M * ∑ i, g i z := by
    intro z
    by_cases hz : ‖z‖ < δ
    · have h1 : |v x - v (x - z)| ≤ ε / 2 := by
        have := hδv (a := x) (b := x - z) (by
          rw [dist_eq_norm]; simpa using hz)
        rw [Real.dist_eq] at this
        exact this.le
      have : 0 ≤ ∑ i, g i z := Finset.sum_nonneg fun i _ =>
        Set.indicator_nonneg (fun z _ => hFnn z) z
      nlinarith [hFnn z, mul_le_mul_of_nonneg_left h1 (hFnn z)]
    · have hex : ∃ i, δ ≤ ‖z i‖ := by
        by_contra hcon
        push Not at hcon
        exact hz ((pi_norm_lt_iff hδ).mpr hcon)
      obtain ⟨i0, hi0⟩ := hex
      have h1 : |v x - v (x - z)| ≤ 2 * M := by
        have a1 := hM x (Set.mem_univ _)
        have a2 := hM (x - z) (Set.mem_univ _)
        rw [Real.norm_eq_abs] at a1 a2
        calc _ ≤ |v x| + |v (x - z)| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      have h2 : g i0 z = F z := Set.indicator_of_mem (by exact hi0) _
      have h3 : g i0 z ≤ ∑ i, g i z :=
        Finset.single_le_sum (f := fun i => g i z)
          (fun i _ => Set.indicator_nonneg (fun z _ => hFnn z) z) (Finset.mem_univ i0)
      have h4 : F z * |v x - v (x - z)| ≤ F z * (2 * M) :=
        mul_le_mul_of_nonneg_left h1 (hFnn z)
      have h5 := mul_nonneg (hFnn z) (show 0 ≤ ε / 2 by positivity)
      calc F z * |v x - v (x - z)| ≤ F z * (2 * M) := h4
        _ = 2 * M * g i0 z := by rw [h2]; ring
        _ ≤ 2 * M * ∑ i, g i z := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ _ := by linarith
  have hcont : Continuous fun z => F z * |v x - v (x - z)| :=
    hF.mul (continuous_const.sub (hv.comp (continuous_const.sub continuous_id))).abs
  have hrhs : Integrable fun z => F z * (ε / 2) + 2 * M * ∑ i, g i z :=
    (integrable_of_continuous' (hF.mul continuous_const)).add
      ((integrable_finsetSum _ fun i _ => hgint i).const_mul _)
  have hint : ∫ z, F z * (ε / 2) + 2 * M * ∑ i, g i z ≤ ε / 2 + 2 * M * d * (C / N) := by
    have hA : Integrable fun z => F z * (ε / 2) := integrable_of_continuous' (hF.mul continuous_const)
    have hB : Integrable fun z => 2 * M * ∑ i, g i z :=
      (integrable_finsetSum _ fun i _ => hgint i).const_mul _
    rw [integral_add hA hB, integral_mul_const, hFint, integral_const_mul,
      integral_finsetSum _ fun i _ => hgint i]
    have : ∀ i, ∫ z, g i z ≤ C / N := fun i => by
      rw [hg]; simp only; rw [integral_fejer_tail N hN δ i]; exact hCt N hN
    have hsum : ∑ i, ∫ z, g i z ≤ d * (C / N) := by
      calc _ ≤ ∑ _i : Fin d, (C / N) := Finset.sum_le_sum fun i _ => this i
        _ = d * (C / N) := by simp
    have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * M by positivity)
    nlinarith
  have hsmall : 2 * M * d * (C / N) < ε / 2 := by
    have h := hNlt
    rw [mul_div_assoc, inv_mul_lt_iff₀ (by positivity)] at h
    have e : 2 * M * d * (C / N) = 2 * M * d * C / N := by ring
    rw [e]; linarith
  rw [Real.dist_eq]
  calc |v x - convFun F v x| = |∫ z, F z * (v x - v (x - z))| := by rw [hdiff]
    _ ≤ ∫ z, ‖F z * (v x - v (x - z))‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = ∫ z, F z * |v x - v (x - z)| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnn z)]
    _ ≤ ∫ z, F z * (ε / 2) + 2 * M * ∑ i, g i z :=
        integral_mono (integrable_of_continuous' hcont) hrhs hpt
    _ < ε := by linarith

/-! ### `L¹`-continuity of translations -/

/-- `L¹` continuity of translations on the torus (density of continuous functions in `L¹`). -/
theorem l1_modulus {g : Torus d → ℝ} (hg : Integrable g) :
    Tendsto (fun h : Torus d => ∫ x, |g (x - h) - g x|) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨φ, -, hφ, hφc, hφi⟩ := hg.exists_hasCompactSupport_integral_sub_le (ε := ε / 4) (by positivity)
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hφc) (ε / 4) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : Torus d) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  rw [Real.dist_eq, sub_zero]
  have i1 : Integrable fun x => |g (x - h) - g x| := ((hg.comp_sub_right h).sub hg).abs
  have i2 : Integrable fun x => |g (x - h) - φ (x - h)| :=
    ((hg.comp_sub_right h).sub (hφi.comp_sub_right h)).abs
  have i3 : Integrable fun x => |φ (x - h) - φ x| := ((hφi.comp_sub_right h).sub hφi).abs
  have i4 : Integrable fun x => |φ x - g x| := (hφi.sub hg).abs
  have hpt : ∀ x, |g (x - h) - g x| ≤
      |g (x - h) - φ (x - h)| + |φ (x - h) - φ x| + |φ x - g x| := fun x => by
    have e : g (x - h) - g x = (g (x - h) - φ (x - h)) + (φ (x - h) - φ x) + (φ x - g x) := by
      ring
    rw [e]; exact abs_add_three _ _ _
  have hI2 : ∫ x, |g (x - h) - φ (x - h)| = ∫ x, |g x - φ x| :=
    integral_sub_right_eq_self (fun x => |g x - φ x|) h
  have hI3 : ∫ x, |φ (x - h) - φ x| ≤ ε / 4 := by
    calc ∫ x, |φ (x - h) - φ x| ≤ ∫ _x : Torus d, ε / 4 :=
          integral_mono i3 (integrable_const _) fun x => by
            have := hδφ (a := x - h) (b := x) (by
              rw [dist_eq_norm]; simpa using hh)
            rw [Real.dist_eq] at this; exact this.le
      _ = ε / 4 := by simp
  have hI4 : ∫ x, |φ x - g x| ≤ ε / 4 := by
    have : ∫ x, |φ x - g x| = ∫ x, ‖g x - φ x‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [abs_sub_comm]
    rw [this]; exact hφ
  have hI2' : ∫ x, |g (x - h) - φ (x - h)| ≤ ε / 4 := by
    rw [hI2]
    have : ∫ x, |g x - φ x| = ∫ x, ‖g x - φ x‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    rw [this]; exact hφ
  have i23 : Integrable fun x => |g (x - h) - φ (x - h)| + |φ (x - h) - φ x| := i2.add i3
  have hmain : ∫ x, |g (x - h) - g x| ≤ ∫ x, (|g (x - h) - φ (x - h)| + |φ (x - h) - φ x| +
      |φ x - g x|) := integral_mono i1 (i23.add i4) hpt
  rw [integral_add i23 i4, integral_add i2 i3] at hmain
  have hnn : 0 ≤ ∫ x, |g (x - h) - g x| := integral_nonneg fun x => abs_nonneg _
  rw [abs_of_nonneg hnn]
  linarith

/-! ### Convolution bounds -/

/-- Young's inequality for `L¹ ⋆ L^∞`: `|g ⋆ h (x)| ≤ ‖g‖_{L¹} M` when `|h| ≤ M`. -/
theorem convFun_bound_of_le {g h : Torus d → ℝ} (hg : Integrable g) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x : Torus d) : |convFun g h x| ≤ (∫ y, |g y|) * M := by
  have hgx : Integrable fun y => |g (x - y)| * M := (hg.comp_sub_left x).abs.mul_const M
  unfold convFun
  rw [← Real.norm_eq_abs]
  calc ‖∫ y, g (x - y) * h y‖ ≤ ∫ y, |g (x - y)| * M :=
        norm_integral_le_of_norm_le hgx (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _))
    _ = (∫ y, |g y|) * M := by
        rw [integral_mul_const, integral_sub_left_eq_self (fun y => |g y|) volume x]

/-- `|g ⋆ h (x)| ≤ ‖g‖_{L¹} ‖h‖_∞` (`supNorm` of a bounded `h`). -/
theorem convFun_bound {g h : Torus d → ℝ} (hg : Integrable g)
    (hh : BddAbove (Set.range fun y => ‖h y‖)) (x : Torus d) :
    |convFun g h x| ≤ (∫ y, |g y|) * Torus.supNorm h :=
  convFun_bound_of_le hg (fun y => by
    rw [← Real.norm_eq_abs]; exact le_ciSup hh y) x

theorem integrable_fejer_mul {N : ℕ} {h : Torus d → ℝ} (hh : Integrable h) (x : Torus d) :
    Integrable fun z => fejer N z * h (x - z) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
    (fejer_continuous (d := d) N).continuousOn
  have := (hh.comp_sub_left x).mul_bdd (fejer_continuous (d := d) N).aestronglyMeasurable
    (c := B) (Filter.Eventually.of_forall fun y => hB y (Set.mem_univ _))
  exact this.congr (Filter.Eventually.of_forall fun z => by simp [mul_comm])

/-- Lower bound for `F_N ⋆ h` (`F_N ≥ 0` with mean one). -/
theorem convFun_fejer_ge {N : ℕ} (hN : 0 < N) {h : Torus d → ℝ} (hh : Integrable h) {m : ℝ}
    (hm : ∀ y, m ≤ h y) (x : Torus d) : m ≤ convFun (fejer N) h x := by
  rw [convFun_eq]
  have hc : Integrable fun z : Torus d => fejer N z * m :=
    integrable_of_continuous' ((fejer_continuous (d := d) N).mul continuous_const)
  have := integral_mono hc (integrable_fejer_mul hh x)
    (fun z => mul_le_mul_of_nonneg_left (hm _) (fejer_nonneg N z))
  rwa [integral_mul_const, integral_fejer N hN, one_mul] at this

/-- Upper bound for `F_N ⋆ h` (`F_N ≥ 0` with mean one). -/
theorem convFun_fejer_le {N : ℕ} (hN : 0 < N) {h : Torus d → ℝ} (hh : Integrable h) {M : ℝ}
    (hM : ∀ y, h y ≤ M) (x : Torus d) : convFun (fejer N) h x ≤ M := by
  rw [convFun_eq]
  have hc : Integrable fun z : Torus d => fejer N z * M :=
    integrable_of_continuous' ((fejer_continuous (d := d) N).mul continuous_const)
  have := integral_mono (integrable_fejer_mul hh x) hc
    (fun z => mul_le_mul_of_nonneg_left (hM _) (fejer_nonneg N z))
  rwa [integral_mul_const, integral_fejer N hN, one_mul] at this

/-- (Young, `F_N ≥ 0`) two-sided bounds are preserved by convolution with `F_N`. -/
theorem convFun_fejer_bound {N : ℕ} (hN : 0 < N) {h : Torus d → ℝ} (hh : Integrable h)
    {m M : ℝ} (hm : ∀ y, m ≤ h y) (hM : ∀ y, h y ≤ M) (x : Torus d) :
    m ≤ convFun (fejer N) h x ∧ convFun (fejer N) h x ≤ M :=
  ⟨convFun_fejer_ge hN hh hm x, convFun_fejer_le hN hh hM x⟩

/-! ### Thermal uniqueness for `d ≥ 1` against the kernel-facts bundle -/

section ThermalUnique

/-- Parseval for the interaction form: `∫ (g*z) z = ∑_k ĝ(k) |ẑ(k)|²`. -/
theorem hasSum_convFun_mul_self' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) {z : Torus d → ℝ} (hz : Continuous z) :
    HasSum (fun k : Lattice d =>
        rieszCoeff d s k * ‖Torus.funFourierCoeff (fun x => (z x : ℂ)) k‖ ^ 2)
      (∫ x, convFun (periodicRiesz d s) z x * z x) := by
  have hg := F.integrable
  have hu : Continuous (convFun (periodicRiesz d s) z) := MFAux.continuous_convFun hg hz
  set u := convFun (periodicRiesz d s) z with hudef
  have hzc : Continuous fun x => (z x : ℂ) := Complex.continuous_ofReal.comp hz
  have huc : Continuous fun x => (u x : ℂ) := Complex.continuous_ofReal.comp hu
  have hP := hasSum_parseval (fun x => (u x : ℂ)) (fun x => (z x : ℂ))
    (MFThermal.memLp_two_of_continuous huc) (MFThermal.memLp_two_of_continuous hzc)
  have hterm : ∀ k : Lattice d,
      conj (Torus.funFourierCoeff (fun x => (u x : ℂ)) k) *
        Torus.funFourierCoeff (fun x => (z x : ℂ)) k =
      ((rieszCoeff d s k * ‖Torus.funFourierCoeff (fun x => (z x : ℂ)) k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [hudef, MFAux.funFourierCoeff_convFun hg hz k, F.fourierCoeff k]
    push_cast
    rw [map_mul, Complex.conj_ofReal]
    rw [mul_assoc, Complex.conj_mul']
  have hval : (∫ t, conj ((u t : ℂ)) * (z t : ℂ)) = ((∫ x, u x * z x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.conj_ofReal]
  simp_rw [hterm, hval] at hP
  exact Complex.hasSum_ofReal.mp hP

/-- The interaction form `∫ (g*z) z` is nonnegative (`ĝ ≥ 0`, `ĝ(0) = 0`). -/
theorem integral_convFun_mul_self_nonneg' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) {z : Torus d → ℝ} (hz : Continuous z) :
    0 ≤ ∫ x, convFun (periodicRiesz d s) z x * z x := by
  refine (hasSum_convFun_mul_self' hd s hs0 hsd F hz).nonneg fun k => ?_
  by_cases hk : k = 0
  · simp [rieszCoeff, hk]
  · exact mul_nonneg (rieszCoeff_pos' hd hs0 hsd k hk).le (sq_nonneg _)

/-- **Uniqueness of the thermal equilibrium**: two continuous positive thermal densities for the
same `V`, `β > 0` and Riesz kernel coincide (no hypothesis on `V`). -/
theorem thermal_unique' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (ρ ρ' : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x)
    (hρ' : IsThermalDensity (periodicRiesz d s) V β ρ') (hρc' : Continuous ρ')
    (hρp' : ∀ x, 0 < ρ' x) :
    ρ' = ρ := by
  have hg := F.integrable
  obtain ⟨c₁, h₁⟩ := MFThermal.log_thermal hρ hρp
  obtain ⟨c₂, h₂⟩ := MFThermal.log_thermal hρ' hρp'
  set z : Torus d → ℝ := fun x => ρ x - ρ' x with hzdef
  have hzc : Continuous z := hρc.sub hρc'
  have hlin : ∀ x, convFun (periodicRiesz d s) ρ x - convFun (periodicRiesz d s) ρ' x =
      convFun (periodicRiesz d s) z x := fun x => (MFThermal.convFun_sub hg hρc hρc' x).symm
  have hdiff : ∀ x, Real.log (ρ x) - Real.log (ρ' x) =
      -β * convFun (periodicRiesz d s) z x + (c₁ - c₂) := by
    intro x
    rw [h₁ x, h₂ x, ← hlin x]
    ring
  have hzint : ∫ x, z x = 0 := by
    rw [hzdef, integral_sub (MFThermal.integrable_of_continuous hρc) (MFThermal.integrable_of_continuous hρc'),
      hρ.1.integral_one, hρ'.1.integral_one]
    ring
  have huc : Continuous (convFun (periodicRiesz d s) z) := MFAux.continuous_convFun hg hzc
  have hlogc : Continuous fun x => (Real.log (ρ x) - Real.log (ρ' x)) * z x := by
    refine Continuous.mul (Continuous.sub ?_ ?_) hzc
    · exact hρc.log fun x => (hρp x).ne'
    · exact hρc'.log fun x => (hρp' x).ne'
  have hE : ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x =
      -β * ∫ x, convFun (periodicRiesz d s) z x * z x := by
    have : ∀ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x =
        -β * (convFun (periodicRiesz d s) z x * z x) + (c₁ - c₂) * z x := by
      intro x; rw [hdiff x]; ring
    simp_rw [this]
    have i1 : Integrable (fun x => convFun (periodicRiesz d s) z x * z x) :=
      MFThermal.integrable_of_continuous (huc.mul hzc)
    have i2 : Integrable z := MFThermal.integrable_of_continuous hzc
    rw [integral_add (i1.const_mul (-β)) (i2.const_mul (c₁ - c₂)), integral_const_mul,
      integral_const_mul, hzint]
    ring
  have hnn := integral_convFun_mul_self_nonneg' hd s hs0 hsd F hzc
  have hle : ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x ≤ 0 := by
    rw [hE]; nlinarith
  have hge : 0 ≤ ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x :=
    integral_nonneg fun x => MFThermal.log_sub_mul_nonneg (hρp x) (hρp' x)
  have h0 : ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x = 0 := le_antisymm hle hge
  have hae : (fun x => (Real.log (ρ x) - Real.log (ρ' x)) * z x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => MFThermal.log_sub_mul_nonneg (hρp x) (hρp' x))
      (MFThermal.integrable_of_continuous hlogc)).mp h0
  have hall := (Continuous.ae_eq_iff_eq volume hlogc continuous_const).mp hae
  funext x
  have hx : (Real.log (ρ x) - Real.log (ρ' x)) * (ρ x - ρ' x) = 0 := congrFun hall x
  rcases mul_eq_zero.mp hx with hx | hx
  · have := Real.log_injOn_pos (Set.mem_Ioi.mpr (hρp x)) (Set.mem_Ioi.mpr (hρp' x))
      (sub_eq_zero.mp hx)
    exact this.symm
  · exact (sub_eq_zero.mp hx).symm


end ThermalUnique

end HRS.PDE.MFThermalExist
