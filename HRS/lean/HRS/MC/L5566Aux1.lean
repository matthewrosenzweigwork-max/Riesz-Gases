import HRS.Sections.Sec4

/-!
# Packet L5566, auxiliary 1: the shifted coefficient difference `b = a(· - e) - a`
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L5566

open HRS

variable {d : ℕ}

lemma l5566_coeff_neg (s c : ℝ) (k : Lattice d) :
    negSpectralCoeff d s c (-k) = negSpectralCoeff d s c k := by
  unfold negSpectralCoeff
  by_cases hk : k = 0
  · simp [hk]
  · have : -k ≠ 0 := neg_ne_zero.mpr hk
    simp [hk, this, enorm_neg]

lemma l5566_enorm_zero : Lattice.enorm (0 : Lattice d) = 0 := by
  have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  simp [Lattice.enorm, this]

lemma l5566_toEuc_sub (k l : Lattice d) :
    Lattice.toEuc (k - l) = Lattice.toEuc k - Lattice.toEuc l := by
  ext i; simp [Lattice.toEuc]

lemma l5566_enorm_single (i : Fin d) : Lattice.enorm (Pi.single i (1 : ℤ) : Lattice d) = 1 := by
  have : Lattice.toEuc (Pi.single i (1 : ℤ) : Lattice d) = EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp [Lattice.toEuc]
    · simp [Lattice.toEuc, Pi.single_apply, h]
  simp [Lattice.enorm, this]

lemma l5566_enorm_sub_le (k : Lattice d) (i : Fin d) :
    |Lattice.enorm (k - Pi.single i (1 : ℤ)) - Lattice.enorm k| ≤ 1 := by
  have h := abs_norm_sub_norm_le (Lattice.toEuc (k - Pi.single i (1 : ℤ))) (Lattice.toEuc k)
  have h2 : Lattice.toEuc (k - Pi.single i (1 : ℤ)) - Lattice.toEuc k =
      - Lattice.toEuc (Pi.single i (1 : ℤ) : Lattice d) := by
    rw [l5566_toEuc_sub]; abel
  rw [h2, norm_neg] at h
  have h3 : ‖Lattice.toEuc (Pi.single i (1 : ℤ) : Lattice d)‖ = 1 := l5566_enorm_single i
  unfold Lattice.enorm
  linarith

/-- mean value inequality for a negative power -/
lemma l5566_rpow_neg_diff {p : ℝ} (hp : p < 0) {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |x ^ p - y ^ p| ≤ |p| * m ^ (p - 1) * |x - y| := by
  have hdiff : ∀ t ∈ Set.Ici m, DifferentiableAt ℝ (fun t : ℝ => t ^ p) t := by
    intro t ht
    have : t ≠ 0 := (lt_of_lt_of_le hm ht).ne'
    exact Real.differentiableAt_rpow_const_of_ne p this
  have hb : ∀ t ∈ Set.Ici m, ‖deriv (fun t : ℝ => t ^ p) t‖ ≤ |p| * m ^ (p - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hm ht
    rw [Real.deriv_rpow_const t p, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm ht (by linarith : p - 1 ≤ 0))
      (abs_nonneg p)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun t : ℝ => t ^ p) (s := Set.Ici m)
    hdiff hb (convex_Ici m) hy hx
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

lemma l5566_b_bound {s c : ℝ} (hs : s < 0) (hc : 0 < c) (i : Fin d) (k : Lattice d)
    (hk : 2 ≤ Lattice.enorm k) :
    |negSpectralCoeff d s c (k - Pi.single i (1 : ℤ)) - negSpectralCoeff d s c k| *
        (2 * Real.pi * Lattice.enorm k) ≤
      (|s - d| * 2 ^ (1 - (s - d)) * (2 * Real.pi)) * negSpectralCoeff d s c k := by
  set p : ℝ := s - d with hpdef
  have hp : p < 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Lattice.enorm (0 : Lattice d) = 0 := l5566_enorm_zero
    linarith
  have hkl := l5566_enorm_sub_le k i
  have hk' : Lattice.enorm k / 2 ≤ Lattice.enorm (k - Pi.single i (1 : ℤ)) := by
    have := (abs_le.mp hkl).1
    linarith
  have hk1 : k - Pi.single i (1 : ℤ) ≠ 0 := by
    intro h
    rw [h] at hk'
    have : Lattice.enorm (0 : Lattice d) = 0 := l5566_enorm_zero
    linarith
  have hπ := Real.pi_pos
  set r : ℝ := 2 * Real.pi * Lattice.enorm k with hr
  set r' : ℝ := 2 * Real.pi * Lattice.enorm (k - Pi.single i (1 : ℤ)) with hr'
  have hr0 : 0 < r := by positivity
  have hrr' : r / 2 ≤ r' := by
    rw [hr, hr']; nlinarith
  have hrr : r / 2 ≤ r := by linarith
  have hdr : |r' - r| ≤ 2 * Real.pi := by
    rw [hr, hr']
    have : r' - r = 2 * Real.pi * (Lattice.enorm (k - Pi.single i (1 : ℤ)) - Lattice.enorm k) := by
      rw [hr, hr']; ring
    rw [← hr, ← hr', this, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith
  have ha : negSpectralCoeff d s c k = c * r ^ p := by
    unfold negSpectralCoeff; simp only [hk0, if_false]; rfl
  have ha' : negSpectralCoeff d s c (k - Pi.single i (1 : ℤ)) = c * r' ^ p := by
    unfold negSpectralCoeff; simp only [hk1, if_false]; rfl
  rw [ha, ha']
  have hmv := l5566_rpow_neg_diff hp (m := r / 2) (by positivity) hrr' hrr
  have hsub : |c * r' ^ p - c * r ^ p| = c * |r' ^ p - r ^ p| := by
    rw [← mul_sub, abs_mul, abs_of_pos hc]
  rw [hsub]
  have hhalf : (r / 2) ^ (p - 1) = 2 ^ (1 - p) * r ^ (p - 1) := by
    rw [Real.div_rpow hr0.le (by norm_num)]
    rw [show (2 : ℝ) ^ (p - 1) = (2 ^ (1 - p))⁻¹ by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring]
    field_simp
  have hrp : r * r ^ (p - 1) = r ^ p := by
    rw [Real.rpow_sub_one hr0.ne']; field_simp
  calc c * |r' ^ p - r ^ p| * r
      ≤ c * (|p| * (r / 2) ^ (p - 1) * |r' - r|) * r := by gcongr
    _ ≤ c * (|p| * (r / 2) ^ (p - 1) * (2 * Real.pi)) * r := by gcongr
    _ = (|p| * 2 ^ (1 - p) * (2 * Real.pi)) * (c * (r * r ^ (p - 1))) := by
        rw [hhalf]; ring
    _ = (|p| * 2 ^ (1 - p) * (2 * Real.pi)) * (c * r ^ p) := by rw [hrp]

end HRS.MC.L5566
