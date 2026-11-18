import HRS.MS.CritForceLead1

/-!
# S8.2 NormalForm packet P05, part 2: the leading inverse (Laplacian identity)

`s82n_leadingInverse` is the Pro definition `leadingInverse` with `criticalS d = d/2` written out.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S82N

open HRS

variable {d : ℕ}

/-- `s = d/2`. -/
def s82n_critS (d : ℕ) : ℝ := (d : ℝ) / 2

/-- Exact leading inverse (degree-zero and degree-two parts). -/
def s82n_leadingInverse {d : ℕ} (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)
    (z : Euc d) : ℝ :=
  let s := s82n_critS d
  let h0 := (∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) / d
  let omega := ‖z‖⁻¹ • z
  let h2 := B omega omega - h0
  (if d = 4 then h0 * Real.log ‖z‖ / (4 * nu) else h0 * ‖z‖ ^ (2 - s) / (4 * nu * (2 - s))) -
    h2 * ‖z‖ ^ (2 - s) / (4 * nu * (s + 2))

lemma s82n_laplacian_radial0 (w : Euc d) (g g' g'' : ℝ → ℝ)
    (h1 : ∀ᶠ t in 𝓝 (‖w‖ ^ 2), HasDerivAt g (g' t) t)
    (h2 : HasDerivAt g' (g'' (‖w‖ ^ 2)) (‖w‖ ^ 2)) :
    Laplacian.laplacian (fun x : Euc d => g (‖x‖ ^ 2)) w =
      2 * d * g' (‖w‖ ^ 2) + 4 * ‖w‖ ^ 2 * g'' (‖w‖ ^ 2) := by
  have := HRS.Parx.laplacian_radial 0 w g g' g'' (by simpa using h1) (by simpa using h2)
  simpa using this

lemma s82n_rpow_deriv_data (a t : ℝ) (ht : 0 < t) :
    (∀ᶠ u in 𝓝 t, HasDerivAt (fun v : ℝ => v ^ a) (a * u ^ (a - 1)) u) ∧
      HasDerivAt (fun u : ℝ => a * u ^ (a - 1)) (a * (a - 1) * t ^ (a - 1 - 1)) t := by
  refine ⟨?_, ?_⟩
  · filter_upwards [Ioi_mem_nhds ht] with u hu
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hu))
  · have := (Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl ht.ne')).const_mul a
    simpa [mul_assoc] using this

lemma s82n_lap_rpow (w : Euc d) (hw : w ≠ 0) (a : ℝ) :
    Laplacian.laplacian (fun x : Euc d => (‖x‖ ^ 2) ^ a) w =
      (2 * d * a + 4 * a * (a - 1)) * (‖w‖ ^ 2) ^ (a - 1) := by
  have ht : 0 < ‖w‖ ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := s82n_rpow_deriv_data a _ ht
  rw [s82n_laplacian_radial0 w (fun v => v ^ a) (fun u => a * u ^ (a - 1))
    (fun u => a * (a - 1) * u ^ (a - 1 - 1)) h1 h2]
  have e : (‖w‖ ^ 2) ^ (a - 1 - 1) = (‖w‖ ^ 2) ^ (a - 1) / ‖w‖ ^ 2 := Real.rpow_sub_one ht.ne' _
  rw [e]
  field_simp

lemma s82n_lap_log (w : Euc d) (hw : w ≠ 0) :
    Laplacian.laplacian (fun x : Euc d => Real.log (‖x‖ ^ 2)) w = (2 * d - 4) / ‖w‖ ^ 2 := by
  have ht : 0 < ‖w‖ ^ 2 := by positivity
  have h1 : ∀ᶠ u in 𝓝 (‖w‖ ^ 2), HasDerivAt Real.log (u⁻¹) u := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact Real.hasDerivAt_log (ne_of_gt hu)
  have h2 : HasDerivAt (fun u : ℝ => u⁻¹) (-((‖w‖ ^ 2) ^ 2)⁻¹) (‖w‖ ^ 2) := by
    simpa using hasDerivAt_inv ht.ne'
  rw [s82n_laplacian_radial0 w Real.log (fun u => u⁻¹) (fun u => -(u ^ 2)⁻¹) h1 h2]
  field_simp
  ring

lemma s82n_lap_quad_rpow (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (w : Euc d) (hw : w ≠ 0) (a : ℝ) :
    Laplacian.laplacian (fun x : Euc d => B x x * (‖x‖ ^ 2) ^ a) w =
      B w w * (8 * a + 4 * a * (a - 1) + 2 * d * a) * (‖w‖ ^ 2) ^ (a - 1) +
        2 * (∑ i, B (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i)) *
          (‖w‖ ^ 2) ^ a := by
  have ht : 0 < ‖w‖ ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := s82n_rpow_deriv_data a _ ht
  rw [s82n_laplacian_quad_radial B hB w (fun v => v ^ a) (fun u => a * u ^ (a - 1))
    (fun u => a * (a - 1) * u ^ (a - 1 - 1)) h1 h2]
  have e : (‖w‖ ^ 2) ^ (a - 1 - 1) = (‖w‖ ^ 2) ^ (a - 1) / ‖w‖ ^ 2 := Real.rpow_sub_one ht.ne' _
  rw [e]
  field_simp

end HRS.MS.S82N
