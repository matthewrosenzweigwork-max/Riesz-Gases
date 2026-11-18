import HRS.MS.R26T8AP29g

/-!
# S8.2 T8A P29 (part h): logarithmic power absorption
`1 + (1 + |log r|)^2 ≤ 10 (1 + r^(-s))` for `0 < r ≤ 1`, `1 ≤ s`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace HRS.MS.R26T8A

theorem r26t8a_p29_logsq (s : ℝ) (hs : 1 ≤ s) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    1 + (1 + |Real.log r|) ^ 2 ≤ 10 * (1 + r ^ (-s)) := by
  set u : ℝ := r⁻¹ with hu
  have hu1 : 1 ≤ u := one_le_inv_iff₀.2 ⟨hr0, hr1⟩
  have hu0 : 0 < u := by linarith
  have hlog : |Real.log r| = Real.log u := by
    rw [hu, Real.log_inv]
    exact abs_of_nonpos (Real.log_nonpos hr0.le hr1)
  have hs2 : 0 < s / 2 := by linarith
  have h1 : Real.log u ≤ u ^ (s / 2) / (s / 2) := Real.log_le_rpow_div hu0.le hs2
  have hp1 : 1 ≤ u ^ (s / 2) := Real.one_le_rpow hu1 hs2.le
  have h2 : u ^ (s / 2) / (s / 2) ≤ 2 * u ^ (s / 2) := by
    rw [div_le_iff₀ hs2]
    nlinarith
  have h3 : 1 + |Real.log r| ≤ 3 * u ^ (s / 2) := by rw [hlog]; linarith
  have h4 : (1 + |Real.log r|) ^ 2 ≤ 9 * (u ^ (s / 2)) ^ 2 := by
    have : 0 ≤ 1 + |Real.log r| := by positivity
    nlinarith
  have h5 : (u ^ (s / 2)) ^ 2 = r ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le, hu, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
    congr 1
    push_cast; ring
  have h6 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0.le _
  rw [h5] at h4
  linarith

end HRS.MS.R26T8A

end
