import HRS.MS.UniqC1

/-!
# Packet C1, part 2: componentwise bounds of the mean-field drift at a fixed time

For `ρ` in the decay class `RgDecay (m+3)`, each component of `meanFieldDriftW D ρ` is `C^{m+1}`, its
derivatives of order `1..m+1` are bounded by `Kc + ΛV` and it grows at most like `(Kc+G₀+ΛV)(1+|x|)`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqC1
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen

variable {d : ℕ}

/-- The constant bounding the derivatives of the convolution part. -/
def c1Kc (d : ℕ) (s MB A : ℝ) : ℝ :=
  d * MB * (movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d))

/-- Bounded derivatives of the components of `∇V`: order `n ≥ 1` is bounded by `ΛV`. -/
theorem c1_gradV_deriv {k : ℕ} {ΛV G₀ : ℝ} {V : Euc d → ℝ} (hV : VHypRd (k + 1) ΛV G₀ V)
    (j : Fin d) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (fun x => gradient V x j) x‖ ≤ ΛV := by
  have e : (fun x => gradient V x j) = fun x => fderiv ℝ V x (EuclideanSpace.single j (1 : ℝ)) := by
    funext x; exact movtr_gradient_apply V x j
  have hVk : ContDiff ℝ (k + 1) V := hV.1.of_le (by exact_mod_cast le_top)
  rw [e]
  have := rg_diruv (n := n) (φ := V) (hVk.of_le (by exact_mod_cast Nat.succ_le_succ hnk))
    (EuclideanSpace.single j 1) x
  rw [rg_norm_single, one_mul] at this
  exact this.trans (hV.2.1 (n + 1) (by omega) (by omega) x)

/-- Componentwise bounds of the mean-field drift. -/
theorem c1_comp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ}
    {A MB ΛV G₀ : ℝ} (hA : 0 ≤ A) {D : WholeDyn d} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 1 + 1) ΛV G₀ D.V)
    {ρ : Euc d → ℝ} (hρ : RgDecay (m + 1 + 2) (fun _ => A) ρ) (j : Fin d) :
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => meanFieldDriftW D ρ x j) ∧
    (∀ n : ℕ, 1 ≤ n → n ≤ m + 1 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun x => meanFieldDriftW D ρ x j) x‖ ≤ c1Kc d s MB A + ΛV) ∧
    (∀ x, ‖meanFieldDriftW D ρ x j‖ ≤ (c1Kc d s MB A + (G₀ + ΛV)) * (1 + ‖x‖)) := by
  have hdr := rg_drift hd hs0 hsd (k := m + 1) (by omega) hA hDs hMB hV hρ j
  refine ⟨hdr.1, fun n hn1 hnm x => ?_, fun x => ?_⟩
  · have hfun : (fun x => meanFieldDriftW D ρ x j) = fun x =>
        (∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d s) ρ x) i) - gradient D.V x j := by
      funext x
      unfold meanFieldDriftW
      rw [PiLp.sub_apply, HRS.Whole.Q09B.q09b_matVec_apply, hDs]
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        RgW (fun _ => (1 : ℝ)) (m + 1)
          (|D.M j i| * (movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d)))
          (fun x => D.M j i * (convGradConvW (rieszKernelGrad d s) ρ x) i) := fun i _ =>
      RgW.const_mul _ (rg_conv_comp hd hs0 hsd hA hρ i)
    have hs := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := m + 1) Finset.univ hterm
    have hK : 0 ≤ movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d) :=
      mul_nonneg (rg_sigma_nonneg hs0)
        (add_nonneg (mul_nonneg hA (rg_near_nonneg s))
          (mul_nonneg (mul_nonneg (by positivity) hA) rg_W_nonneg))
    have hs' := hs.mono (fun x => zero_le_one) (c' := c1Kc d s MB A) (by
      unfold c1Kc
      calc ∑ i : Fin d, |D.M j i| * (movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d))
          ≤ ∑ i : Fin d, MB * (movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d)) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hMB j i) hK
        _ = _ := by simp [Finset.sum_const]; ring)
    have hgV : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => gradient D.V x j) :=
      (rg_gradV (k := m + 1) (by omega) hV j).1
    have hn' : (n : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hnm
    rw [hfun]
    change ‖iteratedFDeriv ℝ n ((fun x => ∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d s) ρ x) i) -
      (fun x => gradient D.V x j)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hs'.1.of_le hn').contDiffAt (hgV.of_le hn').contDiffAt]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · simpa using hs'.2 n hnm x
    · exact c1_gradV_deriv (k := m + 1) hV j hn1 hnm x
  · have := hdr.2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this

end HRS.MS.UniqC1
