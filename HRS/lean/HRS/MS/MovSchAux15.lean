import HRS.MS.MovSchAux14

/-!
# S64 (S6.9), part 10: `movFP` of a translate of `Qc`

Namespace `HRS.MS.MovSch`, prefix `s64_`.
* `s64_phi_hasDeriv`: along the line `ℓ_{ik}(Z,·)` through a non-collision `Z`, `φ = Qc ∘ ℓ` satisfies `φ' = -β drift φ` near `0`;
* `s64_movFP_Qc`: `movFP (Qc(· - a)) X = ∑_{i,k} (q a_k)(-β drift_{ik}(Z) Qc(Z))`, `Z = X - a`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

lemma s64_phi_hasDeriv (s q β : ℝ) {Z : EucConfig d N} (hZ : s64_NC Z) (i : Fin N) (k : Fin d) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt (fun σ : ℝ => s64_Qc d s q β N (s64_ell Z i k σ))
      (-β * s64_drift d s q N i k (s64_ell Z i k τ) * s64_Qc d s q β N (s64_ell Z i k τ)) τ := by
  filter_upwards [s64_NC_eventually hZ i k] with τ hτ
  set h : ℝ → ℝ := fun σ => HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) (s64_ell Z i k σ)
    with hh
  have hD0 : HasDerivAt (fun σ : ℝ => h (τ + σ)) (s64_drift d s q N i k (s64_ell Z i k τ)) 0 := by
    have := s64_H_hasDeriv s q hτ i k
    have e : (fun σ : ℝ => HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q)
        (s64_ell (s64_ell Z i k τ) i k σ)) = fun σ : ℝ => h (τ + σ) := by
      funext σ; simp only [hh, s64_ell_ell]
    rwa [e] at this
  have hD : HasDerivAt h (s64_drift d s q N i k (s64_ell Z i k τ)) τ := by
    have h1 : HasDerivAt (fun σ : ℝ => h (τ + σ)) (s64_drift d s q N i k (s64_ell Z i k τ))
        ((fun x : ℝ => x - τ) τ) := by
      simpa using hD0
    have hin : HasDerivAt (fun x : ℝ => x - τ) 1 τ := (hasDerivAt_id τ).sub_const τ
    have h2 := HasDerivAt.comp (h := fun x : ℝ => x - τ) τ h1 hin
    have e : ((fun σ : ℝ => h (τ + σ)) ∘ fun x : ℝ => x - τ) = h := by
      funext x; simp
    rw [e] at h2
    simpa using h2
  have h3 := ((hD.const_mul (-β)).exp).const_mul
    (HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β)⁻¹
  refine h3.congr_deriv ?_
  unfold s64_Qc
  simp only [hh]
  ring

theorem s64_movFP_Qc (s q β : ℝ) (hβ : β ≠ 0) (a : Euc d) {X : EucConfig d N}
    (hX : s64_NC (fun j => X j - a)) :
    movFP d s q β N (fun Y => s64_Qc d s q β N (fun j => Y j - a)) X =
      ∑ i, ∑ k, (q * a k) * (-β * s64_drift d s q N i k (fun j => X j - a) *
        s64_Qc d s q β N (fun j => X j - a)) := by
  rw [s64_movFP_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  set Z : EucConfig d N := fun j => X j - a with hZdef
  have hf : ∀ σ : ℝ, s64_Qc d s q β N (fun j => s64_ell X i k σ j - a) = s64_Qc d s q β N (s64_ell Z i k σ) := by
    intro σ
    congr 1
    funext j
    rw [s64_ell_shift X a i k σ]
    simp [hZdef]
  have hdr : ∀ τ : ℝ, s64_drift d s q N i k (s64_ell X i k τ) =
      s64_drift d s q N i k (s64_ell Z i k τ) + q * a k := by
    intro τ
    rw [s64_ell_shift X a i k τ, s64_drift_add]
  simp only [hf, hdr]
  have key := s64_1d hβ (φ := fun σ : ℝ => s64_Qc d s q β N (s64_ell Z i k σ))
    (Dr := fun τ : ℝ => s64_drift d s q N i k (s64_ell Z i k τ)) (q * a k)
    (s64_phi_hasDeriv s q β hX i k) (s64_Dr_diff s q hX i k)
  have h0 : HasDerivAt (fun σ : ℝ => s64_Qc d s q β N (s64_ell Z i k σ))
      (-β * s64_drift d s q N i k (s64_ell Z i k 0) * s64_Qc d s q β N (s64_ell Z i k 0)) 0 :=
    (s64_phi_hasDeriv s q β hX i k).self_of_nhds
  simp only [s64_ell_zero] at h0
  rw [key, h0.deriv]

end HRS.MS.MovSch

end
