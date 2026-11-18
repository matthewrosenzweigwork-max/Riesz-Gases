import HRS.Commutator.Torus.NRSTAux28

/-!
# NRS-T, part 29: the `ℝ^d` Riesz bound applied to the cut-off lifts
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_exists_Rs (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (W : SchwartzMap 𝔼 ℂ) :
    ∃ Rs : SchwartzMap 𝔼 ℂ, (∀ ξ, 𝓕 (⇑Rs) ξ = θ ξ * 𝓕 (⇑W) ξ) ∧ ∀ x, Rs x = nrstg_T θ W x := by
  set g : SchwartzMap 𝔼 ℂ := SchwartzMap.smulLeftCLM ℂ θ (𝓕 W) with hg
  refine ⟨𝓕⁻ g, fun ξ => ?_, fun x => ?_⟩
  · have h : (𝓕 (𝓕⁻ g : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ) = g := FourierTransform.fourier_fourierInv_eq _
    have h2 : 𝓕 (⇑(𝓕⁻ g : SchwartzMap 𝔼 ℂ)) = ⇑g := by
      rw [← SchwartzMap.fourier_coe]
      exact congrArg (fun f : SchwartzMap 𝔼 ℂ => (⇑f : 𝔼 → ℂ)) h
    rw [h2, hg, SchwartzMap.smulLeftCLM_apply_apply hθ, smul_eq_mul]
    rfl
  · unfold nrstg_T
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul]
    rw [leibt_e_comm x ξ, hg, SchwartzMap.smulLeftCLM_apply_apply hθ, smul_eq_mul]
    rfl

lemma nrstr_one_le_enorm {k : Lattice d} (hk : k ≠ 0) : 1 ≤ ‖Lattice.toEuc k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : |((k i : ℤ) : ℝ)| ≤ ‖Lattice.toEuc k‖ := by
    have := PiLp.norm_apply_le (Lattice.toEuc k) i
    simpa [Lattice.toEuc, Real.norm_eq_abs] using this
  have h2 : (1 : ℝ) ≤ |((k i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    have := (Int.cast_le (R := ℝ)).2 this
    simpa [Int.cast_abs] using this
  linarith

lemma nrstr_Rd_bound (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (a : Fin d) :
    ∃ Cx : ℝ≥0∞, Cx ≠ ⊤ ∧ ∀ (f : NRST.TPA d) (R : ℝ), 1 ≤ R →
      (∀ k ∈ f.coeff.support, k ≠ 0 ∧ ‖Lattice.toEuc k‖ + 1 / 8 ≤ R) →
      ∃ θ : 𝔼 → ℂ, θ.HasTemperateGrowth ∧
        (∀ k ∈ f.coeff.support, θ (Lattice.toEuc k) = HRS.Commutator.Whole.XBB.xbbRm a (Lattice.toEuc k)) ∧
        ∀ (N : ℝ) (hN : 1 ≤ N), ∃ Rs : SchwartzMap 𝔼 ℂ, (∀ x, Rs x = nrstg_T θ (nrstr_W f N (by linarith)) x) ∧
          eLpNorm (⇑Rs) (ENNReal.ofReal p) volume ≤
            Cx * eLpNorm (⇑(nrstr_W f N (by linarith))) (ENNReal.ofReal p) volume := by
  obtain ⟨Cx, hCx, hRiesz⟩ := HRS.Commutator.Whole.XBB.xbb_riesz hd hp a
  refine ⟨Cx, hCx, fun f R hR1 hf => ?_⟩
  obtain ⟨θ, hθ, hθR⟩ := nrstr_theta_exists hd a hR1
  refine ⟨θ, hθ, fun k hk => ?_, fun N hN => ?_⟩
  · obtain ⟨hk0, hkR⟩ := hf k hk
    exact hθR _ (by linarith [nrstr_one_le_enorm hk0]) (by linarith)
  · have hN0 : 0 < N := by linarith
    obtain ⟨Rs, hFR, hval⟩ := nrstr_exists_Rs θ hθ (nrstr_W f N hN0)
    refine ⟨Rs, hval, ?_⟩
    have hFW : ∀ ξ : 𝔼, (‖ξ‖ < 1 / 2 ∨ R < ‖ξ‖) → 𝓕 (⇑(nrstr_W f N hN0)) ξ = 0 := by
      intro ξ hξ
      refine nrstr_fourierW_zero f hN ξ fun k hk => ?_
      obtain ⟨hk0, hkR⟩ := hf k hk
      have h1 := nrstr_one_le_enorm hk0
      rcases hξ with h | h
      · have : ‖Lattice.toEuc k‖ - ‖ξ‖ ≤ ‖ξ - Lattice.toEuc k‖ := by
          rw [norm_sub_rev]; exact norm_sub_norm_le _ _ |>.trans_eq (by rw [norm_sub_rev]) |>.trans (le_refl _)
        linarith
      · have : ‖ξ‖ - ‖Lattice.toEuc k‖ ≤ ‖ξ - Lattice.toEuc k‖ := norm_sub_norm_le _ _
        linarith
    refine hRiesz (nrstr_W f N hN0) Rs (1 / 2) R (by norm_num) hFW fun ξ => ?_
    by_cases hξ : ‖ξ‖ < 1 / 2 ∨ R < ‖ξ‖
    · rw [hFW ξ hξ, hFR ξ, hFW ξ hξ]; simp
    · push Not at hξ
      rw [hFR ξ, hθR ξ hξ.1 hξ.2]

end HRS.Commutator.TorusNote
