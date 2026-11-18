import HRS.MS.R26T8AP11f21

/-!
# S8.2 T8A P11f (part 22): off the diagonal, `∫ g(x-u) S(u,y) du - localRiesz S x y` equals the smooth model
Splitting `1 = θ1 + ψ0`, `chi = θ2 + ψ0` in the source variable `v = u - y`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem r26t8a_f22_D_eq {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d)
    {Q : Euc d → Euc d → ℝ} (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p | p.1 ≠ p.2})
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) {x y : Euc d} (hxy : x ≠ y)
    (hint : Integrable (fun u => ‖x - u‖ ^ (-((d : ℝ) / 2)) * r26t8a_divSource ρ Q u y)) :
    (∫ u, ‖x - u‖ ^ (-((d : ℝ) / 2)) * r26t8a_divSource ρ Q u y) -
        r26t8a_localRiesz ((d : ℝ) / 2) chi (r26t8a_divSource ρ Q) x y =
      r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) ρ Q (x, y) := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < (d : ℝ) / 2 := by linarith
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨hψ, hθ1, hθ2, hψ1, hψ0, hθ10, hθ20, -, -, -, -⟩ := r26t8a_f20_cutoffs hchi 0
  set z : Euc d := x - y with hz
  set e : ℝ := (d : ℝ) / 2 - d with he
  have hee : -((d : ℝ) / 2) = e := by rw [he]; ring
  set S : Euc d → Euc d → ℝ := r26t8a_divSource ρ Q with hS
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  -- `Stil = S` away from `v = 0`
  have hSS : ∀ v : Euc d, v ≠ 0 → r26t8a_Stil ρ Q (y + v) y = S (y + v) y := by
    intro v hv
    have hmem : (y + v, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
      show y + v ≠ y
      intro h; apply hv; simpa using h
    have hfd : ContDiffAt ℝ 2 (fun w : Euc d => Q w y) (y + v) := by
      have hg : ContDiff ℝ 2 (fun w : Euc d => (w, y)) := contDiff_id.prodMk contDiff_const
      have hm : Set.MapsTo (fun w : Euc d => (w, y)) {w : Euc d | w ≠ y} {p : Euc d × Euc d | p.1 ≠ p.2} :=
        fun w hw => hw
      have := (hQ.comp hg.contDiffOn hm)
      exact this.contDiffAt (isOpen_ne.mem_nhds (by simpa using hmem))
    exact (r26t8a_f9_divSource_eq (ρ := ρ) hfd).symm
  have hae : ∀ᵐ v : Euc d ∂volume, v ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  -- the integrable fibre function
  set F : Euc d → ℝ := fun v => ‖z - v‖ ^ e * S (y + v) y with hF
  have hFint : Integrable F := by
    have := hint.comp_add_left y
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [hF, hz, hee, sub_sub]
  have hψc : Continuous (r26t8a_f20_psi chi) := (hψ.continuous)
  have hwint : ∀ θ : Euc d → ℝ, Continuous θ → (∀ v, |θ v| ≤ 1) → Integrable (fun v => θ v * F v) := by
    intro θ hθc hθb
    refine Integrable.mono' hFint.norm (hθc.aestronglyMeasurable.mul hFint.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    calc ‖θ v‖ * ‖F v‖ ≤ 1 * ‖F v‖ :=
          mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hθb v) (norm_nonneg _)
      _ = ‖F v‖ := one_mul _
  have hch01 : ∀ v : Euc d, 0 ≤ chi v ∧ chi v ≤ 1 := fun v => hchi.2.2.1 v
  have hchiabs : ∀ v : Euc d, |chi v| ≤ 1 := fun v => by
    rw [abs_le]; constructor <;> linarith [(hch01 v).1, (hch01 v).2]
  have hth1abs : ∀ v : Euc d, |r26t8a_f20_th1 chi v| ≤ 1 := fun v => by
    have := hch01 ((4 : ℝ) • v)
    simp only [r26t8a_f20_th1]
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hth2abs : ∀ v : Euc d, |r26t8a_f20_th2 chi v| ≤ 1 := fun v => by
    have h1 := hch01 ((4 : ℝ) • v)
    have h2 := hch01 v
    simp only [r26t8a_f20_th2]
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have id1 : ∀ v : Euc d, r26t8a_f20_th1 chi v + r26t8a_f20_psi chi v = 1 := fun v => by
    simp [r26t8a_f20_th1, r26t8a_f20_psi]
  have id2 : ∀ v : Euc d, r26t8a_f20_th2 chi v + r26t8a_f20_psi chi v = chi v := by
    intro v
    simp only [r26t8a_f20_th2, r26t8a_f20_psi]
    by_cases hv : ‖v‖ ≤ 1 / 2
    · have h1 : chi v = 1 := hchi.2.2.2.1 v (by linarith)
      rw [h1]; ring
    · have h4 : chi ((4 : ℝ) • v) = 0 := hchi.2.2.2.2 _ (by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith [not_le.1 hv])
      rw [h4]; ring
  -- the three weighted integrals
  have hI1 : ∫ v, F v = (∫ v, r26t8a_f20_th1 chi v * F v) + ∫ v, r26t8a_f20_psi chi v * F v := by
    rw [← integral_add (hwint _ hθ1.continuous hth1abs) (hwint _ hψc hψ1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show F v = r26t8a_f20_th1 chi v * F v + r26t8a_f20_psi chi v * F v
    rw [← add_mul, id1, one_mul]
  have hIchi : ∫ v, chi v * F v = (∫ v, r26t8a_f20_th2 chi v * F v) + ∫ v, r26t8a_f20_psi chi v * F v := by
    rw [← integral_add (hwint _ hθ2.continuous hth2abs) (hwint _ hψc hψ1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show chi v * F v = r26t8a_f20_th2 chi v * F v + r26t8a_f20_psi chi v * F v
    rw [← add_mul, id2]
  -- identification of the potentials
  have hPot : ∀ θ : Euc d → ℝ, r26t8a_f20_Pot θ ((d : ℝ) / 2) ρ Q (x, y) = ∫ v, θ v * F v := by
    intro θ
    unfold r26t8a_f20_Pot
    have hsub := integral_sub_left_eq_self
      (fun w : Euc d => ‖w‖ ^ (-((d : ℝ) / 2)) * (θ (x - w - y) * r26t8a_Stil ρ Q (x - w) y)) volume z
    refine Eq.trans hsub.symm ?_
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    have e1 : x - (z - v) = y + v := by rw [hz]; abel
    have e2 : x - (z - v) - y = v := by rw [e1]; abel
    simp only [hF, e1, add_sub_cancel_left, hSS v hv, hee]
    ring
  -- the singular-source potential with the smooth kernel
  have hT2 : (1 - chi z) * (∫ v, r26t8a_f5_G (r26t8a_Kc ((d : ℝ) / 2) chi (1 / 2 : ℝ)) (r26t8a_f20_psi chi)
      (fun v y => r26t8a_Stil ρ Q (y + v) y) v (x, y)) = (1 - chi z) * ∫ v, r26t8a_f20_psi chi v * F v := by
    by_cases hz1 : ‖z‖ ≤ 1
    · have : chi z = 1 := hchi.2.2.2.1 z hz1
      rw [this]; ring
    · congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with v hv
      unfold r26t8a_f5_G
      by_cases hψv : r26t8a_f20_psi chi v = 0
      · simp [hψv]
      · have hv2 : ‖v‖ ≤ 1 / 2 := by
          by_contra h; exact hψv (hψ0 v (not_le.1 h))
        have hzv : ‖z‖ - ‖v‖ ≤ ‖z - v‖ := by
          have := norm_sub_norm_le z v
          linarith [norm_sub_rev z v, norm_sub_norm_le z v]
        have hz2 : (1 / 2 : ℝ) / 2 ≤ ‖x - y - v‖ := by
          have : x - y - v = z - v := rfl
          rw [this]; linarith [not_le.1 hz1]
        have hK := r26t8a_Kc_eq d ((d : ℝ) / 2) chi hchi (δ := (1 / 2 : ℝ)) (by norm_num)
          (u := x - y - v) hz2
        show r26t8a_Kc ((d : ℝ) / 2) chi (1 / 2 : ℝ) (x - y - v) *
          (r26t8a_f20_psi chi v * r26t8a_Stil ρ Q (y + v) y) = r26t8a_f20_psi chi v * F v
        rw [hK, hSS v hv]
        simp only [hF]
        have : x - y - v = z - v := rfl
        rw [this, he]
        ring
  have hlhs1 : (∫ u, ‖x - u‖ ^ (-((d : ℝ) / 2)) * r26t8a_divSource ρ Q u y) = ∫ v, F v := by
    have := integral_add_left_eq_self (fun u : Euc d => ‖x - u‖ ^ (-((d : ℝ) / 2)) * S u y) (μ := volume) y
    refine Eq.trans this.symm ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hF, hz, hee, sub_sub]
  have hloc : r26t8a_localRiesz ((d : ℝ) / 2) chi (r26t8a_divSource ρ Q) x y = chi z * ∫ v, chi v * F v := by
    unfold r26t8a_localRiesz
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hF, hz, he]
    ring
  have hmodel : r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) ρ Q (x, y) =
      (r26t8a_f20_Pot (r26t8a_f20_th1 chi) ((d : ℝ) / 2) ρ Q (x, y) -
        chi z * r26t8a_f20_Pot (r26t8a_f20_th2 chi) ((d : ℝ) / 2) ρ Q (x, y)) +
      (1 - chi z) * ∫ v, r26t8a_f5_G (r26t8a_Kc ((d : ℝ) / 2) chi (1 / 2 : ℝ)) (r26t8a_f20_psi chi)
        (fun v y => r26t8a_Stil ρ Q (y + v) y) v (x, y) := rfl
  rw [hmodel, hlhs1, hloc, hI1, hIchi, hPot, hPot, hT2]
  ring

end HRS.MS.R26T8A
