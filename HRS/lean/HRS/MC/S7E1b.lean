import HRS.MC.Sec7Vocab
import HRS.Equilibrium.Q84aAuxB
import HRS.Equilibrium.Q84dAuxV
import HRS.Equilibrium.LocalDivMain

/-!
# Packet `s7_E1b_cutoff_kernel_admissible`: the pair kernels are admissible chaos kernels

For `0 <= s < d`: `hTransport d s phi` is measurable and symmetric (`grad g` odd), `hCut d s phi eps`
(`eps > 0`) is moreover bounded (`|grad g(z)| <= C (|z|^{-s-1} + 1)` off the `eps`-ball), hence in
`L^2(mu x mu)`; for `s < d/2` the full kernel is in `L^2` by `localDiv_subcritical`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E1b

open HRS HRS.Sec7 HRS.LocalDivAux

variable {d : ℕ}

theorem e1b_meas_transport {s : ℝ} (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (Function.uncurry (hTransport d s φ)) := by
  have e : Function.uncurry (hTransport d s φ) = fun p : Torus d × Torus d =>
      ∑ i, (Torus.partialDeriv i φ p.1 - Torus.partialDeriv i φ p.2) *
        (periodicRieszGrad d s (p.1 - p.2)).ofLp i := by
    funext p; exact hTransport_eq s φ hφ p.1 p.2
  rw [e]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hc : Continuous (Torus.partialDeriv i φ) :=
    StaticLimitAux.continuous_of_smooth (isSmooth_partialDeriv hφ i)
  refine ((hc.measurable.comp measurable_fst).sub (hc.measurable.comp measurable_snd)).mul ?_
  exact (EuclideanSpace.proj i).continuous.measurable.comp
    ((KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd))

theorem e1b_bound_transport {s : ℝ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : Torus d,
      |hTransport d s φ x y| ≤ M * ‖periodicRieszGrad d s (x - y)‖ := by
  have hb : ∀ i : Fin d, ∃ Mi : ℝ, ∀ x, |Torus.partialDeriv i φ x| ≤ Mi := fun i => by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
      (StaticLimitAux.continuous_of_smooth (isSmooth_partialDeriv hφ i)).continuousOn
    exact ⟨M, fun x => by simpa using hM x (Set.mem_univ x)⟩
  choose Mi hMi using hb
  set M0 : ℝ := ∑ i, |Mi i| with hM0
  have hM : ∀ i x, |Torus.partialDeriv i φ x| ≤ M0 := fun i x =>
    (hMi i x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Mi i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨d * (2 * M0), by positivity, fun x y => ?_⟩
  rw [hTransport_eq s φ hφ]
  have hterm : ∀ i : Fin d, |(Torus.partialDeriv i φ x - Torus.partialDeriv i φ y) *
      (periodicRieszGrad d s (x - y)).ofLp i| ≤ 2 * M0 * ‖periodicRieszGrad d s (x - y)‖ := by
    intro i
    rw [abs_mul]
    have h1 : |Torus.partialDeriv i φ x - Torus.partialDeriv i φ y| ≤ 2 * M0 := by
      calc _ ≤ |Torus.partialDeriv i φ x| + |Torus.partialDeriv i φ y| := abs_sub _ _
        _ ≤ M0 + M0 := add_le_add (hM i x) (hM i y)
        _ = 2 * M0 := by ring
    have h2 : |(periodicRieszGrad d s (x - y)).ofLp i| ≤ ‖periodicRieszGrad d s (x - y)‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (periodicRieszGrad d s (x - y)) i
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  calc _ ≤ ∑ i : Fin d, |(Torus.partialDeriv i φ x - Torus.partialDeriv i φ y) *
        (periodicRieszGrad d s (x - y)).ofLp i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 2 * M0 * ‖periodicRieszGrad d s (x - y)‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp; ring

theorem e1b_meas_cut {s : ℝ} (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (ε : ℝ) :
    Measurable (Function.uncurry (hCut d s φ ε)) := by
  have e : Function.uncurry (hCut d s φ ε) = fun p : Torus d × Torus d =>
      if ε < Torus.eucDist p.1 p.2 then Function.uncurry (hTransport d s φ) p else 0 := by
    funext p; rfl
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const (Q84d.q84d_measurable_eucDist_prod d))
    (e1b_meas_transport hsd hφ) measurable_const

theorem e1b_symm_cut {s : ℝ} (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (ε : ℝ)
    (x y : Torus d) : hCut d s φ ε x y = hCut d s φ ε y x := by
  unfold hCut
  rw [eucDist_symm, hTransport_symm hsd hφ]

theorem e1b_bound_cut (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ x y : Torus d, |hCut d s φ ε x y| ≤ B := by
  obtain ⟨M, hM0, hM⟩ := e1b_bound_transport (s := s) hφ
  obtain ⟨Cg, hCg0, hCg⟩ := Q84a.q84a_gg_bound hd hs0 hsd
  refine ⟨M * (Cg * (ε ^ (-s - 1) + 1)), fun x y => ?_⟩
  have hnn : 0 ≤ M * (Cg * (ε ^ (-s - 1) + 1)) := by
    have := Real.rpow_nonneg hε.le (-s - 1)
    positivity
  unfold hCut
  split_ifs with h
  · have hxy : x - y ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      subst h0
      have : Torus.eucDist x x = 0 := by simp [Torus.eucDist]
      linarith
    have h1 := hCg (x - y) hxy
    have h2 : Torus.eucDist (x - y) 0 ^ (-s - 1) ≤ ε ^ (-s - 1) := by
      rw [← PairCorrAux.eucDist_sub_zero]
      exact Real.rpow_le_rpow_of_nonpos hε h.le (by linarith)
    calc |hTransport d s φ x y| ≤ M * ‖periodicRieszGrad d s (x - y)‖ := hM x y
      _ ≤ M * (Cg * (ε ^ (-s - 1) + 1)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hM0
        exact mul_le_mul_of_nonneg_left (by linarith) hCg0
  · simpa using hnn

theorem e1b_memLp_cut (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {ε : ℝ} (hε : 0 < ε) :
    MemLp (Function.uncurry (hCut d s φ ε)) 2 ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  haveI := isProb_withDensityReal hρ.density
  obtain ⟨B, hB⟩ := e1b_bound_cut hd hs0 hsd hφ hε
  refine MemLp.of_bound (e1b_meas_cut hsd hφ ε).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun p => ?_)
  show ‖hCut d s φ ε p.1 p.2‖ ≤ B
  rw [Real.norm_eq_abs]; exact hB p.1 p.2

/-! ### The packet -/

theorem s7_E1b_cutoff_kernel_admissible_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    (∀ ε : ℝ, 0 < ε →
      Measurable (Function.uncurry (hCut d s φ ε)) ∧ (∀ x y, hCut d s φ ε x y = hCut d s φ ε y x) ∧
        MemLp (Function.uncurry (hCut d s φ ε)) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) ∧
    (Measurable (Function.uncurry (hTransport d s φ)) ∧
      ∀ x y, hTransport d s φ x y = hTransport d s φ y x) ∧
    (s < (d : ℝ) / 2 →
      MemLp (Function.uncurry (hTransport d s φ)) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) := by
  refine ⟨fun ε hε => ⟨e1b_meas_cut hsd hφ ε, e1b_symm_cut hsd hφ ε, e1b_memLp_cut hd hs0 hsd hρ hφ hε⟩,
    ⟨e1b_meas_transport hsd hφ, hTransport_symm hsd hφ⟩, fun hs => ?_⟩
  exact (localDiv_subcritical hd hs0 hs ρ hρ φ hφ).1

end HRS.MC.Sec7.E1b
