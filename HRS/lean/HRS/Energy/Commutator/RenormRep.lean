import HRS.Energy.Commutator.RoughLimit
import HRS.Energy.Commutator.RenormAlg

/-!
# Route S, packet S4: Newton's theorem for the force (differentiation of the potential of a charge)

If `∫ G(z - x) dσ(x) = G(z - a) + κ` for `z` outside the ball `B̄(a,η)` and `σ` is carried by that ball, then
`∫ w(y - x) dσ(x) = w(y - a)` for `y` outside the ball, where `w = ∇G`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- The unit coordinate vector. -/
abbrev ev (j : Fin d) : Euc d := EuclideanSpace.single j (1 : ℝ)

theorem mk_line (y : Euc d) (j : Fin d) (s : ℝ) :
    Torus.mk (y + s • ev j) = Torus.mk y + Torus.mk (s • ev j) := KernelGrad.mk_add _ _

theorem tdist_line_a {a y : Torus d} {y0 : Euc d} (hy0 : Torus.mk y0 = y) (j : Fin d) (t : ℝ) :
    KernelGrad.tdist y a - |t| ≤ KernelGrad.tdist (Torus.mk (y0 + t • ev j)) a := by
  set z : Torus d := Torus.mk (y0 + t • ev j) with hz
  have h1 : KernelGrad.tdist (Torus.mk (t • ev j)) 0 ≤ |t| := by
    refine (EnergyAux.tdist_mk_le _).trans ?_
    rw [norm_smul]
    simp
  have := EnergyAux.tdist_add_ge (y - a) (Torus.mk (t • ev j))
  have e : Torus.mk (t • ev j) + (y - a) = z - a := by
    rw [hz, mk_line, hy0]; abel
  rw [e, ← EnergyAux.tdist_def z a] at this
  rw [EnergyAux.tdist_def y a]
  linarith

theorem tdist_line_ge {a y : Torus d} {η : ℝ} {y0 : Euc d} (hy0 : Torus.mk y0 = y) (j : Fin d) {δ : ℝ}
    (hδ : δ = KernelGrad.tdist y a - η) (t : ℝ) (ht : |t| < δ / 2) (x : Torus d)
    (hx : KernelGrad.tdist x a ≤ η) :
    δ / 2 ≤ KernelGrad.tdist (Torus.mk (y0 + t • ev j) - x) 0 := by
  set z : Torus d := Torus.mk (y0 + t • ev j) with hz
  have h2 := tdist_line_a (a := a) hy0 j t
  have h3 := tdist_ge_of_near (y := z) hx
  rw [tdist_symm' x z, EnergyAux.tdist_def z x] at h3
  rw [← hz] at h2
  linarith

theorem repro_of_newton {G : Torus d → ℝ} {w : Torus d → Euc d}
    (hGm : Measurable G) (hwm : Measurable w)
    (hG : ∀ y : Euc d, Torus.mk y ≠ 0 → HasFDerivAt (Torus.lift G)
        (∑ j, w (Torus.mk y) j • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) y)
    (hGbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z : Torus d, δ ≤ KernelGrad.tdist z 0 → |G z| ≤ B)
    (hwbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z : Torus d, δ ≤ KernelGrad.tdist z 0 → ‖w z‖ ≤ B)
    {σ : Measure (Torus d)} [IsFiniteMeasure σ] {a : Torus d} {η κ : ℝ} (hη : 0 ≤ η)
    (hsupp : ∀ᵐ x ∂σ, KernelGrad.tdist x a ≤ η)
    (hnewton : ∀ z : Torus d, η < KernelGrad.tdist z a → ∫ x, G (z - x) ∂σ = G (z - a) + κ)
    {y : Torus d} (hy : η < KernelGrad.tdist y a) :
    ∫ x, w (y - x) ∂σ = w (y - a) := by
  set δ := KernelGrad.tdist y a - η with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨y0, hy0⟩ := (⟨Torus.rep y, Torus.mk_rep y⟩ : ∃ y0 : Euc d, Torus.mk y0 = y)
  obtain ⟨BG, hBG⟩ := hGbdd (δ / 2) (by positivity)
  obtain ⟨Bw, hBw⟩ := hwbdd (δ / 2) (by positivity)
  have hwcomp : ∀ j : Fin d, Measurable fun z => w z j := fun j =>
    (EuclideanSpace.proj j).continuous.measurable.comp hwm
  have h0lt : (0 : ℝ) < δ / 2 := by positivity
  have hint : ∀ j : Fin d, Integrable (fun x => w (y - x) j) σ := by
    intro j
    refine Integrable.mono' (integrable_const Bw) ((hwcomp j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
    filter_upwards [hsupp] with x hx
    have h := tdist_line_ge hy0 j hδ 0 (by simpa using h0lt) x hx
    have h2 := hBw _ (by simpa [hy0] using h)
    rw [Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ j).trans h2
  ext j
  rw [eval_integral_piLp (hf := hint) j]
  -- the one-dimensional derivative of the potential
  set F : ℝ → Torus d → ℝ := fun t x => G (Torus.mk (y0 + t • ev j) - x) with hF
  set F' : ℝ → Torus d → ℝ := fun t x => w (Torus.mk (y0 + t • ev j) - x) j with hF'
  have hD1 : HasDerivAt (fun t => ∫ x, F t x ∂σ) (∫ x, F' 0 x ∂σ) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := 0)
      (bound := fun _ => Bw) (s := Metric.ball 0 (δ / 2)) (Metric.ball_mem_nhds 0 h0lt) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Integrable.mono' (integrable_const BG)
        (hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
      filter_upwards [hsupp] with x hx
      have h := tdist_line_ge hy0 j hδ 0 (by simpa using h0lt) x hx
      exact hBG _ h
    · exact ((hwcomp j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [hsupp] with x hx t ht
      have h := tdist_line_ge hy0 j hδ t (by simpa using ht) x hx
      have h2 := hBw _ h
      exact (PiLp.norm_apply_le _ j).trans h2
    · exact integrable_const Bw
    · filter_upwards [hsupp] with x hx t ht
      have htt : |t| < δ / 2 := by simpa using ht
      have h := tdist_line_ge hy0 j hδ t htt x hx
      set b : Euc d := y0 + t • ev j - Torus.rep x with hb
      have hmkb : Torus.mk b = Torus.mk (y0 + t • ev j) - x := by
        rw [hb, KernelGrad.mk_sub, Torus.mk_rep]
      have hne : Torus.mk b ≠ 0 := by
        rw [hmkb]
        exact EnergyAux.ne_zero_of_tdist_pos (by linarith)
      have HG := hG b hne
      have hline : HasDerivAt (fun s : ℝ => b + (s - t) • ev j) (ev j) t := by
        have h1 : HasDerivAt (fun s : ℝ => (s - t)) 1 t := (hasDerivAt_id t).sub_const t
        have h2 := (h1.smul_const (ev j)).const_add b
        simpa using h2
      have HG' : HasFDerivAt (Torus.lift G) (∑ k, w (Torus.mk b) k • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ))
          (b + (t - t) • ev j) := by
        rw [sub_self, zero_smul, add_zero]; exact HG
      have hcomp := HG'.comp_hasDerivAt t hline
      have hval : (∑ k, w (Torus.mk b) k • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) (ev j) = w (Torus.mk b) j := by
        simp [ev, EuclideanSpace.single_apply]
      rw [hval, hmkb] at hcomp
      refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp, Torus.lift, hF]
      have e : b + (s - t) • ev j = (y0 + s • ev j) - Torus.rep x := by
        rw [hb, sub_smul]; abel
      rw [e, KernelGrad.mk_sub, Torus.mk_rep]
  -- the potential equals `G(· - a) + κ` near `0` (Newton)
  have hD2 : HasDerivAt (fun t => ∫ x, F t x ∂σ) (w (y - a) j) 0 := by
    set b0 : Euc d := y0 - Torus.rep a with hb0
    have hmk0 : Torus.mk b0 = y - a := by rw [hb0, KernelGrad.mk_sub, Torus.mk_rep, hy0]
    have hne0 : Torus.mk b0 ≠ 0 := by
      rw [hmk0]
      exact EnergyAux.ne_zero_of_tdist_pos (by rw [← EnergyAux.tdist_def]; linarith)
    have HG := hG b0 hne0
    have hline : HasDerivAt (fun s : ℝ => b0 + s • ev j) (ev j) 0 := by
      have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const (ev j)).const_add b0
      simpa using h2
    have HG' : HasFDerivAt (Torus.lift G) (∑ k, w (Torus.mk b0) k • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ))
        (b0 + (0 : ℝ) • ev j) := by
      rw [zero_smul, add_zero]; exact HG
    have hcomp := HG'.comp_hasDerivAt 0 hline
    have hval : (∑ k, w (Torus.mk b0) k • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) (ev j) = w (Torus.mk b0) j := by
      simp [ev, EuclideanSpace.single_apply]
    rw [hval, hmk0] at hcomp
    have hcomp2 := hcomp.add_const κ
    refine hcomp2.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) h0lt] with t ht
    have htt : |t| < δ / 2 := by simpa using ht
    have hz := tdist_line_a (a := a) hy0 j t
    have hgt : η < KernelGrad.tdist (Torus.mk (y0 + t • ev j)) a := by linarith
    simp only [hF]
    rw [hnewton _ hgt]
    simp only [Function.comp, Torus.lift]
    have e : b0 + t • ev j = (y0 + t • ev j) - Torus.rep a := by rw [hb0]; abel
    rw [e, KernelGrad.mk_sub, Torus.mk_rep]
  have := hD1.unique hD2
  simpa [hF', hy0] using this

end HRS.Commutator.Renorm
