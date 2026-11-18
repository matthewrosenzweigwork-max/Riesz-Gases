import HRS.Commutator.Torus.TKRAux10

/-!
# T-KR helpers, part 11: `L^q(𝕋^d)` norms of the periodised truncation and of `|x||∇g_>|`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

lemma tkr_centeredRep_measurable : Measurable (KernelGrad.centeredRep : Torus d → Euc d) := by
  have hrep : Measurable (Torus.rep : Torus d → Euc d) := tpos_measurable_rep
  have hc : (KernelGrad.centeredRep : Torus d → Euc d) = fun z => WithLp.toLp 2
      (fun i => if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1) := by
    funext z; rfl
  rw [hc]
  refine (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr fun i => ?_)
  have hi : Measurable fun z : Torus d => (Torus.rep z) i :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hrep
  exact Measurable.ite (measurableSet_le hi measurable_const) hi (hi.sub measurable_const)

lemma tkr_perio_ge_gen {h : Euc d → ℝ} (hnn : ∀ z, 0 ≤ h z)
    (hsum : ∀ y, Summable fun m : Lattice d => h (y + Lattice.toEuc m)) (x : Torus d) :
    h (KernelGrad.centeredRep x) ≤ perio h x := by
  obtain ⟨m, hm⟩ := tpos_centeredRep_eq x
  unfold perio
  rw [hm]
  exact (hsum (Torus.rep x)).le_tsum m (fun j _ => hnn _)

lemma tkr_lintegral_centered {h : Euc d → ℝ} (hmeas : Measurable h) (hnn : ∀ z, 0 ≤ h z)
    (hsum : ∀ y, Summable fun m : Lattice d => h (y + Lattice.toEuc m)) :
    ∫⁻ x : Torus d, ENNReal.ofReal (h (KernelGrad.centeredRep x)) ≤ ∫⁻ y : Euc d, ENNReal.ofReal (h y) := by
  calc ∫⁻ x : Torus d, ENNReal.ofReal (h (KernelGrad.centeredRep x))
      ≤ ∫⁻ x : Torus d, ENNReal.ofReal (perio h x) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (tkr_perio_ge_gen hnn hsum x)
    _ = _ := tpos_lintegral_perio hmeas hnn hsum

/-- `1 ≤ q < ∞` from the Hölder conjugacy with `p > d/(d-s)`. -/
lemma tkr_q_props (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    q ≠ ⊤ ∧ 1 ≤ q.toReal := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hds : 0 < (d : ℝ) - s := by linarith
  have hρ1 : 1 ≤ (d : ℝ) / (d - s) := by rw [le_div_iff₀ hds]; linarith
  have hp1 : 1 < p := lt_of_le_of_lt (by simpa using ENNReal.ofReal_le_ofReal hρ1) hp
  have hpinv : p⁻¹ < 1 := ENNReal.inv_lt_one.2 hp1
  have hqtop : q ≠ ⊤ := by
    intro h
    rw [h, ENNReal.inv_top, add_zero] at hpq
    exact hpinv.ne hpq
  refine ⟨hqtop, ?_⟩
  have hq1 : 1 ≤ q := by
    have : q⁻¹ ≤ 1 := by rw [← hpq]; exact le_add_self
    exact ENNReal.inv_le_one.1 this
  have := ENNReal.toReal_mono hqtop hq1
  simpa using this

end HRS.Commutator.TorusNote
