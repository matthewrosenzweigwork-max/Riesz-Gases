import HRS.MC.E213U18m

/-!
# Packet e213u18 (part n): measurability and boundedness of `x ↦ ℓ_x`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.MC.SEdge HRS.MC.Sec7 HRS.MC.Sec7.S7e

variable {d : ℕ}

section EllReg

variable {s : ℝ} {ρ : Torus d → ℝ}

theorem u18_ellPt_hasSum (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    (hρ : SmoothPosDensity ρ) {r : ℝ} {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C : ℝ} (hmode : s7_ModeData d s γ ρ r a v C)
    (x : Torus d) :
    HasSum (fun k => a k x • s7_eps r k) (ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x) := by
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos _
  have hw : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
      responseRep (periodicRiesz d s) (withDensityReal ρ) γ (Torus.realMode k) x) = fun k => a k x := by
    funext k
    rw [u18_resp_mode hd hs0 hs hγ hρ hmode k x, ← mul_assoc]
    have : Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ r = 1 := by
      rw [← Real.rpow_add (hjp k)]; simp
    rw [this, one_mul]
  have hmem' : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
      responseRep (periodicRiesz d s) (withDensityReal ρ) γ (Torus.realMode k) x) 2 := by
    rw [hw]; exact u18_a_mem hmode x
  have hell : ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x = (⟨fun k => a k x, u18_a_mem hmode x⟩ :
      lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    unfold ellPt
    rw [NegSobolev.ofSeq_of_mem _ hmem']
    congr 1
  rw [hell]
  have := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
    (⟨fun k => a k x, u18_a_mem hmode x⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)
  have hfun : (fun i => lp.single 2 i ((⟨fun k => a k x, u18_a_mem hmode x⟩ :
      lp (fun _ : NonzeroLattice d => ℝ) 2) i)) = fun k => a k x • s7_eps r k := by
    funext k
    unfold s7_eps
    show lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (a k x) =
      a k x • (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)
    rw [← lp.single_smul]
    simp
  rw [hfun] at this
  exact this

theorem u18_ellPt_meas (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) :
    Measurable (ellPt (periodicRiesz d s) (withDensityReal ρ) γ r) ∧
    ∃ B : ℝ, ∀ x, ‖ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x‖ ≤ B := by
  obtain ⟨a, v, C, hmode⟩ := HRS.MC.Sec7.S7a.s7_S7a_mode_data_proof hd hs0 hs r hr γ hγ ρ hρ
  have hcont : ∀ k, Continuous (a k) := fun k => HRS.Q66.q66_cont_of_smooth (hmode.smooth_a k)
  have hb : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
    have := summable_jp_rpow (d := d) (((d : ℝ) + 3) / 2) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
    refine this.congr fun k => ?_
    congr 1; ring
  refine ⟨?_, |C| * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 3)), fun x => ?_⟩
  · refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (NonzeroLattice d)))
      (f := fun (s' : Finset (NonzeroLattice d)) y => ∑ k ∈ s', a k y • s7_eps r k) (fun s' => ?_)
      (tendsto_pi_nhds.2 fun x => u18_ellPt_hasSum hd hs0 hs hγ hρ hmode x)
    exact (continuous_finset_sum _ fun k _ => (hcont k).smul continuous_const).measurable
  · refine (u18_ellPt_hasSum hd hs0 hs hγ hρ hmode x).norm_le_of_bounded
      (hb.hasSum.mul_left |C|) (fun k => ?_)
    rw [norm_smul, s7e_eps_norm, mul_one, Real.norm_eq_abs]
    exact u18_a_bound hmode k x

end EllReg

end HRS.MC.E213U18

end
