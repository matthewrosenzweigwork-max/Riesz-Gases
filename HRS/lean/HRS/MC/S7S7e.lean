import HRS.MC.S7S7eAux2

/-!
# Packet `s7_S7e_pairing_identification` (relocation of `HRS.MC.Sec7.s7_S7e_pairing_identification`)

Proof.  By `s7e_responseRep_eq_of_eq` (uniqueness of the response) `responseRep (e_k)(x) = <k>^r a_k(x)`, hence
`ell_x = sum_k a_k(x) eps_k` (a `HasSum` in `lp`).  A continuous trilinear form expands along this `HasSum`
(`s7e_expand`), and the triple series commutes with `int . dmu` because `|a_k| <= C b_k`, `b_k = <k>^{-d-3}` summable
(`s7e_integral_triple`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7e

open HRS HRS.Sec7 HRS.MC.SEdge

open Classical

variable {d : ℕ}

theorem s7e_continuous_realMode (k : NonzeroLattice d) : Continuous (Torus.realMode k : Torus d → ℝ) := by
  unfold Torus.realMode
  split_ifs
  · exact continuous_const.mul (Torus.continuous_cosMode _)
  · exact continuous_const.mul (Torus.continuous_sinMode _)

theorem s7e_eps_norm (r : ℝ) (k : NonzeroLattice d) : ‖s7_eps r k‖ = 1 := by
  unfold s7_eps
  show ‖(lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)‖ = 1
  rw [lp.norm_single (by norm_num)]
  simp

theorem s7_S7e_pairing_identification_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) (D3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => NegSobolev d r) ℝ) :
    ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
        (∫ x, a k x * a l x * a j x ∂(withDensityReal ρ)) * D3 ![s7_eps r k, s7_eps r l, s7_eps r j] =
      ∫ x, D3 ![ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
        ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
        ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x] ∂(withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set μ := withDensityReal ρ with hμ
  -- the weights
  set b : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-((d : ℝ) + 3)) with hbdef
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos _
  have hb0 : ∀ k, 0 ≤ b k := fun k => (Real.rpow_pos_of_pos (hjp k) _).le
  have hb1 : ∀ k, b k ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  have hb : Summable b := by
    have := summable_jp_rpow (d := d) (((d : ℝ) + 3) / 2) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
    refine this.congr fun k => ?_
    simp only [hbdef]; congr 1; ring
  -- the bounds on a
  have hcont : ∀ k, Continuous (a k) := fun k => HRS.Q66.q66_cont_of_smooth (hmode.smooth_a k)
  set Ca : ℝ := |C₀| with hCa
  have hbound : ∀ k x, |a k x| ≤ Ca * b k := by
    intro k x
    have h1 := HRS.PDE.R2Aux.abs_le_cbNorm (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_a k) 1) x
    refine h1.trans ((hmode.bound_a k).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_abs_self C₀) (hb0 k)
  have hCa0 : 0 ≤ Ca := abs_nonneg _
  -- the coefficients of `ell_x`
  have hcoef : ∀ k x, responseRep (periodicRiesz d s) μ γ (Torus.realMode k) x =
      Lattice.jp k.1 ^ r * a k x := by
    intro k x
    have hjr : Lattice.jp k.1 ^ r * Lattice.jp k.1 ^ (-r) = 1 := by
      rw [← Real.rpow_add (hjp k)]; simp
    refine s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ (h := fun x => Lattice.jp k.1 ^ r * a k x)
      ((s7e_continuous_realMode k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (continuous_const.mul (hcont k)) ?_ ?_ x
    · unfold pair
      rw [integral_const_mul, hmode.mean_zero k, mul_zero]
    · intro y
      rw [s7e_kop_const_mul]
      have h1 := hmode.resp k y
      have hproj : projMean μ (s7_phi r k) y = Lattice.jp k.1 ^ (-r) * projMean μ (Torus.realMode k) y := by
        unfold projMean pair s7_phi
        rw [integral_const_mul]; ring
      rw [hproj] at h1
      calc Lattice.jp k.1 ^ r * a k y + γ * (Lattice.jp k.1 ^ r * Kop (periodicRiesz d s) μ (a k) y)
          = Lattice.jp k.1 ^ r * (a k y + γ * Kop (periodicRiesz d s) μ (a k) y) := by ring
        _ = Lattice.jp k.1 ^ r * (Lattice.jp k.1 ^ (-r) * projMean μ (Torus.realMode k) y) := by rw [h1]
        _ = projMean μ (Torus.realMode k) y := by rw [← mul_assoc, hjr, one_mul]
  have hmem : ∀ x, Memℓp (fun k : NonzeroLattice d => a k x) 2 := by
    intro x
    rw [memℓp_gen_iff (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hb.mul_left (Ca ^ 2))
    have h1 := hbound k x
    calc |a k x| ^ (2 : ℝ) = |a k x| ^ 2 := by rw [Real.rpow_two]
      _ ≤ (Ca * b k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = Ca ^ 2 * (b k * b k) := by ring
      _ ≤ Ca ^ 2 * b k := by
          gcongr
          exact mul_le_of_le_one_left (hb0 k) (hb1 k)
  have hHasSum : ∀ x, HasSum (fun k => a k x • s7_eps r k)
      (ellPt (periodicRiesz d s) μ γ r x) := by
    intro x
    have hw : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
        responseRep (periodicRiesz d s) μ γ (Torus.realMode k) x) = fun k => a k x := by
      funext k
      rw [hcoef k x, ← mul_assoc]
      have : Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ r = 1 := by
        rw [← Real.rpow_add (hjp k)]; simp
      rw [this, one_mul]
    have hmem' : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
        responseRep (periodicRiesz d s) μ γ (Torus.realMode k) x) 2 := by
      rw [hw]; exact hmem x
    have hell : ellPt (periodicRiesz d s) μ γ r x = (⟨fun k => a k x, hmem x⟩ :
        lp (fun _ : NonzeroLattice d => ℝ) 2) := by
      unfold ellPt
      rw [NegSobolev.ofSeq_of_mem _ hmem']
      congr 1
    rw [hell]
    have := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
      (⟨fun k => a k x, hmem x⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)
    have hfun : (fun i => lp.single 2 i ((⟨fun k => a k x, hmem x⟩ :
        lp (fun _ : NonzeroLattice d => ℝ) 2) i)) = fun k => a k x • s7_eps r k := by
      funext k
      unfold s7_eps
      show lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (a k x) =
        a k x • (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)
      rw [← lp.single_smul]
      simp
    rw [hfun] at this
    exact this
  -- expansion of the trilinear form
  have hexp : ∀ x, D3 ![ellPt (periodicRiesz d s) μ γ r x, ellPt (periodicRiesz d s) μ γ r x,
      ellPt (periodicRiesz d s) μ γ r x] = ∑' k, ∑' l, ∑' j, a k x * a l x * a j x *
        D3 ![s7_eps r k, s7_eps r l, s7_eps r j] := fun x =>
    s7e_expand D3 (s7_eps r) (fun k => a k x) _ (hHasSum x)
  simp_rw [hexp]
  -- interchange with the integral
  have hT : ∀ k l j, |D3 ![s7_eps r k, s7_eps r l, s7_eps r j]| ≤ ‖D3‖ := by
    intro k l j
    have := D3.le_opNorm ![s7_eps r k, s7_eps r l, s7_eps r j]
    simpa [Fin.prod_univ_three, Real.norm_eq_abs, s7e_eps_norm] using this
  have hint := s7e_integral_triple μ hb hb0 (Ca ^ 3 * ‖D3‖)
    (fun k l j x => a k x * a l x * a j x * D3 ![s7_eps r k, s7_eps r l, s7_eps r j])
    (fun k l j => ((((hcont k).mul (hcont l)).mul (hcont j)).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun k l j x => by
      have h1 := hbound k x
      have h2 := hbound l x
      have h3 := hbound j x
      have h4 := hT k l j
      have hbk := hb0 k
      have hbl := hb0 l
      have hbj := hb0 j
      rw [abs_mul, abs_mul, abs_mul]
      calc |a k x| * |a l x| * |a j x| * |D3 ![s7_eps r k, s7_eps r l, s7_eps r j]|
          ≤ (Ca * b k) * (Ca * b l) * (Ca * b j) * ‖D3‖ := by
            gcongr
        _ = Ca ^ 3 * ‖D3‖ * b k * b l * b j := by ring)
  rw [hint]
  refine tsum_congr fun k => tsum_congr fun l => tsum_congr fun j => ?_
  rw [integral_mul_const]

end HRS.MC.Sec7.S7e

end
