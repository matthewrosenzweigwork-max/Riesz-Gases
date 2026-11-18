import HRS.MC.S7S7cAux1
import HRS.MC.S7S7bAux13
import HRS.MC.S7S7dAux3
import HRS.MC.S7S7a
import HRS.MC.S7S7cAux7
import HRS.MC.SEdgeB5a

/-!
# Packet `s7_FC_D3`, sub-statement L3: uniform moments of `‖ζ_N‖_{E_r}`

For `n ≥ 1` (written `n = m + 1`), `sup_{N ≥ 1} E_{Q_N} ‖ζ_N‖^{2n} < ∞`.

Route (no Gibbs transfer): `‖ζ‖² = ∑_k c_k²` with `c_k = coord_k ζ = sed_Y Q (φ_k)`.  Weighted Jensen with
weights `a_k = ⟨k⟩^{-(d+1)}` on each finite `S` gives `(∑_S c_k²)^{m+1} ≤ (∑_S a_k)^m ∑_S a_k (c_k²/a_k)^{m+1}`, and
`E[a_k (c_k²/a_k)^{m+1}] = (a_k^{-1})^m E|c_k|^{2(m+1)} ≤ C 2^{m+1} ⟨k⟩^{-(2r(m+1)-(d+1)m)}` (`s7b_Y_moment`), which is
summable.  Finite sets are then removed by monotone convergence (`lintegral_iSup_directed`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCD3

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ}

/-- Weighted Jensen for the `(m+1)`-st power of a finite sum of nonnegative terms. -/
theorem d3a_jensen (m : ℕ) {ι : Type*} (S : Finset ι) (w p : ι → ℝ) (hw : ∀ i ∈ S, 0 < w i)
    (hp : ∀ i ∈ S, 0 ≤ p i) :
    (∑ i ∈ S, w i * p i) ^ (m + 1) ≤ (∑ i ∈ S, w i) ^ m * ∑ i ∈ S, w i * p i ^ (m + 1) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hW : 0 < ∑ i ∈ S, w i := Finset.sum_pos hw hne
  have h1 : ∑ i ∈ S, w i / (∑ i ∈ S, w i) = 1 := by
    rw [← Finset.sum_div]
    exact div_self hW.ne'
  have hJ := (convexOn_pow (m + 1)).map_sum_le (t := S) (w := fun i => w i / (∑ i ∈ S, w i))
    (p := p) (fun i hi => div_nonneg (hw i hi).le hW.le) h1
    (fun i hi => Set.mem_Ici.mpr (hp i hi))
  simp only [smul_eq_mul] at hJ
  have e1 : ∑ i ∈ S, w i / (∑ i ∈ S, w i) * p i = (∑ i ∈ S, w i * p i) / (∑ i ∈ S, w i) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ S, w i / (∑ i ∈ S, w i) * p i ^ (m + 1) =
      (∑ i ∈ S, w i * p i ^ (m + 1)) / (∑ i ∈ S, w i) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at hJ
  have key := mul_le_mul_of_nonneg_right hJ (pow_nonneg hW.le (m + 1))
  have e3 : (∑ i ∈ S, w i * p i) / (∑ i ∈ S, w i) ^ (m + 1) * 0 = 0 := by ring
  rw [← mul_pow, div_mul_cancel₀ _ hW.ne'] at key
  have e4 : (∑ i ∈ S, w i * p i ^ (m + 1)) / (∑ i ∈ S, w i) * (∑ i ∈ S, w i) ^ (m + 1) =
      (∑ i ∈ S, w i) ^ m * ∑ i ∈ S, w i * p i ^ (m + 1) := by
    rw [pow_succ]
    field_simp
  rw [e4] at key
  exact key

/-- The weight identity `(a_k^{-1})^m (|φ_k|-bound)^{2(m+1)} = 2^{m+1} ⟨k⟩^{-e}`. -/
theorem d3a_weight_id (x : ℝ) (hx : 0 < x) (d m : ℕ) (r : ℝ) :
    ((x ^ (-((d : ℝ) + 1)))⁻¹) ^ m * (x ^ (-r) * Real.sqrt 2) ^ (2 * (m + 1)) =
      2 ^ (m + 1) * x ^ (-(2 * r * ((m : ℝ) + 1) - ((d : ℝ) + 1) * m)) := by
  have h2 : Real.sqrt 2 ^ (2 * (m + 1)) = 2 ^ (m + 1) := by
    rw [pow_mul, Real.sq_sqrt (by norm_num)]
  have e1 : (x ^ ((d : ℝ) + 1)) ^ m = x ^ (((d : ℝ) + 1) * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  have e2 : (x ^ (-r)) ^ (2 * (m + 1)) = x ^ (-r * (2 * ((m : ℝ) + 1))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  have e3 : ((d : ℝ) + 1) * m + -r * (2 * ((m : ℝ) + 1)) =
      -(2 * r * ((m : ℝ) + 1) - ((d : ℝ) + 1) * m) := by ring
  calc ((x ^ (-((d : ℝ) + 1)))⁻¹) ^ m * (x ^ (-r) * Real.sqrt 2) ^ (2 * (m + 1))
      = (x ^ ((d : ℝ) + 1)) ^ m * ((x ^ (-r)) ^ (2 * (m + 1)) * 2 ^ (m + 1)) := by
        rw [Real.rpow_neg hx.le, inv_inv, mul_pow, h2]
    _ = x ^ (((d : ℝ) + 1) * m) * x ^ (-r * (2 * ((m : ℝ) + 1))) * 2 ^ (m + 1) := by
        rw [e1, e2]
        ring
    _ = x ^ (((d : ℝ) + 1) * m + -r * (2 * ((m : ℝ) + 1))) * 2 ^ (m + 1) := by
        rw [Real.rpow_add hx]
    _ = 2 ^ (m + 1) * x ^ (-(2 * r * ((m : ℝ) + 1) - ((d : ℝ) + 1) * m)) := by
        rw [e3]
        ring

/-- Pointwise identity `a (c²/a)^{m+1} = (a^{-1})^m |c|^{2(m+1)}` for `a > 0`. -/
theorem d3a_pt (a c : ℝ) (ha : 0 < a) (m : ℕ) :
    a * (c ^ 2 / a) ^ (m + 1) = (a⁻¹) ^ m * |c| ^ (2 * (m + 1)) := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [show |c| ^ (2 * (m + 1)) = (c ^ 2) ^ (m + 1) by rw [pow_mul, sq_abs], div_pow, pow_succ, inv_pow]
  field_simp
  ring

/-- The exponent `2r(m+1) - (d+1)m` exceeds `d` for `r = 2d+6`. -/
theorem d3a_exp_gt (d m : ℕ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) :
    (d : ℝ) < 2 * r * ((m : ℝ) + 1) - ((d : ℝ) + 1) * m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  subst hr
  nlinarith [mul_nonneg hd0 hm0]

/-- **L3** uniform `2n`-th moment of `‖ζ_N‖_{E_r}` under the modulated Gibbs law. -/
theorem d3_zeta_pow (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) (n : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => ‖zetaE r (sed_Q d s N γ ρ) X‖ ^ (2 * n)) (sed_Q d s N γ ρ) ∧
      ∫ X, ‖zetaE r (sed_Q d s N γ ρ) X‖ ^ (2 * n) ∂(sed_Q d s N γ ρ) ≤ C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, fun N hN => ?_⟩
    have : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
      HRS.MC.SEdge.B5a.b5a_Q_prob hd hs0 hs hγ hρ hN
    simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hr2 : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.MC.Sec7.S7b.s7b_Y_moment hd hs0 hs hγ hρ (m + 1)
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 * r * ((m : ℝ) + 1) - ((d : ℝ) + 1) * m := ⟨_, rfl⟩
  have hE : (d : ℝ) < e := by rw [he]; exact d3a_exp_gt d m hr
  have hKs : Summable (fun k : NonzeroLattice d => Cm * (2 ^ (m + 1) * Lattice.jp k.1 ^ (-e))) :=
    ((HRS.MC.Sec7.S7c.s7c_summable_jp hE).mul_left _).mul_left _
  have hKnn : ∀ k : NonzeroLattice d, 0 ≤ Cm * (2 ^ (m + 1) * Lattice.jp k.1 ^ (-e)) := fun k =>
    mul_nonneg hCm0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Torus.jp_pos k.1).le _))
  have ha_pos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 ^ (-((d : ℝ) + 1)) :=
    fun k => Real.rpow_pos_of_pos (Torus.jp_pos k.1) _
  have hasum : Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-((d : ℝ) + 1))) :=
    HRS.MC.Sec7.S7c.s7c_summable_jp (by linarith : (d : ℝ) < (d : ℝ) + 1)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact tsum_nonneg fun k => (ha_pos k).le
  have hAS : ∀ S : Finset (NonzeroLattice d),
      ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) ≤ A := fun S => by
    rw [hA]
    exact sum_le_hasSum S (fun k _ => (ha_pos k).le) hasum.hasSum
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = A ^ m * ∑' k : NonzeroLattice d,
      Cm * (2 ^ (m + 1) * Lattice.jp k.1 ^ (-e)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (pow_nonneg hA0 m) (tsum_nonneg hKnn)
  refine ⟨M, fun N hN => ?_⟩
  haveI : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B5a.b5a_Q_prob hd hs0 hs hγ hρ hN
  set Q := sed_Q d s N γ ρ with hQ
  -- coordinates of `ζ_N`
  have hcc : ∀ (k : NonzeroLattice d) (X : Config d N),
      NegSobolev.coord (zetaE r Q X) k = sed_Y Q (s7_phi r k) X :=
    fun k X => HRS.MC.Sec7.S7c.s7c_coord_zeta hN hr2 Q X k
  have hT : ∀ (k : NonzeroLattice d) (x : Torus d),
      |s7_phi r k x| ≤ Lattice.jp k.1 ^ (-r) * Real.sqrt 2 := by
    intro k x
    have hx : s7_phi r k x = Lattice.jp k.1 ^ (-r) * Torus.realMode k x := rfl
    rw [hx, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _)]
    exact mul_le_mul_of_nonneg_left (Torus.abs_realMode_le k x)
      (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  have hbd : ∀ (k : NonzeroLattice d) (X : Config d N),
      |NegSobolev.coord (zetaE r Q X) k| ≤
        Real.sqrt N * (2 * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2)) := fun k X => by
    rw [hcc]
    exact HRS.MC.Sec7.S7d.s7d_sedY_bdd hN Q (hT k) X
  have hYm : ∀ k : NonzeroLattice d, Measurable (fun X => NegSobolev.coord (zetaE r Q X) k) := by
    intro k
    simp only [hcc]
    exact HRS.MC.Sec7.S7c.s7c_sedY_meas hN _
      (HRS.Q66.q66_cont_of_smooth (HRS.MC.Sec7.S7a.s7a_phi_smooth r k))
  -- per-mode moments
  have hterm : ∀ k : NonzeroLattice d,
      Integrable (fun X => Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1)) Q ∧
      ∫ X, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) ∂Q ≤
        Cm * (2 ^ (m + 1) * Lattice.jp k.1 ^ (-e)) := by
    intro k
    have hpt : (fun X => Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1)) =
        fun X => (Lattice.jp k.1 ^ (-((d : ℝ) + 1)))⁻¹ ^ m *
          |NegSobolev.coord (zetaE r Q X) k| ^ (2 * (m + 1)) :=
      funext fun X => d3a_pt _ _ (ha_pos k) m
    rw [hpt]
    have hmeas : Measurable (fun X => |NegSobolev.coord (zetaE r Q X) k| ^ (2 * (m + 1))) :=
      ((hYm k).abs).pow_const _
    have hbd_pow : ∀ X, ‖|NegSobolev.coord (zetaE r Q X) k| ^ (2 * (m + 1))‖ ≤
        (Real.sqrt N * (2 * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2))) ^ (2 * (m + 1)) := fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbd k X) _
    have hint : Integrable (fun X => |NegSobolev.coord (zetaE r Q X) k| ^ (2 * (m + 1))) Q :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (ae_of_all _ hbd_pow)
    refine ⟨hint.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hcc' : ∫ X, |NegSobolev.coord (zetaE r Q X) k| ^ (2 * (m + 1)) ∂Q =
        ∫ X, |sed_Y Q (s7_phi r k) X| ^ (2 * (m + 1)) ∂Q := by
      simp only [hcc]
    rw [hcc']
    have hmom := hCm (s7_phi r k) (Lattice.jp k.1 ^ (-r) * Real.sqrt 2)
      (HRS.MC.Sec7.S7a.s7a_phi_smooth r k) (hT k) N hN
    have hw := d3a_weight_id (Lattice.jp k.1) (Torus.jp_pos k.1) d m r
    calc (Lattice.jp k.1 ^ (-((d : ℝ) + 1)))⁻¹ ^ m *
          ∫ X, |sed_Y Q (s7_phi r k) X| ^ (2 * (m + 1)) ∂Q
        ≤ (Lattice.jp k.1 ^ (-((d : ℝ) + 1)))⁻¹ ^ m * (Cm * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) ^ (2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left hmom (pow_nonneg (inv_nonneg.2 (ha_pos k).le) m)
      _ = Cm * ((Lattice.jp k.1 ^ (-((d : ℝ) + 1)))⁻¹ ^ m * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) ^ (2 * (m + 1))) := by
          ring
      _ = Cm * (2 ^ (m + 1) * Lattice.jp k.1 ^ (-e)) := by
          rw [hw, he]
  -- the finite-sum functions
  have hGint : ∀ S : Finset (NonzeroLattice d), Integrable (fun X => A ^ m *
      ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1)) Q :=
    fun S => (integrable_finsetSum S fun k _ => (hterm k).1).const_mul _
  have hGnn : ∀ (S : Finset (NonzeroLattice d)) (X : Config d N), 0 ≤ A ^ m *
      ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) :=
    fun S X => mul_nonneg (pow_nonneg hA0 m) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (ha_pos k).le (pow_nonneg (div_nonneg (sq_nonneg _) (ha_pos k).le) _))
  have hGbound : ∀ S : Finset (NonzeroLattice d), ∫ X, A ^ m *
      ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) ∂Q ≤ M := by
    intro S
    rw [integral_const_mul, integral_finsetSum S fun k _ => (hterm k).1, hM]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA0 m)
    exact (Finset.sum_le_sum fun k _ => (hterm k).2).trans (sum_le_hasSum S (fun k _ => hKnn k) hKs.hasSum)
  -- pointwise domination of the finite truncations
  have hpt : ∀ (S : Finset (NonzeroLattice d)) (X : Config d N),
      (∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1) ≤ A ^ m *
        ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
          (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) := by
    intro S X
    have h := d3a_jensen m S (fun k => Lattice.jp k.1 ^ (-((d : ℝ) + 1)))
      (fun k => NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1)))
      (fun k _ => ha_pos k) (fun k _ => div_nonneg (sq_nonneg _) (ha_pos k).le)
    have e : ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) =
        ∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2 :=
      Finset.sum_congr rfl fun k _ => by
        have := (ha_pos k).ne'
        field_simp
    rw [e] at h
    have hS0 : 0 ≤ ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) :=
      Finset.sum_nonneg fun k _ => (ha_pos k).le
    have hsum0 : 0 ≤ ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
        (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (ha_pos k).le
        (pow_nonneg (div_nonneg (sq_nonneg _) (ha_pos k).le) _)
    calc (∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1)
        ≤ (∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ m * ∑ k ∈ S,
            Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
              (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) := h
      _ ≤ A ^ m * ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
            (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS0 (hAS S) m) hsum0
  -- measurability and monotonicity of the truncations
  have hFmeas : ∀ S : Finset (NonzeroLattice d), Measurable (fun X : Config d N =>
      ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1))) :=
    fun S => ((Finset.measurable_sum S fun k _ => (hYm k).pow_const 2).pow_const _).ennreal_ofReal
  have hFmono : Monotone (fun (S : Finset (NonzeroLattice d)) (X : Config d N) =>
      ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1))) := by
    intro S S' hSS' X
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => sq_nonneg _) ?_ _)
    exact Finset.sum_le_sum_of_subset_of_nonneg hSS' (fun k _ _ => sq_nonneg _)
  -- bound on each truncation
  have hFle : ∀ S : Finset (NonzeroLattice d),
      ∫⁻ X, ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1)) ∂Q
        ≤ ENNReal.ofReal M := by
    intro S
    calc ∫⁻ X, ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1)) ∂Q
        ≤ ∫⁻ X, ENNReal.ofReal (A ^ m *
            ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
              (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1)) ∂Q :=
          lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hpt S X)
      _ = ENNReal.ofReal (∫ X, A ^ m *
            ∑ k ∈ S, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) *
              (NegSobolev.coord (zetaE r Q X) k ^ 2 / Lattice.jp k.1 ^ (-((d : ℝ) + 1))) ^ (m + 1) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal (hGint S) (ae_of_all _ (hGnn S))).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (hGbound S)
  -- monotone convergence along finite truncations
  have hsup : ∀ X : Config d N, (⨆ S : Finset (NonzeroLattice d),
      ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1))) =
      ENNReal.ofReal (‖zetaE r Q X‖ ^ (2 * (m + 1))) := by
    intro X
    have hsum := (NegSobolev.coord_sq (zetaE r Q X)).1
    have hnorm2 : ‖zetaE r Q X‖ ^ (2 * (m + 1)) =
        (∑' k, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1) := by
      rw [pow_mul, (NegSobolev.coord_sq (zetaE r Q X)).2]
    have ht : Tendsto (fun S : Finset (NonzeroLattice d) =>
        (∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1)) atTop
        (𝓝 ((∑' k, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1))) :=
      (hsum.hasSum).pow (m + 1)
    have ht' := ENNReal.tendsto_ofReal ht
    have hmono : Monotone (fun S : Finset (NonzeroLattice d) =>
        ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1))) :=
      fun S S' h => hFmono h X
    have hlim := tendsto_atTop_iSup hmono
    have := tendsto_nhds_unique hlim ht'
    rw [this, hnorm2]
  have hdir : Directed (· ≤ ·) (fun (S : Finset (NonzeroLattice d)) (X : Config d N) =>
      ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1))) :=
    hFmono.directed_le
  have hlin : ∫⁻ X, ENNReal.ofReal (‖zetaE r Q X‖ ^ (2 * (m + 1))) ∂Q ≤ ENNReal.ofReal M := by
    calc ∫⁻ X, ENNReal.ofReal (‖zetaE r Q X‖ ^ (2 * (m + 1))) ∂Q
        = ∫⁻ X, ⨆ S : Finset (NonzeroLattice d),
            ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1)) ∂Q :=
          lintegral_congr fun X => (hsup X).symm
      _ = ⨆ S : Finset (NonzeroLattice d), ∫⁻ X,
            ENNReal.ofReal ((∑ k ∈ S, NegSobolev.coord (zetaE r Q X) k ^ 2) ^ (m + 1)) ∂Q :=
          lintegral_iSup_directed (fun S => (hFmeas S).aemeasurable) hdir
      _ ≤ ENNReal.ofReal M := iSup_le fun S => hFle S
  -- conclusion
  have hmeasζ : Measurable (fun X => ‖zetaE r Q X‖ ^ (2 * (m + 1))) :=
    ((HRS.MC.Sec7.S7c.s7c_zeta_meas hN hr2 Q).norm).pow_const _
  have hnn : 0 ≤ᵐ[Q] fun X => ‖zetaE r Q X‖ ^ (2 * (m + 1)) :=
    ae_of_all _ fun X => by positivity
  refine ⟨⟨hmeasζ.aestronglyMeasurable, ?_⟩, ?_⟩
  · exact (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeasζ.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hM0 hlin

end HRS.MC.Sec7.FCD3
