import HRS.MC.CepaDefs
import HRS.MC.CepE1Aux5

/-!
# Packet CEPE4, auxiliary 1: pointwise Lyapunov inequality for the singular force on the alcove

For `x` in the open alcove and `ρ_k = k/N`:
`⟨x - ρ, ∇Φ(x)⟩ ≥ -K₁` and `∑_i |∇Φ(x)_i| ≤ 8N ⟨x - ρ, ∇Φ(x)⟩ + K₂`.
Pair by pair: with `d = x_l - x_k ∈ (0,1)` and `e = (l-k)/N ∈ [1/N, 1-1/N]`,
`π (e - d) cos πd ≥ π/(4N) - 2πN sin πd`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS.MC.Cepa

theorem e4_cos_ge_half {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1 / 4) : 1 / 2 ≤ Real.cos (Real.pi * d) := by
  have h : Real.cos (Real.pi / 3) ≤ Real.cos (Real.pi * d) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    nlinarith [Real.pi_pos]
  rwa [Real.cos_pi_div_three] at h

theorem e4_sin_ge {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1 / 2) : 2 * d ≤ Real.sin (Real.pi * d) := by
  have := Real.mul_le_sin (x := Real.pi * d) (by positivity) (by nlinarith [Real.pi_pos])
  have hp := Real.pi_pos
  have : 2 / Real.pi * (Real.pi * d) = 2 * d := by field_simp
  nlinarith [Real.mul_le_sin (x := Real.pi * d) (by positivity) (by nlinarith [Real.pi_pos])]

/-- The core real inequality. -/
theorem e4_core {δ e d : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (he1 : δ ≤ e) (he2 : e ≤ 1 - δ)
    (hd0 : 0 < d) (hd1 : d < 1) :
    Real.pi * δ / 4 - (2 * Real.pi / δ) * Real.sin (Real.pi * d) ≤
      Real.pi * ((e - d) * Real.cos (Real.pi * d)) := by
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi * d) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hC : 0 ≤ (2 * Real.pi / δ) * Real.sin (Real.pi * d) := by positivity
  by_cases h1 : d ≤ δ / 2
  · have hc := e4_cos_ge_half hd0.le (by linarith)
    have : δ / 4 ≤ (e - d) * Real.cos (Real.pi * d) := by nlinarith
    nlinarith
  by_cases h2 : 1 - δ / 2 ≤ d
  · have hc := e4_cos_ge_half (d := 1 - d) (by linarith) (by linarith)
    have hcos : Real.cos (Real.pi * d) = -Real.cos (Real.pi * (1 - d)) := by
      have : Real.pi * d = Real.pi - Real.pi * (1 - d) := by ring
      rw [this, Real.cos_pi_sub]
    have : δ / 4 ≤ (e - d) * Real.cos (Real.pi * d) := by
      rw [hcos]; nlinarith
    nlinarith
  · replace h1 := not_le.1 h1; replace h2 := not_le.1 h2
    have hs : δ ≤ Real.sin (Real.pi * d) := by
      by_cases hd : d ≤ 1 / 2
      · have := e4_sin_ge hd0.le hd; linarith
      · have hd' : 1 - d ≤ 1 / 2 := by linarith
        have := e4_sin_ge (d := 1 - d) (by linarith) hd'
        have e : Real.sin (Real.pi * d) = Real.sin (Real.pi * (1 - d)) := by
          have : Real.pi * d = Real.pi - Real.pi * (1 - d) := by ring
          rw [this, Real.sin_pi_sub]
        rw [e]; linarith
    have hb : -1 ≤ (e - d) * Real.cos (Real.pi * d) := by
      have hc1 := Real.neg_one_le_cos (Real.pi * d)
      have hc2 := Real.cos_le_one (Real.pi * d)
      have : |e - d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h3 : |(e - d) * Real.cos (Real.pi * d)| ≤ 1 := by
        rw [abs_mul]
        have : |Real.cos (Real.pi * d)| ≤ 1 := Real.abs_cos_le_one _
        nlinarith [abs_nonneg (e - d), abs_nonneg (Real.cos (Real.pi * d))]
      exact (abs_le.1 h3).1
    have h4 : (2 * Real.pi / δ) * δ = 2 * Real.pi := by field_simp
    have h5 : (2 * Real.pi / δ) * δ ≤ (2 * Real.pi / δ) * Real.sin (Real.pi * d) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith


/-- Pairwise estimates for the singular profile. -/
theorem e4_pair {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) {e d : ℝ} (he1 : 1 / (N : ℝ) ≤ e)
    (he2 : e ≤ 1 - 1 / (N : ℝ)) (hd0 : 0 < d) (hd1 : d < 1) :
    -(2 * Real.pi * a) ≤ HRS.MC.CepE1.cepe1_h1 a N d * (d - e) ∧
    2 * |HRS.MC.CepE1.cepe1_h1 a N d| ≤
      8 * N * (HRS.MC.CepE1.cepe1_h1 a N d * (d - e)) + 16 * Real.pi * N * a := by
  have hpi := Real.pi_pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set δ : ℝ := 1 / (N : ℝ) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hNp (by norm_num)]; linarith
  have hNδ : (N : ℝ) * δ = 1 := by rw [hδ]; field_simp
  set A : ℝ := a / N with hA
  have hA0 : 0 < A := by positivity
  have hNA : (N : ℝ) * A = a := by rw [hA]; field_simp
  have hs : 0 < Real.sin (Real.pi * d) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  set s := Real.sin (Real.pi * d) with hsdef
  set c := Real.cos (Real.pi * d) with hcdef
  have hcore := e4_core hδ0 hδ2 he1 he2 hd0 hd1
  set q : ℝ := Real.pi * (c / s) with hq
  have hh : HRS.MC.CepE1.cepe1_h1 a N d = A * (-q) := by
    unfold HRS.MC.CepE1.cepe1_h1; rw [hq, hA]
  have hqe : q * (e - d) = Real.pi * ((e - d) * c) / s := by rw [hq]; field_simp
  have hdiv : (Real.pi * δ / 4) / s - 2 * Real.pi / δ ≤ q * (e - d) := by
    rw [hqe, le_div_iff₀ hs]
    have : ((Real.pi * δ / 4) / s - 2 * Real.pi / δ) * s = Real.pi * δ / 4 - 2 * Real.pi / δ * s := by
      field_simp
    rw [this]; exact hcore
  have hpos : 0 ≤ (Real.pi * δ / 4) / s := by positivity
  have hprod : HRS.MC.CepE1.cepe1_h1 a N d * (d - e) = A * (q * (e - d)) := by rw [hh]; ring
  have hinv : 2 * Real.pi / δ = 2 * Real.pi * N := by rw [hδ]; field_simp
  have hqabs : |q| ≤ Real.pi / s := by
    rw [hq, abs_mul, abs_of_pos hpi, abs_div, abs_of_pos hs]
    have habs : |c| ≤ 1 := Real.abs_cos_le_one _
    calc Real.pi * (|c| / s) ≤ Real.pi * (1 / s) := by gcongr
      _ = Real.pi / s := by ring
  refine ⟨?_, ?_⟩
  · rw [hprod]
    have : -(2 * Real.pi * N) ≤ q * (e - d) := by linarith
    nlinarith
  · rw [hprod, hh, abs_mul, abs_of_pos hA0, abs_neg]
    have h1 : 2 * (A * |q|) ≤ 2 * (A * (Real.pi / s)) := by nlinarith
    have h2 : (Real.pi * δ / 4) / s - 2 * Real.pi * N ≤ q * (e - d) := by linarith
    have h3 : 8 * N * A * ((Real.pi * δ / 4) / s - 2 * Real.pi * N) ≤ 8 * N * A * (q * (e - d)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 8 * N * A * ((Real.pi * δ / 4) / s) = 2 * (A * (Real.pi / s)) := by
      have : (N : ℝ) * δ = 1 := hNδ
      field_simp
      nlinarith [this]
    have h5 : 8 * N * A * (2 * Real.pi * N) = 16 * Real.pi * N * a := by
      rw [← hNA]; ring
    nlinarith

theorem e4_chamberPot_eq (a : ℝ) (N : ℕ) :
    cep_chamberPot a N = HRS.MC.CepE1.cepe1_pair
      (fun u => (a / N) * (-Real.log (2 * Real.sin (Real.pi * u)))) := by
  funext z
  unfold cep_chamberPot HRS.MC.CepE1.cepe1_pair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem e4_Phi_hasGradient {a : ℝ} {N : ℕ} {z : Ch N}
    (hz : ∀ k l : Fin N, k < l → 0 < z l - z k ∧ z l - z k < 1) :
    HasGradientAt (cep_chamberPot a N)
      (HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) z) z := by
  rw [e4_chamberPot_eq]
  refine HRS.MC.CepE1.cepe1_hasGradientAt_pair fun k l hkl => ?_
  exact (HRS.MC.CepE1.cepe1_hasDerivAt_neglog (hz k l hkl)).const_mul _

/-- The centre `ρ_k = k / N`. -/
def e4_rho (N : ℕ) : Ch N := WithLp.toLp 2 fun k => ((k : ℕ) : ℝ) / N

theorem e4_inner_pairGrad (h' : ℝ → ℝ) {N : ℕ} (x y : Ch N) :
    inner ℝ (HRS.MC.CepE1.cepe1_pairGrad h' x) y =
      ∑ k, ∑ l, if k < l then h' (x l - x k) * (y l - y k) else 0 := by
  unfold HRS.MC.CepE1.cepe1_pairGrad
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    rw [real_inner_smul_left, HRS.MC.CepE1.cepe1_inner_vec]
  · simp [hkl]

theorem e4_norm_pairGrad (h' : ℝ → ℝ) {N : ℕ} (x : Ch N) :
    ∑ i, |(HRS.MC.CepE1.cepe1_pairGrad h' x) i| ≤
      2 * ∑ k, ∑ l, if k < l then |h' (x l - x k)| else 0 := by
  have hT : ∀ i, |(HRS.MC.CepE1.cepe1_pairGrad h' x) i| ≤
      (∑ k, if k < i then |h' (x i - x k)| else 0) + ∑ l, if i < l then |h' (x l - x i)| else 0 := by
    intro i
    rw [HRS.MC.CepE1.cepe1_pairGrad_apply]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      split_ifs <;> simp
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      split_ifs <;> simp
  refine (Finset.sum_le_sum fun i _ => hT i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun i k => if k < i then |h' (x i - x k)| else 0)]
  linarith

theorem e4_pointwise {a : ℝ} (ha : 0 < a) {N : ℕ} {x : Ch N} (hx : x ∈ cep_Alcove N) :
    -(2 * Real.pi * a * (N : ℝ) ^ 2) ≤ inner ℝ (x - e4_rho N) (gradient (cep_chamberPot a N) x) ∧
    ∑ i, |(gradient (cep_chamberPot a N) x) i| ≤
      8 * N * inner ℝ (x - e4_rho N) (gradient (cep_chamberPot a N) x) +
        16 * Real.pi * N * a * (N : ℝ) ^ 2 := by
  have hz : ∀ k l : Fin N, k < l → 0 < x l - x k ∧ x l - x k < 1 :=
    fun k l hkl => ⟨by linarith [hx.1 k l hkl], by linarith [hx.2 k l]⟩
  have hg : gradient (cep_chamberPot a N) x =
      HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) x :=
    (e4_Phi_hasGradient hz).gradient
  rw [hg, real_inner_comm, e4_inner_pairGrad]
  have hpair : ∀ k l : Fin N, k < l →
      -(2 * Real.pi * a) ≤ HRS.MC.CepE1.cepe1_h1 a N (x l - x k) * ((x - e4_rho N) l - (x - e4_rho N) k) ∧
      2 * |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| ≤
        8 * N * (HRS.MC.CepE1.cepe1_h1 a N (x l - x k) * ((x - e4_rho N) l - (x - e4_rho N) k)) +
          16 * Real.pi * N * a := by
    intro k l hkl
    have hN : 2 ≤ N := by
      have := k.2; have := l.2; have : (k : ℕ) < l := hkl; omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hkl' : (k : ℕ) + 1 ≤ l := hkl
    have hlN : (l : ℕ) < N := l.2
    set e : ℝ := ((l : ℕ) - (k : ℕ) : ℝ) / N with he
    have hdiff : (x - e4_rho N) l - (x - e4_rho N) k = (x l - x k) - e := by
      simp only [e4_rho, WithLp.ofLp_sub, Pi.sub_apply, he]
      ring
    have h1 : (1 : ℝ) / N ≤ e := by
      rw [he]; apply div_le_div_of_nonneg_right _ hNr.le
      have : ((k : ℕ) : ℝ) + 1 ≤ (l : ℕ) := by exact_mod_cast hkl'
      linarith
    have h2 : e ≤ 1 - 1 / (N : ℝ) := by
      rw [he, show (1 : ℝ) - 1 / N = ((N : ℝ) - 1) / N by field_simp]
      apply div_le_div_of_nonneg_right _ hNr.le
      have : ((l : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hlN
      have : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
      linarith
    rw [hdiff]
    exact e4_pair ha hN h1 h2 (hz k l hkl).1 (hz k l hkl).2
  have hcard : ∀ c : ℝ, (∑ _k : Fin N, ∑ _l : Fin N, c) = (N : ℝ) ^ 2 * c := by
    intro c; simp; ring
  constructor
  · calc -(2 * Real.pi * a * (N : ℝ) ^ 2) = ∑ _k : Fin N, ∑ _l : Fin N, -(2 * Real.pi * a) := by
          rw [hcard]; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
          by_cases hkl : k < l
          · simp only [hkl, ite_true]; exact (hpair k l hkl).1
          · simp only [hkl, ite_false]; nlinarith [Real.pi_pos]
  · refine (e4_norm_pairGrad _ x).trans ?_
    calc 2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| else 0)
        = ∑ k : Fin N, ∑ l : Fin N, 2 * (if k < l then |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| else 0) := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ k : Fin N, ∑ l : Fin N, (8 * N * (if k < l then HRS.MC.CepE1.cepe1_h1 a N (x l - x k) *
            ((x - e4_rho N) l - (x - e4_rho N) k) else 0) + 16 * Real.pi * N * a) := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
          by_cases hkl : k < l
          · simp only [hkl, ite_true]; exact (hpair k l hkl).2
          · simp only [hkl, ite_false, mul_zero, zero_add]; positivity
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hcard]; ring

end HRS.MC.CepE4
