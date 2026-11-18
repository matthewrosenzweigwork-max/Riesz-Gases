/-
# HRS.Equilibrium.Q84dAuxP — packet Q84d: derivative of the Hamiltonian along coordinate lines
-/
import HRS.Equilibrium.Q84dAuxO

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_pair_sum_identity (G : Torus d → ℝ) (hG : ∀ z, G (-z) = -G z) (Y : Config d N)
    (i : Fin N) :
    ∑ p ∈ pairsN N, (((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0)) *
      G (Y p.1 - Y p.2)) = ∑ j ∈ Finset.univ.erase i, G (Y i - Y j) := by
  unfold pairsN
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have e1 : ∀ a b : Fin N, (if a < b then (((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0)) *
      G (Y a - Y b)) else 0) =
      (if a = i then (if i < b then G (Y i - Y b) else 0) else 0) -
        (if b = i then (if a < i then G (Y a - Y i) else 0) else 0) := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a < b
    · subst ha; subst hb; exact absurd hab (lt_irrefl _)
    · subst ha; subst hb; simp
    · subst ha; simp [hb, hab]
    · subst ha; simp [hb, hab]
    · subst hb; simp [ha, hab]
    · subst hb; simp [ha, hab]
    · simp [ha, hb, hab]
    · simp [ha, hb, hab]
  simp_rw [e1]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if b = i then (if a < i then G (Y a - Y i) else 0) else 0)]
  have s1 : ∀ x : Fin N, (∑ x_1 : Fin N, if x = i then (if i < x_1 then G (Y i - Y x_1) else 0) else 0) =
      if x = i then ∑ x_1 : Fin N, (if i < x_1 then G (Y i - Y x_1) else 0) else 0 := by
    intro x; split_ifs <;> simp
  have s2 : ∀ y : Fin N, (∑ x : Fin N, if y = i then (if x < i then G (Y x - Y i) else 0) else 0) =
      if y = i then ∑ x : Fin N, (if x < i then G (Y x - Y i) else 0) else 0 := by
    intro y; split_ifs <;> simp
  simp_rw [s1, s2]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have e2 : ∀ j : Fin N, (if j < i then G (Y j - Y i) else 0) = (if j < i then -G (Y i - Y j) else 0) := by
    intro j
    by_cases h : j < i
    · simp only [h, ite_true]
      have : Y j - Y i = -(Y i - Y j) := by abel
      rw [this, hG]
    · simp [h]
  simp_rw [e2]
  have e3 : Finset.univ.erase i = Finset.univ.filter (fun j => j ≠ i) := by
    ext j; simp
  rw [e3, Finset.sum_filter, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.2 h.le, h.ne']
  · subst h; simp
  · simp [h, not_lt.2 h.le, h.ne]

/-- `∂_{ik}H`, the `k`-th component of the drift `∇V(x_i) + N⁻¹∑_{j≠i}∇g(x_i-x_j)`. -/
def Bik (d : ℕ) (s : ℝ) (V : Torus d → ℝ) {N : ℕ} (i : Fin N) (k : Fin d) (Y : Config d N) : ℝ :=
  (Torus.grad V (Y i)) k +
    (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (periodicRieszGrad d s (Y i - Y j)) k

theorem q84d_mk_neg (x : Euc d) : Torus.mk (-x) = -Torus.mk x := by
  funext a; simp [Torus.mk]

theorem q84d_line_diff (i : Fin N) (k : Fin d) (Y : Config d N) (τ : ℝ) (a b : Fin N) :
    (lineCfg i k Y τ) a - (lineCfg i k Y τ) b = (Y a - Y b) +
      Torus.mk ((((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0)) * τ) • ek k) := by
  rw [lineCfg_eq_add]
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases ha : a = i <;> by_cases hb : b = i
  · simp only [ha, hb, ite_true, sub_self, zero_mul, zero_smul, q84d_mk_zero]
    abel
  · simp only [ha, hb, ite_true, ite_false, sub_zero, one_mul]
    abel
  · simp only [ha, hb, ite_true, ite_false, zero_sub]
    rw [show (-1 * τ) • ek k = -(τ • ek k) by rw [neg_one_mul, neg_smul], q84d_mk_neg]
    abel
  · simp only [ha, hb, ite_false, sub_self, zero_mul, zero_smul, q84d_mk_zero]
    abel

theorem q84d_H_line_deriv (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ}
    (hV : Torus.IsSmooth V) (Y : Config d N) (hY : ∀ a b : Fin N, a ≠ b → Y a ≠ Y b)
    (i : Fin N) (k : Fin d) :
    HasDerivAt (fun τ : ℝ => canonicalHamiltonian (periodicRiesz d s) V (lineCfg i k Y τ))
      (Bik d s V i k Y) 0 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hfun : (fun τ : ℝ => canonicalHamiltonian (periodicRiesz d s) V (lineCfg i k Y τ)) =
      fun τ => (∑ a, V ((lineCfg i k Y τ) a)) +
        (1 / (N : ℝ)) * ∑ p ∈ pairsN N, periodicRiesz d s
          ((lineCfg i k Y τ) p.1 - (lineCfg i k Y τ) p.2) := by
    funext τ; exact q84d_H_eq _ _ _
  rw [hfun]
  -- the potential part
  have hVd : DifferentiableAt ℝ (fun u : Euc d => V (Y i + Torus.mk u)) 0 := by
    rw [q84d_slice_eq]
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) := hV
    exact ((hc.differentiable (by norm_num)) _).comp 0 (differentiableAt_id.const_add _)
  have hVline : HasDerivAt (fun τ : ℝ => V ((lineCfg i k Y τ) i)) ((Torus.grad V (Y i)) k) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => τ • ek k) (ek k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (ek k)
    have hF0 : HasFDerivAt (fun u : Euc d => V (Y i + Torus.mk u))
        (fderiv ℝ (fun u : Euc d => V (Y i + Torus.mk u)) 0) ((fun τ : ℝ => τ • ek k) 0) := by
      simpa using hVd.hasFDerivAt
    have h2 := hF0.comp_hasDerivAt (0 : ℝ) h1
    have e : (fun τ : ℝ => V ((lineCfg i k Y τ) i)) =
        (fun u : Euc d => V (Y i + Torus.mk u)) ∘ fun τ : ℝ => τ • ek k := by
      funext τ; simp [lineCfg]
    rw [e]
    convert h2 using 1
    rw [q84d_slice_grad_comp]
  have hVsum : HasDerivAt (fun τ : ℝ => ∑ a, V ((lineCfg i k Y τ) a))
      ((Torus.grad V (Y i)) k) 0 := by
    have : HasDerivAt (fun τ : ℝ => ∑ a, V ((lineCfg i k Y τ) a))
        (∑ a : Fin N, (if a = i then (Torus.grad V (Y i)) k else 0)) 0 := by
      refine HasDerivAt.fun_sum (fun a _ => ?_)
      by_cases h : a = i
      · subst h; simpa using hVline
      · simp only [h, ite_false]
        have : (fun τ : ℝ => V ((lineCfg i k Y τ) a)) = fun _ => V (Y a) := by
          funext τ; simp [lineCfg, Function.update_of_ne h]
        rw [this]; exact hasDerivAt_const _ _
    simpa using this
  -- the interaction part
  have hpair : ∀ p ∈ pairsN N, HasDerivAt (fun τ : ℝ => periodicRiesz d s
      ((lineCfg i k Y τ) p.1 - (lineCfg i k Y τ) p.2))
      ((((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0)) *
        (periodicRieszGrad d s (Y p.1 - Y p.2)) k)) 0 := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [pairsN] using hp
    have hz : Y p.1 - Y p.2 ≠ 0 := sub_ne_zero.2 (hY _ _ hlt.ne)
    have := q84d_g_line_deriv hd hs0 hsd hz k
      ((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0))
    have e : (fun τ : ℝ => periodicRiesz d s ((lineCfg i k Y τ) p.1 - (lineCfg i k Y τ) p.2)) =
        fun τ => periodicRiesz d s ((Y p.1 - Y p.2) + Torus.mk
          ((((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0)) * τ) • ek k)) := by
      funext τ; rw [q84d_line_diff]
    rw [e]; exact this
  have hsum := HasDerivAt.fun_sum hpair
  have hid := q84d_pair_sum_identity (fun z => (periodicRieszGrad d s z) k)
    (fun z => by simp [HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]) Y i
  have h3 := (hVsum.add (hsum.const_mul (1 / (N : ℝ))))
  convert h3 using 1
  unfold Bik
  rw [← hid]

end HRS.Q84d

end
