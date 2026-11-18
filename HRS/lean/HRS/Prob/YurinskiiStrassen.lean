import Mathlib

/-!
# Strassen's coupling theorem (finite and Euclidean versions)

Helper for Lemma A.37 `M:B:lem:yurinskii` (Yurinskii's coupling), package METR-04.

Plan of the whole proof of `yurinskii_coupling` (Pollard 2002, Ch. 10 §4):

1. (this file) **Strassen**: if `μ(F) ≤ ν(F^r) + ε` for every closed `F ⊆ ℝⁿ`
   (`F^r` the closed `r`-thickening), there is a coupling `π` of `(μ, ν)` with
   `π(|x-y| > r) ≤ ε`.  Proved by finite transport duality (Hahn–Banach, layer-cake),
   discretisation on a grid and Prokhorov compactness of the couplings.
2. (`YurinskiiLindeberg.lean`) Lindeberg replacement of `ξ_i` by independent centred Gaussians
   with the same covariance, for test functions `F ∈ C²` whose Hessian is Lipschitz in the
   quadratic-form sense; `|E F(S) - E F(Z)| ≤ K (1+√3) L`.
3. (in `Metrics.lean`) Gaussian smoothing `F = gsmooth σ f` of the Lipschitz cut-off
   `f = max 0 (δ - dist(·, A^δ))`; `K = 2/σ²`; Gaussian tail via the Chernoff bound
   `P(|σ N| > δ) ≤ 2^{n/2} e^{-δ²/(4σ²)}`; choice `δ²/σ² = 2n + 4 log(1/B)` yields
   `μ(A) ≤ ν(A^{3δ}) + 24 B (1 + log(1/B)/n)`.  Strassen then gives the coupling.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Pointwise

namespace HRS.Yurinskii

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability vectors on pairs. -/
def pairSimplex (ι : Type*) [Fintype ι] : Set (ι × ι → ℝ) := {π | (∀ q, 0 ≤ π q) ∧ ∑ q, π q = 1}

lemma pairSimplex_convex : Convex ℝ (pairSimplex ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun q => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 q)) (mul_nonneg hb (hy.1 q))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2, hy.2]
    linarith

lemma pairSimplex_compact : IsCompact (pairSimplex ι) := by
  refine (isCompact_Icc (a := (0 : ι × ι → ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {π : ι × ι → ℝ | ∀ q, 0 ≤ π q} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun q => isClosed_le (f := fun _ : ι × ι → ℝ => (0 : ℝ))
        (g := fun π => π q) continuous_const (continuous_apply q)
    have h2 : IsClosed {π : ι × ι → ℝ | ∑ q, π q = 1} :=
      isClosed_eq (continuous_finset_sum _ fun q _ => continuous_apply q) continuous_const
    exact h1.inter h2
  · rintro π ⟨h0, h1⟩
    refine ⟨fun q => h0 q, fun q => ?_⟩
    show π q ≤ 1
    rw [← h1]
    exact Finset.single_le_sum (f := fun q => π q) (fun q _ => h0 q) (Finset.mem_univ q)

lemma functional_decomp (φ : ((ι ⊕ ι ⊕ Unit) → ℝ) →L[ℝ] ℝ) (v : (ι ⊕ ι ⊕ Unit) → ℝ) :
    φ v = ∑ k, v (Sum.inl k) * φ (Pi.single (Sum.inl k) 1) +
      ∑ l, v (Sum.inr (Sum.inl l)) * φ (Pi.single (Sum.inr (Sum.inl l)) 1) +
      v (Sum.inr (Sum.inr ())) * φ (Pi.single (Sum.inr (Sum.inr ())) 1) := by
  have := φ.toLinearMap.pi_apply_eq_sum_univ v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hs : ∀ x : ι ⊕ ι ⊕ Unit, (fun j => if x = j then (1:ℝ) else 0) = Pi.single x 1 := by
    intro x; ext j; simp [Pi.single_apply, eq_comm]
  simp only [hs]
  rw [add_assoc]

lemma single_rowsum (k l k' : ι) :
    ∑ l', (Pi.single (k, l) (1:ℝ) : ι × ι → ℝ) (k', l') = if k' = k then 1 else 0 := by
  by_cases h : k' = k
  · subst h
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ hl'; simp [Pi.single_apply, hl']
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun l' _ => by simp [Pi.single_apply, h]

lemma single_colsum (k l l' : ι) :
    ∑ k', (Pi.single (k, l) (1:ℝ) : ι × ι → ℝ) (k', l') = if l' = l then 1 else 0 := by
  by_cases h : l' = l
  · subst h
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'; simp [Pi.single_apply, hk']
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun k' _ => by simp [Pi.single_apply, h]

lemma single_cost (c : ι → ι → ℝ) (k l : ι) :
    ∑ q, (Pi.single (k, l) (1:ℝ) : ι × ι → ℝ) q * c q.1 q.2 = c k l := by
  rw [Finset.sum_eq_single (k, l)]
  · simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp

lemma single_mem (k l : ι) : (Pi.single (k, l) (1 : ℝ) : ι × ι → ℝ) ∈ pairSimplex ι := by
  refine ⟨fun q => ?_, ?_⟩
  · by_cases h : q = (k, l) <;> simp [Pi.single_apply, h]
  · simp

/-- Finite transport duality for a general cost matrix. -/
lemma finite_transport_gen (c : ι → ι → ℝ) (a b : ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hsa : ∑ k, a k = 1) (hsb : ∑ k, b k = 1)
    (S : ℝ)
    (hS : ∀ F G : ι → ℝ, (∀ k l, F k + G l < c k l) → ∑ k, F k * a k + ∑ l, G l * b l ≤ S)
    (η : ℝ) (hη : 0 < η) :
    ∃ π ∈ pairSimplex ι, (∀ k, ∑ l, π (k, l) = a k) ∧
      (∀ l, ∑ k, π (k, l) = b l) ∧ ∑ q, π q * c q.1 q.2 ≤ S + η := by
  by_contra hno
  push Not at hno
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsa
  obtain ⟨k0⟩ := hne
  let Ψl : (ι × ι → ℝ) →ₗ[ℝ] ((ι ⊕ ι ⊕ Unit) → ℝ) :=
    { toFun := fun π => Sum.elim (fun k => ∑ l, π (k, l)) (Sum.elim (fun l => ∑ k, π (k, l))
        (fun _ => ∑ q, π q * c q.1 q.2))
      map_add' := by
        intro x y; ext i; rcases i with k | l | u <;> simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c x; ext i; rcases i with k | l | u <;> simp [Finset.mul_sum, mul_assoc] }
  have hΨc : Continuous Ψl := LinearMap.continuous_of_finiteDimensional Ψl
  let R : Set ((ι ⊕ ι ⊕ Unit) → ℝ) := {v | (∀ k, v (Sum.inl k) = 0) ∧
    (∀ l, v (Sum.inr (Sum.inl l)) = 0) ∧ 0 ≤ v (Sum.inr (Sum.inr ()))}
  have hRc : IsClosed R := by
    have : R = (⋂ k, {v : (ι ⊕ ι ⊕ Unit) → ℝ | v (Sum.inl k) = 0}) ∩
        ((⋂ l, {v : (ι ⊕ ι ⊕ Unit) → ℝ | v (Sum.inr (Sum.inl l)) = 0}) ∩
          {v | 0 ≤ v (Sum.inr (Sum.inr ()))}) := by
      ext v; simp [R]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun k => ?_) (IsClosed.inter (isClosed_iInter fun l => ?_) ?_)
    · exact isClosed_eq (continuous_apply _) continuous_const
    · exact isClosed_eq (continuous_apply _) continuous_const
    · exact isClosed_le continuous_const (continuous_apply _)
  have hRv : Convex ℝ R := by
    intro x hx y hy c d hc hd hcd
    refine ⟨fun k => ?_, fun l => ?_, ?_⟩
    · simp [hx.1 k, hy.1 k]
    · simp [hx.2.1 l, hy.2.1 l]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hc hx.2.2) (mul_nonneg hd hy.2.2)
  let K := Ψl '' pairSimplex ι + R
  have hKc : IsClosed K := hRc.add_left_of_isCompact ((pairSimplex_compact).image hΨc)
  have hKv : Convex ℝ K := ((pairSimplex_convex).linear_image Ψl).add hRv
  let P : (ι ⊕ ι ⊕ Unit) → ℝ := Sum.elim a (Sum.elim b (fun _ => S + η))
  have hP : P ∉ K := by
    rintro ⟨_, ⟨π, hπ, rfl⟩, r, hr, hPe⟩
    have e1 : ∀ k, ∑ l, π (k, l) = a k := fun k => by
      have := congrFun hPe (Sum.inl k); simpa [P, Ψl, hr.1 k] using this
    have e2 : ∀ l, ∑ k, π (k, l) = b l := fun l => by
      have := congrFun hPe (Sum.inr (Sum.inl l)); simpa [P, Ψl, hr.2.1 l] using this
    have e3 := congrFun hPe (Sum.inr (Sum.inr ()))
    simp only [P, Ψl, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Sum.elim_inr] at e3
    have := hno π hπ e1 e2
    have := hr.2.2
    linarith
  obtain ⟨φ, u, hφP, hφK⟩ := geometric_hahn_banach_point_closed hKv hKc hP
  set f : ι → ℝ := fun k => φ (Pi.single (Sum.inl k) 1) with hf
  set g : ι → ℝ := fun l => φ (Pi.single (Sum.inr (Sum.inl l)) 1) with hg
  set lam : ℝ := φ (Pi.single (Sum.inr (Sum.inr ())) 1) with hlam
  have hdec : ∀ v, φ v = ∑ k, v (Sum.inl k) * f k + ∑ l, v (Sum.inr (Sum.inl l)) * g l +
      v (Sum.inr (Sum.inr ())) * lam := fun v => functional_decomp φ v
  have hval : ∀ π ∈ pairSimplex ι, ∀ s : ℝ, 0 ≤ s → u < (∑ k, (∑ l, π (k, l)) * f k +
      ∑ l, (∑ k, π (k, l)) * g l + (∑ q, π q * c q.1 q.2 + s) * lam) := by
    intro π hπ s hs
    have hm : Ψl π + (Pi.single (Sum.inr (Sum.inr ())) s : (ι ⊕ ι ⊕ Unit) → ℝ) ∈ K := by
      refine ⟨Ψl π, ⟨π, hπ, rfl⟩, Pi.single (Sum.inr (Sum.inr ())) s, ⟨?_, ?_, ?_⟩, rfl⟩
      · intro k; simp
      · intro l; simp
      · simpa using hs
    have := hφK _ hm
    rw [hdec] at this
    simpa [Ψl, Pi.single_apply] using this
  have hsingle : ∀ k l (s : ℝ), 0 ≤ s → u < f k + g l + (c k l + s) * lam := by
    intro k l s hs
    have := hval _ (single_mem k l) s hs
    simp only [single_rowsum, single_colsum, single_cost, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hlam0 : 0 ≤ lam := by
    by_contra hneg
    push Not at hneg
    set X := f k0 + g k0 + c k0 k0 * lam with hX
    have hs : 0 ≤ (|X - u| + 1) / (-lam) := div_nonneg (by positivity) (by linarith)
    have h1 := hsingle k0 k0 _ hs
    have e2 : (|X - u| + 1) / (-lam) * lam = -(|X - u| + 1) := by
      have : lam ≠ 0 := hneg.ne
      field_simp
    have h2 := le_abs_self (X - u)
    rw [add_mul, e2] at h1
    linarith
  have hφP' : ∑ k, a k * f k + ∑ l, b l * g l + (S + η) * lam < u := by
    have := hφP
    rw [hdec] at this
    simpa [P] using this
  have hlam : 0 < lam := by
    rcases hlam0.eq_or_lt with h0 | h0
    · exfalso
      have hπ : (fun q : ι × ι => a q.1 * b q.2) ∈ pairSimplex ι := by
        refine ⟨fun q => mul_nonneg (ha _) (hb _), ?_⟩
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, hsb, mul_one, hsa]
      have := hval _ hπ 0 le_rfl
      have r1 : ∀ k, ∑ l, a k * b l = a k := fun k => by rw [← Finset.mul_sum, hsb, mul_one]
      have r2 : ∀ l, ∑ k, a k * b l = b l := fun l => by rw [← Finset.sum_mul, hsa, one_mul]
      simp only [r1, r2, ← h0, mul_zero, add_zero] at this hφP'
      linarith
    · exact h0
  set F : ι → ℝ := fun k => -f k / lam with hF
  set G : ι → ℝ := fun l => -g l / lam with hG
  have hf' : ∀ k, f k = -lam * F k := fun k => by simp only [hF]; field_simp
  have hg' : ∀ l, g l = -lam * G l := fun l => by simp only [hG]; field_simp
  set D : ℝ := ∑ k, F k * a k + ∑ l, G l * b l with hD
  have hsa_f : ∑ k, a k * f k = -lam * ∑ k, F k * a k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [hf' k]; ring
  have hsb_g : ∑ l, b l * g l = -lam * ∑ l, G l * b l := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [hg' l]; ring
  have hFG : ∀ k l, F k + G l + (S + η) - D < c k l := by
    intro k l
    have h1 := hsingle k l 0 le_rfl
    rw [add_zero, hf' k, hg' l] at h1
    have key : lam * (F k + G l + (S + η) - D) < lam * c k l := by
      have e : lam * D = -(∑ k, a k * f k) - ∑ l, b l * g l := by
        rw [hsa_f, hsb_g, hD]; ring
      nlinarith
    exact lt_of_mul_lt_mul_left key hlam.le
  have hlow := hS (fun k => F k + (S + η) - D) G (fun k l => by linarith [hFG k l])
  have e : ∑ k, (F k + (S + η) - D) * a k = ∑ k, F k * a k + (S + η - D) := by
    have : ∀ k, (F k + (S + η) - D) * a k = F k * a k + (S + η - D) * a k := fun k => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hsa]; ring
  rw [e] at hlow
  have : ∑ k, F k * a k + (S + η - D) + ∑ l, G l * b l = S + η := by rw [hD]; ring
  linarith

lemma integral_ind_lt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (w : ℝ) :
    ∫ s in Set.Ioc (0:ℝ) 1, (Set.Iio x).indicator (fun _ => w) s = w * x := by
  rw [setIntegral_indicator measurableSet_Iio]
  have : Set.Ioc (0:ℝ) 1 ∩ Set.Iio x = Set.Ioo 0 x := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h0, _⟩, h2⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩; exact ⟨⟨h0, by linarith⟩, h2⟩
  rw [this, setIntegral_const, smul_eq_mul]
  simp [Measure.real, Real.volume_Ioo, hx0]
  ring

lemma integrableOn_ind (w x : ℝ) :
    IntegrableOn ((Set.Iio x).indicator (fun _ => w)) (Set.Ioc (0:ℝ) 1) := by
  have : IntegrableOn (fun _ : ℝ => w) (Set.Ioc (0:ℝ) 1) := integrableOn_const (by simp)
  exact this.indicator measurableSet_Iio

/-- Layer-cake step of Strassen's theorem: `0 ≤ g, h ≤ 1`, `g l ≤ h k` whenever `R k l`. -/
lemma layer_cake (a b : ι → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hsa : ∑ k, a k = 1) (hsb : ∑ k, b k = 1) (R : ι → ι → Prop) [DecidableRel R] (ε : ℝ)
    (hH : ∀ A : Finset ι, ∑ k ∈ A, a k ≤
      ∑ l ∈ Finset.univ.filter (fun l => ∃ k ∈ A, R k l), b l + ε)
    (g h : ι → ℝ) (hg0 : ∀ l, 0 ≤ g l) (hg1 : ∀ l, g l ≤ 1) (hh0 : ∀ k, 0 ≤ h k)
    (hh1 : ∀ k, h k ≤ 1) (hgh : ∀ k l, R k l → g l ≤ h k) :
    ∑ l, b l * g l - ∑ k, a k * h k ≤ ε := by
  classical
  have e1 : ∑ l, b l * g l = ∫ s in Set.Ioc (0:ℝ) 1,
      ∑ l, (Set.Iio (g l)).indicator (fun _ => b l) s := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_ind_lt _ (hg0 l) (hg1 l)]
    · intro l _
      exact integrableOn_ind _ _
  have e2 : ∑ k, a k * h k = ∫ s in Set.Ioc (0:ℝ) 1,
      ∑ k, (Set.Iio (h k)).indicator (fun _ => a k) s := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_ind_lt _ (hh0 k) (hh1 k)]
    · intro k _
      exact integrableOn_ind _ _
  have hI1 : IntegrableOn (fun s => ∑ l, (Set.Iio (g l)).indicator (fun _ => b l) s)
      (Set.Ioc (0:ℝ) 1) :=
    integrable_finsetSum _ fun l _ => integrableOn_ind _ _
  have hI2 : IntegrableOn (fun s => ∑ k, (Set.Iio (h k)).indicator (fun _ => a k) s)
      (Set.Ioc (0:ℝ) 1) :=
    integrable_finsetSum _ fun k _ => integrableOn_ind _ _
  rw [e1, e2, ← integral_sub hI1 hI2]
  have hpt : ∀ s : ℝ, ∑ l, (Set.Iio (g l)).indicator (fun _ => b l) s -
      ∑ k, (Set.Iio (h k)).indicator (fun _ => a k) s ≤ ε := by
    intro s
    set A : Finset ι := Finset.univ.filter (fun k => h k ≤ s) with hA
    have hH' := hH A
    have key1 : ∀ l, (Set.Iio (g l)).indicator (fun _ => b l) s ≤
        b l - (if ∃ k ∈ A, R k l then b l else 0) := by
      intro l
      by_cases hl : ∃ k ∈ A, R k l
      · have hl' := hl
        obtain ⟨k, hkA, hkR⟩ := hl
        have hks : h k ≤ s := by simpa [hA] using hkA
        have : ¬ s < g l := by have := hgh k l hkR; linarith
        simp [Set.indicator, this, hl']
      · simp [Set.indicator, hl]
        split_ifs <;> simp [hb l]
    have key2 : ∀ k, (Set.Iio (h k)).indicator (fun _ => a k) s =
        a k - (if h k ≤ s then a k else 0) := by
      intro k
      by_cases hk : h k ≤ s
      · have : ¬ s < h k := not_lt.2 hk
        simp [Set.indicator, this, hk]
      · have : s < h k := not_le.1 hk
        simp [Set.indicator, this, hk]
    have s1 : ∑ l, (Set.Iio (g l)).indicator (fun _ => b l) s ≤
        1 - ∑ l ∈ Finset.univ.filter (fun l => ∃ k ∈ A, R k l), b l := by
      calc _ ≤ ∑ l, (b l - (if ∃ k ∈ A, R k l then b l else 0)) :=
            Finset.sum_le_sum fun l _ => key1 l
        _ = _ := by
          rw [Finset.sum_sub_distrib, hsb, Finset.sum_filter]
    have s2 : ∑ k, (Set.Iio (h k)).indicator (fun _ => a k) s = 1 - ∑ k ∈ A, a k := by
      simp_rw [key2]
      rw [Finset.sum_sub_distrib, hsa, hA, Finset.sum_filter]
    rw [s2]
    linarith
  calc ∫ s in Set.Ioc (0:ℝ) 1, (∑ l, (Set.Iio (g l)).indicator (fun _ => b l) s -
        ∑ k, (Set.Iio (h k)).indicator (fun _ => a k) s) ≤ ∫ s in Set.Ioc (0:ℝ) 1, ε := by
        refine setIntegral_mono (hI1.sub hI2) (integrableOn_const (by simp)) fun s => hpt s
    _ = ε := by simp [Measure.real]

/-- Dual side of Strassen's theorem. -/
lemma dual_bound (a b : ι → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hsa : ∑ k, a k = 1) (hsb : ∑ k, b k = 1) (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ k, R k k) (ε : ℝ)
    (hH : ∀ A : Finset ι, ∑ k ∈ A, a k ≤
      ∑ l ∈ Finset.univ.filter (fun l => ∃ k ∈ A, R k l), b l + ε)
    (F G : ι → ℝ) (hFG : ∀ k l, F k + G l < if R k l then 0 else 1) :
    ∑ k, F k * a k + ∑ l, G l * b l ≤ ε := by
  classical
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsa
  obtain ⟨ks, hks⟩ := Finite.exists_max F
  set M := F ks with hM
  set h : ι → ℝ := fun k => min (M - F k) 1 with hh
  set g : ι → ℝ := fun l => max 0 (G l + M) with hg
  have hGM : ∀ l, G l + M < 1 := fun l => by
    have := hFG ks l
    split_ifs at this <;> linarith
  have hh0 : ∀ k, 0 ≤ h k := fun k => le_min (by linarith [hks k]) zero_le_one
  have hh1 : ∀ k, h k ≤ 1 := fun k => min_le_right _ _
  have hg0 : ∀ l, 0 ≤ g l := fun l => le_max_left _ _
  have hg1 : ∀ l, g l ≤ 1 := fun l => max_le zero_le_one (hGM l).le
  have hgh : ∀ k l, R k l → g l ≤ h k := by
    intro k l hkl
    refine max_le (hh0 k) (le_min ?_ (hGM l).le)
    have := hFG k l
    rw [if_pos hkl] at this
    linarith
  have key := layer_cake a b ha hb hsa hsb R ε hH g h hg0 hg1 hh0 hh1 hgh
  have s1 : ∑ k, F k * a k ≤ M - ∑ k, a k * h k := by
    have : ∀ k, F k * a k ≤ M * a k - a k * h k := fun k => by
      have : h k ≤ M - F k := min_le_left _ _
      nlinarith [ha k]
    calc _ ≤ ∑ k, (M * a k - a k * h k) := Finset.sum_le_sum fun k _ => this k
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsa, mul_one]
  have s2 : ∑ l, G l * b l ≤ ∑ l, b l * g l - M := by
    have : ∀ l, G l * b l ≤ b l * g l - M * b l := fun l => by
      have : G l + M ≤ g l := le_max_right _ _
      nlinarith [hb l]
    calc _ ≤ ∑ l, (b l * g l - M * b l) := Finset.sum_le_sum fun l _ => this l
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsb, mul_one]
  linarith

/-- **Strassen's theorem, finite version.** -/
theorem finite_strassen (a b : ι → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hsa : ∑ k, a k = 1) (hsb : ∑ k, b k = 1) (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ k, R k k) (ε : ℝ)
    (hH : ∀ A : Finset ι, ∑ k ∈ A, a k ≤
      ∑ l ∈ Finset.univ.filter (fun l => ∃ k ∈ A, R k l), b l + ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ π ∈ pairSimplex ι, (∀ k, ∑ l, π (k, l) = a k) ∧ (∀ l, ∑ k, π (k, l) = b l) ∧
      ∑ q ∈ Finset.univ.filter (fun q : ι × ι => ¬ R q.1 q.2), π q ≤ ε + η := by
  classical
  obtain ⟨π, hπ, h1, h2, h3⟩ := finite_transport_gen (fun k l => if R k l then (0:ℝ) else 1) a b
    ha hb hsa hsb ε (fun F G hFG => dual_bound a b ha hb hsa hsb R hR ε hH F G hFG) η hη
  refine ⟨π, hπ, h1, h2, ?_⟩
  have : ∑ q ∈ Finset.univ.filter (fun q : ι × ι => ¬ R q.1 q.2), π q =
      ∑ q, π q * (if R q.1 q.2 then (0:ℝ) else 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : R q.1 q.2 <;> simp [h]
  rw [this]; exact h3

end Finite

section Euclid

variable {n : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- Grid rounding on the ball of radius `R`, zero outside. -/
def gridMap (s R : ℝ) (x : 𝔼) : 𝔼 :=
  if ‖x‖ ≤ R then WithLp.toLp 2 (fun i => s * (⌊x i / s⌋ : ℝ)) else 0

lemma measurable_gridMap (s R : ℝ) : Measurable (gridMap (n := n) s R) := by
  unfold gridMap
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ measurable_const
  refine (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp ?_
  refine Measurable.of_eval fun i => ?_
  have : Measurable fun x : 𝔼 => x i := by fun_prop
  have h1 : Measurable fun x : 𝔼 => ⌊x i / s⌋ := Int.measurable_floor.comp (this.div_const s)
  exact (Measurable.of_discrete (f := fun z : ℤ => s * (z : ℝ))).comp h1

lemma gridMap_coord_sub {s : ℝ} (hs : 0 < s) (x : 𝔼) (i : Fin n) :
    0 ≤ x i - s * (⌊x i / s⌋ : ℝ) ∧ x i - s * (⌊x i / s⌋ : ℝ) < s := by
  have h1 := Int.floor_le (x i / s)
  have h2 := Int.lt_floor_add_one (x i / s)
  constructor
  · have := (le_div_iff₀ hs).1 h1
    linarith
  · have := (div_lt_iff₀ hs).1 h2
    linarith

lemma norm_gridMap_sub_le {s R : ℝ} (hs : 0 < s) {x : 𝔼} (hx : ‖x‖ ≤ R) :
    ‖gridMap s R x - x‖ ≤ n * s := by
  unfold gridMap
  rw [if_pos hx]
  have h2 : ‖(WithLp.toLp 2 (fun i => s * (⌊x i / s⌋ : ℝ)) : 𝔼) - x‖ ^ 2 ≤ ((n : ℝ) * s) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, ((WithLp.toLp 2 (fun i => s * (⌊x i / s⌋ : ℝ)) : 𝔼) - x) i ^ 2
        ≤ ∑ _i : Fin n, s ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨h0, h1⟩ := gridMap_coord_sub hs x i
          simp only [PiLp.sub_apply]
          nlinarith
      _ = n * s ^ 2 := by simp
      _ ≤ ((n : ℝ) * s) ^ 2 := by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simp
          · have : (1 : ℝ) ≤ n := by exact_mod_cast h
            nlinarith [sq_nonneg s]
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2

lemma finite_range_gridMap {s : ℝ} (hs : 0 < s) (R : ℝ) :
    (Set.range (gridMap (n := n) s R)).Finite := by
  set K : ℤ := ⌈|R| / s⌉ + 1 with hK
  have hfin : (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-K) K)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  have himg := (hfin.image (fun j : Fin n → ℤ => (WithLp.toLp 2 (fun i => s * (j i : ℝ)) : 𝔼)))
  refine (himg.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  unfold gridMap
  split_ifs with hx
  · right
    refine ⟨fun i => ⌊x i / s⌋, fun i _ => ?_, rfl⟩
    have hxi : |x i| ≤ R := (by
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      linarith : |x i| ≤ R)
    have hR : |x i / s| ≤ |R| / s := by
      rw [abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right (hxi.trans (le_abs_self R)) hs.le
    have hc := Int.le_ceil (|R| / s)
    have h1 := Int.floor_le (x i / s)
    have h2 := Int.lt_floor_add_one (x i / s)
    have h3 := abs_le.1 hR
    constructor
    · have : (-(K : ℝ)) ≤ (⌊x i / s⌋ : ℝ) := by
        have : ((⌈|R| / s⌉ : ℤ) : ℝ) ≥ |R| / s := hc
        rw [hK]; push_cast; linarith
      exact_mod_cast this
    · have : ((⌊x i / s⌋ : ℤ) : ℝ) ≤ K := by
        have : ((⌈|R| / s⌉ : ℤ) : ℝ) ≥ |R| / s := hc
        rw [hK]; push_cast; linarith
      exact_mod_cast this
  · left; rfl

lemma exists_discretization (η R : ℝ) (hη : 0 < η) :
    ∃ T : 𝔼 → 𝔼, Measurable T ∧ (Set.range T).Finite ∧ (∀ x, ‖x‖ ≤ R → ‖T x - x‖ ≤ η) ∧
      (∀ x, ‖T x‖ ≤ ‖x‖ + η) := by
  set s : ℝ := η / (n + 1) with hs
  have hs0 : 0 < s := by positivity
  refine ⟨gridMap s R, measurable_gridMap s R, finite_range_gridMap hs0 R, fun x hx => ?_,
    fun x => ?_⟩
  · refine (norm_gridMap_sub_le hs0 hx).trans ?_
    rw [hs, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  · by_cases hx : ‖x‖ ≤ R
    · have h := norm_gridMap_sub_le hs0 hx
      have h' : (n : ℝ) * s ≤ η := by
        rw [hs, ← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
      calc ‖gridMap s R x‖ = ‖(gridMap s R x - x) + x‖ := by congr 1; abel
        _ ≤ ‖gridMap s R x - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + η := by linarith
    · simp [gridMap, hx]; positivity


/-- Strassen's theorem for finitely supported measures. -/
theorem discrete_coupling (μ' ν' : Measure 𝔼) [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (V : Finset 𝔼) (hμV : μ' (V : Set 𝔼)ᶜ = 0) (hνV : ν' (V : Set 𝔼)ᶜ = 0) (r' ε : ℝ)
    (hr' : 0 ≤ r') (hε : 0 ≤ ε)
    (hH : ∀ A : Finset 𝔼, A ⊆ V → μ' (A : Set 𝔼) ≤
      ν' ((V.filter (fun y => ∃ x ∈ A, dist x y ≤ r') : Finset 𝔼) : Set 𝔼) + ENNReal.ofReal ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ π : Measure (𝔼 × 𝔼), IsProbabilityMeasure π ∧ π.map Prod.fst = μ' ∧
      π.map Prod.snd = ν' ∧ π {p | r' < dist p.1 p.2} ≤ ENNReal.ofReal (ε + η) := by
  classical
  -- index type
  let a : V → ℝ := fun k => (μ' {k.1}).toReal
  let b : V → ℝ := fun k => (ν' {k.1}).toReal
  have hμ1 : μ' (V : Set 𝔼) = 1 := by
    have := measure_add_measure_compl (μ := μ') (s := (V : Set 𝔼)) V.measurableSet
    rw [hμV, add_zero] at this; simpa using this
  have hν1 : ν' (V : Set 𝔼) = 1 := by
    have := measure_add_measure_compl (μ := ν') (s := (V : Set 𝔼)) V.measurableSet
    rw [hνV, add_zero] at this; simpa using this
  have hsum : ∀ (m : Measure 𝔼) [IsProbabilityMeasure m], m (V : Set 𝔼) = 1 →
      ∑ k : V, (m {k.1}).toReal = 1 := by
    intro m _ h1
    have h := sum_measure_singleton (μ := m) (s := V)
    rw [h1] at h
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)]
    rw [show (∑ k : V, m {k.1}) = ∑ x ∈ V, m {x} from Finset.sum_coe_sort V (fun x => m {x})]
    rw [h]; simp
  have hsa : ∑ k, a k = 1 := hsum μ' hμ1
  have hsb : ∑ k, b k = 1 := hsum ν' hν1
  have ha : ∀ k, 0 ≤ a k := fun k => ENNReal.toReal_nonneg
  have hb : ∀ k, 0 ≤ b k := fun k => ENNReal.toReal_nonneg
  -- the relation
  let R : V → V → Prop := fun k l => dist k.1 l.1 ≤ r'
  have hRrefl : ∀ k, R k k := fun k => by simp [R, hr']
  -- finset mass formula
  have hmass : ∀ (m : Measure 𝔼) (A : Finset V),
      m ((A.map (Function.Embedding.subtype _) : Finset 𝔼) : Set 𝔼) = ∑ k ∈ A, m {k.1} := by
    intro m A
    rw [← sum_measure_singleton (μ := m), Finset.sum_map]
    rfl
  have hH' : ∀ A : Finset V, ∑ k ∈ A, a k ≤
      ∑ l ∈ Finset.univ.filter (fun l => ∃ k ∈ A, R k l), b l + ε := by
    intro A
    have h1 := hH (A.map (Function.Embedding.subtype _)) (by
      intro x hx; simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨k, _, rfl⟩ := hx; exact k.2)
    rw [hmass μ' A] at h1
    have h2 : ((V.filter (fun y => ∃ x ∈ A.map (Function.Embedding.subtype _), dist x y ≤ r') : Finset 𝔼) : Set 𝔼) =
        (((Finset.univ.filter (fun l : V => ∃ k ∈ A, R k l)).map (Function.Embedding.subtype _) : Finset 𝔼) : Set 𝔼) := by
      ext y
      simp only [Finset.coe_filter, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_setOf_eq,
        Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and, Finset.mem_map, R]
      constructor
      · rintro ⟨hy, x, ⟨k, hk, rfl⟩, hd⟩
        exact ⟨⟨y, hy⟩, ⟨k, hk, hd⟩, rfl⟩
      · rintro ⟨l, ⟨k, hk, hd⟩, rfl⟩
        exact ⟨l.2, k.1, ⟨k, hk, rfl⟩, hd⟩
    rw [h2, hmass ν'] at h1
    have h3 : (∑ k ∈ A, μ' {k.1}) ≤ (∑ l ∈ Finset.univ.filter (fun l : V => ∃ k ∈ A, R k l), ν' {l.1}) + ENNReal.ofReal ε := h1
    have h4 := ENNReal.toReal_mono (by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 (fun _ _ => measure_ne_top _ _), ENNReal.ofReal_ne_top⟩) h3
    rw [ENNReal.toReal_add (ENNReal.sum_ne_top.2 (fun _ _ => measure_ne_top _ _)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ENNReal.toReal_ofReal hε] at h4
    exact h4
  obtain ⟨π, hπ, h1, h2, h3⟩ := finite_strassen a b ha hb hsa hsb R hRrefl ε hH' η hη
  have hπ0 : ∀ q, 0 ≤ π q := hπ.1
  let πm : Measure (𝔼 × 𝔼) :=
    ∑ q : V × V, ENNReal.ofReal (π q) • Measure.dirac ((q.1.1, q.2.1) : 𝔼 × 𝔼)
  have hpt : ∀ S : Set (𝔼 × 𝔼), MeasurableSet S → πm S =
      ∑ q : V × V, ENNReal.ofReal (π q) * S.indicator 1 ((q.1.1, q.2.1) : 𝔼 × 𝔼) := by
    intro S hS
    simp only [πm, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hS, smul_eq_mul]
  have hfin : ∀ (m : Measure 𝔼), m (V : Set 𝔼)ᶜ = 0 → ∀ S : Set 𝔼, MeasurableSet S →
      m S = ∑ k : V, S.indicator (1 : 𝔼 → ℝ≥0∞) k.1 * m {k.1} := by
    intro m hm S hS
    rw [← measure_inter_conull hm (s := S)]
    have : S ∩ (V : Set 𝔼) = ((V.filter (fun x => x ∈ S) : Finset 𝔼) : Set 𝔼) := by
      ext x; simp [and_comm]
    rw [this, ← sum_measure_singleton, Finset.sum_filter,
      ← Finset.sum_coe_sort V (fun x => if x ∈ S then m {x} else 0)]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.1 ∈ S <;> simp [Set.indicator, hk]
  have hP : πm Set.univ = 1 := by
    rw [hpt _ MeasurableSet.univ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => hπ0 q), hπ.2]; simp
  refine ⟨πm, ⟨hP⟩, ?_, ?_, ?_⟩
  · refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply measurable_fst hS, hpt _ (measurable_fst hS), hfin μ' hμV S hS,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ l : V, (Prod.fst ⁻¹' S).indicator (1 : 𝔼 × 𝔼 → ℝ≥0∞) ((k.1, l.1) : 𝔼 × 𝔼) =
        S.indicator (1 : 𝔼 → ℝ≥0∞) k.1 := fun l => by
      by_cases hk : k.1 ∈ S <;> simp [Set.indicator, hk]
    simp_rw [e]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun l _ => hπ0 _), h1 k,
      mul_comm]
    congr 1
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  · refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply measurable_snd hS, hpt _ (measurable_snd hS), hfin ν' hνV S hS,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e : ∀ k : V, (Prod.snd ⁻¹' S).indicator (1 : 𝔼 × 𝔼 → ℝ≥0∞) ((k.1, l.1) : 𝔼 × 𝔼) =
        S.indicator (1 : 𝔼 → ℝ≥0∞) l.1 := fun k => by
      by_cases hk : l.1 ∈ S <;> simp [Set.indicator, hk]
    simp_rw [e]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hπ0 _), h2 l,
      mul_comm]
    congr 1
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  · have hS : MeasurableSet {p : 𝔼 × 𝔼 | r' < dist p.1 p.2} :=
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
    rw [hpt _ hS]
    have : ∀ q : V × V, ENNReal.ofReal (π q) *
        ({p : 𝔼 × 𝔼 | r' < dist p.1 p.2}).indicator 1 ((q.1.1, q.2.1) : 𝔼 × 𝔼) =
        if ¬ R q.1 q.2 then ENNReal.ofReal (π q) else 0 := by
      intro q
      by_cases hq : R q.1 q.2
      · have : ¬ (r' < dist q.1.1 q.2.1) := not_lt.2 hq
        simp [Set.indicator, this, hq]
      · have : r' < dist q.1.1 q.2.1 := not_le.1 hq
        simp [Set.indicator, this, hq]
    simp_rw [this]
    rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun q _ => hπ0 q)]
    exact ENNReal.ofReal_le_ofReal h3

lemma tendsto_tail (μ : Measure 𝔼) [IsFiniteMeasure μ] :
    Tendsto (fun r : ℝ => μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_norm_gt_of_isTightMeasureSet
    (isTightMeasureSet_singleton (μ := μ) (α := 𝔼))
  simpa using h

lemma exists_radius (μ : Measure 𝔼) [IsFiniteMeasure μ] (τ : ℝ) (hτ : 0 < τ) :
    ∃ R0 : ℝ, ∀ R, R0 ≤ R → μ {x | R < ‖x‖} ≤ ENNReal.ofReal τ := by
  have h := (tendsto_tail μ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hτ))
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.1 h
  exact ⟨R0, fun R hR => (hR0 R hR).le⟩

/-- Verification of the discrete Strassen hypothesis for the discretised measures. -/
lemma discrete_hyp (μ ν : Measure 𝔼) (r ε τ R η : ℝ) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (h : ∀ A : Set 𝔼, IsClosed A → μ A ≤ ν (Metric.cthickening r A) + ENNReal.ofReal ε)
    (T : 𝔼 → 𝔼) (hT : Measurable T) (hTfin : (Set.range T).Finite)
    (hTerr : ∀ x, ‖x‖ ≤ R → ‖T x - x‖ ≤ η)
    (hμR : μ {x | R < ‖x‖} ≤ ENNReal.ofReal τ) (hνR : ν {x | R < ‖x‖} ≤ ENNReal.ofReal τ)
    (A : Finset 𝔼) (hA : A ⊆ hTfin.toFinset) :
    (μ.map T) (A : Set 𝔼) ≤ (ν.map T)
      ((hTfin.toFinset.filter (fun y => ∃ x ∈ A, dist x y ≤ r + 2 * η) : Finset 𝔼) : Set 𝔼)
      + ENNReal.ofReal (ε + 2 * τ) := by
  classical
  rw [Measure.map_apply hT A.measurableSet, Measure.map_apply hT (Finset.measurableSet _)]
  set F : Set 𝔼 := Metric.cthickening η (A : Set 𝔼) with hF
  have hFc : IsClosed F := Metric.isClosed_cthickening
  have s1 : T ⁻¹' (A : Set 𝔼) ⊆ F ∪ {x | R < ‖x‖} := by
    intro x hx
    by_cases hxR : ‖x‖ ≤ R
    · left
      refine Metric.mem_cthickening_of_dist_le x (T x) η (A : Set 𝔼) hx ?_
      rw [dist_eq_norm, ← norm_neg, neg_sub]; exact hTerr x hxR
    · right; exact not_le.1 hxR
  have s2 : Metric.cthickening (r + η) (A : Set 𝔼) ⊆
      T ⁻¹' ((hTfin.toFinset.filter (fun y => ∃ x ∈ A, dist x y ≤ r + 2 * η) : Finset 𝔼) : Set 𝔼)
        ∪ {x | R < ‖x‖} := by
    intro x hx
    by_cases hxR : ‖x‖ ≤ R
    · left
      rw [(A.finite_toSet.isCompact).cthickening_eq_biUnion_closedBall (by linarith)] at hx
      simp only [Set.mem_iUnion, Metric.mem_closedBall, Finset.mem_coe, exists_prop] at hx
      obtain ⟨a, haA, hax⟩ := hx
      simp only [Set.mem_preimage, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]
      refine ⟨by simpa using Set.mem_range_self x, a, haA, ?_⟩
      have := hTerr x hxR
      rw [dist_comm] at hax
      have h3 : dist a (T x) ≤ dist a x + dist x (T x) := dist_triangle _ _ _
      have h4 : dist x (T x) ≤ η := by
        rw [dist_eq_norm, ← norm_neg, neg_sub]; exact this
      linarith
    · right; exact not_le.1 hxR
  have e1 : μ (T ⁻¹' (A : Set 𝔼)) ≤ μ F + ENNReal.ofReal τ :=
    (measure_mono s1).trans ((measure_union_le _ _).trans (add_le_add le_rfl hμR))
  have e2 : ν (Metric.cthickening (r + η) (A : Set 𝔼)) ≤
      ν (T ⁻¹' ((hTfin.toFinset.filter (fun y => ∃ x ∈ A, dist x y ≤ r + 2 * η) : Finset 𝔼) : Set 𝔼))
        + ENNReal.ofReal τ :=
    (measure_mono s2).trans ((measure_union_le _ _).trans (add_le_add le_rfl hνR))
  have e3 := h F hFc
  have e4 : ν (Metric.cthickening r F) ≤ ν (Metric.cthickening (r + η) (A : Set 𝔼)) :=
    measure_mono (by
      have := Metric.cthickening_cthickening_subset hr hη (A : Set 𝔼)
      exact this)
  calc μ (T ⁻¹' (A : Set 𝔼)) ≤ μ F + ENNReal.ofReal τ := e1
    _ ≤ (ν (Metric.cthickening r F) + ENNReal.ofReal ε) + ENNReal.ofReal τ := by gcongr
    _ ≤ ((ν (T ⁻¹' ((hTfin.toFinset.filter (fun y => ∃ x ∈ A, dist x y ≤ r + 2 * η) : Finset 𝔼) : Set 𝔼))
        + ENNReal.ofReal τ) + ENNReal.ofReal ε) + ENNReal.ofReal τ := by
          gcongr
          exact e4.trans e2
    _ = ν (T ⁻¹' ((hTfin.toFinset.filter (fun y => ∃ x ∈ A, dist x y ≤ r + 2 * η) : Finset 𝔼) : Set 𝔼))
        + ENNReal.ofReal (ε + 2 * τ) := by
          have : ENNReal.ofReal (ε + 2 * τ) =
              ENNReal.ofReal ε + ENNReal.ofReal τ + ENNReal.ofReal τ := by
            rw [show ε + 2 * τ = ε + τ + τ by ring, ENNReal.ofReal_add (by positivity) hτ,
              ENNReal.ofReal_add hε hτ]
          rw [this]; ring

/-- **Strassen's coupling theorem** on `ℝⁿ`: if `μ(F) ≤ ν(F^r) + ε` for all closed `F`, there is a
coupling with `π(|x-y| > r) ≤ ε`. -/
theorem strassen_coupling (μ ν : Measure 𝔼) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (h : ∀ A : Set 𝔼, IsClosed A → μ A ≤ ν (Metric.cthickening r A) + ENNReal.ofReal ε) :
    ∃ π : Measure (𝔼 × 𝔼), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      π {p | r < dist p.1 p.2} ≤ ENNReal.ofReal ε := by
  classical
  have hτ : ∀ m : ℕ, (0:ℝ) < 1 / ((m:ℝ) + 1) := fun m => by positivity
  choose R0μ hR0μ using fun m : ℕ => exists_radius μ _ (hτ m)
  choose R0ν hR0ν using fun m : ℕ => exists_radius ν _ (hτ m)
  set R : ℕ → ℝ := fun m => max (max (R0μ m) (R0ν m)) (m : ℝ) with hRdef
  have hRμ : ∀ m, μ {x | R m < ‖x‖} ≤ ENNReal.ofReal (1 / ((m:ℝ) + 1)) := fun m =>
    hR0μ m _ ((le_max_left _ _).trans (le_max_left _ _))
  have hRν : ∀ m, ν {x | R m < ‖x‖} ≤ ENNReal.ofReal (1 / ((m:ℝ) + 1)) := fun m =>
    hR0ν m _ ((le_max_right _ _).trans (le_max_left _ _))
  have hRm : ∀ m : ℕ, (m : ℝ) ≤ R m := fun m => le_max_right _ _
  choose T hTmeas hTfin hTerr hTnorm using
    fun m : ℕ => exists_discretization (1 / ((m:ℝ) + 1)) (R m) (hτ m)
  have hdisc : ∀ m : ℕ, ∃ π : Measure (𝔼 × 𝔼), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ.map (T m) ∧ π.map Prod.snd = ν.map (T m) ∧
      π {p | r + 2 * (1 / ((m:ℝ) + 1)) < dist p.1 p.2} ≤
        ENNReal.ofReal (ε + 3 * (1 / ((m:ℝ) + 1))) := by
    intro m
    have hsupp : ∀ (m' : Measure 𝔼), (m'.map (T m)) ((hTfin m).toFinset : Set 𝔼)ᶜ = 0 := by
      intro m'
      rw [Measure.map_apply (hTmeas m) (Finset.measurableSet _).compl]
      have : T m ⁻¹' ((hTfin m).toFinset : Set 𝔼)ᶜ = ∅ := by
        ext x; simp
      rw [this]; simp
    have hτm := hτ m
    obtain ⟨π, hπ, h1, h2, h3⟩ := discrete_coupling (μ.map (T m)) (ν.map (T m))
      (hTfin m).toFinset (hsupp μ)
      (hsupp ν)
      (r + 2 * (1 / ((m:ℝ) + 1))) (ε + 2 * (1 / ((m:ℝ) + 1))) (by positivity) (by positivity)
      (fun A hA => discrete_hyp μ ν r ε (1 / ((m:ℝ) + 1)) (R m) (1 / ((m:ℝ) + 1)) hr hτm.le hτm.le hε h
        (T m) (hTmeas m) (hTfin m) (hTerr m) (hRμ m) (hRν m) A hA)
      (1 / ((m:ℝ) + 1)) hτm
    refine ⟨π, hπ, h1, h2, h3.trans ?_⟩
    apply ENNReal.ofReal_le_ofReal
    linarith
  choose π hπprob hπ1 hπ2 hπ3 using hdisc
  let u : ℕ → ProbabilityMeasure (𝔼 × 𝔼) := fun m => ⟨π m, hπprob m⟩
  -- tightness of the marginals
  have hmargtight : ∀ (m' : Measure 𝔼) [IsProbabilityMeasure m'],
      IsTightMeasureSet (Set.range fun k : ℕ => m'.map (T k)) := by
    intro m' _
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt]
    have hlim : Tendsto (fun r : ℝ => m' {x | r - 1 < ‖x‖}) atTop (𝓝 0) :=
      (tendsto_tail m').comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id) |>.congr
        (fun r => by simp [sub_eq_add_neg])
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun r0 => ?_)
    rw [iSup_range]
    refine iSup_le fun k => ?_
    simp only
    rw [Measure.map_apply (hTmeas k) (measurableSet_lt measurable_const measurable_norm)]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    have h1 := hTnorm k x
    have h2 : 1 / ((k:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    linarith
  have htight : IsTightMeasureSet {((ρ : ProbabilityMeasure (𝔼 × 𝔼)) : Measure (𝔼 × 𝔼)) |
      ρ ∈ Set.range u} := by
    refine IsTightMeasureSet.prodMk ?_ ?_
    · refine (hmargtight μ).subset ?_
      rintro _ ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩
      exact ⟨m, (hπ1 m).symm⟩
    · refine (hmargtight ν).subset ?_
      rintro _ ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩
      exact ⟨m, (hπ2 m).symm⟩
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨P, -, hP⟩ := hcomp.exists_mapClusterPt (f := atTop) (u := u)
    (le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun m => subset_closure ⟨m, rfl⟩)))
  obtain ⟨φ, hφ, hφP⟩ := hP.tendsto_subseq
  have hTconv : ∀ x : 𝔼, Tendsto (fun k => T k x) atTop (𝓝 x) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
    have : ‖x‖ ≤ R k := (Nat.le_ceil _).trans ((Nat.cast_le.2 hk).trans (hRm k))
    exact hTerr k x this
  have hmarg : ∀ (m' : Measure 𝔼) [IsProbabilityMeasure m'] (pr : 𝔼 × 𝔼 → 𝔼),
      Continuous pr → (∀ k, (π k).map pr = m'.map (T k)) →
      ((P : Measure (𝔼 × 𝔼))).map pr = m' := by
    intro m' _ pr hpr hmap
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
      (((ProbabilityMeasure.continuous_map hpr).tendsto P).comp hφP) g
    have h2 : Tendsto (fun k => ∫ x, g (T (φ k) x) ∂m') atTop (𝓝 (∫ x, g x ∂m')) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun k => ?_)
        (integrable_const _) (fun k => Eventually.of_forall fun x => g.norm_coe_le_norm _)
        (Eventually.of_forall fun x => ?_)
      · exact (g.continuous.measurable.comp (hTmeas _)).aestronglyMeasurable
      · exact (g.continuous.tendsto x).comp ((hTconv x).comp hφ.tendsto_atTop)
    have h3 : ∀ k, ∫ x, g x ∂(((u (φ k)).map pr : ProbabilityMeasure 𝔼) : Measure 𝔼) =
        ∫ x, g (T (φ k) x) ∂m' := by
      intro k
      rw [ProbabilityMeasure.toMeasure_map]
      show ∫ x, g x ∂((π (φ k)).map pr) = _
      rw [hmap, integral_map (hTmeas _).aemeasurable g.continuous.aestronglyMeasurable]
    simp_rw [Function.comp_apply, h3] at h1
    simp only [ProbabilityMeasure.toMeasure_map] at h1
    exact tendsto_nhds_unique h1 h2
  have hfst : (P : Measure (𝔼 × 𝔼)).map Prod.fst = μ := hmarg μ Prod.fst continuous_fst hπ1
  have hsnd : (P : Measure (𝔼 × 𝔼)).map Prod.snd = ν := hmarg ν Prod.snd continuous_snd hπ2
  refine ⟨P, inferInstance, hfst, hsnd, ?_⟩
  -- the cost bound
  have hopen : ∀ j : ℕ, IsOpen {p : 𝔼 × 𝔼 | r + 1 / ((j:ℝ) + 1) < dist p.1 p.2} := fun j =>
    isOpen_lt continuous_const (by fun_prop)
  have hcost : ∀ j : ℕ, (P : Measure (𝔼 × 𝔼)) {p | r + 1 / ((j:ℝ) + 1) < dist p.1 p.2} ≤
      ENNReal.ofReal ε := by
    intro j
    refine ENNReal.le_of_forall_pos_le_add fun c hc _ => ?_
    have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hφP (hopen j)
    refine hlim.trans ?_
    have hev : ∀ᶠ k in atTop, ((u (φ k) : ProbabilityMeasure (𝔼 × 𝔼)) : Measure (𝔼 × 𝔼))
        {p | r + 1 / ((j:ℝ) + 1) < dist p.1 p.2} ≤ ENNReal.ofReal ε + (c : ℝ≥0∞) := by
      have h1 : ∀ᶠ k : ℕ in atTop, 3 * (1 / ((k:ℝ) + 1)) ≤ (c : ℝ) / 2 ∧
          2 * (1 / ((k:ℝ) + 1)) ≤ 1 / ((j:ℝ) + 1) := by
        have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have hc2 : (0:ℝ) < min ((c:ℝ) / 2) (1 / ((j:ℝ) + 1)) / 3 := by
          have : (0:ℝ) < c := by exact_mod_cast hc
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          positivity
        filter_upwards [h0.eventually (gt_mem_nhds hc2)] with k hk
        have := min_le_left ((c:ℝ) / 2) (1 / ((j:ℝ) + 1))
        have := min_le_right ((c:ℝ) / 2) (1 / ((j:ℝ) + 1))
        constructor <;> linarith
      filter_upwards [hφ.tendsto_atTop.eventually h1] with k ⟨hk1, hk2⟩
      refine (measure_mono (fun p hp => ?_)).trans ((hπ3 (φ k)).trans ?_)
      · simp only [Set.mem_setOf_eq] at hp ⊢
        linarith
      · calc ENNReal.ofReal (ε + 3 * (1 / ((φ k : ℝ) + 1))) ≤ ENNReal.ofReal (ε + c / 2) :=
              ENNReal.ofReal_le_ofReal (by linarith)
          _ ≤ ENNReal.ofReal ε + (c : ℝ≥0∞) := by
              rw [ENNReal.ofReal_add hε (by positivity)]
              gcongr
              rw [← ENNReal.ofReal_coe_nnreal]
              exact ENNReal.ofReal_le_ofReal (by linarith [c.coe_nonneg])
    exact liminf_le_of_frequently_le' hev.frequently
  have hunion : {p : 𝔼 × 𝔼 | r < dist p.1 p.2} =
      ⋃ j : ℕ, {p | r + 1 / ((j:ℝ) + 1) < dist p.1 p.2} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hp
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hp)
      exact ⟨j, by linarith⟩
    · rintro ⟨j, hj⟩
      have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone (fun j : ℕ => {p : 𝔼 × 𝔼 | r + 1 / ((j:ℝ) + 1) < dist p.1 p.2}) := by
    intro i j hij p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have : 1 / ((j:ℝ) + 1) ≤ 1 / ((i:ℝ) + 1) := by
      gcongr
    linarith
  rw [hunion, hmono.measure_iUnion]
  exact iSup_le hcost

end Euclid

end HRS.Yurinskii
