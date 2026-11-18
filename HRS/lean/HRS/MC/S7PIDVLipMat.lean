import HRS.MC.S7PIDVLip
import HRS.MC.S7PIDVMat
import HRS.MC.S7PIEMeas

/-!
# Packet PI-D, sub-packet V (helper): the Lipschitz estimate for the propagator matrix at integer levels

For `0 ≤ u ≤ s ≤ t ≤ T` the difference `Δ = pieT u t - pieT u s` of propagator matrices is the matrix of
`U^{u,s}(U^{s,t} - 1)` (cocycle).  With the shifted weights `w_j^{-2}` the integer-level bound
`‖U^{u,t}φ - U^{u,s}φ‖_{H^m} ≤ K (t - s) ‖φ‖_{H^{m+2}}` is the finite-section bound
`pieFinBd (pieWmat w (w^{-2} Δ) (m+2)) (K (t-s))` (`S7PIDV_lipMat`).  Also `pieT 0 0 = 1`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDV

open HRS HRS.PDE HRS.A33 HRS.MC.Sec7.PIE

variable {d : ℕ}

open Classical in
lemma S7PIDV_isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k.1 y) := by
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hlift : Torus.lift (Torus.realMode k) = fun y : Euc d =>
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Real.cos (2 * Real.pi * Lattice.dot k.1 y)
      else Real.sqrt 2 * Real.sin (2 * Real.pi * Lattice.dot k.1 y) := by
    funext y
    unfold Torus.lift Torus.realMode
    simp only [Function.comp, Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hlift]
  split_ifs
  · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hdot))

open Classical in
/-- `U^{0,0} = id` on the modes: the matrix `pieT 0 0` is the identity. -/
lemma S7PIDV_pieT_zero {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (j k : NonzeroLattice d) : pieT D μ 0 0 j k = if j = k then 1 else 0 := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  unfold pieT
  rw [prop_self_zero hd D.s D.hs0 D.hsd J Rg MB Λ VB D ν₀ T μ hA (S7PIDV_isSmooth_realMode k)]
  unfold Torus.funRealCoeff
  exact Torus.realMode_orthonormal j k

/-- finite-section bound of the identity-time matrix at any exponent -/
lemma S7PIDV_finBd_zero {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) (σ : ℝ) :
    pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ 0 0) σ) 1 := by
  classical
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have : pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ 0 0) σ =
      fun j k => if j = k then (1 : ℝ) else 0 := by
    funext j k
    simp only [pieWmat, S7PIDV_pieT_zero H]
    by_cases hjk : j = k
    · subst hjk
      simp only [if_true, mul_one]
      rw [← Real.rpow_add (hw j)]; simp
    · simp [hjk]
  rw [this]
  exact S7PIDV_finBd_id

/-- finite sums of the weighted squared coefficients are bounded by the Sobolev norm -/
lemma S7PIDV_sum_le_sob {g : Torus d → ℝ} {σ : ℝ} (hg : MemSobolev σ g) (Jf : Finset (NonzeroLattice d)) :
    ∑ j ∈ Jf, (Lattice.jp j.1 ^ σ * Torus.funRealCoeff g j) ^ 2 ≤ sobolevNorm σ g ^ 2 := by
  have hpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  obtain ⟨-, hsum⟩ := hg
  have h1 : ∑ j ∈ Jf, (Lattice.jp j.1 ^ σ * Torus.funRealCoeff g j) ^ 2 ≤
      ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * σ) * Torus.funRealCoeff g j ^ 2 := by
    refine (Finset.sum_le_sum fun j _ => le_of_eq ?_).trans
      (hsum.sum_le_tsum Jf fun j _ => mul_nonneg (Real.rpow_nonneg (hpos j).le _) (sq_nonneg _))
    rw [mul_pow, Torus.jp_rpow_sq]
  refine h1.trans ?_
  unfold sobolevNorm
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
  linarith [sq_nonneg (Torus.mean g)]

/-- the tail of the finite-section estimate: if the rows of `Δ ξ` are the coefficients of `g ∈ H^m` with
`‖g‖_{H^m}² ≤ Kc² ∑ x²`, then the shifted weighted matrix obeys the bound -/
lemma S7PIDV_finBd_tail (m : ℕ) (Δ : NonzeroLattice d → NonzeroLattice d → ℝ) (Kf Jf : Finset (NonzeroLattice d))
    (x : NonzeroLattice d → ℝ) (g : Torus d → ℝ) (Kc : ℝ) (hg : MemSobolev (m : ℝ) g)
    (hrow : ∀ j, ∑ k ∈ Kf, Δ j k * (Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k) = Torus.funRealCoeff g j)
    (hnorm : sobolevNorm (m : ℝ) g ^ 2 ≤ Kc ^ 2 * ∑ k ∈ Kf, x k ^ 2) :
    ∑ j ∈ Jf, (∑ k ∈ Kf, pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * Δ j k) ((m + 2 : ℕ) : ℝ) j k * x k) ^ 2 ≤
      Kc ^ 2 * ∑ k ∈ Kf, x k ^ 2 := by
  have hpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hrow' : ∀ j, ∑ k ∈ Kf, pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * Δ j k) ((m + 2 : ℕ) : ℝ) j k * x k =
      Lattice.jp j.1 ^ (m : ℝ) * Torus.funRealCoeff g j := by
    intro j
    rw [← hrow j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [pieWmat]
    have e : Lattice.jp j.1 ^ ((m + 2 : ℕ) : ℝ) * Lattice.jp j.1 ^ (-(2 : ℝ)) = Lattice.jp j.1 ^ (m : ℝ) := by
      rw [← Real.rpow_add (hpos j)]; congr 1; push_cast; ring
    calc Lattice.jp j.1 ^ ((m + 2 : ℕ) : ℝ) * (Lattice.jp j.1 ^ (-(2 : ℝ)) * Δ j k) *
          Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k
        = (Lattice.jp j.1 ^ ((m + 2 : ℕ) : ℝ) * Lattice.jp j.1 ^ (-(2 : ℝ))) *
          (Δ j k * (Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k)) := by ring
      _ = _ := by rw [e]
  simp_rw [hrow']
  exact (S7PIDV_sum_le_sob hg Jf).trans hnorm

/-- **Integer-level Lipschitz bound of the propagator matrix with the shifted weights.** -/
lemma S7PIDV_lipMat {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℕ) (hm : 1 ≤ m) (hmJ : m + 2 ≤ J) (hst : mStar d ≤ m + 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ T →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT D μ u t j k - pieT D μ u s j k))
        ((m + 2 : ℕ) : ℝ)) (K * (t - s)) := by
  classical
  have H' : PIEHyp (m + 2) D μ T := by
    obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
    exact ⟨hd, hst, Rg, MB, Λ, VB, ν₀, StabAux.adjointData_mono hmJ hA⟩
  obtain ⟨K1, hK1, hlip⟩ := S7PIDV_lip_fun m hm H'
  obtain ⟨C0, hC0, hlev⟩ := pie_level_bound H m hm (by omega)
  have hC1 : 0 ≤ max C0 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨max C0 1 * K1, mul_nonneg hC1 hK1, fun u s t hu hus hst' htT => ?_⟩
  rcases hst'.eq_or_lt with rfl | hlt
  · intro Kf Jf x
    simp [pieWmat]
  have hs0 : 0 ≤ s := hu.trans hus
  have ht : t ∈ Set.Ioc 0 T := ⟨hs0.trans_lt hlt, htT⟩
  have hut : u ∈ Set.Icc 0 t := ⟨hu, hus.trans hlt.le⟩
  have hst'' : s ∈ Set.Icc 0 t := ⟨hs0, hlt.le⟩
  intro Kf Jf x
  obtain ⟨ξ, hξ⟩ : ∃ ξ : NonzeroLattice d → ℝ,
      ξ = fun k => Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k := ⟨_, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : Torus d → ℝ, φ = pieComb Kf ξ := ⟨_, rfl⟩
  have hφJ : Dom J φ := by rw [hφdef]; exact pieDom_comb J Kf ξ
  have hφm : Dom (m + 2) φ := by rw [hφdef]; exact pieDom_comb (m + 2) Kf ξ
  obtain ⟨hmem1, hnorm1⟩ := hlip t ht s hst'' φ hφm
  have hφn : sobolevNorm ((m + 2 : ℕ) : ℝ) φ ^ 2 = ∑ k ∈ Kf, x k ^ 2 := by
    rw [hφdef, pieComb_sobolevNorm_sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hξ]
    rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1),
      show (2 * ((m + 2 : ℕ) : ℝ) + 2 * -((m + 2 : ℕ) : ℝ)) = 0 by ring, Real.rpow_zero, one_mul]
  have hnn : ∀ (σ : ℝ) (f : Torus d → ℝ), 0 ≤ sobolevNorm σ f := fun σ f => by
    unfold sobolevNorm; exact Real.sqrt_nonneg _
  obtain ⟨g, hgmem, hgrow, hgnorm⟩ : ∃ g : Torus d → ℝ, MemSobolev (m : ℝ) g ∧
      (∀ j, ∑ k ∈ Kf, (pieT D μ u t j k - pieT D μ u s j k) * ξ k = Torus.funRealCoeff g j) ∧
      sobolevNorm (m : ℝ) g ≤ max C0 1 * (K1 * (t - s) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ) := by
    have e : (fun x => propagator D μ s t φ x - φ x) =
        fun x => 1 * propagator D μ s t φ x + (-1) * φ x := by funext x; ring
    rw [e] at hmem1 hnorm1
    have hψJ : Dom J (propagator D μ s t φ) := pie_prop_dom H ht hst'' hφJ
    have hψc : Continuous (propagator D μ s t φ) := hψJ.1
    rcases hs0.eq_or_lt with h0 | hpos
    · -- s = 0, hence u = 0
      have hs_eq : s = 0 := h0.symm
      subst hs_eq
      have hu0 : u = 0 := le_antisymm hus hu
      subst hu0
      refine ⟨fun x => 1 * propagator D μ 0 t φ x + (-1) * φ x, hmem1, fun j => ?_, ?_⟩
      · have c1 : Torus.funRealCoeff (propagator D μ 0 t φ) j = ∑ k ∈ Kf, ξ k * pieT D μ 0 t j k := by
          rw [hφdef]; exact pie_coeff_comb H ht hut Kf ξ j
        have c2 : Torus.funRealCoeff φ j = ∑ k ∈ Kf, ξ k * pieT D μ 0 0 j k := by
          rw [hφdef, pieComb_coeff]
          simp only [S7PIDV_pieT_zero H, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq]
        rw [pie_funRealCoeff_lin hψc hφJ.1, c1, c2, one_mul, neg_one_mul, ← sub_eq_add_neg,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      · calc sobolevNorm (m : ℝ) (fun x => 1 * propagator D μ 0 t φ x + (-1) * φ x)
            ≤ K1 * (t - 0) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ := hnorm1
          _ ≤ max C0 1 * (K1 * (t - 0) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ) := by
              have h0' : 0 ≤ K1 * (t - 0) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ :=
                mul_nonneg (mul_nonneg hK1 (by linarith [ht.1])) (hnn _ _)
              nlinarith [le_max_right C0 1]
    · have hs : s ∈ Set.Ioc 0 T := ⟨hpos, hlt.le.trans htT⟩
      have hu' : u ∈ Set.Icc 0 s := ⟨hu, hus⟩
      have hχJ : Dom J (fun x => 1 * propagator D μ s t φ x + (-1) * φ x) := dom_closed hψJ hφJ 1 (-1)
      obtain ⟨hmem2, hnorm2⟩ := hlev s hs u hu' _ hχJ
      refine ⟨propagator D μ u s (fun x => 1 * propagator D μ s t φ x + (-1) * φ x), hmem2,
        fun j => ?_, ?_⟩
      · have hsg : propagator D μ u t φ = propagator D μ u s (propagator D μ s t φ) :=
          pie_prop_semigroup H ht hφJ hu hus hlt
        have c1 : Torus.funRealCoeff (propagator D μ u t φ) j = ∑ k ∈ Kf, ξ k * pieT D μ u t j k := by
          rw [hφdef]; exact pie_coeff_comb H ht hut Kf ξ j
        have c2 : Torus.funRealCoeff (propagator D μ u s φ) j = ∑ k ∈ Kf, ξ k * pieT D μ u s j k := by
          rw [hφdef]; exact pie_coeff_comb H hs hu' Kf ξ j
        have c3 := pie_T_sub_coeff H hs hu' hψJ hφJ j
        rw [← c3, ← hsg, c1, c2, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      · calc sobolevNorm (m : ℝ) (propagator D μ u s
              (fun x => 1 * propagator D μ s t φ x + (-1) * φ x))
            ≤ max C0 1 * sobolevNorm (m : ℝ) (fun x => 1 * propagator D μ s t φ x + (-1) * φ x) :=
              hnorm2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn _ _))
          _ ≤ _ := mul_le_mul_of_nonneg_left hnorm1 hC1
  have hgn2 : sobolevNorm (m : ℝ) g ^ 2 ≤ (max C0 1 * K1 * (t - s)) ^ 2 * ∑ k ∈ Kf, x k ^ 2 := by
    calc sobolevNorm (m : ℝ) g ^ 2
        ≤ (max C0 1 * (K1 * (t - s) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ)) ^ 2 :=
          pow_le_pow_left₀ (hnn _ _) hgnorm 2
      _ = (max C0 1 * K1 * (t - s)) ^ 2 * sobolevNorm ((m + 2 : ℕ) : ℝ) φ ^ 2 := by ring
      _ = _ := by rw [hφn]
  have hrow : ∀ j, ∑ k ∈ Kf, (fun j k => pieT D μ u t j k - pieT D μ u s j k) j k *
      (Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k) = Torus.funRealCoeff g j := by
    intro j
    rw [← hgrow j, hξ]
  exact S7PIDV_finBd_tail m (fun j k => pieT D μ u t j k - pieT D μ u s j k) Kf Jf x g _ hgmem hrow hgn2

end HRS.MC.Sec7.S7PIDV

end
