import HRS.MC.S7PIELip

/-!
# Packet PI-E, part 6: coordinatewise Lipschitz continuity of the propagator matrix

`pieT D μ u t j k` is Lipschitz in `t` (for `u ≤ s < t`, from the cocycle `propagator_semigroup` and the level-1 bound) and in
`u` (for `u' ≤ u ≤ t`), with constant `L ⟨k⟩^J` independent of `u, t, j`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33

variable {d : ℕ}

lemma pie_abs_coeff_le {χ : Torus d → ℝ} (hχ : MemSobolev (1 : ℝ) χ) (j : NonzeroLattice d) :
    |Torus.funRealCoeff χ j| ≤ sobolevNorm (1 : ℝ) χ := by
  have hpos : 0 < Lattice.jp j.1 := Torus.jp_pos j.1
  have h1 : Lattice.jp j.1 ^ (2 * (1 : ℝ)) * Torus.funRealCoeff χ j ^ 2 ≤
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * (1 : ℝ)) * Torus.funRealCoeff χ k ^ 2 :=
    hχ.2.le_tsum j fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hj1 : 1 ≤ Lattice.jp j.1 ^ (2 * (1 : ℝ)) := by
    refine Real.one_le_rpow ?_ (by norm_num)
    exact Torus.jp_ge_one j.1
  have h2 : Torus.funRealCoeff χ j ^ 2 ≤ sobolevNorm (1 : ℝ) χ ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
    nlinarith [sq_nonneg (Torus.mean χ), sq_nonneg (Torus.funRealCoeff χ j)]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (Real.sqrt_nonneg _))

lemma pie_funRealCoeff_lin {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ)
    (j : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => a * f x + b * g x) j =
      a * Torus.funRealCoeff f j + b * Torus.funRealCoeff g j := by
  unfold Torus.funRealCoeff
  have e : ∀ x : Torus d, Torus.realMode j x * (a * f x + b * g x) =
      a * (Torus.realMode j x * f x) + b * (Torus.realMode j x * g x) := fun x => by ring
  simp_rw [e]
  rw [integral_add, integral_const_mul, integral_const_mul]
  · exact (ClassicalAux.integrable_of_continuous ((Torus.continuous_realMode j).mul hf)).const_mul a
  · exact (ClassicalAux.integrable_of_continuous ((Torus.continuous_realMode j).mul hg)).const_mul b

lemma pie_sobolev_realMode (k : NonzeroLattice d) (n : ℝ) :
    sobolevNorm n (Torus.realMode k) ≤ Lattice.jp k.1 ^ n := by
  have h := pieComb_sobolevNorm_sq {k} (fun _ => 1) n
  rw [← pieComb_single] at h
  simp only [Finset.sum_singleton, one_pow, mul_one] at h
  have hnn : 0 ≤ sobolevNorm n (Torus.realMode k) := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hp : 0 ≤ Lattice.jp k.1 ^ n := Real.rpow_nonneg (Torus.jp_pos _).le _
  refine (sq_le_sq₀ hnn hp).1 (le_of_eq ?_)
  rw [h, Torus.jp_rpow_sq]

lemma pie_prop_dom {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) {φ : Torus d → ℝ} (hφ : Dom J φ) :
    Dom J (propagator D μ u t φ) := by
  have hJ1 : 1 ≤ J := by
    obtain ⟨hd, hJ, -⟩ := H
    have := ClassicalPart.three_le_mStar d
    omega
  obtain ⟨C, -, hC⟩ := pie_level_bound H J hJ1 le_rfl
  exact ⟨pie_prop_continuous H ht hu hφ, (hC t ht u hu φ hφ).1⟩

lemma pie_prop_lin {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) {φ ψ : Torus d → ℝ} (hφ : Dom J φ)
    (hψ : Dom J ψ) (α β : ℝ) :
    propagator D μ u t (fun x => α * φ x + β * ψ x) =
      fun x => α * propagator D μ u t φ x + β * propagator D μ u t ψ x := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  exact prop_lin hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht hφ hψ α β hu

lemma pie_prop_semigroup {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ} (hφ : Dom J φ) {r σ : ℝ} (hr : 0 ≤ r) (hrσ : r ≤ σ)
    (hσt : σ < t) :
    propagator D μ r t φ = propagator D μ r σ (propagator D μ σ t φ) := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  exact propagator_semigroup hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA t ht φ hφ.1 hφ.2 r σ hr hrσ hσt

/-- difference of two propagator matrix entries as the coefficient of the propagator of a difference -/
lemma pie_T_sub_coeff {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {s : ℝ} (hs : s ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 s) {ψ φ : Torus d → ℝ} (hψ : Dom J ψ)
    (hφ : Dom J φ) (j : NonzeroLattice d) :
    Torus.funRealCoeff (propagator D μ u s ψ) j - Torus.funRealCoeff (propagator D μ u s φ) j =
      Torus.funRealCoeff (propagator D μ u s (fun x => 1 * ψ x + (-1) * φ x)) j := by
  rw [pie_prop_lin H hs hu hψ hφ 1 (-1),
    pie_funRealCoeff_lin (pie_prop_continuous H hs hu hψ) (pie_prop_continuous H hs hu hφ)]
  ring

/-- Lipschitz bound in the terminal time. -/
lemma pie_T_lip_t {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u s t : ℝ, 0 ≤ u → u ≤ s → 0 < s → s < t → t ≤ T → ∀ j k : NonzeroLattice d,
      |pieT D μ u t j k - pieT D μ u s j k| ≤ L * (t - s) * Lattice.jp k.1 ^ (J : ℝ) := by
  have hJ1 : 1 ≤ J := by
    obtain ⟨hd, hJ, -⟩ := H
    have := ClassicalPart.three_le_mStar d
    omega
  obtain ⟨K, hK, hlip⟩ := pie_lip_fun H
  obtain ⟨C1, hC1, hlev⟩ := pie_level_bound H 1 le_rfl hJ1
  simp only [Nat.cast_one] at hlev
  refine ⟨C1 * K, mul_nonneg hC1 hK, fun u s t hu hus hs0 hst htT j k => ?_⟩
  have ht : t ∈ Set.Ioc 0 T := ⟨hs0.trans hst, htT⟩
  have hs : s ∈ Set.Ioc 0 T := ⟨hs0, hst.le.trans htT⟩
  have hust : u ∈ Set.Icc 0 t := ⟨hu, hus.trans hst.le⟩
  have hus' : u ∈ Set.Icc 0 s := ⟨hu, hus⟩
  have hst' : s ∈ Set.Icc 0 t := ⟨hs0.le, hst.le⟩
  have hφ : Dom J (Torus.realMode k) := pieDom_realMode J k
  have hψ : Dom J (propagator D μ s t (Torus.realMode k)) := pie_prop_dom H ht hst' hφ
  have hsg := pie_prop_semigroup H ht hφ hu hus hst
  have hχ : Dom J (fun x => 1 * propagator D μ s t (Torus.realMode k) x + (-1) * Torus.realMode k x) :=
    dom_closed hψ hφ 1 (-1)
  obtain ⟨hmem, hbd⟩ := hlev s hs u hus' _ hχ
  have hχn : sobolevNorm 1 (fun x => 1 * propagator D μ s t (Torus.realMode k) x + (-1) * Torus.realMode k x) ≤
      K * (t - s) * sobolevNorm (J : ℝ) (Torus.realMode k) := by
    have := (hlip t ht s hst' _ hφ).2
    have e : (fun x => 1 * propagator D μ s t (Torus.realMode k) x + (-1) * Torus.realMode k x) =
        fun x => propagator D μ s t (Torus.realMode k) x - Torus.realMode k x := by
      funext x; ring
    rw [e]; exact this
  have hcoef := pie_T_sub_coeff H hs hus' hψ hφ j
  have hTt : pieT D μ u t j k = Torus.funRealCoeff (propagator D μ u s
      (propagator D μ s t (Torus.realMode k))) j := by
    unfold pieT; rw [hsg]
  have hTs : pieT D μ u s j k = Torus.funRealCoeff (propagator D μ u s (Torus.realMode k)) j := rfl
  rw [hTt, hTs, hcoef]
  refine (pie_abs_coeff_le hmem j).trans (hbd.trans ?_)
  have h1 := mul_le_mul_of_nonneg_left hχn hC1
  have h2 := pie_sobolev_realMode k (J : ℝ)
  have hKt : 0 ≤ K * (t - s) := mul_nonneg hK (by linarith)
  calc C1 * sobolevNorm 1 _ ≤ C1 * (K * (t - s) * sobolevNorm (J : ℝ) (Torus.realMode k)) := h1
    _ ≤ C1 * (K * (t - s) * Lattice.jp k.1 ^ (J : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hKt) hC1
    _ = _ := by ring

/-- Lipschitz bound in the initial time. -/
lemma pie_T_lip_u {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u' u t : ℝ, 0 ≤ u' → u' ≤ u → u ≤ t → 0 < t → t ≤ T → ∀ j k : NonzeroLattice d,
      |pieT D μ u' t j k - pieT D μ u t j k| ≤ L * (u - u') * Lattice.jp k.1 ^ (J : ℝ) := by
  have hJ1 : 1 ≤ J := by
    obtain ⟨hd, hJ, -⟩ := H
    have := ClassicalPart.three_le_mStar d
    omega
  obtain ⟨K, hK, hlip⟩ := pie_lip_fun H
  obtain ⟨CJ, hCJ, hlev⟩ := pie_level_bound H J hJ1 le_rfl
  refine ⟨K * CJ, mul_nonneg hK hCJ, fun u' u t hu' hu'u hut ht0 htT j k => ?_⟩
  have ht : t ∈ Set.Ioc 0 T := ⟨ht0, htT⟩
  have hut' : u ∈ Set.Icc 0 t := ⟨hu'.trans hu'u, hut⟩
  rcases hu'u.eq_or_lt with heq | hlt
  · subst heq
    simp
  have hu0 : 0 < u := lt_of_le_of_lt hu' hlt
  have hu : u ∈ Set.Ioc 0 T := ⟨hu0, hut.trans htT⟩
  have hu'' : u' ∈ Set.Icc 0 u := ⟨hu', hlt.le⟩
  have hφ : Dom J (Torus.realMode k) := pieDom_realMode J k
  have hψ : Dom J (propagator D μ u t (Torus.realMode k)) := pie_prop_dom H ht hut' hφ
  have hsg : propagator D μ u' t (Torus.realMode k) =
      propagator D μ u' u (propagator D μ u t (Torus.realMode k)) := by
    rcases hut.eq_or_lt with h | h
    · subst h
      obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
      rw [prop_self_pos hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht hφ]
    · exact pie_prop_semigroup H ht hφ hu' hu'u h
  have hU : Dom J (propagator D μ u' u (propagator D μ u t (Torus.realMode k))) :=
    pie_prop_dom H hu hu'' hψ
  have hco : pieT D μ u' t j k - pieT D μ u t j k =
      Torus.funRealCoeff (fun x => propagator D μ u' u (propagator D μ u t (Torus.realMode k)) x -
        propagator D μ u t (Torus.realMode k) x) j := by
    have e1 : pieT D μ u' t j k = Torus.funRealCoeff
        (propagator D μ u' u (propagator D μ u t (Torus.realMode k))) j := by
      unfold pieT; rw [hsg]
    have e2 : pieT D μ u t j k = Torus.funRealCoeff (propagator D μ u t (Torus.realMode k)) j := rfl
    have e3 : (fun x => propagator D μ u' u (propagator D μ u t (Torus.realMode k)) x -
        propagator D μ u t (Torus.realMode k) x) =
        fun x => 1 * propagator D μ u' u (propagator D μ u t (Torus.realMode k)) x +
          (-1) * propagator D μ u t (Torus.realMode k) x := by funext x; ring
    rw [e1, e2, e3, pie_funRealCoeff_lin hU.1 hψ.1]
    ring
  obtain ⟨hmem, hbd⟩ := hlip u hu u' hu'' _ hψ
  rw [hco]
  refine (pie_abs_coeff_le hmem j).trans (hbd.trans ?_)
  obtain ⟨-, hbJ⟩ := hlev t ht u hut' _ hφ
  have h2 := pie_sobolev_realMode k (J : ℝ)
  have hKt : 0 ≤ K * (u - u') := mul_nonneg hK (by linarith)
  calc K * (u - u') * sobolevNorm (J : ℝ) (propagator D μ u t (Torus.realMode k))
      ≤ K * (u - u') * (CJ * sobolevNorm (J : ℝ) (Torus.realMode k)) :=
        mul_le_mul_of_nonneg_left hbJ hKt
    _ ≤ K * (u - u') * (CJ * Lattice.jp k.1 ^ (J : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCJ) hKt
    _ = _ := by ring

end HRS.MC.Sec7.PIE

end
