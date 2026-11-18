import HRS.MP.RdGenerator
import HRS.Whole.AppendixALemmas2

/-!
# Packet MPRPROP, part 1: the increment bound `IncrementBoundRd` (S.A.22(ii) on `ℝ^d`)

* `rpi_hGamma`: the index relation `m_* + d/2 + 4 < Γ + 2` for the field index `Γ = fd.Gamma` of every
  selected density (given that the density applies);
* `rpi_iter`: abstract differentiation under the integral sign: if `F = ∫ G_τ dμ` pointwise, `G_τ ∈ C^k`
  with `|∂^α G_τ(y)| ≤ N⟨y⟩`, and `F ∈ C^k`, then `∂^α F = ∫ ∂^α G_τ dμ` for `|α| ≤ k`;
* `rpi_increment`: `IncrementBoundRd` from the weighted extension, the terminal-time identity and the
  generator bound.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdProp
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdGen

variable {d : ℕ}

/-! ### (a) The index relation -/

lemma rpi_hGamma {s : ℝ} (fd : FieldDensityRd d s) {M : Matrix (Fin d) (Fin d) ℝ} {invβ ν₀ : ℝ}
    (h : fd.HoldsAt s M invβ ν₀) :
    (mStar d : ℝ) + d / 2 + 4 < ((fd.Gamma : ℝ) + 2) := by
  cases fd with
  | nd Rg =>
    have h1 : FieldDensityRd.Gamma (FieldDensityRd.nd (d := d) (s := s) Rg) = mStar d + d / 2 + 1 + 2 := rfl
    rw [h1]
    have h2 := Nat.div_add_mod d 2
    have h3 := Nat.mod_lt d (by norm_num : 2 > 0)
    have h4 : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) + ((d % 2 : ℕ) : ℝ) := by exact_mod_cast h2.symm
    have h5 : ((d % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast h3
    push_cast
    linarith
  | decSub c =>
    have h1 : FieldDensityRd.Gamma (FieldDensityRd.decSub c) = c.gammaIndex := rfl
    rw [h1]
    unfold DecayingDensity.gammaIndex DecayingDensity.sobolevIndex
    have a1 := Nat.lt_floor_add_one ((d : ℝ) / c.integrability)
    have a2 := Nat.lt_floor_add_one ((d : ℝ) * (1 / 2 - 1 / c.integrability))
    have a3 : (d : ℝ) / c.integrability + (d : ℝ) * (1 / 2 - 1 / c.integrability) = d / 2 := by ring
    push_cast
    linarith
  | decSuperIso m p =>
    have h1 : FieldDensityRd.Gamma (FieldDensityRd.decSuperIso (d := d) (s := s) m p) =
        m + 2 + ⌊(d : ℝ) * (1 / 2 - 1 / p)⌋₊ + 1 := rfl
    rw [h1]
    have hh : (mStar d : ℝ) + d / p < m := h.2.2.1
    have a2 := Nat.lt_floor_add_one ((d : ℝ) * (1 / 2 - 1 / p))
    have a3 : (d : ℝ) * (1 / 2 - 1 / p) = d / 2 - d / p := by ring
    push_cast
    linarith
  | decSuperHilb m =>
    have h1 : FieldDensityRd.Gamma (FieldDensityRd.decSuperHilb (d := d) (s := s) m) =
        m + 2 + ⌊(d : ℝ) * (1 / 2 - 1 / 2)⌋₊ + 1 := rfl
    rw [h1]
    have hh : (mStar d : ℝ) + d / 2 < m := h.2.1
    have a3 : ⌊(d : ℝ) * (1 / 2 - 1 / 2)⌋₊ = 0 := by norm_num
    rw [a3]
    push_cast
    linarith

/-! ### (b) Differentiation under the integral sign -/

lemma rpi_jb_le (y : Euc d) : jbracket y ≤ 1 + ‖y‖ := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg y]

lemma rpi_jb_pos (y : Euc d) : 0 < jbracket y := by
  unfold jbracket; positivity

lemma rpi_hasDerivAt_partial {l : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ (l + 1 : ℕ) f)
    (idx : Fin l → Fin d) (j : Fin d) (y : Euc d) :
    HasDerivAt (fun s : ℝ => partialDeriv idx f (y + s • (EuclideanSpace.single j (1 : ℝ) : Euc d)))
      (partialDeriv (Fin.cons j idx : Fin (l + 1) → Fin d) f y) 0 := by
  set v : Euc d := EuclideanSpace.single j (1 : ℝ) with hv
  have hdiff : Differentiable ℝ (fun z => iteratedFDeriv ℝ l f z) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self l)
  let m0 : Fin l → Euc d := fun p => EuclideanSpace.single (idx p) 1
  let L : (Euc d [×l]→L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousMultilinearMap.apply ℝ (fun _ : Fin l => Euc d) ℝ m0
  have hA : HasFDerivAt (fun z => L (iteratedFDeriv ℝ l f z)) (L.comp (fderiv ℝ (iteratedFDeriv ℝ l f) y)) y :=
    L.hasFDerivAt.comp y (hdiff y).hasFDerivAt
  have hB : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hA' : HasFDerivAt (fun z => L (iteratedFDeriv ℝ l f z)) (L.comp (fderiv ℝ (iteratedFDeriv ℝ l f) y))
      (y + (0 : ℝ) • v) := by simpa using hA
  have h2 := hA'.comp_hasDerivAt (0 : ℝ) hB
  have e : (L.comp (fderiv ℝ (iteratedFDeriv ℝ l f) y)) v =
      partialDeriv (Fin.cons j idx : Fin (l + 1) → Fin d) f y := by
    unfold partialDeriv
    rw [iteratedFDeriv_succ_apply_left]
    simp only [ContinuousLinearMap.comp_apply, L, ContinuousMultilinearMap.apply_apply, m0]
    have e2 : (Fin.tail fun l_1 => (EuclideanSpace.single ((Fin.cons j idx : Fin (l + 1) → Fin d) l_1) (1 : ℝ) : Euc d)) = fun p => EuclideanSpace.single (idx p) 1 := by
      funext p; simp [Fin.tail]
    rw [e2]
    simp [hv]
  rw [e] at h2
  exact h2

lemma rpi_dir {μ : Measure ℝ} [IsFiniteMeasure μ] {G G' : ℝ → Euc d → ℝ} (v x : Euc d) (B : ℝ)
    (hint : ∀ y, Integrable (fun τ => G τ y) μ)
    (hder : ∀ᵐ τ ∂μ, ∀ y, HasDerivAt (fun s : ℝ => G τ (y + s • v)) (G' τ y) 0)
    (hB : ∀ᵐ τ ∂μ, ∀ s : ℝ, |s| < 1 → |G' τ (x + s • v)| ≤ B) :
    Integrable (fun τ => G' τ x) μ ∧
      HasDerivAt (fun s : ℝ => ∫ τ, G τ (x + s • v) ∂μ) (∫ τ, G' τ x ∂μ) 0 := by
  have hmeas : AEStronglyMeasurable (fun τ => G' τ x) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) τ => ((n : ℝ) + 1) * (G τ (x + (1 / ((n : ℝ) + 1)) • v) - G τ x)) (fun n => ?_) ?_
    · exact (((hint _).1.sub (hint x).1).const_mul _)
    · filter_upwards [hder] with τ hτ
      have h := (hτ x).tendsto_slope_zero
      have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => ?_⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        positivity
      refine (h.comp hseq).congr fun n => ?_
      simp only [Function.comp, zero_add, zero_smul, add_zero, smul_eq_mul]
      rw [one_div, inv_inv]
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := μ) (x₀ := 0)
    (s := Metric.ball (0 : ℝ) 1) (bound := fun _ => B) (F := fun s τ => G τ (x + s • v))
    (F' := fun s τ => G' τ (x + s • v)) (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun s => hint _ |>.1)
    (by simpa using hint x) (by simpa using hmeas)
    (by
      filter_upwards [hB] with τ hτ s hs
      rw [Real.norm_eq_abs]
      exact hτ s (by simpa using hs))
    (integrable_const B)
    (by
      filter_upwards [hder] with τ hτ s _
      have h0 : HasDerivAt (fun u : ℝ => G τ ((x + s • v) + u • v)) (G' τ (x + s • v)) (s - s) := by
        rw [sub_self]; exact hτ _
      have h2 := h0.comp_sub_const s s
      convert h2 using 1
      funext u
      congr 1
      module)
  simpa using this

/-- Iterated differentiation under the integral sign. -/
lemma rpi_iter {μ : Measure ℝ} [IsFiniteMeasure μ] {k : ℕ} {G : ℝ → Euc d → ℝ} {F : Euc d → ℝ} {N : ℝ}
    (hN : 0 ≤ N)
    (hGc : ∀ᵐ τ ∂μ, ContDiff ℝ k (G τ))
    (hGb : ∀ᵐ τ ∂μ, ∀ l ≤ k, ∀ idx : Fin l → Fin d, ∀ y, |partialDeriv idx (G τ) y| ≤ N * jbracket y)
    (hFc : ContDiff ℝ k F) (hint : ∀ y, Integrable (fun τ => G τ y) μ)
    (hF : ∀ y, F y = ∫ τ, G τ y ∂μ) :
    ∀ l ≤ k, ∀ idx : Fin l → Fin d, ∀ y, Integrable (fun τ => partialDeriv idx (G τ) y) μ ∧
      partialDeriv idx F y = ∫ τ, partialDeriv idx (G τ) y ∂μ := by
  intro l
  induction l with
  | zero =>
    intro _ idx y
    have e : ∀ f : Euc d → ℝ, partialDeriv idx f y = f y := fun f => by
      simp [partialDeriv, iteratedFDeriv_zero_apply]
    simp only [e]
    exact ⟨hint y, hF y⟩
  | succ l ih =>
    intro hl idx x
    have hl' : l ≤ k := Nat.le_of_succ_le hl
    obtain ⟨j, idx', rfl⟩ : ∃ (j : Fin d) (idx' : Fin l → Fin d), idx = Fin.cons j idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    set v : Euc d := EuclideanSpace.single j (1 : ℝ) with hv
    have hvn : ‖v‖ = 1 := by simp [hv]
    have hGc' : ∀ᵐ τ ∂μ, ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (G τ) :=
      hGc.mono fun τ h => h.of_le (by exact_mod_cast hl)
    obtain ⟨hI, hD⟩ := rpi_dir (μ := μ) (G := fun τ y => partialDeriv idx' (G τ) y)
      (G' := fun τ y => partialDeriv (Fin.cons j idx' : Fin (l + 1) → Fin d) (G τ) y) v x
      (N * (2 + ‖x‖))
      (fun y => (ih hl' idx' y).1)
      (by filter_upwards [hGc'] with τ hτ y using rpi_hasDerivAt_partial hτ idx' j y)
      (by
        filter_upwards [hGb] with τ hτ s hs
        refine (hτ (l + 1) hl _ _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hN
        refine (rpi_jb_le _).trans ?_
        have h1 : ‖x + s • v‖ ≤ ‖x‖ + 1 := by
          calc ‖x + s • v‖ ≤ ‖x‖ + ‖s • v‖ := norm_add_le _ _
            _ ≤ ‖x‖ + 1 := by
              rw [norm_smul, hvn, mul_one, Real.norm_eq_abs]; linarith
        linarith)
    refine ⟨hI, ?_⟩
    have hFd := rpi_hasDerivAt_partial (hFc.of_le (by exact_mod_cast hl)) idx' j x
    have hFd2 : HasDerivAt (fun s : ℝ => partialDeriv idx' F (x + s • v))
        (∫ τ, partialDeriv (Fin.cons j idx' : Fin (l + 1) → Fin d) (G τ) x ∂μ) 0 := by
      have : (fun s : ℝ => partialDeriv idx' F (x + s • v)) =
          fun s : ℝ => ∫ τ, partialDeriv idx' (G τ) (x + s • v) ∂μ :=
        funext fun s => (ih hl' idx' _).2
      rw [this]; exact hD
    exact hFd.unique hFd2

/-- The bound for `∂^α F` obtained from `rpi_iter`. -/
lemma rpi_iter_bound {μ : Measure ℝ} [IsFiniteMeasure μ] {k : ℕ} {G : ℝ → Euc d → ℝ} {F : Euc d → ℝ} {N : ℝ}
    (hN : 0 ≤ N)
    (hGc : ∀ᵐ τ ∂μ, ContDiff ℝ k (G τ))
    (hGb : ∀ᵐ τ ∂μ, ∀ l ≤ k, ∀ idx : Fin l → Fin d, ∀ y, |partialDeriv idx (G τ) y| ≤ N * jbracket y)
    (hFc : ContDiff ℝ k F) (hint : ∀ y, Integrable (fun τ => G τ y) μ)
    (hF : ∀ y, F y = ∫ τ, G τ y ∂μ) {l : ℕ} (hl : l ≤ k) (idx : Fin l → Fin d) (x : Euc d) :
    |partialDeriv idx F x| ≤ μ.real Set.univ * (N * jbracket x) := by
  have h := (rpi_iter hN hGc hGb hFc hint hF l hl idx x).2
  rw [h]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun τ => partialDeriv idx (G τ) x)
    (C := N * jbracket x) (by
      filter_upwards [hGb] with τ hτ
      rw [Real.norm_eq_abs]
      exact hτ l hl idx x)
  rw [Real.norm_eq_abs] at this
  linarith

/-! ### (c) The increment bound -/

/-- A smooth `H^q` test function has finite weighted `C^k` norm when `k + d/2 < q`. -/
lemma rpi_test_weighted (Γ m₀ : ℕ) (hq : ((m₀ + 1 : ℕ) : ℝ) + d / 2 < ((Γ + 2 : ℕ) : ℝ)) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ φ : Euc d → ℝ, IsSobolevTest (((Γ + 2 : ℕ) : ℝ)) φ →
      ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) φ ∧
        weightedSupE (m₀ + 1) (-1) φ ≤ ENNReal.ofReal (Cs * HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) φ) := by
  obtain ⟨Cs, hCs0, hCs⟩ := rg_phi_bounds (d := d) (m₀ + 1) hq
  refine ⟨Cs, hCs0, fun φ hφ => ⟨hφ.1.of_le (by exact_mod_cast le_top), ?_⟩⟩
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  have hj : (j : ℕ) ≤ m₀ + 1 := Nat.lt_succ_iff.1 j.2
  have h1 : |partialDeriv i φ x| ≤ ‖iteratedFDeriv ℝ j φ x‖ := by
    have := (iteratedFDeriv ℝ j φ x).le_opNorm (fun l => (EuclideanSpace.single (i l) (1 : ℝ) : Euc d))
    simp only [rg_norm_single, Finset.prod_const_one, mul_one] at this
    unfold partialDeriv
    rwa [← Real.norm_eq_abs]
  have h2 := hCs φ hφ.1 hφ.2 j hj x
  have h3 : jbracket x ^ (-1 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg_one]
    refine inv_le_one_of_one_le₀ ?_
    unfold jbracket
    exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])
  show jbracket x ^ (-1 : ℝ) * |partialDeriv i φ x| ≤ _
  calc jbracket x ^ (-1 : ℝ) * |partialDeriv i φ x| ≤ 1 * ‖iteratedFDeriv ℝ j φ x‖ :=
        mul_le_mul h3 h1 (abs_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact h2

lemma rpi_exp_bound {K u T : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) :
    K * Real.exp (K * u) ≤ max K 0 * Real.exp (max K 0 * T) := by
  rcases le_total K 0 with hK | hK
  · have h1 : K * Real.exp (K * u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK (Real.exp_pos _).le
    have h2 : 0 ≤ max K 0 * Real.exp (max K 0 * T) := by positivity
    linarith
  · rw [max_eq_left hK]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left huT hK)) hK

/-- **Increment bound** `B:eq:path-propagator-rd` on `ℝ^d` for one coefficient `Cf = D.coeff ρ` carrying a weighted
extension `U` (constant `Cw`) and the adjoint existence input `AdjointInputOneD`; `Cgen` is the constant of the
generator bound `rg_generator_bound` (independent of `D, ρ, T, Cw, U`), and the constant of the increment bound is
`max Cw 0 * exp (max Cw 0 * T) * Cgen`. -/
theorem rpi_increment (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Γ m₀ : ℕ)
    (hm₀ : m₀ ≤ mStar d) (hΓ : (mStar d : ℝ) + d / 2 + 4 < ((Γ : ℝ) + 2))
    (MB Λ ΛV G₀ νbar : ℝ) :
    ∃ Cgen : ℝ, 0 ≤ Cgen ∧ ∀ (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (T Kadj Cw : ℝ)
      (U : ℝ → ℝ → (Euc d → ℝ) → (Euc d → ℝ)),
      D.s = s → HRS.PDE.MatBound MB D.M → VHypRd (Γ + 5) ΛV G₀ D.V → IsRegularMFRd s (Γ + 2 + 3) Λ T ρ →
      0 ≤ D.invβ → D.invβ ≤ νbar →
      AdjointInputOneD (((Γ + 2 : ℕ) : ℝ)) (m₀ + 1) (D.coeff ρ) T Kadj →
      IsWeightedExtension (D.coeff ρ) (m₀ + 1) (Γ + 2) T Cw U →
      IncrementBoundRd (D.coeff ρ) T (Γ + 2) m₀ (max Cw 0 * Real.exp (max Cw 0 * T) * Cgen) := by
  obtain ⟨Cgen, hCgen0, hgen⟩ := rg_generator_bound hd hs0 hsd Γ m₀ hm₀ hΓ MB Λ ΛV G₀ νbar
  have hmS : (m₀ : ℝ) ≤ mStar d := by exact_mod_cast hm₀
  have hq : ((m₀ + 1 : ℕ) : ℝ) + d / 2 < ((Γ + 2 : ℕ) : ℝ) := by
    push_cast at hΓ ⊢; linarith
  obtain ⟨Cs, hCs0, hCs⟩ := rpi_test_weighted (d := d) Γ m₀ hq
  refine ⟨Cgen, hCgen0, ?_⟩
  intro D ρ T Kadj Cw U hDs hMB hV hcoef hν0 hν hadj hU r s' t hr hrs hst htT φ hφ l hl idx x
  set Cf := D.coeff ρ with hCf
  set Kp : ℝ := max Cw 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  set nφ : ℝ := HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) φ with hnφ
  have hnφ0 : 0 ≤ nφ := Real.sqrt_nonneg _
  have hcons : ∀ u, r ≤ u → u ≤ T → U r u φ = propagatorW Cf r u φ := fun u hru huT =>
    hU.consistent r u hr hru huT φ (hadj 0 u le_rfl (hr.trans hru) huT φ hφ).1
  have hgenφ : ∀ τ, 0 ≤ τ → τ ≤ T → ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) (generatorW Cf τ φ) ∧
      weightedSupE (m₀ + 1) (-1) (generatorW Cf τ φ) ≤ ENNReal.ofReal (Cgen * nφ) := fun τ h0 hT =>
    hgen D ρ T hDs hMB hV hcoef hν0 hν τ ⟨h0, hT⟩ φ hφ
  have hTI : ∀ u, r ≤ u → u ≤ T → ∀ y : Euc d,
      IntegrableOn (fun τ => U r τ (generatorW Cf τ φ) y) (Set.Icc r u) ∧
        U r u φ y - φ y = ∫ τ in Set.Icc r u, U r τ (generatorW Cf τ φ) y := fun u hru huT y =>
    hU.terminal_identity r u hr hru huT φ hφ.1 hφ.2 (fun τ hτ =>
      ⟨(hgenφ τ (hr.trans hτ.1) (hτ.2.trans huT)).1,
        lt_of_le_of_lt (hgenφ τ (hr.trans hτ.1) (hτ.2.trans huT)).2 ENNReal.ofReal_lt_top⟩) y
  -- the function `φ` itself
  obtain ⟨hφc, hφw⟩ := hCs φ hφ
  have hbφ : ∀ u, r ≤ u → u ≤ T → ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) (U r u φ) := fun u hru huT =>
    (hU.bound r u hr hru huT φ hφc (lt_of_le_of_lt hφw ENNReal.ofReal_lt_top)).1
  set F : Euc d → ℝ := fun y => propagatorW Cf r t φ y - propagatorW Cf r s' φ y with hF
  set G : ℝ → Euc d → ℝ := fun τ y => U r τ (generatorW Cf τ φ) y with hG
  have hFc : ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) F := by
    have e : F = fun y => U r t φ y - U r s' φ y := by
      funext y
      rw [hcons t (hrs.trans hst) htT, hcons s' hrs (hst.trans htT)]
    rw [e]
    exact (hbφ t (hrs.trans hst) htT).sub (hbφ s' hrs (hst.trans htT))
  have hint : ∀ y, Integrable (fun τ => G τ y) (volume.restrict (Set.Ioc s' t)) := fun y =>
    ((hTI t (hrs.trans hst) htT y).1).mono_set (fun τ hτ => ⟨hrs.trans hτ.1.le, hτ.2⟩)
  have hFeq : ∀ y, F y = ∫ τ in Set.Ioc s' t, G τ y := by
    intro y
    obtain ⟨hI1, h1⟩ := hTI t (hrs.trans hst) htT y
    obtain ⟨hI2, h2⟩ := hTI s' hrs (hst.trans htT) y
    have hsplit := setIntegral_union (μ := volume) (f := fun τ => G τ y)
      (Set.disjoint_left.2 fun τ h1 h2 => absurd h1.2 (not_le.2 h2.1)) measurableSet_Ioc hI2 (hint y)
    rw [Set.Icc_union_Ioc_eq_Icc hrs hst] at hsplit
    have e1 := hcons t (hrs.trans hst) htT
    have e2 := hcons s' hrs (hst.trans htT)
    show propagatorW Cf r t φ y - propagatorW Cf r s' φ y = _
    rw [← e1, ← e2]
    have : (∫ τ in Set.Icc r t, G τ y) = U r t φ y - φ y := h1.symm
    have h2' : (∫ τ in Set.Icc r s', G τ y) = U r s' φ y - φ y := h2.symm
    linarith
  -- bounds for the integrand
  have hGgood : ∀ τ ∈ Set.Ioc s' t, ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) (G τ) ∧
      weightedSupE (m₀ + 1) (-1) (G τ) ≤ ENNReal.ofReal (Kp * Real.exp (Kp * T) * (Cgen * nφ)) := by
    intro τ hτ
    have hτr : r ≤ τ := hrs.trans hτ.1.le
    have hτT : τ ≤ T := hτ.2.trans htT
    have hg := hgenφ τ (hr.trans hτr) hτT
    have hfin : weightedSupE (m₀ + 1) (-1) (generatorW Cf τ φ) < ⊤ :=
      lt_of_le_of_lt hg.2 ENNReal.ofReal_lt_top
    obtain ⟨hc, hb⟩ := hU.bound r τ hr hτr hτT (generatorW Cf τ φ) hg.1 hfin
    refine ⟨hc, hb.trans ?_⟩
    have h1 : ENNReal.ofReal (Cw * Real.exp (Cw * (τ - r))) ≤ ENNReal.ofReal (Kp * Real.exp (Kp * T)) :=
      ENNReal.ofReal_le_ofReal (rpi_exp_bound (sub_nonneg.2 hτr) (by linarith))
    calc ENNReal.ofReal (Cw * Real.exp (Cw * (τ - r))) * weightedSupE (m₀ + 1) (-1) (generatorW Cf τ φ)
        ≤ ENNReal.ofReal (Kp * Real.exp (Kp * T)) * ENNReal.ofReal (Cgen * nφ) :=
          mul_le_mul' h1 hg.2
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hN0 : 0 ≤ Kp * Real.exp (Kp * T) * (Cgen * nφ) := by positivity
  have hGb : ∀ᵐ τ ∂(volume.restrict (Set.Ioc s' t)), ∀ l ≤ m₀ + 1, ∀ idx : Fin l → Fin d, ∀ y,
      |partialDeriv idx (G τ) y| ≤ (Kp * Real.exp (Kp * T) * (Cgen * nφ)) * jbracket y := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ l hl idx y => ?_
    obtain ⟨-, hE⟩ := hGgood τ hτ
    have hfin : weightedSupE (m₀ + 1) (-1) (G τ) < ⊤ := lt_of_le_of_lt hE ENNReal.ofReal_lt_top
    have h1 := rg_partial_weight_bound hfin hl idx y
    have h2 : (weightedSupE (m₀ + 1) (-1) (G τ)).toReal ≤ Kp * Real.exp (Kp * T) * (Cgen * nφ) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
      rwa [ENNReal.toReal_ofReal hN0] at this
    have hjb := rpi_jb_pos y
    rw [Real.rpow_neg_one] at h1
    have h3 : |partialDeriv idx (G τ) y| ≤ jbracket y * (weightedSupE (m₀ + 1) (-1) (G τ)).toReal := by
      rw [inv_mul_le_iff₀ hjb] at h1; exact h1
    calc _ ≤ _ := h3
      _ ≤ jbracket y * (Kp * Real.exp (Kp * T) * (Cgen * nφ)) := mul_le_mul_of_nonneg_left h2 hjb.le
      _ = _ := by ring
  have hGc : ∀ᵐ τ ∂(volume.restrict (Set.Ioc s' t)), ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) (G τ) :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => (hGgood τ hτ).1
  have key := rpi_iter_bound (μ := volume.restrict (Set.Ioc s' t)) hN0 hGc hGb hFc hint hFeq hl idx x
  have hμ : (volume.restrict (Set.Ioc s' t)).real Set.univ = t - s' := by
    simp [Measure.real, Real.volume_Ioc, hst]
  rw [hμ] at key
  have hts : |t - s'| = t - s' := abs_of_nonneg (sub_nonneg.2 hst)
  rw [hts]
  refine key.trans (le_of_eq ?_)
  ring

end HRS.MP.RdProp
