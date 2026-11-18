import HRS.Whole.Orbits

/-!
# S5.2 identification (aux 2): pairing the `𝒦`-valued feature with the test vectors of the reconstruction

For `t ∈ [0,T]` and a Hermite index `α` let `e_α ∈ ℓ²` be the `α`-th unit vector.  The coordinate of the
reconstruction `(𝒯M)(t) = A_T(t) - B_T + B_t` is a combination of pairings of `M_T`, `M_t` with
* `y1 = (e_α, 1_{[0,t]} e_α, 0)` : `⟨z, y1⟩ = coord_α (A_t(z))` (`z.evalA t`),
* `y2 = (0, 0, e_α)` : `⟨z, y2⟩ = coord_α (z.B)`.

Under `OscAdjointInput` the pairings of the feature `Γ_{r,a}(x)` with `y1`, `y2` are explicit:
`⟨Γ, y2⟩ = ∂_aφ_α(x)` and `⟨Γ, y1⟩ = ∂_aU(r,t)φ_α(x)` for `r ≤ t` (resp. `∂_aφ_α(x)` for `t < r ≤ T`)
(the Duhamel identity of `OscAdjointInput`).  Helper names carry the prefix `s52_`; namespace `HRS.MS.S52`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S52

open HRS HRS.Whole

variable {d : ℕ}

/-! ### Test vectors -/

/-- The `α`-th unit vector of `ℓ² = OscDual d m`. -/
def s52e (m : ℝ) (α : MultiIndex d) : OscDual d m :=
  (lp.single 2 α (1 : ℝ) : lp (fun _ : MultiIndex d => ℝ) 2)

lemma s52_inner_e {m : ℝ} (v : OscDual d m) (α : MultiIndex d) :
    inner ℝ v (s52e m α) = OscDual.coord v α := by
  classical
  have h := lp.inner_single_right (𝕜 := ℝ) (G := fun _ : MultiIndex d => ℝ) α (1 : ℝ)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from v)
  have h2 : inner ℝ (show lp (fun _ : MultiIndex d => ℝ) 2 from v)
      (lp.single 2 α (1 : ℝ)) = inner ℝ v (s52e m α) := rfl
  rw [← h2, h]
  simp [OscDual.coord]

/-- `(e_α, 1_{[0,t]} e_α, 0)`. -/
def s52y1 (m T t : ℝ) (α : MultiIndex d) : KSpace d m T :=
  KSpace.mk (s52e m α)
    (indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := t))
      (measure_ne_top (volume.restrict (Set.Icc (0 : ℝ) T)) (Set.Icc (0 : ℝ) t)) (s52e m α)) 0

/-- `(0, 0, e_α)`. -/
def s52y2 (m T : ℝ) (α : MultiIndex d) : KSpace d m T := KSpace.mk 0 0 (s52e m α)

lemma s52_inner_mk (m T : ℝ) (z : KSpace d m T) (a b : OscDual d m) (a' : L2Path d m T) :
    inner ℝ z (KSpace.mk a a' b) = inner ℝ z.A₀ a + inner ℝ z.A' a' + inner ℝ z.B b := by
  unfold KSpace.mk KSpace.A₀ KSpace.A' KSpace.B
  show inner ℝ (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from z)
    (WithLp.toLp 2 (a, WithLp.toLp 2 (a', b))) = _
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only []
  ring


lemma s52_mk_A₀ (m T : ℝ) (a : OscDual d m) (a' : L2Path d m T) (b : OscDual d m) :
    (KSpace.mk a a' b).A₀ = a := rfl

lemma s52_mk_A' (m T : ℝ) (a : OscDual d m) (a' : L2Path d m T) (b : OscDual d m) :
    (KSpace.mk a a' b).A' = a' := rfl

lemma s52_mk_B (m T : ℝ) (a : OscDual d m) (a' : L2Path d m T) (b : OscDual d m) :
    (KSpace.mk a a' b).B = b := rfl

lemma s52_coord_B {m T : ℝ} (z : KSpace d m T) (α : MultiIndex d) :
    OscDual.coord z.B α = inner ℝ z (s52y2 m T α) := by
  rw [s52y2, s52_inner_mk, s52_inner_e]
  simp

lemma s52_coord_add {m : ℝ} (a b : OscDual d m) (α : MultiIndex d) :
    OscDual.coord (a + b) α = OscDual.coord a α + OscDual.coord b α := rfl

lemma s52_coord_sub {m : ℝ} (a b : OscDual d m) (α : MultiIndex d) :
    OscDual.coord (a - b) α = OscDual.coord a α - OscDual.coord b α := rfl

lemma s52_coord_eq_inner {m : ℝ} (v : OscDual d m) (α : MultiIndex d) :
    OscDual.coord v α = inner ℝ (s52e m α) v := by
  rw [real_inner_comm, s52_inner_e]

/-- The pairing of `z ∈ 𝒦` with `y1`: `A₀`-coordinate plus the integral of the `A'` coordinate over `[0,t]`. -/
lemma s52_inner_y1 {m T t : ℝ} (htT : t ≤ T) (z : KSpace d m T) (α : MultiIndex d) :
    inner ℝ z (s52y1 m T t α) = OscDual.coord z.A₀ α +
      ∫ τ in Set.Icc (0 : ℝ) t, OscDual.coord ((z.A' : L2Path d m T) τ) α := by
  rw [s52y1, s52_inner_mk, s52_inner_e]
  simp only [inner_zero_right, add_zero]
  congr 1
  rw [real_inner_comm, L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ]
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 (Set.Icc_subset_Icc_right htT)]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  show inner ℝ (s52e m α) ((z.A' : L2Path d m T) τ) = OscDual.coord ((z.A' : L2Path d m T) τ) α
  rw [s52_coord_eq_inner]

/-- The coordinate of `A_t = A₀ + ∫_0^t A'`. -/
lemma s52_coord_evalA {m T t : ℝ} (_ht0 : 0 ≤ t) (htT : t ≤ T) (z : KSpace d m T) (α : MultiIndex d) :
    OscDual.coord (z.evalA t) α = inner ℝ z (s52y1 m T t α) := by
  rw [s52_inner_y1 htT]
  unfold KSpace.evalA
  rw [s52_coord_add, min_eq_left htT]
  congr 1
  simp only [s52_coord_eq_inner]
  have hint : IntegrableOn (fun τ => (z.A' : L2Path d m T) τ) (Set.Icc (0 : ℝ) t)
      (volume : Measure ℝ) := by
    have h1 : Integrable (fun τ => (z.A' : L2Path d m T) τ) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (Lp.memLp (z.A' : L2Path d m T)).integrable (by norm_num)
    exact h1.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right htT) le_rfl)
  exact (integral_inner hint (s52e m α)).symm

/-- The coordinates of the reconstruction in terms of pairings. -/
lemma s52_coord_recon {m T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {Ω : Type*}
    (M : ℝ → Ω → KSpace d m T) (ζ : Ω) (α : MultiIndex d) :
    OscDual.coord (reconstructPath m T M ζ t) α =
      inner ℝ (M T ζ) (s52y1 m T t α) - inner ℝ (M T ζ) (s52y2 m T α) +
        inner ℝ (M t ζ) (s52y2 m T α) := by
  unfold reconstructPath
  rw [s52_coord_add, s52_coord_sub, s52_coord_evalA ht0 htT, s52_coord_B, s52_coord_B]


/-! ### Pairings of the orbit feature -/

open Classical in
lemma s52_coord_ellVec {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) (α : MultiIndex d) :
    OscDual.coord (ellVec (d := d) m c) α = c α := by
  have h1 : (ellVec (d := d) m c : lp (fun _ : MultiIndex d => ℝ) 2) =
      (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := by
    unfold ellVec
    exact dif_pos h
  unfold OscDual.coord
  rw [h1]

lemma s52_coord_zero {m : ℝ} (α : MultiIndex d) : OscDual.coord (0 : OscDual d m) α = 0 := rfl

/-- `⟨Γ, y2⟩ = Dφ_α(x)`. -/
lemma s52_pair_y2 {C : WholeCoeff d} {m T : ℝ} {Dop : (Euc d → ℝ) → Euc d → ℝ} {r : ℝ} {x : Euc d}
    (hK : Memℓp (fun α : MultiIndex d => Dop (oscTestFun m α) x) 2) (α : MultiIndex d) :
    inner ℝ (orbitFeature C m T Dop r x) (s52y2 m T α) = Dop (oscTestFun m α) x := by
  rw [← s52_coord_B]
  unfold orbitFeature
  simp only []
  rw [s52_mk_B, s52_coord_ellVec hK]

/-- `⟨Γ, y1⟩ = Dφ_α(x) + ∫_0^t 1_{r<τ} D U(r,τ) L_τ φ_α(x) dτ`. -/
lemma s52_pair_y1 {C : WholeCoeff d} {m T t : ℝ} (htT : t ≤ T) {Dop : (Euc d → ℝ) → Euc d → ℝ}
    {r : ℝ} {x : Euc d} (hK : IsOrbitFeatureK C m T Dop r x) (α : MultiIndex d) :
    inner ℝ (orbitFeature C m T Dop r x) (s52y1 m T t α) = Dop (oscTestFun m α) x +
      ∫ τ in Set.Icc (0 : ℝ) t, (if r < τ then Dop (propagatorW C r τ
        (generatorW C τ (oscTestFun m α))) x else 0) := by
  classical
  rw [s52_inner_y1 htT]
  have hmem := hK.2.2
  unfold orbitFeature
  simp only []
  rw [dif_pos hmem, s52_mk_A₀, s52_mk_A', s52_coord_ellVec hK.1]
  congr 1
  have hae : ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ((hmem.toLp _ : L2Path d m T) τ) = (fun τ : ℝ => if r < τ then ellVec (d := d) m (fun α => Dop
        (propagatorW C r τ (generatorW C τ (oscTestFun m α))) x) else 0) τ := hmem.coeFn_toLp
  have hae' : ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ((hmem.toLp _ : L2Path d m T) τ) =
      (fun τ : ℝ => if r < τ then ellVec (d := d) m (fun α => Dop
        (propagatorW C r τ (generatorW C τ (oscTestFun m α))) x) else 0) τ :=
    ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc_right htT) hae
  refine integral_congr_ae ?_
  filter_upwards [hae', ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := t))] with τ h1 h2
  rw [h1]
  by_cases hrτ : r < τ
  · simp only [hrτ, if_true]
    exact s52_coord_ellVec (hK.2.1 τ ⟨hrτ, h2.2.trans htT⟩) α
  · simp only [hrτ, if_false]
    exact s52_coord_zero α


/-! ### The Duhamel identity -/

lemma s52_duhamel_int {C : WholeCoeff d} {m T : ℝ} (hC : OscAdjointInput C m T) {r t : ℝ} (hr : 0 ≤ r)
    (htT : t ≤ T) (a : Fin d) (α : MultiIndex d) (x : Euc d) :
    ∫ τ in Set.Icc (0 : ℝ) t, (if r < τ then gradComp a (propagatorW C r τ
        (generatorW C τ (oscTestFun m α))) x else 0) =
      if r ≤ t then gradComp a (propagatorW C r t (oscTestFun m α)) x -
        gradComp a (oscTestFun m α) x else 0 := by
  classical
  have e : (fun τ : ℝ => if r < τ then gradComp a (propagatorW C r τ
      (generatorW C τ (oscTestFun m α))) x else 0) =
      (Set.Ioi r).indicator (fun τ => gradComp a (propagatorW C r τ
        (generatorW C τ (oscTestFun m α))) x) := by
    funext τ
    by_cases h : r < τ <;> simp [Set.indicator_apply, h]
  rw [e, setIntegral_indicator measurableSet_Ioi]
  by_cases hrt : r ≤ t
  · have hs : Set.Icc (0 : ℝ) t ∩ Set.Ioi r = Set.Ioc r t := by
      ext τ
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨hr.trans h3.le, h2⟩, h3⟩
    rw [hs, if_pos hrt, ← integral_Icc_eq_integral_Ioc]
    exact (hC.duhamel r t hr hrt htT α a x).2.symm
  · have hs : Set.Icc (0 : ℝ) t ∩ Set.Ioi r = ∅ := by
      ext τ
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt]
      intro h; linarith [h.2, not_le.1 hrt]
    rw [hs, if_neg hrt]
    simp

/-- `⟨Γ_{r,a}(x), y2⟩ = ∂_aφ_α(x)` for every `r` (the base part does not depend on `r`). -/
lemma s52_pair_grad_y2 {C : WholeCoeff d} {m T : ℝ} (hC : OscAdjointInput C m T) (hT : 0 ≤ T)
    (a : Fin d) (r : ℝ) (x : Euc d) (α : MultiIndex d) :
    inner ℝ (gradFeature C m T a r x) (s52y2 m T α) = gradComp a (oscTestFun m α) x :=
  s52_pair_y2 (hC.feature a 0 ⟨le_rfl, hT⟩ x).1 α

/-- `⟨Γ_{r,a}(x), y1⟩ = ∂_aU(r,t)φ_α(x)` for `0 ≤ r ≤ t ≤ T`, and `∂_aφ_α(x)` for `t < r ≤ T`. -/
lemma s52_pair_grad_y1 {C : WholeCoeff d} {m T t : ℝ} (hC : OscAdjointInput C m T) (htT : t ≤ T)
    (a : Fin d) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (α : MultiIndex d) :
    inner ℝ (gradFeature C m T a r x) (s52y1 m T t α) =
      if r ≤ t then gradComp a (propagatorW C r t (oscTestFun m α)) x else
        gradComp a (oscTestFun m α) x := by
  unfold gradFeature
  rw [s52_pair_y1 htT (hC.feature a r hr x), s52_duhamel_int hC hr.1 htT]
  by_cases h : r ≤ t <;> simp [h]

end HRS.MS.S52
