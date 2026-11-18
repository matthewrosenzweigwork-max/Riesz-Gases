import HRS.MS.FixEqP3Aux1

/-!
# S5.7 `fixed_equation` (worker S57P), part 14: linearity of the adjoint propagator on bounded smooth data

`S57pFam C θ T j K`: the facts about one coefficient family used below (uniqueness of classical adjoint solutions, linearity and
continuity of the generator, the uniformly local adjoint input through order `j`).
`s57p_orb`: for `ψ ∈ C^{j+1+⌈d/2⌉}` with jets bounded by `B`, the orbit `r ↦ U^{r,t} ψ` is a classical adjoint solution, in `C^j`
with jets bounded by `|K| C_u B`.
`s57p_prop_lin2`: `U^{r,t}(aψ₁ + bψ₂) = a U^{r,t}ψ₁ + b U^{r,t}ψ₂` (uniqueness of classical solutions).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the facts about one family of coefficients -/
structure S57pFam (C : WholeCoeff d) (θ : Euc d → ℝ) (T : ℝ) (j : ℕ) (K : ℝ) : Prop where
  hj : 4 ≤ j
  uniq : HRS.MS.S52B.S52bUniq C T
  lin : S57pLin C T
  gen : S57pGen C T
  adj : UlAdjointInput θ C T j K

theorem s57p_conv_smul (G : Euc d → Euc d) (a : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    convGradConvW G (fun y => a * h y) x = a • convGradConvW G h x := by
  unfold convGradConvW
  rw [← integral_smul]
  congr 1; funext y
  split_ifs
  · rw [smul_smul]; congr 1; ring
  · rw [smul_smul]

theorem s57p_gen_smul (C : WholeCoeff d) (τ : ℝ) {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (a : ℝ) (x : Euc d) :
    generatorW C τ (fun y => a * u y) x = a * generatorW C τ u x := by
  have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hlap : Laplacian.laplacian (fun y => a * u y) x = a * Laplacian.laplacian u x := by
    have h := InnerProductSpace.laplacian_smul (x := x) a (f := u) hu.contDiffAt
    simpa [Pi.smul_def] using h
  have hgr : ∀ y, gradient (fun y => a * u y) y = a • gradient u y := fun y => by
    ext i
    rw [movtr_gradient_apply, PiLp.smul_apply, movtr_gradient_apply,
      fderiv_const_mul (h1.differentiable one_ne_zero y) a]
    simp
  have hnl : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d C.s)
        (fun y => C.ρ τ y * (Torus.matVec C.M.transpose (gradient (fun y => a * u y) y)) j) x) j =
      a * (convGradConvW (rieszKernelGrad d C.s)
        (fun y => C.ρ τ y * (Torus.matVec C.M.transpose (gradient u y)) j) x) j := by
    intro j
    have e : (fun y => C.ρ τ y * (Torus.matVec C.M.transpose (gradient (fun y => a * u y) y)) j) =
        fun y => a * (C.ρ τ y * (Torus.matVec C.M.transpose (gradient u y)) j) := by
      funext y
      rw [hgr y]
      simp only [Torus.matVec, map_smul, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, s57p_conv_smul]
    simp
  show C.ν * Laplacian.laplacian (fun y => a * u y) x +
      inner ℝ (C.drift τ x) (gradient (fun y => a * u y) x) - ∑ j : Fin d, (convGradConvW (rieszKernelGrad d C.s)
        (fun y => C.ρ τ y * (Torus.matVec C.M.transpose (gradient (fun y => a * u y) y)) j) x) j =
    a * (C.ν * Laplacian.laplacian u x + inner ℝ (C.drift τ x) (gradient u x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d C.s)
        (fun y => C.ρ τ y * (Torus.matVec C.M.transpose (gradient u y)) j) x) j)
  rw [hlap, hgr x, inner_smul_right, Finset.sum_congr rfl fun j _ => hnl j, ← Finset.mul_sum]
  ring

theorem s57p_norm_const_mul {u : Euc d → ℝ} {i : ℕ} (hu : ContDiff ℝ i u) (a : ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y => a * u y) x‖ ≤ |a| * ‖iteratedFDeriv ℝ i u x‖ := by
  have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := i) (a := a) (f := u) (x := x) hu.contDiffAt
  have e : (fun y => a * u y) = a • u := by funext y; simp
  rw [e]
  rw [show iteratedFDeriv ℝ i (a • u) x = a • iteratedFDeriv ℝ i u x from by
    simpa [Pi.smul_def] using this]
  rw [norm_smul, Real.norm_eq_abs]

theorem s57p_iter_lin2 {u₁ u₂ : Euc d → ℝ} {i : ℕ} (h₁ : ContDiff ℝ i u₁) (h₂ : ContDiff ℝ i u₂) (a b : ℝ)
    (x : Euc d) :
    iteratedFDeriv ℝ i (fun y => a * u₁ y + b * u₂ y) x =
      a • iteratedFDeriv ℝ i u₁ x + b • iteratedFDeriv ℝ i u₂ x := by
  have h1 : ContDiff ℝ i (a • u₁) := h₁.const_smul a
  have h2 : ContDiff ℝ i (b • u₂) := h₂.const_smul b
  have e : (fun y => a * u₁ y + b * u₂ y) = (a • u₁) + (b • u₂) := by funext y; simp
  rw [e, iteratedFDeriv_add_apply h1.contDiffAt h2.contDiffAt,
    iteratedFDeriv_const_smul_apply h₁.contDiffAt, iteratedFDeriv_const_smul_apply h₂.contDiffAt]

theorem s57p_gen_lin2 {C : WholeCoeff d} {T : ℝ} (L : S57pLin C T) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {B : ℝ}
    {u₁ u₂ : Euc d → ℝ} (h₁ : ContDiff ℝ 3 u₁) (h₂ : ContDiff ℝ 3 u₂)
    (b₁ : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i u₁ x‖ ≤ B) (b₂ : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i u₂ x‖ ≤ B)
    (a b : ℝ) (x : Euc d) :
    generatorW C τ (fun y => a * u₁ y + b * u₂ y) x = a * generatorW C τ u₁ x + b * generatorW C τ u₂ x := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (b₁ 0 (by norm_num) 0)
  have e : (fun y => a * u₁ y + b * u₂ y) = fun y => (a * u₁ y) - ((-b) * u₂ y) := by funext y; ring
  rw [e]
  have hc1 : ContDiff ℝ 3 (fun y => a * u₁ y) := contDiff_const.mul h₁
  have hc2 : ContDiff ℝ 3 (fun y => (-b) * u₂ y) := contDiff_const.mul h₂
  have hbd1 : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (fun y => a * u₁ y) x‖ ≤ (|a| + |b|) * B := by
    intro i hi y
    refine (s57p_norm_const_mul (h₁.of_le (by exact_mod_cast hi)) a y).trans ?_
    exact (mul_le_mul_of_nonneg_left (b₁ i hi y) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg b]) hB0)
  have hbd2 : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (fun y => (-b) * u₂ y) x‖ ≤ (|a| + |b|) * B := by
    intro i hi y
    refine (s57p_norm_const_mul (h₂.of_le (by exact_mod_cast hi)) (-b) y).trans ?_
    rw [abs_neg]
    exact (mul_le_mul_of_nonneg_left (b₂ i hi y) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg a]) hB0)
  rw [L.sub τ hτ _ _ _ hc1 hc2 hbd1 hbd2 x, s57p_gen_smul C τ (h₁.of_le (by norm_num)) a x,
    s57p_gen_smul C τ (h₂.of_le (by norm_num)) (-b) x]
  ring

/-- linear combinations of classical adjoint solutions are classical adjoint solutions -/
theorem s57p_classical_lin2 {C : WholeCoeff d} {T : ℝ} (L : S57pLin C T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {ψ₁ ψ₂ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ} (h₁ : IsClassicalAdjointW C t ψ₁ f₁)
    (h₂ : IsClassicalAdjointW C t ψ₂ f₂) {B : ℝ}
    (hb₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 3 (f₁ r) ∧ ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (f₁ r) x‖ ≤ B)
    (hb₂ : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 3 (f₂ r) ∧ ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (f₂ r) x‖ ≤ B)
    (a b : ℝ) :
    IsClassicalAdjointW C t (fun y => a * ψ₁ y + b * ψ₂ y) (fun r x => a * f₁ r x + b * f₂ r x) := by
  have hrT : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hgl : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, generatorW C r (fun y => a * f₁ r y + b * f₂ r y) x =
      a * generatorW C r (f₁ r) x + b * generatorW C r (f₂ r) x := fun r hr x =>
    s57p_gen_lin2 L (hrT r hr) (hb₁ r hr).1 (hb₂ r hr).1 (hb₁ r hr).2 (hb₂ r hr).2 a b x
  have hit : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ 2, ∀ x,
      iteratedFDeriv ℝ i (fun y => a * f₁ r y + b * f₂ r y) x =
        a • iteratedFDeriv ℝ i (f₁ r) x + b • iteratedFDeriv ℝ i (f₂ r) x := fun r hr i hi x =>
    s57p_iter_lin2 ((h₁.c2 r hr).of_le (by exact_mod_cast hi)) ((h₂.c2 r hr).of_le (by exact_mod_cast hi)) a b x
  refine ⟨fun r hr => (contDiff_const.mul (h₁.c2 r hr)).add (contDiff_const.mul (h₂.c2 r hr)), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro j hj
    obtain ⟨B₁, hB₁⟩ := h₁.bdd j hj
    obtain ⟨B₂, hB₂⟩ := h₂.bdd j hj
    refine ⟨|a| * B₁ + |b| * B₂, fun r hr x => ?_⟩
    rw [hit r hr j hj x]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left (hB₁ r hr x) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hB₂ r hr x) (abs_nonneg _))
  · intro j hj
    have := ((h₁.cont_c2 j hj).const_smul a).add ((h₂.cont_c2 j hj).const_smul b)
    refine this.congr fun p => ?_
    rw [hit p.1.1 p.1.2 j hj p.2]; rfl
  · funext x
    show a * f₁ t x + b * f₂ t x = a * ψ₁ x + b * ψ₂ x
    rw [h₁.terminal, h₂.terminal]
  · intro x r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have := ((h₁.time_deriv x r hr).const_mul a).add ((h₂.time_deriv x r hr).const_mul b)
    convert this using 1
    rw [hgl r hr' x]; ring
  · have h := ((h₁.cont_time_deriv).const_smul a).add ((h₂.cont_time_deriv).const_smul b)
    refine h.congr fun p => ?_
    show a * generatorW C (p.1 : ℝ) (f₁ p.1) p.2 + b * generatorW C (p.1 : ℝ) (f₂ p.1) p.2 =
      generatorW C (p.1 : ℝ) (fun y => a * f₁ p.1 y + b * f₂ p.1 y) p.2
    exact (hgl p.1.1 p.1.2 p.2).symm
  · obtain ⟨B₁, hB₁⟩ := h₁.bdd_time_deriv
    obtain ⟨B₂, hB₂⟩ := h₂.bdd_time_deriv
    refine ⟨|a| * B₁ + |b| * B₂, fun r hr x => ?_⟩
    show |generatorW C r (fun y => a * f₁ r y + b * f₂ r y) x| ≤ _
    rw [hgl r hr x]
    have h1 := hB₁ r hr x
    have h2 := hB₂ r hr x
    calc |a * generatorW C r (f₁ r) x + b * generatorW C r (f₂ r) x|
        ≤ |a * generatorW C r (f₁ r) x| + |b * generatorW C r (f₂ r) x| := abs_add_le _ _
      _ = |a| * |generatorW C r (f₁ r) x| + |b| * |generatorW C r (f₂ r) x| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * (B₁ * (1 + ‖x‖)) + |b| * (B₂ * (1 + ‖x‖)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (|a| * B₁ + |b| * B₂) * (1 + ‖x‖) := by ring

/-- the orbit data of a bounded smooth terminal function -/
theorem s57p_orb {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (j : ℕ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ {C : WholeCoeff d} {T K : ℝ}, UlAdjointInput θ C T j K → ∀ {ψ : Euc d → ℝ} {B : ℝ}, 0 ≤ B →
      ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) ψ →
      (∀ l ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ B) → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsClassicalAdjointW C t ψ (fun r => propagatorW C r t ψ) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ j (propagatorW C r t ψ) ∧
        ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (propagatorW C r t ψ) x‖ ≤ |K| * (Cu * B) := by
  obtain ⟨Cu, hCu0, hCu⟩ := s55_ul_of_sup hθ (j + 1 + ⌈(d : ℝ) / 2⌉₊)
  refine ⟨Cu, hCu0, fun {C T K} adj {ψ B} hB hψ hb t ht => ?_⟩
  have hul : ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ ψ ≤ ENNReal.ofReal (Cu * B) :=
    hCu ψ B hB hψ (fun l hl idx x => (s57p_abs_partialDeriv_le idx ψ x).trans (hb l hl x))
  have hfin : ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ ψ < ⊤ := lt_of_le_of_lt hul ENNReal.ofReal_lt_top
  have hCuB : 0 ≤ Cu * B := mul_nonneg hCu0 hB
  have hulr : (ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ ψ).toReal ≤ Cu * B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hul
    rwa [ENNReal.toReal_ofReal hCuB] at this
  obtain ⟨hex, -, -⟩ := adj t t ht.1 le_rfl ht.2 ψ hψ hfin
  refine ⟨propagatorW_isClassical hex, fun r hr => ?_⟩
  obtain ⟨-, hmem, hcb⟩ := adj r t hr.1 hr.2 ht.2 ψ hψ hfin
  refine ⟨hmem.1, fun i hi x => ?_⟩
  refine (s57p_norm_le_cbNorm hmem hi x).trans (hcb.trans ?_)
  calc K * (ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ ψ).toReal ≤ |K| * (ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ ψ).toReal :=
        mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
    _ ≤ |K| * (Cu * B) := mul_le_mul_of_nonneg_left hulr (abs_nonneg _)

/-- **linearity of the adjoint propagator** on bounded smooth data -/
theorem s57p_prop_lin2 {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {j : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (F : S57pFam C θ T j K) {ψ₁ ψ₂ : Euc d → ℝ} {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) ψ₁)
    (b₁ : ∀ l ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l ψ₁ x‖ ≤ B₁)
    (h₂ : ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) ψ₂)
    (b₂ : ∀ l ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l ψ₂ x‖ ≤ B₂) (a b : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW C r t (fun y => a * ψ₁ y + b * ψ₂ y) =
      fun x => a * propagatorW C r t ψ₁ x + b * propagatorW C r t ψ₂ x := by
  obtain ⟨Cu, hCu0, hCu⟩ := s57p_orb hθ j
  have hB : 0 ≤ |a| * B₁ + |b| * B₂ := by positivity
  have hψ : ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (fun y => a * ψ₁ y + b * ψ₂ y) :=
    (contDiff_const.mul h₁).add (contDiff_const.mul h₂)
  have hbψ : ∀ l ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l (fun y => a * ψ₁ y + b * ψ₂ y) x‖ ≤
      |a| * B₁ + |b| * B₂ := by
    intro l hl x
    rw [s57p_iter_lin2 (h₁.of_le (by exact_mod_cast hl)) (h₂.of_le (by exact_mod_cast hl))]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left (b₁ l hl x) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (b₂ l hl x) (abs_nonneg _))
  obtain ⟨c1, d1⟩ := hCu F.adj hB₁ h₁ b₁ t ht
  obtain ⟨c2, d2⟩ := hCu F.adj hB₂ h₂ b₂ t ht
  obtain ⟨c3, d3⟩ := hCu F.adj hB hψ hbψ t ht
  have hj3 : 3 ≤ j := by have := F.hj; omega
  have hcl := s57p_classical_lin2 F.lin ht c1 c2 (B := |K| * (Cu * max B₁ B₂))
    (fun r hr => ⟨(d1 r hr).1.of_le (by exact_mod_cast hj3), fun i hi x =>
      ((d1 r hr).2 i (by omega) x).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_left _ _) hCu0)
        (abs_nonneg _))⟩)
    (fun r hr => ⟨(d2 r hr).1.of_le (by exact_mod_cast hj3), fun i hi x =>
      ((d2 r hr).2 i (by omega) x).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right _ _) hCu0)
        (abs_nonneg _))⟩) a b
  intro r hr
  have := F.uniq t ht _ _ _ c3 hcl r hr
  funext x
  exact congrFun this x

end HRS.MS.FixEq
