import HRS.Stochastic.Ito
import HRS.Stochastic.Particle
import HRS.Stochastic.SelectedFlow

/-!
# The empirical Itô engine, Lemma 3.6 and Proposition B.3

Package PART-01, packet P1.  See `HRS/Stochastic/PART01_REST_SPEC.md` §1.3, §2, §6.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d N : ℕ}

/-! ### Periodicity on the covering space -/

theorem exists_lattice_of_mk_eq {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ n : Lattice d, x = y + Lattice.toEuc n := by
  have h0 : Torus.mk (x - y) = 0 := by rw [mk_sub', h, sub_self]
  have hi : ∀ i : Fin d, ∃ n : ℤ, n • (1 : ℝ) = (x - y) i := fun i => by
    have := congrFun h0 i
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 this
  choose n hn using hi
  refine ⟨n, ?_⟩
  ext i
  have := hn i
  simp only [zsmul_eq_mul, mul_one] at this
  simp only [Lattice.toEuc, PiLp.add_apply]
  have h2 : (x - y) i = x i - y i := rfl
  linarith

theorem periodic_rep_mk {E : Type*} (G : Euc d → E)
    (hG : ∀ (x : Euc d) (n : Lattice d), G (x + Lattice.toEuc n) = G x) (y : Euc d) :
    G (Torus.rep (Torus.mk y)) = G y := by
  obtain ⟨n, hn⟩ := exists_lattice_of_mk_eq (x := Torus.rep (Torus.mk y)) (y := y)
    (Torus.mk_rep _)
  rw [hn, hG]

theorem fderiv_lift_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Torus d → E) (x : Euc d) (n : Lattice d) :
    fderiv ℝ (Torus.lift φ) (x + Lattice.toEuc n) = fderiv ℝ (Torus.lift φ) x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact Torus.lift_periodic φ z n

theorem grad_mk (φ : Torus d → ℝ) (y : Euc d) :
    Torus.grad φ (Torus.mk y) = gradient (Torus.lift φ) y :=
  periodic_rep_mk (gradient (Torus.lift φ)) (fun x n => by
    unfold gradient; rw [fderiv_lift_periodic]) y

theorem laplacian_mk (φ : Torus d → ℝ) (y : Euc d) :
    Torus.laplacian φ (Torus.mk y) = Laplacian.laplacian (Torus.lift φ) y :=
  periodic_rep_mk (Laplacian.laplacian (Torus.lift φ)) (fun x n => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift φ) (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp only [Torus.iteratedFDeriv_lift_periodic]) y

theorem fderiv_lift_apply_eq_inner (φ : Torus d → ℝ) (y v : Euc d) :
    fderiv ℝ (Torus.lift φ) y v = inner ℝ (Torus.grad φ (Torus.mk y)) v := by
  rw [grad_mk]
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]


/-! ### Empirical sums on the covering space -/

/-- `Y ↦ N⁻¹ ∑ i, g (Y i)` on the covering space `Fin N → Euc d`. -/
def sumLift (N : ℕ) (g : Euc d → ℝ) (Y : Fin N → Euc d) : ℝ := (N : ℝ)⁻¹ * ∑ i, g (Y i)

theorem contDiff_sumLift {n : WithTop ℕ∞} {g : Euc d → ℝ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (sumLift N g) :=
  contDiff_const.mul (ContDiff.sum fun i _ => hg.comp (contDiff_apply ℝ (Euc d) i))

theorem hasFDerivAt_sumLift {g : Euc d → ℝ} (hg : Differentiable ℝ g) (Y : Fin N → Euc d) :
    HasFDerivAt (sumLift N g)
      ((N : ℝ)⁻¹ • ∑ i, (fderiv ℝ g (Y i)).comp (ContinuousLinearMap.proj i)) Y := by
  have h : ∀ i ∈ Finset.univ, HasFDerivAt (fun Z : Fin N → Euc d => g (Z i))
      ((fderiv ℝ g (Y i)).comp (ContinuousLinearMap.proj i)) Y := fun i _ =>
    (hg (Y i)).hasFDerivAt.comp Y (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt
  exact (HasFDerivAt.fun_sum h).const_mul ((N : ℝ)⁻¹)

theorem fderiv_sumLift_apply {g : Euc d → ℝ} (hg : Differentiable ℝ g) (Y u : Fin N → Euc d) :
    fderiv ℝ (sumLift N g) Y u = (N : ℝ)⁻¹ * ∑ i, fderiv ℝ g (Y i) (u i) := by
  rw [(hasFDerivAt_sumLift hg Y).fderiv]
  simp

theorem iteratedFDeriv_sumLift {g : Euc d → ℝ} {n : ℕ} (hg : ContDiff ℝ n g)
    (Y : Fin N → Euc d) (m : Fin n → (Fin N → Euc d)) :
    iteratedFDeriv ℝ n (sumLift N g) Y m =
      (N : ℝ)⁻¹ * ∑ i, iteratedFDeriv ℝ n g (Y i) (fun a => m a i) := by
  have e : sumLift N g = fun Z => (N : ℝ)⁻¹ • ∑ i : Fin N,
      (g ∘ ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)) Z := by
    funext Z; simp [sumLift]
  rw [e, iteratedFDeriv_const_smul_apply' (hf := ?_), iteratedFDeriv_fun_sum_apply]
  · simp only [smul_apply, sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hg Y le_rfl]
    rfl
  · exact fun i _ => (hg.comp (contDiff_apply ℝ (Euc d) i)).contDiffAt
  · exact (ContDiff.sum fun i _ => hg.comp (contDiff_apply ℝ (Euc d) i)).contDiffAt


/-! ### Joint continuity helpers -/

theorem continuousOn_Icc_prod_of_subtype {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z]
    {a b : ℝ} {G : ℝ × E → Z} (h : Continuous fun p : Set.Icc a b × E => G (p.1, p.2)) :
    ContinuousOn G (Set.Icc a b ×ˢ (Set.univ : Set E)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hj : Continuous fun q : ↥(Set.Icc a b ×ˢ (Set.univ : Set E)) =>
      ((⟨q.1.1, q.2.1⟩ : Set.Icc a b), q.1.2) :=
    Continuous.prodMk (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _)
      (continuous_snd.comp continuous_subtype_val)
  exact h.comp hj

theorem IsC12Test.contOn_iter {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) {j : ℕ}
    (hj : j ≤ 2) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) :=
  continuousOn_Icc_prod_of_subtype (hf.cont_c2 j hj)

theorem IsC12Test.contOn_lift {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => Torus.lift (f p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ) := by
  have h := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp_continuousOn
    (hf.contOn_iter (j := 0) (by norm_num))
  refine h.congr fun p _ => ?_
  simp [iteratedFDeriv_zero_eq_comp]

theorem IsC12Test.contOn_timeDeriv {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => ft p.1 (Torus.mk p.2)) (Set.Icc 0 t ×ˢ Set.univ) := by
  refine continuousOn_Icc_prod_of_subtype ?_
  exact hf.cont_time_deriv.comp (continuous_fst.prodMk (Torus.continuous_mk.comp continuous_snd))

theorem fderiv_eq_curry (g : Euc d → ℝ) (y : Euc d) :
    fderiv ℝ g y = continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 g y) := by
  ext u
  simp

/-- `D²g` as a continuous image of `iteratedFDeriv 2 g`. -/
def curry2 (d : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) :
    Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
  ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ : _ ≃ₗᵢ[ℝ] _).toContinuousLinearEquiv :
      _ ≃L[ℝ] _).toContinuousLinearMap.comp
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => Euc d) ℝ : _ ≃ₗᵢ[ℝ] _) L)

theorem continuous_curry2 (d : ℕ) : Continuous (curry2 d) :=
  continuous_const.clm_comp
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => Euc d) ℝ : _ ≃ₗᵢ[ℝ] _).continuous)

theorem fderiv_fderiv_eq_curry2 (g : Euc d → ℝ) (y : Euc d) :
    fderiv ℝ (fderiv ℝ g) y = curry2 d (iteratedFDeriv ℝ 2 g y) := by
  have h : fderiv ℝ g = fun z => continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 g z) :=
    funext (fderiv_eq_curry g)
  rw [h]
  have := LinearIsometryEquiv.comp_fderiv (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ)
    (f := iteratedFDeriv ℝ 1 g) (x := y)
  simp only [Function.comp_def] at this
  rw [this]
  rfl


/-! ### The empirical lift of a `C^{1,2}` test -/

/-- `F r Y := N⁻¹ ∑ i, f r (Torus.mk (Y i))` on the covering space. -/
def empiricalLift (N : ℕ) (f : ℝ → Torus d → ℝ) (r : ℝ) (Y : Fin N → Euc d) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, f r (Torus.mk (Y i))

theorem empiricalLift_eq (N : ℕ) (f : ℝ → Torus d → ℝ) (r : ℝ) :
    empiricalLift N f r = sumLift N (Torus.lift (f r)) := rfl

theorem IsC12Test.continuousOn_time {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft)
    (x : Torus d) : ContinuousOn (fun r => f r x) (Set.Icc 0 t) := by
  have h := ContinuousOn.comp hf.contOn_lift
    (continuous_id.prodMk continuous_const : Continuous fun r : ℝ => (r, Torus.rep x)).continuousOn
    (fun r (hr : r ∈ Set.Icc 0 t) => (⟨hr, mem_univ _⟩ : (r, Torus.rep x) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))))
  refine h.congr fun r _ => ?_
  simp [Torus.lift, Torus.mk_rep]

theorem IsC12Test.continuousOn_timeDeriv_x {t : ℝ} {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (x : Torus d) : ContinuousOn (fun r => ft r x) (Set.Icc 0 t) := by
  have h := ContinuousOn.comp hf.contOn_timeDeriv
    (continuous_id.prodMk continuous_const : Continuous fun r : ℝ => (r, Torus.rep x)).continuousOn
    (fun r (hr : r ∈ Set.Icc 0 t) => (⟨hr, mem_univ _⟩ : (r, Torus.rep x) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))))
  refine h.congr fun r _ => ?_
  simp [Torus.mk_rep]

theorem IsC12Test.hasDerivWithinAt_Icc {t : ℝ} (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (x : Torus d) {r : ℝ} (hr : r ∈ Set.Icc 0 t) :
    HasDerivWithinAt (fun r => f r x) (ft r x) (Set.Icc 0 t) r := by
  have hdiff : DifferentiableOn ℝ (fun r => f r x) (Set.Ioo 0 t) := fun r hr =>
    (hf.time_deriv x r hr).differentiableAt.differentiableWithinAt
  have hder : ∀ r ∈ Set.Ioo 0 t, deriv (fun r => f r x) r = ft r x := fun r hr =>
    (hf.time_deriv x r hr).deriv
  rcases hr.1.eq_or_lt with rfl | h0
  · have h1 : Tendsto (fun r => ft r x) (𝓝[>] 0) (𝓝 (ft 0 x)) :=
      (((hf.continuousOn_timeDeriv_x x) 0 ⟨le_rfl, ht.le⟩).tendsto).mono_left
        (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsGT ht) Ioo_subset_Icc_self))
    have h2 := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      (((hf.continuousOn_time x) 0 ⟨le_rfl, ht.le⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT ht)
      (h1.congr' (eventually_of_mem (Ioo_mem_nhdsGT ht) fun r hr => (hder r hr).symm))
    exact h2.mono Icc_subset_Ici_self
  rcases hr.2.eq_or_lt with rfl | h1
  · have h1 : Tendsto (fun r => ft r x) (𝓝[<] r) (𝓝 (ft r x)) :=
      (((hf.continuousOn_timeDeriv_x x) r ⟨ht.le, le_rfl⟩).tendsto).mono_left
        (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT ht) Ioo_subset_Icc_self))
    have h2 := hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
      (((hf.continuousOn_time x) r ⟨ht.le, le_rfl⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsLT ht)
      (h1.congr' (eventually_of_mem (Ioo_mem_nhdsLT ht) fun r hr => (hder r hr).symm))
    exact h2.mono Icc_subset_Iic_self
  · exact (hf.time_deriv x r ⟨h0, h1⟩).hasDerivWithinAt


theorem contOn_comp_coord {Z : Type*} [TopologicalSpace Z] {t : ℝ} {G : ℝ × Euc d → Z}
    (h : ContinuousOn G (Set.Icc 0 t ×ˢ Set.univ)) (i : Fin N) :
    ContinuousOn (fun p : ℝ × (Fin N → Euc d) => G (p.1, p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) :=
  ContinuousOn.comp h (f := fun p : ℝ × (Fin N → Euc d) => (p.1, p.2 i))
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)).continuousOn
    (fun p hp => ⟨hp.1, mem_univ _⟩)

/-- The right-composition `B ↦ A_i ∘ B ∘ proj_i` used to express `D²` of `sumLift`. -/
def psiComp (d N : ℕ) (i : Fin N) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    (Fin N → Euc d) →L[ℝ] (Fin N → Euc d) →L[ℝ] ℝ :=
  (((ContinuousLinearMap.compL ℝ (Fin N → Euc d) (Euc d) ℝ).flip
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)) :
      (Euc d →L[ℝ] ℝ) →L[ℝ] ((Fin N → Euc d) →L[ℝ] ℝ)).comp
    (B.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i))

theorem continuous_psiComp (d N : ℕ) (i : Fin N) : Continuous (psiComp d N i) :=
  continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

theorem fderiv_fderiv_sumLift {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (Y : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (sumLift N g)) Y =
      (N : ℝ)⁻¹ • ∑ i, psiComp d N i (fderiv ℝ (fderiv ℝ g) (Y i)) := by
  ext u v
  have h := iteratedFDeriv_two_apply (𝕜 := ℝ) (sumLift N g) Y ![u, v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, iteratedFDeriv_sumLift hg]
  simp [psiComp, iteratedFDeriv_two_apply]

instance instContinuousAddCLM2 (d N : ℕ) :
    ContinuousAdd ((Fin N → Euc d) →L[ℝ] (Fin N → Euc d) →L[ℝ] ℝ) := by
  have : IsTopologicalAddGroup ((Fin N → Euc d) →L[ℝ] (Fin N → Euc d) →L[ℝ] ℝ) := inferInstance
  exact this.toContinuousAdd

theorem isC12On_empiricalLift {t : ℝ} (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) : IsC12On t Set.univ (empiricalLift N f) := by
  have hcd : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (Torus.lift (f r)) := fun r hr => hf.c2 r hr
  have hcdN : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (empiricalLift N f r) := fun r hr =>
    contDiff_sumLift (hcd r hr)
  have hA : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (Torus.lift (f p.1)) (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) := fun i => by
    have h := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn
      (contOn_comp_coord (N := N) (hf.contOn_iter (j := 1) (by norm_num)) i)
    exact h.congr fun p _ => by simp [fderiv_eq_curry]
  have hB : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) := fun i => by
    have h := (continuous_curry2 d).comp_continuousOn
      (contOn_comp_coord (N := N) (hf.contOn_iter (j := 2) (by norm_num)) i)
    exact h.congr fun p _ => by simp [fderiv_fderiv_eq_curry2]
  refine
    { cont := ?_
      hasFDerivAt := ?_
      hasFDerivAt_fderiv := ?_
      cont_fderiv := ?_
      cont_fderiv₂ := ?_
      hasDerivWithinAt := ?_
      cont_deriv := ?_ }
  · have : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        (N : ℝ)⁻¹ * ∑ i, Torus.lift (f p.1) (p.2 i)) (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        contOn_comp_coord (N := N) hf.contOn_lift i)
    exact this
  · intro r hr Y _
    exact (((hcdN r hr).differentiable (by norm_num)) Y).hasFDerivAt
  · intro r hr Y _
    exact ((((hcdN r hr).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) Y).hasFDerivAt
  · let R : Fin N → (Euc d →L[ℝ] ℝ) →L[ℝ] ((Fin N → Euc d) →L[ℝ] ℝ) := fun i =>
      (ContinuousLinearMap.compL ℝ (Fin N → Euc d) (Euc d) ℝ).flip
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)
    have h1 : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        R i (fderiv ℝ (Torus.lift (f p.1)) (p.2 i))) (Set.Icc 0 t ×ˢ Set.univ) := fun i =>
      (R i).continuous.comp_continuousOn (hA i)
    have h2 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        ∑ i, R i (fderiv ℝ (Torus.lift (f p.1)) (p.2 i))) (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_finsetSum _ fun i _ => h1 i
    have h3 := h2.const_smul ((N : ℝ)⁻¹)
    refine h3.congr fun p hp => ?_
    rw [empiricalLift_eq, (hasFDerivAt_sumLift ((hcd p.1 hp.1).differentiable (by norm_num)) p.2).fderiv]
    rfl
  · have h1 : ∀ i : Fin N, ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        psiComp d N i (fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) (p.2 i)))
        (Set.Icc 0 t ×ˢ Set.univ) := fun i =>
      (continuous_psiComp d N i).comp_continuousOn (hB i)
    have h2 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        ∑ i, psiComp d N i (fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) (p.2 i)))
        (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_finsetSum _ fun i _ => h1 i
    have h3 := h2.const_smul ((N : ℝ)⁻¹)
    refine h3.congr fun p hp => ?_
    rw [empiricalLift_eq]
    exact fderiv_fderiv_sumLift (hcd p.1 hp.1) p.2
  · intro Y _ r hr
    have h1 : HasDerivWithinAt (fun r => empiricalLift N f r Y)
        ((N : ℝ)⁻¹ * ∑ i, ft r (Torus.mk (Y i))) (Set.Icc 0 t) r :=
      (HasDerivWithinAt.fun_sum fun i _ => hf.hasDerivWithinAt_Icc ht (Torus.mk (Y i)) hr).const_mul _
    rwa [h1.derivWithin (uniqueDiffOn_Icc ht r hr)]
  · have : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        (N : ℝ)⁻¹ * ∑ i, ft p.1 (Torus.mk (p.2 i))) (Set.Icc 0 t ×ˢ Set.univ) :=
      continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        contOn_comp_coord (N := N) hf.contOn_timeDeriv i)
    refine this.congr fun p hp => ?_
    have h1 : HasDerivWithinAt (fun r => empiricalLift N f r p.2)
        ((N : ℝ)⁻¹ * ∑ i, ft p.1 (Torus.mk (p.2 i))) (Set.Icc 0 t) p.1 :=
      (HasDerivWithinAt.fun_sum fun i _ =>
        hf.hasDerivWithinAt_Icc ht (Torus.mk (p.2 i)) hp.1).const_mul _
    exact h1.derivWithin (uniqueDiffOn_Icc ht p.1 hp.1)


/-! ### The covering-space lift of a contact-allowing solution (engine, step E-a) -/

theorem mk_add' (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i; simp [Torus.mk]

theorem measurable_torusGrad {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    Measurable (Torus.grad φ) := by
  have hc : Continuous (gradient (Torus.lift φ)) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      (hφ.continuous_fderiv (by norm_num))
  exact hc.measurable.comp (measurable_torusRep d)

/-- The particle drift as a `Fin N → Euc d`-valued function of the configuration. -/
def driftVec (D : DynData d) (x : Config d N) : Fin N → Euc d := fun i => particleDrift D x i

theorem measurable_driftVec {D : DynData d} (hV : Torus.IsCk 2 D.V) :
    Measurable (driftVec D : Config d N → Fin N → Euc d) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hsum : Measurable fun x : Config d N =>
      ∑ j ∈ Finset.univ.erase i, Torus.matVec D.M (periodicRieszGrad d D.s (x i - x j)) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)).measurable.comp
      ((KernelGrad.measurable_periodicRieszGrad D.hsd).comp ((measurable_pi_apply i).sub (measurable_pi_apply j)))
  have h2 : Measurable fun x : Config d N => Torus.grad D.V (x i) :=
    (measurable_torusGrad hV).comp (measurable_pi_apply i)
  unfold driftVec particleDrift
  exact (hsum.const_smul ((1 : ℝ) / N)).sub h2

/-- The drift process `t ↦ b(X_t)`. -/
def driftProc (D : DynData d) (X : ℝ≥0 → Ω → Config d N) : ℝ≥0 → Ω → (Fin N → Euc d) :=
  fun t ω => driftVec D (X t ω)

/-- The explicit lift to the covering space,
`Y_t = rep ∘ X_0 + ∫_0^t b(X_s) ds + ∑_k (W'_k(t) - W'_k(0)) σ_k`. -/
def liftProc (D : DynData d) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ≥0 → Ω → (Fin N → Euc d) :=
  fun t ω => (fun i => Torus.rep (X 0 ω i)) +
    (∫ s in Set.Icc (0 : ℝ) t, driftProc D X (Real.toNNReal s) ω) +
    ∑ k, (W' t ω k - W' 0 ω k) • liftedNoise D k

theorem liftProc_zero (D : DynData d) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) :
    liftProc D W' X 0 ω = fun i => Torus.rep (X 0 ω i) := by
  simp [liftProc]

theorem liftProc_eq_add (D : DynData d) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (t : ℝ≥0) (ω : Ω) :
    liftProc D W' X t ω = liftProc D W' X 0 ω +
      (∫ s in Set.Icc (0 : ℝ) t, driftProc D X (Real.toNNReal s) ω) +
      ∑ k, (W' t ω k - W' 0 ω k) • liftedNoise D k := by
  rw [liftProc_zero]; rfl

section Lift

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
  {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}

theorem IsFilteredSolution.measurable_init (hF : IsFilteredSolution P ℱ W' W X) (s : ℝ) :
    Measurable[ℱ s] (X 0) := by
  rcases le_or_gt 0 s with hs | hs
  · exact (hF.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
  · have h := hF.progressive.adapted s
    have e : ofNNRealTime X s = X 0 := by
      funext ω
      simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
    rw [e] at h
    exact h

theorem isProgressive_driftProc (hV : Torus.IsCk 2 D.V) (hF : IsFilteredSolution P ℱ W' W X) :
    IsProgressive ℱ (ofNNRealTime (driftProc D X)) :=
  fun i => (measurable_driftVec hV).comp (hF.progressive i)

theorem IsContactStrongSolution.ae_integrableOn_drift {T : ℝ} {X₀ : Ω → Config d N}
    (hX : IsContactStrongSolution P D T X₀ W X) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 t) := by
  obtain ⟨Y₀, hY, hXY⟩ := hX.lift
  filter_upwards [hY] with ω hω
  have h := (hω (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht0]; exact htT)).1
  rw [Real.coe_toNNReal _ ht0] at h
  rw [IntegrableOn, integrable_pi_iff]
  intro i
  have := h i
  rw [hXY]
  exact this

theorem IsContactStrongSolution.ae_lift_eq {T : ℝ} {X₀ : Ω → Config d N}
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = fun i => Torus.mk (liftProc D W' X t ω i) := by
  obtain ⟨Y₀, hY, hXY⟩ := hX.lift
  filter_upwards [hY, hF.coords] with ω hω hc t ht
  obtain ⟨hint, heq⟩ := hω t ht
  funext i
  have hnoise : (∑ k, (W' t ω k - W' 0 ω k) • liftedNoise D k) i =
      Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i) := by
    ext j
    simp only [Finset.sum_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Pi.smul_apply,
      liftedNoise, Fintype.sum_prod_type, hc t, hc 0]
    simp [Pi.single_apply, mul_comm]
  have hA : (∫ s in Set.Icc (0 : ℝ) t, driftProc D X (Real.toNNReal s) ω) i =
      ∫ s in Set.Icc (0 : ℝ) t, particleDrift D (X (Real.toNNReal s) ω) i := by
    have hI : IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 t) := by
      rw [IntegrableOn, integrable_pi_iff]
      intro j
      have := hint j
      rw [hXY]
      exact this
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integral_comp_comm hI).symm
  have hXi : X t ω i = Torus.mk (Y₀ t ω i) := by rw [hXY]; rfl
  have hX0 : X 0 ω i = Torus.mk (Y₀ 0 ω i) := by rw [hXY]; rfl
  rw [hXi, heq i]
  simp only [liftProc]
  simp only [Pi.add_apply, mk_add']
  rw [hnoise, hA, Torus.mk_rep, hX0, hXY]

end Lift


/-! ### Deterministic algebra of the empirical Itô drift -/

section Algebra

/-- The off-diagonal kernel of the interaction pairing (junk `0` on the diagonal). -/
def interKernel (D : DynData d) (ψ : Torus d → ℝ) (x y : Torus d) : ℝ :=
  if x = y then 0 else
    inner ℝ (Torus.grad ψ x - Torus.grad ψ y) (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))

theorem interactionPairing_eq_kernel (D : DynData d) (ψ : Torus d → ℝ) (ν : Measure (Torus d)) :
    interactionPairing D ψ ν ν = (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂ν ∂ν := rfl

theorem interactionPairing_empirical {D : DynData d} {ψ : Torus d → ℝ} (hN : 0 < N)
    (X : Config d N) :
    interactionPairing D ψ (empirical X) (empirical X)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, interKernel D ψ (X i) (X j)) := by
  rw [interactionPairing_eq_kernel]
  congr 1
  have h : ∀ x : Torus d, (∫ y, interKernel D ψ x y ∂(empirical X))
      = (N : ℝ)⁻¹ * ∑ j, interKernel D ψ x (X j) := fun x => pair_empirical hN X _
  simp only [h]
  exact pair_empirical hN X (fun x => (N : ℝ)⁻¹ * ∑ j, interKernel D ψ x (X j))

/-- Symmetrisation of the label-off-diagonal sum (the kernel `w` is odd). -/
theorem sum_inner_offdiag_symm {N : ℕ} (v : Fin N → Euc d) (w : Fin N → Fin N → Euc d)
    (hodd : ∀ i j, w j i = -w i j) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i) (w i j)
      = (1 / 2 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i - v j) (w i j) := by
  have hB : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v j) (w i j)
      = -∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i) (w i j) := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.erase j)
      (fun x y => by simp [Finset.mem_erase, ne_comm])]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hodd y x, inner_neg_right]
  simp only [inner_sub_left, Finset.sum_sub_distrib]
  rw [hB]
  ring

theorem laplacian_eq_sum_fderiv {g : Euc d → ℝ} (y : Euc d) :
    Laplacian.laplacian g y = ∑ j : Fin d,
      fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
  have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin d) ℝ)) y
  rw [h]
  simp [iteratedFDeriv_two_apply]

theorem psiComp_apply' (i : Fin N) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (u v : Fin N → Euc d) :
    psiComp d N i B u v = B (u i) (v i) := by
  simp [psiComp]

/-- The second-order term of `sumLift` along the Brownian directions. -/
theorem sum_fderiv_fderiv_sumLift_liftedNoise (D : DynData d) {g : Euc d → ℝ}
    (hg : ContDiff ℝ 2 g) (Y : Fin N → Euc d) :
    ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (sumLift N g)) Y (liftedNoise D k) (liftedNoise D k)
      = (2 * D.invβ) * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin d,
          fderiv ℝ (fderiv ℝ g) (Y i) (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) := by
  have hc : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ :=
    Real.sq_sqrt (by have := D.hβ; positivity)
  have hσ : ∀ (i' : Fin N) (j : Fin d) (i : Fin N), liftedNoise D (i', j) i
      = if i = i' then Real.sqrt (2 * D.invβ) • EuclideanSpace.single j 1 else 0 := by
    intro i' j i
    simp [liftedNoise, Pi.single_apply]
  simp only [fderiv_fderiv_sumLift hg, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, psiComp_apply', Finset.smul_sum]
  have hk : ∀ (i' : Fin N) (j : Fin d),
      ∑ i : Fin N, (N : ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ g) (Y i))
          (liftedNoise D (i', j) i) (liftedNoise D (i', j) i)
        = (N : ℝ)⁻¹ * (2 * D.invβ) *
          fderiv ℝ (fderiv ℝ g) (Y i') (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
    intro i' j
    rw [Finset.sum_eq_single i']
    · simp only [hσ, if_true, ContinuousLinearMap.map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      linear_combination ((N : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ g) (Y i')
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) * hc
    · intro i _ hi
      simp [hσ, hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Fintype.sum_prod_type]
  simp only [hk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Algebra

section Pointwise

theorem derivWithin_empiricalLift {t : ℝ} (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {r : ℝ} (hr : r ∈ Set.Icc 0 t) (Y : Fin N → Euc d) :
    derivWithin (fun r => empiricalLift N f r Y) (Set.Icc 0 t) r
      = (N : ℝ)⁻¹ * ∑ i, ft r (Torus.mk (Y i)) := by
  have h1 : HasDerivWithinAt (fun r => empiricalLift N f r Y)
      ((N : ℝ)⁻¹ * ∑ i, ft r (Torus.mk (Y i))) (Set.Icc 0 t) r :=
    (HasDerivWithinAt.fun_sum fun i _ => hf.hasDerivWithinAt_Icc ht (Torus.mk (Y i)) hr).const_mul _
  exact h1.derivWithin (uniqueDiffOn_Icc ht r hr)

theorem fderiv_sumLift_lift_apply {φ : Torus d → ℝ} (hφ : ContDiff ℝ 2 (Torus.lift φ))
    (Y u : Fin N → Euc d) :
    fderiv ℝ (sumLift N (Torus.lift φ)) Y u
      = (N : ℝ)⁻¹ * ∑ i, inner ℝ (Torus.grad φ (Torus.mk (Y i))) (u i) := by
  rw [fderiv_sumLift_apply (hφ.differentiable (by norm_num))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_lift_apply_eq_inner]

theorem sum_lap_eq {φ : Torus d → ℝ} (y : Euc d) :
    ∑ j : Fin d, fderiv ℝ (fderiv ℝ (Torus.lift φ)) y (EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1)
      = Torus.laplacian φ (Torus.mk y) := by
  rw [laplacian_mk, laplacian_eq_sum_fderiv]

/-- The label-off-diagonal empirical sum equals the symmetrised interaction pairing. -/
theorem offdiag_identity (D : DynData d) (ψ : Torus d → ℝ) (hN : 0 < N) (X : Config d N)
    (hcol : X ∉ collisionSet d N ∨ D.M = 0) :
    (N : ℝ)⁻¹ * ∑ i, (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        inner ℝ (Torus.grad ψ (X i)) (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, interKernel D ψ (X i) (X j)) := by
  rcases hcol with hcol | hM
  · have hodd : ∀ i j, Torus.matVec D.M (periodicRieszGrad d D.s (X j - X i))
        = -Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)) := by
      intro i j
      rw [show X j - X i = -(X i - X j) from (neg_sub _ _).symm,
        KernelGrad.periodicRieszGrad_neg_of_lt D.hsd]
      simp only [Torus.matVec, map_neg]
    have hsym : ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (Torus.grad ψ (X i))
            (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
        = (1 / 2 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (Torus.grad ψ (X i) - Torus.grad ψ (X j))
            (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j))) :=
      sum_inner_offdiag_symm (fun i => Torus.grad ψ (X i))
        (fun i j => Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
        (fun i j => hodd i j)
    have hk : ∀ i, ∑ j, interKernel D ψ (X i) (X j)
        = ∑ j ∈ Finset.univ.erase i, inner ℝ (Torus.grad ψ (X i) - Torus.grad ψ (X j))
            (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j))) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have h0 : interKernel D ψ (X i) (X i) = 0 := by simp [interKernel]
      rw [h0, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : X i ≠ X j := fun h => hcol ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h⟩
      simp [interKernel, hne]
    simp only [← Finset.mul_sum, hk]
    rw [hsym]
    ring
  · simp [interKernel, hM, Torus.matVec]

end Pointwise

section DriftPointwise

/-- The deterministic drift identity at a configuration `X` with lift `Y`. -/
theorem drift_pointwise {D : DynData d} (hN : 2 ≤ N) {t : ℝ} (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {r : ℝ} (hr : r ∈ Set.Icc 0 t) (X : Config d N) (Y : Fin N → Euc d)
    (hY : ∀ i, Torus.mk (Y i) = X i) (hcol : X ∉ collisionSet d N ∨ D.M = 0) :
    derivWithin (fun r => empiricalLift N f r Y) (Set.Icc 0 t) r
      + fderiv ℝ (empiricalLift N f r) Y (fun i => particleDrift D X i)
      + (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (empiricalLift N f r)) Y (liftedNoise D k) (liftedNoise D k)
    = pair (empirical X) (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
          - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
      + interactionPairing D (f r) (empirical X) (empirical X) := by
  have hc2 : ContDiff ℝ 2 (Torus.lift (f r)) := hf.c2 r hr
  have hN0 : 0 < N := by omega
  have hoff := offdiag_identity D (f r) hN0 X hcol
  rw [derivWithin_empiricalLift ht hf hr, empiricalLift_eq, fderiv_sumLift_lift_apply hc2,
    sum_fderiv_fderiv_sumLift_liftedNoise D hc2, pair_empirical hN0,
    interactionPairing_empirical hN0]
  simp only [sum_lap_eq, hY, particleDrift, inner_sub_right, inner_smul_right, inner_sum,
    real_inner_comm (Torus.grad D.V _)]
  have hsL : ∑ i, ((1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        inner ℝ (Torus.grad (f r) (X i)) (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
        - inner ℝ (Torus.grad D.V (X i)) (Torus.grad (f r) (X i)))
      = ∑ i, (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
          inner ℝ (Torus.grad (f r) (X i)) (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
        - ∑ i, inner ℝ (Torus.grad D.V (X i)) (Torus.grad (f r) (X i)) := by
    rw [Finset.sum_sub_distrib]
  have hsR : ∑ x, (ft r (X x) + D.invβ * Torus.laplacian (f r) (X x)
        - inner ℝ (Torus.grad D.V (X x)) (Torus.grad (f r) (X x)))
      = ∑ x, ft r (X x) + D.invβ * ∑ x, Torus.laplacian (f r) (X x)
        - ∑ x, inner ℝ (Torus.grad D.V (X x)) (Torus.grad (f r) (X x)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  linear_combination hoff + (N : ℝ)⁻¹ * hsL - (N : ℝ)⁻¹ * hsR

end DriftPointwise

/-! ### Measurability and bounds of the empirical noise integrand -/

section NoiseBounds

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ}

theorem isProgressive_comp_measurable' {β E : Type*} [MeasurableSpace β] [MeasurableSpace E]
    (X : ℝ → Ω → E) (hX : IsProgressive ℱ X) (g : ℝ → E → β)
    (hg : Measurable (Function.uncurry g)) :
    IsProgressive ℱ (fun s ω => g s (X s ω)) := by
  intro i
  have h2 : Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      (fun p : Set.Iic i × Ω => ((p.1 : ℝ), X p.1 p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (hX i)
  exact hg.comp h2

/-- The clamped time `s ↦ max 0 (min s t)`, which is the identity on `[0, t]`. -/
def clampTI (t s : ℝ) : ℝ := max 0 (min s t)

theorem clampTI_mem {t : ℝ} (ht : 0 ≤ t) (s : ℝ) : clampTI t s ∈ Set.Icc 0 t :=
  ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem clampTI_of_mem {t s : ℝ} (hs : s ∈ Set.Icc 0 t) : clampTI t s = s := by
  unfold clampTI
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clampTI (t : ℝ) : Continuous (clampTI t) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem continuousOn_gradient_time {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => gradient (Torus.lift (f p.1)) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (Torus.lift (f p.1)) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
    have h := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn
      (hf.contOn_iter (j := 1) (by norm_num))
    exact h.congr fun p _ => by simp [fderiv_eq_curry]
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous).comp_continuousOn h1

theorem continuous_gradient_clamp {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    Continuous (fun p : ℝ × Euc d => gradient (Torus.lift (f (clampTI t p.1))) p.2) := by
  have hq : Continuous fun p : ℝ × Euc d => (clampTI t p.1, p.2) :=
    ((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  have h := ContinuousOn.comp_continuous
    (g := fun p : ℝ × Euc d => gradient (Torus.lift (f p.1)) p.2)
    (f := fun p : ℝ × Euc d => (clampTI t p.1, p.2)) (continuousOn_gradient_time hf) hq
    (fun p => (⟨clampTI_mem ht p.1, Set.mem_univ _⟩ : (clampTI t p.1, p.2) ∈ Set.Icc 0 t ×ˢ Set.univ))
  exact h

theorem measurable_grad_clamp {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    Measurable (fun p : ℝ × Torus d => Torus.grad (f (clampTI t p.1)) p.2) :=
  (continuous_gradient_clamp ht hf).measurable.comp
    (measurable_fst.prodMk ((measurable_torusRep d).comp measurable_snd))

theorem rep_norm_le (x : Torus d) : ‖Torus.rep x‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(Torus.rep x).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
        have h' : (0 : ℝ) ≤ ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)) ∧
            ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)) < 1 := by
          simpa using h
        have hr : (Torus.rep x).ofLp i = ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)) := rfl
        rw [hr, Real.norm_eq_abs, abs_of_nonneg h'.1]
        have : ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)) ^ 2 ≤ 1 := by nlinarith [h'.1, h'.2]
        exact this
    _ = d := by simp

theorem grad_bound {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    ∃ C : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x : Torus d, ‖Torus.grad (f r) x‖ ≤ C := by
  have hK : IsCompact (Set.Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun p : ℝ × Euc d => ‖gradient (Torus.lift (f p.1)) p.2‖)
      (Set.Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d)) :=
    ((continuousOn_gradient_time hf).mono
      (Set.prod_mono subset_rfl (Set.subset_univ _))).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨C, fun r hr x => ?_⟩
  have hmem : (r, Torus.rep x) ∈ Set.Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d) :=
    ⟨hr, mem_closedBall_zero_iff.2 (rep_norm_le x)⟩
  have := hC _ hmem
  rwa [norm_norm] at this

/-- The torus-based integrand of the empirical martingale at time `s`, configuration `Y`. -/
def noiseG (D : DynData d) (t : ℝ) (f : ℝ → Torus d → ℝ) (s : ℝ) (Y : Config d N) :
    (Fin N × Fin d) → ℝ :=
  fun k => if s ∈ Set.Icc 0 t then
    (Real.sqrt (2 * D.invβ) / N) * (Torus.grad (f (clampTI t s)) (Y k.1)) k.2 else 0

theorem empiricalNoiseIntegrand_eq_noiseG (D : DynData d) (t : ℝ) (f : ℝ → Torus d → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (s : ℝ) (ω : Ω) :
    empiricalNoiseIntegrand D t f X s ω = noiseG D t f s (X (Real.toNNReal s) ω) := by
  funext k
  unfold empiricalNoiseIntegrand noiseG
  split_ifs with h
  · rw [clampTI_of_mem h]
  · rfl

theorem measurable_uncurry_noiseG {t : ℝ} (ht : 0 ≤ t) {D : DynData d} {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    Measurable (Function.uncurry (noiseG (N := N) D t f)) := by
  refine measurable_pi_iff.2 fun k => ?_
  have hG : Measurable fun p : ℝ × Config d N => Torus.grad (f (clampTI t p.1)) (p.2 k.1) :=
    (measurable_grad_clamp ht hf).comp (measurable_fst.prodMk ((measurable_pi_apply k.1).comp measurable_snd))
  have hc : Measurable fun p : ℝ × Config d N =>
      (Real.sqrt (2 * D.invβ) / N) * (Torus.grad (f (clampTI t p.1)) (p.2 k.1)) k.2 := by
    have hcoord : Measurable fun v : Euc d => v k.2 := by fun_prop
    exact measurable_const.mul (hcoord.comp hG)
  exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hc measurable_const

theorem abs_noiseG_le {t : ℝ} (ht : 0 ≤ t) {D : DynData d} {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {C : ℝ} (hC : ∀ r ∈ Set.Icc 0 t, ∀ x : Torus d, ‖Torus.grad (f r) x‖ ≤ C)
    (s : ℝ) (Y : Config d N) (k : Fin N × Fin d) :
    |noiseG D t f s Y k| ≤ |Real.sqrt (2 * D.invβ) / N| * |C| := by
  unfold noiseG
  split_ifs with hs
  · have h1 : |(Torus.grad (f (clampTI t s)) (Y k.1)).ofLp k.2| ≤ ‖Torus.grad (f (clampTI t s)) (Y k.1)‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ _
    have h2 := hC (clampTI t s) (clampTI_mem ht s) (Y k.1)
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact h1.trans (h2.trans (le_abs_self C))
  · rw [abs_zero]
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem isProgressiveL2_empiricalNoiseIntegrand [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Config d N}
    (hX : IsProgressive ℱ (ofNNRealTime X)) {t : ℝ} (ht : 0 ≤ t) {D : DynData d}
    {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand (N := N) D t f X) := by
  obtain ⟨C, hC⟩ := grad_bound ht hf
  have hprog : IsProgressive ℱ (fun s ω => noiseG D t f s (X (Real.toNNReal s) ω)) :=
    isProgressive_comp_measurable' (ofNNRealTime X) hX (noiseG D t f) (measurable_uncurry_noiseG ht hf)
  have hfun : empiricalNoiseIntegrand (N := N) D t f X
      = fun s ω => noiseG D t f s (X (Real.toNNReal s) ω) := by
    funext s ω
    exact empiricalNoiseIntegrand_eq_noiseG D t f X s ω
  rw [hfun]
  exact IsProgressiveL2.of_bounded P hprog _ fun s ω k => abs_noiseG_le ht hf hC s _ k

end NoiseBounds

/-! ### The covering lift with a measurable integral part, and the Itô identity -/

section Covering

theorem euc_eq_sum (v : Euc d) : v = ∑ j : Fin d, v j • EuclideanSpace.single j 1 := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  simpa using this.symm

theorem integral_euc_coord {S : Set ℝ} (ψ : ℝ → Euc d) (hψ : IntegrableOn ψ S) :
    ∫ s in S, ψ s = ∑ j : Fin d, (∫ s in S, ψ s j) • EuclideanSpace.single j 1 := by
  have hc : ∀ j : Fin d, Integrable (fun s => ψ s j) (volume.restrict S) := fun j =>
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp hψ
  calc ∫ s in S, ψ s = ∫ s in S, ∑ j : Fin d, ψ s j • EuclideanSpace.single j 1 :=
        integral_congr_ae (Filter.Eventually.of_forall fun s => euc_eq_sum (ψ s))
    _ = ∑ j : Fin d, ∫ s in S, ψ s j • EuclideanSpace.single j 1 :=
        integral_finset_sum _ fun j _ => (hc j).smul_const _
    _ = ∑ j : Fin d, (∫ s in S, ψ s j) • EuclideanSpace.single j 1 :=
        Finset.sum_congr rfl fun j _ => integral_smul_const _ _

/-- The `(i, j)` coordinate of the time integral of the drift over `(0, t]`. -/
def intCoord (D : DynData d) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (i : Fin N) (j : Fin d)
    (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc 0 t, (driftProc D X (Real.toNNReal s) ω i) j

/-- The integral part of the covering lift, assembled from its coordinates (total in `ω`). -/
def intPart (D : DynData d) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ω : Ω) : Fin N → Euc d :=
  fun i => ∑ j : Fin d, intCoord D X t i j ω • EuclideanSpace.single j 1

/-- The covering-space lift `Y_t = rep ∘ X_0 + ∫_0^t b(X_s) ds + ∑_k (W'_k(t) - W'_k(0)) σ_k`
with the integral part assembled coordinatewise, so that it is measurable for every `ω`. -/
def liftProcM (D : DynData d) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ≥0 → Ω → (Fin N → Euc d) :=
  fun t ω => (fun i => Torus.rep (X 0 ω i)) + intPart D X t ω
    + ∑ k, (W' t ω k - W' 0 ω k) • liftedNoise D k

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
  {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}

theorem measurable_intCoord (hV : Torus.IsCk 2 D.V) (hF : IsFilteredSolution P ℱ W' W X)
    (t : ℝ) (i : Fin N) (j : Fin d) :
    Measurable (fun ω => intCoord D X t i j ω) := by
  have hg : Measurable (Function.uncurry
      (fun (_ : ℝ) (v : Fin N → Euc d) (k : Fin N × Fin d) => (v k.1) k.2)) := by
    refine measurable_pi_iff.2 fun k => ?_
    have hc : Measurable fun v : Fin N → Euc d => (v k.1) k.2 := by fun_prop
    exact hc.comp measurable_snd
  have hΦ : IsProgressive ℱ (fun (r : ℝ) (ω : Ω) (k : Fin N × Fin d) =>
      (driftProc D X (Real.toNNReal r) ω k.1) k.2) :=
    isProgressive_comp_measurable' (ofNNRealTime (driftProc D X)) (isProgressive_driftProc hV hF)
      (fun (_ : ℝ) (v : Fin N → Euc d) (k : Fin N × Fin d) => (v k.1) k.2) hg
  have h := measurable_integral_of_progressive hΦ (ψ := id) measurable_id t t le_rfl (i, j)
  exact (h.mono (ℱ.le t) le_rfl)

theorem measurable_intPart (hV : Torus.IsCk 2 D.V) (hF : IsFilteredSolution P ℱ W' W X) (t : ℝ) :
    Measurable (intPart D X t) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold intPart
  exact Finset.measurable_sum _ fun j _ => (measurable_intCoord hV hF t i j).smul_const _

theorem measurable_liftProcM (hV : Torus.IsCk 2 D.V) (hF : IsFilteredSolution P ℱ W' W X)
    (t : ℝ≥0) : Measurable (liftProcM D W' X t) := by
  have hX0 : Measurable (X 0) := (hF.adapted 0).mono (ℱ.le 0) le_rfl
  have hrep : Measurable fun ω => fun i => Torus.rep (X 0 ω i) :=
    measurable_pi_iff.2 fun i => (measurable_torusRep d).comp ((measurable_pi_apply i).comp hX0)
  have hWm : ∀ (s : ℝ≥0) (k : Fin N × Fin d), Measurable fun ω => W' s ω k := fun s k =>
    (measurable_pi_apply k).comp ((hF.brownian.adapted s).mono (ℱ.le s) le_rfl)
  have hnoise : Measurable fun ω => ∑ k, (W' t ω k - W' 0 ω k) • liftedNoise D k :=
    Finset.measurable_sum _ fun k _ => ((hWm t k).sub (hWm 0 k)).smul_const _
  exact (hrep.add (measurable_intPart hV hF t)).add hnoise

theorem liftProcM_zero (ω : Ω) : liftProcM D W' X 0 ω = fun i => Torus.rep (X 0 ω i) := by
  have h0 : ∀ i j, intCoord D X 0 i j ω = 0 := fun i j => by simp [intCoord]
  have hp0 : intPart D X 0 ω = 0 := by
    funext i
    simp [intPart, h0]
  simp [liftProcM, hp0]

theorem liftedNoise_apply (k : Fin N × Fin d) (i : Fin N) :
    liftedNoise D k i = if i = k.1 then Real.sqrt (2 * D.invβ) • EuclideanSpace.single k.2 1 else 0 := by
  simp [liftedNoise, Pi.single_apply]

theorem sum_inner_liftedNoise (g : Fin N → Euc d) (k : Fin N × Fin d) :
    ∑ i, inner ℝ (g i) (liftedNoise D k i) = Real.sqrt (2 * D.invβ) * (g k.1) k.2 := by
  have hx : ∀ x, inner ℝ (g x) (liftedNoise D k x)
      = if x = k.1 then Real.sqrt (2 * D.invβ) * (g x) k.2 else 0 := by
    intro x
    rw [liftedNoise_apply]
    split_ifs with h
    · simp [inner_smul_right, EuclideanSpace.inner_single_right]
    · simp
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The covering integrand of Itô's formula is the torus-based empirical noise integrand. -/
theorem itoIntegrand_eq_noiseG {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft)
    (Z : ℝ≥0 → Ω → (Fin N → Euc d)) (s : ℝ) (ω : Ω)
    (hY : ∀ i, Torus.mk (Z (Real.toNNReal s) ω i) = X (Real.toNNReal s) ω i) :
    itoIntegrand t Set.univ (empiricalLift N f) (ofNNRealTime Z) (fun _ _ => liftedNoise D) s ω
      = noiseG D t f s (X (Real.toNNReal s) ω) := by
  funext k
  unfold itoIntegrand
  by_cases hs : s ∈ Set.Icc 0 t
  · rw [Set.indicator_of_mem hs]
    simp only [Set.mem_univ, Set.setOf_true, Set.indicator_univ, ofNNRealTime_apply]
    rw [empiricalLift_eq, fderiv_sumLift_lift_apply (hf.c2 s hs)]
    simp only [hY]
    have h : ∑ x, inner ℝ (Torus.grad (f s) (X (Real.toNNReal s) ω x)) (liftedNoise D k x)
        = Real.sqrt (2 * D.invβ) * (Torus.grad (f s) (X (Real.toNNReal s) ω k.1)) k.2 :=
      sum_inner_liftedNoise (D := D) (fun i => Torus.grad (f s) (X (Real.toNNReal s) ω i)) k
    unfold noiseG
    rw [if_pos hs, clampTI_of_mem hs, h]
    ring
  · rw [Set.indicator_of_notMem hs]
    simp [noiseG, hs]

/-- The deterministic drift identity in the form of Itô's formula. -/
theorem itoDrift_eq_rhs {t : ℝ} (hN : 2 ≤ N) (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (Z : ℝ≥0 → Ω → (Fin N → Euc d)) (ω : Ω) {s : ℝ}
    (hs : s ∈ Set.Icc 0 t)
    (hY : ∀ i, Torus.mk (Z (Real.toNNReal s) ω i) = X (Real.toNNReal s) ω i)
    (hcol : X (Real.toNNReal s) ω ∉ collisionSet d N ∨ D.M = 0) :
    itoDrift t (empiricalLift N f) (ofNNRealTime Z) (ofNNRealTime (driftProc D X))
        (fun _ _ => liftedNoise D) s ω
      = pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
        + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
            (empirical (X (Real.toNNReal s) ω)) := by
  unfold itoDrift
  exact drift_pointwise hN ht hf hs (X (Real.toNNReal s) ω) (Z (Real.toNNReal s) ω) hY hcol

end Covering

/-! ### Main assembly -/

section Assembly

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
  {X : ℝ≥0 → Ω → Config d N} {D : DynData d}

theorem exists_null_of_ae {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ N0 : Set Ω, MeasurableSet N0 ∧ P N0 = 0 ∧ ∀ ω ∉ N0, p ω :=
  ⟨toMeasurable P {ω | ¬ p ω}, measurableSet_toMeasurable _ _,
    by rw [measure_toMeasurable]; exact ae_iff.1 h,
    fun ω hω => by_contra fun hc => hω (subset_toMeasurable _ _ hc)⟩

theorem intPart_eq_integral (ω : Ω) (τ : ℝ)
    (hint : IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 τ)) :
    intPart D X τ ω = ∫ s in Set.Icc 0 τ, driftProc D X (Real.toNNReal s) ω := by
  rw [integral_Icc_eq_integral_Ioc]
  have hI : IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Ioc 0 τ) :=
    hint.mono_set Set.Ioc_subset_Icc_self
  funext i
  have hpi : (∫ s in Set.Ioc 0 τ, driftProc D X (Real.toNNReal s) ω) i
      = ∫ s in Set.Ioc 0 τ, driftProc D X (Real.toNNReal s) ω i :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integral_comp_comm hI).symm
  have hIi : IntegrableOn (fun s => driftProc D X (Real.toNNReal s) ω i) (Set.Ioc 0 τ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integrable_comp hI
  rw [hpi, integral_euc_coord _ hIi]
  rfl

theorem empiricalLift_eq_pair {N : ℕ} (hN : 0 < N) (f : ℝ → Torus d → ℝ) (r : ℝ)
    (Y : Fin N → Euc d) (x : Config d N) (hY : ∀ i, Torus.mk (Y i) = x i) :
    empiricalLift N f r Y = pair (empirical x) (f r) := by
  rw [pair_empirical hN]
  unfold empiricalLift
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hY i]

theorem itoIntegrand_of_not_mem {t : ℝ} {s : ℝ} (f : ℝ → Torus d → ℝ) (hs : s ∉ Set.Icc 0 t) (Z : ℝ≥0 → Ω → (Fin N → Euc d))
    (ω : Ω) (k : Fin N × Fin d) :
    itoIntegrand t Set.univ (empiricalLift N f) (ofNNRealTime Z) (fun _ _ => liftedNoise D) s ω k
      = 0 := by
  unfold itoIntegrand
  simp [hs]

/-- The empirical Itô identity for `0 < t` (Lemma 3.6, general contact-allowing form). -/
theorem empirical_ito_pos {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V)
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (ht0 : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) (f τ)
        = pair (empirical (X 0 ω)) (f 0)
          + (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
              (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
                - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
              + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
                  (empirical (X (Real.toNNReal r) ω))))
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω := by
  obtain ⟨htL, htT⟩ := ht
  have hpos : 0 < N := by omega
  have hTnn : 0 ≤ T := htL.trans htT
  have hI : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 T) :=
    hX.ae_integrableOn_drift hTnn le_rfl
  have hlift := hX.ae_lift_eq hF
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      intPart D X τ ω = ∫ s in Set.Icc 0 (τ : ℝ), driftProc D X (Real.toNNReal s) ω := by
    filter_upwards [hI] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ hτ]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  obtain ⟨N0, hN0m, hN0P, hN0⟩ := exists_null_of_ae (P := P) (p := fun ω => ∀ τ : ℝ≥0,
    (τ : ℝ) ≤ T → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i)) hlift'
  have hZint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t → liftProcM D W' X τ ω
      = liftProcM D W' X 0 ω + (∫ s in Set.Icc (0 : ℝ) τ, driftProc D X (Real.toNNReal s) ω)
        + ∑ k, (W' τ ω k - W' 0 ω k) • liftedNoise D k := by
    filter_upwards [hint] with ω hω τ hτ
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hω τ (hτ.trans htT)]
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (liftProcM D W' X 0) := by
    intro s
    have e : liftProcM D W' X 0 = fun ω => fun i => Torus.rep (X 0 ω i) :=
      funext fun ω => liftProcM_zero ω
    rw [e]
    have hg : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
      measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
    exact hg.comp (hF.measurable_init s)
  have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω)
      (Set.Icc 0 t) :=
    hI.mono fun ω hω => hω.mono_set (Set.Icc_subset_Icc le_rfl htT)
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := t) htL
    (empiricalLift N f) (isC12On_empiricalLift ht0 hf) (liftedNoise D) (liftProcM D W' X)
    (measurable_liftProcM hV hF) hX₀ (driftProc D X) (isProgressive_driftProc hV hF) hbint hZint
  have hΦ : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) :=
    isProgressiveL2_empiricalNoiseIntegrand (D := D) hF.progressive htL hf
  have hΨloc : IsProgressiveLocL2 P ℱ (empiricalNoiseIntegrand D t f X) := hΦ.locL2
  have hpt : ∀ s : ℝ, ∀ ω ∉ N0, itoIntegrand t Set.univ (empiricalLift N f)
      (ofNNRealTime (liftProcM D W' X)) (fun _ _ => liftedNoise D) s ω
        = empiricalNoiseIntegrand D t f X s ω := by
    intro s ω hω
    rw [empiricalNoiseIntegrand_eq_noiseG]
    by_cases hs : s ∈ Set.Icc 0 t
    · refine itoIntegrand_eq_noiseG hf (liftProcM D W' X) s ω ?_
      have hle : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
        rw [Real.coe_toNNReal _ hs.1]
        exact hs.2.trans htT
      intro i
      exact (congrFun (hN0 ω hω _ hle) i).symm
    · funext k
      rw [itoIntegrand_of_not_mem f hs]
      simp [noiseG, hs]
  have hcongr := localItoIntegral_congr_null hF.brownian hΨloc hN0m hN0P hpt
    (fun s hs ω => by
      funext k
      rw [itoIntegrand_of_not_mem f (fun h => absurd h.1 (not_le.2 hs))]
      rfl)
    (fun s hs ω => by
      funext k
      simp [empiricalNoiseIntegrand, not_le.2 hs])
  have hloc := localItoIntegral_eq_itoIntegral hF.brownian hΦ
  have hcol_ae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc 0 t →
      (X (Real.toNNReal s) ω ∉ collisionSet d N ∨ D.M = 0) := by
    rcases hocc with hM | hNull
    · exact Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun s _ => Or.inr hM
    · unfold NullContactOccupation at hNull
      filter_upwards [hNull] with ω hω
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hω] with s hs hsI
      exact Or.inl fun hc => hs ⟨⟨hsI.1, hsI.2.trans htT⟩, hc⟩
  filter_upwards [hito, hloc, hcongr, hcol_ae, measure_eq_zero_iff_ae_notMem.1 hN0P]
    with ω hitoω hlocω hcongrω hcolω hωN0
  intro τ hτ
  obtain ⟨hτ0, hτt⟩ := hτ
  have hτc : ((Real.toNNReal τ : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal τ hτ0
  have hYs : ∀ s ∈ Set.Icc 0 t, ∀ i, Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i)
      = X (Real.toNNReal s) ω i := by
    intro s hs i
    have hle : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hs.1]
      exact hs.2.trans htT
    exact (congrFun (hN0 ω hωN0 _ hle) i).symm
  have hpt_ω : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc 0 t →
      itoDrift t (empiricalLift N f) (ofNNRealTime (liftProcM D W' X))
        (ofNNRealTime (driftProc D X)) (fun _ _ => liftedNoise D) s ω
      = pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
        + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
            (empirical (X (Real.toNNReal s) ω)) := by
    filter_upwards [hcolω] with s hs hsI
    exact itoDrift_eq_rhs hN ht0 hf (liftProcM D W' X) ω hsI (hYs s hsI) (hs hsI)
  have hτle : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ T := by
    rw [hτc]
    exact hτt.trans htT
  have hIntRHS : IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
      (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
        - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
      + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) := by
    have h1 := hitoω.1.mono_set (Set.Icc_subset_Icc le_rfl hτt)
    refine h1.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hpt_ω, ae_restrict_mem measurableSet_Icc] with s h1s hs
    exact h1s (Set.Icc_subset_Icc le_rfl hτt hs)
  have hτlet : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ t := by
    rw [hτc]
    exact hτt
  have hidω := hitoω.2 (Real.toNNReal τ) hτlet
  rw [hτc] at hidω
  have hL : empiricalLift N f τ (liftProcM D W' X (Real.toNNReal τ) ω)
      = pair (empirical (X (Real.toNNReal τ) ω)) (f τ) :=
    empiricalLift_eq_pair hpos f τ _ _ (fun i => (congrFun (hN0 ω hωN0 _ hτle) i).symm)
  have hF0 : empiricalLift N f 0 (liftProcM D W' X 0 ω)
      = pair (empirical (X 0 ω)) (f 0) :=
    empiricalLift_eq_pair hpos f 0 _ _
      (fun i => (congrFun (hN0 ω hωN0 0 (by simpa using hTnn)) i).symm)
  have hIntEq : ∫ s in Set.Icc 0 (τ : ℝ), itoDrift t (empiricalLift N f)
      (ofNNRealTime (liftProcM D W' X)) (ofNNRealTime (driftProc D X))
      (fun _ _ => liftedNoise D) s ω
      = ∫ s in Set.Icc 0 τ, (pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
          + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
              (empirical (X (Real.toNNReal s) ω))) :=
    setIntegral_congr_ae measurableSet_Icc
      (hpt_ω.mono fun s h hs => h (Set.Icc_subset_Icc le_rfl hτt hs))
  have hInt2 : ∫ s in Set.Icc 0 τ, (pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
          + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
              (empirical (X (Real.toNNReal s) ω)))
      = ∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) := by
    rw [intervalIntegral.integral_of_le hτ0, integral_Icc_eq_integral_Ioc]
  rw [hL, hF0, hIntEq, hInt2, hcongrω τ, hlocω τ] at hidω
  refine ⟨hIntRHS, ?_⟩
  unfold empiricalMartingale
  rw [hτc]
  exact hidω

end Assembly

/-- Lemma 3.6 for a contact-allowing flow (general form, with the integral parenthesised). -/
theorem empirical_ito_of_contact {P : Measure Ω} {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V) (hX : IsContactStrongSolution P D T X₀ W X)
    (hF : IsFilteredSolution P ℱ W' W X) (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) (f τ)
        = pair (empirical (X 0 ω)) (f 0)
          + (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
              (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
                - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
              + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
                  (empirical (X (Real.toNNReal r) ω))))
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω := by
  refine ⟨isProgressiveL2_empiricalNoiseIntegrand (D := D) hF.progressive ht.1 hf, ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    filter_upwards with ω
    intro τ hτ
    have hτ0 : τ = 0 := le_antisymm hτ.2 hτ.1
    subst hτ0
    have hle : ((Real.toNNReal 0 : ℝ≥0) : ℝ) ≤ 0 := by simp
    have hM : empiricalMartingale P ℱ W' D 0 f X (Real.toNNReal 0) ω = 0 := by
      unfold empiricalMartingale
      exact itoIntegral_of_nonpos P ℱ W' _ hle ω
    refine ⟨?_, ?_⟩
    · rw [Set.Icc_self]
      exact (integrableOn_singleton_iff enorm_ne_top).2 (Or.inr (by simp))
    · rw [intervalIntegral.integral_same, hM]
      simp
  · exact empirical_ito_pos hN hV hX hF hocc ht hpos hf

/-- Lemma 3.6 (row 1, `M:B:lem:cepa-empirical-ito`): the Cépa–Lépingle log flow, `d = 1`,
`s = 0`, `M = -a·Id`, `β < ∞`. -/
theorem cepa_empirical_ito
    {N : ℕ} (hN : 2 ≤ N) [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {D : DynData 1}
    (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} {X₀ : Ω → Config 1 N} {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {f ft : ℝ → Torus 1 → ℝ} (hf : IsC12Test t f ft) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) (f τ)
        = pair (empirical (X 0 ω)) (f 0)
          + (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
              (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
                - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
              + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
                  (empirical (X (Real.toNNReal r) ω))))
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω :=
  empirical_ito_of_contact hN hV hX.toContact hF (Or.inr hX.occupation) ht hf

end HRS
