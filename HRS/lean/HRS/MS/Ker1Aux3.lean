import HRS.MS.Ker1Aux2

/-!
# MS-KER1, helper file 3: uniqueness of the periodic Riesz kernel

Two functions satisfying `IsPeriodicRieszKernel d s L` agree off the lattice `Lℤ^d`: the difference `h`
is periodic, locally integrable and has all Fourier coefficients zero; the torus descent
`G` of `h(L ·)` vanishes a.e. (`text_ae_eq_zero_of_fcoef`), hence `h = 0` a.e. and, by continuity, on the
open set off the lattice.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise ContDiff

namespace HRS.MS.Ker1

open HRS HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem ker1_compact_Icc (L : ℝ) : IsCompact {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L} := by
  have h : IsCompact ((fun f : Fin d → ℝ => (WithLp.toLp 2 f : Euc d)) ''
      (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) L)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro hx; exact ⟨x.ofLp, fun i _ => hx i, rfl⟩
  · rintro ⟨f, hf, rfl⟩ i; exact hf i (mem_univ i)

theorem ker1_box_subset_compact (L : ℝ) :
    ker1_box d L ⊆ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L} :=
  fun x hx i => ⟨(hx i).1, (hx i).2.le⟩

theorem ker1_cell_subset_compact : ker1_cell d ⊆ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) 1} :=
  fun x hx i => ⟨(hx i).1.le, (hx i).2⟩

/-- a periodic function that vanishes a.e. on the cell vanishes a.e. -/
theorem ker1_ae_of_cell {φ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (n : Lattice d), φ (x + Lattice.toEuc n) = φ x)
    (h : φ =ᵐ[volume.restrict (ker1_cell d)] 0) : φ =ᵐ[volume] 0 := by
  let S : Lattice d → Set (Euc d) := fun n => {x | ∀ i, x i ∈ Ioc ((n i : ℝ)) ((n i : ℝ) + 1)}
  have hS : ⋃ n, S n = univ := by
    refine eq_univ_of_forall fun x => ?_
    simp only [mem_iUnion]
    refine ⟨fun i => ⌈x i⌉ - 1, fun i => ?_⟩
    simp only [Int.cast_sub, Int.cast_one, mem_Ioc]
    constructor
    · linarith [Int.ceil_lt_add_one (x i), Int.lt_ceil.mpr (show ((⌈x i⌉ - 1 : ℤ) : ℝ) < x i by
        have := Int.ceil_lt_add_one (x i); push_cast; linarith)]
    · linarith [Int.le_ceil (x i)]
  have hms : ∀ n, MeasurableSet (S n) := fun n => by
    have : S n = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun i : Fin d => Ioc ((n i : ℝ)) ((n i : ℝ) + 1)) := by
      ext w; simp [S]
    rw [this]
    exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).preimage
      (PiLp.volume_preserving_ofLp (Fin d)).measurable
  have hall : ∀ n, ∀ᵐ x ∂(volume.restrict (S n)), φ x = 0 := by
    intro n
    have hmp := (measurePreserving_add_right (volume : Measure (Euc d)) (-(Lattice.toEuc n))).restrict_preimage
      (ker1_measurableSet_cell (d := d))
    have hpre : (fun x : Euc d => x + -(Lattice.toEuc n)) ⁻¹' ker1_cell d = S n := by
      ext x
      simp only [ker1_cell, S, mem_preimage, mem_setOf_eq, PiLp.add_apply, PiLp.neg_apply, mem_Ioc,
        Lattice.toEuc]
      constructor <;> intro h i <;> have := h i <;> constructor <;> linarith [this.1, this.2]
    rw [hpre] at hmp
    have := hmp.quasiMeasurePreserving.ae_eq_comp h
    filter_upwards [this] with x hx
    have h2 : φ (x + -(Lattice.toEuc n)) = φ x := by
      have := hper (x + -(Lattice.toEuc n)) n
      rw [neg_add_cancel_right] at this
      exact this.symm
    simpa [h2] using hx
  have : ∀ᵐ x ∂(volume.restrict (⋃ n, S n)), φ x = 0 :=
    (ae_restrict_iUnion_iff _ _).2 hall
  rw [hS, Measure.restrict_univ] at this
  exact this


theorem ker1_measurableSet_box (L : ℝ) : MeasurableSet (ker1_box d L) := by
  have : ker1_box d L = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (0 : ℝ) L) := by
    ext w; simp [ker1_box]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

/-- the character `e^{-2πi (k/L)·x}` -/
def ker1_E (L : ℝ) (k : Lattice d) (x : Euc d) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * x i : ℝ) : ℂ)))

theorem ker1_continuous_E (L : ℝ) (k : Lattice d) : Continuous (ker1_E L k) := by
  unfold ker1_E
  fun_prop

theorem ker1_integrableOn_box_mul {f : Euc d → ℝ} (hf : LocallyIntegrable f volume) (L : ℝ) (k : Lattice d) :
    IntegrableOn (fun x => (f x : ℂ) * ker1_E L k x) (ker1_box d L) := by
  have hK := ker1_compact_Icc (d := d) L
  have h1 : IntegrableOn (fun x => (f x : ℂ)) {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L} :=
    (hf.integrableOn_isCompact hK).ofReal
  exact (h1.mono_set (ker1_box_subset_compact L)).mul_continuousOn_of_subset (ker1_continuous_E L k).continuousOn
    (ker1_measurableSet_box L) hK (ker1_box_subset_compact L)

theorem ker1_kernel_coeff_zero {s L : ℝ} {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) :
    ∫ x in ker1_box d L, (γ x : ℂ) * ker1_E L (0 : Lattice d) x = 0 := by
  have h1 : ∀ x : Euc d, (γ x : ℂ) * ker1_E L (0 : Lattice d) x = (γ x : ℂ) := by
    intro x
    simp [ker1_E]
  simp_rw [h1]
  have h3 := integral_complex_ofReal (μ := volume.restrict (ker1_box d L)) (f := γ)
  have h4 : ∫ x in ker1_box d L, γ x = 0 := hγ.meanZero
  rw [h3, h4]; simp

theorem ker1_kernel_coeff_ne {s L : ℝ} {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ)
    {k : Lattice d} (hk : k ≠ 0) :
    ∫ x in ker1_box d L, (γ x : ℂ) * ker1_E L k x =
      ((rieszConst d s * (2 * Real.pi * (‖(WithLp.toLp 2 fun i => (k i : ℝ) : Euc d)‖ / L)) ^
        (s - d) : ℝ) : ℂ) := hγ.coeff k hk

/-- the Fourier coefficients of the difference of two kernels vanish -/
theorem ker1_coeff_diff_zero {s L : ℝ} {γ γ' : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ)
    (hγ' : IsPeriodicRieszKernel d s L γ') (k : Lattice d) :
    ∫ x in ker1_box d L, ((γ x - γ' x : ℝ) : ℂ) * ker1_E L k x = 0 := by
  have e : ∀ x : Euc d, ((γ x - γ' x : ℝ) : ℂ) * ker1_E L k x =
      (γ x : ℂ) * ker1_E L k x - (γ' x : ℂ) * ker1_E L k x := fun x => by push_cast; ring
  simp_rw [e]
  rw [integral_sub (ker1_integrableOn_box_mul hγ.locInt L k) (ker1_integrableOn_box_mul hγ'.locInt L k)]
  by_cases hk : k = 0
  · subst hk
    rw [ker1_kernel_coeff_zero hγ, ker1_kernel_coeff_zero hγ', sub_self]
  · rw [ker1_kernel_coeff_ne hγ hk, ker1_kernel_coeff_ne hγ' hk, sub_self]


theorem ker1_zero_of_coeff {L : ℝ} (hL : 0 < L) {h : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (z : Fin d → ℤ), h (x + L • latticePt z) = h x)
    (hloc : LocallyIntegrable h volume)
    (hcont : ContinuousOn h {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z})
    (hcoef : ∀ k : Lattice d, ∫ x in ker1_box d L, (h x : ℂ) * ker1_E L k x = 0) :
    ∀ x : Euc d, (∀ z : Fin d → ℤ, x ≠ L • latticePt z) → h x = 0 := by
  set h' : Euc d → ℝ := fun y => h (L • y) with hh'
  have hper' : ∀ (x : Euc d) (n : Lattice d), h' (x + Lattice.toEuc n) = h' x := by
    intro x n
    simp only [hh', smul_add]
    exact hper (L • x) n
  have hloc' : LocallyIntegrable h' volume := ker1_locInt_smul hloc hL.ne'
  have hint' : IntegrableOn h' (ker1_cell d) :=
    (hloc'.integrableOn_isCompact (ker1_compact_Icc 1)).mono_set ker1_cell_subset_compact
  obtain ⟨G, hGi, hG⟩ := ker1_descent h' hper' hint'
  have hfc : ∀ k : Lattice d, Torus.fcoef G k = 0 := by
    intro k
    have h1 := ker1_box_coeff hL G hGi k
    have h2 : ∫ x in ker1_box d L, (G (Torus.mk (L⁻¹ • x)) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * x i : ℝ) : ℂ))) = 0 := by
      rw [← hcoef k]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ker1_E, hG, hh', smul_inv_smul₀ hL.ne']
    rw [h2] at h1
    have hLd : (L : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 hL.ne')
    exact ((mul_eq_zero.1 h1.symm).resolve_left hLd)
  have hGae := HRS.Commutator.TorusNote.text_ae_eq_zero_of_fcoef hGi hfc
  have hcell : h' =ᵐ[volume.restrict (ker1_cell d)] 0 := by
    have := ker1_mk_mp.quasiMeasurePreserving.ae_eq_comp hGae
    have e : h' = G ∘ Torus.mk := funext fun y => (hG y).symm
    rw [e]
    exact this
  have hall := ker1_ae_of_cell hper' hcell
  have hU : IsOpen {y : Euc d | Torus.mk y ≠ 0} := HRS.KernelGrad.isOpen_mk_ne_zero
  have hmk : ∀ y : Euc d, Torus.mk y ≠ 0 → ∀ z : Fin d → ℤ, L • y ≠ L • latticePt z := by
    intro y hy z hz
    apply hy
    have : y = Lattice.toEuc z := smul_right_injective _ hL.ne' hz
    rw [this]; exact ker1_mk_toEuc z
  have hc' : ContinuousOn h' {y : Euc d | Torus.mk y ≠ 0} :=
    hcont.comp (continuous_const_smul L).continuousOn fun y hy => hmk y hy
  have heq := Measure.eqOn_of_ae_eq (μ := volume) (s := {y : Euc d | Torus.mk y ≠ 0})
    (f := h') (g := 0) (ae_restrict_of_ae hall) hc' continuousOn_const
    (by rw [hU.interior_eq]; exact subset_closure)
  intro x hx
  have hy : Torus.mk (L⁻¹ • x) ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := ker1_mk_eq_zero h0
    apply hx n
    have : x = L • (L⁻¹ • x) := (smul_inv_smul₀ hL.ne' x).symm
    rw [this, hn]; rfl
  have := heq hy
  simpa [hh', smul_inv_smul₀ hL.ne'] using this


/-- Uniqueness: every `γ` with `IsPeriodicRieszKernel d s L γ` equals `γ_L` off the lattice `Lℤ^d`. -/
theorem ker1_eq_gam (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) :
    ∀ x : Euc d, (∀ z : Fin d → ℤ, x ≠ L • latticePt z) → γ x = ker1_gam d s L x := by
  have hγ' := ker1_gam_isKernel hd hs0 hsd hL
  have := ker1_zero_of_coeff hL (h := fun x => γ x - ker1_gam d s L x)
    (fun x z => by simp only [hγ.periodic x z, hγ'.periodic x z])
    (hγ.locInt.sub hγ'.locInt)
    ((hγ.smooth.continuousOn).sub (hγ'.smooth.continuousOn))
    (fun k => ker1_coeff_diff_zero hγ hγ' k)
  intro x hx
  have := this x hx
  linarith

end HRS.MS.Ker1
