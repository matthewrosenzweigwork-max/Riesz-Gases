import HRS.PDE.Energy
import HRS.PDE.LinearODE

/-!
# Helpers for the Galerkin approximation (finite boxes, linearity of the generator on
trigonometric polynomials, continuity of the entries, conjugation symmetry)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- The finite box `{k : |k|_∞ ≤ n}` as a `Finset`. -/
def boxFinset (d n : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

theorem mem_boxFinset {n : ℕ} {k : Lattice d} : k ∈ boxFinset d n ↔ InBox n k := by
  simp [boxFinset, InBox, abs_le]

theorem IsTrigPoly.eq_zero {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) {k : Lattice d}
    (hk : ¬ InBox n k) : c k = 0 := by
  by_contra h'
  exact hk (h k h')

theorem InBox.neg {n : ℕ} {k : Lattice d} (h : InBox n k) : InBox n (-k) := by
  intro i
  simpa using h i

theorem inBox_neg_iff {n : ℕ} {k : Lattice d} : InBox n (-k) ↔ InBox n k :=
  ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

theorem isTrigPoly_zero (n : ℕ) : IsTrigPoly n (0 : Coeff d) := fun _ hk => absurd rfl hk

theorem IsTrigPoly.add {n : ℕ} {c₁ c₂ : Coeff d} (h₁ : IsTrigPoly n c₁) (h₂ : IsTrigPoly n c₂) :
    IsTrigPoly n (c₁ + c₂) := by
  intro k hk
  by_contra hb
  apply hk
  simp [h₁.eq_zero hb, h₂.eq_zero hb]

theorem IsTrigPoly.smul {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) (z : ℂ) :
    IsTrigPoly n (z • c) := by
  intro k hk
  by_contra hb
  apply hk
  simp [h.eq_zero hb]

theorem IsTrigPoly.derivCoeff {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) (j : Fin d) :
    IsTrigPoly n (derivCoeff j c) := by
  intro k hk
  by_contra hb
  apply hk
  simp [PDE.derivCoeff, h.eq_zero hb]

theorem isTrigPoly_truncCoeff (n : ℕ) (c : Coeff d) : IsTrigPoly n (truncCoeff n c) := by
  intro k hk
  by_contra hb
  apply hk
  simp [truncCoeff, hb]

theorem IsTrigPoly.truncCoeff_eq {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) :
    truncCoeff n c = c := by
  funext k
  by_cases hb : InBox n k
  · simp [PDE.truncCoeff, hb]
  · simp [PDE.truncCoeff, hb, h.eq_zero hb]

theorem mulCoeff_eq_sum {n : ℕ} (a c : Coeff d) (h : IsTrigPoly n c) (k : Lattice d) :
    mulCoeff a c k = ∑ j ∈ boxFinset d n, a (k - j) * c j := by
  unfold mulCoeff
  apply tsum_eq_sum
  intro j hj
  rw [mem_boxFinset] at hj
  simp [h.eq_zero hj]

theorem mulCoeff_add {n : ℕ} (a c₁ c₂ : Coeff d) (h₁ : IsTrigPoly n c₁) (h₂ : IsTrigPoly n c₂) :
    mulCoeff a (c₁ + c₂) = mulCoeff a c₁ + mulCoeff a c₂ := by
  funext k
  rw [mulCoeff_eq_sum a _ (h₁.add h₂), Pi.add_apply, mulCoeff_eq_sum a _ h₁,
    mulCoeff_eq_sum a _ h₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_add]

theorem mulCoeff_smul (a c : Coeff d) (z : ℂ) : mulCoeff a (z • c) = z • mulCoeff a c := by
  funext k
  unfold mulCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

theorem forwardGen_add {n : ℕ} (D : DynData d) (ρ : Torus d → ℝ) (c₁ c₂ : Coeff d)
    (h₁ : IsTrigPoly n c₁) (h₂ : IsTrigPoly n c₂) :
    forwardGen D ρ (c₁ + c₂) = forwardGen D ρ c₁ + forwardGen D ρ c₂ := by
  funext k
  have e : ∀ j, derivCoeff j (c₁ + c₂) = derivCoeff j c₁ + derivCoeff j c₂ := by
    intro j; funext k; simp [PDE.derivCoeff, mul_add]
  simp only [forwardGen, transportCoeff, nonlocalCoeff, e, Pi.add_apply]
  simp only [mulCoeff_add _ _ _ (h₁.derivCoeff _) (h₂.derivCoeff _), Pi.add_apply]
  simp only [laplaceCoeff, gradRieszCoeff, rieszMult, PDE.derivCoeff, Pi.add_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem forwardGen_smul (D : DynData d) (ρ : Torus d → ℝ) (c : Coeff d) (z : ℂ) :
    forwardGen D ρ (z • c) = z • forwardGen D ρ c := by
  funext k
  have e : ∀ j, derivCoeff j (z • c) = z • derivCoeff j c := by
    intro j; funext k; simp [PDE.derivCoeff]; ring
  simp only [forwardGen, transportCoeff, nonlocalCoeff, e, mulCoeff_smul, Pi.smul_apply,
    smul_eq_mul]
  simp only [laplaceCoeff, gradRieszCoeff, rieszMult, PDE.derivCoeff, Pi.smul_apply,
    smul_eq_mul]
  simp only [mul_sub, mul_add, Finset.mul_sum]
  congr 1
  · congr 1; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-! ### Continuity of the entries in the density -/

theorem driftCoeff_continuousOn (D : DynData d) (ρ : ℝ → Torus d → ℝ) (S : Set ℝ)
    (hρ : ∀ k, ContinuousOn (fun σ => coeffOf (ρ σ) k) S) (j : Fin d) (k : Lattice d) :
    ContinuousOn (fun σ => driftCoeff D (ρ σ) j k) S := by
  unfold driftCoeff gradRieszCoeff rieszMult
  simp only [PDE.derivCoeff]
  refine ContinuousOn.sub ?_ continuousOn_const
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
  exact continuousOn_const.mul (continuousOn_const.mul (hρ k))

theorem forwardGen_continuousOn {n : ℕ} (D : DynData d) (ρ : ℝ → Torus d → ℝ) (S : Set ℝ)
    (hρ : ∀ k, ContinuousOn (fun σ => coeffOf (ρ σ) k) S) (F : Coeff d) (hF : IsTrigPoly n F)
    (k : Lattice d) : ContinuousOn (fun σ => forwardGen D (ρ σ) F k) S := by
  have key : ∀ (a : Coeff d) (j : Fin d) (k : Lattice d),
      mulCoeff a (derivCoeff j F) k = ∑ l ∈ boxFinset d n, a (k - l) * derivCoeff j F l :=
    fun a j k => mulCoeff_eq_sum a _ (hF.derivCoeff j) k
  simp only [forwardGen, transportCoeff, nonlocalCoeff, key]
  simp only [laplaceCoeff, gradRieszCoeff, rieszMult, PDE.derivCoeff]
  refine ContinuousOn.sub (ContinuousOn.add continuousOn_const ?_) ?_
  · refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun l _ => ?_
    exact (driftCoeff_continuousOn D ρ S hρ j _).mul continuousOn_const
  · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have hs : ContinuousOn (fun σ => mulCoeff (coeffOf (ρ σ)) (derivCoeff j F) k) S := by
      simp only [key]
      refine continuousOn_finsetSum _ fun l _ => ?_
      exact (hρ _).mul continuousOn_const
    exact continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul hs))

theorem coeffOf_eq_integral (φ : Torus d → ℝ) (k : Lattice d) :
    coeffOf φ k = ∫ x, Torus.mode (-k) x * (φ x : ℂ) := by
  unfold coeffOf Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  have hm : (@volume (UnitAddTorus (Fin d))
      (@MeasureSpace.pi (Fin d) _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) =
      (volume : Measure (Torus d)) := by
    show Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hm]
  simp [smul_eq_mul, Torus.mode]

theorem coeffOf_continuousOn {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ} (h : CoeffHyp m Λ T μ)
    (k : Lattice d) : ContinuousOn (fun r => coeffOf (μ r) k) (Set.Icc 0 T) := by
  have hint : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (μ r) := by
    intro r hr
    by_contra hn
    have := (h.prob r hr).integral_one
    rw [integral_undef hn] at this
    exact zero_ne_one this
  have e : ∀ r ∈ Set.Icc (0 : ℝ) T, coeffOf (μ r) k =
      ((Torus.cosCoeff (μ r) k : ℝ) : ℂ) + ((-Torus.sinCoeff (μ r) k : ℝ) : ℂ) * Complex.I := by
    intro r hr
    rw [coeffOf_eq_integral]
    exact Torus.integral_mode_mul_real (hint r hr) k
  refine ContinuousOn.congr ?_ e
  have h1 : ContinuousOn (fun r => Torus.cosCoeff (μ r) k) (Set.Icc 0 T) := by
    unfold Torus.cosCoeff
    have := h.cont (Torus.cosMode k) (Torus.continuous_cosMode k)
    simpa using this
  have h2 : ContinuousOn (fun r => Torus.sinCoeff (μ r) k) (Set.Icc 0 T) := by
    unfold Torus.sinCoeff
    have := h.cont (Torus.sinMode k) (Torus.continuous_sinMode k)
    simpa using this
  exact (Complex.continuous_ofReal.comp_continuousOn h1).add
    ((Complex.continuous_ofReal.comp_continuousOn h2.neg).mul continuousOn_const)

/-! ### The finite-dimensional system on the box -/

/-- Coefficients on the box, a finite-dimensional space. -/
abbrev BoxE (d n : ℕ) := ↥(boxFinset d n) → ℂ

/-- Extension by zero from the box. -/
def extBox {n : ℕ} (c : BoxE d n) : Coeff d :=
  fun k => if h : k ∈ boxFinset d n then c ⟨k, h⟩ else 0

/-- Restriction to the box. -/
def resBox {n : ℕ} (F : Coeff d) : BoxE d n := fun k => F k.1

theorem resBox_extBox {n : ℕ} (c : BoxE d n) : resBox (extBox c) = c := by
  funext k
  simp [resBox, extBox, k.2]

theorem extBox_apply_mem {n : ℕ} (c : BoxE d n) {k : Lattice d} (hk : k ∈ boxFinset d n) :
    extBox c k = c ⟨k, hk⟩ := by
  simp [extBox, hk]

theorem extBox_apply_not_mem {n : ℕ} (c : BoxE d n) {k : Lattice d} (hk : k ∉ boxFinset d n) :
    extBox c k = 0 := by
  simp [extBox, hk]

theorem isTrigPoly_extBox {n : ℕ} (c : BoxE d n) : IsTrigPoly n (extBox c) := by
  intro k hk
  by_contra hb
  exact hk (extBox_apply_not_mem c (fun h => hb (mem_boxFinset.1 h)))

theorem extBox_resBox {n : ℕ} {F : Coeff d} (h : IsTrigPoly n F) : extBox (resBox F : BoxE d n) = F := by
  funext k
  by_cases hk : k ∈ boxFinset d n
  · rw [extBox_apply_mem _ hk]; rfl
  · rw [extBox_apply_not_mem _ hk, h.eq_zero (fun hb => hk (mem_boxFinset.2 hb))]

theorem extBox_add {n : ℕ} (c₁ c₂ : BoxE d n) : extBox (c₁ + c₂) = extBox c₁ + extBox c₂ := by
  funext k
  by_cases hk : k ∈ boxFinset d n <;> simp [extBox, hk]

theorem extBox_smul {n : ℕ} (z : ℂ) (c : BoxE d n) : extBox (z • c) = z • extBox c := by
  funext k
  by_cases hk : k ∈ boxFinset d n <;> simp [extBox, hk]

theorem truncCoeff_add (n : ℕ) (c₁ c₂ : Coeff d) :
    truncCoeff n (c₁ + c₂) = truncCoeff n c₁ + truncCoeff n c₂ := by
  funext k; by_cases hk : InBox n k <;> simp [truncCoeff, hk]

theorem truncCoeff_smul (n : ℕ) (z : ℂ) (c : Coeff d) :
    truncCoeff n (z • c) = z • truncCoeff n c := by
  funext k; by_cases hk : InBox n k <;> simp [truncCoeff, hk]

theorem truncCoeff_extBox {n : ℕ} (c : BoxE d n) : truncCoeff n (extBox c) = extBox c :=
  (isTrigPoly_extBox c).truncCoeff_eq

/-- The Galerkin generator `P_n 𝓛 P_n`. -/
def galGen (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) (F : Coeff d) : Coeff d :=
  truncCoeff n (forwardGen D ρ (truncCoeff n F))

/-- The Galerkin generator as a `ℂ`-linear map on the box coefficients. -/
def genLin (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) : BoxE d n →ₗ[ℂ] BoxE d n where
  toFun c := resBox (galGen D ρ n (extBox c))
  map_add' c₁ c₂ := by
    funext k
    have e : truncCoeff n (extBox c₁ + extBox c₂) = extBox c₁ + extBox c₂ :=
      ((isTrigPoly_extBox _).add (isTrigPoly_extBox _)).truncCoeff_eq
    simp only [galGen, truncCoeff_extBox, extBox_add, e]
    rw [forwardGen_add D ρ _ _ (isTrigPoly_extBox c₁) (isTrigPoly_extBox c₂), truncCoeff_add]
    rfl
  map_smul' z c := by
    funext k
    have e : truncCoeff n (z • extBox c) = z • extBox c :=
      ((isTrigPoly_extBox _).smul z).truncCoeff_eq
    simp only [galGen, truncCoeff_extBox, extBox_smul, e]
    rw [forwardGen_smul, truncCoeff_smul]
    rfl

/-- The Galerkin generator as a continuous `ℝ`-linear map on the box coefficients. -/
def genCLM (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) : BoxE d n →L[ℝ] BoxE d n :=
  LinearMap.toContinuousLinearMap ((genLin D ρ n).restrictScalars ℝ)

theorem genCLM_apply (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) (c : BoxE d n) :
    genCLM D ρ n c = resBox (galGen D ρ n (extBox c)) := rfl

theorem genCLM_continuousOn (D : DynData d) (ρ : ℝ → Torus d → ℝ) (n : ℕ) (S : Set ℝ)
    (hρ : ∀ k, ContinuousOn (fun σ => coeffOf (ρ σ) k) S) :
    ContinuousOn (fun σ => genCLM D (ρ σ) n) S := by
  rw [continuousOn_clm_apply]
  intro c
  refine continuousOn_pi.2 fun k => ?_
  have : ∀ σ, genCLM D (ρ σ) n c k = forwardGen D (ρ σ) (extBox c) k.1 := by
    intro σ
    simp only [genCLM_apply, resBox, galGen, truncCoeff_extBox]
    have : InBox n k.1 := mem_boxFinset.1 k.2
    simp [truncCoeff, this]
  simp_rw [this]
  exact forwardGen_continuousOn D ρ S hρ _ (isTrigPoly_extBox c) _

/-- The Galerkin system of level `n` (same as `IsGalerkinSolution` of `WellPosed.lean`). -/
structure IsGalSol (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ) (n : ℕ) (φc : Coeff d)
    (F : ℝ → Coeff d) : Prop where
  trig : ∀ τ, IsTrigPoly n (F τ)
  cont : ∀ k, ContinuousOn (fun τ => F τ k) (Set.Icc 0 t)
  eq : ∀ k, ∀ τ ∈ Set.Icc 0 t,
    F τ k = truncCoeff n φc k + ∫ σ in (0 : ℝ)..τ, galGen D (μ (t - σ)) n (F σ) k

theorem integral_apply_box {n : ℕ} {f : ℝ → BoxE d n} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (k : ↥(boxFinset d n)) :
    (∫ σ in a..b, f σ) k = ∫ σ in a..b, f σ k := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(boxFinset d n) => ℂ) k) hf
  simpa using this.symm

theorem coeffOf_comp_continuousOn {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (k : Lattice d) :
    ContinuousOn (fun σ => coeffOf (μ (t - σ)) k) (Set.Icc 0 t) := by
  refine (coeffOf_continuousOn h k).comp (continuousOn_const.sub continuousOn_id) ?_
  intro σ hσ
  exact ⟨by simpa using hσ.2, by linarith [hσ.1, ht.2]⟩

theorem genCLM_comp_continuousOn {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (D : DynData d) (n : ℕ) :
    ContinuousOn (fun σ => genCLM D (μ (t - σ)) n) (Set.Icc 0 t) :=
  genCLM_continuousOn D (fun σ => μ (t - σ)) n _ (coeffOf_comp_continuousOn h ht)

/-- A Galerkin solution gives a solution of the box ODE. -/
theorem IsGalSol.box_eq {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {D : DynData d} {n : ℕ} {φc : Coeff d}
    {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) :
    ContinuousOn (fun τ => (resBox (F τ) : BoxE d n)) (Set.Icc 0 t) ∧
    (resBox (F 0) : BoxE d n) = resBox (truncCoeff n φc) ∧
    ∀ τ ∈ Set.Icc 0 t, (resBox (F τ) : BoxE d n) = resBox (F 0) +
      ∫ σ in (0 : ℝ)..τ, genCLM D (μ (t - σ)) n (resBox (F σ)) := by
  have hx : ContinuousOn (fun τ => (resBox (F τ) : BoxE d n)) (Set.Icc 0 t) :=
    continuousOn_pi.2 fun k => hF.cont k.1
  have h0 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht.1.le⟩
  have hgen : ∀ σ, genCLM D (μ (t - σ)) n (resBox (F σ)) = resBox (galGen D (μ (t - σ)) n (F σ)) := by
    intro σ
    rw [genCLM_apply, extBox_resBox (hF.trig σ)]
  have h00 : (resBox (F 0) : BoxE d n) = resBox (truncCoeff n φc) := by
    funext k
    have := hF.eq k.1 0 h0
    simpa [resBox] using this
  refine ⟨hx, h00, fun τ hτ => ?_⟩
  have hsub : Set.uIcc 0 τ ⊆ Set.Icc 0 t := Set.uIcc_subset_Icc h0 hτ
  have hint : IntervalIntegrable (fun σ => genCLM D (μ (t - σ)) n (resBox (F σ))) volume 0 τ :=
    (((genCLM_comp_continuousOn h ht D n).clm_apply hx).mono hsub).intervalIntegrable
  funext k
  rw [Pi.add_apply, integral_apply_box hint, h00]
  have := hF.eq k.1 τ hτ
  simp only [resBox, hgen] at this ⊢
  rw [this]

theorem galSol_exists_unique {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (D : DynData d) (n : ℕ)
    (φc : Coeff d) :
    ∃ F : ℝ → Coeff d, IsGalSol D μ t n φc F ∧
      ∀ F', IsGalSol D μ t n φc F' → ∀ τ ∈ Set.Icc 0 t, F' τ = F τ := by
  have hAc := genCLM_comp_continuousOn h ht D n
  obtain ⟨x, hx0, hxc, hxe, -⟩ := linear_ode_exists (fun σ => genCLM D (μ (t - σ)) n) t ht.1.le
    hAc (resBox (truncCoeff n φc))
  have h0 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht.1.le⟩
  refine ⟨fun τ => extBox (x τ), ⟨fun τ => isTrigPoly_extBox _, fun k => ?_, fun k τ hτ => ?_⟩, ?_⟩
  · by_cases hk : k ∈ boxFinset d n
    · simp only [extBox_apply_mem _ hk]
      exact (continuousOn_pi.1 hxc) ⟨k, hk⟩
    · simp only [extBox_apply_not_mem _ hk]
      exact continuousOn_const
  · by_cases hk : k ∈ boxFinset d n
    · have hsub : Set.uIcc 0 τ ⊆ Set.Icc 0 t := Set.uIcc_subset_Icc h0 hτ
      have hint : IntervalIntegrable (fun σ => genCLM D (μ (t - σ)) n (x σ)) volume 0 τ :=
        ((hAc.clm_apply hxc).mono hsub).intervalIntegrable
      have e1 := congrFun (hxe τ hτ) ⟨k, hk⟩
      rw [Pi.add_apply, integral_apply_box hint] at e1
      rw [extBox_apply_mem _ hk, e1]
      have hk' : InBox n k := mem_boxFinset.1 hk
      simp only [resBox, truncCoeff, hk', ite_true, genCLM_apply]
    · have hk' : ¬ InBox n k := fun hb => hk (mem_boxFinset.2 hb)
      simp [extBox_apply_not_mem _ hk, truncCoeff, hk', galGen]
  · intro F' hF' τ hτ
    obtain ⟨hx'c, hx'0, hx'e⟩ := hF'.box_eq h ht
    have key := linear_ode_unique (fun σ => genCLM D (μ (t - σ)) n) t hAc x
      (fun τ => resBox (F' τ)) hxc hx'c (fun τ hτ => by rw [hx0]; exact hxe τ hτ)
      hx'e (hx0.trans hx'0.symm) τ hτ
    rw [← extBox_resBox (hF'.trig τ)]
    exact congrArg extBox key.symm

/-! ### Conjugation symmetry -/

/-- Conjugate reflection `c ↦ conj (c(-·))`; the fixed points are the real coefficients. -/
def reflConj (c : Coeff d) : Coeff d := fun k => conj (c (-k))

theorem reflConj_reflConj (c : Coeff d) : reflConj (reflConj c) = c := by
  funext k; simp [reflConj]

theorem isRealCoeff_iff_reflConj (c : Coeff d) : IsRealCoeff c ↔ reflConj c = c := by
  constructor
  · intro h; funext k; simp [reflConj, h k]
  · intro h k
    have := congrFun h k
    simp only [reflConj] at this
    rw [← this]; simp

theorem reflConj_add (c₁ c₂ : Coeff d) : reflConj (c₁ + c₂) = reflConj c₁ + reflConj c₂ := by
  funext k; simp [reflConj]

theorem reflConj_sum {ι : Type*} (s : Finset ι) (f : ι → Coeff d) :
    reflConj (∑ i ∈ s, f i) = ∑ i ∈ s, reflConj (f i) := by
  funext k; simp [reflConj, Finset.sum_apply]

theorem enorm_neg' (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm Lattice.toEuc
  rw [← norm_neg]
  congr 1
  ext i; simp

theorem rieszCoeff_neg (s : ℝ) (k : Lattice d) : rieszCoeff d s (-k) = rieszCoeff d s k := by
  unfold rieszCoeff
  simp [enorm_neg']

theorem laplaceCoeff_reflConj (c : Coeff d) :
    laplaceCoeff (reflConj c) = reflConj (laplaceCoeff c) := by
  funext k
  simp only [laplaceCoeff, reflConj, enorm_neg', map_mul, map_neg, Complex.conj_ofReal]

theorem derivCoeff_reflConj (j : Fin d) (c : Coeff d) :
    derivCoeff j (reflConj c) = reflConj (derivCoeff j c) := by
  funext k
  simp only [PDE.derivCoeff, reflConj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat, map_intCast, Pi.neg_apply, Int.cast_neg]
  ring

theorem gradRieszCoeff_reflConj (s : ℝ) (i : Fin d) (c : Coeff d) :
    gradRieszCoeff d s i (reflConj c) = reflConj (gradRieszCoeff d s i c) := by
  funext k
  simp only [gradRieszCoeff, rieszMult, PDE.derivCoeff, reflConj, rieszCoeff_neg, map_mul,
    map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_intCast, Pi.neg_apply, Int.cast_neg]
  ring

theorem mulCoeff_reflConj (a c : Coeff d) (ha : IsRealCoeff a) :
    mulCoeff a (reflConj c) = reflConj (mulCoeff a c) := by
  funext k
  simp only [mulCoeff, reflConj]
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Lattice d)).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply, map_mul]
  have h1 : a (k - -j) = conj (a (-k - j)) := by
    rw [show -k - j = -(k - -j) by abel, ha]; simp
  rw [h1, neg_neg]

theorem isRealCoeff_gradRieszCoeff (s : ℝ) (i : Fin d) {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (gradRieszCoeff d s i c) := by
  rw [isRealCoeff_iff_reflConj] at hc ⊢
  rw [← gradRieszCoeff_reflConj, hc]

theorem isRealCoeff_derivCoeff (i : Fin d) {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (derivCoeff i c) := by
  rw [isRealCoeff_iff_reflConj] at hc ⊢
  rw [← derivCoeff_reflConj, hc]

theorem isRealCoeff_driftCoeff (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) (j : Fin d) : IsRealCoeff (driftCoeff D ρ j) := by
  intro k
  have h1 := fun i => isRealCoeff_gradRieszCoeff D.s i hρ k
  have h2 := isRealCoeff_derivCoeff j hV k
  simp only [driftCoeff, map_sub, map_sum, map_mul, Complex.conj_ofReal, h1, h2]

theorem transportCoeff_reflConj (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) (F : Coeff d) :
    transportCoeff D ρ (reflConj F) = reflConj (transportCoeff D ρ F) := by
  funext k
  simp only [transportCoeff, derivCoeff_reflConj]
  show _ = conj (transportCoeff D ρ F (-k))
  simp only [transportCoeff]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulCoeff_reflConj _ _ ((isRealCoeff_driftCoeff D ρ hρ hV j))]
  rfl

theorem nonlocalCoeff_reflConj (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (F : Coeff d) :
    nonlocalCoeff D ρ (reflConj F) = reflConj (nonlocalCoeff D ρ F) := by
  funext k
  simp only [nonlocalCoeff, derivCoeff_reflConj, mulCoeff_reflConj _ _ hρ, gradRieszCoeff_reflConj]
  show _ = conj (nonlocalCoeff D ρ F (-k))
  simp only [nonlocalCoeff]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [reflConj]

theorem forwardGen_reflConj (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) (F : Coeff d) :
    forwardGen D ρ (reflConj F) = reflConj (forwardGen D ρ F) := by
  funext k
  have := congrFun (laplaceCoeff_reflConj F) k
  have h2 := congrFun (transportCoeff_reflConj D ρ hρ hV F) k
  have h3 := congrFun (nonlocalCoeff_reflConj D ρ hρ F) k
  simp only [forwardGen, this, h2, h3, reflConj, map_sub, map_add, map_mul, Complex.conj_ofReal]

theorem truncCoeff_reflConj (n : ℕ) (c : Coeff d) :
    truncCoeff n (reflConj c) = reflConj (truncCoeff n c) := by
  funext k
  by_cases hk : InBox n k
  · simp [truncCoeff, reflConj, hk, inBox_neg_iff]
  · simp [truncCoeff, reflConj, hk, inBox_neg_iff]

theorem galGen_reflConj (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) (n : ℕ) (F : Coeff d) :
    galGen D ρ n (reflConj F) = reflConj (galGen D ρ n F) := by
  unfold galGen
  rw [truncCoeff_reflConj, forwardGen_reflConj D ρ hρ hV, truncCoeff_reflConj]

theorem isTrigPoly_reflConj {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) :
    IsTrigPoly n (reflConj c) := by
  intro k hk
  have : c (-k) ≠ 0 := fun h0 => hk (by simp [reflConj, h0])
  exact inBox_neg_iff.1 (h _ this)

theorem integrable_of_coeffHyp {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ} (h : CoeffHyp m Λ T μ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : Integrable (μ r) := by
  by_contra hn
  have := (h.prob r hr).integral_one
  rw [integral_undef hn] at this
  exact zero_ne_one this

theorem isRealCoeff_coeffOf_density {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    IsRealCoeff (coeffOf (μ r)) :=
  isRealCoeff_coeffOf _ (integrable_of_coeffHyp h hr)

theorem isRealCoeff_coeffOf_V {m : ℕ} {VB : ℝ} {V : Torus d → ℝ} (h : VHyp m VB V) :
    IsRealCoeff (coeffOf V) := by
  have hc : Continuous V := Torus.continuous_of_continuous_lift (h.1.continuous)
  exact isRealCoeff_coeffOf _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem IsGalSol.isReal {m : ℕ} {Λ T VB : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {D : DynData d} (hV : VHyp m VB D.V) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {n : ℕ} {φc : Coeff d} (hφ : IsRealCoeff φc) {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) :
    ∀ τ ∈ Set.Icc 0 t, IsRealCoeff (F τ) := by
  obtain ⟨F₀, hF₀, hu⟩ := galSol_exists_unique h ht D n φc
  have hVr := isRealCoeff_coeffOf_V hV
  have hsol : IsGalSol D μ t n φc (fun τ => reflConj (F τ)) := by
    refine ⟨fun τ => isTrigPoly_reflConj (hF.trig τ), fun k => ?_, fun k τ hτ => ?_⟩
    · exact (Complex.continuous_conj.comp_continuousOn (hF.cont (-k)))
    · have h0 : (0 : ℝ) ≤ τ := hτ.1
      have e := hF.eq (-k) τ hτ
      have hφ' : truncCoeff n φc k = conj (truncCoeff n φc (-k)) := by
        have := congrFun (truncCoeff_reflConj n φc) k
        rw [(isRealCoeff_iff_reflConj φc).1 hφ] at this
        exact this
      have hc : ∀ g : ℝ → ℂ, conj (∫ σ in (0 : ℝ)..τ, g σ) = ∫ σ in (0 : ℝ)..τ, conj (g σ) := by
        intro g
        simp only [intervalIntegral.integral_of_le h0]
        exact integral_conj.symm
      show conj (F τ (-k)) = _
      rw [e, map_add, hφ', hc]
      congr 1
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hσ' : σ ∈ Set.Icc 0 t := Set.uIcc_subset_Icc ⟨le_rfl, ht.1.le⟩ hτ hσ
      have hr : t - σ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hσ'.2], by linarith [hσ'.1, ht.2]⟩
      rw [galGen_reflConj D _ (isRealCoeff_coeffOf_density h hr) hVr]
      rfl
  intro τ hτ
  rw [isRealCoeff_iff_reflConj]
  have h1 := hu _ hsol τ hτ
  have h2 := hu _ hF τ hτ
  exact h1.trans h2.symm


theorem exists_symDiag {M : Matrix (Fin d) (Fin d) ℝ} (h : Torus.SymNonpos M) :
    ∃ (lam : Fin d → ℝ) (q : Fin d → Euc d), IsSymDiag M lam q := by
  have hN : (-(Torus.symPart M)).PosSemidef := h
  have hH := hN.isHermitian
  refine ⟨hH.eigenvalues, fun l => hH.eigenvectorBasis l, ⟨fun l => hN.eigenvalues_nonneg l,
    hH.eigenvectorBasis.orthonormal, fun i j => ?_⟩⟩
  have := congrFun (congrFun hH.spectral_theorem i) j
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal, Matrix.IsHermitian.eigenvectorUnitary_apply] at this
  rw [show ∑ l, hH.eigenvalues l * (hH.eigenvectorBasis l).ofLp i * (hH.eigenvectorBasis l).ofLp j
      = ∑ x, (hH.eigenvectorBasis x).ofLp i * hH.eigenvalues x * (hH.eigenvectorBasis x).ofLp j from
      Finset.sum_congr rfl fun l _ => by ring, ← this]
  simp
/-! ### Energy bound -/

theorem hasDerivWithinAt_of_primitive {t : ℝ} {g f : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc 0 t)) (c : ℂ)
    (hf : ∀ τ ∈ Set.Icc 0 t, f τ = c + ∫ σ in (0 : ℝ)..τ, g σ) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt f (g τ) (Set.Icc 0 t) τ := by
  intro τ hτ
  have ht0 : 0 ≤ t := hτ.1.trans hτ.2
  set B : ℝ → ℂ := Set.IccExtend ht0 (fun s : Set.Icc (0 : ℝ) t => g s) with hBdef
  have hB : Continuous B := hg.domRestrict.Icc_extend'
  have hBg : ∀ s ∈ Set.Icc (0 : ℝ) t, B s = g s := fun s hs => Set.IccExtend_of_mem ht0 _ hs
  have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, B s) (B τ) τ :=
    (hB.integral_hasStrictDerivAt 0 τ).hasDerivAt
  have h2 := (h1.const_add c).hasDerivWithinAt (s := Set.Icc 0 t)
  rw [hBg τ hτ] at h2
  have hint : ∀ u ∈ Set.Icc (0 : ℝ) t, ∫ s in (0 : ℝ)..u, g s = ∫ s in (0 : ℝ)..u, B s := by
    intro u hu
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hBg s (Set.uIcc_subset_Icc ⟨le_rfl, ht0⟩ hu hs)]
  exact h2.congr (fun u hu => by rw [hf u hu, hint u hu]) (by rw [hf τ hτ, hint τ hτ])

theorem gronwall_aux {t : ℝ} {y y' : ℝ → ℝ} (a : ℝ)
    (hy : ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt y (y' τ) (Set.Icc 0 t) τ)
    (hle : ∀ τ ∈ Set.Icc 0 t, y' τ ≤ a * y τ) :
    ∀ τ ∈ Set.Icc 0 t, y τ ≤ Real.exp (a * τ) * y 0 := by
  intro τ hτ
  have ht0 : 0 ≤ t := hτ.1.trans hτ.2
  set z : ℝ → ℝ := fun u => Real.exp (-a * u) * y u with hz
  have hzd : ∀ u ∈ Set.Icc 0 t, HasDerivWithinAt z
      (Real.exp (-a * u) * (y' u - a * y u)) (Set.Icc 0 t) u := by
    intro u hu
    have he : HasDerivAt (fun u => Real.exp (-a * u)) (Real.exp (-a * u) * (-a)) u := by
      have := ((hasDerivAt_id u).const_mul (-a)).exp
      simpa using this
    have := he.hasDerivWithinAt.mul (hy u hu)
    convert this using 1
    ring
  have hanti : AntitoneOn z (Set.Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
    · exact fun u hu => (hzd u hu).continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (((hzd u (Set.Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
        ).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [((hzd u (Set.Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by linarith [hle u (Set.Ioo_subset_Icc_self hu)])
  have h := hanti ⟨le_rfl, ht0⟩ hτ hτ.1
  simp only [hz, mul_zero, Real.exp_zero, one_mul] at h
  have h2 : Real.exp (a * τ) * (Real.exp (-a * τ) * y τ) ≤ Real.exp (a * τ) * y 0 :=
    mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  rwa [← mul_assoc, ← Real.exp_add, show a * τ + -a * τ = 0 by ring, Real.exp_zero, one_mul] at h2

theorem galGen_apply_box {n : ℕ} (D : DynData d) (ρ : Torus d → ℝ) {F : Coeff d}
    (hF : IsTrigPoly n F) {k : Lattice d} (hk : InBox n k) :
    galGen D ρ n F k = forwardGen D ρ F k := by
  simp [galGen, hF.truncCoeff_eq, truncCoeff, hk]

theorem galGen_apply_not_box {n : ℕ} (D : DynData d) (ρ : Torus d → ℝ) (F : Coeff d)
    {k : Lattice d} (hk : ¬ InBox n k) : galGen D ρ n F k = 0 := by
  simp [galGen, truncCoeff, hk]

theorem IsGalSol.integrand_continuousOn {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {D : DynData d} {n : ℕ} {φc : Coeff d}
    {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) (k : Lattice d) :
    ContinuousOn (fun σ => galGen D (μ (t - σ)) n (F σ) k) (Set.Icc 0 t) := by
  by_cases hk : k ∈ boxFinset d n
  · obtain ⟨hx, -, -⟩ := hF.box_eq h ht
    have hc := ((genCLM_comp_continuousOn h ht D n).clm_apply hx)
    have := continuousOn_pi.1 hc ⟨k, hk⟩
    refine this.congr fun σ _ => ?_
    simp only [genCLM_apply, extBox_resBox (hF.trig σ), resBox]
  · have hk' : ¬ InBox n k := fun hb => hk (mem_boxFinset.2 hb)
    simp only [galGen_apply_not_box _ _ _ hk']
    exact continuousOn_const

theorem IsGalSol.hasDeriv {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {D : DynData d} {n : ℕ} {φc : Coeff d}
    {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) (k : Lattice d) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ => F τ k)
      (galGen D (μ (t - τ)) n (F τ) k) (Set.Icc 0 t) τ :=
  hasDerivWithinAt_of_primitive (hF.integrand_continuousOn h ht k) (truncCoeff n φc k)
    (hF.eq k)

/-! ### The sign of the retained terms of `energyRHS` -/

theorem rieszCoeff_nonneg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    0 ≤ rieszCoeff d s k := by
  unfold rieszCoeff
  split_ifs with hk
  · exact le_rfl
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hconst : 0 ≤ rieszConst d s := by
      unfold rieszConst
      split_ifs with h0
      · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.Gamma_pos_of_pos (by positivity)).le
      · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
        exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.Gamma_pos_of_pos (by linarith)).le) (Real.Gamma_pos_of_pos (by linarith)).le
    exact mul_nonneg hconst (Real.rpow_nonneg
      (mul_nonneg (by positivity) (norm_nonneg (Lattice.toEuc k))) _)

theorem symbolK_nonneg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q : Euc d)
    (k : Lattice d) : 0 ≤ symbolK d s q k :=
  mul_nonneg (sq_nonneg _) (rieszCoeff_nonneg hd hs0 hsd k)

theorem quadForm_symbolK_nonneg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q : Euc d)
    (c : Coeff d) : 0 ≤ quadForm (symbolK d s q) c :=
  tsum_nonneg fun k => mul_nonneg (symbolK_nonneg hd hs0 hsd q k) (sq_nonneg _)

theorem gradDerivL2Sq_nonneg (α : Fin d → ℕ) (c : Coeff d) : 0 ≤ gradDerivL2Sq α c := by
  refine tsum_nonneg fun k => mul_nonneg (mul_nonneg (by positivity) ?_) (sq_nonneg _)
  refine Finset.prod_nonneg fun i _ => ?_
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem energyRHS_le (hd : 1 ≤ d) (R : Regime) (Λm : ℝ) (D : DynData d) (m : ℕ)
    (lam : Fin d → ℝ) (q : Fin d → Euc d) (hlam : R.IsR2 → ∀ l, 0 ≤ lam l) (μ : Torus d → ℝ)
    (F : Coeff d) : energyRHS R Λm D m lam q μ F ≤ Λm * hsNormSq m F := by
  unfold energyRHS
  have h1 : 0 ≤ (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F :=
    mul_nonneg (div_nonneg D.hβ (by norm_num))
      (Finset.sum_nonneg fun α _ => gradDerivL2Sq_nonneg α F)
  have h2 : 0 ≤ (if R.IsR2 then (1 / 2) * weightedDissipation D m lam q μ F else 0) := by
    split_ifs with hR
    · refine mul_nonneg (by norm_num) ?_
      unfold weightedDissipation
      refine Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun l _ => ?_
      exact mul_nonneg (hlam hR l) (quadForm_symbolK_nonneg hd D.hs0 D.hsd _ _)
    · exact le_rfl
  linarith

/-! ### The energy identity along Galerkin solutions -/

theorem hsNormSq_trig {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) (m : ℝ) :
    hsNormSq m c = ∑ k ∈ boxFinset d n, sobWeight m k * ‖c k‖ ^ 2 := by
  unfold hsNormSq
  apply tsum_eq_sum
  intro k hk
  rw [h.eq_zero (fun hb => hk (mem_boxFinset.2 hb))]
  simp

theorem hsInner_trig {n : ℕ} {c' : Coeff d} (h : IsTrigPoly n c') (m : ℝ) (c : Coeff d) :
    hsInner m c c' = ∑ k ∈ boxFinset d n, ((sobWeight m k : ℝ) : ℂ) * (c k * conj (c' k)) := by
  unfold hsInner
  apply tsum_eq_sum
  intro k hk
  rw [h.eq_zero (fun hb => hk (mem_boxFinset.2 hb))]
  simp

theorem IsGalSol.hasDeriv_hsNormSq {m' : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m' Λ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {D : DynData d} {n : ℕ}
    {φc : Coeff d} {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) (m : ℝ) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ => hsNormSq m (F τ))
      (2 * (hsInner m (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re) (Set.Icc 0 t) τ := by
  intro τ hτ
  have e : (fun τ => hsNormSq m (F τ)) =
      fun τ => ∑ k ∈ boxFinset d n, sobWeight m k * ‖F τ k‖ ^ 2 :=
    funext fun τ => hsNormSq_trig (hF.trig τ) m
  rw [e]
  have hs := HasDerivWithinAt.fun_sum (u := boxFinset d n)
    (fun k _ => ((hF.hasDeriv h ht k τ hτ).norm_sq).const_mul (sobWeight m k))
  convert hs using 1
  rw [hsInner_trig (hF.trig τ), Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [galGen_apply_box _ _ (hF.trig τ) (mem_boxFinset.1 hk), Complex.re_ofReal_mul,
    Complex.inner]
  ring

theorem sobWeight_nonneg (m : ℝ) (k : Lattice d) : 0 ≤ sobWeight m k :=
  Real.rpow_nonneg (by positivity) _

theorem hsNormSq_truncCoeff_le (n : ℕ) {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    hsNormSq m (truncCoeff n c) ≤ hsNormSq m c := by
  have hle : ∀ k, sobWeight m k * ‖truncCoeff n c k‖ ^ 2 ≤ sobWeight m k * ‖c k‖ ^ 2 := by
    intro k
    by_cases hk : InBox n k
    · simp [truncCoeff, hk]
    · simp [truncCoeff, hk]
      exact mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _)
  have hs : Summable fun k => sobWeight m k * ‖truncCoeff n c k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _)) hle hc
  exact hs.tsum_le_tsum hle hc

theorem galSol_bound {m' : ℕ} {Λ T VB : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m' Λ T μ) {D : DynData d} (hV : VHyp m' VB D.V) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {n : ℕ} {φc : Coeff d} (hφ : IsRealCoeff φc) {m : ℝ} (hmem : MemHs m φc)
    {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) (Λm : ℝ)
    (hform : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ G : Coeff d, IsRealCoeff G → IsTrigPoly n G →
      (hsInner m (forwardGen D (μ r) G) G).re ≤ Λm * hsNormSq m G) :
    ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤ Real.exp (Λm * τ) * hsNorm m φc := by
  have hreal := hF.isReal h hV ht hφ
  have hgr := gronwall_aux (t := t) (y := fun τ => hsNormSq m (F τ)) (2 * Λm)
    (hF.hasDeriv_hsNormSq h ht m) (fun τ hτ => by
      have hr : t - τ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
      have := hform (t - τ) hr (F τ) (hreal τ hτ) (hF.trig τ)
      linarith)
  have h0 : F 0 = truncCoeff n φc := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
    simpa using this
  have hy0 : hsNormSq m (F 0) ≤ hsNormSq m φc := by
    rw [h0]; exact hsNormSq_truncCoeff_le n hmem
  intro τ hτ
  have h1 : hsNormSq m (F τ) ≤ Real.exp (Λm * τ) ^ 2 * hsNormSq m φc := by
    refine (hgr τ hτ).trans ?_
    rw [← Real.exp_nat_mul]
    have : (2 : ℝ) * Λm * τ = ((2 : ℕ) : ℝ) * (Λm * τ) := by push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hy0 (Real.exp_pos _).le
  unfold hsNorm
  calc Real.sqrt (hsNormSq m (F τ)) ≤ Real.sqrt (Real.exp (Λm * τ) ^ 2 * hsNormSq m φc) :=
        Real.sqrt_le_sqrt h1
    _ = Real.exp (Λm * τ) * Real.sqrt (hsNormSq m φc) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

theorem regime_symNonpos {R : Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {invβ ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hR : R.IsR2) (h : R.Holds d s M invβ ν₀ T μ) : Torus.SymNonpos M := by
  cases R with
  | R1 => exact absurd hR (by simp [Regime.IsR2])
  | R2a =>
    have h0 : Torus.symPart M = 0 := h.2
    unfold Torus.SymNonpos
    rw [h0, neg_zero]
    exact Matrix.PosSemidef.zero
  | R2b lam0 => exact h.2.1
  | R2c => exact h.2.2
  | R3 => exact absurd hR (by simp [Regime.IsR2])

end HRS.PDE
