import HRS.MC.CepH3J1

/-!
# Packet CEPH3, part J2: the Fisher integrand on `Config` versus the cylinder integrand
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

/-- The integrand of the Fisher variational formula on `Config`. -/
def h3j_Fint (D : DynData 1) (ζ : Config 1 N → (Fin N → Euc 1)) (X : Config 1 N) : ℝ :=
  -2 * configDiv ζ X
        + 2 * D.invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (fun i => Torus.mk (Z i)))
            (fun i => Torus.rep (X i)) (ζ X)
        - ∑ i, ‖ζ X i‖ ^ 2

lemma h3j_fisher_eq (D : DynData 1) (μ : Measure (Config 1 N)) :
    fisherInfo D N μ = ⨆ (ζ : Config 1 N → (Fin N → Euc 1)) (_ : IsFisherTestField ζ),
      ENNReal.ofReal (∫ X, h3j_Fint D ζ X ∂μ) := rfl

/-- The integrand of the cylinder Fisher variational formula. -/
def h3j_Fch (β : ℝ) (U : Ch N → ℝ) (ζt : Ch N → Ch N) (z : Ch N) : ℝ :=
  -2 * ∑ k : Fin N, fderiv ℝ (fun w => ζt w k) z (EuclideanSpace.single k 1)
        + 2 * β⁻¹ * inner ℝ (gradient U z) (ζt z) - ‖ζt z‖ ^ 2

lemma h3j_cylFisher_ge [NeZero N] (β : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) (ζt : Ch N → Ch N)
    (h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζt) (h2 : ∀ z, ζt (z + cep_diag N) = ζt z)
    (h3 : ∃ R : ℝ, ∀ z, R ≤ Metric.infDist z (cep_Alcove N) → ζt z = 0) :
    ENNReal.ofReal (∫ z, h3j_Fch β U ζt z ∂μ) ≤ cep_cylFisher β U μ := by
  unfold cep_cylFisher
  exact le_iSup₂ (f := fun (ζ : Ch N → Ch N) (_ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧ (∀ z, ζ (z + cep_diag N) = ζ z) ∧
      ∃ R : ℝ, ∀ z, R ≤ Metric.infDist z (cep_Alcove N) → ζ z = 0) =>
    ENNReal.ofReal (∫ z, (-2 * ∑ k : Fin N, fderiv ℝ (fun w => ζ w k) z (EuclideanSpace.single k 1)
        + 2 * β⁻¹ * inner ℝ (gradient U z) (ζ z) - ‖ζ z‖ ^ 2) ∂μ)) ζt ⟨h1, h2, h3⟩

/-- The pull-back field `za` agrees with the cut-off field `zt` near points of the alcove. -/
lemma h3j_zt_eventually_eq [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : IsFisherTestField ζ) :
    ∃ δ > 0, (∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) := by
  obtain ⟨K, hKc, hKd, hK0⟩ := hζ.support
  obtain ⟨δ, hδ, hδK⟩ := h3j_delta σ₀ hKc hKd
  refine ⟨δ, hδ, fun z hz => ?_⟩
  by_cases hzK : h3d_Q σ₀ z ∈ K
  · have hsep := hδK z hz hzK
    have hopen : IsOpen {w : Ch N | ∀ k l : Fin N, k < l → δ / 2 < w l - w k ∧ w l - w k < 1 - δ / 2} := by
      have : {w : Ch N | ∀ k l : Fin N, k < l → δ / 2 < w l - w k ∧ w l - w k < 1 - δ / 2} =
          ⋂ k, ⋂ l, ⋂ (_ : k < l), ({w : Ch N | δ / 2 < w l - w k} ∩ {w : Ch N | w l - w k < 1 - δ / 2}) := by
        ext w; simp
      rw [this]
      refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun _ => ?_
      exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)
    have hz' : z ∈ {w : Ch N | ∀ k l : Fin N, k < l → δ / 2 < w l - w k ∧ w l - w k < 1 - δ / 2} := by
      intro k l hkl
      have := hsep k l hkl
      constructor <;> linarith [this.1, this.2]
    filter_upwards [hopen.mem_nhds hz'] with w hw
    have : h3i_chi δ w = 1 := h3i_chi_eq_one hδ fun k l hkl => ⟨(hw k l hkl).1.le, (hw k l hkl).2.le⟩
    unfold h3i_zt h3i_za
    ext k
    simp [this]
  · have hopen : IsOpen ((h3d_Q σ₀) ⁻¹' Kᶜ) := (hKc.isClosed.isOpen_compl).preimage (h3d_Q_continuous σ₀)
    filter_upwards [hopen.mem_nhds hzK] with w hw
    have h0 : ζ (h3d_Q σ₀ w) = 0 := hK0 _ hw
    unfold h3i_zt h3i_za
    ext k
    simp [h0]

lemma h3j_g_contDiff {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) (i : Fin N) (j : Fin 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) i) j) :=
  (contDiff_piLp_apply (p := 2) (i := j)).comp (contDiff_pi.mp hζ.smooth i)

lemma h3j_g_periodic (ζ : Config 1 N → (Fin N → Euc 1)) (i : Fin N) (j : Fin 1) (Y : Fin N → Euc 1) (n : Fin N → ℤ) :
    (fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) i) j) (Y + h3j_ishift n) =
      (fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) i) j) Y := by
  simp only
  have := h3j_mk_add_ishift Y n
  rw [show (fun i => Torus.mk ((Y + h3j_ishift n) i)) = fun i => Torus.mk (Y i + h3j_ishift n i) from rfl, this]

lemma h3j_Lam_single (σ₀ : Equiv.Perm (Fin N)) (k : Fin N) :
    h3j_LamL σ₀ (EuclideanSpace.single k 1) = configBasis 1 N (σ₀ k, 0) := by
  funext i
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp only [h3j_LamL_apply, cep_unrank, configBasis]
  by_cases h : i = σ₀ k
  · subst h; simp
  · have : σ₀.symm i ≠ k := fun e => h (by rw [← e]; simp)
    simp [h, this]

lemma h3j_div_eq [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : IsFisherTestField ζ) {z : Ch N} {δ : ℝ}
    (hev : ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) :
    configDiv ζ (h3d_Q σ₀ z) =
      ∑ k : Fin N, fderiv ℝ (fun w => h3i_zt σ₀ ζ δ w k) z (EuclideanSpace.single k 1) := by
  have hRHS : ∀ k : Fin N, fderiv ℝ (fun w => h3i_zt σ₀ ζ δ w k) z (EuclideanSpace.single k 1) =
      fderiv ℝ (fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) (σ₀ k)) 0) (h3j_LamL σ₀ z)
        (configBasis 1 N (σ₀ k, 0)) := by
    intro k
    have h1 : (fun w => h3i_zt σ₀ ζ δ w k) =ᶠ[𝓝 z] (fun w => h3i_za σ₀ ζ w k) := by
      filter_upwards [hev] with w hw
      rw [hw]
    rw [h1.fderiv_eq]
    have hdiff := ((h3j_g_contDiff hζ (σ₀ k) 0).differentiable (by norm_num)) (h3j_LamL σ₀ z)
    have hcomp := hdiff.hasFDerivAt.comp z (h3j_LamL σ₀).hasFDerivAt
    have : (fun w => h3i_za σ₀ ζ w k) = (fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) (σ₀ k)) 0) ∘ (h3j_LamL σ₀) := rfl
    rw [this, hcomp.fderiv, ContinuousLinearMap.comp_apply, h3j_Lam_single]
  simp_rw [hRHS]
  unfold configDiv
  simp only
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  rw [← Equiv.sum_comp σ₀]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h3j_rep_Q]
  have := h3j_fderiv_periodic (g := fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) (σ₀ k)) 0)
    (fun Y n => h3j_g_periodic ζ (σ₀ k) 0 Y n) (cep_unrank σ₀ z) (fun i => -⌊z (σ₀.symm i)⌋)
  rw [this]
  rfl

lemma h3j_inner_gradient {f : Ch N → ℝ} (z v : Ch N) : inner ℝ (gradient f z) v = fderiv ℝ f z v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma h3j_stricto_toCh (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) :
    cep_StrictlyOrdered π y ↔ cep_toCh π y ∈ cep_Alcove N := Iff.rfl

lemma h3j_ChL_Lam (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) : h3j_ChL σ₀ (h3j_LamL σ₀ z) = z := by
  rw [h3j_ChL_apply, h3j_LamL_apply]; exact h3g_toCh_unrank σ₀ z

theorem h3j_DU_eq {D : DynData 1} [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    (ζ : Config 1 N → (Fin N → Euc 1)) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (fun i => Torus.mk (Z i)))
        (fun i => Torus.rep (h3d_Q σ₀ z i)) (ζ (h3d_Q σ₀ z)) =
      inner ℝ (gradient (fun w => cep_chamberPot 1 N w + Ψ w) z) (h3i_za σ₀ ζ z) := by
  set T : (Fin N → Euc 1) → ℝ := fun Z => totalPotential D (fun i => Torus.mk (Z i)) with hT
  have hper : ∀ Y n, T (Y + h3j_ishift n) = T Y := by
    intro Y n
    simp only [hT]
    rw [show (fun i => Torus.mk ((Y + h3j_ishift n) i)) = fun i => Torus.mk (Y i + h3j_ishift n i) from rfl,
      h3j_mk_add_ishift]
  rw [h3j_rep_Q, h3j_fderiv_periodic hper]
  set U : Ch N → ℝ := fun w => cep_chamberPot 1 N w + Ψ w with hU
  have hUd : DifferentiableAt ℝ U z :=
    (h3a_hasFDerivAt hz).differentiableAt.add (hΨ.differentiable (by norm_num) z)
  have hopen : IsOpen ((h3j_ChL σ₀) ⁻¹' cep_Alcove N) :=
    h3b_alcove_isOpen.preimage (h3j_ChL σ₀).continuous
  have hmem : cep_unrank σ₀ z ∈ ((h3j_ChL σ₀) ⁻¹' cep_Alcove N) := by
    show h3j_ChL σ₀ (cep_unrank σ₀ z) ∈ cep_Alcove N
    rw [h3j_ChL_apply, h3g_toCh_unrank]; exact hz
  have hev : T =ᶠ[𝓝 (cep_unrank σ₀ z)] (U ∘ h3j_ChL σ₀) := by
    filter_upwards [hopen.mem_nhds hmem] with Z hZ
    exact hΨtot σ₀ Z ((h3j_stricto_toCh σ₀ Z).mpr hZ)
  rw [hev.fderiv_eq]
  have hChLam : h3j_ChL σ₀ (cep_unrank σ₀ z) = z := by
    rw [h3j_ChL_apply]; exact h3g_toCh_unrank σ₀ z
  have hUd' : DifferentiableAt ℝ U (h3j_ChL σ₀ (cep_unrank σ₀ z)) := by
    rw [hChLam]; exact hUd
  have hcomp := hUd'.hasFDerivAt.comp (cep_unrank σ₀ z) (h3j_ChL σ₀).hasFDerivAt
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, hChLam, ← h3j_inner_gradient]
  congr 1
end
end HRS.MC.CepH3
