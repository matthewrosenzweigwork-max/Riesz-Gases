import HRS.MS.CovMeasAux13

/-!
# S10.1 (worker S101B), part 14: measurability of `τ ↦ D_τ(u,v)` on the span of the generators

The generators are `W_{t,α}` (`t ∈ [0,T]`) and `(e_α,0,0)`.  `D_τ(u,v)` depends on `u` only through `x ↦ ⟨Γ_τ(x),u⟩`
(`s101_D_congr_left`), and `⟨Γ_τ(x),(e_α,0,0)⟩ = ⟨Γ_τ(x),W_{0,α}⟩`.  By bilinearity the pairing is a.e.-measurable on the span.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

lemma s101_Gamma_diff (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    Differentiable ℝ (fun x => s101Gamma C m T τ x) := by
  obtain ⟨c, hD⟩ := s101_data_of_horb A.hd A.horb
  obtain ⟨B, hB0, hB⟩ := s101_gamma_smooth A.hd hD
  exact (hB τ hτ).1.differentiable (by exact_mod_cast Nat.succ_ne_zero r)

lemma s101_D_apply (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (u v : KSpace d m T) :
    s101D C m T z τ u v = 2 * C.ν * z τ (s101Fm (s101Gamma C m T τ) (s101Rk u v)) := by
  obtain ⟨K0, -, hK⟩ := s101_D_data A.hd A.hP A.horb
  exact (hK z A.hz τ hτ).1 u v

/-- `D_τ(u,v)` depends on `u` only through `x ↦ ⟨Γ_τ(x),u⟩`. -/
lemma s101_D_congr_left (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {u u' : KSpace d m T}
    (h : ∀ x, inner ℝ (s101Gamma C m T τ x) u = inner ℝ (s101Gamma C m T τ x) u') (v : KSpace d m T) :
    s101D C m T z τ u v = s101D C m T z τ u' v := by
  have hΓ := s101_Gamma_diff A hτ
  rw [s101_D_apply A hτ, s101_D_apply A hτ,
    s101_Fm_Rk_eq_inner hΓ (u := u) (v := v) (f := fun x => inner ℝ (s101Gamma C m T τ x) u)
      (f' := fun x => inner ℝ (s101Gamma C m T τ x) v) (fun x => rfl) (fun x => rfl),
    s101_Fm_Rk_eq_inner hΓ (u := u') (v := v) (f := fun x => inner ℝ (s101Gamma C m T τ x) u)
      (f' := fun x => inner ℝ (s101Gamma C m T τ x) v) (fun x => (h x).symm) (fun x => rfl)]

/-- The generators of the dense subspace of `𝒦`. -/
def s101Gen (m T : ℝ) : Set (KSpace d m T) :=
  {u | ∃ t ∈ Icc (0 : ℝ) T, ∃ α : MultiIndex d, u = s101W m T t α} ∪
    {u | ∃ α : MultiIndex d, u = KSpace.mk (s101e m α) 0 0}

lemma s101_A_eq_W0 (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) (v : KSpace d m T) :
    s101D C m T z τ (KSpace.mk (s101e m α) 0 0) v = s101D C m T z τ (s101W m T 0 α) v := by
  obtain ⟨c, hD⟩ := s101_data_of_horb A.hd A.horb
  refine s101_D_congr_left A hτ (fun x => ?_) v
  have h1 := s101g_A hD hτ α x
  have h2 := s101g_W hD hτ ⟨le_rfl, hT⟩ α x
  unfold s101g at h1 h2
  unfold s101W
  rw [h1, h2, if_neg (not_lt.2 hτ.1)]

theorem s101_D_gen_aem (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {u v : KSpace d m T}
    (hu : u ∈ s101Gen m T) (hv : v ∈ s101Gen m T) :
    AEMeasurable (fun τ => s101D C m T z τ u v) (volume.restrict (Icc 0 T)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  rcases hu with ⟨t, ht, α, rfl⟩ | ⟨α, rfl⟩ <;> rcases hv with ⟨t', ht', β, rfl⟩ | ⟨β, rfl⟩
  · exact s101_D_W_aem A hT ht ht' α β
  · refine (s101_D_W_aem A hT ht h0 α β).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
    show s101D C m T z τ (s101W m T t α) (s101W m T 0 β) =
      s101D C m T z τ (s101W m T t α) (KSpace.mk (s101e m β) 0 0)
    rw [s101_D_symm A hτ (s101W m T t α) (KSpace.mk (s101e m β) 0 0), s101_A_eq_W0 A hT hτ,
      s101_D_symm A hτ (s101W m T 0 β) (s101W m T t α)]
  · refine (s101_D_W_aem A hT h0 ht' α β).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
    show s101D C m T z τ (s101W m T 0 α) (s101W m T t' β) =
      s101D C m T z τ (KSpace.mk (s101e m α) 0 0) (s101W m T t' β)
    rw [s101_A_eq_W0 A hT hτ]
  · refine (s101_D_W_aem A hT h0 h0 α β).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
    show s101D C m T z τ (s101W m T 0 α) (s101W m T 0 β) =
      s101D C m T z τ (KSpace.mk (s101e m α) 0 0) (KSpace.mk (s101e m β) 0 0)
    rw [s101_A_eq_W0 A hT hτ α (KSpace.mk (s101e m β) 0 0),
      s101_D_symm A hτ (s101W m T 0 α) (KSpace.mk (s101e m β) 0 0), s101_A_eq_W0 A hT hτ β (s101W m T 0 α),
      s101_D_symm A hτ (s101W m T 0 β) (s101W m T 0 α)]

theorem s101_D_span_aem (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {u v : KSpace d m T}
    (hu : u ∈ Submodule.span ℝ (s101Gen m T)) (hv : v ∈ Submodule.span ℝ (s101Gen m T)) :
    AEMeasurable (fun τ => s101D C m T z τ u v) (volume.restrict (Icc 0 T)) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    induction hv using Submodule.span_induction with
    | mem v hv => exact s101_D_gen_aem A hT hu hv
    | zero =>
      have : (fun τ => s101D C m T z τ u 0) = fun _ => 0 := by funext τ; simp
      rw [this]; exact aemeasurable_const
    | add v v' _ _ h h' =>
      have : (fun τ => s101D C m T z τ u (v + v')) =
          fun τ => s101D C m T z τ u v + s101D C m T z τ u v' := by funext τ; simp
      rw [this]; exact h.add h'
    | smul c v _ h =>
      have : (fun τ => s101D C m T z τ u (c • v)) = fun τ => c * s101D C m T z τ u v := by
        funext τ; simp
      rw [this]; exact h.const_mul c
  | zero =>
    have : (fun τ => s101D C m T z τ 0 v) = fun _ => 0 := by funext τ; simp
    rw [this]; exact aemeasurable_const
  | add u u' _ _ h h' =>
    have : (fun τ => s101D C m T z τ (u + u') v) =
        fun τ => s101D C m T z τ u v + s101D C m T z τ u' v := by funext τ; simp
    rw [this]; exact h.add h'
  | smul c u _ h =>
    have : (fun τ => s101D C m T z τ (c • u) v) = fun τ => c * s101D C m T z τ u v := by
      funext τ; simp
    rw [this]; exact h.const_mul c

end HRS.MS.CovMeas
