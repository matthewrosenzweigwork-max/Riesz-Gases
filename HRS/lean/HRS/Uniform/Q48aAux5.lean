import HRS.Uniform.Q48aAux4

/-!
# Q48a, part 5: the coordinate integrands of the difference on the whole half-line

`⊤`-copy of `pcXi`, `pc_ctbl_pcXi`, `pc_ItoF_pad` and `pc_Z_isItoC` (`HRS/Prob/HilbertMartingale.lean`) without the
cut-off at the horizon.
-/

noncomputable section

open HRS HRS.MRep HRS.HilbertCLTAux
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48a

section PC3B

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'} {π : Ω' → Ω}
variable {ι : Type*} [Countable ι]

/-- The coordinate integrand `⟨Φ_r u_k, x⟩` on `κ ⊕ ι`, supported on `κ`. -/
def pcXiT (Φ : ℝ → Ω → κ → H) (x : H) (ι : Type*) : ℝ → Ω → κ ⊕ ι → ℝ :=
  fun r ω => Sum.elim (fun k => inner ℝ (Φ r ω k) x) (fun _ => 0)

lemma pc_ctbl_pcXiT {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H) :
    IsCtbl P ℱ (pcXiT Φ x ι) := by
  refine pc_isCtbl_of_HS hΦ x (fun a => ?_) (fun r ω => ?_)
  · rcases a with k | l
    · have h0 : IsProgressive ℱ (fun r ω => inner ℝ (Φ r ω k) x) :=
        fun i => ((hΦ 0).prog k i).inner measurable_const
      simpa [pcXiT] using h0
    · simpa [pcXiT] using isProgressive_const ℱ (0 : ℝ)
  · rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
    have h2 : ∑' l : ι, ‖(pcXiT Φ x ι r ω) (Sum.inr l)‖ₑ ^ 2 = 0 := by
      simp [pcXiT]
    rw [h2, add_zero, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun k => ?_
    simp only [pcXiT, Sum.elim_inl]
    exact pc_enorm_inner_sq_le _ _

lemma pc_ItoF_padT {𝔚' : ℝ≥0 → Ω' → κ ⊕ ι → ℝ} (h𝔚 : IsCylindricalBrownian P' ℱ' 𝔚')
    (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) (hπp : MeasurePreserving π P' P) {Φ : ℝ → Ω → κ → H}
    (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H) (F' : Finset (κ ⊕ ι)) :
    ∀ᵐ ω' ∂P', ∀ τ, ItoF P' ℱ' 𝔚' (fun r ω' => pcXiT Φ x ι r (π ω')) F' τ ω' =
      itoIntegral P' ℱ'
        (fun s ω' (k : F'.preimage Sum.inl Sum.inl_injective.injOn) => 𝔚' s ω' (Sum.inl k))
        (fun r ω' (k : F'.preimage Sum.inl Sum.inl_injective.injOn) =>
          inner ℝ (Φ r (π ω') k) x) τ ω' := by
  classical
  set Fκ := F'.preimage Sum.inl Sum.inl_injective.injOn with hFκ
  let ε : Fκ → F' := fun k => ⟨Sum.inl k, Finset.mem_preimage.1 k.2⟩
  have hε : Function.Injective ε := fun a b h =>
    Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
  have hLg : IsProgressiveL2 P' ℱ' (fun r ω' (k : Fκ) => inner ℝ (Φ r (π ω') k) x) :=
    pc_isProgressiveL2_comp hπm hπp (pc_isProgressiveL2_inner hΦ x Fκ)
  have h1 := itoIntegral_pad ε hε (W₂ := fun s ω' (a : F') => 𝔚' s ω' a) (h𝔚 F')
    ((h𝔚.comp_inj Sum.inl Sum.inl_injective) Fκ) hLg
  have hpad : padFun ε (fun r ω' (k : Fκ) => inner ℝ (Φ r (π ω') k) x) =
      ξF (fun r ω' => pcXiT Φ x ι r (π ω')) F' := by
    funext r ω' a
    obtain ⟨b, hb⟩ := a
    rcases b with k | l
    · have : (⟨Sum.inl k, hb⟩ : F') = ε ⟨k, Finset.mem_preimage.2 hb⟩ := rfl
      simp only [padFun, ξF, pcXiT]
      rw [this, padVec_apply ε hε]
      rfl
    · have hn : (⟨Sum.inr l, hb⟩ : F') ∉ Set.range ε := by
        rintro ⟨k, hk⟩
        exact Sum.inl_ne_inr (congrArg Subtype.val hk)
      simp only [padFun, ξF, pcXiT]
      rw [padVec_of_notMem ε _ hn]
      rfl
  filter_upwards [h1] with ω' h τ
  show itoIntegral P' ℱ' (WF 𝔚' F') (ξF (fun r ω' => pcXiT Φ x ι r (π ω')) F') τ ω' = _
  rw [← hpad]
  exact (h τ).symm

theorem pc_Z_isItoCT {W : ℝ≥0 → Ω → κ → ℝ} (hW : IsCylindricalBrownian P ℱ W)
    {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) {M : ℝ → Ω → H}
    (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) (hπp : MeasurePreserving π P' P)
    {𝔚' : ℝ≥0 → Ω' → κ ⊕ ι → ℝ} (h𝔚 : IsCylindricalBrownian P' ℱ' 𝔚')
    (h𝔚l : ∀ s ω' k, 𝔚' s ω' (Sum.inl k) = W s (π ω') k) (x : H) :
    IsItoC P' ℱ' 𝔚' (fun r ω' => pcXiT Φ x ι r (π ω'))
      (fun τ ω' => inner ℝ (M τ (π ω')) x) := by
  classical
  refine ⟨fun ω' => ?_, fun τ => ?_, fun τ hτ ω' => ?_, fun τ hτ => ?_⟩
  · exact (hM.cont (π ω')).inner continuous_const
  · exact (((hM.adapted τ).inner measurable_const).comp (hπm τ))
  · simp [hM.zero τ hτ (π ω')]
  · have hlim := hM.approx τ hτ x
    have hcomp := hlim.comp (tendsto_finset_preimage_atTop_atTop
      (Sum.inl_injective (α := κ) (β := ι)))
    refine hcomp.congr (fun F' => ?_)
    set Fκ := F'.preimage Sum.inl Sum.inl_injective.injOn with hFκ
    simp only [Function.comp_apply]
    -- the functions on Ω
    set u : ℝ → Ω → Fκ → ℝ := fun r ω (k : Fκ) => inner ℝ (Φ r ω k) x with hu
    have hgL : IsProgressiveL2 P ℱ u := pc_isProgressiveL2_inner hΦ x Fκ
    have hWF : IsBrownianFiltration P ℱ (fun s ω (k : Fκ) => W s ω k) := hW Fκ
    have hWF' : IsBrownianFiltration P' ℱ' (fun s ω' (k : Fκ) => W s (π ω') k) := by
      have := (h𝔚.comp_inj Sum.inl Sum.inl_injective) Fκ
      have e : (fun s ω' (k : Fκ) => 𝔚' s ω' (Sum.inl (k : κ))) =
          (fun s ω' (k : Fκ) => W s (π ω') k) := by
        funext s ω' k; exact h𝔚l s ω' k
      rw [← e]; exact this
    have hK2 := itoIntegral_comp_π hπm hπp hWF hWF' hgL
    have hK3 := pc_ItoF_padT h𝔚 hπm hπp hΦ x F'
    have hWeq : (fun s ω' (k : Fκ) => 𝔚' s ω' (Sum.inl (k : κ))) =
        (fun s ω' (k : Fκ) => W s (π ω') k) := by
      funext s ω' k; exact h𝔚l s ω' k
    have hae : ∀ᵐ ω' ∂P', ‖ItoF P' ℱ' 𝔚' (fun r ω' => pcXiT Φ x ι r (π ω')) F' τ ω' -
          inner ℝ (M τ (π ω')) x‖ₑ ^ 2 =
        (fun ω => ‖itoIntegral P ℱ (fun s ω (k : Fκ) => W s ω k) u τ ω -
          inner ℝ (M τ ω) x‖ₑ ^ 2) (π ω') := by
      filter_upwards [hK3, hK2] with ω' h3 h2
      rw [h3 τ, hWeq, h2 τ]
    have hmeas : Measurable (fun ω => ‖itoIntegral P ℱ (fun s ω (k : Fκ) => W s ω k) u τ ω -
          inner ℝ (M τ ω) x‖ₑ ^ 2) :=
      ((((adapted_itoIntegral P ℱ (fun s ω (k : Fκ) => W s ω k) u τ).mono (ℱ.le _) le_rfl).sub
        (((hM.adapted τ).mono (ℱ.le _) le_rfl).inner measurable_const)).enorm).pow_const 2
    rw [lintegral_congr_ae hae, hπp.lintegral_comp hmeas]

end PC3B

end HRS.Uniform.Q48a
