import HRS.MS.CovMeasAux14

/-!
# S10.1 (worker S101B), part 15: density of the span of the generators in `𝒦`

`s101_span_dense`: the span of `{W_{t,α}} ∪ {(e_α,0,0)}` is dense in `𝒦` (an orthogonal vector has vanishing `ℓ²` components and a vanishing
primitive `t ↦ ∫_0^t ⟨e_α, a'(s)⟩ ds`, hence `a' = 0` by the Lebesgue differentiation theorem).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ} {m T : ℝ}

lemma s101_ae_zero_of_primitive {h : ℝ → ℝ} (hT : 0 ≤ T) (hint : IntegrableOn h (Icc 0 T) volume)
    (h0 : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in Icc 0 t, h s = 0) :
    ∀ᵐ s ∂(volume.restrict (Icc 0 T)), h s = 0 := by
  have hii : IntervalIntegrable h volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hint
  have hF : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, h s = 0 := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    exact h0 t ht
  have hae := hii.ae_hasDerivAt_integral
  have h0n : ∀ᵐ s : ℝ, s ≠ 0 := by simp [ae_iff, measure_singleton]
  have hTn : ∀ᵐ s : ℝ, s ≠ T := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae, h0n, hTn] with x hx hx0 hxT hxI
  have hxuI : x ∈ uIcc 0 T := by rwa [uIcc_of_le hT]
  have h0uI : (0 : ℝ) ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ⟨le_rfl, hT⟩
  have hd := hx hxuI 0 h0uI
  have hxo : x ∈ Ioo 0 T := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxT⟩
  have hev : (fun y => ∫ t in (0 : ℝ)..y, h t) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Icc_mem_nhds hxo.1 hxo.2] with y hy
    exact hF y hy
  have hd0 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, h t) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  exact hd.unique hd0

lemma s101_inner_e (x : OscDual d m) (α : MultiIndex d) : inner ℝ (s101e m α) x = OscDual.coord x α := by
  have h1 := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : MultiIndex d => ℝ) α (1 : ℝ)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from x)
  have h2 : inner ℝ (s101e m α) x = inner ℝ (1 : ℝ)
      ((show lp (fun _ : MultiIndex d => ℝ) 2 from x) α) := h1
  rw [h2]
  simp [OscDual.coord]

lemma s101_inner_Ind (t : ℝ) (e : OscDual d m) (f : L2Path d m T) :
    inner ℝ (s101Ind m T t e) f =
      inner ℝ e (∫ s in Icc (0 : ℝ) t, (f : ℝ → OscDual d m) s ∂(volume.restrict (Icc (0 : ℝ) T))) :=
  L2.inner_indicatorConstLp_eq_inner_setIntegral (𝕜 := ℝ) _ _ _ _

theorem s101_span_dense (hT : 0 ≤ T) :
    (Submodule.span ℝ (s101Gen m T : Set (KSpace d m T))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu
  have hu' : ∀ w ∈ s101Gen m T, inner ℝ w u = 0 := fun w hw => hu w (Submodule.subset_span hw)
  have hueq : u = KSpace.mk u.A₀ u.A' u.B := rfl
  -- the first component
  have h1 : ∀ α, OscDual.coord u.A₀ α = 0 := by
    intro α
    have := hu' (KSpace.mk (s101e m α) 0 0) (Or.inr ⟨α, rfl⟩)
    rw [hueq, s101_inner_mk, inner_zero_left, inner_zero_left, add_zero, add_zero, s101_inner_e] at this
    exact this
  have hA₀ : u.A₀ = 0 := s101_ellVec_ext fun α => by rw [h1 α]; rfl
  -- the last component
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have h3 : ∀ α, OscDual.coord u.B α = 0 := by
    intro α
    have := hu' (s101W m T 0 α) (Or.inl ⟨0, h0T, α, rfl⟩)
    unfold s101W at this
    rw [hueq, s101_inner_mk, inner_zero_left, zero_add, s101_inner_Ind] at this
    have hz : (∫ s in Icc (0 : ℝ) 0, (u.A' : ℝ → OscDual d m) s ∂(volume.restrict (Icc (0 : ℝ) T))) = 0 := by
      refine setIntegral_measure_zero _ ?_
      simp
    rw [hz, inner_zero_right, zero_add, s101_inner_e] at this
    exact this
  have hB : u.B = 0 := s101_ellVec_ext fun α => by rw [h3 α]; rfl
  -- the middle component
  have h4 : ∀ α, ∀ t ∈ Icc (0 : ℝ) T,
      ∫ s in Icc (0 : ℝ) t, inner ℝ (s101e m α) ((u.A' : ℝ → OscDual d m) s)
        ∂(volume.restrict (Icc (0 : ℝ) T)) = 0 := by
    intro α t ht
    have := hu' (s101W m T t α) (Or.inl ⟨t, ht, α, rfl⟩)
    unfold s101W at this
    rw [hueq, s101_inner_mk, inner_zero_left, zero_add, s101_inner_Ind, hB, inner_zero_right,
      add_zero] at this
    have hint : Integrable (fun s => (u.A' : ℝ → OscDual d m) s)
        ((volume.restrict (Icc (0 : ℝ) T)).restrict (Icc (0 : ℝ) t)) :=
      ((Lp.memLp u.A').integrable one_le_two).restrict
    rw [← integral_inner hint] at this
    exact this
  have h5 : ∀ α, ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), OscDual.coord ((u.A' : ℝ → OscDual d m) s) α = 0 := by
    intro α
    have hint : IntegrableOn (fun s => OscDual.coord ((u.A' : ℝ → OscDual d m) s) α) (Icc 0 T) volume := by
      have : Integrable (fun s => inner ℝ (s101e m α) ((u.A' : ℝ → OscDual d m) s))
          (volume.restrict (Icc (0 : ℝ) T)) :=
        ((Lp.memLp u.A').integrable one_le_two).const_inner _
      have h' : Integrable (fun s => OscDual.coord ((u.A' : ℝ → OscDual d m) s) α)
          (volume.restrict (Icc (0 : ℝ) T)) := by simpa [s101_inner_e] using this
      exact h'
    refine s101_ae_zero_of_primitive hT hint fun t ht => ?_
    have := h4 α t ht
    simp only [s101_inner_e] at this
    rwa [Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Icc_subset_Icc_right ht.2)] at this
  have h6 : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), (u.A' : ℝ → OscDual d m) s = 0 := by
    filter_upwards [ae_all_iff.2 h5] with s hs
    exact s101_ellVec_ext fun α => by rw [hs α]; rfl
  have hA' : u.A' = 0 := Lp.eq_zero_iff_ae_eq_zero.2 (by filter_upwards [h6] with s hs; simpa using hs)
  rw [hueq, hA₀, hA', hB]
  rfl

end HRS.MS.CovMeas
