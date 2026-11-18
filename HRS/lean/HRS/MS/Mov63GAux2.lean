import HRS.MS.Mov63GAux1

/-!
# S6.3, packet N8 (part 2): partial derivatives of space-time functions and the Duhamel step

Namespace `HRS.MS.Mov63`, prefix `mng_`.  See `Mov63GAux1`.

* `mngPd i f`: the partial derivative `∂_{x_i} f_t (x)` of a family `f : ℝ → Euc d → ℝ`.
* `mngJC r f`: joint continuity on `[0,∞) × ℝ^d` of `f` and of all iterated partial derivatives of order `≤ r` (recursive definition, so that
  closure under `∂_i`, sums and products is by induction on `r` and needs no Leibniz formula for `iteratedFDeriv`).
* `mngDuh f G`: `f_t(x) = f_0(x) + ∫_0^t G_s(x) ds` (`t ≥ 0`).
* **`mng_duh_pd`**: differentiation under the time integral: `mngDuh f G`, `mngJC 1 G`, smoothness `⇒ mngDuh (∂_i f) (∂_i G)`.
* `mng_duh_hasDeriv`: `mngDuh f G`, `mngJC 0 G` gives the one-sided time derivative `∂_t f_t(x) = G_t(x)` on `[0,∞)`.
* `mng_lap_eq`, `mng_inner_grad`: `Δ g = ∑_i ∂_i∂_i g`, `⟨b, ∇g⟩ = ∑_i b_i ∂_i g`; `mng_pd_comm`: `∂_i∂_k = ∂_k∂_i` on `C²`.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

/-- The `i`-th basis vector. -/
abbrev mngE (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

/-- Partial derivative of a space-time family. -/
def mngPd (i : Fin d) (f : ℝ → Euc d → ℝ) : ℝ → Euc d → ℝ := fun t x => fderiv ℝ (f t) x (mngE i)

/-- Joint continuity of `f` and its iterated partial derivatives of order `≤ r` on `[0,∞) × ℝ^d`. -/
def mngJC : ℕ → (ℝ → Euc d → ℝ) → Prop
  | 0, f => ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Ici 0 ×ˢ univ)
  | r + 1, f => ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Ici 0 ×ˢ univ) ∧ ∀ i, mngJC r (mngPd i f)

/-- Duhamel form. -/
def mngDuh (f G : ℝ → Euc d → ℝ) : Prop :=
  ∀ x, ∀ t : ℝ, 0 ≤ t → f t x = f 0 x + ∫ s in (0 : ℝ)..t, G s x

lemma mngJC_zero {r : ℕ} {f : ℝ → Euc d → ℝ} (h : mngJC r f) :
    ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Ici 0 ×ˢ univ) := by
  cases r with
  | zero => exact h
  | succ r => exact h.1

lemma mngJC_pd {r : ℕ} {f : ℝ → Euc d → ℝ} (h : mngJC (r + 1) f) (i : Fin d) : mngJC r (mngPd i f) := h.2 i

lemma mngJC_mono : ∀ {s r : ℕ} {f : ℝ → Euc d → ℝ}, s ≤ r → mngJC r f → mngJC s f
  | 0, r, f, _, h => mngJC_zero h
  | s + 1, 0, f, hs, _ => absurd hs (by omega)
  | s + 1, r + 1, f, hs, h => ⟨h.1, fun i => mngJC_mono (by omega) (h.2 i)⟩

lemma mngJC_congr {r : ℕ} {f g : ℝ → Euc d → ℝ} (h : mngJC r f) (e : f = g) : mngJC r g := e ▸ h

lemma mng_cd_pd {r : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ (r + 1 : ℕ) g) (i : Fin d) :
    ContDiff ℝ r (fun x => fderiv ℝ g x (mngE i)) := by
  have h1 : ContDiff ℝ r (fderiv ℝ g) := hg.fderiv_right (by exact_mod_cast le_rfl)
  exact h1.clm_apply contDiff_const

lemma mng_pd_add {f g : ℝ → Euc d → ℝ} (hf : ∀ t, Differentiable ℝ (f t)) (hg : ∀ t, Differentiable ℝ (g t))
    (i : Fin d) : mngPd i (fun t x => f t x + g t x) = fun t x => mngPd i f t x + mngPd i g t x := by
  funext t x
  have h : fderiv ℝ (fun y => f t y + g t y) x = fderiv ℝ (f t) x + fderiv ℝ (g t) x :=
    ((hf t x).hasFDerivAt.add (hg t x).hasFDerivAt).fderiv
  simp only [mngPd, h, ContinuousLinearMap.add_apply]

lemma mng_pd_mul {f g : ℝ → Euc d → ℝ} (hf : ∀ t, Differentiable ℝ (f t)) (hg : ∀ t, Differentiable ℝ (g t))
    (i : Fin d) : mngPd i (fun t x => f t x * g t x) =
      fun t x => mngPd i f t x * g t x + f t x * mngPd i g t x := by
  funext t x
  have h : fderiv ℝ (fun y => f t y * g t y) x = f t x • fderiv ℝ (g t) x + g t x • fderiv ℝ (f t) x :=
    ((hf t x).hasFDerivAt.mul (hg t x).hasFDerivAt).fderiv
  simp only [mngPd, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma mng_pd_const_mul {f : ℝ → Euc d → ℝ} (hf : ∀ t, Differentiable ℝ (f t)) (c : ℝ) (i : Fin d) :
    mngPd i (fun t x => c * f t x) = fun t x => c * mngPd i f t x := by
  funext t x
  have h : fderiv ℝ (fun y => c * f t y) x = c • fderiv ℝ (f t) x := ((hf t x).hasFDerivAt.const_mul c).fderiv
  simp only [mngPd, h, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma mng_pd_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → Euc d → ℝ} (hf : ∀ a t, Differentiable ℝ (f a t)) (i : Fin d) :
    mngPd i (fun t x => ∑ a ∈ s, f a t x) = fun t x => ∑ a ∈ s, mngPd i (f a) t x := by
  funext t x
  have h : fderiv ℝ (fun y => ∑ a ∈ s, f a t y) x = ∑ a ∈ s, fderiv ℝ (f a t) x := by
    have := HasFDerivAt.sum (u := s) (A := fun a => f a t) (A' := fun a => fderiv ℝ (f a t) x)
      (x := x) (fun a _ => (hf a t x).hasFDerivAt)
    have e : (fun y => ∑ a ∈ s, f a t y) = ∑ a ∈ s, f a t := by funext y; simp [Finset.sum_apply]
    rw [e]; exact this.fderiv
  simp only [mngPd, h, ContinuousLinearMap.sum_apply]

lemma mng_pd_const (c : ℝ) (i : Fin d) : mngPd i (fun (_ : ℝ) (_ : Euc d) => c) = fun _ _ => 0 := by
  funext t x; simp [mngPd]

lemma mngJC_add : ∀ {r : ℕ} {f g : ℝ → Euc d → ℝ}, (∀ t, ContDiff ℝ r (f t)) → (∀ t, ContDiff ℝ r (g t)) →
    mngJC r f → mngJC r g → mngJC r (fun t x => f t x + g t x)
  | 0, f, g, _, _, hf, hg => ContinuousOn.add hf hg
  | r + 1, f, g, hcf, hcg, hf, hg => by
    refine ⟨ContinuousOn.add hf.1 hg.1, fun i => ?_⟩
    have hdf : ∀ t, Differentiable ℝ (f t) := fun t => (hcf t).differentiable (by simp)
    have hdg : ∀ t, Differentiable ℝ (g t) := fun t => (hcg t).differentiable (by simp)
    rw [mng_pd_add hdf hdg]
    exact mngJC_add (fun t => mng_cd_pd (hcf t) i) (fun t => mng_cd_pd (hcg t) i) (hf.2 i) (hg.2 i)

lemma mngJC_mul : ∀ {r : ℕ} {f g : ℝ → Euc d → ℝ}, (∀ t, ContDiff ℝ r (f t)) → (∀ t, ContDiff ℝ r (g t)) →
    mngJC r f → mngJC r g → mngJC r (fun t x => f t x * g t x)
  | 0, f, g, _, _, hf, hg => ContinuousOn.mul hf hg
  | r + 1, f, g, hcf, hcg, hf, hg => by
    refine ⟨ContinuousOn.mul hf.1 hg.1, fun i => ?_⟩
    have hdf : ∀ t, Differentiable ℝ (f t) := fun t => (hcf t).differentiable (by simp)
    have hdg : ∀ t, Differentiable ℝ (g t) := fun t => (hcg t).differentiable (by simp)
    rw [mng_pd_mul hdf hdg]
    have hf' : ∀ t, ContDiff ℝ r (f t) := fun t => (hcf t).of_le (by exact_mod_cast Nat.le_succ r)
    have hg' : ∀ t, ContDiff ℝ r (g t) := fun t => (hcg t).of_le (by exact_mod_cast Nat.le_succ r)
    exact mngJC_add (fun t => (mng_cd_pd (hcf t) i).mul (hg' t)) (fun t => (hf' t).mul (mng_cd_pd (hcg t) i))
      (mngJC_mul (fun t => mng_cd_pd (hcf t) i) hg' (hf.2 i) (mngJC_mono (Nat.le_succ r) hg))
      (mngJC_mul hf' (fun t => mng_cd_pd (hcg t) i) (mngJC_mono (Nat.le_succ r) hf) (hg.2 i))

lemma mngJC_const (r : ℕ) (c : ℝ) : mngJC (d := d) r (fun _ _ => c) := by
  induction r generalizing c with
  | zero => exact continuousOn_const
  | succ r ih =>
    refine ⟨continuousOn_const, fun i => ?_⟩
    rw [mng_pd_const]
    exact ih 0

lemma mngJC_ofx (r : ℕ) {w : Euc d → ℝ} (hw : ContDiff ℝ r w) : mngJC r (fun _ x => w x) := by
  induction r generalizing w with
  | zero => exact (hw.continuous.comp continuous_snd).continuousOn
  | succ r ih =>
    refine ⟨(hw.continuous.comp continuous_snd).continuousOn, fun i => ?_⟩
    exact ih (mng_cd_pd hw i)

lemma mngJC_sum {ι : Type*} (s : Finset ι) {r : ℕ} {f : ι → ℝ → Euc d → ℝ} (hc : ∀ a t, ContDiff ℝ r (f a t))
    (hf : ∀ a, mngJC r (f a)) : mngJC r (fun t x => ∑ a ∈ s, f a t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mngJC_const (d := d) r 0
  | insert a s ha ih =>
    have h1 := mngJC_add (hc a) (fun t => ?_) (hf a) ih
    · simpa [Finset.sum_insert ha] using h1
    · exact (ContDiff.sum fun b _ => hc b t)

lemma mng_hasDeriv_line {g : Euc d → ℝ} (hg : Differentiable ℝ g) (x : Euc d) (i : Fin d) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => g (x + τ • mngE i)) (fderiv ℝ g (x + τ • mngE i) (mngE i)) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => x + τ • mngE i) (mngE i) τ := by
    simpa using ((hasDerivAt_id τ).smul_const (mngE i)).const_add x
  exact (hg (x + τ • mngE i)).hasFDerivAt.comp_hasDerivAt τ h1

/-- **Differentiation under the time integral.** -/
lemma mng_duh_pd {f G : ℝ → Euc d → ℝ} (hf : ∀ t, Differentiable ℝ (f t)) (hG : ∀ t, Differentiable ℝ (G t))
    (hGc : mngJC 1 G) (hduh : mngDuh f G) (i : Fin d) : mngDuh (mngPd i f) (mngPd i G) := by
  intro x t ht
  have hG0 := mngJC_zero hGc
  have hG1 : ContinuousOn (fun p : ℝ × Euc d => mngPd i G p.1 p.2) (Ici 0 ×ˢ univ) :=
    mngJC_zero (mngJC_pd hGc i)
  -- continuity of the integrands
  have hFc : ∀ τ : ℝ, ContinuousOn (fun s => G s (x + τ • mngE i)) (Ici 0) := fun τ => by
    have := hG0.comp (by fun_prop : Continuous fun s : ℝ => (s, x + τ • mngE i)).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
    exact this
  have hF'c : ∀ τ : ℝ, ContinuousOn (fun s => mngPd i G s (x + τ • mngE i)) (Ici 0) := fun τ => by
    have := hG1.comp (by fun_prop : Continuous fun s : ℝ => (s, x + τ • mngE i)).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
    exact this
  have hIoc : Ioc (0:ℝ) t ⊆ Ici 0 := fun s hs => hs.1.le
  -- the bound
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) t, ∀ y ∈ Metric.closedBall x 1, ‖mngPd i G s y‖ ≤ M := by
    have hK : IsCompact (Icc (0 : ℝ) t ×ˢ Metric.closedBall x 1) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hco : ContinuousOn (fun p : ℝ × Euc d => mngPd i G p.1 p.2) (Icc (0 : ℝ) t ×ˢ Metric.closedBall x 1) :=
      hG1.mono (fun p hp => ⟨hp.1.1, mem_univ _⟩)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hco
    exact ⟨C, fun s hs y hy => hC (s, y) ⟨hs, hy⟩⟩
  have hI : HasDerivAt (fun τ : ℝ => ∫ s in (0 : ℝ)..t, G s (x + τ • mngE i))
      (∫ s in (0 : ℝ)..t, mngPd i G s x) 0 := by
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := t) (F := fun τ s => G s (x + τ • mngE i))
      (F' := fun τ s => mngPd i G s (x + τ • mngE i)) (x₀ := (0 : ℝ)) (s := Metric.ball 0 1)
      (bound := fun _ => M) (Metric.ball_mem_nhds _ one_pos)
      (Filter.Eventually.of_forall fun τ => ?_) ?_ ?_ ?_ ?_ ?_
    · simpa using h.2
    · rw [Set.uIoc_of_le ht]
      exact ((hFc τ).mono hIoc).aestronglyMeasurable measurableSet_Ioc
    · simpa using ContinuousOn.intervalIntegrable_of_Icc ht ((hFc 0).mono Set.Icc_subset_Ici_self)
    · rw [Set.uIoc_of_le ht]
      simpa using ((hF'c 0).mono hIoc).aestronglyMeasurable measurableSet_Ioc
    · refine Filter.Eventually.of_forall fun s hs τ hτ => ?_
      rw [Set.uIoc_of_le ht] at hs
      refine hM s ⟨hs.1.le, hs.2⟩ _ ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : ‖τ • mngE i‖ = |τ| := by simp [norm_smul]
      simp only [add_sub_cancel_left, this]
      have := Metric.mem_ball.1 hτ
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun s hs τ hτ => ?_
      exact mng_hasDeriv_line (hG s) x i τ
  have hΦ : HasDerivAt (fun τ : ℝ => f t (x + τ • mngE i)) (mngPd i f t x) 0 := by
    simpa [mngPd] using mng_hasDeriv_line (hf t) x i 0
  have hΨ : HasDerivAt (fun τ : ℝ => f 0 (x + τ • mngE i)) (mngPd i f 0 x) 0 := by
    simpa [mngPd] using mng_hasDeriv_line (hf 0) x i 0
  have hsum := hΨ.add hI
  have e : (fun τ : ℝ => f t (x + τ • mngE i)) =
      fun τ => f 0 (x + τ • mngE i) + ∫ s in (0 : ℝ)..t, G s (x + τ • mngE i) :=
    funext fun τ => hduh _ t ht
  rw [e] at hΦ
  exact hΦ.unique hsum

lemma mng_duh_hasDeriv {f G : ℝ → Euc d → ℝ} (hG : mngJC 0 G) (hduh : mngDuh f G) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => f s x) (G t x) (Ici 0) t := by
  have hc : ContinuousOn (fun s => G s x) (Ici 0) :=
    hG.comp (by fun_prop : Continuous fun s : ℝ => (s, x)).continuousOn (fun s hs => ⟨hs, mem_univ _⟩)
  have hI : ∀ r ∈ Ici (0 : ℝ), f r x = f 0 x + ∫ s in (0 : ℝ)..r, G s x := fun r hr => hduh x r hr
  have hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (fun s => G s x) volume 0 b := fun b hb =>
    ContinuousOn.intervalIntegrable_of_Icc hb (hc.mono Set.Icc_subset_Ici_self)
  have h1 : HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, G s x) (G t x) (Ici 0) t := by
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      have hm : StronglyMeasurableAtFilter (fun s => G s x) (𝓝[>] (0:ℝ)) volume :=
        (hc.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0
      exact intervalIntegral.integral_hasDerivWithinAt_right (hint 0 le_rfl) hm
        ((hc 0 (Set.mem_Ici.2 le_rfl)).mono_of_mem_nhdsWithin self_mem_nhdsWithin |> fun h => h.mono Set.Ioi_subset_Ici_self)
    · have hm : StronglyMeasurableAtFilter (fun s => G s x) (𝓝 t) volume :=
        (hc.mono (Ioi_subset_Ici_self)).stronglyMeasurableAtFilter isOpen_Ioi t hpos
      have := intervalIntegral.integral_hasDerivAt_right (hint t ht) hm
        ((hc.continuousAt (Ici_mem_nhds hpos)))
      exact this.hasDerivWithinAt
  exact (h1.const_add (f 0 x)).congr hI (hI t ht)

lemma mng_lap_eq {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (x : Euc d) :
    Laplacian.laplacian g x = ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ g y (mngE i)) x (mngE i) := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin d) ℝ)) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h1 : HasFDerivAt (fun y => fderiv ℝ g y (mngE i)) ((fderiv ℝ (fderiv ℝ g) x).flip (mngE i)) x := by
    have := (hasFDerivAt_const (𝕜 := ℝ) (mngE i) x)
    have h2 := hd.hasFDerivAt.clm_apply this
    simpa using h2
  rw [h1.fderiv]
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

lemma mng_inner_grad {g : Euc d → ℝ} (hg : Differentiable ℝ g) (x b : Euc d) :
    inner ℝ b (gradient g x) = ∑ i : Fin d, b i * fderiv ℝ g x (mngE i) := by
  rw [HRS.MS.PoisKolm.kl_inner_gradient]
  have : b = ∑ i : Fin d, (b i : ℝ) • mngE i := by
    ext j; simp [mngE, Pi.single_apply]
  conv_lhs => rw [this]
  rw [map_sum]
  simp

lemma mng_pd_comm {f : ℝ → Euc d → ℝ} (hf : ∀ t, ContDiff ℝ 2 (f t)) (i k : Fin d) :
    mngPd i (mngPd k f) = mngPd k (mngPd i f) := by
  funext t x
  have hd : DifferentiableAt ℝ (fderiv ℝ (f t)) x :=
    ((hf t).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h1 : fderiv ℝ (fun y => fderiv ℝ (f t) y (mngE k)) x (mngE i) = fderiv ℝ (fderiv ℝ (f t)) x (mngE i) (mngE k) := by
    have h2 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (mngE k) x)
    have : fderiv ℝ (fun y => fderiv ℝ (f t) y (mngE k)) x = (fderiv ℝ (fderiv ℝ (f t)) x).flip (mngE k) := by
      simpa using h2.fderiv
    rw [this]; rfl
  have h3 : fderiv ℝ (fun y => fderiv ℝ (f t) y (mngE i)) x (mngE k) = fderiv ℝ (fderiv ℝ (f t)) x (mngE k) (mngE i) := by
    have h2 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (mngE i) x)
    have : fderiv ℝ (fun y => fderiv ℝ (f t) y (mngE i)) x = (fderiv ℝ (fderiv ℝ (f t)) x).flip (mngE i) := by
      simpa using h2.fderiv
    rw [this]; rfl
  show fderiv ℝ (fun y => fderiv ℝ (f t) y (mngE k)) x (mngE i) = fderiv ℝ (fun y => fderiv ℝ (f t) y (mngE i)) x (mngE k)
  rw [h1, h3]
  exact ((hf t).contDiffAt.isSymmSndFDerivAt (by simp)) (mngE i) (mngE k)


end HRS.MS.Mov63

end
