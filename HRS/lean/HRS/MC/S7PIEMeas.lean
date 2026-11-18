import HRS.MC.S7PIEVcont

/-!
# Packet PI-E, part 9: continuity in `t`, in `u`, in `F`, and joint measurability of `V^{t,u}F`
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33 HRS.Sec7

variable {d : ℕ}

/-- standing data of the packet: the adjoint hypotheses at level `J` and the exponents `n₀ < m ≤ n₀ + 1 ≤ J` -/
def PIEData (J : ℕ) (D : DynData d) (μ : ℝ → Torus d → ℝ) (T : ℝ) (m : ℝ) (n₀ : ℕ) : Prop :=
  PIEHyp J D μ T ∧ 1 ≤ n₀ ∧ n₀ + 1 ≤ J ∧ (n₀ : ℝ) < m ∧ m ≤ n₀ + 1

lemma pie_tendsto_of_lip {X : Type*} {l : Filter X} (f g : X → ℝ) (f0 g0 Lc : ℝ)
    (hlip : ∀ᶠ x in l, |f x - f0| ≤ Lc * |g x - g0|) (hg : Tendsto g l (𝓝 g0)) :
    Tendsto f l (𝓝 f0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h0 : Tendsto (fun x => Lc * |g x - g0|) l (𝓝 0) := by
    have := ((hg.sub_const g0).abs).const_mul Lc
    simpa using this
  exact squeeze_zero' (Eventually.of_forall fun x => dist_nonneg)
    (hlip.mono fun x hx => by rwa [Real.dist_eq]) h0

lemma pie_T_lip_t' {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u t t₀ : ℝ, 0 ≤ u → u < t → u < t₀ → t ≤ T → t₀ ≤ T → ∀ j k : NonzeroLattice d,
      |pieT D μ u t j k - pieT D μ u t₀ j k| ≤ L * |t - t₀| * Lattice.jp k.1 ^ (J : ℝ) := by
  obtain ⟨L, hL, hlip⟩ := pie_T_lip_t H
  refine ⟨L, hL, fun u t t₀ hu hut hut₀ htT ht₀T j k => ?_⟩
  rcases lt_trichotomy t t₀ with h | h | h
  · have := hlip u t t₀ hu hut.le (hu.trans_lt hut) h ht₀T j k
    rw [abs_sub_comm, abs_of_neg (sub_neg.2 h), neg_sub]
    exact this
  · subst h; simp
  · have := hlip u t₀ t hu hut₀.le (hu.trans_lt hut₀) h htT j k
    rw [abs_of_pos (sub_pos.2 h)]
    exact this

lemma pie_T_lip_u' {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u u₀ t : ℝ, 0 ≤ u → 0 ≤ u₀ → u ≤ t → u₀ ≤ t → 0 < t → t ≤ T →
      ∀ j k : NonzeroLattice d,
      |pieT D μ u t j k - pieT D μ u₀ t j k| ≤ L * |u - u₀| * Lattice.jp k.1 ^ (J : ℝ) := by
  obtain ⟨L, hL, hlip⟩ := pie_T_lip_u H
  refine ⟨L, hL, fun u u₀ t hu hu₀ hut hu₀t ht0 htT j k => ?_⟩
  rcases le_total u u₀ with h | h
  · have := hlip u u₀ t hu h hu₀t ht0 htT j k
    rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact this
  · have := hlip u₀ u t hu₀ h hut ht0 htT j k
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact this

/-- strong continuity of `t ↦ V^{t,u}F` at `t₀ > u` -/
lemma pie_V_tendsto_t {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} {n₀ : ℕ}
    (P : PIEData J D μ T m n₀) {u : ℝ} (hu : 0 ≤ u) (x₀ : Set.Icc (0 : ℝ) T) (hx₀ : u < x₀.1)
    (F : NegSobolev d m) :
    Tendsto (fun x : Set.Icc (0 : ℝ) T => Vprop D μ m x.1 u F) (𝓝 x₀) (𝓝 (Vprop D μ m x₀.1 u F)) := by
  obtain ⟨H, hn₀, hJ, hm0, hm1⟩ := P
  obtain ⟨L, hL, hlip⟩ := pie_T_lip_t' H
  have hev : ∀ᶠ x : Set.Icc (0 : ℝ) T in 𝓝 x₀, u < x.1 :=
    (continuous_subtype_val.tendsto x₀).eventually (lt_mem_nhds hx₀)
  refine pie_V_tendsto H m n₀ hn₀ hJ hm0 hm1 (𝓝 x₀) (fun x => x.1) (fun _ => u) x₀.1 u ?_
    ⟨⟨hu.trans_lt hx₀, x₀.2.2⟩, hu, hx₀.le⟩ ?_ F
  · filter_upwards [hev] with x hx
    exact ⟨⟨hu.trans_lt hx, x.2.2⟩, hu, hx.le⟩
  · intro j k
    refine pie_tendsto_of_lip _ (fun x : Set.Icc (0 : ℝ) T => x.1) _ x₀.1 (L * Lattice.jp k.1 ^ (J : ℝ))
      ?_ (continuous_subtype_val.tendsto x₀)
    filter_upwards [hev] with x hx
    have := hlip u x.1 x₀.1 hu hx hx₀ x.2.2 x₀.2.2 j k
    calc _ ≤ L * |x.1 - x₀.1| * Lattice.jp k.1 ^ (J : ℝ) := this
      _ = _ := by ring

/-- continuity of `u ↦ V^{t,u}F` on `[0,t]` -/
lemma pie_V_continuous_u {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} {n₀ : ℕ}
    (P : PIEData J D μ T m n₀) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (F : NegSobolev d m) :
    Continuous (fun u : Set.Icc (0 : ℝ) t => Vprop D μ m t u.1 F) := by
  obtain ⟨H, hn₀, hJ, hm0, hm1⟩ := P
  obtain ⟨L, hL, hlip⟩ := pie_T_lip_u' H
  rw [continuous_iff_continuousAt]
  intro x₀
  refine pie_V_tendsto H m n₀ hn₀ hJ hm0 hm1 (𝓝 x₀) (fun _ => t) (fun x => x.1) t x₀.1
    (Eventually.of_forall fun x => ⟨ht, x.2⟩) ⟨ht, x₀.2⟩ ?_ F
  intro j k
  refine pie_tendsto_of_lip _ (fun x : Set.Icc (0 : ℝ) t => x.1) _ x₀.1 (L * Lattice.jp k.1 ^ (J : ℝ))
    (Eventually.of_forall fun x => ?_) (continuous_subtype_val.tendsto x₀)
  have := hlip x.1 x₀.1 t x.2.1 x₀.2.1 x.2.2 x₀.2.2 ht.1 ht.2 j k
  calc _ ≤ L * |x.1 - x₀.1| * Lattice.jp k.1 ^ (J : ℝ) := this
    _ = _ := by ring

lemma pie_ext {m : ℝ} (X Y : NegSobolev d m) (h : ∀ k, NegSobolev.coord X k = NegSobolev.coord Y k) :
    X = Y := by
  show (X : lp (fun _ : NonzeroLattice d => ℝ) 2) = (Y : lp (fun _ : NonzeroLattice d => ℝ) 2)
  exact lp.ext (funext h)

lemma pie_coeff_summable {m : ℝ} (F : NegSobolev d m) :
    Summable fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j) ^ 2 := by
  have hcoord : ∀ j : NonzeroLattice d,
      Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j = NegSobolev.coord F j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos j.1)]; simp
  obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
  exact hF2.congr fun j => by rw [hcoord]

/-- linearity of `V^{t,u}` (under a finite-section bound) -/
lemma pie_Vprop_sub (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hH : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) A)
    (F G : NegSobolev d m) :
    Vprop D μ m t u (F - G) = Vprop D μ m t u F - Vprop D μ m t u G := by
  apply pie_ext
  intro k
  have hwpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have e3 : NegSobolev.coord (Vprop D μ m t u F - Vprop D μ m t u G) k =
      NegSobolev.coord (Vprop D μ m t u F) k - NegSobolev.coord (Vprop D μ m t u G) k := rfl
  rw [e3, pie_Vprop_coord D μ m t u hA hH (F - G) k, pie_Vprop_coord D μ m t u hA hH F k,
    pie_Vprop_coord D μ m t u hA hH G k]
  have hF := pie_row_summable hwpos hH (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
  have hG := pie_row_summable hwpos hH (fun j => NegSobolev.fourierCoeff G j) (pie_coeff_summable G) k
  have e4 : ∀ j, NegSobolev.fourierCoeff (F - G) j = NegSobolev.fourierCoeff F j - NegSobolev.fourierCoeff G j := by
    intro j
    unfold NegSobolev.fourierCoeff
    have : NegSobolev.coord (F - G) j = NegSobolev.coord F j - NegSobolev.coord G j := rfl
    rw [this, mul_sub]
  simp_rw [e4, sub_mul]
  rw [Summable.tsum_sub hF hG]
  ring

lemma pie_V_lip_F (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hH : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) A)
    (F G : NegSobolev d m) :
    ‖Vprop D μ m t u F - Vprop D μ m t u G‖ ≤ A * ‖F - G‖ := by
  rw [← pie_Vprop_sub D μ m t u hA hH F G]
  exact pie_Vbound_of_finBd D μ m t u hA hH (F - G)

/-- joint continuity of `(u, F) ↦ V^{t,u}F` on `[0,t] × E_m` -/
lemma pie_V_jointCont {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} {n₀ : ℕ}
    (P : PIEData J D μ T m n₀) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) :
    Continuous (fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => Vprop D μ m t p.1.1 p.2) := by
  have P' := P
  obtain ⟨H, hn₀, hJ, hm0, hm1⟩ := P
  obtain ⟨A, hA, hAb⟩ := pie_finBd_real H m n₀ hn₀ hJ hm0 hm1
  rw [continuous_iff_continuousAt]
  rintro ⟨u₀, F₀⟩
  have e : (fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => Vprop D μ m t p.1.1 p.2) =
      fun p => Vprop D μ m t p.1.1 (p.2 - F₀) + Vprop D μ m t p.1.1 F₀ := by
    funext p
    rw [pie_Vprop_sub D μ m t p.1.1 hA (hAb t ht p.1.1 p.1.2) p.2 F₀]
    abel
  have h1 : Tendsto (fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => Vprop D μ m t p.1.1 (p.2 - F₀))
      (𝓝 (u₀, F₀)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hq : Tendsto (fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => A * ‖p.2 - F₀‖) (𝓝 (u₀, F₀)) (𝓝 0) := by
      have : Tendsto (fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => ‖p.2 - F₀‖) (𝓝 (u₀, F₀)) (𝓝 0) := by
        have h := ((continuous_snd.sub continuous_const).norm :
          Continuous fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => ‖p.2 - F₀‖).tendsto (u₀, F₀)
        simpa using h
      simpa using this.const_mul A
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) hq
    have := pie_V_lip_F D μ m t p.1.1 hA (hAb t ht p.1.1 p.1.2) p.2 F₀
    have h0 : Vprop D μ m t p.1.1 (p.2 - F₀) = Vprop D μ m t p.1.1 p.2 - Vprop D μ m t p.1.1 F₀ :=
      pie_Vprop_sub D μ m t p.1.1 hA (hAb t ht p.1.1 p.1.2) p.2 F₀
    rw [h0]; exact this
  have h2 : Tendsto (fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => Vprop D μ m t p.1.1 F₀)
      (𝓝 (u₀, F₀)) (𝓝 (Vprop D μ m t u₀.1 F₀)) :=
    ((pie_V_continuous_u P' ht F₀).tendsto u₀).comp (continuous_fst.tendsto (u₀, F₀))
  have h0' : Vprop D μ m t u₀.1 0 = 0 := by
    have := pie_Vprop_sub D μ m t u₀.1 hA (hAb t ht u₀.1 u₀.2) 0 0
    simpa using this
  have h3 := h1.add h2
  rw [zero_add] at h3
  rw [ContinuousAt, e]
  simpa [h0'] using h3

/-- measurability of `u ↦ V^{t,u}(b u)` on a measurable subset of `[0,t]` -/
lemma pie_V_aesm {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} {n₀ : ℕ}
    (P : PIEData J D μ T m n₀) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {S : Set ℝ} (hS : MeasurableSet S)
    (hSt : S ⊆ Set.Icc 0 t) {b : ℝ → NegSobolev d m} (hb : AEStronglyMeasurable b (volume.restrict S)) :
    AEStronglyMeasurable (fun u => Vprop D μ m t u (b u)) (volume.restrict S) := by
  have hproj : Continuous (fun p : ℝ × NegSobolev d m => (Set.projIcc 0 t ht.1.le p.1, p.2)) :=
    (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  have hΦ : Continuous (fun p : ℝ × NegSobolev d m =>
      Vprop D μ m t (Set.projIcc 0 t ht.1.le p.1).1 p.2) :=
    by
      have h : Continuous ((fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => Vprop D μ m t p.1.1 p.2) ∘
          (fun p : ℝ × NegSobolev d m => (Set.projIcc 0 t ht.1.le p.1, p.2))) :=
        Continuous.comp (pie_V_jointCont P ht) hproj
      exact h
  have hg : AEStronglyMeasurable (fun u => (u, b u)) (volume.restrict S) :=
    aestronglyMeasurable_id.prodMk hb
  refine (hΦ.comp_aestronglyMeasurable hg).congr ?_
  refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun u hu => ?_)
  simp only [Function.comp]
  rw [Set.projIcc_of_mem _ (hSt hu)]

end HRS.MC.Sec7.PIE

end
