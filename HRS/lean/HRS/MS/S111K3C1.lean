import HRS.MS.S111K3A
import HRS.MS.S111K3B2

/-!
# S11.1 continuation (S11K3), B03 part C1: the covariance density of the shifted window, generic measurability tools

`k3D C m T u z v`: the bounded symmetric bilinear form `(h,k) ↦ 2ν z^v(Σ_a ⟨h,Γ_{v,a}⟩⟨k,Γ_{v,a}⟩)` on `𝒦_T`
(`Γ_{v,a} = r2WindowFeature (∂_a) u v`), with the trace-norm bound `‖D_v‖₁ ≤ 2|ν| ‖z^v‖ K age(v)²` (from `s111k_Dform_data`).
Generic: a Borel set of full measure on which a family of bilinear forms is entrywise measurable once its pairings
on a dense generating set are a.e.-measurable (`k3_exists_good`), and the shifted dyadic approximation `k3_aem_diag`.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.S52 HRS.MS.FixEq
open Classical

variable {d : ℕ}

/-- The gradient window features `Γ_{v,a}`. -/
def k3G (C : WholeCoeff d) (m T u v : ℝ) (i : Fin d) : Euc d → KSpace d m T :=
  fun x => r2WindowFeature C m T (gradComp i) u v x

/-- The standing hypotheses of the shifted covariance density. -/
structure K3Adm (C : WholeCoeff d) (m T u c0 : ℝ) (r : ℕ) (b : MultiIndex d → ℝ) (Pw K1 : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) : Prop where
  hd : 1 ≤ d
  hP : (d : ℝ) < 2 * Pw
  hW : S111k2WindowOrbitInput C m c0 r b
  hbS : Summable fun α => b α ^ 2
  hc0 : 0 ≤ c0
  hu : 0 ≤ u
  hT : 0 ≤ T
  hK1 : 0 ≤ K1
  hG : ∀ v ∈ Icc (0 : ℝ) (u + T), ∀ i : Fin d, ContDiff ℝ r (k3G C m T u v i) ∧
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (k3G C m T u v i) x‖ ≤ K1 * s111k2_age c0 u v
  hz : S101Lin r Pw (u + T) z
  hmeas : R2JIntegrandMeas C m (u + T) z

open Classical in
/-- The covariance density of `z` at forcing time `v` as a bilinear form on `𝒦_T`. -/
def k3D (C : WholeCoeff d) (m T u : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ) : K3Bil d m T :=
  if h : ∃ Dc : K3Bil d m T, ∀ x y, Dc x y =
      2 * C.ν * z v (s111kFg (k3G C m T u v) (s101Rk x y)) then h.choose else 0

variable {C : WholeCoeff d} {m T u c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {Pw K1 : ℝ}
  {z z' : ℝ → (Euc d → ℝ) → ℝ}

theorem k3_D_data (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) :
    (∀ x y, k3D C m T u z v x y = 2 * C.ν * z v (s111kFg (k3G C m T u v) (s101Rk x y))) ∧
    (∀ x y, k3D C m T u z v x y = k3D C m T u z v y x) ∧
    BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) =>
      ∑ i, |k3D C m T u z v (p.1.2.1 i) (p.1.2.2 i)|) ∧
    ENNReal.ofReal (HRS.traceNormForm (k3D C m T u z v)) ≤
      ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z v) *
        ENNReal.ofReal (s57pC d r Pw * s101Cf d r (K1 * s111k2_age c0 u v)) := by
  have hη := s101_isBounded_of_lin A.hz hv (2 * C.ν)
  have hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (k3G C m T u v i) := fun i => (A.hG v hv i).1
  have hGb : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (k3G C m T u v i) x‖ ≤ K1 * s111k2_age c0 u v :=
    fun i j hj x => (A.hG v hv i).2 j hj x
  have hA0 : 0 ≤ K1 * s111k2_age c0 u v := mul_nonneg A.hK1 (Real.exp_pos _).le
  obtain ⟨Dc, hDc, hsym, hbdd, htr⟩ := s111k_Dform_data (G := k3G C m T u v) (r := r) (P := Pw)
    (A := K1 * s111k2_age c0 u v) A.hP hG hGb hA0 hη
  have hex : ∃ Dc : K3Bil d m T, ∀ x y, Dc x y =
      2 * C.ν * z v (s111kFg (k3G C m T u v) (s101Rk x y)) := ⟨Dc, hDc⟩
  have hEq : k3D C m T u z v = Dc := by
    have hspec : ∀ x y, k3D C m T u z v x y = 2 * C.ν * z v (s111kFg (k3G C m T u v) (s101Rk x y)) := by
      unfold k3D; rw [dif_pos hex]; exact hex.choose_spec
    ext x y
    rw [hspec, hDc]
  rw [hEq]
  refine ⟨hDc, hsym, hbdd, htr.trans ?_⟩
  exact mul_le_mul' (s101_dualNormE_smul_le (r := r) (P := Pw) (2 * C.ν) (z v)) le_rfl

lemma k3_D_apply (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) (x y : KSpace d m T) :
    k3D C m T u z v x y = 2 * C.ν * z v (s111kFg (k3G C m T u v) (s101Rk x y)) :=
  (k3_D_data A hv).1 x y

lemma k3_D_symm (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) (x y : KSpace d m T) :
    k3D C m T u z v x y = k3D C m T u z v y x :=
  (k3_D_data A hv).2.1 x y

lemma k3_Fg_eq {G : Fin d → Euc d → KSpace d m T} {h k : KSpace d m T} {f f' : Fin d → Euc d → ℝ}
    (hf : ∀ i x, inner ℝ (G i x) h = f i x) (hf' : ∀ i x, inner ℝ (G i x) k = f' i x) :
    s111kFg G (s101Rk h k) = fun x => ∑ i, f i x * f' i x := by
  funext x
  simp only [s111kFg, s101Rk_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (G i x) h, real_inner_comm (G i x) k, hf, hf']

/-- `D_v(h,k)` depends on `h` only through the pairing functions `x ↦ ⟨Γ_{v,a}(x),h⟩`. -/
lemma k3_D_congr_left (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    {h h' : KSpace d m T} (hh : ∀ i x, inner ℝ (k3G C m T u v i x) h = inner ℝ (k3G C m T u v i x) h')
    (k : KSpace d m T) : k3D C m T u z v h k = k3D C m T u z v h' k := by
  rw [k3_D_apply A hv, k3_D_apply A hv,
    k3_Fg_eq (G := k3G C m T u v) (h := h) (k := k) (f := fun i x => inner ℝ (k3G C m T u v i x) h)
      (f' := fun i x => inner ℝ (k3G C m T u v i x) k) (fun i x => rfl) (fun i x => rfl),
    k3_Fg_eq (G := k3G C m T u v) (h := h') (k := k) (f := fun i x => inner ℝ (k3G C m T u v i x) h)
      (f' := fun i x => inner ℝ (k3G C m T u v i x) k) (fun i x => (hh i x).symm) (fun i x => rfl)]

lemma k3_D_zero_left (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    {h : KSpace d m T} (hh : ∀ i x, inner ℝ (k3G C m T u v i x) h = 0) (k : KSpace d m T) :
    k3D C m T u z v h k = 0 := by
  have := k3_D_congr_left A hv (h := h) (h' := 0) (fun i x => by rw [hh i x, inner_zero_right]) k
  rw [this]; simp

/-! ### Generic measurability tools -/

/-- A Borel set of full measure (in `E`) on which the family `D` is entrywise measurable, from the a.e.-measurability of the
pairings on a dense generating set. -/
theorem k3_exists_good (D : ℝ → K3Bil d m T) {E : Set ℝ} (hE : MeasurableSet E) {Gen : Set (KSpace d m T)}
    (hden : Dense (Submodule.span ℝ Gen : Set (KSpace d m T)))
    (hgen : ∀ h ∈ Gen, ∀ k ∈ Gen, AEMeasurable (fun v => D v h k) (volume.restrict E)) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ E ∧ volume (E \ G) = 0 ∧
      ∀ h k : KSpace d m T, Measurable (fun v => if v ∈ G then D v h k else 0) := by
  classical
  have hspan : ∀ h ∈ Submodule.span ℝ Gen, ∀ k ∈ Submodule.span ℝ Gen,
      AEMeasurable (fun v => D v h k) (volume.restrict E) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      intro k hk
      induction hk using Submodule.span_induction with
      | mem k hk => exact hgen h hh k hk
      | zero =>
        have : (fun v => D v h 0) = fun _ => 0 := by funext v; simp
        rw [this]; exact aemeasurable_const
      | add k k' _ _ hk hk' =>
        have : (fun v => D v h (k + k')) = fun v => D v h k + D v h k' := by funext v; simp
        rw [this]; exact hk.add hk'
      | smul c k _ hk =>
        have : (fun v => D v h (c • k)) = fun v => c * D v h k := by funext v; simp
        rw [this]; exact hk.const_mul c
    | zero =>
      intro k _
      have : (fun v => D v 0 k) = fun _ => 0 := by funext v; simp
      rw [this]; exact aemeasurable_const
    | add h h' _ _ hh hh' =>
      intro k hk
      have : (fun v => D v (h + h') k) = fun v => D v h k + D v h' k := by funext v; simp
      rw [this]; exact (hh k hk).add (hh' k hk)
    | smul c h _ hh =>
      intro k hk
      have : (fun v => D v (c • h) k) = fun v => c * D v h k := by funext v; simp
      rw [this]; exact (hh k hk).const_mul c
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (↥(Submodule.span ℝ Gen))
  set 𝒟 : Set (KSpace d m T) := Subtype.val '' s with h𝒟
  have h𝒟c : 𝒟.Countable := hsc.image _
  have h𝒟S : ∀ w ∈ 𝒟, w ∈ Submodule.span ℝ Gen := by rintro _ ⟨x, _, rfl⟩; exact x.2
  have h𝒟d : Dense 𝒟 := by
    have hdr : DenseRange (Subtype.val : Submodule.span ℝ Gen → KSpace d m T) := by
      unfold DenseRange; rw [Subtype.range_coe]; exact hden
    exact hdr.dense_image continuous_subtype_val hsd
  have : Countable ↥𝒟 := h𝒟c.to_subtype
  have hpair : ∀ p : ↥𝒟 × ↥𝒟, AEMeasurable (fun v => D v p.1 p.2) (volume.restrict E) :=
    fun p => hspan _ (h𝒟S _ p.1.2) _ (h𝒟S _ p.2.2)
  choose h hhm hhe using hpair
  have hall : ∀ᵐ v ∂(volume.restrict E), ∀ p : ↥𝒟 × ↥𝒟, D v p.1 p.2 = h p v := ae_all_iff.2 hhe
  obtain ⟨B', hBB', hB'm, hB'0⟩ := exists_measurable_superset_of_null (ae_iff.1 hall)
  set G : Set ℝ := E \ B' with hG
  have hGm : MeasurableSet G := hE.diff hB'm
  have hGsub : G ⊆ E := fun v hv => hv.1
  have hGnull : volume (E \ G) = 0 := by
    have : E \ G = B' ∩ E := by
      ext v; simp only [hG, mem_diff, mem_inter_iff, not_and, not_not]; tauto
    rw [this]
    rw [Measure.restrict_apply hB'm] at hB'0
    exact hB'0
  refine ⟨G, hGm, hGsub, hGnull, fun u' v' => ?_⟩
  obtain ⟨x, hx𝒟, hxu⟩ := mem_closure_iff_seq_limit.1 (h𝒟d u')
  obtain ⟨y, hy𝒟, hyv⟩ := mem_closure_iff_seq_limit.1 (h𝒟d v')
  refine measurable_of_tendsto_metrizable (f := fun n v => if v ∈ G then D v (x n) (y n) else 0)
    (fun n => ?_) ?_
  · have : (fun v => if v ∈ G then D v (x n) (y n) else 0) =
        fun v => if v ∈ G then h (⟨x n, hx𝒟 n⟩, ⟨y n, hy𝒟 n⟩) v else 0 := by
      funext v
      by_cases hv : v ∈ G
      · have hvB : v ∉ B' := hv.2
        have : ∀ p : ↥𝒟 × ↥𝒟, D v p.1 p.2 = h p v := by
          by_contra hcon
          exact hvB (hBB' hcon)
        simp only [hv, if_true]
        exact this (⟨x n, hx𝒟 n⟩, ⟨y n, hy𝒟 n⟩)
      · simp [hv]
    rw [this]
    exact Measurable.ite hGm (hhm _) measurable_const
  · refine tendsto_pi_nhds.2 fun v => ?_
    by_cases hv : v ∈ G
    · simp only [hv, if_true]
      have hcont : Continuous fun p : KSpace d m T × KSpace d m T => D v p.1 p.2 :=
        (D v).continuous₂ |>.comp continuous_id
      exact (hcont.tendsto (u', v')).comp (hxu.prodMk_nhds hyv)
    · simp [hv]

/-- The shifted dyadic approximation: `τ = v - u` is approximated from the right by the grid `s101tn T n (v - u)`. -/
theorem k3_aem_diag {T : ℝ} (hT : 0 ≤ T) (u : ℝ) {E : Set ℝ} (hE : MeasurableSet E)
    (hEsub : E ⊆ Icc u (u + T))
    (Dm : ℝ → K3Bil d m T) (a b a' b' : ℝ → KSpace d m T)
    (H1 : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable (fun v => Dm v (a t) (b t)) (volume.restrict (E ∩ Iio (u + t))))
    (H2 : ∀ v ∈ E, v - u < T → Tendsto (fun n => a (s101tn T n (v - u))) atTop (𝓝 (a' v)) ∧
      Tendsto (fun n => b (s101tn T n (v - u))) atTop (𝓝 (b' v))) :
    AEMeasurable (fun v => Dm v (a' v) (b' v)) (volume.restrict E) := by
  classical
  set F : ℕ → ℕ → ℝ → ℝ := fun n k v =>
    if v < u + s101tk T n k then Dm v (a (s101tk T n k)) (b (s101tk T n k)) else 0 with hF
  have hFm : ∀ n k, AEMeasurable (F n k) (volume.restrict E) := by
    intro n k
    have h1 := H1 (s101tk T n k) (s101tk_mem hT n k)
    have h2 : AEMeasurable (fun v => Dm v (a (s101tk T n k)) (b (s101tk T n k)))
        ((volume.restrict E).restrict (Iio (u + s101tk T n k))) := by
      rw [Measure.restrict_restrict measurableSet_Iio, inter_comm]; exact h1
    have : F n k = (Iio (u + s101tk T n k)).indicator
        (fun v => Dm v (a (s101tk T n k)) (b (s101tk T n k))) := by
      funext v; simp [hF, Set.indicator, mem_Iio]
    rw [this]
    exact (aemeasurable_indicator_iff measurableSet_Iio).2 h2
  have hS : ∀ n, AEMeasurable (fun v => F n ⌊(v - u) * 2 ^ n⌋₊ v) (volume.restrict E) := by
    intro n
    refine s101_aem_index (fun v => ⌊(v - u) * 2 ^ n⌋₊) ?_ (F n) (hFm n)
    exact Nat.measurable_floor.comp ((measurable_id.sub_const u).mul_const _)
  have hTnull : ∀ᵐ v ∂(volume.restrict E), v - u < T := by
    have : volume ({u + T} : Set ℝ) = 0 := Real.volume_singleton
    have h2 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ u + T :=
      (measure_eq_zero_iff_ae_notMem.1 this).mono fun v h => by simpa using h
    filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hE] with v h1 h3
    have := (hEsub h3).2
    have h4 : v < u + T := lt_of_le_of_ne this h1
    linarith
  refine aemeasurable_of_tendsto_metrizable_ae atTop hS ?_
  filter_upwards [hTnull, ae_restrict_mem hE] with v hvT hvE
  have hv0 : 0 ≤ v - u := by linarith [(hEsub hvE).1]
  obtain ⟨ha, hb⟩ := H2 v hvE hvT
  have heq : ∀ n, F n ⌊(v - u) * 2 ^ n⌋₊ v = Dm v (a (s101tn T n (v - u))) (b (s101tn T n (v - u))) := by
    intro n
    have : v - u < s101tk T n ⌊(v - u) * 2 ^ n⌋₊ := s101tn_lt hv0 hvT n
    have h' : v < u + s101tk T n ⌊(v - u) * 2 ^ n⌋₊ := by linarith
    simp only [hF, h', if_true]
    rfl
  simp_rw [heq]
  have hcont : Continuous fun p : KSpace d m T × KSpace d m T => Dm v p.1 p.2 :=
    (Dm v).continuous₂ |>.comp continuous_id
  exact (hcont.tendsto (a' v, b' v)).comp (ha.prodMk_nhds hb)

end HRS.MS.S111K3
