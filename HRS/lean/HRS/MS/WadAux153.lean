import HRS.MS.WadAux152

/-!
# S8.3, packet S8G-4: weighted decay of pair jets, closure properties

`S8gPD M n F`: `F : ℝ^d × ℝ^d → ℝ` is `C^n` and `⟨x⟩^{-M}⟨y⟩^{-M}‖D^kF(x,y)‖ → 0` at infinity for `k ≤ n` (the decay half of `MemCMpair`).
It is closed under sums (`s8g_pd_add`, `s8g_pd_sum`), contains separated products of one-body functions with weighted decaying jets
(`s8g_pd_mul`), and is closed under approximation of the jets in the weighted sup norm (`s8g_pd_of_approx`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def S8gPD (M : ℝ) (n : ℕ) (F : Euc d × Euc d → ℝ) : Prop :=
  ContDiff ℝ (n : WithTop ℕ∞) F ∧ ∀ k ≤ n, Tendsto (fun z : Euc d × Euc d =>
    jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ k F z‖) (cocompact (Euc d × Euc d)) (𝓝 0)

def S8gDec (M : ℝ) (n : ℕ) (u : Euc d → ℝ) : Prop :=
  ContDiff ℝ (n : WithTop ℕ∞) u ∧ ∀ i ≤ n,
    Tendsto (fun x : Euc d => jbracket x ^ (-M) * ‖iteratedFDeriv ℝ i u x‖) (cocompact (Euc d)) (𝓝 0)

theorem s8g_bdd {f : Euc d → ℝ} (hc : Continuous f) (ht : Tendsto f (cocompact (Euc d)) (𝓝 0)) :
    ∃ B : ℝ, ∀ x, |f x| ≤ B :=
  ⟨‖s8g_mk f hc ht‖, fun x => s8g_norm_apply_le (s8g_mk f hc ht) x⟩

theorem s8g_dec_of_memCMj {M : ℝ} {n : ℕ} {u : Euc d → ℝ} (hu : MemCMj M n u) : S8gDec M n u := by
  obtain ⟨hcd, hcm⟩ := (s83_memCMj_iff M n u).1 hu
  refine ⟨hcd, fun i hi => ?_⟩
  have := (hcm i hi).2
  refine this.congr fun x => ?_
  rw [Real.rpow_neg (s83_jb_pos x).le, div_eq_inv_mul]

theorem s8g_dec_add_const {M : ℝ} (hM : 0 < M) {n : ℕ} {u : Euc d → ℝ} (hu : S8gDec M n u) (c : ℝ) :
    S8gDec M n (fun x => u x + c) := by
  refine ⟨hu.1.add contDiff_const, fun i hi => ?_⟩
  have hc : ContDiff ℝ (i : WithTop ℕ∞) u := hu.1.of_le (by exact_mod_cast hi)
  have e : ∀ x, ‖iteratedFDeriv ℝ i (fun x => u x + c) x‖ ≤
      ‖iteratedFDeriv ℝ i u x‖ + (if i = 0 then |c| else 0) := by
    intro x
    have e1 : (fun x => u x + c) = u + (fun _ => c) := rfl
    rw [e1, iteratedFDeriv_add_apply hc.contDiffAt contDiffAt_const]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hi0)]; simp [Nat.pos_iff_ne_zero.1 hi0]
  have hz : Tendsto (fun x : Euc d => jbracket x ^ (-M) * (if i = 0 then |c| else 0)) (cocompact (Euc d)) (𝓝 0) := by
    have h1 : Tendsto (fun x : Euc d => jbracket x ^ (-M)) (cocompact (Euc d)) (𝓝 0) :=
      (tendsto_rpow_neg_atTop hM).comp s85_tendsto_jb
    simpa using h1.mul_const (if i = 0 then |c| else 0)
  have hs := (hu.2 i hi).add hz
  rw [add_zero] at hs
  refine squeeze_zero (fun x => mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (norm_nonneg _)) (fun x => ?_) hs
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (e x) (Real.rpow_nonneg (s83_jb_pos x).le _)

theorem s8g_pd_of_approx {M : ℝ} {n : ℕ} {F : Euc d × Euc d → ℝ} (hF : ContDiff ℝ (n : WithTop ℕ∞) F)
    (h : ∀ ε > 0, ∃ F' : Euc d × Euc d → ℝ, S8gPD M n F' ∧ ∀ k ≤ n, ∀ z : Euc d × Euc d,
      ‖iteratedFDeriv ℝ k F z - iteratedFDeriv ℝ k F' z‖ ≤ ε * (jbracket z.1 ^ M * jbracket z.2 ^ M)) :
    S8gPD M n F := by
  refine ⟨hF, fun k hk => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F', hF', hd⟩ := h (ε / 3) (by positivity)
  have h1 := Metric.tendsto_nhds.1 (hF'.2 k hk) (ε / 3) (by positivity)
  filter_upwards [h1] with z hz
  have hx := Real.rpow_pos_of_pos (s83_jb_pos z.1) M
  have hy := Real.rpow_pos_of_pos (s83_jb_pos z.2) M
  have hx' : jbracket z.1 ^ (-M) * jbracket z.1 ^ M = 1 := by
    rw [← Real.rpow_add (s83_jb_pos z.1)]; simp
  have hy' : jbracket z.2 ^ (-M) * jbracket z.2 ^ M = 1 := by
    rw [← Real.rpow_add (s83_jb_pos z.2)]; simp
  have hw : 0 ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) :=
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _) (Real.rpow_nonneg (s83_jb_pos z.2).le _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hw (norm_nonneg _))]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hw (norm_nonneg _))] at hz
  have hle : ‖iteratedFDeriv ℝ k F z‖ ≤ ‖iteratedFDeriv ℝ k F' z‖ + ε / 3 * (jbracket z.1 ^ M * jbracket z.2 ^ M) := by
    have := norm_sub_norm_le (iteratedFDeriv ℝ k F z) (iteratedFDeriv ℝ k F' z)
    linarith [hd k hk z]
  calc jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ k F z‖
      ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
        (‖iteratedFDeriv ℝ k F' z‖ + ε / 3 * (jbracket z.1 ^ M * jbracket z.2 ^ M)) :=
        mul_le_mul_of_nonneg_left hle hw
    _ = jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ k F' z‖ + ε / 3 *
        ((jbracket z.1 ^ (-M) * jbracket z.1 ^ M) * (jbracket z.2 ^ (-M) * jbracket z.2 ^ M)) := by ring
    _ = jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ k F' z‖ + ε / 3 := by
        rw [hx', hy']; ring
    _ < ε / 3 + ε / 3 := by linarith
    _ < ε := by linarith

theorem s8g_pd_add {M : ℝ} {n : ℕ} {F G : Euc d × Euc d → ℝ} (hF : S8gPD M n F) (hG : S8gPD M n G) :
    S8gPD M n (fun z => F z + G z) := by
  refine ⟨hF.1.add hG.1, fun k hk => ?_⟩
  have hs := (hF.2 k hk).add (hG.2 k hk)
  rw [add_zero] at hs
  refine squeeze_zero (fun z => mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _)
    (Real.rpow_nonneg (s83_jb_pos z.2).le _)) (norm_nonneg _)) (fun z => ?_) hs
  have e : (fun z => F z + G z) = F + G := rfl
  have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  rw [e, iteratedFDeriv_add_apply (hF.1.of_le hk').contDiffAt (hG.1.of_le hk').contDiffAt]
  have hw : 0 ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) :=
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _) (Real.rpow_nonneg (s83_jb_pos z.2).le _)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hw

theorem s8g_pd_zero (M : ℝ) (n : ℕ) : S8gPD M n (fun _ : Euc d × Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun k hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using tendsto_const_nhds
  · simp only [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hk0), Pi.zero_apply, norm_zero, mul_zero]
    exact tendsto_const_nhds

theorem s8g_pd_sum {M : ℝ} {n : ℕ} {ι : Type} (t : Finset ι) {F : ι → Euc d × Euc d → ℝ}
    (hF : ∀ p ∈ t, S8gPD M n (F p)) : S8gPD M n (fun z => ∑ p ∈ t, F p z) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using s8g_pd_zero M n
  | insert a t ha ih =>
    have := s8g_pd_add (hF a (Finset.mem_insert_self a t)) (ih fun p hp => hF p (Finset.mem_insert_of_mem hp))
    simpa [Finset.sum_insert ha] using this

theorem s8g_pd_mul {M : ℝ} {n : ℕ} {u v : Euc d → ℝ} (hu : S8gDec M n u) (hv : S8gDec M n v) :
    S8gPD M n (fun z : Euc d × Euc d => u z.1 * v z.2) := by
  have hu1 : ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => u z.1) := hu.1.comp contDiff_fst
  have hv1 : ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d × Euc d => v z.2) := hv.1.comp contDiff_snd
  refine ⟨hu1.mul hv1, fun k hk => ?_⟩
  have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  -- termwise decay
  have hterm : ∀ i ∈ Finset.range (k + 1), Tendsto (fun z : Euc d × Euc d =>
      (k.choose i : ℝ) * ((jbracket z.1 ^ (-M) * ‖iteratedFDeriv ℝ i u z.1‖) *
        (jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖))) (cocompact (Euc d × Euc d)) (𝓝 0) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have ha := hu.2 i (hik.trans hk)
    have hb := hv.2 (k - i) ((Nat.sub_le _ _).trans hk)
    have hac : Continuous fun x : Euc d => jbracket x ^ (-M) * ‖iteratedFDeriv ℝ i u x‖ :=
      (s85_jb_rpow_continuous (-M)).mul
        ((hu.1.continuous_iteratedFDeriv (by exact_mod_cast hik.trans hk)).norm)
    have hbc : Continuous fun x : Euc d => jbracket x ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v x‖ :=
      (s85_jb_rpow_continuous (-M)).mul
        ((hv.1.continuous_iteratedFDeriv (by exact_mod_cast (Nat.sub_le _ _).trans hk)).norm)
    obtain ⟨Ba, hBa⟩ := s8g_bdd hac ha
    obtain ⟨Bb, hBb⟩ := s8g_bdd hbc hb
    have h0 : Tendsto (fun z : Euc d × Euc d => (jbracket z.1 ^ (-M) * ‖iteratedFDeriv ℝ i u z.1‖) *
        (jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖)) (cocompact (Euc d × Euc d)) (𝓝 0) := by
      rw [← Filter.coprod_cocompact, Filter.coprod, tendsto_sup]
      constructor
      · have h1 : Tendsto (fun z : Euc d × Euc d => jbracket z.1 ^ (-M) * ‖iteratedFDeriv ℝ i u z.1‖)
            (comap Prod.fst (cocompact (Euc d))) (𝓝 0) := ha.comp tendsto_comap
        refine squeeze_zero (fun z => mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)
          (norm_nonneg _)) (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (norm_nonneg _)))
          (fun z => ?_) (by simpa using h1.mul_const Bb)
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le (-M))
          (norm_nonneg (iteratedFDeriv ℝ i u z.1)))
        have := hBb z.2
        rwa [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.2).le (-M))
          (norm_nonneg (iteratedFDeriv ℝ (k - i) v z.2)))] at this
      · have h1 : Tendsto (fun z : Euc d × Euc d => jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖)
            (comap Prod.snd (cocompact (Euc d))) (𝓝 0) := hb.comp tendsto_comap
        refine squeeze_zero (fun z => mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)
          (norm_nonneg _)) (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (norm_nonneg _)))
          (fun z => ?_) (by simpa using h1.const_mul Ba)
        have hbn : 0 ≤ jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖ :=
          mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.2).le (-M)) (norm_nonneg _)
        have hA := hBa z.1
        rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le (-M))
          (norm_nonneg (iteratedFDeriv ℝ i u z.1)))] at hA
        calc _ = (jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖) *
              (jbracket z.1 ^ (-M) * ‖iteratedFDeriv ℝ i u z.1‖) := mul_comm _ _
          _ ≤ (jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖) * Ba :=
            mul_le_mul_of_nonneg_left hA hbn
          _ = _ := mul_comm _ _
    simpa using h0.const_mul (k.choose i : ℝ)
  have hsum := tendsto_finsetSum _ hterm
  rw [Finset.sum_const_zero] at hsum
  refine squeeze_zero (fun z => mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _)
    (Real.rpow_nonneg (s83_jb_pos z.2).le _)) (norm_nonneg _)) (fun z => ?_) hsum
  have hmul := norm_iteratedFDeriv_mul_le hu1 hv1 z hk'
  have hw : 0 ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) :=
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _) (Real.rpow_nonneg (s83_jb_pos z.2).le _)
  calc jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ k (fun z : Euc d × Euc d => u z.1 * v z.2) z‖
      ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : Euc d × Euc d => u z.1) z‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun z : Euc d × Euc d => v z.2) z‖ := mul_le_mul_of_nonneg_left hmul hw
    _ = ∑ i ∈ Finset.range (k + 1), jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ((k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : Euc d × Euc d => u z.1) z‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun z : Euc d × Euc d => v z.2) z‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ((jbracket z.1 ^ (-M) * ‖iteratedFDeriv ℝ i u z.1‖) *
        (jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ (k - i) v z.2‖)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := s8g_iter_fst hu.1 (hik.trans hk) z
        have h2 := s8g_iter_snd hv.1 ((Nat.sub_le k i).trans hk) z
        have hc0 : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
        calc jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ((k.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun z : Euc d × Euc d => u z.1) z‖ *
              ‖iteratedFDeriv ℝ (k - i) (fun z : Euc d × Euc d => v z.2) z‖)
            ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ((k.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i u z.1‖ * ‖iteratedFDeriv ℝ (k - i) v z.2‖) := by
              refine mul_le_mul_of_nonneg_left ?_ hw
              exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _)
                (mul_nonneg hc0 (norm_nonneg _))
          _ = _ := by ring

end HRS.MS.Wad
