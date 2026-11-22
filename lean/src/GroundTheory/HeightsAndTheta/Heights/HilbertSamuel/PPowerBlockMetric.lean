import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.ExistsFormOfMemChartRingZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockMetric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

alias homog_congr := SectionNormSqExtension.homog_congr
alias homog_zero := SectionNormSqExtension.homog_zero
alias homog_add := SectionNormSqExtension.homog_add
alias homog_neg := SectionNormSqExtension.homog_neg
alias homog_sub := SectionNormSqExtension.homog_sub
alias homog_sum := SectionNormSqExtension.homog_sum
alias homog_one := SectionNormSqExtension.homog_one
alias homog_C := SectionNormSqExtension.homog_C
alias homog_mul := SectionNormSqExtension.homog_mul
alias homog_X := SectionNormSqExtension.homog_X
alias homog_pow := SectionNormSqExtension.homog_pow

def chartMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem homog_chartMon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMon c d) d :=
  SectionNormSqExtension.homog_chartMon c d

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k :=
  SectionNormSqExtension.aeval_chartMon y c d

theorem eval_chartMon (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k :=
  SectionNormSqExtension.eval_chartMon z c d

alias mConeMap_homog := SectionNormSqExtension.mConeMap_homog
alias vanish := SectionNormSqExtension.vanish
alias exists_form_of_mem_chartRingZ := SectionNormSqExtension.exists_form_of_mem_chartRingZ
alias exists_chartForm := SectionNormSqExtension.exists_chartForm

theorem zpow_combine {F : Type*} [Field F] {x : F} (hx : x ≠ 0) {du dw N D : ℕ} {a : ℤ}
    (hw : (dw : ℤ) = a + N) (hle : du + dw ≤ D) :
    x ^ du * x ^ N * x ^ (D - (du + dw)) = x ^ (-a) * x ^ D := by
  simp only [← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  rw [Nat.cast_sub hle]
  push_cast
  omega

alias y_ne_zero := SectionNormSqExtension.y_ne_zero

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + n * a k) ∧
    aeval y g = s * aeval y h

theorem cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} {g h g' h' : MRing ι}
    (hr : IsRep y a n s g h) (hr' : IsRep y a n s g' h') {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) :=
  SectionNormSqExtension.cross hr hr' hz

theorem exists_rep_at {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ gh : MRing ι × MRing ι, IsRep y a n s gh.1 gh.2 ∧ eval z (map (Int.castRingHom ℂ) gh.2) ≠ 0 :=
  SectionNormSqExtension.exists_rep_at hs hz

alias metric_ne := SectionNormSqExtension.metric_ne

def val (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ := by
  classical
  exact if hsz : s ∈ chartLat y A.a n ∧ z ∈ mcPts (mCoordIdeal y) then
    eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.1) /
      (eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.2) * (A.h z : ℂ) ^ n)
  else 0

theorem val_spec {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h) :
    eval z (map (Int.castRingHom ℂ) g) =
      val y A n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n :=
  SectionNormSqExtension.val_spec hs hz hr

theorem secNormAt_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : secNormAt y A n s z = ‖val y A n s z‖ :=
  SectionNormSqExtension.secNormAt_eq hs hz

theorem exists_val_ne {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hv : ∀ j, v j ∈ chartLat y A.a m) (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) : ∃ j, val y A m (v j) x ≠ 0 := by
  classical
  choose c hc using hx.1
  obtain ⟨d, e, G, he, hG, hGy⟩ := SectionNormSqExtension.exists_chartData y A m N v hv c
  obtain ⟨j, hj⟩ := SectionNormSqExtension.exists_G_ne hgen (fun k => y_ne_zero hx (hc k))
    he hG hGy hx hc
  refine ⟨j, fun hzero => hj ?_⟩
  rw [val_spec (hv j) hx ⟨e, d, hG j, homog_chartMon c d, he, hGy j⟩, hzero, zero_mul, zero_mul]

def oldIdx (N : ℕ) (p : Σ k, ι k) : Σ k, addIdx ι N k := ⟨some p.1, p.2⟩

theorem oldIdx_injective (N : ℕ) : Function.Injective (oldIdx (ι := ι) N) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
  subst h1
  have h2 := (Sigma.mk.inj_iff.mp h).2
  have h3 : i = i' := eq_of_heq h2
  rw [h3]

theorem mConeMap_rename (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (f : MRing ι) :
    mConeMap (addBlock y v) (rename (oldIdx N) f) = rename (R := Ω) some (mConeMap y f) := by
  have key : (mConeMap (addBlock y v)).comp (rename (oldIdx N)) =
      ((rename (R := Ω) (some : K → Option K)).restrictScalars ℤ).comp (mConeMap y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, oldIdx, addBlock]
  exact DFunLike.congr_fun key f

theorem mConeMap_new (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (j : Fin N) :
    mConeMap (addBlock y v) (X ⟨none, j⟩ : MRing (addIdx ι N)) = MvPolynomial.C (v j) * MvPolynomial.X none := by
  simp [mConeMap, addBlock]

theorem rename_mem {y : (Σ k, ι k) → Ω} {N : ℕ} (v : Fin N → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    rename (oldIdx N) f ∈ mCoordIdeal (addBlock y v) := by
  have hf' : f ∈ RingHom.ker (mConeMap y) := hf
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  rw [RingHom.mem_ker, mConeMap_rename, RingHom.mem_ker.mp hf', map_zero]

theorem eval_rename_old {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (oldIdx N) f)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]
  rfl

theorem oldPart_mem {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {z : (Σ k, addIdx ι N k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun f hf => ?_⟩
  rw [← eval_rename_old]
  exact hz.2 _ (rename_mem v hf)

theorem new_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n N : ℕ} {v : Fin N → Ω} {j j' : Fin N}
    {g h g' h' : MRing ι} (hr : IsRep y a n (v j) g h) (hr' : IsRep y a n (v j') g' h')
    {z : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) :
    z ⟨none, j⟩ * (eval (basePart₂ z) (map (Int.castRingHom ℂ) g') *
        eval (basePart₂ z) (map (Int.castRingHom ℂ) h)) =
      z ⟨none, j'⟩ * (eval (basePart₂ z) (map (Int.castRingHom ℂ) g) *
        eval (basePart₂ z) (map (Int.castRingHom ℂ) h')) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := hr'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    simp only [Pi.add_apply]
    zify
    linear_combination hd' k - hd k
  have e1 := mConeMap_homog y (homog_mul hg' hh)
  have e2 := mConeMap_homog y (homog_mul hg hh')
  rw [hdeg] at e1
  have a1 : aeval y (g' * h) = v j' * aeval y h' * aeval y h := by rw [map_mul, hy']
  have a2 : aeval y (g * h') = v j * aeval y h * aeval y h' := by rw [map_mul, hy]
  have hmem : (X ⟨none, j⟩ * rename (oldIdx N) (g' * h) - X ⟨none, j'⟩ * rename (oldIdx N) (g * h') :
      MRing (addIdx ι N)) ∈ mCoordIdeal (addBlock y v) := by
    show _ ∈ RingHom.ker (mConeMap (addBlock y v))
    rw [RingHom.mem_ker, map_sub, map_mul (mConeMap (addBlock y v)), map_mul (mConeMap (addBlock y v)),
      mConeMap_rename, mConeMap_rename, e1, e2, a1, a2, mConeMap_new, mConeMap_new]
    simp only [map_mul, rename_C]
    ring
  have := hz.2 _ hmem
  simp only [map_sub, map_mul, map_X, eval_X, eval_rename_old, sub_eq_zero] at this
  simpa only [map_mul, eval_mul] using this

theorem graph_prop {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hv : ∀ j, v j ∈ chartLat y A.a m) (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    {z : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) :
    ∃ c : ℂ, ∀ j, z ⟨none, j⟩ = c * val y A m (v j) (basePart₂ z) := by
  have hx := oldPart_mem hz
  obtain ⟨j₀, hj₀⟩ := exists_val_ne hv hgen hx
  choose gh hgh hne using fun j => exists_rep_at (hv j) hx
  refine ⟨z ⟨none, j₀⟩ / val y A m (v j₀) (basePart₂ z), fun j => ?_⟩
  have e := new_cross (hgh j) (hgh j₀) hz
  rw [val_spec (hv j) hx (hgh j), val_spec (hv j₀) hx (hgh j₀)] at e
  have hH := metric_ne (A := A) hx m
  rw [div_mul_eq_mul_div, eq_div_iff hj₀]
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (hne j) (hne j₀)) hH)
  linear_combination e

theorem tangent_old {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {P0 : Ideal (MRing ι)}
    (hP0 : P0 ≤ mCoordIdeal y) {z w : (Σ k, addIdx ι N k) → ℂ}
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w) :
    IsConeTangent (Int.castRingHom ℂ) P0 (basePart₂ z) (basePart₂ w) := by
  classical
  intro f hf
  refine Eq.trans ?_ (hw _ (rename_mem v (hP0 hf)))
  refine Fintype.sum_of_injective (oldIdx N) (oldIdx_injective N) _ _ (fun p hp => ?_) (fun p => ?_)
  · have h0 : pderiv p (map (Int.castRingHom ℂ) (rename (oldIdx N) f)) = 0 := by
      rw [map_rename]
      apply pderiv_eq_zero_of_notMem_vars
      intro hmem
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hmem)
      exact hp ⟨q, rfl⟩
    rw [h0, map_zero, zero_mul]
  · rw [map_rename, pderiv_rename (oldIdx_injective N), eval_rename]
    rfl

theorem leviForm_congr {E : Type} [Fintype E] {φ ψ : (E → ℂ) → ℝ} {z : E → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : E → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact hy.fderiv_eq
  unfold leviForm
  rw [h1.fderiv_eq]

theorem isOpen_blocks {K : Type} [Fintype K] {ι : K → Type} :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def addedBlockNormSq {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) : ℝ := ∑ j : Fin N, ‖z ⟨none, j⟩‖ ^ 2

theorem newSq_pos {N : ℕ} {z : (Σ k, addIdx ι N k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < addedBlockNormSq z := by
  obtain ⟨j, hj⟩ := hz none
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hj) 2)
    (Finset.single_le_sum (f := fun j : Fin N => ‖z ⟨none, j⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j))

theorem contDiff_newSq {N : ℕ} {n : WithTop ℕ∞} : ContDiff ℝ n (addedBlockNormSq (ι := ι) (N := N)) := by
  unfold addedBlockNormSq
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨none, j⟩ : Σ k, addIdx ι N k))

theorem contDiff_oldPart {N : ℕ} {n : WithTop ℕ∞} : ContDiff ℝ n (basePart₂ (ι := ι) (N := N)) :=
  contDiff_pi.mpr fun p => contDiff_apply ℝ ℂ (⟨some p.1, p.2⟩ : Σ k, addIdx ι N k)

variable [DecidableEq K]

def graphLine (S : ((Σ k, ι k) → ℂ) → ℝ)
    (hSp : ∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x)
    (hSt : ∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) (N : ℕ) :
    HermLine (addIdx ι N) where
  a := unitDeg (none : Option K)
  h z := Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z))
  pos z hz := div_pos (Real.sqrt_pos.mpr (newSq_pos hz)) (Real.sqrt_pos.mpr (hSp _ fun k => hz (some k)))
  smul c z hc := by
    have h1 : addedBlockNormSq (fun p => c p.1 * z p) = ‖c none‖ ^ 2 * addedBlockNormSq z := by
      simp only [addedBlockNormSq, norm_mul, mul_pow, Finset.mul_sum]
    have h2 : S (basePart₂ (fun p => c p.1 * z p)) = S (basePart₂ z) :=
      hSt (fun k => c (some k)) (basePart₂ z) fun k => hc (some k)
    have h3 : (∏ k, ‖c k‖ ^ (unitDeg (none : Option K)) k) = ‖c none‖ := by
      rw [Fintype.prod_option]
      simp [unitDeg]
    rw [h1, h2, h3, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_div_assoc]

theorem isSmoothHerm_graphLine {S : ((Σ k, ι k) → ℂ) → ℝ}
    (hSp : ∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x)
    (hSt : ∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) {N : ℕ}
    (hSs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (graphLine S hSp hSt N) := by
  intro z hz
  have hx : basePart₂ z ∈ {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} := fun k => hz (some k)
  have hS : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => S (basePart₂ z)) z :=
    (hSs.contDiffAt (isOpen_blocks.mem_nhds hx)).comp z contDiff_oldPart.contDiffAt
  show ContDiffWithinAt ℝ _ (fun z => Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z))) _ z
  exact ((contDiff_newSq.contDiffAt.sqrt (newSq_pos hz).ne').div (hS.sqrt (hSp _ hx).ne')
    (Real.sqrt_pos.mpr (hSp _ hx)).ne').contDiffWithinAt

theorem conj_graphLine {S : ((Σ k, ι k) → ℂ) → ℝ}
    (hSp : ∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x)
    (hSt : ∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) {N : ℕ}
    (hSc : ∀ x : (Σ k, ι k) → ℂ, S (fun p => (starRingEnd ℂ) (x p)) = S x) :
    IsConjInvariantH (graphLine S hSp hSt N) := by
  intro z
  show Real.sqrt (addedBlockNormSq _) / Real.sqrt (S (basePart₂ _)) = Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z))
  have h1 : addedBlockNormSq (fun p => (starRingEnd ℂ) (z p)) = addedBlockNormSq z := by simp [addedBlockNormSq]
  have h2 : S (basePart₂ (fun p => (starRingEnd ℂ) (z p))) = S (basePart₂ z) := hSc (basePart₂ z)
  rw [h1, h2]

end PowerBlockMetric

open PowerBlockMetric in

theorem PowerBlockMetric.proof (hExt : SectionNormSqExtension.Statement) : PowerBlockMetric.Statement := by
  intro K _ _ ι _ Ω _ y A P0 m N v hP0 hsemi hconj hv hgen
  obtain ⟨S, hSs, hSp, hSt, hSc, hSv, hSl⟩ := hExt K ι Ω y A m N v hsemi.1 hconj hv hgen
  refine ⟨graphLine S hSp hSt N, mCoordIdeal (addBlock y v), rfl, conj_graphLine hSp hSt hSc, le_rfl,
    ⟨isSmoothHerm_graphLine hSp hSt hSs, fun z hz w hw => ?_⟩, fun z hz j => ?_⟩
  · have hU : ∀ᶠ z' in 𝓝 z, z' ∈ {z' : (Σ k, addIdx ι N k) → ℂ | ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0} :=
      isOpen_blocks.mem_nhds hz.1
    have heq : (fun z' => Real.log ((graphLine S hSp hSt N).h z')) =ᶠ[𝓝 z]
        (fun z' : (Σ k, addIdx ι N k) → ℂ =>
          Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) := by
      filter_upwards [hU] with z' hz'
      have h1 := newSq_pos hz'
      have h2 := hSp (basePart₂ z') (fun k => hz' (some k))
      show Real.log (Real.sqrt (addedBlockNormSq z') / Real.sqrt (S (basePart₂ z'))) = _
      rw [Real.log_div (Real.sqrt_pos.mpr h1).ne' (Real.sqrt_pos.mpr h2).ne', Real.log_sqrt h1.le,
        Real.log_sqrt h2.le]
      rfl
    rw [leviForm_congr heq, hSl z hz w hw]
    exact mul_nonneg (Nat.cast_nonneg m)
      (hsemi.2 (basePart₂ z) (oldPart_mem hz) (basePart₂ w) (tangent_old hP0 hw))
  · obtain ⟨c, hc⟩ := graph_prop hv hgen hz
    have hx := oldPart_mem hz
    have hsn : ∀ j, secNormAt y A m (v j) (basePart₂ z) = ‖val y A m (v j) (basePart₂ z)‖ :=
      fun j => secNormAt_eq (hv j) hx
    have hT : S (basePart₂ z) = ∑ j, secNormAt y A m (v j) (basePart₂ z) ^ 2 := hSv _ hx
    have hTpos : 0 < S (basePart₂ z) := hSp _ hx.1
    have hN : addedBlockNormSq z = ‖c‖ ^ 2 * S (basePart₂ z) := by
      rw [hT, Finset.mul_sum, addedBlockNormSq]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcj : z ⟨none, j⟩ = c * val y A m (v j) (basePart₂ z) := hc j
      rw [hcj, norm_mul, mul_pow, hsn]
    have hB : (graphLine S hSp hSt N).h z = ‖c‖ := by
      show Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z)) = ‖c‖
      rw [hN, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_div_assoc,
        div_self (Real.sqrt_pos.mpr hTpos).ne', mul_one]
    rw [hB, hc j, norm_mul, hsn j, mul_comm]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
