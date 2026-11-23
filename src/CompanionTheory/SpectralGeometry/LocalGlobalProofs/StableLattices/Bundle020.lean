module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle002
public import Formalism.RealPlaceAnalysis.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.DSKType

open CompanionTheory.D.DSIC PI.UpqRep

theorem kset_subset_ujset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  have h3 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 h1)
  show inUJ ε g
  unfold inUJ
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem typeOfHW (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by
  intro n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw
  obtain ⟨S₀, hfd, hxS, hst⟩ := hfin
  have hinj : Function.Injective S.subtype := S.injective_subtype
  have := hfd
  have hU : FiniteDimensional ℂ (S₀.comap S.subtype) := by
    refine FiniteDimensional.of_injective
      (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : S₀ => (y : H)) hab
  have hUst : KStab ε E (S₀.comap S.subtype) := by
    refine (hS n ε H σ S E hσ hM _ hU).2 ?_
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := by
    intro a b hab y z
    have := hM.unit a b y z
    simpa [Formalism.REAL.sgn, hab] using this
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap S.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap S.subtype).map S.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap S.subtype) := by
      refine (hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)

end GlobalTheory.CompanionTheory.DSKType
end

section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmBracket

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c := by
  subst ha hb hc
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ F x :=
    hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [(hD.hasFDerivAt.clm_apply L.hasFDerivAt).fderiv, (hD.hasFDerivAt.clm_apply M.hasFDerivAt).fderiv]
  simp [hs (M x) (L x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem lie_bracket {J X Y : Mat n} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0 := by
  have hLX : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * J = J * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * J = J * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem hasDerivAt_ext (h : RepOn G σ) {X g : Mat n} (hX : ∀ t, ex X t ∈ G) (hg : g ∈ G) {f F : Mat n → H}
    {U : Set (Mat n)} (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ G → f x = F x) :
    HasDerivAt (fun t => f (g * ex X t)) (fderiv ℝ F g (g * X)) 0 :=
  hasDerivAt_local (A := G) (γ := fun t => g * ex X t) (fun t => h.mul_mem _ hg _ (hX t))
    (by simp [ex_zero]) (hasDerivAt_mul_ex g X) hU hgU hF hfF

theorem ds_ds (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G) {v : H}
    (hv : IsSm G σ v) {F : Mat n → H} {U : Set (Mat n)} (hU : IsOpen U) (h1 : (1 : Mat n) ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ x ∈ U, x ∈ G → σ x v = F x) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x, L x = x * Y) :
    ds σ X (ds σ Y v) = fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, g ∈ G → σ g (ds σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgG
    rw [apply_ds h hY hgG (hv.differentiableAt h hY), hL]
    exact (hasDerivAt_ext h (f := fun x => σ x v) hY hgG hU hg hF hfF).deriv
  have h2 := hasDerivAt_ext h (f := fun g => σ g (ds σ Y v)) hX h.one_mem hU h1 hG hGe
  simp only [Matrix.one_mul] at h2
  exact h2.deriv

theorem ds_bracket (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G)
    (hXY : ∀ t, ex (X * Y - Y * X) t ∈ G) {v : H} (hv : IsSm G σ v) :
    ds σ X (ds σ Y v) - ds σ Y (ds σ X v) = ds σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  have h2 := hasDerivAt_ext h (f := fun x => σ x v) hXY h.one_mem hU h1 hF hfF
  simp only [Matrix.one_mul] at h2
  have e : ds σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h2.deriv
  let L : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [ds_ds h hX hY hv hU h1 hF hfF L hL, ds_ds h hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))

theorem smBracket : CompanionTheory.D.DSIC.SmBracket := by
  intro n ε H _ _ σ hσ X Y hX hY v hv
  have h : RepOn (UJset ε) σ :=
    ⟨by simp [UJset, PI.UpqRep.inUJ], fun a ha b hb => Formalism.REAL.indefinite_unitary_mul_mem ε ha hb, hσ.1.1, hσ.1.2⟩
  have hex : ∀ Z, inG ε Z → ∀ t, ex Z t ∈ UJset ε := fun Z hZ t => Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t
  exact ds_bracket h (hex X hX) (hex Y hY) (hex _ (lie_bracket hX hY)) hv

theorem smBracket_of : CompanionTheory.D.DSIC.SmLin → CompanionTheory.D.DSIC.SmBracket := fun _ => smBracket

end GlobalTheory.CompanionTheory.SmBracket
end
end

section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ZetaHighest

open CompanionTheory.D.DSIC Formalism.REAL

variable {n : ℕ}

theorem blk_strictMono (ε : Fin n → Bool) (s : Bool) : StrictMono (blk ε s) :=
  ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).strictMono

theorem blk_mem (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) : ε (blk ε s i) = s := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i
  exact (Finset.mem_filter.1 h).2

theorem blk_surj (ε : Fin n → Bool) (s : Bool) (a : Fin n) (h : ε a = s) : ∃ i, blk ε s i = a := by
  have h1 : a ∈ Set.range ((univ.filter fun a => ε a = s).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    simpa using h
  exact h1

theorem prod_blk (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℂ) :
    ∏ i, f (blk ε s i) = ∏ a ∈ univ.filter (fun a => ε a = s), f a := by
  refine Finset.prod_bij (fun i _ => blk ε s i) ?_ ?_ ?_ ?_
  · intro i _; simp [blk_mem]
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    obtain ⟨i, hi⟩ := blk_surj ε s a (Finset.mem_filter.1 ha).2
    exact ⟨i, mem_univ _, hi⟩
  · intro i _; rfl

theorem card_below (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) :
    (univ.filter fun b => b < blk ε s i ∧ ε b = ε (blk ε s i)).card = i := by
  rw [← Fin.card_Iio i]
  symm
  refine Finset.card_bij (fun j _ => blk ε s j) ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_univ, true_and, blk_mem, and_true]
    exact blk_strictMono ε s (Finset.mem_Iio.1 hj)
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    have ha' := (Finset.mem_filter.1 ha).2
    obtain ⟨j, hj⟩ := blk_surj ε s a (ha'.2.trans (blk_mem ε s i))
    refine ⟨j, Finset.mem_Iio.2 ?_, hj⟩
    rw [← (blk_strictMono ε s).lt_iff_lt, hj]
    exact ha'.1

theorem card_total (ε : Fin n → Bool) (c : Fin n) :
    ((univ.filter fun b => c < b ∧ ε b = ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b = ε c).card : ℝ) +
      ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) + 1
      = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = c then 1 else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  rw [h2]
  conv_lhs => rw [h1]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · by_cases e : ε b = ε c <;> simp [h, h.ne, not_lt.2 h.le, e]
  · simp [h]
  · by_cases e : ε b = ε c <;> simp [h, h.ne', not_lt.2 h.le, e]

theorem card_other (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ)
      = nb ε false := by
  unfold nb
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]
  · simp [h, hc]
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]

theorem wt_false (ε : Fin n → Bool) (c : Fin n) (hc : ε c = false) :
    wtA (A1 ε) c = -((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.1 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.1
    rw [h, hc] at this
    exact Bool.false_ne_true this
  have h2 : ((A1 ε).filter fun i => i.1.2 = c).card = (univ.filter fun b => c < b ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.1, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext h (hi.2.trans hj.2.symm))
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(a, c), ?_, hc⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp

theorem wt_true (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    wtA (A1 ε) c = ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.2 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.2
    rw [h, hc] at this
    exact Bool.false_ne_true this.symm
  have h2 : ((A1 ε).filter fun i => i.1.1 = c).card = (univ.filter fun b => b < c ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.2, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext (hi.2.trans hj.2.symm) h)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(c, a), hc, ?_⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp

theorem gam_false (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε false)) :
    gam ε lam (blk ε false i) = lam (blk ε false i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  have h1 := card_total ε (blk ε false i)
  have h2 := wt_false ε _ (blk_mem ε false i)
  have h3 := card_below ε false i
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith

theorem gam_true (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε true)) :
    gam ε lam (blk ε true i) = lam (blk ε true i) - ((n : ℝ) - 1) / 2 + (nb ε false : ℝ) + (i : ℕ) := by
  have h1 := card_total ε (blk ε true i)
  have h2 := wt_true ε _ (blk_mem ε true i)
  have h3 := card_below ε true i
  have h4 := card_other ε _ (blk_mem ε true i)
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith

theorem block_eigen (ε : Fin n → Bool) (s : Bool) (μ : Fin n → ℝ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) (hF : _root_.CompanionTheory.D.DSIC.KRel ε F)
    (hx : KHighest ε F μ x) (u : ℂ) :
    qminor F (blk ε s) (blk ε s) u x = (∏ i : Fin (nb ε s), (u - (i : ℂ) + (μ (blk ε s i) : ℂ))) • x := by
  have inj : ∀ i j, blk ε s i = blk ε s j ↔ i = j := fun i j => (blk_strictMono ε s).injective.eq_iff
  have hgl : GlRel (fun i j => F (blk ε s i) (blk ε s j)) := by
    intro a b c d
    have := hF (blk ε s a) (blk ε s b) (blk ε s c) (blk ε s d) (by simp [blk_mem]) (by simp [blk_mem])
    simpa only [inj] using this
  have hw : IsHW (fun i j => F (blk ε s i) (blk ε s j)) (fun i => (μ (blk ε s i) : ℂ)) x :=
    ⟨fun a => hx.1 _, fun a b h => hx.2 _ _ (blk_strictMono ε s h) (by simp [blk_mem])⟩
  have hq : qminor F (blk ε s) (blk ε s) u = qdet (fun i j => F (blk ε s i) (blk ε s j)) u := by
    simp only [qdet, qminor, Tm, inj, id]
  rw [hq]
  exact qDetHW V _ _ _ x hgl hw u

theorem zetaHW : CompanionTheory.D.DSIC.ZetaHW := by
  intro n ε lam V _ _ F x hF hx Y
  unfold zeta
  rw [Module.End.mul_apply, block_eigen ε true _ V F x hF hx, map_smul, block_eigen ε false _ V F x hF hx,
    smul_smul]
  congr 1
  have e1 : ∀ i : Fin (nb ε true), (Y + ((n : ℂ) - 1) / 2 - (nb ε false : ℂ) - (i : ℂ) +
      (gam ε lam (blk ε true i) : ℂ)) = Y + lam (blk ε true i) := by
    intro i; rw [gam_true]; push_cast; ring
  have e2 : ∀ i : Fin (nb ε false), (Y + ((n : ℂ) - 1) / 2 - (i : ℂ) +
      (gam ε lam (blk ε false i) : ℂ)) = Y + lam (blk ε false i) := by
    intro i; rw [gam_false]; push_cast; ring
  simp only [e1, e2]
  rw [prod_blk ε true fun a => Y + (lam a : ℂ), prod_blk ε false fun a => Y + (lam a : ℂ), Formalism.QuantumDeterminants.capP,
    ← Finset.prod_filter_mul_prod_filter_not univ (fun a => ε a = true)]
  simp only [Bool.not_eq_true]

end GlobalTheory.CompanionTheory.ZetaHighest
end
end
