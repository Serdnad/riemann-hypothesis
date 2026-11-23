module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartLaw

theorem awayMap_notMem {R : Type} [CommRing R] (g : R) (w : Sp (Localization.Away g)) : g ∉ (awayMap g w).asIdeal := by
  intro h
  have : algebraMap R (Localization.Away g) g ∈ w.asIdeal := h
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit g))

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {t : T ⟶ S} {t' : T' ⟶ S} (k : T' ⟶ T)
    (a b : Over.mk t ⟶ H) (a₁ b₁ : Over.mk t' ⟶ H) (ha : a₁.left = k ≫ a.left) (hb : b₁.left = k ≫ b.left) :
    (a₁ * b₁).left = k ≫ (a * b).left := by
  have ht : k ≫ t = t' := by
    have e1 : a.left ≫ H.hom = t := Over.w a
    have e2 : a₁.left ≫ H.hom = t' := Over.w a₁
    rw [← e1, ← e2, ha]; exact (Category.assoc _ _ _).symm
  let κ : Over.mk t' ⟶ Over.mk t := Over.homMk k ht
  have e1 : a₁ = κ ≫ a := Over.OverMorphism.ext ha
  have e2 : b₁ = κ ≫ b := Over.OverMorphism.ext hb
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem lift_open (σ : Setup) (x : Sp σ.R) {T : Scheme.{0}} (c : T ⟶ (σ.C x).G.left) (d : T ⟶ Sp (Localization.Away σ.f))
    (e : c ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) = d ≫ awayMap σ.f) : ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c := by
  refine ⟨IsOpenImmersion.lift (σ.V x).ι c ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (σ.hV x _).2 ?_
  have h1 := awayMap_notMem σ.f (d τ)
  rw [← Scheme.Hom.comp_apply, ← e] at h1
  exact h1

theorem chart_mul_generic (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (s : T ⟶ Sp (FractionRing (σ.C x).R))
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  obtain ⟨l, hl⟩ := lift_open σ x (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) (pullback.snd _ _ ≫ (σ.C x).y) (by
    rw [pullback.condition_assoc, Category.assoc, (σ.C x).hy, σ.hρ])
  have hα : (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
    have := σ.compat x _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rw [Category.id_comp] at this
    rw [this, Category.assoc, E.onV, ← Category.assoc, hl]
  let P : (Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) → (Over.mk s ⟶ (Over.pullback (jK (σ.C x).R)).obj (σ.C x).G) :=
    fun c => Over.homMk (pullback.lift c.left s (Over.w c)) (pullback.lift_snd _ _ _)
  have hP : ∀ c, c.left = (P c).left ≫ pullback.fst (σ.C x).G.hom (jK (σ.C x).R) := fun c => (pullback.lift_fst _ _ _).symm
  have hA : ∀ c (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA → c'.left = (P c).left ≫ (σ.C x).α := by
    intro c c' h
    rw [← cancel_mono E.ιA, ← h, hP c]
    exact (Category.assoc _ _ _).trans ((congrArg ((P c).left ≫ ·) hα.symm).trans (Category.assoc _ _ _).symm)
  have ht : t₂ = s ≫ (σ.C x).y := by
    have e1 : a'.left ≫ σ.A.hom = t₂ := Over.w a'
    have e2 : (P a).left ≫ ((Over.pullback (jK (σ.C x).R)).obj (σ.C x).G).hom = s := Over.w (P a)
    have e3 := (σ.C x).gen.1.w
    rw [← e1, hA a a' ha]
    exact (Category.assoc _ _ _).trans ((congrArg ((P a).left ≫ ·) e3).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (σ.C x).y) e2)))
  subst ht
  have m1 := (σ.C x).gen.2 (Over.mk s) (P a) (P b) a' b' (hA a a' ha) (hA b b' hb)
  have m2 := (isGrpPullback_pullback (σ.C x).G (jK (σ.C x).R)).2 (Over.mk s) (P a) (P b) a b (hP a) (hP b)
  exact (congrArg (· ≫ E.emb x) m2).trans ((Category.assoc _ _ _).trans ((congrArg ((P a * P b).left ≫ ·) hα.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.ιA) m1.symm))))

theorem chart_mul_flat (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (t₁ : T ⟶ Sp (σ.C x).R) [Flat t₁]
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk t₁ ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have := E.sep
  obtain ⟨w, -⟩ := E.openIn x
  have p1 : ∀ c : Over.mk t₁ ⟶ (σ.C x).G, (c.left ≫ E.emb x) ≫ E.p = t₁ ≫ spMap (σ.ρ x) := fun c => by
    have e : c.left ≫ (σ.C x).G.hom = t₁ := Over.w c
    rw [Category.assoc, w, ← Category.assoc, e]
  have p2 : ∀ c : Over.mk t₂ ⟶ σ.A, (c.left ≫ E.ιA) ≫ E.p = t₂ ≫ awayMap σ.f := fun c => by
    have e : c.left ≫ σ.A.hom = t₂ := Over.w c
    rw [Category.assoc, E.cartA.w, ← Category.assoc, e]
  have : IsSchemeTheoreticallyDominant (jK (σ.C x).R) :=
    schDom_spec_map _ (IsFractionRing.injective (σ.C x).R (FractionRing (σ.C x).R))
  have : IsSchemeTheoreticallyDominant (pullback.fst t₁ (jK (σ.C x).R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback t₁ (jK (σ.C x).R)).flip
  refine ext_of_schDom E.p (by rw [p1, p2, ← p1 a, ← p2 a', ha]) (pullback.fst t₁ (jK (σ.C x).R)) ?_
  let k := pullback.fst t₁ (jK (σ.C x).R)
  let Q : (Over.mk t₁ ⟶ (σ.C x).G) → (Over.mk (pullback.snd t₁ (jK (σ.C x).R) ≫ jK (σ.C x).R) ⟶ (σ.C x).G) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (Over.w c)).trans pullback.condition))
  let Q' : (Over.mk t₂ ⟶ σ.A) → (Over.mk (k ≫ t₂) ⟶ σ.A) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (Over.w c)))
  have h := chart_mul_generic σ E x _ _ (Q a) (Q b) (Q' a') (Q' b')
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) ha).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hb).trans (Category.assoc _ _ _).symm))
  rw [mul_left_comp k a b (Q a) (Q b) rfl rfl, mul_left_comp k a' b' (Q' a') (Q' b') rfl rfl] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

theorem chart_mulAgree : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  intro σ E x T t₁ t₂ a b a' b' ha hb
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  have := (σ.C x).semi.smooth
  obtain ⟨w, -⟩ := E.openIn x
  have hl : ∀ (c : Over.mk t₁ ⟶ (σ.C x).G) (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA →
      ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c.left ∧ l ≫ σ.φ x = c'.left := by
    intro c c' h
    obtain ⟨l, hl⟩ := lift_open σ x c.left (c'.left ≫ σ.A.hom) (by
      rw [← w, ← Category.assoc, h, Category.assoc, E.cartA.w, Category.assoc])
    refine ⟨l, hl, ?_⟩
    rw [← cancel_mono E.ιA, Category.assoc, E.onV, ← Category.assoc, hl]
    exact h
  obtain ⟨la, ha1, ha2⟩ := hl a a' ha
  obtain ⟨lb, hb1, hb2⟩ := hl b b' hb
  let q : (σ.V x).toScheme ⟶ Sp (σ.C x).R := (σ.V x).ι ≫ (σ.C x).G.hom
  have hq : la ≫ q = lb ≫ q := by
    have e1 : a.left ≫ (σ.C x).G.hom = t₁ := Over.w a
    have e2 : b.left ≫ (σ.C x).G.hom = t₁ := Over.w b
    simp only [q, ← Category.assoc, ha1, hb1]
    exact e1.trans e2.symm
  have hu : pullback.snd q q ≫ σ.φ x ≫ σ.A.hom = pullback.fst q q ≫ σ.φ x ≫ σ.A.hom := by
    rw [← cancel_mono (awayMap σ.f)]
    simp only [Category.assoc]
    rw [(σ.cart x).w]
    exact (pullback.condition_assoc (f := q) (g := q) _).symm
  let a₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.fst q q ≫ (σ.V x).ι) (Category.assoc _ _ _)
  let b₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.snd q q ≫ (σ.V x).ι)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let a₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.fst q q ≫ σ.φ x) (Category.assoc _ _ _)
  let b₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.snd q q ≫ σ.φ x)
    ((Category.assoc _ _ _).trans hu)
  have h := chart_mul_flat σ E x (pullback.fst q q ≫ q) _ a₀ b₀ a₁ b₁
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
  let k := pullback.lift la lb hq
  have k1 : k ≫ pullback.fst q q = la := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd q q = lb := pullback.lift_snd _ _ _
  rw [mul_left_comp k a₀ b₀ a b (ha1.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb1.symm.trans (by rw [← k2]; exact Category.assoc _ _ _)),
    mul_left_comp k a₁ b₁ a' b' (ha2.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb2.symm.trans (by rw [← k2]; exact Category.assoc _ _ _))]
  exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) h).trans (Category.assoc _ _ _).symm)

end GlobalTheory.Desc.ChartLaw
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (h : X ⟶ Sp R) :
    gp X ≫ h = spMap (cst h) := by
  apply ext_of_isAffine
  rw [gp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (cst h) =
      (Scheme.ΓSpecIso _).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := rfl
  simp [e]

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hd : ringKrullDim O ≤ 1) {a : O} (ha : a ∈ maximalIdeal O) (v : K) :
    ∃ N : ℕ, ∃ c : O, algebraMap O K a ^ N * v = algebraMap O K c := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  haveI : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hrad : a ∈ (Ideal.span {y}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hne : J ≠ ⊥ := fun h => hy0 (by
      have := hJ (Ideal.mem_span_singleton_self y); rw [h] at this; exact (Submodule.mem_bot _).1 this)
    have : J.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot J hne
    rw [IsLocalRing.eq_maximalIdeal this]; exact ha
  obtain ⟨N, hN⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN
  refine ⟨N, c * x, ?_⟩
  have hy' : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  rw [← map_pow, ← hc, map_mul, map_mul]
  field_simp

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {z : X} {g : X.functionField} (h : RegAt z g) (n : ℕ) :
    RegAt z (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one z).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem eq_of_specializes {X : Scheme.{0}} [IsIntegral X] {z w : X} (hd : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    (hwz : w ⤳ z) (hw : w ≠ genericPoint X) : w = z := by
  by_contra hne
  have hw' : w ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact hwz
  obtain ⟨p, rfl⟩ := hw'
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec X).specializes trivial
  obtain ⟨q, hq⟩ := hη
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p.asIdeal = ⊥ := by
    by_contra h
    haveI := p.isPrime
    have hm := Ideal.isMaximal_of_isPrime_of_ne_bot p.asIdeal h
    have : p = closedPoint _ := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    apply hne; rw [this, Scheme.fromSpecStalk_closedPoint]
  have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
    show p.asIdeal ≤ q.asIdeal; rw [hp]; exact bot_le)
  have h1 : X.fromSpecStalk z p ⤳ genericPoint X := hq ▸ hpq.map (X.fromSpecStalk z).continuous
  have h2 : genericPoint X ⤳ X.fromSpecStalk z p := (genericPoint_spec X).specializes trivial
  exact hw (h1.antisymm h2).eq

theorem θ_comp_c₀ (σ : Setup) (x : Sp σ.R) :
    (σ.θ x).comp σ.c₀ = (cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl₁, hl₂⟩ := σ.hθ x
  have w := (σ.cart x).w
  simp only [Category.assoc] at w
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    calc spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      _ = l ≫ σ.φ x ≫ σ.A.hom ≫ awayMap σ.f := by
          rw [Setup.c₀, ← gp_comp, ← Category.assoc, ← hl₂]; simp only [Category.assoc]
      _ = l ≫ (σ.V x).ι ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [w]
      _ = gp _ ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [← Category.assoc l, hl₁]
      _ = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
          rw [← Category.assoc, gp_comp]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
  simpa using e'

theorem zeroAt_cst {R : Type} [CommRing R] {Y : Scheme.{0}} [IsIntegral Y] (h : Y ⟶ Sp R) (r : R) (z : Y)
    (hz : r ∈ (h z).asIdeal) : ZeroAt z (cst h r) := by
  rw [zeroAt_iff]
  refine ⟨regAt_fnOf (U := ⊤) trivial trivial _, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (x := z) (U := ⊤) trivial (gen_mem (x := z) trivial) _).1 hu
  rw [RingHom.comp_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  exact h1 hz

theorem exists_pow_mul_mem_codimOne_regular_chart : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  intro σ x u
  haveI := (σ.C x).semi
  haveI : Smooth (σ.C x).G.hom := IsSemiAbelian.smooth
  haveI : QuasiCompact (σ.C x).G.hom := IsSemiAbelian.quasiCompact
  haveI : IsLocallyNoetherian (σ.C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom
  haveI : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  haveI : IsNoetherian (σ.C x).G.left := {}
  haveI : TopologicalSpace.NoetherianSpace (σ.C x).G.left := IsNoetherian.noetherianSpace
  have hg : σ.θ x (σ.c₀ σ.f) = cst (σ.C x).G.hom (σ.ρ x σ.f) := RingHom.congr_fun (θ_comp_c₀ σ x) σ.f
  set g := cst (σ.C x).G.hom (σ.ρ x σ.f)
  set v := σ.θ x u
  let P : Set (σ.C x).G.left := {z | ¬ RegAt z v}
  have hP : IsClosed P := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hzU, a, ha⟩ := RegAt.exists_fnOf (not_not.1 hz)
    exact ⟨U, fun y hy => not_not.2 (ha ▸ regAt_fnOf hy _ a), U.isOpen, hzU⟩
  obtain ⟨S, hS, hirr, hPS⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible ⟨P, hP⟩
  let F : Set (σ.C x).G.left := ⋃ t ∈ S, {w | IsGenericPoint w (t : Set _)}
  have hF : F.Finite := hS.biUnion fun t _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb
  have hPt : ∀ t ∈ S, (t : Set (σ.C x).G.left) ⊆ P := fun t ht => by
    have : t ≤ sSup S := le_sSup ht
    rw [← hPS] at this
    exact this
  let C : TopologicalSpace.Closeds (σ.C x).G.left :=
    ⟨⋃ t ∈ S, (t : Set _), hS.isClosed_biUnion fun t _ => t.isClosed⟩
  have hPC : P ⊆ (C : Set _) := by
    have : sSup S ≤ C := sSup_le fun t ht y hy => Set.mem_iUnion₂.2 ⟨t, ht, hy⟩
    rw [← hPS] at this
    exact this
  have key : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → z ∈ P → z ∈ F := by
    intro z hz hzP
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 (hPC hzP)
    have hw : IsGenericPoint (hirr t ht).genericPoint (t : Set _) := by
      have := (hirr t ht).isGenericPoint_genericPoint_closure
      rwa [t.isClosed.closure_eq] at this
    have hwP : (hirr t ht).genericPoint ∈ P := hPt t ht hw.mem
    have hwη : (hirr t ht).genericPoint ≠ genericPoint _ := fun h => hwP (h ▸ regAt_genericPoint v)
    have := eq_of_specializes hz.1.le (hw.specializes hzt) hwη
    exact Set.mem_iUnion₂.2 ⟨t, ht, this ▸ hw⟩
  have hpt : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ∃ N : ℕ, RegAt z (g ^ N * v) := by
    intro z hz
    obtain ⟨a, ha, hag⟩ := zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2
    obtain ⟨N, c, hc⟩ := exists_pow_mul_mem hz.1.le ha v
    exact ⟨N, c, by rw [← hc, hag]⟩
  classical
  let N : (σ.C x).G.left → ℕ := fun z => if h : Vert (σ.C x).G.hom (σ.ρ x σ.f) z then Classical.choose (hpt z h) else 0
  refine ⟨hF.toFinset.sup N, fun z hz => ?_⟩
  have hgz : RegAt z g := (zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2).regAt
  rw [map_mul, map_pow, hg]
  by_cases hzP : z ∈ P
  · have hle : N z ≤ hF.toFinset.sup N := Finset.le_sup (hF.mem_toFinset.2 (key z hz hzP))
    have hN : RegAt z (g ^ N z * v) := by
      simp only [N, dif_pos hz]; exact Classical.choose_spec (hpt z hz)
    rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc]
    exact (regAt_pow hgz _).mul hN
  · exact (regAt_pow hgz _).mul (not_not.1 hzP)

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

noncomputable section

namespace GlobalTheory.Desc.FlatInter

theorem exists_fin_sum {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M ⊗[R] N) : ∃ (n : ℕ) (u : Fin n → M) (r : Fin n → N), x = ∑ i, u i ⊗ₜ[R] r i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul m n => exact ⟨1, fun _ => m, fun _ => n, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, u, r, rfl⟩ := hx
    obtain ⟨m, u', r', rfl⟩ := hy
    exact ⟨n + m, Fin.append u u', Fin.append r r', by simp [Fin.sum_univ_add]⟩

theorem mem_range_iInf {R K R₁ : Type} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup R₁] [Module R R₁]
    [Module.Flat R R₁] {J : Type} [Finite J] (N : J → Submodule R K) (T : K ⊗[R] R₁)
    (hT : ∀ j, T ∈ LinearMap.range ((N j).subtype.rTensor R₁)) :
    T ∈ LinearMap.range ((⨅ j, N j).subtype.rTensor R₁) := by
  classical
  have := Fintype.ofFinite J
  let π : K →ₗ[R] ∀ j, K ⧸ N j := LinearMap.pi fun j => (N j).mkQ
  have hex : Function.Exact (⨅ j, N j).subtype π := by
    rw [LinearMap.exact_iff]
    simp [π, LinearMap.ker_pi]
  have hex' := Module.Flat.rTensor_exact R₁ hex
  rw [← LinearMap.exact_iff.mp hex']
  rw [LinearMap.mem_ker]
  let e := TensorProduct.piLeft R R₁ (fun j => K ⧸ N j)
  apply e.injective
  rw [map_zero]
  funext j
  have hj : LinearMap.proj j ∘ₗ e.toLinearMap ∘ₗ π.rTensor R₁ = (N j).mkQ.rTensor R₁ := by
    ext x r
    simp [π, e]
  have := congrArg (fun f => f T) hj
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval] at this
  rw [this, Pi.zero_apply, ← LinearMap.mem_ker, rTensor_mkQ]
  exact hT j

def tensorMap {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K]
    (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) :
    K ⊗[R] R₁ →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun r => c r * θ u) (fun a b => by simp [add_mul]))
      (fun a b => by ext r; simp [mul_add]))
    (fun a u r => by
      simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, hc]
      ring)

theorem tensorMap_tmul {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a))
    (u : K) (r : R₁) : tensorMap θ c hc (u ⊗ₜ[R] r) = c r * θ u := rfl

end GlobalTheory.Desc.FlatInter


open GlobalTheory.Desc.FlatInter in
theorem GlobalTheory.Desc.spanBy_iInter_of_flat : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) → (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → ∀ (J : Type) [Finite J] [Nonempty J] (N : J → Submodule R K), spanBy c (θ '' ⋂ j, (N j : Set K)) = ⋂ j, spanBy c (θ '' (N j : Set K)) := by
  intro R R₁ K L _ _ _ _ _ _ _ θ c hc hinj J _ _ N
  let Φ := tensorMap θ c hc
  have hΦ : ∀ x, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨n, u, r, rfl⟩ := exists_fin_sum x
    apply hinj n u r

    simpa [Φ, map_sum, tensorMap_tmul] using hx
  ext v
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    refine Set.mem_iInter.2 fun j => ⟨n, r, t, fun i => Set.image_mono (Set.iInter_subset _ j) (ht i), rfl⟩
  · intro hv
    have key : ∀ j, ∃ T ∈ LinearMap.range ((N j).subtype.rTensor R₁), Φ T = v := by
      intro j
      obtain ⟨n, r, t, ht, rfl⟩ := Set.mem_iInter.1 hv j
      choose u hu hut using ht
      refine ⟨(N j).subtype.rTensor R₁ (∑ i, (⟨u i, hu i⟩ : N j) ⊗ₜ[R] r i), LinearMap.mem_range_self _ _, ?_⟩

      simp [Φ, map_sum, tensorMap_tmul, hut]
    choose T hT hTv using key
    obtain ⟨j₀⟩ := ‹Nonempty J›
    have heq : ∀ j, T j = T j₀ := fun j => by
      have := hΦ (T j - T j₀) (by rw [map_sub, hTv, hTv, sub_self])
      exact sub_eq_zero.1 this
    obtain ⟨y, hy⟩ := mem_range_iInf N (T j₀) fun j => heq j ▸ hT j
    obtain ⟨n, w, s, rfl⟩ := exists_fin_sum y
    refine ⟨n, s, fun i => θ (w i), fun i => ⟨w i, ?_, rfl⟩, ?_⟩
    · exact Set.mem_iInter.2 fun j => (Submodule.mem_iInf N).1 (w i).2 j
    · rw [← hTv j₀, ← hy]

      simp [Φ, map_sum, tensorMap_tmul]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem fnOf_app_of_pff : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  intro X Y _ _ m φ hφ V hV hV' a
  have h : gp Y ≫ m = spMap φ ≫ gp X := by
    obtain ⟨l, h1, h2⟩ := hφ
    rw [Category.comp_id] at h1
    rw [← h1, h2]
  have hloc : IsLocalHom φ := inferInstance
  have e1 : Spec.map (m.stalkMap (genericPoint Y)) ≫ X.fromSpecStalk (m (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) := by
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]; exact h
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of Y.functionField)).symm.injective
    (a₁ := ⟨m (genericPoint Y), m.stalkMap (genericPoint Y), inferInstance⟩)
    (a₂ := ⟨genericPoint X, CommRingCat.ofHom φ, hloc⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e1)
  obtain ⟨h₁, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only at e3
  have key : X.presheaf.germ V _ hV' ≫ m.stalkMap (genericPoint Y) =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ := by
    rw [e3, TopCat.Presheaf.stalkCongr_hom]
    exact X.presheaf.germ_stalkSpecializes_assoc hV' _ _
  have key' : m.app V ≫ Y.presheaf.germ (m ⁻¹ᵁ V) (genericPoint Y) hV' =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ :=
    (Scheme.Hom.germ_stalkMap m V (genericPoint Y) hV').symm.trans key
  exact congrArg (fun q => CommRingCat.Hom.hom q a) key'

end GlobalTheory.Desc
end
end
