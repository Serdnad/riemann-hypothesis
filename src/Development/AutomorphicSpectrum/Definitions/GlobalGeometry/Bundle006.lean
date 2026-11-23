module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K] {X : Scheme.{0}}

structure CurveIn (C : ACurve K) (ζ : Spec (CommRingCat.of K) ⟶ X) where

  x : ∀ i : C.I, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ x i = ζ
  ae : ∀ U : X.Opens, centre ζ ∈ U → {i | centre (x i) ∉ U}.Finite

variable {C : ACurve K} {ζ : Spec (CommRingCat.of K) ⟶ X}

def CurveIn.lieLat (Y : CurveIn C ζ) {G : Over X} [GrpObj G] {V : Type} [AddCommGroup V] [Module K V]
    (M : LieModel G ζ V) : C.I → AddSubgroup V := fun i =>
  AddSubgroup.closure {e | ∃ v : epsAt (Y.x i) ⟶ G, IsTanAt G (Y.x i) v ∧
    (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (C.v i).valuationSubring.subtype)) ≫ v.left}

def CurveIn.IsDeg (Y : CurveIn C ζ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω)
    (n : ℤ) : Prop :=
  ∃ (h₀ : genPt ξ ⤳ centre ζ) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (s₀ : Ω) (s : C.I → Ω) (r : C.I → K),
    Λ.IsGenAt ⟨centre ζ, h₀⟩ s₀ ∧ (∀ i, Λ.IsGenAt ⟨centre (Y.x i), h i⟩ (s i)) ∧
      (∀ i, r i ≠ 0 ∧ ValAt ξ ζ (s i / s₀) (r i)) ∧ {i | C.v i (r i) ≠ 1}.Finite ∧
      n = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (r i))

def coordDeg (C : ACurve K) {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → K)
    (a : B → ℤ) : ℤ :=
  ∑ k, a k * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (Finset.univ.sup fun c : ι k => C.v i (w ⟨k, c⟩))

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def genFibre (O : Type) [CommRing O] [Algebra O Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) :=
  {p | ∀ o : O, o ≠ 0 → unitAt ξ p (algebraMap O Ω o)}

def ConstClosed (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] : Prop :=
  ∀ a : Ω, IsAlgebraic O a → ∃ x y : O, y ≠ 0 ∧ a * algebraMap O Ω y = algebraMap O Ω x

def lineLat (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) : Lat ξ Ω := fun x =>
  Submodule.span (regAt ξ x) {t | ∃ f : Ω, IsCoeffAt A B p q a b x f ∧ t = f⁻¹}

def SplitModAt (A : Lat ξ E) (ϖ : Ω) {N : ℕ} (J : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))) (x y : Cpt ξ) : Prop :=
  (∀ w ∈ A y, ∀ k, J x w k ∈ regAt ξ y ∧ (J x w k - J y w k) / ϖ ∈ regAt ξ y) ∧
    ∃ R : (Fin N → Ω) →ₗ[Ω] E, (∀ k, R (Pi.single k 1) ∈ A y) ∧ ∀ w ∈ A y, ∃ w' ∈ A y, R (J x w) = w + ϖ • w'

def ExactModLat (A B : Lat ξ E) (ϖ : Ω) (N : ℕ) : Prop :=
  ∃ J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω)), ∀ x : Cpt ξ, ¬ unitAt ξ x ϖ → ∃ U : X.Opens, x.1 ∈ U ∧
    ∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → SplitModAt A ϖ J x y ∧ SplitModAt B ϖ J' x y ∧
      ∀ w ∈ A y, ∀ w' ∈ B y, dotProduct (J x w) (J' x w') / ϖ ∈ regAt ξ y

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem not_mem_flagStep {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (i : Fin r) :
    b i ∉ flagStep Ω b i := by
  exact hb.notMem_span_image (by simp)

theorem gr_isGenAt {r : ℕ} (L : Lat ξ E) (b b₀ : Fin r → E) (p : Cpt ξ) (hL : L.IsFrameAt b p)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) (c : Ω)
    (hc : b i - c • b₀ i ∈ flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨hb, hLp⟩ := hL
  have hbi : b i ∉ flagStep Ω b i := not_mem_flagStep b hb i
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hbi
    rw [hF]
    simpa using hc
  refine ⟨hc0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨e, he, het⟩
    rw [hLp] at he
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he
    have het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i := het
    set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS
    have hFS : flagStep Ω b₀ i ≤ S := by
      rw [← hF]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k, fun hki => ?_, rfl⟩
      subst hki
      exact lt_irrefl (k : ℕ) hk
    have h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S := S.smul_mem c (hFS het')
    have h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S :=
      S.smul_mem c (Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))
    have h3 : t • (b i - c • b₀ i) ∈ S := S.smul_mem t (hFS hc)
    have heq : (c * (d i : Ω) - t) • b i =
        c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k -
          t • (b i - c • b₀ i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      module
    have key : (c * (d i : Ω) - t) • b i ∈ S := by
      rw [heq]
      exact S.sub_mem (S.sub_mem h1 h2) h3
    have hzero : c * (d i : Ω) - t = 0 := by
      by_contra hne
      apply hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)
      have := S.smul_mem (c * (d i : Ω) - t)⁻¹ key
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    refine Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩
    show (d i : Ω) * c = t
    rw [mul_comm]
    exact sub_eq_zero.mp hzero
  · refine Submodule.span_le.mpr ?_
    rintro _ rfl
    refine Submodule.subset_span ⟨b i, ?_, hc⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem zpow_ratio (Λ : Lat ξ Ω) (p : Cpt ξ) (s t : Ω) (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) (n : ℤ) :
    (t / s) ^ n ∈ regAt ξ p := by
  obtain ⟨hs0, hsp⟩ := hs
  obtain ⟨ht0, htp⟩ := ht
  have h1 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hsp, htp]
    exact Submodule.mem_span_singleton_self t
  have h2 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← htp, hsp]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h2
  have hts : t / s = a := by
    rw [div_eq_iff hs0]
    exact ha.symm
  have hst : s / t = a' := by
    rw [div_eq_iff ht0]
    exact ha'.symm
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hts]
    exact pow_mem a.2 m
  · rw [zpow_negSucc, ← inv_pow, inv_div, hst]
    exact pow_mem a'.2 _

theorem tens_isGenAt {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨s', hs', rfl⟩
    have hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.FlagModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def evC (z : (Σ k, ι k) → ℂ) (f : MRing ι) : ℂ := eval z (map (Int.castRingHom ℂ) f)

def conjPt (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => starRingEnd ℂ (z p)

def conjLine (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := A.h (conjPt z)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa [conjPt] using hi⟩
  smul c z hc := by
    have h := A.smul (fun k => starRingEnd ℂ (c k)) (conjPt z) (fun k => by simpa using hc k)
    have e : conjPt (fun p => c p.1 * z p) = fun p => starRingEnd ℂ (c p.1) * conjPt z p := by
      funext p
      simp [conjPt]
    rw [e, h]
    simp

def UnitRatio (P : Ideal (MRing ι)) (f g : MRing ι) : Prop :=
  f ∉ P ∧ g ∉ P ∧ ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

def IsLineIso (P : Ideal (MRing ι)) (a b : K → ℤ) (f g : MRing ι) : Prop :=
  (∃ α γ : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g γ ∧ ∀ k, (α k : ℤ) - γ k = a k - b k) ∧ UnitRatio P f g

def IsDefectOn (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (f g : MRing ι) (A B : HermLine ι)
    (w : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ z ∈ Xo, ∀ u v : MRing ι, u * f - v * g ∈ P → evC z u ≠ 0 →
    w z = Real.log (‖evC z v‖ / ‖evC z u‖ * B.h z / A.h z)

def IsoLineOn (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (A B : HermLine ι) : Prop :=
  ∃ f g : MRing ι, IsLineIso P A.a B.a f g ∧ IsDefectOn P Xo f g A B fun _ => 0

section Join

variable {K₁ K₂ : Type} (ι₁ : K₁ → Type) (ι₂ : K₂ → Type)

def joinIdx : K₁ ⊕ K₂ → Type := Sum.elim ι₁ ι₂

instance instFintypeJoinIdx [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] : ∀ k, Fintype (joinIdx ι₁ ι₂ k)
  | Sum.inl k => inferInstanceAs (Fintype (ι₁ k))
  | Sum.inr k => inferInstanceAs (Fintype (ι₂ k))

def joinInl : (Σ k, ι₁ k) → Σ k, joinIdx ι₁ ι₂ k := fun p => ⟨Sum.inl p.1, p.2⟩

def joinInr : (Σ k, ι₂ k) → Σ k, joinIdx ι₁ ι₂ k := fun p => ⟨Sum.inr p.1, p.2⟩

variable {ι₁ ι₂}

def joinVec {Ω : Type} (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) : (Σ k, joinIdx ι₁ ι₂ k) → Ω
  | ⟨Sum.inl k, i⟩ => y₁ ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => y₂ ⟨k, i⟩

end Join

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenWeilModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def ext {ξ : Spec (CommRingCat.of Ω) ⟶ X} {k : Type} [Field k] (i : Ω →+* k) :
    Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl

theorem unitOn_ext {k : Type} [Field k] (i : Ω →+* k) (u : Ωˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map i.toMonoidHom u) := by
  ext
  exact congrArg (fun f => f.hom (u : Ω)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)).symm

theorem unitOn_bij {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toMulEquiv).bijective

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

end GlobalTheory.CompanionTheory.Ar.GenWeilModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure GenWeil (G : Over X) [GrpObj G] (L : LB G.left) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ)
    (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ) : Prop where
  finite : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1}
  mul_left : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g
  mul_right : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g'
  perfect : ∀ χ : (Over.mk ξ ⟶ G) → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') →
    ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g
  nondeg : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1
  weil : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (xk gk : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ), xk.left = spMap i ≫ x.left → gk.left = spMap i ≫ g.left →
      (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = i (e x g))

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev TateIsoAt (D : Datum H) (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

def IsFullLevelAt (D : Datum H) (t : SAB H X) (ξ : Sp Ω ⟶ X) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)) :
    Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k), ∃ I : TateIsoAt D t (spMap i ≫ ξ),
    (I.ζ N : k) = i z ∧ ∀ a, (I.ev N a).left = spMap i ≫ (ev a).left

end GlobalTheory.CompanionTheory.Ar.XR
end
end
