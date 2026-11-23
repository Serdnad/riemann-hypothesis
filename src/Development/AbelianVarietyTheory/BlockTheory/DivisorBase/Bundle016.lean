module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

def CplxEq {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ) {m m' : ℕ}
    (c : Fin m → ℂ) (v : Fin m → V) (c' : Fin m' → ℂ) (v' : Fin m' → V) : Prop :=
  letI := σ.toAlgebra
  (∑ i, c i ⊗ₜ[K] v i : ℂ ⊗[K] V) = ∑ k, c' k ⊗ₜ[K] v' k

def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial

section OneField

variable {K : Type} [Field K] [NumberField K]

section Geo

variable (G : Geo K) (s : Fin G.D → Fin G.N → K) (σ : K →+* ℂ)

def mulPow {a j l : ℕ} (h : j + a = l) (α : MonoDeg (Fin G.D) a) : G.Sec j →ₗ[K] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) α ((Nat.cast_add j a).symm.trans (congrArg _ h))

variable {G s} (hs : G.IsGood s)

end Geo

section Data

variable (X : Data K) (s : Fin X.D → Fin X.N → K) (σ : K →+* ℂ)

theorem add_sub_D : X.D + (X.T - X.D) = X.T := Nat.add_sub_cancel' ((Nat.le_succ _).trans X.le_T)

def spaceP : Submodule K (X.Sec X.T) :=
  ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)

def spaceV : Submodule K (X.Sec X.T) := X.global X.T ⊔ spaceP X s

variable {X s} (hs : X.IsGood s)

end Data

end OneField

variable {F : Type} [Field F] [NumberField F] (X : Data F)


variable (E : Type) [Field E] [NumberField E] [Algebra F E]

variable {E}

def Complexify : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (β : (F →+* ℂ) → ℝ), IsTotallyComplex F → (∀ σ, 0 < β σ) →
    X.MulStable → X.MulBound β →
      (∀ σ, X.MulBoundAt σ (β σ)) ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], (X.baseChange E).MulStable

end GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase

section Surface

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]

def IsProjSurface : Prop :=
  IsIntegral T ∧ topologicalKrullDim T = 2 ∧ IsProjOver (strHom k (X := T))

variable {T}

def degCh2 (E : T.Modules) (r : ℕ) : ℚ :=
  ((chi k E + chi k (VB.dual E) - 2 * r * chi k (structureModule T) : ℤ) : ℚ) / 2

variable {k}

end Surface

section Abelian

variable {S S' : Scheme.{0}} (A : Over S)

def toBase (s : S' ⟶ S) {Y : Over S'} (x : Y ⟶ (Over.pullback s).obj A) :
    Over.mk (Y.hom ≫ s) ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom s) (by
    have := Over.w x
    simp only [Over.mk_hom, Category.assoc, pullback.condition]
    rw [← this]; simp)

def sqToBase (s : S' ⟶ S) :
    ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).left ⟶ (A ⊗ A).left :=
  (lift (toBase A s (fst _ _)) (toBase A s (snd _ _))).left

variable [GrpObj A]

def IsPrincipalPol (c : Pic (A ⊗ A).left) : Prop :=
  pull (lift (1 : A ⟶ A) (𝟙 A)).left c = 0 ∧ pull (lift (𝟙 A) (1 : A ⟶ A)).left c = 0 ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S),
      ∃ (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB),
        Out.RelAmple ((Over.pullback s).obj A) L ∧ Out.KTriv ((Over.pullback s).obj A) L ∧
          pull (sqToBase A s) c = lam (cls L hL) (fst _ _) (snd _ _)

theorem isPrincipalPol_of_polAV (P : Out.PolAV S) :
    IsPrincipalPol P.A (lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A)) := by
  have := P.isAb.comm
  refine ⟨?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [pull_lam, lift_fst, lam_one_left]
  · rw [pull_lam, lift_snd, lam_one_right]
  · have h := isGrpPullback_pullback P.A s
    have hL := pull_isLB P.isLB (pullback.fst P.A.hom s)
    obtain ⟨w, hw⟩ := (cls_eq_iff hL hL).1 rfl
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
      (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
    refine ⟨_, hL, relAmple_pull h.1 P.isLB hL ((isGen_iff w).1 hw) U hU
      (fun y => by rwa [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]) P.ample,
      kTriv_pull h P.isLB hL ((isGen_iff w).1 hw) P.ktriv, ?_⟩
    rw [sqToBase, pull_lam, lift_fst, lift_snd, cls_pull P.isLB, lam_pull_of_isGrpPullback h]
    rfl

end Abelian

open Formalism.BasicNotions

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open scoped ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def dimAt (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) : ℚ) : ℝ)

def ratio (D : D7) (i : Fin D.R.m) (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) : ℝ :=
  (μ 𝓕).toReal * ∏ τ, dimAt D i τ

def wtSize (D : D7) (i : Fin D.R.m) : ℝ :=
  ∑ τ, ∑ a, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ)|

def Sizes (D : D7) (L : ℝ) : Prop :=
  (D.R.f : ℝ) * D.R.r * D.R.nV ≤ Real.exp L ∧ (∀ i, wtSize D i ≤ Real.exp L ^ 2) ∧
    Real.log ((D.host.g 0 : ℝ) * D.host.g 1) ≤ 30 * L ∧ Real.log D.host.rdE + |dlogL D 1| ≤ 2 * L

variable {D : D7}

abbrev levW {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) :
    Subgroup (GL (Fin (Wc D i).rank) (Formalism.IndefR.Lev.EAf D)) :=
  lev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P)

abbrev formsW {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (Wc D i) S) : Submodule ℂ (MMap M) :=
  Mult θ M (levS _ (C.βW i) (C.datWp i P)) (levChi _ (C.βW i) (C.datWp i P))

def expW (D : D7) (i : Fin D.R.m) : WTZ D.host.E := wtZ (wtA (kapTop D i)) (kapTop D i).n

variable (T : CoreJ D) (i : Fin D.R.m)

def scalarForms (s : T.Q.c.F →+* ℂ) : Submodule ℂ (FDSec (T.U ((i : ℕ) + 1) s).X) :=
  holSub (T.U ((i : ℕ) + 1) s).X (modelWt (T.U ((i : ℕ) + 1) s) (expW D i))

def probSq (s : T.Q.c.F →+* ℂ) (f : FDSec (T.U ((i : ℕ) + 1) s).X) : ℝ :=
  (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (expW D i) *
    (petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
      (modelWt (T.U ((i : ℕ) + 1) s) (expW D i)) f).toReal) ^ 2

def adFun {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X) :
    GA D (Wc D i) → ℂ :=
  hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (expW D i) : ℂ) •
    adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
      (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f)

theorem probSq_rdU (s : T.Q.c.F →+* ℂ) (f : T.R ((i : ℕ) + 1)) :
    probSq T i s (rdU (T.U ((i : ℕ) + 1) s) f) =
      petAt (T.U ((i : ℕ) + 1) s) (xiR D) (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muQ1 (T.V ((i : ℕ) + 1) s)) (expW D i) f ^ 2 := rfl

theorem adFun_rdU {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : T.R ((i : ℕ) + 1)) :
    adFun T i hV (rdU (T.U ((i : ℕ) + 1) s) f) = phiC T hV (wtA (kapTop D i)) f := by
  unfold adFun phiC CoreJ.phiJ expW
  rw [lieFacZ_wtZ]

variable [Algebra T.Q.c.F D.what₂.LL]

abbrev gd (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := goodOf T.Q.c (res T σ)

def Corr (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i) {M : DSModel (Wc D i) (parAt (Wc D i) σ)}
    (F : MMap M) (f : FDSec (T.U ((i : ℕ) + 1) (gd T σ)).X) : Prop :=
  (GoodEmb T.Q.c (res T σ) ∧ ∃ v, IsExtVec M v ∧ F v = adFun T i hV f) ∨
    (¬ GoodEmb T.Q.c (res T σ) ∧ ∃ v : M.Vec, IsUnitV v ∧ F v = fun g => conj (adFun T i hV f g))

def ExactRatio {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ)
    (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) : Prop :=
  ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (σ : D.what₂.LL →+* ℂ) (M : DSModel (Wc D i) (parAt (Wc D i) σ)) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i),
      ∀ F ∈ formsW C i P θ M, ∀ f ∈ scalarForms T i (gd T σ), Corr T i σ hV F f →
        (∃ c, IsMultIP M μ 𝓕 F F c) ∧ ipAt M μ 𝓕 F F = ((ratio D i μ 𝓕 * probSq T i (gd T σ) f : ℝ) : ℂ)

def RatioBound (i : Fin D.R.m) (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (L : ℝ) : Prop :=
  (∀ τ, Real.log (dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L) ∧
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) ∧
    Real.log (ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)

def IndexBound {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) : Prop :=
  (levW C i P).relIndex (levW C i (LevelP.full _ _ _)) ≠ 0 ∧
    Real.log ((levW C i P).relIndex (levW C i (LevelP.full _ _ _))) ≤
      2 * D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.host.g 0 : ℝ) * D.host.g 1)

def OneMeasure (D : D7) : Prop :=
  ∀ (Tu : Type) (C : LevCh D Tu) (t0 : Tu), C.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ),
    IndexBound C i P ∧ (∀ τ, 1 ≤ dimAt D i τ) ∧
      ∀ (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))), IsMeasFD (Wc D i) (levW C i P) μ 𝓕 →
        μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ExactRatio C i P μ 𝓕 ∧ ∀ L, Sizes D L → RatioBound i μ 𝓕 L


end GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes
end
end
