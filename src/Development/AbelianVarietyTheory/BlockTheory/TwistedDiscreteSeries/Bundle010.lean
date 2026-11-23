module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Mathlib.Basic.Complex.Basic
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDefiniteSpace (V : HSp D) : Prop := V.SigOK ∧ V.IsDefinite

def IsOpenCompactLevel (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧ IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

def levelFin (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (Lev.toAfE V K).comap (finHom V).range.subtype

def classGroupAt (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : Bridge.Gf V) : Subgroup (GQ V) :=
  Bridge.stab (Bridge.ratF V) (levelFin V K) x

structure IsClassFun (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (Φ : GA D V → ℂ) : Prop where

  left : ∀ γ ∈ GQ V, ∀ h, Φ (γ * h) = Φ h

  real : ∀ k ∈ GinfC V, ∀ h, Φ (h * k) = Φ h

  level : ∀ k ∈ Lev.levA V K, ∀ h, Φ (h * k) = Φ h

def ClassSumIntegral : Prop :=
  ∀ (D : D7) (V : HSp D), IsDefiniteSpace V →
    ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K →
      ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 →
        ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levelFin V K) y →
          ∀ (z : I → GA D V), (∀ i, (finHom V).rangeRestrict (z i) = y i) →
            ∀ (Φ : GA D V → ℂ), IsClassFun V K Φ →
              (∀ i, Finite (classGroupAt V K (y i))) ∧ IntegrableOn Φ 𝓕 μ ∧
                ∫ h in 𝓕, Φ h ∂μ = ∑ i, ((Nat.card (classGroupAt V K (y i)) : ℂ))⁻¹ * Φ (z i)

variable {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}

theorem map_conj_inv {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) : f (a⁻¹ * b * a) = (f a)⁻¹ * f b * f a := by
  rw [map_mul, map_mul, map_inv]

theorem mem_levelFin (w : GA D V) : (finHom V).rangeRestrict w ∈ levelFin V K ↔ Lev.finE V w ∈ K := Iff.rfl

theorem mem_classGroupAt (z : GA D V) (γ : GQ V) :
    γ ∈ classGroupAt V K ((finHom V).rangeRestrict z) ↔ Lev.finE V (z⁻¹ * (γ : GA D V) * z) ∈ K := by
  unfold classGroupAt
  rw [Bridge.mem_stab]
  have e : ((finHom V).rangeRestrict z)⁻¹ * Bridge.ratF V γ * (finHom V).rangeRestrict z =
      (finHom V).rangeRestrict (z⁻¹ * (γ : GA D V) * z) := by
    have e0 : Bridge.ratF V γ = (finHom V).rangeRestrict (γ : GA D V) := by
      simp only [Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [e0]
    exact (map_conj_inv (finHom V).rangeRestrict z γ).symm
  rw [e]
  exact mem_levelFin _

end GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i t)

def IsLiftV (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) : Prop :=
  rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf (Vc D i)) : GL _ _)) = R.eG g

def IsAlgV (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q) (x y : (R.HV i t).H) : Prop :=
  (R.HV i t).e y = ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x)

def algW (i : Fin D.R.m) (c : G → ℂ) : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG c)

theorem algW_eC (i : Fin D.R.m) :
    algW R i (RealDat.eC (A := A) (sg0 D A)) = postOn _ (R.eWf i (sg0 D A)) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def classSumAt (f f' : S.Forms) : ℂ :=
  ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ ((f : S.Cl → S.V) c) ((f' : S.Cl → S.V) c)

def IsUnitaryAt {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (g : G) (f f' : S.Forms), classSumAt S σ (r g f) (r g f') = classSumAt S σ f f'

end ClassSum

section Statement

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}

structure DefiniteUnitary (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop where

  what₂ : ∀ (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtildeCSD t) σ (A.leftGroupActionRight t)

  lifts : ∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtCSD i t) σ (A.leftGroupActionLift i t)

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ActsUnitarily (R : RealDat D A Ks) : Prop where

  what₂ : IsUnitaryRep R.gE

  formsW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

  definite : DefiniteUnitary A

end Statement

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev mmul {A : Type} [CommRing A] {l m n : ℕ} (x : Matrix (Fin l) (Fin m) A) (y : Matrix (Fin m) (Fin n) A) :
    Matrix (Fin l) (Fin n) A := x * y

def IsIsom (V V' : HSp D) (R : Type) [CommRing R] [Algebra D.host.F R]
    (j : Matrix (Fin V'.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] R)) : Prop :=
  Function.Bijective j.mulVec ∧
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig R) j * V'.gram.map (Formalism.UG.inclE (F := D.host.F) R) * j =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) R)

def IsLocLatIsom (V V' : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (j : Matrix (Fin V'.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) : Prop :=
  IsIsom V V' (v.adicCompletion D.host.F) j ∧
    j.mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _)

def IsLatIsom (V V' : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) : Prop :=
  IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j ∧
    j.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) = (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _)

def OnePlaceOver (T : Set (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∀ PP ∈ T, ∀ PP' ∈ T, ¬ IsConjPl PP PP'

def MatchesAt (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D))
    (T : Set (Formalism.L2.DIV.Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) : Prop :=
  ∃ u : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    mmul β'.val (u.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = mmul j β.val ∧
      ∀ PP ∈ T, ∀ a b, Formalism.L2.DIV.resS D.host.F PP (u a b) = if a.val = b.val then 1 else 0

def castDat {n n' : ℕ} (h : n = n') (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Formalism.L2.DIV.LevDat D.host.E ℂ n' where
  r := L.r
  hr := L.hr.trans h.le
  t := L.t
  s := L.s
  Pg := L.Pg
  Q := L.Q
  P := L.P
  cg := L.cg
  xq := L.xq

def IsConjBy (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (φ : GfC V ≃ₜ* GfC V') : Prop :=
  ∀ g : GfC V, mmul (finE V' (φ g : GA D V')).val j = mmul j (finE V (g : GA D V)).val

def inA (V : HSp D) (R : Finset (GfC V)) : Finset (GA D V) := R.map (Function.Embedding.subtype _)

def imA {V V' : HSp D} (φ : GfC V ≃ₜ* GfC V') (R : Finset (GfC V)) : Finset (GA D V') :=
  inA V' (R.map φ.toEquiv.toEmbedding)

def ReadIn {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (T : Set (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  (∀ PP ∈ L.Pg, PP ∈ T) ∧ ∀ PP ∈ L.Q, PP ∈ T

structure Carries (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (M : ℕ) (T : Set (Formalism.L2.DIV.Pl D.host.E))
    (φ : GfC V ≃ₜ* GfC V') : Prop where

  stabLoc : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V),
    Formalism.UG.bc (Formalism.UG.prV v) (finE V (g : GA D V)) ∈ Formalism.UG.levelVL D.sp.cm.sig V.gram v Λ ↔
      Formalism.UG.bc (Formalism.UG.prV v) (finE V' (φ g : GA D V')) ∈ Formalism.UG.levelVL D.sp.cm.sig V'.gram v Λ'

  supp : ∀ (f : Formalism.L2.Theta.AE D) (g : GfC V), SuppF V f (g : GA D V) ↔ SuppF V' f (φ g : GA D V')

  det : ∀ g : GfC V, (Formalism.L2.Theta.mt V' (φ g : GA D V')).det = (Formalism.L2.Theta.mt V (g : GA D V)).det

  lev : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ g : GfC V,
    (g : GA D V) ∈ levG V β L ↔ (φ g : GA D V') ∈ levG V' β' (castDat h L)

  chi : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ g : GfC V, (g : GA D V) ∈ levG V β L →
    levChi V' β' (castDat h L) (φ g : GA D V') = levChi V β L (g : GA D V)

  lift : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ (g0 : Formalism.L2.DIV.G0 L.Pg L.r) (g : GfC V),
    IsLevelLift V β L g0 (g : GA D V) ↔ IsLevelLift V' β' (castDat h L) g0 (φ g : GA D V')

  sph : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), (M : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S) →
    ∀ g : GfC V, (g : GA D V) ∈ KsphC V S ↔ (φ g : GA D V') ∈ KsphC V' S

  heckeElt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (k : ℕ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → Formalism.L2.NTheta.IsIdemAt e P → ∀ g : GfC V,
    Formalism.L2.NTheta.IsHeckeElt V e ϖ k (g : GA D V) ↔ Formalism.L2.NTheta.IsHeckeElt V' e ϖ k (φ g : GA D V')

  heckeAt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ), (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ g : GfC V,
    IsHeckeAt V P k (g : GA D V) ↔ IsHeckeAt V' P k (φ g : GA D V')

  divAt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → IsPrimeIdem P e f → ∀ g : GfC V,
    DivAt V e ϖ d (g : GA D V) ↔ DivAt V' e ϖ d (φ g : GA D V')

  opAt : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ R : Finset (GfC V),
    IsHeckeOpAt V (levS V β L) (levChi V β L) S P k (inA V R) ↔
      IsHeckeOpAt V' (levS V' β' (castDat h L)) (levChi V' β' (castDat h L)) S P k (imA φ R)

  opFull : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Formalism.L2.DIV.Pl D.host.E) (d : List ℤ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ R : Finset (GfC V),
    Hecke₂ V (levS V β L) (levChi V β L) S P d (inA V R) ↔
      Hecke₂ V' (levS V' β' (castDat h L)) (levChi V' β' (castDat h L)) S P d (imA φ R)

def GlobalIsometry (D : D7) : Prop :=
  ∀ (V V' : HSp D), V.rank = V'.rank →
    ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
      (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ),
      IsSDFrame V β Λ N → IsSDFrame V' β' Λ' N' →
      ∀ T : Set (Formalism.L2.DIV.Pl D.host.E), OnePlaceOver T →
        ∃ j, IsLatIsom V V' Λ Λ' j ∧ MatchesAt V V' β β' T j

def InducedIso (D : D7) : Prop :=
  ∀ (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ),
    IsSDFrame V β Λ N → IsSDFrame V' β' Λ' N' →
    ∀ (T : Set (Formalism.L2.DIV.Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)),
      IsLatIsom V V' Λ Λ' j → MatchesAt V V' β β' T j →
      ∃ φ : GfC V ≃ₜ* GfC V', IsConjBy V V' j φ ∧ Carries V V' h Λ Λ' β β' (N * N') T φ

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

section Abstract

variable {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E]

def HasRationalTest (σ : K →+* ℂ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ e ∈ S, ∀ a, ∃ z : K, σ z = ψ a e

end Abstract

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

end Interface

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowTestModel (R : RealDat D A Ks) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (R.HE.H →ₗ[ℂ] ℂ)), (∀ e : R.HE.H, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), ∃ z : D.what₂.LL, D.what₂.embLL z = ψ a (R.Th t (R.jX t x))

def twFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E →ₗ[ℂ] ℂ) : Tw s E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.out x))
  map_add' x y := by rw [Tw.out_add, map_add (f := _), map_add (f := _)]
  map_smul' z x := by rw [Tw.out_smul, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

def untwFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Tw s E →ₗ[ℂ] ℂ) : E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.mkL s E x))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' z x := by rw [map_smulₛₗ, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

theorem test_tw_iff {K E : Type} [Field K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {σ σ' : K →+* ℂ}
    (h : ∀ a, σ' a = cj s (σ a)) {ι : Type} {X : ι → Type} (v : ∀ t, X t → E) :
    (∃ (n : ℕ) (ψ : Fin n → (Tw s E →ₗ[ℂ] ℂ)), (∀ e : Tw s E, (∀ a, ψ a e = 0) → e = 0) ∧
      ∀ t x a, ∃ z : K, σ' z = ψ a (Tw.mk s (v t x))) ↔
    (∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ t x a, ∃ z : K, σ z = ψ a (v t x)) := by
  constructor
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => untwFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    refine ⟨z, ?_⟩
    have := congrArg (cj s) ((h z).symm.trans hz)
    rw [cj_cj] at this
    exact this
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => twFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    exact ⟨z, (h z).trans (congrArg (cj s) hz)⟩

end Concrete

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

def IsTransRep {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r)
    (M : HMod (Bridge.Gf V → W)) (ρ : Representation ℂ G M.H) : Prop :=
  ∀ g x, IsTranslate V β L (eG g) (M.e x) (M.e (ρ g x))

variable {V β L}

end Space

def Commutes {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsPosReal (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

variable {D : D7}




end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

end
end
