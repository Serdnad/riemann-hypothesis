module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ThetaSchur (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T')) (𝓕 : Set (WO S T')), IsCovolOne (ratL T' S) μ 𝓕 →
    ∀ L : Module.End ℂ (WO S T' → ℂ), (∀ f, IsThetaFunO ψ S T' f → IsThetaFunO ψ S T' (L f)) →
      (∃ C : ℝ, ∀ f, IsThetaFunO ψ S T' f → nrm2 μ 𝓕 (L f) ≤ C * nrm2 μ 𝓕 f) →
      (∀ w f, IsThetaFunO ψ S T' f → L (heisO ψ S T' w f) = heisO ψ S T' w (L f)) →
      ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T' f → L f = c • f

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := levG _ (R.βW i) (R.datWp i R.triv)

def coef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) / thetaIP μ 𝓕 (R.vP i t) (R.vP i t)

def jointVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)

def IsUnitVec (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1

def val (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : (R.HW i (sg0 D A)).H) :
    GA D (Wc D i) → ℂ :=
  (R.HW i (sg0 D A)).e x fun ρ => v ρ

def AdjFormula (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ v, IsUnitVec R i v → ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W),
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t)

def LevFix (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ k ∈ levW R i, ∀ P, R.ωP i t (1, k) (R.ptP i t P) = R.ptP i t P

def FactInf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), ∀ P P',
    thetaIP μ 𝓕 (R.ωP i t (1, u * γ) (R.ptP i t P)) (R.ptP i t P') =
      thetaIP μ 𝓕 (R.ωP i t (1, u) (R.ptP i t P)) (R.ptP i t P') * coef R i t μ 𝓕 γ

def RealLow (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ

def VecNe (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 ∧
    ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0

def trPair (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) (x y : (R.HW i (sg0 D A)).H) : ℂ :=
  ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
    (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y))

def FinSum (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

def TrivAt (V : HSp D) (f : AE D) (g : GA D V) : Prop := ∀ a b, f * (mt V g - 1) a b = 0

def IsFinIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) : Prop :=
  ∃ ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε

def FinMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k →
      coef R i t μ 𝓕 (γ * k) = coef R i t μ 𝓕 γ * coef R i t μ 𝓕 k

def BadSupp (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f →
    ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → coef R i t μ 𝓕 k = 0

def latIndex (W : HSp D) (g : GA D W) : ℕ :=
  ((Formalism.L2.NTheta.LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).relIndex (Formalism.L2.NTheta.LamHat W)

def GoodMod (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k →
      ‖coef R i t μ 𝓕 k‖ ^ 2 * (latIndex (Wc D i) k : ℝ) ^ (Vc D i).rank = 1

def IndexSum (W : HSp D) (n : ℕ) : Prop :=
  ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
    ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') →
      ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ s v

def LocSmall (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 →
    ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
      ∀ C : Finset (GA D (Wc D i)), (∀ g ∈ C, SuppF (Wc D i) f g ∧ g ∉ levW R i) →
        (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ levW R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v

def LevProd (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  levW R i ≤ GfC (Wc D i) ∧ (∀ k ∈ levW R i, levChi _ (R.βW i) (R.datWp i R.triv) k = 1) ∧
  ∃ cmp : HeightOneSpectrum (𝓞 D.host.F) → (GA D (Wc D i) →* GA D (Wc D i)),
    (∀ v f, IsFinIdem D v f → ∀ g, SuppF (Wc D i) f (cmp v g) ∧ TrivAt (Wc D i) f (g * (cmp v g)⁻¹)) ∧
    (∀ g ∈ GfC (Wc D i), (g ∈ levW R i ↔ ∀ v, cmp v g ∈ levW R i) ∧ {v | cmp v g ∉ levW R i}.Finite)

def TransLaws (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∃ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) ∧
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∀ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) →
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C →
      ∀ y, ∃ y', (R.HW i (sg0 D A)).e y' = heckeOn (R.MW i (sg0 D A)) C ((R.HW i (sg0 D A)).e y) ∧
        ∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' = ∑ δ ∈ C, trPair R i (γ * δ) x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ k ∈ levW R i, ∀ k' ∈ levW R i, ∀ x y, trPair R i (k * γ * k') x y = trPair R i γ x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ⁻¹ x y = star (trPair R i γ y x)) ∧
  ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ

end GlobalTheory.RawLift

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt

abbrev BCRel : Type 1 :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)),
    IrrGL (k := v.adicCompletion K) → IrrGL (k := u.adicCompletion L) → Prop

section Cyc

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def CycAt (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) : Prop :=
  IsGalois K L ∧ (Module.finrank K L).Prime ∧ u.under (𝓞 K) = v ∧
    ∀ u' : HeightOneSpectrum (𝓞 L), u'.under (𝓞 K) = v → u' = u

def Conj {u : HeightOneSpectrum (𝓞 L)} (s : L ≃ₐ[K] L) (Y Y' : IrrGL (k := u.adicCompletion L)) : Prop :=
  ∃ i : u.adicCompletion L ≃+* u.adicCompletion L, Continuous i ∧
    (∀ x : L, i (algebraMap L _ x) = algebraMap L _ (s x)) ∧ RepRel i Y Y'


variable (L) in
def KillsNorms {v : HeightOneSpectrum (𝓞 K)} (η : (v.adicCompletion K)ˣ →* ℂˣ) : Prop :=
  ∀ (z : L) (y : (v.adicCompletion K)ˣ), (y : v.adicCompletion K) = algebraMap K _ (Algebra.norm K z) → η y = 1

variable (K) in
def IsOrbitProd {u : HeightOneSpectrum (𝓞 L)} (Y : (L ≃ₐ[K] L) → IrrGL (k := u.adicCompletion L))
    (X : IrrGL (k := u.adicCompletion L)) : Prop :=
  (∀ s, (Y s).IsCusp ∧ Conj s (Y 1) (Y s)) ∧ Function.Injective Y ∧
    ∃ (g : ℕ) (e : Fin g ≃ (L ≃ₐ[K] L)) (hd : ∑ i, (Y (e i)).1 = X.1), Nonempty (X.rep.Equiv (prodIrr (fun i => Y (e i)) hd))

end Cyc

section Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}



end Loc

structure LocalBCAt {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)}
    (B : IrrGL (k := v.adicCompletion K) → IrrGL (k := u.adicCompletion L) → Prop) : Prop where

  ex : ∀ x, x.IsCusp → ∃! X, B x X

  shape : ∀ x X, x.IsCusp → B x X → X.IsCusp ∨ ((∃ Y, IsOrbitProd K Y X) ∧ ∀ η hη, KillsNorms L η → x.tw η hη = x)

  desc : ∀ X, X.IsCusp → (∀ s : L ≃ₐ[K] L, Conj s X X) → ∃ x, x.IsCusp ∧ B x X

  ind : ∀ Y : (L ≃ₐ[K] L) → IrrGL (k := u.adicCompletion L), (∀ s, (Y s).IsCusp ∧ Conj s (Y 1) (Y s)) → Function.Injective Y →
    ∃ x X, x.IsCusp ∧ B x X ∧ IsOrbitProd K Y X

  fib : ∀ x x' X, x.IsCusp → x'.IsCusp → B x X → B x' X → ∃ η hη, KillsNorms L η ∧ x' = x.tw η hη

def LocalBC (BC : BCRel) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)), CycAt v u → LocalBCAt (BC K L v u)

def StrongBC (BC : BCRel) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)), CycAt v u →
    ∀ (n c : ℕ) (π : CuspSub K n) (m : Fin c → ℕ) (P : ∀ i, CuspSub L (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) →
    UpperTheory.V.Published.WeakBC (CG.mk π).HasSat
      (fun w B => ∃ B' : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (B' i)) ∧ B = ∑ i, B' i) →
    ∀ (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : ∀ i, SmIrr (GL (Fin (m i)) (u.adicCompletion L))),
    π.IsLocComp v τ → (∀ i, (P i).IsLocComp u (T i)) →
    ∀ (t : ℕ) (x : Fin t → IrrGL (k := v.adicCompletion K)) (X : Fin t → IrrGL (k := u.adicCompletion L))
      (S : Fin t → Multiset (IrrGL (k := u.adicCompletion L))) (S' : Fin c → Multiset (IrrGL (k := u.adicCompletion L))),
    HasSupport τ.ρ (Finset.univ.val.map x) → (∀ j, BC K L v u (x j) (X j) ∧ HasSupport (X j).rep (S j)) →
    (∀ i, HasSupport (T i).ρ (S' i)) → ∑ i, S' i = ∑ j, S j

section Ind

variable (K : Type) {L Ω : Type} [Field K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]


end Ind

end GlobalTheory.FunExt

end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.FormDict

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure FinIso where
  κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L
  left : ∀ x : L, κ (x ⊗ₜ 1) = algebraMap L _ x
  right : ∀ (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))), NG.OverPl w v →
    ∃ i : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L, Continuous i ∧
      ∀ a : FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L), κ (1 ⊗ₜ a) w = i (a v)
  j : GAf L n →* UA L n
  fin : ∀ x, j x ∈ finU (E := L) (n := n)
  loc : ∀ (x : GAf L n) (w : HeightOneSpectrum (𝓞 L)) (s t : Fin n),
    (cLoc w (j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) w
  onto : ∀ y ∈ finU (E := L) (n := n), ∃ x, j x = y

variable {L n}

def Dict (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)) : Prop :=
  IsAutRepU U ∧ U.map (LinearMap.funLeft ℂ ℂ F.j) =
    Submodule.span ℂ {φ | ∃ f ∈ π.S, ∃ lam : Module.Dual ℂ π.W, φ = fun x => lam (f x)}

end GlobalTheory.FormDict

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ)

structure Cover : Type 1 where

  c' : Coeff T.Q.l
  hle : T.Q.c.F ≤ c'.F

  d : DeltaDat (T.Q.Xo j) c' 0

  σ₂ : d.c₂.F →+* ℂ
  U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r
  dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r
  cc₂ : U₂.Comp → ℂ

variable {T j σ}

namespace Cover

variable (C : Cover T j σ)

def inc : T.Q.c.F →+* C.d.c₂.F := (C.d.eF : C.c'.F →+* C.d.c₂.F).comp (incF T.Q.c C.c' C.hle)

def rd (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂) (rdU C.U₂ f₂)

def IsPull (f : T.R j) (f₂ : Rul C.d.Xo₂ C.d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [Algebra T.Q.c.F k] [Algebra C.c'.F k] [Algebra C.d.c₂.F k] (h : AlgOver T.Q.c C.c' C.hle k),
    (∀ x : C.c'.F, algebraMap C.d.c₂.F k (C.d.eF x) = algebraMap C.c'.F k x) →
    ∀ (y₂ : FrPt C.d.Xo₂ C.d.c₂ k) (y : FrPt (T.Q.Xo j) C.c' k), FrOver C.d y₂ y →
      evR C.d.Xo₂ C.d.c₂ f₂ y₂ = evR (T.Q.Xo j) T.Q.c f (y.res C.hle h)

def IsUnif : Prop :=
  C.d.IsLev ∧ C.d.l₂.A = 1 ∧ C.σ₂.comp C.inc = σ ∧ IsUnf C.U₂ ∧
    (∀ h, (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom) ∧
    ∃ (hr : (T.V j σ).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : FamilyUnif C.d.Xo₂ (C.σ₂.comp (IntermediateField.inclusion C.d.c₂.le).toRingHom)
        (fun i => relab C.d.c₂ C.σ₂ (e i).1))
      (ik : C.U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (C.U₂.X k).Λ)
      (th : ∀ k, (C.U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k, ModelW (T.V j σ) hr (C.U₂.X k)) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat C.U₂ (T.V j σ) hr C.dict₂ (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th
          (T.x₀ j σ)

def IsPinned (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  CUnit C.cc₂ ∧ ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → C.rd a f₂ = T.phiJ j σ a f

def cuspSec (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul C.d.Xo₂ C.d.c₂) :=
  {f₂ | f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n ∧ rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n)}

def ratForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (GA D (T.V j σ) → ℂ) := C.rd a '' C.cuspSec a n

def intForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) :
    Set (GA D (T.V j σ) → ℂ) :=
  C.rd a '' {f₂ | f₂ ∈ C.cuspSec a n ∧ ∀ la ∈ S, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f₂}

theorem intForms_subset (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) :
    C.intForms a n S ⊆ C.ratForms a n := Set.image_mono fun _ h => h.1

end Cover

variable (T j σ)

def baseForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (GA D (T.V j σ) → ℂ) :=
  T.phiJ j σ a '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}

def baseInt (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) :
    Set (GA D (T.V j σ) → ℂ) :=
  T.phiJ j σ a '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) ∧
    ∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f}

end GlobalTheory.CoverRead
end
end
