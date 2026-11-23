module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong TensorProduct

namespace GlobalTheory.CongPhi

def phiSum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} (x : WD h) (σ : Weil h) (n : ℕ) : ℂ :=
  ((x.charPol σ).roots.map (· ^ n)).sum

def JointApprox {k Γ : Type} [NormedField k] [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k))
    (S : ℕ → k) (s : (Γ →* GL (Fin a) k) → ℕ → k) : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ (t : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k),
    (t : Set (Γ →* GL (Fin a) k)) ⊆ C ∧ (∀ g : Γ, ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ ≤ ε) ∧
      ∀ j ≤ n, ‖S j - ∑ ρ ∈ t, c ρ * s ρ j‖ ≤ ε

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)



end Local

section Om

variable {l : ℕ} [Fact l.Prime]

def matRep {K : FinExt l} (L : FinExt l) {a : ℕ} (r' : ↥(GK K) →* GL (Fin a) ↥L.1) :
    Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥L.1 ≃ₐ[↥L.1] _) : _ →* _).comp ((Units.coeHom _).comp r')

def IsMod {K : FinExt l} {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) :
    Prop :=
  ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ g).val i j

def CrysLe (P : LocPrime l) (K : FinExt l) {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (N : ℕ) : Prop :=
  ∃ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1), IsMod ρ L r' ∧ Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (matRep L r') ∧
    Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD K) (matRep L r') ≤ Formalism.WeaklyAdmissibleFiltrations.FilV (P.PD K) (LL := ↥L.1) (V := Fin a → ↥L.1) (-(N : ℤ)) ∧
    Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD K) (matRep L r') ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV (P.PD K) (LL := ↥L.1) (V := Fin a → ↥L.1) ((N : ℤ) + 1) = ⊥


end Om

def ClosedPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w),
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O)
      (hBw : Pst.Induces Bw),
    ∀ (J : (E →+* Qbar l) → Multiset ℤ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ C : Set (_root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)),
      (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (J τ)) →
    ∀ (σ : Weil hA) (S : ℕ → Qbar l),
      JointApprox r C S (fun ρ n => ι.symm (phiSum (wdAt P ι Bw hA hBw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) σ n)) →
      ∀ n : ℕ, phiSum (wdAt P ι Bw hA hBw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) σ n = ι (S n)

end GlobalTheory.CongPhi

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GoodCusp (y : IrrGL (k := k)) : Prop :=
  y.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) ∧
    ∃ (y₀ : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), fixed y₀.rep (KOne k (Fin y₀.1)) ≠ ⊥ ∧ y = y₀.tw χ hχ)

def Good (x : IrrGL (k := k)) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, GoodCusp y

def Toral (x : IrrGL (k := k)) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, y.1 = 1

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

variable (h) in
def TypeLaw (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∀ (E' : Type) [Field E'] [NumberField E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      (rc (cls σ)).mono0 ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

structure LawsT (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop where
  dim : ∀ x, (rc x).lpDim = x.1
  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum rc l
  cusp : ∀ x, x.IsCusp → IsIrrWD (rc x)
  nu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s
  absCentral : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖
  twist : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))
  central : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, Good x → HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)
  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) →
    Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc (cls π') = (rc (cls π)).lpDual
  inj : ∀ x y, Good y → rc x = rc y → x = y
  depth : ∀ x, Good x → fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x)
  type : TypeLaw h rc


end GlobalTheory.RecT

end
end
