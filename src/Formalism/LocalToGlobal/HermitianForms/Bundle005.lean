module

public import Formalism.LocalToGlobal.HermitianForms.Bundle004
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

def latCrd (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : letI := D.host.cmStar; Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  L.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

theorem clsCrd_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c = latCrd D i hi (D.clsLat u i c) := rfl

def badQ (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  badG D ∪ (Q : Set (HeightOneSpectrum (𝓞 D.host.F)))

variable {D : D7}



structure LevelChart (D : D7) (T : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (i : ℕ) (hi : i ≤ D.R.m) {cl : Type}
    (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) where
  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad

  y : cl → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, stab c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

def ClsTied.toChart {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) :
    LevelChart D (D.mem u).A.T (badG D) i hi ((D.mem u).C.stab i) (clsCrd D u i hi) where
  lev := K.lev
  y := K.y
  y_bij := K.y_bij
  y_lat := K.y_lat
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def lamTG (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW (M.lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)



structure ValuationCompatibleChart {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
    (okW : D.what₂.places.Pl → Prop) {Ch : Type} (chOf : C.cls i → Ch) {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop where

  Fi : ∀ φ : C.cls i → C.Y i → ℂ, φ ∈ M.Fi i ↔
    ∀ β, (fun (c : {c // chOf c = β}) z => φ c.1 (eY.symm z)) ∈ FiC (K β).lev (embT D) (lamTG M i) (K β).y

  rat : ∀ φ : C.cls i → C.Y i → ℂ, (∃ x, M.emb i x = φ) ↔
    φ ∈ M.Fi i ∧ ∀ c, ∃ P ∈ RatSpan D (M.lam i), ∀ z, φ c z = fnOf _ (shiftOf (lamTG M i)) 1 P (eY z)

  lat : ∀ w, okW w → ∀ x : (M.lat i).V, x ∈ M.S i w ↔
    ∀ (c : C.cls i) (B : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (lat c)) B →
      ∃ P ∈ IntSpan D w (M.lam i),
        ∀ z, M.emb i x c z =
          fnOf _ (shiftOf (lamTG M i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (eY z)

def IpVTieG {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi) : Prop :=
  ∀ c (o : Fr D i hi), o.IsON → ∀ P ∈ CSpan (M.lam i), ∀ Q ∈ CSpan (M.lam i),
    M.ipV i c
      (fun z => fnOf _ (shiftOf (lamTG M i)) (fun τ => (o.1 τ)⁻¹) P (eY z))
      (fun z => fnOf _ (shiftOf (lamTG M i)) (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
    nfAll (M.lam i) Q P

def NormTieG {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (M.lat i).V)
    (Pc : C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, M.emb i x c z =
      fnOf _ (shiftOf (lamTG M i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (M.lat i).b (M.lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, (C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamTG M i) τ)) *
          (nfAll (M.lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re



structure DilationCompatibleChart {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    {Ch : Type} (chOf : C.cls i → Ch) {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop where
  ch : ∀ v a c, chOf (M.dil i v a c) = chOf c
  dil : ∀ v (a : (A.Fv v)ˣ) (k : ℤ), (k : A.Fv v) = a → ∀ β (c : {c // chOf c = β}) δ,
    IsDia (K β).lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' ((K β).y ⟨M.dil i v a c.1, (ch v a c.1).trans c.2⟩) : Cls (K β).lev) = Quotient.mk'' ((K β).y c * δ)
  dilT : ∀ v (a : (A.Fv v)ˣ) (k : ℤ), (k : A.Fv v) = a → ∀ β (c : {c // chOf c = β}) δ,
    IsDia (K β).lev (eV v).1 (eV v).2 k δ → ∀ g ∈ AdFun (K β).lev (embT D),
    M.dilT i v a c.1 (fun z => g ((K β).y ⟨M.dil i v a c.1, (ch v a c.1).trans c.2⟩) (eY z)) =
      fun z => g ((K β).y c * δ) (eY z)

end Gen

end Formalism.L2.Forms
end
end

section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def sgTG : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW (M.sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)



structure ClassesAtPrimes (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) where
  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad

  y : M.clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : M.clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)

  stabI : ∀ c, M.stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

variable {M}



structure ValuationAtPrimes {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad) (okW : D.what₂.places.Pl → Prop) where

  sg : ∀ τ (i : Fin (D.R.N D.R.m - 1)),
    ((M.sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i

  eW : P.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ)

  ptC : ∀ z, z ∈ M.ptC ↔ eW z ∈ FiC K.lev (embT D) (sgTG M) K.y

  ipP : ∀ (o : FrP D), o.IsON → ∀ (z z' : P.Wrow)
    (Pc Qc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    (∀ c, Pc c ∈ CSpan M.sg) → (∀ c, Qc c ∈ CSpan M.sg) →
    (∀ c, eW z c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Pc c)) →
    (∀ c, eW z' c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Qc c)) →
    M.ipP z z' = ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll M.sg (Qc c) (Pc c)

  rat : ∀ z, (∃ x, M.ptEmb x = z) ↔
    z ∈ M.ptC ∧ ∀ c, ∃ Pc ∈ RatSpan D M.sg, eW z c = fnOf _ (shiftOf (sgTG M)) 1 Pc

  lat : ∀ w, okW w → ∀ x : M.ptLat.V, x ∈ M.SP w ↔
    ∀ (c : M.clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (K.lat c : Set _) B →
      ∃ Pc ∈ IntSpan D w M.sg, eW (M.ptEmb x) c =
        fnOf _ (shiftOf (sgTG M)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) Pc

def NormPTieG {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
    (W : ValuationAtPrimes K okW) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : M.ptLat.V)
    (Pc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW (M.ptEmb x) c =
      fnOf _ (shiftOf (sgTG M)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt M.ptLat.b M.ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgTG M) τ)) *
          (nfAll M.sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

end Gen

def ClsPTied.toG {u : D.what₂.Word} (K : ClsPTied u) : ClassesAtPrimes (D.fm u) (badG D) where
  lev := K.lev
  y := K.y
  y_bij := K.y_bij
  lat := K.lat
  y_lat := K.y_lat
  lat_fin := K.lat_fin
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

end Formalism.L2.Forms

end
end
