module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal

namespace GlobalTheory.TwSys

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsTameInertiaElementAtTwistPrime (i : X.Tw) (z : GE N) : Prop :=
  ∃ v ∈ X.pD i, ∃ A : ValuationSubring N.Om, IsPlaceOver A v ∧ z ∈ Ine (F := D.host.E) A ∧
    IsUnit (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) ∧
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal →
      ∃ n : ℕ, Nat.Coprime n (X.l i * Ideal.absNorm v.asIdeal) ∧ z ^ n ∈ U

def Over (P v : PlE D.host) : Prop := v = P ∨ IsConjPl D.host P v

def GoodChar (i : X.Tw) (M : ℕ) (P : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) : Prop :=
  IsOpen (d.ker : Set (GE N)) ∧ AntiHom X.cc d ∧ TrivAbove d (X.l i) ∧
    (∀ v, ¬ Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, d σ = 1) ∧
    (∀ v, Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := D.host.E) A, d σ = c)

def AdmFam (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  IsOpen (H : Set (GE N)) ∧ H.Normal ∧
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) ∧
    ∀ P, P ∉ S → IsSplitPl D.host P → DecV N P ≤ H → GoodChar X i M P (d P)

def SlopeTestRemainingChoices (i : X.Tw) (M : ℕ) (A : Finset (PlE D.host)) {ι : Type} (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ q v, Over (P q) v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % (2 * X.l i ^ M) = 1) ∧
    (∀ q q', Over (P q) (P q') → q = q') ∧ ∀ q, GoodChar X i M (P q) (d q)

def Steps (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (z : GE N) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ a (σ : GE N), IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ H) ∧
    ∀ a b (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (.inl b) σ = Multiplicative.ofAdd (if a = b then 1 else 0)

def IsQ {ι : Type} (P : ι → PlE D.host) (Q : Finset (PlE D.host)) : Prop := ∀ v, v ∈ Q ↔ ∃ q, Over (P q) v

abbrev Del (i : X.Tw) (M : ℕ) (ι : Type) : Type := Multiplicative (ι → ZMod (X.l i ^ M))

abbrev abelian₂ (i : X.Tw) (M : ℕ) (ι : Type) : Type := MonoidAlgebra (X.O0 i) (Del X i M ι)

def delAll (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* Del X i M ι where
  toFun g := Multiplicative.ofAdd fun q => Multiplicative.toAdd (d q g)
  map_one' := by simp; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl


open Classical in
def toLam (i : X.Tw) (M : ℕ) (ι : Type) : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] abelian₂ X i M ι :=
  MvPolynomial.aeval fun q => MonoidAlgebra.of (X.O0 i) (Del X i M ι) (Multiplicative.ofAdd (Pi.single q 1)) - 1

def repOn {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O) (κ : G →* Λˣ)
    (B : Type) [AddCommGroup B] [Module Λ B] : Representation Λ G (Fin r → B) where
  toFun g := ((κ g : Λˣ) : Λ) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))
  map_one' := by simp [matAct_one]
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul, matAct_mul]
    rw [smul_mul_smul_comm]

variable {X} (bkP : BKPh X)


open Classical in
def bkOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (v : PlE D.host) : Submodule Λ (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span Λ {x | ∃ (z : Z1 ((repOn ρ κ B).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin r → X.O0 i) (b : B),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) ∧
      (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin r → B) g a = algebraMap (X.O0 i) Λ (y g a) • b) ∧
      x = Submodule.Quotient.mk z}
  else ⊥

def selOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (Q : Finset (PlE D.host)) : Submodule Λ (H1 (repOn ρ κ B)) :=
  Formalism.GaloisCohomology.SelAll (repOn ρ κ B) N.plOm
    (Formalism.GaloisCohomology.bkCond (repOn ρ κ B) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ B))

def delInv (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* (abelian₂ X i M ι)ˣ :=
  ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits.comp (delAll X i M d))⁻¹

def Computes (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) : Prop :=
  ∃ e : ∀ (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B],
      (∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) →
      (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[abelian₂ X i M ι] ↥(selOn bkP i (Tgl i s) (delInv i M d) B Q)),
    ∀ (B B' : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module (abelian₂ X i M ι) B'] [TopologicalSpace B'] [DiscreteTopology B']
      (hB : ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) (hB' : ∀ b : B', ∃ n : ℕ, (X.l i ^ n) • b = 0)
      (f : B →ₗ[abelian₂ X i M ι] B') (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ)))
      (z : Z1 (repOn (Tgl i s) (delInv i M d) B)) (z' : Z1 (repOn (Tgl i s) (delInv i M d) B')),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e B hB x).1 = Submodule.Quotient.mk z → (e B' hB' x').1 = Submodule.Quotient.mk z'

def valE (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) : ℝ≥0∞ :=
  ((IsDiscreteValuationRing.addVal R x : ℕ∞) : ℝ≥0∞) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ≥0∞)

def SelPoly (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (F : MvPolynomial ι (X.O0 i)) : Prop :=
  ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ) (ψ : GE N →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
    (∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
    sLen bkP i s k Q ψ =
      valE (X.Ok i k) (X.l i) (MvPolynomial.eval₂ (phiK X i k) (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) F)

def GalHyp (i : X.Tw) (s : X.Sig i) : Prop :=
  IsotypicValuationAtRing bkP i s ∧ ValuationStabilityAtRing X i s ∧ SelfDual i s ∧ NoJump bkP i s ∧ True ∧ Gen.adm3 D ∧ 100 ≤ D.R.r

end GlobalTheory.TwSys

end
end

section

noncomputable section

namespace GlobalTheory.TripleGal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def rd (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ) : X.O0 i →+* ℂ :=
  ι.comp (algebraMap (X.O0 i) (FractionRing (X.O0 i)))

def cj (D : Formalism.BasicNotions.D7) : D.host.E →+* D.host.E :=
  (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom

def UnrRho (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v, v ∉ placesOver D.host.E (X.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, X.rhoS i s σ = 1

def HodgeL (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)), ∀ r ∈ ({X.rhoS i s, Tgl i s} : Set _),
    (bkP.br i v hv).IsdRW (D.loc (X.l i)) (r.comp (DecV N v).subtype) ∧
    ((∀ k, X.l i ≠ D.host.g k) → (bkP.br i v hv).IsCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)) ∧
    (bkP.br i v hv).IsPotCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)

def NoInv (i : X.Tw) (M : GE N → Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ x : Fin D.R.r → FractionRing (X.O0 i), (∀ g ∈ Dec (F := D.host.E) A,
      ((M g).map (algebraMap (X.O0 i) (FractionRing (X.O0 i)))).mulVec x = x) → x = 0

def NegCount (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v v' (hv : v ∈ placesOver D.host.E (X.l i)) (hv' : v' ∈ placesOver D.host.E (X.l i))
    (τ : EmbV bkP i v hv) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' →
    dimD bkP i v hv (Tgl i s) τ + dimD bkP i v' hv' (Tgl i s) τ' =
      dimFil0 bkP i v hv (Tgl i s) τ + dimFil0 bkP i v' hv' (Tgl i s) τ' + D.R.r

def Pure (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ) : Prop :=
  ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl (X := X) i → ∀ A : ValuationSubring N.Om, IsPlaceOver (F := D.host.E) A v →
    ∀ σ : GE N, IsFrob (F := D.host.E) A (normV v) σ → ∀ z : ℂ,
      ((Tmat i s σ).charpoly.map (rd i ι)).IsRoot z → ‖z‖ = ((normV v : ℕ) : ℝ) ^ ((1 - (D.R.t : ℝ)) / 2)

def ReadEmb (bkP : BKPh X) (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ) : Prop :=
  ∀ (x : D.host.E) (n d : X.O0 i), IsFrac bkP i v hv (τ (cE bkP i v hv x)) n d → rd i ι d * τc x = rd i ι n

def JumpsAre (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ)
    (J : (D.host.E →+* ℂ) → Multiset ℤ) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ), ReadEmb bkP i ι v hv τ τc →
    ∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = ((J τc).count a : ℤ)

def GoodJ (D : Formalism.BasicNotions.D7) (J : (D.host.E →+* ℂ) → Multiset ℤ) : Prop :=
  ∀ τc, Multiset.card (J τc) = D.R.r ∧ J (τc.comp (cj D)) = (J τc).map (fun a => (D.R.t : ℤ) - 1 - a) ∧
    ∀ a ∈ J τc, a < -1 ∨ (D.R.t : ℤ) < a

def CharDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ g g' : GE N, (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    (Tdual i s g').charpoly = ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).charpoly

def FrobDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → (∀ P', IsConjPl D.host P P' → P' ∉ X.S0 i) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver (F := D.host.E) A P →
    ∀ g g' : GE N, IsFrob (F := D.host.E) A (normV P) g → (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    (Tdual i s g').charpoly = ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).charpoly

def HkFrob (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ σ : GE N, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ⁻¹ →
    ∀ k, k ≤ D.R.r → (-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2) * X.hEig i s k P =
      algebraMap (X.O0 i) (X.O i)
        ((((((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s σ).charpolyRev).coeff k)


def HkSat (A : NAut N) (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ) (π : A.CG D.R.r) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ k, k ≤ D.R.r → ∃ h : X.O0 i,
    X.hEig i s k P = algebraMap (X.O0 i) (X.O i) h ∧
    rd i ι h = ((normV P : ℕ) : ℂ) ^ (((k : ℂ) * ((D.R.r : ℂ) - k)) / 2) *
      ((A.frobEig (A.locG π P)).map fun a => a⁻¹ * ((normV P : ℕ) : ℂ) ^ (-((D.R.r : ℂ) + D.R.t) / 2)).esymm k

structure RowFacts (A : NAut N) (i : X.Tw) (π₁ π : A.CG D.R.r) : Prop where
  unr₁ : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → A.unr (A.locG π₁ w)
  mono₁ : ∀ w, A.mono0 (A.locG π₁ w)
  unr : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ X.pD i → A.unr (A.locG π w)
  mono : ∀ w, A.mono0 (A.locG π w)
  csd : A.csd π
  ralg : A.ralg π
  anti : ∀ τc, A.infG π (τc.comp (cj D)) = (A.infG π τc).map fun z => -z
  window : ∀ τc, ∀ z ∈ A.infG π τc, ∀ a : ℤ, (a : ℂ) = -z + ((D.R.t : ℂ) - 1) / 2 → a < -1 ∨ (D.R.t : ℤ) < a

end GlobalTheory.TripleGal

end
end
