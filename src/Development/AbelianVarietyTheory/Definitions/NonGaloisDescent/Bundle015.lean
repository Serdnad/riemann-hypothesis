module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Formalism.DoubleCosetMeasures.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TripleGal

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf)

def rk1 {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) : Γ →* GL (Fin 1) K :=
  (Units.map (Matrix.scalar (Fin 1) : K →+* Matrix (Fin 1) (Fin 1) K).toMonoidHom).comp χ


open Classical in
def GalAbove (D : D7) : Prop :=
  ∀ (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l)), IsGaloisRepOf D π l ι r →
    ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsdRAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (D.naut.mono0 (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∃ J : Multiset ℤ, IsJumpsAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ J ∧
          J.map (fun n : ℤ => (n : ℂ)) =
            (D.naut.infG π (ι.toRingHom.comp τ)).map fun z => ((D.R.r : ℂ) - 1) / 2 - z

def CharAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
      IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧ IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype)) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)}

end GlobalTheory.TripleGal

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.ResSel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)


variable (X) in
def IsCj (g g' : GE N) : Prop := ∀ x, g' x = X.cc (g (X.cc.symm x))

def IsDual (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Prop :=
  ∀ g, (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = Tdual i s g

def ResTriv (g : GE N) : Prop :=
  (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) = 1 ∧ IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1

def Small (L : Subgroup (GE N)) (z : GE N) : Prop :=
  IsOpen (L : Set (GE N)) ∧ L.Normal ∧ (∀ g g', IsCj X g g' → (g ∈ L ↔ g' ∈ L)) ∧ (∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ g ∈ L, ResTriv i s g

section Field

variable (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]

def IsRes : Prop := ∀ x ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) K x = 0

def ResIso : Prop :=
  ∃ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A ∧
    ∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)

abbrev red (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Representation K (GE N) (Fin D.R.r → K) := repOn ρ (1 : GE N →* Kˣ) K

variable {i K}

abbrev cl {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) : H1 (red i K ρ) := Submodule.Quotient.mk x

def form {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ')) (g h g' h' : GE N) : K :=
  x.1 g ⬝ᵥ y.1 h - x.1 g' ⬝ᵥ y.1 h'

end Field

def SpanOdd : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ¬ ResIso i s K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ (n n' : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n' → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → LinearIndependent K (fun b => cl (y b)) → ∀ c : Fin n → Fin n' → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → c = 0

def SpanTwo : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A →
      (∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)) →
    ∀ (n : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → (∀ a g g', IsCj X g g' → (y a).1 g' = A.mulVec ((x a).1 g)) →
      ∀ c : Fin n → Fin n → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → ∀ a b, c a b = c b a

def EqDim : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    Module.Finite K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) ∧ Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) ∧
      Module.finrank K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) = Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅)

def Position (M : ℕ) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (φ φ' : Fin R → GE N) : Prop :=
  SlopeTestRemainingChoices X i M ∅ P d ∧ (∃ z L, IsTameInertiaElementAtTwistPrime X i z ∧ Small i s L z ∧ Steps X i M L z P d) ∧
    ∀ a, (∀ g ∈ DecV N (P (.inr a)), ResTriv i s g) ∧ IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧
      IsCj X (φ a) (φ' a)

def FirstHalf : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ', 1 ≤ M → Position i s M P d φ φ' →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ a v, Over (P (.inl a)) v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

def FirstPlace : Prop :=
  ∀ (P : PlE D.host) (z : GE N) (L : Subgroup (GE N)), IsTameInertiaElementAtTwistPrime X i z → Small i s L z →
    (∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1) →
    (∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ v, Over P v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

theorem mod_l_eq_one {M n : ℕ} (hM : 1 ≤ M) (hn : n % (2 * X.l i ^ M) = 1) : n % X.l i = 1 := by
  have hd : X.l i ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  rw [← Nat.mod_mod_of_dvd _ hd, hn, Nat.mod_eq_of_lt (Fact.out : (X.l i).Prime).one_lt]

def Recip : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q →
    ∀ γ γ' : Fin R → GE N, (∀ a, γ a ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))) ∧
      d (.inr a) (γ a) = Multiplicative.ofAdd 1 ∧ IsCj X (γ a) (γ' a)) →
    ∃ c : Fin R → Kˣ, ∀ (x : Z1 (red i K (Tgl i s))) (y : Z1 (red i K ρ)),
      cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
      ∑ a, (c a : K) * form x y (γ a) (φ a) (γ' a) (φ' a) = 0


variable (X) in
def StepAB : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z →
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal → ∀ (A : Finset (PlE D.host)) (R : ℕ) (h : Fin R → GE N),
    (∀ a, h a ∈ H ∧ ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → h a ζ = ζ) →
    ∃ P : Fin R ⊕ Fin R → PlE D.host, SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M U z P (fun q => d (P q)) ∧
      (∀ q v, Over (P q) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧
      ∀ a, ∃ σ g : GE N, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ ∧ g * σ * g⁻¹ * (h a)⁻¹ ∈ U

def Corank {R : ℕ} (φ φ' : Fin R → GE N) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∃ c : Fin R → K,
    ∀ x : Fin (e + 1) → Z1 (red i K (Tgl i s)), (∀ a, cl (x a) ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) →
      (∀ a (y : Z1 (red i K ρ)), cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
        ∑ b, c b * form (x a) y (φ b) (φ b) (φ' b) (φ' b) = 0) → ¬ LinearIndependent K (fun a => cl (x a))

def ResBound : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 4 * D.R.r * R + 2 < X.l i ^ M →
    Position i s M P d φ φ' → IsQ P Q →
    ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))), Computes bkP i s M d Q Φ →
      (Corank bkP i s φ φ' 0 → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m)) ∧
      (Corank bkP i s φ φ' 1 → a = 0 ∨ ∃ b c, ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.adjugate b c →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m))

def ChooseH : Prop :=
  ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L : Subgroup (GE N), IsOpen (L : Set (GE N)) → L.Normal → (∀ s ∈ T, Small i s L z) →
    ∃ (h : Fin R → GE N) (U : Subgroup (GE N)), (∀ a, h a ∈ L) ∧ IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧
      ∀ φ φ' : Fin R → GE N, (∀ a, IsCj X (φ a) (φ' a) ∧ ∃ g, g * φ a * g⁻¹ * (h a)⁻¹ ∈ U) →
        ∀ s ∈ T, Corank bkP i s φ φ' (if nu X i = 0 then 0 else 1)

theorem IsCj.unique {g g' g'' : GE N} (h : IsCj X g g') (h' : IsCj X g g'') : g' = g'' :=
  AlgEquiv.ext fun x => (h x).trans (h' x).symm

def dualRep : GE N →* GL (Fin D.R.r) (X.O0 i) :=
  MonoidHom.toHomUnits
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]
        simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul]
        rw [smul_mul_smul_comm] }

theorem isDual_dualRep : IsDual i s (dualRep i s) := fun _ => rfl

end GlobalTheory.ResSel
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.Prism
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime]

theorem semiBC_of_basis {A B M N J : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (b : Module.Basis J A M)
    (c : Module.Basis J B N) (h : ∀ i, u (b i) = c i) : SemiBC u := by
  intro Q _ _ v
  refine ⟨c.constr B fun i => v (b i), fun x => ?_, fun w hw => c.ext fun i => ?_⟩
  · exact LinearMap.congr_fun (b.ext (f₁ := (c.constr B fun i => v (b i)).comp u) (f₂ := v) fun i => by
      rw [LinearMap.comp_apply, h, Module.Basis.constr_basis]) x
  · rw [Module.Basis.constr_basis, ← h, hw]

def piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) : (J → A) →ₛₗ[f] (J → B) where
  toFun x i := f (x i)
  map_add' x y := funext fun i => map_add f (x i) (y i)
  map_smul' c x := funext fun i => map_mul f c (x i)

theorem piMap_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {J : Type} [DecidableEq J] (i : J) :
    piMap f J (Pi.single i 1) = Pi.single i 1 := by
  ext1 k
  change f (Pi.single (M := fun _ => A) i 1 k) = _
  simp [Pi.single_apply, apply_ite f]

theorem semiBC_piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) [Fintype J]
    [DecidableEq J] : SemiBC (piMap f J) :=
  semiBC_of_basis (Pi.basisFun A J) (Pi.basisFun B J) fun i => by
    rw [Pi.basisFun_apply, Pi.basisFun_apply, piMap_single]

def piFrob {A : Type} [CommRing A] (φ : A →+* A) (d : A) (J : Type) :
    (J → A) →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) (J → A) where
  toFun x := LocalizedModule.mk (piMap φ J x) 1
  map_add' x y := by simp
  map_smul' c x := by
    rw [RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk, LinearMap.map_smulₛₗ]

theorem exists_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A} {y m : M} {k : ℕ}
    (h : IsFrac d (LocalizedModule.mk y 1) m k) : ∃ r : ℕ, d ^ r • d ^ k • y = d ^ r • m := by
  obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 h
  exact ⟨r, by simpa [Submonoid.smul_def] using hr⟩

def unitPow (l : ℕ) (R : Type) [CommRing R] (J : Type) [Fintype J] [DecidableEq J] : FCrys l R where
  M P := J → P.A
  fin _ := inferInstance
  proj _ := inferInstance
  tr f := piMap f.f J
  tr_bc f := semiBC_piMap f.f J
  tr_id _ _ := rfl
  tr_comp _ _ _ := rfl
  Φ P d := piFrob P.D.φ d J
  Φ_bc P d := semiBC_of_basis (Pi.basisFun _ J) ((Pi.basisFun P.A J).ofIsLocalizedModule
    (Localization.Away (d : P.A)) (Submonoid.powers (d : P.A)) (LocalizedModule.mkLinearMap _ _)) fun i => by
      rw [Module.Basis.ofIsLocalizedModule_apply, Pi.basisFun_apply]
      exact congrArg (LocalizedModule.mk · 1) (piMap_single _ i)
  Φ_nat := by
    intro P P' f d d' x m k n j h1 h2
    obtain ⟨r, hr⟩ := exists_of_isFrac h1
    obtain ⟨s, hs⟩ := exists_of_isFrac h2
    refine ⟨r + s, funext fun i => ?_⟩
    have ha : (d : P.A) ^ r * ((d : P.A) ^ k * P.D.φ (x i)) = (d : P.A) ^ r * m i := congrFun hr i
    have hb : (d' : P'.A) ^ s * ((d' : P'.A) ^ j * P'.D.φ (f.f (x i))) = (d' : P'.A) ^ s * n i := congrFun hs i
    have ha' := congrArg f.f ha
    simp only [map_mul, map_pow, f.f_φ] at ha'
    change (f.f d * d') ^ (r + s) * ((d' : P'.A) ^ j * f.f (m i) - f.f d ^ k * n i) = 0
    linear_combination (-(f.f d) ^ s * (d' : P'.A) ^ (r + s + j)) * ha' +
      (f.f d ^ (r + s + k) * (d' : P'.A) ^ r) * hb

def unitPowMap (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] [DecidableEq J]
    (β : Module.Basis J ℤ_[l] T) : (unitPow l ↥(OL F) J).M (ainfObj F) →ₛₗ[(inclW l).comp (ainfId F).toRingHom]
      (WCb l ⊗[ℤ_[l]] T) :=
  (β.baseChange (WCb l)).equivFun.symm.toLinearMap.comp (piMap ((inclW l).comp (ainfId F).toRingHom) J)

theorem unitPowMap_apply (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (x : J → Ainf l) :
    unitPowMap F β x = ∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i := by
  refine ((β.baseChange (WCb l)).equivFun_symm_apply fun i => inclW l (x i)).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one]

theorem sum_frob {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) {d : Ainf l}
    (hd : d ≠ 0) (x m : J → Ainf l) (k r : ℕ)
    (h : ∀ i, d ^ r * (d ^ k * WittVector.frobenius (x i)) = d ^ r * m i) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) =
      ∑ i, inclW l (m i) ⊗ₜ[ℤ_[l]] β i := by

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, frobW_inclW,
    ← mul_left_cancel₀ (pow_ne_zero r hd) (h i), map_mul, map_pow, smul_tmul', smul_eq_mul]

theorem sum_gal {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) (g : GQ l)
    (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x) (x : J → Ainf l) :
    ∑ i, inclW l (Per.σA g (x i)) ⊗ₜ[ℤ_[l]] β i =
      TensorProduct.map (galW l g).toLinearMap ρ (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, galW_inclW, hρ]

theorem unitPowMap_frob (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (d : Ainf l) (hd : d ≠ 0) (x m : J → Ainf l) (k : ℕ)
    (h : IsFrac d (LocalizedModule.mk (piMap WittVector.frobenius J x) 1) m k) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (unitPowMap F β x) =
      unitPowMap F β m := by
  obtain ⟨r, hr⟩ := exists_of_isFrac h
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_frob β hd x m k r fun i => congrFun hr i

theorem unitPowMap_gal (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (g : GQ l) (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x)
    (x : J → Ainf l) : unitPowMap F β (fun i => Per.σA g (x i)) =
      TensorProduct.map (galW l g).toLinearMap ρ (unitPowMap F β x) := by
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_gal β g ρ hρ x

theorem realises_unitPow (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (ρ : ↥(GK F) → (T →ₗ[ℤ_[l]] T)) (hρ : ∀ g x, ρ g x = x) :
    Realises F (unitPow l ↥(OL F) J) (ainfObj F) (ainfId F) T ρ (unitPowMap F β) := by
  have hAinf : IsAinf F (ainfObj F) (ainfId F) := by
    refine ⟨fun _ => rfl, fun _ => Iff.rfl, ?_⟩
    intro x a h
    have hθ : ainfQuot l (Ideal.Quotient.mk _ a) = ainfQuot l ((ainfQuot l).symm (intToOC F x)) :=
      congrArg (ainfQuot l) h
    rw [RingEquiv.apply_symm_apply] at hθ
    exact congrArg Subtype.val hθ
  refine ⟨hAinf, ?_, ?_, ?_⟩
  · exact SemiBC.comp_equiv (semiBC_piMap ((inclW l).comp (ainfId F).toRingHom) J)
      (β.baseChange (WCb l)).equivFun.symm
  · intro d hd x m k h
    exact unitPowMap_frob F β d.1 hd x m k h
  · intro g x
    exact unitPowMap_gal F β g (ρ g) (hρ g) x

end GlobalTheory.BKReal
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E) in
def pFin : Ad E →+* Af E := RingHom.snd (InfiniteAdeleRing E) (Af E)

def secRow {R : Type*} [CommRing R] (y : Fin a → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if (i : ℕ) + 1 = a then y j else (1 : Matrix (Fin a) (Fin a) R) i j


open Classical in
def secInv (y : Fin a → Cinf E) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (secRow y).det then (Matrix.nonsingInvUnit (secRow y) h)⁻¹ else 1

def rowAct (ξ : Fin a → E) (g : GA E a) : Fin a → Ad E :=
  Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ i)) (g : Matrix (Fin a) (Fin a) (Ad E))


variable (E) in
def natLat (N : ℕ) : Set (Af E) :=
  {x | ∃ z : Af E, (∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧ x = (N : Af E) * z}


open Classical in
def indN (N : ℕ) (y : Fin a → Af E) : ℂ :=
  if ∀ i : Fin a, y i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ natLat E N then 1 else 0


variable (E a) in
def detPow (x : ℝ) (g : GA E a) : ℝ := ‖((chiDet a (GlobalTheory.HeckeGal.Model.absPow E x) g : ℂˣ) : ℂ)‖

def Psi (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  φ (g * infGL E a (secInv fun i => pInf E (y i))) * starRingEnd ℂ (φ' (g * infGL E a (secInv fun i => pInf E (y i)))) *
    Φ (fun i => pInf E (y i)) * indN N (fun i => pFin E (y i))

def thetaSum (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (g : GA E a) : ℂ :=
  ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, Psi φ φ' Φ N g (rowAct ξ.1 g)

def Zint (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∫ g in 𝓕, thetaSum φ φ' Φ N g * (detPow E a x g : ℂ) ∂μ

end GlobalTheory.RSJ
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll

variable (D : D7)

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)



end GlobalTheory.SupLaw.Model

end
end
