module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GLp.Model

open Polynomial GlobalTheory.GLq GlobalTheory.GLp
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem red_surjective (n : ℕ) : Function.Surjective (red g n) := by
  intro x
  have hs : Function.Surjective (PadicInt.toZMod (p := g)) := ZMod.ringHom_surjective _
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun i j => Function.surjInv hs ((x : Mt g n) i j)
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (x : Mt g n) := by
    ext i j; exact Function.surjInv_eq hs _
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 x.isUnit).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).2 hd).unit, ?_⟩
  ext i j
  exact congrFun (congrFun hM i) j

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero, MonoidHom.mem_ker]

theorem lift_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (k : GL (Fin n) ℤ_[g]) : π (lift g n (red g n k)) v = π (inc g n k) v := by
  have h := Function.invFun_eq (f := red g n) ⟨k, rfl⟩
  have h2 := (mem_principalCongruenceFixedVectors_iff π v).1 hv (k⁻¹ * Function.invFun (red g n) (red g n k)) (by simp [h])
  have : lift g n (red g n k) = inc g n k * inc g n (k⁻¹ * Function.invFun (red g n) (red g n k)) := by
    simp [lift]
  rw [this, map_mul, Module.End.mul_apply, h2]

theorem isIrrRep_iff {G : Type} [Group G] (π : Representation ℂ G V) : IsIrrRep π ↔ π.IsIrreducible := by
  constructor
  · rintro ⟨hn, h⟩
    haveI : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun e => by
      have : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule e
      exact bot_ne_top this⟩
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun x v hv => W.apply_mem_toSubmodule x hv) with e | e
    · left; exact Subrepresentation.toSubmodule_injective e
    · right; exact Subrepresentation.toSubmodule_injective e
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have : (⊥ : Subrepresentation π) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
      exact bot_ne_top this
    · rcases eq_bot_or_eq_top (⟨W, fun x v hv => hW x v hv⟩ : Subrepresentation π) with e | e
      · left; exact congrArg Subrepresentation.toSubmodule e
      · right; exact congrArg Subrepresentation.toSubmodule e

def chRep {G : Type} [Group G] (φ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun x := (φ x : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

@[simp] theorem chRep_apply {G : Type} [Group G] (φ : G →* ℂˣ) (x : G) (v : ℂ) : chRep φ x v = φ x * v := by
  simp [chRep]

theorem isIrrRep_chRep {G : Type} [Group G] (φ : G →* ℂˣ) : IsIrrRep (chRep φ) :=
  ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

def detRep (n : ℕ) (μ : ℚ_[g]ˣ →* ℂˣ) : Representation ℂ (GL (Fin n) ℚ_[g]) ℂ :=
  chRep (μ.comp Matrix.GeneralLinearGroup.det)

theorem exists_gen (L : LabelDatum g) : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 ∧
    orderOf u = g - 1 := by
  have hp : g.Prime := Fact.out
  have ho := L.gen_order 1 one_pos
  rw [pow_one] at ho
  have h1 : L.gen 1 ^ (g - 1) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hpos : 0 < g - 1 := by have := hp.two_le; omega
  have h2 : L.gen 1 ^ g = L.gen 1 := by
    have : L.gen 1 ^ g = L.gen 1 ^ (g - 1 + 1) := by congr 1; omega
    rw [this, pow_succ, h1, one_mul]
  obtain ⟨c, hc⟩ : ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = L.gen 1 := by
    obtain ⟨m, hm⟩ := (mem_bot_iff_intCast g (Formalism.CyclotomicNorms.Fbar g)).1
      ((Subfield.mem_bot_iff_pow_eq_self (Formalism.CyclotomicNorms.Fbar g) g).2 h2)
    exact ⟨m, by simpa using hm⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc] at h1; simp [hpos.ne'] at h1
  refine ⟨Units.mk0 c hc0, hc, ?_⟩
  rw [← ho, ← hc, ← orderOf_units, Units.val_mk0]
  exact (orderOf_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom (algebraMap (ZMod g) _).injective c).symm

theorem isCharLab_exists (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) : ∃ c, IsCharLab L χ c := by
  obtain ⟨u, hu, ho⟩ := exists_gen L
  have hpos : 0 < g - 1 := by have := (Fact.out : g.Prime).two_le; omega
  haveI : NeZero (g - 1) := ⟨hpos.ne'⟩
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have hprim : IsPrimitiveRoot (T u) (g - 1) := by
    rw [← ho, ← orderOf_injective T hT u]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (χ u : ℂ)) (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ho, pow_orderOf_eq_one]; simp)
  refine ⟨(u ^ m : (ZMod g)ˣ), Units.ne_zero _, fun w hw => ?_⟩
  have : w = u := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hw.trans hu.symm))
  rw [this, ← hm, ← map_pow]; rfl

end GlobalTheory.GLp.Model
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys

def Cheb : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → U.Normal → ∀ (g : G F Ω) (A : Finset (HeightOneSpectrum (𝓞 F))),
  ∃ v, v ∉ A ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
    ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ U ∧ ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U

def OrdHyp (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l M R nmax v : ℕ)
    (f : MvPolynomial (Fin R ⊕ Fin R) O) : Prop :=
  ∃ Dd g : MvPolynomial (Fin R ⊕ Fin R) O,
    f - Dd * g ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧
    IsDiscreteValuationRing.addVal O (g.coeff 0) ≤ v ∧
    ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧
      Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈
        Ideal.span (Set.range fun q =>
          (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def K1 : Prop := ∀ (i : X.Tw) (M : ℕ), 1 ≤ M → ∃ H S d, AdmFam X i M H S d

def PropE (N0 : X.Tw → ℕ) : Prop :=
  ∀ (i : X.Tw) (lam : X.abelian₂ i) (z : GE N), X.NonzeroIndexPlace i → (∃ s, SOk X i lam s) → (∑ δ, X.th i ∅ lam δ) ≠ 0 → IsTameInertiaElementAtTwistPrime X i z →
    ∃ (H : Subgroup (GE N)) (v : ℕ), IsOpen (H : Set (GE N)) ∧ H.Normal ∧
      (v : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) = c0 X i lam + N0 i ∧
      ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d (Q : Finset (PlE D.host)), 1 ≤ M →
        SlopeTestRemainingChoices X i M ∅ P d → Steps X i M H z P d → IsQ P Q →
        ∃ f : MvPolynomial (Fin R ⊕ Fin R) (X.O i), OrdHyp (X.O i) (X.l i) M R 2 v f ∧
          ∀ (k : ℕ) (u : Fin R ⊕ Fin R → (X.Ok i k)ˣ) (ψ' : X.RCG i Q →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
            (∀ g, ψ' (X.art i Q g) = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
            algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
                (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) =
              ((X.l i : ℕ) : FractionRing (X.Ok i k)) ^ N0 i * thEval X i Q lam k ψ'

variable {X} (bkP : BKPh X)

def ThmS : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d
    (Q : Finset (PlE D.host)), 1 ≤ M → SlopeTestRemainingChoices X i M ∅ P d → IsQ P Q →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c)

def SelmerLengthsByDeterminant : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d (Q : Finset (PlE D.host)),
    1 ≤ M → SlopeTestRemainingChoices X i M ∅ P d → IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)),
    Computes bkP i s M d Q Φ → ∀ F, toLam X i M ι F = Φ.det → SelPoly bkP i s M d Q F

def OrdBound (i : X.Tw) (μ : ℕ∞) : Prop :=
  ∀ (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∃ R Dd M₀ : ℕ, ∀ M, M₀ ≤ M →
    ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
        Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤ μ

def ResidualBoundOddPrimes : Prop := ∀ i : X.Tw, nu X i = 0 → OrdBound bkP i 0

def ThmC : Prop :=
  ∀ i : X.Tw, 0 < nu X i → OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i))

def GaloisSideTwistedSelmerAuxiliaryPrimes : Prop :=
  ∀ (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∃ R Dd M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M, M₀ ≤ M →
    ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∃ F, SelPoly bkP i s M (fun q => d (P q)) Q F ∧
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤
          IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def IsCoord (i : X.Tw) (M : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ Q, ConjCl (D := D) Q → ∀ (P : PlE D.host) (hP : P ∈ Q) (σ : GE N),
    Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (d P σ)

def DelUTie : Prop := ∀ (i : X.Tw) (M : ℕ), X.NonzeroIndexPlace i → 1 ≤ M → ∃ H S d, AdmFam X i M H S d ∧ IsCoord Y i M d

def HeckeLaws : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → (∀ j b k P k' P', Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P → Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P' →
      Y.hkF i j b k P * Y.hkF i j b k' P' = Y.hkF i j b k' P' * Y.hkF i j b k P) ∧
    ∀ s P, X.hEig i s 0 P = 1

def PqF (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (y : X.Ok i k) :
    Module.End (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  1 + ∑ n ∈ Finset.Icc 1 D.R.r, ((-1 : X.Ok i k) ^ n * ((normV P : ℕ) : X.Ok i k) ^ (n * (n - 1) / 2) * y ^ n) •
    (Formalism.MainNotions.IntegralHeckeForms.hkO Y i j b n P).baseChange (X.Ok i k)


open Classical in
def ThURel : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    ∃ (ch : Set (PlE D.host)) (sg : Bool), (∀ P P', IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) ∧
      (∀ M k χ (a : Y.Dat i j b), Formalism.MainNotions.IntegralHeckeForms.specU Y i j b ∅ M k χ (Y.thU i j b ∅ M a) =
        (1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i j b a) ∧
      ∀ (M : ℕ) d (Q : Finset (PlE D.host)) (a : Y.Dat i j b), IsCoord Y i M d → QOk X i Q →
        Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q → Disjoint Q (Y.lev i j b a) →
        (∀ P ∈ Q, GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
        ∀ (P Pb : PlE D.host), P ∈ Q → Pb ∈ Q → P ≠ Pb → IsConjPl D.host P Pb → P ∈ ch →
        ∀ (k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
          (χ' : Multiplicative (DelQM D.host (X.l i) ((Q.erase P).erase Pb) M) →* (X.Ok i k)ˣ),
          (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
            x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩)) →
          ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ →
            Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (Y.thU i j b Q M a) =
              PqF Y i j b k P ((psiAt sg χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k)
                (Formalism.MainNotions.IntegralHeckeForms.specU Y i j b ((Q.erase P).erase Pb) M k χ' (Y.thU i j b ((Q.erase P).erase Pb) M a))

def PropABCD : Prop :=
  ∀ (i : X.Tw) (F : Formalism.MainNotions.IntegralHeckeForms.RFam Y i) (j : ℕ) (b : Bool) (z : GE N), X.NonzeroIndexPlace i → j ∈ Finset.Icc 1 D.R.m →
    Formalism.MainNotions.IntegralHeckeForms.ABHyp Y i F j b → IsTameInertiaElementAtTwistPrime X i z →
    ∃ (H : Subgroup (GE N)) (A : Finset (PlE D.host)) (v nmax : ℕ), IsOpen (H : Set (GE N)) ∧ H.Normal ∧
      ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d (Q : Finset (PlE D.host)), 1 ≤ M → IsCoord Y i M d →
        SlopeTestRemainingChoices X i M A P (fun q => d (P q)) → Steps X i M H z P (fun q => d (P q)) → (hQ : IsQ P Q) →
        ∃ f : MvPolynomial (Fin R ⊕ Fin R) (X.O i), OrdHyp (X.O i) (X.l i) M R nmax v f ∧
          ∀ (k : ℕ) (u : Fin R ⊕ Fin R → (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
            (∀ q, u q ^ (X.l i ^ M) = 1) →
            (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) =
              ∏ q, u q ^ (x ⟨P q, (hQ _).2 ⟨q, Or.inl rfl⟩⟩).val) →
            MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f ≠ 0 →
            ∀ Tψ : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b),
              Formalism.MainNotions.IntegralHeckeForms.IsLatIn Tψ (((Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))).restrictScalars
                (X.O i)).baseChange (X.Ok i k)) →
              (∀ a ∈ F.S j b, ((F.A j b).baseChange (X.Ok i k))
                (Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (Y.thU i j b Q M a)) ∈ Tψ) →
              Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) ((F.B j b).baseChange (X.Ok i k)) Tψ ≤
                Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) (F.B j b) (F.Th j b) +
                  (nval (X.Ok i k) (X.l i) (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) -
                    (v : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ))

def AllGood : Prop := ∀ i : X.Tw, X.NonzeroIndexPlace i → ∀ s : X.Sig i, goodE Y i s

end GlobalTheory.TwSys

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.SelFun

def Tors (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (B : Type) [AddCommGroup B] [Module Λ B] : Prop :=
  ∀ b : B, ∃ n : ℕ, ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, x • b = 0

section Maps

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B']

theorem repOn_map (f : B →ₗ[Λ] B') (g : Γ) (m : Fin r → B) :
    f.compLeft (Fin r) (repOn ρ κ B g m) = repOn ρ κ B' g (f.compLeft (Fin r) m) := by
  funext a

  simp [repOn, matAct, map_sum, Finset.smul_sum]

variable [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace B'] [DiscreteTopology B']

def h1Map (f : B →ₗ[Λ] B') : H1 (repOn ρ κ B) →ₗ[Λ] H1 (repOn ρ κ B') :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (repOn_map ρ κ f)

def h1MapSubgroup (U : Subgroup Γ) (f : B →ₗ[Λ] B') :
    H1 ((repOn ρ κ B).comp U.subtype) →ₗ[Λ] H1 ((repOn ρ κ B').comp U.subtype) :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (fun g m => repOn_map ρ κ f g.1 m)

end Maps

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  (Q : Finset (PlE D.host))

def Setup : Prop :=
  GalHyp bkP i s ∧ IsLocalHom (algebraMap (X.O0 i) Λ) ∧ Module.Finite (X.O0 i) Λ ∧
    IsOpen (κ.ker : Set (GE N)) ∧ (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) ∧ TrivAbove κ (X.l i) ∧
    (∀ v ∈ Q, v ∉ placesOver D.host.E (X.l i)) ∧
    ∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, κ σ = 1

def SelMaps : Prop :=
  ∀ (B B' : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[Λ] B'),
    (selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ f) ≤ selOn bkP i (Tgl i s) κ B' Q

def NoInv : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    H0 (repOn (Tgl i s) κ B) = ⊥

def LocSat : Prop :=
  ∀ v ∈ placesOver D.host.E (X.l i),
  ∀ (B' B : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ f : B' →ₗ[Λ] B, Function.Injective f → ∀ y : H1 ((repOn (Tgl i s) κ B').comp (DecV N v).subtype),
      h1MapSubgroup (Tgl i s) κ (DecV N v) f y ∈ bkOn bkP i (Tgl i s) κ B v → y ∈ bkOn bkP i (Tgl i s) κ B' v

def SelLeft : Prop :=
  ∀ (B' B B'' : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], Tors Λ B → Tors Λ B'' →
    ∀ (f : B' →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g →
      Function.Injective (h1Map (Tgl i s) κ f) ∧
      ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, h1Map (Tgl i s) κ g y = 0 →
        ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ f x = y

def SelColim : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, ∃ B' : Submodule Λ B, B'.FG ∧
      ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ B'.subtype x = y

def LocCount : Prop :=
  ∀ (K : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K], IsSimpleModule Λ K →
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ K v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        Nat.card K ^ (D.R.f * D.R.r)

def SelObs : Prop :=
  ∀ (K B B'' : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K]
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], IsSimpleModule Λ K → Tors Λ B →
    ∀ (f : K →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g → Function.Surjective g →
      Finite (selOn bkP i (Tgl i s) κ K Q) ∧
      Finite (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ∧
      Nat.card (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ≤ Nat.card (selOn bkP i (Tgl i s) κ K Q)


open CategoryTheory in
def KernelRep : Prop :=
  ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    [Finite (IsLocalRing.ResidueField Λ)] (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
    (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ y : F.obj B, ∃ B' : Submodule Λ B, B'.FG ∧
      y ∈ LinearMap.range (F.map (ModuleCat.ofHom B'.subtype)).hom) →
    (∀ (K B B'' : ModuleCat.{0} Λ), IsSimpleModule Λ K → Tors Λ B → ∀ (f : K ⟶ B) (g : B ⟶ B''),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
      Finite (F.obj K) ∧ Finite (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ∧
        Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ≤ Nat.card (F.obj K)) →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) Λ), (∀ b c, ¬ IsUnit (Φ b c)) ∧
      ∃ e : ∀ B : ModuleCat.{0} Λ, Tors Λ B → (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[Λ] F.obj B),
        ∀ (B B' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB' : Tors Λ B') (f : B ⟶ B')
          (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ))),
          (∀ c, x'.1 c = f.hom (x.1 c)) → e B' hB' x' = (F.map f).hom (e B hB x)

end GlobalTheory.SelFun
end
end

section

noncomputable section

namespace GlobalTheory.LiftLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LabCompat (i : N.Loc) : Prop := ∀ σ Sig, HasParamW N A i σ Sig → (N.goodRow σ ↔ goodSig N A Sig)

def AtMOfParam (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → ∀ σ, HasParamW N A i σ Sig → AtM N A i σ

def CharSum : Prop :=
  ∀ (w : PlE H) (a b χ : A.LP w) (s : ℝ), A.lpDim χ = 1 →
    A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
    A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧ A.lpChar (A.lpZero w) χ = A.lpZero w

end Rec

section Exp

open Formalism.MainNotions.IntegralHeckeForms

def CommG (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (D.nexp.actG i j b g).toLinearMap ∘ₗ D.nexp.hkF i j b k P = D.nexp.hkF i j b k P ∘ₗ (D.nexp.actG i j b g).toLinearMap

end Exp

end GlobalTheory.LiftLeaf
end
end
