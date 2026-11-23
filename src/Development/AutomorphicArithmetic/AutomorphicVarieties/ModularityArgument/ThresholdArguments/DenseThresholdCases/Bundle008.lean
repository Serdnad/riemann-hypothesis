module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle003
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (ξ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) (t : ℤ), IsOpen (ξ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) → IsCharOf ι χ (cycBar F Ω l ^ t * ξ) → ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ s : Weil h, ((χ.loc w (a s) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (t * deg s) * ι (ξ (s : _root_.Formalism.ConjugateSelfDual.G F Ω) : Qbar l) := by
  intro N F Ω _ _ _ _ _ l _ ι χ ξ t hξ ⟨hc, art, n, hart, _, hL⟩ w hw A h a ha s
  haveI : Finite (_root_.Formalism.ConjugateSelfDual.G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen hξ
  have hN : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := UpperTheory.V.Loc.laHecke h art hart ι χ n _ hL ⟨a, ha⟩
  have h2 := UpperTheory.V.Loc.laArith N.aut.art h hw ((cycBar F Ω l ^ t * ξ).comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype)
    (hc.comp continuous_subtype_val) t ξ.ker.index (Nat.pos_of_ne_zero hN) fun g _ => by
      have e : ((cycBar F Ω l ^ t * ξ).comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) g * cycBar F Ω l g ^ (-t) = ξ g := by
        show cycBar F Ω l g ^ t * ξ g * cycBar F Ω l g ^ (-t) = ξ g
        rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, ← map_pow]
      exact ξ.ker.pow_index_mem _
  have h3 := UpperTheory.V.Loc.laUnique h ⟨a, ha⟩ _ _ _ h1 h2
  haveI : Fintype {j : w.adicCompletion F →+* Qbar l // Continuous j} := @Fintype.ofFinite _ (finite_contEmb w)
  have h4 : locPow ι n w (a s : w.adicCompletion F) = Hi.algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ t := by
    unfold locPow Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [neg_injective (congrFun h3 j), zpow_one]
  have h0 : Hi.algPow w (fun _ : F →+* Qbar l => 1) (a s : w.adicCompletion F) ^ t ≠ 0 := by
    refine zpow_ne_zero _ ?_
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero)
  have h5 := hL.loc (a s) s (ha.glob art hart s)
  have h6 := UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s
  have h7 : (((cycBar F Ω l ^ t * ξ) (s : _root_.Formalism.ConjugateSelfDual.G F Ω) : (Qbar l)ˣ) : Qbar l) =
      (cycBar F Ω l (s : _root_.Formalism.ConjugateSelfDual.G F Ω) : Qbar l) ^ t * (ξ (s : _root_.Formalism.ConjugateSelfDual.G F Ω) : Qbar l) := by
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_mul]
    rfl
  rw [h7, h6, h4, mul_zpow, mul_right_comm, mul_left_inj' h0, eq_comm, RingEquiv.symm_apply_eq] at h5
  rw [h5, map_mul, map_zpow₀, map_zpow₀, map_natCast, ← zpow_mul, mul_comm t]
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.W UpperTheory.V.Ws.Eb
namespace UpperTheory.V.Th
section Abstract
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {K : Type} [Field K] {n : ℕ}
end Abstract
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}
structure AutomorphicPointGalois (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous ρ
  rep : x.IsRep (ρ.comp V.pr)
  arith : ∃ h, x.Arith h
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (ρ.comp V.pr)
  unr0 : ∀ g ∈ V.frame.I0, ρ g = 1
  flag : ∀ v : V.frame.Vl, HasFlag (ρ.comp (V.frame.φ v)) (x.psi v)
structure AutomorphicPointLocallyGeneric (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop extends toAPt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ where
  free : Free V.frame fun v => x.psi v
  irr : TypeI V.frame ρ
  n3 : N3 V.frame ρ
end U
def DenseThresholdMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ → OrdZero r ρ fun v => x.psi v
def AdjointLiftingTheorem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ → Par x → AdZero V ρ
end UpperTheory.V.Th
end
end
end

section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
def Step_jacProd_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    (∃ y : Jacquet π (unipRad k G.e), y ≠ 0 ∧ ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)), jacU G.e π m y = G.eta m • y) →
    IsTwSphProd π G.d G.hd G.μ
def CMainForAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → (∃ x : V, x ≠ 0 ∧ x ∈ G.Eig π) → IsTwSphProd π G.d G.hd G.μ
end Grp
end UpperTheory.TNZ
end
end
end

section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
def Step_jacFin_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsSmooth (jacU G.e π) ∧ HasFiniteLength (jacU G.e π)
def Step_tensor_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth σ → σ.IsIrreducible → G.HasEtaVec σ →
    ∃ (Y : Fin G.s → Type) (_ : ∀ a, AddCommGroup (Y a)) (_ : ∀ a, Module ℂ (Y a))
      (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) ∧ (∀ a, (τ a).IsIrreducible) ∧ (∀ a, HasDetVec (τ a) (G.μ a)) ∧
        Nonempty (σ.Equiv (piTensor τ))
def Step_suppProd_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) → (∀ a, HasDetVec (τ a) (G.μ a)) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsTwSphProd π G.d G.hd G.μ
end Grp
end UpperTheory.TNZ
end
end
end
