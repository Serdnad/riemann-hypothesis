module

public import Development.EtaleCohomology.EtaleSheaves.HZeroPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
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
import all Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ResBijPf

def TwSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem sep' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sec_empty {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} [IsEmpty U] (y z : Sec F U) : y = z :=
  sep' ⊥ (Scheme.bot_mem_grothendieckTopology U) y z (fun _ _ h => h.elim)

variable {q : ℕ} {i : ℤ}

theorem smul_mod {U : Scheme.{0}} (G : Sec (tw q i) U) (a : ℕ) : a • G = (a % q) • G := by
  apply _root_.tw_nsmul_mod <;> assumption

theorem smul_eq_of_cast {U : Scheme.{0}} (G : Sec (tw q i) U) {a b : ℕ} (h : (a : ZMod q) = b) : a • G = b • G := by
  rw [smul_mod G a, smul_mod G b, (ZMod.natCast_eq_natCast_iff' a b q).1 h]

theorem cast_of_smul_eq (hT : TwSec) [NeZero q] {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) {a b : ℕ}
    (h : a • twGen i ζ = b • twGen i ζ) : (a : ZMod q) = b := by
  rw [ZMod.natCast_eq_natCast_iff']
  rw [smul_mod _ a, smul_mod _ b] at h
  have ha := Nat.mod_lt a (NeZero.pos q)
  have hb := Nat.mod_lt b (NeZero.pos q)
  have key : ∀ x y : ℕ, x < q → y < q → x ≤ y → x • twGen i ζ = y • twGen i ζ → x = y := by
    intro x y hx hy hxy he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [add_smul] at he
    have hd : d • twGen i ζ = 0 := by
      have := congrArg (fun t => t - x • twGen i ζ) he
      simpa using this.symm
    have := (hT q i).2.2.1 U ζ d hd
    have : d = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  rcases le_total (a % q) (b % q) with hab | hab
  · exact key _ _ ha hb hab h
  · exact (key _ _ hb ha hab h.symm).symm

end LateralTheory.E.ResBijPf

namespace LateralTheory.E.ResBijPf
variable {q : ℕ} {i : ℤ}

theorem surj (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤))
    (s : Sec (tw q i) U) : ∃ k : ℕ, s = k • twGen i ζ := by
  apply _root_.UpperTheory.twisted_section_eq_nsmul_generator_of_connected <;> assumption

theorem gen_bij (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤)) :
    Function.Bijective (fun k : ZMod q => k.val • twGen i ζ) := by
  refine ⟨fun k k' h => ?_, fun s => ?_⟩
  · have := cast_of_smul_eq hT ζ h
    simpa using this
  · obtain ⟨n, rfl⟩ := surj (i := i) hT ζ s
    refine ⟨(n : ZMod q), smul_eq_of_cast _ ?_⟩
    simp

theorem ResBij_of (hT : TwSec) : LateralTheory.E.HZeroPf.ResBij := by
  intro q i Y X f hY hX ⟨ζ⟩
  have : NeZero q := ⟨fun h0 => by
    subst h0
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    have h := ζ.2.1
    simp only [Nat.cast_zero, isUnit_zero_iff] at h
    exact zero_ne_one h⟩
  have h1 := gen_bij (i := i) hT ζ
  have h2 := gen_bij (i := i) hT (ζ.map f.appTop.hom)
  have e : (Sec.res (F := tw q i) f) ∘ (fun k : ZMod q => k.val • twGen i ζ) =
      fun k : ZMod q => k.val • twGen i (ζ.map f.appTop.hom) := by
    funext k
    simp only [Function.comp]
    rw [res_nsmul', (hT q i).2.2.2.1]
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

end LateralTheory.E.ResBijPf
