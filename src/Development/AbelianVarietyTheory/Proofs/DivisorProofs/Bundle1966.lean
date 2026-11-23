module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_level_algClosed_charZero :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (P : PolAV (Sp C)) (k : ℕ), 1 ≤ k → ∃ ζ : Cˣ, Nonempty (Out.Level P k (unitOn ζ)) := by
  intro C _ _ _ P k hk
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : NeZero (k : C) := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C k
  let ze : Cˣ := (hζ.isUnit (by omega)).unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ze] using hζ)
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk0 ze hze
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : C →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k := fun φ =>
    hze.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp C) P k (unitOn ze)
    (by have := nt C; exact prim (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 (by omega))
    pt hpt hw
  exact ⟨ze, ⟨lev⟩⟩

end GlobalTheory.MBLow
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem theta_nonvanish_coset (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) (a : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => (a * x).left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ (a * x) τ v ∧ v ≠ 0 :=
  abelianSchemeLaws_all.1.goodPt k P N hN hNk θ hθ a

theorem theta_nonvanish_torsion (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => x.left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ x τ v ∧ v ≠ 0 := by
  obtain ⟨x, hx, rest⟩ := theta_nonvanish_coset k P N hN hNk θ hθ 1
  exact ⟨1 * x, by rw [_root_.one_mul]; exact hx, rest⟩

end GlobalTheory.Poinc.Sep
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibreTheta

theorem exists_sec_nonempty : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S),
    IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]),
      (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  intro S P K _ t hI
  let T : Over S := Over.mk t
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.abelianSchemeLaws_all.2.secTwist S P 1 le_rfl K t (1 : T ⟶ P.A)
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)

  have nz : ∃ j, (b i₀).f j ≠ 0 := by
    by_contra hz
    push_neg at hz
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have h0 : ∀ r' : Fin (1 ^ P.g) → Γ(T.left, ⊤), ∀ j, (b i₀).f j = ∑ i, ((T ⊗ P.A).left.presheaf.map
        (homOfLE le_top).op).hom ((fst T P.A).left.appTop.hom (r' i)) * (b i).f j := fun r' j => by
      rw [su, hz j, mul_zero]
    have := (hu (fun _ => 0) (h0 _)).trans (hu (fun _ => 1) (h0 _)).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  obtain ⟨j, hj⟩ := nz
  haveI : IsReduced (T ⊗ P.A).left := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (T ⊗ P.A).left.basicOpen ((b i₀).f j) := by
    by_contra h
    push_neg at h
    exact hj (eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy' => (h y hy').elim))
  have hy₀ : y ∈ nonzeroLocus (b i₀) := TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩
  have hF : FormEq (![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left] : Fin 2 → _)
      ![((1 : ℕ) : ℤ) - 1, 1] (![(snd T P.A).left] : Fin 1 → _) ![1] := by
    intro U _ h
    rw [e]; simp [Fin.prod_univ_succ]
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec P.isLB hF (b i₀)
  choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  refine ⟨s, y, ?_⟩
  show y ∈ nonzeroLocus s
  rw [GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval s y hJ', hs _ (𝟙 _) y J hJ']
  exact (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval (b i₀) y hJ').1 hy₀

end GlobalTheory.FibreTheta
end
end
