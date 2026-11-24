module

import GroundTheory.AutomorphicForms.FiniteBruhat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.DoubleCoset
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools.BruhatKO

open DoubleCoset

variable {n : ℕ} {k : Type} [Field k]

private theorem borel_eq : borel k (Fin n) = GroundTheory.Automorphic.borel n k := by
  ext g
  exact (mem_borel _).trans (GroundTheory.Automorphic.mem_borel_iff g).symm

private theorem pm_eq (σ : Equiv.Perm (Fin n)) : pm k n σ = GroundTheory.Automorphic.permGL k σ := by
  ext i j
  rw [pm_apply, GroundTheory.Automorphic.permGL_apply]

private theorem exists_mem_doubleCoset_pm (g : GL (Fin n) k) :
    ∃ σ : Equiv.Perm (Fin n), g ∈ doubleCoset (pm k n σ) (borel k (Fin n)) (borel k (Fin n)) := by
  simpa only [pm_eq, borel_eq] using GroundTheory.Automorphic.exists_mem_doubleCoset_permGL g

private theorem doubleCoset_pm_injective {σ τ : Equiv.Perm (Fin n)} {g : GL (Fin n) k}
    (hσ : g ∈ doubleCoset (pm k n σ) (borel k (Fin n)) (borel k (Fin n)))
    (hτ : g ∈ doubleCoset (pm k n τ) (borel k (Fin n)) (borel k (Fin n))) : σ = τ := by
  rw [pm_eq, borel_eq] at hσ hτ
  exact GroundTheory.Automorphic.doubleCoset_permGL_injective hσ hτ

private theorem map_pm {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : Equiv.Perm (Fin n)) :
    GeneralLinearGroup.map (n := Fin n) f (pm R n w) = pm S n w := by
  ext i j
  show f ((pm R n w : Matrix (Fin n) (Fin n) R) i j) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem red_surj {O : Type} [CommRing O] [IsLocalRing O] :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  choose s hs using IsLocalRing.residue_surjective (R := O)
  let M : Matrix (Fin n) (Fin n) O := (g : Matrix (Fin n) (Fin n) _).map s
  have hM : (IsLocalRing.residue O).mapMatrix M = g := by
    ext i j
    exact hs _
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hM]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  ext i j
  show IsLocalRing.residue O ((u : Matrix (Fin n) (Fin n) O) i j) = _
  rw [hu]
  exact hs _

end UpperTheory.V.AlgebraTools.BruhatKO

open UpperTheory.V.AlgebraTools.BruhatKO in
theorem UpperTheory.V.AlgebraTools.bruhatKO :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (∀ w : Equiv.Perm (Fin n), pm k n w ∈ KO k (Fin n)) ∧ ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n), ∃ a ∈ iwahori k (Fin n), ∃ b ∈ iwahori k (Fin n), g = a * pm k n w * b := by
  intro k _ _ _ _ n
  refine ⟨fun w => ⟨pm 𝒪[k] n w, map_pm _ w⟩, ?_⟩
  rintro _ ⟨g, rfl⟩
  set ι := GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) with hι
  set r := GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) with hr
  have hinj : Function.Injective ι := by
    intro x y h
    ext i j
    exact congrArg (fun z : GL (Fin n) k => (z : Matrix (Fin n) (Fin n) k) i j) h
  have key : ∀ w : Equiv.Perm (Fin n),
      (∃ a ∈ iwahori k (Fin n), ∃ b ∈ iwahori k (Fin n), ι g = a * pm k n w * b) ↔
        r g ∈ DoubleCoset.doubleCoset (pm 𝓀[k] n w) (borel 𝓀[k] (Fin n)) (borel 𝓀[k] (Fin n)) := by
    intro w
    have e1 : ι (pm 𝒪[k] n w) = pm k n w := map_pm _ w
    have e2 : r (pm 𝒪[k] n w) = pm 𝓀[k] n w := map_pm _ w
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, h⟩
      have h' : g = a * pm 𝒪[k] n w * b := hinj (by rw [map_mul, map_mul, e1]; exact h)
      exact ⟨r a, ha, r b, hb, by rw [h', map_mul, map_mul, e2]⟩
    · rintro ⟨x, hx, y, hy, h⟩
      obtain ⟨b, rfl⟩ := red_surj y
      refine ⟨ι (g * b⁻¹ * (pm 𝒪[k] n w)⁻¹), ⟨_, ?_, rfl⟩, ι b, ⟨b, hy, rfl⟩, ?_⟩
      · show r _ ∈ borel 𝓀[k] (Fin n)
        have : r (g * b⁻¹ * (pm 𝒪[k] n w)⁻¹) = x := by
          rw [map_mul, map_mul, map_inv, map_inv, h, e2]
          exact (by group : x * pm 𝓀[k] n w * r b * (r b)⁻¹ * (pm 𝓀[k] n w)⁻¹ = x)
        rw [this]; exact hx
      · rw [← e1, ← map_mul, ← map_mul]
        congr 1
        group
  obtain ⟨w, hw⟩ := exists_mem_doubleCoset_pm (r g)
  exact ⟨w, (key w).2 hw, fun v hv => doubleCoset_pm_injective ((key v).1 hv) hw⟩
