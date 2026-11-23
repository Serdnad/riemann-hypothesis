module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle188
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle019
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.PackingFacts

def zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    rw [div_add_div _ _ hb0 hb0']
    push_cast
    ring
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; rw [neg_div]⟩

theorem mem_range_zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zp Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_adjoin_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin o T) : w ∈ Algebra.adjoin o' T := by
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem mem_adjoin_of_int (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin ℤ T) : w ∈ Algebra.adjoin o T :=
  mem_adjoin_of_range_le (o := ℤ) (o' := o) (fun n : ℤ => ⟨((n : ℤ) : o), by rw [map_intCast, eq_intCast]⟩) T hw

theorem isUnit_natCast {A O : Type} [CommRing A] [CommRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := by
  have hbm : (b : A) ∉ m := by
    intro hbm
    have hcop : IsCoprime (b : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hb).symm
    obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom A)
    have h1 : (1 : A) ∈ m := by
      rw [← huv]
      simp only [eq_intCast, Int.cast_natCast]
      exact add_mem (m.mul_mem_left _ hbm) (m.mul_mem_left _ hpm)
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)
  have := IsLocalization.map_units O (⟨(b : A), hbm⟩ : m.primeCompl)
  simpa using this

theorem exists_denom {o A O Ω : Type} [CommRing o] [CommRing A] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra A Ω]
    [Algebra A O] [Algebra O Ω] [IsScalarTower A O Ω] (M : Submonoid A) [IsLocalization M O] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) {w : Ω} (hw : w ∈ Algebra.adjoin O T) :
    ∃ s : M, w * algebraMap A Ω s ∈ Algebra.adjoin o T := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj M r
    refine ⟨s, ?_⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, e, ← IsScalarTower.algebraMap_apply]
    exact hA _
  | add x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x + y) * algebraMap A Ω ((b * b' : M) : A) =
        x * algebraMap A Ω b * algebraMap A Ω b' + y * algebraMap A Ω b' * algebraMap A Ω b := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact add_mem (mul_mem hx (hA _)) (mul_mem hy (hA _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x * y) * algebraMap A Ω ((b * b' : M) : A) = x * algebraMap A Ω b * (y * algebraMap A Ω b') := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact mul_mem hx hy

theorem isIntegrallyClosed_of_denom {o O Ω : Type} [CommRing o] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra O Ω]
    (B : Subalgebra o Ω) (B' : Subalgebra O Ω) [IsIntegrallyClosed B] (hle : ∀ w ∈ B, w ∈ B')
    (hden : ∀ w ∈ B', ∃ s ∈ B, (∃ t ∈ B', s * t = 1) ∧ w * s ∈ B) : IsIntegrallyClosed B' := by
  let ψ : B →+* B' := (algebraMap B Ω).codRestrict _ fun s => hle _ s.2
  letI : Algebra B B' := ψ.toAlgebra
  let M : Submonoid B := (IsUnit.submonoid B').comap ψ
  haveI hloc : IsLocalization M B' := by
    refine ⟨fun s => s.2, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, ⟨t, ht, e⟩, hws⟩ := hden a a.2
      have hu : IsUnit (ψ ⟨s, hs⟩) := IsUnit.of_mul_eq_one (⟨t, ht⟩ : B') (Subtype.ext e)
      exact ⟨⟨⟨_, hws⟩, ⟨⟨s, hs⟩, hu⟩⟩, Subtype.ext rfl⟩
    · have h' : (r : Ω) = s := congrArg (fun z : B' => (z : Ω)) h
      rw [Subtype.ext h']
  have hM : M ≤ nonZeroDivisors B := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
    have hu : IsUnit (ψ s) := hs
    rw [h, map_zero] at hu
    exact not_isUnit_zero hu
  exact isIntegrallyClosed_of_isLocalization B' M hM

end PositivityTheory.Xgn.PackingFacts

open PositivityTheory.Xgn.PackingFacts in
theorem PositivityTheory.Xgn.torsion_packing_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ c' hc'
  haveI hch : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, -, -, -, hchart⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (zp Ω p) (mem_range_zp Ω p)
  obtain ⟨-, hic, hfr, x₀, hx₀, -⟩ := hchart c' hc'
  obtain ⟨-, -, -, hconst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  have eO := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := O) y c' hc'
  have eo := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := zp Ω p) y c' hc'
  have eZ := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := ℤ) y c' hc'
  have hr : ∀ a : zp Ω p, algebraMap (zp Ω p) Ω a ∈ (algebraMap O Ω).range := by
    intro a
    obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zp Ω p _).1 ⟨a, rfl⟩
    have hu := isUnit_natCast (O := O) m p hpm b hb
    refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
    rw [hab, map_mul, map_intCast, div_eq_mul_inv]
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
  have hle : ∀ w ∈ chartRing (zp Ω p) (mseg y) c', w ∈ CR O y c' := by
    intro w hw
    exact eO.ge (mem_adjoin_of_range_le hr _ (eo.le hw))
  have hA : ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin (zp Ω p) (Set.range fun j => mseg y j / mseg y c') := by
    intro a
    have h1 : algebraMap A Ω a ∈ chartRing ℤ (mseg y) c' := hconst c' hc' a
    rw [eZ] at h1
    exact mem_adjoin_of_int _ _ h1
  refine ⟨hch, ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.FiniteType O (CR O y c') := by
      refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => mseg y j / mseg y c').toFinset, ?_⟩
      rw [Set.Finite.coe_toFinset]
      exact eO.symm
    exact Algebra.FiniteType.isNoetherianRing O _
  · refine isIntegrallyClosed_of_denom (chartRing (zp Ω p) (mseg y) c') (CR O y c') hle fun w hw => ?_
    obtain ⟨s, hs⟩ := exists_denom m.primeCompl _ hA (eO.le hw)
    have hu := IsLocalization.map_units O s
    refine ⟨algebraMap A Ω s, eo.ge (hA _), ⟨algebraMap O Ω ↑hu.unit⁻¹, Subalgebra.algebraMap_mem _ _, ?_⟩, eo.ge hs⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu.mul_val_inv, map_one]
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, h, -, e⟩ := IsFractionRing.div_surjective (A := chartRing (zp Ω p) (mseg y) c') a
    exact ⟨⟨g, hle _ g.2⟩, ⟨h, hle _ h.2⟩, e.symm⟩
  · let ψ : chartRing (zp Ω p) (mseg y) c' →+* CR O y c' :=
      (algebraMap (chartRing (zp Ω p) (mseg y) c') Ω).codRestrict _ fun s => hle _ s.2
    refine ⟨spMap ψ ≫ x₀, ?_⟩
    have e : spMap (algebraMap (CR O y c') Ω) ≫ spMap ψ = spMap ((algebraMap (CR O y c') Ω).comp ψ) :=
      (Spec.map_comp _ _).symm
    rw [← Category.assoc, e]
    exact hx₀
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionOnChart

def zloc (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by simp [neg_div]⟩
  mul_mem' := by
    rintro x z ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro x z ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hb hb', ?_⟩
    have h0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    have h0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb' (h ▸ dvd_zero p)
    push_cast
    rw [div_add_div _ _ h0 h0']

theorem zloc_range (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zloc Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) :=
  ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem overring {R₀ R Ω : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] [Field Ω]
    [Algebra R₀ Ω] [Algebra R Ω] [IsIntegrallyClosed R₀] [IsFractionRing R₀ Ω]
    (hinj : Function.Injective (algebraMap R Ω))
    (hle : ∀ x : R₀, ∃ r : R, algebraMap R Ω r = algebraMap R₀ Ω x)
    (hden : ∀ r : R, ∃ (s x : R₀) (u : R), algebraMap R₀ Ω s * algebraMap R Ω u = 1 ∧
      algebraMap R Ω r * algebraMap R₀ Ω s = algebraMap R₀ Ω x) :
    IsIntegrallyClosed R ∧ IsFractionRing R Ω := by
  choose φ hφ using hle
  let f : R₀ →+* R :=
    { toFun := φ
      map_one' := hinj (by rw [hφ, map_one, map_one])
      map_zero' := hinj (by rw [hφ, map_zero, map_zero])
      map_mul' := fun a b => hinj (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_add' := fun a b => hinj (by rw [hφ, map_add (f := _), map_add (f := _), hφ, hφ]) }
  have hf : ∀ x, algebraMap R Ω (f x) = algebraMap R₀ Ω x := hφ
  clear_value f
  have hfi : Function.Injective f := fun a b h => IsFractionRing.injective R₀ Ω (by rw [← hf, ← hf, h])
  let M : Submonoid R₀ := (IsUnit.submonoid R).comap f
  have hM : M ≤ nonZeroDivisors R₀ := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero fun h => by
      have hu : IsUnit (f s) := hs
      rw [h, map_zero] at hu
      exact not_isUnit_zero hu
  letI : Algebra R₀ R := f.toAlgebra
  have hloc : IsLocalization M R := by
    refine (isLocalization_iff _ _).2 ⟨fun s => s.2, fun z => ?_, fun {x z} h => ⟨1, by rw [hfi h]⟩⟩
    obtain ⟨s, x, u, hu, hx⟩ := hden z
    have hs : IsUnit (f s) := IsUnit.of_mul_eq_one u (hinj (by rw [map_mul, hf, hu, map_one]))
    refine ⟨(x, ⟨s, hs⟩), hinj ?_⟩
    change algebraMap R Ω (z * f s) = algebraMap R Ω (f x)
    rw [map_mul, hf, hf, hx]
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hinj
  refine ⟨isIntegrallyClosed_of_isLocalization R M hM, IsFractionRing.of_field _ _ fun ω => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R₀) ω
  exact ⟨f a, f b, by rw [hf, hf]⟩

section Loc

variable {Ω : Type} [Field Ω] {A : Type} [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime]
  (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]

include O in
theorem inv_mem_range {s : A} (hs : s ∉ m) :
    algebraMap A Ω s ≠ 0 ∧ ∃ u : O, algebraMap O Ω u = (algebraMap A Ω s)⁻¹ := by
  obtain ⟨u, hu⟩ := (IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)).exists_right_inv
  have h : algebraMap A Ω s * algebraMap O Ω u = 1 := by
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul]
    exact (congrArg _ hu).trans (map_one _)
  exact ⟨left_ne_zero_of_mul_eq_one h, u, eq_inv_of_mul_eq_one_right h⟩

theorem zloc_le [CharZero Ω] (p : ℕ) [Fact p.Prime] (hp : (p : A) ∈ m) (z : zloc Ω p) :
    ∃ u : O, algebraMap O Ω u = (z : Ω) := by
  obtain ⟨x, a, b, hb, rfl⟩ := z
  have hbm : (b : A) ∉ m := by
    intro h
    have hc : IsCoprime (p : ℤ) (b : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hb)
    obtain ⟨u, v, huv⟩ := hc
    have h1 : (u : A) * (p : A) + (v : A) * (b : A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact (‹m.IsPrime›).ne_top ((Ideal.eq_top_iff_one m).2
      (h1 ▸ m.add_mem (m.mul_mem_left _ hp) (m.mul_mem_left _ h)))
  obtain ⟨-, u, hu⟩ := inv_mem_range (Ω := Ω) m O hbm
  refine ⟨(a : O) * u, ?_⟩
  rw [map_mul, hu, map_intCast, map_natCast]
  exact (div_eq_mul_inv _ _).symm

theorem le_adjoin {o : Type} [CommRing o] [Algebra o Ω] (T : Set Ω)
    (ho : ∀ z : o, ∃ u : O, algebraMap O Ω u = algebraMap o Ω z) :
    ∀ x ∈ Algebra.adjoin o T, x ∈ Algebra.adjoin O T := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht => exact Algebra.subset_adjoin ht
  | algebraMap z =>
    obtain ⟨u, hu⟩ := ho z
    rw [← hu]
    exact Subalgebra.algebraMap_mem _ u
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem exists_den {o : Type} [CommRing o] [Algebra o Ω] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) :
    ∀ x ∈ Algebra.adjoin O T, ∃ s : A, s ∉ m ∧ x * algebraMap A Ω s ∈ Algebra.adjoin o T := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht =>
    refine ⟨1, m.primeCompl.one_mem, ?_⟩
    rw [map_one, _root_.mul_one]
    exact Algebra.subset_adjoin ht
  | algebraMap z =>
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl z
    refine ⟨s, s.2, ?_⟩
    have h' := congrArg (algebraMap O Ω) h
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h'
    rw [h']
    exact hA a
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hz⟩ := hz
    refine ⟨s * t, m.primeCompl.mul_mem hs ht, ?_⟩
    have e : (x + z) * algebraMap A Ω (s * t) =
        x * algebraMap A Ω s * algebraMap A Ω t + z * algebraMap A Ω t * algebraMap A Ω s := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem hx (hA t)) (mul_mem hz (hA s))
  | mul x z _ _ hx hz =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hz⟩ := hz
    refine ⟨s * t, m.primeCompl.mul_mem hs ht, ?_⟩
    have e : (x * z) * algebraMap A Ω (s * t) =
        x * algebraMap A Ω s * (z * algebraMap A Ω t) := by
      rw [map_mul]; ring
    rw [e]
    exact mul_mem hx hz

include m in
theorem main {o : Type} [CommRing o] [Algebra o Ω] (T : Set Ω)
    (ho : ∀ z : o, ∃ u : O, algebraMap O Ω u = algebraMap o Ω z)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T)
    (h1 : IsIntegrallyClosed (Algebra.adjoin o T)) (h2 : IsFractionRing (Algebra.adjoin o T) Ω) :
    IsIntegrallyClosed (Algebra.adjoin O T) ∧ IsFractionRing (Algebra.adjoin O T) Ω := by
  refine overring (R₀ := Algebra.adjoin o T) (R := Algebra.adjoin O T) Subtype.val_injective
    (fun x => ⟨⟨x.1, le_adjoin O T ho x.1 x.2⟩, rfl⟩) fun r => ?_
  obtain ⟨s, hs, hz⟩ := exists_den m O T hA r.1 r.2
  obtain ⟨h0, u, hu⟩ := inv_mem_range (Ω := Ω) m O hs
  refine ⟨⟨_, hA s⟩, ⟨_, hz⟩, ⟨algebraMap O Ω u, Subalgebra.algebraMap_mem _ u⟩, ?_, rfl⟩
  change algebraMap A Ω s * algebraMap O Ω u = 1
  rw [hu, mul_inv_cancel₀ h0]

end Loc

end PositivityTheory.Xgn.FunctionOnChart

theorem PositivityTheory.Xgn.exists_function_on_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hp O _ _ _ _ _ _ _ c' hc'
  haveI : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, hA, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  obtain ⟨-, -, -, -, -, -, hch⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
    (PositivityTheory.Xgn.FunctionOnChart.zloc Ω p) (PositivityTheory.Xgn.FunctionOnChart.zloc_range Ω p)
  obtain ⟨-, h1, h2, -⟩ := hch c' hc'
  refine ⟨?_, PositivityTheory.Xgn.FunctionOnChart.main m O (Set.range fun j => mseg y j / mseg y c')
    (PositivityTheory.Xgn.FunctionOnChart.zloc_le m O p hp) (fun a => ?_) h1 h2⟩
  · haveI : Algebra.FiniteType O (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) :=
      Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
    exact Algebra.FiniteType.isNoetherianRing O (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c'))
  · have h : algebraMap A Ω a ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c') := hA c' hc' a
    generalize algebraMap A Ω a = x at h
    induction h using Algebra.adjoin_induction with
    | mem t ht => exact Algebra.subset_adjoin ht
    | algebraMap n => simpa using intCast_mem _ n
    | add s t _ _ hs ht => exact add_mem hs ht
    | mul s t _ _ hs ht => exact mul_mem hs ht
end
