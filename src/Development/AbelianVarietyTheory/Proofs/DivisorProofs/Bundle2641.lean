module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem hypS_polAV_pullback : ∀ {S S' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (f : S' ⟶ S) (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → HypS P.A P.L → HypS P'.A P'.L :=
  fun {S S'} P P' f ψ h hb hS =>
    GlobalTheory.SymBaseChange.hypS_baseChange S S' P.A P'.A f ψ P.L P'.L P.isLB P'.isLB h hb hS

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Points

theorem eq_of_forall_mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {z z' : X} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : ∀ f : Γ(X, U), z ∈ X.basicOpen f ↔ z' ∈ X.basicOpen f) : z = z' := by
  have key : ∀ (x : U) (f : Γ(X, U)),
      f ∉ (hU.primeIdealOf x).asIdeal ↔ x.1 ∈ X.basicOpen f := by
    intro x f
    have e1 := hU.fromSpec_primeIdealOf x
    have e2 := hU.fromSpec_preimage_basicOpen f
    have : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x.1 ∈ X.basicOpen f := by
      rw [← e1]; rfl
    rw [← this, e2]; rfl
  have e : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩ := by
    apply PrimeSpectrum.ext
    ext f
    rw [← not_iff_not, key, key]
    exact h f
  have e1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [e] at e1
  exact e1.symm.trans e2

theorem point_eq_of_inv_mem_iff :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  intro o Ω _ _ _ M U hU z z' hz hz' h
  refine eq_of_forall_mem_basicOpen_iff hU hz hz' fun f => ?_
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have ha : valF M.pt U f ∈ M.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
  rw [← isUnit_valF_iff hz f, ← isUnit_valF_iff hz' f, isUnit_O_iff, isUnit_O_iff]
  exact and_congr_right fun h0 => h _ ha h0

end GlobalTheory.Points
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Poinc

theorem prime_eq_nonunits_at_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ P : Ideal (M.ringOn (U : Set M.Z)), P.IsPrime →
      ∃ z ∈ U, ∀ a : M.ringOn (U : Set M.Z), a ∈ P ↔ ((a : Ω) = 0 ∨ (a : Ω)⁻¹ ∉ M.O z) := by
  intro o Ω _ _ _ M U hU hne P hP
  let e := M.sectionsEquiv U hne
  let P' : Ideal Γ(M.Z, U) := P.comap (e : Γ(M.Z, U) →+* M.ringOn (U : Set M.Z))
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  let x : Spec Γ(M.Z, U) := (⟨P', hP'⟩ : PrimeSpectrum Γ(M.Z, U))
  have hz : hU.fromSpec x ∈ U := by
    have h := hU.range_fromSpec
    exact h.subset ⟨x, rfl⟩
  refine ⟨hU.fromSpec x, hz, fun a => ?_⟩
  obtain ⟨f, rfl⟩ := e.surjective a
  have key : hU.fromSpec x ∈ M.Z.basicOpen f ↔ f ∉ P' := by
    have h := hU.fromSpec_preimage_basicOpen f
    have h2 : x ∈ hU.fromSpec ⁻¹ᵁ M.Z.basicOpen f ↔ hU.fromSpec x ∈ M.Z.basicOpen f := Iff.rfl
    rw [← h2, h]
    exact PrimeSpectrum.mem_basicOpen f (⟨P', hP'⟩ : PrimeSpectrum Γ(M.Z, U))
  have hu := isUnit_valF_iff hz f
  rw [isUnit_O_iff] at hu
  have hmem : e f ∈ P ↔ f ∈ P' := Iff.rfl
  rw [hmem, coe_sectionsEquiv, ← not_iff_not, ← key, ← hu]
  simp only [not_or, not_not]

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

theorem GlobalTheory.Poinc.finite_preimage_integral : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ U : M₁.Z.Opens, IsAffineOpen U → (U : Set M₁.Z).Nonempty → ∀ b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z), ∃ f : Polynomial Ω₁, f.Monic ∧ (∀ i, f.coeff i ∈ M₁.ringOn (U : Set M₁.Z)) ∧ Polynomial.eval₂ (algebraMap Ω₁ Ω₂) b f = 0 := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hq hg U hUa hU b hb
  have hpt : ⊤ ≤ (M₂.pt ≫ q) ⁻¹ᵁ U := by
    rw [hg]
    exact fun x _ => M₁.top_le_preimage_pt hU (x := (spMap (algebraMap Ω₁ Ω₂)) x) trivial
  have hV : (((q ⁻¹ᵁ U : M₂.Z.Opens)) : Set M₂.Z).Nonempty :=
    ⟨M₂.pt (IsLocalRing.closedPoint Ω₂), hpt (x := IsLocalRing.closedPoint Ω₂) trivial⟩
  have h1 : ∀ a : Γ(M₁.Z, U), valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) = algebraMap Ω₁ Ω₂ (valF M₁.pt U a) := by
    intro a
    refine (valR_comp M₂.pt q U a).symm.trans ?_
    rw [hg]
    exact valR_spMap_comp _ M₁.pt U (M₁.top_le_preimage_pt hU) a
  have hint : (q.app U).hom.IsIntegral := RingHom.IsIntegral.of_finite (hq.finite_app U hUa)
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hV).1 hb
  obtain ⟨P, hPm, hP⟩ := hint g
  refine ⟨P.map (M₁.res U hU), hPm.map _, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact (RatModel.mem_ringOn_iff_exists hU).2 ⟨P.coeff i, (M₁.res_apply U hU _).symm⟩
  · have hc : (algebraMap Ω₁ Ω₂).comp (M₁.res U hU) = (M₂.res (q ⁻¹ᵁ U) hV).comp (q.app U).hom := by
      ext a
      simp only [RingHom.comp_apply, RatModel.res_apply]
      exact (h1 a).symm
    rw [Polynomial.eval₂_map, hc, ← RatModel.res_apply _ _ hV, ← Polynomial.hom_eval₂, hP, map_zero]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem natCast_prime_not_isUnit_stalk (X : Scheme.{0}) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y (cPt p))) := by
  intro hu
  have h := hu.map (Scheme.stalkClosedPointTo y).hom
  rw [map_natCast] at h
  refine (not_isUnit_OO_iff ((p : ℕ) : OO p)).2 ?_ h
  have e : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_lt_one_iff.2 dvd_rfl

theorem dvd_of_not_isUnit_stalk (X : Scheme.{0}) (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ X) (n : ℕ)
    (h : ¬ IsUnit ((n : ℕ) : X.presheaf.stalk (y (cPt q)))) : q ∣ n := by
  have h1 : ¬ IsUnit ((Scheme.stalkClosedPointTo y).hom (n : X.presheaf.stalk (y (cPt q)))) :=
    fun hu => h ((isUnit_map_iff (Scheme.stalkClosedPointTo y).hom _).1 hu)
  rw [map_natCast, not_isUnit_OO_iff] at h1
  have e : (((n : ℕ) : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((n : ℕ) : ℚ_[q]) := by simp
  rw [e, PadicAlgCl.norm_extends] at h1
  exact Padic.norm_natCast_lt_one_iff.1 h1

theorem eq_of_cPt_eq : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X)
    (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  intro X p q hp hq y y' h
  have h1 := natCast_prime_not_isUnit_stalk X p y
  have h2 : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y' (cPt q))) := by
    rw [← h]; exact h1
  have h3 := dvd_of_not_isUnit_stalk X q y' p h2
  exact ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h3).symm

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem RatModel.val_prod_zpow : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (z : M.Z), (∀ w, y w ⤳ z) → ∀ {ι : Type} (s : Finset ι) (f : ι → Ω) (m : ι → ℤ), (∀ i, f i ≠ 0 ∧ f i ∈ M.O z ∧ (f i)⁻¹ ∈ M.O z) → M.val y (∏ i ∈ s, f i ^ m i) = ∏ i ∈ s, M.val y (f i) ^ m i := by
  intro o' Ω _ _ _ M K _ y z h ι s f m hf
  have hmem : ∀ i, f i ^ m i ∈ M.O z := by
    intro i
    rcases Int.eq_nat_or_neg (m i) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast]; exact pow_mem (hf i).2.1 n
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem (hf i).2.2 n
  have hval : ∀ i, M.val y (f i ^ m i) = M.val y (f i) ^ m i := by
    intro i
    have hinv : M.val y (f i)⁻¹ = (M.val y (f i))⁻¹ := by
      have e := RatModel.val_mul h (hf i).2.1 (hf i).2.2
      rw [mul_inv_cancel₀ (hf i).1, RatModel.val_one] at e
      exact (eq_inv_of_mul_eq_one_right e.symm)
    rcases Int.eq_nat_or_neg (m i) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast, zpow_natCast]
      exact map_pow (RatModel.valHomOf y z h) ⟨f i, (hf i).2.1⟩ n
    · rw [hn, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow, ← hinv]
      exact map_pow (RatModel.valHomOf y z h) ⟨(f i)⁻¹, (hf i).2.2⟩ n
  have e := map_prod (RatModel.valHomOf y z h) (fun i => (⟨f i ^ m i, hmem i⟩ : M.O z)) s
  have hc : (↑(∏ i ∈ s, (⟨f i ^ m i, hmem i⟩ : M.O z)) : Ω) = ∏ i ∈ s, f i ^ m i := by
    exact map_prod (M.O z).subtype _ s
  rw [RatModel.valHomOf_apply, hc] at e
  rw [e]
  exact Finset.prod_congr rfl fun i _ => by rw [RatModel.valHomOf_apply]; exact hval i

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem intClosure_aut_extends : ∀ (o₁ Ω₁ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (z₁ : M₁.Z), letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ σ : (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[M₁.Z.presheaf.stalk z₁] (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂), ∃ σ' : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, σ' (b : Ω₂) = ((σ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : Ω₂) := by
  intro o₁ Ω₁ _ _ _ Ω₂ _ _ _ M₁ z₁ σ
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₁ := (M₁.stalkHom z₁).toAlgebra
  haveI : IsDomain (M₁.Z.presheaf.stalk z₁) := (M₁.stalkHom_injective z₁).isDomain _
  haveI : FaithfulSMul (M₁.Z.presheaf.stalk z₁) Ω₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M₁.stalkHom_injective z₁)
  haveI : IsFractionRing (M₁.Z.presheaf.stalk z₁) Ω₁ := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M₁.O z₁) x
    refine ⟨(M₁.stalkEquiv z₁).symm a, (M₁.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : M₁.O z₁, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₁ ((M₁.stalkEquiv z₁).symm c) = c := fun c => by
      change M₁.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic Ω₁ Ω₂ := inferInstance
  refine ⟨(galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ, fun b => ?_⟩
  have := algebraMap_galRestrict_apply (M₁.Z.presheaf.stalk z₁)
    ((galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ) b
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem fg_ringOn_of_isAffineOpen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → (M.ringOn U).FG :=
  fun _ _ _ _ _ _ _ hU hne => GlobalTheory.ZH.RatModel.fg_ringOn hU hne

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_lift_finite_through_point : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ (p : ℕ) [Fact p.Prime] (Y : Sp (OO p) ⟶ Z) (w : X), f w = (gPt p ≫ Y) (IsLocalRing.closedPoint (PadicAlgCl p)) → ∃ y : Sp (OO p) ⟶ X, y ≫ f = Y ∧ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) = w := by
  intro X Z f hf p _ Y w hw

  set x : Sp (PadicAlgCl p) ⟶ Z := gPt p ≫ Y with hxdef
  obtain ⟨⟨z, φ⟩, hzφ⟩ := (Scheme.SpecToEquivOfField (PadicAlgCl p) Z).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hzφ
  have hz : f w = z := by
    rw [hw, ← hzφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _)
  subst hz
  have hfin := GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite f w
  letI := (f.residueFieldMap w).hom.toAlgebra
  letI := φ.hom.toAlgebra
  haveI : Module.Finite (Z.residueField (f w)) (X.residueField w) := hfin
  haveI : Algebra.IsAlgebraic (Z.residueField (f w)) (X.residueField w) := inferInstance
  let ψ : X.residueField w →ₐ[Z.residueField (f w)] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  set y0 : Sp (PadicAlgCl p) ⟶ X := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField w with hy0
  have hy0f : y0 ≫ f = gPt p ≫ Y := by
    rw [← hxdef, ← hzφ, hy0, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have hy0w : y0 (IsLocalRing.closedPoint (PadicAlgCl p)) = w :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply w _)

  haveI : IsProper f := inferInstance
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (hE { R := OO p, K := PadicAlgCl p, i₁ := y0, i₂ := Y, commSq := ⟨hy0f⟩ }).exists_lift
  refine ⟨l, hl2, ?_⟩
  have : gPt p ≫ l = y0 := hl1
  rw [this, hy0w]

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevCalc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {d d' d'' : ℕ}

theorem sRel_comp {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨ψ, hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  refine ⟨ψ ≫ φ, hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sRel_cancel {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨χ, hχ, ⟨χ₂, hs', hw'⟩, hl'⟩ := m'
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨F₂, ⟨h₁, h₂⟩, ?_⟩, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a ^ d'').left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a ^ d'')
      have a₂ : (c'.lev a ^ d').left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a ^ d')
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem sRel_principal {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f)
    (hc : c.Principal) : c'.Principal := by
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

theorem sRel_mul {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f) (e : ℕ) :
    SRel c' c (d' * e) (d * e) f := by
  obtain ⟨φ, pb, sq, hl⟩ := m
  refine ⟨φ, pb, sq, fun a => ?_⟩
  rw [pow_mul, pow_mul]
  exact pow_section pb _ _ (hl a) e

theorem sRel_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m =>
    ⟨⟨sRel_comp m, sRel_cancel m⟩, sRel_principal m, sRel_mul m⟩

end GlobalTheory.SiegLevCalc
end
end
