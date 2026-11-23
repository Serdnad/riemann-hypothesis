module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle689
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionField
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section
namespace GlobalTheory.Poinc.Chart

theorem stalkMap_finite_of_chart (K A : Type) [Field K] [CommRing A] {X Y : Scheme.{0}} (q : Y ⟶ X) (j : Sp A ⟶ Y)
    (φ : A →+* K) [IsFinite q] [IsOpenImmersion j] (hφ : ∀ z : K, ∃ a c : A, z = φ a / φ c) (g : Sp K ⟶ X)
    (hg : g = spMap φ ≫ j ≫ q) : (g.stalkMap (genericPoint (Sp K))).hom.Finite := by
  rw [← Category.assoc] at hg
  subst hg
  have hpt : genericPoint (Sp K) = closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  rw [hpt]
  have h1 : ((spMap φ ≫ j) ≫ q).stalkMap (closedPoint (CommRingCat.of K)) =
      Scheme.stalkClosedPointTo ((spMap φ ≫ j) ≫ q) ≫ (stalkClosedPointIso (CommRingCat.of K)).inv :=
    (Iso.eq_comp_inv _).2 rfl
  rw [h1]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).inv).2) ?_
  rw [Scheme.stalkClosedPointTo_comp]
  set τ := Scheme.stalkClosedPointTo (spMap φ ≫ j) with hτdef
  have h2 : q.stalkMap _ ≫ τ = (X.residue _ ≫ q.residueFieldMap _) ≫ Y.descResidueField τ := by
    rw [Scheme.residue_residueFieldMap, Category.assoc, Scheme.residue_descResidueField]
  have hτ : ∀ a : A, ∃ s, τ.hom s = φ a := by
    intro a
    have h3 : τ = j.stalkMap _ ≫ Scheme.stalkClosedPointTo (spMap φ) := Scheme.stalkClosedPointTo_comp _ _
    have h5 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K)))) ≫
        j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))) ≫ Scheme.stalkClosedPointTo (spMap φ) =
        CommRingCat.ofHom φ := by
      rw [IsIso.inv_hom_id_assoc, Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))))).hom a, ?_⟩
    rw [h3]
    exact congrArg (fun m => m.hom a) h5
  have hsurj : Function.Surjective (Y.descResidueField τ).hom := by
    intro z
    obtain ⟨a, c, rfl⟩ := hφ z
    obtain ⟨s, hs⟩ := hτ a
    obtain ⟨t, ht⟩ := hτ c
    refine ⟨Y.residue _ s / Y.residue _ t, ?_⟩
    rw [map_div₀, ← hs, ← ht]
    rfl
  rw [h2]
  exact (RingHom.Finite.of_surjective _ hsurj).comp ((GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite q _).comp
    (RingHom.Finite.of_surjective _ (Scheme.residue_surjective X _)))

theorem exists_chart : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro n N X Y sX sY q hn hN hsX hsY hq he hs η hη
  obtain ⟨η', hη', rfl⟩ := GlobalTheory.QuotTriple.genericPoints_subset_image (π := q) hη
  have hgen : (sY η').asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY η' := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap sY hb
    have h1 : closure {η'} ⊆ closure ({z'} : Set Y) := hz'.closure_subset
    have h2 : closure ({z'} : Set Y) ⊆ closure {η'} := hη'.2 isIrreducible_singleton.closure h1
    have h3 : η' ⤳ z' := specializes_iff_closure_subset.2 h2
    have : z' = η' := (hz'.antisymm h3).eq
    rw [← this, e]
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η') isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : LocallyOfFiniteType sY := inferInstance
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨η', hηU⟩
  have hP : hU.fromSpec P = η' := hU.fromSpec_primeIdealOf _
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1, hP]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω := ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) = q η'
    rw [hw, hP]
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    refine stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom)
      (fun z => ?_) _ (by rw [← e]; simp only [Category.assoc])
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨a, c, rfl⟩

end GlobalTheory.Poinc.Chart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem bigSizes_of (g N r : ℕ) (hN : 1 + 2 * g * 2 ^ g < N)
    (hr : 6 * (N ^ g * g.factorial) + 2 * (N ^ g * g.factorial) * (g * 4 ^ g) < r) :
    1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N ∧
    2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N
      < (r * N : ℕ) ∧
    6 * (N ^ g * g.factorial) < r * N := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have e1 : (2 : ℝ) ^ ((g : ℝ) / 2) ≤ 2 ^ g := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e2 : (2 : ℝ) ^ ((g : ℝ) / 2 - 1) ≤ 2 ^ g := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e3 : (3 / 2 : ℝ) ^ g ≤ 2 ^ g := pow_le_pow_left₀ (by norm_num) (by norm_num) g
  have hNpos : 0 < N := by omega
  refine ⟨?_, ?_, ?_⟩
  · have hN' : ((1 + 2 * g * 2 ^ g : ℕ) : ℝ) < N := by exact_mod_cast hN
    push_cast at hN'
    have : 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) ≤ 2 * g * 2 ^ g := by gcongr
    linarith
  · set X : ℕ := N ^ g * g.factorial
    have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
    have hr' : ((6 * X + 2 * X * (g * 4 ^ g) : ℕ) : ℝ) < r := by exact_mod_cast hr
    push_cast at hr'
    have hC : (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) ≤ g * 4 ^ g := by
      have h4 : (4 : ℝ) ^ g = 2 ^ g * 2 ^ g := by rw [← mul_pow]; norm_num
      rw [h4, ← _root_.mul_assoc]
      have hp1 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ g := by positivity
      have hp2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by positivity
      gcongr
    have h1 : 2 * (X : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) < r := by
      have : 2 * (X : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1))
          ≤ 2 * X * (g * 4 ^ g) := by gcongr
      have h6 : (0 : ℝ) ≤ 6 * X := by positivity
      linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    push_cast
    exact mul_lt_mul_of_pos_right h1 hNr
  · have h1 : 6 * (N ^ g * g.factorial) < r := by omega
    calc 6 * (N ^ g * g.factorial) < r := h1
      _ ≤ r * N := Nat.le_mul_of_pos_right r hNpos

theorem bigSizes : ∀ (g n : ℕ), n.Prime → Odd n → ∃ k j : ℕ, 2 ≤ k ∧ 1 ≤ j ∧ ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω), S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  intro g n hp _
  have hn : 1 < n := hp.one_lt
  set k := (1 + 2 * g * 2 ^ g) + 2 with hk
  set N₀ := (n ^ k) ^ 2 with hN₀
  set M := 6 * (N₀ ^ g * g.factorial) + 2 * (N₀ ^ g * g.factorial) * (g * 4 ^ g) with hM
  refine ⟨k, M + 1, by omega, by omega, ?_⟩
  intro o Ω _ _ _ S hg hN hr
  have hkN : 1 + 2 * g * 2 ^ g < N₀ := by
    have h1 : k < n ^ k := Nat.lt_pow_self hn
    have h2 : n ^ k ≤ (n ^ k) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hjr : M < n ^ (M + 1) := by
    have := Nat.lt_pow_self (n := M + 1) hn
    omega
  unfold GlobalTheory.ZH.ThetaSys.Big
  rw [hg, hN, hr]
  exact bigSizes_of g N₀ (n ^ (M + 1)) hkN hjr

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.UTestBaseChange

theorem baseChange : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsDiscreteValuationRing V₂] [Algebra (FractionRing V₂) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ → (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) → ∀ σ : FractionRing u.V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing u.V) (PadicAlgCl p) →
  ∃ (u' : ρ.UTest p y₀) (τ : FractionRing V₂ →+* FractionRing u'.V) (e : u'.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).comp τ = algebraMap (FractionRing V₂) (PadicAlgCl p) ∧
    (∀ χ r, u.PsiNorm (e χ) r → u'.PsiNorm χ r) ∧
    (∀ x, (T x).left ≫ u.φ = x.left ≫ u'.φ) ∧
    (∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) x', 1 ≤ m → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk'.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x')) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk' : QkPt u'.D.toPre (PadicAlgCl p) m, e pk'.y = pk.y ∧ QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' (T.symm x)) := by
  intro o Ω _ _ _ S ρ p _ y₀ u V₂ _ _ _ _ hc₂ hn₂ σ hσ
  have inj₂ := IsFractionRing.injective V₂ (FractionRing V₂)
  have hσv : ∀ z, algebraMap (FractionRing V₂) (PadicAlgCl p) (σ z) = algebraMap (FractionRing u.V) (PadicAlgCl p) z :=
    fun z => RingHom.congr_fun hσ z
  have hmem : ∀ v : u.V, σ (algebraMap u.V (FractionRing u.V) v) ∈ Set.range (algebraMap V₂ (FractionRing V₂)) :=
    fun v => (hn₂ _).1 (by rw [hσv]; exact (u.norm_le _).2 ⟨v, rfl⟩)
  choose gf hgf using hmem
  let g : u.V →+* V₂ :=
    { toFun := gf
      map_one' := inj₂ (by rw [hgf, map_one, map_one, map_one])
      map_mul' := fun a b => inj₂ (by rw [map_mul, hgf, hgf, hgf, map_mul, map_mul])
      map_zero' := inj₂ (by rw [hgf, map_zero, map_zero, map_zero])
      map_add' := fun a b => inj₂ (by rw [map_add (f := _), hgf, hgf, hgf, map_add (f := _), map_add (f := _)]) }
  have hgv : ∀ v, algebraMap V₂ (FractionRing V₂) (g v) = σ (algebraMap u.V _ v) := hgf
  have hK : σ.comp (algebraMap u.V _) = (algebraMap V₂ _).comp g := RingHom.ext fun v => (hgv v).symm
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V) (σ.injective (by rw [← hgv, ← hgv, h]))
  have hI : (IsLocalRing.maximalIdeal u.V).map g ≤ IsLocalRing.maximalIdeal V₂ := by
    rw [Ideal.map_le_iff_le_comap]
    intro v hv
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    apply (IsLocalRing.mem_maximalIdeal _).1 hv
    have hv0 : algebraMap u.V (FractionRing u.V) v ≠ 0 := by
      intro h0
      have : g v = 0 := inj₂ (by rw [hgv, h0, map_zero, map_zero])
      rw [← hw] at this
      exact w.ne_zero this
    have e1 : algebraMap V₂ (FractionRing V₂) (w⁻¹ : V₂ˣ) = σ (algebraMap u.V _ v)⁻¹ := by
      rw [map_inv₀ σ, ← hgv, ← hw]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    obtain ⟨t, ht⟩ := (u.norm_le _).1 (by rw [← hσv, ← e1]; exact (hn₂ _).2 ⟨_, rfl⟩)
    refine isUnit_iff_exists_inv.2 ⟨t, IsFractionRing.injective u.V (FractionRing u.V) ?_⟩
    rw [map_mul, ht, mul_inv_cancel₀ hv0, map_one]
  have aV : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have aV₂ : AdmBase V₂ (IsLocalRing.maximalIdeal V₂) := ⟨inferInstance, inferInstance, inferInstance, hc₂⟩
  have sq : spMap σ ≫ jK u.V = jK V₂ ≫ spMap g := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hK
  obtain ⟨D', hD, A', gA, U', hPU, gp, hL, hgen⟩ := GlobalTheory.UnifMove.exists_pull aV aV₂ g hg hI σ sq u.semi u.U
  have hyK : spMap (σ.comp u.yK) = spMap σ ≫ spMap u.yK :=
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom σ))
  have cart' : IsGrpPullback A'.A ρ.P.A (spMap (σ.comp u.yK)) (gA ≫ u.φ) := (gp.comp u.cart).congr hyK.symm rfl
  have lb' : LBIso A'.L (ρ.P.L.pull (gA ≫ u.φ)) :=
    LBIso.trans A'.isLB (pull_isLB u.A.isLB gA) (pull_isLB ρ.P.isLB _) hL (GlobalTheory.PolDeg.lbIso_pull_comp u.lb gA rfl)
  have semi' : IsSemiAbelian ((Over.pullback (specOf g)).obj u.G) :=
    GlobalTheory.isSemiAbelian_of_unifPre_dvr V₂ D' A' _ U'.toUnifPre
  have fac' : (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp (σ.comp u.yK) = y₀ := by
    rw [← RingHom.comp_assoc, hσ, u.fac]
  let u' : ρ.UTest p y₀ :=
    { V := V₂, complete := hc₂, norm_le := hn₂, yK := σ.comp u.yK, fac := fac'
      A := A', φ := gA ≫ u.φ, cart := cart', lb := lb'
      G := (Over.pullback (specOf g)).obj u.G, semi := semi', D := D', U := U' }
  have sF : jFK (R := V₂) (PadicAlgCl p) ≫ spMap σ = jFK (R := u.V) (PadicAlgCl p) := by
    refine (Spec.map_comp _ _).symm.trans ?_
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hσ
  have wI : ∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A,
      x.left ≫ u.A.A.hom = jFK (R := V₂) (PadicAlgCl p) ≫ spMap σ :=
    fun x => (Over.w x).trans sF.symm
  let Tf : (TFK (R := V₂) (PadicAlgCl p) ⟶ A'.A) → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) := fun x =>
    Over.homMk (x.left ≫ gA) (by
      show (x.left ≫ gA) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p)
      rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w x]; exact sF)
  let Ti : (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) → (TFK (R := V₂) (PadicAlgCl p) ⟶ A'.A) := fun x =>
    Over.homMk (gp.1.lift x.left (jFK (R := V₂) (PadicAlgCl p)) (wI x)) (gp.1.lift_snd _ _ _)
  let T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    { toFun := Tf, invFun := Ti
      left_inv := fun x => Over.OverMorphism.ext
        (gp.1.hom_ext (gp.1.lift_fst _ _ _) ((gp.1.lift_snd _ _ _).trans (Over.w x).symm))
      right_inv := fun x => Over.OverMorphism.ext (gp.1.lift_fst _ _ _) }
  have hT : ∀ x, (T x).left = x.left ≫ gA := fun x => rfl
  have hTs : ∀ x, (T.symm x).left ≫ gA = x.left := fun x => gp.1.lift_fst _ _ _
  have hL2 := GlobalTheory.abelianSchemeLaws_all
  have hFc : ∀ r : u.V, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) r) =
      algebraMap (FractionRing V₂) (PadicAlgCl p) (algebraMap V₂ (FractionRing V₂) (g r)) := fun r => by
    rw [hgv]; exact (hσv _).symm
  have hτall := fun m : ℕ => GlobalTheory.exists_qk_pull_equiv hL2.1 hL2.2 u.V V₂ g u.D.toPre D'.toPre hD u.D.tau_bimult
    D'.tau_bimult (PadicAlgCl p) hFc m
  choose τq hτq using hτall
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj u.G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  have fwd : ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
      (x' : TFK (R := V₂) (PadicAlgCl p) ⟶ A'.A), 1 ≤ m → x'.left ≫ gA = x.left →
      QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU U'.toUnifPre (PadicAlgCl p) m (τq m pk) x' := by
    intro m pk x x' hm hx H
    obtain ⟨hy, hgq⟩ := ((hτq m).1 pk _).1 rfl
    refine GlobalTheory.qkToAk_baseChange hL2.1.globalFns hL2.1.secBaseChange u.V V₂ _ _ aV aV₂ g u.D u.A u.G u.U
      _ (Iso.refl _) mR A' D' hD U' hPU (PadicAlgCl p) hFc m hm pk x (τq m pk) x' hy hgq ?_ H
    have n : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
    have hbc : (Iso.refl ((Over.pullback (specOf g)).obj u.G)).hom.left ≫ pullback.fst u.G.hom (specOf g) =
        pullback.fst u.G.hom (spMap g) := Category.id_comp _
    rw [hbc, ← hgen, ← Category.assoc U'.gen.inv.left, n, Category.id_comp, ← Category.assoc, hx]
  refine ⟨u', RingHom.id _, hD.xe, T, rfl, ?_, fun x => Category.assoc _ _ _, ?_, ?_⟩
  · intro χ r h j hj
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZH.RealCase.exists_chart u (hD.xe χ)
    have e := GlobalTheory.ZH.PsiNormPull.norm_psi_pull p u.V V₂ g (fun v => by rw [hgv]; exact (hσv _).symm)
      (fun v => (hn₂ _).2 ⟨v, rfl⟩) u.D.toPre D'.toPre hD χ (j₀ PUnit.unit) (j PUnit.unit) hj₀ hj
    exact e.trans (h j₀ hj₀)
  · intro m pk' x' hm H'
    obtain ⟨w₀, hw₀⟩ := U'.ext
    open MonObj in
    have ht' : x' ^ m = 1 := (H' w₀ hw₀).1
    open MonObj in
    have ht : (T x') ^ m = 1 := GlobalTheory.ThetaDescent.pow_eq_one_of_pull sF gp (hT x').symm ht'
    have hmF : ((m : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨pk₀, H₀⟩ := GlobalTheory.TorsionAnyChar.exists_qkToAkU u.V _ aV u.D u.A u.G u.semi u.U (PadicAlgCl p) m hmF
      (T x') ht
    have H₁ : QkToAkU U'.toUnifPre (PadicAlgCl p) m (τq m pk₀) x' := fwd m pk₀ (T x') x' hm rfl H₀
    have hE : QkPt.Equiv D'.toPre (PadicAlgCl p) (τq m pk₀) pk' :=
      GlobalTheory.TorsionMapInj.qkToAk_injective_closed V₂ _ aV₂ D' A' _ semi' U' (PadicAlgCl p) m hm _ _ x' H₁ H'
    have hE' : QkPt.Equiv u.D.toPre (PadicAlgCl p) pk₀ ((τq m).symm pk') :=
      ((hτq m).2.1 pk₀ ((τq m).symm pk')).2 (by rw [Equiv.apply_symm_apply]; exact hE)
    obtain ⟨hy, -⟩ := ((hτq m).1 ((τq m).symm pk') pk').1 (Equiv.apply_symm_apply _ _)
    refine ⟨(τq m).symm pk', ?_, GlobalTheory.ArcClauseCompare.qkToAkU_of_equiv u.U.toUnifPre hm hE' H₀⟩
    rw [hy, AddEquiv.apply_symm_apply]
  · intro m pk x hm H
    obtain ⟨hy, -⟩ := ((hτq m).1 pk _).1 rfl
    exact ⟨τq m pk, by rw [hy]; exact hD.xe.apply_symm_apply _, fwd m pk x (T.symm x) hm (hTs x) H⟩
end GlobalTheory.Poinc.UTestBaseChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UTraitHyp

theorem hypS_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  intro V _ _ I E _ _ _ H t P
  letI := P.A.isAb.comm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ t.G P.A.A (jK V) _ t.PP.L P.A.L t.PP.isLB P.A.isLB h1 h2
    ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
      by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

end GlobalTheory.UTraitHyp

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (A₁ : PolAV (Sp (FractionRing R₁))), (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) → ∀ (n k j : ℕ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : R₁) → ∀ (ζ : R₁ˣ), ReciprocityTheory.ChartRestriction.G.Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ)) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : GlobalTheory.ZH.ArithBase o Ω) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (b : o →+* R₁) (e : Ω →+* FractionRing R₁) (φ : A₁.A.left ⟶ ρS.P.A.left), S.g = A₁.g ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) ∧ IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ ∧ LBIso A₁.L (ρS.P.L.pull φ) := by
  first | exact @GlobalTheory.Mum.exists_thetaSys_spread | exact GlobalTheory.Mum.exists_thetaSys_spread | (intros; apply GlobalTheory.Mum.exists_thetaSys_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ExpansionNonzero

theorem exists_term_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  intro V _ _ _ hV D' A' G' _ _ U' U₀ _ σ' f' hf ⟨j, hj⟩
  have := hV.1
  have := U'.semi.smooth
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have := FibreNonzero.isIso_snd_left G'
  have : IsReduced (𝟙_ _ ⊗ G').left := isReduced_of_isOpenImmersion (snd (𝟙_ _) G').left
  have h : (𝟙_ _ ⊗ G').left.basicOpen (σ'.f j) ≠ ⊥ := fun h => hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  refine GlobalTheory.SectionUnif.exists_term_ne_zero (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge U' 1 σ' f' hf y ?_
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

end GlobalTheory.ExpansionNonzero
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  first | exact @GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field | exact GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field | (intros; apply GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field <;> assumption)
end
