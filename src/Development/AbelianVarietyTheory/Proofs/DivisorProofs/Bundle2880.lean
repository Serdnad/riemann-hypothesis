module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep


open Module in
theorem comap_map_eq_of_isUnit_finrank : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing V'] [IsDomain V'] [Algebra V V'] [Module.Finite V V'], Function.Injective (algebraMap V V') → IsUnit ((Module.finrank V V' : ℕ) : V) → ∀ I : Ideal V, (I.map (algebraMap V V')).comap (algebraMap V V') = I := by
  intro V V' _ _ _ _ _ _ _ hinj hunit I
  refine le_antisymm ?_ Ideal.le_comap_map
  let K := FractionRing V
  let L := FractionRing V'
  have hinjL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V V' L]
    exact (IsFractionRing.injective V' L).comp hinj
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinjL
  letI : Algebra K L := FractionRing.liftAlgebra V L
  haveI : IsScalarTower V K L := FractionRing.isScalarTower_liftAlgebra V L
  have hrank : finrank K L = finrank V V' := IsFractionRing.finrank_eq V K V' L
  have hn0 : finrank K L ≠ 0 := by
    intro h
    rw [← hrank, h, Nat.cast_zero] at hunit
    exact not_isUnit_zero hunit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hn0)
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'

  have htrV : ∀ z : V', ∃ t : V, algebraMap V K t = Algebra.trace K L (algebraMap V' L z) := by
    intro z
    have hz : IsIntegral V (algebraMap V' L z) :=
      (Algebra.IsIntegral.isIntegral (R := V) z).map (IsScalarTower.toAlgHom V V' L)
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hz)
  have hmul : ∀ (i : V) (w : L), Algebra.trace K L (algebraMap V L i * w) =
      algebraMap V K i * Algebra.trace K L w := by
    intro i w
    rw [IsScalarTower.algebraMap_apply V K L, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have key : ∀ y ∈ I.map (algebraMap V V'), ∀ z : V', ∃ c ∈ I,
      algebraMap V K c = Algebra.trace K L (algebraMap V' L (z * y)) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩ z
      obtain ⟨t, ht⟩ := htrV z
      refine ⟨i * t, I.mul_mem_right t hi, ?_⟩
      rw [map_mul, ht, mul_comm z, map_mul, ← IsScalarTower.algebraMap_apply V V' L, hmul]
    · intro z
      exact ⟨0, I.zero_mem, by simp⟩
    · intro x y _ _ hx hy z
      obtain ⟨c, hc, hcx⟩ := hx z
      obtain ⟨d, hd, hdy⟩ := hy z
      exact ⟨c + d, I.add_mem hc hd, by rw [map_add (f := _), hcx, hdy, mul_add, map_add (f := _), map_add (f := _)]⟩
    · intro w x _ hx z
      obtain ⟨c, hc, hcx⟩ := hx (z * w)
      exact ⟨c, hc, by rw [hcx, smul_eq_mul, _root_.mul_assoc]⟩
  intro a ha
  obtain ⟨c, hc, hca⟩ := key _ ha 1
  rw [_root_.one_mul, ← IsScalarTower.algebraMap_apply V V' L, IsScalarTower.algebraMap_apply V K L,
    Algebra.trace_algebraMap, hrank, nsmul_eq_mul, ← map_natCast (algebraMap V K), ← map_mul] at hca
  have hc' : c = (finrank V V' : V) * a := IsFractionRing.injective V K hca
  obtain ⟨u, hu⟩ := hunit
  have : a = ↑u⁻¹ * c := by rw [hc', ← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [this]
  exact I.mul_mem_left _ hc

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


open KaehlerDifferential TensorProduct in
theorem mapBaseChange_residueField_bijective_of_etale_fibre :
    ∀ (A C B Ω : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Field Ω] [Algebra A Ω] (Q : Ideal B) [Q.IsPrime] (Q' : Ideal (TensorProduct A Ω B)) [Q'.IsPrime] (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = Q → f ∉ Q' → ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale → Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) := by
  intro A C B Ω _ _ _ _ _ _ _ _ _ Q _ Q' _ f hQ hf het
  classical
  letI : Algebra C (TensorProduct A Ω C) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (TensorProduct A Ω B) := Algebra.TensorProduct.rightAlgebra
  set ψ := ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp
    (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom) with hψ
  letI : Algebra (TensorProduct A Ω C) (Localization.Away f) := ψ.toAlgebra
  haveI : Algebra.Etale (TensorProduct A Ω C) (Localization.Away f) := het
  haveI : IsScalarTower Ω (TensorProduct A Ω C) (Localization.Away f) :=
    IsScalarTower.of_algebraMap_eq fun w => by
      change _ = ψ _
      simp [hψ, Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply Ω (TensorProduct A Ω B) (Localization.Away f)]

  have hunit : IsUnit (algebraMap (TensorProduct A Ω B) Q'.ResidueField f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]; exact hf
  letI : Algebra (Localization.Away f) Q'.ResidueField :=
    (Localization.awayLift (algebraMap (TensorProduct A Ω B) Q'.ResidueField) f hunit).toAlgebra
  have hlift : ∀ s, algebraMap (Localization.Away f) Q'.ResidueField
      (algebraMap (TensorProduct A Ω B) (Localization.Away f) s) =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField s := fun s =>
    IsLocalization.Away.lift_eq f hunit s
  have hBK : ∀ b : B, algebraMap B Q'.ResidueField b =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField (algebraMap B (TensorProduct A Ω B) b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q') Q'.ResidueField,
      IsScalarTower.algebraMap_apply B (TensorProduct A Ω B) (Localization.AtPrime Q'),
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra C Q'.ResidueField := ((algebraMap B Q'.ResidueField).comp (algebraMap C B)).toAlgebra
  haveI : IsScalarTower C B Q'.ResidueField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨eB, heB⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω B (TensorProduct A Ω B)
    (Localization.Away f) Q'.ResidueField (fun x => by rw [hlift, hBK])
  obtain ⟨eC, heC⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω C (TensorProduct A Ω C)
    (Localization.Away f) Q'.ResidueField (fun x => by
      change algebraMap B Q'.ResidueField (algebraMap C B x) =
        algebraMap (Localization.Away f) Q'.ResidueField (ψ ((1 : Ω) ⊗ₜ[A] x))
      rw [hBK, hψ, RingHom.comp_apply, hlift]
      congr 1)
  set K := Q'.ResidueField
  let E := eC.trans eB.symm
  have hE : ∀ c : C, E ((1 : K) ⊗ₜ[C] KaehlerDifferential.D A C c) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (algebraMap C B c) := by
    intro c
    simp only [E, LinearEquiv.trans_apply, heC, LinearEquiv.symm_apply_eq, heB]
    rfl
  have hE' : ∀ ω : Ω[C⁄A], E ((1 : K) ⊗ₜ[C] ω) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro ω
    have hω : ω ∈ Submodule.span C (Set.range (KaehlerDifferential.D A C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; rw [hE, KaehlerDifferential.map_D]
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _), TensorProduct.tmul_add]
    | smul c x _ hx =>
      have h1 : (1 : K) ⊗ₜ[C] (c • x) = algebraMap C K c • ((1 : K) ⊗ₜ[C] x) := by
        rw [TensorProduct.tmul_smul]; exact (algebraMap_smul K c _).symm
      rw [h1, map_smul, hx, LinearMap.map_smul_of_tower, ← algebraMap_smul B c,
        TensorProduct.tmul_smul, ← algebraMap_smul K (algebraMap C B c)]
      rfl
  have hE'' : ∀ (k : K) (ω : Ω[C⁄A]), E (k ⊗ₜ[C] ω) = k ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro k ω
    have h1 : k ⊗ₜ[C] ω = k • ((1 : K) ⊗ₜ[C] ω) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h1, map_smul, hE', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  letI : Algebra Q.ResidueField K :=
    (Ideal.ResidueField.map Q Q' (algebraMap B (TensorProduct A Ω B)) (by rw [← hQ]; rfl)).toAlgebra
  haveI : IsScalarTower B Q.ResidueField K := IsScalarTower.of_algebraMap_eq fun b => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap, hBK]
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_bijective_iff_bijective Q.ResidueField K]
  let cM := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K
    (TensorProduct C B Ω[C⁄A])
  let cN := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K Ω[B⁄A]
  let cC := TensorProduct.AlgebraTensorModule.cancelBaseChange C B K K Ω[C⁄A]
  have key : ∀ z, ((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K z =
      cN.symm (E (cC (cM z))) := by
    intro z
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add (f := _), h₁, h₂]
      | tmul l m =>
        induction m using TensorProduct.induction_on with
        | zero => simp
        | add m₁ m₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add (f := _), h₁, h₂]
        | tmul b ω =>
          simp only [cM, cN, cC, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            KaehlerDifferential.mapBaseChange_tmul, hE'', TensorProduct.smul_tmul]
  have hfun : ⇑(((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K) =
      ⇑cN.symm ∘ ⇑E ∘ ⇑cC ∘ ⇑cM := funext key
  rw [hfun]
  exact cN.symm.bijective.comp (E.bijective.comp (cC.bijective.comp cM.bijective))

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory

theorem fibre_exists_finite_generizing {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z)
    (hq : Continuous q) (z : Z) :
    ∃ T : Set Y, T.Finite ∧ (∀ e ∈ T, q e = z) ∧ ∀ w, q w = z → ∃ e ∈ T, e ⤳ w := by
  have hfin : (irreducibleComponents (q ⁻¹' {z})).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have key : ∀ C : irreducibleComponents (q ⁻¹' {z}),
      ∃ e : Y, q e = z ∧ ∀ c ∈ C.1, e ⤳ (c : Y) := by
    intro C
    have hC : IsIrreducible C.1 := C.2.1
    have hCi : IsIrreducible (((↑) : q ⁻¹' {z} → Y) '' C.1) :=
      hC.image _ continuous_subtype_val.continuousOn
    have hgen := hCi.isGenericPoint_genericPoint_closure
    refine ⟨hCi.genericPoint, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hC.nonempty
      have hcz : q c = z := c.2
      have h1 : hCi.genericPoint ⤳ (c : Y) := hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
      have h2 : hCi.genericPoint ∈ closure (((↑) : q ⁻¹' {z} → Y) '' C.1) := hgen.mem
      have h3 : closure (((↑) : q ⁻¹' {z} → Y) '' C.1) ⊆ q ⁻¹' closure {z} :=
        (closure_mono (by rintro _ ⟨d, -, rfl⟩; exact d.2)).trans (hq.closure_preimage_subset _)
      have h4 : z ⤳ q hCi.genericPoint := specializes_iff_mem_closure.2 (h3 h2)
      have h5 : q hCi.genericPoint ⤳ z := by
        have := h1.map hq
        rwa [hcz] at this
      exact (h5.antisymm h4).eq
    · intro c hc
      exact hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
  choose f hf using key
  haveI : Finite (irreducibleComponents (q ⁻¹' {z})) := hfin.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨C, rfl⟩
    exact (hf C).1
  · intro w hw
    let w' : q ⁻¹' {z} := ⟨w, hw⟩
    refine ⟨f ⟨_, irreducibleComponent_mem_irreducibleComponents w'⟩, ⟨_, rfl⟩, ?_⟩
    exact (hf _).2 w' mem_irreducibleComponent

theorem fibre_const_of_specializes_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  intro Y Z _ _ _ _ _ q hq z hpc P hP a b ha hb hPa
  obtain ⟨T, hTf, hTz, hTs⟩ := fibre_exists_finite_generizing q hq z
  by_contra hPb
  have closed : ∀ R : Y → Prop, IsClosed (⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y)) :=
    fun R => (hTf.subset (show {e ∈ T | R e} ⊆ T from fun _ h => h.1)).isClosed_biUnion (fun _ _ => isClosed_closure)
  have mem : ∀ (R : Y → Prop) (e w : Y), e ∈ T → R e → e ⤳ w →
      w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) := by
    intro R e w he hR hs
    exact Set.mem_biUnion ⟨he, hR⟩ (specializes_iff_mem_closure.1 hs)
  have mem' : ∀ (R : Y → Prop) (w : Y), w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) →
      ∃ e, e ∈ T ∧ R e ∧ e ⤳ w := by
    intro R w hw
    obtain ⟨e, ⟨he, hR⟩, hc⟩ := Set.mem_iUnion₂.1 hw
    exact ⟨e, he, hR, specializes_iff_mem_closure.2 hc⟩
  obtain ⟨w, hwS, hwt, hwt'⟩ := isPreconnected_closed_iff.1 hpc _ _ (closed P) (closed (fun e => ¬ P e))
    (by
      intro w hw
      obtain ⟨e, he, hs⟩ := hTs w hw
      by_cases h : P e
      · exact Or.inl (mem P e w he h hs)
      · exact Or.inr (mem _ e w he h hs))
    (by
      obtain ⟨e, he, hs⟩ := hTs a ha
      exact ⟨a, ha, mem P e a he ((hP e a (hTz e he) ha hs).2 hPa) hs⟩)
    (by
      obtain ⟨e, he, hs⟩ := hTs b hb
      exact ⟨b, hb, mem (fun e => ¬ P e) e b he (fun h => hPb ((hP e b (hTz e he) hb hs).1 h)) hs⟩)
  have hwz : q w = z := hwS
  obtain ⟨e₁, h₁, hP₁, hs₁⟩ := mem' P w hwt
  obtain ⟨e₂, h₂, hP₂, hs₂⟩ := mem' _ w hwt'
  exact hP₂ ((hP e₂ w (hTz e₂ h₂) hwz hs₂).2 ((hP e₁ w (hTz e₁ h₁) hwz hs₁).1 hP₁))

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreTransport

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ G₂ : Over S'} [GrpObj G₁] [GrpObj G₂]
    {f₁ f₂ : S' ⟶ S} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁)
    (h₂ : IsGrpPullback G₂ G f₂ φ₂) (hf : f₁ = f₂) :
    ∃ e : G₁.left ⟶ G₂.left, IsGrpPullback G₁ G₂ (𝟙 S') e ∧ e ≫ φ₂ = φ₁ := by
  subst hf
  refine ⟨h₂.1.lift φ₁ G₁.hom h₁.1.w, IsGrpPullback.cancel h₂ ?_ ?_, h₂.1.lift_fst _ _ _⟩
  · rw [h₂.1.lift_fst, Category.id_comp]; exact h₁
  · rw [h₂.1.lift_snd]; simp

theorem isGrpPullback_of_isIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    [IsMonHom e] [IsIso e] : IsGrpPullback G₁ G₂ (𝟙 S) e.left := by
  haveI : IsIso e.left := inferInstanceAs (IsIso ((Over.forget S).map e))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ e := Over.OverMorphism.ext (by simp [k, hx])
  have ey : y₀ = k ≫ y ≫ e := Over.OverMorphism.ext (by simp [k, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [k]

theorem transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro V V₁ K _ _ _ B _ ρ ev σ f₁ hm hi
  have sp : ∀ t : V₁ →+* K, spMap (t.comp ρ) = spMap t ≫ spMap ρ := fun t => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have two : ∀ t : V₁ →+* K, IsGrpPullback ((Over.pullback (spMap t)).obj ((Over.pullback (spMap ρ)).obj B)) B
      (spMap t ≫ spMap ρ) (pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap t) ≫ pullback.fst B.hom (spMap ρ)) :=
    fun t => (isGrpPullback_pullback _ (spMap t)).comp (isGrpPullback_pullback B (spMap ρ))
  obtain ⟨e₀, h₀, w₀⟩ := exists_compare (isGrpPullback_pullback B (spMap (ev.comp ρ))) (two ev) (sp ev)
  obtain ⟨e₁, h₁, w₁⟩ := exists_compare (two (σ.toRingHom.comp ev))
    (isGrpPullback_pullback B (spMap (σ.toRingHom.comp (ev.comp ρ)))) (sp (σ.toRingHom.comp ev)).symm
  refine ⟨e₀ ≫ f₁.left ≫ e₁, ?_, fun T x y hy₁ hy₂ => ?_⟩
  · have := h₀.comp ((isGrpPullback_of_isIso f₁).comp h₁)
    rwa [Category.id_comp, Category.id_comp] at this
  · have hx : x = y ≫ e₀ := by
      refine (two ev).1.hom_ext ?_ ?_
      · rw [Category.assoc, w₀]; exact hy₁.symm
      · rw [Category.assoc, h₀.1.w, Category.comp_id]; exact hy₂.symm
    rw [hx, Category.assoc, Category.assoc, Category.assoc, w₁]

end GlobalTheory.FibreTransport
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Twist

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (b : R →+* R') (a : R' →+* R'') :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem twist_fibre_iso : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (L : LB X.left), L.IsLB →
  ∀ (K : Type) [Field K]
  (ev : V₁ →+* K) (σ : K ≃+* K) (K₀ : Type) [Field K₀] (e : K₀ →+* K), σ.toRingHom.comp e = e →
  ∀ (Z : Over (Sp K)) [GrpObj Z] (LZ : LB Z.left), LZ.IsLB → ∀ (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  LBIso (L.pull (pullback.fst X.hom (spMap ev))) (LZ.pull ψ) →
  ∀ (Y : Over (Sp K₀)) [GrpObj Y] (L₀ : LB Y.left), L₀.IsLB → ∀ (φ : Z.left ⟶ Y.left), IsGrpPullback Z Y (spMap e) φ →
  LBIso LZ (L₀.pull φ) →
  ∃ f : ((Over.pullback (spMap ev)).obj X).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X).left,
    IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) (𝟙 _) f ∧
    LBIso (L.pull (pullback.fst X.hom (spMap ev))) (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) ∧
    ∀ (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left) (y₀ : Sp K₀ ⟶ Y.left), q ≫ ψ ≫ φ = spMap e ≫ y₀ →
      q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
      q ≫ f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst X.hom (spMap ev) := by
  intro V₁ _ X _ L hL K _ ev σ K₀ _ e hσe Z _ LZ hLZ ψ hψ H1 Y _ L₀ hL₀ φ hφ H2
  have hs : spMap σ.toRingHom ≫ spMap e = spMap e := by rw [spMap_comp_spMap, hσe]
  have hev : spMap σ.toRingHom ≫ spMap ev = spMap (σ.toRingHom.comp ev) := spMap_comp_spMap _ _
  have hX := isGrpPullback_pullback X (spMap ev)
  have hXσ := isGrpPullback_pullback X (spMap (σ.toRingHom.comp ev))
  have hχ := hψ.comp hφ
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : pullback X.hom (spMap (σ.toRingHom.comp ev)) ⟶ pullback X.hom (spMap ev),
      ρ ≫ pullback.fst X.hom (spMap ev) = pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) ∧
      ρ ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) ≫ spMap σ.toRingHom :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ.toRingHom)
      (by rw [pullback.condition, Category.assoc, hev]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hρ : IsGrpPullback ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) ((Over.pullback (spMap ev)).obj X)
      (spMap σ.toRingHom) ρ := hX.cancel (hXσ.congr hev.symm hρ1.symm) hρ2
  have hσχ := hρ.comp hχ
  obtain ⟨f, hf1, hf2⟩ : ∃ f : pullback X.hom (spMap ev) ⟶ pullback X.hom (spMap (σ.toRingHom.comp ev)),
      f ≫ ρ ≫ ψ ≫ φ = ψ ≫ φ ∧
      f ≫ pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd X.hom (spMap ev) :=
    ⟨hσχ.1.lift (ψ ≫ φ) (pullback.snd X.hom (spMap ev))
      (by rw [hχ.1.w]; simp only [Category.id_comp, hs]; try rfl), hσχ.1.lift_fst _ _ _, hσχ.1.lift_snd _ _ _⟩
  have hfg : IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X)
      (𝟙 _) f :=
    hσχ.cancel (hχ.congr (by simp only [Category.id_comp, hs]) hf1.symm)
      (by rw [Category.comp_id]; exact hf2)
  have hτ1 : f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = (f ≫ ρ) ≫ pullback.fst X.hom (spMap ev) := by
    rw [Category.assoc, hρ1]
  have hτχ : (f ≫ ρ) ≫ ψ ≫ φ = ψ ≫ φ := by rw [Category.assoc, hf1]
  have hτ2 : (f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap ev) ≫ spMap σ.toRingHom := by
    rw [Category.assoc, hρ2, ← Category.assoc, hf2]
  refine ⟨f, hfg, ?_, ?_⟩
  · have K1 : LBIso (LZ.pull ψ) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull LZ ψ ψ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => φ) _ ψ fun _ => rfl) H2
    have hA := pull_isLB hL (pullback.fst X.hom (spMap ev))
    have hC := pull_isLB hL₀ (ψ ≫ φ)
    have AC := LBIso.trans hA (pull_isLB hLZ ψ) hC H1 K1
    have D : LBIso (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => pullback.fst X.hom (spMap ev)) _ (f ≫ ρ) fun _ => hτ1)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => ψ ≫ φ) _ (f ≫ ρ) fun _ => hτχ.symm) AC
    exact LBIso.trans hA hC (pull_isLB hL _) AC D.symm
  · intro q y₀ hq hq'
    have hqτ : q ≫ f ≫ ρ = spMap σ.toRingHom ≫ q := by
      apply hχ.1.hom_ext
      · rw [Category.assoc, hτχ, hq, Category.assoc, hq, ← Category.assoc, hs]
      · show (q ≫ f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = (spMap σ.toRingHom ≫ q) ≫ pullback.snd X.hom (spMap ev)
        rw [Category.assoc, hτ2, ← Category.assoc, hq', Category.assoc, hq', Category.id_comp, Category.comp_id]
    rw [hτ1, ← Category.assoc, hqτ, Category.assoc]

end GlobalTheory.Poinc.Sep.Twist
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_baseChange : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  first | exact @GlobalTheory.SymBaseChange.symm_pull | exact GlobalTheory.SymBaseChange.symm_pull | (intros; apply GlobalTheory.SymBaseChange.symm_pull <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.fibre_const_of_specialisation_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  first | exact @GlobalTheory.fibre_const_of_specializes_invariant | exact GlobalTheory.fibre_const_of_specializes_invariant | (intros; apply GlobalTheory.fibre_const_of_specializes_invariant <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibre_iso_grpPullback_identity_transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  first | exact @GlobalTheory.FibreTransport.transport | exact GlobalTheory.FibreTransport.transport | (intros; apply GlobalTheory.FibreTransport.transport <;> assumption)

end
end
