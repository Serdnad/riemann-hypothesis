module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle484
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dualBasis_coord_mem_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ M _ _ _ _ k lb l hl j
  haveI : Module.Free O M := Module.free_of_flat_of_isLocalRing
  let ε := Module.Free.chooseBasis O M
  have hsum : l = ∑ i, l (ε i) • ε.dualBasis i := by
    refine ε.ext fun a => ?_
    simp [Module.Basis.dualBasis_apply_self, Finset.sum_apply, LinearMap.sum_apply]

  rw [hsum, map_sum]
  simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hl _)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.FGFun

theorem fg_functionField : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (sG : G ⟶ Sp F), IsProjOver sG → ∀ (P Ω : Type) [Field P] [Field Ω] (φ : P →+* G.functionField) (t : Sp P ⟶ Sp F) (ι : G.functionField →+* Ω), spMap ι ≫ G.fromSpecStalk (genericPoint G) ≫ sG = spMap ι ≫ spMap φ ≫ t → (letI := φ.toAlgebra; (⊤ : IntermediateField P G.functionField).FG) := by
  intro F _ G _ sG hproj P Ω _ _ φ t ι h
  letI := φ.toAlgebra
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  obtain ⟨β, hβ⟩ := Spec.map_surjective (G.fromSpecStalk (genericPoint G) ≫ sG)
  have hβτ : ∀ c : F, β.hom c = φ (τ.hom c) := by
    rw [← hβ] at h
    simp only [← Spec.map_comp] at h
    have h' := Spec.map_injective h
    intro c
    apply ι.injective
    have := congrArg (fun f => f.hom c) h'
    simpa using this
  have hft : LocallyOfFiniteType sG := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    haveI := isProper_str F N
    infer_instance
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint G))
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have e : U ≤ sG ⁻¹ᵁ ⊤ := by simp
  have hfin := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) sG hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  have key : sG.appLE ⊤ U e ≫ G.presheaf.germ U _ hx = (Scheme.ΓSpecIso (.of F)).hom ≫ β := by
    rw [← Scheme.ΓSpecIso_naturality, hβ, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have h3 : (Spec (G.presheaf.stalk (genericPoint G))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (G.presheaf.stalk (genericPoint G))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
    rw [h3]
    simp
  classical
  letI : Algebra Γ(Sp F, ⊤) Γ(G, U) := (sG.appLE ⊤ U e).hom.toAlgebra
  have hfin' : Algebra.FiniteType Γ(Sp F, ⊤) Γ(G, U) := hfin
  obtain ⟨s, hs⟩ := hfin'.out
  have hmem : ∀ a : Γ(G, U), (G.presheaf.germ U _ hx).hom a ∈
      IntermediateField.adjoin P ((s.image (G.presheaf.germ U _ hx).hom : Finset _) : Set G.functionField) := by
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(G, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx' =>
      exact IntermediateField.subset_adjoin _ _ (by rw [Finset.coe_image]; exact ⟨x, hx', rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f.hom r) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [RingHom.algebraMap_toAlgebra, this, hβτ]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨s.image (G.presheaf.germ U _ hx).hom, eq_top_iff.2 fun f _ => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen G U hU
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(G, U)) f
  exact div_mem (hmem a) (hmem b)

end GlobalTheory.FGFun
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem appLE_basicOpen_surjective_of_mul_mem_range {X Z : Scheme.{0}} (φ : X ⟶ Z) {V : Z.Opens}
    (haff : IsAffineOpen (φ ⁻¹ᵁ V)) (r : Γ(Z, V))
    (h : ∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b)
    (A : Z.Opens) (B : X.Opens) (e : B ≤ φ ⁻¹ᵁ A) (hA : A = Z.basicOpen r)
    (hB : B = X.basicOpen ((φ.app V).hom r)) : Function.Surjective (φ.appLE A B e) := by
  subst hA hB
  set s := (φ.app V).hom r with hs
  intro y
  let resX : Γ(X, φ ⁻¹ᵁ V) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  let resZ : Γ(Z, V) →+* Γ(Z, Z.basicOpen r) := (Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op).hom
  let g := (φ.appLE (Z.basicOpen r) (X.basicOpen s) e).hom
  haveI := haff.isLocalization_basicOpen s
  obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers s) y
  obtain ⟨b, hb⟩ := h c
  have hu : IsUnit (resZ r) := Z.toRingedSpace.isUnit_res_basicOpen r
  have hv : IsUnit (resX s) := X.toRingedSpace.isUnit_res_basicOpen s
  have hg : ∀ t, g (resZ t) = resX (φ.app V t) := by
    intro t
    simp only [g, resZ, resX]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hc' : y * resX s ^ n = resX c := by rw [← map_pow]; exact hc
  let x := resZ b * ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) ^ (n + 1)
  refine ⟨x, ?_⟩
  have hx : g x * resX s ^ (n + 1) = y * resX s ^ (n + 1) := by
    calc g x * resX s ^ (n + 1) = g (x * resZ r ^ (n + 1)) := by rw [RingHom.map_mul g x (resZ r ^ (n + 1)), map_pow, hg r]
      _ = g (resZ b) := by
          congr 1
          simp only [x, mul_assoc, ← mul_pow]
          rw [show ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) * resZ r = 1 from
            hu.val_inv_mul, one_pow, mul_one]
      _ = resX (φ.app V b) := hg b
      _ = resX (s * c) := by rw [hb]
      _ = y * resX s ^ (n + 1) := by rw [map_mul, ← hc']; ring
  exact (hv.pow (n + 1)).mul_left_inj.1 hx

theorem isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) →
      ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) →
        IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  intro X Z φ V hV haff r h
  have hpre : φ ⁻¹ᵁ Z.basicOpen r = X.basicOpen ((φ.app V).hom r) := Scheme.preimage_basicOpen φ r
  haveI : IsAffine (Z.basicOpen r) := hV.basicOpen r
  haveI : IsAffine (φ ⁻¹ᵁ Z.basicOpen r) := by
    have := haff.basicOpen ((φ.app V).hom r)
    rw [← hpre] at this
    exact this
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  exact appLE_basicOpen_surjective_of_mul_mem_range φ haff r h _ _ _ (by simp) (by simp [hpre])

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_of_isFinite_of_flat_geometric_fibres_over :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left :=
  fun S X Y f h1 h0 h2 h3 H =>
    flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S X Y f h1 h0 h2 h3 H

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem isAffineOpen_preimage_and_finite_app_of_isFinite_restrict :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  intro X Z φ V hV hf
  haveI : IsAffine (V : Scheme) := hV
  have h1 : IsAffine (φ ⁻¹ᵁ V : Scheme) := isAffine_of_isAffineHom (φ ∣_ V)
  refine ⟨h1, ?_⟩
  have h2 := hf.finite_app ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h2
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [← e]
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinSchemeRank

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₗ[R] S :=
    { e with map_smul' := fun r x => by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  rw [f.length_eq]
  exact Module.length_eq_of_surjective (S := R) (R := S) (M := S) e.surjective

theorem finrank_eq_length_of_isLocalRing (k : Type*) [Field k] [IsAlgClosed k] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra k A] [Module.Finite k A] :
    (Module.finrank k A : ℕ∞) = Module.length A A := by
  haveI : IsLocalHom (algebraMap k A) :=
    ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h => by simp [h] at ha⟩
  haveI : Module.Finite k (IsLocalRing.ResidueField A) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)).toLinearMap
      IsLocalRing.residue_surjective
  have hb : Function.Bijective (algebraMap k (IsLocalRing.ResidueField A)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have h1 : Module.length k (IsLocalRing.ResidueField A) = 1 := by
    rw [Module.length_eq_finrank,
      ← (AlgEquiv.ofBijective (Algebra.ofId k _) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
    rfl
  rw [← Module.length_eq_finrank, IsLocalRing.length_restrictScalars k A A,
    ← Module.length_eq_of_surjective (S := k) (R := IsLocalRing.ResidueField k)
      (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective, h1, _root_.mul_one]

theorem finrank_eq_card_mul (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] (m : ℕ∞)
    (hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m) :
    (Module.finrank k B : ℕ∞) = Nat.card (PrimeSpectrum B) * m := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI := Fintype.ofFinite (PrimeSpectrum B)
  have h : ∀ p : PrimeSpectrum B, (Module.finrank k (Localization.AtPrime p.asIdeal) : ℕ∞) = m := by
    intro p
    haveI : Module.Finite k (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective (Algebra.algHom k B (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
    rw [← hm p, finrank_eq_length_of_isLocalRing k]
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum B k, Nat.cast_sum]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem card_algHom_eq_card_primeSpectrum (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    Nat.card (B →ₐ[k] k) = Nat.card (PrimeSpectrum B) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  let F : (B →ₐ[k] k) → PrimeSpectrum B := fun φ => ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
  · intro φ ψ h
    have h' : RingHom.ker φ = RingHom.ker ψ := congrArg PrimeSpectrum.asIdeal h
    ext b
    have : b - algebraMap k B (φ b) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [h', RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact this.symm
  · intro p
    haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
    letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
    have hb : Function.Bijective (algebraMap k (B ⧸ p.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ p.asIdeal)) hb
    refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k p.asIdeal), ?_⟩
    ext x
    change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem finrank_eq_card_sections_mul : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k),
    IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) →
    ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  intro k _ _ P q hq m hm z
  haveI := hq
  haveI : IsAffine P := isAffine_of_isAffineHom q
  let B : Type := Γ(P, ⊤)
  letI : Algebra k B := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop).hom.toAlgebra
  let q' : Spec (CommRingCat.of B) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k B))
  have hq1 : P.isoSpec.hom ≫ q' = q := GlobalTheory.IwLevel.FiberCard.isoSpec_hom_specMap_appTop' q
  have hq2 : q' = P.isoSpec.inv ≫ q := by rw [← hq1, Iso.inv_hom_id_assoc]
  haveI : IsFinite q' := by rw [hq2]; infer_instance
  haveI : Module.Finite k B :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp (inferInstanceAs (IsFinite q')))
  haveI : Flat q' := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Flat q := by rw [← hq1]; infer_instance
  have hrk : q.finrank z = Module.finrank k B := by
    rw [← hq1, Scheme.Hom.finrank_comp_left_of_isIso]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap k B z).trans ?_
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hsec : Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} = Nat.card (B →ₐ[k] k) := by
    let F : {s : Sp k ⟶ P // s ≫ q = 𝟙 _} → (B →ₐ[k] k) := fun s =>
      { (Spec.preimage (s.1 ≫ P.isoSpec.hom)).hom with
        commutes' := fun c => by
          have h : CommRingCat.ofHom (algebraMap k B) ≫ Spec.preimage (s.1 ≫ P.isoSpec.hom) = 𝟙 _ := by
            apply Spec.map_injective
            rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc]
            exact (congrArg (s.1 ≫ ·) hq1).trans s.2
          exact congrArg (fun u => u.hom c) h }
    refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
    · intro s₁ s₂ h
      apply Subtype.ext
      have h1 : Spec.preimage (s₁.1 ≫ P.isoSpec.hom) = Spec.preimage (s₂.1 ≫ P.isoSpec.hom) := by
        ext c
        exact congrArg (fun u : B →ₐ[k] k => u c) h
      have h2 := congrArg Spec.map h1
      rw [Spec.map_preimage, Spec.map_preimage] at h2
      simpa using congrArg (· ≫ P.isoSpec.inv) h2
    · intro φ
      let s : Sp k ⟶ P := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.isoSpec.inv
      have hs' : s ≫ P.isoSpec.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) := by simp [s]
      have hs : s ≫ q = 𝟙 _ := by
        rw [← hq1, ← Category.assoc, hs', ← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext c
        exact φ.commutes c
      refine ⟨⟨s, hs⟩, ?_⟩
      ext b
      change (Spec.preimage (s ≫ P.isoSpec.hom)).hom b = φ b
      rw [hs', Spec.preimage_map]
      rfl
  have hstalk : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m := by
    intro p
    have hU := isAffineOpen_top P
    have hp : hU.fromSpec p ∈ (⊤ : P.Opens) := by simp
    letI : Algebra B (P.presheaf.stalk (hU.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨hU.fromSpec p, hp⟩
    haveI : IsLocalization p.asIdeal.primeCompl (P.presheaf.stalk (hU.fromSpec p)) :=
      hU.isLocalization_stalk' p hp
    rw [← hm (hU.fromSpec p)]
    exact length_self_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (P.presheaf.stalk (hU.fromSpec p))).toRingEquiv
  rw [hrk, hsec, card_algHom_eq_card_primeSpectrum k B]
  exact finrank_eq_card_mul k B m hstalk

end GlobalTheory.FinSchemeRank
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.smooth_genericFibre_closure_partition | exact GlobalTheory.smooth_genericFibre_closure_partition | (intros; apply GlobalTheory.smooth_genericFibre_closure_partition <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothCrit

theorem smooth_of_lift (A R : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] (g : A →+* R) (hg : g.FiniteType)
    (H : (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (g) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (g) = β)) : g.Smooth := by
  algebraize [g]
  have : Algebra.FinitePresentation A R := Algebra.FinitePresentation.of_finiteType.mp hg
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A R)
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) R := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) R) := hf
  have hmax : ∀ (m : Ideal R) [m.IsMaximal], Algebra.IsSmoothAt A m := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have key := GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' A (MvPolynomial (Fin n) A) R (R ⧸ m) fun ℓ => GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting A (MvPolynomial (Fin n) A) R (R ⧸ m) hs Ideal.Quotient.mk_surjective H ℓ
    exact (GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective A (MvPolynomial (Fin n) A) R (R ⧸ m) hs m
      (Ideal.mk_ker).symm).mpr key
  have hU : Algebra.smoothLocus A R = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Algebra.smoothLocus A R := @hmax m hm
    exact ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm).mem_open Algebra.isOpen_smoothLocus hm'
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩

theorem smooth_of_artinian_lift : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  intro B _ _ X s hs H
  constructor
  intro U hU V hV e
  haveI : IsNoetherianRing Γ(Sp B, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact smooth_of_lift _ _ _ (HasRingHomProperty.appLE @LocallyOfFiniteType s hs ⟨U, hU⟩ ⟨V, hV⟩ e) (GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift B X s H U hU V hV e)

end GlobalTheory.SmoothCrit
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  first | exact @GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra | exact GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra | (intros; apply GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra <;> assumption)
end

section

open Complex Matrix

theorem _root_.GlobalTheory.T.exists_theta_division_point_ne_zero : ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | exact GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero <;> assumption)
end
