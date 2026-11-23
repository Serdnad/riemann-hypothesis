module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
import Formalism.LocalRingCardinality.DataHost
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle147
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle074
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle931
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroSummand

variable {R : Type} [CommRing R] (I : Ideal R) {C : Type 1} [AddCommGroup C] [Module R C]

theorem smul_top_eq_sup {P Q : Submodule R C} (h : IsCompl P Q) :
    I • (⊤ : Submodule R C) = I • P ⊔ I • Q := by
  rw [← h.sup_eq_top, Submodule.smul_sup]

theorem sup_smul_top_eq {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊔ I • (⊤ : Submodule R C) = P ⊔ I • Q := by
  rw [smul_top_eq_sup I h, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • P ≤ P)]

theorem inf_smul_top {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊓ I • (⊤ : Submodule R C) = I • P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxJ⟩ := Submodule.mem_inf.mp hx
    rw [smul_top_eq_sup I h, Submodule.mem_sup] at hxJ
    obtain ⟨a, ha, b, hb, rfl⟩ := hxJ
    have hbQ : b ∈ Q := Submodule.smul_le_right hb
    have hbP : b ∈ P := by
      have e : b = (a + b) - a := by abel
      rw [e]; exact P.sub_mem hxP (Submodule.smul_le_right ha)
    have hb0 : b = 0 := (Submodule.disjoint_def.mp h.disjoint) b hbP hbQ
    simpa [hb0] using ha
  · exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)

theorem smul_smul_top (hI : I ^ 2 = 0) : I • I • (⊤ : Submodule R C) = ⊥ := by
  rw [← Submodule.mul_smul, ← sq, hI, Submodule.zero_eq_bot, Submodule.bot_smul]

theorem smul_le_of_sup_eq (hI : I ^ 2 = 0) {K F : Submodule R C}
    (h : K ⊔ I • ⊤ = F ⊔ I • ⊤) : I • K ≤ I • F := by
  calc I • K ≤ I • (K ⊔ I • ⊤) := Submodule.smul_mono le_rfl le_sup_left
    _ = I • F := by rw [h, Submodule.smul_sup, smul_smul_top I hI, sup_bot_eq]

end GlobalTheory.SqZeroSummand


open GlobalTheory.SqZeroSummand in
theorem GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero :
    ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  intro R _ I hI C _ _ F K N hFN hKF
  have isCompl_of : K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N := by
    intro hi
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxN
      have hx : x ∈ F ⊔ I • N := by
        rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hxK
      obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hbN : b ∈ N := Submodule.smul_le_right hb
      have hyN : y ∈ N := by
        have e : y = (y + b) - b := by abel
        rw [e]; exact N.sub_mem hxN hbN
      have hy0 : y = 0 := (Submodule.disjoint_def.mp hFN.disjoint) y hy hyN
      subst hy0
      rw [zero_add] at hxK hxN ⊢
      have hbJ : b ∈ K ⊓ I • (⊤ : Submodule R C) :=
        ⟨hxK, Submodule.smul_mono le_rfl le_top hb⟩
      rw [hi] at hbJ
      exact (Submodule.disjoint_def.mp hFN.disjoint) b hbJ.1 hbN
    · rw [codisjoint_iff, eq_top_iff, ← hFN.sup_eq_top]
      have h1 : I • F ≤ K := by
        have : I • F ≤ K ⊓ I • ⊤ := by
          rw [hi]; exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)
        exact this.trans inf_le_left
      have h2 : F ≤ K ⊔ N := by
        calc F ≤ F ⊔ I • ⊤ := le_sup_left
          _ = K ⊔ I • ⊤ := hKF.symm
          _ = K ⊔ (I • F ⊔ I • N) := by rw [smul_top_eq_sup I hFN]
          _ ≤ K ⊔ N := sup_le le_sup_left
              (sup_le (h1.trans le_sup_left) (Submodule.smul_le_right.trans le_sup_right))
      exact sup_le h2 le_sup_right
  refine ⟨isCompl_of, ?_⟩
  rintro ⟨N', hKN'⟩
  have hi : K ⊓ I • ⊤ = F ⊓ I • ⊤ := by
    rw [inf_smul_top I hKN', inf_smul_top I hFN]
    exact le_antisymm (smul_le_of_sup_eq I hI hKF) (smul_le_of_sup_eq I hI hKF.symm)
  have hKN := isCompl_of hi
  refine ⟨hi, (N.projection K hKN.symm) ∘ₗ F.subtype, ?_, ?_, ?_⟩
  · intro c
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    refine ⟨?_, Submodule.projection_apply_mem _ _, Submodule.sub_projection_mem _ _⟩
    have hc : c.1 ∈ K ⊔ I • N := by
      rw [← sup_smul_top_eq I hKN, hKF]; exact Submodule.mem_sup_left c.2
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp hc
    rw [← hkb, map_add (f := _), (Submodule.projection_apply_eq_zero_iff _).mpr hk, zero_add,
      Submodule.projection_apply_of_mem_left _ (Submodule.smul_le_right hb)]
    exact Submodule.smul_mono le_rfl le_top hb
  · intro c hc
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have h' : c.1 ∈ K ⊓ I • (⊤ : Submodule R C) := by rw [hi]; exact ⟨c.2, hc⟩
    exact (Submodule.projection_apply_eq_zero_iff _).mpr h'.1
  · intro k hk
    have hk' : k ∈ F ⊔ I • N := by
      rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hk
    obtain ⟨f, hf, b, hb, hfb⟩ := Submodule.mem_sup.mp hk'
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have hbN : b ∈ N := Submodule.smul_le_right hb
    have ef : f = k - b := by rw [← hfb]; abel
    rw [ef, map_sub, (Submodule.projection_apply_eq_zero_iff _).mpr hk,
      Submodule.projection_apply_of_mem_left _ hbN]
    abel
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_semilinear_lift_of_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (P : Type) [AddCommGroup P] [Module R₀ P], Module.Projective R₀ P → ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (W : Submodule R M), (∀ r, π r = 0 → ∀ m ∈ W, r • m = 0) → ∀ (q : M →ₗ[R] M') (v : P →+ M'), (∀ r w, v (π r • w) = r • v w) → (∀ w, ∃ m ∈ W, q m = v w) → ∃ u : P →+ M, (∀ r w, u (π r • w) = r • u w) ∧ (∀ w, u w ∈ W) ∧ ∀ w, q (u w) = v w := by
  intro R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq
  classical
  choose m hmW hmq using hq
  choose σ hσ using hπ
  have key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x := by
    intro r s x hx h
    have := hW (r - s) (by rw [map_sub, h, sub_self]) x hx
    rwa [sub_smul, sub_eq_zero] at this
  let f : P → R₀ →+ M := fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by
    intro a b
    rw [← add_smul]
    exact key _ _ _ (hmW w) (by rw [map_add (f := _), hσ, hσ, hσ]))
  have hf : ∀ w c, f w c = σ c • m w := fun _ _ => rfl
  let g : (P →₀ R₀) →+ M := Finsupp.liftAddHom f
  have hg : ∀ w c, g (Finsupp.single w c) = σ c • m w := by
    intro w c
    simp only [g, Finsupp.liftAddHom_apply_single, hf]
  have g1 : ∀ r x, g (π r • x) = r • g x := by
    intro r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single w c =>
      rw [Finsupp.smul_single, hg, hg, smul_smul]
      exact key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])
  have g2 : ∀ x, g x ∈ W := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | single w c => rw [hg]; exact W.smul_mem _ (hmW w)
  have g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single w c =>
      rw [hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]
      rfl
  obtain ⟨s, hs⟩ := hP.out
  refine ⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro r w
    show g (s (π r • w)) = r • g (s w)
    rw [map_smul, g1]
  · intro w
    exact g2 _
  · intro w
    show q (g (s w)) = v w
    rw [g3, hs]

end GlobalTheory.LiftSys
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)


section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)


variable {O}

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Towers

variable (T : ThetaX D)

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)


end GlobalTheory.ThetaInner

end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Rigidity

theorem spMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hs : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) :
    Function.Surjective (spMap π) := by
  have h := _root_.range_comap_of_surjective R₀ π hs
  have h2 : PrimeSpectrum.zeroLocus (RingHom.ker π : Set R) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact (Submodule.mem_bot R).1 this
  rw [h2, Set.range_eq_univ] at h
  exact h

theorem eq_comp_section : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (P X : Over (Sp R)) (P₀ : Over (Sp R₀)) (l : P₀.left ⟶ P.left), IsPullback l P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f : P ⟶ X) (s₀ : Sp R₀ ⟶ X.left), l ≫ f.left = P₀.hom ≫ s₀ →
    f.left = P.hom ≫ ε ≫ f.left := by
  intro R R₀ _ _ π hs hn P X P₀ l hpb hsm hpr hgc ε hε f s₀ hf
  have := hsm
  have := hpr
  have : GeometricallyIntegral P.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.hom hsm hgc
  have hsurj : ∀ V : (Sp R).Opens, Function.Surjective (P.hom.app V).hom := fun V => by
    have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange
      exists_noetherian_model_of_smooth P.hom V
    exact (ConcreteCategory.bijective_of_isIso (P.hom.app V)).2
  have hloc : ∀ t : Sp R, ∃ V : (Sp R).Opens, t ∈ V ∧
      (P.hom ⁻¹ᵁ V).ι ≫ f.left = (P.hom ⁻¹ᵁ V).ι ≫ P.hom ≫ ε ≫ f.left := by
    intro t
    obtain ⟨t₀, ht₀⟩ := spMap_surjective π hs hn t
    refine local_rigidity _ _ _ P.hom ε f.left hε inferInstance hsurj t (s₀ t₀) ?_
    intro x hx
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := P.hom) (g := spMap π) x t₀
      (hx.trans ht₀.symm)
    have e₁ : l (hpb.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    have e₂ : P₀.hom (hpb.isoPullback.inv z) = t₀ := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
    rw [← e₁, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply, e₂]
  choose V hV hfg using hloc
  have hc : TopologicalSpace.IsOpenCover (fun t => P.hom ⁻¹ᵁ V t) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P.hom x, hV (P.hom x)⟩
  exact (P.left.openCoverOfIsOpenCover _ hc).hom_ext _ _ fun t => hfg t

end GlobalTheory.Rigidity
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilLift

theorem surjective_spMap_of_isNilpotent_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isProper_and_geometricallyConnected_of_smooth_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  intro R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc
  have hs : Surjective (spMap π) := surjective_spMap_of_isNilpotent_ker π hπ hn
  have hc : IsClosedImmersion (spMap π) := .spec_of_surjective _ hπ
  have : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs
  have : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc
  have : IsProper (i ≫ X.hom) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective i X.hom
  have : IsSeparated X.hom := GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom
  have : LocallyOfFiniteType X.hom := inferInstance
  refine ⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hφ : RingHom.ker π ≤ RingHom.ker φ.hom := by
    intro a ha
    obtain ⟨n, hn⟩ := hn
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    have h0 : IsNilpotent a := ⟨n, this⟩
    exact (h0.map φ.hom).eq_zero
  let ψ : R₀ →+* K := RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩
  have hψ : ∀ a, ψ (π a) = φ.hom a := fun a ↦
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a
  let y' : Spec (CommRingCat.of K) ⟶ Sp R₀ := Spec.map (CommRingCat.ofHom ψ)
  have hy : y' ≫ spMap π = Spec.map φ := by
    simp only [y', spMap, ← Spec.map_comp]
    congr 1
    ext a
    exact hψ a
  rw [← hy] at hz
  let p : Z ⟶ X₀.left := hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])
  refine hgc.geometrically_connectedSpace y' p snd ?_
  exact IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq

end GlobalTheory.NilLift
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.FieldDescentSm

theorem smoothOfRelativeDimension_and_geometricallyConnected_descend : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  intro k E _ _ _ Y X p q π H D hX hD hq
  have hf := GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)
  have hsq : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hsm : Smooth p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq
  have hp : GeometricallyConnected p :=
    GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H
  refine ⟨?_, hp⟩
  have hc : ConnectedSpace Y :=
    hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨x⟩ := hX
  obtain ⟨D', hD'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)
  have h' : SmoothOfRelativeDimension D' q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]
  exact hD'

end GlobalTheory.FieldDescentSm
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SmoothProperModel

theorem exists_smooth_proper_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f →
    ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧
      IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  intro k _ X f hsm hpr
  obtain ⟨R₀, _, φ, X₀, f₀, π, hm⟩ := GlobalTheory.T.scheme_models_spread k X f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := GlobalTheory.T.smooth_spreads_out k R₀ φ X X₀ f f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := GlobalTheory.T.isProper_spreads_out k R₁ φ₁ X _ f _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  have sm₂' : Smooth (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := inferInstance
  let ψ₃ : R₂ →+* φ₂.range := φ₂.rangeRestrict
  have e₃ : φ₂.range.subtype.comp ψ₃ = φ₂ := by ext x; rfl
  have ft₃ : Algebra.FiniteType ℤ φ₂.range :=
    haveI := ft₂
    Algebra.FiniteType.of_surjective ψ₃.toIntAlgHom φ₂.rangeRestrict_surjective
  have m₃ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₃ ft₃ m₂
  exact ⟨φ₂.range, _, _, _, ft₃, inferInstance, inferInstance, m₃.2.2.2.2⟩

end GlobalTheory.SmoothProperModel
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.one_add_strictLower_mem_closure_transvection' : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.one_add_strictLower_mem_closure_transvection | exact GlobalTheory.one_add_strictLower_mem_closure_transvection | (intros; apply GlobalTheory.one_add_strictLower_mem_closure_transvection <;> assumption)
end
