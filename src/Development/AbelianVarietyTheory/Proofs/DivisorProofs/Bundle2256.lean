module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

@[expose] public section

section

open IsLocalRing TensorProduct

namespace GlobalTheory.JacobianDerivation

theorem isRegularLocalRing_quotient : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T)
    (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) →
    (Matrix.of fun i j => D i (f j)).det ∉ n →
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  intro T _ _ h f D n _ hf hdet
  classical
  let A := Localization.AtPrime n
  haveI : IsRegularLocalRing A := IsRegularRing.isRegularLocalRing_localization n
  let x : Fin h → A := fun j => algebraMap T A (f j)
  have hx : ∀ j, x j ∈ maximalIdeal A := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A n (f j)).mpr (hf j)

  have hrow0 : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 →
      ∀ i, ∑ j, a j * algebraMap T A (D i (f j)) ∈ maximalIdeal A := by
    intro a ha i
    obtain ⟨D', hD'⟩ := @GlobalTheory.derivation_extend_localization_atPrime ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
      (@IsScalarTower.of_algebraMap_eq' ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
        (Subsingleton.elim _ _)) n _ _
      { toFun := fun t => algebraMap T A (D i t)
        map_add' := fun s t => by simp
        map_smul' := fun m t => by simp [Algebra.smul_def]
        map_one_eq_zero' := by simp
        leibniz' := fun s t => by simp [Algebra.smul_def] }
    letI : Algebra ℤ A := Ring.toIntAlgebra A
    have hsq : ∀ y ∈ maximalIdeal A ^ 2, D' y ∈ maximalIdeal A := by
      intro y hy
      rw [pow_two] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun y z hy hz => ?_)
      · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
      · rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    have h1 := hsq _ ha

    rw [map_sum] at h1
    have h2 : ∀ j, D' (a j * x j) = a j * algebraMap T A (D i (f j)) + x j * D' (a j) := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD']
      rfl
    simp_rw [h2, Finset.sum_add_distrib] at h1
    have h3 : ∑ j, x j * D' (a j) ∈ maximalIdeal A :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx j)
    simpa using Ideal.sub_mem _ h1 h3
  have hind : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 → ∀ j, a j ∈ maximalIdeal A := by
    intro a ha
    have hrow := hrow0 a ha
    let φ : T →+* ResidueField A := (residue A).comp (algebraMap T A)
    let M : Matrix (Fin h) (Fin h) (ResidueField A) := φ.mapMatrix (Matrix.of fun i j => D i (f j))
    have hM : M.det ≠ 0 := by
      rw [← RingHom.map_det]
      intro h0
      have hu : IsUnit (algebraMap T A (Matrix.of fun i j => D i (f j)).det) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A n _).mpr hdet
      exact (residue_ne_zero_iff_isUnit _).mpr hu h0
    have hv : M.mulVec (fun j => residue A (a j)) = 0 := by
      funext i
      have := (residue_eq_zero_iff _).mpr (hrow i)

      rw [map_sum] at this
      simp only [Matrix.mulVec, dotProduct, M, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply, φ, RingHom.comp_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
    intro j
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hv) j
    exact (residue_eq_zero_iff _).mp this

  let τ : Fin h → maximalIdeal A := fun i => ⟨x i, hx i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by

      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * x j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  have hrange : (Set.range fun i => ((τ i : maximalIdeal A) : A)) = Set.range x := rfl
  rw [hrange] at hs
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quot_regular A t x hs hd
  have hmap : (Ideal.span (Set.range f)).map (algebraMap T A) = Ideal.span (Set.range x) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  show IsRegularLocalRing (A ⧸ (Ideal.span (Set.range f)).map (algebraMap T A))
  rw [hmap]
  exact hreg

end GlobalTheory.JacobianDerivation
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lineBundle_section_nonzeroLocus_eq_affineOpen :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
      (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V →
      (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) →
      ∃ M : LB A.left, M.IsLB ∧ ∃ s : LB.Sec M, Out.nonzeroLocus s = V := by
  intro R _ _ _ _ A _ hA V hV hs
  obtain ⟨c, L, hL, s, -, e⟩ := GlobalTheory.T.affineOpen_meeting_fibres_is_nonvanishingLocus R A hA V hV hs
  exact ⟨L, hL, s, e⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineConst
open Polynomial

theorem projLine_map_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  intro k _ _ B _ hB f₀ f₁ h0 h1 h01 a b
  have := hB.proper
  haveI hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let pt : Sp k := IsLocalRing.closedPoint k
  let e : B.left := (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left pt
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ e) isOpen_univ
  let L := Localization.Away (X : Polynomial k)
  let t : L := algebraMap (Polynomial k) L X
  let ti : L := IsLocalization.Away.invSelf (X : Polynomial k)
  have hti : t * ti = 1 := IsLocalization.Away.mul_invSelf (X : Polynomial k)
  let g₀ := famMap B f₀ h0 L t
  let g₁ := famMap B f₁ h1 L ti
  have hc := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 L t ti hti
  let V : Set (Sp L) := {τ | ∀ x : Sp (Polynomial L), spMap (algebraMap L (Polynomial L)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W}
  have hV : IsOpen V := GlobalTheory.T.isOpen_setOf_fibre_charts_mem L _ g₀ g₁ hc W

  have hfib : ∀ (χ : L →ₐ[k] k) (x' : Sp (Polynomial k)),
      spMap (algebraMap L (Polynomial L)) (spMap (Polynomial.mapRingHom (χ : L →+* k)) x') = spMap χ.toRingHom pt := by
    intro χ x'
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.mapRingHom (χ : L →+* k)).comp (algebraMap L (Polynomial L)) =
        (algebraMap k (Polynomial k)).comp (χ : L →+* k) := by
      ext z; simp [Polynomial.algebraMap_apply]
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]
    congr 1
    exact hsub.elim _ _
  have hW₀ : ∀ χ : L →ₐ[k] k, spMap χ.toRingHom pt ∈ V →
      (∀ x', famMap B f₀ h0 k (χ t) x' ∈ W) ∧ (∀ x', famMap B f₁ h1 k (χ ti) x' ∈ W) := by
    intro χ hχ
    constructor
    · intro x'
      rw [← famMap_base B f₀ h0 χ t, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).1
    · intro x'
      rw [← famMap_base B f₁ h1 χ ti, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).2
  have hinW : ∀ R : Type, ∀ _ : CommRing R, ∀ _ : Algebra k R, ∀ (f : Sp (Polynomial k) ⟶ B.left)
      (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (x : Sp (Polynomial R)), famMap B f hf R 1 x ∈ W := by
    intro R _ _ f hf x
    rw [famMap_one, Scheme.Hom.comp_apply]
    have hx : (spMap (algebraMap k (Polynomial R))) x = pt := hsub.elim _ _
    rw [hx]
    exact heW

  let χ₁ : L →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers (X : Polynomial k))
    (f := Polynomial.aeval (1 : k)) (by
      rintro ⟨_, n, rfl⟩
      simp)
  have hχ₁t : χ₁ t = 1 := by simp [χ₁, t]
  have hχ₁ti : χ₁ ti = 1 := by
    have := congrArg χ₁ hti
    rw [map_mul, hχ₁t, _root_.one_mul, map_one] at this
    exact this
  have h1V : spMap χ₁.toRingHom pt ∈ V := by
    intro x hx
    obtain ⟨x', rfl⟩ := GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint L k χ₁.toRingHom
      (fun z => ⟨algebraMap k L z, by simp⟩) x hx
    constructor
    · have := famMap_base B f₀ h0 χ₁ t
      rw [hχ₁t] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₀ h0 x'
    · have := famMap_base B f₁ h1 χ₁ ti
      rw [hχ₁ti] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₁ h1 x'
  have hF := GlobalTheory.T.finite_compl_punctured_line_open k V hV χ₁ h1V
  set F := {c : k | c ≠ 0 ∧ ∀ χ : L →ₐ[k] k, χ (algebraMap (Polynomial k) _ X) = c → spMap χ.toRingHom pt ∉ V}

  have hscale : ∀ c : k, c ≠ 0 → c ∉ F → ∀ a : k,
      spMap (Polynomial.evalRingHom (c * a)) ≫ f₀ = spMap (Polynomial.evalRingHom a) ≫ f₀ := by
    intro c hc0 hcF
    simp only [F, Set.mem_setOf_eq, not_and, not_forall, not_not] at hcF
    obtain ⟨χ, hχt, hχV⟩ := hcF hc0
    obtain ⟨hA, hB'⟩ := hW₀ χ hχV
    have hu : χ t * χ ti = 1 := by rw [← map_mul, hti, map_one]
    have hcmp := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 k (χ t) (χ ti) hu
    have key := GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq k B.left W hW _ _ hA hB' hcmp
    have := scale_inv_of_famMap B f₀ h0 (χ t) key
    simpa [t, hχt] using this
  have hunit : ∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f₀ = spMap (Polynomial.evalRingHom 1) ≫ f₀ := by
    intro c hc
    have hfin : ((F ∪ {0}) ∪ (fun d => c / d) '' F).Finite :=
      (hF.union (Set.finite_singleton 0)).union (hF.image _)
    obtain ⟨d, hd⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or, not_exists,
      not_and] at hd
    obtain ⟨⟨hdF, hd0⟩, hd'⟩ := hd
    have hcd0 : c / d ≠ 0 := div_ne_zero hc hd0
    have hcdF : c / d ∉ F := fun h => hd' (c / d) h (by field_simp)
    have e1 := hscale d hd0 hdF (c / d * 1)
    have e2 := hscale (c / d) hcd0 hcdF 1
    rw [_root_.mul_one] at e1 e2
    rw [show d * (c / d) = c by field_simp] at e1
    rw [e1, e2]
  exact GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero k B.left B.hom f₀ h0 hunit a b

end GlobalTheory.LineConst
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  first | exact @GlobalTheory.SmoothStalk.smooth_stalk | exact GlobalTheory.SmoothStalk.smooth_stalk | (intros; apply GlobalTheory.SmoothStalk.smooth_stalk <;> assumption)
end
