module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle003
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.lineBundle_trivial_basicOpen_of_trivial_fibre_product : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  first | exact @GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod | exact GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod | (intros; apply GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem princ_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ _
  haveI := Di.fin
  have hΛ : (LinearMap.range φ0).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map φ0 Module.Finite.fg_top
  have hM : 0 < l.M * l.A := Nat.mul_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨S, hS⟩ := GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM
  refine ⟨S, fun γ hγ => ?_⟩
  obtain ⟨s, hs, hst, hc⟩ := hS γ hγ
  refine ⟨s, hs, hst, fun a _ => ?_, fun a => ?_⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.A • b, by rw [e, map_nsmul, mul_smul]⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.M • b, by rw [e, map_nsmul, mul_comm, mul_smul]⟩

end GlobalTheory.FrameUnif
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerGam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma perFr_lact (X : Data E r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hm : ∀ t : X.Ψ, mat (lact γ x) t = (γ : Matrix (Fin r) (Fin r) E).map t.1 * mat x t := fun _ => rfl
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  unfold perFr
  simp only [hm, GlobalTheory.PerMove.emb_mulVec]
  split_ifs
  · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _),
      Matrix.mul_one]
  · rfl
  · rw [GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl


omit [IsCMField E] in
lemma exists_equiv (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) :
    ∃ f : Λ ≃ₗ[𝓞 E] Λ, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), (hγ _).1 a.2⟩
            invFun := fun a => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E),
              (hγ _).2 (by rw [hri]; exact a.2)⟩
            map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun a => Subtype.ext (hli _)
            right_inv := fun a => Subtype.ext (hri _) }, fun _ => rfl⟩

end GlobalTheory.PerGam

namespace GlobalTheory

theorem per_gam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ γ ∈ (M.X k).Γ, ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La, ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) ∧ ∀ x ∈ (M.X k).dom, ∀ a, Pf (lact γ x) (gam a) = Pf x a := by
  intro E _ _ _ H Dw l Xo c σ g e F r M _ hB _ k Pf hP γ hγ
  obtain ⟨⟨hU, hS⟩, hM, hA⟩ := (hB.gam k γ).1 hγ
  obtain ⟨f, hf⟩ := PerGam.exists_equiv _ γ hS
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (f.trans (M.φ k).symm)
  have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    rw [← hf]
    simp [gam]
  have key : ∀ (n : ℕ) (a b : (F.Di k).La),
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + n • (M.φ k b : Fin r → E) → gam a = a + n • b := by
    intro n a b h
    apply (M.φ k).injective
    apply Subtype.ext
    rw [hg, h, map_add (f := _), map_nsmul]
    rfl
  refine ⟨gam, ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩, fun x _ a => ?_⟩
  · have h1 := hB.ef k (gam a) (gam b)
    rw [hg, hg, hU, ← hB.ef k a b] at h1
    exact_mod_cast h1
  · obtain ⟨b, hb⟩ := hM a ha
    exact ⟨b, key _ a b hb⟩
  · obtain ⟨b, hb⟩ := hA a
    exact ⟨b, key _ a b hb⟩
  · funext j
    rw [hP, hP, hg, PerGam.perFr_lact _ γ hU]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section
namespace GlobalTheory.Frames

theorem spMap_dualMap_left {R T T' : Type} [CommRing R] [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']
    (ρ : T →ₐ[R] T') : (Chart.spMap (SqZero.dualMap ρ)).left = spMap (dualMap (ρ : T →+* T')) := by
  rw [Chart.spMap_left]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem existsUnique_glue_dual_of_isTerminal {R : Type} [CommRing R] (hR : IsTerminal (Sp R)) {S : Type} [CommRing S]
    [Algebra R S] (Y : Scheme.{0}) {κ : Type} (h : κ → S) (hs : Ideal.span (Set.range h) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y)
    (hw : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) :
    ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by
  let X : Over (Spec (CommRingCat.of R)) := Over.mk (hR.from Y)
  let w' : ∀ i, Chart.sp (R₀ := R) (DualNumber (Localization.Away (h i))) ⟶ X := fun i =>
    Over.homMk (w i) (hR.hom_ext _ _)
  let q : ∀ k, S →ₐ[R] Localization.Away (h k) := fun k => SqZero.awayHom R (h k)
  have hq : ∀ k, SqZero.IsAway (q k) (h k) := fun k => SqZero.isAway_awayHom _
  let p : ∀ k l, S →ₐ[R] Localization.Away (h k * h l) := fun k l => SqZero.awayHom R (h k * h l)
  have hp : ∀ k l, SqZero.IsAway (p k l) (h k * h l) := fun k l => SqZero.isAway_awayHom _
  choose a ha using fun k l => (hq k).lift (p k l)
    (isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact (hp k l).unit))
  choose b hb using fun k l => (hq l).lift (p k l)
    (isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact (hp k l).unit))
  have hs' := SqZero.span_range_map hs (SqZero.inlS R S)
  obtain ⟨z, hz⟩ := SqZero.away_glue (X := X) hs' (fun k => SqZero.dualMap (q k))
    (fun k => (hq k).dualMap) w' (fun k l =>
      SqZero.agree_of_isAway (hq k).dualMap (hq l).dualMap (a₀ := SqZero.dualMap (a k l))
        (b₀ := SqZero.dualMap (b k l)) (by rw [SqZero.dualMap_comp, SqZero.dualMap_comp, ha, hb])
        (by rw [SqZero.dualMap_comp, ha, ← map_mul]; exact (hp k l).dualMap)
        (Over.OverMorphism.ext (by
          rw [Over.comp_left, Over.comp_left, spMap_dualMap_left, spMap_dualMap_left]
          exact hw k l _ _ (RingHom.ext fun x => AlgHom.congr_fun (ha k l) x)
            (RingHom.ext fun x => AlgHom.congr_fun (hb k l) x))))
  have hz' : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ z.left = w i := fun i => by
    have : (Chart.spMap (SqZero.dualMap (q i))).left ≫ z.left = w i := congrArg CommaMorphism.left (hz i)
    rw [spMap_dualMap_left] at this
    exact this
  refine ⟨z.left, hz', fun y hy => ?_⟩
  let y' : Chart.sp (R₀ := R) (DualNumber S) ⟶ X := Over.homMk y (hR.hom_ext _ _)
  have : y' = z := SqZero.away_ext (X := X) hs' (fun k => SqZero.dualMap (q k))
    (fun k => (hq k).dualMap) fun k => Over.OverMorphism.ext (by
      rw [Over.comp_left, Over.comp_left, spMap_dualMap_left]
      exact (hy k).trans (hz' k).symm)
  exact congrArg CommaMorphism.left this

theorem existsUnique_glue_dual : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y, (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) → ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i :=
  fun _ _ Y _ h hs w hw => existsUnique_glue_dual_of_isTerminal specZIsTerminal Y h hs w hw

end GlobalTheory.Frames
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem point_from_fg_subalgebra {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F) {X : Scheme.{0}}
    (s : X ⟶ Sp K) [LocallyOfFinitePresentation s] (S : Type) [CommRing S] [Algebra F S] (x : Sp S ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap F S).comp φ)) :
    ∃ S₀ : Subalgebra F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ X, x₀ ≫ s = spMap ((algebraMap F S₀).comp φ) ∧
      spMap S₀.val.toRingHom ≫ x₀ = x := by
  classical
  let P : Finset S ⥤ CommRingCat.{0} :=
    { obj t := .of (Algebra.adjoin F (t : Set S))
      map {t t'} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cP : Cocone P :=
    { pt := .of S
      «ι» := { app t := CommRingCat.ofHom (Algebra.adjoin F (t : Set S)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcP : IsColimit cP := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : S := x
        exact ⟨({x'} : Finset S), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin F (({x'} : Finset S) : Set S)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset S)ᵒᵖ ⥤ Scheme.{0} := P.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cP.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcP.op
  let κ (t : (Finset S)ᵒᵖ) : G.obj t ⟶ Sp K :=
    spMap ((algebraMap F (Algebra.adjoin F (t.unop : Set S))).comp φ)
  have hι {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : G.map f ≫ κ t' = κ t := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (t : (Finset S)ᵒᵖ) : cG.π.app t ≫ κ t = spMap ((algebraMap F S).comp φ) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hG (t : (Finset S)ᵒᵖ) : IsAffine (G.obj t) := inferInstanceAs (IsAffine (Spec _))
  have hGa {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : IsAffineHom (G.map f) := inferInstance
  obtain ⟨i, y₀, hy₀, hy₁⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    ({ app := κ, naturality := fun t t' f => (hι f).trans (Category.comp_id _).symm } :
      G ⟶ (Functor.const _).obj (Sp K)) s cG hcG x
    (NatTrans.ext (funext fun t => (hι' t).trans hx.symm))
  exact ⟨Algebra.adjoin F (i.unop : Set S), ⟨i.unop, rfl⟩, y₀, hy₁, hy₀⟩

theorem moduli_point_from_fg_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∃ S₀ : Subalgebra c.F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ Xo.X, x₀ ≫ Xo.s = sOf c S₀ ∧ spMap S₀.val.toRingHom ≫ x₀ = x := by
  intro E _ _ _ H Dw l Xo c S _ _ x hx
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  exact point_from_fg_subalgebra (IntermediateField.inclusion c.le).toRingHom Xo.s S x hx

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.PeriodRowsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem isTypeFn_letters (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := fun τ => by
    have hval : relab c σ τ (H.rt : E) = σ ⟨τ (H.rt : E), c.conj τ _⟩ := rfl
    rw [hval]
    refine ⟨fun h => congrArg Subtype.val (σ.injective (h.trans hσ0.symm)), fun h => ?_⟩
    exact (congrArg σ (Subtype.ext h)).trans hσ0
  intro τ
  obtain ⟨τ₀, rfl⟩ := Finite.injective_iff_surjective.1 hinj τ
  have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
    have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
      Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
    have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    rw [Nat.card_congr (e1.trans (e2.trans (Equiv.sigmaSubtype τ₀))), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    exact if_pos ((hrel τ₀).1 h)
  · rw [hcard]
    exact if_neg (fun h' => h ((hrel τ₀).2 h'))

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}

end GlobalTheory.PeriodRowsCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_eigen_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  intro E _ _ _ H l c S _ _ N _ _ ρ m
  classical
  have hσ₀ : Function.Injective (fun τ : E →+* ℂ => embK c τ) := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective
      (RingHom.ext fun a => by
        have h1 := embK_coe c τ a
        have h2 := embK_coe c τ' a
        have h3 : embK c τ a = embK c τ' a := RingHom.congr_fun h a
        exact h1.symm.trans ((congrArg _ h3).trans h2))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => (algebraMap c.F S).comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) (algebraMap c.F S) (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map (algebraMap c.F S))
  have hI := EigenSplit.isInternal_eigenSub hσ ρ
  let A := fun τ : E →+* ℂ => EigenSplit.eigenSub ρ ((algebraMap c.F S).comp (embK c τ))
  have hsum : ∀ x : DirectSum _ (fun τ => A τ), DirectSum.coeAddMonoidHom A x = ∑ τ, (x τ : N) :=
    fun x => by
      conv_lhs => rw [← DirectSum.sum_univ_of x]

      simp [map_sum, DirectSum.coeAddMonoidHom_of]
  obtain ⟨x, hx⟩ := hI.2 m
  refine ⟨fun τ => x τ, ⟨fun τ a => EigenSplit.mem_eigenSub.1 (x τ).2 a, (hsum x).symm.trans hx⟩, ?_⟩
  rintro f ⟨hf, hm⟩
  let y : DirectSum _ (fun τ => A τ) :=
    DFinsupp.equivFunOnFintype.symm fun τ => ⟨f τ, EigenSplit.mem_eigenSub.2 (hf τ)⟩
  have hy : y = x := hI.1 (((hsum y).trans hm).trans hx.symm)
  funext τ
  rw [← hy]
  rfl

end GlobalTheory.Frames
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_comap_eq : ∀ (F : IntermediateField ℚ ℂ) (U : ValuationSubring F) (p : ℕ), (p : F) ∈ U.nonunits → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  first | exact @GlobalTheory.exists_valuationSubring_complex_comap_val_eq | exact GlobalTheory.exists_valuationSubring_complex_comap_val_eq | (intros; apply GlobalTheory.exists_valuationSubring_complex_comap_val_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem unitRes_top_injective {S : Scheme.{0}} {T : Over S} :
    Function.Injective (Out.unitRes (T := T) ⊤) := by
  intro a b h
  have hi : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
  have hi' : IsIso (⊤ : T.left.Opens).ι.appTop := inferInstanceAs (IsIso ((⊤ : T.left.Opens).ι.app ⊤))
  have hb : Function.Injective (⊤ : T.left.Opens).ι.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso (⊤ : T.left.Opens).ι.appTop).1
  exact Units.ext (hb (congrArg Units.val h))

theorem unitOn_injective_of_commRing {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  exact Units.ext (hb (congrArg Units.val h))

theorem weilIs_unique_fieldPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (n : ℤ) (x y : Over.mk t ⟶ G) (c c' : kˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x y (unitOn c') → c = c' := by
  intro S G _ L hL k _ t n x y c c' h h'
  let p : (Over.mk t).left := (⊥ : PrimeSpectrum k)
  have top : ∀ V : (Over.mk t).left.Opens, p ∈ V → V = ⊤ := fun V hV =>
    eq_top_iff.2 fun q _ => by
      have : q = p := Subsingleton.elim (α := PrimeSpectrum k) q p
      exact this ▸ hV
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := top V hV
  obtain rfl := top V' hV'
  exact unitOn_injective_of_commRing (unitRes_top_injective
    (H1.commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)))

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem extendGen : extendGenSt.{0} :=
  (GlobalTheory.cubical_extends_and_extendGen GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.GenExtend.existsUnique_gen_extend).2

end GlobalTheory.Exist
end
