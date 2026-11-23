module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle039
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KunnethSymmProductAffineCovers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle033
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpFamilyMatrixRelationsDense
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFactor

lemma ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.HkFam.hom_ext_of_geometric_points <;> assumption

theorem exists_unique_factor : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩

end GlobalTheory.HkFactor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.generator_extends_from_genericFibre_valuationRing : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  first | exact @GlobalTheory.ValGenExtend.triv_of_triv_generic | exact GlobalTheory.ValGenExtend.triv_of_triv_generic | (intros; apply GlobalTheory.ValGenExtend.triv_of_triv_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.torsionBasis_geometric_fibres_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  first | exact @GlobalTheory.CoverGlue.torsionBasis_of_cover | exact GlobalTheory.CoverGlue.torsionBasis_of_cover | (intros; apply GlobalTheory.CoverGlue.torsionBasis_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt

theorem rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = resG Y h s := dif_pos h

theorem exists_locDerK : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀ := by
  intro K _ R _ Y X q p m D W₀ hW d₀ hadd hmul hbase
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧
      (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    refine der_exists f (m.app (X.basicOpen f)).hom
      (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add (f := _)])
      (fun a b => ?_)
    have e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) =
        resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a) :=
      fun a => app_res m (X.basicOpen_le f) a
    rw [e, e]
    simp only [hmul, map_add (f := _), map_mul]
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG Y (pre_le m k) (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k))
      (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add (f := _), map_mul, RingHom.comp_apply, app_res m k]
    · simp only [δmul, map_mul, RingHom.comp_apply]
    · change resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [res_res X, δres, δres, res_res Y]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
      (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1) :=
          fun y hy => e.ge hy
        have e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) =
            resG Y (pre_le m kj) (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, res_res X, res_res X]
        have e'' := congrArg (resG Y k) e'
        rw [res_res Y, res_res Y] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add (f := _), δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep m hW (h'.trans h) _ _ (fun f k => ?_)
    rw [rsT_eq (pre_le m h')]
    refine Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]
  · intro W h r
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep m hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

theorem locDerK_unique {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ : X.Opens} (hW : IsAffineOpen W₀)
    (d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (h : LocDerK q p m D W₀ d)
    (h' : LocDerK q p m D W₀ d') (e : d W₀ = d' W₀) (W : X.Opens) (hle : W ≤ W₀) : d W = d' W := by
  funext s
  refine sep m hW hle _ _ (fun f k => ?_)
  rw [← rsT_eq (pre_le m k), ← rsT_eq (pre_le m k), ← h.res W _ k hle, ← h'.res W _ k hle]
  haveI := hW.isLocalization_basicOpen f
  refine der_unique f (m.app (X.basicOpen f)).hom (d _) (d' _) (h.mul _ (X.basicOpen_le f))
    (h'.mul _ (X.basicOpen_le f)) (fun a => ?_) _
  change d _ (resG X (X.basicOpen_le f) a) = d' _ (resG X (X.basicOpen_le f) a)
  rw [h.res W₀ _ _ le_rfl, h'.res W₀ _ _ le_rfl, e]

theorem exists_unique_locDerK : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → (∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀) ∧ ∀ d d', LocDerK q p m D W₀ d → LocDerK q p m D W₀ d' → d W₀ = d' W₀ → ∀ W, W ≤ W₀ → d W = d' W :=
  fun K _ R _ Y X q p m D W₀ hW =>
    ⟨exists_locDerK K R Y X q p m D W₀ hW, fun d d' h h' e W hle => locDerK_unique hW d d' h h' e W hle⟩

end GlobalTheory.LocDerExtK
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.kunneth_symm_product_affine_covers : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))), (∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  first | exact @GlobalTheory.KS.Kunneth.kunneth_symm | exact GlobalTheory.KS.Kunneth.kunneth_symm | (intros; apply GlobalTheory.KS.Kunneth.kunneth_symm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_lattice_uniformisation_of_prim_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)), t.Prim w w' → ∃ (La : Type) (_ : AddCommGroup La) (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.PrimUnif.exists_unif_of_prim | exact GlobalTheory.PrimUnif.exists_unif_of_prim | (intros; apply GlobalTheory.PrimUnif.exists_unif_of_prim <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem omegaStd_single_single_eq_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      Out.stdSymp g (finCongr (two_mul g).symm (finSumFinEquiv a))
        (finCongr (two_mul g).symm (finSumFinEquiv b)) := by
  unfold Out.stdSymp omegaStd
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, zero_mul,
      sub_zero, zero_sub, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_neg_distrib] <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem exists_equiv_omegaStd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) {g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M)
    (h : ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) :
    ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] M, ∀ x y, B (bas' x) (bas' y) = omegaStd x y := by
  set e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm) with he
  refine ⟨(LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas, ?_⟩
  have hs : ∀ a, (LinearEquiv.funCongrLeft ℤ ℤ e.symm) (Pi.single a (1 : ℤ)) = Pi.single (e a) 1 := by
    intro a
    funext k
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  let Ω : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ) :=
    LinearMap.mk₂ ℤ omegaStd
      (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
      (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
  have hB : B.compl₁₂ ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap
      ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap = Ω := by
    refine LinearMap.ext_basis (Pi.basisFun ℤ _) (Pi.basisFun ℤ _) fun a b => ?_
    simp only [Pi.basisFun_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, hs, h,
      Ω, LinearMap.mk₂_apply]
    exact (omegaStd_single_single_eq_stdSymp a b).symm
  intro x y
  exact LinearMap.congr_fun₂ hB x y

theorem sympBasis_std : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), IsSympBasis D bas → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La, ∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y := by
  intro E _ _ _ H D g bas hb
  refine ⟨?_, exists_equiv_omegaStd D.EF bas hb⟩
  have h1 := (LinearEquiv.finrank_eq bas).symm
  rw [finrank_int_lattice D, Module.finrank_fin_fun] at h1
  omega

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.primeToPart_level_exists_unique_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ), p.Prime → (∀ l : Level H, l.GoodAt p → ∃ l₀ : Level H, IsPrimeToPart l₀ l p) ∧ (∀ l l₀ : Level H, IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧ ∀ l₀' : Level H, IsPrimeToPart l₀' l p → l₀' = l₀) ∧ ∀ l l' l₀ l₀' : Level H, IsPrimeToPart l₀ l p → IsPrimeToPart l₀' l' p → l.Dvd l' → l₀.Dvd l₀' := by
  first | exact @GlobalTheory.Models.primeToPart_spec | exact GlobalTheory.Models.primeToPart_spec | (intros; apply GlobalTheory.Models.primeToPart_spec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.FibreAct

theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G' ⟶ G) [IsIso ψ]
    [IsMonHom ψ] : IsGrpPullback G' G (𝟙 S) ψ.left := by
  haveI : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget S).map ψ))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let U : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = U ≫ x ≫ ψ := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have ey : y₀ = U ≫ y ≫ ψ := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

theorem exists_lift_act {O : Type} [CommRing O] {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  have w : ∀ c, (φ ≫ (a.act c).left) ≫ G.hom = G'.hom ≫ f := fun c => by
    rw [Category.assoc, Over.w, h.1.w]
  let r : O → (G' ⟶ G') := fun c => Over.homMk (h.1.lift (φ ≫ (a.act c).left) G'.hom (w c)) (h.1.lift_snd _ _ _)
  have hr : ∀ c, (r c).left ≫ φ = φ ≫ (a.act c).left := fun c => h.1.lift_fst _ _ _
  have key : ∀ T : Over S', ∃ e : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G),
      ∀ x c, e (x ≫ r c) = e x ≫ a.act c := fun T => by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h T _ rfl
    exact ⟨e, fun x c => Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hr, Category.assoc])⟩
  obtain ⟨e, he⟩ := key G'
  have he' : ∀ c, e (r c) = e (𝟙 G') ≫ a.act c := fun c => by rw [← he, Category.id_comp]
  refine ⟨⟨r, fun c => ?_, e.injective ?_, fun c d => e.injective ?_, fun c d => e.injective ?_⟩, hr⟩
  · haveI := a.hom c
    refine ⟨?_, ?_⟩
    · obtain ⟨e₁, he₁⟩ := key (𝟙_ (Over S'))
      have o : η[G'] = (1 : 𝟙_ (Over S') ⟶ G') := by rw [Hom.one_def]; simp
      apply e₁.injective
      rw [he₁, o, map_one, MonObj.one_comp]
    · obtain ⟨e₂, he₂⟩ := key (G' ⊗ G')
      have m₁ : μ[G'] = fst G' G' * snd G' G' := by rw [Hom.mul_def]; simp
      have m₂ : (r c ⊗ₘ r c) ≫ μ[G'] = (fst G' G' ≫ r c) * (snd G' G' ≫ r c) := by
        rw [Hom.mul_def]; congr 1
      apply e₂.injective
      rw [m₂, he₂, m₁, map_mul, map_mul, he₂, he₂, MonObj.mul_comp]
  · rw [he', a.one, Category.comp_id]
  · rw [he, he', he', a.mul, Category.assoc]
  · rw [map_mul, he', he', he', a.add, MonObj.comp_mul]

theorem exists_fibre_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H S) (x : Sp ℂ ⟶ S) (β : o →+* ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (m : A₀.left ⟶ t.A.left), IsPEL D a bas ρ t τ → x ≫ s = spMap β → IsGrpPullback A₀ t.A x m → ∃ (act : OAct (𝓞 E) t.A) (act₀ : OAct (𝓞 E) A₀), (∀ c, (act₀.act c).left ≫ m = m ≫ (act.act c).left) ∧ DetCond D act₀ (𝟙 _) (β ρ) := by
  intro E _ _ _ H D g k J a bas o _ b ρ S s t τ x β A₀ _ m hP hx hm
  obtain ⟨φ, hφ, -, -, hd⟩ := hP
  haveI := hφ
  have hi : IsGrpPullback t.A τ.G (𝟙 S) φ.inv.left := isGrpPullback_of_iso φ.inv
  obtain ⟨act, hact⟩ := exists_lift_act hi τ.act
  obtain ⟨act₀, hact₀⟩ := exists_lift_act hm act
  refine ⟨act, act₀, hact₀, fun σ => ?_⟩
  have L : ∀ n, LieMult act₀ (𝟙 _) σ n ↔ LieMult τ.act x σ n := fun n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hm hact₀ ℂ (𝟙 _) σ n,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.id_comp, Category.comp_id]
  rw [L, L]
  exact (hd ℂ x β hx).1 σ

end GlobalTheory.FibreAct
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' A A' e : ℕ), 0 < S' → 0 < A' → S ∣ S' → A ∣ A' → (∃ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b) ∧ ∀ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b → (S = S' → A' ∣ S ^ e → IsFinite (spMap b) ∧ Etale (spMap b) ∧ Surjective (spMap b)) ∧ (A = A' → IsOpenImmersion (spMap b) ∧ ∀ x : Sp (RZ H S A), x ∈ Set.range (spMap b) ↔ (S' : RZ H S A) ∉ x.asIdeal) := by
  first | exact @GlobalTheory.BaseRing.inclusion_RZ | exact GlobalTheory.BaseRing.inclusion_RZ | (intros; apply GlobalTheory.BaseRing.inclusion_RZ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (S e : ℕ), 0 < S → l.A ∣ S ^ e → (∃ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S l.A) ∧ ∀ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  first | exact @GlobalTheory.BaseRing.isDedFrac_RZ | exact GlobalTheory.BaseRing.isDedFrac_RZ | (intros; apply GlobalTheory.BaseRing.isDedFrac_RZ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.dense_fromSet_sharpClass : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧ (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧ ∀ j i, t.pt i ≫ t.act j = (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  first | exact @GlobalTheory.sharp_family_relations | exact GlobalTheory.sharp_family_relations | (intros; apply GlobalTheory.sharp_family_relations <;> assumption)
end
