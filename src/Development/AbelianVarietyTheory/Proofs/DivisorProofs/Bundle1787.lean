module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenAffine

open GeneratorFunctor

set_option backward.isDefEq.respectTransparency false

theorem exists_torus_one (S : Scheme.{0}) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : Γ(T, ⊤)ˣ), IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        g.appTop.hom t.val = v.val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        g.appTop.hom t.val = g'.appTop.hom t.val → g = g' := by
  refine ⟨(splitTorus S ℤ).left, (splitTorus S ℤ).hom, charUnit S ℤ 1, inferInstance,
    inferInstance, fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : ℤ →+ Additive Γ(Z, ⊤)ˣ := zmultiplesHom _ (Additive.ofMul v)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S ℤ (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S ℤ).hom)
    let a : Z' ⟶ splitTorus S ℤ := Over.homMk g h
    let a' : Z' ⟶ splitTorus S ℤ := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S ℤ Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine AddMonoidHom.ext_int ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans hk).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this

theorem pb_inv_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (f.appLE U W h).hom (x⁻¹).val = ((pb f U W h x)⁻¹).val := by
  rw [← map_inv, pb_val]

end GenAffine


set_option backward.isDefEq.respectTransparency false in
open GeneratorFunctor GenAffine Opposite in
theorem generatorScheme_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  intro B N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor (N := fun _ : Unit => N) fun _ => hN).has_representation
  let x : Pt (fun _ : Unit => N) G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  have hinj : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ G), Pt.map g x = Pt.map g' x → g = g' :=
    fun g g' h => e.homEquiv.injective (by rw [he, he]; exact h)
  have hsurj : ∀ {Z : Scheme.{0}} (y : Pt (fun _ : Unit => N) Z), ∃ g : Z ⟶ G, Pt.map g x = y :=
    fun y => ⟨e.homEquiv.symm y, by rw [← he, Equiv.apply_symm_apply]⟩
  have hloc : ∀ i, IsAffineHom (x.b ∣_ N.U i) ∧ LocallyOfFiniteType (x.b ∣_ N.U i) := by
    intro i
    obtain ⟨T, p, t, hpa, hpl, hex, hun⟩ := exists_torus_one (N.U i).toScheme
    have hb : ∀ k : Unit, ⊤ ≤ (p ≫ (N.U i).ι) ⁻¹ᵁ ((fun _ : Unit => N) k).U ((fun _ => i) k) :=
      fun k z _ => (p z).2
    let yT : Pt (fun _ : Unit => N) T :=
      Pt.ofChart (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t)
    obtain ⟨ψ, hψ⟩ := hsurj yT
    have hψb : ψ ≫ x.b = p ≫ (N.U i).ι := congrArg Pt.b hψ
    let ψ₀ : T ⟶ (x.b ⁻¹ᵁ N.U i).toScheme := IsOpenImmersion.lift (x.b ⁻¹ᵁ N.U i).ι ψ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change x.b (ψ z) ∈ N.U i
      rw [← Scheme.Hom.comp_apply, hψb, Scheme.Hom.comp_apply]
      exact (p z).2)
    have hψ₀ : ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι = ψ := IsOpenImmersion.lift_fac _ _ _
    have hv : ⊤ ≤ (x.b ⁻¹ᵁ N.U i).ι ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => z.2
    obtain ⟨φ, hφp, hφt⟩ := hex _ (x.b ∣_ N.U i) (pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i))
    have h2 : ψ₀ ≫ φ = 𝟙 T := by
      refine hun T _ _ ?_ ?_
      · rw [Category.assoc, hφp, Category.id_comp, ← cancel_mono (N.U i).ι, Category.assoc,
          morphismRestrict_ι, ← Category.assoc, hψ₀, hψb]
      · have htop : ∀ {Y Z : Scheme.{0}} (f : Z ⟶ Y), ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun f z _ => trivial
        have hφu : pb φ ⊤ ⊤ (htop φ) t = pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i) :=
          Units.ext ((pb_top _ _ _).trans hφt)
        have hψ' : ⊤ ≤ 𝟙 T ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have hψ'' : ⊤ ≤ ψ ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have e1 : pb (ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι) (x.b ⁻¹ᵁ N.U i) ⊤ (hψ₀ ▸ hψ'') (x.s () i) =
            pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) := pb_congr hψ₀ _ _ _ _
        have e2 : pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) =
            pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) := (pb_id_comp ψ _ _ _ le_rfl hψ' _).symm
        have hbT : ⊤ ≤ 𝟙 T ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p z).2
        have e3 : pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) = pb (𝟙 T) _ ⊤ hbT (yT.s () i) :=
          Pt.congr hψ () i (𝟙 T) ⊤ hψ' hbT
        have e4 : (pb (𝟙 T) _ ⊤ hbT (yT.s () i)).val = (Scheme.Hom.appTop (𝟙 T)).hom t.val :=
          Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () (𝟙 T) _
        refine (pb_top (ψ₀ ≫ φ) (htop _) t).symm.trans ?_
        rw [← pb_pb ψ₀ φ ⊤ ⊤ ⊤ (htop φ) (htop ψ₀), hφu, pb_pb]
        exact (congrArg Units.val (e1.trans (e2.trans e3))).trans e4
    have h1 : φ ≫ ψ₀ = 𝟙 _ := by
      rw [← cancel_mono (x.b ⁻¹ᵁ N.U i).ι, Category.assoc, hψ₀, Category.id_comp]
      refine hinj _ _ ?_
      have hbeq : (φ ≫ ψ) ≫ x.b = (x.b ⁻¹ᵁ N.U i).ι ≫ x.b := by
        rw [Category.assoc, hψb, ← Category.assoc, hφp, morphismRestrict_ι]
      have hx' : ⊤ ≤ φ ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hy' : ⊤ ≤ φ ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p (φ z)).2
      have hA : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((φ ≫ ψ) ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hB : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((x.b ⁻¹ᵁ N.U i).ι ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => z.2
      have hC : ⊤ ≤ (φ ≫ ψ) ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have f1 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hA ()) ((Pt.map (φ ≫ ψ) x).s () i) =
          pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f2 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hB ()) ((Pt.map (x.b ⁻¹ᵁ N.U i).ι x).s () i) =
          pb (x.b ⁻¹ᵁ N.U i).ι (x.b ⁻¹ᵁ N.U i) ⊤ hv (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f3 : pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) =
          pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) := (pb_pb φ ψ (x.b ⁻¹ᵁ N.U i) ((ψ ≫ x.b) ⁻¹ᵁ N.U i) ⊤ le_rfl hx' (x.s () i)).symm
      have f4 : pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) = pb φ _ ⊤ hy' (yT.s () i) :=
        Pt.congr hψ () i φ ⊤ hx' hy'
      have f5 : (pb φ _ ⊤ hy' (yT.s () i)).val = φ.appTop.hom t.val :=
        Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () φ hy'
      refine Pt.ext_chart hbeq (fun _ => i) hA hB (fun k => ?_)
      cases k
      refine f1.trans (f3.trans (f4.trans (Units.ext ?_))) |>.trans f2.symm
      exact f5.trans hφt
    have : IsIso φ := ⟨⟨ψ₀, h1, h2⟩⟩
    rw [← hφp]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨G, x.b, fun i => (x.s () i)⁻¹, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover
    fun i => (hloc i).1, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).2,
    fun i i' => ?_, fun Z b s hs => ?_⟩
  · have hc : res (Scheme.Hom.preimage_mono x.b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (x.s () i') =
        pullU x.b _ (N.g i i') *
          res (Scheme.Hom.preimage_mono x.b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (x.s () i) := by
      rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
      exact x.compat () i i' _ inf_le_left inf_le_right
    dsimp only
    rw [map_inv, map_inv, hc, mul_inv, mul_inv_cancel_left]
  · have hs' : ∀ i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ N.U i) (h' : W ≤ b ⁻¹ᵁ N.U i'),
        pb (𝟙 Z) (b ⁻¹ᵁ N.U i') W h' (s i')⁻¹ =
          pb b (N.U i ⊓ N.U i') W (le_inf h h') (N.g i i') * pb (𝟙 Z) (b ⁻¹ᵁ N.U i) W h (s i)⁻¹ := by
      intro i i' W h h'
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ (N.U i ⊓ N.U i')) W (le_inf h h')) (hs i i')
      rw [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this
      rw [map_inv, map_inv, this, mul_inv, mul_inv_cancel_left]
    let y : Pt (fun _ : Unit => N) Z := ⟨b, fun _ i => (s i)⁻¹, fun _ i i' W h h' => hs' i i' W h h'⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ i, (g.appLE (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i)
        (by rw [← hg]; exact le_rfl)).hom ((x.s () i)⁻¹).val = (s i).val) ↔ Pt.map g x = y := by
      intro g
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        cases k
        have h2 : (pb g _ (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i))⁻¹ = s i :=
          Units.ext ((pb_inv_val _ _ _ _ _).symm.trans (h i))
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        exact (inv_eq_iff_eq_inv.1 h2).symm.trans h3.symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun i => ?_⟩
        have := Pt.congr h () i (𝟙 Z) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) le_rfl
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        have h4 : pb (𝟙 Z) (b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) le_rfl (s i)⁻¹ = (s i)⁻¹ := pb_id _ _
        have h5 : pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) =
            (s i)⁻¹ := h3.symm.trans (this.trans h4)
        rw [pb_inv_val, h5, inv_inv]
    obtain ⟨g0, hg0⟩ := hsurj y
    exact ⟨g0, (key g0).2 hg0, fun g hg => hinj _ _ (((key g).1 hg).trans hg0.symm)⟩

end GlobalTheory
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.ColsInLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat

variable {D : D7}

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (finIncl D).rTensor D.host.E

theorem lift_eq (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    lift D z = finEmb D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lift_finPart (z : AE D) (h : infPart D z = 0) : lift D (finPart D z) = z := by
  have key : ∀ z : AE D, z =
      (show Ainf D.host.F →ₗ[D.host.F] AF D.host.F from
        LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E (infPart D z) +
      lift D (finPart D z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a e =>
      change _ = (pairA D.host.F a.1 0) ⊗ₜ[D.host.F] e + (pairA D.host.F 0 a.2) ⊗ₜ[D.host.F] e
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero a.1).symm (zero_add a.2).symm
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  have := key z
  rw [h, map_zero, zero_add] at this
  exact this.symm

def col (V W : HSp D) (b : Fin V.rank) : (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ WO V W where
  toFun z := Matrix.of fun i j => if j = b then lift D (z i) else 0
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _)]
    split_ifs <;> simp

theorem col_mem (V W : HSp D) (hV : V.gram = 1) (k : GA D W) (b : Fin V.rank)
    (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latGHat W k) :
    col V W b z ∈ latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
      (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hz
    have hz' : z ∈ hat D.host.F (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) := by
      rw [← SetLike.mem_coe, GlobalTheory.MovedLat.hat_hLat]
      rw [gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1] at hz
      exact hz
    have hs : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      intro i _
      by_cases h : i = b
      · subst h; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have := rankOne_mem_latO V W _ _ a ha _ (pure_mem_hatL _ 1 (one_mem _) _ hs) _
      (GlobalTheory.PrincInLevel.swap_mem_hatL _ z hz')
    convert this using 1
    ext i j
    change (if j = b then lift D (((1 : Af D.host.F) ⊗ₜ a) * z i) else 0) = _
    simp only [rankOne, Matrix.of_apply, hV, cF_tmul, eToEAf, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.sum_tmul]
    have e : ∑ l, star ((Pi.single b 1 : Fin V.rank → D.host.E) l) *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) l j = if j = b then 1 else 0 := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Pi.single_apply]
      split_ifs <;> simp
    rw [e]
    split_ifs
    · rw [lift_eq, map_mul, ← Algebra.TensorProduct.one_def, mul_one]
      rfl
    · simp
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem mem_latO_of_cols : ∀ (D : D7) (V W : HSp D), V.gram = 1 → ∀ (k : GA D W) (x : WO V W), x.map (infPart D) = 0 → (∀ b, (fun a => finPart D (x a b)) ∈ latGHat W k) → x ∈ (latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) := by
  intro D V W hV k x h0 hc
  have e : x = ∑ b, col V W b fun a => finPart D (x a b) := by
    ext i j
    rw [Matrix.sum_apply]
    change _ = ∑ b, if j = b then lift D (finPart D (x i b)) else 0
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    exact (lift_finPart _ (congrFun (congrFun h0 i) j)).symm
  rw [e]
  exact sum_mem fun b _ => col_mem V W hV k b _ (hc b)

end GlobalTheory.ColsInLat

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.JetBase

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

variable {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]

theorem map_pairP_basis {n : ℕ} (lam : ι → DomWeight n) (i j : VVIdx lam) :
    σ (pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVVfun K lam i) (bVVfun K lam j)) =
      pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (map σ (bVVfun K lam i)) (map σ (bVVfun K lam j)) := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  have e1 : map σ (bVVfun K lam i) = map (Int.castRingHom ℂ) Q := by
    rw [hQ, MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  have e2 : σ (extNorm K lam) = extNorm ℂ lam := by
    rw [pb_extNorm_eq, pb_extNorm_eq, extNormB, extNormB, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
  rw [pairP_apply, pairP_apply, pb_gramTw_one, pb_gramTw_one, pb_blockAct_one_tr, pb_blockAct_one_tr, fockL_apply, fockL_apply,
    map_mul, map_div₀, map_one, e2]
  congr 1
  rw [e1, pb_fockS_int, ← e1, GlobalTheory.Proof.TensorMapDescent.fockB_map, hQ, pb_fockS_int]

theorem sqAt_eq {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) (y : Formalism.L2.DIV.VV ℂ lam)
    (h : (y : Pol ℂ ι n) = map σ (x : Pol K ι n)) : sqAt σ lam x = invNormSq lam y := by
  have hx : (x : Pol K ι n) = ∑ i, (bVV K lam).repr x i • bVVfun K lam i := by
    conv_lhs => rw [← (bVV K lam).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  have hy : (y : Pol ℂ ι n) = ∑ i, σ ((bVV K lam).repr x i) • map σ (bVVfun K lam i) := by
    rw [h]
    conv_lhs => rw [hx]

    simp only [map_sum, smul_eq_C_mul, map_mul, map_C]
  unfold sqAt invNormSq
  congr 1
  rw [pairK_apply, hy]

  simp only [pairK_apply, bVV_coe, map_pairP_basis, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
  LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {a b : ℕ}


omit [StarRing K] in
theorem degAt_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ)
    (hμ : μ ∈ (subD K ι a b (P * ∏ τ, frDet K a τ ^ lastEntry (nu τ))).support) (τ : ι) :
    ((_root_.GlobalTheory.ColNorms.degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ : ℕ) : ℤ) = ∑ i, (nu τ).w i := by
  classical
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ
    (GlobalTheory.JetDeg.sharp_hom (fun τ => lastEntry (nu τ)) τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  have hd : _root_.GlobalTheory.ColNorms.degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ = Finsupp.weight (GlobalTheory.JetDeg.derW a b τ) μ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, _root_.GlobalTheory.ColNorms.degAt, Finset.sum_filter,
      Finset.sum_subset (Finset.subset_univ _)]
    · simp [GlobalTheory.JetDeg.derW]
    · intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk]
      simp
  rw [hd, h]
  push_cast
  obtain ⟨h0, ⟨s', hs'⟩, -⟩ := hw τ
  have e : ∀ i, (nu τ).w i = ((lam τ).natW i : ℤ) + lastEntry (nu τ) := fun i => by
    have hi := i.2
    have ha : 0 < a := by omega
    rw [GlobalTheory.JetDeg.natW_cast, lastEntry, DomWeight.detShift, DomWeight.detShift, dite_eq_left ha, dite_eq_left ha,
      Int.toNat_of_nonneg (h0 _), hs', hs']
    ring
  simp [e, Finset.sum_add_distrib, mul_comm]


omit [StarRing K] in
theorem map_jetMap_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ)
    (hJ : ∀ e, (∀ τ, ((_root_.GlobalTheory.ColNorms.degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    map σ (jetMap J (fun τ => lastEntry (nu τ)) P) = jetMap J' (fun τ => lastEntry (nu τ)) (map σ P) := by
  have hdet : ∀ τ : ι, map σ (frDet K a τ) = frDet ℂ a τ := fun τ => by
    rw [GlobalTheory.JetPoint.map_frDet, frDet]
    simp only [map_X]
  rw [GlobalTheory.GO.map_jetMap σ J J' 1 _ P fun μ hμ => by
    rw [one_mul]; exact hJ _ (degAt_eq lam nu lam' hw P hP μ hμ), one_smul]
  simp [jetMap, hdet]

end GlobalTheory.JetBase

theorem GlobalTheory.coefOpLe_jetOp_of_opNormSqLe : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((_root_.GlobalTheory.ColNorms.degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  intro K _ _ _ σ ι _ a b lam nu lam' hw hK hC J J' hJ t ht x
  have h := ht ⟨MvPolynomial.map σ (x : Pol K ι a), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ lam' _ _ ?_) h
  rw [GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hC _ _ (Subtype.prop _)), GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hK _ _ x.2)]
  exact (GlobalTheory.JetBase.map_jetMap_eq σ lam nu lam' hw J J' hJ _ x.2).symm

end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.adicTensor_exists_rational_add_integral_mul : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  first | (exact @GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (exact GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB  <;> assumption)
end
