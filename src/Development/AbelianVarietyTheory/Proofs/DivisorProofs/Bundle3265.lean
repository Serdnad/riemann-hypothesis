module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R}

theorem ext_of_pts (hP : IsProper π) (hS : Surjective π) (hI : IsIntegral S) {Y W : Over (Sp R)} (hY : Flat Y.hom)
    (f₁ f₂ : Y ⟶ W) (h : ∀ (T : Over S) (P : Over.mk (T.hom ≫ π) ⟶ Y), P ≫ f₁ = P ≫ f₂) : f₁ = f₂ := by
  have hpb : IsPullback (pullback.fst Y.hom π) (pullback.snd Y.hom π) Y.hom π := IsPullback.of_hasPullback _ _
  have key : pullback.fst Y.hom π ≫ f₁.left = pullback.fst Y.hom π ≫ f₂.left := by
    have := h (Over.mk (pullback.snd Y.hom π)) (Over.homMk (pullback.fst Y.hom π) pullback.condition)
    simpa using congrArg CommaMorphism.left this
  obtain ⟨h₀, _, hu⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S Y.left (pullback Y.hom π) W.left π Y.hom (pullback.fst Y.hom π)
    (pullback.snd Y.hom π) hP hS hI hY hpb (pullback.fst Y.hom π ≫ f₁.left)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])
  ext
  exact (hu _ rfl).trans (hu _ key.symm).symm

variable {G' : Over S} {G : Over (Sp R)} {β : G'.left ⟶ G.left}

def dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : Over.mk (T.hom ≫ π) ⟶ G :=
  Over.homMk (x.left ≫ β) (by
    change x.left ≫ β ≫ G.hom = T.hom ≫ π
    rw [hpb.w, ← Category.assoc, Over.w x])

def up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) : T ⟶ G' :=
  Over.homMk (hpb.lift a.left T.hom (by simpa using Over.w a)) (hpb.lift_snd _ _ _)

theorem dn_up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) :
    dn hpb (up hpb a) = a := by
  ext; simp [dn, up]

theorem up_dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : up hpb (dn hpb x) = x := by
  ext; apply hpb.hom_ext <;> simp [dn, up]

end GlobalTheory.Mum.DescGrp

end

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R} {G' : Over S} [GrpObj G'] {G : Over (Sp R)} {β : G'.left ⟶ G.left}

theorem pt_mul (hpb : IsPullback β G'.hom G.hom π) (m : G ⊗ G ⟶ G)
    (hm : ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β)
    (T : Over S) (a b : Over.mk (T.hom ≫ π) ⟶ G) : lift a b ≫ m = dn hpb (up hpb a * up hpb b) := by
  ext
  rw [hm T (up hpb a) (up hpb b) a b (by simp [up]) (by simp [up])]
  rfl

theorem pt_one (hpb : IsPullback β G'.hom G.hom π) (e : 𝟙_ (Over (Sp R)) ⟶ G)
    (he : ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) (T : Over S) :
    toUnit (Over.mk (T.hom ≫ π)) ≫ e = dn hpb 1 := by
  ext; rw [he]; rfl

theorem pt_inv (hpb : IsPullback β G'.hom G.hom π) (i : G ⟶ G)
    (hi : ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      (x₀ ≫ i).left = x⁻¹.left ≫ β) (T : Over S) (a : Over.mk (T.hom ≫ π) ⟶ G) :
    a ≫ i = dn hpb (up hpb a)⁻¹ := by
  ext; rw [hi T (up hpb a) a (by simp [up])]; rfl

section shapes
variable {G : Over (Sp R)} {T : Over (Sp R)}

theorem sh_assocL (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (m ▷ G) ≫ m = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _) ≫ m) (P ≫ snd _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_assocR (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (α_ G G G).hom ≫ (G ◁ m) ≫ m =
      lift (P ≫ fst _ _ ≫ fst _ _) (lift (P ≫ fst _ _ ≫ snd _ _) (P ≫ snd _ _) ≫ m) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneL (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (λ_ G).inv ≫ (e ▷ G) ≫ m = lift (toUnit T ≫ e) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneR (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (ρ_ G).inv ≫ (G ◁ e) ≫ m = lift P (toUnit T ≫ e) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_comm (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (β_ G G).hom ≫ m = lift (P ≫ snd _ _) (P ≫ fst _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_id (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ m = lift (P ≫ fst _ _) (P ≫ snd _ _) ≫ m := by
  rw [← comp_lift, lift_fst_snd, Category.comp_id]
theorem sh_invL (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift i (𝟙 G) ≫ m = lift (P ≫ i) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_invR (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift (𝟙 G) i ≫ m = lift P (P ≫ i) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_unit (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) : P ≫ toUnit G ≫ e = toUnit T ≫ e := by
  rw [← Category.assoc, comp_toUnit]
end shapes

theorem flat_prod2 (G : Over (Sp R)) [Flat G.hom] : Flat (G ⊗ G).hom :=
  inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
theorem flat_prod3 (G : Over (Sp R)) [Flat G.hom] : Flat ((G ⊗ G) ⊗ G).hom := by
  have := flat_prod2 G
  exact inferInstanceAs (Flat (pullback.fst (G ⊗ G).hom G.hom ≫ (G ⊗ G).hom))

end GlobalTheory.Mum.DescGrp


open GlobalTheory.Mum.DescGrp in
theorem GlobalTheory.Mum.descGrpObj_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ (m : G ⊗ G ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (i : G ⟶ G), (∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β) → (∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) → (∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β) → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hP hS hI G' _ _ G β hsm hpb m e i hm he hi
  haveI : Smooth G.hom := hsm
  have f1 : Flat G.hom := inferInstance
  have f2 : Flat (G ⊗ G).hom := flat_prod2 G
  have f3 : Flat ((G ⊗ G) ⊗ G).hom := flat_prod3 G
  have hM := pt_mul hpb m hm
  have hE := pt_one hpb e he
  have hI' := pt_inv hpb i hi
  have a1 : e ▷ G ≫ m = (λ_ G).hom := by
    rw [← cancel_epi (λ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneL, Category.comp_id, hE, hM, up_dn, _root_.one_mul, dn_up]
  have a2 : G ◁ e ≫ m = (ρ_ G).hom := by
    rw [← cancel_epi (ρ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneR, Category.comp_id, hE, hM, up_dn, _root_.mul_one, dn_up]
  have a3 : m ▷ G ≫ m = (α_ G G G).hom ≫ G ◁ m ≫ m := by
    refine ext_of_pts hP hS hI f3 _ _ (fun T P => ?_)
    rw [sh_assocL, sh_assocR]
    simp only [hM, up_dn, _root_.mul_assoc]
  have a4 : lift i (𝟙 G) ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invL, sh_unit, hE, hI', hM, up_dn, _root_.inv_mul_cancel]
  have a5 : lift (𝟙 G) i ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invR, sh_unit, hE, hI', hM, up_dn, _root_.mul_inv_cancel]
  have a6 : (β_ G G).hom ≫ m = m := by
    refine ext_of_pts hP hS hI f2 _ _ (fun T P => ?_)
    rw [sh_comm, sh_id P m, hM, hM]
    letI : CommMonoid (T ⟶ G') := Hom.commMonoid
    rw [_root_.mul_comm]
  letI inst : GrpObj G :=
    { one := e, mul := m, inv := i, one_mul := a1, mul_one := a2, mul_assoc := a3, left_inv := a4,
      right_inv := a5 }
  exact ⟨inst, ⟨a6⟩, hpb, fun T x y x₀ y₀ hx hy => by
    rw [Hom.mul_def]; exact hm T x y x₀ y₀ hx hy⟩
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem expBij_of_basis_card : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → 1 ≤ k → ∀ (Λ : Type) [Fintype Λ] (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k), Fintype.card Λ = k ^ A.g → (∀ l, U.Expands k (σ l) (b l)) → U.ExpBij k := by
  intro R _ _ I D A G _ _ U k hR hk Λ _ b σ hcard hσ
  classical
  obtain ⟨β, -, hβ⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose C hC using fun l => (hβ (σ l)).exists
  have hCc : ∀ l, GlobalTheory.UnifPowAdm.IsComb (pullback.snd G.hom (jK R)) (σ l) (C l) β := fun l jj => hC l jj
  let Φ : (Λ → FractionRing R) →ₗ[FractionRing R] (Fin (k ^ A.g) → FractionRing R) :=
    { toFun := fun c a => ∑ l, c l * C l a
      map_add' := fun c d => by funext a; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _ }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨s, hs⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
    have h1 := hs.trans hCc
    have hz : ∀ a, ∑ l, c l * C l a = 0 := fun a => congrFun hc a
    have h0 : ∀ jj, s.f jj = 0 := fun jj => by
      rw [h1 jj]
      simp [hz]
    have hE := GlobalTheory.UnifPowAdm.expands_comb U k hσ hs
    have h2 := GlobalTheory.ExpZero.main R I D A G U k hR s _ h0 hE
    exact funext fun l => Fintype.linearIndependent_iff.1 b.linearIndependent c h2 l
  have hsurj : Function.Surjective Φ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [hcard]
  refine GlobalTheory.UnifPowAdm.expBij_of_basis U k hR b σ hσ fun s => ?_
  obtain ⟨d, hd, -⟩ := hβ s
  obtain ⟨c, rfl⟩ := hsurj d
  obtain ⟨s', hs'⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
  have e : s' = s := (hs'.trans hCc).unique fun jj => hd jj
  exact ⟨c, e ▸ hs'⟩

end GlobalTheory.ProdUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem famDim_of_expBij : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → U.ExpBij k → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g := by
  intro R _ _ I D A G _ _ U k hk hbij
  obtain ⟨b, hex, huniq⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin : ∀ (c : Fin (k ^ A.g) → FractionRing R) (s : U.SecK k),
      (∀ j, s.f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) →
      U.Expands k s (∑ i, c i • F i) := fun c s hs =>
    GlobalTheory.UnifPowAdm.expands_comb U k (s := b) hF (fun j => hs j)
  let φ : (Fin (k ^ A.g) → FractionRing R) →ₗ[FractionRing R] Fam D.toPre (FractionRing R) k :=
    Fintype.linearCombination (FractionRing R) F
  have hφ : ∀ c, φ c = ∑ i, c i • F i := fun c => rfl
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 := hlin c s hs
    have h2 := hlin c' s' hs'
    rw [← hφ] at h1 h2
    rw [← h] at h2
    have e : s = s' := (hbij.2 (φ c)).unique h1 h2
    subst e
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

end GlobalTheory.ProdUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_affine_open_of_finset_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ s : Finset G.left,
    (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR G _ _ hG s hs
  haveI : IsNoetherianRing R := hR.1
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth G.hom := hG.smooth
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom

  rcases s.eq_empty_or_nonempty with hs0 | ⟨x₀, hx₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, by simp [hs0]⟩

  have hcl : ∀ x : G.left, ∃ y ∈ closure ({x} : Set G.left), IsClosed ({y} : Set G.left) :=
    fun x => isClosed_closure.exists_closed_singleton ⟨x, subset_closure rfl⟩
  choose f hfx hfc using hcl
  have hsp : ∀ x, x ⤳ f x := fun x => specializes_iff_mem_closure.2 (hfx x)
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  have hfib : ∀ x ∈ s, G.hom (f x) = closedPoint R := by
    intro x hx
    have h1 : G.hom x ⤳ G.hom (f x) := (hsp x).map G.hom.continuous
    rw [hs x hx] at h1
    have h2 := specializes_iff_mem_closure.1 h1
    exact closure_minimal (subset_refl _) hcp h2
  classical
  let s' : Finset G.left := s.image f
  have hs' : ∀ y ∈ s', G.hom y = closedPoint R ∧ IsClosed ({y} : Set G.left) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hfib x hx, hfc x⟩
  suffices H : ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ y ∈ s', y ∈ O by
    obtain ⟨O, hO, hyO⟩ := H
    exact ⟨O, hO, fun x hx => (hsp x).mem_open O.2 (hyO _ (Finset.mem_image_of_mem f hx))⟩

  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : G.left.Opens) from trivial)

  obtain ⟨O, ⟨u, huO, hu⟩, hmove⟩ :=
    GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open R G hG V ⟨x₀, hxV, hs x₀ hx₀⟩ s' hs'

  obtain ⟨R₁, _, _, _, ρ, a, hfin, het, ha, haO⟩ :=
    GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR G hG.smooth O ⟨u, huO, hu⟩
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin.2.2
  haveI : Algebra.Etale R R₁ := het
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Module.Free R R₁ := Module.free_of_flat_of_isLocalRing

  let A : Over.mk (spMap ρ) ⟶ G := Over.homMk a ha
  obtain ⟨W, hW, hzW⟩ := GlobalTheory.T.exists_affineOpen_translate_baseChange R R₁ ρ G V hV A

  have hpb : IsPullback (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ)) G.hom
      (spMap (algebraMap R R₁)) := IsPullback.of_hasPullback G.hom (spMap ρ)
  refine GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange R R₁ G.left (pullback G.hom (spMap ρ)) G.hom (pullback.snd _ _) (pullback.fst _ _)
    hpb inferInstance inferInstance W hW s' ?_
  intro z hz
  let Ω := (pullback G.hom (spMap ρ)).residueField z
  let z' : Sp Ω ⟶ pullback G.hom (spMap ρ) := (pullback G.hom (spMap ρ)).fromSpecResidueField z
  have hz' : ∀ w, z' w = z := fun w => Scheme.fromSpecResidueField_apply z w
  let t : Sp Ω ⟶ Sp R := z' ≫ pullback.fst _ _ ≫ G.hom
  let x : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.fst _ _) (by simp [t])
  let a' : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.snd _ _ ≫ a)
    (by simp only [t, Over.mk_hom, Category.assoc, ha, pullback.condition])
  have hx : ∀ w, x.left w ∈ s' := by
    intro w
    show (z' ≫ pullback.fst _ _) w ∈ s'
    rw [Scheme.Hom.comp_apply, hz']
    exact hz
  have ha' : ∀ w, a'.left w ∈ O := by
    intro w
    show (z' ≫ pullback.snd _ _ ≫ a) w ∈ O
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact haO ⟨_, rfl⟩
  have hV' := hmove Ω t x a' hx ha'
  have := hzW Ω z' t x a' rfl rfl hV' (closedPoint Ω)
  first
    | exact (Scheme.fromSpecResidueField_apply z _) ▸ this
    | simpa only [hz'] using this
    | (convert this using 1; exact (hz' _).symm)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdDim

theorem smoothDim_tensor {S : Scheme.{0}} {A B : Over S} {g g' : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    (hg' : SmoothOfRelativeDimension g' B.hom) : SmoothOfRelativeDimension (g' + g) (A ⊗ B).hom := by
  have : SmoothOfRelativeDimension g' (Limits.pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip hg'
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g' g _ _

theorem g_eq_add : ∀ (S : Scheme.{0}) (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A),
    Nonempty S → IsIso (lift a₁ a₂) → P.g = P₁.g + P₂.g := by
  intro S P P₁ P₂ a₁ a₂ ⟨s⟩ hi
  have h := smoothDim_tensor P₁.smoothDim P₂.smoothDim
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget S).map (lift a₁ a₂)))
  have hw : (lift a₁ a₂).left ≫ (P₁.A ⊗ P₂.A).hom = P.A.hom := Over.w _
  have h2 : SmoothOfRelativeDimension (0 + (P₂.g + P₁.g)) P.A.hom := by
    rw [← hw]
    exact smoothOfRelativeDimension_comp 0 (P₂.g + P₁.g) _ _
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h2 (eSec P.A s)
  omega

end GlobalTheory.ProdDim
end
