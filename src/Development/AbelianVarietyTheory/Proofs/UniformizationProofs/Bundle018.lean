module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecLift
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_sec_lift_alt : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ (N' : LB X') (w' : LB.Iso N' (N.pull β)), N'.IsLB → w'.IsGen → ∀ s' : LB.Sec N', ∃ s : LB.Sec N, (∀ z (k : (N).ι) (k' : (N').ι), (β) z ∈ (N).U k → z ∈ (N').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  first | exact @GlobalTheory.SecLift.exists_sec_lift | exact GlobalTheory.SecLift.exists_sec_lift | (intros; apply GlobalTheory.SecLift.exists_sec_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_eq_mul_of_vanishing_mod_element : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  first | exact @GlobalTheory.SectionKernel.exists_sec_of_vanishing | exact GlobalTheory.SectionKernel.exists_sec_of_vanishing | (intros; apply GlobalTheory.SectionKernel.exists_sec_of_vanishing <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxKernel

open GlobalTheory.KerPow

variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]

theorem hasGen_flat (F : J → (X' ⟶ X)) {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : HasGen (LB.LinComb L F (fun _ => 1)) ψ ε) :
    HasGen L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  have le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K := K × J) (fun q => ψ q.1 ≫ F q.2) j →
      y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  refine gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε)
    (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1))
    (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H
  refine (gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans
    (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i))
    (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)
  simp only [zpow_one, Category.assoc, Finset.prod_zpow]

theorem gen_of_chart {M : LB Y} (hM : M.IsLB) (i₀ : M.ι) (h : ∀ y, y ∈ M.U i₀) : ∃ t : LB.Gen M, t.IsGen := by
  refine ⟨⟨fun i => res (le_inf le_rfl (fun y _ => h y) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have := LB.res_cocycle hM i j i₀ (W := M.U i ⊓ M.U j) le_rfl (le_inf inf_le_right fun y _ => h y)
    (le_inf inf_le_left fun y _ => h y)
  refine (LB.res_res _ _ _).trans (this.symm.trans (congrArg₂ (· * ·) ?_ (LB.res_res _ _ _).symm))
  exact unit_ext fun y hy => gm_res _ y _ hy _

theorem locGen_base (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by
  intro p
  choose j hj using fun k => exists_chart hL (b k p)
  refine ⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k

theorem locGen_flat (F : J → (X' ⟶ X)) {π : Y ⟶ B} {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : LocGen (LB.LinComb L F (fun _ => 1)) π ψ ε) :
    LocGen L (K := K × J) π (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  exact ⟨V, hV, (hasGen_flat F t).pull (𝟙 _) fun q => by rw [Category.id_comp, Category.assoc]⟩

end GlobalTheory.BoxKernel

namespace GlobalTheory


open KerPow BoxKernel in
theorem kTriv_boxLB : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  intro S G' G _ _ _ _ j p L hL hK R _ t x hx
  classical
  have H : LocGen (boxLB L p.pr) (K := Fin 2) (fst (Over.mk t) G').left
      ![(translPt G' x).left, (snd (Over.mk t) G').left] ![1, -1] := (locGen_iff _ _ _).1 hx
  clear hx
  generalize Over.mk t = T at x H
  refine p.lim.hom_ext fun ⟨i⟩ => ?_
  have := p.hom
  show x ≫ p.pr i = (1 : T ⟶ G') ≫ p.pr i
  rw [MonObj.one_comp]
  let u : G ⟶ G' := p.lim.lift (Fan.mk G fun i' => if i' = i then 𝟙 G else 1)
  have hu : ∀ i', u ≫ p.pr i' = if i' = i then 𝟙 G else 1 := fun i' => p.lim.fac _ ⟨i'⟩
  let a : Fin 2 → (T ⊗ G ⟶ G') := ![(fst T G ≫ x) * (snd T G ≫ u), snd T G ≫ u]
  have H₁ := H.baseChange (π' := (fst T G).left) (T ◁ u).left (𝟙 _)
    ((congrArg (fun q => q.left) (whiskerLeft_fst T u)).trans (Category.comp_id _).symm)
    (φ' := fun k => (a k).left) (fun k => by
      fin_cases k
      · refine congrArg (fun q => q.left) (show T ◁ u ≫ ((fst T G' ≫ x) * snd T G') = (fst T G ≫ x) * (snd T G ≫ u) from ?_)
        rw [MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T u))
  let b : Fin 2 × Fin j → (T ⟶ G) := fun q => ![x ≫ p.pr q.2, 1] q.1
  have H₂ := locGen_base hL (fst T G).left (fun q => (b q).left)
    (fun q => if q.2 = i then 0 else (![1, -1] : Fin 2 → ℤ) q.1)
  refine eq_one_of_locGen hK _ ((locGen_flat _ H₁).comb hL H₂ fun U _ h => ?_)
  have e₀ : ∀ k i', i' ≠ i → (a k).left ≫ (p.pr i').left = (fst T G).left ≫ (b (k, i')).left := fun k i' hi => by
    refine congrArg (fun q => q.left) (show a k ≫ p.pr i' = fst T G ≫ b (k, i') from ?_)
    fin_cases k
    · show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i' = fst T G ≫ x ≫ p.pr i'
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_neg hi, MonObj.comp_one, _root_.mul_one]
    · show (snd T G ≫ u) ≫ p.pr i' = fst T G ≫ 1
      rw [Category.assoc, hu, if_neg hi, MonObj.comp_one, MonObj.comp_one]
  have e₁ : ∀ k, (a k).left ≫ (p.pr i).left =
      (![(translPt G (x ≫ p.pr i)).left, (snd T G).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · refine congrArg (fun q => q.left)
        (show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i = (fst T G ≫ x ≫ p.pr i) * snd T G from ?_)
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_pos rfl, Category.comp_id]
    · refine congrArg (fun q => q.left) (show (snd T G ≫ u) ≫ p.pr i = snd T G from ?_)
      rw [Category.assoc, hu, if_pos rfl, Category.comp_id]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single i (fun i' _ hi => ?_) (fun hi => (hi (Finset.mem_univ _)).elim)]
  · simp only [if_true, zpow_zero, inv_one, _root_.mul_one, e₁]
  · simp only [if_neg hi, e₀ k i' hi, mul_inv_cancel]

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.StabFlat

theorem flat_of_regular {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] {ϖ : V}
    (hϖ : Irreducible ϖ) (σ : V →+* C) (h : IsSMulRegular C (σ ϖ)) : σ.Flat := by
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, mul_assoc, map_pow] at h1
  exact (h.pow n).right_eq_zero_of_smul (((u.isUnit.map σ).mul_right_eq_zero).1 h1)

theorem flat_of_ideals : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → ∃ I : Ideal (X.presheaf.stalk (j h)), IsSMulRegular (X.presheaf.stalk (j h) ⧸ I) (σ ϖ) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ _ ϖ hϖ X H f j hj hI
  refine Flat.of_stalkMap _ fun h => ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have reg : IsSMulRegular (H.presheaf.stalk h) ((j.stalkMap h).hom (σ.hom ϖ)) := by
    by_cases hu : IsUnit (σ.hom ϖ)
    · exact (hu.map _).isRegular.left.isSMulRegular
    obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hu
    have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
      (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
        ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
    have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
    have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have e : y (IsLocalRing.closedPoint _) = h := by
      apply j.isClosedEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
      exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
    have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
    refine IsSMulRegular.of_right_eq_zero_of_smul fun b hb => ?_
    obtain ⟨a, rfl⟩ := j.stalkMap_surjective h b
    refine h₁ (Ideal.Quotient.eq_zero_iff_mem.1 (hr.right_eq_zero_of_smul ?_))
    have := congrArg ψ.hom hb
    rw [smul_eq_mul, map_mul, hψ', hψ', map_zero] at this
    exact this
  have fl : (σ ≫ j.stalkMap h).hom.Flat := flat_of_regular hϖ _ reg
  have e : σ ≫ j.stalkMap h = StructureSheaf.toStalk V ((j ≫ f) h) ≫ (j ≫ f).stalkMap h := by
    apply Spec.map_injective
    refine Eq.trans ?_ (Spec.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Spec.fromSpecStalk_eq' (CommRingCat.of V) ((j ≫ f) h)))
    rw [Spec.map_comp, hσ, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (j ≫ f)).symm
  let S := (Spec (CommRingCat.of V)).presheaf.stalk ((j ≫ f) h)
  letI : Algebra V S := StructureSheaf.stalkAlgebra V ((j ≫ f) h)
  have : ((j ≫ f) h).asIdeal.IsPrime := PrimeSpectrum.isPrime (R := V) _
  have : IsLocalization.AtPrime S ((j ≫ f) h).asIdeal := StructureSheaf.IsLocalization.to_stalk V _
  letI : Algebra V (H.presheaf.stalk h) := (σ ≫ j.stalkMap h).hom.toAlgebra
  letI : Algebra S (H.presheaf.stalk h) := ((j ≫ f).stalkMap h).hom.toAlgebra
  have : IsScalarTower V S (H.presheaf.stalk h) := IsScalarTower.of_algebraMap_eq' (congrArg (·.hom) e)
  exact (Module.flat_iff_of_isLocalization S ((j ≫ f) h).asIdeal.primeCompl (H.presheaf.stalk h)).2 fl

theorem height_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] (g : ℕ)
    [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] (m : Ideal B) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = g := by
  have : Nontrivial B := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hm.ne_top (Subsingleton.elim _ _)
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime.trans
    (SmoothDim.ringKrullDim_of_etale_mvPolynomial K B g).le) ?_
  letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
    (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
    (S := MvPolynomial (Fin g) K) inferInstance inferInstance
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI hp := SmoothDim.isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
    (m.under (MvPolynomial (Fin g) K))
  letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
  rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
  rw [← h1, WithBot.coe_le_coe, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (m.under (MvPolynomial (Fin g) K)) m]
  exact le_self_add

theorem localization_of_isStandardSmooth {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R] [CommRing A]
    {ϖ : V} (h₀ : ϖ ∈ nonZeroDivisors V) [(Ideal.span {ϖ}).IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : ρ ϖ ∈ n) :
    IsNoetherianRing A ∧ algebraMap R A (ρ ϖ) ∈ nonZeroDivisors A ∧
      IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) ∧
      ringKrullDim (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) = g := by
  have hq : (Ideal.quotientMap ((Ideal.span {ϖ}).map ρ) ρ Ideal.le_comap_map).IsStandardSmoothOfRelativeDimension g := by
    have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange.{0} g)
    exact MorphismProperty.of_isPushout
      (P := RingHom.toMorphismProperty (@RingHom.IsStandardSmoothOfRelativeDimension g))
      (NilpotentLift.isPushout_quotient_map (Ideal.span {ϖ}) (CommRingCat.ofHom ρ)).flip hρ
  letI := ρ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g V R := hρ
  have : Algebra.IsStandardSmooth V R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing V R
  refine ⟨IsLocalization.isNoetherianRing n.primeCompl A inferInstance, ?_, ?_⟩
  · have h₁ : IsSMulRegular R ϖ := Module.Flat.isSMulRegular_of_nonZeroDivisors h₀
    refine IsLocalization.map_nonZeroDivisors_le n.primeCompl A ⟨ρ ϖ, ?_, rfl⟩
    exact mem_nonZeroDivisors_iff_left.2 fun x hx => h₁.right_eq_zero_of_smul hx
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  set J := (Ideal.span {ϖ}).map ρ with hJ
  obtain ⟨φ, -, hφ⟩ := hq.exists_etale_mvPolynomial
  have hJ' : J = Ideal.span {ρ ϖ} := by rw [hJ, Ideal.map_span, Set.image_singleton]
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker, hJ', Ideal.span_singleton_le_iff_mem]
  letI := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) (R ⧸ J) := hφ.toAlgebra
  have : IsRegularRing (R ⧸ J) := isRegularRing_of_etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) _
  have hm : (n.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (Ideal.span {algebraMap R A (ρ ϖ)}).comap (algebraMap R A) := by
    rw [hJ', Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self _
  letI : Algebra (R ⧸ J) (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ Ideal.span {algebraMap R A (ρ ϖ)})
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ', Ideal.map_span, Set.image_singleton])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  refine ⟨?_, (IsLocalization.AtPrime.ringKrullDim_eq_height (n.map (Ideal.Quotient.mk J)) _).trans
    (height_of_etale_mvPolynomial (V ⧸ Ideal.span {ϖ}) (R ⧸ J) g _)⟩
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem stalk_of_smooth : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → IsNoetherianRing (X.presheaf.stalk x) ∧ σ ϖ ∈ nonZeroDivisors (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) ∧ ringKrullDim (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) = g := by
  intro V _ _ _ ϖ hϖ X f g hg x hx σ hσ hn
  obtain ⟨U, hU, W, hW, hxW, e, H⟩ := hg.exists_isStandardSmoothOfRelativeDimension x
  have hfx : f x = IsLocalRing.closedPoint V := by
    refine ((congrArg f Scheme.fromSpecStalk_closedPoint.symm).trans
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ)).trans ?_
    refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
      (PrimeSpectrum.isPrime _).ne_top ?_))
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hn
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 (hfx ▸ e hxW)
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ f.appLE ⊤ W e
  have hρ : ρ.hom.IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).2 H
  have hc : ρ ≫ X.presheaf.germ W x hxW = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [← hσ, ← hW.fromSpecStalk_eq_fromSpecStalk hxW, Spec.map_comp, Spec.map_comp, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hW e, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hl : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  have hs : algebraMap Γ(X, W) (X.presheaf.stalk x) (ρ.hom ϖ) = σ ϖ := congrArg (fun q => q.hom ϖ) hc
  haveI : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal V
  rw [← hs]
  refine localization_of_isStandardSmooth (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hρ
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal ?_
  by_contra hm
  exact hn (hs ▸ IsLocalization.map_units (X.presheaf.stalk x)
    (⟨_, hm⟩ : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl))

end GlobalTheory.StabFlat
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionThetaLocal

theorem exists_theta_of_pow_eq_one : ∀ (S₀ : Scheme.{0}) (G : Over S₀) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (S : Type) [CommRing S] [IsLocalRing S] (t : Spec (CommRingCat.of S) ⟶ S₀) (k : ℕ) (x : Over.mk t ⟶ G), x ^ k = 1 → ∃ θ : ThetaGrp G L.L (k : ℤ) (Over.mk t), θ.pt = x := by
  intro S₀ G _ _ L c S _ _ t k x hx
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_cubN c (1 : Over.mk t ⊗ G ⟶ G) (fst (Over.mk t) G ≫ x) (snd (Over.mk t) G) k
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := S) L.L L.isLB (K := Fin 2)
    ![x.left, (1 : Over.mk t ⟶ G).left] ![-(k : ℤ), k]
  have hm : (fst (Over.mk t) G ≫ x) ^ k = 1 := by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : (fst (Over.mk t) G).left ≫ (1 : Over.mk t ⟶ G).left = (1 : Over.mk t ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk t) G).left ≫ x.left = (fst (Over.mk t) G ≫ x).left := rfl
  have h3 : translPt G x = (fst (Over.mk t) G ≫ x) * snd (Over.mk t) G := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen L.isLB
    (φ' := ![(snd (Over.mk t) G).left, (translPt G x).left]) (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      erw [h1, h2]
      rw [hm, h3]
      simp only [_root_.one_mul, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ e (fst (Over.mk t) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.TorsionThetaLocal
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_eq_stalkMap_gs_id {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (y : Y') (U : Y.Opens) (hy : τ y ∈ U) (a : Γ(Y, U)) :
    gs τ y U a = (τ.stalkMap y).hom (gs (𝟙 Y) (τ y) U a) := by
  have e : gs (𝟙 Y) (τ y) U a = (Y.presheaf.germ U (τ y) hy).hom a := gs_eq (𝟙 Y) (τ y) U hy a
  rw [e, gs_eq τ y U hy]
  exact (Scheme.Hom.germ_stalkMap_apply τ U y hy a).symm

theorem sval_ne_zero_of_isIso : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)), (∃ j, s.f j ≠ 0) → ∀ (Y' : Scheme.{0}) (τ : Y' ⟶ Y) [IsIso τ] (y : Y') (J), Good L y J → sval s τ y J ≠ 0 := by
  intro X Y _ L hL K _ φ ε s hs Y' τ _ y J hJ h0
  have hG : Good L (τ y) (fun χ : Y ⟶ X => J (τ ≫ χ)) := fun χ => hJ (τ ≫ χ)
  have h1 := (exists_ne_zero_iff_sval_ne_zero s hG).1 hs
  rw [sval_of s (𝟙 Y) (τ y) _ (fun k => J (τ ≫ φ k)) (fun k => by rw [Category.id_comp])] at h1
  apply h1
  have h2 : gs τ y (LB.wchart L φ (fun k => J (τ ≫ φ k))) (s.f (fun k => J (τ ≫ φ k))) = 0 := h0
  have h3 := (gs_eq_stalkMap_gs_id τ y _ (hJ.mem φ τ) _).symm.trans h2
  have hinj : Function.Injective (τ.stalkMap y).hom :=
    (ConcreteCategory.bijective_of_isIso (τ.stalkMap y)).1
  exact (map_eq_zero_iff _ hinj).1 h3

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sec_eq_zero_of_sval_whiskerRight_zero : ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (z : (T' ⊗ B).left) (J), Good L z J → sval d (ψ ▷ B).left z J = 0) → ∀ j, d.f j = 0 := by
  first | exact @GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero | exact GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero | (intros; apply GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero <;> assumption)
end
