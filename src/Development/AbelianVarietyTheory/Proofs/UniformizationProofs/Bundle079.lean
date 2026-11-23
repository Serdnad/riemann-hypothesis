module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.MulSupp

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_eq_zero (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J}
    (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem exists_sub_sum {N : Type} (a : LB.Sec (LB.LinComb L φ ε)) (p : N → LB.Sec (LB.LinComb L φ ε)) (s : Finset N) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval a r z J - ∑ i ∈ s, sval (p i) r z J := by
  refine ⟨⟨fun j => a.f j - ∑ i ∈ s, (p i).f j, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩

  · rw [map_sub, map_sub, map_sum, map_sum, mul_sub, Finset.mul_sum, a.compat]
    exact congrArg _ (Finset.sum_congr rfl fun b _ => (p b).compat i j)
  · have hm := hJ.mem φ r
    refine (gs_eq r z _ hm _).trans ?_
    refine (congrArg _ (map_sub _ _ _)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·) (gs_eq r z _ hm _).symm ?_))
    refine (congrArg _ (map_sum _ _ _)).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun b _ => ?_))
    exact (gs_eq r z _ hm _).symm
end

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

noncomputable def cubAt (α β : D.X) {Z : Scheme.{0}} (ψ : Z ⟶ D.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
    (ψ ≫ (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A))).left) z J

theorem val_pull_cub (α β : D.X) {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {Z : Scheme.{0}}
    (r : Z ⟶ Y.left) (z : Z) {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p)).left) r z J = cubAt D α β (r ≫ p.left) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p) =
      p ≫ lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A)) := by
    simp only [comp_lift, comp_toUnit_assoc, Category.comp_id]
  rw [e, Over.comp_left, ← Category.assoc]
  rfl

theorem exists_prod (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (α β : D.X) (a : SecBT D T k α) (b : SecBT D T l β) :
    ∃ p : SecBT D T (k + l) (α + β), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval p r z J = sval a r z J * sval b r z J * (cubAt D α β (r ≫ (snd T D.P.A).left) z J).val := by
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := famφT D T (α + β)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _)
        (prod_cub (toUnit _ ≫ D.c α) (toUnit _ ≫ D.c β) (snd T D.P.A) h))).trans ?_
      have e₀ : ∀ u, padd D.P.A (snd T D.P.A) u = u * snd T D.P.A :=
        fun u => mul_comm (snd T D.P.A) u
      have e₁ : toUnit (T ⊗ D.P.A) ≫ D.c (α + β) = (toUnit _ ≫ D.c α) * (toUnit _ ≫ D.c β) := by
        rw [D.c_add]; exact MonObj.comp_mul _ _ _
      have e₂ : toUnit (T ⊗ D.P.A) ≫ η[D.P.A] = 1 := rfl
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, famφT, DegPre.famε, e₀, e₁, e₂, Matrix.cons_val]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec a b) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (snd T D.P.A))).left) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨p, fun Z r z J hJ => (hp Z r z J hJ).trans ?_⟩
  exact (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)
    ((sval_genSec _ _ r z hJ).trans (congrArg Units.val (val_pull_cub D α β _ r z hJ))))

variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_coord_mul {e : ℕ} (g : GtCoord I D e G) (α β : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left)
    (z : Z) {J} (hJ : Good D.P.L z J) :
    val (g.t (α + β)) x z J * cubAt D α β (x ≫ g.pG.left) z J = val (g.t α) x z J * val (g.t β) x z J := by
  have E := val_corr hJ (g.t_mul α β) x
  exact ((val_mul hJ _ _ _).trans (congrArg _ (val_pull_cub D α β g.pG x z hJ))).symm.trans (E.trans (val_mul hJ _ _ _))

theorem level {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G) (Λ : AddSubgroup D.X) (k l : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) (f) (f') (f'')
    (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) l σ' f') (h'' : U.ExpT (𝟙_ _) (k + l) σ'' f'')
    (hm : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J →
      sval σ'' r z J = sval σ r z J * sval σ' r z J)
    (hf : ∀ α ∉ Λ, ∀ j, (f α).f j = 0) (hf' : ∀ α ∉ Λ, ∀ j, (f' α).f j = 0) (χ₀ : D.X) (hχ : χ₀ ∉ Λ) (e : ℕ)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f'' χ₀) r z J = 0 := by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  obtain ⟨s'', hs''⟩ := h'' e
  have c₁ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left),
      (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (snd (𝟙_ _) G).left = x ≫ (fstG I e G).left := fun Z x =>
    (Category.assoc _ _ _).trans (congrArg (fun q => x ≫ q.left) (lift_snd (toUnit _) (fstG I e G)))
  have c₂ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left →
      r ≫ (fst (𝟙_ _) D.P.A).left = (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (fst (𝟙_ _) G).left := by
    intro Z x r hr
    have a₁ : fst (𝟙_ _) D.P.A = snd _ D.P.A ≫ toUnit _ := toUnit_unique _ _
    have a₂ : (U.gt e).pG ≫ toUnit _ = lift (toUnit _) (fstG I e G) ≫ fst (𝟙_ _) G := toUnit_unique _ _
    rw [a₁, Over.comp_left, ← Category.assoc, hr]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => x ≫ q.left) a₂).trans (Category.assoc _ _ _).symm)
  have ex : ∀ (g : D.X) (p : D.X × D.X), ∃ q : SecBT D (𝟙_ _) (k + l) g,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval q r z J = if p.1 + p.2 = g then
        sval (f p.1) r z J * sval (f' p.2) r z J * (cubAt D p.1 p.2 (r ≫ (snd _ D.P.A).left) z J).val else 0 := by
    intro g p
    by_cases hp : p.1 + p.2 = g
    · subst hp
      simpa only [if_true] using exists_prod D (𝟙_ _) k l p.1 p.2 (f p.1) (f' p.2)
    · exact ⟨H1.SectionArithmetic.secZero _, fun Z r z J hJ => by rw [if_neg hp]; exact sval_eq_zero _ (fun _ => rfl) r z hJ⟩
  choose q hq using ex
  choose d hd using fun g => exists_sub_sum (f'' g) (q g) (s ×ˢ s')
  let S : Finset D.X := s'' ∪ (s ×ˢ s').image (fun p => p.1 + p.2)
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  by_cases hS : χ₀ ∈ S
  swap
  · exact (hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ).1 χ₀ fun h => hS (Finset.mem_union_left _ h)
  have H := sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) (Fin 4) (famφT D (𝟙_ _))
    (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
      obtain ⟨-, E⟩ := hs Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨-, E'⟩ := hs' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨E₀, E''⟩ := hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      rw [hm _ _ z JG hJG, pow_add, _root_.mul_mul_mul_comm, E, E', Finset.sum_mul_sum, ← Finset.sum_product'] at E''
      simp only [hd _ Z r z J hJ, hq _ _ Z r z J hJ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [sub_eq_zero, ← Finset.sum_subset Finset.subset_union_left (fun g _ hg => by rw [E₀ g hg, zero_mul]), ← E'',
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : D.X × D.X => p.1 + p.2) hp)), hr,
        _root_.mul_mul_mul_comm, ← Units.val_mul, ← val_coord_mul (U.gt e) p.1 p.2 x z hJ, Units.val_mul]
      ring) χ₀ hS Z x r hr z J hJ
  rw [hd χ₀ Z r z J hJ, Finset.sum_eq_zero, sub_zero] at H
  · exact H
  intro p _
  rw [hq χ₀ p Z r z J hJ]
  split_ifs with hp
  · by_cases h₁ : p.1 ∈ Λ
    · have h₂ : p.2 ∉ Λ := fun h₂ => hχ (hp ▸ Λ.add_mem h₁ h₂)
      rw [sval_eq_zero _ (hf' _ h₂) r z hJ, mul_zero, zero_mul]
    · rw [sval_eq_zero _ (hf _ h₁) r z hJ, zero_mul, zero_mul]
  · rfl

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  intro V _ _ _ hV D A G _ _ U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  have eV : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V eV
  have : Nontrivial Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := eV.symm.nontrivial
  have : IsLocalRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    IsLocalRing.of_surjective' eV.toRingHom eV.surjective
  refine sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun a ha => ?_) _ D.P.L D.P.isLB
    (Fin 4) _ _ (f'' χ₀) (fun e => LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f'' χ₀)
      (level U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ e))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro hu
  have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) := hu
  have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
  rw [Iso.inv_hom_id_apply] at this
  exact ha this

end GlobalTheory.MulSupp
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.WeightTwo

theorem exists_sec_finsum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {I : Type} (s : Finset I) (d : I → LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval t r z J = ∑ i ∈ s, sval (d i) r z J := by
  refine ⟨⟨fun j => ∑ i ∈ s, (d i).f j, fun j j' => ?_⟩, fun Z r z J hJ => ?_⟩

  · rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (d i).compat j j'
  · exact DVR.gs_fsum r z _ (hJ.mem φ r) _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem formEq_cancel (k l : ℕ) (α β : D.X) :
    FormEq (Sum.elim (fun a => (D.P.A ◁ g.pG).left ≫ Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
        (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) a)
        (fun a => (snd D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.Oφ g.pG β a))
      (Sum.elim (Sum.elim (DegPre.famε k) (DegPre.famε l)) Oinvε)
      (Sum.elim (fun i => (fst D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.famφB α i)
        (fun _ : Unit => (snd D.P.A _ ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ))) := by
  intro U _ h
  have e₁ : (D.P.A ◁ g.pG).left ≫ (fst D.P.A D.P.A).left = (fst D.P.A _).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e₂ : (D.P.A ◁ g.pG).left ≫ (snd D.P.A D.P.A).left = (snd D.P.A _).left ≫ g.pG.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have f₀ : g.pG.left ≫ D.famφB β 0 = g.pG.left := Category.comp_id _
  have f₁ : g.pG.left ≫ D.famφB β 1 = D.Oφ g.pG β 0 := by
    change (g.pG ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left = (padd D.P.A g.pG (toUnit _ ≫ D.c β)).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  have f₂ : g.pG.left ≫ D.famφB β 2 = D.Oφ g.pG β 1 := by
    change (g.pG ≫ toUnit _ ≫ D.c β).left = (toUnit _ ≫ D.c β).left
    rw [comp_toUnit_assoc]
  have f₃ : g.pG.left ≫ D.famφB β 3 = D.Oφ g.pG β 3 := by
    change (g.pG ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]
  have f₄ : D.Oφ g.pG β 2 = g.pG.left := rfl
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, reassoc_of% e₁, reassoc_of% e₂,
    Finset.univ_unique, Finset.prod_singleton]
  rw [_root_.mul_assoc]
  congr 1
  rw [Fin.prod_univ_four, Fin.prod_univ_four, f₀, f₁, f₂, f₃, f₄, Over.comp_left _ _ _ (snd D.P.A _) g.pG]
  generalize h (_ ≫ g.pG.left) = a
  generalize h (_ ≫ D.Oφ g.pG β 0) = b
  generalize h (_ ≫ D.Oφ g.pG β 1) = c
  generalize h (_ ≫ D.Oφ g.pG β 3) = d
  change a ^ ((l : ℤ) - 1) * b ^ (1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) *
    (b ^ (-1 : ℤ) * c ^ (1 : ℤ) * a ^ (1 : ℤ) * d ^ (-1 : ℤ)) = a ^ (l : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem level (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i))
      (Sum.elim (DegPre.famε k) (DegPre.famε l)))) (s : Finset D.X)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj R I e G).left),
      xe ≫ g.pG.left = x.left → ye ≫ g.pG.left = y.left →
      xe ≫ (thickObj R I e G).hom = ye ≫ (thickObj R I e G).hom → ∀ (z : T.left) (J), Good D.P.L z J →
      ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J *
        ((val (g.t α) xe z J).val * (val (g.t β) ye z J).val) = 0)
    (α : D.X) (hα : α ∈ s) (β : D.X) (hβ : β ∈ s) (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left)
    (hr : ∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (D.P.A ⊗ D.P.A).hom)
    (z : Z) (J) (hJ : Good D.P.L z J) : sval (d (α, β)) r z J = 0 := by
  let Ge := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcl : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have ex : ∀ α : D.X, ∃ t : LB.Sec (LB.LinComb D.P.L
      (Sum.elim (fun i => (fst D.P.A Ge).left ≫ D.famφB α i) (fun _ : Unit => (snd D.P.A Ge ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ)))), ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ Ge).left) (z : Z) (J),
      Good D.P.L z J → sval t r z J = ∑ β ∈ s, sval (d (α, β)) (r ≫ (D.P.A ◁ g.pG).left) z J *
        (val (g.t β) (r ≫ (snd D.P.A Ge).left) z J).val := by
    intro α
    choose u hu using fun β : D.X => exists_sec D.P.isLB (formEq_cancel g k l α β)
      (pullMulSec (d (α, β)) (D.P.A ◁ g.pG).left (LB.pullGen D.P.L _ _ (g.t β) (snd D.P.A Ge).left)
        (DVR.pullGen_isGen D.P.L _ _ _ (g.t_gen β) _))
    obtain ⟨t, ht⟩ := exists_sec_finsum s u
    refine ⟨t, fun Z r z J hJ => (ht Z r z J hJ).trans (Finset.sum_congr rfl fun β _ => ?_)⟩
    rw [hu β Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_pull hJ]
  choose t ht using ex
  have h₁ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ _ _ t s (by
    intro Z x r hx z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ Ge).hom) ⟶ D.P.A ⊗ Ge := Over.homMk r rfl
    have E := H _ (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) x (r ≫ (snd D.P.A Ge).left) hx.symm
      (Category.assoc _ _ _) (by
        rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc]
        have w₁ : g.pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w g.pG
        have w₂ : (snd D.P.A Ge).left ≫ (thickObj R I e G).hom ≫ thick R I e = (D.P.A ⊗ Ge).hom :=
          Over.w (snd D.P.A Ge)
        rw [w₂, ← w₁, ← Category.assoc, ← hx, Category.assoc, Over.w]) z J hJ
    have e₁ : lift (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) = r' ≫ D.P.A ◁ g.pG := by
      ext1 <;> simp
    rw [e₁] at E
    refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) E
    rw [ht α Z r z J hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [_root_.mul_assoc, mul_comm (val (g.t β) _ z J).val]
    rfl) α hα
  have h₂ := LiftTest.main R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ D.P.L D.P.isLB _ _ _ (t α) h₁
  have h₃ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _
    (fun β => Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
      (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) _ (fun β => d (α, β)) s (by
    intro Z y r hy z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ D.P.A ⊗ D.P.A := Over.homMk r rfl
    let y' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ Ge := Over.homMk y (by
      change y ≫ Ge.hom = r ≫ (D.P.A ⊗ D.P.A).hom
      rw [← Over.w g.pG, ← Category.assoc, ← hy, Category.assoc, Over.w])
    have hy' : r' ≫ snd _ _ = y' ≫ g.pG := Over.OverMorphism.ext hy
    have e₁ : lift (r' ≫ fst _ _) y' ≫ D.P.A ◁ g.pG = r' := by
      ext1
      · simp
      · rw [hy', Category.assoc, whiskerLeft_snd, lift_snd_assoc]
    have e₂ : (lift (r' ≫ fst _ _) y').left ≫ (D.P.A ◁ g.pG).left = r := congrArg CommaMorphism.left e₁
    have e₃ : (lift (r' ≫ fst _ _) y').left ≫ (snd D.P.A Ge).left = y :=
      congrArg CommaMorphism.left (lift_snd (r' ≫ fst _ _) y')
    have E := h₂ Z (lift (r' ≫ fst _ _) y').left ⟨y ≫ (thickObj R I e G).hom, by
      rw [Over.w, Category.assoc]
      exact Over.w y'⟩ z J hJ
    rw [ht α _ _ z J hJ, e₂, e₃] at E
    exact E) β hβ
  exact LiftTest.main R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (d (α, β)) h₃ Z r hr z J hJ

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε k) (DegPre.famε l)))), (∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ s : Finset D.X, s₀ ⊆ s → ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = 0) → ∀ p j, (d p).f j = 0) := by
  classical
  intro V _ _ _ hV D A G _ _ U k l d H p j
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : Smooth (D.P.A ⊗ D.P.A).hom := inferInstanceAs (Smooth (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom))
  have : GeometricallyConnected (D.P.A ⊗ D.P.A).hom := by
    change GeometricallyConnected (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom)
    exact GeometricallyConnected.comp _ _
  refine sec_eq_zero_of_thickenings_of_section V (IsLocalRing.maximalIdeal V)
    (IsLocalRing.maximalIdeal_le_jacobson _) (D.P.A ⊗ D.P.A) (lift η[D.P.A] η[D.P.A]) _
    (DVR.linComb_isLB D.P.L D.P.isLB _ _) (d p) (fun e j => app_sec_eq_zero_of_sval D.P.isLB (d p) _ ?_ j) j
  obtain ⟨s₀, hs⟩ := H e
  exact level (U.gt e) k l d (insert p.1 (insert p.2 s₀))
    (hs _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))) p.1 (Finset.mem_insert_self _ _) p.2
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) _ _
    ⟨pullback.snd _ _, pullback.condition.symm⟩

end GlobalTheory.WeightTwo
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem dim_eq_add_finrank_of_kernel {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    [IsMonHom i] [Flat q.left] [Surjective q.left] [IsAffineHom q.left] (hk : IsPullback i (toUnit _) q (η[B]))
    {g g' : ℕ} (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := (H1.torus_dim S X).smooth
  have : Smooth q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem PreU.dim_eq : (AllPre fun {_} _ _ _ {D} {A} {_} _ _ _ => A.g = D.P.g + D.rank) := by
  intro V _ _ _ _ D A G _ _ U
  have hs : Smooth G.hom := U.semi.smooth
  have : GeometricallyConnected G.hom := U.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have bc : ∀ {S' : Scheme.{0}} {X : Over (Spec (CommRingCat.of V))} {m : ℕ} (f : S' ⟶ Spec (CommRingCat.of V)),
      SmoothOfRelativeDimension m X.hom → SmoothOfRelativeDimension m ((Over.pullback f).obj X).hom :=
    fun f h => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h
  have h₁ : n = A.g := by
    have a := A.smoothDim
    have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
      have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
      rw [← Over.w U.gen.hom]; infer_instance
    let f := jK V
    letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
    letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj (F := Over.pullback f)
    exact (H1.dim_unique _ (bc _ hn) b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  let c := U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  exact h₁.symm.trans (dim_eq_add_finrank_of_kernel (Classical.arbitrary _) c.q c.i c.isKernel (bc _ hn)
    (bc _ D.P.smoothDim))

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem nonempty_tq_pullback_comp {T S S' : Scheme.{0}} (r : T ⟶ S') (f : S' ⟶ S) {g : T ⟶ S} (h : g = r ≫ f)
    (G : Over S) [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ ((Over.pullback f).obj G) X) :
    Nonempty (TQ ((Over.pullback g).obj G) X) := by
  subst h
  obtain ⟨Q', -⟩ := exists_tq_baseChange _ _ _ X _ _ _
    ((isGrpPullback_of_iso (pullCompIso r f G)).comp (isGrpPullback_pullback _ r)) Q
  exact ⟨Q'⟩

theorem thick_zero_factor (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ r, thick V (IsLocalRing.maximalIdeal V) 0 = r ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (show IsLocalRing.maximalIdeal V ≤ IsLocalRing.maximalIdeal V ^ (0 + 1) by simp))), ?_⟩
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion : (∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : ℕ) (σ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => g.pG.left) (fun _ => (k : ℤ)))), ∃! f : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)), ∃ s : Finset D.X, (∀ α ∉ s, ∀ j, (f α).f j = 0) ∧ ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J → sval σ (𝟙 (thickObj R I e G).left) z J = ∑ α ∈ s, sval (f α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val) := by
  first | exact @GlobalTheory.existsUnique_level_expansion | exact GlobalTheory.existsUnique_level_expansion | (intros; apply GlobalTheory.existsUnique_level_expansion <;> assumption)
end
