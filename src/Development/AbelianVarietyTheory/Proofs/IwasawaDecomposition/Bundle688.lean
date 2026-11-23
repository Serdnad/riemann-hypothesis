module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle151
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SqCompare


open GlobalTheory.CoordCompare GlobalTheory.PrimNorm GlobalTheory.MulPull in
theorem sq_law {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hT : ∃ t : LB.Gen (Theta A M), t.IsGen) {Y : Over S} (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A)
    (v : LB.Gen (LB.LinComb M (diffφ y a b) ![2, -2, 2, -2])) (hv : v.IsGen) :
    ∃ v' : LB.Gen (LB.LinComb M (diffφ y (a * a) (b * b)) ![1, -1, 1, -1]), v'.IsGen := by
  have hc := fun p q s : Y ⟶ A => diff₃_ptCls (T := Y) hM hT p q s
  have h := (hasGen_iff hM _ _).1 ⟨v, hv⟩
  rw [Fin.prod_univ_four] at h
  refine (hasGen_iff hM _ _).2 ?_
  rw [Fin.prod_univ_four]
  set m := ptCls M Y with hm
  set α := toUnit Y ≫ a
  set β := toUnit Y ≫ b
  have cα : toUnit Y ≫ (a * a) = α * α := MonObj.comp_mul _ _ _
  have cβ : toUnit Y ≫ (b * b) = β * β := MonObj.comp_mul _ _ _
  change m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ) = 1 at h
  change m (y * (toUnit Y ≫ (b * b))) ^ (1 : ℤ) * m (y * (toUnit Y ≫ (a * a))) ^ (-1 : ℤ) *
    m (toUnit Y ≫ (a * a)) ^ (1 : ℤ) * m (toUnit Y ≫ (b * b)) ^ (-1 : ℤ) = 1
  rw [cα, cβ]
  have kα := diff₂_mul_right hc y α α
  have kβ := diff₂_mul_right hc y β β
  calc _ = (diff₂ m y (β * β) * (diff₂ m y β * diff₂ m y β)⁻¹) *
        (diff₂ m y (α * α) * (diff₂ m y α * diff₂ m y α)⁻¹)⁻¹ *
        (m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ)) := by
        apply Additive.ofMul.injective
        simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
    _ = 1 := by rw [← kα, ← kβ, h, mul_inv_cancel, mul_inv_cancel, inv_one, _root_.mul_one, _root_.mul_one]


open GlobalTheory.CoordCompare TorusCoord in
theorem sq_desc {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G)
    (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] [Mono Φ.left] (hp : g'.pG ≫ Φ = g.pG)
    (w : LB.Iso (LB.LinComb D'.P.L (K := Fin 1) (fun _ => 𝟙 D'.P.A.left) (fun _ => 2))
      ((LB.LinComb D.P.L (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => 2)).pull Φ.left)) (hw : w.IsGen)
    (χ : D.X) (χ' : D'.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ)) ![2, -2, 2, -2]), v.IsGen := by
  obtain ⟨t, ht, W, hW⟩ := GlobalTheory.T.exists_square_generator_through_squareIso D.P.isLB D'.P.isLB w hw (D'.Oφ g'.pG χ') Oinvε (g'.t χ') (g'.t_gen χ')
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) (ε' := ![2, -2, 2, -2])
    (fun U _ h => by
      have e2 := prod_diff (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) ((Over.map (thick R I e)).map g.q) h
      have e3 : ∏ k, h (g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^ (![2, -2, 2, -2] : Fin 4 → ℤ) k =
          (∏ k, h (((Over.map (thick R I e)).map g.q).left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^
            (![1, -1, 1, -1] : Fin 4 → ℤ) k) ^ (2 : ℤ) := by
        simp only [Fin.prod_univ_four, mul_zpow, ← zpow_mul]
        rfl
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (e3.trans (congrArg (· ^ (2 : ℤ)) e2)).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, Oφ_comp_hom, hp, Fintype.prod_sum_type]
      simp only [Fin.prod_univ_four]
      let T := (Over.map (thick R I e)).obj (thickObj R I e G)
      show h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left ^ (2 * (-1 : ℤ)) * h (toUnit T ≫ D'.c χ' ≫ Φ).left ^ (2 * (1 : ℤ)) *
          h g.pG.left ^ (2 * (1 : ℤ)) * h (1 : T ⟶ D.P.A).left ^ (2 * (-1 : ℤ)) *
        ((h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ)) *
         (h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ))) =
        (h (g.pG * (toUnit T ≫ D.c χ)).left * (h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left)⁻¹ *
          h (toUnit T ≫ D'.c χ' ≫ Φ).left * (h (toUnit T ≫ D.c χ).left)⁻¹) ^ (2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t χ)) (LB.invGen D.P.L _ _ (g.t χ))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))
      (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))))
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
    obtain ⟨h₁, h₂⟩ := ratio_invariant g g' Φ hp χ χ' hker r r' z J J' hJ hJ' h
    have hWeq : (fun k => r ≫ D'.Oφ g'.pG χ' k) = (fun k => r' ≫ D'.Oφ g'.pG χ' k) :=
      funext (Oφ_congr χ' g'.pG r r' h₁)
    rw [hu' Z r z J hJ, hu' Z r' z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
      hW Z r z J J' hJ hJ', hW Z r' z J J' hJ hJ', hWeq]
    calc _ = W Z z (fun k => r' ≫ D'.Oφ g'.pG χ' k) J J' *
          (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) ^ 2 := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel
      _ = _ := by
          rw [h₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel)
  exact ⟨v, hv⟩

end GlobalTheory.SqCompare


open GlobalTheory.CoordCompare in
theorem GlobalTheory.SqCompare.c_two_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' hL Φ w hw hΦ hpG xe hval x
  obtain ⟨hN, -, hC, -⟩ := hR
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hpG e)
  have hmono : Mono Φ.hom.left := inferInstance
  set a := D'.toPre.c x ≫ Φ.hom
  set b := D.toPre.c (xe x)
  have desc : ∀ n, ∃ v : LB.Gen (LB.LinComb D.toPre.P.L
      (diffφ (D.toPre.prBe (maximalIdeal R) n) (a * a) (b * b)) ![1, -1, 1, -1]), v.IsGen := fun n => by
    obtain ⟨v, hv⟩ := GlobalTheory.SqCompare.sq_desc (U.gt n) (U'.gt n) Φ.hom (hp' n) w hw (xe x) x
      (fun Z r z J J' hJ hJ' h h' => hval n Z r z J J' hJ hJ' h h' x)
    exact GlobalTheory.SqCompare.sq_law D.toPre.P.isLB ⟨D.toPre.cub.t, D.toPre.cub.isGen⟩ _ _ _ v hv
  have hab : a * a = b * b := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
      D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ (a * a)) (toUnit _ ≫ (b * b)) fun n => by
        obtain ⟨v, hv⟩ := desc n
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
            pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.toPre.P.A] ≫ ·) h
  have e1 : D'.toPre.c (2 • x) ≫ Φ.hom = a * a := by
    rw [two_nsmul, D'.toPre.c_add, padd, ← Hom.mul_def, MonObj.mul_comp]
  have e2 : D.toPre.c (xe (2 • x)) = b * b := by
    rw [map_nsmul, two_nsmul, D.toPre.c_add, padd, ← Hom.mul_def]
  rw [e1, e2, hab]
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnifSqCompare

theorem mem_sq {X : Scheme.{0}} {L : LB X} {x : X} {j : L.ι} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ↔ x ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

end UnifSqCompare



open UnifCompare UnifSqCompare in
theorem unif_sq_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' hL
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hGF : GlobalFnsSt := allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := allSixLaws.1.secBaseChange
  have hA : AmpleSt := allSixLaws.1.ample
  obtain ⟨wL₀, hwL₀⟩ := hL
  obtain ⟨wL, hwL, hrig⟩ := GlobalTheory.T.exists_rescale_rigidified_square_iso _ G U.LG U'.LG wL₀ hwL₀
  choose β hβm hβ using unifPre_abelianPart_iso R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre
  choose v hvg hv using fun e =>
    GlobalTheory.T.polarization_squares_agree_at_each_thickening hGF R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre wL hwL hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R (maximalIdeal R) e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q U'.toUnifPre, Category.assoc, hβl,
      trans_comp_q U.toUnifPre, ← Category.assoc, hβl]
  have hR' := hR
  obtain ⟨hN, -, -, hC⟩ := hR'
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square hS hA R (maximalIdeal R) D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R (maximalIdeal R) e D'.toPre.P.A).left,
        y ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') →
        thickMap R (maximalIdeal R) e D'.toPre.P.A y ∈
          ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β (e + 1)).hom.left ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) (e + 1) D'.toPre.P.A).left).U (fun _ => fun _ => j') := by
      intro y hy
      have k : thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫
          (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j)) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j')) (trans_comp_proj e _)).mpr (mem_pull.1 hy.2))⟩
    have hz : r z ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') :=
      ⟨mem_pull.2 (mem_sq.2 hj), mem_pull.2 (mem_sq.2 hj')⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_sq.1 (mem_pull.1 hx.1))
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_sq.1 (mem_pull.1 hx.2)
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R (maximalIdeal R) e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U'.toUnifPre e x j' jL' hM' hL', gw_trans U.toUnifPre e x j jL hM hL, trans_comp_q U'.toUnifPre,
      trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have hpG : ∀ e, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot (maximalIdeal R)
  have hΦ : IsMonHom Φ.hom := by
    refine AbelianPartIso.isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R (maximalIdeal R) e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (hpG e)))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨Φ, w, wL, hw, hwL, hΦ, fun e => ⟨hpG e, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
    ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
  rw [Category.assoc] at h
  exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end
