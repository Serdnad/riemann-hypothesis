module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle028
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem GenFib.nonempty_of_baseChange :
    Out.PolBaseChangeSt → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))), Nonempty (GenFib P) := by
  intro hB K _ _ P
  obtain ⟨P₀, φ, h⟩ := exists_isPolFibre hB (algebraMap (𝓞 K) K) P
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis P₀.A P₀.smoothDim
  exact ⟨⟨P₀, φ, h, v, hv⟩⟩

end GlobalTheory.CM
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CM

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

variable {S : Scheme.{0}} {A B X Y : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj Y] [IsCommMonObj Y]

theorem exists_gen_lam_two (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a : X ⟶ A) (g : Y ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ X)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ Y) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ Y)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫ (psum A ![fst X Y ≫ a, snd X Y ≫ g] I).left =
          (psum A ![fst T Y ≫ y ≫ a, (snd T Y ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T Y ≫ y) (snd T Y ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst X Y ≫ a = fst T Y ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd X Y ≫ g = (snd T Y ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T Y).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T Y ≫ y ≫ a).left)⁻¹ * h (fst T Y ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T Y) (snd T Y ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T Y) (snd T Y ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ Y, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

theorem weil_value_eq_of_lamEq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hY : IsAbelianScheme Y) {N : RigLB A} {L : RigLB B} (cN : CubicalStr A N) (cL : CubicalStr B L)
    (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) [IsMonHom f₂] [IsMonHom g₂]
    (H : LamEq N.L f₁ f₂ L.L g₁ g₂) {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ X)
    (z : T ⟶ Y) (hf : (y ≫ f₁) ^ n = 1) (hg : (y ≫ g₁) ^ n = 1) (hz : z ^ n = 1) (e e' : Γ(T.left, ⊤)ˣ)
    (he : WeilIs B L.L n (y ≫ g₁) (z ≫ g₂) e) (he' : WeilIs A N.L n (y ≫ f₁) (z ≫ f₂) e') : e = e' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨t, ht, v⟩ := exists_gen_lam_two hG hB cL p₀ hT g₁ g₂ n y hg
  obtain ⟨t', ht', v'⟩ := exists_gen_lam_two hG hA cN p₀ hT f₁ f₂ n y hf
  choose J hJ using fun χ : T.left ⟶ B.left => exists_chart L.isLB (χ p)
  choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := PairingOfLam.val_ratio L.isLB N.isLB H _ t ht t' ht' (fst T Y).left (WeilCube.surj_fst hG hY T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ Y)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ'
  rw [v z e hz he p J hJ, v' z e' hz he' p J' hJ'] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem weilEq_of_lamEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) := by
  intro hl k _ _ _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ H n x y c _ hx hy
  haveI := A.isAb.comm
  haveI := B.isAb.comm
  haveI := Y.isAb.comm
  obtain ⟨rA, hrA⟩ := A.rigid
  obtain ⟨rB, hrB⟩ := B.rigid
  obtain ⟨⟨cA⟩, -⟩ := hl.cube _ A ⟨A.L, rA, A.isLB, hrA⟩ rfl
  obtain ⟨⟨cB⟩, -⟩ := hl.cube _ B ⟨B.L, rB, B.isLB, hrB⟩ rfl
  let T : Over (Sp k) := Over.mk (𝟙 _)
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have h₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have h₃ : (x ≫ g₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₄ : (y ≫ g₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have key := weil_value_eq_of_lamEq hl.globalFns A.isAb B.isAb Y.isAb cA cB f₁ f₂ g₁ g₂ H p₀ hT n x y h₁ h₃ hy
  constructor
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ B n T).1 _ _ h₃ h₄
    exact key e _ he h ▸ he
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ A n T).1 _ _ h₁ h₂
    exact (key _ e h he).symm ▸ he

end GlobalTheory.CM
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorKernel

open GlobalTheory.CechPic

section Local

variable {Y Y' B : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ Y), (∀ z, π (f z) ∈ V) → pull f c = 0

theorem LocZero.add {π : Y ⟶ B} {c d : Pic Y} (hc : LocZero π c) (hd : LocZero π d) : LocZero π (c + d) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  obtain ⟨V', hV', H'⟩ := hd p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, fun Z f hf => ?_⟩
  rw [map_add (f := _), H Z f fun z => (hf z).1, H' Z f fun z => (hf z).2, add_zero]

theorem LocZero.pull {π : Y ⟶ B} {c : Pic Y} (hc : LocZero π c) (k : Y' ⟶ Y) :
    LocZero (k ≫ π) (pull k c) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  exact ⟨V, hV, fun Z f hf => (pull_comp f k c).symm.trans (H Z (f ≫ k) hf)⟩

theorem locZero_base (π : Y ⟶ B) (d : Pic B) : LocZero π (pull π d) := by
  obtain ⟨D, hD, rfl⟩ := cls_surj d
  intro p
  obtain ⟨i, hi⟩ := exists_chart hD p
  refine ⟨D.U i, hi, fun Z f hf => (pull_comp f π _).symm.trans ?_⟩
  exact (cls_eq_zero_iff (pull_isLB hD (f ≫ π))).2
    (BoxKernel.gen_of_chart (pull_isLB hD _) (fun _ => i) fun z => mem_pull.2 (hf z))

theorem locZero_iff (π : Y ⟶ B) {M : LB Y} (hM : M.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (M.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls M hM) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (pull_isLB hM _), cls_pull hM]
  refine ⟨fun H Z f hf => ?_, fun H => H _ _ fun z => z.2⟩
  have hr : Set.range f ⊆ Set.range (π ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf z
  rw [← IsOpenImmersion.lift_fac (π ⁻¹ᵁ V).ι f hr, pull_comp, H, map_zero]

end Local

section Group

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem translDiff_iff {L : LB A.left} (hL : L.IsLB) (x : T ⟶ A) :
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [locZero_iff _ hD]
  have e : lam (cls L hL) (fst T A ≫ x) (snd T A) = cls _ hD +
      pull (fst T A).left (pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL)) := by
    have e₁ : cls _ hD = pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
      refine (cls_linComb hL _ _ hD).trans ?_
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, lam]
    abel
  refine ⟨fun H => e ▸ H.add (locZero_base _ _), fun H => ?_⟩
  have := H.add (locZero_base _ (-(pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL))))
  rwa [e, map_neg, add_neg_cancel_right] at this

end Group

end GlobalTheory.HermTensorKernel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.TensorBundle

open GlobalTheory.PrimNorm GlobalTheory.MulPull GlobalTheory.Serre

section Algebra

variable {O V W U I : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
  [AddCommGroup U] [Fintype I]

def gramForm (β : V →+ V →+ U) (p : I → W →ₗ[O] V) (g : I → I → O) (x y : W) : U :=
  ∑ k : I × I, β (g k.1 k.2 • p k.1 x) (p k.2 y)

variable {β : V →+ V →+ U} {p : I → W →ₗ[O] V} {g : I → I → O} {br : O ≃+* O}

theorem gramForm_add_left (x y z : W) : gramForm β p g (x + y) z = gramForm β p g x z + gramForm β p g y z := by
  simp only [gramForm, map_add (f := _), smul_add, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem gramForm_add_right (x y z : W) : gramForm β p g x (y + z) = gramForm β p g x y + gramForm β p g x z := by
  simp only [gramForm, map_add (f := _), Finset.sum_add_distrib]

theorem gramForm_zero (y : W) : gramForm β p g 0 y = 0 := by
  simp [gramForm]

theorem gramForm_adj (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (c : O) (x y : W) :
    gramForm β p g (c • x) y = gramForm β p g x (br c • y) := by
  simp only [gramForm, map_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_comm, ha]

theorem gramForm_comm (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) (x y : W) : gramForm β p g x y = gramForm β p g y x :=
  Fintype.sum_equiv (Equiv.prodComm I I) _ _ fun k => by
    rw [ha, hs, ← hg]
    rfl

theorem gramForm_polar (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) {w : O} (hw : w + br w = 1) (x y : W) :
    gramForm β p g (x + y) (w • (x + y)) + -gramForm β p g x (w • x) + -gramForm β p g y (w • y) +
      gramForm β p g 0 (w • 0) = gramForm β p g x y := by
  have e : gramForm β p g x y = gramForm β p g x (w • y) + gramForm β p g y (w • x) := by
    rw [gramForm_comm hs ha hg y, gramForm_adj ha, ← gramForm_add_right, ← add_smul, hw, one_smul]
  rw [e, gramForm_zero, smul_add, gramForm_add_left, gramForm_add_right, gramForm_add_right]
  abel

theorem gramForm_pure (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (hb : ∀ c, br (br c) = c)
    {x y : W} {u v : V} {s s' : I → O} (hx : ∀ i, p i x = s i • u) (hy : ∀ i, p i y = s' i • v) :
    gramForm β p g x y = β ((∑ k : I × I, br (s' k.2) * (g k.1 k.2 * s k.1)) • u) v := by

  rw [Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hx, hy, mul_smul (br _), ha (br _), hb, mul_smul]

theorem hermitian_expand {M : Type} [AddCommGroup M] [Module O M] (h : M →ₗ[O] M →+ O)
    (hh : ∀ x y, h y x = br (h x y)) (e : I → M) (s s' : I → O) :
    ∑ k : I × I, br (s' k.2) * (h (e k.1) (e k.2) * s k.1) = h (∑ i, s i • e i) (∑ i, s' i • e i) := by
  have sm : ∀ c x y, h x (c • y) = br c * h x y := fun c x y => by
    rw [hh (c • y) x, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, map_mul, ← hh]

  rw [map_sum h, AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sm, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm (s i)]

end Algebra

section Geometry

variable {S : Scheme.{0}} {O : Type} [CommRing O] {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A]
  [IsCommMonObj A] {L : LB G.left}

def lamForm (a : OAct O G) (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta G L), t.IsGen) (T : Over S) :
    Pts a T →+ Pts a T →+ Additive (PullClass L T.left) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (diff₂ (ptCls L T) x.hom y.hom))
    fun y z => congrArg Additive.ofMul (diff₂_mul_right (diff₃_ptCls hL hT) x.hom y.hom z.hom))
    fun x y => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left (diff₃_ptCls hL hT) x.hom y.hom z.hom)

variable {I : Type} [Fintype I]

def prodMap (f f' : I → (A ⟶ G)) (k : I × ULift.{0} (Finset (Fin 2))) : A.left ⟶ G.left :=
  (psum G ![f k.1, f' k.1] k.2.down).left

def prodExp (k : I × ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - k.2.down.card)

def prodCls (L : LB G.left) (f f' : I → (A ⟶ G)) {Y : Scheme.{0}} (ψ : Y ⟶ A.left) : PullClass L Y :=
  ∏ k, cls L (ψ ≫ prodMap f f' k) ^ prodExp k

omit [GrpObj A] [IsCommMonObj A] in
theorem prodCls_left (f f' : I → (A ⟶ G)) {T : Over S} (x : T ⟶ A) :
    prodCls L f f' x.left = ∏ k, diff₂ (ptCls L T) (x ≫ f k) (x ≫ f' k) := by
  rw [prodCls, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun k _ => prod_square x (f k) (f' k) (cls L)

end Geometry

theorem exists_tensor_bundle : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (br : O ≃+* O) (w : O) (L : LB G.left) (h : M →ₗ[O] M →+ O), Module.Finite O M → Module.Projective O M → w + br w = 1 → (∀ c, br (br c) = c) → (∀ x y, h y x = br (h x y)) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (br c))) →
  ∃ N : LB A.left, N.IsLB ∧ Out.Rigidified A N ∧ (∃ t : LB.Gen (Theta A N), t.IsGen) ∧ ∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G) := by
  intro S O _ G A _ _ _ _ a b M _ _ t br w L h _ _ hw hb hh hL hT ha
  obtain ⟨P⟩ := Summand.nonempty O M
  let c : Fin P.n → M →ₗ[O] O := fun i => LinearMap.proj i ∘ₗ P.incl
  let e : Fin P.n → M := fun i => P.proj (Pi.single i 1)
  have he : ∀ m, ∑ i, c i m • e i = m := fun m => by
    have : ∑ i, P.incl m i • (Pi.single i 1 : Fin P.n → O) = P.incl m := by
      ext j
      simp [Pi.single_apply]

    simp only [e, ← map_smul, ← map_sum]
    exact (congrArg P.proj this).trans congr($(P.proj_incl) m)
  let π : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (c i)
  have hπ : ∀ i, IsLinearHom b a (π i) := fun i => t.isLinearHom_mapLeft _ _
  let g : Fin P.n → Fin P.n → O := fun i j => h (e i) (e j)
  let f : Fin P.n × Fin P.n → (A ⟶ G) := fun k => π k.1 ≫ a.act (g k.1 k.2)
  let f' : Fin P.n × Fin P.n → (A ⟶ G) := fun k => b.act w ≫ π k.2
  let B : ∀ T : Over S, Pts b T → Pts b T → Additive (PullClass L T.left) := fun T =>
    gramForm (lamForm a hL hT T) (fun i => Pts.post (hπ i) T) g
  have hs : ∀ (T : Over S) x y, lamForm a hL hT T x y = lamForm a hL hT T y x := fun T x y =>
    congrArg Additive.ofMul (diff₂_comm _ _)
  have hadj : ∀ (T : Over S) (r : O) x y, lamForm a hL hT T (r • x) y = lamForm a hL hT T x (br r • y) :=
    fun T r x y => by
      have := ha r
      unfold LamEq at this
      rw [Category.comp_id, Category.comp_id] at this
      exact congrArg Additive.ofMul (diff₂_ptCls_adj hL this x.hom y.hom)
  have hq : ∀ (T : Over S) (x : T ⟶ A), prodCls L f f' x.left = (B T (Pts.mk b x) (w • Pts.mk b x)).toMul :=
    fun T x => by
      rw [prodCls_left]
      refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (toMul_sum _ _).symm
      simp only [f, f', ← Category.assoc]
      rfl
  have h₂ : ∀ (T : Over S) (x y : T ⟶ A), diff₂ (fun q : T ⟶ A => prodCls L f f' q.left) x y =
      (B T (Pts.mk b x) (Pts.mk b y)).toMul := fun T x y => by
    simp only [diff₂, hq]
    exact congrArg Additive.toMul (gramForm_polar (hs T) (hadj T) (fun i j => hh _ _) hw (Pts.mk b x) (Pts.mk b y))
  refine ⟨LB.LinComb L (prodMap f f') prodExp, DVR.linComb_isLB _ hL _ _, ?_, ?_, fun m m' => ?_⟩
  · refine hasGen_nested (K' := PUnit) hL _ _ (fun _ => eSec A) (fun _ => 1) ?_
    rw [Fintype.prod_unique, zpow_one]
    refine (hq _ η[A]).trans ?_
    have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by simp [Hom.one_def]
    rw [e]
    exact congrArg Additive.toMul (gramForm_zero _)
  · refine hasGen_nested hL _ _ (thφ A (x3 A)) thε ((GlobalTheory.AbLaw.Cube.prod_theta (prodCls L f f')).trans
      ((prod_cub _ _ _ (prodCls L f f')).trans ?_))
    have e := diff₂_mul_left_eq (m := fun q : G3 A ⟶ A => prodCls L f f' q.left) (x3 A 0) (x3 A 1) (x3 A 2)
    rw [h₂, h₂, h₂, Pts.mk_mul] at e
    exact mul_eq_right.1 (e.symm.trans (congrArg Additive.toMul (gramForm_add_left _ _ _)))
  · refine lbIso_nested hL _ _ _ _ _ _ ((prod_square_id _ _ (prodCls L f f')).trans
      (Eq.trans ?_ (prod_square_id _ _ (cls L)).symm))
    have k : ∀ (u : G ⊗ G ⟶ G) (m : M) i,
        Pts.post (hπ i) _ (Pts.mk b (u ≫ t.tmul m)) = c i m • Pts.mk a u := fun u m i => Pts.ext (by
      simp only [Pts.hom_post, Pts.hom_mk, Pts.hom_smul, π, Category.assoc, IsTensor.tmul_mapLeft,
        IsTensor.self_tmul])
    rw [h₂, Category.comp_id]
    refine congrArg Additive.toMul ((gramForm_pure (hadj _) hb (k _ m) (k _ m')).trans ?_)
    rw [(hermitian_expand h hh e (fun i => c i m) fun i => c i m' :
      ∑ k : Fin P.n × Fin P.n, br (c k.2 m') * (g k.1 k.2 * c k.1 m) = _), he, he]
    rfl

end GlobalTheory.TensorBundle
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem isLieNormSq_iff_eq_pi_div_covolume :
    ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (L : PeriodPair), P.g = 1 → IsTangent v → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → 0 < Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ ∀ r, IsLieNormSq P v s r ↔ r = Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  intro hU hB R _ P v s L hg hv hΛ
  have key : ∀ r, IsLieNormSq P v s r → 0 < r ∧ r = Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
    rintro r ⟨P', φ, v', u, Hm, χ, w, hP, hv', hA, hd, rfl⟩
    obtain ⟨hw, hL⟩ := hΛ P' φ v' u w hP hv' hd
    obtain ⟨Ef, hEf, hbij⟩ := (GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).2.2 Hm χ hA
    have hpos : 0 < (hermForm Hm w w).re := hA.2.1 w hw
    have e := hermForm_principal_dim_one P'.g u.Λ w L Hm Ef (hP.1.trans hg) hw hL hA.1 hpos hEf hbij 1 1
    refine ⟨mul_pos Real.pi_pos hpos, ?_⟩
    rw [one_smul, map_one, _root_.mul_one, one_div, ← Complex.ofReal_inv] at e
    rw [e, Complex.ofReal_re, div_eq_mul_inv]
  obtain ⟨r₀, h₀⟩ := exists_isLieNormSq hU hB P hv s
  obtain ⟨h1, h2⟩ := key r₀ h₀
  exact ⟨h2 ▸ h1, fun r => ⟨fun h => (key r h).2, fun h => (h.trans h2.symm) ▸ h₀⟩⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_polarisedAbelianScheme_power : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  first | exact @GlobalTheory.CM.exists_polAV_isPowGrp | exact GlobalTheory.CM.exists_polAV_isPowGrp | (intros; apply GlobalTheory.CM.exists_polAV_isPowGrp <;> assumption)
end
