module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle074
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

section Calc

variable {S : Scheme.{0}} {X Y A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj C] [IsCommMonObj C] {L : LB A.left} {M : LB B.left} {N : LB C.left}

theorem lamEq_symm' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq M g₁ g₂ L f₁ f₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).1

theorem lamEq_swap' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq L f₂ f₁ M g₂ g₁ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.1

theorem lamEq_trans' (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B}
    {g₂ : Y ⟶ B} {k₁ : X ⟶ C} {k₂ : Y ⟶ C} (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq M g₁ g₂ N k₁ k₂) :
    LamEq L f₁ f₂ N k₁ k₂ :=
  ((LamCalc.lamEq_calculus S X Y A B C L M N hL hM hN f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ k₁ k₂).2.1 h).2.2.1 h'

theorem lamEq_pre (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) {X' Y' : Over S} (a : X' ⟶ X) (b : Y' ⟶ Y) :
    LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂) :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.2.2.1 X' Y' a b

variable (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen)
include hL hM hT hT'

theorem lamEq_mul_left' {f₁ f₁' : X ⟶ A} {f₂ : Y ⟶ A} {g₁ g₁' : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq L f₁' f₂ M g₁' g₂) : LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁' f₂ f₂ g₁ g₁' g₂ g₂ g₁ g₂).2.2.1 hT hT' h).1 h'

theorem lamEq_prod_left {J : Type} (s : Finset J) (f : J → (X ⟶ A)) (g : J → (X ⟶ B)) (f₂ : Y ⟶ A) (g₂ : Y ⟶ B)
    (h0 : LamEq L (1 : X ⟶ A) f₂ M (1 : X ⟶ B) g₂) (h : ∀ i ∈ s, LamEq L (f i) f₂ M (g i) g₂) :
    LamEq L (s.prod f) f₂ M (s.prod g) g₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM (f i) (s.prod f) f₂ f₂ (g i) (s.prod g) g₂ g₂
      (g i) g₂).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).1
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lamEq_prod_right {J : Type} (s : Finset J) (f₁ : X ⟶ A) (g₁ : X ⟶ B) (f : J → (Y ⟶ A)) (g : J → (Y ⟶ B))
    (h0 : LamEq L f₁ (1 : Y ⟶ A) M g₁ (1 : Y ⟶ B)) (h : ∀ i ∈ s, LamEq L f₁ (f i) M g₁ (g i)) :
    LamEq L f₁ (s.prod f) M g₁ (s.prod g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ (f i) (s.prod f) g₁ g₁ (g i) (s.prod g)
      g₁ (g i)).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).2
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Calc

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G)

theorem act_zero' : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have := congrArg (fun u => (act.act 0)⁻¹ * u) h
  simpa using this.symm

theorem act_sum' {J : Type} (s : Finset J) (c : J → O) : act.act (s.sum c) = s.prod fun i : J => act.act (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using act_zero' act
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, act.add, ih]

end Act

theorem exists_thetaGen' (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  exact ⟨c.t, c.isGen⟩

theorem weilEq_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG m hm z f hf hfm x r hr
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have hβ : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have lA : (X.A true).t.PP.L.IsLB := (X.A true).t.PP.isLB
  have lB : X.B.t.PP.L.IsLB := X.B.t.PP.isLB
  have tA := exists_thetaGen' hL (X.A true).pol
  have tB := exists_thetaGen' hL X.B.pol
  haveI : IsMonHom f := hf.1
  haveI hφ : ∀ a, IsMonHom (phiP X a) := fun a => (X.lin (Sum.inl a)).1
  haveI hact : ∀ s, IsMonHom ((X.A true).t.act.act s) := (X.A true).t.act.hom
  have toLam : ∀ (f₁ f₂ : (X.A true).t.G ⟶ X.B.t.G) (g₁ g₂ : (X.A true).t.G ⟶ (X.A true).t.G), IsMonHom f₁ →
      IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
      WeilEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
      LamEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ := fun f₁ f₂ g₁ g₂ h₁ h₂ h₃ h₄ h =>
    (PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol (X.A true).pol f₁ f₂ g₁ g₂
      h₁ h₂ h₃ h₄ ℂ _).2 inferInstance hβ h

  have E1 : ∀ a b, LamEq X.B.t.PP.L ((X.A true).t.act.act (z a) ≫ phiP X a) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro a b
    have := lamEq_pre lB lA (toLam _ _ _ _ (hφ a) (hφ b) (hact _) inferInstance (hG.1 a b))
      ((X.A true).t.act.act (z a)) ((X.A true).t.act.act (x b))
    rwa [← (X.A true).t.act.mul, Category.comp_id] at this

  have S1 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (∑ a, z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro b
    have h0 : LamEq X.B.t.PP.L (1 : (X.A true).t.G ⟶ X.B.t.G) ((X.A true).t.act.act (x b) ≫ phiP X b)
        (X.A true).t.PP.L (1 : (X.A true).t.G ⟶ (X.A true).t.G) ((X.A true).t.act.act (x b)) := by
      have := lamEq_pre lB lA (E1 b b) (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
    have := lamEq_prod_left lB lA tB tA Finset.univ (fun a => (X.A true).t.act.act (z a) ≫ phiP X a)
      (fun a => (X.A true).t.act.act (z a * gP a b)) _ _ h0 (fun a _ => E1 a b)
    rwa [← hfm, ← act_sum'] at this

  have M1 : ∀ t y : 𝓞 E, LamEq (X.A true).t.PP.L ((X.A true).t.act.act t) ((X.A true).t.act.act y)
      (X.A true).t.PP.L ((X.A true).t.act.act (t * H.bar y)) (𝟙 _) := by
    intro t y
    have h2 := lamEq_pre lA lA (lamEq_swap' lA lA (LamF.lamEq_adj (X.A true).t y)) ((X.A true).t.act.act t) (𝟙 _)
    rwa [Category.comp_id, Category.id_comp, Category.id_comp, ← (X.A true).t.act.mul] at h2
  have F2 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b) (X.A true).t.PP.L (𝟙 _)
      ((X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) := fun b =>
    lamEq_trans' lB lA lA (lamEq_trans' lB lA lA (S1 b) (M1 _ _)) (LamF.lamEq_adj (X.A true).t _)

  obtain ⟨r', hr'⟩ := GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP f
    (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) hf (isLinearHom_prod X x)
  haveI hψ : IsMonHom (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) := (isLinearHom_prod X x).1
  have R := toLam _ _ _ _ inferInstance hψ (hact r') inferInstance hr'
  have Rm : ∀ n : ℕ, LamEq X.B.t.PP.L (f ^ n) (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act ((n : 𝓞 E) * r')) (𝟙 _) := by
    intro n
    induction n with
    | zero =>
      have := lamEq_pre lB lA R (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rw [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
      rwa [pow_zero, Nat.cast_zero, zero_mul, act_zero']
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, _root_.one_mul, (X.A true).t.act.add]
      exact lamEq_mul_left' lB lA tB tA ih R
  have RmA := lamEq_trans' lB lA lA (Rm m) (LamF.lamEq_adj (X.A true).t ((m : 𝓞 E) * r'))
  have base2 : LamEq X.B.t.PP.L (f ^ m) (1 : (X.A true).t.G ⟶ X.B.t.G) (X.A true).t.PP.L (𝟙 _)
      (1 : (X.A true).t.G ⟶ (X.A true).t.G) := by
    have := lamEq_pre lB lA RmA (𝟙 _) (1 : (X.A true).t.G ⟶ (X.A true).t.G)
    rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
  have S2 := lamEq_prod_right lB lA tB tA Finset.univ (f ^ m) (𝟙 _)
    (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) base2 (fun b _ => F2 b)
  have hsum : (∑ b, H.bar ((∑ a, z a * gP a b) * H.bar (x b))) = H.bar ((m : 𝓞 E) * r) := by

    rw [hr, ← map_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [← act_sum', hsum] at S2

  have U := lamEq_swap' lA lA (lamEq_trans' lA lB lA (lamEq_symm' lB lA S2) RmA)
  have e₁ := PairingInj.eq_of_lamEq hL _ (X.A true).pol _ _ _ U
  have hg : 1 ≤ (X.A true).pol.g := NumInh.dim_pos_of_hasType X.split X.ρ_sq (X.A true) X.typeP
  have e₂ := H.bar.injective (LamF.Faithful.act_injective hL E K (X.A true).pol (X.A true).t.act hg e₁)
  have e₃ : r = r' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne' : (m : 𝓞 E) ≠ 0) e₂
  rw [e₃]
  exact hr'

end GlobalTheory.FlatCM.HomLat

end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.RosatiCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem weilEq_prod_snd {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs' : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ s, G i) :=
      Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
        (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hG i
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf (hG a).isMonHom hs'.isMonHom _ _ (h a) ih

theorem exists_mul_eq_gram_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p q X gP gQ hG n x f hn hf hfx a
  have hφ : ∀ b, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X b) := fun b => X.lin (Sum.inl b)
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    (phiP X a) f (hφ a) hf
  have h1 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun _ : ℕ => f) (fun _ => hf) (fun _ => r) (fun _ => hr)
    (Finset.nonempty_range_iff.2 hn.ne')
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hfx] at h1
  have h2 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (hφ b)) (fun b => gP a b * H.bar (x b))
    (fun b => GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hφ a).isMonHom (hφ b).isMonHom _ (x b) (hG.1 a b))
    (T := Finset.univ) ⟨a, Finset.mem_univ a⟩
  exact ⟨r, GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)⟩

end GlobalTheory.FlatCM.RosatiCoord
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem exists_isGram_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, h⟩ := GlobalTheory.FlatCM.GramExists.exists_isGram E H K ρ σ₁ p 0 X
  exact ⟨gP, gQ, h, (GlobalTheory.GramAt.gram_det X h).1⟩

end GlobalTheory.FlatCM.HomLat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel


theorem _root_.GlobalTheory.T.goodSplitPlace_translation_acts_through_weil : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ν α : (Fv D.host.F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      ∀ g : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁), ∃ k : GA D (G.V (.grid i j)),
        ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r → ∃ φ₁ ∈ GlobalTheory.WeilM.SB _,
          om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ r) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ₁ r ∧ ι φ₁ = omB ν α g 1 (ι φ) := by
  first | exact @GlobalTheory.LocWeilAct.act_omB | exact GlobalTheory.LocWeilAct.act_omB | (intros; apply GlobalTheory.LocWeilAct.act_omB <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_localWeilOperators_supportedAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  first | exact @GlobalTheory.LocalWeilOps.local_ops | exact GlobalTheory.LocalWeilOps.local_ops | (intros; apply GlobalTheory.LocalWeilOps.local_ops <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_localWeilHom_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  first | exact @GlobalTheory.LocalWeilHom.local_weil_hom | exact GlobalTheory.LocalWeilHom.local_weil_hom | (intros; apply GlobalTheory.LocalWeilHom.local_weil_hom <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_doubledEigenfunctions_line_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))) := by
  first | exact @GlobalTheory.VDblLine.vdbl_line | exact GlobalTheory.VDblLine.vdbl_line | (intros; apply GlobalTheory.VDblLine.vdbl_line <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_doubledVacuumCondition_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  first | exact @GlobalTheory.DblVacUniq.dbl_vac_unique | exact GlobalTheory.DblVacUniq.dbl_vac_unique | (intros; apply GlobalTheory.DblVacUniq.dbl_vac_unique <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.lowering_part_kills_fock_product_minors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus (R.MW i σ) τ, ∀ h, RderC R.θ (Wc D i) τ Z (fun g => thetaKO om h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f (deltaAtEmb D i σ))) = 0 := by
  first | exact @GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero | exact GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero | (intros; apply GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_unitaryQuotientVolume_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∃ (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ volQ WW ν ≠ 0 := by
  first | exact @GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero | exact GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero | (intros; apply GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (ξ : Ω[Sec (str A) U.1⁄ℂ]), (∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ = 0) → ξ = 0 := by
  first | exact @GlobalTheory.form_eq_zero_of_evForm_eq_zero | exact GlobalTheory.form_eq_zero_of_evForm_eq_zero | (intros; apply GlobalTheory.form_eq_zero_of_evForm_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ), DifferentiableOn ℂ h (pre u.ex U.1) → (∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) → ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.exists_closed_form_fderiv_eq | exact GlobalTheory.CechPer.exists_closed_form_fderiv_eq | (intros; apply GlobalTheory.CechPer.exists_closed_form_fderiv_eq <;> assumption)
end
