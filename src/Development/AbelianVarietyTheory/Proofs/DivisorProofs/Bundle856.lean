module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle826
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle827
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem lvlIdem_apply_of_mem_eig {Γ V : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (x : V) (hx : x ∈ eig ρ Hb lam) :
    ρ.asAlgebraHom (Formalism.L2.DIV.lvlIdem Hb lam) x = x := by
  classical
  rw [mem_eig] at hx
  have hc : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Formalism.L2.DIV.lvlIdem

  rw [map_sum, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]
  have e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹ := fun h => by
    rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem finrank_eig_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  intro Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff
  set p := Formalism.L2.DIV.lvlIdem Hb lam with hp
  set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW
  let f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p)) :=
    ((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod
      ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxe, hxk⟩ hx0
    have h0 : ρ.asAlgebraHom (b 0 * p) x = 0 := by
      have := congrArg (fun z => ((z.1 : _) : V)) hx0; simpa [f] using this
    have h1 : ρ.asAlgebraHom (b 1 * p) x = 0 := by
      have := congrArg (fun z => ((z.2 : _) : V)) hx0; simpa [f] using this
    have hpx : ρ.asAlgebraHom p x = x := lvlIdem_apply_of_mem_eig ρ Hb lam x hxe
    have hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x := fun k => by
      rw [map_mul, Module.End.mul_apply, hpx]
    have hb0 : ρ.asAlgebraHom (b 0) x = 0 := (hb 0).trans h0
    have hb1 : ρ.asAlgebraHom (b 1) x = 0 := (hb 1).trans h1
    have hek : ρ.asAlgebraHom e x = 0 := hxk
    have hx1 : x = ρ.asAlgebraHom (1 - e) x := by
      rw [map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]; rfl
    have : x = 0 := by
      rw [hx1, he, map_sub, map_add (f := _), map_mul]
      simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]
    exact Subtype.ext this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  have hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤
      c * s k * finrank ℂ (eig ρ Hb lam) := by
    intro k
    have hid : b k * p * (b k * p) = b k * p := by
      calc b k * p * (b k * p) = b k * (p * b k) * p := by simp only [mul_assoc]
        _ = b k * (b k * p) * p := by rw [hcomm k]
        _ = (b k * b k) * (p * p) := by simp only [mul_assoc]
        _ = b k * p := by rw [hidem k, Formalism.L2.DIV.lvlIdem_idem]
    obtain ⟨r, hr, hle⟩ := GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid
    rw [hcoeff k] at hr
    have hHb : (0 : ℝ) < Nat.card Hb := by exact_mod_cast Nat.card_pos
    have hH : (0 : ℝ) < Nat.card (H k) := by exact_mod_cast Nat.card_pos
    have hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k := by
      have hHbC : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast hHb.ne'
      have : ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ) := by
        push_cast; rw [hr]; field_simp
      exact_mod_cast this
    have hs : 0 ≤ s k := by
      have : 0 ≤ (Nat.card (H k) : ℝ) * s k := by rw [← hrR]; positivity
      exact le_of_mul_le_mul_left (by simpa using this) hH
    have hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam) := by positivity
    have hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r := by exact_mod_cast hle
    have key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by
      calc ((n k : ℝ) * r) * Nat.card Hb = ((n k : ℝ) * Nat.card (H k)) * s k := by rw [mul_assoc, hrR]; ring
        _ ≤ (c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) * s k := mul_le_mul_of_nonneg_right (hcard k) hs
        _ = (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by ring
    exact hleR.trans (le_of_mul_le_mul_right key hHb)
  have hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) +
      finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p))) := by exact_mod_cast hdim
  calc (finrank ℂ W : ℝ) ≤ _ := hdimR
    _ ≤ c * s 0 * finrank ℂ (eig ρ Hb lam) + c * s 1 * finrank ℂ (eig ρ Hb lam) := add_le_add (hbnd 0) (hbnd 1)
    _ = c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by ring

end GlobalTheory.BadCount
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  first | exact @GlobalTheory.Dieu.height_eq_and_dual_isog | exact GlobalTheory.Dieu.height_eq_and_dual_isog | (intros; apply GlobalTheory.Dieu.height_eq_and_dual_isog <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjHyp

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem main : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) →
    Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  intro R _ C C' _ _ F G H adj
  have hl : ∀ c, pullHyp1 (counitCoef F adj) (pullHyp1 (CoefMap.restrict F G) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    exact (pullHyp1_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (pullHyp1_id c)
  have hr : ∀ c, pullHyp1 (CoefMap.restrict F G) (pullHyp1 (counitCoef F adj) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    refine ((pullHyp1_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (pullHyp1_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.AdjHyp
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem restrict_cover_affine_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  intro R _ X s J U hU
  apply restrict_bijective_one_of_basis s
  · intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let G : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span G = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  · intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩

end GlobalTheory.CechDR
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvalNat

theorem evalAt_natural : ∀ {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U), ∃ h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U, (∀ f : Γ(X, U), evalAt (spMap φ ≫ x) U h' f = φ (evalAt x U h f)) ∧ ∀ (U' : X.Opens) (i : U ≤ U') (h'' : ⊤ ≤ x ⁻¹ᵁ U') (f : Γ(X, U')), evalAt x U' h'' f = evalAt x U h ((X.presheaf.map (homOfLE i).op).hom f) := by
  intro X C C' _ _ φ x U h
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ ((spMap φ) p))
  refine ⟨h', fun f ↦ ?_, fun U' i h'' f ↦ ?_⟩
  · have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
        x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
      rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
      congr 2
    exact congrArg (fun t ↦ t.hom f) e
  · have e : x.appLE U' ⊤ h'' = X.presheaf.map (homOfLE i).op ≫ x.appLE U ⊤ h := by
      rw [Scheme.Hom.map_appLE]
    unfold evalAt
    rw [e]
    rfl

end GlobalTheory.EvalNat
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
private theorem isNilpotent_of_mem_of_isNilDP {B : Type} [CommRing B]
    {J : Ideal B} (δ : DividedPowers J) (hδ : _root_.GlobalTheory.Cris.IsNilDP δ) {x : B} (hx : x ∈ J) :
    IsNilpotent x := by
  obtain ⟨N, hN⟩ := hδ
  refine ⟨N, ?_⟩
  have h := hN [(N, x)] (by simpa using hx) (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← δ.factorial_mul_dpow_eq_pow hx, h, mul_zero]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
theorem _root_.GlobalTheory.Cris.exists_finite_small_cover (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤)
    (T : _root_.GlobalTheory.Cris.Thick κ s) : ∃ (n : ℕ) (b : Fin n → T.B),
      Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : _root_.GlobalTheory.Cris.Thick κ s) (u : T ⟶ S),
        IsUnit (u.φ (b i)) → _root_.GlobalTheory.Cris.IsSmall κ s U S := by
  classical
  let G : Set T.B₀ := {f | ∃ k, ∀ p : PrimeSpectrum T.B₀,
    f ∉ p.asIdeal → T.x.base p ∈ U k}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let p : PrimeSpectrum T.B₀ := ⟨m, hm.isPrime⟩
    have hp : T.x.base p ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (fun q : PrimeSpectrum T.B₀ ↦ T.x.base q) ⁻¹' (U k))
        hk ((U k).isOpen.preimage T.x.continuous)
    exact hpf (hle (Ideal.subset_span ⟨k, fun q hq ↦ hsub hq⟩))
  obtain ⟨t, htG, htspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  let e := t.equivFin
  have hlift : ∀ i : Fin t.card, ∃ y, T.π y = (e.symm i : T.B₀) :=
    fun i ↦ T.surj _
  choose b hb using hlift
  refine ⟨t.card, b, ?_, ?_⟩
  · have hmap : Ideal.map T.π (Ideal.span (Set.range b)) = ⊤ := by
      rw [Ideal.map_span, ← htspan]
      congr 1
      ext f
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [hb]
        exact (e.symm i).2
      · intro hf
        exact ⟨b (e ⟨f, hf⟩), ⟨_, rfl⟩, by rw [hb, Equiv.symm_apply_apply]⟩
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective _ T.surj).1
      (hmap ▸ Submodule.mem_top : (1 : T.B₀) ∈ _)
    have hJ : 1 - y ∈ T.J := by
      rw [← T.ker, map_sub, map_one, hy1, sub_self]
    have hunit : IsUnit y := by
      have := (isNilpotent_of_mem_of_isNilDP _ T.nil hJ).isUnit_one_sub
      simpa using this
    exact Ideal.eq_top_of_isUnit_mem _ hy hunit
  · intro i S u hu
    obtain ⟨k, hk⟩ := htG (e.symm i).2
    refine ⟨k, fun q _ ↦ ?_⟩
    show S.x.base q ∈ U k
    rw [← u.pt, Scheme.Hom.comp_apply]
    apply hk
    intro hq
    have h1 : u.φ₀ (e.symm i : T.B₀) ∈ q.asIdeal := hq
    rw [← hb, u.comm] at h1
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map S.π))

end GlobalTheory.Cris
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero : GlobalTheory.EtC.A9 := by
  first | exact @GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | exact GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | (intros; apply GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ f : ∀ k, Hol (K.W k), (∀ k k' (h : K.le 0 k' k), Charts.sh h (f k) = f k') → ∃ G : Tot I g → ℂ, AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, (f k).fn p = G p) ∧ (∀ (l : Λ) (q : Hol F.V), (∀ k k' (h : K.le l k' k), Charts.sh h (f k) = f k' + K.cst k' q) → ∀ p : Tot I g, p.1 ∈ F.V → G (F.shift l p) = G p + q.fn p.1) ∧ ((∀ k a, dw a (f k) = 0) → ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0)) := by
  intro I _ g Λ _ F K hK f hf
  classical
  have indep : ∀ k₁ k₂ p, p ∈ K.W k₁ → p ∈ K.W k₂ → (f k₁).fn p = (f k₂).fn p := by
    intro k₁ k₂ p h₁ h₂
    obtain ⟨k, hk, hl₁, hl₂⟩ := hK.2 0 k₁ k₂ p h₁ (by rw [F.shift_zero]; exact h₂)
    have e₁ := Charts.fn_sh hl₁ (f k₁) hk
    have e₂ := Charts.fn_sh hl₂ (f k₂) hk
    rw [hf k₁ k hl₁, F.shift_zero] at e₁
    rw [hf k₂ k hl₂, F.shift_zero] at e₂
    rw [← e₁, ← e₂]
  let G : Tot I g → ℂ := fun p ↦ if h : ∃ k, p ∈ K.W k then (f h.choose).fn p else 0
  have hG : ∀ k, ∀ p ∈ K.W k, (f k).fn p = G p := by
    intro k p hp
    have h : ∃ k, p ∈ K.W k := ⟨k, hp⟩
    simp only [G, dif_pos h]
    exact indep _ _ _ hp h.choose_spec
  have hGev : ∀ k, ∀ p ∈ K.W k, G =ᶠ[𝓝 p] (f k).fn := fun k p hp ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hp] with q hq using (hG k q hq).symm
  refine ⟨G, ?_, hG, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk⟩ := hK.1 p hp
    exact ((f k).analytic p hk).congr (hGev k p hk).symm
  · intro l q hq p hp
    obtain ⟨k₁, h₁⟩ := hK.1 p hp
    obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l p) hp
    obtain ⟨k, hk, -, hl⟩ := hK.2 l k₁ k₂ p h₁ h₂
    have e := congrArg (fun u ↦ Hol.fn u p) (hq k₂ k hl)
    rw [Charts.fn_sh hl _ hk, Hol.fn_add _ _ hk, Charts.fn_cst K k q hk] at e
    rw [← hG k₂ _ h₂, ← hG k p hk, e]
  · intro h0 z hz w
    have hder : ∀ w' : Fin g → ℂ, HasFDerivAt (fun u ↦ G (z, u)) (0 : (Fin g → ℂ) →L[ℂ] ℂ) w' := by
      intro w'
      obtain ⟨k, hk⟩ := hK.1 (z, w') hz
      have hfd : HasFDerivAt (fun u : Fin g → ℂ ↦ ((z, u) : Tot I g))
          (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) w' :=
        (hasFDerivAt_const z w').prodMk (hasFDerivAt_id w')
      have hGd : HasFDerivAt G (fderiv ℂ (f k).fn (z, w')) (z, w') := by
        rw [← (hGev k _ hk).fderiv_eq]
        exact (((f k).analytic _ hk).differentiableAt.congr_of_eventuallyEq (hGev k _ hk)).hasFDerivAt
      have hL : (fderiv ℂ (f k).fn (z, w')).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) = 0 := by
        have hs : ∀ a : Fin g, fderiv ℂ (f k).fn (z, w') ((0, Pi.single a 1) : Tot I g) = 0 := by
          intro a
          have := Hol.fn_der ((0, Pi.single a 1) : Tot I g) (f k) hk
          rw [show Hol.der _ (f k) = dw a (f k) from rfl, h0 k a, ← Hol.ev_apply _ hk, map_zero] at this
          exact this.symm
        refine ContinuousLinearMap.ext fun v ↦ ?_

        rw [← Finset.univ_sum_single v, map_sum, ContinuousLinearMap.zero_apply]
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        have e : Pi.single a (v a) = v a • (Pi.single a 1 : Fin g → ℂ) := by
          rw [← Pi.single_smul]; simp
        rw [e, map_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hs a, smul_zero]
      have := hGd.comp w' hfd
      rw [hL] at this
      exact this
    exact is_const_of_fderiv_eq_zero (fun w' ↦ (hder w').differentiableAt) (fun w' ↦ (hder w').fderiv) w 0

end GlobalTheory.AnPer.Charts
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  first | exact @GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | exact GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | (intros; apply GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_unique_period_quasiLogarithm_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate), QL μ' ⊤ f → ∃! y : F.B, c.HasPeriod F.θ t f y := by
  first | exact @GlobalTheory.PeriodExists.main | exact GlobalTheory.PeriodExists.main | (intros; apply GlobalTheory.PeriodExists.main <;> assumption)
end
