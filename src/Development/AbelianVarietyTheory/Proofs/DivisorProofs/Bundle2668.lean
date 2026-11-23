module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle673
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle675
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle674
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteOrder

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem two_smul_pow {G M : Type*} [Group G] [AddCommGroup M] (q : G → M) (q1 : q 1 = 0)
    (hq : ∀ x y : G, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹) (ψ : G) (n : ℕ) :
    (2 : ℤ) • q (ψ ^ n) = ((n : ℤ) * (n + 1)) • q ψ + ((n : ℤ) * (n - 1)) • q ψ⁻¹ := by
  induction n using Nat.twoStepInduction with
  | zero => simp [q1]
  | one => simp [two_zsmul]
  | more n h0 h1 =>
    have h := hq (ψ ^ (n + 1)) ψ
    rw [← pow_succ, pow_succ ψ n, mul_inv_cancel_right, ← pow_succ] at h
    push_cast at h1 ⊢
    linear_combination (norm := module) (2 : ℤ) • h - h0 + (2 : ℤ) • h1

theorem pull_one_eq_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h0 : pull (η[A]).left c = 0 := GlobalTheory.cechPic_sp_field_eq_zero K _
  rw [Hom.one_def, Over.comp_left, pull_comp, h0, map_zero]

theorem pull_iter {S : Scheme.{0}} {A : Over S} (σ : A ≅ A) (c : Pic A.left)
    (h : pull σ.hom.left c = c) (m : ℕ) : pull (GlobalTheory.SerreField.iter σ m).hom.left c = c := by
  induction m with
  | zero => exact pull_id c
  | succ m ih =>
    change pull ((GlobalTheory.SerreField.iter σ m).hom.left ≫ σ.hom.left) c = c
    rw [pull_comp, h, ih]

theorem eff_add_nsmul {X : Scheme.{0}} [IsIntegral X] {a b : Pic X} (ha : Eff a) (hb : Eff b) (k : ℕ) :
    Eff (a + k • b) := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [succ_nsmul, ← add_assoc]; exact eff_add _ _ ih hb

theorem exists_ge_cast_ne_zero (K : Type) [Field K] (t : ℕ) : ∃ n : ℕ, t ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : (t : K) = 0
  · exact ⟨t + 1, by omega, by simp [h]⟩
  · exact ⟨t, le_rfl, h⟩

theorem finiteOrder_of_const_of_cube :
    GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  intro hConst hCube K _ _ A _ _ hA L hL hAmp σ hσ hfix
  haveI : IsIntegral A.left := GlobalTheory.SS.isIntegral_of_abelian A hA
  let q : (A ⟶ A) → Pic A.left := fun u => pull u.left (cls L hL)
  have q1 : q 1 = 0 := pull_one_eq_zero A _
  have hq : ∀ x y : A ⟶ A, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹ := by
    intro x y
    have h : q (x * y * y⁻¹) + q x + q y + q y⁻¹ = q (x * y) + q (x * y⁻¹) + q (y * y⁻¹) + q 1 :=
      hCube K A hA L hL hAmp (cls L hL) x y y⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, q1, add_zero, add_zero] at h
    exact h.symm
  obtain ⟨d, hd, r, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hAmp
  have heff : ∀ u : A ⟶ A, Eff ((d : ℤ) • q u) := fun u => by
    have h := eff_pull_of_veryAmpleBy K A.hom _ r s (GlobalTheory.AbLaw.isLB_pw hL d) hs u.left inferInstance
    rwa [cls_pw hL, map_zsmul] at h
  obtain ⟨t₀, ht₀⟩ := hConst K A hA L hL hAmp
    ((2 * d : ℤ) • (q (𝟙 A) + q (𝟙 A) + q (𝟙 A) + q (𝟙 A)⁻¹))
  obtain ⟨n, hn, hnK⟩ := exists_ge_cast_ne_zero K t₀
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hnK)
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA (k + 1) hnK
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.SerreField.exists_iter_fix σ (𝟙_ (Over (Sp K))) (k + 1)
  refine ⟨m, hm0, ?_⟩
  have hx : q (GlobalTheory.SerreField.iter σ m).hom = q (𝟙 A) := (pull_iter σ _ hfix m).trans (pull_id _).symm
  have hxm : IsMonHom (GlobalTheory.SerreField.iter σ m).hom := inferInstance
  generalize (GlobalTheory.SerreField.iter σ m).hom = x at hm hx hxm ⊢
  have hu : IsMonHom (x * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, e⟩ := hdiv _ hu (fun y hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hm y hy, Category.comp_id, mul_inv_cancel])
  have h1 := hq x (𝟙 A)
  rw [hx, e] at h1
  have h2 := two_smul_pow q q1 hq ψ (k + 1)
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * ((k + 1) * (k + 2))) (hn.trans ?_) ψ hψ ?_
    · nlinarith [Nat.zero_le k, Nat.mul_le_mul_right ((k + 1) * (k + 2)) hd]
    · have h3 := eff_add_nsmul (eff_add _ _ (heff (x * 𝟙 A)) (heff (x * 𝟙 A))) (heff ψ⁻¹) ((k + 1) * k)
      convert h3 using 1
      change _ - _ • q ψ = _
      rw [← natCast_zsmul, ← natCast_zsmul]
      push_cast at h2 ⊢
      linear_combination (norm := module) (d : ℤ) • h2 - (2 * d : ℤ) • h1
  rw [hψ1, one_pow] at e
  exact mul_inv_eq_one.1 e

end GlobalTheory.AmpleFiniteOrder
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  first | exact @GlobalTheory.KeyFourth.exists_unit_secZ_keyRule | exact GlobalTheory.KeyFourth.exists_unit_secZ_keyRule | (intros; apply GlobalTheory.KeyFourth.exists_unit_secZ_keyRule <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.ShFam.HolFrames

theorem exists_affine_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {T : Scheme.{0}} (io : T ⟶ gen Y) (y : T) :
    ∃ (W : T.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(T, W))
      (_ : EigFrame Y φ (((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y)),
      y ∈ W ∧ ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genStr Y = spMap φ := by
  obtain ⟨U, hU, φ, f, hy, hφ, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H D l Xo c O β Y (io y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (a := y) (u := (io ⁻¹ᵁ U : T.Opens)) hy (io ⁻¹ᵁ U).2
  have hW : IsAffineOpen W := hW
  have e : (show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io =
      spMap (io.appLE U W hWU).hom ≫ (show Sp Γ(gen Y, U) ⟶ gen Y from hU.fromSpec) :=
    (IsAffineOpen.SpecMap_appLE_fromSpec io hU hW hWU).symm
  obtain ⟨g, -⟩ := exists_bc f (io.appLE U W hWU).hom (φ' := (io.appLE U W hWU).hom.comp φ)
    (x' := ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y) rfl (by rw [e, Category.assoc])
  refine ⟨W, hW, _, g, hyW, ?_⟩
  rw [e, Category.assoc, spMap_comp₂]
  exact congrArg _ hφ


open GlobalTheory.Points GlobalTheory.ShFam.EigLoc in
theorem exists_affine_holFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io → io ≫ genStr Y = B.str → ∃ (W : B.X → B.X.Opens) (hW : ∀ y, IsAffineOpen (W y)) (φ : ∀ y, c.F →+* Γ(B.X, W y)) (fr : ∀ y, EigFrame Y (φ y) (((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genι Y)) (a : B.X → GlobalTheory.CxPts B.str e → CxFr Y e), (∀ y, y ∈ W y) ∧ (∀ y, ((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genStr Y = spMap (φ y)) ∧ (∀ y p, (a y p).1.1 = p.1 ≫ io) ∧ (∀ y p (h : p ∈ GlobalTheory.CxPts.ptsIn B.str e (W y)) ρ i, (a y p).2.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i) ∧ ∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (A : Set V) (x : V → GlobalTheory.CxPts B.str e), IsOpen A → IsHolTo A (fun b => (x b).1) → Set.MapsTo x A (GlobalTheory.CxPts.ptsIn B.str e (W y)) → HolFam A (fun b => a y (x b)) := by
  intro E _ _ _ H D l Xo c O _ β Y e B io _ hio
  choose U hU φ fr hy hφ using fun y => exists_affine_frame Y io y
  have hov : ∀ p : GlobalTheory.CxPts B.str e, (p.1 ≫ io) ≫ genStr Y = spMap e := fun p => by
    rw [Category.assoc, hio, p.2]
  have hp : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)),
      spMap (GlobalTheory.CxPts.evHom h) ≫ (show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) = p.1 := fun y p h =>
    specMap_valMap_fromSpec (hU y) p.1 h
  have hx : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)), (p.1 ≫ io) ≫ genι Y =
      spMap (GlobalTheory.CxPts.evHom h) ≫ ((show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) ≫ io) ≫ genι Y := fun y p h => by
    rw [← hp y p h]
    simp only [Category.assoc]
  have ex : ∀ y (p : GlobalTheory.CxPts B.str e), ∃ g : EigFrame Y e ((p.1 ≫ io) ≫ genι Y),
      ∀ h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y), ∀ ρ i,
        g.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i := fun y p => by
    by_cases h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)
    · obtain ⟨g, hg⟩ := exists_bc (fr y) (GlobalTheory.CxPts.evHom h) (φ' := e) (spMap_inj (by
        rw [spMap_comp₂, ← hφ y, ← hov p, ← hp y p h]
        simp only [Category.assoc])) (hx y p h)
      exact ⟨g, fun _ => hg⟩
    · obtain ⟨g⟩ := exists_eigFrame E H D l Xo c O β Y ℂ e _ (hov p)
      exact ⟨g, fun h' => (h h').elim⟩
  choose g hg using ex
  refine ⟨U, hU, φ, fr, fun y p => ⟨⟨p.1 ≫ io, hov p⟩, g y p⟩, hy, hφ, fun _ _ => rfl, hg,
    fun y V _ _ _ A x hA hol hm => ⟨fun W f => by
      simp only [valAt'_eq_valR, valR_comp]
      exact hol (io ⁻¹ᵁ W) ((io.app W).hom f), fun ρ i => ?_⟩⟩
  exact holTan_dualMap hA ((fr y).v ρ i) (fun b hb => GlobalTheory.CxPts.evHom (hm hb)) (fun a => ⟨_,
    (hol (U y) a).2.mono fun b hb => ⟨hb, hm hb⟩, fun b hb => (GlobalTheory.CxPts.ev_eq (hm hb) a).symm⟩)
    fun b hb => hg y _ (hm hb) ρ i

end GlobalTheory.ShFam.HolFrames
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj
open GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg GlobalTheory.FlagMod
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.ChartLieFrame

theorem eq_of_loc {Z : Scheme.{0}} {W : Z.Opens} {a b : Γ(Z, W)}
    (h : ∀ p ∈ W, ∃ (N : Z.Opens) (e : N ≤ W), p ∈ N ∧ resG Z e a = resG Z e b) : a = b :=
  ext_ev_loc fun p hp => by
    obtain ⟨N, e, hpN, hab⟩ := h p hp
    exact ⟨N, hpN, fun S _ z hz hN => by rw [← ev_res z e hN hz a, ← ev_res z e hN hz b, hab]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

def Rep (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)) : Prop :=
  ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W)),
    VB.dualApp s h w = tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (h.trans hU)) j)) (tau_le hW le_rfl) w

theorem tanLin_res (M : MChart Y) {W W₀ V : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (hV : W₀ ≤ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega Y.t.G, V)) (j : Fin M.n) :
    tanLin Y.t (tau_le hW (e.trans hV)) s (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j) =
      fun i => resG Y.X e (tanLin Y.t (tau_le hW₀ hV) s (lieBasis M (tau hW₀) (tau_le hW₀ hM) j) i) := by
  have φe : spMap (ev (tau hW) W₀ (tau_le hW e)) ≫ tau hW₀ = tau hW := spMap_ev (tau hW) hW₀ (tau_le hW e)
  rw [← tanPull_lieBasis M _ φe (tau_le hW₀ hM) (tau_le hW (e.trans hM)) j,
    tanLin_tanPull Y.t _ φe (tau_le hW₀ hV) (tau_le hW (e.trans hV))]
  funext i
  exact ev_tau hW e (tau_le hW e) _

theorem tanEv_res (M : MChart Y) {W W₀ : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W₀)) (j : Fin M.n) :
    tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j)) (tau_le hW le_rfl) (resM _ e w) =
      resG Y.X e (tanEv Y.t (isTan_tv (lieBasis M (tau hW₀) (tau_le hW₀ hM) j)) (tau_le hW₀ le_rfl) w) := by
  rw [tanEv_resM]
  exact congrFun (tanLin_res M hW hW₀ e hM le_rfl ![w] j) 0

theorem Rep.res {M : MChart Y} {j : Fin M.n} {U : Y.X.Opens} {hU : U ≤ M.U} {s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) {U' : Y.X.Opens} (e : U' ≤ U) : Rep M j (e.trans hU) (resM _ e s) := fun W hW h w => by
  rw [VB.dualApp_res]
  exact hs W hW (h.trans e) w

theorem rep_unique (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {s s' : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) (hs' : Rep M j hU s') : s = s' :=
  VB.dual_ext fun W h w => eq_of_loc fun p hp => by
    obtain ⟨N, hN, hpN, hNW'⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W) hp
    have hNW : N ≤ W := hNW'
    refine ⟨N, hNW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← VB.dualApp_resM, hs N hN, hs' N hN]

theorem rep_of_cover (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {ι : Type} (V : ι → Y.X.Opens)
    (hV : ∀ k, V k ≤ U) (hc : U ≤ iSup V) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U))
    (H : ∀ k, Rep M j ((hV k).trans hU) (resM _ (hV k) s)) : Rep M j hU s := fun W hW h w =>
  eq_of_loc fun p hp => by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (h hp))
    obtain ⟨N, hN, hpN, hNW⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W ⊓ V k) ⟨hp, hk⟩
    have eW : N ≤ W := fun q hq => (hNW hq).1
    have eV : N ≤ V k := fun q hq => (hNW hq).2
    refine ⟨N, eW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← tanEv_res M hN hW eW (h.trans hU) w j]
    have := H k N hN eV (resM _ eW w)
    rw [VB.dualApp_res] at this
    exact this

def locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n) (hC : IsAffineOpen C.U)
    (hM : C.U ≤ M.U) : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U) :=
  ∑ i : Fin n, (tanLin Y.t (tau_le hC le_rfl) C.e (lieBasis M (tau hC) (tau_le hC hM) j) i : Γ(Y.X, C.U)) •
    (C.isFrame.coord i : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U))

theorem rep_locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n)
    (hC : IsAffineOpen C.U) (hM : C.U ≤ M.U) : Rep M j hM (locSec M j C hC hM) := fun W hW h w => by
  rw [locSec, VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    VB.IsFrame.dualApp_coord, smul_eq_mul]
  conv_rhs => rw [← (C.isFrame.basis h).sum_repr w]
  rw [tanEv_sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [VB.IsFrame.basis_apply, tanEv_resM, ev_tau_self, RingHom.id_apply, _root_.mul_comm]
  exact congrArg (((C.isFrame.basis h).repr w i) * ·) (congrFun (tanLin_res M hW hC h hM le_rfl C.e j) i).symm

theorem exists_rep (M : MChart Y) (j : Fin M.n) : ∃ s : Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), Rep M j le_rfl s := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  let V : (Σ n : ℕ, {C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n // IsAffineOpen C.U ∧ C.U ≤ M.U}) → Y.X.Opens :=
    fun k => k.2.1.U
  have hV : ∀ k, V k ≤ M.U := fun k => k.2.2.2
  have hc : M.U ≤ iSup V := fun p hp => by
    obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
    obtain ⟨N, hN, hpN, hNU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := M.U ⊓ U₀) ⟨hp, hp₀⟩
    have e₁ : N ≤ M.U := fun q hq => (hNU hq).1
    have e₂ : N ≤ U₀ := fun q hq => (hNU hq).2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨n, ⟨⟨N, fun i => resM _ e₂ (e i), he.res e₂⟩, hN, e₁⟩⟩, hpN⟩
  have hrep : ∀ k, Rep M j (hV k) (locSec M j k.2.1 k.2.2.1 k.2.2.2) := fun k => rep_locSec M j _ _ _
  obtain ⟨t, ht⟩ := Twist.exists_sec_of_cover V hV hc (fun k => locSec M j k.2.1 k.2.2.1 k.2.2.2) fun k k' =>
    rep_unique M j (inf_le_left.trans (hV k)) ((hrep k).res inf_le_left) ((hrep k').res inf_le_right)
  exact ⟨t, rep_of_cover M j le_rfl V hV hc t fun k => by rw [ht k]; exact hrep k⟩

theorem isFrame_of_rep (M : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ j, Rep M j le_rfl (f j)) :
    VB.IsFrame f := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  refine VB.isFrame_of_forall_exists fun V h p hp => ?_
  obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := V ⊓ U₀) ⟨hp, hp₀⟩
  have e₁ : W ≤ V := fun q hq => (hWU hq).1
  have e₂ : W ≤ U₀ := fun q hq => (hWU hq).2
  let C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n := ⟨W, fun i => resM _ e₂ (e i), he.res e₂⟩
  refine ⟨W, e₁, hpW, ?_⟩
  let R := (C.isFrame.dual.basis (le_rfl : C.U ≤ C.U)).equivFun
  let T : (Fin M.n → Γ(Y.X, W)) → (Fin n → Γ(Y.X, W)) :=
    (tanLin Y.t (tau_le hW (le_rfl : W ≤ C.U)) C.e) ∘ (lieBasis M (tau hW) (tau_le hW (e₁.trans h))).equivFun.symm
  have hT : Function.Bijective T :=
    (HodgeCech.tanLin_bijective Y.t C (tau hW) (tau_le hW le_rfl)).comp (LinearEquiv.bijective _)
  have key : ∀ a, R (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j)) a) = T a := by
    intro a
    funext i

    simp only [R, T, Function.comp_apply, Module.Basis.equivFun_apply, VB.IsFrame.dual_basis_repr,
    Fintype.linearCombination_apply, VB.dualApp_sum, LinearMap.sum_apply, VB.dualApp_smul, LinearMap.smul_apply,
    VB.dualApp_res, Module.Basis.equivFun_symm_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, GlobalTheory.LB.resG_self]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf k W hW _ _, GlobalTheory.Twist.resM_self]
    rfl
  have hc : R ∘ (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j))) = T := funext key
  exact (Function.Bijective.of_comp_iff' R.bijective _).1 (hc ▸ hT)

theorem rep_chg (M M' : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ i, Rep M i le_rfl (f i))
    (j : Fin M'.n) :
    Rep M' j inf_le_right (∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f i)) := fun W hW h w => by
  have ev' : ∀ v, tanEv Y.t (isTan_tv v) (tau_le hW le_rfl) w = tanLin Y.t (tau_le hW le_rfl) ![w] v 0 := fun v => rfl
  rw [VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply, VB.dualApp_res, smul_eq_mul]

  rw [ev', ← (lieBasis M (tau hW) (tau_le hW (h.trans inf_le_left))).sum_toMatrix_smul_self
  (lieBasis M' (tau hW) (tau_le hW (h.trans inf_le_right))) j, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hf i W hW (h.trans inf_le_left) w, ev']
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← chg_map M M' (tau hW) (tau_le hW (h.trans inf_le_left)) (tau_le hW (h.trans inf_le_right)) (tau_le hW h),
    Matrix.map_apply, ev_tau hW h]

theorem exists_lieFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y
  choose f hf using fun (M : MChart Y) (j : Fin M.n) => exists_rep M j
  exact ⟨f, fun M => isFrame_of_rep M (f M) (hf M), fun M M' j =>
    rep_unique M' j inf_le_right ((hf M' j).res inf_le_right) (rep_chg M M' (f M) (hf M) j)⟩

end GlobalTheory.ChartLieFrame
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirigUniq

theorem one_comp_monHom {S : Scheme.{0}} {T A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem pull_comp_left {S : Scheme.{0}} {U V W : Over S} (g : U ⟶ V) (f : V ⟶ W) (c : GlobalTheory.CechPic.Pic W.left) :
    GlobalTheory.CechPic.pull (g ≫ f).left c = GlobalTheory.CechPic.pull g.left (GlobalTheory.CechPic.pull f.left c) := by
  rw [Over.comp_left, GlobalTheory.CechPic.pull_comp]

theorem pic_eq_zero_of_fpqc {S : Scheme.{0}} (X Y Y' : Over S) [GrpObj X] (hX : IsAbelianScheme X)
    (c : Y' ⟶ Y) (hfl : Flat c.left) (hsu : Surjective c.left) (hqc : QuasiCompact c.left)
    (d : GlobalTheory.CechPic.Pic (X ⊗ Y).left)
    (h0 : GlobalTheory.CechPic.pull (lift (1 : Y ⟶ X) (𝟙 Y)).left d = 0)
    (h1 : GlobalTheory.CechPic.pull (lift (fst X Y') (snd X Y' ≫ c)).left d = 0) : d = 0 := by
  obtain ⟨D, hD, rfl⟩ := GlobalTheory.CechPic.cls_surj d
  have t := GlobalTheory.RigDesc.triv_of_triv_zero_of_fpqc S X Y Y' hX c hfl hsu hqc D hD
    ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h0) ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h1)
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hD).2 t

end GlobalTheory.BirigUniq

namespace GlobalTheory.BirigUniq

end GlobalTheory.BirigUniq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_isotropic_hermitianSpace_of_negativeIndex : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  first | exact @GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx | exact GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx | (intros; apply GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧ GlobalTheory.Published.AbelianDeRham.BaseChange := by
  first | exact @GlobalTheory.abelianDeRham_free_hodge_baseChange | exact GlobalTheory.abelianDeRham_free_hodge_baseChange | (intros; apply GlobalTheory.abelianDeRham_free_hodge_baseChange <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing : GlobalTheory.Published.AbelianDeRham → ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring <;> assumption)
end
