module

import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle525
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle487
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle535
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up.SerCp
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ExportSeries hiding Base



set_option linter.unusedVariables false

section L1
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

private def weight {n : ℕ} (x : ExportSeries.Weight a.D n) : ExportSeries.Weight b.D n where
  p := (by with_unfolding_all exact (x.p :))
  q := (by with_unfolding_all exact (x.q :))
  ap := (by with_unfolding_all exact (x.ap :))
  am := (by with_unfolding_all exact (x.am :))
  c := (by with_unfolding_all exact (x.c :))
  lam := (by with_unfolding_all exact (x.lam :))

private def twist {A : Type} [CommGroup A] (x : Twist a.D A) : Twist b.D A where
  Q := (by with_unfolding_all exact (x.Q :))
  chi := (by with_unfolding_all exact (x.chi :))
  res := (by with_unfolding_all exact (x.res :))

private def typeDat {r : ℕ} (x : TypeDat a.D r) : TypeDat b.D r where
  Pg := (by with_unfolding_all exact (x.Pg :))
  P := (by with_unfolding_all exact (x.P :))
  mu := (by with_unfolding_all exact (x.mu :))

private def frame {S T : HSp a.D} (x : Frame S T) : @Frame b.D ((S)) ((T)) where
  ψ := (by with_unfolding_all exact (x.ψ :))
  θ := (by with_unfolding_all exact (x.θ :))
  sT := (by with_unfolding_all exact (x.sT :))
  BS := (by with_unfolding_all exact (x.BS :))
  BT := (by with_unfolding_all exact (x.BT :))
  ΛS := (by with_unfolding_all exact (x.ΛS :))
  ΛT := (by with_unfolding_all exact (x.ΛT :))
  βS := (by with_unfolding_all exact (x.βS :))
  βT := (by with_unfolding_all exact (x.βT :))
  f₀ := (by with_unfolding_all exact (x.f₀ :))

private def base {S T : HSp a.D} (x : ExportSeries.Base S T) : @ExportSeries.Base b.D ((S)) ((T)) where
  hr := (by with_unfolding_all exact (x.hr :))
  F := frame b x.F
  G := (by with_unfolding_all exact ((typeDat b x.G) :))
  de := twist b x.de
  w := (by with_unfolding_all exact ((weight b x.w) :))
  mu0 := (by with_unfolding_all exact (x.mu0 :))
  eta := (by with_unfolding_all exact (x.eta :))













end L1

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

end L2

private abbrev lt {B : Base} {C : Cols B} (c : Late B C) (n : NStage B C c.W) : Late B C := ⟨c.W, c.V, c.S, n, c.G⟩

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)

section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N}

end





section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N} {ρ : Setup X}
  {Y : NExp (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N X} {i : X.Tw} {j : Fin (lt c a).D.R.m} {s : Bool} {rd : Rd ρ Y i j s}

end

end L2

section L3
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)
  {Γ : Type} [i1 : Group Γ] [i2 : Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 (lt c a).D.what₂.LL Γ Pl0 I0 (List ℕ) T (lt c a).D.R.m} {Ks : Type} [i3 : Field Ks] [i4 : NumberField Ks]
  [iK : Algebra Ks (lt c a).D.what₂.LL] {Rl : RealDat3 (lt c a).D A3 Ks}
  {v₀ : ∀ (j : Fin (lt c a).D.R.m) (σ : (lt c a).D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec} {j : Fin (lt c a).D.R.m}
  {X : ExportSeries.Base (Vc (lt c a).D j) (Wc (lt c a).D j)} {ν : ℂ}

end L3

section L4
open GlobalTheory.SeriesTie
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)

end L4

end GlobalTheory.HeightCounting.Up.SerCp
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chartLie_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U), ∃ v' : Fin M.n → (epsR (PowerSeries ℂ) ⟶ W.t.G), (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ i) ∧ IsLieBasis v' := by
  intro E _ _ _ H Dw l Xo c σ V Y a χ W M hM
  have cast : ∀ (p q : Sp (PowerSeries ℂ) ⟶ Y.X) (_ : p = q) (n : SABMap W.t Y.t p),
      ∃ n' : SABMap W.t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ (spMap (ev χ M.U hM) ≫ M.hU.fromSpec) (GlobalTheory.FlagMod.spMap_ev χ M.hU hM).symm W.m
  obtain ⟨v', hv', hb, -⟩ := M.lie (PowerSeries ℂ) (ev χ M.U hM) W.t m'
  refine ⟨v', fun j => ?_, hb⟩
  rw [← hm', hv' j]
  have e : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev χ M.U hM) = dualMap (ev χ M.U hM) := by
    ext x <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, dualMap]
  rw [e]

theorem exists_lieComb_matrix : ∀ (R : Type) [CommRing R] [Nontrivial R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n n' : ℕ) (v : Fin n → (epsR R ⟶ G)) (v' : Fin n' → (epsR R ⟶ G)), IsLieBasis v → IsLieBasis v' → ∃ h : n' = n, ∃ A : Matrix (Fin n) (Fin n) R, IsUnit A.det ∧ ∀ i, IsLieComb (A i) v (v' (Fin.cast h.symm i)) := by
  intro R _ _ G _ _ O _ act n n' v v' hv hv'
  let b := GlobalTheory.Serre.Lie.basis act hv
  let b' := GlobalTheory.Serre.Lie.basis act hv'
  have h : n' = n := by simpa using Fintype.card_congr (b'.indexEquiv b)
  subst h
  refine ⟨rfl, (b.toMatrix b').transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose]
    refine IsUnit.of_mul_eq_one (b'.toMatrix b).det ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · have hv_eq : v = fun k => (b k).hom := funext fun k => (GlobalTheory.Serre.Lie.hom_basis (a := act) hv k).symm
    rw [Fin.cast_eq_self, ← GlobalTheory.Serre.Lie.hom_basis (a := act) hv' i, hv_eq, GlobalTheory.Serre.Lie.isLieComb_iff]
    congr 1
    conv_lhs => rw [← b.sum_repr (b' i)]
    rfl

theorem lieCoord_det_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M h1 h2 h3 h4 h5 h6
  obtain ⟨e, v, z, hev, hv, hz⟩ := GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc E H Dw l Xo c σ V Y a χ W g ty Fu Ha
  obtain ⟨v', hv'1, hv'2⟩ := exists_chartLie_along E H Dw l Xo c σ V Y a χ W M h6
  obtain ⟨hn, A, hA, hAc⟩ := exists_lieComb_matrix (PowerSeries ℂ) W.t.G (𝓞 E) W.t.act g M.n v v' hv hv'2
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum E H Dw l Xo c σ V Y a χ W g ty Fu Ha M h6 e v z hn (fun i => v' (Fin.cast hn.symm i)) A
    h1 h2 h3 h4 h5 hev hv hz (fun i => hv'1 _) hAc
  by_cases hex : ∃ w : ℂ, T₀ < w.im ∧ ∀ i k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)
  swap
  · refine ⟨T₀, 1, one_pos, ?_⟩
    intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
    exact (hex ⟨w, hw, fun i k => (hT₀ w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf i).1 k⟩).elim
  obtain ⟨w₀, -, hs⟩ := hex
  obtain ⟨T', C, hC, hb⟩ := GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi g A w₀ hA hs
  have hd : 0 < ‖(Matrix.of z).det‖ := norm_pos_iff.2 hz
  refine ⟨max T₀ T', C * (‖(Matrix.of z).det‖ + ‖(Matrix.of z).det‖⁻¹), by positivity, ?_⟩
  intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
  have hM : (Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j) =
      (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m) * Matrix.of z := by
    ext i j
    rw [Matrix.of_apply, ((hT₀ w (lt_of_le_of_lt (le_max_left _ _) hw) yF e1 e2 hz' x φ hk hg u Wv hf hdf i).2 j),
      Matrix.mul_apply]
    rfl
  rw [hM, Matrix.det_mul, norm_mul]
  obtain ⟨b1, b2⟩ := hb w (lt_of_le_of_lt (le_max_right _ _) hw)
  set d := ‖(Matrix.of z).det‖
  set t := ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖
  constructor
  · rw [mul_inv, ← div_eq_mul_inv]
    calc C⁻¹ / (d + d⁻¹) ≤ C⁻¹ * d := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ d * (d + d⁻¹) := by rw [mul_add, mul_inv_cancel₀ hd.ne']; nlinarith
          nlinarith [inv_pos.2 hC]
      _ ≤ t * d := mul_le_mul_of_nonneg_right b1 hd.le
  · calc t * d ≤ C * d := mul_le_mul_of_nonneg_right b2 hd.le
      _ ≤ C * (d + d⁻¹) := by nlinarith [inv_pos.2 hd]

end GlobalTheory.ArcNormal
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntHyp_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → KerEntHyp Pl O Bs Y (I.tw l l0 Z) := fun I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8 =>
  ⟨GlobalTheory.T.targetPairing_sizes_in_coefficientField_valueGroup I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.trueChains_kernelDatum_sourceSideLattice I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelDatum_lattice_target_side_trueChains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelEntries_form_true_chains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8⟩

end GlobalTheory.Mem.Col2.TC

end
end
