module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle506
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupForm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.AvgColJet

theorem fockIn_frC {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ) (hj : j < D.R.m)
    (f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f)
    (Q : PolF D (G.pT (.top t j)).rank (G.pS (.top t j)).rank) :
    fockIn W N.frC (.top t j) f Q = W.fock (.top t j) f (AvgCol.frCh W N j Q) := by
  have hn : DefNode D.R.m (.top j) ∧ DefNode D.R.m (.top (j + 1)) :=
    ⟨show j ≤ D.R.m by omega, show j + 1 ≤ D.R.m by omega⟩
  have c1 : W.cart (.top j) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.1)
  have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.2)
  have e : ∀ X, DefNode D.R.m X → N.frC X = fun τ => W.onb X τ * AvgCol.frRel W N X τ := by
    intro X hX
    funext τ
    have hu : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ)
    rw [AvgCol.frRel, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  simp only [fockIn, GridData.Weil.fock, GridData.cartS, GridData.onT, GridData.onS, c1, c2, e _ hn.1, e _ hn.2]
  rw [GlobalTheory.FockBaseChange.pureTensorO_subst D W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ f hf]
  rfl

theorem fockComp_frC_eq_jetOp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  intro D T L sc G W U S μ0 hL j hj t d hd x y
  have hp : DefPair D.R.m (Pair.top t j : Pair T) := show j + 1 ≤ D.R.m by omega
  have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd).1
  unfold fockComp
  refine congrArg (fun F => Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1))) F (nuEnd G (.top t j))) (funext fun m => ?_)
  unfold jetTab kerFin
  have hid : m.mapDomain (fvar G (.top t j)) = m := Finsupp.mapDomain_id
  rw [hid, Subgroup.coe_mul, Subgroup.coe_mul, GlobalTheory.FockReal.ker_mul, fockIn_frC hL W S.N t j hj _ hf]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om (.top t j)) (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
    W.θ W.θ_is _ (S.N.u _).2 _ (S.N.u _).2 _ _ _ _ _ _ hf

end GlobalTheory.AvgColJet
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem movedVec_theta_fockVac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (p : Pair T), DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (movedVec t S d) ∧
      ∀ ρ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) (movedVec t S d) := by
  intro D T L sc G W U S t p hp d hd
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  exact GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2

end GlobalTheory.RowReal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_eq_thetaLift_definiteGroup_form : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (h : GA D (Vc D i)) (w : (R.cV i).W), ∃ x : (R.HV i t).H, ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t x (fun ρ => u ρ) g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := by
  first | exact @GlobalTheory.TraceLift.exists_thF_eq_thetaKO | exact GlobalTheory.TraceLift.exists_thF_eq_thetaKO | (intros; apply GlobalTheory.TraceLift.exists_thF_eq_thetaKO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory

theorem funSub_evalExpand_exists {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] :
    ∃ (P : Finset X) (e : X → V), ∀ w ∈ W, w = ∑ x ∈ P, (w : X → ℂ) x • e x := by
  first
  | exact @_root_.GlobalTheory.FinsetKernelTrivial.main
  | exact _root_.GlobalTheory.FinsetKernelTrivial.main
  | (apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetKernelTrivial.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetKernelTrivial.main ..)

theorem funSub_multilinear_expand {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {N : Type} [AddCommMonoid N] [Module ℂ N]
    (Φ : MultilinearMap (RingHom.id ℂ) (fun i => V i) N) (P : ∀ i, Finset (X i))
    (e : ∀ i, X i → V i)
    (h : ∀ i, V i) (hh : ∀ i, h i = ∑ x ∈ P i, (h i : X i → ℂ) x • e i x) :
    Φ h = ∑ x ∈ Fintype.piFinset P, (∏ i, (h i : X i → ℂ) (x i)) • Φ (fun i => e i (x i)) := by
  conv_lhs => rw [show h = fun i => ∑ x ∈ P i, (h i : X i → ℂ) x • e i x from funext hh]
  rw [Φ.map_sum_finset]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Φ.map_smul_univ, RingHom.id_apply]

end GlobalTheory

namespace GlobalTheory

theorem funProd_multilinear_sum_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap (RingHom.id ℂ) (fun i => V i)
      (MultilinearMap (RingHom.id ℂ) (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  intro ι κ Δ _ _ _ _ X Y V V' M τ f f' g g' hfg
  classical
  let Wf : ∀ i, Submodule ℂ (V i) := fun i =>
    Submodule.span ℂ ((τ.support.image (fun d => f d i) ∪ τ.support.image (fun d => f' d i) :
      Finset (V i)) : Set (V i))
  let Wg : ∀ j, Submodule ℂ (V' j) := fun j =>
    Submodule.span ℂ ((τ.support.image (fun d => g d j) ∪ τ.support.image (fun d => g' d j) :
      Finset (V' j)) : Set (V' j))
  choose P e hP using fun i => funSub_evalExpand_exists (V i) (Wf i)
  choose Q e' hQ using fun j => funSub_evalExpand_exists (V' j) (Wg j)
  have key : ∀ (F : Δ → ∀ i, V i) (G : Δ → ∀ j, V' j),
      (∀ d ∈ τ.support, ∀ i, F d i ∈ Wf i) → (∀ d ∈ τ.support, ∀ j, G d j ∈ Wg j) →
      (τ.sum fun d a => a * M (F d) (G d)) =
        ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
          M (fun i => e i (x i)) (fun j => e' j (y j)) *
            τ.sum fun d a => a * (∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j) := by
    intro F G hF hG
    have hM : ∀ d ∈ τ.support, M (F d) (G d) = ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
        M (fun i => e i (x i)) (fun j => e' j (y j)) *
          ((∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j)) := by
      intro d hd
      rw [funSub_multilinear_expand M P e (F d) (fun i => hP i _ (hF d hd i))]
      rw [sum_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [smul_apply,
        funSub_multilinear_expand (M fun i => e i (x i)) Q e' (G d) (fun j => hQ j _ (hG d hd j)),
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [smul_eq_mul]; ring
    rw [Finsupp.sum]
    refine (Finset.sum_congr rfl (fun d hd => congrArg (τ d * ·) (hM d hd))).trans ?_
    simp_rw [Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  have memf : ∀ d ∈ τ.support, ∀ i, f d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memf' : ∀ d ∈ τ.support, ∀ i, f' d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  have memg : ∀ d ∈ τ.support, ∀ j, g d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memg' : ∀ d ∈ τ.support, ∀ j, g' d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  rw [key f g memf memg, key f' g' memf' memg']
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [hfg x y]

end GlobalTheory
end
