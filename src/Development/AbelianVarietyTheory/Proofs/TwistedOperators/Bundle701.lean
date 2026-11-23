module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle693
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPassPlaceModelsLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.isRowFlagTilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  first | exact @GlobalTheory.TiltUnique.tilt_unique | exact GlobalTheory.TiltUnique.tilt_unique | (intros; apply GlobalTheory.TiltUnique.tilt_unique <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_cellValue_of_steps_large_depth : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch → (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s := by
  first | exact @GlobalTheory.RowVal.valAt_big | exact GlobalTheory.RowVal.valAt_big | (intros; apply GlobalTheory.RowVal.valAt_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_heisenberg_combinations_joint_row_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  first | exact @GlobalTheory.RowCombGood.comb_good | exact GlobalTheory.RowCombGood.comb_good | (intros; apply GlobalTheory.RowCombGood.comb_good <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.vacuumDatum_trivialCombination_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  first | exact @GlobalTheory.VacComb.main | exact GlobalTheory.VacComb.main | (intros; apply GlobalTheory.VacComb.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.hasLocalLatticeMatrices_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x y : GA D (G.V (.grid D.R.m j)))
    (g g' : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj y g' → HasLoc t B hj (x * y) (fun w => g w * g' w) := by
  first | exact @GlobalTheory.RowVal.hasLoc_mul | exact GlobalTheory.RowVal.hasLoc_mul | (intros; apply GlobalTheory.RowVal.hasLoc_mul <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.iteratedInvariantIntegral_doubleCoset_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  first | exact @GlobalTheory.RowVal.niter_cellSum | exact GlobalTheory.RowVal.niter_cellSum | (intros; apply GlobalTheory.RowVal.niter_cellSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.rowTest_mem_latticeStabilizer_of_localMatrices : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t, ∀ j, 1 ≤ j → ∀ (hj : j ≤ D.R.m) (x : GA D (ch.G.V (.grid D.R.m j)))
    (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj x g → (∀ w, g w ∈ givenLevel ch.G t w.1 (D.R.m, j)) → x ∈ latGrp ch.G j := by
  first | exact @GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc | exact GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc | (intros; apply GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.unfoldedProductFunction_eq_of_local_identity : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  first | exact @GlobalTheory.LocAsm.unfolded_eq_of_local_eq | exact GlobalTheory.LocAsm.unfolded_eq_of_local_eq | (intros; apply GlobalTheory.LocAsm.unfolded_eq_of_local_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfoldingJointData_twist_ratio_at_detRoots : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t t' : T) (M M' : Vol ch.G) (hM : M.Is t) (hM' : M'.Is t') (P : PolDown ch.G) (h : Pts ch.G) (x : ℕ → (AE D)ˣ), (∀ k, IsDetRoot _ (h k) (x k)) → h D.R.m = 1 → ∀ j, Even j → j < D.R.m → conAt ch.W hM' (fockD ch.W t' (fun j => ch.rm.vT D.R.m j) P) h j = ((((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x j))⁻¹ * (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) • conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) h j := by
  first | exact @GlobalTheory.ConTwist.conAt_twist_big | exact GlobalTheory.ConTwist.conAt_twist_big | (intros; apply GlobalTheory.ConTwist.conAt_twist_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.BaseMoveAt

theorem val_of_reGL_eq_inv_diagGL {k : Type} [Field k] {a b : ℕ} (h : a = b) (Y : GL (Fin a) k) (c : Fin b → kˣ)
    (hY : GlobalTheory.StepData.reGL (finCongr h) Y = (GlobalTheory.SplitFlip.diagGL c)⁻¹) :
    (Y : Matrix (Fin a) (Fin a) k) = diagonal fun i => (((c (Fin.cast h i))⁻¹ : kˣ) : k) := by
  subst h
  have e : GlobalTheory.StepData.reGL (finCongr (rfl : a = a)) Y = Y := by
    ext i j
    simp [GlobalTheory.StepData.reGL]
  rw [e] at hY
  rw [hY]
  rfl

theorem submatrix_mulVec_comp {k : Type} [CommRing k] {m n ι : Type} [Fintype n] [Fintype ι] (M : Matrix m n k) (F : ι ≃ n)
    (y : n → k) : (M.submatrix id F) *ᵥ (fun i => y (F i)) = M *ᵥ y := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id]
  exact Fintype.sum_equiv F _ _ fun _ => rfl

end GlobalTheory.BaseMoveAt

namespace GlobalTheory.BaseMoveAt



theorem lat_moves_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → ∀ (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (t : T), t ∈ U → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ b : Pts G, IsBase t S.B b → ∀ w ∈ locPl G t, ∀ p : GlobalTheory.FinPl.SplitPt D (Kw w), Formalism.L2.NTheta.IsIdemAt p.e w → (∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a))) → ∀ x : Fin (G.V (.grid D.R.m 0)).rank → Kw w, ((fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = p.v) ↔ (fun i => p.sec (((Formalism.L2.Theta.mt _ (b 0)).map p.pr *ᵥ x) i)) ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = p.v)) := by
  intro D T L sc μ₀ hL hde G W U S t ht hc b hb w hw p hpw hpr x
  have h0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hpr' : ∀ a : D.host.E, p.pr (incA D a) = algebraMap D.host.E (Kw w) a := fun a =>
    (hpr _).trans (GlobalTheory.FunObj.Good.cpt_incA w a)
  have hN : (Formalism.L2.Theta.mt _ (b 0)).map p.pr =
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) := by
    ext i j
    rw [Matrix.map_apply, hpr]
    rfl
  obtain ⟨e, -, -, hloc⟩ := hb.1
  have hl := hloc ⟨w, hw⟩
  simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply] at hl
  have hY := val_of_reGL_eq_inv_diagGL _ _ _ hl
  simp only [Fin.coe_cast, topRank_eq G t w (Nat.zero_le _), map_mul, map_inv] at hY
  have hrow := S.row t ht w hw 0 h0
  unfold GlobalTheory.FunObj.IsSumFrame at hrow
  simp only [if_true] at hrow
  have hΛ : G.Λ (.grid D.R.m 0) = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m h0 le_rfl
  have hR : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    simp [GlobalTheory.RowShape.rowN, h0]

  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (G.V (.grid D.R.m 0)).rank → Kw w, δ = fun i =>
      ((((unifAt w) ^ (cosExp G w * (i.1 + 1 - (G.V (.top 0)).rank)))⁻¹ : (Kw w)ˣ) : Kw w) := ⟨_, rfl⟩
  have hcomm : ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) =
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) * diagonal δ := by
    rw [hδ, ← hY, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

  obtain ⟨s, hs⟩ : ∃ s : Fin (D.R.m - 1 - 0) → Kw w, s = fun r =>
      frameSign (Kw w) (D.R.m - 1 - 0) r * ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      M' = (fromCols (frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι) (G.rowDec 0 h0).a).map
        (fun a => p.pr (incA D a)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      Q = fromBlocks ((GlobalTheory.StdFrames.loc w (S.βp 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) 0 0 (diagonal s) := ⟨_, rfl⟩
  have hLb : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)).submatrix id
      (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank) = M' * Q := by
    have hM'' : M' = fromCols ((frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι).map
        (algebraMap D.host.E (Kw w))) ((G.rowDec 0 h0).a.map (algebraMap D.host.E (Kw w))) := by
      rw [hM']
      ext i j
      rcases j with j | j <;> simp [hpr']
    rw [hrow, hM'', hQ, fromCols_mul_fromBlocks, hs]
    simp only [Matrix.mul_zero, add_zero, zero_add]

  have hδl : ∀ i, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inl i)) = 1 := by
    intro i
    have hi : i.1 + 1 - (G.V (.top 0)).rank = 0 := by have := i.2; omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hδr : ∀ r, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inr r)) =
      ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1)))⁻¹ := by
    intro r
    have hi : (G.V (.top 0)).rank + r.1 + 1 - (G.V (.top 0)).rank = r.1 + 1 := by omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hQc : Q * diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) =
      diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) * Q := by
    ext i j
    rw [mul_diagonal, diagonal_mul, hQ]
    rcases i with i | i <;> rcases j with j | j
    · simp [hδl]
    · simp
    · simp
    · by_cases h : i = j
      · subst h; exact mul_comm _ _
      · simp [diagonal_apply, h]
  obtain ⟨z, hx, hNx⟩ : ∃ z, M' *ᵥ z = x ∧
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x =
        M' *ᵥ (diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ z) := by
    obtain ⟨y, hy⟩ : ∃ y : Fin (G.V (.grid D.R.m 0)).rank → Kw w, y = (((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0))⁻¹ : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x := ⟨_, rfl⟩
    have hxy : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ y = x := by
      rw [hy, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨Q *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i), ?_, ?_⟩
    · rw [mulVec_mulVec, ← hLb, submatrix_mulVec_comp, hxy]
    · rw [← hxy, mulVec_mulVec, hcomm, ← mulVec_mulVec, ← submatrix_mulVec_comp _ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank), hLb]
      have hv : (fun i => (diagonal δ *ᵥ y) (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i)) =
          diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i) := by
        funext i
        simp [mulVec_diagonal]
      rw [hv]
      simp only [mulVec_mulVec]
      rw [Matrix.mul_assoc, hQc]

  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have h3 := GlobalTheory.FunObj.ne_zero_of_conj h2.1 h2.2
  have h1' := GlobalTheory.FunObj.ne_zero_of_conj h1.1 h1.2
  have hA := GlobalTheory.FunObj.count_AA_AAbar w (GlobalTheory.FunObj.Good.badInt_notMem hL hde hc hw)
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [GlobalTheory.ChiGrid.Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  have hI1 : ∀ r, stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r ≠ 0 := fun r =>
    mul_ne_zero (pow_ne_zero _ h2.1) (inv_ne_zero (pow_ne_zero _ h3))
  have hn1 : ∀ r : Fin (D.R.m - 1 - 0), FractionalIdeal.count D.host.E w
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r) = ((cosExp G w * (r.1 + 1) : ℕ) : ℤ) := by
    intro r
    rw [GlobalTheory.FunObj.count_stairId h2.1 h3, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar,
      FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ h1' (inv_ne_zero hmo),
      FractionalIdeal.count_inv, FractionalIdeal.count_inv, GlobalTheory.FunObj.count_modulBar G hw, GlobalTheory.FunObj.count_modul, hA.1, hA.2]
    push_cast
    ring
  have hrId : ∀ r, GlobalTheory.RowShape.rowId D 0 r = stairId D.host.AA D.host.AAbar (D.R.m - 1 - 0) r := by
    intro r
    simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc]
  have hI2 : ∀ r, GlobalTheory.RowShape.rowId D 0 r ≠ 0 := fun r => by
    rw [hrId]
    exact mul_ne_zero (pow_ne_zero _ h1.1) (inv_ne_zero (pow_ne_zero _ h1'))
  have hn2 : ∀ r, FractionalIdeal.count D.host.E w (GlobalTheory.RowShape.rowId D 0 r) = ((0 : ℕ) : ℤ) := by
    intro r
    rw [hrId, GlobalTheory.FunObj.count_stairId h1.1 h1', hA.1, hA.2]
    simp
  have hϖ := GlobalTheory.SplitFlip.IsUnif.irreducible (isUnif_unifAt w)
  rw [hN, hNx]
  subst hx
  subst hM'
  rw [hΛ, hR, GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero),
    GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero)]
  simp only [mulVec_diagonal, hδl, one_mul, hδr]
  refine and_congr Iff.rfl (forall_congr' fun r => ?_)
  rw [GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI1 r) (hn1 r), GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI2 r) (hn2 r)]
  have hq : ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [ho, pow_zero, one_mul, ← mul_assoc]
    exact (inv_mul_cancel₀ hq).symm ▸ (one_mul _)
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [pow_zero, one_mul] at ho
    rw [← ho, ← mul_assoc]
    exact ((mul_inv_cancel₀ hq).symm ▸ (one_mul _)).symm

end GlobalTheory.BaseMoveAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.fockVectors_pass_placeModels_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D) (v f : SchDown ch.G t) (P : PolDown ch.G) (j : Fin D.R.m) (φ : WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ), IsThetaFunO ch.W.ψ _ _ (v j) → IsLocVec ch.W (.mu t D.R.m j) e (v j) φ (f j) → IsThetaFunO ch.W.ψ _ _ (fockD ch.W t v P j) ∧ IsLocVec ch.W (.mu t D.R.m j) e (fockD ch.W t v P j) φ (fockD ch.W t f P j) := by
  first | exact @GlobalTheory.FockPlace.main | exact GlobalTheory.FockPlace.main | (intros; apply GlobalTheory.FockPlace.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_combination_depends_on_product_function : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 := by
  first | exact @GlobalTheory.CombDet.comb_det | exact GlobalTheory.CombDet.comb_det | (intros; apply GlobalTheory.CombDet.comb_det <;> assumption)
end
