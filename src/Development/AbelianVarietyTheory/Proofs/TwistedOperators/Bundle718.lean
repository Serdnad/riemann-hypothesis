module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle695
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle697
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle699
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle711
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensors
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLaw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle716
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle715
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowShape

theorem moves_of_forall {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (hL : Submodule.IsLattice D.host.E L)
    (hM : Submodule.IsLattice D.host.E M) (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L M (· = v)) :
    GlobalTheory.FinPl.Moves S g L M (fun _ => True) := by
  intro y hy
  have hT := fun (N : GlobalTheory.FinPl.Lat S) (hN : Submodule.IsLattice D.host.E N) (z : Fin S.rank → AE D) =>
    ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 N z hN
  have hmy : ∀ i, (Formalism.L2.Theta.mt S g *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [hT L hL y, hT M hM _]
  refine ⟨fun ⟨_, h2⟩ => ⟨hmy, fun v _ e he => ?_⟩, fun ⟨_, h2⟩ => ⟨hy, fun v _ e he => ?_⟩⟩
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    have := (h v (e • y) hs).1 (h2 v trivial e he)
    rwa [Matrix.mulVec_smul] at this
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    refine (h v (e • y) hs).2 ?_
    rw [Matrix.mulVec_smul]
    exact h2 v trivial e he

theorem moves0_of_selfDual : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G 0) → ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hN t b hb
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc := hch.guard t
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hΛ : IsSelfDualC _ (ch.G.Λ (.grid D.R.m 0)) :=
    (ch.G.isV (X := .grid D.R.m 0) ⟨le_rfl, Nat.zero_le _⟩ (fun j e => by injection e with h1 h2; omega)).sd
  apply moves_of_forall _ _ _ _ hΛ.1 hN.1
  intro v
  classical
  by_cases hv : ∃ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) = v
  · obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨e, ⟨⟨es, hes, -⟩, -⟩, -, -⟩ := hb.1
    obtain ⟨p, hpe, hpv, hpr⟩ := GlobalTheory.T.exists_cmSplitPoint_at_place_over_split D w (es w) (hes w hw) s.hF
    have key := GlobalTheory.T.gridBasePoint_carries_lattice_to_movedLattice hL hde ch.G ch.W Set.univ ch.S.toGridChoice t trivial hc b hb w hw p (hpe ▸ hes w hw) hpr
    rw [← hpv, ← GlobalTheory.Core.Mi.LatMatch.sMoves_one]
    refine GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D _ p _ _ _ 1 (b 0) hΛ hN (GlobalTheory.Core.Mi.LatMatch.normOneAt_one _) fun x => ?_
    rw [map_one, one_smul]
    exact key x
  · push_neg at hv
    have hv0 : v ∉ ch.G.pl.S0 := fun h0 => hv (ch.G.pl.w v)
      (Finset.mem_union_left _ (by simpa [Places.W0] using ⟨v, h0, rfl⟩)) (ch.G.pl.under_w h0)
    intro y hy
    rw [GlobalTheory.T.gridBasePoint_trivial_offTensorPlaces ch.G t ch.S.B b hb v hv y hy]
    exact GlobalTheory.T.lattice_off_S0_last_level_iff ch.G v hv0 y hy

theorem moves0 : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True :=
  big_mono (fun _ h => h.1 (h.2 0 (Nat.zero_le _))) (Big.and moves0_of_selfDual GlobalTheory.T.isSelfDual_gridRowMovedLattice_largeDepth)

end GlobalTheory.RowShape
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.rowTest_tupleTerm_measures_differ_by_scalars : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (M M' : Vol ch.G), M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
    ∃ x : Node → ℝ≥0, Scales M M' x ∧
      ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → x X = 1 := by
  first | exact @GlobalTheory.TermScales.exists_scales | exact GlobalTheory.TermScales.exists_scales | (intros; apply GlobalTheory.TermScales.exists_scales <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flippedFiniteTensor_sum_prod_local_pure_tensors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (β : CosFam ch.G t) (e : AE D), IsIdemSum e (locPl ch.G t) → ∃ (α : Type) (SA : Finset α) (xA : α → ℂ) (φ : α → (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fd : α → SchDown ch.G t) (fr : α → SchRow ch.G), (∀ a ∈ SA, ∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ a w b)) ∧ (∀ a ∈ SA, (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd a j)) ∧ (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr a i))) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → ∏ w, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ a ∈ SA, xA a * ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ a w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  first | exact @GlobalTheory.LocAsm.flipFin_productExpansion | exact GlobalTheory.LocAsm.flipFin_productExpansion | (intros; apply GlobalTheory.LocAsm.flipFin_productExpansion <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFlatLaws

theorem flatS_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y _ f hf
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  refine ⟨fun N hN => ?_, fun ξ => ?_⟩
  · exact GlobalTheory.FlatShiftPf.flatAt_shift hψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν s.vU.unit.1 _ _ f N hN
  · exact GlobalTheory.FlatLawsDuality.flatAt_iso dV dW s.vS s.vT s.vU.ν _ _ hψ f hf ξ

end GlobalTheory.AscFlatLaws

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, AddMonoidAlgebra.coeff u.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.colMap d (ch.S.ptTop c) u).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.ColField.colMap_coeff_mem | exact GlobalTheory.RowTest.ColField.colMap_coeff_mem | (intros; apply GlobalTheory.RowTest.ColField.colMap_coeff_mem <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.flatMap_heisenberg_and_hom_transformation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  first | exact @GlobalTheory.AscFlatLaws.flatS_laws | exact GlobalTheory.AscFlatLaws.flatS_laws | (intros; apply GlobalTheory.AscFlatLaws.flatS_laws <;> assumption)

end
end
