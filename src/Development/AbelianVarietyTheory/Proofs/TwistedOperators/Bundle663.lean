module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle657
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle591
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

section FockAll

open Classical

variable {D : D7}

def fockSubOn {m n : ℕ} (s : Finset D.what₂.Tau) (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    if y.1 ∈ s then
      ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
        else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)
    else MvPolynomial.X y

variable {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)

theorem fockSubOn_empty (Q : MvPolynomial (FVar D m n) ℂ) : fockSubOn ∅ pS pT κS κT Q = Q := by
  have e : fockSubOn (∅ : Finset D.what₂.Tau) pS pT κS κT = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [fockSubOn, MvPolynomial.aeval_X, Finset.notMem_empty, if_false, AlgHom.id_apply]
  rw [e, AlgHom.id_apply]

theorem fockSubOn_univ : fockSubOn Finset.univ pS pT κS κT = fockSubAll pS pT κS κT := by
  apply MvPolynomial.algHom_ext
  intro y
  simp only [fockSubOn, fockSubAll, MvPolynomial.aeval_X, Finset.mem_univ, if_true]

theorem fockSub_fockSubOn {τ : D.what₂.Tau} {s : Finset D.what₂.Tau} (hτ : τ ∉ s) (Q : MvPolynomial (FVar D m n) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ) (fockSubOn s pS pT κS κT Q) =
      fockSubOn (insert τ s) pS pT κS κT Q := by
  suffices e : (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ)).comp (fockSubOn s pS pT κS κT) =
      fockSubOn (insert τ s) pS pT κS κT from DFunLike.congr_fun e Q
  apply MvPolynomial.algHom_ext
  intro y
  rw [AlgHom.comp_apply]
  by_cases hy : y.1 ∈ s
  · have hne : y.1 ≠ τ := fun h => hτ (h ▸ hy)

    simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_true, or_true,
    map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hne, if_false]
  · by_cases h2 : y.1 = τ
    · obtain ⟨ρ, a, b⟩ := y
      simp only at h2 hy
      subst h2
      simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_false, true_or,
        if_true]
    · simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, h2, if_false,
        or_false]

theorem om_pureTensorO_compact_all (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.OmT S T) (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (hpS : ∀ ρ, pS ρ ≤ S.rank) (hpT : ∀ ρ, pT ρ ≤ T.rank)
    (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
    (hBS : ∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) (hBT : ∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hvac : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f)
    (κS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (κT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hκS : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) (hκT : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ))
    (x : GA D S) (y : GA D T) (hx : x ∈ GinfC S) (hy : y ∈ GinfC T)
    (hxc : ∀ ρ, compAt θ ρ (mt S x) = BS ρ * κS ρ * (BS ρ)⁻¹)
    (hyc : ∀ ρ, compAt θ ρ (mt T y) = BT ρ * κT ρ * (BT ρ)⁻¹)
    (c : ℂ) (hc : om (x, y) f = c • f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      c • pureTensorO ψ θ S T sS sT BS BT f (fockSubAll pS pT κS κT Q) := by
  have hUS : ∀ ρ, compAt θ ρ (mt S x) ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S x ρ
  have hUT : ∀ ρ, compAt θ ρ (mt T y) ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ T y ρ
  have hAS : ∀ τ, IsAtTau θ S τ (BS τ * κS τ * (BS τ)⁻¹) (atTau θ S τ (compAt θ τ (mt S x))) := fun τ => by
    rw [← hxc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (hUS τ)
  have hAT : ∀ τ, IsAtTau θ T τ (BT τ * κT τ * (BT τ)⁻¹) (atTau θ T τ (compAt θ τ (mt T y))) := fun τ => by
    rw [← hyc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ (hUT τ)
  have hev : ∀ τ, ∃ e : ℂ, om (atTau θ S τ (compAt θ τ (mt S x)), atTau θ T τ (compAt θ τ (mt T y))) f = e • f :=
    fun τ => by
      obtain ⟨mS, mT, h⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
      exact ⟨_, h sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf hvac (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ)⟩
  choose e he using hev
  let MSs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt S x) else 1
  let MTs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt T y) else 1
  have hUSs : ∀ s ρ, MSs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MSs, if_pos h]; exact hUS ρ
    · simp only [MSs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have hUTs : ∀ s ρ, MTs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MTs, if_pos h]; exact hUT ρ
    · simp only [MTs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have key : ∀ s : Finset D.what₂.Tau, ∀ Q, om (realAll θ S (MSs s), realAll θ T (MTs s)) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      (∏ τ ∈ s, e τ) • pureTensorO ψ θ S T sS sT BS BT f (fockSubOn s pS pT κS κT Q) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro Q
      have h1 : MSs ∅ = 1 := by funext ρ; simp [MSs]
      have h2 : MTs ∅ = 1 := by funext ρ; simp [MTs]
      rw [h1, h2, realAll_one hθ, realAll_one hθ, Prod.mk_one_one, map_one, Module.End.one_apply, Finset.prod_empty,
        one_smul, fockSubOn_empty]
    · intro τ s hτ ih Q
      have eS : realAll θ S (MSs (insert τ s)) = atTau θ S τ (compAt θ τ (mt S x)) * realAll θ S (MSs s) := by
        rw [realAll_eq_atTau_mul hθ (hUSs (insert τ s)) τ]
        congr 2
        · simp [MSs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MSs, hτ]
          · simp [MSs, Function.update_of_ne h, h]
      have eT : realAll θ T (MTs (insert τ s)) = atTau θ T τ (compAt θ τ (mt T y)) * realAll θ T (MTs s) := by
        rw [realAll_eq_atTau_mul hθ (hUTs (insert τ s)) τ]
        congr 2
        · simp [MTs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MTs, hτ]
          · simp [MTs, Function.update_of_ne h, h]
      rw [eS, eT, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih Q, map_smul,
        GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf τ
          (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ) (e τ) (he τ),
        smul_smul, fockSub_fockSubOn pS pT κS κT hτ, Finset.prod_insert hτ, mul_comm (e τ)]
  have hxr : realAll θ S (MSs Finset.univ) = x :=
    realAll_eq hθ (hUSs _) ⟨hx, fun ρ => by simp only [MSs, Finset.mem_univ, if_true]; rfl⟩
  have hyr : realAll θ T (MTs Finset.univ) = y :=
    realAll_eq hθ (hUTs _) ⟨hy, fun ρ => by simp only [MTs, Finset.mem_univ, if_true]; rfl⟩
  have hall := key Finset.univ
  rw [hxr, hyr, fockSubOn_univ] at hall
  have hE : om (x, y) f = (∏ τ, e τ) • f := by
    have h1 := hall 1
    rw [map_one (fockSubAll pS pT κS κT)] at h1
    simpa only [GlobalTheory.FiniteFock.pureTensorO_one] using h1
  rw [hall Q]
  by_cases hf0 : f = 0
  · subst hf0
    have z : ∀ P, pureTensorO ψ θ S T sS sT BS BT 0 P = 0 := fun P => by
      have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
      rwa [zero_smul, zero_smul] at this
    simp only [z, smul_zero]
  · have hce : c = ∏ τ, e τ := smul_left_injective ℂ hf0 (hc.symm.trans hE)
    rw [hce]

end FockAll

theorem om_fock_compact_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  intro D T L sc G W p hp pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT x y hx hy hxc hyc c hc Q
  exact om_pureTensorO_compact_all D W.ψ W.θ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (W.om p) (W.om_is p hp) W.θ_is
    (G.cartS W.cart p) (G.onS W.onb p) (G.onT W.cart p) (G.onT W.onb p) pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT
    x y hx hy hxc hyc c hc Q

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

theorem mul_adaptedFrame_of_blocks {N r c N' : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (F : Matrix (Fin N) (Fin r) ℂ)
    (O Mmm : Matrix (Fin r) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (y : Matrix (Fin c) (Fin c) ℂ)
    (hr : r = c) (hc : c + 1 = N') (hN : N = N') (hO : IsUnit O.det)
    (h1 : A * F = F * Mmm) (h2 : Mmm = O * y.submatrix (Fin.cast hr) (Fin.cast hr) * O⁻¹) (h3 : A * Zc = Zc) :
    A * Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) =
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) *
      (Matrix.reindex (finSumFinEquiv.trans (finCongr hc)) (finSumFinEquiv.trans (finCongr hc))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast hN) (Fin.cast hN) := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have hK : (Matrix.reindex (e.trans (finCongr rfl)) (e.trans (finCongr rfl))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast rfl) (Fin.cast rfl) =
      (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm := by
    ext a k
    simp [Matrix.reindex_apply]
  rw [hT, hK, Matrix.submatrix_mul_equiv]
  have hL : A * (Matrix.fromCols (F * O) Zc).submatrix id e.symm = (A * Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    rfl
  rw [hL, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, h3]
  congr 2
  · rw [← Matrix.mul_assoc, h1, h2]
    simp only [Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.mul_zero, add_zero, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hO, Matrix.mul_one]
    congr 2
  · simp

theorem ptTop_inOnb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  intro D T L sc G μ0 hL W g n hn τ
  by_cases h : (n : ℕ) < D.R.m
  · have hP : PosOnb W (.top (⟨n, h⟩ : Fin D.R.m)) := posOnb_of_defNode W μ0 hL (X := .top (⟨n, h⟩ : Fin D.R.m)) h.le
    have hd : IsUnit (W.onb (.top (⟨n, h⟩ : Fin D.R.m)) τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
    have e1 := compAt_kappa_fst g ⟨n, h⟩ hP τ
    have e2 : ∀ k : Fin D.R.m, (rowComp (rowSizes D) g (Fin.castSucc k) τ).1 = (g.1 k τ).1 := fun k => by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact congrArg (fun x => (x τ).1) (Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j))
        (embed (rowSizes D).nC_succ (g.2 (Fin.last _))) g.1 k)
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, n = Fin.castSucc k := ⟨⟨n, h⟩, Fin.ext rfl⟩
    rw [ptTop_lt W g h]
    erw [e1]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    erw [e2 k]
    rfl
  · have hm : (n : ℕ) = D.R.m := by have := n.2; omega
    obtain rfl : n = Fin.last D.R.m := Fin.ext hm
    have hF := hn rfl
    have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
    have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
    have hdT : IsUnit (topFrame W τ).det := by
      rw [← hF τ]; exact Matrix.isUnit_det_of_left_inverse (hPt τ)
    have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
    have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
          compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
    have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
        G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
    have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
        W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
          (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
      compAt_kappa_snd g (Fin.last D.R.m) hPg τ
    have hA := mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
      ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
      (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3
    have key : (topFrame W τ)⁻¹ * compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ =
        (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
          (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
      have hA' : compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
          (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
            (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := hA
      rw [Matrix.mul_assoc, hA', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdT, Matrix.one_mul]
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]; exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast, hF τ]
    exact key

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

namespace GlobalTheory.RowReal

theorem sum_conjSub_cast {ι : Type} {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (U : Matrix (Fin a') (Fin a') ℂ)
    (V : Matrix (Fin b') (Fin b') ℂ) (hV : star V * V = 1) (τ : ι) (p : Fin a) (q : Fin b) :
    ∑ x : Fin a, ∑ y : Fin b, MvPolynomial.C ((starRingEnd ℂ) (U.submatrix (Fin.cast ha) (Fin.cast ha) x p) *
        (starRingEnd ℂ) ((V.submatrix (Fin.cast hb) (Fin.cast hb))⁻¹ q y)) *
        (MvPolynomial.X (τ, Fin.cast hb y, Fin.cast ha x) : MvPolynomial (ι × Fin b' × Fin a') ℂ) =
      ∑ x : Fin b', ∑ y : Fin a', MvPolynomial.C ((V ⊗ₖ (star U)ᵀ) (x, y) (Fin.cast hb q, Fin.cast ha p)) *
        MvPolynomial.X (τ, x, y) := by
  subst ha hb
  have e : ∀ {n : ℕ} (h : n = n) (M : Matrix (Fin n) (Fin n) ℂ), M.submatrix (Fin.cast h) (Fin.cast h) = M := fun _ _ => by
    ext; simp
  simp only [e, Fin.cast_eq_self]
  rw [Matrix.inv_eq_left_inv hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 2
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def, RingHomCompTriple.comp_apply,
    RingHom.id_apply, Complex.conj_conj]
  ring

theorem trRow_fockSubAll : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  intro D T L sc G i u v Q
  have hL : ∀ P, linSub (homMat _ _ (u, v)) P = MvPolynomial.aeval (R := ℂ) (fun p : D.what₂.Tau × (Fin ((rowSizes D).nC (i + 1)) × Fin ((rowSizes D).nC i)) => ∑ j, MvPolynomial.C ((homMat _ _ (u, v)) p.1 j p.2) * (MvPolynomial.X (p.1, j) : MvPolynomial _ ℂ)) P := fun _ => rfl
  rw [hL, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, p, q⟩

  simp only [AlgHom.comp_apply, fockSubAll, trRow, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_mul, MvPolynomial.rename_C, Fintype.sum_prod_type]
  have hc : ¬ ((p : ℕ) < (G.V (.grid i D.R.m)).rank ↔ (q : ℕ) < 0) := by simp [p.2]
  simp only [if_neg hc]
  have hH : ∀ τ', homMat _ _ (u, v) τ' = ((v τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) ⊗ₖ (star ((u τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ))ᵀ := fun _ => rfl
  simp only [hH]
  exact sum_conjSub_cast _ _ _ _ (v τ).2.1 τ p q

end GlobalTheory.RowReal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem fockSubAll_rename_unitary {D : D7} {m n a b : ℕ} (ha : n = a) (hb : m = b)
    (u : UG D.what₂.Tau a) (v : UG D.what₂.Tau b) (Q : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2))
      (fockSubAll (fun _ => n) (fun _ => m)
        (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast ha) (Fin.cast ha))
        (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast hb) (Fin.cast hb)) Q) =
      linSub (homMat a b (u, v))
        (MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2)) Q) := by
  subst ha hb
  have hinv : ∀ τ, ((u τ : Matrix (Fin n) (Fin n) ℂ))⁻¹ = star (u τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 (u τ).2)
  have hc : ∀ k : ℕ, (Fin.cast (rfl : k = k)) = id := fun k => by funext i; rfl
  rw [hc, hc]
  have hid : (fun x : FVar D m n => (x.1, (id x.2.1 : Fin m), (id x.2.2 : Fin n))) = id := rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply, AlgHom.id_apply]
  have hs : ∀ k (M : Matrix (Fin k) (Fin k) ℂ), M.submatrix id id = M := fun _ _ => rfl
  simp only [hs]
  show _ = (MvPolynomial.aeval (R := ℂ) fun p : D.what₂.Tau × (Fin m × Fin n) => ∑ j, MvPolynomial.C ((homMat n m (u, v)) p.1 j p.2) *
    (MvPolynomial.X (p.1, j) : MvPolynomial (D.what₂.Tau × (Fin m × Fin n)) ℂ)) Q
  refine DFunLike.congr_fun ?_ Q
  refine MvPolynomial.algHom_ext fun y => ?_
  obtain ⟨τ, p, q⟩ := y
  simp only [fockSubAll, MvPolynomial.aeval_X, hinv, homMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Fin.is_lt, iff_self, if_true, Matrix.transpose_apply, Matrix.star_apply]

theorem trCol_fockSubAll_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  intro D T L sc G j u v Q
  exact fockSubAll_rename_unitary _ _ u v Q

end GlobalTheory.RowReal
end
