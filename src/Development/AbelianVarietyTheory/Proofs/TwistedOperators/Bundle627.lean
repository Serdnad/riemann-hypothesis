module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle335
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle169
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle546
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle329
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowVertex

open GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def firstIx (D : D7) : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩

def rowShift0 (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)) :
    (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (firstIx D) D.R.m) (G.toPair (.chi (firstIx D) D.R.m)
    ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)

theorem rowShift0_theta (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    {f : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ}
    (h : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (rowShift0 S k f) :=
  (W.om_is _ (inRange_chi (firstIx D))).om_pres _ _ h

def movedRow (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) :
    ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ :=
  Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D)))

theorem rowMapV_update_zero (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid 0 D.R.m))
    (hg : IsThetaFunO W.ψ (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) (gs (firstIx D))) :
    rowMapV S gs (Function.update y 0 (y 0 * k)) = rowMapV S (movedRow S k gs) y := by
  unfold rowMapV movedRow
  refine congrArg (fun F => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) F D.R.m) _) ?_
  funext i
  by_cases hi : i < D.R.m
  · simp only [dif_pos hi]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [Function.update_self, Function.update_of_ne (show (0 + 1 : ℕ) ≠ 0 by omega)]
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨0, hi⟩ = rowShift0 S k (gs (firstIx D)) :=
        Function.update_self _ _ _
      have hm : y 0 * k * S.N.u (.grid 0 D.R.m) =
          (y 0 * S.N.u (.grid 0 D.R.m)) * ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)) := by group
      rw [hu, hm]
      exact congrArg _ (GlobalTheory.KerTrans.fockComp_mul_fin W S.N.frC (inRange_chi (firstIx D)) _ hg _ _ _)
    · have h2 : (⟨i, hi⟩ : Fin D.R.m) ≠ firstIx D := by
        intro h; have := congrArg Fin.val h; simp [firstIx] at this; omega
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨i, hi⟩ = gs ⟨i, hi⟩ :=
        Function.update_of_ne h2 _ _
      have hy1 : Function.update y 0 (y 0 * k) i = y i := Function.update_of_ne (by omega) _ _
      have hy2 : Function.update y 0 (y 0 * k) (i + 1) = y (i + 1) := Function.update_of_ne (by omega) _ _
      rw [hu, hy1, hy2]
  · simp only [dif_neg hi]

theorem prod_update_smul {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (F : ∀ i, X i → ℂ) (i₀ : ι) (h : X i₀ → ℂ)
    (c : ℂ) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (c • h) i (ys i) = c * ∏ i, Function.update F i₀ h i (ys i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end GlobalTheory.FirstRowVertex

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockFrameChange

private theorem sum4_lemma {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := by
  calc ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k, ∑ k', ∑ l, ∑ l', f k l k' l' :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l, ∑ l', f k l k' l' := Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l', ∑ l, f k l k' l' :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := Finset.sum_congr rfl fun k' _ => Finset.sum_comm

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) =
      GlobalTheory.CompactHowe.substF (fun τ => h τ * h' τ) (fun τ => g τ * g' τ) P := by
  unfold GlobalTheory.CompactHowe.substF
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun F => (MvPolynomial.aeval F) P) (funext fun p => ?_)
  obtain ⟨τ, a, b⟩ := p

  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine (sum4_lemma _).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem change_mul {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) : F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * M * F * (F⁻¹ * A) := by
  calc F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * (A * A⁻¹) * M * A := by simp only [Matrix.mul_assoc]
    _ = F⁻¹ * M * A := by rw [hA, Matrix.mul_one]
    _ = F⁻¹ * M * (F * F⁻¹) * A := by rw [hF, Matrix.mul_one]
    _ = F⁻¹ * M * F * (F⁻¹ * A) := by simp only [Matrix.mul_assoc]

theorem change_mul_invT {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ((F⁻¹ * A)⁻¹).transpose * ((A⁻¹ * M * A)⁻¹).transpose = ((F⁻¹ * M * F)⁻¹).transpose * ((F⁻¹ * A)⁻¹).transpose := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev (F⁻¹ * A) (A⁻¹ * M * A),
    ← Matrix.mul_inv_rev (F⁻¹ * M * F) (F⁻¹ * A), change_mul hA hF M]

theorem subst_change {ι : Type} {N n : ℕ} {A F : ι → Matrix (Fin N) (Fin N) ℂ} {A' F' : ι → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ τ, A τ * (A τ)⁻¹ = 1) (hF : ∀ τ, F τ * (F τ)⁻¹ = 1) (hA' : ∀ τ, A' τ * (A' τ)⁻¹ = 1)
    (hF' : ∀ τ, F' τ * (F' τ)⁻¹ = 1) (M : ι → Matrix (Fin N) (Fin N) ℂ) (M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
                 (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ))
                 (GlobalTheory.CompactHowe.substF (fun τ => ((A τ)⁻¹ * M τ * A τ).map (starRingEnd ℂ))
                   (fun τ => ((((A' τ)⁻¹ * M' τ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) =
      GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * M τ * F τ).map (starRingEnd ℂ))
        (fun τ => ((((F' τ)⁻¹ * M' τ * F' τ)⁻¹).transpose).map (starRingEnd ℂ))
        (GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  rw [substF_mul, substF_mul]
  exact congrArg₂ (fun h g => GlobalTheory.CompactHowe.substF h g P)
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul (hA τ) (hF τ)])
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul_invT (hA' τ) (hF' τ)])

theorem map_mul_inv {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (g : GL (Fin n) E) :
    g.1.map φ * (g.1.map φ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h := (Matrix.isUnits_det_units g).map φ
  rw [RingHom.map_det] at h
  exact h

private theorem fock_frame_lemma {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS A' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT A : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hBS : ∀ τ, BS τ * (BS τ)⁻¹ = 1) (hBT : ∀ τ, BT τ * (BT τ)⁻¹ = 1)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) A' A f P =
      pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f
        (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((BS τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  have e1 : A' = fun τ => BS τ * ((BS τ)⁻¹ * A' τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBS τ, Matrix.one_mul]
  have e2 : A = fun τ => BT τ * ((BT τ)⁻¹ * A τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBT τ, Matrix.one_mul]
  conv_lhs => rw [e1, e2]
  exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ S T hψ hθ BS (fun τ => (BS τ)⁻¹ * A' τ) BT
    (fun τ => (BT τ)⁻¹ * A τ) f hf P

theorem exists_frame_change : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ σ₀ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank,
      (∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d → ∀ P,
        W.fock (.chi i D.R.m) (S.Z.vec d) P = fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d) (σ₀ P)) ∧
      ∀ k : GA D (G.V (.grid i D.R.m)), k ∈ GinfC (G.V (.grid i D.R.m)) →
        ∀ k' : GA D (G.V (.grid (i + 1) D.R.m)), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) → ∀ P,
          σ₀ (realSubst W W.onb (.chi i D.R.m) k k' P) = realSubst W S.N.frC (.chi i D.R.m) k k' (σ₀ P) := by
  intro D T L sc G W U S μ0 hL i hi
  have hdT : DefNode D.R.m (Node.grid i D.R.m) := by
    unfold DefNode
    exact ⟨hi.le, rfl⟩
  have hdS : DefNode D.R.m (Node.grid (i + 1) D.R.m) := by
    unfold DefNode
    exact ⟨hi, rfl⟩
  have hdP : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := by
    unfold DefPair
    exact ⟨hi, rfl⟩
  have honb : ∀ X, DefNode D.R.m X → ∀ τ, W.onb X τ * (W.onb X τ)⁻¹ = 1 := fun X hX τ =>
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ))
  have hfr : ∀ X τ, S.N.frC X τ * (S.N.frC X τ)⁻¹ = 1 := fun X τ => map_mul_inv (tauE D τ) (S.N.fr X)
  refine ⟨(GlobalTheory.CompactHowe.substF
      (fun τ => ((S.N.frC (Node.grid i D.R.m) τ)⁻¹ * W.onb (Node.grid i D.R.m) τ).map (starRingEnd ℂ))
      (fun τ => ((((S.N.frC (Node.grid (i + 1) D.R.m) τ)⁻¹ * W.onb (Node.grid (i + 1) D.R.m) τ)⁻¹).transpose).map
        (starRingEnd ℂ))).toLinearMap, ?_, ?_⟩
  · intro t _ d hd P
    have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hdP d hd).1
    have hcS : G.cartS W.cart (Pair.chi i D.R.m : Pair T) = fun _ => -1 := by
      funext τ
      show -W.cart (Node.grid (i + 1) D.R.m) τ = -1
      rw [GlobalTheory.FockReal.cart_def hL W hdS τ]
    have hcT : G.onT W.cart (Pair.chi i D.R.m : Pair T) = fun _ => 1 := by
      funext τ
      exact GlobalTheory.FockReal.cart_def hL W hdT τ
    unfold GlobalTheory.ChiGrid.GridData.Weil.fock GlobalTheory.FunObj.fockIn
    rw [hcS, hcT, AlgHom.toLinearMap_apply]
    exact fock_frame_lemma W.ψ W.θ (G.V (Node.grid (i + 1) D.R.m)) (G.V (Node.grid i D.R.m)) W.ψ_std W.θ_is
      (S.N.frC (Node.grid (i + 1) D.R.m)) (W.onb (Node.grid (i + 1) D.R.m))
      (S.N.frC (Node.grid i D.R.m)) (W.onb (Node.grid i D.R.m))
      (hfr _) (hfr _) (S.Z.vec d) hf P
  · intro k _ k' _ P
    unfold GlobalTheory.FockReal.realSubst
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    exact subst_change (A := W.onb (Node.grid i D.R.m)) (F := S.N.frC (Node.grid i D.R.m))
      (A' := W.onb (Node.grid (i + 1) D.R.m)) (F' := S.N.frC (Node.grid (i + 1) D.R.m))
      (fun τ => honb _ hdT τ) (hfr _) (fun τ => honb _ hdS τ) (hfr _) _ _ P

end GlobalTheory.FockFrameChange

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

def conjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp ω

theorem conjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    conjRep ω p F = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (ω p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F)) := rfl

def adjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep T S :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint (conjRep ω)

theorem adjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (h : GA D T) (g : GA D S) (F : WO T S → ℂ) :
    adjRep ω (h, g) F = fun y => ω (g, h) (fun x => F (adjO T S x)) (adjO S T y) := by
  funext y
  show starRingEnd ℂ (starRingEnd ℂ (ω (g, h) (fun x => starRingEnd ℂ (starRingEnd ℂ (F (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x))))
    (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S y))) = _
  simp only [Complex.conj_conj, GlobalTheory.ConjAdjWeil.dagger_eq]


open GlobalTheory.FockAdjoint in
def swapHom {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank →ₐ[ℂ] PolF D S.rank T.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)


open GlobalTheory.FockAdjoint in
def swapInv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D S.rank T.rank →ₐ[ℂ] PolF D T.rank S.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1)

open GlobalTheory.FockAdjoint in
theorem swapHom_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D T.rank S.rank) :
    swapHom A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapHom]

open GlobalTheory.FockAdjoint in
theorem swapInv_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D S.rank T.rank) :
    swapInv A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapInv]


open GlobalTheory.FockAdjoint in
def swapEquiv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank ≃ₐ[ℂ] PolF D S.rank T.rank :=
  AlgEquiv.ofAlgHom (swapHom A B) (swapInv A B)
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapInv_X, map_mul, swapHom_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapHom_X, map_mul, swapInv_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])

end GlobalTheory.AdjTr

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
noncomputable section

namespace GlobalTheory.RowsPartNe


open GlobalTheory.Mem.RowSides in
theorem jX_injective_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (hM : R.IsModels) (t : T) :
    Function.Injective (R.jX t) := by
  intro f g hfg
  refine semi_injective_of_basis (A.MtildeCSD t).basis (R.B.R t).pres.extL
    (classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.1.1 ?_
  exact (hM.jX t f).symm.trans ((congrArg (R.HX t).e hfg).trans (hM.jX t g))

theorem exists_rowPart_ne_bot_positiveDimension : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → ∃ p, R.EEp3 p ≠ ⊥ := by
  intro hH hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hIn hGE hPos
  by_contra hne
  push_neg at hne
  have hcar := GlobalTheory.Hk3.carries_of_rows_top hP hH R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP D) hOk hC hEx hIn hGE hPos
  have hc0 : ∀ c, R.EEc c = ⊥ := by
    intro c
    by_contra h
    obtain ⟨p, hp⟩ := hcar c h
    have hle : R.EEc c ≤ R.EEp3 p := by
      unfold RealDat3.EEp3
      exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl
    rw [hne p, le_bot_iff] at hle
    exact h hle
  obtain ⟨hCore, hSF, hEq, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  obtain ⟨h, -, -, htop, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP R.toRealDat) R.SF hSF
  have hbot : (⊤ : Submodule ℂ R.HE.H) = ⊥ := by
    rw [← htop]
    simp only [← hEq, hc0, iSup_bot]
  have hzero : ∀ x : R.HE.H, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Submodule ℂ R.HE.H) := Submodule.mem_top
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).1 hx
  have hM := (RealDat3.characterisation_of_weak hC hEx).models
  have hL : R.toRealDat.LPos F.lv2 := fun b => by
    cases b
    · exact hPos false
    · exact hPos true
  refine (GlobalTheory.QPosCompare.lPos_iff_ne_bot R.toRealDat F.lv2).1 hL false ?_
  have hZ : (R.toRealDat.toCx F.lv2).Z A3.A.μ0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hy0 : y = 0 := hzero (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y)
    rw [hy0, map_zero] at hy
    have h1 : R.jX A3.A.μ0 x = 0 := hy.symm
    rw [Submodule.mem_bot]
    exact jX_injective_of_models hM A3.A.μ0 (h1.trans (map_zero _).symm)
  rw [hZ]
  exact BlockDat.good_part_coordinates_bot _ _

end GlobalTheory.RowsPartNe
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefLinks

theorem exists_ioP_of_realDat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hω hv i
  obtain ⟨-, io, hio⟩ := GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R h0 hf hm hω hv
  exact ⟨io i, fun t => hio i t⟩

end GlobalTheory.IndefLinks
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem rowPlacement_iota_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.IndefR.RationalEmbedding.inst D)
    (ι : GA D (Yc D 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  have := eq_of_heq hι
  subst this
  rfl

theorem rowPlacement_exists : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X Gd h ι tS cG hlev hgrp hmod hhost hE0 hι hιE hpin htS hmove
  have hιeq : ι = (iotaX X h).toMulEquiv := rowPlacement_iota_eq h ι hι
  subst hιeq
  have hfirst : ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2})
      (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ RowLevelMatchAt R F X h t := by
    obtain ⟨t, ht, hconj, hframe⟩ := GlobalTheory.T.exists_finite_element_conj_rowLevel_character R F X h hlev hgrp hmod
    exact ⟨t, ht, hconj, GlobalTheory.T.rowLevelMatchAt_of_levelConjugation R F X h hlev hgrp hmod cG t hιE hpin hE0 ht hconj hframe⟩
  obtain ⟨hconjS, hmatchS⟩ := hmove hfirst
  exact ⟨hfirst, GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation hDS R F X h hlev hgrp hmod hhost hιE Gd tS htS hconjS hmatchS⟩

end GlobalTheory
end
