module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdapted
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSmulInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondEmbeddingAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

abbrev mQJ : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  (Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ * (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ

theorem mQJ_unit : IsUnit (mQJ X p θ Q).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_reindex_self]
  exact (Units.isUnit (Matrix.GeneralLinearGroup.det Q)).mul (isUnit_det_split_form X p θ)

theorem secondCoords_eq_mulVec (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v = mQJ X p θ Q *ᵥ (pr2 θ v ∘ (idxEquiv X).symm) := by
  unfold crd2; rw [Matrix.mulVec_mulVec]

theorem crd_surj (a b : IdxD D → FpX X p) : ∃ x, crd1 X p θ Q x = a ∧ crd2 X p θ Q x = b := by
  set w1 := (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ a
  set w2 := (mQJ X p θ Q)⁻¹ *ᵥ b
  refine ⟨fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j)), ?_, ?_⟩
  · have : pr1 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w1 := by
      funext i; simp [pr1]
    unfold crd1; rw [this, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · have : pr2 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w2 := by
      funext i; simp [pr2]
    rw [secondCoords_eq_mulVec, this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (mQJ_unit X p θ Q), Matrix.one_mulVec]

theorem crd_inj (x : Fin X.B.I.n → TpX X p) (h1 : crd1 X p θ Q x = 0) (h2 : crd2 X p θ Q x = 0) : x = 0 := by
  have e1 : pr1 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ v) h1
    simp only [crd1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  have e2 : pr2 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (mQJ X p θ Q)⁻¹ *ᵥ v) h2
    simp only [secondCoords_eq_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (mQJ_unit X p θ Q),
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  funext j
  have a1 := congrFun e1 (idxEquiv X j)
  have a2 := congrFun e2 (idxEquiv X j)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at a1 a2
  have : θ (x j) = 0 := Prod.ext a1 a2
  simpa using congrArg θ.symm this

theorem oEp_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ OvA X p ∧ (θ t).2 ∈ OvA X p := by
  obtain ⟨j⟩ : Nonempty (IdxD D) := ⟨zI⟩
  obtain ⟨x1, hx1a, hx1b⟩ := crd_surj X p θ Q (Pi.single j 1) 0
  obtain ⟨x2, hx2a, hx2b⟩ := crd_surj X p θ Q 0 (Pi.single j 1)
  have hint : IntVec (OvA X p) (Pi.single j (1 : FpX X p)) := fun i => by
    by_cases h : i = j
    · subst h; simp [ValuationSubring.one_mem]
    · simp [h, ValuationSubring.zero_mem]
  have hz : IntVec (OvA X p) (0 : IdxD D → FpX X p) := fun _ => ValuationSubring.zero_mem _
  have l1 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x1).2 ⟨hx1a ▸ hint, hx1b ▸ hz⟩)
  have l2 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x2).2 ⟨hx2a ▸ hz, hx2b ▸ hint⟩)
  have c1 := ((latCrd_of X p θ Q hL _).1 l1).1 j
  have c2 := ((latCrd_of X p θ Q hL _).1 l2).2 j
  rw [firstCoords_tensor_smul, hx1a] at c1
  rw [secondCoords_tensor_smul, hx2b] at c2
  simp at c1 c2
  exact ⟨c1, c2⟩

def OEpSplit : Prop := θ.symm (1, 0) ∈ OEp X p ∧ θ.symm (0, 1) ∈ OEp X p

theorem splitA_of_lat (hL : LatBasis X p θ (reindex₂ X p Q)) (hO : OEpSplit X p θ) : SplitA X p θ Q :=
  splitA_of X p θ Q (oEp_int X p θ Q hL) hO.1 hO.2 (latCrd_of X p θ Q hL) (crd_inj X p θ Q) (crd_surj X p θ Q)

theorem reduction_image_of_adapted_mod (hb : AdBridgeIso X.B.I) (hC : LatCoreX)
    (h : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ OEpSplit X p θ ∧
      ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, hO, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted X p hb hC ⟨θ, hθ, Q, hL, splitA_of_lat X p θ Q hL hO, hA⟩

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def liftE (r : 𝓞 X.B.I.F) : 𝓞 X.B.I.E :=
  ⟨algebraMap X.B.I.F X.B.I.E (r : X.B.I.F),
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)⟩

theorem liftE_coe (r : 𝓞 X.B.I.F) : ((liftE X r : 𝓞 X.B.I.E) : X.B.I.E) = algebraMap X.B.I.F X.B.I.E (r : X.B.I.F) := rfl

def starE (a : 𝓞 X.B.I.E) : 𝓞 X.B.I.E :=
  ⟨star (a : X.B.I.E), (RingOfIntegers.isIntegral_coe a).map (starRingEnd X.B.I.E).toIntAlgHom⟩

theorem hform_zero_left (x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J 0 x = 0 := by
  simp [Formalism.UG.hform]

theorem hform_add_left (y y' x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (y + y') x =
      Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x + Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y' x := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (a : 𝓞 X.B.I.E) (y x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (a • y) x =
      star (a : X.B.I.E) * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show star ((a • y) i) * X.B.I.J i j * x j = star (a : X.B.I.E) * (star (y i) * X.B.I.J i j * x j)
  rw [Pi.smul_apply, Algebra.smul_def]
  show star ((a : X.B.I.E) * y i) * _ * _ = _
  rw [star_mul']
  ring

theorem locGlob_of (hN : DenomP X p θ) : LocGlob X p θ := by
  classical
  intro x hx
  obtain ⟨S, hS⟩ := X.B.I.L_fg
  have hSL : ∀ g ∈ S, g ∈ X.B.I.L := fun g hg => hS ▸ Submodule.subset_span hg
  have hg : ∀ g ∈ S, ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ c : 𝓞 X.B.I.E,
      (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g x :=
    fun g hgS => hN _ (hx g (hSL g hgS)).1 (hx g (hSL g hgS)).2
  choose! s hs c hc using hg
  set t : 𝓞 X.B.I.F := ∏ g ∈ S, s g with ht_def
  have ht : t ∉ p.1.asIdeal := by
    intro h
    have := p.1.isPrime
    obtain ⟨g, hgS, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hs g hgS hg
  set T : X.B.I.E := algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) with hT
  have hkey : ∀ g ∈ S, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g (T • x) ∈
      (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
    intro g hgS
    rw [hform_smul_right]
    refine ⟨liftE X (∏ h ∈ S.erase g, s h) * c g, ?_⟩
    rw [map_mul]
    show ((liftE X (∏ h ∈ S.erase g, s h) : 𝓞 X.B.I.E) : X.B.I.E) * ((c g : 𝓞 X.B.I.E) : X.B.I.E) = _
    rw [hc g hgS, liftE_coe, hT, ht_def, ← Finset.mul_prod_erase S s hgS]
    have hm : ((s g * ∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) =
        (s g : X.B.I.F) * ((∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) := map_mul (algebraMap _ _) _ _
    rw [hm, map_mul]
    ring
  have hTx : T • x ∈ X.B.I.L := by
    refine (X.B.I.L_dual _).2 fun y hy => ?_
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem g hg => exact hkey g hg
    | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
    | add y y' _ _ h1 h2 =>
        obtain ⟨c1, e1⟩ := h1
        obtain ⟨c2, e2⟩ := h2
        exact ⟨c1 + c2, by rw [map_add (f := _), e1, e2, hform_add_left]⟩
    | smul a y _ h1 =>
        obtain ⟨c1, e1⟩ := h1
        exact ⟨starE X a * c1, by rw [map_mul, e1, hform_smul_left]; rfl⟩
  obtain ⟨hinv, hne⟩ := unit_of_notMem X p t ht
  have hM : (fun j => iota2 X p θ ((T • x) j)) ∈ Mlat2 X p θ := Submodule.subset_span ⟨T • x, hTx, rfl⟩
  have heq : (fun j => iota2 X p θ (x j)) =
      (⟨(algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹, hinv⟩ : OpX X p) • (fun j => iota2 X p θ ((T • x) j)) := by
    funext j
    show iota2 X p θ (x j) = (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹ * iota2 X p θ (T * x j)
    rw [map_mul, hT, secondEmbedding_algebraMap, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [heq]
  exact Submodule.smul_mem _ _ hM

theorem latBasisAll_of_parts
    (hN : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → DenomP X p θ)
    (hA : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → ApproxP X p θ) :
    LatBasisAll X p := latBasisAll_of_back X p (fun θ hθ => dualBack_of X p θ (locGlob_of X p θ (hN θ hθ)) (hA θ hθ))

end Loc

end MassDataIdxSteps
end
end
