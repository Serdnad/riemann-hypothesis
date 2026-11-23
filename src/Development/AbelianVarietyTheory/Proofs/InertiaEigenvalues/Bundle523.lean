module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle503
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle507
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle512
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle513
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.CuspGeneric

theorem good_top : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  intro E _ _ m ψ f hc hl hv
  refine ⟨hc, fun γ _ g => hl γ g, by
    intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul], hv⟩

end GlobalTheory.CuspGeneric

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory.GoodMul

theorem good_mul_invariant : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  intro E _ _ a m ψ f c hf hc hl hu
  refine ⟨hc.mul hf.cont, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hrm g => ?_⟩
  · show c _ * f _ = c g * f g
    rw [hl γ hγ g, hf.left γ hγ g]
  · show c _ * f _ = _ * (c g * f g)
    rw [hu k k y g, hf.law k hk y g]; ring
  · have h : (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) =
        fun x => c g * f (blkU x * g) := by
      funext x; rw [hu r m x g]
    show avg _ (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) = 0
    rw [h, avg_const_mul, hf.van r hr hrm g, mul_zero]

end GlobalTheory.GoodMul
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical




namespace GlobalTheory.LocDisj

theorem map_cA_smul_of_fix (D : D7) {m n : ℕ} (f : AE D) (hf : cA D f = f) (X : Matrix (Fin m) (Fin n) (AE D)) :
    (f • X).map (cA D) = f • X.map (cA D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hf]

theorem map_toEAf_smul (D : D7) {m n : ℕ} (f : AE D) (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (f • Y).map (toEAf D) = toEAf D f • Y.map (toEAf D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem frMapAdj_smul_of_fix (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (x : WO V W) :
    frMapAdj V W βV βW (f • x) = toEAf D f • frMapAdj V W βV βW x := by
  unfold frMapAdj
  have h3 : (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((f • (x : Matrix (Fin W.rank) (Fin V.rank) (AE D))).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D))
      = f • (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((x : Matrix (Fin W.rank) (Fin V.rank) (AE D)).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D)) := by
    rw [map_cA_smul_of_fix D f hf, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h3, map_toEAf_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_smul_eq {n : ℕ} {R : Type} [CommRing R] (c : R) (β : GL (Fin n) R) (M : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ i j, c * (M - 1) i j = 0) :
    c • (β⁻¹.val * M * β.val) = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hM : c • M = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← sub_eq_zero, ← smul_sub]
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h0 i j
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]

theorem split_mul {m n : ℕ} {R : Type} [CommRing R] (c : R) (A A' : Matrix (Fin m) (Fin n) R) (K : Matrix (Fin n) (Fin n) R)
    (hx : c • A = c • A') (hK : (1 - c) • K = (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) :
    A' * K = c • (A * K) + (1 - c) • A' := by
  calc A' * K = (c + (1 - c)) • (A' * K) := by rw [add_sub_cancel, one_smul]
    _ = (c • A') * K + A' * ((1 - c) • K) := by rw [add_smul, Matrix.smul_mul, Matrix.mul_smul]
    _ = (c • A) * K + A' * ((1 - c) • (1 : Matrix (Fin n) (Fin n) R)) := by rw [hx, hK]
    _ = c • (A * K) + (1 - c) • A' := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]

theorem suppF_entry (D : D7) (W : HSp D) (f : AE D) (k : GA D W) (hk : SuppF W f k) (i j : Fin W.rank) :
    (1 - toEAf D f) * ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = 0 := by
  have e : ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = toEAf D ((Formalism.L2.Theta.mt W k - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_one (toEAf D), ← map_sub, ← map_mul, sub_mul, one_mul, hk i j, sub_self, map_zero]

end GlobalTheory.LocDisj

namespace GlobalTheory.LocDisj

theorem frMapAdj_mul_frame_eq (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (k : GA D W) (hk : SuppF W f k) (x x' : WO V W) (hxx : ∀ a b, f * x a b = f * x' a b) :
  (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  have hfx : f • x = f • x' := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hxx a b
  have hx : toEAf D f • frMapAdj V W βV βW x = toEAf D f • frMapAdj V W βV βW x' := by
    rw [← frMapAdj_smul_of_fix D V W βV βW f hf, ← frMapAdj_smul_of_fix D V W βV βW f hf, hfx]
  exact split_mul (toEAf D f) _ _ _ hx (conj_smul_eq _ βW _ (suppF_entry D W f k hk))

end GlobalTheory.LocDisj
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.HalfLatFin

theorem isHalf_of_nsmul {D : D7} {m n : ℕ} (e : AE D) {N : ℕ} (hN : 0 < N) {t t' w : Mx D m n}
    (ht : IsHalf e t) (ht' : IsHalf e t') (hw : t = t' + N • w) : IsHalf e w := by
  intro i j
  have h0 : t i j = t' i j + N • w i j := by
    have := congrFun (congrFun hw i) j
    simpa using this
  have hw' : N • w i j = t i j - t' i j := by rw [h0]; abel
  have h1 : (N : D.host.F) • (e * w i j - w i j) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, smul_sub, ← mul_smul_comm, hw', mul_sub, ht i j, ht' i j, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast hN.ne'))

end GlobalTheory.HalfLatFin

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.SplitDecl

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem embTypeUc_iff (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUc τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i false w hw τ := by
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    refine ⟨h1, (starRingEnd ℂ).comp φ, ?_, fun x y hy => by simpa using h2 x y hy⟩
    show ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) ∈
      D.host.cmType
    have : ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) = φ := by
      ext1 x
      simp [GlobalTheory.SplitRowProbe.conj_sqrt]
    rw [this]; exact hφ
  · rintro ⟨h1, ψ, hψ, h2⟩
    refine ⟨h1, ψ.comp (D.host.conj : D.host.E →+* D.host.E), hψ, fun x y hy => ?_⟩
    rw [h2 x y hy]
    simp [GlobalTheory.SplitRowProbe.conj_sqrt]

theorem embTypeUe_iff (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUe ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  cases ep
  · simp only [EmbeddingTypes.EmbTypeUe, Bool.false_eq_true, if_false]
    exact embTypeUc_iff τ
  · simp only [EmbeddingTypes.EmbTypeUe, if_true]
    rfl

theorem plTypeUe_iff (ep : Bool) :
    EmbeddingTypes.PlTypeUe i w hw ep ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.PlIn (N := D.nd) D.nbr i ep w hw := by
  constructor
  · intro h
    exact ⟨GlobalTheory.SplitRowProbe.nonempty_emb D i w hw, fun τ => (embTypeUe_iff ep τ).1 (h τ)⟩
  · intro h τ
    exact (embTypeUe_iff ep τ).2 (h.2 τ)

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def decl (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) : TruncatedSeriesCountingIdentities.Decl D i where
  row := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  col := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  disj := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  cover := by
    intro v
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    tauto

theorem mem_col (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).col ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

theorem mem_row (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).row ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) →
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  intro D i ep hs
  obtain ⟨hPl, hTy⟩ := GlobalTheory.SplitRowAll.splitRow_at D
  have hP := hPl _ hs
  have hT := hTy i hs
  have hl : D.nd.l i ≠ 0 := hs.1.ne_zero
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    constructor
    · rintro ⟨-, hv', h⟩
      exact h
    · intro h
      exact ⟨hv, hv, h⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨-, ⟨v', hv', hc⟩, -⟩ := hP v hv
      have hx := (hT.2.2.2 ep).1 v hv v' hc
      have hv'c : v' ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
        rcases hx with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      obtain ⟨-, ⟨u', hu', hc'⟩, -⟩ := hP u hu
      have he : v = u' := GlobalTheory.Proof.ConjugatePlaces.isConjPl_unique hc hc'
      subst he
      refine ⟨hu', fun hvc => ?_⟩
      rcases (hT.2.2.2 ep).1 u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · obtain ⟨-, h5, -, -, hg, hcls⟩ := hs
    exact ⟨le_trans (by norm_num) h5, Or.inl hcls, fun _ v hv => (hP v hv).1, hg 0, hg 1⟩

end GlobalTheory.SplitDecl

end
end

section


theorem _root_.GlobalTheory.T.isCrys_of_split_alt : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) [FiniteDimensional Qp LL] (W : Matrix (Fin n) (Fin n) B), IsUnit W.det → (∀ g, (Matrix.of fun i j => algebraMap Qp B (e.repr (ρ g (e j)) i)) * W.map (PD.actB g) = W) → Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  first | exact @GlobalTheory.SplitCrys.isCrys_of_split | exact GlobalTheory.SplitCrys.isCrys_of_split | (intros; apply GlobalTheory.SplitCrys.isCrys_of_split <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  first | exact @GlobalTheory.NormCharL.exists_continuous_ne_zero_one | exact GlobalTheory.NormCharL.exists_continuous_ne_zero_one | (intros; apply GlobalTheory.NormCharL.exists_continuous_ne_zero_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory

theorem continuous_mul_norm_rpow_neg_half :
    Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, zero_mul, tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun z : ℂ => ‖z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖)
        = fun z => ‖z‖ ^ (1 / 2 : ℝ) := by
      funext z
      rcases eq_or_ne z 0 with rfl | hz
      · simp [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]
      · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        have h2 : ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_add hp]; norm_num
        rw [h2, Real.rpow_one]
    rw [hfun]
    have hc : Continuous fun z : ℂ => ‖z‖ ^ (1 / 2 : ℝ) :=
      continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))
    simpa [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)] using hc.tendsto 0
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply ContinuousAt.mul continuousAt_id
    apply Complex.continuous_ofReal.continuousAt.comp
    exact continuous_norm.continuousAt.rpow_const (Or.inl hn)

end GlobalTheory
end

section

open TensorProduct Module

theorem _root_.GlobalTheory.T.exists_periodMatrix_of_finrank_alt : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F), (∀ g, (A g).det ≠ 0) → (∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c) → (∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b) → (∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n → ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  first | exact @GlobalTheory.RegularRing.exists_periodMatrix_of_finrank | exact GlobalTheory.RegularRing.exists_periodMatrix_of_finrank | (intros; apply GlobalTheory.RegularRing.exists_periodMatrix_of_finrank <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  exact @GlobalTheory.NormChar.exists_prime_norm_char_ne_one
end

section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FunExt.ConjLift

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω]

theorem mem_Dec_of_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : ∀ x, σ x ∈ A ↔ x ∈ A) : σ ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσ]
  show (σ * σ⁻¹) x ∈ A ↔ x ∈ A
  rw [mul_inv_cancel]; rfl

variable (s : L ≃ₐ[K] L) (g : G K Ω) (hgs : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (s x))
include hgs


variable {A : ValuationSubring Ω}

omit hgs

end GlobalTheory.FunExt.ConjLift
end
end
