module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Formalism.FockGram.StatementFock
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle235
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.AvgRightLp

end GlobalTheory.AvgRightLp
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockDelta

variable {D : D7}

theorem minor_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k =>
      (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval fun y : FVar D m n =>
    if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at hev
  have hI : (MvPolynomial.eval fun y : FVar D m n =>
      if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hc : a + (β : ℕ) < m ∧ b + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    unfold varF
    rw [dite_eq_left hc, MvPolynomial.eval_X]
    dsimp only
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (Fin.ext (by omega))).elim
    · exact (h1 (by subst h2; omega)).elim
    · rfl
  rw [hI, Matrix.det_one] at hev
  exact one_ne_zero hev

theorem minorPlus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (k : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorPlus
  have h := minor_ne_zero (D := D) (m := m) (n := n) τ 0 0 k (by omega) (by omega)
  simpa only [zero_add] using h

theorem minorMinus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p k : ℕ) (hm : p + k ≤ m) (hn : k ≤ n) :
    (minorMinus τ p k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorMinus
  exact minor_ne_zero τ p (n - k) k hm (by omega)

theorem deltaAt_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p : ℕ) (ap : ℕ → ℕ) (q : ℕ) (am : ℕ → ℕ)
    (hpq : p + q ≤ m) (hmn : m ≤ n) :
    (deltaAt τ p ap q am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold deltaAt
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorMinus_ne_zero τ p (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega

theorem delta_ne_zero {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta
  exact Finset.prod_ne_zero_iff.mpr fun τ _ => deltaAt_ne_zero τ _ _ _ _ (hpq τ) hmn

theorem fock_self_pos {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ Formalism.E.fock P P = (a : ℂ) := by
  refine ⟨∑ m ∈ P.support, Complex.normSq (P.coeff m) * (Formalism.A.mfact m : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos ?_ ?_) ?_
    · exact Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
    · unfold Formalism.A.mfact
      exact Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    · exact Finset.nonempty_iff_ne_empty.mpr fun he => hP (MvPolynomial.support_eq_empty.mp he)
  · unfold Formalism.E.fock
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_natCast]

end GlobalTheory.FockDelta


open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
theorem GlobalTheory.FockDelta.fock_deltaAtEmb_pos :
    ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧
      Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  intro D i σ
  apply GlobalTheory.FockDelta.fock_self_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb
  have hi := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
  apply GlobalTheory.FockDelta.delta_ne_zero
  · intro ρ
    exact le_of_eq (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _)
  · rw [hW]
    exact r_le_V i
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TwistRatBij

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem inclR_eq (e : E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e = (Algebra.TensorProduct.lid F E).symm e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.lid_symm_apply]

theorem inclR_lid (x : F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (Algebra.TensorProduct.lid F E x) = x := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).symm_apply_apply x

theorem lid_inclR (e : E) :
    Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e) = e := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).apply_symm_apply e

theorem lid_sigR (σ : E →ₐ[F] E) (x : F ⊗[F] E) :
    σ (Algebra.TensorProduct.lid F E x) =
      Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

abbrev matOf {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR R σ J from x) : GL (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E))

theorem diagH_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Formalism.UG.UJ (σ : E →+* E) J) (i j : Fin n) :
    matOf (diagH σ J F g) i j =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := rfl

theorem diagH_bijective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), Function.Bijective (diagH σ J F) := by
  intro F E _ _ _ σ n J
  constructor
  · intro g h hgh
    apply Subtype.ext; apply Units.ext; ext i j
    have h1 := congrArg (fun x => matOf x i j) hgh
    simp only [diagH_val] at h1
    have h2 := congrArg (Algebra.TensorProduct.lid F E) h1
    rwa [lid_inclR, lid_inclR] at h2
  · intro h
    let h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR F σ J := h
    let L : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
    let g : GL (Fin n) E := Formalism.UG.bc L h'.1
    have hL : ∀ x, (σ : E →+* E) (L x) = L (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := fun x => lid_sigR σ x
    have hmem : g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      have hh : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) ((h'.1 : GL (Fin n) (F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J *
          ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J := h'.2
      have hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J).map L = J := by
        ext r s; exact lid_inclR (J r s)
      show Formalism.UG.cT (σ : E →+* E) ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) * J *
        ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) = J
      generalize ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) = M at hh ⊢
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) (σ : E →+* E) L hL, ← hJ,
        ← Matrix.map_mul, ← Matrix.map_mul, hh]
    refine ⟨⟨g, hmem⟩, ?_⟩
    apply Subtype.ext; apply Units.ext; ext i j
    exact inclR_lid _

end GlobalTheory.TwistRatBij
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistEquiRat

variable {D : D7}

theorem integral_mul_left {m n : ℕ} (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n))
    (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓨) (P Q : Mx D m m) (hP : P ∈ GlobalTheory.MixModel.ratMx D m m)
    (hQ : Q ∈ GlobalTheory.MixModel.ratMx D m m) (hPQ : P * Q = 1) (hQP : Q * P = 1) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓨, φ (P * a) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  let eA : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => P * a
      invFun := fun a => Q * a
      left_inv := fun a => by show Q * (P * a) = a; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
      right_inv := fun a => by show P * (Q * a) = a; rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add P a b }
  have hc : Continuous (fun a : Mx D m n => P * a) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun a : Mx D m n => Q * a) := continuous_const.matrix_mul continuous_id
  let eH : Mx D m n ≃ₜ Mx D m n := ⟨eA.toEquiv, hc, hc'⟩
  let eM : Mx D m n ≃ᵐ Mx D m n := eH.toMeasurableEquiv
  haveI := h.1
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hc hc'
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : GlobalTheory.MixModel.ratMx D m n → GlobalTheory.MixModel.ratMx D m n :=
    fun g => ⟨P * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hP g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨Q * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hQ g.2⟩, ?_⟩⟩
    · have e := congrArg (fun x : GlobalTheory.MixModel.ratMx D m n => Q * (x : Mx D m n)) hg
      simp only [eG, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at e
      exact Subtype.ext e
    · apply Subtype.ext
      show P * (Q * (g : Mx D m n)) = g
      rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hF : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) (eM.symm ⁻¹' 𝓨) (μ.map eM) := by
    refine h.2.1.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show Q * (P * (g : Mx D m n) + x) = (g : Mx D m n) + Q * x
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓨) = 𝓨 := by
    ext a; simp
  have hvol : (μ.map eM) (eM.symm ⁻¹' 𝓨) = 1 := by
    rw [MeasurableEquiv.map_apply, hpre]; exact h.2.2
  have e1 := hmp.setIntegral_preimage_emb eM.measurableEmbedding φ (eM.symm ⁻¹' 𝓨)
  rw [hpre] at e1
  exact e1.trans (GlobalTheory.MixModel.covolOne_integral_eq h ⟨hHaar, hF, hvol⟩ φ hφ)

theorem symplOH_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  have hM : (adj D C * V.gram)ᴴ = V.gram * C := by
    rw [Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose]
    show V.gram * (Cᴴ)ᴴ = V.gram * C
    rw [Matrix.conjTranspose_conjTranspose]
  have hX0 : X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X = 0 := by
    have e : GlobalTheory.MixModel.adj X = GlobalTheory.MixModel.rat (V.gram * C) := by
      rw [hXdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) * GlobalTheory.MixModel.rat V.gram⁻¹ * GlobalTheory.MixModel.rat (V.gram * C) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C (q₀.map (incA D)) = q₀.map (incA D) * X := rfl
  have e3 : isoPart V W C a = a * X := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * (GlobalTheory.MixModel.gA W * (q₀.map (incA D) * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D)) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D))
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X) * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D)) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart; exact Matrix.add_mul _ _ _

theorem ratW_eq_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) :
    ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := by
  unfold isoPart ratW; exact Matrix.map_mul

end GlobalTheory.TwistEquiRat

namespace GlobalTheory.TwistEquiRat

theorem res_heisO_rat_equi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (γ : GA D W) (γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), γ ∈ GQ W → Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hμ γ γ₀ hγ hγ₀ y f hf
  have hstd := hω.std
  set w₀ := isoPart V W C' (Matrix.map y (incA D)) with hw₀
  have hact : ∀ x : WO V W, actO V W 1 γ x = Formalism.L2.Theta.mt W γ * x := by
    intro x
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e1 : isoPart V W C' (Matrix.map (γ₀ * y) (incA D)) = actO V W 1 γ w₀ := by
    rw [hact, hw₀]
    show Matrix.map (γ₀ * y) (incA D) * (((adj D C' * V.gram).map (incA D)) : Mx D r V.rank) = Formalism.L2.Theta.mt W γ * (Matrix.map y (incA D) * (((adj D C' * V.gram).map (incA D)) : Mx D r V.rank))
    rw [Matrix.map_mul, ← hγ₀, Matrix.mul_assoc]
  have e2 : heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f) =
      ω (1, γ) (heisO ψ V W w₀ f) := by
    rw [e1]; exact (hω.om_heis 1 γ w₀ f hf).symm
  rw [e2]
  set G := heisO ψ V W w₀ f with hGdef
  have hG : IsThetaFunO ψ V W G := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd V W).1 w₀ f hf
  have hrat := GlobalTheory.WeilRat.om_rat_actO D ψ hstd V W χS χT ω hω 1 (one_mem _) γ hγ G hG
  have hQP : Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ = 1 := GlobalTheory.MixModel.mt_mul_inv W γ
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have hpt : ∀ a, ω (1, γ) G (isoPart V W C a + midPart V V' W B 0) =
      G (isoPart V W C (Formalism.L2.Theta.mt W γ⁻¹ * a) + midPart V V' W B 0) := by
    intro a
    rw [hmid, add_zero, add_zero, ← hrat, hact]
    refine congrArg (ω (1, γ) G) ?_
    show a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) = Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W γ⁻¹ * a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank))
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  show ∫ a in 𝓨, ω (1, γ) G (isoPart V W C a + midPart V V' W B 0) ∂μ =
    ∫ a in 𝓨, G (isoPart V W C a + midPart V V' W B 0) ∂μ
  simp only [hpt]
  have hper : ∀ q ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      G (isoPart V W C (q + a) + midPart V V' W B 0) = G (isoPart V W C a + midPart V V' W B 0) := by
    intro q hq a
    obtain ⟨q₀, rfl⟩ := hq
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    rw [hmid, add_zero, add_zero, e3, isoPart_add, ← ratW_eq_isoPart, hG.quasi, ratW_eq_isoPart, symplOH_isoPart V W C hs.frame, neg_zero, AddChar.map_zero_eq_one,
      one_mul]
  exact integral_mul_left μ 𝓨 hμ _ _ ((GlobalTheory.MixModel.mem_GQ_iff W γ⁻¹).1 (inv_mem hγ))
    ((GlobalTheory.MixModel.mem_GQ_iff W γ).1 hγ) hPQ hQP (fun a => G (isoPart V W C a + midPart V V' W B 0)) hper

end GlobalTheory.TwistEquiRat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymplBound

theorem symplAt_pick {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (i : Fin T.rank) (j : Fin S.rank) (w : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ
      (((tauE D τ D.host.xi0)⁻¹ * w) • ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ)) X =
      2 * (w * starRingEnd ℂ (X i j)).re := by
  have hc : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hT := GlobalTheory.SmoothAutCheck.gramAt_unit T τ
  have hS := GlobalTheory.SmoothAutCheck.gramAt_unit S τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  congr 2
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have e1 : (gramAt D S τ)⁻¹ * Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ) =
      (gramAt D S τ)⁻¹ * (Xᴴ * Matrix.single i j (1 : ℂ)) * gramAt D S τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (gramAt D T τ), mul_nonsing_inv _ hT, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ hS, Matrix.one_mul,
    Matrix.trace_mul_single]
  simp only [Matrix.conjTranspose_apply, MulOpposite.op_one, one_smul, Complex.star_def]
  field_simp

theorem bound : ∀ (D : D7) (S T : HSp D) (τ : D.what₂.Tau), ∃ (n : ℕ) (zs : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ) (κ : ℝ), ∀ X : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∑ i, ∑ j, ‖X i j‖ ≤ κ * ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs l) X| := by
  intro D S T τ
  let g : Fin 2 × Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun p =>
    ((tauE D τ D.host.xi0)⁻¹ * Complex.I ^ (p.1 : ℕ)) •
      ((gramAt D T τ)⁻¹ * Matrix.single p.2.1 p.2.2 (1 : ℂ) * gramAt D S τ)
  let e := Fintype.equivFin (Fin 2 × Fin T.rank × Fin S.rank)
  refine ⟨_, fun l => g (e.symm l), 1, fun X => ?_⟩
  rw [one_mul, Equiv.sum_comp e.symm (fun p => |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (g p) X|),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [g, symplAt_pick, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
  have h1 : (starRingEnd ℂ (X i j)).re = (X i j).re := Complex.conj_re _
  have h2 : (Complex.I * starRingEnd ℂ (X i j)).re = (X i j).im := by simp
  rw [h1, h2, abs_mul, abs_mul, abs_two]
  have := Complex.norm_le_abs_re_add_abs_im (X i j)
  nlinarith [abs_nonneg (X i j).re, abs_nonneg (X i j).im]

end GlobalTheory.SymplBound
end
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

theorem _root_.GlobalTheory.T.classTerm_converges_of_lintegral_unfolding_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → ∀ (μ : Measure H) (𝓕 : Set H) (ν : Measure (Quot (cent γ))) (a : ℝ≥0∞), a < ⊤ → (∀ G : H → ℝ≥0∞, Measurable G → ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ = a * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂ν) → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → Integrable (fun q : Quot (cent γ) => f (q.out⁻¹ * γ * q.out)) ν → ∫ q, f (q.out⁻¹ * γ * q.out) ∂ν = c → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (a.toReal * c) := by
  first | exact @GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq | exact GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq | (intros; apply GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq <;> assumption)
end
