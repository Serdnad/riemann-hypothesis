module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Matrix NumberField
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.QuotientNormCoisometry

theorem norm_one_le {k : ℕ} : ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

theorem norm_mul_coisom {m k l : ℕ} (T : Matrix (Fin m) (Fin k) ℂ) (W : Matrix (Fin k) (Fin l) ℂ)
    (hW : W * Wᴴ = 1) : ‖T * W‖ = ‖T‖ := by
  have hWt : ‖Wᴴ‖ ≤ 1 := by
    have h1 : ‖Wᴴ‖ * ‖Wᴴ‖ = ‖W * Wᴴ‖ := by
      rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose]
    rw [hW] at h1
    nlinarith [norm_nonneg Wᴴ, norm_one_le (k := k)]
  have hW1 : ‖W‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose] at hWt
  apply le_antisymm
  · calc ‖T * W‖ ≤ ‖T‖ * ‖W‖ := l2_opNorm_mul _ _
      _ ≤ ‖T‖ := mul_le_of_le_one_right (norm_nonneg _) hW1
  · calc ‖T‖ = ‖T * W * Wᴴ‖ := by rw [Matrix.mul_assoc, hW, Matrix.mul_one]
      _ ≤ ‖T * W‖ * ‖Wᴴ‖ := l2_opNorm_mul _ _
      _ ≤ ‖T * W‖ := mul_le_of_le_one_right (norm_nonneg _) hWt

theorem inv_met {k : ℕ} (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsUnit Y.det) :
    ((Y⁻¹)ᴴ * Y⁻¹)⁻¹ = Y * Yᴴ := by
  rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hY, conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ (by rw [det_conjTranspose]; exact hY.star)]

theorem norm_quot {n d D : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin D) (Fin n) ℂ)
    (XQ : Matrix (Fin D) (Fin D) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (hQ : IsUnit XQ.det ∧ (XQ⁻¹)ᴴ * XQ⁻¹ = (P * A⁻¹ * Pᴴ)⁻¹) (hX : IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = A)
    (V : Matrix (Fin d) (Fin D) ℂ) : ‖Y * V * XQ‖ = ‖Y * (V * P) * X‖ := by
  have hA : A⁻¹ = X * Xᴴ := by rw [← hX.2, inv_met X hX.1]
  have hQinv : IsUnit (XQ⁻¹).det := isUnit_nonsing_inv_det XQ hQ.1
  have hBu : IsUnit (P * A⁻¹ * Pᴴ).det := by
    rw [← isUnit_nonsing_inv_det_iff, ← hQ.2, det_mul, det_conjTranspose]
    exact hQinv.star.mul hQinv
  have hB : P * A⁻¹ * Pᴴ = XQ * XQᴴ := by
    rw [← nonsing_inv_nonsing_inv _ hBu, ← hQ.2, inv_met XQ hQ.1]
  have hW : (XQ⁻¹ * P * X) * (XQ⁻¹ * P * X)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc XQ⁻¹ * P * X * (Xᴴ * (Pᴴ * (XQ⁻¹)ᴴ)) = XQ⁻¹ * (P * (X * Xᴴ) * Pᴴ) * (XQ⁻¹)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = XQ⁻¹ * (XQ * XQᴴ) * (XQ⁻¹)ᴴ := by rw [← hA, hB]
      _ = (XQ⁻¹ * XQ) * (XQᴴ * (XQ⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [nonsing_inv_mul _ hQ.1, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hQ.1, conjTranspose_one]
  have e : Y * (V * P) * X = (Y * V * XQ) * (XQ⁻¹ * P * X) := by
    calc Y * (V * P) * X = Y * V * (XQ * XQ⁻¹) * P * X := by
          rw [mul_nonsing_inv _ hQ.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, norm_mul_coisom _ _ hW]

theorem htMap_quot {K : Type} [Field K] [NumberField K] [StarRing K] {n d D : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hQ : Formalism.DivisionValues.IsQuotMetric P H XQ)
    (hX : ∀ v : InfinitePlace K, IsUnit (X v).det ∧ ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (vb : Matrix (Fin d) (Fin D) K) :
    Formalism.HN.htMap (Pi.basisFun K (Fin D)) XQ (Pi.basisFun K (Fin d)) X' vb.mulVecLin =
      Formalism.HN.htMap (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin d)) X' (vb * P).mulVecLin := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Formalism.HN.opNormAt
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin b) (Fin a) K),
      LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) M.mulVecLin = M := fun M => by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hm, hm]
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ),
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ = ‖M‖ := fun M => (l2_opNorm_def M).symm
  rw [e, e, Matrix.map_mul, norm_quot (H.map v.embedding) (P.map v.embedding) (XQ v) (X v) (X' v)⁻¹ (hQ v) (hX v)]

section Bound

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open _root_.Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem bound_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) :
    (D.R.m : ℝ) * aOne d.G C p.Z.b ≤ d.O.bIPa C p.Z.b := by
  have hS := LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.sig_le d ∅ (fun _ => 0) hC
  have hN := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bIPa aOne
  rw [hN]
  show (D.R.m : ℝ) * (C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * sig d.G) ≤
    C * D.R.f * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * (d.data (fun _ => 1) ∅ fun _ => 0).Sig0 C p.Z.b
  have h0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS h0]

end Bound


end GlobalTheory.QuotientNormCoisometry

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumChar

open Formalism.L2.JoinChr

theorem locE_sum {D : D7} {ι : Type} (s : Finset ι) (f : ι → AE D)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (k : D.host.E) :
    locE D (∑ i ∈ s, f i) k = ∏ i ∈ s, locE D (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [locE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih fun i hi j hj hij => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : f a * ∑ i ∈ s, f i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i hi => hf a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    unfold locE
    linear_combination (-(incA D k - 1) * (incA D k - 1)) * h0

theorem char_eq_prod : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  intro D Q eQ h k y hy c ψ hψ
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hIP : ∀ P ∈ Q, Formalism.L2.NTheta.IsIdemAt (cA D (es P)) (conjPl P) := fun P hP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes P hP) fun _ => Iff.rfl
  let g : Pl D.host.E → AE D := fun P => if P ∈ Q then cA D (es P) else 0
  have hg : ∀ P, g P * g P = g P := fun P => by
    by_cases hP : P ∈ Q
    · simp only [g, if_pos hP]; exact (hIP P hP).1.1
    · simp only [g, if_neg hP, mul_zero]
  have horth : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → g P * g P' = 0 := fun P hP P' hP' hne => by
    simp only [g, if_pos hP, if_pos hP', ← map_mul]
    rw [idem_orth (idemAt_split (hes P hP)) (hes P hP) (hes P' hP') hne, map_zero]
  have hsum : cA D (∑ P ∈ Q, es P) = ∑ P ∈ Q, g P := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun P hP => by simp only [g, if_pos hP]
  have hy' : y = ∏ P ∈ Q, locU (hg P) k := by
    apply Units.ext
    rw [hy, Units.coe_prod, hsum, locE_sum Q g horth]
    rfl
  rw [hy', map_prod]
  have hcoe : ∀ (s : Finset (Pl D.host.E)) (u : Pl D.host.E → Circle),
      (((∏ P ∈ s, u P : Circle)) : ℂ) = ∏ P ∈ s, ((u P : Circle) : ℂ) := fun s u =>
    map_prod Circle.coeHom u s
  rw [hcoe]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hpl : IsPlIdem D (g P) (conjPl P) := by
    simp only [g, if_pos hP]; exact GlobalTheory.HeckeDetChar.isPlIdem (hIP P hP)
  exact hψ.2 (conjPl P) (g P) hpl k (locU (hg P) k) (locU_val _ _)

end GlobalTheory.IdemSumChar
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localElements_commute_distinct_realPlaces : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ) (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x → isLocEnv V pl ok i' y → x * y = y * x := by
  first | exact @GlobalTheory.LocComm.mul_comm_of_isLocEnv | exact GlobalTheory.LocComm.mul_comm_of_isLocEnv | (intros; apply GlobalTheory.LocComm.mul_comm_of_isLocEnv <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM

namespace GlobalTheory.GenFree

theorem exists_free_away (A M : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] : ∃ g : A, g ≠ 0 ∧ Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨g, hg, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨g, nonZeroDivisors.ne_zero hg, hfree⟩

theorem free_basicOpen {X Y : Scheme.{0}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (g : Γ(Y, V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free (Localization.Away g) (LocalizedModule.Away g Γ(X, f ⁻¹ᵁ V))) :
    letI := (f.app (Y.basicOpen g)).hom.toAlgebra
    Module.Free Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have hpre : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen _ _
  let A := Γ(Y, V)
  let M := Γ(X, f ⁻¹ᵁ V)
  let R := Γ(Y, Y.basicOpen g)
  let N := Γ(X, f ⁻¹ᵁ Y.basicOpen g)
  letI : Algebra A R := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g R := hV.isLocalization_basicOpen g
  have hle : f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ V := f.preimage_mono (Y.basicOpen_le g)
  letI : Algebra M N := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI : IsLocalization.Away (algebraMap A M g) N :=
    hV'.isLocalization_of_eq_basicOpen (f.app V g) (homOfLE hle) hpre
  letI : Algebra R N := (f.app (Y.basicOpen g)).hom.toAlgebra
  letI : Algebra A N := ((algebraMap R N).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A M N := IsScalarTower.of_algebraMap_eq fun a => by
    change (f.app _).hom ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom a) =
      (X.presheaf.map (homOfLE hle).op).hom ((f.app V).hom a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers g)) N := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers g) (IsScalarTower.toAlgHom A M N).toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (IsScalarTower.toAlgHom A M N).toLinearMap
  let b₀ := Module.Free.chooseBasis (Localization.Away g) (LocalizedModule.Away g M)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) R
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars A ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) R
  exact Module.Free.of_basis (Module.Basis.ofRepr Ψ')

theorem exists_dim_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp F) [LocallyOfFiniteType q] :
    ∃ n : ℕ, topologicalKrullDim Y = n := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (genericPoint Y))
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ q)
  have hφ : Spec.map φ = hU.fromSpec ≫ q := Spec.map_preimage _
  letI : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  obtain ⟨d, h₁, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F q U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem exists_affine_finite_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (sY : Y ⟶ Sp k) (f : X ⟶ Y), IsProjOver (f ≫ sY) → IsProjOver sY → f (genericPoint X) = genericPoint Y → topologicalKrullDim X ≤ topologicalKrullDim Y → ∀ n : ℕ, f.residueDegree (genericPoint X) = n → ∃ V : Y.Opens, genericPoint Y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f ⁻¹ᵁ V) ∧ (letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n) := by
  intro k _ X Y _ _ sY f hX hY hη hdim n hn
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hX
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hY
  have : IsProper f := IsProper.of_comp f sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsDominant f := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
    (Set.singleton_subset_iff.2 ⟨_, hη⟩)⟩
  have hs := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  obtain ⟨d, hdY⟩ := exists_dim_eq k sY
  have hdX : topologicalKrullDim X = d :=
    (le_antisymm hdim (PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective)).trans hdY
  have hd : f.residueDegree (genericPoint X) ≠ 0 :=
    GenFinite.residueDegree_genericPoint_ne_zero k X Y sY f d inferInstance inferInstance hs hdX hdY
  obtain ⟨V₀, hV₀, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f
    (genericPoint Y) ((Set.finite_singleton (genericPoint X)).subset
      fun y hy => GenFiniteEtale.eq_genericPoint f hη hd hy)
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV₀
  replace hV : IsAffineOpen V := hV
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨hW, hf⟩ := GenFiniteEtale.finite_app_of_le f hV hle
  letI := (f.app V).hom.toAlgebra
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hf
  obtain ⟨g, hg, hfree⟩ := exists_free_away Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  have hU := hV.basicOpen g
  have hxU := GenFiniteEtale.genericPoint_mem_basicOpen hg
  obtain ⟨hW', hf'⟩ := GenFiniteEtale.finite_app_of_le f hU ((Y.basicOpen_le g).trans hle)
  refine ⟨Y.basicOpen g, hxU, hU, hW', free_basicOpen f hV hW g hfree, hf', ?_⟩
  have := (GenFiniteEtale.affine_pair f hη hd hU hW' le_rfl (show f _ ∈ Y.basicOpen g from hη ▸ hxU)).2.2.1
  rw [← f.app_eq_appLE] at this
  exact this.trans hn

end GlobalTheory.GenFree
end
