module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle109
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle574
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.SquareLocus.translate_mul_inv_isLocus | exact GlobalTheory.SquareLocus.translate_mul_inv_isLocus | (intros; apply GlobalTheory.SquareLocus.translate_mul_inv_isLocus <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.LieInt

theorem exists_exp_unitary {a : ℕ} (u : Matrix.unitaryGroup (Fin a) ℂ) :
    ∃ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S ∧ NormedSpace.exp S = u := by
  have hJ : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin a => true) = 1 := by
    simp [ReciprocityTheory.ChartRestriction.DS.Jm]
  obtain ⟨Z, ⟨hG, -⟩, hZ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_exp_eq_of_mem_Kset (ε := fun _ : Fin a => true)
    (k := (u : Matrix (Fin a) (Fin a) ℂ)) ⟨u.2, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  refine ⟨Z, ?_, hZ⟩
  unfold ReciprocityTheory.ChartRestriction.DS.inG at hG
  rw [hJ, Matrix.mul_one, Matrix.one_mul] at hG
  exact eq_neg_of_add_eq_zero_left hG

theorem colDer_neg {ι : Type} [DecidableEq ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) :
    (GlobalTheory.ColLie.colDer (d := d) τ (-S)) = -GlobalTheory.ColLie.colDer τ S := by
  simp [GlobalTheory.ColLie.colDer, Finset.sum_neg_distrib, neg_smul]

theorem trace_map_conj {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (hS : S.conjTranspose = -S) :
    (S.map (starRingEnd ℂ)).trace = -S.trace := by
  have h : (S.map (starRingEnd ℂ)).trace = S.conjTranspose.trace := by
    simp [Matrix.trace, Matrix.diag, Matrix.conjTranspose_apply]
  rw [h, hS, Matrix.trace_neg]

theorem act_eq (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X)
    (eT : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (hA : ∀ τ j, A.ε τ j = true) (hB : ∀ τ i, B.ε τ i = true)
    (hn : ∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) (τ : D.what₂.Tau)
    (S : Matrix (Fin M.rank) (Fin M.rank) ℂ) (hS : S.conjTranspose = -S) :
    ∃ Z ∈ lieAt M τ, GlobalTheory.RealQuot.actS ε A B eT τ Z =
      GlobalTheory.ColLie.colDer τ S - (((n₀ τ : ℕ) : ℂ) * S.trace) • (1 : Module.End ℂ (PolF D X.rank M.rank)) := by
  classical
  set F := A.fr τ with hF
  have hFu : IsUnit F := A.fr_unit τ
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hFu
  have hFFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd
  have hFiF : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hJ : Formalism.REAL.Jm (A.ε τ) = 1 := by
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, hA τ]
  have hG : gramAt D M τ = F.conjTranspose * F := by
    rw [← A.fr_gram τ, hJ, Matrix.mul_one]
  set Zf : Matrix (Fin M.rank) (Fin M.rank) ℂ := if ε then S else S.map (starRingEnd ℂ) with hZf
  have hZfs : Zf.conjTranspose = -Zf := by
    rcases ε with _ | _
    · simp only [hZf, if_false, Bool.false_eq_true]
      ext i j
      have := congrFun (congrFun hS j) i
      simp [Matrix.conjTranspose_apply] at this ⊢
      rw [this, neg_neg]
    · simpa [hZf] using hS
  refine ⟨F⁻¹ * Zf * F, ?_, ?_⟩
  · show (F⁻¹ * Zf * F).conjTranspose * gramAt D M τ + gramAt D M τ * (F⁻¹ * Zf * F) = 0
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hZfs]
    have h1 : (F⁻¹).conjTranspose * F.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one]
    calc _ = F.conjTranspose * -Zf * ((F⁻¹).conjTranspose * F.conjTranspose) * F +
          F.conjTranspose * (F * F⁻¹) * Zf * F := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, hFFi]; simp [Matrix.mul_neg, Matrix.neg_mul]
  · have hconj : F * (F⁻¹ * Zf * F) * F⁻¹ = Zf := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFFi, Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
    have htr : (F⁻¹ * Zf * F).trace = Zf.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hFFi, Matrix.one_mul]
    have hsg : (GlobalTheory.SquareComm.frSgn ε A).ε τ = fun _ => !ε := by
      funext j
      simp [GlobalTheory.SquareComm.frSgn, hA τ j]
    have hn' : ((n₀ τ : ℕ) : ℂ) = (((if ε then eT τ else -eT τ) : ℚ) : ℂ) - (X.rank : ℂ) / 2 := by
      have := congrArg (fun x : ℚ => (x : ℂ)) (hn τ)
      push_cast at this ⊢
      exact this
    unfold GlobalTheory.RealQuot.actS
    rw [hsg, hconj, htr]
    rcases ε with _ | _
    · have h2 := GlobalTheory.T.fockSourceGlActionSymmetrised_same_signs (D := D) τ (fun _ : Fin M.rank => !false) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h2]
      have hY : Zf.map (starRingEnd ℂ) = S := by
        ext i j
        simp [hZf]
      have hZt : Zf.trace = -S.trace := by
        simp only [hZf, Bool.false_eq_true, if_false]
        exact trace_map_conj S hS
      rw [hY, hZt, hn']
      simp only [Bool.false_eq_true, if_false]
      push_cast
      module
    · have h1 := GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs (D := D) τ (fun _ : Fin M.rank => !true) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h1]
      have hY : (Zf.map (starRingEnd ℂ)).transpose = -S := by
        rw [← hS]
        ext i j
        simp [hZf, Matrix.conjTranspose_apply]
      have hYt : (Zf.map (starRingEnd ℂ)).trace = -S.trace := by
        simp only [hZf, if_true]
        exact trace_map_conj S hS
      have hZt : Zf.trace = S.trace := by simp [hZf]
      rw [hY, hYt, hZt, hn', colDer_neg]
      simp only [if_true]
      push_cast
      module

theorem colSub_unitary_of_coinv : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  intro D ε M X A B eT n₀ Q _ _ q hA hB hn hker
  have hS : ∀ τ (S : Matrix (Fin M.rank) (Fin M.rank) ℂ), S.conjTranspose = -S → ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.ColLie.colDer τ S P) = (((n₀ τ : ℕ) : ℂ) * S.trace) • q P := by
    intro τ S hS P
    obtain ⟨Z, hZ, he⟩ := act_eq D ε M X A B eT n₀ hA hB hn τ S hS
    have hmem : GlobalTheory.RealQuot.actS ε A B eT τ Z P ∈ GlobalTheory.RealQuot.coinv ε A B eT :=
      Submodule.subset_span ⟨τ, Z, hZ, P, rfl⟩
    have h0 := hker hmem
    rw [LinearMap.mem_ker, he, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      sub_eq_zero] at h0
    exact h0
  have h1 : ∀ τ (u : Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (u : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        ((u : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro τ u P
    obtain ⟨S, hS', he⟩ := exists_exp_unitary u
    rw [← he]
    exact GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation _ _ τ (n₀ τ) Q q (GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp _ _ τ) (hS τ) S hS' P
  intro g P
  have key : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.MinorFrame.colSub (fun τ => if τ ∈ s then (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) P) =
        (∏ τ ∈ s, (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro P
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, one_smul]
      rw [GlobalTheory.MinorFrame.colSub_one, AlgHom.id_apply]
    | insert τ s hτ ih =>
      intro P
      have hsplit : (fun σ => if σ ∈ insert τ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) =
          fun σ => GlobalTheory.ColLie.atPl τ (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) σ *
            (if σ ∈ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) := by
        funext σ
        by_cases h : σ = τ
        · subst h
          simp [GlobalTheory.ColLie.atPl, hτ]
        · simp [GlobalTheory.ColLie.atPl, h, Function.update_of_ne h]
      rw [hsplit, GlobalTheory.MinorFrame.colSub_mul, h1, ih, smul_smul, Finset.prod_insert hτ]
  have := key Finset.univ P
  simp only [Finset.mem_univ, if_true] at this
  rw [this]
  rfl

end GlobalTheory.LieInt
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.GelfandKazhdanHerm

open scoped InnerProductSpace

theorem exists_invariant_hermitian : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  intro hB E _ _ _ a π hπ
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hc : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
    ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level
  have hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hB.of_invariant (π.cusp φ hφ) (hπ φ hφ)
    exact (memL2_iff_isSqInt (hc φ hφ) (π.cusp φ hφ).1.left (hπ φ hφ)).2
      (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC)
  let T := toL2ₗ μ π.V hm
  have hinj : Function.Injective T := toL2ₗ_injective hm hc
  have hR : ∀ (g : GA E a) (x y : L2 (latticeGL E a) μ),
      ⟪R (latticeGL E a) μ g x, R (latticeGL E a) μ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y => by
    let U : L2 (latticeGL E a) μ →ₗᵢ[ℂ] L2 (latticeGL E a) μ :=
      ⟨(R (latticeGL E a) μ g).toLinearMap, fun v => norm_R _ v⟩
    exact U.inner_map_map x y
  refine ⟨((innerₛₗ ℂ).comp T).compl₂ T, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ
    exact inner_conj_symm (T ψ) (T φ)
  · intro φ h0
    have hT : T φ ≠ 0 := fun e => h0 (hinj (e.trans (map_zero T).symm))
    change 0 < (⟪T φ, T φ⟫_ℂ).re
    first
      | exact (re_inner_self_pos (𝕜 := ℂ)).2 hT
      | exact inner_self_pos.2 hT
      | exact (RCLike.inner_self_pos).2 hT
      | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using hT)
  · intro k φ ψ
    change ⟪T (π.op (.fin k) φ), T (π.op (.fin k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (finGL E a k) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.fin k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.fin k) _ ψ.2)).symm
  · intro k φ ψ
    change ⟪T (π.op (.cpt k) φ), T (π.op (.cpt k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (infGL E a (Unitary.toUnits k)) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.cpt k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.cpt k) _ ψ.2)).symm
  · intro X φ ψ
    change ⟪T (π.op (.lie X) φ), T ψ⟫_ℂ + ⟪T φ, T (π.op (.lie X) ψ)⟫_ℂ = 0
    have := GlobalTheory.T.lie_skew_adjoint_matrix E a μ π.V hm π.stable (fun θ hθ => (π.cusp θ hθ).1) X φ ψ
    rw [eq_neg_iff_add_eq_zero] at this
    exact this

end GlobalTheory.GelfandKazhdanHerm

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D d : ℕ}

def part (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

variable {ρ ρ' : AlgChart p σ D → CxPts p σ → ℝ}

def transMat (c c' : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1) a

def IsForm (M : AlgChart p σ D → CxPts p σ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    M c y = chg (transMat c c' y) (M c' y)) ∧
  (∀ c : AlgChart p σ D, ContinuousOn (fun v => M c (c.e.symm v)) c.e.target) ∧
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, (M c y).IsHermitian

variable {A M M' J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}

def chernMat {B : LB X} (φ : Weight p σ B) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess φ (pick φ.isLB y) y

theorem chernMat_congr {L N : HermLB p} (e : L.Isometric N) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : chernMat (L.φ σ) c y = chernMat (N.φ σ) c y := by
  unfold chernMat
  exact (e.hess_eq c hy (mem_pick _ y) (mem_pick _ y)).symm

section Flag

variable {E : X.Modules} {r : ℕ} (h : VMetric p E r) (fl : Vert.Flag E r)

end Flag

section Cell

variable {ι : Type} [Fintype ι] {r : ι → ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))



def emb {m : ℕ} (i : Fin m) : Fin i ⊕ Fin 1 → Fin m := Sum.elim (Fin.castLE i.isLt.le) fun _ => i



variable {m : ℕ}

variable {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)

end Cell

end GlobalTheory.MixDens
end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem mem_unipRad_iff_dual {C D : Matrix (Fin n) (Fin r) E} (xy : cT (σ : E →+* E) C * J * D = 1) (g : GAd σ J) :
    g ∈ unipRad σ J C ↔ ((matHom _ σ J g).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin r) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J g).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
  constructor
  · intro hg
    simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
      sub_eq_iff_eq_add, zero_add]
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, -, h3⟩ := hg
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, xy, Matrix.mul_one, Matrix.one_mul, sub_self]
      choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
        (funext fun j => congrFun (congrFun hT j) k)
      refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
      rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
      ext i k
      exact congrFun (ha k) i
    | one => exact ⟨by simp, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a1, A, a2⟩ := ha
      obtain ⟨b1, B, b2⟩ := hb
      refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
        add_assoc]
    | inv a _ ha =>
      obtain ⟨a1, A, a2⟩ := ha
      have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
        conv_lhs => rw [← a1]
        rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      refine ⟨i1, -A, ?_⟩
      have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
      rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
      rw [Matrix.mul_neg]
      conv_rhs => rw [this]
      abel
  · rintro ⟨h1, B, h2⟩
    refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
    · have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
      have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
      conv_lhs => rw [← h1, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J g).1)]
      exact congrArg _ hg
    · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
          fun i => inclR (F := F) (AF F) (x i) := by
        funext i
        have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
        exact this.symm
      rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]

end GlobalTheory.EisCT

end
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrame

theorem yx_eq_one : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) * X = 1 := by
  intro D V r X Y hW
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  have hX : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X) = X := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, star_star]
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJ, Formalism.UG.cT_one] at h
  rwa [Matrix.mul_assoc]

end GlobalTheory.WittFrame
end
