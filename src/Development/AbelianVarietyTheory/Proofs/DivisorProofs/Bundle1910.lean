module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196

@[expose] public section

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

theorem GlobalTheory.MinorFrame.exists_unitary_detChar_ne : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  intro ι _ a ha n n₀ hne
  classical
  obtain ⟨τ₀, hτ⟩ := Function.ne_iff.mp hne
  have hN : n τ₀ + n₀ τ₀ + 1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1) :=
    Complex.isPrimitiveRoot_exp _ hN
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := hz.norm'_eq_one hN
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]; simp
  let d : Fin a → ℂ := Function.update 1 ⟨0, ha⟩ z
  have hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = ⟨0, ha⟩
    · subst i; simpa [d] using hzz
    · simp [d, hi]
  let g : ι → Matrix.unitaryGroup (Fin a) ℂ := fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1
  refine ⟨g, ?_⟩
  have key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀ := by
    intro m
    unfold GlobalTheory.MinorFrame.detChar
    rw [Finset.prod_eq_single τ₀]
    · simp only [g, if_pos rfl, Matrix.det_diagonal, d]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [key, key]
  intro h
  exact hτ (hz.pow_inj (by omega) (by omega) h)
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

namespace GlobalTheory.MinorFrame

open MvPolynomial

theorem colSub_totalDegree_le {ι : Type} [Fintype ι] {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  classical
  unfold colSub
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have h1 : (∑ j' : Fin a, C (g i.1 j' i.2.2) * (X (i.1, i.2.1, j') : Pol ι d a)).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ h1
    _ = s i := mul_one _

theorem star_detChar_mul_detChar {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (g : ι → Matrix.unitaryGroup (Fin a) ℂ) :
    starRingEnd ℂ (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) *
      detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
  unfold detChar
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [map_pow, ← mul_pow]
  have h : starRingEnd ℂ (g τ : Matrix (Fin a) (Fin a) ℂ).det * (g τ : Matrix (Fin a) (Fin a) ℂ).det = 1 := by
    rw [starRingEnd_apply, ← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 (g τ).2,
      Matrix.det_one]
  rw [h, one_pow]

@[reducible] def fockCore {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := Formalism.L2.DIV.fockS x.1 y.1
  conj_inner_symm x y := (fockS_conj x.1 y.1).symm
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx, Formalism.L2.DIV.fockS]
    · exact (fockS_self_re_pos hx).le
  add_left x y z := by
    show Formalism.L2.DIV.fockS (x.1 + y.1) z.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_add₂]
    rfl
  smul_left x y r := by
    show Formalism.L2.DIV.fockS (r • x.1) y.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  definite x hx := by
    by_contra h
    have h' : x.1 ≠ 0 := fun e => h (Subtype.ext e)
    have := fockS_self_re_pos h'
    rw [show Formalism.L2.DIV.fockS x.1 x.1 = 0 from hx] at this
    simp at this

theorem exists_mem_inv_eq_of_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  intro ι _ a d n Pr _ _ q hq P
  classical
  let S : Submodule ℂ (Pol ι d a) := restrictTotalDegree (Var ι d a) ℂ P.totalDegree
  haveI : FiniteDimensional ℂ S :=
    inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Var ι d a) ℂ P.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fockCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  have hmemS : ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (x : Pol ι d a), x ∈ S → colSub g x ∈ S := fun g x hx =>
    (mem_restrictTotalDegree _ _ _).2 ((colSub_totalDegree_le g x).trans ((mem_restrictTotalDegree _ _ _).1 hx))
  let gen : Set S := {w | ∃ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (x : S),
      (w : Pol ι d a) = colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) x.1 -
        detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • x.1}
  let K : Submodule ℂ S := Submodule.span ℂ gen
  have hK : ∀ w ∈ K, q (w : Pol ι d a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, y, hy⟩ := hx
      rw [hy, map_sub, map_smul, hq, sub_self]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hPS : P ∈ S := (mem_restrictTotalDegree _ _ _).2 le_rfl
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (⟨P, hPS⟩ : S)
  refine ⟨z.1, ?_, ?_⟩
  · intro g
    set G := colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) z.1 with hG
    set c := detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) with hc
    let w : S := ⟨G - c • z.1, S.sub_mem (hmemS _ _ z.2) (S.smul_mem c z.2)⟩
    have hw : w ∈ K := Submodule.subset_span ⟨g, z, rfl⟩
    have h1 : Formalism.L2.DIV.fockL z.1 (G - c • z.1) = 0 := Submodule.inner_left_of_mem_orthogonal hw hz
    have h2 : Formalism.L2.DIV.fockL (G - c • z.1) z.1 = 0 := Submodule.inner_right_of_mem_orthogonal hw hz
    have hinv : Formalism.L2.DIV.fockL G G = Formalism.L2.DIV.fockL z.1 z.1 := by
      rw [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hG, fockS_colSub_unitary]
    have hcc := star_detChar_mul_detChar n g
    rw [← hc] at hcc
    have e1 : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) =
        Formalism.L2.DIV.fockL (G - c • z.1) G - c * Formalism.L2.DIV.fockL (G - c • z.1) z.1 := by
      rw [map_sub, map_smul, smul_eq_mul]
    have e2 : Formalism.L2.DIV.fockL (G - c • z.1) G =
        Formalism.L2.DIV.fockL G G - starRingEnd ℂ c * Formalism.L2.DIV.fockL z.1 G := by
      rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    have h1' : Formalism.L2.DIV.fockL z.1 G - c * Formalism.L2.DIV.fockL z.1 z.1 = 0 := by
      rw [← h1, map_sub, map_smul, smul_eq_mul]
    have hWW : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) = 0 := by
      linear_combination e1 + e2 - c * h2 + hinv - starRingEnd ℂ c * h1' - Formalism.L2.DIV.fockL z.1 z.1 * hcc
    by_contra hne
    have hne' : G - c • z.1 ≠ 0 := sub_ne_zero.2 hne
    have := fockS_self_re_pos hne'
    rw [← Formalism.L2.DIV.fockL_apply, hWW] at this
    simp at this
  · have hP : P = y.1 + z.1 := congrArg Subtype.val hyz
    rw [hP, map_add (f := _), hK y hy, zero_add]

end GlobalTheory.MinorFrame
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.BigNZ

open GlobalTheory.WeilM GlobalTheory.AdelicU

section Generic

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

def IsFinPart (M : Model σ X Y) (T : Finset (Pl F)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ v, v ∉ T → φ v = M.vac v

def IsLagrModel (M : Model σ X Y) (ψ : AddChar (AF F) ℂ) (v : Pl F) (A A' : Set (Matrix (Fin n) (Fin d) (AE F E)))
    {Z : Type} [TopologicalSpace Z] [Add Z] (co : Matrix (Fin n) (Fin d) (AE F E) → Z)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Z → ℂ)) : Prop :=
  Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB Z : Set _) ∧
  (∀ u ∈ A, ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ z, ι φ₁ z = ι φ (z + co u)) ∧
  ∀ u ∈ A', ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ x ∈ A,
    ι φ₁ (co x) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) * ι φ (co x)

theorem isFinPart_vac {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (h : M.IsGood ψ) (T : Finset (Pl F)) : IsFinPart M T M.vac :=
  ⟨fun v => (h.vac v).1, fun _ _ => rfl⟩

theorem isLagrModel_of_isLin {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : Pl F} {π₁ π₀ : AE F E →+* Fv F v} {co ι}
    (h : M.IsLin ψ π₁ π₀ co ι) :
    IsLagrModel M ψ v {u | At (evFin F v) u ∧ u.map π₀ = 0} {u | At (evFin F v) u ∧ u.map π₁ = 0} co ι :=
  ⟨h.bij, fun u hu => h.trans u hu.1 hu.2, fun u hu φ hφ φ₁ hφ₁ a x hx => h.mult u hu.1 hu.2 φ hφ φ₁ hφ₁ a x hx.1 hx.2⟩

end Generic

section Grid

open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num Geo IsTripleOf mulG colV adjV₁)
open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def IsTied (t : T) (i j : ℕ) (e : Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  Γ.V.L = conjSub (G.Λ (.grid (i + 1) (j + 1))) ∧
  Γ.W.L = pairLat (scLat D.host.AA (G.Λ (.grid i (j + 1)))) (conjSub (scLat D.host.AA (conjSub (G.Λ (.grid (i + 1) j))))) e ∧
  (∀ v, v ∈ X.T ↔ ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
  ∀ v : Bs.P, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v.1 → splitPrime (Bs.τ v) = w

variable {i j : ℕ}

def mixHalf (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (negSp (spW G i j)) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCo (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mulG (negSp (spW G i j)) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def IsLocFn (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : Geo G i j) (w : Pl D.host.E)
    (v : Pl D.host.F) (Ψ : Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ)
    (φ : (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ) : Prop :=
  φ ∈ SB _ ∧ ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧ ι φ = Ψ

end Grid

end GlobalTheory.BigNZ

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitUnitLift

open GlobalTheory.SplitGLLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : Pl (F := F)} {n : ℕ}

theorem unitary_eps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g))ᵀ * incM F J *
      (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g)).map (cA σ) = incM F J := by
  set p := pairHom (J.map τ) hJ g - 1 with hp
  have hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p := rfl
  rw [hN, map_one_add_cA]
  have tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)),
      (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f := fun f A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have e : J.map τ * (J.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have gi : ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 :=
    Units.inv_mul g
  apply mat_ext h τ
  · intro w
    rw [tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]
    simp
  · intro u hu
    rw [tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]
    simp
  · rw [tr, map_one_add_piW, map_one_add_piW, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW τ) ∘ ⇑(inclR (F := F) (AF F))) = J.map τ :=
      Matrix.ext fun i j => piW_inclR τ (J i j)
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ *
      ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ) = J.map τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one,
      ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]
  · rw [tr, map_one_add_piW_comp, map_one_add_piW_comp, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW (τ.comp σ)) ∘ ⇑(inclR (F := F) (AF F))) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [piW_inclR, AlgHom.comp_apply, herm, map_mul, AlgHom.commutes]
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)ᵀ *
      (algebraMap F (Fv F v) ε • (J.map τ)ᵀ) * (g : Matrix (Fin n) (Fin n) (Fv F v)) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi,
      Matrix.mul_one]

def liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (oneAdd (liftMat h τ)).comp (pairHom (J.map τ) hJ)

def liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* UA σ J where
  toFun g := ⟨⟨liftN h τ J hJ g, liftN h τ J hJ g⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
    by rw [← map_mul, inv_mul_cancel, map_one]⟩, unitary_eps h τ J ε herm hJ g⟩
  map_one' := Subtype.ext (Units.ext (map_one (liftN h τ J hJ)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (liftN h τ J hJ) g g'))

theorem mat_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    mat (liftU h τ J ε herm hJ g) = 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1) := rfl

theorem liftU_mem_UAt (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (X : Spc F E n) (ε : F)
    (herm : ∀ i j, σ (X.J j i) = algebraMap F E ε * X.J i j) (hJ : IsUnit (X.J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    liftU h τ X.J ε herm hJ g ∈ UAt σ X (evFin F v) := by
  show At (evFin F v) (mat _ - 1)
  rw [mat_liftU, add_sub_cancel_left]
  exact at_liftMat h τ _

theorem liftU_piW (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW τ) = g.val := by
  rw [mat_liftU, map_one_add_piW]
  exact add_sub_cancel _ _

theorem liftU_piW_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW (τ.comp σ)) = (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * J.map τ := by
  rw [mat_liftU, map_one_add_piW_comp]
  exact add_sub_cancel _ _

theorem isUnit_det_of_cartan (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) (e : E →+* ℂ) (c : ℂ) (hc : c ≠ 0)
    (θ : Matrix (Fin n) (Fin n) ℂ) (hθ : IsCartan (c • J.map e) θ) : IsUnit (J.map τ).det := by
  have h1 : (c • J.map e).det ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hx : star y ≠ 0 := fun h => hy (by simpa using congrArg star h)
    have := hθ.2.2 (star y) hx
    rw [star_star, hMy, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have h2 : J.det ≠ 0 := by
    intro h0
    apply h1
    have hd : (J.map e).det = e J.det := (RingHom.map_det e J).symm
    rw [Matrix.det_smul, hd, h0, map_zero, mul_zero]
  have hd : (J.map τ).det = τ J.det := (AlgHom.map_det τ J).symm
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 h2

end GlobalTheory.SplitUnitLift
end
end

section

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer.Smooth


end GlobalTheory.ThK.CuspTransfer.Smooth

open GlobalTheory.SiegelSet (IsRealLine)
open GlobalTheory.Orb (archMat IsSmoothRealFam)

namespace GlobalTheory.ThK.CuspTransfer.Smooth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem line_fam (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : IsSmoothRealFam γ ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  choose y e1 e2 using hγ
  obtain rfl : γ = fun t => embArch σ J w (y t) := funext e1
  exact GlobalTheory.Orb.isSmoothRealFam_embArch h τ fun i j => by
    simp only [e2]; exact GlobalTheory.Orb.contDiff_exp_smul_entry Z i j





end GlobalTheory.ThK.CuspTransfer.Smooth


end
end
