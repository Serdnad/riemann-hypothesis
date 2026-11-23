module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle325
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.EMtLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) : Transport (reX Z X) u F' where
  wt := T.wt
  wt_isom := T.wt_isom
  wt_e := T.wt_e
  wt_f := T.wt_f
  weight_z := T.weight_z
  ιA := T.ιA
  ιA_rat := T.ιA_rat
  ιA_int := T.ιA_int
  h0 := T.h0
  hc := T.hc
  hc_rep := fun c => by rw [hy]; exact T.hc_rep c
  J := T.J
  J_eqv := T.J_eqv
  J_val := T.J_val
  J_isom := fun c ξ η => by rw [he]; exact T.J_isom c ξ η



theorem colDictL_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (hK : X.LevelSubgroupCharacter) (x : Cu X u hK) :
    colDictL (reX Z X) (reTr Z T hy he) hK x = colDictL X T hK x := by
  funext c z
  show T.J (shP X u x.1 (T.hc c)) (F'.val0.eY z) = T.J (shP X u x.1 (T.hc c)) (F.val0.eY z)
  rw [he]
  rfl

end GlobalTheory.Mem.SRe

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open TopologicalSpace
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open Formalism.L2.Pj (FrPt CAt embK)
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts
open GlobalTheory.AllWt (Psi ptF framesOn LiesOn)
open scoped ComplexOrder

namespace GlobalTheory.TrueCx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}

section Std

variable (X : Data E r) (hj : j ≤ r) (κ : Tau ≃ X.Ψ)

def stdMat (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem frameCo_stdMat (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (stdMat X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  show reindex _ _ (_ * (mat (x0F X) τ * _)) = _
  rw [nonsing_inv_mul_cancel_left _ _ (det_x0F X τ).isUnit]
  simp

theorem domPt_stdMat (z : Pt Tau j (r - j)) : domPt X hj κ (stdMat X hj κ z) = z := by
  funext t
  simp [domPt, frameCo_stdMat, moeb_zero]

theorem stdMat_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    stdMat X hj κ z ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · show (mat (x0F X) τ * _).det ≠ 0
    rw [det_mul, det_reindex_self, det_fromBlocks_zero₂₁]
    simpa using det_x0F X τ
  have h0 := congrArg transpose (isOrth_x0F X τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0
  set N : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 (z (κ.symm τ)) 0 1 with hN
  have h1 : reindex (idx hj) (idx hj) (gram τ.1 X.Gm (mat (stdMat X hj κ z) τ))ᵀ = Nᴴ * -Jpq j (r - j) * N := by
    rw [gram_eq_mul, ← reindex_sgn hj, ← h0]
    show reindex _ _ ((mat (x0F X) τ * reindex _ _ N)ᴴ * _ * (mat (x0F X) τ * reindex _ _ N)) = _
    simp only [conjTranspose_mul, reindex_apply, conjTranspose_submatrix, ← submatrix_mul_equiv _ _ _ (idx hj).symm,
      submatrix_submatrix, Equiv.symm_symm, Equiv.self_comp_symm, submatrix_id_id, Matrix.mul_assoc]
  have h2 : (Nᴴ * -Jpq j (r - j) * N).toBlocks₂₂ = hQ (z (κ.symm τ)) := by
    simp [hN, Jpq, fromBlocks_conjTranspose, fromBlocks_neg, fromBlocks_multiply, hQ, sub_eq_neg_add]
  have h3 : X.gramPos (stdMat X hj κ z) τ = ((hQ (z (κ.symm τ))).submatrix (finCongr hp) (finCongr hp))ᵀ := by
    ext a b
    have e : ∀ a : Fin X.p0, (idx hj).symm (Sum.inr (finCongr hp a)) = Fin.castLE X.p0_le a :=
      fun a => Fin.ext (idx_symm_inr hj _)
    rw [← h2, ← h1]
    simp only [transpose_apply, submatrix_apply, toBlocks₂₂, of_apply, reindex_apply, e, Data.gramPos]
  rw [h3]
  exact (PosDef.submatrix (hz (κ.symm τ)) (finCongr hp).injective).transpose


open Classical in
def stdFrame (hp : X.p0 = r - j) (z : Pt Tau j (r - j)) : X.dom :=
  if h : z ∈ DomI Tau j (r - j) then ⟨stdMat X hj κ z, stdMat_mem X hj κ hp h⟩
  else ⟨stdMat X hj κ 0, stdMat_mem X hj κ hp fun _ => zero_mem_hcDom _ _⟩

theorem stdFrame_val (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    (stdFrame X hj κ hp z).1 = stdMat X hj κ z := by rw [stdFrame, dite_eq_left hz]

theorem domPt_stdFrame (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    domPt X hj κ (stdFrame X hj κ hp z).1 = z := by rw [stdFrame_val X hj κ hp hz, domPt_stdMat]

end Std

section Tor

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ)

abbrev torC : Scheme.{0} := pullback Y.s (spMap σ)

abbrev torStr : torC Y σ ⟶ Sp ℂ := pullback.snd Y.s (spMap σ)

abbrev torPr : torC Y σ ⟶ Y.X := pullback.fst Y.s (spMap σ)

abbrev TorPts : Type := CxPts (torStr Y σ) (RingHom.id ℂ)

variable {Y σ}

variable (Y)

def ptC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.XF c := ptF (S := CAt σ) y

def xC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.X := y.x

theorem ptC_fst (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.fst _ _ = xC y := pullback.lift_fst _ _ _

theorem ptC_snd (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.snd _ _ = spMap σ := pullback.lift_snd _ _ _

def torPt (y : FrPt Xo c (CAt σ)) : TorPts Y σ :=
  ⟨pullback.lift (ptC y ≫ Y.j) (spMap (RingHom.id ℂ)) (by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, ptC_snd, ← Spec.map_comp, ← Spec.map_comp]
      rfl), pullback.lift_snd _ _ _⟩

theorem torPt_pr (y : FrPt Xo c (CAt σ)) : (torPt Y y).1 ≫ torPr Y σ = ptC y ≫ Y.j := pullback.lift_fst _ _ _

abbrev LieAt (y : TorPts Y σ) : Type := TanM (y.1 ≫ torPr Y σ) Y.t.G


variable (σ) in
abbrev LieForm : Type := ∀ y : TorPts Y σ, LieAt Y y →ₗ[ℂ] LieAt Y y →ₗ⋆[ℂ] ℂ

def lieEquiv (y : FrPt Xo c (CAt σ)) : TanM (xC y) Xo.univ.t.G ≃ₗ[ℂ] LieAt Y (torPt Y y) :=
  (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm.trans (pushE Y.m (ptC y) (torPt_pr Y y).symm)

end Tor

section Bd

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ}

variable (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)


def letter (t : Tau) : Psi H := (letterAt hσ).symm (T t)


variable [Fintype Tau]


variable (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k)))

variable {Y U hU e hσ T B}

end Bd

section Flat

open GlobalTheory.FlatLine GlobalTheory.AllWt

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {x : ℝ}
  (sig : ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : Psi H), FlatSec (fun σ => (U σ).toPj) x Z τ)
  {σ : c.F →+* ℂ} (hU : IsUnf (U σ)) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)

variable {U sig hU hσ T}

end Flat

end GlobalTheory.TrueCx
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TrueColsTest

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Normal

variable {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)

end Normal

variable {B : Base} {X : PreX B.toPre} {I : TC B X}


section Gen
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mt_finite {R : Ranks} {J : ChainIn E K ι R} (Q : PerIn J) (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) :
    FiniteDimensional ℂ (Q.Mt emb σ) := by
  letI := Q.clFin h
  haveI : FiniteDimensional ℂ (VV ℂ Q.sgT) := Module.Finite.of_basis (bVV ℂ Q.sgT)
  let r : Q.Mt emb σ →ₗ[ℂ] (Q.S'.Cl → VV ℂ Q.sgT) :=
    { toFun := fun F c => ⟨F.1 c.1 (Q.S'.rep c), (F.2 c.1 _).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective r ((injective_iff_map_eq_zero r).2 fun F hF => ?_)
  apply Subtype.ext
  funext b d
  have h0 : F.1 b (Q.S'.rep (Q.S'.cl b d)) = 0 := congrArg Subtype.val (congrFun hF (Q.S'.cl b d))
  have h1 := (F.2 b (Q.S'.rep (Q.S'.cl b d))).2 (Q.S'.mv b d) (by rw [hH]; trivial)
  rw [h0, map_zero, smul_zero] at h1
  exact (congrArg (F.1 b) (Q.S'.mv_smul b d)).symm.trans h1
end Gen


theorem ipC_herm (l : I.Laws) (u : B.Word) (x y) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 y x) = ((I.cols l).fm u).ipC 0 x y := by
  unfold MemberForms.ipC

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  congr 1
  · simp [ColumnChain.wt]
  · exact (ClassSumPos.ipVal_herm _ _ _ _ _).symm

theorem ipC_pos (l : I.Laws) (u : B.Word) (x) (hx : x ∈ ((I.cols l).mem u).A.Mu0) (h0 : x ≠ 0) :
    0 < (((I.cols l).fm u).ipC 0 x x).re := by
  letI := (I.chIn u I.mu0).clFin (l.ch u _) 0
  exact (ClassSumPos.classSum_pos_herm (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (base_fOk B) ((l.ch u _).step 0)).1 x hx h0

theorem fits (l : I.Laws) : RowsRestModel.Fits (I.cols l)
    fun a => Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL) := by
  have key : ∀ u a, Nonempty (((I.cols l).PTw u a).Mt ≃ₗ[ℂ]
      RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) := fun u a => by
    haveI := mt_finite B.fields.emb B.embLL (I.perIn B.u₀ a) (l.per _ a) fun _ => rfl
    have key : Nonempty ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL ≃ₗ[ℂ]
        RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq finrank_euclideanSpace_fin.symm
    exact key
  refine ⟨fun u => key u I.mu0, key, fun u x y => ipC_herm l u _ _, fun u x => ?_, fun u x hx => ?_⟩
  · by_cases h0 : x.1 = 0
    · simp [h0, MemberForms.ipC]
    · exact (ipC_pos l u x.1 x.2.1 h0).le
  · by_contra h0
    have := ipC_pos l u x.1 x.2.1 fun e => h0 (Subtype.ext e)
    rw [hx] at this
    simp at this

theorem later (l : I.Laws) (hB : StagesInhab.HasLetters B.toPre) : Nonempty (TC.Later B (I.cols l)) := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  let W := RowsRestModel.model (fits l) 1 1 1
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => ipC_herm l u x y) (fun u x hx h => ipC_pos l u x hx h) (show 1 ≤ 2 * 1 by omega)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  exact ⟨⟨GaloisStage.adapt W, V, S, N, G⟩⟩

theorem kStd_spec (X : PreX B.toPre) (u : B.Word) (n : ℕ) :
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (kStd X u n) p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (kStd X u n) = 1) ∧
    ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 (((kStd X u n)⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) :=
  Classical.epsilon_spec (BasePoint.exists_kStd X (base_fields_primes_ok B X).2.1 u n)

end GlobalTheory.Mem.Col2.TrueColsTest

end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain _root_.Formalism.L2 Formalism.L2.NT



structure NAllC (D : D7) (C : NChoice D) where
  gal : NGalTied D
  n : NormalizedHeckeDataPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : ChoiceC D C
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y

def GoodCl (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, TwistedAt D w →
    (Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace (C.twI w) ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w) ∧ I.Ok (C.twI w)) →
    ExpGood D I (avD D (avDesign D) (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩

variable {D : D7} {C : NChoice D} {I : TwIn D}

def NAllC.toAll (A : NAllC D C) (h : GoodCl D C I) : NormalizedTwistCompatibility D C I :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, h, A.choice.conj⟩ }

def NAllC.ofAll (A : NormalizedTwistCompatibility D C I) : NAllC D C :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, A.choice.conj⟩ }

theorem goodCl_of_all (A : NormalizedTwistCompatibility D C I) : GoodCl D C I := A.choice.good

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

structure PhtOn {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (Wd : WDSide D T) (fr : OmFrame D)
    (p : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ), (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → Prop) : Prop where
  card : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (τ : D.host.E →+* Qbar l) (w : PlE D.host), p l a r →
    (∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ ‖τ (x : D.host.E)‖ < 1) → Wd.IsdRW l ι r w → Multiset.card (Wd.jumpsW l ι r τ) = a

def PhtCmp : Prop :=
  ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Wd : WDSide D T), PhtOn Wd fr fun l _ a r =>
    Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))

end GlobalTheory.HeightCounting

end
end
