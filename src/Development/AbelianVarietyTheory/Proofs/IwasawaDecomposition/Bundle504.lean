module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle419
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle475
import Formalism.LocalToGlobal.Columns.Bundle014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle301
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle428
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle397
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle398
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle501
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr



theorem goodO_setDiv : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  intro D nch xd N h hg
  obtain ⟨⟨⟨E, N0, S⟩, hE, hA, hC⟩, hsep⟩ := hg
  subst hE
  exact ⟨⟨⟨{ (twEOf xd) with }, N0, S⟩, rfl, hA, hC⟩, hsep⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.R3.Rw.NormTie

section
open _root_.Formalism.L2.Col
variable {Y : Fields} {Pr : Primes Y} {R : Ranks} (W : Wts Y Pr.Word R) (Ch : Chars Y Pr R.m)
  (sel : HeightOneSpectrum (𝓞 Y.F) → HeightOneSpectrum (𝓞 Y.E)) {S : Set ℕ} (mu : Tup Y.F Y.E Y.K S)
  (P : Formalism.L2.Col.LevFam Y.E Y.K R.r Pr.vGs) (hX : Y.Ok)

theorem isFormOf_zOf (y) : IsFormOf W Ch sel mu hX P (ColTie.zOf W Ch sel mu P hX y) (TieModel.frm W Ch sel mu hX P y) :=
  ⟨(ColTie.resK W Ch sel mu hX).symm (ColTie.formK W Ch sel mu P hX y), ColTie.zOf_mem W Ch sel mu P hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

end



theorem normAt_eq_norm_tie : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  intro X px I hX Xg tr a O _ φ s t e hcrd x
  have hs := GlobalTheory.Mem.ColTie.zOf_surjective X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX
  obtain ⟨y, rfl⟩ : ∃ y, (GlobalTheory.Mem.ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) = x := hs x
  have hF := isFormOf_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y
  obtain ⟨x', hx', hj⟩ := hcrd y
  have hx2 : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x' (TieModel.frm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y) := hx'
  have hxx := TieModel.isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hx2 hF
  subst hxx
  rw [← hj]
  have hmk := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX).2
    (InfinitePlace.mk X.B.embLL) (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)
  have hip : (Formalism.L2.Col.mtildeGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)).ip
      (Formalism.L2.Col.mtildeOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I))
      (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 =
      Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y :=
    ColTie.ipLev_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y
  have hin : inner ℂ (t.j y) (t.j y) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) :=
    t.forms.inner y y
  have hσ : ∀ z : X.B.fields.K, X.B.embLL (star z) = starRingEnd ℂ (X.B.embLL z) := ColTie.sig_starCx X.B
  have hn : ((‖t.j y‖ ^ 2 : ℝ) : ℂ) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) := by
    rw [← hin, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [LinearEquiv.refl_apply, Formalism.L2.Col.GSD.ipAt_eq_ipEmb] at hmk
  rcases InfinitePlace.embedding_mk_eq X.B.embLL with he | he
  · rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ, hip] at hmk
    have h2 := Complex.ofReal_injective (hmk.trans hn.symm)
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · have hσ' : ∀ w : X.B.fields.K, (ComplexEmbedding.conjugate X.B.embLL) (star w) =
        starRingEnd ℂ ((ComplexEmbedding.conjugate X.B.embLL) w) := by
      intro w
      simp only [ComplexEmbedding.conjugate_coe_eq, hσ]
    rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ', hip, ComplexEmbedding.conjugate_coe_eq, ← hn, Complex.conj_ofReal] at hmk
    have h2 := Complex.ofReal_injective hmk
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end GlobalTheory.Mem.R3.Rw.NormTie
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.CsumForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

theorem ipK_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform ((csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← ipK_eq_card_mul_ipLev W Ch sel mu P hX, ipK_zOf_eq]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section TC

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι)

theorem cSum_toCx (x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I))
    (x' : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x') =
      B.embLL (ipLev (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX x x') := by
  rw [Df.cSum_apply]
  unfold ipLev GSD.ip GSD.ipOf CSD.csum

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold Df.cTerm
  rw [map_mul, map_inv₀, map_natCast, GSD.wt_eq]
  congr 1
  exact (map_pairV_one _ _ (sig B) (fun x => B.starLL_cx x) _ _).symm

end TC

theorem cSum_toCx_rowForm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  intro X px I hX Xg tr a y x hx
  obtain ⟨F, h, hF, rfl⟩ := hx
  have e1 : ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX F =
      ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := eq_of_heq hF
  have e2 : (⟨F.1, h⟩ : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) =
      ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := by
    apply Subtype.ext
    show F.1 = ((ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)).1
    rw [← e1, LinearEquiv.symm_apply_apply]
  rw [cSum_toCx, e2]
  exact congrArg X.B.embLL (ipLev_zOf_eq (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y)

end GlobalTheory.Mem.CsumForm
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.PerId
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_crd_equiv (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ}
    {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) :
    ∃ e : Df.MtCx I a ≃ₗ[ℂ] s.A.T, ∀ y, IsCrd I hX a e
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y) := by
  obtain ⟨e, he⟩ := ColTie.exists_equiv_of_bases (σ := ColTie.sig X.B)
    (n := ColTie.dimP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX)
    (ColTie.jP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B)) t.j
    (ColTie.linearIndependent_jP_single (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    (ColTie.span_range_jP_single_eq_top (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    t.forms.li t.forms.span
  refine ⟨e, fun y => ⟨ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y, ?_, (he y).symm⟩⟩
  exact ⟨(ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y),
    ColTie.zOf_mem (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩



theorem exists_perT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  intro B f T w Z hX Xg tr p tA
  have hE := fun a : w.I.ι => exists_crd_equiv (w.st Z) w.I hX Xg tr a (tA a)
  choose e he using hE
  have hG : ∀ u a, ∃ g : Df.MtCx w.I a ≃ₗ[ℂ] (TC.per w.I w.l u a).Mt, ∀ F, Df.SameForm w.I w.l u a F (g F) := fun u a =>
    Df.mtCx_equiv_per w.I w.ok w.pins w.l hX u a
  choose g hg using hG
  refine ⟨⟨fun u => (g u w.I.mu0).symm.trans (e w.I.mu0), fun u a => (g u a).symm.trans (e a)⟩, ⟨⟨e, ?_, ?_, he⟩⟩⟩
  · intro u F
    have h1 : ((g u w.I.mu0).symm.trans (e w.I.mu0)).symm (e w.I.mu0 F) = g u w.I.mu0 F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u w.I.mu0 F
  · intro u a F
    have h1 : ((g u a).symm.trans (e a)).symm (e a F) = g u a F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u a F

end GlobalTheory.Mem.R3.Rw.PerId
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ex

@[reducible] def reset {B : Base} {C : Cols B} (W : RowsRest B C) (mt ma : B.places.Pl → C.Tup)
    (hmt : ∀ v, mt (B.places.conj v) = mt v) (hma : ∀ v, ma (B.places.conj v) = ma v)
    (hor : ∀ v, ma v = C.mu0 ∨ ma v = mt v) : RowsRest B C :=
  { W with
    muAt := ma
    muAt_conj := hma
    muTw := mt
    muTw_conj := hmt
    muAt_or := hor
    kaBig := GlobalTheory.Mem.DfGen.kaBigB B
    kaSmall := GlobalTheory.Mem.DfGen.kaSmallB B
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host }

theorem kapDef_of_ka {B : Base} {C : Cols B} (W' : RowsRest B C) (hb : W'.kaBig = GlobalTheory.Mem.DfGen.kaBigB B)
    (hs : W'.kaSmall = GlobalTheory.Mem.DfGen.kaSmallB B) : ∀ V S N G, DV.KapDef (assemble B C W' V S N G) := by
  intro V S N G j _ _ τ
  refine ⟨fun i => ?_, fun c => ?_⟩
  · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
    rw [hb]
    exact (GlobalTheory.Mem.DfGen.aPlusB_int B j τ i).choose_spec.symm
  · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
    rw [hs]
    show ((-(GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose : ℤ) : ℚ) = -GlobalTheory.Mem.DfGen.aMinusB B j τ c
    push_cast
    rw [← (GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose_spec]

end GlobalTheory.Mem.R3.Rw.Ex

end

open GlobalTheory.Mem.R3.Rw.Ex in
theorem GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  intro B f T w hX Wt hWt
  classical
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  have hmem : ∀ v, ∃ a, w.I.xi a = T.xiTw f v := fun v => by
    have h : T.xiTw f v ∈ Set.range w.I.xi := by
      rw [w.xi_range]; exact Or.inr ⟨v, rfl⟩
    exact h
  have hconj : ∀ v, T.xiTw f (B.places.conj v) = T.xiTw f v := fun v => by
    unfold TwDat.xiTw
    rw [GlobalTheory.Mem.Top.TwFin.resChar_conj, (T.conj v).1]
  let mt : B.places.Pl → w.C.Tup := fun v => Classical.choose (hmem v)
  have hmt : ∀ v, mt (B.places.conj v) = mt v := fun v => by
    show Classical.choose (hmem (B.places.conj v)) = Classical.choose (hmem v)
    have : ∀ x y (hx : ∃ a, w.I.xi a = x) (hy : ∃ a, w.I.xi a = y), x = y →
        Classical.choose hx = Classical.choose hy := by
      rintro x y hx hy rfl; rfl
    exact this _ _ _ _ (hconj v)
  let ma : B.places.Pl → w.C.Tup := fun v => if v ∈ Wt then mt v else w.C.mu0
  have hma : ∀ v, ma (B.places.conj v) = ma v := fun v => by
    simp only [ma, hWt v, hmt v]
  have hor : ∀ v, ma v = w.C.mu0 ∨ ma v = mt v := fun v => by
    by_cases h : v ∈ Wt
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  refine ⟨reset R.W mt ma hmt hma hor, ⟨fun v => Classical.choose_spec (hmem v), fun v h => if_pos h, fun v h => if_neg h⟩,
    fun W' hb hs => kapDef_of_ka W' hb hs, GlobalTheory.MemN.shaOK_shaTrue B.toPre⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.HeightCounting.FirstFacts

theorem pair_of_over (D : D7) {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (hPq : ∀ v, NG.OverPl (Pq v) v) (P P' : PlE D.host) (hc : IsConjPl D.host P P') (hne : P ≠ P') :
    P ∈ Set.range Pq ↔ P' ∉ Set.range Pq := by
  have e := (GlobalTheory.PlacePair.comap_eq_iff D P P').2 (Or.inr hc)
  constructor
  · rintro ⟨v, rfl⟩ ⟨v', rfl⟩
    obtain rfl : v = v' := HeightOneSpectrum.ext ((hPq v).symm.trans (e.trans (hPq v')))
    exact hne rfl
  · intro h
    let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := P.under _
    have hv : NG.OverPl P v := rfl
    rcases (GlobalTheory.PlacePair.comap_eq_iff D P (Pq v)).1 (hv.trans (hPq v).symm) with e1 | e1
    · exact ⟨v, e1.symm⟩
    · exact absurd ⟨v, GlobalTheory.GalChar.isConjPl_unique e1 hc⟩ h

theorem vstd_of_over {K : GlobalTheory.Mem.Top.Ctx} (X : GlobalTheory.Mem.Stages) (hX : K.Over X.B.toPre) (i : Fin X.toD7.R.m) :
    FWT.VStd X.toD7 i := by
  obtain ⟨-, -, -, -, -, hVf, -⟩ := GlobalTheory.Mem.HostFrames.frames_of_over K X hX
  obtain ⟨h1, h2⟩ := hVf i
  rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
  refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
  · rw [HSpace.gram, h1, Matrix.one_apply]
  · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
    refine forall_congr' fun a => ?_
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]; exact y.2
    · intro h
      exact ⟨⟨x a, h⟩, rfl⟩

theorem mem_range_of_mem_QE {X : Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {Q : HeightOneSpectrum (𝓞 X.E)} : ∀ {ξ}, Q ∈ Col.QE sel ξ → Q ∈ Set.range sel := by
  classical
  intro ξ h
  unfold Col.QE at h
  split_ifs at h
  · obtain ⟨v, -, e⟩ := Finset.mem_image.1 h
    exact ⟨v, e⟩
  · exact absurd h (Finset.notMem_empty _)

end GlobalTheory.HeightCounting.FirstFacts

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DnMove



theorem gl_inv_map_mul_map {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (A : GL (Fin n) E) (y : Matrix (Fin n) (Fin n) ℂ) :
    ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map φ * ((A : Matrix (Fin n) (Fin n) E).map φ * y) = y := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem tr_eq_of_isTr {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (hY : I.IdY l Z u a i hi eY) (b : (I.stp u a i).β) (g0 : (I.stp u a i).G b)
    (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hγ : (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam b g0) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i)
    (hT : IsTr (atInf (embT (I.rec7 l Z)) γ.1.1) (eY s') (eY s)) :
    (I.stp u a i).tr B.fields.emb B.embLL b g0 h s = B.embLL (((I.stp u a i).chr b g0 : B.LLˣ) : B.LL) * h s' := by
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g0)⁻¹ s) = _
  congr 2
  apply Subtype.ext
  funext τ
  have h1 := hT τ
  rw [hY, hY] at h1
  show (((I.stp u a i).gam b g0)⁻¹ : GL (Fin (B.R.N i)) B.fields.E).1.map _ * s.1 τ = s'.1 τ
  have h2 : atInf (embT (I.rec7 l Z)) (γ.1.1) τ = (((I.stp u a i).gam b g0 : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E).map (embAt B.embLL B.fields.emb τ) := by
    rw [← hγ]
    show (γ.1.1).map (embT (I.rec7 l Z) τ) = (γ.1.1).map (embAt B.embLL B.fields.emb τ)
    congr 1
    ext x
    show B.host.emb τ x = B.embLL (B.tauLL τ x)
    rw [← GlobalTheory.Mem.PreXModel.embLL_tauLL]
    rfl
  rw [h1, h2]
  exact gl_inv_map_mul_map _ _ _

theorem dnNatTieG_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → DnNatTieG L eY eV K := by
  intro B X I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL
  intro v β c g hg
  have hβ := GlobalTheory.T.move_down_level_prime_keeps_chart I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  obtain ⟨γ, η, κ, hγ, hη, hrel, hchi⟩ := GlobalTheory.T.moveDown_levelPrime_adelic_factorisation I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg hβ
  refine ⟨hβ, γ, η, κ, hη, hrel, GlobalTheory.T.downMove_localDualLattice_eq_levelPrime I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ,
    GlobalTheory.T.move_down_level_functional_eq I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ, ?_⟩
  intro h s s' hT
  show (I.stp u a i).trTo B.fields.emb B.embLL c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) h s = _
  rw [hchi]
  exact tr_eq_of_isTr I l Z u a i hi eY hY _ _ γ hγ h s s' hT

end GlobalTheory.DnMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nonvanishing_finite_datum_definite_lift : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q P : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D), T.rank ≤ S.rank → IsIdemSum e P → (∀ PP ∈ Pg, PP ∈ P) → (∀ PP ∈ Q, PP ∈ P) → ∃ x : WO S T, IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := by
  first | exact @GlobalTheory.AdjDatumNe.exists_datum_ne_zero | exact GlobalTheory.AdjDatumNe.exists_datum_ne_zero | (intros; apply GlobalTheory.AdjDatumNe.exists_datum_ne_zero <;> assumption)
end
