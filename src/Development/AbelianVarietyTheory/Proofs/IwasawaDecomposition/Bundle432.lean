module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle425
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle417
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
public import Formalism.LocalToGlobal.Columns.Record
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.TiedUpDnA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.Columns.Bundle032
public import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem secondG_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

end GlobalTheory.Mem.Top.GroupRetwisting
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



theorem _root_.GlobalTheory.T.liftResidueTwistCharacter_eq_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  first | exact @GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar | exact GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar | (intros; apply GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



namespace GlobalTheory.Mem.LevResXi

theorem embLL_resChar_eq_xiR : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (t : TupU I U) (w : Pl X.toD7.host.E),
      w ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) → ∀ (u : (kP w)ˣ),
      X.toD7.what₂.embLL ((Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w u :
        X.B.fields.Kˣ) : X.B.fields.K) = ((L.xiR t w u : ℂˣ) : ℂ) := by
  intro X px I U L hI hV hL t w hw u
  rw [xiR_eq_map_resChar X px I U L hI hV hL t w hw u]
  rfl

end GlobalTheory.Mem.LevResXi
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



theorem _root_.GlobalTheory.T.typePrimes_disjoint_twistChosenPrimes : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ t : TupU I U, Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel t.1) := by
  first | exact @GlobalTheory.Mem.LevDisj.places_disjoint | exact GlobalTheory.Mem.LevDisj.places_disjoint | (intros; apply GlobalTheory.Mem.LevDisj.places_disjoint <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_finiteGroupIdentification_fixedPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), IsPlacewiseIdentity X (px := px) eG ∧ (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  first | exact @GlobalTheory.Mem.R3.exists_grpIdent | exact GlobalTheory.Mem.R3.exists_grpIdent | (intros; apply GlobalTheory.Mem.R3.exists_grpIdent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.GoodSetExists

section Gen

variable {G : Type} [Group G] [Fintype G]

theorem one_ne_zero_of_mem (ψ : G → ℂ) (h : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) : ψ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := h
  intro e
  rw [Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at e
  exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem coeff_conj_of_center {e : MonoidAlgebra ℂ G} (he : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (x y : G) :
    e.coeff (y * x * y⁻¹) = e.coeff x := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (y * x))
    ((Subalgebra.mem_center_iff.1 he (MonoidAlgebra.single y 1)).symm)
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at h
  exact h

end Gen

section Record

variable (X : Stages) (px : PreX X.B.toPre)

theorem exists_goodSet_Ks (eR : Gc X.B px ≃* G0g X.toD7.nd) :
    ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  classical
  let σ := X.B.embLL
  let f := MonoidAlgebra.domCongr ℂ ℂ eR.symm
  let e : MonoidAlgebra ℂ (Gc X.B px) := f X.toD7.ntypes.e0
  have hcoeff : ∀ g, e.coeff g = X.toD7.ntypes.e0.coeff (eR g) := fun g => by
    simp [e, f, MonoidAlgebra.domCongr_apply]
  obtain ⟨hcen0, hid0⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  have hid : e * e = e := by simp only [e, ← map_mul, hid0]
  have hcen : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc X.B px)) := by
    refine Subalgebra.mem_center_iff.2 fun b => ?_
    obtain ⟨c, rfl⟩ := f.surjective b
    simp only [e, ← map_mul, (Subalgebra.mem_center_iff.1 hcen0 c)]
  have hcard : Fintype.card (Gc X.B px) = X.B.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eR.toEquiv]
    have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
    rw [Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
    rfl
  obtain ⟨z, hzK, hz⟩ := X.B.roots_Ks X.B.restRowsFiniteGroupCard (by simp)
  have hzp : IsPrimitiveRoot z (Fintype.card (Gc X.B px)) := by
    rw [hcard, ← IsPrimitiveRoot.map_iff_of_injective σ.injective]
    rw [show σ z = _ from hz]
    exact Complex.isPrimitiveRoot_exp _ X.B.restRowsFiniteGroupCard_pos.ne'
  refine ⟨Formalism.L2.Col.XgE σ e, Model.goodSet_of_idem X eR _ Formalism.L2.Col.XgE_irr fun g => ?_, fun g => ?_⟩
  · let A := (Formalism.L2.Col.gxIrrSet_finite (G := Gc X.B px) (k := ℂ)).toFinset
    have hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := Gc X.B px) ℂ := fun ψ => Set.Finite.mem_toFinset _
    have hexp := GlobalTheory.T.centralIdempotent_eq_sum_character_idempotents A e (fun ψ hψ => one_ne_zero_of_mem ψ ((hA ψ).1 hψ)) (GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality A hA)
      (fun ψ hψ x => GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar e (coeff_conj_of_center hcen) ψ ((hA ψ).1 hψ) x) hid
    have himg : (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) =
        (Formalism.L2.Col.XgE σ e).image (fun χ g => σ (χ g)) := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_image, hA, Formalism.L2.Col.mem_XgE]
      constructor
      · rintro ⟨hψ, hs⟩
        obtain ⟨χ, hχ, hχψ⟩ := GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card σ z hzp ψ hψ
        refine ⟨χ, ⟨hχ, ?_⟩, funext hχψ⟩
        simp only [hχψ]
        exact hs
      · rintro ⟨χ, ⟨hχ, hs⟩, rfl⟩
        exact ⟨GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet σ χ hχ, hs⟩
    have hinj : Set.InjOn (fun (χ : Gc X.B px → X.B.LL) g => σ (χ g)) (Formalism.L2.Col.XgE σ e : Set _) :=
      fun χ _ χ' _ h => funext fun g => σ.injective (congrFun h g)
    rw [← hcoeff g]
    conv_rhs => rw [hexp]

    rw [himg, coeff_idemOf, coeff_idemOf, Finset.sum_image hinj, map_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp [σ, map_div₀, map_mul, map_natCast]
  · rw [coeff_idemOf]
    have hcl : ∀ y ∈ Subring.closure ({z} : Set X.B.LL), y ∈ X.B.Ks := fun y hy => by
      have : Subring.closure ({z} : Set X.B.LL) ≤ X.B.Ks.toSubfield.toSubring := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        exact hzK
      exact this hy
    refine IntermediateField.sum_mem _ fun χ hχ => ?_
    have hχ' := Formalism.L2.Col.XgE_irr χ hχ
    exact IntermediateField.mul_mem _ (IntermediateField.div_mem _ (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' 1))
      (IntermediateField.natCast_mem _ _)) (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' _))

end Record

end GlobalTheory.Mem.R3.GoodSetExists

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.psiLevelPairCompatible_of_columnLevels : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) → (∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) → PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) := by
  first | exact @GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf | exact GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf | (intros; apply GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_charts_reading_step_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  first | exact @GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | exact GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | (intros; apply GlobalTheory.Mem.Col2.TC.Chart0.charts_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnLat

theorem locP_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : p = q) (L : Submodule R W) : Formalism.HermitianLatticesTheory.localization₂ p L = Formalism.HermitianLatticesTheory.localization₂ q L := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem extF_eq (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E))
    (g : Module.Dual (Res P) (TDat.Red M P)) (y : Fin n → E) : TDat.extF M P g y = modP.ext P M g y := by
  classical
  unfold TDat.extF
  split_ifs with h
  · obtain ⟨s, hs, z, hz, hgz⟩ := h.choose_spec
    have hsy : s • y ∈ M := hz ▸ z.2
    have e := modP.ext_spec P M g y hs hsy
    have ez : z = ⟨s • y, hsy⟩ := Subtype.ext hz
    subst ez
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [e, ← hgz]
    rfl
  · by_cases hy : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M
    · exfalso
      obtain ⟨s, hs, hsy⟩ := hy
      exact h ⟨modP.ext P M g y, s, hs, ⟨s • y, hsy⟩, rfl, (modP.ext_spec P M g y hs hsy).symm⟩
    · unfold modP.ext
      rw [dite_eq_right hy]

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem ok_dn_extF {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : M = d.dnN P) (g : Module.Dual (Res P.1) (TDat.Red M P.1)) (hg : g ≠ 0) :
    (d.dn P (TDat.extF M P.1 g)).Ok := by
  subst hM
  have e : TDat.extF (d.dnN P) P.1 g = modP.ext P.1 (d.dnN P) g := funext (extF_eq _ _ g)
  rw [e]
  have hF := modP.ext_funAt P.1 (d.dnN P) g
  refine hd.dn P hP hF.add hF.smul hF.off ?_
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra H
    push Not at H
    exact hg (LinearMap.ext H)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x.1, x.2, by rw [modP.ext_of_mem]; exact hz⟩

theorem locP_Lsh_dn {a : 𝓞 E} (ha : SepElt ST a) {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    {f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal} (hd' : (d.dn P f').Ok) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dn P f').Lsh = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L := by
  rw [hd'.locP_Lsh ha P]
  show Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dnN P) = _
  rw [(hd.dnN_spec P hne).2.2.2, tud_locP_L ha ⟨d, hd⟩ P]
  exact le_antisymm
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact lv_kerAt_le ⟨d, hd⟩ ha P hx)
    (localization_le_of_smul_mem (ha.off P) fun x hx => lv_smul_LshKer_mem ⟨d, hd⟩ ha P hx)

theorem mulLat_Lsh_rep {K : Type} [Field K] [NumberField K] [StarRing K] (S : GStep E K n) (hS : S.Ok) (b : S.β) (d : S.D b)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : γ = (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E)) :
    Formalism.L2.Forms.mulLat γ (S.Lsh b (S.rep (S.cl b d))) = S.Lsh b d := by
  subst hγ
  ext x
  unfold Formalism.L2.Forms.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) y).2 hy
    rwa [S.mv_smul] at h
  · intro hx
    refine ⟨((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x, ?_, ?_⟩
    · refine (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) _).1 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, S.mv_smul]
      exact hx
    · show (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.DnLat


open GlobalTheory.Mem.Col2.DnLat in

theorem GlobalTheory.Mem.Col2.TC.dn_locP_lat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (mulLat γ.1.1 (LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) = Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ
  obtain ⟨hg1, -, hcrd⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hlat := (hcrd u a).1
  have hPv : PvG (D := I.rec7 l Z) (I.resT l u a) v = (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    unfold PvG resT
    ext x
    exact Submodule.Quotient.mk_eq_zero _

  rw [@locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, @locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, hlat, hlat]
  have hdual : ∀ M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E),
      LdG (I.rec7 l Z) i hi M = Formalism.HermitianLatticesTheory.dual (hStd (I.rec7 l Z).host.E ((I.rec7 l Z).R.N i)) M := fun M => by
    unfold LdG
    rw [hg1]
    unfold dualL
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ M
  have hok : (I.atIn u a).Ok := l.lev u a
  have hT := hok.tied i
  have hSok : (I.stp u a i).Ok := (l.ch u a).step i
  have hmul := mulLat_Lsh_rep (I.stp u a i) hSok c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) (congrArg Units.val hγ)
  have hm := moveHyp_of_ok l.pr u v
  have hMove : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hm.ne, hm.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hsep := sepElt_of_ok l.pr u
  have hOk := ok_dn_extF (hT.ok c.1.1 ((I.stp u a i).rep c.1)) v hMove (hT.dnN_eq c.1.1 ((I.stp u a i).rep c.1) v) g hg
  have key : Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal
      (Formalism.L2.Forms.mulLat γ.1.1 ((I.stp u a i).Lsh c.1.1
        ((I.stp u a i).rep ((I.stp u a i).cl c.1.1 (((I.atIn u a).A i).dnPt v c.1 g))))) =
      Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (((I.atIn u a).A i).deco c.1.1 ((I.stp u a i).rep c.1)).L := by
    refine (congrArg (Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal)
      (hmul.trans ((hT.Lsh_eq _ _).trans (congrArg Deco.Lsh (hT.dn_deco _ _ _ _ hOk))))).trans ?_
    exact locP_Lsh_dn hsep (hT.ok _ _) v hMove.ne hOk
  exact (congrArg (fun M => Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (Formalism.L2.Forms.mulLat γ.1.1 M))
    (hdual _)).trans key
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.TorusTorsionPoint

theorem eq_torus_of_classify : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), FormalEq P.U.toUnifPre x₀ g₀ → ∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) (τ : Multiplicative P.D.toPre.X →* A'ˣ) (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → ∀ (g : GtPt P.D.toPre (Over.mk (spMap (f.comp a)))), (∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) → ∀ (h : Over.mk (spMap (f.comp a)) ⟶ N), GtPt.IsPull h.left g₀ g → h.left ≫ x₀.left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ := by
  intro E _ _ _ H R _ _ _ t P N g₀ x₀ hform A A' _ _ a ha f t₀ m₀ τ z hz g hg h hpull
  have ha' : ∀ x ∈ maximalIdeal R, (f.comp a) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, ha x hx, map_zero]
  have hρ := GlobalTheory.TorusPart.map_pow_one_eq_zero ha
  have hρ' := GlobalTheory.TorusPart.map_pow_one_eq_zero ha'
  have eR : (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ =
      (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X ≫ (P.U.gt 0).i.left) ≫
        pullback.fst t.G.hom (thick R (maximalIdeal R) 0) := by
    rw [Over.comp_left, Category.assoc]
    have k := GlobalTheory.TorusPart.gtTorus_left (P.U.gt 0) hρ m₀.cart
    exact (congrArg (z.left ≫ ·) k).trans (by simp only [Category.assoc])
  have hN : (h.left ≫ x₀.left) ≫ t.G.hom = GlobalTheory.TorusPart.thickPt 0 hρ' ≫ thick R (maximalIdeal R) 0 := by
    rw [GlobalTheory.TorusPart.thickPt_thick, Category.assoc, Over.w x₀, Over.w h]; rfl
  let y₁ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 t.G).left :=
    pullback.lift (h.left ≫ x₀.left) (GlobalTheory.TorusPart.thickPt 0 hρ') hN
  let y₂ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 t.G).left :=
    z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X ≫ (P.U.gt 0).i.left
  have e₁ : h.left ≫ x₀.left = y₁ ≫ pullback.fst t.G.hom (thick R (maximalIdeal R) 0) :=
    (pullback.lift_fst _ _ _).symm
  have hP := (GlobalTheory.TorsionFormCompare.formalEq_iff P.U.toUnifPre x₀ g₀).1 hform
  have hc := hP 0 (Sp A') h.left y₁ e₁.symm
  obtain ⟨hb, hv⟩ := (GlobalTheory.FormalPoint.hasCoords_iff _ 0 g₀ h.left y₁).1 hc
  suffices hy : y₁ = y₂ by rw [eR, e₁, hy]
  refine GlobalTheory.TorusCoord.ext_of_val (P.U.gt 0) y₁ y₂ ?_ ?_
  · rw [hb, ← hpull.1, (hg 0).1, GlobalTheory.TorusCoord.pG_left]
    have hk : (P.U.gt 0).i.left ≫ (P.U.gt 0).q.left =
        (splitTorus _ P.D.toPre.X).hom ≫ eSec (thickObj R (maximalIdeal R) 0 P.D.toPre.P.A) := by
      have := congrArg Over.Hom.left (P.U.gt 0).isKernel.w
      rw [Over.comp_left, Over.comp_left] at this
      exact this
    have hE : eSec (thickObj R (maximalIdeal R) 0 P.D.toPre.P.A) ≫
        pullback.fst P.D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
        thick R (maximalIdeal R) 0 ≫ eSec P.D.toPre.P.A :=
      GlobalTheory.UnitValue.eSec_pullback_fst _ _
    have hz' : z.left ≫ (splitTorus (Sp A) P.D.toPre.X).hom = spMap f := Over.w z
    have hfa : spMap f ≫ spMap a = spMap (f.comp a) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    simp only [y₂, Category.assoc]
    rw [reassoc_of% hk, hE, ← Category.assoc (GlobalTheory.SplitTorus.bcMap _ _), GlobalTheory.SplitTorus.bcMap_hom,
      Category.assoc, reassoc_of% (GlobalTheory.TorusPart.thickPt_thick hρ), reassoc_of% hz', reassoc_of% hfa]
    rfl
  · intro χ w J hJ
    rw [hv χ w J hJ]
    have l₁ : val (g₀.s χ) h.left w J = gm (𝟙 _) w ⊤ (unitOn (τ (Multiplicative.ofAdd χ))) := by
      have c₁ := val_corr hJ (hpull.2 χ) (𝟙 _)
      rw [val_pull hJ, Category.id_comp] at c₁
      exact c₁.symm.trans (GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) (𝟙 _) hJ)
    rw [l₁]
    let Z₀ : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :=
      Over.mk ((z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X) ≫
        (splitTorus _ P.D.toPre.X).hom)
    let τ' : Z₀ ⟶ splitTorus _ P.D.toPre.X :=
      Over.homMk (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X) rfl
    have k := GlobalTheory.TorusCoord.val_t_act (P.U.gt 0) τ' 1 χ (𝟙 Z₀.left) w J hJ
    have k₁ : 𝟙 Z₀.left ≫ (τ' ≫ (P.U.gt 0).i * 1).left = y₂ := by
      rw [_root_.mul_one, Category.id_comp, Over.comp_left]
      simp only [τ', y₂, Over.homMk_left, Category.assoc]
    have k₂ : val ((P.U.gt 0).t χ) (𝟙 Z₀.left ≫ (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 t.G).left) w J = 1 := by
      have e : (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 t.G).left = Z₀.hom ≫ eSec (thickObj R (maximalIdeal R) 0 t.G) := by
        rw [Hom.one_def, Over.comp_left]; rfl
      rw [e, Category.id_comp, ← val_pull hJ, val_corr hJ ((P.U.gt 0).t_unit χ), val_one]
    have k₃ : GlobalTheory.splitTorusPointsEquiv _ P.D.toPre.X Z₀ τ' (Multiplicative.ofAdd χ) =
        unitOn (τ (Multiplicative.ofAdd χ)) := by
      refine Units.ext ?_
      rw [← hz χ, GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val]
      simp only [τ', Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        GlobalTheory.SplitTorus.bcMap_appTop_chi]
    rw [k₁, k₂, k₃, _root_.mul_one] at k
    exact k.symm

end GlobalTheory.TorusTorsionPoint
end
end
