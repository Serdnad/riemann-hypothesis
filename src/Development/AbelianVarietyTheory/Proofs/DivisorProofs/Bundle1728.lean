module

public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
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
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedIdem

open _root_.Formalism.L2.Col

variable {D : D7}

theorem sigR_mem_intAE {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha, cO _ x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem finPart_cA (z : Formalism.L2.Theta.AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem finPart_conj_mem {e : Formalism.L2.Theta.AE D} {x : D.host.E}
    (h : finPart D (e * incA D x) ∈ intAE D) : finPart D (cA D e * incA D (star x)) ∈ intAE D := by
  have := sigR_mem_intAE h
  rwa [← finPart_cA, RingHom.map_mul, cA_incA] at this

theorem isIdemAt_conj {e : Formalism.L2.Theta.AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e Q)
    (h : ∀ x, x ∈ P.asIdeal ↔ cO _ x ∈ Q.asIdeal) : IsIdemAt (cA D e) P := by
  obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
  refine ⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, h3, by rw [cA_cA, add_comm, h4]⟩,
    fun x h0 => ?_⟩
  have h0' : cO _ x ≠ 0 := by
    intro h1
    apply h0
    rw [← cO_cO x, h1, map_zero]
  rw [h, h5 _ h0']
  refine not_congr ⟨fun hm => ?_, fun hm => ?_⟩
  · have := finPart_conj_mem hm
    rw [star_inv₀] at this
    have h6 : star ((cO _ x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := star_star (x : D.host.E)
    rwa [h6] at this
  · have := finPart_conj_mem hm
    rw [star_inv₀, cA_cA] at this
    exact this

theorem exists_isIdemAt : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal → ∃ e : Formalism.L2.Theta.AE D, IsIdemAt e P := by
  intro D P hP
  have hex : ∃ a ∈ P.asIdeal, cO _ a ∉ P.asIdeal := by
    by_contra hn
    push Not at hn
    apply hP
    ext x
    rw [mem_conjIdeal]
    exact ⟨fun hx => by simpa only [cO_cO] using hn _ hx, hn x⟩
  obtain ⟨a, ha, ha'⟩ := hex
  let v : HeightOneSpectrum (𝓞 D.host.F) := P.under (𝓞 D.host.F)
  have hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := rfl
  obtain ⟨e, he⟩ := GlobalTheory.MovedSplit.exists_splitAt D v ⟨P.asIdeal, P.isPrime, hv, a, ha, cO _ a, rfl, ha'⟩
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e he
  have hsub : (P.asIdeal : Set (𝓞 D.host.E)) ⊆ Q.asIdeal ∪ (Q.asIdeal.comap (cO _) : Ideal (𝓞 D.host.E)) := by
    intro x hx
    obtain ⟨n, hn, -⟩ := GlobalTheory.MovedSplit.exists_int D (x * cO _ x) (by
      show star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul', star_star, mul_comm])
    have h1 : n ∈ v.asIdeal := by
      rw [← hv, Ideal.mem_comap, hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hQv, Ideal.mem_comap, hn] at h1
    exact Q.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h | h
  · have : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact ⟨e, this ▸ hQ⟩
  · have := Q.isPrime
    have h2 := P.isMaximal.eq_of_le (Ideal.comap_ne_top (cO _) Q.isPrime.ne_top) h
    exact ⟨_, isIdemAt_conj hQ fun x => by rw [h2, Ideal.mem_comap]⟩

end GlobalTheory.MovedIdem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.GramFrame

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x u v : n → A) : Formalism.UG.hform τ J x (u + v) = Formalism.UG.hform τ J x u + Formalism.UG.hform τ J x v := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (x y : n → A) : Formalism.UG.hform τ J x (a • y) = a * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x : n → A) : Formalism.UG.hform τ J x 0 = 0 := by
  simp [Formalism.UG.hform]

variable {D : D7}

theorem sigR_inclE (x : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (D.sp.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem inclE_int (b : 𝓞 D.host.E) :
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (algebraMap (𝓞 D.host.E) D.host.E b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)

theorem hform_inclE {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (y i)) =
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y) := by

  simp only [Formalism.UG.hform, map_sum, map_mul, sigR_inclE, Matrix.map_apply]
  rfl

theorem pair_hatL {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (x y : Fin n → Formalism.IndefR.Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) x y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, hx0, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y0, hy0, rfl⟩ := hy
      rw [hform_inclE]
      obtain ⟨b, hb⟩ := h x0 hx0 y0 hy0
      rw [← hb]
      exact inclE_int b
    | zero => rw [hform_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [hform_add_right]; exact add_mem ha hb
    | smul s a _ ha => rw [Subring.smul_def, hform_smul_right]; exact mul_mem s.2 ha
  | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
  | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
    exact mul_mem (GlobalTheory.LevSplit.sigR_int s.2) ha

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_hform' {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    Formalism.UG.prV (E := E) v (Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
      (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x y) =
    Formalism.UG.hform (Formalism.UG.sigR σ (v.adicCompletion F))
      (J.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)))
      (fun i => Formalism.UG.prV (E := E) v (x i)) (fun i => Formalism.UG.prV (E := E) v (y i)) := by
  have hs : ∀ z, Formalism.UG.prV (E := E) v (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) z) =
      Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.prV (E := E) v z) :=
    fun z => RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) z

  simp only [Formalism.UG.hform, map_sum, map_mul, hs, Matrix.map_apply]
  rfl

theorem inv_int {n : ℕ} (σ : E →ₐ[F] E)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E)
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hlat : Submodule.IsFullLattice E Λ) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (hd : Formalism.L2.Forms.dualL (σ : E →+* E) J Λ ≤ Λ)
    (G' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hG' : Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
      J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.val * G' = 1) :
    ∀ i j, G' i j ∈ Formalism.L2.Herm.intAf F E := by
  intro i j
  have key : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
        (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x
        (β.val *ᵥ (G' *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.intAf F E := by
    intro x hx
    have ha := (hfr x).1 hx
    have e : x = β.val *ᵥ ((β⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, GlobalTheory.DualCompletion.hform_mulVec_left]
    have e2 : (Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
        J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ (β.val *ᵥ (G' *ᵥ Pi.single j 1)) =
        Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG', Matrix.one_mulVec]
    rw [e2]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hσ _ (ha k)) ?_
    rw [Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k)) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
            (v.adicCompletionIntegers F).toSubring) Λ := by
    intro v
    have hm := (GlobalTheory.DualCompletion.mem_latS_dualL σ J hJ v Λ hlat
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k))).2
    refine Submodule.span_mono (Set.image_mono hd) (hm fun u hu => ?_)
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x0, hx0, rfl⟩ := hu
      have h3 := key _ (Submodule.subset_span ⟨x0, hx0, rfl⟩)
      have h4 := Formalism.UG.P.afsplit_prV_int (E := E) v _ h3
      rw [prV_hform'] at h4
      exact h4
    | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
    | smul s a _ ha =>
      rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
      exact mul_mem (Formalism.L2.G.RelativeIndexFlags.sigR_mem v σ s.2) ha
  have hc : β.val *ᵥ (G' *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
    Formalism.L2.Geo.Def.PN.latS_of_loc Λ hlat.span_eq_top _ hloc
  have h5 := (hfr _).1 hc i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_single_one] at h5
  exact h5

end General

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_entry {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (Formalism.UG.cT τ B * J * B) i j = Formalism.UG.hform τ J (B *ᵥ Pi.single i 1) (B *ᵥ Pi.single j 1) := by
  rw [GlobalTheory.DualCompletion.hform_col, map_one, one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

end GlobalTheory.GramFrame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.SemiCharValue

theorem exists_abstract_value {G R : Type} [AddCommGroup G] [AddCommGroup R] (ψ : AddChar R ℂ) (hψ : ∀ r, ‖ψ r‖ ≤ 1)
    (B : G → G → R) (hl : ∀ x y z, B (x + y) z = B x z + B y z) (hr : ∀ x y z, B x (y + z) = B x y + B x z)
    (ha : ∀ x, B x x = 0) (L : AddSubgroup G) (K : G → Prop) (K0 : K 0) (Ksub : ∀ x y, K x → K y → K (x - y))
    (hKL : ∀ l ∈ L, K l → l = 0) (hB : ∀ x, K x → ∀ l ∈ L, B x l = 0)
    (h2 : ∀ a ∈ L, ∀ u ∈ L, ψ (B a u + B a u) = 1)
    (p q : G → G) (padd : ∀ x y, p (x + y) = p x + p y) (pq : ∀ x, p x + q x = x)
    (adj : ∀ x y, B (p x) y = B x (q y)) (pL : ∀ l ∈ L, p l ∈ L) :
    ∃ χ : G → ℂ, (∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧
      (∀ x y, K y → χ (x + y) = χ x) ∧ (∀ u ∈ L, ∀ x, ψ (B x (2 • u)) * χ (x + 2 • u) = χ x) ∧
      (∀ u ∈ L, B (p u) u = 0 → ∀ x, ψ (B x u) * χ (x + u) = χ x) ∧
      ∀ l ∈ L, χ l = ψ (B (p l) l) := by
  classical
  have Kadd : ∀ x y, K x → K y → K (x + y) := fun x y hx hy => by
    have := Ksub x (0 - y) hx (Ksub 0 y K0 hy)
    rwa [zero_sub, sub_neg_eq_add] at this
  have skew : ∀ x y, B x y + B y x = 0 := fun x y => by
    have := ha (x + y)
    rwa [hl, hr, hr, ha, ha, zero_add, add_zero] at this
  let χ : G → ℂ := fun x => if h : ∃ l ∈ L, K (x - l) then ψ (B (p h.choose) h.choose) else 0
  have hn : ∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0 := fun x h => dif_neg h
  have hy : ∀ x, ∀ l ∈ L, K (x - l) → χ x = ψ (B (p l) l) := fun x l hl' hk => by
    have h : ∃ l ∈ L, K (x - l) := ⟨l, hl', hk⟩
    have e : h.choose = l := by
      have h1 := Ksub _ _ hk h.choose_spec.2
      rw [sub_sub_sub_cancel_left] at h1
      exact sub_eq_zero.1 (hKL _ (L.sub_mem h.choose_spec.1 hl') h1)
    show dite _ _ _ = _
    rw [dite_eq_left h, e]
  have gen : ∀ u ∈ L, (∀ l ∈ L, ψ (B l u) * ψ (B (p (l + u)) (l + u)) = ψ (B (p l) l)) →
      ∀ x, ψ (B x u) * χ (x + u) = χ x := fun u hu H x => by
    by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      have e : B x u = B l u := by
        have := hl (x - l) l u
        rwa [sub_add_cancel, hB _ hk u hu, zero_add] at this
      rw [hy x l hl' hk, hy (x + u) (l + u) (L.add_mem hl' hu) (by rwa [add_sub_add_right_eq_sub]), e, H l hl']
    · rw [hn x h, hn (x + u), mul_zero]
      rintro ⟨l, hl', hk⟩
      exact h ⟨l - u, L.sub_mem hl' hu, by rwa [← sub_add, sub_add_eq_add_sub]⟩
  refine ⟨χ, hn, fun x => ?_, ?_, fun x y hk => ?_, fun u hu => ?_, fun u hu h0 => ?_,
    fun l hl' => hy l l hl' (by rwa [sub_self])⟩
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk]; exact hψ _
    · rw [hn x h]; simp
  · rw [hy 0 0 L.zero_mem (by rwa [sub_zero])]
    have : B (p 0) 0 = 0 := by
      have := hr (p 0) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [this, AddChar.map_zero_eq_one]
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk, hy (x + y) l hl' (by rw [← sub_add_eq_add_sub]; exact Kadd _ _ hk ‹_›)]
    · rw [hn x h, hn (x + y)]
      rintro ⟨l, hl', hk'⟩
      refine h ⟨l, hl', ?_⟩
      have := Ksub _ _ hk' hk
      rwa [show x + y - l - y = x - l by abel] at this
  · refine gen _ (L.nsmul_mem hu 2) fun l hl' => ?_
    have e : B (p (l + 2 • u)) (l + 2 • u) = B (p l) l + (B (p l) u + B (p l) u) +
        (B (p u) (l + 2 • u) + B (p u) (l + 2 • u)) := by
      conv_lhs => rw [padd, hl, hr, two_nsmul, hr, padd, hl]
      rw [two_nsmul]
    rw [e, two_nsmul, hr, h2 l hl' u hu, one_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      h2 _ (pL l hl') u hu, h2 _ (pL u hu) _ (L.add_mem hl' (L.add_mem hu hu)), mul_one, mul_one]
  · refine gen _ hu fun l hl' => ?_
    have e : B l u + B (p (l + u)) (l + u) = B (p l) l + (B (p l) u + B (p l) u) := by
      have e1 : B l u = B (p l) u + B (q l) u := by rw [← hl, pq]
      have e2 := skew u (q l)
      rw [padd, hl, hr, hr, h0, adj u l, e1]
      rw [← sub_eq_zero]
      refine Eq.trans ?_ e2
      abel
    rw [← AddChar.map_add_eq_mul, e, AddChar.map_add_eq_mul, h2 _ (pL l hl') u hu, mul_one]

theorem exists_semichar_value : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ b : 𝓞 D.host.E, (b : D.host.E) + star (b : D.host.E) = 1 → ∃ χ : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) χ ∧ ∀ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), χ l = ψ (symplOH S T (l.map fun z => incA D (b : D.host.E) * z) l) := by
  intro D ψ S T ΛS ΛT hψ hS hT b hb
  have hinf := GlobalTheory.SemiChar.latO_inf S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True
  obtain ⟨f1, f2, f3, f4, -, -, f7, f8, f9⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  have g := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨χ, -, -, -, -, c5, c6, c7⟩ := exists_abstract_value ψ (fun r => (hψ.1.2.1 r).le) (symplOH S T) f1 f2 f3
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (fun x => x.map (finPart D) = 0) (by funext i j; exact (finPart D).map_zero)
    (fun x y hx hy => by
      funext i j
      have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
      have h2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
      show finPart D (x i j - y i j) = 0
      rw [RingHom.map_sub, h1, h2, sub_zero])
    (fun l hl hk => by
      funext i j
      exact GlobalTheory.FockCompare.RealChart.adele_tensor_ext (l i j) (congrFun (congrFun (hinf l hl) i) j)
        (congrFun (congrFun hk i) j))
    (fun x hx l hl => f9 x l hx (hinf l hl))
    (fun a ha u hu => by rw [f4]; exact (g a (hinf a ha)).1 ha u hu)
    (fun x => x.map fun z => incA D (b : D.host.E) * z) (fun x => x.map fun z => cA D (incA D (b : D.host.E)) * z)
    (GlobalTheory.SemiChar.map_mul_add _)
    (fun x => by
      funext i j
      show incA D (b : D.host.E) * x i j + incA D (star (b : D.host.E)) * x i j = x i j
      rw [← add_mul, ← RingHom.map_add (f := _), hb, RingHom.map_one, one_mul])
    (f7 _) (GlobalTheory.SemiChar.latO_mul_int S T _ _ _ b)
  refine ⟨χ, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, c7⟩
  · funext x; exact c5 u hu x
  · funext x; exact c6 u hu (f8 e _ u he.2.1 hh) x

end GlobalTheory.SemiCharValue
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.typePrime_sizes_le_budget_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → DGamSize Fm → ∀ Cd : ℝ, ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err Cd C := by
  first | exact @GlobalTheory.TypeSize.typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo | exact GlobalTheory.TypeSize.typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo | (intros; apply GlobalTheory.TypeSize.typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  first | exact @GlobalTheory.PlaneNorm.exists_rational_middle_vector | exact GlobalTheory.PlaneNorm.exists_rational_middle_vector | (intros; apply GlobalTheory.PlaneNorm.exists_rational_middle_vector <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.relDetIdeal_selfDual_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.SelfDualDetNorm.detId_normOne | exact GlobalTheory.SelfDualDetNorm.detId_normOne | (intros; apply GlobalTheory.SelfDualDetNorm.detId_normOne <;> assumption)
end
