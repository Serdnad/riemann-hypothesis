module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle022
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle457
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389

@[expose] public section

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KModExistsStep

theorem kModExists_holds : CompanionTheory.D.LK.KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists CompanionTheory.D.DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs CompanionTheory.D.DSIC.hKFinStab
    CompanionTheory.D.DSIC.hStabLink CompanionTheory.D.DSIC.hHWofType CompanionTheory.D.DSIC.hTypeOfHW

end GlobalTheory.CompanionTheory.KModExistsStep
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjType

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

noncomputable def rt (P : HeightOneSpectrum (𝓞 E)) : ℝ := (Real.sqrt ((Ideal.absNorm P.asIdeal : ℕ) : ℝ))⁻¹

theorem rt_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < rt P :=
  inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot))))

theorem rt_sq (P : HeightOneSpectrum (𝓞 E)) : rt P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [rt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem mk_eq (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : FinitePlace.mk P (k : E) = (rt P ^ ordF P k) ^ 2 := by
  obtain ⟨u, hu, hk⟩ := GlobalTheory.EtaConjChar.exists_unit_part P k
  generalize ordF P k = n at hk ⊢
  rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, GlobalTheory.EtaConjLocal.mk_unit P hu,
    GlobalTheory.EtaConjLocal.mk_unif, mul_one, ← rt_sq, sq, sq, mul_zpow]

theorem prod_rt [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) : (∏ i, ‖φ i k‖) * ∏ P ∈ S, rt P ^ ordF P k = 1 := by
  have h := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    finprod_eq_prod_of_mulSupport_subset (s := S)] at h
  · rw [← sq_eq_sq₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun P _ => (zpow_pos (rt_pos P) _).le)) zero_le_one, one_pow, mul_pow, ← Finset.prod_pow,
      ← Finset.prod_pow, ← h]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
    · exact Finset.prod_congr rfl fun P _ => (mk_eq P k).symm
  · intro P hP
    refine hS P fun h0 => hP ?_
    exact (mk_eq P k).trans (by rw [h0]; simp)

theorem prod_val (χ : HChar E) (hu : ∀ P, χ.UnrAt P) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) :
    ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ S, (((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF P k =
      ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) := by
  have h := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at h
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => hS P fun h0 => hP (by simp [h0]))] at h
  have h' := congrArg (Units.val : ℂˣ → ℂ) h
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at h'
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, h', one_mul]
  push_cast
  rfl

theorem unrAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1) : χ.UnrAt P := by
  intro x
  have hc : IsClopen {x : (P.adicCompletion E)ˣ | IsUnitAt P x} := by
    have := (Valued.isClopen_sphere (P.adicCompletion E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := P.adicCompletion E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on (p := fun x => IsUnitAt P x → χ.loc P x = 1) x ?_
    fun k hk => h k ((P.valuedAdicCompletion_eq_valuation' _).symm.trans hk)
  exact isClosed_imp hc.2 (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)

variable {L : Type} [Field L] (ι σ : L →+* ℂ) {χ χ' : HChar E} (hu : ∀ P, χ.UnrAt P) (hu' : ∀ P, χ'.UnrAt P)
  (y : HeightOneSpectrum (𝓞 E) → L) (hy : ∀ P, ι (y P) = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ))
  (hy' : ∀ P, σ (y P) = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ))

include hu hu' hy hy'

theorem inf_eq [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (hi : χ.HasInf φ fun _ => 1)
    (ht : ∀ k : E, ∃ t : L, ι t = ∏ i, φ i k ∧ σ t = ∏ i, φ i k) (k : Eˣ) : χ'.inf k = χ.inf k := by
  obtain ⟨t, ht1, ht2⟩ := ht k
  let S := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
  have hS : ∀ P, ordF P k ≠ 0 → P ∈ S := fun P hP => (Set.Finite.mem_toFinset _).2 hP
  have h1 := prod_val χ hu k S hS
  have h2 := prod_val χ' hu' k S hS
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) (prod_rt φ hφ k S hS)
  have h4 : ((χ.inf k : ℂˣ) : ℂ) * ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = ∏ i, φ i k := by
    rw [hi k, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_one, div_mul_cancel₀ _ (by simp)]
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h2
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h3
  generalize ∏ P ∈ S, y P ^ ordF P k = Y at h1 h2
  generalize ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) = r at h1 h2 h3
  generalize ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = s at h3 h4
  have h5 : Y * t = 1 := ι.injective (by
    rw [map_mul, map_one, ht1, ← h4, ← h3, ← h1]
    ring)
  have h6 : σ Y * (∏ i, φ i k) = 1 := by rw [← ht2, ← map_mul, h5, map_one]
  refine Units.ext ?_
  calc ((χ'.inf k : ℂˣ) : ℂ) = (χ'.inf k : ℂˣ) * (σ Y * (((χ.inf k : ℂˣ) : ℂ) * s)) := by rw [h4, h6, mul_one]
    _ = (χ.inf k : ℂˣ) * (s * (((χ'.inf k : ℂˣ) : ℂ) * σ Y)) := by ring
    _ = _ := by rw [h2, h3, mul_one]

theorem resFin_eq {F : Type} [Field F] [NumberField F] [Algebra F E] (h2 : Module.finrank F E = 2)
    (hF : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal) (hr : χ.ResEta F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ'.resFin v k = χ.resFin v k := by
  have key : ∀ (ψ : HChar E), (∀ P, ψ.UnrAt P) →
      ∏ P ∈ aboveF (L := E) F v, (((ψ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF v k =
        ((ψ.resFin v k : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ ^ ordF v k := by
    intro ψ hψ
    have h1 : ∏ P ∈ aboveF (L := E) F v, rt P = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
      rw [← sq_eq_sq₀ (Finset.prod_nonneg fun P _ => (rt_pos P).le) (by positivity), ← Finset.prod_pow]
      simp only [rt_sq]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, GlobalTheory.ToricDistribution.prod_absNorm hF, h2, Nat.cast_pow, inv_pow]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    · rw [HChar.resFin_apply, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [GlobalTheory.HeckeProduct.locK_unr ψ (hψ P), GlobalTheory.ToricDistribution.ordF_up hF, GlobalTheory.ToricDistribution.mem_aboveF.1 hP,
        Units.val_zpow_eq_zpow_val]
    · rw [Finset.prod_zpow, ← Complex.ofReal_prod, h1]
      simp
  have h1 := key χ hu
  have h3 := key χ' hu'
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h3
  obtain ⟨z, hz⟩ : ∃ z : L, ∀ f : L →+* ℂ, f z = ((χ.resFin v k : ℂˣ) : ℂ) := by
    rw [hr.1, etaFin]
    split_ifs
    · exact ⟨(-1) ^ ordF v k, fun f => by simp⟩
    · exact ⟨1, fun f => by simp⟩
  have h4 : ∏ P ∈ aboveF (L := E) F v, y P ^ ordF v k = z * ((Ideal.absNorm v.asIdeal : ℕ) : L)⁻¹ ^ ordF v k :=
    ι.injective (by rw [h1, map_mul, hz, map_zpow₀, map_inv₀, map_natCast])
  rw [h4, map_mul, hz, map_zpow₀, map_inv₀, map_natCast] at h3
  refine Units.ext (mul_right_cancel₀ (zpow_ne_zero _ (inv_ne_zero ?_)) h3.symm)
  exact Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

end General

theorem isEtaT_of_conj {D : D7} {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {η η' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E}
    (hc : ChrEq η χ) (hc' : ChrEq η' χ') (hχ : IsEtaT D.host χ) (hη : IsEtaConj σ η η') : IsEtaT D.host χ' := by
  have hu' : ∀ P, χ'.UnrAt P := fun P => unrAt_of_locK χ' P (GlobalTheory.EtaConjChar.locK_eq_one hc' hη.2.1 P)
  have hy : ∀ P, ∃ y : D.what₂.LL, D.what₂.embLL y = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ) ∧
      σ y = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ) := by
    intro P
    obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
    obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
    rw [hc.2 P e he _ (locU he.1 (unif P)) rfl] at hy1
    rw [hc'.2 P e he _ (locU he.1 (unif P)) rfl] at hy2
    refine ⟨y, ?_, ?_⟩
    · simpa only [HChar.val, rt, Ideal.absNorm_eq_natCard] using hy1
    · simpa only [HChar.val, rt, Ideal.absNorm_eq_natCard] using hy2
  choose y hy hy' using hy
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  haveI := hcm.cplx
  obtain ⟨hb, hl⟩ := (labels_overK σ).1 hσ
  have hinf : ∀ k, (χ' * χ⁻¹).inf k = 1 := fun k => by
    rw [HChar.inf_mul, HChar.inf_inv, mul_inv_eq_one]
    refine inf_eq D.what₂.embLL σ hχ.unr hu' y hy hy' (embPsi D.host) hcm.bij hχ.inf (fun a => ?_) k
    refine ⟨∏ τ, labLL D τ a, ?_, ?_⟩
    · rw [map_prod, ← D.eTau.prod_comp]
      exact Finset.prod_congr rfl fun τ _ => embLL_embE D _
    · rw [map_prod, ← D.eTau.prod_comp, ← hb.prod_comp]
      exact Finset.prod_congr rfl fun ρ _ => RingHom.congr_fun (hl ρ) a
  obtain ⟨n, hn, ho⟩ := GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one _ _ hinf
  have hp : ∀ x, (χ' * χ⁻¹).1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) ho
  have hξ : IsClsF D.host (χ' * χ⁻¹) := by
    refine ⟨HChar.isUnitary_of_order hn ho, fun P => (hu' P).mul (hχ.unr P).inv, hinf, fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, HChar.resFin_inv, mul_inv_eq_one]
      exact resFin_eq D.what₂.embLL σ hχ.unr hu' y hy hy' hcm.rank
        (GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm) hχ.res v k
    · rw [HChar.resInf_apply]
      exact Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hn.ne' hp w' _
  have := hχ.mul_cls hξ
  rwa [mul_comm χ', mul_inv_cancel_left] at this

end GlobalTheory.EtaConjType
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ProjLift

theorem exists_factor {A B X I : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup X] [Module ℂ X]
    (L₁ : A →ₗ[ℂ] X) (L₂ : B →ₗ[ℂ] X) (j : I → B) (hj : Submodule.span ℂ (Set.range j) = ⊤) (h : ∀ x, ∃ t, L₁ t = L₂ (j x)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y, L₁ (φ y) = L₂ y := by
  have h1 : ∀ y, L₂ y ∈ LinearMap.range L₁ := fun y =>
    (Submodule.span_le (p := (LinearMap.range L₁).comap L₂)).2 (by rintro _ ⟨x, rfl⟩; exact h x) (hj.ge Submodule.mem_top)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property L₁.rangeRestrict (L₂.codRestrict _ h1) L₁.surjective_rangeRestrict
  exact ⟨φ, fun y => congrArg Subtype.val (LinearMap.congr_fun hφ y)⟩

section Low

open Matrix Formalism.MainNotions.S GlobalTheory.DefLift

variable {D : D7}


open Classical in
theorem eq_on_low {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ)
    {U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) (v : ∀ τ, lowT M τ) : T (fun τ => (v τ : M.sm τ)) = U v := by
  have hT' : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
    intro τ g hg v w hw
    clear h
    induction hT using Submodule.span_induction with
    | mem T hT => exact hT.equiv τ g hg v w hw
    | zero => rfl
    | add x y _ _ hx hy => exact (congrArg₂ (· + ·) hx hy).trans rfl
    | smul a x _ hx => exact (congrArg (a • ·) hx).trans rfl
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT' τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem kEquiv_thetaP {θ : InfFam D} {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {Δ : PolF D W.rank V.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} {B : Submodule ℂ (GA D V → c.W)}
    {thP : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ))}
    (hth : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω h g φ) pt io B thP) (y : B) :
    KEquiv θ M ((thP y).compMultilinearMap (PiTensorProduct.tprod ℂ)) := by
  intro τ k hk v u hu
  have hmul : ∀ h g k φ, thetaKO ω h (g * k) φ = thetaKO ω h g (ω (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  funext g
  simp only [LinearMap.compMultilinearMap_apply, rTr, hth.eq, Lift.thetaPInt, hmul, hio.2.1 τ k hk v u hu]

theorem exists_lift {θ : InfFam D} {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D W)} {χ : GA D W → ℂ} {A B I : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : A →ₗ[ℂ] MMap M) (he : ∀ t, e t ∈ Mult θ M J χ)
    (L : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ)))
    (hL : ∀ y, KEquiv θ M ((L y).compMultilinearMap (PiTensorProduct.tprod ℂ))) (j : I → B)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (v : ∀ τ, lowT M τ) (hv : ∀ τ, v τ ≠ 0)
    (h : ∀ x, ∃ t, e t (fun τ => (v τ : M.sm τ)) = L (j x) (PiTensorProduct.tprod ℂ v)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y (u : ∀ τ, lowT M τ), e (φ y) (fun τ => (u τ : M.sm τ)) = L y (PiTensorProduct.tprod ℂ u) := by
  let L₁ : A →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun t u => e t (fun τ => (u τ : M.sm τ))
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  let L₂ : B →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun y u => L y (PiTensorProduct.tprod ℂ u)
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  obtain ⟨φ, hφ⟩ := exists_factor L₁ L₂ j hj fun x => (h x).imp fun t ht =>
    funext fun u => eq_on_low h1 h2 (he t) (hL (j x)) v hv ht u
  exact ⟨φ, fun y u => congrFun (hφ y) u⟩

end Low

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem holShape_of_overK (R : RealDat D A Ks) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) :
    GlobalTheory.HolDict.HolShape (R.MW i σ) := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
    rw [← hs ρ]
    exact GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  exact fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩

theorem proj_apply (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : (R.HW i σ).H)
    (v : (R.MW i σ).Vec) :
    (R.HW i σ).e ((∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) t) v = R.eWf i σ ((R.HW i σ).e t v) := by

  simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
  MultilinearMap.smul_apply, hg i σ, postOn_apply]
  rfl


end GlobalTheory.GalLift.ProjLift

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLagr

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      ∃ Cy : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) G.W.J) Cy := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw
  have hF := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hT.base v w hvw
  obtain ⟨y, u, hu, hy⟩ := GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert F E σ B hT.base _ _ _ G.W hT.geo.hW hT.geo.even v w hvw hF
  obtain ⟨z, hz⟩ := GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt F E σ B hT.base v w hvw hF u hu
  refine GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor F E σ hT.base.cm v hF (a + a') G.W.J hT.geo.even hT.geo.hW.skew
    (GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace F E σ B _ _ _ G.W hT.geo.hW) ⟨z * y, ?_⟩
  rw [hy, hz, map_mul]
  ring

end GlobalTheory.InertLagr
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.KFinLoc

theorem split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl (F := F), Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ B hB v
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi
  · left
    obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩
  · exact Or.inr hi

end GlobalTheory.KFinLoc
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF


theorem _root_.GlobalTheory.T.theta_function_heisenberg_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  first | exact @GlobalTheory.HeisThetaF.isThetaFunOF_heisOF | exact GlobalTheory.HeisThetaF.isThetaFunOF_heisOF | (intros; apply GlobalTheory.HeisThetaF.isThetaFunOF_heisOF <;> assumption)
end
