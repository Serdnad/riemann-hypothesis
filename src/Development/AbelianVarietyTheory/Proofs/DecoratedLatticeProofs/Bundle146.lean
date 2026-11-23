module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittFlagUnipotentFixerFundamentalDomainLayers
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FinPl.AlmostAll

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {c : 𝓞 E} (hc : c ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ c' : 𝓞 E, (n : 𝓞 E) = c * c' := by
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc
  · obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    exact ⟨c', by rw [← hc', mul_comm]⟩

theorem exists_nat_bounds {E : Type} [Field E] [NumberField E]
    {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    ∃ N M : ℕ, N ≠ 0 ∧ M ≠ 0 ∧ (∀ a ∈ I, ∃ b : 𝓞 E, (N : E) * a = algebraMap (𝓞 E) E b) ∧ (M : E) ∈ I := by
  obtain ⟨d, hd, hint⟩ := I.isFractional
  obtain ⟨N, hN, d', hdd'⟩ := exists_nat_eq_mul (nonZeroDivisors.ne_zero hd)
  have hsub : (I : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 hI
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hsub
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hrs
  have hs0 : algebraMap (𝓞 E) E (s : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero s.2)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hrs
    exact hrs.elim hx0 hs0
  have hrI : algebraMap (𝓞 E) E r ∈ (I : Submodule (𝓞 E) E) := by
    rw [← hrs, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hxI
  obtain ⟨M, hM, r', hrr'⟩ := exists_nat_eq_mul hr0
  refine ⟨N, M, hN, hM, fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hint a (FractionalIdeal.mem_coe.2 ha)
    refine ⟨d' * b, ?_⟩
    rw [map_mul, hb, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_comm d' d, ← hdd', map_natCast]
  · have : (M : E) = r' • algebraMap (𝓞 E) E r := by
      rw [Algebra.smul_def, ← map_mul, mul_comm r' r, ← hrr', map_natCast]
    rw [← FractionalIdeal.mem_coe, this]
    exact Submodule.smul_mem _ _ hrI

theorem eventually_notMem {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : N ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (N : 𝓞 F) ∉ v.asIdeal := by
  have h0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, not_not] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem inv_mem_integers {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (N : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (N : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  have h2 : Valued.v (algebraMap F (Fv F v) (N : F)) = 1 := by
    rw [← h1]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (N : F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, h2, inv_one]

theorem smul_inv_mem {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) {α : Af F} (hα : α ∈ intAf F) (h0 : ∀ w, ¬ w = v → evalV F w α = 0) :
    (N : F)⁻¹ • α ∈ intAf F ∧ ∀ w, ¬ w = v → evalV F w ((N : F)⁻¹ • α) = 0 := by
  have key : ∀ w, evalV F w ((N : F)⁻¹ • α) = algebraMap F (Fv F w) (N : F)⁻¹ * evalV F w α := by
    intro w
    rw [map_smul, Algebra.smul_def]
  have hα' : ∀ w, evalV F w α ∈ w.adicCompletionIntegers F := hα
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [key]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (inv_mem_integers hv) (hα' w)
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [key, h0 w hw, mul_zero]

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  show ((0 : Ainf F), c • α) = c • ((0 : Ainf F), α)
  rw [Prod.smul_mk, smul_zero]

theorem tmul_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {N : ℕ} (hN : N ≠ 0) (α : Af F) (z : E) :
    pairA F 0 α ⊗ₜ[F] z = pairA F 0 ((N : F)⁻¹ • α) ⊗ₜ[F] ((N : E) * z) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hz : (N : E) * z = (N : F) • z := by
    rw [Algebra.smul_def, map_natCast]
  rw [hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← pairA_smul, smul_smul,
    mul_inv_cancel₀ hN', one_smul]

theorem latA_eq_latV (D : D7) :
    ∀ᶠ v : Pl D in cofinite, ∀ (S : HSp D) (L : Lat S), latA S L (· = v) = latV S L (· = v) := by
  obtain ⟨N, M, hN, hM, hNI, hMI⟩ := exists_nat_bounds (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  filter_upwards [eventually_notMem (F := D.host.F) hN, eventually_notMem (F := D.host.F) hM]
    with v hvN hvM
  intro S L
  apply le_antisymm
  · rw [latA, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvN hα h0
    rw [latV, latMul]
    refine AddSubgroup.subset_closure ⟨(N : D.host.F)⁻¹ • α, hα', h0', 1, rfl, b • x, L.smul_mem b hx, ?_⟩
    funext i
    have e : (N : D.host.E) * (a * x i) = 1 * (b • x) i := by
      rw [one_mul, Pi.smul_apply, Algebra.smul_def, ← hb, mul_assoc]
    rw [tmul_eq hN α (a * x i), e]
  · rw [latV, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvM hα h0
    rw [latA, latMul]
    refine AddSubgroup.subset_closure ⟨(M : D.host.F)⁻¹ • α, hα', h0', (M : D.host.E), hMI, x, hx, ?_⟩
    funext i
    rw [one_mul, tmul_eq hM α (x i)]

end GlobalTheory.FinPl.AlmostAll
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AeUnit

theorem idem_mul_finPart (D : D7) (v : Pl D) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  rw [map_mul, Algebra.TensorProduct.map_tmul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, map_one, ← Algebra.TensorProduct.one_def, one_mul]
  · have h0 : GlobalTheory.FinPl.compAt D w a = 0 := (Submodule.mem_iInf _).1 ha.2 ⟨w, hw⟩
    have h1 : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (finPart D a) = 0 := h0
    rw [h1, mul_zero]

theorem inv_smul_singleV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℤ)
    (h : (N : 𝓞 F) ∉ v.asIdeal) : (N : F)⁻¹ • singleV F v 1 ∈ intAf F := by
  intro w
  rw [map_smul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, ← Algebra.algebraMap_eq_smul_one,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : w.valuation F (algebraMap (𝓞 F) F N) = 1 := (w.valuation_eq_one_iff_notMem (K := F)).2 h
    rw [map_intCast] at h1
    have h2 : Valued.v (algebraMap F (Fv F w) (N : F)⁻¹) = w.valuation F (N : F)⁻¹ :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [h2, map_inv₀, h1, inv_one]
  · rw [GlobalTheory.LatVac.evalV_singleV_ne F v w hw, smul_zero]
    exact zero_mem _

theorem tmul_eq_inv_smul_tmul {F M P : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup P] [Module F P]
    (N : ℤ) (hN : (N : F) ≠ 0) (x : M) (c : P) : x ⊗ₜ[F] c = ((N : F)⁻¹ • x) ⊗ₜ[F] (N • c) := by
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F N c, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem eventually_incA_mul_mem_intAt : ∀ (D : D7) (c : D.host.E), ∀ᶠ v : Pl D in cofinite,
    ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro D c
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨N, hN, hint⟩ := halg.exists_integral_multiple
  have hN' : (N : 𝓞 D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hfin := Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.F)})
    (fun h => hN' (Ideal.span_singleton_eq_bot.1 h))
  filter_upwards [hfin.compl_mem_cofinite] with v hv a ha
  have hv' : (N : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hv (Ideal.dvd_span_singleton.2 h)
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨N • c, hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

end GlobalTheory.FinPl.AeUnit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffSympl

theorem placeIdem_smul_latO {D : D7} {S T : HSp D} {MS : Set (Fin S.rank → D.host.E)}
    {MT : Set (Fin T.rank → D.host.E)} {P : Pl D → Prop} {v : Pl D} (hv : ¬ P v) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) : ∀ u ∈ latO S T MS MT P, algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = 0 := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w 0
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [hP w hv, mul_zero]
      · rw [h0 w hw, zero_mul]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    rw [this, TensorProduct.zero_tmul]
  | zero => exact smul_zero _
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem symplO_off_eq_zero (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E))
    (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) : ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T,
    (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := by
  intro hv u hu x hx
  obtain ⟨ε, hε, he⟩ := p.above
  have hx' : (p.e + cA D p.e) • x = x := Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hx]
  have hc : cA D (p.e + cA D p.e) = p.e + cA D p.e := by rw [map_add (f := _), cA_cA, add_comm]
  rw [← hx', ← hc, ← GlobalTheory.PlaceModel.symplO_smul, he, placeIdem_smul_latO hv hε u hu,
    GlobalTheory.PlaceModel.symplO_zero_left]

end GlobalTheory.FinPl.OffSympl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.LatVHat

theorem gen_mem (D : D7) (S : HSp D) (L : Lat S) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (x : Fin S.rank → D.host.E)
    (hx : x ∈ L) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((1 : D.host.E) * x i)))) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) L := by
  have hint : (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    apply Subring.subset_closure
    right
    refine ⟨⟨α, ?_⟩, rfl⟩
    intro v
    exact hα v
  have hgen : (fun i => Formalism.UG.inclE (F := D.host.F) (Af D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have := Submodule.smul_mem _ (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) hgen
  convert this using 1
  ext i
  show _ = ((1 : D.host.E) ⊗ₜ[D.host.F] α) * (x i ⊗ₜ[D.host.F] (1 : Af D.host.F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

theorem latV_mem_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  intro D S L P y hy
  let Φ : (Fin S.rank → AE D) →+ (Fin S.rank → Formalism.IndefR.Lev.EAf D) :=
    AddMonoidHom.compLeft ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)).toAddMonoidHom (Fin S.rank)
  have hle : latV S L P ≤ (Formalism.L2.Herm.hatL (F := D.host.F) L).toAddSubgroup.comap Φ := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact gen_mem D S L α hα x hx
  exact hle hy

end GlobalTheory.LatVHat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.wittFlagUnipotentFixer_fundamentalDomain_layers : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → ∀ (vb : VolM D ρ V₀.rank) (ν : Measure (UX D ρ)), SFinite vb.μ → SFinite ν → IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ))) ((lC.prod (vb.μ.prod ν)).map e) := by
  intro D V V₀ ρ d e he lC 𝓒 _ _ hC vb ν _ _
  have : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  have : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).1
  have : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.2.2.1
  have : Countable (ratMx D ρ V₀.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := ⟨continuous_add.measurable⟩
  have rat_coords {b : Mx D ρ V₀.rank} {c : skewA D ρ}
      (h : d.nB b * d.nC c ∈ GQ V) : b ∈ ratMx D ρ V₀.rank ∧ c.1 ∈ ratMx D ρ ρ := by
    have hm := (mem_GQ_iff V _).1 h
    have hb : b ∈ ratMx D ρ V₀.rank := by
      have e1 : d.pX ⬝ (mt V (d.nB b * d.nC c) ⬝ d.j0) = b := by
        rw [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc, d.pX_jX,
          Matrix.one_mul, zero_add]
      rw [← e1]
      exact ratMx_mul (rat_mem _) (ratMx_mul hm (rat_mem _))
    refine ⟨hb, ?_⟩
    have hc : d.nC c ∈ GQ V := by
      have := mul_mem (inv_mem (d.nB_mem_GQ hb)) h
      rwa [inv_mul_cancel_left] at this
    have hm2 := (mem_GQ_iff V _).1 hc
    have e2 : d.pX ⬝ (mt V (d.nC c) ⬝ d.jY) = c.1 := by
      rw [d.nC_jY, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, zero_add]
    rw [← e2]
    exact ratMx_mul (rat_mem _) (ratMx_mul hm2 (rat_mem _))
  have act_coords (c' c : skewA D ρ) (b' b : Mx D ρ V₀.rank) (u : GL (Fin ρ) (AE D)) :
      d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u)) =
        d.nC (c' + c + cComm V₀ b' b) * (d.nB (b' + b) * d.levi u) := by
    have h1 : d.nB b' * d.nC c = d.nC c * d.nB b' := (d.nC_mul_nB b' c).symm
    have h2 : d.nB (b' + b) * d.nC (cComm V₀ b' b) = d.nC (cComm V₀ b' b) * d.nB (b' + b) :=
      (d.nC_mul_nB _ _).symm
    calc d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u))
        = d.nC c' * (d.nB b' * d.nC c) * d.nB b * d.levi u := by simp only [mul_assoc]
      _ = d.nC c' * d.nC c * (d.nB b' * d.nB b) * d.levi u := by rw [h1]; simp only [mul_assoc]
      _ = d.nC c' * d.nC c * d.nC (cComm V₀ b' b) * d.nB (b' + b) * d.levi u := by
          rw [d.nB_mul_nB, h2]; simp only [mul_assoc]
      _ = d.nC (c' + c + cComm V₀ b' b) * (d.nB (b' + b) * d.levi u) := by
          rw [d.nC_add, d.nC_add]; simp only [mul_assoc]
  have mem_radX_iff (n : GA D V) : n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c := by
    constructor
    · intro hn
      obtain ⟨hf, hx⟩ := Subgroup.mem_inf.1 hn
      obtain ⟨⟨c, b, u⟩, hu⟩ := e.surjective ⟨n, hf⟩
      have hn' : n = d.nC c * (d.nB b * d.levi u.1) :=
        (congrArg Subtype.val hu).symm.trans (he (c, b, u))
      change mt V n ⬝ d.jX = d.jX at hx
      have hX : mt V n ⬝ d.jX = d.jX ⬝ u.1.1 := by
        rw [hn', mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX,
          ← Matrix.mul_assoc (mt V (d.nB b)), d.nB_jX,
          ← Matrix.mul_assoc (mt V (d.nC c)), d.nC_jX]
      have hmat : d.pX ⬝ (d.jX ⬝ u.1.1) = d.pX ⬝ d.jX :=
        congrArg (fun X => d.pX ⬝ X) (hX.symm.trans hx)
      rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at hmat
      have hu' : u.1 = 1 := Units.ext hmat
      exact ⟨b, c, by rw [hn', hu', map_one, mul_one, d.nC_mul_nB]⟩
    · rintro ⟨b, c, rfl⟩
      refine Subgroup.mem_inf.2 ⟨mul_mem (d.nB_mem_NFlag b) (d.nC_mem_NFlag c), ?_⟩
      change mt V (d.nB b * d.nC c) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX]
  have hκ : ∀ b' : Mx D ρ V₀.rank, Measurable (cComm V₀ b') := by
    intro b'
    have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
    have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
    have h1 : Continuous fun b : Mx D ρ V₀.rank => half D • (b ⬝ plus V₀ b' - b' ⬝ plus V₀ b) :=
      ((continuous_id.matrix_mul continuous_const).sub (continuous_const.matrix_mul hp)).const_smul (half D)
    exact (h1.subtype_mk _).measurable
  have key : ∀ (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) (p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ)),
      d.nC c' * d.nB b' * (e p : GA D V) = (e (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2) : GA D V) := by
    intro c' b' p
    rw [he p, he (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2)]
    exact act_coords c' p.1 b' p.2.1 p.2.2.1
  have hsm : ∀ (g : ↥((GQ V ⊓ radX d).subgroupOf (flagN d))) (x : flagN d),
      ((g • x : flagN d) : GA D V) = ((g : flagN d) : GA D V) * (x : GA D V) := fun _ _ => rfl
  refine GlobalTheory.Layers.isFundamentalDomain_layers (mA := lC) (mB := vb.μ) (ν := ν) ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) (ratMx D ρ V₀.rank) (cComm V₀) hκ e
    ?_ ?_ ?_ hC vb.covol.2.1
  · intro g g' x h
    rw [Subgroup.smul_def, Subgroup.smul_def] at h
    exact Subtype.ext (mul_right_cancel h)
  · rintro ⟨⟨γ, hγN⟩, hγ⟩
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨b, c, hbc⟩ := (mem_radX_iff γ).1 (Subgroup.mem_inf.1 hγ).2
    subst hbc
    have hr := rat_coords (Subgroup.mem_inf.1 hγ).1
    refine ⟨⟨c, AddSubgroup.mem_addSubgroupOf.2 hr.2⟩, ⟨b, hr.1⟩, fun p => Subtype.ext ?_⟩
    rw [Subgroup.smul_def]
    have h := key c b p
    rw [d.nC_mul_nB] at h
    exact h
  · rintro ⟨c', hc'⟩ ⟨b', hb'⟩
    have hrad : d.nC c' * d.nB b' ∈ radX d := (mem_radX_iff _).2 ⟨b', c', d.nC_mul_nB b' c'⟩
    have hQ : d.nC c' * d.nB b' ∈ GQ V :=
      mul_mem (d.nC_mem_GQ (AddSubgroup.mem_addSubgroupOf.1 hc')) (d.nB_mem_GQ hb')
    have hN : d.nC c' * d.nB b' ∈ flagN d := (Subgroup.mem_inf.1 hrad).1
    let g : ((GQ V ⊓ radX d).subgroupOf (flagN d)) :=
      ⟨⟨d.nC c' * d.nB b', hN⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hQ, hrad⟩)⟩
    refine ⟨g, fun p => Subtype.ext ((hsm g (e p)).trans (key c' b' p))⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobi_invariant_function_integrable : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K → (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  first | exact @GlobalTheory.Unf.jac_absConv | exact GlobalTheory.Unf.jac_absConv | (intros; apply GlobalTheory.Unf.jac_absConv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.isMulRightInvariant_map_wittFlagCoordinates_haar : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → ((lC.prod (vb.μ.prod vU.ν)).map e).IsMulRightInvariant := by
  first | exact @GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord | exact GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord | (intros; apply GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ (v : VolM D T.rank S.rank) p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → thPair v.μ v.𝓕 (om p f) (om p f') = thPair v.μ v.𝓕 f f' := by
  first | exact @GlobalTheory.WeilPairing.thPair_om_eq | exact GlobalTheory.WeilPairing.thPair_om_eq | (intros; apply GlobalTheory.WeilPairing.thPair_om_eq <;> assumption)
end
