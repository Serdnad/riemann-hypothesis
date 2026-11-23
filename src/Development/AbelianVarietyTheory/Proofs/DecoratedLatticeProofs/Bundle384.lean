module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle356
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.functional_values_integral_vectors_of_integer_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  first | exact @GlobalTheory.FinPl.SplitPt.hasVal_of_int_vectors | exact GlobalTheory.FinPl.SplitPt.hasVal_of_int_vectors | (intros; apply GlobalTheory.FinPl.SplitPt.hasVal_of_int_vectors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  first | exact @GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | exact GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | (intros; apply GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  first | exact @GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt | exact GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt | (intros; apply GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.exists_splitPlace_component_ringHom_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.SplitPhi.exists_ringHom_int | exact GlobalTheory.FinPl.SplitPhi.exists_ringHom_int | (intros; apply GlobalTheory.FinPl.SplitPhi.exists_ringHom_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitUnif

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_eq_mul (v : HeightOneSpectrum (𝓞 F)) (T b : 𝓞 F) (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2)
    (hb : b ∈ v.asIdeal) : ∃ c ∈ v.adicCompletionIntegers F,
      algebraMap F (v.adicCompletion F) (b : F) = algebraMap F (v.adicCompletion F) (T : F) * c := by
  have hT0 : T ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hle : v.intValuation b ≤ v.intValuation T := by
    have h3 := (v.intValuation_le_pow_iff_mem b 1).2 (by simpa using hb)
    refine h3.trans ?_
    by_contra h
    rw [not_le] at h
    apply h2
    rw [← v.intValuation_le_pow_iff_mem]
    have h0 : v.intValuation T ≠ 0 := v.intValuation_ne_zero _ hT0
    rw [← WithZero.exp_log h0] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega
  have hTF : (T : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hT0
  refine ⟨algebraMap F (v.adicCompletion F) ((b : F) / (T : F)), ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h := v.valuedAdicCompletion_eq_valuation' ((b : F) / (T : F))
    change Valued.v (((b : F) / (T : F) : F) : v.adicCompletion F) ≤ 1
    rw [h, map_div₀]
    have e1 : v.valuation F (b : F) = v.intValuation b := v.valuation_of_algebraMap b
    have e2 : v.valuation F (T : F) = v.intValuation T := v.valuation_of_algebraMap T
    rw [e1, e2]
    exact div_le_one_of_le₀ hle zero_le
  · rw [← map_mul, mul_div_cancel₀ _ hTF]

theorem incl_eq_mul [StarRing E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hv : ∀ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b ∈ P → b ∈ v.asIdeal) (T : 𝓞 F) (t t' : 𝓞 E)
    (ht' : (t' : E) = star (t : E)) (htt : t * t' = algebraMap (𝓞 F) (𝓞 E) T) (hco : IsCoprime t t') (ht : t ∈ P)
    (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2) (a : 𝓞 E) (ha : a ∈ P) :
    ∃ c ∈ intV E v, Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E) * c := by
  have hO : ∀ r : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  have hF : ∀ x : F, Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E x) =
      (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) x := fun x => by
    change (algebraMap F E x) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  let a' : 𝓞 E := ⟨star (a : E), (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (RingHom.id ℤ) (starRingEnd E)
    (RingHom.ext_int _ _)⟩
  have ha' : (a' : E) = star (a : E) := rfl
  obtain ⟨b₀, hb₀⟩ := (hc.fixed ((t' * a + t * a' : 𝓞 E) : E)).1 (by
    change star ((t' : E) * (a : E) + (t : E) * star (a : E)) = (t' : E) * (a : E) + (t : E) * star (a : E)
    rw [ht', star_add, star_mul', star_mul', star_star, star_star, add_comm])
  have hint : IsIntegral ℤ b₀ := by
    rw [← isIntegral_algebraMap_iff (B := E), hb₀]
    exact RingOfIntegers.isIntegral_coe _
  let b : 𝓞 F := ⟨b₀, hint⟩
  have hb : algebraMap (𝓞 F) (𝓞 E) b = t' * a + t * a' := RingOfIntegers.ext hb₀
  obtain ⟨c, hc1, hc2⟩ := exists_eq_mul v T b h1 h2
    (hv b (by rw [hb]; exact add_mem (P.mul_mem_left _ ha) (P.mul_mem_right _ ht)))
  have hcV : (1 : E) ⊗ₜ[F] c ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨c, hc1⟩, rfl⟩)
  obtain ⟨α, β, hαβ⟩ := hco
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι
  have e1 : ι t' * ι a + ι t * ι a' = ι t * ι t' * ((1 : E) ⊗ₜ[F] c) := by
    have l : ι t' * ι a + ι t * ι a' = ι (algebraMap F E (b : F)) := by
      rw [← map_mul ι, ← map_mul ι, ← map_add ι]
      exact congrArg ι hb₀.symm
    have r : ι t * ι t' = ι (algebraMap F E (T : F)) := by
      rw [← map_mul ι]
      exact congrArg (fun z : 𝓞 E => ι (z : E)) htt
    rw [l, r, hF, hF, hc2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have e2 : ι α * ι t + ι β * ι t' = 1 := by
    rw [← map_mul ι, ← map_mul ι, ← map_add ι, ← map_one ι]
    exact congrArg (fun z : 𝓞 E => ι (z : E)) hαβ
  refine ⟨ι α * ι a + ι β * (ι t' * ((1 : E) ⊗ₜ[F] c) - ι a'),
    add_mem (mul_mem (hO _) (hO _)) (mul_mem (hO _) (sub_mem (mul_mem (hO _) hcV) (hO _))), ?_⟩
  linear_combination (-(ι a)) * e2 + ι β * e1

end General




theorem eq_mul_of_val_lt_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (T : ℕ) (t t' : 𝓞 D.host.E), (t' : D.host.E) = star (t : D.host.E) → t * t' = (T : 𝓞 D.host.E) → IsCoprime t t' → t ∈ P.asIdeal → (T : 𝓞 D.host.F) ∈ p.v.asIdeal → (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2 → ∀ y : AE D, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) ∈ Formalism.BasicNotions.intV D.host.E p.v → valuation k (p.pr y) < 1 → ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  intro D k _ _ _ _ p P hP T t t' ht' htt hco ht h1 h2 y hy hval
  obtain ⟨π₀, hπ₀, -, -, hres⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP
  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h3 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h3
    exact h3.symm
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, Formalism.UG.P.afsplit_IE_int p.v _ hy⟩
  have hs : s ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := by
    rw [← Formalism.L2.DIV.resS_eq_zero_iff, hres]
    change valuation k (π₀ (Formalism.UG.P.afsplitIE p.v _)) < 1
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul, hπ₀]
    exact hval
  have hv : ∀ b : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ P.asIdeal → b ∈ p.v.asIdeal := fun b hb => by
    rw [GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under p hP]
    exact hb
  have key : ∀ z ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal, ∃ c ∈ intV D.host.E p.v,
      Formalism.UG.prV (E := D.host.E) p.v (z : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact incl_eq_mul D.sp.cm p.v P.asIdeal hv (T : 𝓞 D.host.F) t t' ht' (by rw [htt, map_natCast]) hco ht h1 h2 a ha
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc, ea⟩ := ha
      obtain ⟨d, hd, eb⟩ := hb
      exact ⟨c + d, add_mem hc hd, by rw [Subring.coe_add, map_add (f := _), ea, eb, mul_add]⟩
    | smul r a _ ha =>
      obtain ⟨c, hc, ea⟩ := ha
      exact ⟨Formalism.UG.prV (E := D.host.E) p.v r * c, mul_mem (Formalism.UG.P.afsplit_prV_int p.v _ r.2) hc, by
        rw [smul_eq_mul, Subring.coe_mul, map_mul, ea, mul_left_comm]⟩
  obtain ⟨c, hc, e⟩ := key s hs
  refine ⟨c, hc, ?_⟩
  rw [← e]
  exact (Formalism.UG.P.afsplit_prV_IE p.v _).symm

end GlobalTheory.LocMod.SplitUnif
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitCoord

open GlobalTheory.FinPl




theorem coord_int_last : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  intro D k _ _ _ _ p P hP n t ht Lb hLb y hy
  obtain ⟨π₀, hπ₀, -, hint, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP

  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h1 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h1
    exact h1.symm

  let π : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k :=
    { toFun := fun s => π₀ (Formalism.UG.P.afsplitIE p.v s)
      map_one' := heps
      map_mul' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a * b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) * π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_mul (Formalism.UG.P.afsplitIE p.v), map_mul π₀]
      map_zero' := by
        show π₀ (Formalism.UG.P.afsplitIE p.v 0) = 0
        rw [map_zero (Formalism.UG.P.afsplitIE p.v), map_zero π₀]
      map_add' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a + b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) + π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_add (Formalism.UG.P.afsplitIE p.v), map_add π₀] }
  have hπ : ∀ z, π (Formalism.UG.prV (E := D.host.E) p.v z) = π₀ z := fun z => by
    change π₀ (Formalism.UG.P.afsplitIE p.v _) = _
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul]

  have hV : intV D.host.E p.v ≤ (𝒪[k]).comap π := by
    refine Subring.closure_le.2 ?_
    rintro s (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · change π (Formalism.UG.prV (E := D.host.E) p.v ((x : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∈ 𝒪[k]
      rw [hπ]
      exact hint ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
    · change π₀ ((1 : D.host.E) ⊗ₜ[D.host.F] Formalism.UG.P.afsplitI p.v (x : p.v.adicCompletion D.host.F)) ∈ 𝒪[k]
      exact hint ⟨_, Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd p.v _ x.2⟩, rfl⟩)⟩

  have key : ∀ w ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb,
      ∀ r : Fin n, π (w r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (π (w r)) < 1) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      intro r
      obtain ⟨ρ, hρ, hlast⟩ := (hLb x).1 hxL r
      have h0 : π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) = p.pr (incA D (ρ : D.host.E)) := by
        rw [hρ]
        change π (Formalism.UG.prV (E := D.host.E) p.v ((ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) = _
        rw [hπ, ← hπ₀]
        rfl
      refine ⟨?_, fun hr => ?_⟩
      · change π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) ∈ 𝒪[k]
        have hq : toEAf D (incA D (ρ : D.host.E)) =
            (ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
          first | rfl | simp [toEAf, finPart, incA]
        have hm : toEAf D (incA D (ρ : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hq]; exact Subring.subset_closure (Or.inl ⟨⟨(ρ : D.host.E), ρ, rfl⟩, rfl⟩)
        rw [h0, ← hπ₀]
        exact hint ⟨_, hm⟩
      · change valuation k (π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r))) < 1
        rw [h0, ← GlobalTheory.LocMod.LevBack.pr_lt p hP]
        obtain ⟨c, hc⟩ := hlast hr
        rw [hc]; exact Ideal.mul_mem_right _ _ ht
    | zero =>
      intro r
      simp
    | add a b _ _ ha hb =>
      intro r
      refine ⟨?_, fun hr => ?_⟩
      · rw [Pi.add_apply, map_add (f := _)]; exact add_mem (ha r).1 (hb r).1
      · rw [Pi.add_apply, map_add (f := _)]; exact Valuation.map_add_lt _ ((ha r).2 hr) ((hb r).2 hr)
    | smul s a _ ha =>
      intro r
      have hs : π s ∈ 𝒪[k] := hV s.2
      have e1 : π ((s • a) r) = π s * π (a r) := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨?_, fun hr => ?_⟩
      · rw [e1]; exact mul_mem hs (ha r).1
      · rw [e1, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 hs)) ((ha r).2 hr)
  intro r
  have h := key _ hy r
  rw [hπ, hπ₀] at h
  exact h

end GlobalTheory.LocMod.SplitCoord
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem GlobalTheory.IntPlaces.mem_of_idem_sum {R : Type} [CommRing R] {n : ℕ} (S : Set R) (hS0 : (0 : R) ∈ S)
    (E : Fin n → R) (hEE : ∀ i, E i * E i = E i) (hE : ∀ i j, i ≠ j → E i * E j = 0) (G : Fin n → R → Prop)
    (hint : ∀ i z, z ∈ S ↔ (1 - E i) * z ∈ S ∧ G i z) (hG : ∀ i j z, i ≠ j → G i z → G i ((1 - E j) * z)) :
    ∀ z, (∑ i, E i) * z = z → (∀ i, G i z) → z ∈ S := by
  have key : ∀ s : Finset (Fin n), ∀ z, (∑ i ∈ s, E i) * z = z → (∀ i ∈ s, G i z) → z ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      rw [Finset.sum_empty, zero_mul] at hz
      rw [← hz]
      exact hS0
    | insert a s ha ih =>
      intro z hz hzi
      rw [Finset.sum_insert ha] at hz
      refine (hint a z).2 ⟨?_, hzi a (Finset.mem_insert_self a s)⟩
      have hET : E a * ∑ i ∈ s, E i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hE a i fun h => ha (h ▸ hi)
      have hw : (1 - E a) * z = (∑ i ∈ s, E i) * z := by
        calc (1 - E a) * z = (1 - E a) * ((E a + ∑ i ∈ s, E i) * z) := by rw [hz]
          _ = (∑ i ∈ s, E i) * z := by linear_combination (-z) * hEE a + (-z) * hET
      refine ih _ ?_ fun i hi => ?_
      · linear_combination (-1 : R) * hw + (-z) * hET
      · exact hG i a z (fun h => ha (h ▸ hi)) (hzi i (Finset.mem_insert_of_mem hi))
  exact fun z hz hzi => key Finset.univ z hz fun i _ => hzi i


open GlobalTheory.IdemSupport in
theorem GlobalTheory.IntPlaces.mem_intAf_of_split : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n k _ _ _ _ q P hI hP π' hπ hint z0 hz0 hzi0
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd : ∀ i, IsDelta ((GlobalTheory.StdFrames.toAd D).comp (Formalism.IndefR.Datum.toEAf D)) (P i) (q i).e :=
    fun i => delta_of_isIdemAt hΦ (hI i)
  have horth : ∀ i j, i ≠ j → (q i).e * (q j).e = 0 := by
    intro i j hij
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P i
    · rw [(hd j).2.2 Q (fun h => hij (hP (hQ.symm.trans h))), mul_zero]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hidem : ∀ i, (q i).e * (q i).e = (q i).e := by
    intro i
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul]) fun Q => ?_
    rw [ev_mul]
    by_cases hQ : Q = P i
    · rw [hQ, (hd i).2.1, mul_one]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hpr : ∀ i j, i ≠ j → π' i (Formalism.IndefR.Datum.toEAf D (q j).e) = 0 := by
    intro i j hij
    rw [hπ, ← (q i).pr_sec ((q i).pr (q j).e), (q i).sec_pr, horth i j hij, map_zero]
  refine GlobalTheory.IntPlaces.mem_of_idem_sum (Formalism.L2.Herm.intAf D.host.F D.host.E : Set _) (zero_mem _)
    (fun i => Formalism.IndefR.Datum.toEAf D (q i).e) (fun i => by rw [← RingHom.map_mul, hidem])
    (fun i j hij => by rw [← RingHom.map_mul, horth i j hij, RingHom.map_zero]) (fun i z => π' i z ∈ 𝒪[k i])
    hint (fun i j z hij hz => ?_) z0 (by rw [show (∑ i, Formalism.IndefR.Datum.toEAf D (q i).e) = Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) from
      (map_sum (Formalism.IndefR.Datum.toEAf D).toAddMonoidHom (fun i => (q i).e) Finset.univ).symm]; exact hz0) hzi0
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hpr i j hij, sub_zero, one_mul]
  exact hz
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem besLev_per_congr {D : D7} {ρ : ℕ} {B B' : BesLev D ρ} (h : B = B') (ψ) {φ : GA D B.A → ℂ} {φ' : GA D B'.A → ℂ}
    {g : GA D B.V → ℂ} {g' : GA D B'.V → ℂ} (h1 : HEq φ φ') (h2 : HEq g g') : B.per ψ φ g = B'.per ψ φ' g' := by
  subst h
  rw [eq_of_heq h1, eq_of_heq h2]

end GlobalTheory.MiTop
end
