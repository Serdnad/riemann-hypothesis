module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactOfComplete
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (C H : ∀ v, Subgroup (Y v)), (∀ v, (H v).relIndex (C v) ≠ 0) → (∀ᶠ v in cofinite, C v ≤ H v) → (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  first | exact @GlobalTheory.RelIdxRestr.relIndex_iInf_comap | exact GlobalTheory.RelIdxRestr.relIndex_iInf_comap | (intros; apply GlobalTheory.RelIdxRestr.relIndex_iInf_comap <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → ∀ (F : X → ℂ) (Fv : ∀ v, Y v → ℂ), (∀ x, F x = ∏ᶠ v, Fv v (pf v x)) → (∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y) → (∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) → ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) = ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  first | exact @GlobalTheory.EulerAbs.finsum_doubleCoset_restr | exact GlobalTheory.EulerAbs.finsum_doubleCoset_restr | (intros; apply GlobalTheory.EulerAbs.finsum_doubleCoset_restr <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.StabInt.mem_KGL_of_commute | exact GlobalTheory.StabInt.mem_KGL_of_commute | (intros; apply GlobalTheory.StabInt.mem_KGL_of_commute <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.NormScaleHaar
open Formalism.UG GlobalTheory.AdelicU

theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

end GlobalTheory.NormScaleHaar
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem UQ.norm_of_fixed_unit {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (w w' : E) (hs : star w = w) (h1 : ‖w‖ ≤ 1)
    (h1' : ‖w'‖ ≤ 1) (hww : w * w' = 1) : ∃ v : E, v * star v = w := by
  obtain ⟨ζ, -, hζ⟩ := GlobalTheory.NormUnits.exists_far_unit F E
  obtain ⟨a, ha⟩ := GlobalTheory.NormUnits.fixed_mem_range F E ζ hζ w hs
  have hprod : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, hww, norm_one]
  have hwn : ‖w‖ = 1 := by
    refine le_antisymm h1 ?_
    by_contra h
    push_neg at h
    have : ‖w‖ * ‖w'‖ < 1 :=
      calc ‖w‖ * ‖w'‖ ≤ ‖w‖ * 1 := by gcongr
        _ < 1 := by simpa using h
    linarith
  have han : ‖a‖ = 1 := by rw [← norm_algebraMap' E a, ha, hwn]
  obtain ⟨v, hv⟩ := GlobalTheory.NormUnits.norm_onto_units F E a han
  exact ⟨v, by rw [hv, ha]⟩

theorem UQ.unit_fixed_is_norm : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  intro K t ht hct
  obtain ⟨F, nF, nE, hE, nA, st, hU, hst, hball⟩ := K.exists_unram
  have hmul : ∀ x y : K.E, @HMul.hMul K.E K.E K.E (@instHMul K.E nE.toMul) x y = x * y := by
    intro x y; rw [← hE]
  have hone : @OfNat.ofNat K.E 1 (@One.toOfNat1 K.E nE.toOne) = 1 := by rw [← hE]
  obtain ⟨u, rfl⟩ := ht
  have hww : algebraMap K.O K.E u * algebraMap K.O K.E (u⁻¹ : K.Oˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨v, hv⟩ := @UQ.norm_of_fixed_unit F K.E nF nE nA st hU (algebraMap K.O K.E u)
    (algebraMap K.O K.E (u⁻¹ : K.Oˣ)) (by rw [hst]; exact hct) ((hball _).2 ⟨u, rfl⟩) ((hball _).2 ⟨_, rfl⟩)
    (by rw [hmul, hone]; exact hww)
  refine ⟨v, ?_⟩
  rw [← hst, ← hmul]; exact hv

end GlobalTheory.UnitLemma
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  first | exact @GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact | exact GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact | (intros; apply GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory

theorem selfDual_orthogonal_unit_step : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hLfg hLspan hdual k f hfL horth hunit hk
  have alg_inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hadd2 : ∀ y z z', h y (z + z') = h y z + h y z' := by
    intro y z z'
    rw [hsym (z + z') y, hadd, map_add (f := _), ← hsym, ← hsym]
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym (a • z) y, hsmul, map_mul, ← hsym]
  let H1 : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z,
      map_smul' := fun a y => by simp [hsmul] }
  let H2 : V → V →+ K.E := fun y => AddMonoidHom.mk' (fun z => h y z) (hadd2 y)
  have h0l : ∀ z, h 0 z = 0 := fun z => (H1 z).map_zero
  have hsub1 : ∀ a b z, h (a - b) z = h a z - h b z := fun a b z => (H1 z).map_sub a b
  have hsub2 : ∀ y a b, h y (a - b) = h y a - h y b := fun y a b => (H2 y).map_sub a b
  have hsum1 : ∀ (g : Fin k → V) z, h (∑ i, g i) z = ∑ i, h (g i) z :=
    fun g z => map_sum (H1 z) g Finset.univ
  have hsum2 : ∀ (g : Fin k → V) y, h y (∑ i, g i) = ∑ i, h y (g i) :=
    fun g y => map_sum (H2 y) g Finset.univ
  have hsmulO : ∀ (o : K.O) (v : V), (algebraMap K.O K.E o) • v = o • v :=
    fun o v => algebraMap_smul K.E o v
  have hint : ∀ y ∈ L, ∀ z ∈ L, ∃ a : K.O, h y z = algebraMap K.O K.E a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    exact ⟨a, ha.symm⟩
  have hs : ∀ i, h (f i) (f i) ≠ 0 := by
    intro i
    obtain ⟨t, ht, he⟩ := hunit i
    rw [he]
    intro h0
    apply ht.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  let M : Submodule K.O V :=
    { carrier := {y | y ∈ L ∧ ∀ i, h y (f i) = 0}
      add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, fun i => by rw [hadd, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, fun i => h0l (f i)⟩
      smul_mem' := fun o y hy => ⟨L.smul_mem o hy.1, fun i => by rw [← hsmulO, hsmul, hy.2 i, mul_zero]⟩ }
  have memM : ∀ y, y ∈ M ↔ y ∈ L ∧ ∀ i, h y (f i) = 0 := fun y => Iff.rfl

  have hP : ∀ l ∈ L, ∃ p ∈ M, (∀ w, (∀ i, h w (f i) = 0) → h w l = h w p) ∧
      (l ∉ Submodule.span K.E (Set.range f) → p ≠ 0) := by
    intro l hl
    set g : Fin k → V := fun i => (h l (f i) / h (f i) (f i)) • f i with hg
    have hgL : ∀ i, g i ∈ L := by
      intro i
      obtain ⟨a, ha⟩ := hint l hl (f i) (hfL i)
      obtain ⟨t, ht, he⟩ := hunit i
      have hc : h l (f i) / h (f i) (f i) = algebraMap K.O K.E (a * ↑ht.unit⁻¹) := by
        rw [ha, he, map_mul, div_eq_mul_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
      simp only [hg]
      rw [hc, hsmulO]
      exact L.smul_mem _ (hfL i)
    refine ⟨l - ∑ i, g i, (memM _).2 ⟨L.sub_mem hl (L.sum_mem fun i _ => hgL i), fun j => ?_⟩,
      fun w hw => ?_, fun hn h0 => ?_⟩
    · rw [hsub1, hsum1, Finset.sum_eq_single j]
      · simp only [hg, hsmul]
        rw [div_mul_cancel₀ _ (hs j), sub_self]
      · intro i _ hij
        simp only [hg, hsmul, horth i j hij, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · rw [hsub2, hsum2, Finset.sum_eq_zero, sub_zero]
      intro i _
      simp only [hg, hsmul2, hw i, mul_zero]
    · apply hn
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hspan : Submodule.span K.E (Set.range f) ≠ ⊤ := by
    intro htop
    have h1 := finrank_range_le_card (R := K.E) f
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
    omega
  obtain ⟨l, hl, hlnot⟩ : ∃ l ∈ L, l ∉ Submodule.span K.E (Set.range f) := by
    by_contra hcon
    push_neg at hcon
    apply hspan
    rw [eq_top_iff, ← hLspan]
    exact Submodule.span_le.2 (fun x hx => hcon x hx)
  have hMne : M ≠ ⊥ := by
    obtain ⟨p, hpM, -, hp0⟩ := hP l hl
    intro hb
    rw [hb] at hpM
    exact hp0 hlnot ((Submodule.mem_bot _).1 hpM)

  by_contra hno
  push_neg at hno
  let Q : Submodule K.O K.E := Submodule.map (Algebra.linearMap K.O K.E) (IsLocalRing.maximalIdeal K.O)
  have hQsmul : ∀ (o : K.O) x, x ∈ Q → algebraMap K.O K.E o * x ∈ Q := by
    intro o x hx
    rw [← Algebra.smul_def]
    exact Q.smul_mem o hx
  have hQdiag : ∀ y ∈ M, h y y ∈ Q := by
    intro y hy
    obtain ⟨t, ht⟩ := hint y hy.1 y hy.1
    refine Submodule.mem_map.2 ⟨t, ?_, by rw [Algebra.linearMap_apply, ht]⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hno y hy.1 hy.2 t hu ht
  have hpol : ∀ y ∈ M, ∀ z ∈ M, ∀ o : K.O,
      algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z ∈ Q := by
    intro y hy z hz o
    obtain ⟨μ, hμ⟩ := K.c_int o
    have hw : y + (algebraMap K.O K.E o) • z ∈ M := by
      rw [hsmulO]
      exact M.add_mem hy (M.smul_mem o hz)
    have e : algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z =
        h (y + (algebraMap K.O K.E o) • z) (y + (algebraMap K.O K.E o) • z) - h y y
          - algebraMap K.O K.E o * (algebraMap K.O K.E μ * h z z) := by
      simp only [hadd, hadd2, hsmul, hsmul2, hμ]
      ring
    rw [e]
    exact Q.sub_mem (Q.sub_mem (hQdiag _ hw) (hQdiag _ hy)) (hQsmul _ _ (hQsmul _ _ (hQdiag _ hz)))
  have hQall : ∀ y ∈ M, ∀ z ∈ M, h y z ∈ Q := by
    intro y hy z hz
    obtain ⟨a, b, hab, hnot⟩ := K.c_res
    have h1 := hpol y hy z hz 1
    have h2 := hpol y hy z hz a
    simp only [map_one, one_mul] at h1
    rw [hab] at h2
    have h3 : algebraMap K.O K.E (a - b) * h y z ∈ Q := by
      have := Q.sub_mem (hQsmul a _ h1) h2
      convert this using 1
      rw [map_sub]
      ring
    obtain ⟨e, he⟩ := hint y hy.1 z hz.1
    rw [he, ← map_mul] at h3
    obtain ⟨m', hm', hm'e⟩ := Submodule.mem_map.1 h3
    rw [Algebra.linearMap_apply] at hm'e
    have hme := alg_inj hm'e
    rw [hme] at hm'
    rw [he]
    exact Submodule.mem_map.2 ⟨e,
      ((IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hm').resolve_left hnot, rfl⟩

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπm : IsLocalRing.maximalIdeal K.O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπmem : π ∈ IsLocalRing.maximalIdeal K.O := by
    rw [hπm]; exact Ideal.mem_span_singleton_self π
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  have hle : M ≤ IsLocalRing.maximalIdeal K.O • M := by
    intro w hw
    have hw' : (algebraMap K.O K.E π)⁻¹ • w ∈ M := by
      refine (memM _).2 ⟨(hdual _).2 fun l hl => ?_, fun i => by rw [hsmul, hw.2 i, mul_zero]⟩
      obtain ⟨p, hp, hpw, -⟩ := hP l hl
      rw [hsmul, hpw w hw.2]
      obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 (hQall w hw p hp)
      rw [hπm, Ideal.mem_span_singleton'] at hb
      obtain ⟨d, rfl⟩ := hb
      rw [← hbe, Algebra.linearMap_apply, map_mul]
      exact ⟨d, by field_simp⟩
    have hweq : w = π • ((algebraMap K.O K.E π)⁻¹ • w) := by
      rw [← hsmulO, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    rw [hweq]
    exact Submodule.smul_mem_smul hπmem hw'
  have hfg : M.FG := Submodule.FG.of_le hLfg (fun y hy => hy.1)
  exact hMne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle
    (IsLocalRing.maximalIdeal_le_jacobson _))

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hermitian_form_det_unit_and_twist : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  first | exact @GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | exact GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | (intros; apply GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_traceForm_of_twistedNorm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  first | exact @GlobalTheory.TwTraceForm.exists_trace_form | exact GlobalTheory.TwTraceForm.exists_trace_form | (intros; apply GlobalTheory.TwTraceForm.exists_trace_form <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.isIntegral_of_preserves_fullLattice : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A) (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ z ∈ L, u * z ∈ L) → IsIntegral K.O u := by
  first | exact @GlobalTheory.UnitLemma.isIntegral_of_lat_stable | exact GlobalTheory.UnitLemma.isIntegral_of_lat_stable | (intros; apply GlobalTheory.UnitLemma.isIntegral_of_lat_stable <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical


theorem _root_.GlobalTheory.T.traceForm_linearIsometry_eq_mul_normOneTorus : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (u β : B.A), B.σ β = β * ((-1) ^ n * u) → Algebra.adjoin K.E {u} = ⊤ → (∀ y, (∀ z, B.herm β y z = 0) → y = 0) → ∀ f : B.A →ₗ[K.E] B.A, Function.Surjective f → (∀ y z, B.herm β (f y) (f z) = B.herm β y z) → ∃ a : B.Aˣ, a ∈ B.T ∧ ∀ y, f y = (a : B.A) * y := by
  first | exact @GlobalTheory.IsomMulTorus.isom_eq_mul | exact GlobalTheory.IsomMulTorus.isom_eq_mul | (intros; apply GlobalTheory.IsomMulTorus.isom_eq_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.gramMatrix_traceForm_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  first | exact @GlobalTheory.GramChange.gram_basis_change | exact GlobalTheory.GramChange.gram_basis_change | (intros; apply GlobalTheory.GramChange.gram_basis_change <;> assumption)
end
