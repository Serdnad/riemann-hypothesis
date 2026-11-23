module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle368
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Twist

open scoped TensorProduct Matrix



theorem exists_pow_projArch_not_mem_of_eigen_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  intro D V g x hx hg w K hK
  classical
  set c : Fin V.rank → D.host.E := ⇑(V.frame.repr x) with hc_def
  have hM : (g.1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) • c := by
    have h1 := congrArg (fun y => ⇑(V.frame.repr y)) hg
    simp only [GlobalTheory.Cusp.ratAct, map_smul, Finsupp.coe_smul] at h1
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, LinearMap.toMatrix_toLin] at h1
    exact h1
  have hMn : ∀ n : ℕ, ((g ^ n).1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) ^ n • c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    have : V.frame.repr x = 0 := Finsupp.ext h
    simpa using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual D.host.F D.host.E, φ (c j) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hj ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)

  let ι : D.host.E →+* w.Completion ⊗[D.host.F] D.host.E := inclR (F := D.host.F) w.Completion
  let Λ : w.Completion ⊗[D.host.F] D.host.E →ₗ[w.Completion] w.Completion :=
    (TensorProduct.AlgebraTensorModule.rid D.host.F w.Completion w.Completion).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map LinearMap.id φ
  have hΛ1 : ∀ e : D.host.E, Λ (ι e) = algebraMap D.host.F w.Completion (φ e) := by
    intro e
    simp [Λ, ι, inclR, Algebra.algebraMap_eq_smul_one]
  have : IsModuleTopology w.Completion (w.Completion ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing w.Completion _
  have hΛ : Continuous Λ := IsModuleTopology.continuous_of_linearMap Λ
  let f : GArch D.sp.cm.sig V.gram w → w.Completion := fun h =>
    Λ (((matHom _ D.sp.cm.sig V.gram h).val *ᵥ (fun i => ι (c i))) j)
  have hm : Continuous fun h : GArch D.sp.cm.sig V.gram w =>
      (matHom _ D.sp.cm.sig V.gram h).val :=
    Units.continuous_val.comp (isEmbedding_matHom _ _ _).continuous
  have hf : Continuous f := hΛ.comp ((continuous_apply j).comp (hm.matrix_mulVec continuous_const))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have he : ∀ γ : GF V, (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w γ)).val = (γ.1.1).map ι :=
    fun γ => rfl
  have hval : ∀ n : ℕ, f (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V)) =
      algebraMap D.host.F w.Completion ((2 : D.host.F) ^ n * φ (c j)) := by
    intro n
    have e1 : (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V))).val = ((g ^ n).1.1).map ι := he (g ^ n)
    simp only [f]
    rw [e1, show (fun i => ι (c i)) = ⇑ι ∘ c from rfl, ← RingHom.map_mulVec, hMn n, Pi.smul_apply, smul_eq_mul, hΛ1]
    congr 1
    rw [show (2 : D.host.E) ^ n * c j = ((2 : D.host.F) ^ n) • c j by rw [Algebra.smul_def, map_pow, map_ofNat],
      map_smul, smul_eq_mul]
  have hnorm : ∀ a : D.host.F, ‖algebraMap D.host.F w.Completion a‖ = w a := fun a => by
    rw [show algebraMap D.host.F w.Completion a = ((a : D.host.F) : w.Completion) from by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]]
    exact AbsoluteValue.Completion.norm_coe _
  have hpos : 0 < w (φ (c j)) := (InfinitePlace.pos_iff).2 hφ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / w (φ (c j))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun hmem => ?_⟩
  rw [show projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) = ratArch D.sp.cm.sig V.gram w (g ^ n : GF V) from
    projArch_ratEmb _ _ w _] at hmem
  have h1 := hC _ hmem
  rw [hval, hnorm, map_mul, map_pow] at h1
  have h2 : w (2 : D.host.F) = 2 := by
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  rw [h2] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

end GlobalTheory.Twist
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Cusp.WeightCommute

open Matrix

variable {D : D7} {V : HSp D}

theorem ratAct_mul' (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one' (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem hT_ratAct (γ : GF V) (a b : V.V) :
    V.hT (GlobalTheory.Cusp.ratAct D.sp.cm V γ a) (GlobalTheory.Cusp.ratAct D.sp.cm V γ b) = V.hT a b := by
  have hγ : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 * V.gram * γ.1.1 = V.gram := γ.2
  have hc : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 = Matrix.conjTranspose γ.1.1 := by
    ext i j; rfl
  rw [hc] at hγ
  have hr : ∀ w, V.frame.repr (GlobalTheory.Cusp.ratAct D.sp.cm V γ w) = γ.1.1 *ᵥ V.frame.repr w := fun w => by
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, GlobalTheory.Cusp.ratAct, LinearMap.toMatrix_toLin]
  have hform : ∀ x y : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, hr, hr, hform, hform, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hγ]

theorem hT_frame (Φ : WittFrame V) (i j : Fin (wittIndex V)) :
    V.hT (Φ.f j) (Φ.e i) = (if i = j then 1 else 0) ∧ V.hT (Φ.e j) (Φ.f i) = (if i = j then 1 else 0) ∧
    V.hT (Φ.e j) (Φ.e i) = 0 ∧ V.hT (Φ.f j) (Φ.f i) = 0 := by
  refine ⟨Φ.ef i j, ?_, Φ.ee i j, Φ.ff i j⟩
  rw [← V.herm.eq (Φ.f i) (Φ.e j)]
  have h : V.hT (Φ.f i) (Φ.e j) = if j = i then 1 else 0 := Φ.ef j i
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

end GlobalTheory.Cusp.WeightCommute


open GlobalTheory.Cusp.WeightCommute in
theorem GlobalTheory.Cusp.WeightCommute.commute_of_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  intro D V Φ u γ g t h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨xv, hxv⟩ : ∃ xv : Fin (wittIndex V) → V.V, ∀ i, xv i = if u i = 1 then Φ.e i else Φ.f i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ yv : Fin (wittIndex V) → V.V, ∀ i, yv i = if u i = 1 then Φ.f i else Φ.e i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (wittIndex V)), ∀ i, i ∈ S ↔ u i ≠ 0 :=
    ⟨Finset.univ.filter (fun i => u i ≠ 0), fun i => by simp⟩
  have hsgn : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  have hne : (-1 : SignType) ≠ 1 := by decide
  have hs : ∀ i ∈ S, u i = 1 ∨ u i = -1 := fun i hi => hsgn _ ((hS i).1 hi)
  have key := hT_frame Φ
  have neq : ∀ i j, u i = 1 → u j = -1 → i ≠ j := by
    rintro i j a b rfl; rw [a] at b; exact hne b.symm

  have mx : ∀ i ∈ S, xv i ∈ Φ.sub u := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hxv, if_pos a]; exact Submodule.subset_span (Or.inl ⟨i, a, rfl⟩)
    · rw [hxv, if_neg (by rw [a]; exact hne)]; exact Submodule.subset_span (Or.inr ⟨i, a, rfl⟩)
  have my : ∀ i ∈ S, yv i ∈ Φ.sub (-u) := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hyv, if_pos a]
      exact Submodule.subset_span (Or.inr ⟨i, show -(u i) = -1 by rw [a], rfl⟩)
    · rw [hyv, if_neg (by rw [a]; exact hne)]
      exact Submodule.subset_span (Or.inl ⟨i, show -(u i) = 1 by rw [a]; rfl, rfl⟩)

  have genX : ∀ z, (∀ i ∈ S, V.hT (xv i) z = 0) → ∀ w ∈ Φ.sub u, V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub u ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = 1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_pos (show u i = 1 from hi)] at this
        exact this
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = -1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_neg (by rw [show u i = -1 from hi]; exact hne)] at this
        exact this
    exact hle hw
  have genY : ∀ z, (∀ i ∈ S, V.hT (yv i) z = 0) → ∀ w ∈ Φ.sub (-u), V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have a : u i = -1 := neg_eq_iff_eq_neg.1 (show -(u i) = 1 from hi)
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_neg (by rw [a]; exact hne)] at this
        exact this
      · have a : u i = 1 := by
          have h' : -(u i) = -1 := hi
          simpa using h'
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_pos a] at this
        exact this
    exact hle hw

  have pxx : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (xv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.1
    · rw [(key i j).1, if_neg (neq i j a b)]
    · rw [(key i j).2.1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.2
  have pyy : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (yv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.2
    · rw [(key i j).2.1, if_neg (neq i j a b)]
    · rw [(key i j).1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.1
  have pyx : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (xv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).1
    · rw [(key i j).2.2.1, if_neg (neq i j a b)]
    · rw [(key i j).2.2.2, if_neg (neq j i b a).symm]
    · exact (key i j).2.1
  have pxy : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (yv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.1
    · rw [(key i j).2.2.2, if_neg (neq i j a b)]
    · rw [(key i j).2.2.1, if_neg (neq j i b a).symm]
    · exact (key i j).1

  have decomp : ∀ v : V.V, ∃ x ∈ Φ.sub u, ∃ y ∈ Φ.sub (-u), ∃ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) ∧
      (∀ w ∈ Φ.sub (-u), V.hT w z = 0) ∧ v = x + y + z := by
    intro v
    refine ⟨∑ i ∈ S, V.hT (yv i) v • xv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (mx i hi)),
      ∑ i ∈ S, V.hT (xv i) v • yv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (my i hi)),
      v - (∑ i ∈ S, V.hT (yv i) v • xv i) - ∑ i ∈ S, V.hT (xv i) v • yv i, genX _ ?_, genY _ ?_, by abel⟩
    · intro j hj

      rw [map_sub, map_sub, map_sum, map_sum,
      Finset.sum_eq_zero (fun i hi => by rw [map_smul, pxx i hi j hj, smul_zero]),
      Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pxy i hi j hj, if_neg hij, smul_zero])
        (fun h => absurd hj h),
      map_smul, pxy j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp
    · intro j hj

      rw [map_sub, map_sub, map_sum, map_sum,
      Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pyx i hi j hj, if_neg hij, smul_zero])
        (fun h => absurd hj h),
      Finset.sum_eq_zero (fun i hi => by rw [map_smul, pyy i hi j hj, smul_zero]),
      map_smul, pyx j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp

  have inv_app : ∀ w, GlobalTheory.Cusp.ratAct D.sp.cm V γ (GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ w) = w := by
    intro w; rw [← ratAct_mul', mul_inv_cancel, ratAct_one']
  have zX : ∀ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) →
      ∀ w ∈ Φ.sub u, V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h3 w hw)
  have zY : ∀ z, (∀ w ∈ Φ.sub (-u), V.hT w z = 0) →
      ∀ w ∈ Φ.sub (-u), V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h4 w hw)
  have hmat : (g * γ).1.1 = (γ * g).1.1 := by
    apply (Matrix.toLin V.frame V.frame).injective
    apply LinearMap.ext
    intro v
    show GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ) v = GlobalTheory.Cusp.ratAct D.sp.cm V (γ * g) v
    rw [ratAct_mul', ratAct_mul']
    obtain ⟨x, hx, y, hy, z, hzX, hzY, rfl⟩ := decomp v
    simp only [map_add (f := _)]
    rw [h5 _ (h1 x hx), h6 _ (h2 y hy), h7 _ (zX z hzX) (zY z hzY), h5 x hx, h6 y hy, h7 z hzX hzY,
      map_smul, map_smul]
  exact Subtype.ext (Units.ext hmat)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

theorem isEnum_cast' {S : SPar} {n k : ℕ} (h : k = n) {lam : Fin n → ℝ} {ε : Fin n → Bool} (hE : IsEnum S lam ε) :
    IsEnum S (fun i : Fin k => lam (Fin.cast h i)) (fun i => ε (Fin.cast h i)) := by
  subst h
  simpa using hE

theorem UH_mul' {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem conj_mul' {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (x y : Matrix (Fin n) (Fin n) ℂ) :
    B * (x * y) * B⁻¹ = B * x * B⁻¹ * (B * y * B⁻¹) := by
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  calc B * (x * y) * B⁻¹ = B * x * (B⁻¹ * B) * y * B⁻¹ := by rw [hBi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = B * x * B⁻¹ * (B * y * B⁻¹) := by simp only [Matrix.mul_assoc]

end GlobalTheory.PackLoc

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.TrFinExt

private theorem eq_of_finE_map_prV_eq_forall_place {D : D7} (V : HSp D) (a b : GA D V)
    (h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V a).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V b).val.map (Formalism.UG.prV (E := D.host.E) u))
    (i j : Fin V.rank) :
    (Formalism.IndefR.Lev.finE V a).val i j = (Formalism.IndefR.Lev.finE V b).val i j := by

  rw [← sub_eq_zero]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  have hw := congrFun (congrFun (h w) i) j
  rw [Matrix.map_apply, Matrix.map_apply] at hw
  rw [map_sub, hw, sub_self]

theorem gfc_ext : ∀ {D : D7} (V : HSp D) (x y : GfC V), (∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V (x : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V (y : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u)) → x = y := by
  intro D V x y h

  have hx : infHom V (x : GA D V) = 1 := x.2
  have hy : infHom V (y : GA D V) = 1 := y.2
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply GlobalTheory.FinIsoGrp.proj_inj D
  · have ex := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => g.val i j) hx
    have ey := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => g.val i j) hy
    exact ex.trans ey.symm
  · have e := eq_of_finE_map_prV_eq_forall_place V (x : GA D V) (y : GA D V) h i j
    rw [GlobalTheory.FinIsoGrp.finE_val, GlobalTheory.FinIsoGrp.finE_val] at e
    exact e

end GlobalTheory.TrFinExt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.tensor_irreducible_of_countable_dimension_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.TensIrr.tensor_irreducible | exact GlobalTheory.TensIrr.tensor_irreducible | (intros; apply GlobalTheory.TensIrr.tensor_irreducible <;> assumption)
end
