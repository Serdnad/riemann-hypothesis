module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle715
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle008
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.LocCore

theorem adj_det_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    (∀ i j, v (A.adjugate i j) ≤ 1) ∧ v A.det ≤ 1 := by
  let A' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have hA' : A'.map v.integer.subtype = A := by ext i j; rfl
  constructor
  · intro i j
    have h := RingHom.map_adjugate v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.adjugate i j).2
  · have h := RingHom.map_det v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.det).2

theorem solve_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A B κ : Matrix (Fin n) (Fin n) K) (hAB : A * κ = B)
    (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hdA : v A.det = 1) (hdB : v B.det = 1) :
    (∀ a b, v (κ a b) ≤ 1) ∧ v κ.det = 1 ∧
      ((∀ i j, v ((A - 1) i j) < 1) → (∀ i j, v ((B - 1) i j) < 1) →
        ∀ a b, v ((κ - 1) a b) < 1) := by
  obtain ⟨hadj, -⟩ := adj_det_integral v A hA
  have key : A.det • κ = A.adjugate * B := by
    rw [← hAB, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have key' : A.det • (κ - 1) = A.adjugate * (B - A) := by
    rw [smul_sub, key, Matrix.mul_sub, Matrix.adjugate_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h := congrFun (congrFun key a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hadj a k) (hB k b)
  · have h := congrArg v (congrArg Matrix.det hAB)
    rw [Matrix.det_mul, map_mul, hdA, one_mul, hdB] at h
    exact h
  · intro hA1 hB1 a b
    have h := congrFun (congrFun key' a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    have hBA : (B - A) k b = (B - 1) k b - (A - 1) k b := by
      simp only [Matrix.sub_apply, sub_sub_sub_cancel_right]
    have hlt : v ((B - A) k b) < 1 := by
      rw [hBA]; exact lt_of_le_of_lt (v.map_sub _ _) (max_lt (hB1 k b) (hA1 k b))
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hadj a k)) hlt

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

noncomputable def topAt {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) :
    Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion D.host.E P) :=
  fun i j => GlobalTheory.StdFrames.cpt P (U (Fin.castLE hmn i) j)

theorem topAt_facts {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (hU : IsIntM U)
    (hdU : IsUnit (topL n (redM P U)).det) :
    (∀ i j, Valued.v (topAt P hmn U i j) ≤ 1) ∧ Valued.v (topAt P hmn U).det = 1 ∧
      (topL n (redM P U) = 1 → ∀ i j, Valued.v ((topAt P hmn U - 1) i j) < 1) := by
  let S := Formalism.L2.Herm.intAf (↥D.host.F) D.host.E
  let A' : Matrix (Fin n) (Fin n) S := fun i j => ⟨U (Fin.castLE hmn i) j, hU _ _⟩
  let φ : S →+* HeightOneSpectrum.adicCompletion D.host.E P :=
    (GlobalTheory.StdFrames.cpt P).comp S.subtype
  have hA : A'.map φ = topAt P hmn U := by ext i j; rfl
  have hred : A'.map (resS (↥D.host.F) P) = topL n (redM P U) := by
    ext i j
    simp only [Matrix.map_apply, topL, redM]
    rw [dite_eq_left ⟨lt_of_lt_of_le i.2 hmn, j.2⟩, dite_eq_left (hU _ _)]
    rfl
  have hint : ∀ i j, Valued.v (topAt P hmn U i j) ≤ 1 := by
    intro i j
    have := (GlobalTheory.StdFrames.mem_OA_iff (U (Fin.castLE hmn i) j)).1 (hU _ _) P
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  have hφ : ∀ s : S, resS (↥D.host.F) P s = 0 ↔ Valued.v (φ s) < 1 :=
    fun s => GlobalTheory.AdIsom.resS_eq_zero_iff_cpt P s
  refine ⟨hint, ?_, ?_⟩
  · apply le_antisymm ((adj_det_integral Valued.v _ hint).2)
    have h1 : resS (↥D.host.F) P A'.det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hred]; exact hdU.ne_zero
    rw [Ne, hφ, not_lt, RingHom.map_det, RingHom.mapMatrix_apply, hA] at h1
    exact h1
  · intro h1 i j
    have hm : (resS (↥D.host.F) P).mapMatrix (A' - 1) = 0 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hred, h1, sub_self]
    have h2 : resS (↥D.host.F) P ((A' - 1) i j) = 0 := by
      have := congrFun (congrFun hm i) j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hm' : φ.mapMatrix (A' - 1) = topAt P hmn U - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hA]
    have h3 : (topAt P hmn U - 1) i j = φ ((A' - 1) i j) := by
      have e := congrFun (congrFun hm' i) j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      exact e.symm
    rw [h3]
    exact (hφ _).1 h2

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

theorem kappa_integral_at : ∀ (D : D7) (P : Pl D.host.E) (m n : ℕ) (U Y : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (κ : Matrix (Fin n) (Fin n) (Formalism.IndefR.Datum.EAf D)) (c : Formalism.IndefR.Datum.EAf D), GlobalTheory.StdFrames.cpt P c = 1 → (HMul.hMul U κ : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) = c • Y + (1 - c) • U → IsIntM U → IsIntM Y → IsUnit (topL n (redM P U)).det → IsUnit (topL n (redM P Y)).det → (∀ a b, GlobalTheory.StdFrames.cpt P (κ a b) ∈ P.adicCompletionIntegers D.host.E) ∧ Valued.v (GlobalTheory.StdFrames.cpt P κ.det) = 1 ∧ (topL n (redM P U) = 1 → topL n (redM P Y) = 1 → ∀ a b, Valued.v (GlobalTheory.StdFrames.cpt P ((κ - 1) a b)) < 1) := by
  intro D P m n U Y κ c hc hUk hU hY hdU hdY
  by_cases hmn : n ≤ m
  swap
  · exfalso
    push_neg at hmn
    have h0 : (topL n (redM P U)).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero ⟨m, hmn⟩
      intro j
      simp [topL]
    rw [h0] at hdU
    exact not_isUnit_zero hdU
  set cp := GlobalTheory.StdFrames.cpt (D := D) P with hcp
  obtain ⟨hAi, hAd, hA1⟩ := topAt_facts P hmn U hU hdU
  obtain ⟨hBi, hBd, hB1⟩ := topAt_facts P hmn Y hY hdY
  have hAB : topAt P hmn U * κ.map cp = topAt P hmn Y := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg cp (congrFun (congrFun hUk (Fin.castLE hmn i)) j)

    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
    map_mul, map_add, map_sub, map_one, hc, sub_self, zero_mul, add_zero, one_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    exact h
  obtain ⟨k1, k2, k3⟩ := solve_integral Valued.v _ _ _ hAB hAi hBi hAd hBd
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (k1 a b)
  · rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact k2
  · intro h1 h2 a b
    have e : cp.mapMatrix (κ - 1) = κ.map cp - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply]
    have e2 := congrFun (congrFun e a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e2
    rw [e2]
    exact k3 (hA1 h1) (hB1 h2) a b

end GlobalTheory.LocCore
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  first | exact @GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos | exact GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos | (intros; apply GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertHeckeEigen

open Formalism.UG GlobalTheory.PRep

section Abstract

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def quotMap (p : G →* H) (K : Subgroup H) : G ⧸ K.comap p → H ⧸ K :=
  Quotient.map' p fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact hab

theorem quotMap_mk (p : G →* H) (K : Subgroup H) (a : G) :
    quotMap p K (a : G ⧸ K.comap p) = (p a : H ⧸ K) := rfl

theorem quotMap_bijective (p : G →* H) (hp : Function.Surjective p) (K : Subgroup H) :
    Function.Bijective (quotMap p K) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quotMap_mk, quotMap_mk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  · intro d
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨a, rfl⟩ := hp y
    exact ⟨a, rfl⟩

theorem heckeVec_comp_surj (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (ρ : Representation ℂ H V) {v : V} (hv : v ∈ fixed ρ K) :
    GlobalTheory.LFun.heckeVec (ρ.comp p) (K.comap p) (fun x => h (p x)) v = GlobalTheory.LFun.heckeVec ρ K h v := by
  let e := Equiv.ofBijective _ (quotMap_bijective p hp K)
  rw [GlobalTheory.LFun.heckeVec_eq_of_section hh hv (fun d => p (e.symm d).out) fun d => ?_]
  · rw [← finsum_comp_equiv e (f := fun d => h (p (e.symm d).out) • ρ (p (e.symm d).out) v)]
    simp only [Equiv.symm_apply_apply]
    rfl
  · rw [← quotMap_mk, QuotientGroup.out_eq']
    exact e.apply_symm_apply d

theorem finite_support_comp (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (hf : {d : H ⧸ K | h d.out ≠ 0}.Finite) :
    {c : G ⧸ K.comap p | h (p c.out) ≠ 0}.Finite := by
  refine (hf.preimage (quotMap_bijective p hp K).1.injOn).subset fun c hc => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hc ⊢
  have hk : (quotMap p K c).out⁻¹ * p c.out ∈ K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← quotMap_mk, QuotientGroup.out_eq']
  have e1 := hh 1 ⟨_, hk⟩ (quotMap p K c).out
  simp only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] at e1
  rwa [e1] at hc

theorem heckeVec_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (S : Finset (G ⧸ K))
    (hS : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ S) (x : V) :
    GlobalTheory.LFun.heckeVec ρ K h x = ∑ c ∈ S, h c.out • ρ c.out x := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => hS c fun h0 => hc ?_
  simp [h0]

theorem mem_of_mem_iSup {ι : Type} (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hσ : σ.IsIrreducible)
    (f : ι → W →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (Z : Submodule ℂ V)
    (hZ : ∀ i v, (∀ k ∈ K, σ k v = v) → f i v ∈ Z) (hZK : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V)
    (hK : ∀ k ∈ K, ρ k φ = φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : φ ∈ Z := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7; revert G V W h_3 h_4 h_5 h_6 h_7 ι ρ σ hσ f hf K Z hZ hZK φ hK hφ; exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range)
  | exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | (apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range ..)

end Abstract

end GlobalTheory.InertHeckeEigen


open GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in
theorem GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  intro L _ _ _ n U hU w s ϖ q hq p hp σ hcomp α0 hsat φ hφ hfix h hh
  have hfin : {c : locU n w ⧸ (KU s n).comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hq n) hh.2)
  have hS : ∀ c : locU n w ⧸ (KU s n).comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let lam := SatU ϖ q h (fun i => (α0 i : ℂ))
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ (KU s n).comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl

  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.ρ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype (σ.ρ.comp p) (σ.ρ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) → σ.V →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.ρ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this

  have hZ : ∀ i v, (∀ k ∈ ((KU s n).comap p : Set (locU n w)), (σ.ρ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ.ρ (KU s n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ.ρ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [((hsat.2 v hvK hv0).2.2 h hh)] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.ρ.comp p) c.out v) := by

          rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ ((KU s n).comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.ρ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitRealPrime

theorem exists_prime_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ p : ℕ, p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, -, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E 0
  refine ⟨p, hp, fun w hw => ?_⟩
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨a, b, hab, ha, hb⟩ :=
    GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
  by_cases h : a = w
  · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
  · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

end GlobalTheory.SplitRealPrime
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rec_of_rec_literal : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  first | exact @GlobalTheory.LocLanglands.isRec_of_isRecLit | exact GlobalTheory.LocLanglands.isRec_of_isRecLit | (intros; apply GlobalTheory.LocLanglands.isRec_of_isRecLit <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.AdmBK

theorem litGoodO_all : LitGoodO := fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

theorem blochKato_dimFormula_all_finiteExt_coeffField (D : D7) : TruncatedSeriesCountingBounds.adm8 D := fun l _ K LL _ =>
  GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL

theorem admBK_loc_of_blochKato_tateDuality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilators_of D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D)
    (fun l _ K => GlobalTheory.TateTop.tateH2_of_duality_loc hTD l (D.loc l) K) (blochKato_dimFormula_all_finiteExt_coeffField D) litGoodO_all

end GlobalTheory.AdmBK
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BKaRows

theorem bkaAll_of_hypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilator_above_l D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D) GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing

end GlobalTheory.BKaRows
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_hwOf_fonOf_cmpOf' : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  first | exact @GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | exact GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | (intros; apply GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf <;> assumption)
end
