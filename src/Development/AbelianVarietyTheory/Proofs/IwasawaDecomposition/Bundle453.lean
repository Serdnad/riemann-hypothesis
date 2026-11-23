module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle802
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle363
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle417
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
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
import ReciprocityTheory.Automorphisms.PlaceA
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtRed

section Split

open ReciprocityTheory.Aut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)

theorem i_mem (a : 𝓞 E) : s.i (a : E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (s.split_le_one a)

def iInt : 𝓞 E →+* s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  ((s.i : E →+* s.v.adicCompletion (maximalRealSubfield E)).comp (algebraMap (𝓞 E) E)).codRestrict _ (i_mem s)

theorem mem_max_iff (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    x ∈ IsLocalRing.maximalIdeal (s.v.adicCompletionIntegers (maximalRealSubfield E)) ↔
      Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

def psiR : 𝓞 E →+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  (IsLocalRing.residue _).comp (iInt s)

theorem psiR_eq_zero (a : 𝓞 E) : psiR s a = 0 ↔ a ∈ s.w.asIdeal := by
  rw [psiR, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  exact Iff.rfl

theorem psiR_surj : Function.Surjective (psiR s) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  obtain ⟨a, ha⟩ := adic_exists_approx s.v _ hx
  refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a, ?_⟩
  rw [psiR, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((iInt s (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
      s.v.adicCompletion (maximalRealSubfield E)) = algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) a := by
    show s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a : 𝓞 E)) : E) = _
    rw [split_coe_algebraMap, AlgHom.commutes]; rfl
  rw [AddSubgroupClass.coe_sub, e, Valuation.map_sub_swap]
  exact ha

def kEqv : kP s.w ≃+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  RingEquiv.ofBijective (Ideal.Quotient.lift s.w.asIdeal (psiR s) fun a ha => (psiR_eq_zero s a).2 ha)
    ⟨by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [Ideal.Quotient.lift_mk, psiR_eq_zero] at hq
      exact Ideal.Quotient.eq_zero_iff_mem.2 hq,
    fun y => by
      obtain ⟨a, rfl⟩ := psiR_surj s y
      exact ⟨Ideal.Quotient.mk s.w.asIdeal a, Ideal.Quotient.lift_mk _ _ _⟩⟩

def phiR : s.v.adicCompletionIntegers (maximalRealSubfield E) →+* kP s.w :=
  ((kEqv s).symm : _ →+* kP s.w).comp (IsLocalRing.residue _)

theorem phiR_surj : Function.Surjective (phiR s) :=
  (kEqv s).symm.surjective.comp IsLocalRing.residue_surjective

theorem phiR_eq_zero (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    phiR s x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (kEqv s).symm.injective,
    IsLocalRing.residue_eq_zero_iff, mem_max_iff]

theorem kEqv_mk (a : 𝓞 E) : kEqv s (Ideal.Quotient.mk s.w.asIdeal a) = psiR s a :=
  Ideal.Quotient.lift_mk s.w.asIdeal (psiR s) (fun a ha => (psiR_eq_zero s a).2 ha)

theorem phiR_i (a : 𝓞 E) : phiR s ⟨_, i_mem s a⟩ = Ideal.Quotient.mk s.w.asIdeal a := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  rw [kEqv_mk]; rfl

theorem exists_approx (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    ∃ a : 𝓞 E, Valued.v ((x : s.v.adicCompletion (maximalRealSubfield E)) - s.i (a : E)) < 1 ∧
      phiR s x = Ideal.Quotient.mk s.w.asIdeal a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (phiR s x)
  refine ⟨a, ?_, ha.symm⟩
  have h : phiR s (x - ⟨_, i_mem s a⟩) = 0 := by
    rw [map_sub, phiR_i, ha, sub_self]
  have h2 := (phiR_eq_zero s _).1 h
  rwa [AddSubgroupClass.coe_sub] at h2

end Split

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem km_mem_UA (κ : Formalism.AUTREP.GAf D.host.E n) : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
  show Formalism.UG.cT (GlobalTheory.StdFrameExist.sgA D) (GlobalTheory.StdFrameExist.kmat κ).1 *
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *
      (GlobalTheory.StdFrameExist.kmat κ).1 = (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, GlobalTheory.StdFrameExist.cT_kmat]

theorem km_mem_St_iff (κ : Formalism.AUTREP.GAf D.host.E n) :
    km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  rw [GlobalTheory.StdFrameExist.mem_Umax_iff]
  constructor
  · rintro ⟨y, hy⟩ i j
    have e : (GlobalTheory.StdFrameExist.kmat κ).1 i j = ((y.1 i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      show (km D n κ).1 i j = _
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    rw [e]
    exact (y.1 i j).2
  · intro h
    have h' : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 :=
      (GlobalTheory.StdFrameExist.mem_Umax_iff _).1 (inv_mem ((GlobalTheory.StdFrameExist.mem_Umax_iff κ).2 h))
    have hm : (GlobalTheory.StdFrameExist.kmat κ).1 * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.mul_inv]
    have hm' : (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 * (GlobalTheory.StdFrameExist.kmat κ).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.inv_mul]
    refine ⟨⟨Matrix.of fun i j => ⟨_, h i j⟩, Matrix.of fun i j => ⟨_, h' i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have := congrFun (congrFun hm i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ).1 i x * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · ext i j
      have := congrFun (congrFun hm' i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 i x * (GlobalTheory.StdFrameExist.kmat κ).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · apply Units.ext
      ext i j
      simp [frGL, intGL, Formalism.UG.bc]
      rfl

theorem red_eq_one (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (PP : Pl D.host.E) (hT : ReciprocityTheory.Aut.TrivOutside A κ) (hP : NG.OverPl PP v) (hv : v ∉ A) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  refine Formalism.L2.DIV.reduction_local D.host.F D.host.E n 1 PP v hP.symm _ ((km_mem_St_iff D n κ).2 hκ) ?_
  have h := hT v hv
  apply Units.ext
  ext i j
  have e := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at e
  exact e

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem red_split (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a b : Fin n) :
    ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = phiR s ⟨_, h⟩ := by
  obtain ⟨y, hy⟩ := (km_mem_St_iff D n κ).2 hκ
  have hz : (κ.1.val a b) ∈ ReciprocityTheory.Aut.ALint D.host.E := hκ a b
  have hz' := GlobalTheory.RowGood.tr_int rfl hz
  rw [GlobalTheory.RowGood.tr_rfl] at hz'
  have hmem : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s hz')
  refine ⟨hmem, ?_⟩
  obtain ⟨c, hc, hφ⟩ := exists_approx s ⟨_, hmem⟩
  rw [hφ]
  have hyab : ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = κ.1.val a b := by
    have e : (km D n κ).1 a b = ((y.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    exact e.symm
  rw [← hy, redFn_frGL]
  have := GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (κ.1.val a b) (y.val a b)
    (by rw [GlobalTheory.RowGood.tr_rfl]; exact hyab) c hc
  exact this

end GlobalTheory.MtRed

end

namespace GlobalTheory.MtRed

theorem km_reduction : ∀ (D : D7) (n : ℕ), (∀ κ, km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E)) ∧ (∀ κ, km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n) ∧ (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v) (PP : Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w, Function.Surjective φ ∧ (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) ∧ (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) ∧ ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ a b, ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = φ ⟨_, h⟩ := by
  intro D n
  exact ⟨km_mem_UA D n, km_mem_St_iff D n, fun κ hκ A v PP hT hP hv => red_eq_one D n κ hκ A v PP hT hP hv,
    fun s => ⟨phiR s, phiR_surj s, phiR_eq_zero s, fun a => ⟨i_mem s a, phiR_i s a⟩,
      fun κ hκ a b => red_split D n κ hκ s a b⟩⟩

end GlobalTheory.MtRed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc

theorem membership_iff_unipSym : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  intro D X h hE hg k hk Ns hNs
  have hK2 : k ∈ X.K2 ↔ K2cong X.B.I X.B.g X.e0 X.z0 X.bw k := ⟨fun hm => hm.2, fun hm => ⟨hk, hm⟩⟩
  have hLf : ∀ y ∈ X.B.I.Lf, (X.B.I.fmat k - 1) *ᵥ y ∈ X.B.I.Lf := by
    intro y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hk y).1 hy) hy
  have hS1 : ∀ a : Fin D.R.rS, X.e0 '' {b | b.1 < a.1} ⊆ X.B.I.Lf := by
    rintro a _ ⟨b, -, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS2 : Set.range X.e0 ⊆ X.B.I.Lf := by
    rintro _ ⟨b, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS3 : ∀ i : Fin D.R.k, Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} ⊆ X.B.I.Lf := by
    rintro i _ (⟨b, rfl⟩ | ⟨j, -, rfl⟩)
    · exact (X.vectorsInLattice.1 b).1
    · exact (X.vectorsInLattice.2.2 j).1
  have hK : K2cong X.B.I X.B.g X.e0 X.z0 X.bw k ↔
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k := by
    have e1 := fun a => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS1 a) _ (hLf _ (X.vectorsInLattice.1 a).1)
    have e2 := GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ hS2 _ (hLf _ X.vectorsInLattice.2.1)
    have e3 := fun i => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS3 i) _ (hLf _ (X.vectorsInLattice.2.2 i).1)
    constructor
    · rintro ⟨h1, h2, h3⟩ w hw
      exact ⟨fun a => (e1 a).1 (h1 a) w hw, e2.1 h2 w hw, fun i => (e3 i).1 (h3 i) w hw⟩
    · intro H
      exact ⟨fun a => (e1 a).2 fun w hw => (H w hw).1 a, e2.2 fun w hw => (H w hw).2.1,
        fun i => (e3 i).2 fun w hw => (H w hw).2.2 i⟩
  have hgE : ((X.B.g : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [X.g_eq, Nat.cast_mul]
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    rintro ⟨kk, v⟩
    rw [hgE]
    fin_cases kk
    · exact Ideal.mul_mem_right _ _ (hg ⟨0, v⟩)
    · exact Ideal.mul_mem_left _ _ (hg ⟨1, v⟩)
  have hP : (∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k) ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), CondAt X (D.naut.plGw kv.1 kv.2) k ∧
        CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k := by
    constructor
    · intro H kv
      refine ⟨H _ (hgw kv), H _ ?_⟩
      rw [GlobalTheory.DimPartsCompare.mem_cPl, map_natCast]
      exact hgw kv
    · intro H w hw
      rw [hgE] at hw
      rcases w.isPrime.mem_or_mem hw with h0 | h1
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 0 w h0
        · exact (H ⟨0, v⟩).1
        · exact (H ⟨0, v⟩).2
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 1 w h1
        · exact (H ⟨1, v⟩).1
        · exact (H ⟨1, v⟩).2
  rw [hK2, hK, hP]
  exact forall_congr' fun kv => (GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj D X h hE hg k hk kv).symm.trans (GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span D X h hE hg k hk kv (Ns kv) (hNs kv)).symm

end GlobalTheory.Mem.GroupLoc
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem autIso_symm {π π' : NG.AutRep L n} (h : π.Iso π') : π'.Iso π := (NG.AutRep.iso_equivalence (L := L) (n := n)).symm h

theorem autIso_trans {π π' π'' : NG.AutRep L n} (h : π.Iso π') (h' : π'.Iso π'') : π.Iso π'' :=
  (NG.AutRep.iso_equivalence (L := L) (n := n)).trans h h'

theorem clsA_eq_iff (π π' : NG.AutRep L n) : clsA π = clsA π' ↔ π.Iso π' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.automorphic_rep_cm_quotient_model L n π'
    have h2 : m ∈ (clsA π).1 := by rw [h]; exact hm
    exact autIso_trans h2 (autIso_symm hm)
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => autIso_trans (autIso_symm h) h', fun h' => autIso_trans h h'⟩

theorem clsW_eq_iff (a b : NG.AlgWt L n) : clsW a = clsW b ↔ a.Iso b := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_coordinate_model_of_algWeight L n b
    have h2 : m ∈ (clsW a).1 := by rw [h]; exact hm
    exact h2.trans hm.symm
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem rep_iso (π : NG.AutRep L n) : (clsA π).rep.Iso π :=
  (clsA_eq_iff _ _).1 (AUq.cls_rep (clsA π))

theorem repW_iso (a : NG.AlgWt L n) : (clsW a).rep.Iso a :=
  (clsW_eq_iff _ _).1 (WtQ.cls_rep (clsW a))

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : π.SphAt v) : π'.SphAt v := by
  obtain ⟨-, T, hT⟩ := h
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  refine ⟨(T ⟨f, hf⟩ : _), (T ⟨f, hf⟩).2, ?_, fun κ hκ ht => ?_⟩
  · intro h0
    apply hf0
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val (T.injective (this.trans T.map_zero.symm))
    exact this
  · have := hT κ ⟨f, hf⟩ ⟨f, hf⟩ (hfix κ hκ ht).symm
    exact this.symm

omit [NumberField L] [IsCMField L] in
theorem overPl_unique {w : HeightOneSpectrum (𝓞 L)} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (h : NG.OverPl w v) (h' : NG.OverPl w v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem locAt_of_split (π : NG.AutRep L n) (s : SplitPlace L) : ∃ x, LocAt π s.w x := by
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  exact ⟨_, s, σ, rfl, hσ, HEq.rfl⟩

theorem locAt_unique {π π' : NG.AutRep L n} (hi : π.Iso π') {w : HeightOneSpectrum (𝓞 L)} {x x'}
    (hx : LocAt π w x) (hx' : LocAt π' w x') : x = x' := by
  obtain ⟨s, σ, hs, hσ, e⟩ := hx
  obtain ⟨s', σ', hs', hσ', e'⟩ := hx'
  obtain ⟨σ₀, -, hu⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  have h1 := hu π s rfl σ ((NG.AutRep.iso_equivalence (L := L) (n := n)).refl π) hσ
  have h2 := hu π' s' (hs'.trans hs.symm) σ' hi hσ'
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 L)) (_ : u = u') (a : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u.adicCompletion L)))
      (b : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u'.adicCompletion L))), HEq a b →
      HEq (⟨n, a⟩ : GlobalTheory.LocGL.IrrGL (k := u.adicCompletion L)) (⟨n, b⟩ : GlobalTheory.LocGL.IrrGL (k := u'.adicCompletion L)) := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    rfl
  have h3 : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls σ') :=
    key _ _ (hs.trans hs'.symm) _ _ (h1.trans h2.symm)
  exact eq_of_heq (e.symm.trans (h3.trans e'))

end

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (D : D7)

theorem f_sat (π : NG.AutRep D.host.E D.R.nV) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : PlE D.host)
    (hv : NG.OverPl w v) (Dv : InertDatum D.host.E D.R.nV v w) (hα : ∃ α, NG.SatAt π Dv α) :
    ∃ α, NG.SatAt π Dv α ∧ satOf (clsA π).rep w = Finset.univ.val.map α := by
  obtain ⟨α, hα⟩ := hα
  have hex : ∃ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' ∧ NG.SatAt (clsA π).rep Dv' α' :=
    ⟨v, Dv, α, hv, GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ π _ (autIso_symm (rep_iso π)) v w hv Dv Dv α hα⟩
  unfold satOf
  rw [dite_eq_left hex]
  have key : ∀ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' → NG.SatAt (clsA π).rep Dv' α' → NG.SatAt π Dv α' := by
    intro v' Dv' α' hv' hs'
    have e := overPl_unique hv hv'
    subst e
    exact GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ _ π (rep_iso π) v w hv _ Dv _ hs'
  obtain ⟨hv', hs'⟩ := hex.choose_spec.choose_spec.choose_spec
  exact ⟨_, key _ _ _ hv' hs', rfl⟩

theorem f_wt (π : NG.AutRep D.host.E D.R.nV) (a : NG.AlgWt D.host.E D.R.nV) (hd : π.toAlgWt.IsDual a) :
    wtOf D (clsA π).rep = clsW a := by
  have hπ : (clsA π).rep.toAlgWt.Iso π.toAlgWt := (rep_iso π).1
  obtain ⟨b, hb, hbu, hba⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ π.toAlgWt
  have hrb : (clsA π).rep.toAlgWt.IsDual b := (hba _ hπ.symm).1
  have hex : ∃ b, (clsA π).rep.toAlgWt.IsDual b := ⟨b, hrb⟩
  unfold wtOf
  rw [dite_eq_left hex]
  obtain ⟨b', -, hbu', -⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ (clsA π).rep.toAlgWt
  have h1 : b'.Iso hex.choose := (hbu' _).1 hex.choose_spec
  have h2 : b'.Iso b := (hbu' _).1 hrb
  have h3 : b.Iso a := (hbu a).1 hd
  exact (clsW_eq_iff _ _).2 ((h1.symm.trans h2).trans h3)

theorem f_infW (a : NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ) (hl : a.HWAt τ lam) :
    NG.infOf (hwOf (clsW a).rep τ) = NG.infOf lam := by
  have hi : a.Iso (clsW a).rep := (repW_iso a).symm
  obtain ⟨b0, hb0, hb0', hhw⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ a
  have hr : (clsW a).rep.HWAt τ lam := ((hhw _ hi).2 τ lam hl)
  obtain ⟨huniq, hanti⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ (clsW a).rep τ
  have hex : ∃ lam, (clsW a).rep.HWAt τ lam ∧ Antitone lam := ⟨lam, hr, hanti lam hr⟩
  unfold hwOf
  rw [dite_eq_left hex, huniq.unique hex.choose_spec.1 hr]

end

end GlobalTheory.AutQuot
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCoset_moves_with_frameChange : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | exact GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.invActs_cqOf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCosetsInFrames_eq_iff_reductions : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (r r' : PtAt R sel mu cst u j), cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r = GlobalTheory.Mem.Col2.ChEx.cqOf r' := by
  exact @GlobalTheory.Mem.Col2.ChEx.cosetIn_eq_iff_bar_cq
end
