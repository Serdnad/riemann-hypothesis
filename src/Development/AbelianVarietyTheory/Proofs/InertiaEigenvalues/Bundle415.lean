module

import Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.Domain
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Mathlib.RingTheory.Flat.TorsionFree
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.WittTensorFixed

theorem tensor_flat {R W T : Type} [CommRing R] [CommRing W] [Algebra R W] [AddCommGroup T]
    [Module R T] [Module.Flat R T] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : W ⊗[R] T, ∃ b, TensorProduct.map f.toLinearMap LinearMap.id b - b = y) ∧
    (∀ b : W ⊗[R] T, TensorProduct.map f.toLinearMap LinearMap.id b = b ↔
      ∃ t : T, b = (1 : W) ⊗ₜ[R] t) ∧
    Function.Injective (fun t : T => (1 : W) ⊗ₜ[R] t) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : W ⊗[R] T,
      TensorProduct.map f.toLinearMap LinearMap.id b - b = g.rTensor T b := by
    intro b
    simp only [g, LinearMap.rTensor_sub, LinearMap.rTensor_id, LinearMap.sub_apply,
      LinearMap.id_apply]
    rfl
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := rTensor_exact T hex gsurj
  have emb : ∀ t : T, (1 : W) ⊗ₜ[R] t = i.rTensor T ((1 : R) ⊗ₜ[R] t) := by
    intro t
    simp [i]
  have hrange : ∀ x : R ⊗[R] T, i.rTensor T x = (1 : W) ⊗ₜ[R] TensorProduct.lid R T x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r t =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, i, Algebra.linearMap_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, TensorProduct.tmul_add]
  refine ⟨fun y => ?_, fun b => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.rTensor_surjective T gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have hiff : TensorProduct.map f.toLinearMap LinearMap.id b = b ↔ g.rTensor T b = 0 := by
      rw [← key, sub_eq_zero]
    rw [hiff, hexT]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨TensorProduct.lid R T x, hrange x⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(1 : R) ⊗ₜ t, (emb t).symm⟩
  · have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
    intro t t' h
    have h' : i.rTensor T ((1 : R) ⊗ₜ[R] t) = i.rTensor T ((1 : R) ⊗ₜ[R] t') := by
      rw [← emb, ← emb]
      exact h
    simpa using congrArg (TensorProduct.lid R T) (hinj h')

theorem baseChange_flat {R W O : Type} [CommRing R] [CommRing W] [Algebra R W] [CommRing O]
    [Algebra R O] [Module.Flat R O] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : O ⊗[R] W, ∃ b, Algebra.TensorProduct.map (AlgHom.id O O) f b - b = y) ∧
    (∀ b : O ⊗[R] W, Algebra.TensorProduct.map (AlgHom.id O O) f b = b →
      ∃ z, b = algebraMap O (O ⊗[R] W) z) ∧
    Function.Injective (algebraMap O (O ⊗[R] W)) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : O ⊗[R] W,
      Algebra.TensorProduct.map (AlgHom.id O O) f b - b = g.lTensor O b := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul o w => simp [g, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), ← hx, ← hy]; abel
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := lTensor_exact O hex gsurj
  have emb : ∀ z : O, algebraMap O (O ⊗[R] W) z = i.lTensor O (z ⊗ₜ[R] (1 : R)) := by
    intro z
    simp [i]
  have hrange : ∀ x : O ⊗[R] R,
      i.lTensor O x = algebraMap O (O ⊗[R] W) (TensorProduct.rid R O x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, i, Algebra.linearMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, ← TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  refine ⟨fun y => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.lTensor_surjective O gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have h0 : g.lTensor O b = 0 := by rw [← key, hb, sub_self]
    obtain ⟨x, rfl⟩ := (hexT b).mp h0
    exact ⟨TensorProduct.rid R O x, hrange x⟩
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := O) i hi
    intro z z' h
    rw [emb, emb] at h
    simpa using congrArg (TensorProduct.rid R O) (hinj h)

theorem algebraMap_WCb_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  apply Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.zl_WCb_injective <;> assumption

theorem flat_lattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) :
    Module.Flat O ↥T.L.T := by

  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  have hax' : a • x = 0 := hax
  rw [Submodule.mem_bot]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hLL : algebraMap O LL a ≠ 0 := fun h => ha0 (hO (by rw [h, map_zero]))
  have hx0 : (algebraMap O LL a) • (x : T.V) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, hax']
    rfl
  exact Subtype.ext ((smul_eq_zero.mp hx0).resolve_left hLL)

theorem lattice_fixed {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap O R z)
    (hi : Function.Injective (algebraMap O R)) :
    (∀ y : TW R T, ∃ b, TWmap f T b - b = y) ∧
    (∀ b : TW R T, TWmap f T b = b ↔ ∃ t : ↥T.L.T, b = (1 : R) ⊗ₜ[O] t) ∧
    Function.Injective (fun t : ↥T.L.T => (1 : R) ⊗ₜ[O] t) := by
  haveI := flat_lattice hO T
  unfold TW TWmap
  exact tensor_flat f hs hk hi

theorem ring_fixed (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ y : RW LL, ∃ b, φRW LL b - b = y) ∧
    (∀ b : RW LL, φRW LL b = b → ∃ z, b = algebraMap ↥(OL LL) (RW LL) z) ∧
    Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  obtain ⟨_, -, -, -, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  unfold RW φRW
  exact baseChange_flat (frobW l) hs hk (algebraMap_WCb_injective l)



theorem main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ y : TW (RW LL) T, ∃ b, TWmap (φRW LL) T b - b = y) ∧ (∀ b : TW (RW LL) T, TWmap (φRW LL) T b = b ↔ ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  intro l _ K LL T
  obtain ⟨hdvr, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := fun a b h => Subtype.ext h
  obtain ⟨hs, hk, hi⟩ := ring_fixed l LL
  exact lattice_fixed hO T (φRW LL) hs hk hi

end GlobalTheory.WittTensorFixed
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open scoped ENNReal

noncomputable section

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

theorem toReal_enat (a : ℕ∞) : ((a : ℝ≥0∞)).toReal = (a.toNat : ℝ) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n => simp

theorem nlen_toReal (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] :
    (BaseSizes.nlen O l M).toReal = (lenUnit (O := O) l M : ℝ) := by
  unfold BaseSizes.nlen lenUnit
  rw [ENNReal.toReal_div, toReal_enat, toReal_enat]
  push_cast
  rfl

theorem nlen_ne_top {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (hl : Module.length O (O ⧸ Ideal.span {(l : O)}) ≠ 0) :
    BaseSizes.nlen O l M ≠ ⊤ := by
  unfold BaseSizes.nlen
  exact ENNReal.div_ne_top (by simpa using hM) (by simpa using hl)

theorem param_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) : BaseSizes.param D i ρ = JumpDictionary.PP D i ρ := by
  have hI : Finset.Icc 1 D.R.t = (Finset.range D.R.t).map (addRightEmbedding 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨c - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  unfold BaseSizes.param JumpDictionary.PP JumpDictionary.param JumpDictionary.run
  congr 1
  rw [hI, Finset.map_val, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, addRightEmbedding_apply]
  push_cast
  rfl

theorem embSide_false (D : D7) (ρ : D.what₂.Tau) : BaseSizes.embSide D ρ false = JumpDictionary.embOver D ρ true := by
  ext x
  simp [BaseSizes.embSide, JumpDictionary.embOver, ComplexEmbedding.conjugate_coe_eq, WeightFamilies.emb_conj]

theorem weightTie_of (D : D7) (h : JumpDictionary.WeightParam D) (i : D.nd.Loc) : BaseSizes.WeightTie D i := by
  refine ⟨true, fun ρ => ⟨-1 / 2, ?_, ?_⟩⟩
  · rw [show BaseSizes.embSide D ρ true = JumpDictionary.embOver D ρ false from rfl, (h i ρ).1, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring
  · rw [show BaseSizes.embSide D ρ (!true) = JumpDictionary.embOver D ρ true from embSide_false D ρ, (h i ρ).2, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring

theorem isRankRPart_of (D : D7) (i : D.nd.Loc) (r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ₀ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (h : BlockRepresentationsSemisimple.IsComplement D.nd i r₀ ρ₀) :
    BaseSizes.IsRankRPart D i r₀ ρ₀ := by
  obtain ⟨e, he⟩ := h.rho
  refine ⟨h.cont, e, fun g u => ?_⟩
  have := he g u
  rw [BlockRepresentationsSemisimple.blockRep_apply] at this
  exact this

end GlobalTheory.NLink.RowE

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

theorem main : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  intro D L r ρ exc hCB hW hP hK hS h3 hexc i hTw hl hg hx π hπ
  have hg' := (D.Zgood_tie i π).1 hπ
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 hg'.1
  have hHG : HG D.nd D.naut i := ⟨π, hg'⟩
  have hk : ∀ k, D.nd.l i ≠ D.host.g k := by
    intro k hk
    apply hg
    rw [hk]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have hExc : D.nd.l i ∉ BaseSizes.Exc L := by
    rw [← hexc]
    exact_mod_cast hx
  have hB := hCB i hl hk hExc (GlobalTheory.NLink.RowE.weightTie_of D hW i) hHG (r i) (hP.good i) π hZ (ρ i π)
    (GlobalTheory.NLink.RowE.isRankRPart_of D i _ _ (hP.compl i π hZ))
  obtain ⟨hK1, hK2⟩ := hK i hTw
  have hram := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i

  have hsP : BaseSizes.sPi D i π (ρ i π) ≠ ⊤ := GlobalTheory.NLink.RowE.nlen_ne_top _ _ (hK1 π hπ).1.ne hram.1
  have hsR : (BaseSizes.sPi D i π (ρ i π)).toReal = (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) :=
    GlobalTheory.NLink.RowE.nlen_toReal _ _ _

  have hodd : Odd (D.nd.l i) := by
    refine (D.nd.lPrime i).out.odd_of_ne_two fun h2 => ?_
    have h4 : (3 : ℝ) < (D.nd.l i : ℝ) := lt_of_le_of_lt h3 hl
    rw [h2] at h4
    norm_num at h4
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) ≠ ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact @hS (D.nd.l i) (D.nd.lPrime i) e he.1 he.2
  have hshaF : BaseSizes.shaSum D i ≠ ⊤ := by
    unfold BaseSizes.shaSum
    exact ENNReal.sum_ne_top.2 fun e he => by simpa using hsha e he
  have hshaR : (BaseSizes.shaSum D i).toReal = TwistedPlaces.VVr D (D.nd.l i) := by
    unfold BaseSizes.shaSum TwistedPlaces.VVr
    rw [ENNReal.toReal_sum (fun e he => by simpa using hsha e he)]
    rw [show D.what₂.VV (D.nd.l i) = ∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e from rfl,
      show Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t by ext; simp; omega]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_Ioo.1 he
    rw [GlobalTheory.NLink.RowE.toReal_enat, D.nd.sha_eq (D.nd.l i) e he'.1 he'.2 _ (ENat.coe_toNat (hsha e he)).symm]
    push_cast
    rfl

  have hvC : BaseSizes.vClass D i ≠ ⊤ := by
    unfold BaseSizes.vClass
    simp
  have hvCR : (BaseSizes.vClass D i).toReal = TwistedPlaces.vhE D (D.nd.l i) := by
    unfold BaseSizes.vClass TwistedPlaces.vhE hE
    simp

  have hzeta : ∀ P ∈ D.nd.Q i, BaseSizes.zetaP D i P - 1 ≠ 0 := by
    intro P hP
    rw [BaseSizes.zetaP_eq D i P hP, sub_ne_zero]
    exact ((GlobalTheory.TameDesign.main D i).2 P (Or.inr hP)).2.2.1 hP
  have hvO : ∀ P ∈ D.nd.Q i, BaseSizes.vO (D.nd.O i) (D.nd.l i) (BaseSizes.zetaP D i P - 1) ≠ ⊤ := by
    intro P hP
    refine GlobalTheory.NLink.RowE.nlen_ne_top _ _ ?_ hram.1
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (hzeta P hP))
  have hepsF : BaseSizes.epsQ D i ≠ ⊤ := by
    unfold BaseSizes.epsQ
    exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 hvO)
  have hepsR : (BaseSizes.epsQ D i).toReal ≤ TwistedPlaces.epsL (D.nd.l i) := by
    refine Eq.trans_le ?_ hK2
    unfold BaseSizes.epsQ
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum hvO]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    unfold BaseSizes.vO
    rw [GlobalTheory.NLink.RowE.nlen_toReal, BaseSizes.zetaP_eq D i P hP]

  have hvcc : (BaseSizes.vCC D i π).toReal = (D.nd.vcc i π : ℝ) := by
    rw [GlobalTheory.Proof.QuotientLengthInfimum.vCC_eq]
    exact GlobalTheory.NLink.RowE.nlen_toReal _ _ _
  have hmono := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩, hepsF⟩) hB
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩) hepsF,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩) hvC, ENNReal.toReal_add hsP hshaF,
    hvcc, hsR, hshaR, hvCR] at hmono
  unfold Bd
  linarith

end GlobalTheory.NLink.RowE

end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  first | exact @GlobalTheory.ZetaDenominator.zetaBound | exact GlobalTheory.ZetaDenominator.zetaBound | (intros; apply GlobalTheory.ZetaDenominator.zetaBound <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem normV_zpow_deg_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (σ' : Weil h') (σ : Weil h) (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v' : ℕ) : ℝ) ^ deg σ' = ((normV v : ℕ) : ℝ) ^ deg σ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, ha⟩ := σ'.2
  obtain ⟨c, d, hc⟩ := σ.2
  rw [deg_eq ha, deg_eq hc]
  set q' := normV v' with hq'
  set q := normV v with hq
  have hq'0 : 0 < q' := (zero_lt_one.trans (one_lt_normV v'))
  have hq0 : 0 < q := (zero_lt_one.trans (one_lt_normV v))
  have key : ∀ x : Ω, A.valuation x ≤ 1 →
      A.valuation (x ^ (q' ^ a * q ^ d) - x ^ (q ^ c * q' ^ b)) < 1 := by
    intro x hx
    have hy : A.valuation ((σ' : G L Ω) x) ≤ 1 := val_apply_le_one ha.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (ha.2 x hx) (q ^ d)
    have h2' := hc.2 x hx
    rw [hσ] at h2'
    have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2' (q' ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h2
    rw [mul_comm (q ^ d) (q' ^ b)] at h2
    exact cong_trans (cong_symm h1) h2
  have hN : q' ^ a * q ^ d = q ^ c * q' ^ b := by
    rcases lt_trichotomy (q' ^ a * q ^ d) (q ^ c * q' ^ b) with hlt | heq | hgt
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq'0 a) (pow_pos hq0 d)) hlt
      exact absurd (cong_symm (key x hx)) hx'
    · exact heq
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq0 c) (pow_pos hq'0 b)) hgt
      exact absurd (key x hx) hx'
  have hR : ((q' : ℕ) : ℝ) ^ a * ((q : ℕ) : ℝ) ^ d = ((q : ℕ) : ℝ) ^ c * ((q' : ℕ) : ℝ) ^ b := by
    exact_mod_cast hN
  have h1 : ((q' : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((q : ℕ) : ℝ) ≠ 0 := by positivity
  rw [zpow_sub₀ h1, zpow_sub₀ h2, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h2)]
  linarith

end GlobalTheory.LocLanglands

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands
end
