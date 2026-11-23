module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StrInert

theorem not_isSplitPl_of_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : ¬ IsSplitPl D.host w := by
  rw [GlobalTheory.ConjPlaceOff.isSplitPl_iff]
  rintro ⟨x, hx, hcx⟩
  apply hcx
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin] at hx ⊢
  have key : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal ≤
      (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal).comap
        (Formalism.HermitianLattices.Ext.L3.conjO D.host.E) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : Formalism.HermitianLattices.Ext.L3.conjO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) =
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      apply RingOfIntegers.ext
      rw [Formalism.HermitianLattices.Ext.L3.conjO_coe]
      have : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [this]
      exact Formalism.IndefR.Eqv.star_algebraMapF D _
    rw [e]
    exact Ideal.mem_map_of_mem _ ha
  exact key hx

theorem not_mem_badPl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : GlobalTheory.Hk3.Good R t w)
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) :
    w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  intro h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl, Finset.mem_image, Finset.mem_union] at h
  obtain ⟨PP, hPP, he⟩ := h
  have hne := (hw PP hPP).1
  apply hne
  unfold Formalism.UG.IsInertAt at hin
  have hle : w.asIdeal ≤ PP.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap]
    intro a ha
    have : ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal = PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
    rw [← this, he]
    exact ha
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le PP.isPrime.ne_top hle)).symm

end GlobalTheory.StrInert
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.WeilDeligne

theorem isNilpotent_map_left {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X : Module.End K U} (Y : Module.End K W) (hX : IsNilpotent X) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem isNilpotent_map_right {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (X : Module.End K U) {Y : Module.End K W} (hY : IsNilpotent Y) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hY
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem commute_map {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X X' : Module.End K U} {Y Y' : Module.End K W}
    (hX : Commute X X') (hY : Commute Y Y') :
    Commute (TensorProduct.map X Y) (TensorProduct.map X' Y') := by
  show TensorProduct.map X Y * TensorProduct.map X' Y' = TensorProduct.map X' Y' * TensorProduct.map X Y
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hX.eq, hY.eq]

theorem IsFrobSS.tensor : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {ρ : ↥(Weil h) → Module.End ℂ V} {N : Module.End ℂ V} {a : WDRep h V} {ρ' : ↥(Weil h) → Module.End ℂ V'} {N' : Module.End ℂ V'} {b : WDRep h V'}, IsFrobSS ρ N a → IsFrobSS ρ' N' b → IsFrobSS (fun g => TensorProduct.map (ρ g) (ρ' g)) (N.rTensor V' + N'.lTensor V) (a.tensor b) := by
  intro E Ω _ _ _ _ _ A w h V V' _ _ _ _ _ _ ρ N a ρ' N' b ha hb
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ]
    exact commute_map (ha.2 g).1 (hb.2 g).1
  · rw [WDRep.tensor_ρ]
    have e : TensorProduct.map (ρ g) (ρ' g) - TensorProduct.map (a.ρ g) (b.ρ g) =
        TensorProduct.map (ρ g - a.ρ g) (ρ' g) + TensorProduct.map (a.ρ g) (ρ' g - b.ρ g) :=
      TensorProduct.ext' fun x y => by
        simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    rw [e]
    refine Commute.isNilpotent_add ?_ (isNilpotent_map_left _ (ha.2 g).2)
      (isNilpotent_map_right _ (hb.2 g).2)
    exact commute_map ((ha.2 g).1.symm.sub_left (Commute.refl _))
      ((Commute.refl _).sub_right (hb.2 g).1.symm)

end GlobalTheory.WeilDeligne
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

open Polynomial Module

namespace GlobalTheory.Pst.TwistLetters

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {L : FinExt l}
  (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

def smulEnd : (Fin 1 → ↥L.1) →ₗ[ℚ_[l]] End ℚ_[l] V where
  toFun v' := ((LinearMap.lsmul ↥L.1 V) (v' 0)).restrictScalars ℚ_[l]
  map_add' x y := by ext v; simp [add_smul]
  map_smul' c x := by ext v; simp [smul_assoc]

def mulB : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) →ₗ[ℚ_[l]] End ℚ_[l] (V ⊗[ℚ_[l]] Bst P) :=
  TensorProduct.lift ((TensorProduct.mapBilinear (RingHom.id ℚ_[l]) V (Bst P) V (Bst P)).compl₁₂ (smulEnd V)
    (LinearMap.mul ℚ_[l] (Bst P)))

@[simp] theorem mulB_tmul (v' : Fin 1 → ↥L.1) (b' : Bst P) (v : V) (b : Bst P) :
    mulB (L := L) P V (v' ⊗ₜ b') (v ⊗ₜ b) = (v' 0 • v) ⊗ₜ (b' * b) := by
  simp [mulB, smulEnd]

variable {P V}

theorem mulB_smul (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V y (a • x) = a • mulB (L := L) P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', smul_smul, smul_smul, mul_comm]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_smul_left (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V (a • y) x = a • mulB (L := L) P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', Pi.smul_apply, smul_eq_mul, mul_smul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V y (mulV P ↥L.1 V c x) = mulV P ↥L.1 V c (mulB (L := L) P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_left_comm]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulV_mulB (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) x = mulV P ↥L.1 V c (mulB (L := L) P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_assoc]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem phiV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    phiV P ↥L.1 V (mulB (L := L) P V y x) = mulB (L := L) P V (phiV P ↥L.1 (Fin 1 → ↥L.1) y) (phiV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, phiV_tmul, phiV_tmul, phiV_tmul, mulB_tmul, map_mul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem monV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    monV P ↥L.1 V (mulB (L := L) P V y x) = mulB (L := L) P V (monV P ↥L.1 (Fin 1 → ↥L.1) y) x +
      mulB (L := L) P V y (monV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, monV_tmul, monV_tmul, monV_tmul, mulB_tmul, mulB_tmul, ← TensorProduct.tmul_add]
      congr 1
      simp only [monSt_apply, derivative_mul]
      ring
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

variable {K : FinExt l} (ρs ρt : Representation ↥L.1 ↥(GK K) V)
  (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)

theorem stRep_mulB (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K))
    (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g (mulB (L := L) P V y x) = mulB (L := L) P V (stRep P ρm g y) (stRep P ρs g x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, stRep_tmul, stRep_tmul, stRep_tmul, mulB_tmul, map_mul, ht, hm, map_smul, Pi.smul_apply,
        smul_eq_mul, smul_smul, mul_smul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mem_Dpst (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    {x : V ⊗[ℚ_[l]] Bst P} {y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρs) (hy : y ∈ Dpst P ρm) :
    mulB (L := L) P V y x ∈ Dpst P ρt := by
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρs).mp hx
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρm).mp hy
  refine (mem_Dpst P ρt).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
  rw [stRep_mulB ρs ρt ρm χ hm ht, h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
    h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]

variable (P)

set_option synthInstance.maxHeartbeats 100000 in
def dmul (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) :
    ↥(Dpst P ρs) →ₗ[↥L.1] ↥(Dpst P ρm) →ₗ[↥L.1] ↥(Dpst P ρt) :=
  LinearMap.mk₂ ↥L.1 (fun x y => ⟨mulB (L := L) P V y.1 x.1, mulB_mem_Dpst ρs ρt ρm χ hm ht x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul]))
    (fun x y y' => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul_left]))

variable (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)

@[simp] theorem coe_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    (dmul P ρs ρt ρm χ hm ht x y : V ⊗[ℚ_[l]] Bst P) = mulB (L := L) P V y.1 x.1 := rfl

theorem dmul_mulD_left (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht (mulD P ρs c x) y = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulB_mulV])

theorem dmul_mulD_right (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht x (mulD P ρm c y) = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulV_mulB])

theorem phiD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    phiD P ρt (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (phiD P ρs x) (phiD P ρm y) :=
  Subtype.ext (by simp [phiV_mulB])

theorem monD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    monD P ρt (dmul P ρs ρt ρm χ hm ht x y) =
      dmul P ρs ρt ρm χ hm ht (monD P ρs x) y + dmul P ρs ρt ρm χ hm ht x (monD P ρm y) :=
  Subtype.ext ((monV_mulB y.1 x.1).trans (add_comm _ _))

theorem actD_dmul (g : ↥(GK K)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    actD P ρt g (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (actD P ρs g x) (actD P ρm g y) :=
  Subtype.ext (by simp [stRep_mulB ρs ρt ρm χ hm ht])

end GlobalTheory.Pst.TwistLetters
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Pst.BridgeWD

theorem wdAt_bridge_indep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O O' _ _ _ _ _ _ Bw Bw' hj hj' a r hc hr hr'
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge l P AI hT ι E Ω A w O O' Bw Bw' h hj hj' a r hc hr hr'

end GlobalTheory.Pst.BridgeWD
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  first | exact @GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge | exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge | (intros; apply GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocSplitGraph

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  intro L _ _ _ n a S₁ S₂ s σ₁ σ₂ h₁ h₂ hE
  obtain ⟨E⟩ := hE
  obtain ⟨i₁, T₁, hi₁, hiL₁, hT₁inj, hT₁S, hT₁eq⟩ := h₁
  obtain ⟨i₂, T₂, hi₂, hiL₂, hT₂inj, hT₂S, hT₂eq⟩ := h₂

  have hci : i₁ = i₂ := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (i₁ : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i₂ := by
      refine hd.equalizer hi₁ hi₂ (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hiL₁, hiL₂]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  let F : σ₁.V →ₗ[ℂ] (GAf L n → a.W) × (GAf L n → a.W) := T₁.prod (T₂ ∘ₗ E.toLinearEquiv.toLinearMap)
  have hF : ∀ u, F u = (T₁ u, T₂ (E u)) := fun u => rfl
  have hEint : ∀ g u, E (σ₁.ρ g u) = σ₂.ρ g (E u) := fun g u => LinearMap.congr_fun (E.isIntertwining' g) u
  have hnt : Nontrivial σ₁.V := by
    haveI := σ₁.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ₁.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ₁.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  refine ⟨LinearMap.range F, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_ne (0 : σ₁.V)
    intro h
    have hm : F u ∈ LinearMap.range F := ⟨u, rfl⟩
    rw [h, Submodule.mem_bot, hF, Prod.mk_eq_zero] at hm
    exact hu (hT₁inj (hm.1.trans (map_zero T₁).symm))
  · rintro _ ⟨u, rfl⟩
    exact ⟨hT₁S u, hT₂S (E u)⟩
  · rintro x hx _ ⟨u, rfl⟩
    refine ⟨σ₁.ρ (Matrix.GeneralLinearGroup.map i₁.toRingHom (s.loc n x)) u, ?_⟩
    rw [hF, hF, hT₁eq x hx u, hEint, hT₂eq x hx (E u)]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : v = 0 := hT₁inj (hv.1.trans (map_zero T₁).symm)
    rw [← hv.2, hv0, map_zero, map_zero]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : E v = 0 := hT₂inj (hv.2.trans (map_zero T₂).symm)
    have : v = 0 := by simpa using hv0
    rw [← hv.1, this, map_zero]

end GlobalTheory.LocSplitGraph
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.DeRhamRead
open Formalism.BasicNotions.Loc

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (r : Γ →* GL (Fin a) (Om l)) (hr : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l)))) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

theorem isdRW_iff_isdRAt : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  intro D T W l _ ι w hw O _ _ _ B hj a r hr
  obtain ⟨LL', hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G D.host.E D.nd.Om) a r hr B.LL
  obtain ⟨r₁, c₁, rfl⟩ := exists_model_of_mem r hr LL' hmem
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  exact (H LL' hL a r₁ c₁).2.1.trans (hm.isdRAt_iff (D.loc l)).symm

end GlobalTheory.DeRhamRead
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  first | (exact @GlobalTheory.W1.SchFF.finiteEtale_functionField) | (exact GlobalTheory.W1.SchFF.finiteEtale_functionField) | (intros; apply GlobalTheory.W1.SchFF.finiteEtale_functionField  <;> assumption)
end
