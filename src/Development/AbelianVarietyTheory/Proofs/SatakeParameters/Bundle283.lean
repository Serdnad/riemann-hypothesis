module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle261
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.blockCharacter_eq_inv_at_transposeInv_lowerBlockDet : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → ∃ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (d * b * d⁻¹) ∧ ∀ μ : (s.w.adicCompletion L)ˣ →* ℂˣ, IsTame μ → blockChar μ (Matrix.GeneralLinearGroup.map c.toRingHom a) = (((μ (Units.map c.toMonoidHom u))⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD | exact GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD | (intros; apply GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section

open Module

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (L : FinExt l)

def toA : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) ≃ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  (TensorProduct.congr (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1) (LinearEquiv.refl ℚ_[l] (Bst P))).trans
    (TensorProduct.comm ℚ_[l] ↥L.1 (Bst P))

@[simp] theorem toA_tmul (v : Fin 1 → ↥L.1) (b : Bst P) : toA P L (v ⊗ₜ b) = b ⊗ₜ v 0 := rfl

variable {P L}

theorem toA_mulB (y' y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' y) = toA P L y' * toA P L y := by
  induction y' using TensorProduct.inductionOn with
  | tmul v' b' =>
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      rw [GlobalTheory.Pst.TwistLetters.mulB_tmul, toA_tmul, toA_tmul, toA_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    | add x x' hx hx' => simp only [map_add, mul_add, hx, hx']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, add_mul, hy, hy']

theorem toA_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c • toA P L y := by
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    rw [mulV_tmul, toA_tmul, toA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x x' hx hx' => simp only [map_add, smul_add, hx, hx']

theorem toA_stRep {K : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (g : ↥(GK K)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (stRep P ρm g y) =
      Algebra.TensorProduct.map (actSt P (g : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) (toA P L y) *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g) := by
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    rw [stRep_tmul, toA_tmul, toA_tmul, hm, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp [mul_comm]
  | add x x' hx hx' => simp only [map_add, add_mul, hx, hx']

end GlobalTheory.Pst.UnitLetter
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem units_zpow_bilin_comm {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (B : M₁ →ₗ[R] M₂ →ₗ[R] M₃) (u₁ : (Module.End R M₁)ˣ) (u₂ : (Module.End R M₂)ˣ) (u₃ : (Module.End R M₃)ˣ)
    (h : ∀ x y, (u₃ : Module.End R M₃) (B x y) = B ((u₁ : Module.End R M₁) x) ((u₂ : Module.End R M₂) y))
    (n : ℤ) (x : M₁) (y : M₂) :
    ((u₃ ^ n : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁ ^ n : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂ ^ n : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
  have hinv : ∀ x y, ((u₃⁻¹ : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
    intro x y
    have e₁ := LinearMap.congr_fun (Units.mul_inv u₁) x
    have e₂ := LinearMap.congr_fun (Units.mul_inv u₂) y
    rw [Module.End.mul_apply, Module.End.one_apply] at e₁ e₂
    conv_lhs => rw [← e₁, ← e₂, ← h]
    have e₃ := LinearMap.congr_fun (Units.inv_mul u₃) (B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y))
    rw [Module.End.mul_apply, Module.End.one_apply] at e₃
    exact e₃
  induction n using Int.induction_on generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinv, ih]

end GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem phiU_zpow_dmul : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht _ _ _ n x y
  exact units_zpow_bilin_comm (dmul P ρs ρt ρm χ hm ht) (phiU P ρs) (phiU P ρm) (phiU P ρt)
    (fun x y => phiD_dmul P ρs ρt ρm χ hm ht x y) n x y

end GlobalTheory.Pst.TwistLetters
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem loc_mul (Dv : InertDatum L n v w) (x y : GAf L n) : Dv.loc (x * y) = Dv.loc x * Dv.loc y :=
  (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x y

theorem mem_dc_iff (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    (h3 : ∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n →
      ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k)
    (h4 : ∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y)
    {a x : GAf L n} (ha : TrivOutside {v} a) (hx : TrivOutside {v} x) :
    (⟨Dv.loc x, h1 x⟩ : Formalism.UG.GU Dv.σw n) ∈ DoubleCoset.doubleCoset (⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n)
        (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) ↔
      ∃ k₁ ∈ InertSph.Kv L n v, ∃ k₂ ∈ InertSph.Kv L n v, x = k₁ * a * k₂ := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, e⟩
    obtain ⟨κ₁, t₁, e₁⟩ := h3 k₁.1 k₁.2
    obtain ⟨κ₂, t₂, e₂⟩ := h3 k₂.1 k₂.2
    have u₁ : κ₁ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₁ t₁
      (fun i j => by rw [e₁]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₁ i j)
    have u₂ : κ₂ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₂ t₂
      (fun i j => by rw [e₂]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₂ i j)
    refine ⟨κ₁, ⟨u₁, t₁⟩, κ₂, ⟨u₂, t₂⟩, h4 _ _ hx
      (GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul t₁ ha) t₂) ?_⟩
    calc Dv.loc x = k₁.1 * Dv.loc a * k₂.1 := congrArg Subtype.val e
      _ = Dv.loc κ₁ * Dv.loc a * Dv.loc κ₂ := by rw [e₁, e₂]
      _ = Dv.loc (κ₁ * a * κ₂) := by rw [loc_mul, loc_mul]
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ⟨Dv.loc k₂, h1 k₂⟩,
      h2 k₂ hk₂.1 (h1 k₂), ?_⟩
    apply Subtype.ext
    show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
    rw [loc_mul, loc_mul]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem exists_reps (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    {a : GAf L n} (ha : TrivOutside {v} a) :
    ∃ R : Finset (GAf L n), GlobalTheory.SphLabelOps.Reps (InertSph.Kv L n v) a R := by
  classical
  set K := InertSph.Kv L n v
  let p : GAf L n → Prop := fun x => ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂
  have tp : ∀ x, p x → TrivOutside {v} x := by
    rintro _ ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  have hfin : Set.Finite {c : GAf L n ⧸ K | ∃ x : GAf L n, (x : GAf L n ⧸ K) = c ∧ p x} := by
    refine GlobalTheory.SatInd.CosetFin.finite_cosets (GlobalTheory.SatInd.CosetFin.locHom Dv) (Formalism.UG.GU Dv.σw n)
      (Formalism.UG.KU Dv.σw n) K p _
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram ⟨Dv.loc a, h1 a⟩) ?_ ?_
    · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨h1 _, ⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ?_⟩
      have e : (⟨GlobalTheory.SatInd.CosetFin.locHom Dv (k₁ * a * k₂), h1 _⟩ : Formalism.UG.GU Dv.σw n) =
          (⟨Dv.loc k₁, h1 k₁⟩ * ⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n) * ⟨Dv.loc k₂, h1 k₂⟩ := by
        apply Subtype.ext
        show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
        rw [loc_mul, loc_mul]
      rw [e]
      exact (QuotientGroup.mk_mul_of_mem _ (h2 k₂ hk₂.1 (h1 k₂))).symm
    · intro x y hx hy hz hk
      have ht : TrivOutside {v} (x⁻¹ * y) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tp x hx)) (tp y hy)
      exact ⟨GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht
        (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j), ht⟩
  refine ⟨hfin.toFinset.image (fun c => c.out), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨x, hxc, k₁, hk₁, k₂, hk₂, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hc
    have hm : (k₁ * a * k₂)⁻¹ * c.out ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', hxc]
    exact ⟨k₁, hk₁, k₂ * ((k₁ * a * k₂)⁻¹ * c.out), mul_mem hk₂ hm, by group⟩
  · intro x hx
    have hc : (x : GAf L n ⧸ K) ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 ⟨x, rfl, hx⟩
    refine ⟨(x : GAf L n ⧸ K).out, ⟨Finset.mem_image_of_mem _ hc, ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    · rintro γ ⟨hγ, hγx⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hγ
      have : c = (x : GAf L n ⧸ K) := by
        rw [← QuotientGroup.out_eq' c]
        exact QuotientGroup.eq.2 hγx
      rw [this]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

theorem dcOp_eq_heckeFunI : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n) → (∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → (∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k) → (∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y) → ∀ a : GAf L n, TrivOutside {v} a → ∃ (R : Finset (GAf L n)) (ha : Formalism.UG.GU Dv.σw n → ℂ), GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R ∧ ha ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W), (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv ha φ := by
  intro L _ _ _ n v w Dv h1 h2 h3 h4 a ha
  classical
  set K := InertSph.Kv L n v
  obtain ⟨R, hR⟩ := exists_reps Dv h1 h2 ha
  have tR : ∀ γ ∈ R, TrivOutside {v} γ := by
    intro γ hγ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 γ hγ
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  refine ⟨R, Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩, hR,
    Formalism.UG.P.double_coset_indicator_mem _ _ _ _, fun W _ _ φ hφ => ?_⟩

  have hv1 : ∀ x : GAf L n, TrivOutside {v} x → (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂) →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) = 1 := by
    intro x hx hp
    unfold Formalism.AUTREP.InertDatum.hval
    rw [dite_eq_left (h1 x)]
    exact Formalism.UG.P.dosetInd_of_mem ℂ _ _ _ ((mem_dc_iff Dv h1 h2 h3 h4 ha hx).2 hp)
  have hv0 : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) ≠ 0 →
      ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂ := by
    intro x hx h0
    unfold Formalism.AUTREP.InertDatum.hval at h0
    rw [dite_eq_left (h1 x)] at h0
    refine (mem_dc_iff Dv h1 h2 h3 h4 ha hx).1 ?_
    by_contra hn
    exact h0 (Formalism.UG.P.dosetInd_of_not_mem ℂ _ _ _ hn)
  funext g
  rw [Finset.sum_apply]
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientGroup.mk : GAf L n → GAf L n ⧸ Umax L n))]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun γ hγ => ?_
      have hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = (γ : GAf L n ⧸ Umax L n) ∧ TrivOutside {v} x :=
        ⟨γ, rfl, tR γ hγ⟩
      rw [dite_eq_left hc]
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have hU : γ⁻¹ * hc.choose ∈ Umax L n := QuotientGroup.eq.1 e.symm
      have hT : TrivOutside {v} (γ⁻¹ * hc.choose) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) hxt
      have hp : ∃ k₁ ∈ K, ∃ k₂ ∈ K, hc.choose = k₁ * a * k₂ := by
        obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := hR.1 γ hγ
        exact ⟨k₁, hk₁, k₂ * (γ⁻¹ * hc.choose), mul_mem hk₂ ⟨hU, hT⟩, by rw [← mul_assoc, ← e']; group⟩
      rw [hv1 _ hxt hp, one_smul]
      have := congrFun (hφ _ hU hT) (g * γ)
      show φ (g * γ) = φ (g * hc.choose)
      rw [← this]
      show φ (g * γ * (γ⁻¹ * hc.choose)) = φ (g * hc.choose)
      group
    · intro γ hγ γ' hγ' e
      have hU : γ⁻¹ * γ' ∈ Umax L n := QuotientGroup.eq.1 e
      have hT : TrivOutside {v} (γ⁻¹ * γ') :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) (tR γ' hγ')
      exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hU, hT⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = c ∧ TrivOutside {v} x
    · rw [dite_eq_left hc] at hc0
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have h0 : Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc hc.choose) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc0; exact hc0 rfl
      obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := hR.2 _ (hv0 _ hxt h0)
      rw [Finset.coe_image]
      refine ⟨γ, hγ, ?_⟩
      show (γ : GAf L n ⧸ Umax L n) = c
      rw [← e]
      exact QuotientGroup.eq.2 hγx.1
    · exact absurd (dif_neg hc) hc0

end GlobalTheory.InertDCOp
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


noncomputable section

namespace GlobalTheory.SmGL.Relabel

section General

variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

def indPull {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : H →* G) (hφ : Continuous φ)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ q ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (φ g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      show f.1.1 (φ (q * g)) = τ q (f.1.1 (φ g))
      rw [map_mul, ← hp, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (IsOpen.preimage hφ f.2) (by simp)) fun g hg => by
        have hg' : ind P σ (φ g) f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (φ x)
        show f.1.1 (φ (x * g)) = f.1.1 (φ x)
        rw [map_mul]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smInd_equiv_comp {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : G →* H) (φ' : H →* G)
    (hφ : Continuous φ) (hφ' : Continuous φ') (h1 : ∀ x, φ (φ' x) = x) (h2 : ∀ x, φ' (φ x) = x)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ' q ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : H) = φ p ∧ τ q = σ p) :
    Nonempty ((smInd P σ).Equiv ((smInd Q τ).comp φ)) := by
  refine ⟨.mk (LinearEquiv.ofLinear (indPull φ' hφ' h) (indPull φ hφ h') ?_ ?_) fun g => ?_⟩
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ (φ' x)) = f.1.1 x
    rw [h1]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' (φ x)) = f.1.1 x
    rw [h2]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' x * g) = f.1.1 (φ' (x * φ g))
    rw [map_mul, h2]

end General

section Blocks

open GlobalTheory.EmptyFirstBlock

variable {R : Type} [CommRing R] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem continuous_reindexGL [TopologicalSpace R] (ψ : n ≃ n') :
    Continuous (reindexGL (R := R) ψ) :=
  Continuous.units_map _ (continuous_pi fun i => continuous_pi fun j =>
    continuous_apply_apply (ψ.symm i) (ψ.symm j))

theorem reindexGL_symm_reindexGL (ψ : n ≃ n') (g : GL n R) :
    reindexGL ψ.symm (reindexGL ψ g) = g :=
  Units.ext (Matrix.ext fun i j => by simp [val_reindexGL])

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem exists_parab_reindexGL {e : (Σ a, m a) ≃ n} {e' : (Σ a, m a) ≃ n'} (ψ : n ≃ n')
    (h : ∀ x, ψ.symm (e' x) = e x) (p : parab R e) :
    ∃ q : parab R e', (q : GL n' R) = reindexGL ψ p ∧ leviProj R e' q = leviProj R e p := by
  refine ⟨⟨reindexGL ψ p, mem_parab_iff.2 fun a b i j hab => ?_⟩, rfl, ?_⟩
  · rw [val_reindexGL, h, h]
    exact mem_parab_iff.1 p.2 a b i j hab
  · funext a
    ext i j
    show (reindexGL ψ (p : GL n R) : Matrix n' n' R) (e' ⟨a, i⟩) (e' ⟨a, j⟩) =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩)
    rw [val_reindexGL, h, h]

end Blocks

theorem parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  intro k _ _ _ _ α _ _ m _ _ n n' _ _ _ _ e ψ W _ _ ρ
  refine smInd_equiv_comp _ (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ.symm)
    (continuous_reindexGL ψ) (continuous_reindexGL ψ.symm)
    (reindexGL_symm_reindexGL ψ.symm) (reindexGL_symm_reindexGL ψ) (fun q => ?_) (fun p => ?_)
  · obtain ⟨p, hp, hl⟩ := exists_parab_reindexGL (e' := e) ψ.symm (fun x => rfl) q
    exact ⟨p, hp, congrArg (twist ρ (deltaHalf k m)) hl⟩
  · obtain ⟨q, hq, hl⟩ := exists_parab_reindexGL (e' := e.trans ψ) ψ (fun x => by simp) p
    exact ⟨q, hq, congrArg (twist ρ (deltaHalf k m)) hl⟩

end GlobalTheory.SmGL.Relabel
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.level_quotient_eq_twisted_top : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  first | exact @GlobalTheory.TopLevQ.levQTop_eq_twTt | exact GlobalTheory.TopLevQ.levQTop_eq_twTt | (intros; apply GlobalTheory.TopLevQ.levQTop_eq_twTt <;> assumption)
end
