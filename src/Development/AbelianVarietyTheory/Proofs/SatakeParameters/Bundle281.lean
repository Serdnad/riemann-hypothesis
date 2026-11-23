module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle157
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle243
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle004
public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle259
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle264
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.irreducible_subquotient_eigenvector : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V), x ≠ 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧ ∀ (g : G) (c : ℂ), ρ g x = c • x → τ g y = c • y := by
  first | exact @GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero | exact GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero | (intros; apply GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.isSubquotient_of_exact_middle_irreducible : ∀ (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q] (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A) (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ), τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ → IsSubquotient τ α ∨ IsSubquotient τ κ := by
  first | exact @GlobalTheory.isSubquotient_of_exact_middle | exact GlobalTheory.isSubquotient_of_exact_middle | (intros; apply GlobalTheory.isSubquotient_of_exact_middle <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.piExteriorTensor_isSubquotient_of_forall : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := by
  first | exact @GlobalTheory.piTensor_isSubquotient_of_forall | exact GlobalTheory.piTensor_isSubquotient_of_forall | (intros; apply GlobalTheory.piTensor_isSubquotient_of_forall <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitPlace_unitsCharacter_eq_of_agree_on_field : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, ξ u = μ (Units.map c.toMonoidHom u) := by
  first | exact @GlobalTheory.ConjDense.eq_of_agree | exact GlobalTheory.ConjDense.eq_of_agree | (intros; apply GlobalTheory.ConjDense.eq_of_agree <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.blocks_lt_of_parabolicUnipotentRadical_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  first | exact @GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot | exact GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot | (intros; apply GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS s Ds hDt hDs R hRD hRu
  exact GlobalTheory.BiInvScalar.biInv_scalar L n W ρ S hS s Ds hDt hDs R hRD hRu
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), IsConjPl D.host w s.w → (GlobalTheory.TypeTame.conjSP s).w = w ∧ ∀ x : D.host.E, (GlobalTheory.TypeTame.conjSP s).i x = s.i (D.host.conj x) := by
  first | exact @GlobalTheory.TypeTame.conjSP_w_of_isConjPl | exact GlobalTheory.TypeTame.conjSP_w_of_isConjPl | (intros; apply GlobalTheory.TypeTame.conjSP_w_of_isConjPl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

abbrev sz (r t : ℕ) : Fin 2 → ℕ := ![r, t]

theorem sum_sz (r t : ℕ) : ∑ a, sz r t a = r + t := by simp [sz]

def blocks2 (r t : ℕ) : (Σ a : Fin 2, Fin (sz r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sz r t)

theorem blocks2_zero (r t : ℕ) (i : Fin r) : blocks2 r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 0 i).trans ?_
  simp

theorem blocks2_one (r t : ℕ) (j : Fin t) : blocks2 r t ⟨1, j⟩ = Fin.natAdd r j := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 1 j).trans ?_
  simp [sz]

theorem twoE_false (r t : ℕ) (i : Fin r) : two (stdSum (rfl : r + t = r + t)) ⟨false, i⟩ = Fin.castAdd t i := by
  ext; simp

theorem twoE_true (r t : ℕ) (j : Fin t) : two (stdSum (rfl : r + t = r + t)) ⟨true, j⟩ = Fin.natAdd r j := by
  ext; simp

end GlobalTheory.JacBlockTwo

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inl' (r t : ℕ) (i : Fin r) : stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i := by
  ext; simp

theorem stdSum_inr' (r t : ℕ) (j : Fin t) : stdSum (rfl : r + t = r + t) (Sum.inr j) = Fin.natAdd r j := by
  ext; simp

def IsUpperUnip {r t : ℕ} (g : GL (Fin (r + t)) k) : Prop :=
  (∀ (i : Fin t) (j : Fin r), (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.castAdd t j) = 0) ∧
  (∀ i j : Fin r, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.castAdd t i) (Fin.castAdd t j) =
    (1 : Matrix (Fin r) (Fin r) k) i j) ∧
  (∀ i j : Fin t, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.natAdd r j) =
    (1 : Matrix (Fin t) (Fin t) k) i j)

theorem mem_unipRad_two {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (two (stdSum (rfl : r + t = r + t))) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_two]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← stdSum_inl', ← stdSum_inr']; exact h0 i j
    · rw [← twoE_false, ← twoE_false]; exact hD false i j
    · rw [← twoE_true, ← twoE_true]; exact hD true i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j i => ?_, ?_⟩
    · have := h0 j i; rwa [← stdSum_inl', ← stdSum_inr'] at this
    · rintro (_ | _) i j
      · have := h1 i j; rwa [← twoE_false, ← twoE_false] at this
      · have := h2 i j; rwa [← twoE_true, ← twoE_true] at this

theorem mem_unipRad_blocks2 {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (blocks2 r t) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← blocks2_one, ← blocks2_zero]; exact h0 1 0 i j (by decide)
    · rw [← blocks2_zero, ← blocks2_zero]; exact hD 0 i j
    · rw [← blocks2_one, ← blocks2_one]; exact hD 1 i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · match a, b with
      | 0, 0 => intro i j hab; exact absurd hab (lt_irrefl _)
      | 0, 1 => intro i j hab; exact absurd hab (by decide)
      | 1, 0 => intro i j _; rw [blocks2_one r t i, blocks2_zero r t j]; exact h0 i j
      | 1, 1 => intro i j hab; exact absurd hab (lt_irrefl _)
    · match a with
      | 0 => intro i j; rw [blocks2_zero r t i, blocks2_zero r t j]; exact h1 i j
      | 1 => intro i j; rw [blocks2_one r t i, blocks2_one r t j]; exact h2 i j

theorem unipRad_blocks2 (r t : ℕ) :
    unipRad k (blocks2 r t) = unipRad k (two (stdSum (rfl : r + t = r + t))) := by
  ext g; rw [mem_unipRad_blocks2, mem_unipRad_two]

theorem unipRad_two_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (two (stdSum (rfl : r + t = r + t))) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨h0, h1, h2⟩ := mem_unipRad_two.1 hh.1
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by ext i j; exact h2 i j
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply]) 1
    (by rw [hsub, det_one, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

theorem mulSingle_mem_KO {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) (a : Bool) :
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) a ∈ KO k (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _
  · rw [Pi.mulSingle_eq_same]; exact hg

theorem deltaHalf_mulSingle {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    deltaHalf k (Two (Fin r) (Fin t)) (Pi.mulSingle true g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_mem_KO (r := r) hg a)

theorem act_mulSingle {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    π (leviEmb k (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle true g)) v =
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (two (stdSum (rfl : r + t = r + t)))
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_mem_KO hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_mem_KO hg a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [← twoE_true, ← twoE_false]
    exact leviEmb_apply_ne k _ _ (by decide) _ _
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Matrix (Fin r) (Fin r) k) i j :=
    fun i j => by
      rw [← twoE_false, ← twoE_false, hdef, leviEmb_apply_same, Pi.mulSingle_eq_of_ne (by decide)]
      rfl
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = g.val := by
    ext i j
    rw [Matrix.submatrix_apply, ← twoE_true, ← twoE_true, hdef, leviEmb_apply_same, Pi.mulSingle_eq_same]
  exact hv h hKO (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply])
    (Matrix.GeneralLinearGroup.det g) (by rw [hsub, Matrix.GeneralLinearGroup.val_det_apply])

theorem jacquet_ne_zero_of_isBlockVec_two : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), _root_.GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  intro hP k _ _ _ _ r t χ V _ _ π v hsm hirr hχ hv0 hv
  refine ⟨?_, ?_⟩
  · intro hx
    apply hv0
    have hx' : (Submodule.Quotient.mk v : Jacquet π (unipRad k (blocks2 r t))) = 0 := by
      rw [unipRad_blocks2]; exact hx
    refine hP k (r + t) 2 (sz r t) (blocks2 r t) ⟨V, π, hsm, hirr⟩ v ?_ hx'
    rw [unipRad_blocks2]
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_two_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro g hg
    rw [jac_mk, deltaHalf_mulSingle hg, act_mulSingle hv hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlockTwo

end
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tame_block_vector_jacquet_nonzero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  first | exact @GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec | exact GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec | (intros; apply GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong

theorem linearIndependent_simulEigen {J V : Type} [AddCommGroup V] [Module ℂ V] (T : J → V →ₗ[ℂ] V)
    (S : Set (J → ℂ)) (v : S → V) (hv : ∀ χ, v χ ≠ 0)
    (hT : ∀ (χ : S) j, T j (v χ) = (χ : J → ℂ) j • v χ) : LinearIndependent ℂ v := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)

def opLin {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) :
    V →ₗ[ℂ] V :=
  f.sum fun g c => c • ρ g

theorem opLin_apply {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ)
    (v : V) : opLin ρ f v = opOf ρ f v := by
  simp [opLin, opOf, Finsupp.sum, LinearMap.sum_apply]

theorem eq_zero_of_finU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (h0 : ∀ g ∈ finU (E := E) (n := n), φ g = 0) : φ = 0 := by
  refine Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_
  rintro x ⟨γ, hγ, g, hg, rfl⟩
  simp only [Pi.zero_apply]
  rw [hφ.left γ hγ g]
  exact h0 g hg

theorem finU_holds : FinU := by
  intro E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  have hφ : IsAutFormU φ := hU.aut.aut φ hφU
  have heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ := fun j => hact U hU.aut φ hφU hφK j
  obtain ⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU (E := E) (n := a), φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (eq_zero_of_finU hφ h)
  choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ
  obtain ⟨M, hMfin, hM⟩ := GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ
  have heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ := fun σ j =>
    GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)
  have hne : ∀ σ, φ' σ ≠ 0 := by
    intro σ h
    have e := hφ'eq σ g₀ hg₀
    rw [h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective] at e
    exact hφg₀ e
  have hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite := by
    set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS
    have hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ) := fun χ => χ.2
    choose sel hsel using hch
    let v : S → (UA E a → ℂ) := fun χ => φ' (sel χ)
    have hli : LinearIndependent ℂ v := by
      refine linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_
      intro χ j
      rw [opLin_apply, heig', ← hsel χ]
    let v' : S → M := fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp M.subtype hli
    have : Finite S := hli'.finite
    exact Set.toFinite S
  obtain ⟨L, hL, hLmem⟩ := GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic l ι J (η U) hfin
  exact ⟨⟨L, hL⟩, hLmem⟩

end GlobalTheory.Cong
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (κ : GAf L n), κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  first | exact @GlobalTheory.InertStdLat.loc_mem_KU | exact GlobalTheory.InertStdLat.loc_mem_KU | (intros; apply GlobalTheory.InertStdLat.loc_mem_KU <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

theorem _root_.GlobalTheory.T.exists_trivOutside_inertLocal_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  first | exact @GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq | exact GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq | (intros; apply GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq <;> assumption)
end
