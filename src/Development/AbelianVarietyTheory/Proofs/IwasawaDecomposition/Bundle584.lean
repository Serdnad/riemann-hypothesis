module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlace
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.CompAtUniq

open Topology
open scoped WithZero

theorem ball_mem_nhds' {K : Type} [Field K] [Valued K ℤᵐ⁰] (x r : K) (hr : r ≠ 0) :
    {y | Valued.v (y - x) < Valued.v r} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation K ℤᵐ⁰).restrict r ≠ 0 := by simp [hr]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem val_div_sub_one_lt {K : Type} [Field K] [Valued K ℤᵐ⁰] {u y : K} {c : ℤᵐ⁰} (hu : u ≠ 0)
    (hc : c ≤ 1) (h : Valued.v (y - u) < Valued.v u * c) : y ≠ 0 ∧ Valued.v (u * y⁻¹ - 1) < c := by
  have hvu : Valued.v u ≠ 0 := by simpa using hu
  have hlt : Valued.v (y - u) < Valued.v u := lt_of_lt_of_le h (mul_le_of_le_one_right' hc)
  have hvy : Valued.v y = Valued.v u := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvy; exact hvu hvy.symm
  refine ⟨hy, ?_⟩
  have : u * y⁻¹ - 1 = -((y - u) * y⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hvy]
  have hpos : (0 : ℤᵐ⁰) < Valued.v u := pos_iff_ne_zero.2 hvu
  calc Valued.v (y - u) * (Valued.v u)⁻¹ < Valued.v u * c * (Valued.v u)⁻¹ :=
        mul_lt_mul_of_pos_right h (inv_pos.2 hpos)
    _ = c := by field_simp

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  intro L _ _ _ χ s ξ ξ' hξ hξ'
  obtain ⟨⟨N₁, hN₁⟩, hk⟩ := hξ
  obtain ⟨⟨N₂, hN₂⟩, hk'⟩ := hξ'
  ext1 u
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  have hπ' : Valued.v ((π : s.v.adicCompletion (maximalRealSubfield L))) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  set N := max N₁ N₂ with hN
  have hN1 : N₁ ≤ N := le_max_left _ _
  have hN2 : N₂ ≤ N := le_max_right _ _
  have hu0 : (u : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := u.ne_zero
  have hπ0 : (π : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := by
    intro h; rw [h, map_zero] at hπ'; exact (WithZero.exp_ne_zero) hπ'.symm
  have hvr : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) * (π : s.v.adicCompletion (maximalRealSubfield L)) ^ N)
      = Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) * WithZero.exp (-(N : ℤ)) := by
    rw [map_mul, map_pow, hπ', ← WithZero.exp_nsmul]; congr 2; simp
  have hnhds := ball_mem_nhds' (u : s.v.adicCompletion (maximalRealSubfield L)) _ (mul_ne_zero hu0 (pow_ne_zero N hπ0))
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v).mem_nhds hnhds
  rw [Set.mem_setOf_eq, hvr] at hx
  have hle : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  obtain ⟨hy0, hw⟩ := val_div_sub_one_lt hu0 hle hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  set k : Lˣ := Units.mk0 (algebraMap (maximalRealSubfield L) L x) ((map_ne_zero _).2 hx0) with hkdef
  have hik : ((Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k : _) : s.v.adicCompletion (maximalRealSubfield L))
      = algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x := by
    simp [k]
  set w : (s.v.adicCompletion (maximalRealSubfield L))ˣ := u * (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)⁻¹ with hwdef
  have hu : u = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k * w := by simp [w]
  have hw' : Valued.v ((w : s.v.adicCompletion (maximalRealSubfield L)) - 1) < WithZero.exp (-(N : ℤ)) := by
    have : (w : s.v.adicCompletion (maximalRealSubfield L)) = (u : s.v.adicCompletion (maximalRealSubfield L)) *
        (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x)⁻¹ := by
      rw [hwdef, Units.val_mul, Units.val_inv_eq_inv_val, hik]
    rw [this]; exact hw
  have e1 : ξ w = 1 := hN₁ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  have e2 : ξ' w = 1 := hN₂ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  clear_value w
  rw [hu, map_mul, map_mul, e1, e2, hk, hk']

end GlobalTheory.CompAtUniq

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaUnit

theorem val_det_block {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Fintype ι] [DecidableEq ι]
    (v : Valuation K Γ) (p : ι → Prop) [DecidablePred p] (A B : Matrix ι ι K)
    (hA : ∀ a b, v (A a b) ≤ 1) (hB : ∀ a b, v (B a b) ≤ 1) (hAB : A * B = 1)
    (hlow : ∀ a b, p a → ¬ p b → v (A a b) < 1) :
    v (Matrix.of fun a b : {x // p x} => A a.1 b.1).det = 1 := by
  let O := v.valuationSubring
  let A' : Matrix ι ι O := Matrix.of fun a b => ⟨A a b, hA a b⟩
  let B' : Matrix ι ι O := Matrix.of fun a b => ⟨B a b, hB a b⟩
  have hAB' : A' * B' = 1 := by
    ext a b
    have := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.one_apply] at this ⊢
    rw [AddSubmonoidClass.coe_finsetSum, apply_ite (fun x : O => (x : K))]
    simpa [A', B'] using this
  let f := IsLocalRing.residue O
  have hf : ∀ a b, p a → ¬ p b → f (A' a b) = 0 := by
    intro a b ha hb
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact hlow a b ha hb
  let A₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => A' a.1 b.1
  let B₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => B' a.1 b.1
  have h1 : f.mapMatrix A₁ * f.mapMatrix B₁ = 1 := by
    ext a b
    have h := congrArg f (congrFun (congrFun hAB' a.1) b.1)

    rw [Matrix.mul_apply, map_sum, ← Fintype.sum_subtype_add_sum_subtype p] at h
    rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x}))
      (fun c _ => by rw [map_mul, hf a.1 c.1 a.2 c.2, zero_mul]), add_zero] at h
    rw [Matrix.mul_apply]
    simp only [map_mul] at h
    refine Eq.trans h ?_
    simp only [Matrix.one_apply, Subtype.ext_iff]
    split_ifs <;> simp
  have h2 : f A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : ((A₁.det : O) : K) = (Matrix.of fun a b : {x // p x} => A a.1 b.1).det := by
    have := RingHom.map_det O.subtype A₁
    exact this
  rw [← h3]
  refine le_antisymm A₁.det.2 (not_lt.1 fun hlt => h2 ?_)
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact hlt

theorem detDD_unit_supDiag_int : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  intro L _ _ _ n r s h hp
  have key : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring →
      ∀ a b, Valued.v (g.val a b) ≤ 1 := by
    rintro g ⟨x, rfl⟩ a b
    exact (x.val a b).2
  have hA := key h hp.1
  have hB := key h⁻¹ (inv_mem hp.1)
  refine ⟨?_, ?_⟩
  · exact val_det_block Valued.v (fun x : Fin n => r ≤ x.val) h.val (h⁻¹).val hA hB (by simp)
      (fun a b ha hb => hp.2 a b ha (not_le.1 hb))
  · unfold NG.supDiag
    refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun b _ => ?_
    split_ifs
    · exact hA a b
    · simp

end GlobalTheory.ParaUnit
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.exists_class_trivial_stabiliser_at_typePlace : ∀ (D : D7) (k : Fin 2) (s : SplitPlace D.host.E), s.w ∈ placesOver D.host.E (D.host.g k) → ∃ g : GAf D.host.E D.R.nV, ∀ γ ∈ GQ D.host.E D.R.nV, g⁻¹ * γ * g ∈ Umax D.host.E D.R.nV → NG.UniRT s D.R.r (s.loc _ (g⁻¹ * γ * g)) → γ = 1 := by
  first | exact @GlobalTheory.NeatUni.exists_trivial_stabiliser | exact GlobalTheory.NeatUni.exists_trivial_stabiliser | (intros; apply GlobalTheory.NeatUni.exists_trivial_stabiliser <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ClassForm

theorem double_coset_unique {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {J : Subgroup (GAf L n)} {g : GAf L n}
    (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1)
    {γ γ' : GQ L n} {κ κ' : J} (h : (γ : GAf L n) * g * κ = (γ' : GAf L n) * g * κ') : γ = γ' ∧ κ = κ' := by
  have key : g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by
    calc g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g
        = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ : GAf L n) * g * κ) * (κ : GAf L n)⁻¹ := by group
      _ = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ' : GAf L n) * g * κ') * (κ : GAf L n)⁻¹ := by rw [h]
      _ = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by group
  have hmem : (γ' : GAf L n)⁻¹ * γ ∈ GQ L n := (GQ L n).mul_mem ((GQ L n).inv_mem γ'.2) γ.2
  have h1 := hg _ hmem (key ▸ J.mul_mem κ'.2 (J.inv_mem κ.2))
  have hγ : (γ : GAf L n) = γ' := by
    rw [inv_mul_eq_one] at h1; exact h1.symm
  refine ⟨Subtype.ext hγ, Subtype.ext ?_⟩
  rw [hγ, mul_assoc, mul_assoc] at h
  exact (mul_left_cancel (mul_left_cancel h))


open Classical in
noncomputable def cosetForm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) : W :=
  if h : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2 then ((χ h.choose.2 : Kˣ) : K) • ρ h.choose.1 w else 0

theorem cosetForm_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) (w : W) (γ : GQ L n) (κ : J) :
    cosetForm ρ J χ g w ((γ : GAf L n) * g * κ) = ((χ κ : Kˣ) : K) • ρ γ w := by
  have hex : ∃ p : GQ L n × J, (γ : GAf L n) * g * κ = (p.1 : GAf L n) * g * p.2 := ⟨(γ, κ), rfl⟩
  unfold cosetForm
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := double_coset_unique hg hex.choose_spec
  rw [← h1, ← h2]

theorem cosetForm_not {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) (hx : ¬ ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2) :
    cosetForm ρ J χ g w x = 0 := by
  unfold cosetForm; rw [dite_eq_right hx]

theorem exists_form_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ g hg
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨cosetForm ρ J χ g w, ⟨fun δ x => ?_, fun μ x => ?_⟩, fun h0 => hw ?_⟩
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (δ : GAf L n) * ((γ : GAf L n) * g * κ) = ((δ * γ : GQ L n) : GAf L n) * g * κ := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_smul, map_mul, Module.End.mul_apply]
    · have hx' : ¬ ∃ p : GQ L n × J, (δ : GAf L n) * x = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(δ⁻¹ * γ, κ), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at hp ⊢
        rw [← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', map_zero]
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (γ : GAf L n) * g * κ * μ = (γ : GAf L n) * g * ((κ * μ : J) : GAf L n) := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_mul, Units.val_mul, mul_comm, mul_smul]
    · have hx' : ¬ ∃ p : GQ L n × J, x * μ = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(γ, κ * μ⁻¹), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hp ⊢
        rw [← mul_assoc, ← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', smul_zero]
  · have := congrFun h0 g
    have e := cosetForm_apply ρ J χ g hg w 1 1
    simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one, one_smul] at e
    rw [e, Module.End.one_apply] at this
    simpa using this

end GlobalTheory.ClassForm
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TameUnitOne

open Formalism.L2.NX

theorem tameVal_eq_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type}
    [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ)
    (hopen : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal)
    (hI : ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A P → ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1)
    (u : 𝓞 E) (hu1 : u - 1 ∈ P.asIdeal) : NX.tameVal φ P e u = 1 := by
  have hu : u ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := P.asIdeal.sub_mem h hu1
    simpa using this))
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨hq2, -⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖne : algebraMap E Ω (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ((ϖ : E)) = 0 := (map_eq_zero _).1 h
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h']
    exact zero_mem _
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) (show 0 < Formalism.ConjugateSelfDual.normV P - 1 by omega)
  have hπne : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖne hπ.symm
  have hv : A.valuation ((1 : Formalism.ConjugateSelfDual.G E Ω) π / π - algebraMap E Ω (u : E)) < 1 := by
    rw [AlgEquiv.one_apply, div_self hπne]
    have h1 := (hA (u - 1)).2 hu1
    have e1 : (1 : Ω) - algebraMap E Ω (u : E) = -(algebraMap E Ω (((u - 1 : 𝓞 E)) : E)) := by
      push_cast
      ring
    rw [e1, Valuation.map_neg]
    exact h1
  have hT := GlobalTheory.TameResRead.tameRep_zpow hA (one_mem _) hϖ1 hϖ2 hπ hu hv e
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep φ P e m hopen hm hI _ u hu hT, one_zpow, map_one]

end GlobalTheory.TameUnitOne

namespace GlobalTheory.LevCmp

end GlobalTheory.LevCmp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem exists_nontrivial_addChar_eq_of_ne (p : ℕ) [Fact p.Prime] (Pr : Prop) (φ : AddChar (ZMod p) ℂ) (h : Pr → φ ≠ 1) :
    ∃ ψ' : AddChar (ZMod p) ℂ, ψ' ≠ 1 ∧ (Pr → ψ' = φ) := by
  by_cases hP : Pr
  · exact ⟨φ, h hP, fun _ => rfl⟩
  · refine ⟨ZMod.stdAddChar, ?_, fun h' => absurd h' hP⟩
    intro h1
    have hprim := ZMod.isPrimitive_stdAddChar p
    apply hprim (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, h1]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem split_places_same_natCast_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L) (n : ℕ), s.v = s'.v →
    ((n : ℕ) : 𝓞 L) ∈ s.w.asIdeal → ((n : ℕ) : 𝓞 L) ∈ s'.w.asIdeal := by
  intro L _ _ _ s s' n hv hn
  have e : ((n : ℕ) : 𝓞 L) = algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L) (n : 𝓞 (NumberField.maximalRealSubfield L)) := (map_natCast _ n).symm
  rw [e] at hn ⊢
  have h1 : ((n : ℕ) : 𝓞 (NumberField.maximalRealSubfield L)) ∈ s.v.asIdeal := by
    rw [← s.w_under]; exact Ideal.mem_comap.mpr hn
  rw [hv] at h1
  rw [← s'.w_under] at h1
  exact Ideal.mem_comap.mp h1

end GlobalTheory
end
