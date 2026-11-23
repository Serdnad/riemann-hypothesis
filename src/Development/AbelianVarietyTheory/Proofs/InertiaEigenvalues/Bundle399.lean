module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle378
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.SplitHeckeComm

theorem gelfand {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Subgroup G)
    (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂) (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂)
    (hR' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * β * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J)
    (x : W) (hx : ∀ k ∈ J, ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  let f : G ⧸ J → W := fun c => ρ c.out x
  have hf : ∀ g : G, f (g : G ⧸ J) = ρ g x := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J g
    simp only [f, hk, map_mul, Module.End.mul_apply, hx k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ρ γ (∑ δ ∈ B, ρ δ x)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ J) := fun A B => by
    rw [Finset.sum_product]

    simp only [hf, map_sum, map_mul, Module.End.mul_apply]
  rw [key, key]
  let T : Finset (G ⧸ J) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ J)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ J))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ β α S R hS hS' hR hR' c

theorem gelfand_sub {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (H U : Subgroup G)
    (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a) (hH : ∀ k ∈ H, τ k ∈ H)
    (hU : ∀ k ∈ U, τ k ∈ U)
    (hdc : ∀ g ∈ H, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ τ g = k₁ * g * k₂) (α β : G) (R S : Finset G)
    (hα : α ∈ H) (hβ : β ∈ H)
    (hR' : ∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ U)
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * α * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ U)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * β * k₂)
    (x : W) (hx : ∀ k ∈ U, k ∈ H → ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  have hmem : ∀ (a : G) (A : Finset G), a ∈ H →
      (∀ γ ∈ A, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * a * k₂) → ∀ γ ∈ A, γ ∈ H := by
    intro a A ha h γ hγ
    obtain ⟨k₁, -, k₂, -, h₁, h₂, rfl⟩ := h γ hγ
    exact H.mul_mem (H.mul_mem h₁ ha) h₂
  have hsum : ∀ A : Finset G, (∀ γ ∈ A, γ ∈ H) → ∀ y : W,
      ∑ γ ∈ A, ρ γ y = ∑ γ ∈ A.subtype (· ∈ H), ρ (γ : G) y := fun A hA y =>
    (Finset.sum_subtype_of_mem (fun γ => ρ γ y) hA).symm
  have h1 : ∀ (a : G) (ha : a ∈ H) (A : Finset G),
      (∀ γ ∈ A, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * a * k₂) →
      ∀ γ ∈ (A.subtype (· ∈ H) : Finset H), ∃ k₁ ∈ U.subgroupOf H, ∃ k₂ ∈ U.subgroupOf H, γ = k₁ * ⟨a, ha⟩ * k₂ := by
    intro a ha A h γ hγ
    obtain ⟨k₁, u₁, k₂, u₂, h₁, h₂, e⟩ := h γ (Finset.mem_subtype.1 hγ)
    exact ⟨⟨k₁, h₁⟩, u₁, ⟨k₂, h₂⟩, u₂, Subtype.ext e⟩
  have h2 : ∀ (a : G) (ha : a ∈ H) (A : Finset G), (∀ γ ∈ A, γ ∈ H) →
      (∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * a * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * x ∈ U) →
      ∀ x : H, (∃ k₁ ∈ U.subgroupOf H, ∃ k₂ ∈ U.subgroupOf H, x = k₁ * ⟨a, ha⟩ * k₂) →
        ∃! γ, γ ∈ (A.subtype (· ∈ H) : Finset H) ∧ γ⁻¹ * x ∈ U.subgroupOf H := by
    rintro a ha A hA h x ⟨k₁, u₁, k₂, u₂, e⟩
    obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := h x ⟨k₁, u₁, k₂, u₂, k₁.2, k₂.2, congrArg Subtype.val e⟩
    refine ⟨⟨γ, hA γ hγ⟩, ⟨Finset.mem_subtype.2 hγ, hu⟩, fun δ hδ => Subtype.ext ?_⟩
    exact huniq δ ⟨Finset.mem_subtype.1 hδ.1, hδ.2⟩
  have hRH := hmem α R hα hR
  have hSH := hmem β S hβ hS
  rw [hsum R hRH, hsum S hSH x, hsum S hSH, hsum R hRH x]
  refine gelfand (ρ.comp H.subtype) (U.subgroupOf H) (fun g => ⟨τ g, hH g g.2⟩)
    (fun a b => Subtype.ext (hmul a b)) (fun a => Subtype.ext (hinv a)) (fun g => ?_) (fun k hk => hU k hk)
    ⟨α, hα⟩ ⟨β, hβ⟩ _ _ (h1 α hα R hR) (h2 α hα R hRH hR') (h1 β hβ S hS) (h2 β hβ S hSH hS') x
    (fun k hk => hx k hk k.2)
  obtain ⟨k₁, u₁, k₂, u₂, h₁, h₂, e⟩ := hdc g g.2
  exact ⟨⟨k₁, h₁⟩, u₁, ⟨k₂, h₂⟩, u₂, Subtype.ext e⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def trivSub (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 L⁺))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside T x}
  mul_mem' := by
    intro x y hx hy w hw
    show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    rw [Units.val_mul, Matrix.map_mul, hx w hw, hy w hw, mul_one]
  one_mem' := by
    intro w _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := by
    intro x hx w hw
    have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    have h2 := congrArg (fun M => M.map (compAt L w)) h1
    simp only [Matrix.map_mul, hx w hw, mul_one] at h2
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

def tr (x : GAf L n) : GAf L n :=
  ⟨Formalism.UG.P.heckecomm_tr x.1, by
    have hm : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x.1 = 1 := x.2
    have h := congrArg Matrix.transpose (mul_eq_one_comm.mp hm)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    exact h⟩

theorem loc_tr (s : SplitPlace L) (x : GAf L n) : s.loc n (tr x) = Formalism.UG.P.heckecomm_tr (s.loc n x) :=
  Units.ext rfl

theorem mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
    (h : s.loc n x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L⁺ s.v)) : x ∈ Umax L n := by
  have hint : ∀ a ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L⁺ s.v), ∀ i j,
      Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
    rintro _ ⟨g, rfl⟩ i j
    exact ((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov L⁺ s.v)) i j).2
  have h1 := hint _ h
  have h2 := hint _ (inv_mem h)
  rw [← map_inv] at h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x.1 = 1 := x.2
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

theorem tr_mem_trivSub (T : Set (HeightOneSpectrum (𝓞 L⁺))) (x : GAf L n) (hx : x ∈ trivSub n T) :
    tr x ∈ trivSub n T := by
  intro w hw
  have h := congrArg Matrix.transpose (hx w hw)
  rw [Matrix.transpose_one] at h
  exact h

theorem tr_doubleCoset (s : SplitPlace L) (g : GAf L n) (hg : g ∈ trivSub n {s.v}) :
    ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, k₁ ∈ trivSub n {s.v} ∧ k₂ ∈ trivSub n {s.v} ∧ tr g = k₁ * g * k₂ := by
  obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp L⁺ s.v n (s.loc n g)
  obtain ⟨k, hk, ek⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s a.1
  have hk' : k ∈ trivSub n {s.v} := hk
  have ht : (k * g)⁻¹ * tr g ∈ trivSub n {s.v} := mul_mem (inv_mem (mul_mem hk' hg)) (tr_mem_trivSub _ g hg)
  refine ⟨k, mem_Umax_of_loc s k hk (ek ▸ a.2), (k * g)⁻¹ * tr g, mem_Umax_of_loc s _ ht ?_, hk', ht, by group⟩
  rw [map_mul, map_inv, map_mul, loc_tr, e, ek, inv_mul_cancel_left]
  exact b.2

def rtRep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (GAf L n) (GAf L n → W) where
  toFun := NG.rt L n
  map_one' := LinearMap.ext fun f => funext fun g => congrArg f (mul_one g)
  map_mul' x y := LinearMap.ext fun f => funext fun g => congrArg f (mul_assoc g x y).symm

theorem doubleCoset_comm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L) (α β : GAf L n) (Ra Rb : Finset (GAf L n)), TrivOutside {s.v} α → TrivOutside {s.v} β → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ Ra ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Ra, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * α * k₂) → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ Rb ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Rb, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * β * k₂) → ∀ f : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → ∑ γ ∈ Ra, NG.rt L n γ (∑ δ ∈ Rb, NG.rt L n δ f) = ∑ δ ∈ Rb, NG.rt L n δ (∑ γ ∈ Ra, NG.rt L n γ f) := by
  intro L _ _ _ n W _ _ s α β Ra Rb hα hβ hR' hR hS' hS f hf
  exact gelfand_sub (rtRep L n W) (trivSub n {s.v}) (Umax L n) tr
    (fun a b => Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)) (fun a => Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1))
    (tr_mem_trivSub _) (fun k hk i j => hk j i) (tr_doubleCoset s) α β Ra Rb hα hβ hR' hR hS' hS f hf

end GlobalTheory.SplitHeckeComm

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



namespace GlobalTheory.Pass.LocDirect

theorem lenMod_span_sUnion_le_of_directed : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set (Set M)) (H : Submodule O M) (N : ℕ∞),
    (∀ A ∈ S, ∀ B ∈ S, ∃ C ∈ S, A ⊆ C ∧ B ⊆ C) →
    (∀ A ∈ S, BlochKatoDuality.lenMod (Submodule.span O A) H ≤ N) →
    BlochKatoDuality.lenMod (Submodule.span O (⋃₀ S)) H ≤ N := by
  intro O M _ _ _ S H N hdir hA
  classical
  apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset
  intro F hF
  rcases S.eq_empty_or_nonempty with hS | ⟨A0, hA0⟩
  · have hF0 : (↑F : Set M) = ∅ := by
      rw [hS, Set.sUnion_empty] at hF
      exact Set.subset_empty_iff.mp hF
    rw [hF0, Submodule.span_empty, GlobalTheory.Pass.LocDual.lenMod_eq_height_map, Submodule.map_bot,
      Order.height_bot]
    exact zero_le
  · have key : ∀ G : Finset M, (↑G : Set M) ⊆ ⋃₀ S → ∃ A ∈ S, (↑G : Set M) ⊆ A := by
      intro G
      induction G using Finset.induction_on with
      | empty => intro _; exact ⟨A0, hA0, by simp⟩
      | insert a G ha ih =>
        intro hG
        rw [Finset.coe_insert, Set.insert_subset_iff] at hG
        obtain ⟨B, hB, haB⟩ := hG.1
        obtain ⟨A, hA', hGA⟩ := ih hG.2
        obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA' B hB
        refine ⟨C, hC, ?_⟩
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hBC haB, hGA.trans hAC⟩
    obtain ⟨A, hAS, hFA⟩ := key F hF
    refine le_trans ?_ (hA A hAS)
    rw [GlobalTheory.Pass.LocDual.lenMod_eq_height_map, GlobalTheory.Pass.LocDual.lenMod_eq_height_map]
    exact Order.height_mono (Submodule.map_mono (Submodule.span_mono hFA))

end GlobalTheory.Pass.LocDirect
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.lengthModulo_span_le_of_forall_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  first | exact @GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | exact GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | (intros; apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

variable {D : D7}

open Classical in
theorem goodTw_union {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S} {A B Q : Finset (PlE D.host)} {k : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S (A ∪ B) Q k ψ) :
    IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ ∧ Disjoint Q B := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨⟨⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.1, h2.2.2.1⟩, h3⟩, h4⟩, h2.2.2.2⟩

def Reading.Pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w)
    {Q : Finset (PlE D.host)} (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
    (algebraMap (D.ntw.Ok i k) ρ.Oe ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))

def HasReading (p : TwPack D) (b : Bool) (w : D.what₂.places.Pl) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∃ ρ : Reading p.1 p.2.2.1 b w, ρ.Pulls (BlochKatoReduction.Gen.psiAt b p.2.2.2) ψ₀

theorem psiAt_not {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (x : Γ) :
    BlochKatoReduction.Gen.psiAt (!b) ψ x = (BlochKatoReduction.Gen.psiAt b ψ x)⁻¹ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem pull_inv {L K A B Δ : Type} [Field L] [Field K] [CommRing A] [CommRing B] [Group Δ] [Fintype Δ] (e : L →+* K)
    (m : A →+* B) (m' : B →+* K) (χ : Δ →* Aˣ) (x : Lˣ) (δ : Δ) (h : e (x : L) = m' (m (χ δ : A))) :
    x ^ Fintype.card Δ = 1 ∧ e ((x⁻¹ : Lˣ) : L) = m' (m (((χ δ)⁻¹ : Aˣ) : A)) := by
  constructor
  · apply Units.ext
    apply e.injective
    rw [Units.val_pow_eq_pow_val, map_pow e, h, ← map_pow m', ← map_pow m, ← Units.val_pow_eq_pow_val, ← map_pow χ,
      pow_card_eq_one]
    simp
  · rw [Units.val_inv_eq_inv_val, map_inv₀, h]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem Reading.Pulls.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} {ρ : Reading i k b w}
    {Q : Finset (PlE D.host)} {ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (hρ : ρ.Pulls ψ ψ₀) (h : ∀ x, ψ' x = (ψ x)⁻¹) : (ρ.conj hG).Pulls ψ' ψ₀ := by
  intro g
  have h0 := pull_inv ρ.emb (algebraMap (D.ntw.Ok i k) ρ.Oe) (algebraMap ρ.Oe (FractionRing ρ.Oe)) ψ (ψ₀ g) (D.ntw.art i Q g) (hρ g)
  have h2 := h0.2
  rw [← star_root Fintype.card_pos h0.1, ← h] at h2
  exact h2

theorem HasReading.conj (hG : IsGalois ℚ ↥D.LL0) {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h : HasReading p b w ψ₀) :
    HasReading p (!b) (D.what₂.places.conj w) ψ₀ :=
  let ⟨ρ, hρ⟩ := h
  ⟨ρ.conj hG, hρ.conj hG (psiAt_not b _)⟩

def RankEq (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =
    Module.finrank (FractionRing (D.ntw.Ok i k)) (D.nexp.MtV i j b k Q (ψ.comp (D.ntw.art i Q)))

theorem exists_formsIso {Oe : Type} [CommRing Oe] [IsDomain Oe] [IsDiscreteValuationRing Oe] {A : Type} [CommRing A] [IsDomain A] [Algebra A Oe]
    (hinj : Function.Injective (algebraMap A Oe)) {V : Type} [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) (e : D.what₂.LL →+* FractionRing Oe) (μ : D.what₂.Tup) (j : ℕ) (c : Prop)
    (h : c → Module.finrank D.what₂.LL (D.what₂.MtL μ j) = Module.finrank (FractionRing A) V) :
    ∃ f : D.what₂.MtL μ j →ₛₗ[e] FractionRing Oe ⊗[A] V, c →
      (∀ (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) D.what₂.LL (D.what₂.MtL μ j)),
        LinearIndependent (FractionRing Oe) (fun a => f (b a)) ∧
          Submodule.span (FractionRing Oe) (Set.range fun a => f (b a)) = ⊤) ∧
      Submodule.span Oe (f '' {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}) =
        Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V)) := by
  by_cases hj : c
  · obtain ⟨h1, h2, h3⟩ := form_gen (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _)
      (D.what₂.jMt_basis _ j _) _ (D.what₂.MtLat μ j).span_top (D.what₂.MtLat_sub _ j)
    obtain ⟨h4, h5⟩ := baseChange_lattice hinj Λ hfg hspan
    obtain ⟨f, hf⟩ := exists_semilinear e _ h2 h3
      (Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V))) ((h hj).trans h4.symm)
    exact ⟨f, fun _ => ⟨fun b => hf.1 _ b, hf.2⟩⟩
  · exact ⟨0, fun h1 => absurd h1 hj⟩

section ChoiceOf

variable (twI : D.what₂.places.Pl → D.ntw.Tw) (b : D.what₂.places.Pl → Bool) (Q : D.what₂.places.Pl → Finset (PlE D.host))
  (k : D.what₂.places.Pl → ℕ) (ψ : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k w))ˣ)
  (hr : ∀ w, ReadsAt (twI w) (b w) w) (ρ : ∀ w, Reading (twI w) (k w) (b w) w)
  (h : ∀ w, TwistedAt D w → RankEq (twI w) (b w) (Q w) (k w) (ψ w) w)

def choiceOf : NChoice D :=
  let H := fun w j => exists_formsIso (ρ w).inj _
    (D.nexp.MtLat_fg (twI w) j (b w) (k w) (Q w) ((ψ w).comp (D.ntw.art (twI w) (Q w))))
    (D.nexp.MtLat_span _ _ _ _ _ _) (ρ w).emb (D.what₂.muTw w) j (TwistedAt D w ∧ 1 ≤ j ∧ j ≤ D.R.m)
    fun c => h w c.1 j c.2.1 c.2.2
  { twI := twI
    twI_l := fun w => (hr w).l_eq
    sd := b
    Q := Q
    k' := k
    psi' := ψ
    Oe := fun w => (ρ w).Oe
    algOOe := fun w => ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
      (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
    towOe := fun w =>
      letI := ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
        (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Oe_inj := fun w => (ρ w).inj
    Oe_fin := fun w => (ρ w).fin
    Oe_loc := fun w => (ρ w).loc
    embW := fun w => (ρ w).emb
    embW_w := fun w => (ρ w).emb_w
    eMt := fun w j => (H w j).choose
    eMt_basis := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).1
    eMt_lat := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).2 }

end ChoiceOf

theorem readsAt_of_tie {C : NChoice D} (h : NChTie D C) (w : D.what₂.places.Pl) : ReadsAt (C.twI w) (C.sd w) w := by
  intro x
  obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb (C.twI w) (C.sd w))
  haveI := isLocalHom_phiK (C.twI w) (C.k' w)
  haveI := C.Oe_loc w
  have h1 : C.embW w ((x : ↥D.LL0) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w))
      (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    have h2 := h.embedding_baseField_condition w x (φ x) 1 one_ne_zero (by rw [map_one, mul_one, hφ]; rfl)
    simp only [map_one, mul_one] at h2
    exact h2
  have h2 : (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (C.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y = sideEmb (C.twI w) (C.sd w) (x : ↥D.LL0)) ↔
      ¬ IsUnit (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    rw [isUnit_map_iff, isUnit_map_iff]
    exact ⟨fun ⟨y, hy, hy'⟩ => IsFractionRing.injective _ (FractionRing _) (hy'.trans (hφ x).symm) ▸ hy,
      fun hu => ⟨_, hu, hφ x⟩⟩
  rw [h2]
  generalize algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x)) = u at h1
  generalize ((x : ↥D.LL0) : D.what₂.LL) = x' at h1
  by_cases hx : x' = 0
  · subst hx
    rw [map_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    simp [h1]
  have h3 : 0 < D.what₂.places.val w x' ↔ ¬ 0 ≤ D.what₂.places.val w x'⁻¹ := by
    rw [val_pos_iff, val_nonneg_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 (by simpa using hx))]
  have hu : algebraMap (C.Oe w) (FractionRing (C.Oe w)) u ≠ 0 := h1 ▸ (map_ne_zero _).2 hx
  rw [h3, C.embW_w, map_inv₀, h1, not_iff_not]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v⁻¹ : (C.Oe w)ˣ), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩
  · rintro ⟨v, hv⟩
    exact IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing (C.Oe w))
      (by rw [map_mul, hv, mul_inv_cancel₀ hu, map_one]))

theorem ReadsAt.of_pair (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {v w : D.what₂.places.Pl} (h : ReadsAt i b v)
    (h' : OverOnePair D v w) : ∃ b', ReadsAt i b' w := by
  rcases h' with h' | h'
  · exact ⟨b, h.of_overOne h'⟩
  · exact ⟨!b, (h.conj hG).of_overOne h'⟩

abbrev Pass (D : D7) : Type := (∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)) × Finset (TwPack D)

variable {D₀ D₁ : D7} {E₀ : IntegralHeckeForms.XD D₀} {E₁ : IntegralHeckeForms.XD D₁} {E : IntegralHeckeForms.XD D}

end GlobalTheory.TwistChoice

end
end
