module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle095
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.AbsIrrMap

theorem isAbsIrrChar_map : ∀ {K K' G : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G]
    (φ : K →+* K') (χ : G → K), IsAbsIrrChar χ → IsAbsIrrChar (fun g => φ (χ g)) := by
  intro K K' G _ _ _ _ _ _ φ χ h
  classical
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let A := AlgebraicClosure K
  let A' := AlgebraicClosure K'
  letI : Algebra K A' := ((algebraMap K' A').comp φ).toAlgebra
  let ψ : A →ₐ[K] A' := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : ∀ x : K, ψ (algebraMap K A x) = algebraMap K' A' (φ x) := fun x => by
    rw [AlgHom.commutes]; rfl
  let ρ' : Representation A' G (Fin n → A') := GlobalTheory.BrauerRealise.mapScalars (ψ : A →+* A') ρ
  have hch : ∀ g, ρ'.character g = ψ (ρ.character g) :=
    GlobalTheory.BrauerRealise.character_mapScalars (ψ : A →+* A') ρ
  refine ⟨n, ρ', GlobalTheory.BrauerRealise.isIrreducible_of_sum_char_mul_char_inv ρ' ?_, fun t => ?_⟩
  · have : Invertible ((Nat.card G : ℕ) : A) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have hcard : ((Nat.card G : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : A) := by
      field_simp at ho
      simpa using ho

    simp only [hch, ← map_mul, ← map_sum, hsum]
    exact map_natCast ψ _
  · rw [hch, hρ, hψ]

end GlobalTheory.AbsIrrMap
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MoveTyped

open Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem isSubrep_bot (ρ : Representation ℂ (GQ L n) W) :
    IsSubrep ρ (⊥ : Submodule ℂ (GAf L n → W)) :=
  ⟨bot_le, fun h f hf => by
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    exact map_zero _⟩

theorem isSubrep_sup {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊔ Y) :=
  ⟨sup_le hX.le hY.le, fun h f hf => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩

theorem isSubrep_inf {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊓ Y) :=
  ⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩

theorem sup_typed_eq_bot {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {X Y : Submodule ℂ (GAf L n → W)} (hX : IsSubrep ρ X) (hXT : X ⊓ TypeSp ρ J χ = ⊥)
    (hY : IsIrrRep ρ Y) (hYT : Y ⊓ TypeSp ρ J χ = ⊥) : (X ⊔ Y) ⊓ TypeSp ρ J χ = ⊥ := by
  by_cases hXY : X ⊓ Y = ⊥
  · rw [eq_bot_iff]
    rintro v ⟨hv, hvT⟩
    have hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v := hvT
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧
        rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b := by
      intro κ
      have e := hvT'.2 κ
      rw [map_add (f := _), smul_add] at e
      have hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y := by
        refine ⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩
        have hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a =
            ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        rw [hab]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)
      rw [hXY, Submodule.mem_bot, sub_eq_zero] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact add_left_cancel e
    have ha0 : a ∈ X ⊓ TypeSp ρ J χ := ⟨ha, hX.le ha, fun κ => (key κ).1⟩
    have hb0 : b ∈ Y ⊓ TypeSp ρ J χ := ⟨hb, hY.1.le hb, fun κ => (key κ).2⟩
    rw [hXT, Submodule.mem_bot] at ha0
    rw [hYT, Submodule.mem_bot] at hb0
    simp [ha0, hb0]
  · have hle : X ⊓ Y = Y := (hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY
    have hYX : Y ≤ X := hle ▸ inf_le_left
    rw [sup_eq_left.2 hYX, hXT]

theorem typed_eq_bot_of_iso {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {S S' : Submodule ℂ (GAf L n → W)} (hS : IsSubrep ρ S) (hiso : IsoRep S S')
    (h : S ⊓ TypeSp ρ J χ = ⊥) : S' ⊓ TypeSp ρ J χ = ⊥ := by
  obtain ⟨T, hT⟩ := hiso
  rw [eq_bot_iff]
  rintro u ⟨hu, huT⟩
  have huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u := huT
  obtain ⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩ := ⟨T.symm _, T.apply_symm_apply _⟩
  have hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W) := by
    intro κ
    let f' : S := ⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩
    have e := hT κ f f' rfl
    have hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f) := by
      apply Subtype.ext
      rw [e, map_smul, Submodule.coe_smul, hfu]
      exact huT'.2 κ
    have := congrArg Subtype.val (T.injective hTT)
    simpa [f'] using this
  have hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ := ⟨f.2, hS.le f.2, hf⟩
  rw [h, Submodule.mem_bot] at hfm
  have hf0 : f = 0 := Subtype.ext hfm
  rw [hf0, map_zero] at hfu
  have := congrArg Subtype.val hfu
  simpa using this.symm

theorem typed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S →
    Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  intro L _ _ _ n W _ _ ρ J χ S hS hne h0
  apply hne
  have hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥ :=
    fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0
  have fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} →
      IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [isSubrep_bot]
    | insert a s ha ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨h1, h2⟩ := ih hs.2
      rw [Finset.iSup_insert, sup_comm]
      exact ⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩
  rw [eq_bot_iff]
  rintro v ⟨hv, hvT⟩
  unfold isoTyp at hv
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hv
  have hb := (fin s hs).2
  rw [eq_bot_iff] at hb
  exact hb ⟨hvs, hvT⟩

end GlobalTheory.MoveTyped
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MultIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem mem_AFall_iff {ρ : Representation ℂ (GQ L n) W} {f : GAf L n → W} :
    f ∈ NG.AFall L n ρ ↔ (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
      ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g := Iff.rfl

theorem mem_HomG_iff {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    {Φ : S →ₗ[ℂ] (GAf L n → W)} :
    Φ ∈ NG.HomG ρ S ↔ (∀ f, Φ f ∈ NG.AFall L n ρ) ∧ ∀ (h : GAf L n) (f f' : S),
      (f' : GAf L n → W) = NG.rt L n h (f : GAf L n → W) → Φ f' = NG.rt L n h (Φ f) := Iff.rfl

theorem comp_mem_AFall {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x)) {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) :
    (fun g => A (f g)) ∈ NG.AFall L n ρ' := by
  obtain ⟨h1, N, hN, h2⟩ := mem_AFall_iff.1 hf
  exact mem_AFall_iff.2 ⟨fun γ g => by simp only [h1 γ g, hA], N, hN, fun κ hκ g => by simp only [h2 κ hκ g]⟩

def transport {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) :
    NG.HomG ρ S →ₗ[ℂ] NG.HomG ρ' S' where
  toFun Φ := ⟨(LinearMap.compLeft A (GAf L n)).comp ((Φ : S →ₗ[ℂ] (GAf L n → W)).comp T), mem_HomG_iff.2
     ⟨fun f => comp_mem_AFall A hA ((mem_HomG_iff.1 Φ.2).1 (T f)),
      fun h f f' e => by
        have := (mem_HomG_iff.1 Φ.2).2 h (T f) (T f') (hT h f f' e)
        simp only [LinearMap.comp_apply]
        rw [this]
        rfl⟩⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp
  map_smul' c Φ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp

theorem transport_apply {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) (Φ : NG.HomG ρ S) (x : S') (g : GAf L n) :
    ((transport A hA T hT Φ : S' →ₗ[ℂ] (GAf L n → W')) x) g = A ((Φ : S →ₗ[ℂ] (GAf L n → W)) (T x) g) := rfl

theorem mult_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  rintro L _ _ _ n π π' ⟨⟨A, hA⟩, ⟨T, hT⟩⟩
  have hTs : ∀ (h : GAf L n) (g g' : π'.S), (g' : GAf L n → π'.W) = NG.rt L n h (g : GAf L n → π'.W) →
      ((T.symm g' : π.S) : GAf L n → π.W) = NG.rt L n h ((T.symm g : π.S) : GAf L n → π.W) := by
    intro h g g' hg
    have key := hT h (T.symm g) ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ rfl
    rw [LinearEquiv.apply_symm_apply, ← hg] at key
    have e2 : T ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ = g' := Subtype.ext key
    rw [← e2, LinearEquiv.symm_apply_apply]
  have hAs : ∀ γ x, A.symm (π'.ρ γ x) = π.ρ γ (A.symm x) := by
    intro γ x
    apply A.injective
    rw [LinearEquiv.apply_symm_apply, hA, LinearEquiv.apply_symm_apply]
  let F := transport (ρ := π.ρ) (ρ' := π'.ρ) A.toLinearMap hA T.symm.toLinearMap hTs
  let G := transport (ρ := π'.ρ) (ρ' := π.ρ) A.symm.toLinearMap hAs T.toLinearMap hT
  let e : NG.HomG π.ρ π.S ≃ₗ[ℂ] NG.HomG π'.ρ π'.S := LinearEquiv.ofLinear F G
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
  exact e.finrank_eq

end GlobalTheory.MultIso

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutUnr

section Fixed
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_mem_biSup (ρ : Representation ℂ (GQ L n) W) (K : Set (GAf L n))
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (∀ S ∈ t, NG.IsIrrRep ρ S) → ∀ f ∈ ⨆ S ∈ t, S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ S ∈ t, ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert S t hS ih =>
    intro ht f hf hf0 hfix
    have ht' : ∀ S' ∈ t, NG.IsIrrRep ρ S' := fun S' h => ht S' (Finset.mem_insert_of_mem h)
    have hSi := ht S (Finset.mem_insert_self _ _)
    have hNst : ∀ h, ∀ g ∈ ⨆ S' ∈ t, S', NG.rt L n h g ∈ ⨆ S' ∈ t, S' := by
      intro h
      have hle : (⨆ S' ∈ t, S') ≤ (⨆ S' ∈ t, S').comap (NG.rt L n h) := by
        refine iSup₂_le fun S' hS' g hg => ?_
        exact (le_iSup₂ (f := fun (S'' : Submodule ℂ (GAf L n → W)) (_ : S'' ∈ t) => S'') S' hS')
          ((ht' S' hS').1.stable h g hg)
      exact fun g hg => hle hg
    rw [Finset.iSup_insert] at hf
    by_cases hd : S ⊓ (⨆ S' ∈ t, S') = ⊥
    · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
      have hfa : ∀ κ ∈ K, NG.rt L n κ a = a ∧ NG.rt L n κ b = b := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have h1 : NG.rt L n κ a - a = b - NG.rt L n κ b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        have hm : NG.rt L n κ a - a ∈ S ⊓ (⨆ S' ∈ t, S') :=
          ⟨S.sub_mem (hSi.1.stable κ a ha) ha, h1 ▸ Submodule.sub_mem _ hb (hNst κ b hb)⟩
        rw [hd, Submodule.mem_bot] at hm
        refine ⟨sub_eq_zero.1 hm, ?_⟩
        rw [hm] at h1
        exact (sub_eq_zero.1 h1.symm).symm
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' b hb hf0 fun κ hκ => (hfa κ hκ).2
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨S, Finset.mem_insert_self _ _, a, ha, ha0, fun κ hκ => (hfa κ hκ).1⟩
    · have hsub : NG.IsSubrep ρ (S ⊓ (⨆ S' ∈ t, S')) :=
        ⟨inf_le_left.trans hSi.1.le, fun h g hg => ⟨hSi.1.stable h g hg.1, hNst h g hg.2⟩⟩
      have heq : S ⊓ (⨆ S' ∈ t, S') = S := (hSi.2.2 _ hsub inf_le_left).resolve_left hd
      have hSN : S ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
      have hfN : f ∈ ⨆ S' ∈ t, S' := (sup_le hSN le_rfl) hf
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' f hfN hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem exists_fixed_of_isoTyp (ρ : Representation ℂ (GQ L n) W) {S : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (K : Set (GAf L n)) {f : GAf L n → W} (hf : f ∈ NG.isoTyp ρ S)
    (hf0 : f ≠ 0) (hfix : ∀ κ ∈ K, NG.rt L n κ f = f) : ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  unfold NG.isoTyp at hf
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g, hg, hg0, hgf⟩ :=
    exists_fixed_of_mem_biSup ρ K s (fun S' h => (hs h).1) f hfs hf0 hfix
  obtain ⟨T, hT⟩ := (hs hS').2
  refine ⟨(T.symm ⟨g, hg⟩ : S), (T.symm ⟨g, hg⟩).2, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hg0
    have h1 : T.symm ⟨g, hg⟩ = 0 := Subtype.ext h0
    have h2 := congrArg T h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact congrArg Subtype.val h2
  · set a := T.symm ⟨g, hg⟩
    have e := hT κ a ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ rfl
    have hTa : ((T a : _) : GAf L n → W) = g := by simp [a]
    rw [hTa, hgf κ hκ] at e
    have e2 : T ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ = T a := Subtype.ext (e.trans hTa.symm)
    exact congrArg Subtype.val (T.injective e2)

end Fixed

end GlobalTheory.AutUnr

namespace GlobalTheory.AutUnr

theorem mem_placesOver_of_overPl {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])


end GlobalTheory.AutUnr
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem locTied_any (D' : D7) : Nonempty (Formalism.L2.LocTied D') :=
  ⟨⟨fun l _ => GlobalTheory.LocArith.arithTied l (D'.loc l), fun i w hw => D'.nbr_ind i w hw,
    fun i w hw => D'.ntwbr_ind i w hw⟩⟩

end GlobalTheory.HeightCounting

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.ChiOneRead

theorem localIdele_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E P u = Units.map (Formalism.L2.NC.locM P) u := by
  classical
  apply Units.ext
  rfl

theorem sqrt_zpow (q : ℕ) (r : ℕ) (t nV : ℕ) (h : nV = r + t) :
    ((Real.sqrt q : ℝ) : ℂ) ^ (-(r : ℤ)) = ((q : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 + (1 - (nV : ℝ)) / 2) : ℝ) : ℂ) := by
  subst h
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2) = -(r : ℝ) / 2 := by push_cast; ring
  rw [e]
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast; ring

end GlobalTheory.ChiOneRead
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlacesExc

theorem finite_exceptional : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  intro D l hl
  have h1 : (placesOver D.host.E l).Finite := Formalism.L2.Fam.NPC.placesOver_fin D.host l hl
  have h2 : (placesS D l).Finite := Formalism.L2.Fam.NPC.exceptional_places_finite D.host l
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset] at hv
  exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩

end GlobalTheory.PlacesExc
end
