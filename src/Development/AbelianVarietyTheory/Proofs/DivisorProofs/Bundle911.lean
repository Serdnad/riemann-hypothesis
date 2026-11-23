module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle880
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Parabolic.LeviGen

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism Matrix

variable {F : Type} [Field F] {r d d' : ℕ}

theorem mem_range_blockEnum (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (i : Fin r) :
    i ∈ Set.range (blockEnum b c h) ↔ b i = c := by
  have e : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) := Finset.range_orderEmbOfFin _ h
  rw [e]
  simp [block]

theorem extendMat_comm (e : Fin d ↪ Fin r) (e' : Fin d' ↪ Fin r) (h : ∀ a a', e a ≠ e' a')
    (M : Matrix (Fin d) (Fin d) F) (N : Matrix (Fin d') (Fin d') F) :
    extendMat e M * extendMat e' N = extendMat e' N * extendMat e M := by
  have h1 : (incl F e)ᵀ * incl F e' = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, h a a']
  have h2 : (incl F e')ᵀ * incl F e = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, (h a' a).symm]
  have h3 : incl F e * (M - 1) * (incl F e)ᵀ * (incl F e' * (N - 1) * (incl F e')ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e)ᵀ, h1]; simp
  have h4 : incl F e' * (N - 1) * (incl F e')ᵀ * (incl F e * (M - 1) * (incl F e)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e')ᵀ, h2]; simp
  simp only [extendMat, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [add_mul, mul_add, h3, h4, one_mul, mul_one]
  abel

def leviIncl (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    GL (Fin d) F →* levi F b :=
  ((blockTri (κ := F) b).subtype.comp (blockHom F b c h)).codRestrict _ fun g => by
    refine mem_levi.2 fun i j hij => ?_
    show extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = 0
    rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
    simp only [mem_range_blockEnum]
    omega

theorem leviIncl_val (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    ((leviIncl F b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) := rfl

def leviRes (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    levi F b →* GL (Fin d) F :=
  leviBlock b (blockEnum b c h) (blockEnum b c h).injective fun i j hij => by
    rw [mem_range_blockEnum, ← hij, blockEnum_mem b c h]

theorem leviRes_apply (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (m : levi F b) (a a' : Fin d) :
    (leviRes F b c h m : Matrix (Fin d) (Fin d) F) a a' =
      ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c h a) (blockEnum b c h a') := rfl

theorem leviRes_leviIncl (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    leviRes F b c h (leviIncl F b c h g) = g := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_in]

theorem leviRes_leviIncl_ne (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c' ≠ c) (g : GL (Fin d) F) : leviRes F b c' h' (leviIncl F b c h g) = 1 := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_out]
  · simp [Matrix.one_apply]
  · left
    rw [mem_range_blockEnum, blockEnum_mem b c' h']
    exact hc

theorem leviIncl_comm (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c ≠ c') (g : GL (Fin d) F) (g' : GL (Fin d') F) :
    Commute (leviIncl F b c h g) (leviIncl F b c' h' g') := by
  refine Subtype.ext (Units.ext ?_)
  refine extendMat_comm _ _ (fun a a' e => hc ?_) _ _
  rw [← blockEnum_mem b c h a, e, blockEnum_mem b c' h']

theorem iSup_range_leviIncl (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c) :
    (⨆ c : Set.range b, (leviIncl F b c (h c)).range) = ⊤ := by
  classical
  have key : ∀ s : Finset (Set.range b), ∀ m : levi F b,
      (∀ c : Set.range b, c ∉ s → leviRes F b c (h c) m = 1) →
        m ∈ ⨆ c : Set.range b, (leviIncl F b c (h c)).range := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro m hm
      have : m = 1 := by
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        by_cases hij : b i = b j
        · let c : Set.range b := ⟨b i, i, rfl⟩
          obtain ⟨a, ha⟩ := (mem_range_blockEnum b c (h c) i).2 rfl
          obtain ⟨a', ha'⟩ := (mem_range_blockEnum b c (h c) j).2 hij.symm
          have h1 := leviRes_apply b c (h c) m a a'
          rw [hm c (Finset.notMem_empty _), ha, ha'] at h1
          rw [← h1]
          have : i = j ↔ a = a' := by rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
          simp [Matrix.one_apply, this]
        · rw [m.2 i j hij]
          simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      rw [this]
      exact Subgroup.one_mem _
    | insert c s _ ih =>
      intro m hm
      have e : m = m * leviIncl F b c (h c) (leviRes F b c (h c) m)⁻¹ *
          leviIncl F b c (h c) (leviRes F b c (h c) m) := by simp
      rw [e]
      refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
      by_cases hcc : c' = c
      · subst hcc
        rw [map_mul, leviRes_leviIncl, mul_inv_cancel]
      · rw [map_mul, leviRes_leviIncl_ne b _ _ (fun e => hcc (Subtype.ext e)), mul_one]
        exact hm c' (by simp [hcc, hc'])
  have := Fintype.ofFinite (Set.range b)
  exact eq_top_iff.2 fun m _ => key Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc

theorem levi_generated : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c), ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi F b,
    (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
      (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧ (⨆ c, (f c).range) = ⊤ ∧
    ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F), Commute (f c x) (f c' y) :=
  fun F _ _ b d h => ⟨fun c => leviIncl F b c (h c), fun _ _ => rfl, iSup_range_leviIncl b d h,
    fun c c' hc x y => leviIncl_comm b (h c) (h c') (fun e => hc (Subtype.ext e)) x y⟩

end GlobalTheory.Parabolic.LeviGen
end
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
open Matrix in

theorem _root_.GlobalTheory.T.exists_levi_generated_commuting_blockGL :
    ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
      (h : ∀ c : Set.range b, (block b c).card = d c),
      ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi (k := F) b,
        (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
          (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧
        (⨆ c, (f c).range) = ⊤ ∧
        ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F),
          Commute (f c x) (f c' y) := by
  classical
  intro F _ r b d h
  have mem_enum (c : Set.range b) (i : Fin r) :
      i ∈ Set.range (blockEnum b c (h c)) ↔ b i = c := by
    have hrange : Set.range (blockEnum b c (h c)) = (block b c : Set (Fin r)) :=
      Finset.range_orderEmbOfFin _ (h c)
    rw [hrange]
    simp [block]
  let f (c : Set.range b) : GL (Fin (d c)) F →* levi (k := F) b :=
    ((blockTri (κ := F) b).subtype.comp (blockHom F b c (h c))).codRestrict _ fun g => by
      refine mem_levi.2 fun i j hij => ?_
      show extendMat (blockEnum b c (h c)) (g : Matrix (Fin (d c)) (Fin (d c)) F) i j = 0
      rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      simp only [mem_enum]
      omega
  let res (c : Set.range b) : levi (k := F) b →* GL (Fin (d c)) F :=
    leviBlock b (blockEnum b c (h c)) (blockEnum b c (h c)).injective fun i j hij => by
      rw [mem_enum, ← hij, blockEnum_mem b c (h c)]
  have f_apply (c : Set.range b) (g : GL (Fin (d c)) F) :
      ((f c g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        extendMat (blockEnum b c (h c)) (g : Matrix (Fin (d c)) (Fin (d c)) F) := rfl
  have res_apply (c : Set.range b) (m : levi (k := F) b) (a a' : Fin (d c)) :
      (res c m : Matrix (Fin (d c)) (Fin (d c)) F) a a' =
        ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c (h c) a)
          (blockEnum b c (h c) a') := rfl
  have res_f (c : Set.range b) (g : GL (Fin (d c)) F) : res c (f c g) = g := by
    refine Units.ext (Matrix.ext fun a a' => ?_)
    rw [res_apply, f_apply, extendMat_in]
  have res_f_ne (c c' : Set.range b) (hc : c' ≠ c) (g : GL (Fin (d c)) F) :
      res c' (f c g) = 1 := by
    refine Units.ext (Matrix.ext fun a a' => ?_)
    rw [res_apply, f_apply, extendMat_out]
    · simp [Matrix.one_apply]
    · left
      rw [mem_enum, blockEnum_mem b c' (h c')]
      exact fun e => hc (Subtype.ext e)
  refine ⟨f, fun _ _ => rfl, ?_, ?_⟩
  · have generated : ∀ s : Finset (Set.range b), ∀ m : levi (k := F) b,
        (∀ c : Set.range b, c ∉ s → res c m = 1) → m ∈ ⨆ c : Set.range b, (f c).range := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro m hm
        have hm_one : m = 1 := by
          refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
          by_cases hij : b i = b j
          · let c : Set.range b := ⟨b i, i, rfl⟩
            obtain ⟨a, ha⟩ := (mem_enum c i).2 rfl
            obtain ⟨a', ha'⟩ := (mem_enum c j).2 hij.symm
            have hentry := res_apply c m a a'
            rw [hm c (Finset.notMem_empty _), ha, ha'] at hentry
            rw [← hentry]
            have heq : i = j ↔ a = a' := by
              rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
            simp [Matrix.one_apply, heq]
          · rw [m.2 i j hij]
            simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
        rw [hm_one]
        exact Subgroup.one_mem _
      | insert c s _ ih =>
        intro m hm
        let g := f c (res c m)
        have hg : m = m * g⁻¹ * g := by simp
        rw [hg]
        refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
        change res c' (m * (f c (res c m))⁻¹) = 1
        by_cases hcc : c' = c
        · subst c'
          rw [map_mul, map_inv, res_f, mul_inv_cancel]
        · rw [map_mul, map_inv, res_f_ne c c' hcc, inv_one, mul_one]
          exact hm c' (by simp [hcc, hc'])
    let := Fintype.ofFinite (Set.range b)
    exact eq_top_iff.2 fun m _ => generated Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc
  · intro c c' hc x y
    refine Subtype.ext (Units.ext ?_)
    change ((f c x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
        ((f c' y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      ((f c' y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
        ((f c x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
    rw [f_apply, f_apply]
    let e := blockEnum b c (h c)
    let e' := blockEnum b c' (h c')
    change extendMat e (x : Matrix (Fin (d c)) (Fin (d c)) F) *
        extendMat e' (y : Matrix (Fin (d c')) (Fin (d c')) F) =
      extendMat e' (y : Matrix (Fin (d c')) (Fin (d c')) F) *
        extendMat e (x : Matrix (Fin (d c)) (Fin (d c)) F)
    have disjoint (a : Fin (d c)) (a' : Fin (d c')) : e a ≠ e' a' := by
      intro he
      apply hc
      apply Subtype.ext
      rw [← blockEnum_mem b c (h c) a, ← blockEnum_mem b c' (h c') a']
      exact congrArg b he
    have hxy : (incl F e)ᵀ * incl F e' = 0 := by
      ext a a'
      simp [incl, Matrix.mul_apply, Matrix.one_apply, disjoint a a']
    have hyx : (incl F e')ᵀ * incl F e = 0 := by
      ext a' a
      simp [incl, Matrix.mul_apply, Matrix.one_apply, (disjoint a a').symm]
    let X := incl F e * ((x : Matrix (Fin (d c)) (Fin (d c)) F) - 1) * (incl F e)ᵀ
    let Y := incl F e' * ((y : Matrix (Fin (d c')) (Fin (d c')) F) - 1) * (incl F e')ᵀ
    have hXY : X * Y = 0 := by
      dsimp [X, Y]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e)ᵀ, hxy]
      simp
    have hYX : Y * X = 0 := by
      dsimp [X, Y]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e')ᵀ, hyx]
      simp
    change (1 + X) * (1 + Y) = (1 + Y) * (1 + X)
    simp only [add_mul, mul_add, hXY, hYX, one_mul, mul_one]
    abel
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.Proof.BlockConj

theorem range_blockEnum {r d : ℕ} (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (k : Fin r) :
    k ∈ Set.range (blockEnum b c h) ↔ b k = c := by
  have h1 : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) :=
    Finset.range_orderEmbOfFin (block b c) h
  rw [h1]
  simp [block]

theorem blockHom_conj_permGL (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r))
    (hw : ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) (i : Fin r) :
    (block b (b i)).card = (block b' (b' (w i))).card ∧
    ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d),
      ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F,
        (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w =
          permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  refine ⟨?_, fun d h h' => ?_⟩
  · refine Finset.card_equiv w fun k => ?_
    simp [block, hw k i]
  · set e := blockEnum b (b i) h with he
    set e' := blockEnum b' (b' (w i)) h' with he'
    have hr : ∀ k, k ∈ Set.range e ↔ w k ∈ Set.range e' := fun k => by
      rw [he, he', range_blockEnum, range_blockEnum, hw k i]
    have hex : ∀ a, ∃ a', e' a' = w (e a) := fun a => (hr (e a)).1 ⟨a, rfl⟩
    choose p hp using hex
    have hinj : Function.Injective p := fun a a' haa => by
      apply e.injective
      apply w.injective
      rw [← hp, ← hp, haa]
    let π₀ : Equiv.Perm (Fin d) := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)
    have hπ : ∀ a, e' (π₀ a) = w (e a) := hp
    refine ⟨permGL F π₀, fun g => ?_⟩
    refine eq_mul_inv_iff_mul_eq.1 ?_
    ext k l
    obtain ⟨k, rfl⟩ := w.surjective k
    obtain ⟨l, rfl⟩ := w.surjective l
    rw [conj_permGL_apply]
    show extendMat e' ((permGL F π₀ * g * (permGL F π₀)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) (w k) (w l)
      = extendMat e (g : Matrix (Fin d) (Fin d) F) k l
    by_cases hkl : k ∈ Set.range e ∧ l ∈ Set.range e
    · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hkl
      rw [← hπ, ← hπ, extendMat_in, extendMat_in, conj_permGL_apply]
    · rw [not_and_or] at hkl
      rw [extendMat_out _ _ _ _ hkl, extendMat_out _ _ _ _ (by rwa [← hr, ← hr])]
      simp [Matrix.one_apply]

end GlobalTheory.Proof.BlockConj
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.Div

theorem resG_eq_inv_mul_appLE {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {φ : X' ⟶ X}
    (w : LB.Iso H' (H.pull φ)) (k : H.ι) (k' : H'.ι) (a : Γ(X, H.U k)) (b : Γ(X', H'.U k'))
    (h : ∀ z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ a = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ b) :
    resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b =
      ((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val *
        (φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
          (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a := by
  apply fn_ext
  intro x hx
  have hk : φ x ∈ H.U k := (GlobalTheory.Cartier.pull_U H φ _).le hx.1
  have hx' : x ∈ H'.U k' := hx.2
  have e := h x hk hx'
  have h1 : gs (𝟙 X') x _ (resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b) =
      gs (𝟙 X') x _ b := gs_res (𝟙 X') x inf_le_right hx b
  have h2 : gs (𝟙 X') x _ ((φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
      (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a) = gs φ x _ a := by
    have := gs_res (𝟙 X') x (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le) hx ((φ.app (H.U k)).hom a)
    refine Eq.trans ?_ (this.trans ((gs_pull (𝟙 X') φ x (H.U k) hk a).trans (by rw [Category.id_comp])))
    rfl
  have h3 : gs (𝟙 X') x _ (((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val) =
      ((Geo.Tor.gw w (𝟙 _) x k k')⁻¹).val := by
    rw [gs_unit (𝟙 X') x _ hx, map_inv]
    rfl
  rw [h1, gs_mul (𝟙 X') x _ hx, h2, h3, e, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem isClosedImmersion_of_veryAmpleBy_compat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  intro R _ X f H n s hH hs X' f' H' s' φ w hH' hs' hf _ hrel
  subst hf
  obtain ⟨hc, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hs
  obtain ⟨hc', hci'⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff (φ ≫ f) s').1 hs'
  have heq : GlobalTheory.ProjSpace.toProj (φ ≫ f) s' hc' = φ ≫ GlobalTheory.ProjSpace.toProj f s hc := by
    refine GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hc φ hc' fun z => ?_
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact ⟨(H.pull φ).U (fun _ => k) ⊓ H'.U k', ⟨(GlobalTheory.Cartier.pull_U H φ _).ge hk, hk'⟩, k,
      inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le, k', inf_le_right, _,
      fun j => resG_eq_inv_mul_appLE w k k' _ _ fun y hy hy' => hrel j y k k' hy hy'⟩
  have : IsClosedImmersion (φ ≫ GlobalTheory.ProjSpace.toProj f s hc) := heq ▸ hci'
  exact IsClosedImmersion.of_comp_isClosedImmersion φ (GlobalTheory.ProjSpace.toProj f s hc)

end GlobalTheory.Div
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw.SecBC


open GlobalTheory.AbLaw in
theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar
    (hV : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B]
      (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → FirstCohomologyVanishes (pw M (a : ℤ)))
    (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hA : IsAbelianScheme A)
    (hL : L.IsLB) (hAm : RelAmple A L) (a : ℕ) (ha : 1 ≤ a) (T : Over S) (K : Type) [Field K] [IsAlgClosed K]
    (q : Spec (CommRingCat.of K) ⟶ T.left) :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)),
      IsPullback π f' (fst T A).left q ∧ FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  let s : Spec (CommRingCat.of K) ⟶ S := q ≫ T.hom
  let AK : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj A
  let g : AK.left ⟶ A.left := pullback.fst A.hom s
  have hg : IsPullback g AK.hom A.hom s := IsPullback.of_hasPullback A.hom s
  let M : LB AK.left := L.pull g
  have hM : M.IsLB := LB.isLB_pull hL g
  have hAK : IsAbelianScheme AK := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := s (default : PrimeSpectrum K)) trivial
  have hsub : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hMA : RelAmple AK M := ReciprocityTheory.ChartRestriction.G.Geo.Tor.relAmple_pull (w := ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso M) hg hL hM
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM)) U hU
    (fun y => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]) hAm
  have hK := hV K AK M hAK hM hMA a ha
  have H := isPullback_snd A T
  let π : AK.left ⟶ (T ⊗ A).left := H.lift g (AK.hom ≫ q) (by rw [hg.w, Category.assoc])
  have e₁ : π ≫ (snd T A).left = g := H.lift_fst _ _ _
  have e₂ : π ≫ (fst T A).left = AK.hom ≫ q := H.lift_snd _ _ _
  refine ⟨AK.left, π, AK.hom, IsPullback.of_right (by rw [e₁]; exact hg) e₂ H, ?_⟩
  refine h1Zero_of_isIso _ _ (𝟙 _) (pw M a) _ inferInstance (isLB_pw hM _)
    (LB.isLB_pull (LB.isLB_linComb hL _ _) π) ?_ hK
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (chartOut L (fun _ : Fin 1 => (snd T A).left) (fun _ => (a : ℤ)) π
    (fun _ => 𝟙 _ ≫ g) fun _ => by rw [e₁, Category.id_comp]) (chartPw M a)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm (ReciprocityTheory.ChartRestriction.G.Geo.Tor.iso_linComb
      ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM))
      (fun _ : Fin 1 => 𝟙 _) (fun _ => (a : ℤ))))

theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all : ((∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π)) := by
  intro hV S A _ _ L hA hL hAm a ha T K _ _ q
  exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar hV S A L hA hL hAm a ha T K q
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection : ∀ (P G₁ G₂ : Type) [Group P] [Finite P] [Group G₁] [Group G₂] (π : P →* G₁ × G₂), Function.Surjective π → ∀ (φ₁ Y₁ : G₁ → ℂ) (φ₂ Y₂ : G₂ → ℂ), IsChar ℂ ℂ Y₁ → IsChar ℂ ℂ Y₂ → Kills φ₁ Y₁ → Kills φ₂ Y₂ → Kills (fun p => φ₁ (π p).1 * φ₂ (π p).2) (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
  first | (exact @GlobalTheory.Shin.kills_prod_comp_surj) | (exact GlobalTheory.Shin.kills_prod_comp_surj) | (intros; apply GlobalTheory.Shin.kills_prod_comp_surj <;> assumption)
end
