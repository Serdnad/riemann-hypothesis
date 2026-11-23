module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

namespace GlobalTheory

open Representation

theorem intertwiner_mem_iSup_range_eq_sum_smul (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hS : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id)
    (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ)
    (hinj : Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)))
    (ψ : π.IntertwiningMap ρ)
    (hψ : LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap) :
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  classical
  let Φ : (Fin m → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
  have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by
    intro w; simp [Φ, LinearMap.sum_apply]
  have hΦinj : Function.Injective Φ := by
    intro a b h; apply hinj; simpa [hΦ] using h
  have hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Pi.single j n, ?_⟩
    rw [hΦ]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ := fun n =>
    hle (hψ ⟨n, rfl⟩)
  let e := LinearEquiv.ofInjective Φ hΦinj
  let Wm : N →ₗ[ℂ] (Fin m → N) := e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem
  have hW : ∀ n, Φ (Wm n) = ψ n := by
    intro n
    simp only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩ := e.apply_symm_apply _
    have h3 := congrArg Subtype.val h2
    change Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n
    rw [← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]
    exact h3
  have hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j) := by
    intro g n
    apply hΦinj

    rw [hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(φ j).isIntertwining]
  have hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n := by
    intro j
    let θ : π.IntertwiningMap π :=
      (LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by
        intro g v
        simp [hWg])
    obtain ⟨c, hc⟩ := hS θ
    refine ⟨c, fun n => ?_⟩
    have h1 : Wm n j = θ.toLinearMap n := rfl
    rw [h1, hc]
    simp
  choose c hc using hc
  refine ⟨c, fun n => ?_⟩
  rw [← hW, hΦ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, map_smul]

end GlobalTheory
end

section

namespace GlobalTheory.FixedVec

theorem exists_irreducible_subrep_fixed : ∀ (G G' W : Type) [Group G] [Finite G] [Fintype G']
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (i : G' → G) (c : G' → ℂ) (x : W),
    x ≠ 0 → ∑ g, c g • ρ (i g) x = x → ∃ U : Subrepresentation ρ,
      FiniteDimensional ℂ U.toSubmodule ∧ U.toRepresentation.IsIrreducible ∧
      ∃ y : U.toSubmodule, y ≠ 0 ∧ ∑ g, c g • U.toRepresentation (i g) y = y := by
  intro G G' W _ _ _ _ _ ρ i c x hx hfix
  classical
  let P : Subrepresentation ρ → Prop := fun S =>
    FiniteDimensional ℂ S.toSubmodule ∧ ∃ y ∈ S.toSubmodule, y ≠ 0 ∧ ∑ g, c g • ρ (i g) y = y
  let S0 : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun g => ρ g x), by
      intro g v hv
      have hle : (Submodule.span ℂ (Set.range fun g => ρ g x)).map (ρ g) ≤
          Submodule.span ℂ (Set.range fun g => ρ g x) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
        exact ⟨g * h, by simp [map_mul]⟩
      exact hle (Submodule.mem_map_of_mem hv)⟩
  have hP0 : P S0 :=
    ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range _), x,
      Submodule.subset_span ⟨1, by simp⟩, hx, hfix⟩
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, P S ∧ Module.finrank ℂ S.toSubmodule = m :=
    ⟨_, S0, hP0, rfl⟩
  obtain ⟨S, ⟨hSfd, y, hyS, hy0, hyfix⟩, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, P T →
      Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  haveI := hSfd
  let E : S.toSubmodule →ₗ[ℂ] S.toSubmodule := ∑ g, c g • S.toRepresentation (i g)
  have hEapp : ∀ z, E z = ∑ g, c g • S.toRepresentation (i g) z := by
    intro z
    simp [E, LinearMap.sum_apply]
  have hE : ∀ z : S.toSubmodule, ((E z : S.toSubmodule) : W) = ∑ g, c g • ρ (i g) (z : W) := by
    intro z
    rw [hEapp]
    simp [Subrepresentation.toRepresentation]
  have key : ∀ T : Subrepresentation S.toRepresentation, T.toSubmodule ≠ ⊤ →
      ∀ a ∈ T.toSubmodule, a ≠ 0 → E a = a → False := by
    intro T hT a ha ha0 hafix
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hPT : P T' := by
      refine ⟨?_, (a : W), ⟨a, ha, rfl⟩, ?_, ?_⟩
      · exact Submodule.finiteDimensional_of_le (S₂ := S.toSubmodule) (by
          rintro _ ⟨v, -, rfl⟩
          exact v.2)
      · intro h
        exact ha0 (Subtype.ext h)
      · rw [← hE]
        exact congrArg Subtype.val hafix
    have h1 := hmin T' hPT
    have h2 : Module.finrank ℂ T'.toSubmodule = Module.finrank ℂ T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 := Submodule.finrank_lt hT
    omega
  let y' : S.toSubmodule := ⟨y, hyS⟩
  have hy'0 : y' ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hy'fix : E y' = y' := Subtype.ext (by rw [hE]; exact hyfix)
  refine ⟨S, hSfd, ?_, y', hy'0, by rw [← hEapp]; exact hy'fix⟩
  haveI : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule ℂ S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      have hm' : y' ∈ (⊥ : Submodule ℂ S.toSubmodule) := h' ▸ Submodule.mem_top
      exact hy'0 ((Submodule.mem_bot ℂ).1 hm')⟩
  refine ⟨fun T => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hTb, hTt⟩ := hne
  haveI hss : S.toRepresentation.IsSemisimpleRepresentation := by
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  obtain ⟨T', hc⟩ := exists_isCompl T
  have hsup : T.toSubmodule ⊔ T'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hc.sup_eq_top
  have hinf : T.toSubmodule ⊓ T'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hc.inf_eq_bot
  have hTt' : T.toSubmodule ≠ ⊤ := fun h => hTt (Subrepresentation.toSubmodule_injective h)
  have hT't : T'.toSubmodule ≠ ⊤ := by
    intro h
    apply hTb
    apply Subrepresentation.toSubmodule_injective
    rw [h, inf_top_eq] at hinf
    exact hinf
  have hmemE : ∀ U : Subrepresentation S.toRepresentation, ∀ z ∈ U.toSubmodule,
      E z ∈ U.toSubmodule := by
    intro U z hz
    rw [hEapp]
    exact Submodule.sum_mem _ (fun g _ => Submodule.smul_mem _ _ (U.apply_mem_toSubmodule _ hz))
  have hyin : y' ∈ T.toSubmodule ⊔ T'.toSubmodule := hsup ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hyin
  have hsum : E a + E b = a + b := by rw [← map_add (f := _), hab, hy'fix]
  have hd : E a - a ∈ T.toSubmodule ⊓ T'.toSubmodule := by
    refine ⟨Submodule.sub_mem _ (hmemE T a ha) ha, ?_⟩
    have : E a - a = b - E b := by
      rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
    rw [this]
    exact Submodule.sub_mem _ hb (hmemE T' b hb)
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at hd
  have hd' : E b = b := by
    have := hsum
    rw [hd] at this
    exact add_left_cancel this
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := by
      intro hb0
      apply hy'0
      rw [← hab, ha0, hb0, add_zero]
    exact key T' hT't b hb hb0 hd'
  · exact key T hTt' a ha ha0 hd

end GlobalTheory.FixedVec
end

section

namespace GlobalTheory.PiIsotypic

open Representation

theorem nontrivial_of_isIrreducible {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  haveI := h
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule K V))).symm)

theorem exists_irreducible_subrep {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

def subrepOrderIso {K G V V' : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : Representation K G V) (τ : Representation K G V')
    (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v)) :
    Subrepresentation σ ≃o Subrepresentation τ where
  toFun T := ⟨T.toSubmodule.map (e : V →ₗ[K] V'), by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨σ g v, T.apply_mem_toSubmodule g hv, (he g v).symm⟩⟩
  invFun U := ⟨U.toSubmodule.comap (e : V →ₗ[K] V'), by
    intro g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact U.apply_mem_toSubmodule g hv⟩
  left_inv T := Subrepresentation.ext (Submodule.comap_map_eq_of_injective e.injective _)
  right_inv U := Subrepresentation.ext (Submodule.map_comap_eq_of_surjective e.surjective _)
  map_rel_iff' {a b} := by
    show a.toSubmodule.map (e : V →ₗ[K] V') ≤ b.toSubmodule.map (e : V →ₗ[K] V') ↔
      a.toSubmodule ≤ b.toSubmodule
    exact Submodule.map_le_map_iff_of_injective e.injective _ _

theorem isIrreducible_of_linearEquiv {K G V V' : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K V'] (σ : Representation K G V)
    (τ : Representation K G V') (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v))
    (h : σ.IsIrreducible) : τ.IsIrreducible := by
  haveI := h
  exact (subrepOrderIso σ τ e he).symm.isSimpleOrder

end GlobalTheory.PiIsotypic

namespace GlobalTheory.PiIsotypic

open Representation

theorem isotypic_factor_of_isIrreducible_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  intro ι _ _ G _ _ W _ _ _ ρ hρ i
  classical
  haveI : Nontrivial W := nontrivial_of_isIrreducible ρ hρ
  let ρi : Representation ℂ (G i) W := ρ.comp (MonoidHom.mulSingle G i)
  obtain ⟨S, hS⟩ := exists_irreducible_subrep ρi
  let n := Module.finrank ℂ S.toSubmodule
  let e : S.toSubmodule ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let τ : Representation ℂ (G i) (Fin n → ℂ) :=
    { toFun := fun g => e.toLinearMap ∘ₗ S.toRepresentation g ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hτe : ∀ g v, τ g (e v) = e (S.toRepresentation g v) := by
    intro g v; simp [τ]
  have hτ : τ.IsIrreducible := isIrreducible_of_linearEquiv S.toRepresentation τ e hτe hS
  let φ0 : (Fin n → ℂ) →ₗ[ℂ] W := S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have hφ0 : ∀ g z, φ0 (τ g z) = ρ (Pi.mulSingle i g) (φ0 z) := by
    intro g z
    simp [φ0, τ]
    rfl
  have hinj : Function.Injective φ0 :=
    Subtype.val_injective.comp e.symm.injective
  refine ⟨n, τ, hτ, ⟨φ0, hinj, hφ0⟩, ?_⟩
  set T : Set W := {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W,
    (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} with hTdef
  have hstab : ∀ g y, y ∈ T → ρ g y ∈ T := by
    rintro g y ⟨φ, hφ, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
    let g' : ∀ j, G j := g * Pi.mulSingle i (g i)⁻¹
    have hcomm : ∀ h : G i, g' * Pi.mulSingle i h = Pi.mulSingle i h * g' := by
      intro h
      funext j
      by_cases hj : j = i
      · subst hj
        simp [g']
      · simp [g', Pi.mulSingle_eq_of_ne hj]
    have hg : g = g' * Pi.mulSingle i (g i) := by
      simp only [g', mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, mul_one]
    refine ⟨ρ g' ∘ₗ φ, ?_, LinearMap.mem_range.2 ⟨τ (g i) z, ?_⟩⟩
    · intro h z'
      simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    · simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, ← hg]
  let U : Subrepresentation ρ := ⟨Submodule.span ℂ T, fun g v hv => by
    have hle : Submodule.span ℂ T ≤ (Submodule.span ℂ T).comap (ρ g) :=
      Submodule.span_le.2 (fun y hy => Submodule.subset_span (hstab g y hy))
    exact hle hv⟩
  haveI := hρ
  rcases eq_bot_or_eq_top U with h | h
  · exfalso
    have hspan : Submodule.span ℂ T = ⊥ := congrArg Subrepresentation.toSubmodule h
    haveI : Nontrivial (Fin n → ℂ) := nontrivial_of_isIrreducible τ hτ
    obtain ⟨z, hz⟩ := exists_ne (0 : Fin n → ℂ)
    have hmem : φ0 z ∈ Submodule.span ℂ T :=
      Submodule.subset_span ⟨φ0, hφ0, LinearMap.mem_range.2 ⟨z, rfl⟩⟩
    rw [hspan, Submodule.mem_bot] at hmem
    exact hz (hinj (by rw [hmem, map_zero]))
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.PiIsotypic
end

section

open MeasureTheory

noncomputable section

namespace GlobalTheory.AffineMean

theorem affine_fundamentalDomain_mean :
    ∀ (g : ℕ) (Λ' Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
      (c : Fin g → ℂ) (f : (Fin g → ℂ) → ℝ), Countable Λ' → (∀ z, L z ∈ Λ' ↔ z ∈ Λ₁) →
      IsAddFundamentalDomain Λ' Fd' volume → (∀ a ∈ Λ', ∀ z, f (z + a) = f z) →
      (∫ z in Fd', f z) / (volume Fd').toReal = 1 →
      IsAddFundamentalDomain Λ₁ ((fun z => L z + c) ⁻¹' Fd') volume ∧
        (∫ z in (fun z => L z + c) ⁻¹' Fd', f (L z + c)) / (volume ((fun z => L z + c) ⁻¹' Fd')).toReal = 1 := by
  intro g Λ' Λ₁ Fd' L c f hcount hΛ hF' _ hmean
  let L' : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := L.restrictScalars ℝ
  have hL : ∀ z, L' z = L z := fun z => rfl
  let e : (Fin g → ℂ) ≃ᵐ (Fin g → ℂ) :=
    (L'.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addRight c)).toMeasurableEquiv
  have he : ∀ z, e z = L z + c := fun z => rfl
  have hpre : (fun z => L z + c) ⁻¹' Fd' = e ⁻¹' Fd' := rfl
  have hd : LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ≠ 0 := (LinearEquiv.isUnit_det' L').ne_zero
  have hmapL : Measure.map L' volume =
      ENNReal.ofReal |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hc : 0 < |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| := abs_pos.2 (inv_ne_zero hd)
  generalize |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| = k at hmapL hc
  have hmap : Measure.map e volume = ENNReal.ofReal k • volume := by
    have h1 : (e : (Fin g → ℂ) → (Fin g → ℂ)) = (fun z => z + c) ∘ (L' : (Fin g → ℂ) → (Fin g → ℂ)) := rfl
    have hLm : Measurable (L' : (Fin g → ℂ) → (Fin g → ℂ)) :=
      L'.toContinuousLinearEquiv.continuous.measurable
    rw [h1, ← Measure.map_map (measurable_add_const c) hLm, hmapL, Measure.map_smul, map_add_right_eq_self]
    exact (measurable_add_const c).aemeasurable
  have hq : Measure.QuasiMeasurePreserving e volume volume :=
    ⟨e.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let ε : Λ' → Λ₁ := fun a => ⟨L.symm a, (hΛ _).1 (by rw [L.apply_symm_apply]; exact a.2)⟩
  have hε : Function.Bijective ε :=
    ⟨fun a b hab => Subtype.ext (L.symm.injective (congrArg Subtype.val hab)),
      fun a => ⟨⟨L a, (hΛ _).2 a.2⟩, Subtype.ext (L.symm_apply_apply _)⟩⟩
  have hF2 : IsAddFundamentalDomain Λ₁ (e ⁻¹' Fd') volume :=
    hF'.preimage_of_equiv hq hε fun a z => by
      change L (L.symm (a : Fin g → ℂ) + z) + c = (a : Fin g → ℂ) + (L z + c)
      rw [map_add (f := _), L.apply_symm_apply, add_assoc]
  have i2 : ∫ z in e ⁻¹' Fd', f (e z) = k * ∫ z in Fd', f z := by
    have := setIntegral_map_equiv (μ := volume) e f Fd'
    rw [hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at this
    exact this.symm
  have i3 : (volume (e ⁻¹' Fd')).toReal = k * (volume Fd').toReal := by
    rw [← e.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  refine ⟨hpre ▸ hF2, ?_⟩
  rw [hpre]
  have i2' : ∫ z in e ⁻¹' Fd', f (L z + c) = k * ∫ z in Fd', f z := i2
  rw [i2', i3, mul_div_mul_left _ _ hc.ne', hmean]

end GlobalTheory.AffineMean
end
end

section

namespace GlobalTheory.ProdSubProdBound

theorem prod_sub_prod_le {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
    {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}
    (ha : ∀ i, v (a i) ≤ 1) (hb : ∀ i, v (b i) ≤ 1) (hab : ∀ i, v (a i - b i) ≤ c) :
    v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have hB : v (∏ i ∈ s, b i) ≤ 1 := by
      rw [map_prod]; exact Finset.prod_le_one' (fun i _ => hb i)
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · rw [v.map_mul]
      calc v (a j) * v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ 1 * c := mul_le_mul' (ha j) ih
        _ = c := one_mul c
    · rw [v.map_mul]
      calc v (a j - b j) * v (∏ i ∈ s, b i) ≤ c * 1 := mul_le_mul' (hab j) hB
        _ = c := mul_one c

theorem main : ∀ {K Γ : Type} [inst : Field K] [inst_1 : LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}, (∀ (i : ι), (v : K → Γ) (a i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (b i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (a i - b i) ≤ c) → (v : K → Γ) (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c :=
  fun s => prod_sub_prod_le s

end GlobalTheory.ProdSubProdBound
end
