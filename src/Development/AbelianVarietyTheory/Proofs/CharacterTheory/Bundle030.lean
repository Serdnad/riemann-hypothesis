module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_pair_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ _ _ G _ _ φ a hφ ha hp
  obtain ⟨m, σ, hσ, hφ⟩ := hφ
  obtain ⟨n, ρ, ha⟩ := ha
  have hφ' : φ = fun g => algebraMap K L (σ.character g) := funext hφ
  have ha' : a = fun g => algebraMap K L (ρ.character g) := funext ha
  have h := GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining K L G (Fin m → K) (Fin n → K) σ ρ
  rw [← hφ', ← ha'] at h
  have hex : ∃ f : Representation.IntertwiningMap σ ρ, f ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : Subsingleton (Representation.IntertwiningMap σ ρ) :=
      ⟨fun x y => (hne x).trans (hne y).symm⟩
    apply hp
    rw [h, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  obtain ⟨f, hf⟩ := hex
  haveI := hσ
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G (Fin n → K) (Fin m → K) ρ σ f hi
  refine ⟨c, hc, funext fun g => ?_⟩
  rw [Pi.add_apply, ha g, hφ g, hc' g]

end GlobalTheory.BI
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

def weightStabiliser {L G : Type} [Field L] [Group G] (B : Subgroup G) (hB : B.Normal)
    (lam : B →* Lˣ) : Subgroup G where
  carrier := {g | ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b}
  one_mem' := by
    intro b b' h
    have : b' = b := Subtype.ext (by simpa using h)
    rw [this]
  mul_mem' := by
    intro g h hg hh b b' e
    have hc : g⁻¹ * (b : G) * g ∈ B := by
      simpa using hB.conj_mem b b.2 g⁻¹
    have h1 := hg b ⟨_, hc⟩ rfl
    have h2 := hh ⟨_, hc⟩ b' (by rw [e]; simp [mul_assoc])
    rw [h2, h1]
  inv_mem' := by
    intro g hg b b' e
    exact (hg b' b (by rw [e]; simp [mul_assoc])).symm

theorem nontrivial_of_isIrreducible {L G V : Type} [Field L] [Group G] [AddCommGroup V]
    [Module L V] (ρ : Representation L G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  obtain ⟨x, y, hxy⟩ := h.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem irrChar_linear_or_induced : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  intro L _ _ _ G _ _ χ hG ⟨n, ρ, hρ, hχ⟩
  have hχ' : ∀ g, χ g = ρ.character g := fun g => by simpa using hχ g
  haveI := nontrivial_of_isIrreducible ρ hρ
  by_cases hR : ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ
  · exact Or.inr hR
  left
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible L G (Fin n → L) ρ hρ
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    refine GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central G (Module.End L (Fin n → L)) ρ hG ?_
    intro B hB hBc
    obtain ⟨lam, v, hv, hlam⟩ := GlobalTheory.T.exists_character_eigenvector_of_commuting_representation L B (Fin n → L) (ρ.comp B.subtype)
      (fun a b => hBc a a.2 b b.2)
    obtain ⟨e, he0, hee, heB, heT, heN⟩ := GlobalTheory.T.exists_weight_idempotent_of_eigenvector L G (Fin n → L) ρ B
      (weightStabiliser B hB lam) lam v hB hv hlam (fun _ => Iff.rfl)
    obtain ⟨ψ, hψ, hind⟩ := GlobalTheory.T.character_eq_induced_of_imprimitivity_system L G (Fin n → L) ρ _ e hρ he0 hee heT heN
    have hT : weightStabiliser B hB lam = ⊤ := by
      by_contra hT
      exact hR ⟨_, hT, ψ, hψ, funext fun g => (hχ' g).trans (hind g)⟩
    have he1 : e = 1 := hs1 e he0 hee (fun g => heT g (hT ▸ Subgroup.mem_top g))
    intro b hb g
    have := heB ⟨b, hb⟩
    rw [he1, mul_one] at this
    change ρ b = _ at this
    rw [this, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  obtain ⟨lam, v, hv, hlam⟩ := GlobalTheory.T.exists_character_eigenvector_of_commuting_representation L G (Fin n → L) ρ hcomm
  exact ⟨lam, fun g => (hχ' g).trans (hs2 lam v hv hlam g)⟩

end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem primitive_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr f m hf h0
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  have key : ∀ n : ℕ, ∀ g : Module.End F V,
      Module.finrank F V - Module.finrank F (LinearMap.ker (aeval g f)) = n →
      LinearMap.charpoly g = f ^ m → φ g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hn hg
    by_cases htop : LinearMap.ker (aeval g f) = ⊤
    · exact h0 g hg (LinearMap.ker_eq_top.mp htop)
    have hCH : ∀ g' : Module.End F V, LinearMap.charpoly g' = f ^ m → aeval g' (f ^ m) = 0 := by
      intro g' hg'
      rw [← hg']
      exact LinearMap.aeval_self_charpoly g'
    have hbot : LinearMap.ker (aeval g f) ≠ ⊥ := by
      intro hb
      have hinj : Function.Injective (aeval g f : Module.End F V) := LinearMap.ker_eq_bot.mp hb
      have hinj' : Function.Injective ((aeval g f) ^ m : Module.End F V) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate m
      rw [← map_pow, hCH g hg] at hinj'
      apply htop
      rw [hb, eq_comm, eq_bot_iff]
      intro x _
      exact (Submodule.mem_bot F).mpr (hinj' (by simp))
    have hinv : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc : aeval g f * g = g * aeval g f := by
        have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
        simpa using this
      have := congrArg (fun k : Module.End F V => k x) hc
      simpa [hx] using this
    have hsum := hpr _ hbot htop g hinv
    have hfin : (nilRad (LinearMap.ker (aeval g f))).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hterm : ∀ h ∈ hfin.toFinset, φ (g + h) =
        if LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) then φ g else 0 := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      have hcp : LinearMap.charpoly (g + h) = f ^ m := by
        rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V _ g hinv).2 h hh, hg]
      obtain ⟨hle, heq⟩ := GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle F V g h f hh
      split_ifs with hc
      · obtain ⟨e, he⟩ := GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g (g + h) f m hf (hCH g hg) (hCH _ hcp) (heq hc)
        rw [← he, hcl e g]
      · have hlt : LinearMap.ker (aeval g f) < LinearMap.ker (aeval (g + h) f) :=
          lt_of_le_of_ne hle (Ne.symm hc)
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt
        have h2 := Submodule.finrank_le (LinearMap.ker (aeval (g + h) f))
        exact ih _ (by omega) (g + h) rfl hcp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    refine (mul_eq_zero.mp hsum).resolve_left ?_
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨0, ?_⟩
    simp [nilRad]
  intro g hg
  exact key _ g rfl hg

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) = s (LinearMap.charpoly (g.restrict hg)) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_le | exact GlobalTheory.CuspGL.finsum_psi_le | (intros; apply GlobalTheory.CuspGL.finsum_psi_le <;> assumption)
end
