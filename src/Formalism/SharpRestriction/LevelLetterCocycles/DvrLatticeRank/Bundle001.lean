module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankInverseBounds

open Module
open scoped Classical

variable {O V : Type*} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]

def Inv (γ : V →ₗ[O] V) (K' P : Submodule O V) : Submodule O V :=
  P ⊓ K'.comap (γ - LinearMap.id)

abbrev InvQ (γ : V →ₗ[O] V) (K' P : Submodule O V) : Type _ :=
  ↥(Inv γ K' P) ⧸ K'.comap (Inv γ K' P).subtype

abbrev Gr (P P' : Submodule O V) : Type _ := ↥P ⧸ P'.comap P.subtype

private theorem mem_Inv_iff_mem_and_sub_mem {γ : V →ₗ[O] V} {K' P : Submodule O V} {x : V} :
    x ∈ Inv γ K' P ↔ x ∈ P ∧ γ x - x ∈ K' := by
  first
  | exact Iff.rfl

theorem inv_mono (γ : V →ₗ[O] V) (K' : Submodule O V) {P P' : Submodule O V} (h : P' ≤ P) :
    Inv γ K' P' ≤ Inv γ K' P := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_Inv_iff_mem_and_sub_mem.mp hx
  exact mem_Inv_iff_mem_and_sub_mem.mpr ⟨h h1, h2⟩

theorem rank_eq_zero_of_smul {M : Type*} [AddCommGroup M] [Module O M] (a : O) (ha : a ≠ 0)
    (h : ∀ x : M, a • x = 0) : Module.rank O M = 0 := by
  first
  | exact rank_eq_zero_iff.mpr fun x => ⟨a, ha, h x⟩

theorem step (γ : V →ₗ[O] V) (K' : Submodule O V) (hK : ∀ x ∈ K', γ x ∈ K')
    (F0 F1 : Submodule O V) (c : O) (h10 : F1 ≤ F0) (hγ : ∀ x ∈ F0, γ x - c • x ∈ F1) :
    Module.rank O (InvQ γ K' F0) ≤ Module.rank O (InvQ γ K' F1) +
      (if c = 1 then Module.rank O (Gr F0 F1) else 0) := by
  have hle : Inv γ K' F1 ≤ Inv γ K' F0 := inv_mono γ K' h10
  let f : InvQ γ K' F1 →ₗ[O] InvQ γ K' F0 :=
    Submodule.mapQ (K'.comap (Inv γ K' F1).subtype)
      (K'.comap (Inv γ K' F0).subtype) (Submodule.inclusion hle) (by
        intro x hx
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
        exact hx)
  let π : ↥(Inv γ K' F0) →ₗ[O] InvQ γ K' F0 ⧸ LinearMap.range f :=
    (LinearMap.range f).mkQ ∘ₗ (K'.comap (Inv γ K' F0).subtype).mkQ
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨x, rfl⟩
  have key : ∀ x : ↥(Inv γ K' F0),
      (K'.comap (Inv γ K' F0).subtype).mkQ x ∈ LinearMap.range f → π x = 0 := by
    intro x hx
    simp only [π, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hquot : Module.rank O (InvQ γ K' F0 ⧸ LinearMap.range f) ≤
      (if c = 1 then Module.rank O (Gr F0 F1) else 0) := by
    split_ifs with hc1
    · let ψ : ↥(Inv γ K' F0) →ₗ[O] Gr F0 F1 :=
        (F1.comap F0.subtype).mkQ ∘ₗ Submodule.inclusion (fun y hy => (mem_Inv_iff_mem_and_sub_mem.mp hy).1)
      have hker : LinearMap.ker ψ ≤ LinearMap.ker π := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        have hxF1 : (x : V) ∈ F1 := by
          first
          | (simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
              Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx
             exact hx)
        apply key
        have hx1 : (x : V) ∈ Inv γ K' F1 :=
          mem_Inv_iff_mem_and_sub_mem.mpr ⟨hxF1, (mem_Inv_iff_mem_and_sub_mem.mp x.2).2⟩
        refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨x, hx1⟩, ?_⟩
        first
        | rfl
      let g : ↥(Inv γ K' F0) ⧸ LinearMap.ker ψ →ₗ[O]
          InvQ γ K' F0 ⧸ LinearMap.range f :=
        (LinearMap.ker ψ).liftQ π hker
      have hg : Function.Surjective g := by
        intro b
        obtain ⟨a, rfl⟩ := hπ b
        exact ⟨Submodule.Quotient.mk a, rfl⟩
      calc _ ≤ Module.rank O (↥(Inv γ K' F0) ⧸ LinearMap.ker ψ) :=
            LinearMap.rank_le_of_surjective g hg
        _ = Module.rank O (LinearMap.range ψ) := ψ.quotKerEquivRange.rank_eq
        _ ≤ Module.rank O (Gr F0 F1) := Submodule.rank_le _
    · apply le_of_eq
      apply rank_eq_zero_of_smul (c - 1) (sub_ne_zero.mpr hc1)
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      rw [← map_smul π]
      apply key
      obtain ⟨hxF0, hxK⟩ := mem_Inv_iff_mem_and_sub_mem.mp x.2
      have hmem : c • (x : V) - γ x ∈ Inv γ K' F1 := by
        refine mem_Inv_iff_mem_and_sub_mem.mpr ⟨?_, ?_⟩
        · rw [← neg_sub]
          exact F1.neg_mem (hγ _ hxF0)
        · have e : γ (c • (x : V) - γ x) - (c • (x : V) - γ x) = c • (γ x - x) - γ (γ x - x) := by
            simp only [map_sub, map_smul, smul_sub]
            abel
          rw [e]
          exact K'.sub_mem (K'.smul_mem c hxK) (hK _ hxK)
      refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
      have e1 : f (Submodule.Quotient.mk ⟨_, hmem⟩) =
          (Submodule.Quotient.mk (Submodule.inclusion hle ⟨_, hmem⟩) : InvQ γ K' F0) := by
        first
        | rfl
      rw [e1, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      convert K'.neg_mem hxK using 1
      simp only [map_sub, map_smul, Submodule.subtype_apply, Submodule.coe_inclusion, sub_smul,
        one_smul]
      abel
  calc Module.rank O (InvQ γ K' F0)
      = Module.rank O (InvQ γ K' F0 ⧸ LinearMap.range f) +
          Module.rank O (LinearMap.range f) := by
        exact (rank_quotient_add_rank_of_isDomain _).symm
    _ ≤ (if c = 1 then Module.rank O (Gr F0 F1) else 0) +
          Module.rank O (InvQ γ K' F1) :=
        add_le_add hquot (by
          first
          | exact LinearMap.rank_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          | exact LinearMap.rank_le_of_surjective f.rangeRestrict (fun y => by
              obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
              exact ⟨x, Subtype.ext hx⟩))
    _ = _ := add_comm _ _

end Formalism.MainNotions.N.Ln34.RankInverseBounds

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Module

variable {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X]

theorem finrank_map_mkQ (Oth S : Submodule LL X) (h : Disjoint S Oth) :
    finrank LL ↥(S.map Oth.mkQ) = finrank LL ↥S := by
  have hinj : Function.Injective (Oth.mkQ ∘ₗ S.subtype) := by
    intro x y hxy
    have hxy' : Oth.mkQ (x : X) = Oth.mkQ (y : X) := hxy
    simp only [Submodule.mkQ_apply] at hxy'
    rw [Submodule.Quotient.eq] at hxy'
    have h0 : (x : X) - y = 0 := (Submodule.disjoint_def.mp h) _ (sub_mem x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp h0)
  have hr : LinearMap.range (Oth.mkQ ∘ₗ S.subtype) = S.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  calc finrank LL ↥(S.map Oth.mkQ)
        = finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ S.subtype)) := by rw [hr]
    _ = finrank LL ↥S := ((LinearEquiv.ofInjective _ hinj).finrank_eq).symm

theorem match_fil (I D Oth : Submodule LL X) [FiniteDimensional LL ↥I] [FiniteDimensional LL ↥D]
    (hDO : Disjoint D Oth) (hdim : finrank LL ↥I = finrank LL ↥D) (hDI : D ≤ I ⊔ Oth) :
    Disjoint I Oth ∧ ∀ F : Submodule LL X, F ≤ D → finrank LL ↥(I ⊓ (F ⊔ Oth)) = finrank LL ↥F := by
  have hsupmap : ∀ P : Submodule LL X, (P ⊔ Oth).map Oth.mkQ = P.map Oth.mkQ := by
    intro P
    first
      | rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
      | simp [Submodule.map_sup]
  have hmap : D.map Oth.mkQ ≤ I.map Oth.mkQ := by
    calc D.map Oth.mkQ ≤ (I ⊔ Oth).map Oth.mkQ := Submodule.map_mono hDI
      _ = I.map Oth.mkQ := hsupmap I
  haveI hfin : FiniteDimensional LL ↥(I.map Oth.mkQ) := by
    first
      | infer_instance
      | exact Module.Finite.map I Oth.mkQ
  have hDmap : finrank LL ↥(D.map Oth.mkQ) = finrank LL ↥D :=
    finrank_map_mkQ Oth D hDO
  have hIle : finrank LL ↥(I.map Oth.mkQ) ≤ finrank LL ↥I := by
    first
      | exact Submodule.finrank_map_le _ _
      | apply Submodule.finrank_map_le
  have hle2 : finrank LL ↥(D.map Oth.mkQ) ≤ finrank LL ↥(I.map Oth.mkQ) := by
    first
      | exact Submodule.finrank_le_finrank_of_le hmap
      | exact LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hmap)
  have hIeq : finrank LL ↥(I.map Oth.mkQ) = finrank LL ↥I := by omega
  have hrI : LinearMap.range (Oth.mkQ ∘ₗ I.subtype) = I.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Oth.mkQ ∘ₗ I.subtype)
  have hr' : finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ I.subtype)) = finrank LL ↥I := by
    rw [hrI]; exact hIeq
  have hk : finrank LL ↥(LinearMap.ker (Oth.mkQ ∘ₗ I.subtype)) = 0 := by omega
  have hkb : LinearMap.ker (Oth.mkQ ∘ₗ I.subtype) = ⊥ := by
    first
      | exact Submodule.finrank_eq_zero.mp hk
      | exact (Submodule.finrank_eq_zero (S := LinearMap.ker (Oth.mkQ ∘ₗ I.subtype))).mp hk
      | (haveI := Module.finrank_zero_iff.mp hk; exact Submodule.eq_bot_of_subsingleton)
  have hinj : Function.Injective (Oth.mkQ ∘ₗ I.subtype) := LinearMap.ker_eq_bot.mp hkb
  have hdisj : Disjoint I Oth := by
    rw [Submodule.disjoint_def]
    intro x hxI hxO
    have h1 : (Oth.mkQ ∘ₗ I.subtype) ⟨x, hxI⟩ = (Oth.mkQ ∘ₗ I.subtype) 0 := by
      rw [map_zero]
      show Oth.mkQ x = 0
      first
        | (rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxO)
        | simp [hxO]
    have h2 := hinj h1
    first
      | exact congrArg Subtype.val h2
      | simpa using congrArg Subtype.val h2
  refine ⟨hdisj, fun F hF => ?_⟩
  have hFO : Disjoint F Oth := hDO.mono_left hF
  have hJO : Disjoint (I ⊓ (F ⊔ Oth)) Oth := hdisj.mono_left inf_le_left
  have heq : (I ⊓ (F ⊔ Oth)).map Oth.mkQ = F.map Oth.mkQ := by
    apply le_antisymm
    · calc (I ⊓ (F ⊔ Oth)).map Oth.mkQ ≤ (F ⊔ Oth).map Oth.mkQ := Submodule.map_mono inf_le_right
        _ = F.map Oth.mkQ := hsupmap F
    · intro y hy
      obtain ⟨f, hfF, rfl⟩ := Submodule.mem_map.mp hy
      have hfD : Oth.mkQ f ∈ I.map Oth.mkQ := hmap (Submodule.mem_map.mpr ⟨f, hF hfF, rfl⟩)
      obtain ⟨i, hiI, hif⟩ := Submodule.mem_map.mp hfD
      have hsub : i - f ∈ Oth := by
        simp only [Submodule.mkQ_apply] at hif
        exact (Submodule.Quotient.eq Oth).mp hif
      have h3 : f + (i - f) ∈ F ⊔ Oth := Submodule.add_mem_sup hfF hsub
      have hi : i ∈ F ⊔ Oth := by
        first
          | simpa using h3
          | (rw [add_sub_cancel] at h3; exact h3)
      exact Submodule.mem_map.mpr ⟨i, Submodule.mem_inf.mpr ⟨hiI, hi⟩, hif⟩
  calc finrank LL ↥(I ⊓ (F ⊔ Oth))
        = finrank LL ↥((I ⊓ (F ⊔ Oth)).map Oth.mkQ) :=
          (finrank_map_mkQ Oth _ hJO).symm
    _ = finrank LL ↥(F.map Oth.mkQ) := by rw [heq]
    _ = finrank LL ↥F := finrank_map_mkQ Oth F hFO

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

section

namespace DualFramesAlt.Val

open scoped BigOperators

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

private theorem prime_prime_padicInt : Prime (p : ℤ_[p]) := PadicInt.irreducible_p.prime

private theorem not_prime_dvd_padicInt_unit (w : ℤ_[p]ˣ) : ¬ (p : ℤ_[p]) ∣ (w : ℤ_[p]) :=
  fun h => prime_prime_padicInt.not_unit (isUnit_of_dvd_unit h (Units.isUnit _))

lemma emult_eq_valuation {x : ℤ_[p]} (hx : x ≠ 0) :
    emultiplicity (p : ℤ_[p]) x = x.valuation := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [emultiplicity_mul hP, emultiplicity_eq_zero.mpr (not_prime_dvd_padicInt_unit _), zero_add,
    emultiplicity_pow_self_of_prime hP]

lemma valuation_eq_of_emult {x : ℤ_[p]} {n : ℕ} (h : emultiplicity (p : ℤ_[p]) x = n) :
    x.valuation = n := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [emult_eq_valuation hx] at h
  exact_mod_cast h

lemma emult_of_valuation_one {x : ℤ_[p]} (hx : x ≠ 0) (h1 : x.valuation = 1) :
    emultiplicity (p : ℤ_[p]) x = 1 := by
  rw [emult_eq_valuation hx, h1, Nat.cast_one]

lemma p_dvd_of_valuation_one {x : ℤ_[p]} (hx : x ≠ 0) (h1 : x.valuation = 1) :
    (p : ℤ_[p]) ∣ x := by
  have h := emult_of_valuation_one hx h1
  by_contra hn
  rw [emultiplicity_eq_zero.mpr hn] at h
  exact zero_ne_one h

lemma not_dvd_of_dvd_sub_one {u : ℤ_[p]} (h : (p : ℤ_[p]) ∣ u - 1) : ¬ (p : ℤ_[p]) ∣ u := by
  intro hu
  have h1 : (p : ℤ_[p]) ∣ 1 := by simpa using dvd_sub hu h
  exact prime_prime_padicInt.not_unit (isUnit_of_dvd_one h1)

lemma dvd_of_natCast_dvd_natCast {m : ℕ} (h : (p : ℤ_[p]) ∣ (m : ℤ_[p])) : p ∣ m := by
  have h1 := (PadicInt.norm_lt_one_iff_dvd _).mpr h
  have h2 : ‖((m : ℤ) : ℤ_[p])‖ < 1 := by simpa using h1
  exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h2)

lemma emult_pow_sub_one (hodd : p ≠ 2) {u : ℤ_[p]} (hdvd : (p : ℤ_[p]) ∣ u - 1)
    (he : emultiplicity (p : ℤ_[p]) (u - 1) = 1) {k : ℕ} (hk : k ≠ 0) :
    emultiplicity (p : ℤ_[p]) (u ^ k - 1) = ((1 + padicValNat p k : ℕ) : ℕ∞) := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  have hp1 : Odd p := hp.out.odd_of_ne_two hodd
  have hu : ¬ (p : ℤ_[p]) ∣ u := not_dvd_of_dvd_sub_one hdvd
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.out.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hval : padicValNat p (p ^ e * m) = e := by
    rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  have h1 : emultiplicity (p : ℤ_[p]) (u ^ p ^ e - 1 ^ p ^ e) = 1 + e := by
    rw [emultiplicity_pow_prime_pow_sub_pow_prime_pow hP hp1 hdvd hu e, he]
  rw [one_pow] at h1
  have hx : ¬ (p : ℤ_[p]) ∣ u ^ p ^ e := fun h => hu (hP.dvd_of_dvd_pow h)
  have hxy : (p : ℤ_[p]) ∣ u ^ p ^ e - 1 := by
    have h2 := sub_dvd_pow_sub_pow u 1 (p ^ e)
    rw [one_pow] at h2
    exact hdvd.trans h2
  have hmR : ¬ (p : ℤ_[p]) ∣ (m : ℤ_[p]) := fun h => hm (dvd_of_natCast_dvd_natCast h)
  have key : emultiplicity (p : ℤ_[p]) ((u ^ p ^ e) ^ m - 1 ^ m)
      = emultiplicity (p : ℤ_[p]) (u ^ p ^ e - 1) :=
    emultiplicity_pow_sub_pow_of_prime hP hxy hx hmR
  rw [one_pow, ← pow_mul] at key
  rw [key, h1, hval]
  norm_cast

lemma emult_zpow_sub_one (hodd : p ≠ 2) (u : ℤ_[p]ˣ) (hdvd : (p : ℤ_[p]) ∣ (u : ℤ_[p]) - 1)
    (he : emultiplicity (p : ℤ_[p]) ((u : ℤ_[p]) - 1) = 1) {i : ℤ} (hi : i ≠ 0) :
    emultiplicity (p : ℤ_[p]) (((u ^ i : ℤ_[p]ˣ) : ℤ_[p]) - 1)
      = ((1 + padicValNat p i.natAbs : ℕ) : ℕ∞) := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hi (by simp)
    have hab : ((n : ℤ)).natAbs = n := by simp
    rw [hab, zpow_natCast, Units.val_pow_eq_pow_val]
    exact emult_pow_sub_one hodd hdvd he hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hi (by simp)
    have hab : (-(n : ℤ)).natAbs = n := by simp
    have h1 : (((u ^ n)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
    have hrw : (((u ^ (-(n : ℤ))) : ℤ_[p]ˣ) : ℤ_[p]) - 1
        = (((u ^ n)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * -((u : ℤ_[p]) ^ n - 1) := by
      rw [zpow_neg, zpow_natCast]
      linear_combination h1
    rw [hab, hrw, emultiplicity_mul hP, emultiplicity_eq_zero.mpr (not_prime_dvd_padicInt_unit _), zero_add,
      emultiplicity_neg]
    exact emult_pow_sub_one hodd hdvd he hn

end SlopeTestRemainingChoices

theorem val_prod_one_sub_zpow {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (u : ℤ_[p]ˣ) (hu1 : ((u : ℤ_[p]) - 1).valuation = 1) (hu0 : (u : ℤ_[p]) - 1 ≠ 0)
    (Ω : Finset ℤ) (h0 : (0 : ℤ) ∉ Ω) :
    (∏ i ∈ Ω, (1 - ((u ^ i : ℤ_[p]ˣ) : ℤ_[p]))).valuation
      = ∑ i ∈ Ω, (1 + padicValNat p i.natAbs) := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  have hdvd := p_dvd_of_valuation_one hu0 hu1
  have he := emult_of_valuation_one hu0 hu1
  have key : ∀ i ∈ Ω, emultiplicity (p : ℤ_[p]) (1 - ((u ^ i : ℤ_[p]ˣ) : ℤ_[p]))
      = ((1 + padicValNat p i.natAbs : ℕ) : ℕ∞) := by
    intro i hi
    rw [← neg_sub, emultiplicity_neg]
    exact emult_zpow_sub_one hodd u hdvd he (fun h => h0 (h ▸ hi))
  apply valuation_eq_of_emult
  rw [Finset.emultiplicity_prod hP, Finset.sum_congr rfl key, Nat.cast_sum]

end DualFramesAlt.Val
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.AdicCompletionMax

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_eq_max_pow {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.span {p} = IsLocalRing.maximalIdeal O ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (mt Ideal.span_singleton_eq_bot.mp hp0) hϖ
  refine ⟨n, Nat.one_le_iff_ne_zero.mpr ?_, ?_⟩
  · rintro rfl
    rw [pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at hn
    exact absurd hn ((IsLocalRing.mem_maximalIdeal _).1 hpm)
  · rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

private theorem isAdicComplete_of_isAdicComplete_pow {J : Ideal O} {k : ℕ} (hk : 1 ≤ k)
    (h : IsAdicComplete (J ^ k) O) : IsAdicComplete J O := by
  have key : ∀ n : ℕ, (J ^ k) ^ n = J ^ (k * n) := fun n => (pow_mul J k n).symm
  have hkn : ∀ n : ℕ, n ≤ k * n := fun n => by simpa using Nat.mul_le_mul hk (le_refl n)
  have hle : ∀ {a b : ℕ}, a ≤ b → J ^ b • (⊤ : Submodule O O) ≤ J ^ a • ⊤ :=
    fun hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [key]
    exact hx (k * n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => f (k * n))
      (fun {a b} hab => by
        rw [key]
        exact hf (Nat.mul_le_mul (le_refl k) hab))
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (k * n) [SMOD (J ^ n • ⊤ : Submodule O O)] := hf (hkn n)
    have h2 : f (k * n) ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := by
      have h3 := hL n
      rw [key] at h3
      exact SModEq.mono (hle (hkn n)) h3
    exact h1.trans h2

theorem isAdicComplete_max {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O)
    [h : IsAdicComplete (Ideal.span {p}) O] : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  obtain ⟨k, hk, hkeq⟩ := span_eq_max_pow hp0 hpm
  rw [hkeq] at h
  exact isAdicComplete_of_isAdicComplete_pow hk h

end Formalism.MainNotions.N.Ln34.AdicCompletionMax
end
end
