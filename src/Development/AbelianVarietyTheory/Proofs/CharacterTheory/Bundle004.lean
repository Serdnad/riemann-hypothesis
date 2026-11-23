module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.GroupTheory.PGroup
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

section

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

section
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W) : Representation K G W where
  toFun g := e.conj (ρ g)
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp

theorem transportRep_apply (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

theorem character_transportRep [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) :
    (transportRep ρ e).character g = ρ.character g :=
  LinearMap.trace_conj' (ρ g) e

def transportSubOrderIso (ρ : Representation K G V) (e : V ≃ₗ[K] W) :
    Subrepresentation (transportRep ρ e) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule.comap e.toLinearMap, fun g v hv => by
    have := S.apply_mem_toSubmodule g (v := e v) hv
    simpa [transportRep_apply] using this⟩
  invFun S := ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
    have := S.apply_mem_toSubmodule g (v := e.symm w) hw
    simpa [transportRep_apply] using this⟩
  left_inv S := by ext w; simp
  right_inv S := by ext v; simp
  map_rel_iff' {S T} := by
    constructor
    · intro h w hw
      have h1 : e.symm w ∈ S.toSubmodule.comap e.toLinearMap := by
        show e (e.symm w) ∈ S.toSubmodule
        rw [e.apply_symm_apply]; exact hw
      have h2 : e (e.symm w) ∈ T.toSubmodule := h h1
      rw [e.apply_symm_apply] at h2
      exact h2
    · intro h v hv
      exact h (show e v ∈ S from hv)

end

theorem _root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V),
      _root_.GlobalTheory.BI.IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧
        (ρ.IsIrreducible →
          _root_.GlobalTheory.BI.IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  intro K L _ _ _ G _ V _ _ _ ρ
  set e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  have hchar : ∀ g, (_root_.GlobalTheory.BI.transportRep ρ e).character g = ρ.character g := by
    intro g
    exact LinearMap.trace_conj' (ρ g) e
  refine ⟨⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, fun g => ?_⟩, fun hρ => ?_⟩
  · rw [hchar]
  · refine ⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, ?_, fun g => ?_⟩
    · have hs : IsSimpleOrder (Subrepresentation ρ) := hρ
      exact (_root_.GlobalTheory.BI.transportSubOrderIso ρ e).isSimpleOrder_iff.mpr hs
    · rw [hchar]

end GlobalTheory.BI
end
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem character_pairing_eq_finrank_hom (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    (G : Type) [Group G] [Finite G] {n m : ℕ} (ρ : Representation K G (Fin n → K))
    (σ : Representation K G (Fin m → K)) :
    pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g))
      = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hK := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  rw [map_natCast] at hK
  rw [← hK]

  simp only [pair, finsum_eq_sum_of_fintype, map_mul, map_inv₀, map_natCast, map_sum]

theorem pair_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  intro K L _ _ _ _ _ G _ _
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    simp only [pair, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      mul_add]
  · rintro a b ⟨n, ρ, hρ⟩ ⟨m, σ, hσ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap σ ρ), ?_⟩
    rw [show a = fun g => algebraMap K L (ρ.character g) from funext hρ,
      show b = fun g => algebraMap K L (σ.character g) from funext hσ]
    exact character_pairing_eq_finrank_hom K L G σ ρ
  · rintro φ ⟨n, ρ, hirr, hρ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap ρ ρ), ?_, ?_⟩
    · have : IsSimpleModule (MonoidAlgebra K G) ρ.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra K G) _
      obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v ≠ 0 := exists_ne (0 : ρ.asModule)
      have : Nontrivial (Representation.IntertwiningMap ρ ρ) :=
        ⟨⟨Representation.IntertwiningMap.id ρ, 0, fun h => hv (by
          have hv0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
          rwa [Representation.IntertwiningMap.id_apply, Representation.IntertwiningMap.coe_zero,
            Pi.zero_apply] at hv0)⟩⟩
      have : Module.Finite K (Representation.IntertwiningMap ρ ρ) :=
        Module.Finite.equiv (Representation.invariantsEquivIntertwiningMap ρ ρ)
      exact Module.finrank_pos
    · rw [show φ = fun g => algebraMap K L (ρ.character g) from funext hρ]
      exact character_pairing_eq_finrank_hom K L G ρ ρ
  · intro a b
    simp only [pair, finsum_eq_sum_of_fintype]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])
end GlobalTheory.BI
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem exists_representation_character_eq_add (K : Type) [Field K] (G : Type) [Group G]
    (n m : ℕ) (ρ : Representation K G (Fin n → K)) (σ : Representation K G (Fin m → K)) :
    ∃ τ : Representation K G (Fin (n + m) → K),
      ∀ g, τ.character g = ρ.character g + σ.character g := by
  let e : ((Fin n → K) × (Fin m → K)) ≃ₗ[K] (Fin (n + m) → K) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) K K).symm ≪≫ₗ
      LinearEquiv.funCongrLeft K K finSumFinEquiv.symm
  refine ⟨{ toFun := fun g => e.conj ((ρ g).prodMap (σ g)), map_one' := ?_, map_mul' := ?_ },
    fun g => ?_⟩
  · simp only [map_one, LinearMap.prodMap_one]
    exact e.conj_id
  · intro g h
    simp only [map_mul]
    rw [← LinearMap.prodMap_mul]
    exact e.conj_comp _ _
  · simp only [Representation.character]
    show LinearMap.trace K _ (e.conj _) = _
    rw [LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem _root_.GlobalTheory.BI.isChar_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (G : Type) [Group G], _root_.GlobalTheory.BI.IsChar K L (0 : G → L) ∧
      ∀ a b : G → L, _root_.GlobalTheory.BI.IsChar K L a → _root_.GlobalTheory.BI.IsChar K L b →
        _root_.GlobalTheory.BI.IsChar K L (a + b) := by
  intro K L _ _ _ G _
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.BI.IsChar
    refine ⟨0, 1, fun g => ?_⟩
    simp [Representation.character]
  · intro a b ha hb
    unfold _root_.GlobalTheory.BI.IsChar at ha hb ⊢
    obtain ⟨n, ρ, hρ⟩ := ha
    obtain ⟨m, σ, hσ⟩ := hb
    obtain ⟨τ, hτ⟩ := exists_representation_character_eq_add K G n m ρ σ
    refine ⟨n + m, τ, fun g => ?_⟩
    rw [Pi.add_apply, hρ g, hσ g, hτ g, map_add (f := _)]

end GlobalTheory.BI
end

section

open GlobalTheory.BI
namespace GlobalTheory

theorem isChar_restrict_conj_one : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  intro K L _ _ _ G _ χ hχ
  obtain ⟨n, ρ, hρ⟩ := hχ
  refine ⟨?_, ?_, n, ?_, ?_⟩
  · intro H _ f
    exact ⟨n, ρ.comp f, fun h => hρ (f h)⟩
  · intro g x
    rw [hρ, hρ]
    have hc := ρ.char_conj g x⁻¹
    rw [inv_inv] at hc
    rw [hc]
  · rw [hρ, Representation.char_one]
    simp
  · rintro rfl
    funext g
    have hz : ρ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hρ, Pi.zero_apply, Representation.character, hz, map_zero, map_zero]
end GlobalTheory
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.commute_all : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), _root_.GlobalTheory.BI.AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by
  intro G _ _ M _ φ hG hyp
  obtain ⟨p, hp, A, hAn, hAc, hpow⟩ := hG
  let Z : Subgroup G :=
    { carrier := {b | ∀ g, φ b * φ g = φ g * φ b}
      mul_mem' := fun {x y} hx hy g => by
        rw [map_mul, mul_assoc, hy g, ← mul_assoc, hx g, mul_assoc]
      one_mem' := fun g => by simp
      inv_mem' := fun {x} hx g => by
        have h1 : φ x⁻¹ * φ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h2 : φ x * φ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc φ x⁻¹ * φ g = φ x⁻¹ * φ g * (φ x * φ x⁻¹) := by rw [h2, mul_one]
          _ = φ x⁻¹ * (φ x * φ g) * φ x⁻¹ := by rw [hx g]; simp only [mul_assoc]
          _ = φ g * φ x⁻¹ := by rw [← mul_assoc, h1, one_mul] }
  have hZ : ∀ b, b ∈ Z ↔ ∀ g, φ b * φ g = φ g * φ b := fun b => Iff.rfl
  have hZn : Z.Normal := ⟨fun b hb g => by
    rw [hZ] at hb ⊢
    intro h
    have e : φ (g * b * g⁻¹) = φ b := by
      rw [map_mul, map_mul, ← hb g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [e]
    exact hb h⟩
  have hAZ : A ≤ Z := fun a ha => (hZ a).2 (hyp A hAn (fun x hx y hy => by
    rw [← map_mul, ← map_mul, hAc x hx y hy]) a ha)
  suffices hZtop : Z = ⊤ by
    intro a b
    exact (hZ a).1 (hZtop ▸ Subgroup.mem_top a) b
  by_contra hne
  have hP : IsPGroup p (G ⧸ Z) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := hpow g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hAZ hk⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (G ⧸ Z) := QuotientGroup.nontrivial_iff.mpr hne
  haveI := hP.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (G ⧸ Z))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (z : G ⧸ Z)
  have hzc : ∀ q : G ⧸ Z, ∀ i : ℤ, q * (z : G ⧸ Z) ^ i = (z : G ⧸ Z) ^ i * q := fun q i =>
    ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i)) q)
  let C : Subgroup G := (Subgroup.zpowers (z : G ⧸ Z)).comap (QuotientGroup.mk' Z)
  have hmemC : ∀ c ∈ C, ∃ i : ℤ, ∃ b ∈ Z, c = g ^ i * b := by
    intro c hc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine ⟨i, (g ^ i)⁻¹ * c, ?_, by group⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hg]
    exact hi
  have hCn : C.Normal := ⟨fun c hc h => by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hi ⊢
    rw [← hi, hzc, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hCc : ∀ x ∈ C, ∀ y ∈ C, φ x * φ y = φ y * φ x := by
    intro x hx y hy
    obtain ⟨i, b1, hb1, rfl⟩ := hmemC x hx
    obtain ⟨j, b2, hb2, rfl⟩ := hmemC y hy
    rw [hZ] at hb1 hb2
    have key : ∀ (i j : ℤ) (b1 b2 : G), (∀ g, φ b1 * φ g = φ g * φ b1) →
        φ (g ^ i * b1) * φ (g ^ j * b2) = φ (g ^ (i + j)) * (φ b1 * φ b2) := by
      intro i j b1 b2 hb1
      rw [map_mul, map_mul, mul_assoc, ← mul_assoc (φ b1), hb1, mul_assoc, ← mul_assoc,
        ← map_mul, ← zpow_add]
    rw [key i j b1 b2 hb1, key j i b2 b1 hb2, add_comm, hb1 b2]
  have hgC : g ∈ C := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp [hg]⟩
  have hgZ : g ∈ Z := (hZ g).2 (hyp C hCn hCc g hgC)
  apply hz1
  apply Subtype.ext
  rw [← hg]
  exact (QuotientGroup.eq_one_iff g).mpr hgZ

end GlobalTheory.BI
end

section

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem subgroupFunctionExtendByZero_conj_of_mem {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L)
    (hψ : ∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) (a : G) (y : H) :
    ext0 H ψ ((y : G)⁻¹ * a * y) = ext0 H ψ a := by
  unfold ext0
  by_cases ha : a ∈ H
  · have h1 : (y : G)⁻¹ * a * y ∈ H := H.mul_mem (H.mul_mem (H.inv_mem y.2) ha) y.2
    rw [dite_eq_left ha, dite_eq_left h1]
    exact hψ ⟨a, ha⟩ y
  · have h1 : ¬ (y : G)⁻¹ * a * y ∈ H := by
      intro h
      apply ha
      have h2 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem y.2 h) (H.inv_mem y.2)
      have h3 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ = a := by group
      rwa [h3] at h2
    rw [dite_eq_right ha, dite_eq_right h1]

theorem out_mul_bijective {G : Type} [Group G] (H : Subgroup G) :
    Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * (p.2 : G)) := by
  constructor
  · rintro ⟨q, y⟩ ⟨q', y'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : ((q.out * (y : G) : G) : G ⧸ H) = ((q'.out * (y' : G) : G) : G ⧸ H) := by rw [h]
      rw [QuotientGroup.mk_mul_of_mem _ y.2, QuotientGroup.mk_mul_of_mem _ y'.2,
        QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    subst hq
    have : y = y' := Subtype.ext (mul_left_cancel h)
    rw [this]
  · intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨((x : G ⧸ H), y⁻¹), ?_⟩
    simp [hy]

theorem ind_eq_finsum_cosets : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  intro L _ _ G _ _ H ψ hψ g
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (G ⧸ H)
  have := Fintype.ofFinite H
  have hc : (Nat.card H : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold ind
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← (out_mul_bijective H).sum_comp (fun x : G => ext0 H ψ (x⁻¹ * g * x)), Fintype.sum_prod_type]
  have h1 : ∀ q : G ⧸ H, ∑ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
      = (Nat.card H : L) * ext0 H ψ (q.out⁻¹ * g * q.out) := by
    intro q
    have h2 : ∀ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
        = ext0 H ψ (q.out⁻¹ * g * q.out) := by
      intro y
      rw [← subgroupFunctionExtendByZero_conj_of_mem H ψ hψ (q.out⁻¹ * g * q.out) y]
      congr 1
      group
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp only [h1]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.BI
end
end

section

namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.AbByP.subgroup :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by
  intro G _ T h
  unfold _root_.GlobalTheory.BI.AbByP at h ⊢
  obtain ⟨p, hp, A, hA, hcomm, hpow⟩ := h
  haveI := hA
  refine ⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm _ ha _ hb)
  · intro g
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩

end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI


open Polynomial in
theorem _root_.GlobalTheory.BI.char_coset_sum_eq_zero :
    ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ χ → ∀ H : Subgroup G,
      ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  intro G _ _ χ hχc H hH g
  obtain ⟨n, ρ, hρ⟩ := hχc
  have := Fintype.ofFinite H
  have hχ : ∀ x, χ x = LinearMap.trace ℂ _ (ρ x) := fun x => by
    simp [hρ, Representation.character]
  rw [finsum_eq_sum_of_fintype] at hH ⊢
  simp only [hχ] at hH ⊢

  rw [← map_sum] at hH
  set S : Module.End ℂ (Fin n → ℂ) := ∑ u : H, ρ u with hS
  have habs : ∀ v : H, ρ v * S = S := by
    intro v
    rw [hS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
    simp [map_mul]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hSS : S * S = (Fintype.card H : ℂ) • S := by
    conv_lhs => arg 1; rw [hS]
    rw [Finset.sum_mul]
    simp only [habs, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hidem : IsIdempotentElem ((Fintype.card H : ℂ)⁻¹ • S) := by
    unfold IsIdempotentElem
    rw [smul_mul_smul, hSS, smul_smul]
    congr 1
    field_simp
  have hP : (Fintype.card H : ℂ)⁻¹ • S = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1 (by rw [map_smul, hH, smul_zero])
  have hS0 : S = 0 := by simpa [hcard] using hP
  have hsum : ∑ u : H, LinearMap.trace ℂ _ (ρ (g * u)) = LinearMap.trace ℂ _ (ρ g * S) := by

    rw [Finset.mul_sum, map_sum]
    simp [map_mul]
  rw [hsum, hS0, mul_zero, map_zero]

end GlobalTheory.BI
end
