module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle020
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.SplittingField.Construction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerFlat

theorem exists_unique_of_isPullback : ∀ {P R₁ R₂ R₀ : CommRingCat.{0}} (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → ∀ (x : R₁) (y : R₂), g₁.hom x = g₂.hom y → ∃! p : P, f₁.hom p = x ∧ f₂.hom p = y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h x y hxy
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, hp₁, hp₂⟩ := H.2.2 x y hxy
  exact ⟨p, ⟨hp₁, hp₂⟩, fun q hq => H.2.1 q p ⟨hq.1.trans hp₁.symm, hq.2.trans hp₂.symm⟩⟩

theorem isPushout_of_surjective_of_ker : ∀ {P R B C : CommRingCat.{0}} (a : P ⟶ B) (f : P ⟶ R) (c : B ⟶ C) (a' : R ⟶ C), a ≫ c = f ≫ a' → Function.Surjective f → Function.Surjective c → RingHom.ker c.hom = (RingHom.ker f.hom).map a.hom → IsPushout a f c a' := by
  intro P R B C a f c a' w hf hc hk
  have hw : ∀ p, c.hom (a.hom p) = a'.hom (f.hom p) := fun p => congr($(w) p)
  have key : ∀ (s : PushoutCocone a f), RingHom.ker c.hom ≤ RingHom.ker s.inl.hom := by
    intro s
    rw [hk, Ideal.map_le_iff_le_comap]
    intro p hp
    have e : s.inl.hom (a.hom p) = s.inr.hom (f.hom p) := congr($(s.condition) p)
    rw [Ideal.mem_comap, RingHom.mem_ker, e, (RingHom.mem_ker).mp hp, map_zero]
  let d : ∀ (s : PushoutCocone a f), C ⟶ s.pt := fun s =>
    CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker c.hom) s.inl.hom (fun x hx => key s hx)).comp
      (RingHom.quotientKerEquivOfSurjective hc).symm.toRingHom)
  have hd : ∀ (s : PushoutCocone a f) (b : B), (d s).hom (c.hom b) = s.inl.hom b := by
    intro s b
    have : (RingHom.quotientKerEquivOfSurjective hc).symm (c.hom b) = Ideal.Quotient.mk _ b := by
      apply (RingHom.quotientKerEquivOfSurjective hc).injective
      simp
    simp [d, this]
    rfl
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_⟩⟩
  · intro s; ext b; exact hd s b
  · intro s; ext r
    obtain ⟨p, rfl⟩ := hf r
    change (d s).hom (a'.hom (f.hom p)) = s.inr.hom (f.hom p)
    rw [← hw, hd]
    exact congr($(s.condition) p)
  · intro s m h1 _
    ext x
    obtain ⟨b, rfl⟩ := hc x
    rw [hd]
    exact congr($(h1) b)

theorem surjective_ker_of_isPushout : ∀ {R₁ R₀ B₁ B₀ : CommRingCat.{0}} (a₁ : R₁ ⟶ B₁) (g₁ : R₁ ⟶ R₀) (b₁ : B₁ ⟶ B₀) (a₀ : R₀ ⟶ B₀), IsPushout a₁ g₁ b₁ a₀ → Function.Surjective g₁ → Function.Surjective b₁ ∧ RingHom.ker b₁.hom = (RingHom.ker g₁.hom).map a₁.hom := by
  intro R₁ R₀ B₁ B₀ a₁ g₁ b₁ a₀ h hg
  let J : Ideal B₁ := (RingHom.ker g₁.hom).map a₁.hom
  let q : B₁ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let a' : R₀ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a₁.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom)
  have w : a₁ ≫ q = g₁ ≫ a' := by
    ext r
    have e0 : (RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r) = Ideal.Quotient.mk _ r := by
      apply (RingHom.quotientKerEquivOfSurjective hg).injective
      simp
    change Ideal.Quotient.mk J (a₁.hom r) = Ideal.quotientMap J a₁.hom Ideal.le_comap_map ((RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r))
    rw [e0]
    rfl
  have h' := isPushout_of_surjective_of_ker a₁ g₁ q a' w hg Ideal.Quotient.mk_surjective Ideal.mk_ker
  have e := IsPushout.inl_isoIsPushout_hom _ _ h h'
  let φ := h.isoIsPushout _ _ h'
  have hb : ∀ x, φ.hom.hom (b₁.hom x) = Ideal.Quotient.mk J x := fun x => congr($(e) x)
  have hinj : Function.Injective φ.hom.hom := fun x y hxy => by
    simpa using congrArg φ.inv.hom hxy
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ.hom.hom y)
    exact ⟨x, hinj (by rw [hb, hx])⟩
  · ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hb]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0; exact hinj (h0.trans (map_zero _).symm)

theorem ker_eq_map_of_fibre : ∀ (P R₁ R₂ B B₁ B₂ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing B₁] [CommRing B₂] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (a : P →+* B) (a₁ : R₁ →+* B₁) (a₂ : R₂ →+* B₂) (c₁ : B →+* B₁) (c₂ : B →+* B₂) (I₂ : Ideal R₂), c₁.comp a = a₁.comp f₁ → c₂.comp a = a₂.comp f₂ → Function.Surjective c₂ → (∀ k ∈ I₂, ∃ p : P, f₁ p = 0 ∧ f₂ p = k) → (∀ x : B, c₁ x = 0 → c₂ x = 0 → x = 0) → (∀ x : B, c₁ x = 0 → c₂ x ∈ I₂.map a₂) → RingHom.ker c₁ = (RingHom.ker f₁).map a := by
  intro P R₁ R₂ B B₁ B₂ _ _ _ _ _ _ f₁ f₂ a a₁ a₂ c₁ c₂ I₂ w₁ w₂ hc₂ hlift hj hker
  have w₁' : ∀ p, c₁ (a p) = a₁ (f₁ p) := fun p => by simpa using RingHom.congr_fun w₁ p
  have w₂' : ∀ p, c₂ (a p) = a₂ (f₂ p) := fun p => by simpa using RingHom.congr_fun w₂ p
  have claim : ∀ y ∈ I₂.map a₂, ∃ z ∈ (RingHom.ker f₁).map a, c₁ z = 0 ∧ c₂ z = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨p, hp1, hp2⟩ := hlift k hk
      exact ⟨a p, Ideal.mem_map_of_mem _ hp1, by rw [w₁', hp1, map_zero], by rw [w₂', hp2]⟩
    | zero => exact ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨z1, h1, e1, e1'⟩ := hu
      obtain ⟨z2, h2, e2, e2'⟩ := hv
      exact ⟨z1 + z2, Ideal.add_mem _ h1 h2, by rw [map_add (f := _), e1, e2, add_zero], by rw [map_add (f := _), e1', e2']⟩
    | smul s u _ hu =>
      obtain ⟨z, hz, e, e'⟩ := hu
      obtain ⟨t, rfl⟩ := hc₂ s
      exact ⟨t * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, e, mul_zero], by rw [map_mul, e', smul_eq_mul]⟩
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨z, hz, e, e'⟩ := claim _ (hker x hx)
    have h0 : x - z = 0 := hj _ (by rw [map_sub, hx, e, sub_zero]) (by rw [map_sub, e', sub_self])
    rw [sub_eq_zero.mp h0]
    exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, w₁', (RingHom.mem_ker).mp hp, map_zero]

theorem isNilpotent_ker_of_fibre : ∀ (P R₁ R₂ R₀ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing R₀] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (g₁ : R₁ →+* R₀) (g₂ : R₂ →+* R₀), g₁.comp f₁ = g₂.comp f₂ → RingHom.ker f₁ ⊓ RingHom.ker f₂ = ⊥ → IsNilpotent (RingHom.ker g₂) → IsNilpotent (RingHom.ker f₁) := by
  intro P R₁ R₂ R₀ _ _ _ _ f₁ f₂ g₁ g₂ w hj hn
  obtain ⟨n, hn⟩ := hn
  refine ⟨n + 1, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff]
  intro x hx
  have h1 : x ∈ RingHom.ker f₁ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
  have hle : (RingHom.ker f₁).map f₂ ≤ RingHom.ker g₂ := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, ← w, RingHom.comp_apply,
      (RingHom.mem_ker).mp hy, map_zero]
  have h2 : f₂ x ∈ (RingHom.ker g₂) ^ (n + 1) := by
    have := Ideal.mem_map_of_mem f₂ hx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle _ this
  rw [pow_succ, hn, Submodule.zero_eq_bot, Submodule.bot_mul] at h2
  have h3 : x ∈ RingHom.ker f₁ ⊓ RingHom.ker f₂ := ⟨h1, by simpa using h2⟩
  rw [hj] at h3
  exact h3

theorem mul_injective_of_flat : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf

theorem flat_quotient_of_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat

theorem schlessinger_flat : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  intro P R₁ R₂ R₀ B₁ B₂ B₀ B f₁ f₂ g₁ g₂ a₁ a₂ a₀ b₁ b₂ c₁ c₂ a hP hg₁ hg₂ hn₁ hn₂ hA₁ hA₂ hfl₁ hfl₂ hB hac₁ hac₂
  have eP := exists_unique_of_isPullback f₁ f₂ g₁ g₂ hP
  have eB := exists_unique_of_isPullback c₁ c₂ b₁ b₂ hB
  obtain ⟨hb₁, hkb₁⟩ := surjective_ker_of_isPushout a₁ g₁ b₁ a₀ hA₁ hg₁
  obtain ⟨hb₂, hkb₂⟩ := surjective_ker_of_isPushout a₂ g₂ b₂ a₀ hA₂ hg₂
  have wP : g₁.hom.comp f₁.hom = g₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hP.w]
  have wB : ∀ x, b₁.hom (c₁.hom x) = b₂.hom (c₂.hom x) := fun x => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hB.w]
  have w₁ : c₁.hom.comp a.hom = a₁.hom.comp f₁.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₁]
  have w₂ : c₂.hom.comp a.hom = a₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₂]
  have sf₁ : Function.Surjective f₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hg₂ (g₁.hom x)
    obtain ⟨p, hp, -⟩ := eP x y hy.symm
    exact ⟨p, hp.1⟩
  have sf₂ : Function.Surjective f₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hg₁ (g₂.hom y)
    obtain ⟨p, hp, -⟩ := eP x y hx
    exact ⟨p, hp.2⟩
  have sc₁ : Function.Surjective c₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hb₂ (b₁.hom x)
    obtain ⟨p, hp, -⟩ := eB x y hy.symm
    exact ⟨p, hp.1⟩
  have sc₂ : Function.Surjective c₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hb₁ (b₂.hom y)
    obtain ⟨p, hp, -⟩ := eB x y hx
    exact ⟨p, hp.2⟩
  have jB : ∀ x : B, c₁.hom x = 0 → c₂.hom x = 0 → x = 0 := fun x h1 h2 => by
    obtain ⟨p, -, hu⟩ := eB 0 0 (by simp)
    rw [hu x ⟨h1, h2⟩, hu 0 ⟨by simp, by simp⟩]
  have jP : RingHom.ker f₁.hom ⊓ RingHom.ker f₂.hom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨p, -, hu⟩ := eP 0 0 (by simp)
    rw [Ideal.mem_bot, hu x ⟨hx.1, hx.2⟩, hu 0 ⟨by simp, by simp⟩]
  have kc₁ : RingHom.ker c₁.hom = (RingHom.ker f₁.hom).map a.hom :=
    ker_eq_map_of_fibre P R₁ R₂ B B₁ B₂ f₁.hom f₂.hom a.hom a₁.hom a₂.hom c₁.hom c₂.hom (RingHom.ker g₂.hom) w₁ w₂ sc₂
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP 0 k (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk).symm)
        exact ⟨p, hp.1, hp.2⟩) jB
      (fun x hx => by
        rw [← hkb₂, RingHom.mem_ker, ← wB, hx, map_zero])
  have kc₂ : RingHom.ker c₂.hom = (RingHom.ker f₂.hom).map a.hom :=
    ker_eq_map_of_fibre P R₂ R₁ B B₂ B₁ f₂.hom f₁.hom a.hom a₂.hom a₁.hom c₂.hom c₁.hom (RingHom.ker g₁.hom) w₂ w₁ sc₁
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP k 0 (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk))
        exact ⟨p, hp.2, hp.1⟩) (fun x h2 h1 => jB x h1 h2)
      (fun x hx => by
        rw [← hkb₁, RingHom.mem_ker, wB, hx, map_zero])
  have nil₁ : IsNilpotent (RingHom.ker f₁.hom) :=
    isNilpotent_ker_of_fibre P R₁ R₂ R₀ f₁.hom f₂.hom g₁.hom g₂.hom wP jP hn₂
  refine ⟨?_, isPushout_of_surjective_of_ker a f₁ c₁ a₁ hac₁ sf₁ sc₁ kc₁, isPushout_of_surjective_of_ker a f₂ c₂ a₂ hac₂ sf₂ sc₂ kc₂⟩
  letI : Algebra P B := a.hom.toAlgebra
  change Module.Flat P B
  exact GlobalTheory.NilpotentFlat.flat_of_isNilpotent P (RingHom.ker f₁.hom) nil₁ B
    (flat_quotient_of_flat P R₁ B B₁ f₁.hom a₁.hom c₁.hom sf₁ sc₁ w₁ kc₁ hfl₁)
    (mul_injective_of_flat P R₂ B B₂ (RingHom.ker f₁.hom) f₂.hom a₂.hom c₂.hom sf₂ sc₂ w₂ kc₂ jP hfl₂)

end GlobalTheory.SchlessingerFlat
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem sum_eval_eq_of_sum_monomial_eq {ι S : Type} [Fintype ι] [Fintype S] (x y : ι → S → ℂ)
    (h : ∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) (Q : MvPolynomial S ℂ) :
    ∑ i, MvPolynomial.eval (x i) Q = ∑ i, MvPolynomial.eval (y i) Q := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h d]

theorem exists_perm_of_sum_monomial_eq :
    ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ),
      (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) →
      ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  classical
  intro ι S _ _ x y h
  have hcard : ∀ p : S → ℂ, Fintype.card {i // x i = p} = Fintype.card {i // y i = p} := by
    intro p
    obtain ⟨Q, hQ1, hQ0⟩ := exists_mvPolynomial_pick_point S
      (Finset.univ.image x ∪ Finset.univ.image y) p
    have key : ∀ z : ι → S → ℂ, (∀ i, z i ∈ Finset.univ.image x ∪ Finset.univ.image y) →
        ∑ i, MvPolynomial.eval (z i) Q = (Fintype.card {i // z i = p} : ℂ) := by
      intro z hz
      have : ∀ i, MvPolynomial.eval (z i) Q = if z i = p then 1 else 0 := by
        intro i
        split_ifs with hi
        · rw [hi, hQ1]
        · exact hQ0 _ (hz i) hi
      simp only [this]
      rw [Finset.sum_boole, Fintype.card_subtype]
    have h1 := key x (fun i => by simp)
    have h2 := key y (fun i => by simp)
    have h3 := sum_eval_eq_of_sum_monomial_eq x y h Q
    rw [h1, h2] at h3
    exact_mod_cast h3
  refine ⟨Equiv.ofFiberEquiv (f := x) (g := y) (fun p => Fintype.equivOfCardEq (hcard p)),
    fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

end GlobalTheory.QFam
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem exists_fin_enum_multiset {α : Type} : ∀ (n : ℕ) (M : Multiset α), Multiset.card M = n →
    ∃ u : Fin n → α, Multiset.map u Finset.univ.val = M := by
  classical
  intro n
  induction n with
  | zero =>
    intro M hM
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at hM
    subst hM; simp
  | succ n ih =>
    intro M hM
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card M)
    obtain ⟨u, hu⟩ := ih (M.erase a) (by rw [Multiset.card_erase_of_mem ha, hM]; rfl)
    refine ⟨Fin.cons a u, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu, Multiset.cons_erase ha]

theorem homogenize_multiset_prod_X_sub_C {E : Type} [Field E] (R : Multiset E) :
    Polynomial.homogenize (R.map fun a => Polynomial.X - Polynomial.C a).prod (Multiset.card R)
      = (R.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      Polynomial.homogenize_mul _ _ (m := 1) (n := Multiset.card R) ?_ ?_, ih]
    · simp [Multiset.map_cons]
    · exact Polynomial.natDegree_X_sub_C_le a
    · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

theorem binary_form_splits : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 →
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E)
      (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧
      ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A),
        ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) =
          algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by
  intro F _ m p hp
  classical
  set q : F[X] := ∑ i : Fin (m + 1), Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) with hq_def
  have hcoeff : ∀ i : Fin (m + 1), q.coeff i = p i := by
    intro i
    simp only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h.symm)
    · simp
  have hq0 : q ≠ 0 := by
    intro h; apply hp; funext i; rw [← hcoeff i, h]; simp
  have hdeg : q.natDegree ≤ m := by
    rw [hq_def]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro i _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)
  let E := q.SplittingField
  set Q : E[X] := q.map (algebraMap F E) with hQ_def
  have hsplit : Q.Splits := Polynomial.SplittingField.splits q
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero hq0
  have hQdeg : Q.natDegree = q.natDegree := Polynomial.natDegree_map _
  set d := Q.natDegree with hd
  have hdm : d ≤ m := hQdeg ▸ hdeg
  have hcard : Multiset.card Q.roots = d := hsplit.natDegree_eq_card_roots.symm
  let M : Multiset (E × E) := Q.roots.map (fun r => (-r, 1)) + Multiset.replicate (m - d) (1, 0)
  have hM : Multiset.card M = m := by simp [M, hcard]; omega
  obtain ⟨u, hu⟩ := exists_fin_enum_multiset m M hM
  refine ⟨E, inferInstance, inferInstance, inferInstance, Q.leadingCoeff, fun j => (u j).1,
    fun j => (u j).2, ?_, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hQ0
  · intro j
    have hj : u j ∈ M := by rw [← hu]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
    simp only [M, Multiset.mem_add, Multiset.mem_map, Multiset.mem_replicate] at hj
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    rcases hj with ⟨r, _, hr⟩ | ⟨_, hr⟩
    · rw [← hr] at h1; simp at h1
    · rw [hr] at h0; simp at h0
  · intro A _ _ x y
    have hform : Polynomial.homogenize Q m = ∑ i : Fin (m + 1),
        MvPolynomial.C (algebraMap F E (p i)) * (MvPolynomial.X 0 ^ (i : ℕ) *
          MvPolynomial.X 1 ^ (m - i)) := by

      rw [hQ_def, congrArg (Polynomial.map (algebraMap F E)) hq_def, Polynomial.map_sum, Polynomial.homogenize_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (Nat.lt_succ_iff.mp i.2)]
    have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard.trans hd)
    have hP := homogenize_multiset_prod_X_sub_C Q.roots
    rw [hcard] at hP
    have key : Polynomial.homogenize Q m = MvPolynomial.C Q.leadingCoeff *
        ((Q.roots.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod *
          MvPolynomial.X 1 ^ (m - d)) := by
      calc Polynomial.homogenize Q m
          = Polynomial.homogenize (Polynomial.C Q.leadingCoeff *
              ((Q.roots.map fun a => Polynomial.X - Polynomial.C a).prod * 1)) (d + (m - d)) := by
            rw [mul_one, hfac, Nat.add_sub_cancel' hdm]
        _ = _ := by
            rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_mul _ _ ?_ ?_, hP,
              Polynomial.homogenize_one]
            · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
            · simp
    have h1 := congrArg (MvPolynomial.aeval (R := E) (σ := Fin 2) ![y, x]) (hform.symm.trans key)

    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h1
    have hprod : ∏ j, (algebraMap E A (u j).1 * x + algebraMap E A (u j).2 * y) =
        (M.map fun st => algebraMap E A st.1 * x + algebraMap E A st.2 * y).prod := by
      rw [← hu, Multiset.map_map]; rfl
    simp only [mul_assoc] at h1 ⊢
    rw [h1, hprod]
    simp only [M, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Function.comp_def,
      Multiset.map_replicate, Multiset.prod_replicate]
    congr 2
    · congr 1
      refine Multiset.map_congr rfl fun r _ => ?_
      simp only [map_neg, map_one]
      ring
    · simp

end GlobalTheory.Nef
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.exists_flat_ideal_valuationRing_pullback : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  first | exact @GlobalTheory.FlatHilbAff.exists_flat_ideal | exact GlobalTheory.FlatHilbAff.exists_flat_ideal | (intros; apply GlobalTheory.FlatHilbAff.exists_flat_ideal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace GlobalTheory.IdealGlue

theorem exists_comap_eq : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  intro X ι V f hf hcov J hJ
  exact idealSheaf_glue_of_openImmersions (fun 𝒜 h1 h2 k h3 => GlobalTheory.T.exists_idealSheafData_of_compatible_ideals 𝒜 h1 h2 k h3)
    V f hf (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩) J hJ

end GlobalTheory.IdealGlue
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine : ∀ {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens), (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | (exact @GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine) | (exact GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine) | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.closedImmersion_restrict_clopen_factorization : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  first | (exact @GlobalTheory.clopen_cut_closedImmersion) | (exact GlobalTheory.clopen_cut_closedImmersion) | (intros; apply GlobalTheory.clopen_cut_closedImmersion <;> assumption)
end
