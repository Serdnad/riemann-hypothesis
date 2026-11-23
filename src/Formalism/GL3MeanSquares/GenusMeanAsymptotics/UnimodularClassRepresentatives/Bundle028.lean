module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle022
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardMapEquiv
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2.IA

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem surjective_of_nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop

theorem exists_adj {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (s : V →ₗ⋆[K] V →ₗ[K] K) : ∃ Y : V →ₗ[K] V, ∀ x y, h x (Y y) = s x y := by
  have hex : ∀ y, ∃ w, ∀ x, h x w = s x y := by
    intro y
    let l : V →ₗ[K] K :=
      { toFun := fun x => star (s x y)
        map_add' := fun a b => by simp
        map_smul' := fun a b => by simp [starRingEnd_apply] }
    obtain ⟨w, hw⟩ := surjective_of_nondegenerate hn l
    refine ⟨w, fun x => ?_⟩
    have h1 : h w x = star (s x y) := by rw [hw]; rfl
    have h2 := hs.eq w x
    rw [← h2, h1, starRingEnd_apply, star_star]
  choose Y hY using hex
  refine ⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [map_sub, map_add (f := _), hY, hY, hY, map_add (f := _), sub_self]
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]

section Lat

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def phi (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) : V →ₗ⋆[K] V →ₗ[K] K :=
  (h.comp (X : V →ₗ[K] V)).compl₂ (X : V →ₗ[K] V) - h

theorem phi_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) (x y : V) :
    phi h X x y = h (X x) (X y) - h x y := rfl

theorem star_phi {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]

theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) : algebraMap F K (π : F) ≠ 0 := by
  intro h0
  have h1 : (π : F) = 0 := (map_eq_zero (algebraMap F K)).1 h0
  have h2 : π = 0 := by exact_mod_cast h1
  exact hπ' (h2 ▸ zero_mem _)

theorem sesq_scale (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (s : V →ₗ⋆[K] V →ₗ[K] K) {n m : ℕ} (hnm : n + 2 * r ≤ m)
    (hs : ∀ x ∈ locF 𝔭 B₀, ∀ y ∈ locF 𝔭 B₀, s x y ∈ pK K 𝔭 m) :
    ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, s x y ∈ pK K 𝔭 n := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  have hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F) := (hF _).2 ⟨_, rfl⟩
  intro x hx y hy
  have hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)
  have hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)
  have h1 := pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul] at h1
  obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 h1
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * r) h0)
  calc algebraMap F K (π : F) ^ (2 * r) * s x y
      = algebraMap F K (π : F) ^ r * (algebraMap F K (π : F) ^ r * s x y) := by ring
    _ = algebraMap F K (π : F) ^ (n + 2 * r) * b := e
    _ = _ := by ring

theorem end_scale {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring

end Lat

end Formalism.HermitianLattices.Ext.L3.D2.IA
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

theorem isoCount_one_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - (-(Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  have e1 : extP K 𝔭 ^ 1 = P := by
    rw [pow_one]
    exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP
      (by rw [← conjIdeal_eq_comap]; exact hc) hθ
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_inert hK hF hP hc]
  have hσ : ∀ x, NormResidues.sigEquiv P hc (NormResidues.sigEquiv P hc x) = x := NormResidues.sigHom_sigHom P hc
  have hne : ∃ x, NormResidues.sigEquiv P hc x ≠ x := by
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [NormResidues.sigEquiv_mk] at h
    exact Ideal.Quotient.eq.1 h.symm
  have h1 := UnitaryNormCounts.card_inert (m := Fin m) (Ideal.quotEquivOfEq e1) (NormResidues.sigEquiv P hc)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [star_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, NormResidues.sigEquiv_mk]
      rfl) hσ hne _ hq (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (u i))
    (by
      intro i
      rw [star_mk, star_def, hu])
    (fun i => isUnit_mk (hunit i) 1)
  unfold isoCount
  rw [diagonal_map (map_zero _), h1]
  exact card_unitary_fin _ hσ hne _ hq m

theorem isoCount_one_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - ((Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have e1 : extP K 𝔭 ^ 1 ≤ P := by
    rw [pow_one]
    exact Ideal.map_comap_le
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have := finite_quot (K := K) h𝔭 1
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_split hK hF hP hc]
  have hb : Function.Bijective fun a : 𝓞 K ⧸ extP K 𝔭 ^ 1 =>
      (Ideal.Quotient.factor e1 (star a), Ideal.Quotient.factor e1 a) := by
    apply Function.Surjective.bijective_of_nat_card_le
    · intro y
      obtain ⟨z, hz⟩ := NormResidues.pairHom_surjective hP hc y
      refine ⟨Ideal.Quotient.mk _ z, ?_⟩
      rw [← hz, NormResidues.pairHom_apply]
      show (Ideal.Quotient.factor e1 (star (Ideal.Quotient.mk _ z)), _) = _
      rw [star_mk]
      rfl
    · rw [absNorm_extP_pow hK hF h𝔭, Nat.card_prod, Nat.card_eq_fintype_card, hq]
      apply le_of_eq
      ring
  have h1 := UnitaryNormCounts.card_split (m := Fin m) (Ideal.Quotient.factor e1) hb
    ((diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)))
    (by
      rw [map_mk_conjTranspose, diagonal_conjTranspose]
      congr 2
      funext i
      exact hu i)
    (by
      rw [diagonal_map (map_zero _), det_diagonal]
      exact Finset.univ.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
        (fun i _ => isUnit_mk (hunit i) 1))
  unfold isoCount
  rw [h1]
  exact card_GL_fin _ hq m

theorem isoCount_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) :
    (isoCount 𝔭 1 (diagonal u) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 m := by
  have hF := hFF.out
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  unfold alphaStd
  rw [etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [isoCount_one_inert hK hP hc u hu hunit, ite_eq_left hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]
    congr 2
    ring
  · rw [isoCount_one_split hK hP hc u hu hunit, ite_eq_right hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]

theorem isoCount_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by
  have hg : (diagonal u)ᴴ = diagonal u := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hu i
  have hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤ := by
    rw [Matrix.det_diagonal, ← Ideal.prod_span_singleton]
    exact Ideal.prod_sup_eq_top fun i _ => hunit i
  rw [isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]
  push_cast
  rw [isoCount_one hK h𝔭 u hu hunit]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCB

section Alg

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w

theorem skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]

theorem skewY_skew {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring

theorem laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by
  apply han
  have h1 : h z z = m * h z (Y z) := by
    have := congrArg (h z) hz
    rwa [map_smul, smul_eq_mul] at this
  have h2 : h z z = l * h (Y z) z := by
    have := congrArg (fun t => h t z) hz
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this
    exact this
  have h3 := hY z z
  have h4 : h z (Y z) = 0 := by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3
  rw [h1, h4, mul_zero]

theorem exists_cayley [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩

end Alg

section Int

open WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem skewY_mem (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : ℕ} {u w z : V} {θ : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A J w) (hθ : InI 𝔭 J θ) (hz : InL 𝔭 A 0 z) : InL 𝔭 A J (skewY h u w θ z) := by
  rw [skewY_apply]
  refine InL.add hp ?_ ?_
  · refine (InL.smul hp (i := J) ?_ hu).mono (by omega)
    exact InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega))
      ((hw.form hp hF hA hz).mono (by omega))
  · exact (InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)

theorem mem_of_resolvent (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add (f := _), map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add (f := _), map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2

end Int

end Formalism.HermitianLattices.Ext.L3.WCB
end
end
