module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle066
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OverSplit

theorem ker_isMaximal {A : Type} [CommRing A] {T : ℕ} [Fact T.Prime] (ψ : A →+* ZMod T) :
    (RingHom.ker ψ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ψ (ZMod.ringHom_surjective ψ)

theorem exists_roots {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {T : ℕ} [Fact T.Prime] (ψ : O →+* ZMod T)
    (p n : O) (x y : ZMod T) (hp : ψ p = x + y) (hn : ψ n = x * y) (hxy : x ≠ y) :
    ∃ r r' : O, r + r' = p ∧ r * r' = n ∧ ψ r = x ∧ ψ r' = y ∧ IsUnit (r - r') := by
  have hk : ∀ z, z ∈ IsLocalRing.maximalIdeal O ↔ ψ z = 0 := fun z => by
    rw [← IsLocalRing.eq_maximalIdeal (ker_isMaximal ψ), RingHom.mem_ker]
  have hu : ∀ z, ψ z ≠ 0 → IsUnit z := fun z hz => by
    by_contra h
    exact hz ((hk z).1 h)
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective ψ x
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  obtain ⟨r, hr, hra⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O)
    (Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X + Polynomial.C n) (by monicity!) a
    (by rw [hk]; simp [ha, hp, hn]; ring)
    (by
      refine IsUnit.map _ (hu _ ?_)
      have : ψ (Polynomial.eval a (Polynomial.derivative
          (Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X + Polynomial.C n))) = x - y := by
        simp [ha, hp]; ring
      rwa [this])
  have hrx : ψ r = x := by
    rw [hk, map_sub, ha, sub_eq_zero] at hra; exact hra
  have hr' : r ^ 2 - p * r + n = 0 := by simpa using hr
  have hry : ψ (p - r) = y := by rw [map_sub, hp, hrx]; ring
  refine ⟨r, p - r, by ring, by linear_combination -hr', hrx, hry, hu _ ?_⟩
  rwa [map_sub, hrx, hry]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def inclO (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F →+* intV E v :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)).toRingHom.comp
      (v.adicCompletionIntegers F).subtype) _
    fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)

theorem coe_inclO (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletionIntegers F) :
    ((inclO E v a : intV E v) : E ⊗[F] v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] (a : v.adicCompletion F) := rfl

theorem exists_inclO_eq (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 E)
    (hx : (x : E) ∈ (algebraMap F E).range) :
    ∃ p : v.adicCompletionIntegers F, inclO E v p = GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v x := by
  obtain ⟨b, hb⟩ := hx
  have hi : IsIntegral ℤ b := by
    rw [← isIntegral_algebraMap_iff (B := E) , hb]
    exact x.isIntegral_coe
  let b' : 𝓞 F := ⟨b, hi⟩
  have hx' : x = algebraMap (𝓞 F) (𝓞 E) b' := by
    apply Subtype.ext
    exact hb.symm
  refine ⟨algebraMap (𝓞 F) _ b', Subtype.ext ?_⟩
  rw [coe_inclO, GlobalTheory.OverCompare.coe_toIntV, hx', GlobalTheory.OverCompare.tmul_algebraMap]
  rfl

end GlobalTheory.OverSplit


open GlobalTheory.OverSplit in
theorem GlobalTheory.OverSplit.exists_splitting_of_character :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) → ∀ (v : HeightOneSpectrum (𝓞 F)) (T : ℕ), T.Prime → ∀ χ : intV E v →+* ZMod T, ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, IsSplitting σ v s ∧ ∀ a : intV E v, Valued.v (prP s a) < 1 → χ a = 0 := by
  intro F E _ _ _ _ _ σ hdeg hσ hfix hunr v T hT χ
  have : Fact T.Prime := ⟨hT⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set ι := GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v with hι
  obtain ⟨θ, t, ht, hθt⟩ := hunr _ (ker_isMaximal (χ.comp ι))
  have hxy : χ (ι θ) ≠ χ (ι t) := by
    intro h
    apply hθt
    rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, RingHom.comp_apply, h, sub_self]
  have e1 : ((θ + t : 𝓞 E) : E) = θ + σ θ := by rw [← ht]; rfl
  have e2 : ((θ * t : 𝓞 E) : E) = θ * σ θ := by rw [← ht]; rfl
  obtain ⟨p, hp⟩ := exists_inclO_eq v (θ + t) (hfix _ (by rw [e1, map_add (f := _), hσ, add_comm]))
  obtain ⟨n, hn⟩ := exists_inclO_eq v (θ * t) (hfix _ (by rw [e2, map_mul, hσ, mul_comm]))
  obtain ⟨r, r', hs, hm, hr, hr', hu⟩ := exists_roots (χ.comp (inclO E v)) p n (χ (ι θ)) (χ (ι t))
    (by rw [RingHom.comp_apply, hp, map_add (f := _), map_add (f := _)])
    (by rw [RingHom.comp_apply, hn, map_mul, map_mul]) hxy
  obtain ⟨s, hsp, hsθ⟩ := GlobalTheory.RootSplitting.exists_isSplitting F E σ hdeg hσ hfix v θ r r' θ.isIntegral_coe hu
    (by
      have := congrArg Subtype.val hp
      rw [← e1]
      refine this.symm.trans ?_
      rw [← hs]; rfl)
    (by
      have := congrArg Subtype.val hn
      rw [← e2]
      refine this.symm.trans ?_
      rw [← hm]; rfl)
  refine ⟨s, hsp, fun a ha => ?_⟩
  let a₁ : v.adicCompletionIntegers F := ⟨(s a).1, ((hsp.2.2 a).1 a.2).1⟩
  have ha₁ : χ (inclO E v a₁) = 0 := by
    have h1 : a₁ ∈ IsLocalRing.maximalIdeal _ :=
      (ValuationSubring.valuation_lt_one_iff _ _).2
        ((Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.1 ha)
    rw [← IsLocalRing.eq_maximalIdeal (ker_isMaximal (χ.comp (inclO E v)))] at h1
    exact h1
  have key : (ι θ - inclO E v r') * a = (ι θ - inclO E v r') * inclO E v a₁ := by
    apply Subtype.ext
    apply s.injective
    have h0 : s ((ι θ - inclO E v r' : intV E v) : E ⊗[F] v.adicCompletion F) =
        ((r : v.adicCompletion F) - r', 0) := by
      rw [AddSubgroupClass.coe_sub, map_sub, coe_inclO, hsp.1, hι, GlobalTheory.OverCompare.coe_toIntV, hsθ]
      simp
    rw [Subring.coe_mul, Subring.coe_mul, map_mul, map_mul, h0, coe_inclO, hsp.1]
    ext <;> simp [a₁]
  have := congrArg χ key
  rw [map_mul, map_mul, ha₁, mul_zero, map_sub] at this
  have hr'' : χ (inclO E v r') = χ (ι t) := hr'
  rw [hr''] at this
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hxy)

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.LatLocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

theorem mem_latS_adele_iff (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ := by
  obtain ⟨m, l, -, hl⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  have hv : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : Fin k → E ⊗[F] v.adicCompletion F),
      w ∈ locLat v Λ ↔ ∃ t : Fin m → v.adicCompletion F,
        (∀ j, t j ∈ (v.adicCompletionIntegers F).toSubring) ∧ w = fun i => ∑ j, l j i ⊗ₜ[F] t j :=
    fun v w => hl _ _ w
  rw [hl]
  constructor
  · rintro ⟨t, ht, rfl⟩ v
    refine (hv v _).2 ⟨fun j => t j v, fun j => ht j v, ?_⟩
    funext i

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => Formalism.UG.P.afsplit_prV_tmul v _ _
  · intro h
    choose t ht hu using fun v => (hv v _).1 (h v)
    let s : Fin m → FiniteAdeleRing (𝓞 F) F := fun j =>
      ⟨fun v => t v j, Filter.Eventually.of_forall fun v => ht v j⟩
    refine ⟨s, fun j v => ht v j, ?_⟩
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_

    rw [map_sub, sub_eq_zero, map_sum]
    refine (congrFun (hu v) i).trans ?_
    exact Finset.sum_congr rfl fun j _ => (Formalism.UG.P.afsplit_prV_tmul v (l j i) (s j)).symm

theorem mem_of_forall_locLat (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (x : Fin k → E)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) : x ∈ Λ := by
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin k) Λ hΛ hspan]
  show ((1⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [inv_one, Units.val_one, one_mulVec, mem_latS_adele_iff Λ hΛ]
  exact hx

theorem mem_range_of_forall_intV (a : E)
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) :
    a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have := mem_of_forall_locLat (F := F) Λ hfin hspan (fun _ => a) fun v => by
    have h2 : (fun _ => inclE (F := F) (v.adicCompletion F) (1 : E)) ∈ locLat v Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := (locLat v Λ).smul_mem (⟨_, ha v⟩ : intV E v) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (v.adicCompletion F) a * inclE (F := F) (v.adicCompletion F) (1 : E)
    rw [map_one, mul_one]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem latS_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range :=
  fun _ _ _ _ _ _ _ _ Λ hΛ =>
    ⟨mem_latS_adele_iff Λ hΛ, mem_of_forall_locLat Λ hΛ, mem_range_of_forall_intV⟩

end GlobalTheory.LatLocGlob
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare

theorem exists_int_approx_all (F : Type) [Field F] [NumberField F] (T : ℕ) (hT : T ≠ 0)
    (t : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ht : ∀ v, t v ∈ v.adicCompletionIntegers F) :
    ∃ ρ : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), ∃ w ∈ v.adicCompletionIntegers F,
      t v = algebraMap F (v.adicCompletion F) (ρ : F) + T • w := by
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, Filter.Eventually.of_forall ht⟩
  obtain ⟨ρ, w, hw, e⟩ := Formalism.UG.P.csGlob_intAdApprox F (T : 𝓞 F) (by exact_mod_cast hT) a ht
  refine ⟨ρ, fun v => ⟨w v, hw v, ?_⟩⟩
  rw [map_natCast, ← nsmul_eq_mul] at e
  have h : a v = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ + T • w) v := by rw [← e]
  exact h

theorem exists_lattice_approx_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  intro F E _ _ _ _ _ k Λ hΛ T hT y hy
  obtain ⟨m, l, hl, H⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  choose t ht hyt using fun v : HeightOneSpectrum (𝓞 F) =>
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring (y v)).1 (hy v)
  choose ρ hρ using fun j : Fin m =>
    exists_int_approx_all F T hT (fun v => t v j) (fun v => ht v j)
  refine ⟨∑ j, algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hl j), fun v => ?_⟩
  choose w hw hwt using fun j => hρ j v
  refine ⟨fun i => ∑ j, l j i ⊗ₜ[F] w j,
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _).2 ⟨w, hw, rfl⟩, ?_⟩
  rw [hyt v]
  funext i

  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_sum, Finset.smul_sum,
  ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hwt j, TensorProduct.tmul_add]
  congr 1
  · have h1 : algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j i = (ρ j : F) • l j i := by
      rw [Algebra.smul_def, Algebra.smul_def]; rfl
    rw [h1, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  · exact map_nsmul (TensorProduct.mk F E (v.adicCompletion F) (l j i)) T (w j)

end GlobalTheory.OverCompare
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.normal_form_bounds_unfolding

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance GlobalTheory.Proof.NormalFormAtPrime

variable {E : Type} [Field E] [NumberField E]

theorem nonneg_of_intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (h : IntAt P ((qOf P : E) ^ k)) : 0 ≤ k := by
  by_contra hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
  subst hm
  obtain ⟨r, s, hs, e⟩ := h
  apply hs
  have hq := qOf_ne_zero P
  have e' : s = (qOf P : 𝓞 E) * ((qOf P : 𝓞 E) ^ m * r) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E _
    rw [map_mul, map_mul, map_pow, map_natCast, ← e, zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem le_of_zpow_eq {P : HeightOneSpectrum (𝓞 E)} {a b : ℤ} {u : E} (hu : IntAt P u)
    (h : (qOf P : E) ^ a = (qOf P : E) ^ b * u) : b ≤ a := by
  have hq := qOf_ne_zero P
  have : (qOf P : E) ^ (a - b) = u := by
    rw [zpow_sub₀ hq, h]
    field_simp
  have := nonneg_of_intAt_zpow (this ▸ hu)
  omega

variable [StarRing E] {n c : ℕ}

omit [NumberField E] [StarRing E] in
theorem inX_natAdd (x : Fin n → E) (b : Fin c) : Loc.inX E n c x (Fin.natAdd n b) = 0 := by
  rw [inX_apply, dite_eq_right (by simp)]

omit [NumberField E] [StarRing E] in
theorem atN_natAdd (v : Fin (n + c) → E) (b : Fin c) : Loc.atN v (n + b.1) = v (Fin.natAdd n b) := by
  unfold Loc.atN
  rw [dite_eq_left (by omega)]
  rfl

omit [NumberField E] [StarRing E] in
theorem nfGen_natAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i b : Fin c) :
    nfGen q n c e z i (Fin.natAdd n b) = if b = i then (q : E) ^ e i else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : (if i.1 = 0 then Loc.inX E n c z else 0 : Fin (n + c) → E) (Fin.natAdd n b) = 0 := by
    split_ifs
    · exact inX_natAdd _ _
    · rfl
  rw [h0]
  simp [Loc.eN, Fin.val_inj]

omit [NumberField E] [StarRing E] in
theorem nfGen_castAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) (a : Fin n) :
    nfGen q n c e z i (Fin.castAdd c a) = if i.1 = 0 then (q : E) ^ e i * z a else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
    unfold Loc.eN
    rw [if_neg (by have := a.2; simp; omega)]
  rw [h0]
  split_ifs
  · rw [inX_castAdd]; simp
  · simp

theorem coords_of_mem {P : HeightOneSpectrum (𝓞 E)} (hc : 1 ≤ c) {e : Fin c → ℤ} {z : Fin n → E} {y : Fin (n + c) → E}
    (hy : y ∈ nfLat P n c e z) :
    (∀ b, ∃ u, IntAt P u ∧ y (Fin.natAdd n b) = (qOf P : E) ^ e b * u) ∧
      ∀ a, IntAt P (y (Fin.castAdd c a) - y (Fin.natAdd n ⟨0, hc⟩) * z a) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hy
  have h1 : ∀ b, (Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i : Fin (n + c) → E) (Fin.natAdd n b) =
      (qOf P : E) ^ e b * s b := by
    intro b
    rw [Pi.add_apply, inX_natAdd, Finset.sum_apply]
    simp [nfGen_natAdd, mul_comm]
  refine ⟨fun b => ⟨s b, hs b, h1 b⟩, fun a => ?_⟩
  rw [h1, Pi.add_apply, inX_castAdd, Finset.sum_apply, Finset.sum_eq_single ⟨0, hc⟩]
  · rw [Pi.smul_apply, nfGen_castAdd, if_pos rfl, smul_eq_mul]
    convert (mem_stdAt_iff l).1 hl a using 1
    ring
  · intro b _ hb
    rw [Pi.smul_apply, nfGen_castAdd, if_neg (fun h => hb (Fin.ext h)), smul_zero]
  · simp

theorem nfGen_mem (P : HeightOneSpectrum (𝓞 E)) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen (qOf P) n c e z i ∈ nfLat P n c e z :=
  ⟨0, zero_mem _, Pi.single i 1, intV_single P i, by simp [Pi.single_apply]⟩

omit [NumberField E] [StarRing E] in
theorem nfGen_mem_Ufl (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen q n c e z i ∈ Loc.Ufl E n c (i.1 + 1) := by
  unfold nfGen
  refine Submodule.smul_mem _ _ (add_mem (eN_mem_Ufl (by omega)) ?_)
  split_ifs
  · exact inX_mem_Ufl _ _
  · exact zero_mem _

end GlobalTheory.Proof.normal_form_bounds_unfolding
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.parahoric_le_integral_gl

theorem inX_mem_nfLat_iff {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ)
    (e : Fin c → ℤ) (z : Sp E n) (x : Sp E n) :
    Loc.inX E n c x ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z ↔ x ∈ stdAt E n P := by
  constructor
  · rintro ⟨l, hl, s, -, h⟩
    have hs : ∀ b, s b = 0 := by
      intro b
      have h1 := congrFun h (Fin.natAdd n b)
      have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
      have h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0 := fun y => by
        rw [inX_apply, dite_eq_right (by simp)]
      have h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) =
          if b = i then ((qOf P : E) ^ e i) else 0 := by
        intro i
        unfold IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen
        rw [Pi.smul_apply, Pi.add_apply]
        have h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0 := by
          split_ifs
          · exact h2 z
          · rfl
        rw [h4]
        simp [Loc.eN, Fin.val_inj]
      rw [Pi.add_apply, h2, h2, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h
    rwa [inX_injective h]
  · intro hx
    exact ⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  rintro X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) sharp j P := by
    have := Subgroup.mem_comap.1 hr
    simpa using this
  unfold Jat at hJ
  rw [if_neg hP] at hJ
  have hk := hJ.1
  have key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P := by
    intro y
    rw [← hnf, mem_stdAt_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : h⁻¹ (h w) = w := h.symm_apply_apply w
      rw [this]
      exact (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw
    · intro hy
      exact ⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩
  rw [← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key,
    ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]
  have : (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x)) := by
    change h⁻¹ (r (h (h.symm _))) = _
    rw [h.apply_symm_apply]
  rw [this]

end GlobalTheory.Proof.parahoric_le_integral_gl
end
end
