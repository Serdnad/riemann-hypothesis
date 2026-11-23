module

public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle257
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem cm_fixed_integer (cm : CMData F E) (x : 𝓞 E) (hx : star (x : E) = (x : E)) :
    ∃ t : 𝓞 F, (x : E) = algebraMap F E t := by
  obtain ⟨t, ht⟩ := (cm.fixed x).1 hx
  have hi : IsIntegral ℤ t := by
    have h1 : IsIntegral ℤ (algebraMap F E t) := by
      rw [ht]; exact RingOfIntegers.isIntegral_coe x
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨t, hi⟩, ht.symm⟩

theorem cm_exists_unit_disc (cm : CMData F E) (M : Ideal (𝓞 F)) (hM : M.IsMaximal) :
    ∃ θ : 𝓞 E, ∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧
      (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ M := by
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) M (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le)
  obtain ⟨θ, s, hs, hθ⟩ := cm.cmUnram.2.2 P hP
  have hs' : (s : E) = star (θ : E) := hs
  obtain ⟨t, ht⟩ := cm_fixed_integer cm (θ + s) (by
    change star ((θ : E) + s) = (θ : E) + s
    rw [hs', star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := cm_fixed_integer cm (θ * s) (by
    change star ((θ : E) * s) = (θ : E) * s
    rw [hs', star_mul, star_star])
  change (θ : E) + s = _ at ht
  change (θ : E) * s = _ at hn
  refine ⟨θ, t, n, hs' ▸ ht, hs' ▸ hn, fun h => hθ ?_⟩
  rw [← hPM, Ideal.mem_comap] at h
  have e : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (θ - s) ^ 2 := by
    apply RingOfIntegers.coe_injective
    have h1 : ∀ z : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) = algebraMap F E (z : F) :=
      fun z => rfl
    rw [h1]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = ((θ : E) - s) ^ 2
    rw [← ht, ← hn]; ring
  rw [e] at h
  exact hP.isPrime.mem_of_pow_mem 2 h

theorem cm_exists_coords (cm : CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ p q : F, x = algebraMap F E p + algebraMap F E q * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by linear_combination -h)
  have hq : star ((x - star x) / (θ - star θ)) = (x - star x) / (θ - star θ) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]
    field_simp
    ring
  obtain ⟨q, hq'⟩ := (cm.fixed _).1 hq
  have hp : star (x - (x - star x) / (θ - star θ) * θ) = x - (x - star x) / (θ - star θ) * θ := by
    rw [star_sub, star_mul, hq]
    field_simp
    ring
  obtain ⟨p, hp'⟩ := (cm.fixed _).1 hp
  exact ⟨p, q, by rw [hp', hq']; ring⟩

theorem cm_local_neg_one (cm : CMData F E) (θ : 𝓞 E) (t n : 𝓞 F)
    (ht : (θ : E) + star (θ : E) = algebraMap F E t) (hn : (θ : E) * star (θ : E) = algebraMap F E n)
    (hθ : (θ : E) - star (θ : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A B : v.adicCompletion F,
      A ^ 2 + A * B * algebraMap F (v.adicCompletion F) t + B ^ 2 * algebraMap F (v.adicCompletion F) n = -1 ∧
      (t ^ 2 - 4 * n ∉ v.asIdeal → A ∈ v.adicCompletionIntegers F ∧ B ∈ v.adicCompletionIntegers F) := by
  have key : ∀ (a b : v.adicCompletionIntegers F) (t n : 𝓞 F),
      a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t +
        b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 →
      (a : v.adicCompletion F) ^ 2 + a * b * algebraMap F (v.adicCompletion F) t +
        b ^ 2 * algebraMap F (v.adicCompletion F) n = -1 := by
    intro a b t n h
    have h2 := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) h
    have h1 : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) z : v.adicCompletionIntegers F) :
        v.adicCompletion F) = algebraMap F (v.adicCompletion F) (z : F) := fun z => rfl
    push_cast at h2
    rw [h1, h1] at h2
    exact h2
  by_cases hd : t ^ 2 - 4 * n ∈ v.asIdeal
  · obtain ⟨θ', h⟩ := cm_exists_unit_disc cm v.asIdeal v.isMaximal
    obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ' h
    have h := key a b t' n' h
    obtain ⟨p, q, hpq⟩ := cm_exists_coords cm θ hθ θ'
    have hs : ∀ z : F, star (algebraMap F E z) = algebraMap F E z := fun z => (cm.fixed _).2 ⟨z, rfl⟩
    have hst : star (θ' : E) = algebraMap F E p + algebraMap F E q * star (θ : E) := by
      rw [hpq, star_add, star_mul, hs, hs, mul_comm]
    have e1 : (t' : F) = 2 * p + q * t := by
      apply (algebraMap F E).injective
      simp only [map_add (f := _), map_mul, map_ofNat]
      rw [← ht', ← ht, hst, hpq]; ring
    have e2 : (n' : F) = p ^ 2 + p * q * t + q ^ 2 * n := by
      apply (algebraMap F E).injective
      simp only [map_add (f := _), map_mul, map_pow]
      rw [← hn', ← ht, ← hn, hst, hpq]; ring
    rw [e1, e2] at h
    simp only [map_add (f := _), map_mul, map_pow, map_ofNat] at h
    refine ⟨a + b * algebraMap F _ p, b * algebraMap F _ q, ?_, fun h => (h hd).elim⟩
    linear_combination h
  · obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ ⟨t, n, ht, hn, hd⟩
    have h := key a b t' n' h
    have e1 : (t' : F) = t := (algebraMap F E).injective (ht'.symm.trans ht)
    have e2 : (n' : F) = n := (algebraMap F E).injective (hn'.symm.trans hn)
    rw [e1, e2] at h
    exact ⟨a, b, h, fun _ => ⟨a.2, b.2⟩⟩

end

theorem neg_one_norm_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1 := by
  intro F E _ _ _ _ _ _ cm
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  obtain ⟨θ, t, n, ht, hn, hd⟩ := cm_exists_unit_disc cm M hM
  have hd0 : t ^ 2 - 4 * n ≠ 0 := fun h => hd (h ▸ M.zero_mem)
  have hθ : (θ : E) - star (θ : E) ≠ 0 := by
    intro h
    apply hd0
    apply RingOfIntegers.coe_injective
    apply (algebraMap F E).injective
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = 0
    rw [← ht, ← hn]
    linear_combination ((θ : E) - star (θ : E)) * h
  choose A B hAB hint using cm_local_neg_one cm θ t n ht hn hθ
  have hfin : {v : HeightOneSpectrum (𝓞 F) | t ^ 2 - 4 * n ∈ v.asIdeal}.Finite := by
    have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {t ^ 2 - 4 * n})
      (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
    simpa only [Ideal.dvd_span_singleton] using this
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, t ^ 2 - 4 * n ∉ v.asIdeal := by
    simpa only [Filter.eventually_cofinite, not_not] using hfin
  let a : FiniteAdeleRing (𝓞 F) F := ⟨A, hev.mono fun v hv => (hint v hv).1⟩
  let b : FiniteAdeleRing (𝓞 F) F := ⟨B, hev.mono fun v hv => (hint v hv).2⟩
  have hab : a ^ 2 + a * b * algebraMap F (FiniteAdeleRing (𝓞 F) F) t +
      b ^ 2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) n = -1 := by
    apply FiniteAdeleRing.ext
    intro v
    have := hAB v
    rw [sq, sq] at this ⊢
    exact this
  let L : E →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F := Algebra.TensorProduct.includeLeft
  let Rr : FiniteAdeleRing (𝓞 F) F →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.includeRight
  refine ⟨Rr a + L θ * Rr b, ?_⟩
  have hL : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (L x) = L (star x) := fun x => by
    simp [Formalism.UG.sigR, L, CMData.sig, starRingEnd_apply]
  have hR : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (Rr x) = Rr x := fun x => by
    simp [Formalism.UG.sigR, Rr]
  have h1 := congrArg L ht
  have h2 := congrArg L hn
  have h3 := congrArg Rr hab
  simp only [map_add (f := _), map_mul, map_pow, map_neg, map_one, AlgHom.commutes] at h1 h2 h3
  rw [map_add (f := _), map_mul, hL, hR, hR]
  rw [← h1, ← h2] at h3
  linear_combination h3

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Shift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}

end Shift

section Read

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem classPresOf_ext (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    (f : (S.toCSD h).Forms) (g : G) :
    (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q g)) := by

  have key : ∀ (γ : Γ) (c : S.Cl) (k : J),
      (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (ι γ * A.y c * k))) := by
    intro γ c k
    have e1 : (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        (χ k : ℂ) • ρ γ (coef ((f : S.Cl → S.V) c)) :=
      ClassPres.ext_eq (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl) f γ c k
    have e2 : A.q (ι γ * A.y c * k) = A.gl (γ, k⁻¹) • S.outSec.rep c := by
      rw [A.q_mul, A.q_y]
    have e3 : (((S.res h).symm f : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
      have := S.resOf_apply h S.outSec ((S.res h).symm f) c
      rw [← this]
      show ((((S.res h) ((S.res h).symm f)).1 : S.Cl → S.V) c) = _
      rw [LinearEquiv.apply_symm_apply]
    have e4 := (S.mem_EqFun _).1 ((S.res h).symm f).2 (A.gl (γ, k⁻¹)) (S.outSec.rep c)
    rw [e1, e2, e4, e3, hgl, map_inv, inv_inv, Units.smul_def]
  rw [(classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).dec_spec g]
  exact key _ _ _

variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ : Γ →* Module.End ℂ W} {ρ' : Γ' →* Module.End ℂ W}
  {J' : Subgroup G'} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ} {T : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ}

theorem transport_ext (P : ClassPres ι T σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) (f : T.Forms) (g : G) :
    (P.transport eG eΓ hι hρ hJ hχ).ext (f : T.Cl → T.V) (eG g) = P.ext f g := by
  rw [P.dec_spec g]
  have hk : eG (P.decK g : G) ∈ J' := by
    rw [hJ]; exact Subgroup.mem_map_of_mem eG.toMonoidHom (P.decK g).2
  have e : eG (ι (P.decG g) * P.y (P.decC g) * (P.decK g : G)) =
      ι' (eΓ (P.decG g)) * (P.transport eG eΓ hι hρ hJ hχ).y (P.decC g) * ((⟨_, hk⟩ : J') : G') := by
    rw [map_mul, map_mul, hι]; rfl
  rw [e, ClassPres.ext_eq, ClassPres.ext_eq, hχ, hρ]
  rfl

end Read

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'}

variable (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ' : Γ' →* Module.End ℂ W) (k : G) (eG : G ≃* G') (eΓ : Γ ≃* Γ')
    (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (J' : Subgroup G') (χ' : J' →* ℂˣ)
    (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ κ : J, (κ : G) ∈ A.K1 → ∀ hx : eG (k * κ * k⁻¹) ∈ J', χ' ⟨_, hx⟩ = 1)
    (hgl : ∀ (γ : Γ) (κ : J) (v : S.V) (hx : eG (k * κ * k⁻¹) ∈ J'),
      coef (S.ρ (A.gl (γ, κ)) v) = ((χ' ⟨_, hx⟩)⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v))

end Assemble

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

theorem ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n) :
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show Formalism.L2.Col.toGLm E n (Formalism.UG.glEquiv (γ : GL (Fin n) E)) = _
  simp only [Formalism.L2.Col.toGLm, Formalism.UG.glEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftPres
end
end

section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

noncomputable section

namespace GlobalTheory.SameAtOfLoc

theorem exists_smul_mem_of_le_locP {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (𝓞 E) W] (Q : HeightOneSpectrum (𝓞 E)) {A B : Submodule (𝓞 E) W} (hA : A.FG)
    (h : A ≤ localization₂ Q.asIdeal B) : ∃ s ∉ Q.asIdeal, ∀ x ∈ A, s • x ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  have key : ∃ s ∉ Q.asIdeal, ∀ a ∈ S, s • a ∈ B := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Formalism.L2.DIV.lc_one_notMem Q, by simp⟩
    | insert a S ha ih =>
      obtain ⟨s, hs, hS⟩ := ih (le_trans (Submodule.span_mono (by
        rw [Finset.coe_insert]; exact Set.subset_insert _ _)) h)
      obtain ⟨t, ht, hta⟩ := (Formalism.L2.DIV.lc_mem_locP Q B a).1
        (h (Submodule.subset_span (by simp)))
      refine ⟨t * s, Formalism.L2.DIV.lc_mul_notMem Q ht hs, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact B.smul_mem s hta
      · rw [mul_smul]; exact B.smul_mem t (hS b hb)
  obtain ⟨s, hs, hS⟩ := key
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact B.smul_mem r hx

end GlobalTheory.SameAtOfLoc

namespace GlobalTheory


open GlobalTheory.SameAtOfLoc in
theorem sameAt_of_localized_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A →
    Submodule.IsLattice E B → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B → SameAt Q A B := by
  intro E _ _ _ n Q A B hA hB h
  obtain ⟨a, ha, h1⟩ := exists_smul_mem_of_le_locP Q hB.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q B)
  obtain ⟨a', ha', h2⟩ := exists_smul_mem_of_le_locP Q hA.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q A)
  exact ⟨a, ha, a', ha', h1, h2⟩

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.DualLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem hStd_osmul_right (y : Sp E n) (c : 𝓞 E) (z : Sp E n) :
    hStd E n y (c • z) = c • hStd E n y z := by
  rw [← algebraMap_smul E c z, map_smul, algebraMap_smul]

theorem mem_localization_dual_iff (Q : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) (Sp E n)) (hL : L.FG) (x : Sp E n) :
    x ∈ localization₂ Q.asIdeal (dual (hStd E n) L) ↔
      ∀ y ∈ localization₂ (conjPrime₂ Q).asIdeal L, hStd E n y x ∈ localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP Q _ x).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP (conjPrime₂ Q) L y).1 hy
    rw [mem_conjP] at ht
    have h1 := (mem_dual L (s • x)).1 hsx (t • y) hty
    rw [hStd_osmul_left, smul_smul, hStd_osmul_right] at h1
    refine (mem_locP Q _ _).2 ⟨cO E t * s, ?_, h1⟩
    intro hm
    rcases Q.isPrime.mem_or_mem hm with h | h
    · exact ht h
    · exact hs h
  · intro H
    obtain ⟨S, hS⟩ := hL
    have H' : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ s • hStd E n y x ∈ (1 : Submodule (𝓞 E) E) := by
      intro y hy
      have hyL : y ∈ L := hS ▸ Submodule.subset_span hy
      exact (mem_locP Q _ _).1 (H y (Formalism.L2.DIV.lc_le_locP (conjPrime₂ Q) L hyL))
    choose f hf hfx using H'
    refine (mem_locP Q _ x).2 ⟨∏ y ∈ S.attach, f y.1 y.2, ?_, ?_⟩
    · intro hm
      obtain ⟨a, _, ha⟩ := (Q.isPrime.prod_mem_iff).1 hm
      exact hf a.1 a.2 ha
    · rw [mem_dual]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        rw [hStd_osmul_right, ← Finset.prod_erase_mul S.attach (fun a => f a.1 a.2) (Finset.mem_attach S ⟨z, hz⟩),
          mul_smul]
        exact Submodule.smul_mem _ _ (hfx z hz)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply]; exact add_mem ha hb
      | smul r a _ ha =>
        rw [hStd_osmul_left, hStd_osmul_right]
        exact Submodule.smul_mem _ _ ha

theorem use₅ (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n))
    (hA : Submodule.IsLattice E A) (hB : Submodule.IsLattice E B)
    (h : localization₂ (conjPrime₂ Q).asIdeal A = localization₂ (conjPrime₂ Q).asIdeal B) :
    localization₂ Q.asIdeal (dual (hStd E n) A) = localization₂ Q.asIdeal (dual (hStd E n) B) := by
  ext x
  rw [mem_localization_dual_iff Q A hA.fg, mem_localization_dual_iff Q B hB.fg, h]

end GlobalTheory.DualLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.etaTilde_isUnitArg_at_cmType_places : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  first | exact @GlobalTheory.EtaUnitArg.etaT_isUnitArg | exact GlobalTheory.EtaUnitArg.etaT_isUnitArg | (intros; apply GlobalTheory.EtaUnitArg.etaT_isUnitArg <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, IsCharAF F ψ := by
  first | exact @GlobalTheory.GaugeEx.CharZero.exists_isCharAF | exact GlobalTheory.GaugeEx.CharZero.exists_isCharAF | (intros; apply GlobalTheory.GaugeEx.CharZero.exists_isCharAF <;> assumption)
end
