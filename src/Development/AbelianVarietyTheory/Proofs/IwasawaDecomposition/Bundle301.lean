module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem shaOK_shaTrue (B : Pre) : ShaOK B (GaloisStage.shaTrue B.host) := by
  refine ⟨fun p _ => GaloisStage.lData B.host p, ?_⟩
  intro p hp e _ _ n h
  rw [GaloisStage.shaTrue, dite_eq_left hp.out]
  show ((Formalism.GaloisCohomology.shaLen (GaloisStage.lData B.host p) (e : ℤ)).toNat : ℚ) = n
  rw [h, ENat.toNat_natCast]

end GlobalTheory.MemN
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

theorem _root_.GlobalTheory.T.definiteBaseData_admissible : ∀ (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m), Ch.Ok → Ch.FromHecke B.wts B.embLL → (B.dat X Ch).Ok := by
  first | exact @GlobalTheory.Mem.DatLaws.dat_ok | exact GlobalTheory.Mem.DatLaws.dat_ok | (intros; apply GlobalTheory.Mem.DatLaws.dat_ok <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Mem.TypeNormPin

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2.Pj

section Push

variable {K F : Type} [Field K] [Field F] (φ : K →+* F)

theorem span_image_span (S : Set K) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 K) S : Set K)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : K) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

theorem extend_span (S : Set K) : extend φ (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 F) (φ '' S) :=
  span_image_span φ S

end Push

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_sqrt_iff (g : R.GG) :
    H.emb g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ↔ g ∈ R.Psi :=
  (factEmb R H).2 g

theorem cmHostBaseEmbedding_sqrtMinusD : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem conj_ne : starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem emb_sqrt_cases (σ : H.E →+* ℂ) : σ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ∨
    starRingEnd ℂ (σ H.sqrtMinusD) = Complex.I * (Real.sqrt H.d : ℂ) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
    apply H.φ₀.injective
    rw [map_pow, cmHostBaseEmbedding_sqrtMinusD, h0]
    simp
  have h1 : σ H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 := by
    rw [← map_pow, h, h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact Or.inl h2
  · right; rw [h2]; simp

def embSum : Tau R ⊕ Tau R → (H.E →+* ℂ) :=
  Sum.elim (fun g => H.emb g) (fun g => (starRingEnd ℂ).comp (H.emb g))

theorem embSum_bij : Function.Bijective (embSum H) := by
  refine ⟨?_, fun σ => ?_⟩
  · have hne : ∀ a b : Tau R, H.emb a ≠ (starRingEnd ℂ).comp (H.emb b) := fun a b h => by
      have h1 := DFunLike.congr_fun h H.sqrtMinusD
      rw [RingHom.comp_apply, (emb_sqrt_iff H _).2 a.2, (emb_sqrt_iff H _).2 b.2] at h1
      exact conj_ne H h1.symm
    rintro (a | a) (b | b) hab
    · exact congrArg _ (Subtype.ext ((factEmb R H).1.1 hab))
    · exact absurd hab (hne a b)
    · exact absurd hab.symm (hne b a)
    · refine congrArg _ (Subtype.ext ((factEmb R H).1.1 (RingHom.ext fun x => ?_)))
      exact (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
  · rcases emb_sqrt_cases H σ with h | h
    · obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
      exact ⟨Sum.inl ⟨g, (emb_sqrt_iff H g).1 h⟩, rfl⟩
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 ((starRingEnd ℂ).comp σ)
      refine ⟨Sum.inr ⟨g, (emb_sqrt_iff H g).1 (by rw [hg]; exact h)⟩, RingHom.ext fun x => ?_⟩
      change starRingEnd ℂ (H.emb g x) = _
      rw [hg]; simp

theorem emb_conj (g : R.GG) (x : H.E) : H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) :=
  H.conjE_apply _ x

end Host

theorem exists_hom (X : Stages) (Q : Par X.toD7) (h : Q.PinField) :
    ∃ φ : X.B.Ks →+* Q.c.F, ∀ x : X.B.Ks, ((φ x : Q.c.F) : ℂ) = X.B.embLL x := by
  let e : 𝓞 Q.c.F ≃+* 𝓞 X.B.Ks := Q.eO
  have he : ∀ y : 𝓞 Q.c.F, X.B.embLL ((e y : X.B.Ks) : X.B.LL) = ((y : Q.c.F) : ℂ) := h
  let φ : X.B.Ks ≃+* Q.c.F := IsFractionRing.ringEquivOfRingEquiv e.symm
  have hφ : ∀ y : 𝓞 X.B.Ks, ((φ (algebraMap _ X.B.Ks y) : Q.c.F) : ℂ) =
      X.B.embLL ((algebraMap _ X.B.Ks y : X.B.Ks) : X.B.LL) := fun y => by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine ⟨φ.toRingHom, fun x => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) x
  change ((φ (_ / _) : Q.c.F) : ℂ) = _
  rw [map_div₀, IntermediateField.coe_div, hφ, hφ, IntermediateField.coe_div, map_div₀]

theorem kPsiIn_of_hom (B : Base) [IsCMField B.host.E] {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host B.host.E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum Hh)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ B.R.m) (hp : Dw.p = (B.R.sigW j).1) (hq : Dw.q = (B.R.sigW j).2)
    (h1 : (Hh.rt : B.host.E) = B.host.sqrtMinusD) (h2 : Hh.rt0 = B.host.φ₀ B.host.sqrtMinusD)
    (φ : B.Ks →+* c.F) (hφ : ∀ x : B.Ks, ((φ x : c.F) : ℂ) = B.embLL x) : KPsiIn (Dw := Dw) c := by
  intro 𝔞 h𝔞
  obtain ⟨β, hβ0, hβ, habs⟩ := B.kPsi j hj1 hj2 𝔞 h𝔞
  have hE : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y := fun y => RingHom.congr_fun B.embE_φ₀ y
  have himg : ∀ (τ : B.host.E →+* ℂ) (f : B.host.E → B.host.E), (∀ a, B.host.φ₀ (f a) = τ a) →
      φ '' {x : B.Ks | ∃ a ∈ 𝔞, (x : B.LL) = B.embE (f (a : B.host.E))} =
        (embK c τ) '' (𝔞 : Set (𝓞 B.host.E)) := by
    intro τ f hf
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, hx⟩, rfl⟩
      refine ⟨a, ha, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hx, hE, hf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨_, B.E_le_Ks (f a)⟩, ⟨a, ha, rfl⟩, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hE, hf]
  refine ⟨φ β, (map_ne_zero φ).2 hβ0, ?_, fun σ => ?_⟩
  · have := congrArg (extend φ) hβ
    rw [extend_span, Set.image_singleton, map_prod] at this
    rw [this, ← (embSum_bij B.host).prod_comp fun τ =>
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 B.host.E))) ^ Dw.mult τ,
      Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hs : B.host.emb g B.host.sqrtMinusD = Complex.I * (Real.sqrt B.host.d : ℂ) :=
      (emb_sqrt_iff B.host _).2 g.2
    have h0 : Hh.rt0 = Complex.I * (Real.sqrt B.host.d : ℂ) := h2.trans (cmHostBaseEmbedding_sqrtMinusD B.host)
    have m1 : Dw.mult (embSum B.host (Sum.inl g)) = (B.R.sigW j).1 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos (by rw [h1, h0]; exact hs)]
      exact hp
    have m2 : Dw.mult (embSum B.host (Sum.inr g)) = (B.R.sigW j).2 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_neg]
      · exact hq
      · rw [h1, h0]
        change ¬ starRingEnd ℂ (B.host.emb g B.host.sqrtMinusD) = _
        rw [hs]
        exact conj_ne B.host
    rw [map_mul, map_pow, map_pow, extend_span, extend_span, m1, m2,
      himg (embSum B.host (Sum.inl g)) (B.host.sigmaOf g) (fun _ => rfl),
      himg (embSum B.host (Sum.inr g)) (fun a => B.host.sigmaOf g (B.host.conj a))
        (fun a => emb_conj B.host g a)]
  · rw [hp, hq]
    exact habs (σ.comp φ)

theorem hermitianCodeWordStages_typeNorms_principal : ∀ X : Stages, OKPsi X.toD7 := by
  intro X Q hQ j hj
  obtain ⟨φ, hφ⟩ := exists_hom X Q hQ.2.2.1
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  obtain ⟨-, h1, h2, -⟩ := hQ.1
  exact @kPsiIn_of_hom X.B (instCMHost X.toD7) Q.H Q.l Q.c (Q.Dw j) j hj.1 hj.2 hp hq h1 h2 φ hφ

end GlobalTheory.Mem.TypeNormPin

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem exp_div_mul_eq_zpow_mul_zpow {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Nat.Coprime p q) :
    ∃ a b : ℤ, Complex.exp (2 * Real.pi * Complex.I / ((p * q : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / ((p * (p - 1) : ℕ) : ℂ)) ^ a *
        Complex.exp (2 * Real.pi * Complex.I / ((q * (q - 1) : ℕ) : ℂ)) ^ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨v * p', u * q', ?_⟩
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have h1 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (q' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h3 : (p' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h4 : (q' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h5 : (u : ℂ) * (p' + 1) + v * (q' + 1) = 1 := by exact_mod_cast huv
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * h5

theorem Base.exists_root_mul (B : Base) : ∃ y : B.O, B.embLL (B.OtoLL y) =
    Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
  have p0 := B.host.g_prime 0
  have p1 := B.host.g_prime 1
  obtain ⟨z₀, hz₀, e₀⟩ := B.roots_Ks (B.host.g 0 * (B.host.g 0 - 1)) (by simp)
  obtain ⟨z₁, hz₁, e₁⟩ := B.roots_Ks (B.host.g 1 * (B.host.g 1 - 1)) (by simp)
  obtain ⟨a, b, hab⟩ := exp_div_mul_eq_zpow_mul_zpow p0.two_le p1.two_le
    ((Nat.coprime_primes p0 p1).2 B.host.g_ne)
  have hmem : z₀ ^ a * z₁ ^ b ∈ B.Ks := mul_mem (zpow_mem hz₀ a) (zpow_mem hz₁ b)
  have he : B.embLL (z₀ ^ a * z₁ ^ b) =
      Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
    rw [map_mul, map_zpow₀, map_zpow₀, e₀, e₁, hab]
  have hne : B.host.g 0 * B.host.g 1 ≠ 0 := mul_ne_zero p0.ne_zero p1.ne_zero
  have hint : IsIntegral ℤ (B.embLL (z₀ ^ a * z₁ ^ b)) := by
    rw [he]
    exact (Complex.isPrimitiveRoot_exp _ hne).isIntegral (Nat.pos_of_ne_zero hne)
  have hint' : IsIntegral ℤ (z₀ ^ a * z₁ ^ b) :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hint
  refine ⟨⟨⟨z₀ ^ a * z₁ ^ b, hmem⟩, ?_⟩, he⟩
  exact (isIntegral_algHom_iff (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom Subtype.val_injective).1 hint'

theorem hermitianCodeWordStages_has_rootOfUnity : ∀ X : Stages, OZeta X.toD7 := fun X => X.B.exists_root_mul

end GlobalTheory.Mem
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem Base.OtoLL_injective' (B : Base) : Function.Injective B.OtoLL := by
  intro x y h
  apply RingOfIntegers.ext
  exact Subtype.ext h

theorem hermitianCodeWordStages_ringOfIntegers_full : ∀ X : Stages, OFull X.toD7 := by
  intro X
  refine ⟨X.B.OtoLL_injective', ?_⟩
  let f : X.B.Ks →+* ℂ := X.B.embLL.comp (algebraMap X.B.Ks X.B.LL)
  have hle : FO X.toD7 ≤ f.toRatAlgHom.fieldRange := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 X.B.Ks) X.B.Ks y, rfl⟩
  intro z hz hint
  obtain ⟨x, rfl⟩ := hle hz
  have hx : IsIntegral ℤ x := (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 hint
  exact ⟨(⟨x, hx⟩ : 𝓞 X.B.Ks), rfl⟩

end GlobalTheory.Mem
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem mem_FO_assembled_iff :
    ∀ (X : Stages) (z : ℂ), z ∈ FO X.toD7 ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z := by
  intro X z
  have hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL) := fun _ => rfl
  constructor
  · intro hz
    have hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact ⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩
    obtain ⟨x, hx, rfl⟩ := hle hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)
    have hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL) := by
      have := congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab
      exact this.symm
    rw [hx', map_div₀, ← hphi a, ← hphi b]
    exact div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)

end GlobalTheory.Mem
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem iSup_range_weight_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  intro E _ _ _ n π τ lam h
  obtain ⟨-, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.exists_embRet E n τ
  have heq : (GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  have hσ : Representation.IsIrreducible ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
    rw [heq]
    exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)
  let F : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype))
      (π.rep.comp (embU n τ).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h0 =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))
  exact (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (embU n τ) π.V _ _ π.rep (embU n τ).subtype _ _
    π.isIrreducible_rep hσ hσ (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

end GlobalTheory.DefU
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InfSurj

theorem list_prod_single {G ι : Type} [Monoid G] [DecidableEq ι] (v : ι) (a : G) :
    ∀ l : List ι, l.Nodup → v ∈ l → (l.map fun u => if u = v then a else 1).prod = a
  | [], _, h => absurd h List.not_mem_nil
  | u :: l, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.prod_cons]
    by_cases hu : u = v
    · subst hu
      have : (l.map fun w => if w = u then a else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun w hw => if_neg fun (e : w = u) => hn.1 (e ▸ hw)
      rw [if_pos rfl, this, List.prod_map_one, mul_one]
    · rw [if_neg hu, one_mul]
      exact list_prod_single v a l hn.2 ((List.mem_cons.1 h).resolve_left (Ne.symm hu))

end GlobalTheory.InfSurj

theorem GlobalTheory.InfSurj.exists_infU_cAll_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  intro E _ _ _ n g hg
  classical
  have he := fun v : InfinitePlace E => GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
  choose e he using he
  let y : InfinitePlace E → UA E n := fun v => ((e v).symm ⟨(g v : Matrix (Fin n) (Fin n) ℂ), hg v⟩ : embU n v.embedding)
  have hy : ∀ v, y v ∈ embU n v.embedding := fun v => ((e v).symm _).2
  have hyv : ∀ v, cEmb v.embedding (y v) = g v := fun v => by
    rw [← he v, ContinuousMulEquiv.apply_symm_apply]
    ext i j
    rfl
  have hyu : ∀ u v, u ≠ v → cEmb v.embedding (y u) = 1 := fun u v huv => by
    have h := (Subgroup.mem_inf.1 (hy u)).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h v.embedding
    rw [Subgroup.mem_iInf] at h2
    exact h2 (by rw [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]; exact Ne.symm huv)
  refine ⟨(Finset.univ.toList.map y).prod, ?_, ?_⟩
  · refine (infU E n).list_prod_mem fun z hz => ?_
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact (Subgroup.mem_inf.1 (hy u)).1
  · funext v
    change cEmb v.embedding _ = g v
    rw [map_list_prod, List.map_map]
    have : (Finset.univ.toList.map (cEmb v.embedding ∘ y)) = Finset.univ.toList.map fun u => if u = v then g v else 1 :=
      List.map_congr_left fun u _ => by
        by_cases h : u = v
        · subst h; simp [hyv]
        · simp [h, hyu u v h]
    rw [this]
    exact GlobalTheory.InfSurj.list_prod_single v (g v) _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ v))
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.algebraicHeckeCharacter_value_mem_kummerField : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [_root_.NumberField.IsTotallyComplex L] (φ₀ : L →+* ℂ) (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∀ (v : HeightOneSpectrum (𝓞 L)) (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → χ.inf k * χ.val v ^ h = 1 → χ.valTw ((r : ℝ) / 2) v ∈ kummerField φ₀ h := by
  first | exact @GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField | exact GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField | (intros; apply GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.rootsOfUnity_mem_rayClassField_of_multiple : ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K)) (p : ℕ), p ≠ 0 → 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → IsRayField K M 𝔮 → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧ IsFrob L v σ} = ⊤ → (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  first | exact @GlobalTheory.Mem.RayZeta.root_mem_rayField | exact GlobalTheory.Mem.RayZeta.root_mem_rayField | (intros; apply GlobalTheory.Mem.RayZeta.root_mem_rayField <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.local_lattice_span_at_place : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Pl : Rows.Places K) i (hF : ((I.S i).fam emb (lamT hc i)).Ok) (w : Pl.Pl) P, Submodule.span K (locW Pl w (BLat J emb hc i hF P) : Set ((I.S i).hlat emb (lamT hc i) hF).V) = ⊤ := by
  first | exact @GlobalTheory.Mem.BSpan.span_locW_BLat | exact GlobalTheory.Mem.BSpan.span_locW_BLat | (intros; apply GlobalTheory.Mem.BSpan.span_locW_BLat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact GlobalTheory.Mem.LatGood.lawGood S emb σ lam hF hS hS.lsh_full_lat h
end
