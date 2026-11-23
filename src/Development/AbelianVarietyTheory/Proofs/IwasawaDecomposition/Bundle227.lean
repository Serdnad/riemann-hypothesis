module

public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.TwQCmp
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductTorusWeightBlockTranslates
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IdemOf (F : Type) [Field F] [NumberField F] [Algebra F E] (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ε * ε = ε ∧ ∀ x : 𝓞 E, x ≠ 0 → (x ∈ Q.asIdeal ↔ ε * iA F E ((x : E)⁻¹) ∉ Formalism.L2.Herm.intAf F E)

namespace IdemOf

variable {Q : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε)
include h

theorem div_mem {t : 𝓞 E} (ht : t ∉ Q.asIdeal) : ε * iA F E ((t : E)⁻¹) ∈ Formalism.L2.Herm.intAf F E := by
  have t0 : t ≠ 0 := fun h0 => ht (h0 ▸ Q.asIdeal.zero_mem)
  by_contra hn
  exact ht ((h.2 t t0).2 hn)

theorem mem : ε ∈ Formalism.L2.Herm.intAf F E := by
  have := h.div_mem (one_notMem Q)
  simpa using this

theorem one_sub_mem : 1 - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) h.mem

theorem mul_one_sub : ε * (1 - ε) = 0 := by rw [mul_sub, h.1, mul_one, sub_self]

theorem mul_mem_of_val {x : E} (hx : Q.valuation E x ≤ 1) : ε * iA F E x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨a, t, ht, e⟩ := qsp_frac Q x hx
  have t0 : (t : E) ≠ 0 := fun h0 => ht (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e2 : x = (t : E)⁻¹ * algebraMap (𝓞 E) E a := by
    rw [← e]; field_simp
  rw [e2, map_mul, ← mul_assoc]
  exact mul_mem (h.div_mem ht) (iA_mem a)

theorem resS_eq_zero {w : Pl E} (hw : w ≠ Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : ε * a ∈ Formalism.L2.Herm.intAf F E) :
    resS F w ⟨ε * a, ha⟩ = 0 := by
  obtain ⟨t, htw, htQ⟩ : ∃ t ∈ w.asIdeal, t ∉ Q.asIdeal := by
    by_contra hn
    push Not at hn
    exact hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hn))
  have t0 : (t : E) ≠ 0 := fun h0 => htQ (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e : (⟨ε * a, ha⟩ : Formalism.L2.Herm.intAf F E) = oToS F E t * (⟨_, h.div_mem htQ⟩ * ⟨ε * a, ha⟩) := by
    apply Subtype.ext
    show ε * a = iA F E (t : E) * (ε * iA F E ((t : E)⁻¹) * (ε * a))
    have : iA F E (t : E) * iA F E ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ t0, map_one]
    linear_combination (-(ε * a) * ε) * this - a * h.1
  rw [e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htw, zero_mul]

omit h in
theorem val_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    Q.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
  rw [show (ϖ : E) = algebraMap (𝓞 E) E ϖ from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (Q.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have a2 := (Q.intValuation_le_pow_iff_mem ϖ 2).not.2 h2
  have h0 : Q.intValuation ϖ ≠ 0 := fun h0 => a2 (by rw [h0]; exact zero_le)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log h0]
  congr 1
  push_cast at a1 a2
  omega

omit h in
theorem unif_ne {ϖ : 𝓞 E} (h2 : ϖ ∉ Q.asIdeal ^ 2) : (ϖ : E) ≠ 0 := fun h0 =>
  h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)

theorem div_pow_mem {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) {a : Formalism.L2.Herm.intAf F E}
    (ha : a ∈ idS F (Q.asIdeal ^ m)) :
    ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine Submodule.span_induction
    (p := fun (a : Formalism.L2.Herm.intAf F E) _ => ε * iA F E (((ϖ : E) ^ m)⁻¹) * (a : E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨p, hp, rfl⟩
    rw [← iA_coe, mul_assoc, ← map_mul]
    refine h.mul_mem_of_val ?_
    have a1 := (Q.intValuation_le_pow_iff_mem p m).2 hp
    rw [map_mul, map_inv₀, map_pow, val_unif h1 h2, HeightOneSpectrum.valuation_of_algebraMap, ← WithZero.exp_nsmul,
      inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
    simpa using a1
  · simp
  · intro a b _ _ ha hb
    rw [Subring.coe_add, mul_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem c.2 ha

theorem one_sub_mem_idS [StarRing E] (m : ℕ) : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) ∈ idS F (Q.asIdeal ^ m) := by
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q.asIdeal Q.ne_bot Q.isPrime.ne_top 1
  rw [pow_one] at h1
  have hi : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨ε, h.mem⟩ = 0 :=
    Subtype.ext (by show (1 - ε) * ε = 0; rw [mul_comm, h.mul_one_sub])
  have h3 : resS F Q ⟨1 - ε, h.one_sub_mem⟩ = 0 := by
    have := congrArg (resS F Q) hi
    rw [map_mul, map_zero] at this
    refine (mul_eq_zero.1 this).resolve_right fun h0 => ?_
    have h4 := h.div_pow_mem h1 h2 1 (a := ⟨ε, h.mem⟩) (by rw [pow_one]; exact mem_idS_of_resS h0)
    have ϖ0 : ϖ ≠ 0 := fun h0 => h2 (h0 ▸ zero_mem _)
    refine (h.2 ϖ ϖ0).1 h1 ?_
    rwa [pow_one, mul_right_comm, h.1] at h4
  have h5 := Ideal.pow_mem_pow (mem_idS_of_resS h3) m
  have h6 : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨1 - ε, h.one_sub_mem⟩ = ⟨1 - ε, h.one_sub_mem⟩ :=
    Subtype.ext (by show (1 - ε) * (1 - ε) = 1 - ε; linear_combination h.1)
  rcases m with _ | m
  · unfold idS
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial
  · rw [IsIdempotentElem.pow_succ_eq m h6] at h5
    unfold idS at h5 ⊢
    rwa [Ideal.map_pow]

theorem mem_idS_pow_iff [StarRing E] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) (a : Formalism.L2.Herm.intAf F E) :
    a ∈ idS F (Q.asIdeal ^ m) ↔ ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨h.div_pow_mem h1 h2 m, fun ha => ?_⟩
  have e : a = oToS F E (ϖ ^ m) * ⟨_, ha⟩ + ⟨1 - ε, h.one_sub_mem⟩ * a := by
    apply Subtype.ext
    show (a : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * (ε * iA F E (((ϖ : E) ^ m)⁻¹) * a) + (1 - ε) * a
    have : iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * iA F E (((ϖ : E) ^ m)⁻¹) = 1 := by
      rw [← map_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ (unif_ne h2)), map_one]
    linear_combination (-(ε * (a : E ⊗[F] Formalism.L2.Herm.Af F))) * this
  rw [e]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow h1 m)))
    (Ideal.mul_mem_right _ _ (h.one_sub_mem_idS m))

end IdemOf

end GlobalTheory.InertNbr
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft NumberField

namespace GlobalTheory.GeoModel

variable (D : D7)

def fracO : IntermediateField ℚ D.what₂.LL := IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

theorem otoLL_mem (y : D.what₂.O) : D.what₂.OtoLL y ∈ fracO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

variable {D} {T : HostTied D} {C : CharFrame D}

def toInt (h : OTied D T C) : D.what₂.O →+* 𝓞 (fracO D) where
  toFun y := ⟨⟨D.what₂.OtoLL y, otoLL_mem D y⟩, by
    have hq : IsIntegral ℤ (T.jLL (D.what₂.OtoLL y)) := ((h.range _).1 ⟨y, rfl⟩).2
    let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
    have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
    exact (isIntegral_algHom_iff f hf).1 hq⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; exact map_mul D.what₂.OtoLL a b
  map_zero' := by ext; simp
  map_add' a b := by ext; exact map_add D.what₂.OtoLL a b

theorem toInt_val (h : OTied D T C) (y : D.what₂.O) : ((toInt h y : fracO D) : D.what₂.LL) = D.what₂.OtoLL y := rfl

theorem toInt_bijective (h : OTied D T C) : Function.Bijective (toInt h) := by
  refine ⟨fun a b hab => h.inj ?_, fun z => ?_⟩
  · have := congrArg (fun w : 𝓞 (fracO D) => ((w : fracO D) : D.what₂.LL)) hab
    simpa [toInt_val] using this
  · set x : D.what₂.LL := ((z : fracO D) : D.what₂.LL) with hx
    have hint : IsIntegral ℤ (T.jLL x) := by
      let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
      have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
      exact (isIntegral_algHom_iff f hf).2 z.2
    have hmem : T.jLL x ∈ KsQ D T C h.pieces := by
      have hx' : x ∈ fracO D := (z : fracO D).2
      have h1 : T.jLL x ∈ (fracO D).map T.jLL.toRatAlgHom := ⟨x, hx', rfl⟩
      rw [fracO, IntermediateField.adjoin_map] at h1
      refine (IntermediateField.adjoin_le_iff.2 ?_) h1
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ((h.range _).1 ⟨y, rfl⟩).1
    obtain ⟨y, hy⟩ := (h.range _).2 ⟨hmem, hint⟩
    refine ⟨y, ?_⟩
    ext
    exact T.jLL.injective hy

def eO (h : OTied D T C) : 𝓞 (fracO D) ≃+* D.what₂.O := (RingEquiv.ofBijective _ (toInt_bijective h)).symm

end GlobalTheory.GeoModel
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)
      have h3 := mul_mem h2 h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
      exact h3
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

theorem toEAf_incA (D : D7) (x : D.host.E) : toEAf D (incA D x) = eToEAf D x := rfl

theorem eToEAf_int (D : D7) (x : 𝓞 D.host.E) :
    eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)

theorem conj_mem_at (D : D7) (e : AE D) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have hi : IsIntegral ℤ (D.sp.cm.sig (c : D.host.E)) :=
    (show IsIntegral ℤ (c : D.host.E) from c.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom
  have h3 := mul_mem h2 (eToEAf_int D ⟨_, hi⟩)
  rw [map_mul, toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  change D.sp.cm.sig a = ((n : 𝓞 D.host.E) : D.host.E)⁻¹ * D.sp.cm.sig (c : D.host.E)
  rw [hc', hcast, map_mul, map_natCast]
  field_simp

theorem conj_mem_intAf : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rintro D e P ⟨⟨es, hes, rfl⟩, -⟩ hP a ha

  rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => conj_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

end GlobalTheory.IdemIntegral
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RedAdjCong

theorem conj_smul_entry {E R : Type} [CommRing E] [CommRing R] (φ : E →+* R) {m n : ℕ} (t : R) (d : E)
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (G : Matrix (Fin m) (Fin m) E)
    (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin m) (Fin n) E) (i : Fin m) (j : Fin n) :
    t * (A * (G * (d • M) * H).map φ * B) i j = φ d * (t * (A * (G * M * H).map φ * B) i j) := by
  have h2 : ∀ N : Matrix (Fin m) (Fin n) E, (d • N).map φ = φ d • N.map φ := by
    intro N
    ext b a
    simp
  rw [Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    mul_left_comm]

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)

theorem adj_add (X Y : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => X b + Y b) i j = uMat S T βS βT e X i j + uMat S T βS βT e Y i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((X b + Y b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = (Matrix.of fun b a => D.sp.cm.sig (X b a)) + (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add (eToEAf D)), Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, mul_add]

theorem adj_smul (c : D.host.E) (X : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => c • X b) i j = eToEAf D (D.sp.cm.sig c) * uMat S T βS βT e X i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((c • X b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (X b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h]
  exact conj_smul_entry (eToEAf D) _ _ _ _ _ _ _ i j

end GlobalTheory.RedAdjCong

namespace GlobalTheory


open GlobalTheory.RedAdjCong in
theorem redM_adj_congr : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E), (∀ a ∈ J, ∃ a' ∈ PP.asIdeal, (a' : D.host.E) = star (a : D.host.E)) → ∀ x x' : Fin S.rank → La, (∀ b, x b - x' b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) := by
  intro D S T βS βT e La _ _ ι hint J PP hJ x x' hx
  ext i j
  let f : (Fin S.rank → La) →+ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    AddMonoidHom.mk' (fun y => ⟨uMat S T βS βT e (fun b => ι (y b)) i j, hint y i j⟩) (by
      intro y z
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (y b + z b)) i j = _ + _
      simp only [map_add (f := _)]
      exact adj_add S T βS βT e _ _ i j)
  let g : (Fin S.rank → La) →+ kP PP := (resS D.host.F PP).toAddMonoidHom.comp f
  have hg : ∀ y, redM PP (uMat S T βS βT e fun b => ι (y b)) i j = g y := by
    intro y
    unfold redM
    rw [dite_eq_left (hint y i j)]
    rfl
  have hs : ∀ a ∈ J, ∀ y : Fin S.rank → La, g (a • y) = 0 := by
    intro a ha y
    obtain ⟨a', ha', hc⟩ := hJ a ha
    have h1 : f (a • y) = oToS D.host.F D.host.E a' * f y := by
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (a • y b)) i j = eToEAf D (a' : D.host.E) * uMat S T βS βT e (fun b => ι (y b)) i j
      rw [hc]
      simp only [map_smul]
      exact adj_smul S T βS βT e (a : D.host.E) (fun b => ι (y b)) i j
    show resS D.host.F PP (f (a • y)) = 0
    rw [h1, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', zero_mul]
  have h0 : ∀ (b : Fin S.rank) (l : La), l ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) → g (Pi.single b l) = 0 := by
    intro b l hl
    refine Submodule.smul_induction_on hl ?_ ?_
    · intro a ha m _
      rw [Pi.single_smul']
      exact hs a ha _
    · intro u v hu hv
      rw [Pi.single_add, map_add (f := _), hu, hv, add_zero]
  have h3 : g (x - x') = 0 := by

    rw [← Finset.univ_sum_single (x - x'), map_sum]
    exact Finset.sum_eq_zero fun b _ => h0 b _ (hx b)
  rw [hg, hg]
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.FockTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ptStable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  intro D ψ θ hψ hθ S T sS sT BS BT f P hf
  exact (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

end GlobalTheory.FockTheta

end
end

section

open Formalism.BasicNotions

namespace GlobalTheory.VecTheta

theorem vecThetaSD : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_stepVec h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_thPVec h⟩

end GlobalTheory.VecTheta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.minorProduct_torusWeight_block_translates : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (τ : D.what₂.Tau), ∃ e : Fin m → ℕ, (∀ (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (l : Fin m → ℂ), (∀ ρ, ρ ≠ τ → c ρ = 1) → c τ = Matrix.diagonal l → MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ)) (delta p q ap am : MvPolynomial (FVar D m n) ℂ) = (∏ a, l a ^ e a) • (delta p q ap am : MvPolynomial (FVar D m n) ℂ)) ∧ ∀ c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ ρ, ρ ≠ τ → c ρ = 1) → (∀ a b : Fin m, (b : ℕ) < p τ → p τ ≤ (a : ℕ) → c τ b a = 0) → ∀ s ∈ (MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ)) (delta p q ap am : MvPolynomial (FVar D m n) ℂ)).support, ∑ a : Fin m, (a : ℕ) * e a ≤ ∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j) := by
  first | exact @GlobalTheory.MinorWeight.delta_torus_weight | exact GlobalTheory.MinorWeight.delta_torus_weight | (intros; apply GlobalTheory.MinorWeight.delta_torus_weight <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.allPositive_model_finiteDimensional_compactType : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), M.ε τ = allPos V.rank → FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ IsURepOn (UJset (allPos V.rank)) (M.σ τ) ∧ IsKTypeOf (allPos V.rank) (M.σ τ) (Formalism.QuantumDeterminants.lowK (allPos V.rank) (M.lam τ)) ⊤ := by
  first | exact @GlobalTheory.CompactModel.model_allPos | exact GlobalTheory.CompactModel.model_allPos | (intros; apply GlobalTheory.CompactModel.model_allPos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowestKType_smoothVectors_isKStable : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), IsKStableOn (M.ε τ) (M.σ τ) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ) := by
  first | exact @GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm | exact GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm | (intros; apply GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm <;> assumption)
end
