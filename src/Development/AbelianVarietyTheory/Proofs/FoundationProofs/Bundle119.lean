module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle094
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KZero

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected

theorem eventually_ne_zero {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb0 : (b : Mero) ≠ 0) :
    ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
  have hA : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs
  obtain ⟨z0, hz0, hbz0⟩ : ∃ z0 ∈ Hs, b z0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb0 (Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) h))
  have h0 : analyticOrderAt b z0 ≠ ⊤ := by
    rw [(hA z0 hz0).analyticOrderAt_eq_zero.2 hbz0]; exact ENat.zero_ne_top
  filter_upwards [hA.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top,
    Filter.self_mem_codiscreteWithin Hs] with z hz hzH
  rcases hz with hz | hz
  · exact (hA z hzH).analyticOrderAt_eq_zero.1 hz
  · exact absurd hz (hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_Hs hz0 hzH h0)

theorem cast_of_mul {M M' : ℕ} {x : ℤ} {y : ℤ} (h : (x : ZMod (M * M')) = y) : (x : ZMod M) = y := by
  have := congrArg (ZMod.castHom (dvd_mul_right M M') (ZMod M)) h
  simpa using this

theorem gamma_mul_le {M M' : ℕ} : CongruenceSubgroup.Gamma (M * M') ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast cast_of_mul (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast cast_of_mul (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast cast_of_mul (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast cast_of_mul (y := 1) (by exact_mod_cast h4)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_pow_eq_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (G : X.Kˣ) : X.cls l n (G ^ (l ^ n)) = 0 := by
  rw [Tower.cls, Submodule.Quotient.mk_eq_zero, ofMul_pow]
  have e : (1 : ℤ_[l]) ⊗ₜ[ℤ] ((l ^ n) • Additive.ofMul G) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul G) := by
    rw [← natCast_zsmul, TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast
    rfl
  rw [e]
  have hl : (l : ℤ_[l]) ∈ idl l := Ideal.subset_span (Set.mem_singleton _)
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top

end GlobalTheory.KZ.H3.KZero

namespace GlobalTheory.KZ.H3


open KZero in
theorem kum_near_zero_eval : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  intro Ω _ _ ε X l _ n x χ hK hN
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hroot⟩, hχ⟩ := hK
  obtain ⟨M', hM', hz⟩ := hN
  have hmpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hne := eventually_ne_zero hb hb0
  obtain ⟨φ, hφ⟩ := Quot.exists_rep (X.an (f : X.K))
  have hφ' : X.an (f : X.K) = (φ : Mero) := hφ.symm
  rw [hφ', ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hroot

  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma (M * M'),
      ((fun z => a (mob (ofSL γ) z) * b z : ℂ → ℂ) : Mero) = ((fun z => a z * b (mob (ofSL γ) z) : ℂ → ℂ) : Mero) := by
    intro γ hγ
    have h1 : γ ∈ CongruenceSubgroup.Gamma M := gamma_mul_le hγ
    have h2 : γ ∈ CongruenceSubgroup.Gamma M' := gamma_mul_le (M := M') (M' := M) (by rw [mul_comm]; exact hγ)
    refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz' => ?_)
    have := hχ γ h1 z hz'
    rw [hz γ h2] at this
    simpa using this

  have hP : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ (l ^ n) - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hmpos _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ', sub_eq_zero, ← Filter.Germ.coe_pow,
      Filter.Germ.coe_eq]
    filter_upwards [hroot, hne] with z h1 h2
    simp only [Pi.pow_apply, Pi.div_apply, Pi.mul_apply] at h1 ⊢
    rw [div_pow, ← h1]
    field_simp
  obtain ⟨g, hg⟩ := X.sat a b (M * M') (Nat.mul_pos hM hM') ha hb hb0 hlev hP
  obtain ⟨ψ, hψ⟩ := Quot.exists_rep (X.an g)
  have hψ' : X.an g = (ψ : Mero) := hψ.symm
  rw [hψ', ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hg
  haveI : Nontrivial Mero := ⟨⟨(b : Mero), 0, hb0⟩⟩
  have hgm : g ^ (l ^ n) = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ', hφ', ← Filter.Germ.coe_pow, Filter.Germ.coe_eq]
    filter_upwards [hroot, hg, hne] with z h1 h2 h3
    simp only [Pi.pow_apply, Pi.mul_apply] at h1 h2 ⊢
    have h4 : ψ z ^ (l ^ n) * b z ^ (l ^ n) = φ z * b z ^ (l ^ n) := by rw [← mul_pow, h2, h1]
    exact mul_right_cancel₀ (pow_ne_zero _ h3) h4
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hmpos.ne'] at hgm
    exact f.ne_zero hgm.symm
  have hfG : f = (Units.mk0 g hg0) ^ (l ^ n) := by
    ext; simp [hgm]
  rw [hx, hfG]
  exact cls_pow_eq_zero X l n _

end GlobalTheory.KZ.H3
end

section

noncomputable section

namespace GlobalTheory.Glue.IoInh

open GlobalTheory.K5 GlobalTheory.KZ

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem ev_single (ψ : O0 p →+* Ωl) (e : Ωl) (h1 : IsInt (p := p) e) (h2 : IsAlgZp p e) (a : Lau p) (c : ℤ → Ωl)
    (hc : ∀ r, c r = e * zp Ωl (a.coeff r)) :
    Ev ψ c (e * ψ (algebraMap (Lau p) (O0 p) a)) (e * ψ (algebraMap (Lau p) (O0 p) (thL a))) :=
  ⟨1, fun _ => e, fun _ => a, fun _ => ⟨h1, h2⟩, fun r => by simp [hc], by simp, by simp⟩

theorem zp_intCast (m : ℤ) : zp Ωl (m : ℤ_[p]) = (m : Ωl) := by
  rw [zp, ← HahnSeries.C_apply, map_intCast, map_intCast, map_intCast]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem const_mem (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : algebraMap Ω X.K c ∈ KT X L :=
  (X.sl _).commutes c

theorem exp_const (X : GlobalTheory.KZ.Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ}
  {ψ : O0 p →+* Ωl} {io : KT X (p ^ n) →+* Ωl}

theorem io_const_of_mem (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) (hA : c ∈ A) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  classical
  obtain ⟨x', hx⟩ := hio.ev ⟨algebraMap Ω X.K c, const_mem X _ c⟩ {c} (fun r => by
    simp only [exp_const]
    split_ifs
    · exact ⟨hA, IntermediateField.subset_adjoin _ _ (by simp)⟩
    · exact ⟨zero_mem _, zero_mem _⟩)
  have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have h2 := ev_single ψ (j c) ((hc.int c).1 hA) (hc.alg c) 1
    (fun r : ℤ => j ((X.exp (algebraMap Ω X.K c)).coeff ((r : ℚ) / (p : ℚ) ^ n))) (fun r => by
      simp only [exp_const]
      by_cases hr : r = 0
      · subst hr
        have : zp Ωl (1 : ℤ_[p]) = 1 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 1
        simp [this]
      · have : zp Ωl (0 : ℤ_[p]) = 0 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 0
        have h3 : (r : ℚ) / (p : ℚ) ^ n ≠ 0 := div_ne_zero (by exact_mod_cast hr) hp0
        simp [this, h3, HahnSeries.coeff_one, hr])
  have := (GlobalTheory.EvUniq.ev_unique p Ωl h T n ψ hψ _ _ _ _ _ hx h2).1
  rwa [map_one, map_one, mul_one] at this

theorem io_const (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  rcases A.mem_or_inv_mem c with hA | hA
  · exact io_const_of_mem h hc hψ hio c hA
  · have h1 := io_const_of_mem h hc hψ hio c⁻¹ hA
    have h2 : (⟨algebraMap Ω X.K c⁻¹, const_mem X _ c⁻¹⟩ : KT X (p ^ n)) = ⟨algebraMap Ω X.K c, const_mem X _ c⟩⁻¹ :=
      Subtype.ext (map_inv₀ _ _)
    rw [h2, map_inv₀, map_inv₀] at h1
    exact inv_injective h1

end Local

end GlobalTheory.Glue.IoInh
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3

open Filter Topology

theorem isOpen_Hs_place : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isConnected_Hs_place : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

theorem exists_analyticAt_of_order_nonneg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ Hs) (f : X.K) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : X.an f * (b : Mero) = (a : Mero))
    (hord : 0 ≤ meromorphicOrderAt (a / b) τ) :
    ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs_place
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs_place
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs_place
  have hM : MeromorphicAt (a / b) τ := (hA τ hτ).meromorphicAt.div (hB τ hτ).meromorphicAt
  refine ⟨toMeromorphicNFAt (a / b) τ, ?_, hM.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord⟩
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have h2 : X.an f = ((a / b : ℂ → ℂ) : Mero) := by
    calc X.an f = X.an f * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (X.an f * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  rw [h2]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [compl_finite_mem_codiscreteWithin (s := Hs) (Set.finite_singleton τ)] with z hz
  exact hM.eqOn_compl_singleton_toMeromorphicNFAt hz

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

open Filter Topology

theorem exists_place_at_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs,
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  intro Ω _ _ ε X hj τ hτ
  have h0 : ∃ φ : ℂ → ℂ, X.an 0 = (φ : Mero) ∧ AnalyticAt ℂ φ τ :=
    ⟨0, by rw [map_zero, Filter.Germ.coe_zero], analyticAt_const⟩
  let W : ValuationSubring X.K :=
    { carrier := {f | ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ}
      zero_mem' := h0
      one_mem' := ⟨1, by rw [map_one, Filter.Germ.coe_one], analyticAt_const⟩
      add_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ + ψ, by rw [map_add (f := _), h1, h3, Filter.Germ.coe_add], h2.add h4⟩
      mul_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ * ψ, by rw [map_mul, h1, h3, Filter.Germ.coe_mul], h2.mul h4⟩
      neg_mem' := by
        rintro f ⟨φ, h1, h2⟩
        exact ⟨-φ, by rw [map_neg, h1, Filter.Germ.coe_neg], h2.neg⟩
      mem_or_inv_mem' := by
        intro f
        by_cases hf : f = 0
        · left; rw [hf]; exact h0
        obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero f
        have hu : X.an f⁻¹ * X.an f = 1 := by rw [← map_mul, inv_mul_cancel₀ hf, map_one]
        by_cases hord : 0 ≤ meromorphicOrderAt (a / b) τ
        · left
          exact exists_analyticAt_of_order_nonneg X hτ f a b ha hb hb0 hab hord
        · right
          have ha0 : (a : Mero) ≠ 0 := by
            intro h
            apply hb0
            calc (b : Mero) = X.an f⁻¹ * (X.an f * (b : Mero)) := by rw [← mul_assoc, hu, one_mul]
              _ = 0 := by rw [hab, h, mul_zero]
          have hba : X.an f⁻¹ * (a : Mero) = (b : Mero) := by rw [← hab, ← mul_assoc, hu, one_mul]
          have hinv : b / a = (a / b)⁻¹ := by
            funext z; simp [inv_div]
          have hord' : 0 ≤ meromorphicOrderAt (b / a) τ := by
            rw [hinv, meromorphicOrderAt_inv]
            push_neg at hord
            generalize meromorphicOrderAt (a / b) τ = o at hord ⊢
            induction o with
            | top => simp at hord
            | coe n =>
              have hn : n < 0 := by exact_mod_cast hord
              have : (0 : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ -n)
              simpa using this
          exact exists_analyticAt_of_order_nonneg X hτ f⁻¹ b a hb ha ha0 hba hord' }
  refine ⟨W, ⟨fun c => ⟨fun _ => ε c, X.an_c c, analyticAt_const⟩, ?_⟩, fun f => Iff.rfl⟩
  obtain ⟨φ, h1, h2⟩ := hj
  exact ⟨φ, h1, h2.analyticAt (isOpen_Hs_place.mem_nhds hτ)⟩

end GlobalTheory.KZ.H3
end
end

section

noncomputable section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

open PowerSeries in
private theorem one_add_X_pow_eq_sum_fin_choose {R : Type} [CommRing R] (p j : ℕ) (hj : j < p) :
    (1 + X : R⟦X⟧) ^ j = ∑ i : Fin p, ((j.choose i : ℕ) : R⟦X⟧) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]
  have hsub : Finset.range (j + 1) ⊆ Finset.range p := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub (fun i _ hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mul_comm]

open PowerSeries in
private theorem subsingleton_of_isUnit_natCast_of_isAdicComplete {R : Type} [CommRing R] (p : ℕ)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (hu : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
  constructor
  intro a b
  have h := hR.toIsHausdorff.haus (a - b) (fun n => by
    rw [htop, Ideal.top_pow, Submodule.top_smul]; exact SModEq.top)
  exact sub_eq_zero.1 h


open PowerSeries in
theorem _root_.GlobalTheory.Col.exists_basis_one_add_X_pow (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) :
    ∃ b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      (@Algebra.toModule _ _ _ _ (_root_.GlobalTheory.Col.phi (R := R) p hp.out.pos).toRingHom.toAlgebra), ∀ i, b i = (1 + X) ^ (i : ℕ) := by
  by_cases hn : (p : R) ∈ nonunits R
  · haveI := hR
    set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn
    have he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ)) := fun i => by
      show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _
      unfold _root_.GlobalTheory.Col.Model.basis
      rw [Module.Basis.mk_apply]
      rfl
    let v : Fin p → _root_.GlobalTheory.Col.Model.Up R p :=
      fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))
    have hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i := by
      intro j
      simp only [he, Algebra.smul_def, map_natCast]
      exact one_add_X_pow_eq_sum_fin_choose p j j.2
    have hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧) := by
      intro j i
      rw [hv, e.repr_sum_self]
    have hdet : e.det v = 1 := by
      rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular]
      · simp [Module.Basis.toMatrix_apply, hrepr]
      · intro i j hij
        simp [Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
    obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) := Module.Basis.mk hli hspan.ge
    have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan.ge i
    exact ⟨b, hb⟩
  · have hu : IsUnit (p : R) := by simpa [mem_nonunits_iff] using hn
    haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu
    haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧›
    haveI : Subsingleton (Fin p →₀ R⟦X⟧) := ⟨fun a b => Finsupp.ext fun i => Subsingleton.elim _ _⟩
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) :=
      Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
    have hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ)) := fun i => Subsingleton.elim _ _
    exact ⟨b, hb⟩

end GlobalTheory.Col
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem isAlgZp_tower_zeta {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : IsAlgZp (p := p) (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
  · simp [(T.prim n).pow_eq_one]

theorem mem_of_fixed_ggeo_gn : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) →
    (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F →
    ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p _ Ω _ _ hc T n F hO hA hq o ho
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  haveI : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  letI : Algebra (O0 p) F := f.toAlgebra
  haveI : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) := fun a b h => hc.inj (congrArg Subtype.val h)
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  haveI : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have key := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) o).2 fun σ => by
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ (isAlgZp_tower_zeta T n)⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := key
  exact x.2

end GlobalTheory.GeoFix
end

section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.ramified_divisibility_of_unramified_divisibility : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (v : Valuation Ω ℝ≥0) (ψ : O0 p →+* Ω) (E F : ℕ) (π : Ω) (κ : Fin F → Ω), 1 ≤ E → 0 < v (p : Ω) → v (p : Ω) < 1 → v π ^ E = v (p : Ω) → (∀ j, v (κ j) ≤ 1) → (∀ y, v (ψ y) ≤ 1) → (∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 → ∀ j, (p : Lau p) ∣ b j) → ∀ b : Fin F → Fin E → Lau p, v (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s := by
  first | exact @GlobalTheory.KZ.ramified_divisible_of_unramified | exact GlobalTheory.KZ.ramified_divisible_of_unramified | (intros; apply GlobalTheory.KZ.ramified_divisible_of_unramified <;> assumption)
end
