module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Mathlib.RingTheory.FiniteType
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Topology.Sheaves.Presheaf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem reduced_finiteType_iff_testRing :
    ∀ (K : Type) [Field K], (∀ (R : Type) [CommRing R] [Algebra K R], Algebra.FiniteType K R → IsReduced R → ∃ p : TRing K, Nonempty (p.R ≃ₐ[K] R)) ∧ ∀ p : TRing K, Algebra.FiniteType K p.R ∧ IsReduced p.R := by
  intro K _
  refine ⟨fun R _ _ hft hred => ?_, fun p => ⟨inferInstance, ?_⟩⟩
  · obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
    have hrad : (RingHom.ker f).IsRadical := by
      intro x hx
      obtain ⟨m, hm⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hm
      exact (RingHom.mem_ker).2 (IsReduced.eq_zero _ ⟨m, hm⟩)
    exact ⟨⟨n, RingHom.ker f, hrad⟩, ⟨Ideal.quotientKerAlgEquivOfSurjective hf⟩⟩
  · exact (Ideal.isRadical_iff_quotient_reduced p.I).1 p.3

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.Relab

theorem relab_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H l c σ hσ
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0) := by
    intro τ'
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
    have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      rw [hval, ← hσ0]
      exact congrArg σ (Subtype.ext hx)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
          rw [← map_neg]
          exact congrArg σ (Subtype.ext hx)
        rw [← hval, h, hσ0] at h1
        exact h0 (by linear_combination h1 / 2)
      · exfalso
        exact h0 (by linear_combination (h.symm.trans hx) / 2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, hrel, ?_, ?_⟩
  · intro τ
    ext a
    have key : ∀ (ρ : E →+* ℂ) (x : E), conjEmb ρ x = ρ (IsCMField.complexConj E x) := fun ρ x =>
      (IsCMField.complexEmbedding_complexConj E ρ x).symm
    rw [key]
    exact congrArg σ (Subtype.ext (key τ a))
  · intro Dw g e τ
    obtain ⟨τ₀, rfl⟩ := hsurj τ
    have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
      have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
        Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
      have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
        e.subtypeEquiv (fun _ => Iff.rfl)
      have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀) := Equiv.sigmaSubtype τ₀
      rw [Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hcard]
      unfold Datum.mult
      rw [if_pos ((hrel τ₀).1 h)]
    · rw [hcard]
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hrel τ₀).2 h'))]

end GlobalTheory.Relab
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem two_mul_card_of_cmType_finset (E : Type) [Field E] [NumberField E]
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    2 * Ψ.card = Module.finrank ℚ E := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  rw [← NumberField.Embeddings.card E ℂ]
  have h1 : (Ψᶜ).card = Ψ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_
    · intro τ hτ
      rw [Finset.mem_compl] at hτ
      exact (hΨ _).mpr (by rw [hcc]; exact hτ)
    · intro a _ b _ h
      have := congrArg ComplexEmbedding.conjugate h
      rwa [hcc, hcc] at this
    · intro τ hτ
      refine ⟨ComplexEmbedding.conjugate τ, ?_, hcc τ⟩
      rw [Finset.mem_compl]
      exact (hΨ τ).mp hτ
  have h2 := Finset.card_add_card_compl Ψ
  omega

theorem finrank_skewHermitian_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ρ : ℕ) (Ψ : Finset (E →+* ℂ)),
      (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
      ∀ W : Submodule ℚ (Matrix (Fin ρ) (Fin ρ) E), (∀ β, β ∈ W ↔ FJ.IsSkew β) →
        Module.finrank ℚ W = Ψ.card * ρ ^ 2 := by
  intro E _ _ _ ρ Ψ hΨ W hW
  have hcard := two_mul_card_of_cmType_finset E Ψ hΨ
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : E, δ ≠ 0 ∧ IsCMField.complexConj E δ = -δ := by
    have hne : IsCMField.complexConj E ≠ 1 := IsCMField.complexConj_ne_one E
    obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply]
    ring
  have hW' : ∀ β, β ∈ W ↔ ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hW
  let f : (W × W) →ₗ[ℚ] Matrix (Fin ρ) (Fin ρ) E :=
    { toFun := fun p => (p.1 : Matrix (Fin ρ) (Fin ρ) E) + δ • (p.2 : Matrix (Fin ρ) (Fin ρ) E)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply,
          smul_comm δ c] }
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨A, B⟩ h
    have hA := (hW' _).mp A.2
    have hB := (hW' _).mp B.2
    have h0 : ∀ a b, (A : Matrix (Fin ρ) (Fin ρ) E) a b + δ * (B : Matrix (Fin ρ) (Fin ρ) E) a b = 0 :=
      fun a b => by
        have := congrFun (congrFun h a) b
        simpa [f] using this
    have h1 : ∀ a b, (A : Matrix (Fin ρ) (Fin ρ) E) a b = 0 ∧ (B : Matrix (Fin ρ) (Fin ρ) E) a b = 0 := by
      intro a b
      have e1 := h0 a b
      have e2 := congrArg (IsCMField.complexConj E) (h0 b a)
      rw [map_add (f := _), map_mul, hδ, hA, hB, map_zero] at e2
      have e3 : (A : Matrix (Fin ρ) (Fin ρ) E) a b = 0 := by linear_combination (e1 - e2) / 2
      refine ⟨e3, ?_⟩
      rw [e3, zero_add] at e1
      exact (mul_eq_zero.mp e1).resolve_left hδ0
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext a b; exact (h1 a b).1
    · ext a b; exact (h1 a b).2
  have hsurj : Function.Surjective f := by
    intro M
    refine ⟨(⟨Matrix.of fun a b => (M a b - IsCMField.complexConj E (M b a)) / 2, (hW' _).mpr ?_⟩,
      ⟨Matrix.of fun a b => (M a b + IsCMField.complexConj E (M b a)) / (2 * δ), (hW' _).mpr ?_⟩), ?_⟩
    · intro a b
      simp only [Matrix.of_apply, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_ofNat]
      ring
    · intro a b
      simp only [Matrix.of_apply, map_div₀, map_add (f := _), map_mul, hδ,
        IsCMField.complexConj_apply_apply, map_ofNat]
      field_simp
      ring
    · ext a b
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      field_simp
      ring
  have hfin := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_prod, Module.finrank_matrix, ← hcard, Fintype.card_fin] at hfin
  have : 2 * Module.finrank ℚ W = 2 * (Ψ.card * ρ ^ 2) := by
    rw [two_mul, hfin]; ring
  omega

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := by simp [cc]
theorem cc_mul' (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]
theorem cc_neg' (x : E) : cc (-x) = -cc x := by simp [cc]
theorem cc_zero' : cc (0 : E) = 0 := by simp [cc]
theorem cc_cc' (x : E) : cc (cc x) = x := by simp [cc]
theorem cc_sum' {ι : Type} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]

theorem herm_add_l (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_add_r (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp [herm, cc_add', mul_add, Finset.sum_add_distrib]

theorem herm_comb_l (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (y : Fin r → E) : herm G (∑ a, c a • e a) y = ∑ a, c a * herm G (e a) y := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_comb_r (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (x : Fin r → E) : herm G x (∑ a, c a • e a) = ∑ a, cc (c a) * herm G x (e a) := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cc_sum', cc_mul', Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_swap (X : Data E r) (x y : Fin r → E) : herm X.Gm x y = cc (herm X.Gm y x) := by
  simp only [herm, cc_sum', cc_mul', cc_cc', X.Gm_herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem herm_nondeg (X : Data E r) (w : Fin r → E) (h : ∀ v, herm X.Gm v w = 0) : w = 0 := by
  have h1 : X.Gm *ᵥ (fun b => cc (w b)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    simpa [herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det h1
  funext b
  have h3 : cc (w b) = 0 := congrFun h2 b
  rw [← cc_cc' (w b), h3, cc_zero']
  rfl

theorem zMatE_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (v : Fin r → E) :
    FJ.zMatE X e β *ᵥ v = v + ∑ a, (∑ b, β a b * herm X.Gm v (e b)) • e a := by
  funext k
  simp only [FJ.zMatE, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => ?_
  ring

theorem zMatE_zero (X : Data E r) (e : Fin ρ → Fin r → E) : FJ.zMatE X e 0 = 1 := by
  ext k l
  simp [FJ.zMatE, Matrix.one_apply]

theorem zMatE_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X cu.e (β + β') = FJ.zMatE X cu.e β * FJ.zMatE X cu.e β' := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec]
  simp only [zMatE_mulVec, herm_add_l, herm_comb_l, cu.iso, mul_zero, Finset.sum_const_zero,
    add_zero, Matrix.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
  abel

theorem zMatE_unitary (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) (u v : Fin r → E) :
    herm X.Gm (FJ.zMatE X cu.e β *ᵥ u) (FJ.zMatE X cu.e β *ᵥ v) = herm X.Gm u v := by
  simp only [zMatE_mulVec, herm_add_l, herm_add_r, herm_comb_l, herm_comb_r, cu.iso, mul_zero,
    Finset.sum_const_zero, add_zero, cc_sum', cc_mul', hβ _ _, ← herm_swap, Finset.sum_mul]
  rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  ring

theorem zMatE_injective (X : Data E r) (cu : FJ.CuspFD X ρ) :
    Function.Injective (FJ.zMatE X cu.e) := by
  intro β β' h
  have h1 : ∀ v a, ∑ b, β a b * herm X.Gm v (cu.e b) = ∑ b, β' a b * herm X.Gm v (cu.e b) := by
    intro v a
    have h2 := congrArg (· *ᵥ v) h
    simp only [zMatE_mulVec, add_right_inj] at h2
    exact Fintype.linearIndependent_iffₛ.1 cu.ind _ _ h2 a
  ext a b
  have h3 : ∑ b, cc (β a b - β' a b) • cu.e b = 0 := by
    refine herm_nondeg X _ fun v => ?_
    simp only [herm_comb_r, cc_cc', sub_mul, Finset.sum_sub_distrib, h1 v a, sub_self]
  have h4 : cc (β a b - β' a b) = 0 := Fintype.linearIndependent_iff.1 cu.ind _ h3 b
  rw [← sub_eq_zero, ← cc_cc' (β a b - β' a b), h4, cc_zero']

def zGamSub (X : Data E r) (cu : FJ.CuspFD X ρ) : AddSubgroup (Matrix (Fin ρ) (Fin ρ) E) where
  carrier := FJ.zGam X cu
  zero_mem' := ⟨fun a b => by simp [cc_zero'], 1, X.Γ.one_mem, by simp [zMatE_zero]⟩
  add_mem' := by
    rintro β β' ⟨h, γ, hγ, e⟩ ⟨h', γ', hγ', e'⟩
    refine ⟨fun a b => ?_, γ * γ', X.Γ.mul_mem hγ hγ', ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, cc_add', h, h']; ring
    · rw [zMatE_add, ← e, ← e', Units.val_mul]
  neg_mem' := by
    rintro β ⟨h, γ, hγ, e⟩
    refine ⟨fun a b => ?_, γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    · rw [Matrix.neg_apply, Matrix.neg_apply, cc_neg', h]
    · refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [e, ← zMatE_add, add_neg_cancel, zMatE_zero]

end GlobalTheory.CuspCentre
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem mem_crdI_one_iff_of_adapted {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    {X : Data E r} (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (h : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) (v : Fin ρ → E) :
    v ∈ FJ.crdI 1 cu ↔ ∀ b, v b ∈ cc' b := by
  constructor
  · intro hv
    unfold FJ.crdI at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, hax⟩ := hv
      rw [← h, ← hax]
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 (FractionalIdeal.mem_coe.1 ha)
      rw [algebraMap_smul]
      exact X.Λ.smul_mem o hx.1
    | zero => exact fun b => (cc' b).zero_mem
    | add x y _ _ hx hy =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 (hx b)) (FractionalIdeal.mem_coe.2 (hy b)))
    | smul c x _ hx =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.2 (hx b)))
  · intro hv
    refine Submodule.subset_span ⟨1, FractionalIdeal.mem_coe.2 (FractionalIdeal.one_mem_one _),
      ∑ i, v i • cu.e i, ⟨(h v).2 hv, ?_⟩, one_smul _ _⟩
    exact (show ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) from
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem mem_dualOE_xcFD_one_iff_of_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  intro E _ _ _ r ρ X cu cc' h u
  have hc := mem_crdI_one_iff_of_adapted cu cc' h
  constructor
  · intro hu a y hy
    have hm : (Pi.single a y : Fin ρ → E) ∈ FJ.XcFD 1 cu := by
      refine Submodule.subset_span fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (x a) ((hc x).1 hx a)
      refine ⟨n, ?_⟩
      rw [← hn]
      congr 1
      simp [Pi.single_apply]
    have h2 := hu _ hm
    simpa [Pi.single_apply] using h2
  · intro hu x hx
    change ∑ i, u i * x i ∈ (algebraMap (𝓞 E) E).range
    unfold FJ.XcFD at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine sum_mem fun i _ => hu i (x i) fun a' ha' => ?_
      have hm : (Pi.single i a' : Fin ρ → E) ∈ FJ.crdI 1 cu := by
        rw [hc]
        intro b
        by_cases hb : b = i
        · subst hb; simpa using ha'
        · rw [Pi.single_eq_of_ne hb]; exact (cc' b).zero_mem
      obtain ⟨n, hn⟩ := hx _ hm
      refine ⟨n, ?_⟩
      rw [hn]
      congr 1
      simp [Pi.single_apply]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul c x _ hx =>
      have e : ∑ i, u i * (c • x) i = algebraMap (𝓞 E) E c * ∑ i, u i * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def]; ring
      rw [e]
      exact mul_mem ⟨c, rfl⟩ hx

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_cusp_pseudoBasis_adapted_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  first | exact @GlobalTheory.exists_cusp_pseudoBasis | exact GlobalTheory.exists_cusp_pseudoBasis | (intros; apply GlobalTheory.exists_cusp_pseudoBasis <;> assumption)
end
