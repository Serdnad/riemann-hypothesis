module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_poly_ev_line {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℚ)
    (A B : Matrix ι ι ℂ) : ∃ p : Polynomial ℂ, ∀ t : ℂ, p.eval t = ev f (A + t • B) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C (algebraMap ℚ ℂ a), fun t => by simp [ev]⟩
  | add f g hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    refine ⟨p + q, fun t => ?_⟩
    rw [Polynomial.eval_add, hp, hq]
    simp [ev]
  | mul_X f ij hf =>
    obtain ⟨p, hp⟩ := hf
    refine ⟨p * (Polynomial.C (A ij.1 ij.2) + Polynomial.X * Polynomial.C (B ij.1 ij.2)), fun t => ?_⟩
    rw [Polynomial.eval_mul, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    simp [ev]

theorem one_add_smul_mem_of_sq_zero :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ →
      ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  intro ι _ _ Γ hΓ ε hε h1 t
  have hn : ∀ n : ℕ, 1 + (n : ℂ) • ε ∈ Γ := by
    intro n
    induction n with
    | zero => simpa using hΓ.one_mem
    | succ n ih =>
      have h := hΓ.mul_mem _ ih _ h1
      have e : (1 + (n : ℂ) • ε) * (1 + ε) = 1 + ((n + 1 : ℕ) : ℂ) • ε := by
        rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hε, smul_zero, add_zero, Nat.cast_succ,
          add_smul, one_smul, add_assoc]
      rwa [e] at h
  apply hΓ.closed
  intro f hf
  obtain ⟨p, hp⟩ := exists_poly_ev_line f 1 ε
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective ?_
    intro n
    show p.eval (n : ℂ) = 0
    rw [hp]
    exact hf _ (hn n)
  rw [← hp, hp0, Polynomial.eval_zero]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isLog_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  intro ι _ _ x hx
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hx
  have hp : (xᴴ * x).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self x (Matrix.mulVec_injective_iff_isUnit.2 hu)
  have hs := hp.1.spectral_theorem
  refine ⟨_, (hp.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hp.1.eigenvalues i), ?_, rfl, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff).1 hp.1.eigenvectorUnitary.2
  · have he : (fun i => ((Real.exp (Real.log (hp.1.eigenvalues i)) : ℝ) : ℂ)) = RCLike.ofReal ∘ hp.1.eigenvalues := by
      funext i
      rw [Real.exp_log (hp.eigenvalues_pos i)]
      rfl
    rw [he]
    exact hs

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mem_mul_eq_zero_of_isNilpotent {R : Type*} [Ring R] (J : Ideal R) [J.IsTwoSided]
    (hJ : IsNilpotent J) (h0 : J ≠ ⊥) : ∃ a ∈ J, a ≠ 0 ∧ ∀ b ∈ J, b * a = 0 := by
  obtain ⟨n, hn⟩ := hJ
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, J ^ (k + 1) ≠ ⊥ := by
    intro k
    induction k with
    | zero => simpa [Submodule.pow_one] using h0
    | succ k ih =>
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      obtain ⟨b, hb, hba⟩ := hcon a (Ideal.pow_le_self (Nat.succ_ne_zero k) ha) ha0
      intro h
      apply hba
      have : b * a ∈ J ^ (k + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul hb ha
      rw [h] at this
      simpa using this
  apply key n
  rw [Submodule.pow_succ, hn]
  simp

theorem map_mem_jacobson_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) {b : R} (hb : b ∈ Ring.jacobson R) : f b ∈ Ring.jacobson S := by
  have : RingHomSurjective f := ⟨hf⟩
  exact Ring.le_comap_jacobson (f := f) hb

noncomputable def spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ) :
    Subalgebra ℂ (Matrix ι ι ℂ) :=
  (Submodule.span ℂ Γ).toSubalgebra (Submodule.subset_span h.one_mem) (by
    intro x y hx hy
    have h1 := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact h.mul_mem a ha b hb)

theorem map_mem_spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) {x : Matrix ι ι ℂ} (hx : x ∈ spanAlg h) : x.map σ ∈ spanAlg h := by
  change x ∈ Submodule.span ℂ Γ at hx
  change Matrix.map x (⇑σ : ℂ → ℂ) ∈ Submodule.span ℂ Γ
  induction hx using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (h.aut_mem σ g hg)
  | zero =>
    have e : Matrix.map (0 : Matrix ι ι ℂ) (⇑σ : ℂ → ℂ) = 0 := by
      ext i j; simp
    rw [e]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have e : Matrix.map (a + b) (⇑σ : ℂ → ℂ) = Matrix.map a (⇑σ : ℂ → ℂ) + Matrix.map b (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have e : Matrix.map (c • a) (⇑σ : ℂ → ℂ) = σ c • Matrix.map a (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.smul_mem _ _ ha

noncomputable def spanAlgMap {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : spanAlg h →+* spanAlg h :=
  RingHom.codRestrict ((σ : ℂ →+* ℂ).mapMatrix.comp (spanAlg h).val.toRingHom) (spanAlg h)
    (fun x => map_mem_spanAlg h σ x.2)

theorem spanAlgMap_surjective {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : Function.Surjective (spanAlgMap h σ) := by
  intro y
  refine ⟨⟨y.1.map σ.symm, map_mem_spanAlg h σ.symm y.2⟩, ?_⟩
  apply Subtype.ext
  ext i j
  simp [spanAlgMap]

theorem ss_of_isSemisimpleRing {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    [IsSemisimpleRing (spanAlg h)] : SS Γ := by
  intro W hW
  have hW' : ∀ x ∈ Submodule.span ℂ Γ, ∀ v ∈ W, x *ᵥ v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => exact hW x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [smul_mulVec]; exact W.smul_mem _ hx
  let U : Submodule (spanAlg h) (ι → ℂ) :=
    { W.toAddSubmonoid with smul_mem' := fun c v hv => hW' c.1 c.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  have hsm : ∀ (x : Matrix ι ι ℂ), x ∈ spanAlg h → ∀ v ∈ U', x *ᵥ v ∈ U' :=
    fun x hx v hv => U'.smul_mem ⟨x, hx⟩ hv
  let W' : Submodule ℂ (ι → ℂ) :=
    { U'.toAddSubmonoid with
      smul_mem' := fun c v hv => by
        have := hsm (c • 1) ((spanAlg h).smul_mem (spanAlg h).one_mem c) v hv
        rwa [smul_mulVec, one_mulVec] at this }
  refine ⟨W', fun g hg v hv => hsm g (Submodule.subset_span hg) v hv, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.1 hU.disjoint x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have : x ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hy hz

theorem exists_socle_radical_of_not_ss :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  intro ι _ _ Γ h hss
  have : IsArtinianRing (spanAlg h) := IsArtinianRing.of_finite ℂ _
  have h0 : Ring.jacobson (spanAlg h) ≠ ⊥ := by
    intro h0
    have := IsArtinianRing.isSemisimpleRing_iff_jacobson.2 h0
    exact hss (ss_of_isSemisimpleRing h)
  obtain ⟨a, ha, ha0, hba⟩ := exists_mem_mul_eq_zero_of_isNilpotent (Ring.jacobson (spanAlg h))
    IsSemiprimaryRing.isNilpotent h0
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∀ b ∈ Ring.jacobson (spanAlg h), b.1 *ᵥ v = 0}
      add_mem' := fun {x y} hx hy b hb => by rw [mulVec_add, hx b hb, hy b hb, add_zero]
      zero_mem' := fun b _ => mulVec_zero _
      smul_mem' := fun c v hv b hb => by rw [mulVec_smul, hv b hb, smul_zero] }
  refine ⟨W, ?_, ?_, a.1, a.2, fun h1 => ha0 (Subtype.ext h1), ?_, fun v hv => hv a ha⟩
  · intro g hg v hv b hb
    have hg' : g ∈ spanAlg h := Submodule.subset_span hg
    have h1 : b * (⟨g, hg'⟩ : spanAlg h) ∈ Ring.jacobson (spanAlg h) := Ideal.mul_mem_right _ _ hb
    have h2 := hv _ h1
    rw [MulMemClass.coe_mul, ← mulVec_mulVec] at h2
    exact h2
  · intro σ v hv b hb
    have h1 : spanAlgMap h σ.symm b ∈ Ring.jacobson (spanAlg h) :=
      map_mem_jacobson_of_surjective _ (spanAlgMap_surjective h σ.symm) hb
    have h2 := hv _ h1
    funext i
    have h3 := congrArg σ (congrFun h2 i)

    simpa [spanAlgMap, mulVec, dotProduct, map_sum] using h3
  · intro v b hb
    rw [mulVec_mulVec]
    have := congrArg Subtype.val (hba b hb)
    change b.1 * a.1 = 0 at this
    rw [this, zero_mulVec]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finrank_span_blk_image_lt :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  intro ι _ _ Γ e a ha ha0 hblk

  let L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun x => blk e x
      map_add' := fun x y => by
        simp only [blk, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c x => by
        simp only [blk, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }
  have himg : Submodule.span ℂ (blk e '' Γ) = (Submodule.span ℂ Γ).map L := by
    rw [Submodule.map_span]
    rfl
  rw [himg]

  set S := Submodule.span ℂ Γ with hS
  let f := L.domRestrict S
  have hrange : LinearMap.range f = S.map L := LinearMap.range_domRestrict S L
  have hker : (⟨a, ha⟩ : S) ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply]
    exact hblk
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hker
    exact ha0 (congrArg Subtype.val hker)
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker f) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  omega

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem quad_unique {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) {a b c d : F}
    (e : algebraMap F E a + algebraMap F E b * θ = algebraMap F E c + algebraMap F E d * θ) :
    a = c ∧ b = d := by
  have hbd : b = d := by
    by_contra hne
    have h0 : b - d ≠ 0 := sub_ne_zero.mpr hne
    have h0' : algebraMap F E (b - d) ≠ 0 := by
      exact (map_ne_zero _).2 h0
    have hθ : θ = algebraMap F E ((c - a) / (b - d)) := by
      rw [map_div₀, eq_div_iff h0', map_sub, map_sub]
      linear_combination e
    apply h.nonsq
    refine ⟨(c - a) / (b - d), (algebraMap F E).injective ?_⟩
    rw [map_mul, ← hθ, ← h.sq, sq]
  refine ⟨(algebraMap F E).injective ?_, hbd⟩
  rw [hbd] at e
  exact add_right_cancel e

theorem isQuad_galois_and_embedding : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → IsGalois F E ∧ (∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ) ∧ ∀ (L : Type) [Field L] (φ : F →+* L) (r : L), r ^ 2 = φ δ → ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  intro F E _ _ _ _ δ θ σ h
  refine ⟨?_, ?_, ?_⟩
  · haveI : FiniteDimensional F E := by
      classical
      refine ⟨⟨{1, θ}, ?_⟩⟩
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Finset.coe_pair, Submodule.mem_span_pair]
      exact ⟨a, b, by simp [Algebra.smul_def]⟩
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    have h1 : σ (algebraMap F E a + algebraMap F E b * θ)
        = algebraMap F E a + algebraMap F E b * θ :=
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.mem_top _)
    rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj] at h1
    have h2 : algebraMap F E a + algebraMap F E (-b) * θ
        = algebraMap F E a + algebraMap F E b * θ := by
      rw [← h1, map_neg]; ring
    have h3 := (quad_unique h h2).2
    have hb : b = 0 := by linear_combination (-1/2 : F) * h3
    rw [hb, map_zero, zero_mul, add_zero]
    exact IntermediateField.algebraMap_mem _ a
  · intro τ
    have h1 : τ θ ^ 2 = θ ^ 2 := by
      rw [← map_pow, h.sq, AlgEquiv.commutes]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · left
      ext x
      obtain ⟨a, b, rfl⟩ := h.span x
      simp [e]
    · right
      ext x
      obtain ⟨a, b, rfl⟩ := h.span x
      simp [e, h.conj]
  · intro L _ φ r hr
    choose A B hAB using h.span
    have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
        A x = a ∧ B x = b := fun x a b e => quad_unique h ((hAB x).symm.trans e)
    have hal : ∀ a : F, φ (A (algebraMap F E a)) + φ (B (algebraMap F E a)) * r = φ a := by
      intro a
      obtain ⟨h1, h2⟩ := key (algebraMap F E a) a 0 (by simp)
      simp [h1, h2]
    refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
              map_one' := by simpa using hal 1
              map_zero' := by simpa using hal 0
              map_add' := ?_
              map_mul' := ?_ }, hal, ?_⟩
    · intro x y
      obtain ⟨h1, h2⟩ := key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
        have hx := hAB x
        have hy := hAB y
        have hs := h.sq
        simp only [map_add (f := _), map_mul]
        linear_combination y * hx + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hy
          + algebraMap F E (B x) * algebraMap F E (B y) * hs)
      simp only [h1, h2, map_add (f := _), map_mul]
      linear_combination (-(φ (B x) * φ (B y))) * hr
    · intro x y
      obtain ⟨h1, h2⟩ := key (x + y) (A x + A y) (B x + B y) (by
        have hx := hAB x
        have hy := hAB y
        simp only [map_add (f := _)]
        linear_combination hx + hy)
      simp only [h1, h2, map_add (f := _)]
      ring
    · obtain ⟨h1, h2⟩ := key θ 0 1 (by simp)
      simp [h1, h2]

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_hiUnits_sup_sqs_of_even {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (p : Kˣ)
    (hp : w (p : K) = WithZero.exp (-1)) (x : Kˣ) (m : ℤ)
    (hx : w (x : K) = WithZero.exp (2 * m)) :
    x ∈ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ) := by
  have h1 : w ((x * (p ^ m) ^ 2 : Kˣ) : K) = 1 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_mul, map_pow,
      map_zpow₀, hx, hp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp
  have hU : x * (p ^ m) ^ 2 ∈ hiUnits w 0 := by
    refine ⟨h1, ?_⟩
    refine le_trans (w.map_sub _ _) (max_le ?_ ?_)
    · rw [h1]; simp
    · simp
  have hS : ((p ^ m)⁻¹) ^ 2 ∈ sqs (⊤ : Subgroup Kˣ) := ⟨(p ^ m)⁻¹, trivial, rfl⟩
  have : x = (x * (p ^ m) ^ 2) * ((p ^ m)⁻¹) ^ 2 := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  rw [this]
  exact Subgroup.mul_mem_sup hU hS

theorem index_sqs_top_le : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K),
    w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 →
    (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧
      (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  intro K _ w π hπ h0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hdvd : (hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ)).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨Units.mk0 π hπ0, fun b => ?_⟩
    have hb : w (b : K) ≠ 0 := by simp
    have hb' : w (b : K) = WithZero.exp (WithZero.log (w (b : K))) := (WithZero.exp_log hb).symm
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (WithZero.log (w (b : K)))
    · right
      exact mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ b m (by rw [hb', hm])
    · left
      refine mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ _ m ?_
      rw [Units.val_mul, map_mul, hb', hm, Units.val_mk0, hπ, ← WithZero.exp_add]
      congr 1
      ring
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_right : sqs (⊤ : Subgroup Kˣ) ≤ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ))
  rw [Subgroup.relIndex_sup_right] at hmul
  have hle : sqs (hiUnits w 0) ≤ sqs (⊤ : Subgroup Kˣ) := Subgroup.map_mono le_top
  have hd2 := Subgroup.relIndex_dvd_of_le_left (hiUnits w 0) hle
  have hd : (sqs (⊤ : Subgroup Kˣ)).index ∣ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
    rw [← hmul, mul_comm]
    exact Nat.mul_dvd_mul hdvd hd2
  have hpos : 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 := mul_ne_zero two_ne_zero h0
  exact ⟨ne_zero_of_dvd_ne_zero hpos hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd⟩

end GlobalTheory.QNorm
end
