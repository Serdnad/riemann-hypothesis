module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.RepresentationTheory.Semisimple
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle005
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle003
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbInt

theorem res_mul' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g h : Matrix κ κ A) :
    res b (g * h) = res b g * res b h := by
  ext p q

  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
  Fintype.sum_prod_type]

theorem res_one' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) :
    res b (1 : Matrix κ κ A) = 1 := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, map_one, Matrix.one_apply]
    by_cases h' : p.2 = q.2
    · rw [if_pos h', if_pos (Prod.ext h h')]
    · rw [if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]
  · rw [if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]

theorem repr_mem {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (R₀ : Subring R) (h1 : ∀ i, b.repr 1 i ∈ R₀) (x : A)
    (hx : ∀ p q, Algebra.leftMulMatrix b x p q ∈ R₀) (k : β) : b.repr x k ∈ R₀ := by

  have hsum : x = ∑ i, b.repr 1 i • (x * b i) := by
    conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i := by
    conv_lhs => rw [hsum]

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hk]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)

theorem inv_mem {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (R₀ : Subring R)
    (M N : Matrix ι ι R) (hNM : N * M = 1) (hM : ∀ p q, M p q ∈ R₀) (hd : N.det ∈ R₀) (p q : ι) :
    N p q ∈ R₀ := by

  have hadj : N = N.det • M.adjugate := by
    have h1 : N * M * M.adjugate = M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    rw [← h1, smul_smul, hd1, one_smul]

  let M' : Matrix ι ι R₀ := Matrix.of fun p q => ⟨M p q, hM p q⟩
  have hM' : R₀.subtype.mapMatrix M' = M := by ext; rfl
  have hA : M.adjugate p q = R₀.subtype (M'.adjugate p q) := by
    rw [← hM', ← RingHom.map_adjugate]; rfl
  rw [hadj, Matrix.smul_apply, smul_eq_mul, hA]
  exact Subring.mul_mem _ hd (M'.adjugate p q).2

theorem repr_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by

  have hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c) := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R))
      ((algebraMap F A).comp (algebraMap ℚ F))) c
  have hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i := by
    conv_lhs => rw [← ω.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]
  rw [hx, Module.Basis.repr_sum_self]

theorem res_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {κ R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (g : Matrix κ κ F) :
    res b (g.map (algebraMap F A)) = (res ω g).map (algebraMap ℚ R) := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb,
    ← map_mul]
  exact repr_map ω b hb _ _

theorem emb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  refine ⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_,
    fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩
  ·

    have hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀ := fun p q => by
      simpa [emb] using he (Sum.inl p) (Sum.inl q)
    have hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀ := by
      simpa [emb] using he (Sum.inr ()) (Sum.inr ())
    have hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1 := by
      rw [← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']
    have hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀ :=
      fun p q => inv_mem R₀ _ _ hinv hres hdet p q
    exact ⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k,
      repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩
  · have hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) :
        Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A) := rfl
    have hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) :
        Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A) := by
      rw [← map_inv]; rfl
    unfold emb
    rw [hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]
    ext (x | x) (y | y) <;> simp [RingHom.map_det]

end GlobalTheory.ClassFin.EmbInt
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def dotPerp (U : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  U.dualAnnihilator.comap (dotProductEquiv ℂ ι).toLinearMap

private theorem mem_dotPerp (U : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) :
    v ∈ dotPerp U ↔ ∀ w ∈ U, v ⬝ᵥ w = 0 := by
  simp [dotPerp, Submodule.mem_dualAnnihilator, dotProductEquiv]

private theorem dotPerp_isCompl {U U' : Submodule ℂ (ι → ℂ)} (h : IsCompl U U') :
    IsCompl (dotPerp U) (dotPerp U') :=
  (Submodule.orderIsoMapComap (dotProductEquiv ℂ ι)).symm.isCompl (Subspace.isCompl_dualAnnihilator h)

private theorem dotPerp_dotPerp (U : Submodule ℂ (ι → ℂ)) : dotPerp (dotPerp U) = U := by
  ext v
  constructor
  · intro hv
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U), Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨w, rfl⟩ := (dotProductEquiv ℂ ι).surjective φ
    have h := (mem_dotPerp _ v).1 hv w hφ
    rw [dotProduct_comm] at h
    simpa [dotProductEquiv] using h
  · intro hv
    rw [mem_dotPerp]
    intro w hw
    rw [dotProduct_comm]
    exact (mem_dotPerp _ w).1 hw v hv

private theorem dotPerp_invariant (U : Submodule ℂ (ι → ℂ)) (g : Matrix ι ι ℂ)
    (h : ∀ v ∈ U, g *ᵥ v ∈ U) : ∀ v ∈ dotPerp U, gᵀ *ᵥ v ∈ dotPerp U := by
  intro v hv
  rw [mem_dotPerp] at hv ⊢
  intro w hw
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  exact hv _ (h w hw)

theorem ss_transpose :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  intro ι _ _ Γ hΓ W hW
  obtain ⟨U', hU', hc⟩ := hΓ (dotPerp W) (fun g hg => by
    simpa using dotPerp_invariant W gᵀ (hW _ ⟨g, hg, rfl⟩))
  refine ⟨dotPerp U', ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact dotPerp_invariant U' g (hU' g hg)
  · have := dotPerp_isCompl hc
    rwa [dotPerp_dotPerp] at this

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private theorem subrepresentation_isCompl_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (p q : Subrepresentation ρ) :
    IsCompl p q ↔ IsCompl p.toSubmodule q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    Subrepresentation.ext_iff, Subrepresentation.ext_iff, Subrepresentation.toSubmodule_inf,
    Subrepresentation.toSubmodule_sup]
  rfl


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), _root_.GlobalTheory.ClassFin.SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  intro ι _ _ G _ V _ _ ρ b
  set e := b.equivFun
  have he : ∀ (g : G) (v : V), (LinearMap.toMatrix b b (ρ g)).mulVec (e v) = e (ρ g v) := fun g v =>
    LinearMap.toMatrix_mulVec_repr b b (ρ g) v

  have hmap : ∀ p : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p) →
      ∀ M ∈ Set.range (fun g => LinearMap.toMatrix b b (ρ g)), ∀ w ∈ p.map (e : V →ₗ[ℂ] (ι → ℂ)),
        M.mulVec w ∈ p.map (e : V →ₗ[ℂ] (ι → ℂ)) := by
    rintro p hp _ ⟨g, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hp g hv, (he g v).symm⟩
  have hcomap : ∀ W : Submodule ℂ (ι → ℂ),
      (∀ M ∈ Set.range (fun g => LinearMap.toMatrix b b (ρ g)), ∀ w ∈ W, M.mulVec w ∈ W) →
        ∀ (g : G) ⦃v : V⦄, v ∈ W.comap (e : V →ₗ[ℂ] (ι → ℂ)) → ρ g v ∈ W.comap (e : V →ₗ[ℂ] (ι → ℂ)) := by
    intro W hW g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact hW _ ⟨g, rfl⟩ _ hv
  let Φ := Submodule.orderIsoMapComap e
  constructor
  · intro hS
    refine ⟨fun p => ?_⟩
    obtain ⟨W', hW', hc⟩ := hS _ (hmap p.toSubmodule p.apply_mem_toSubmodule)
    refine ⟨⟨W'.comap (e : V →ₗ[ℂ] (ι → ℂ)), hcomap W' hW'⟩, ?_⟩
    rw [subrepresentation_isCompl_iff]
    have := (Φ.symm.isCompl_iff).1 hc
    simpa [Φ, Submodule.comap_map_eq_of_injective e.injective] using this
  · intro hC W hW
    obtain ⟨q, hq⟩ := hC.exists_isCompl ⟨W.comap (e : V →ₗ[ℂ] (ι → ℂ)), hcomap W hW⟩
    refine ⟨q.toSubmodule.map (e : V →ₗ[ℂ] (ι → ℂ)), hmap _ q.apply_mem_toSubmodule, ?_⟩
    rw [subrepresentation_isCompl_iff] at hq
    have := (Φ.isCompl_iff).1 hq
    simpa [Φ, Submodule.map_comap_eq_of_surjective e.surjective] using this

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
private lemma one_lt_valued_inv_iff_mem {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) (hx : x ≠ 0) :
    1 < Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) ↔ x ∈ Q.asIdeal := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact one_lt_inv₀ (zero_lt_iff.mpr (Q.intValuation_ne_zero x hx))


open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.adele_idem_prime_criterion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E)), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ (e : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (ε : _root_.HeckeCharacterZeroLocus.ThmBIn.AF F), _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → e * e = e → e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e → ((∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E)) ↔ ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0)) := by
  intro F E _ _ _ _ _ Φ hΦ hint hplace e P v ε hε he heε
  obtain ⟨h0, -⟩ := hplace v ε hε
  have ha : (Φ e).1 = 0 := by
    have h := congrArg (fun z => (Φ z).1) heε
    simp only [map_mul, Prod.fst_mul, h0, mul_zero] at h
    exact h.symm
  have hidem : ∀ Q, (Φ e).2 Q = 0 ∨ (Φ e).2 Q = 1 := by
    intro Q
    have h := congrArg (fun z => (Φ z).2 Q) he
    rw [map_mul] at h
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h
  have key : ∀ x : 𝓞 E, x ≠ 0 → (_root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔
      ∃ Q, (Φ e).2 Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hint, map_mul, hΦ]
    push_neg
    constructor
    · rintro ⟨Q, hQ⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) at hQ
      rcases hidem Q with h | h
      · rw [h, zero_mul, map_zero] at hQ
        exact absurd hQ (not_lt.mpr zero_le')
      · rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx] at hQ
        exact ⟨Q, h, hQ⟩
    · rintro ⟨Q, h, hQ⟩
      refine ⟨Q, ?_⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q)
      rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx]
      exact hQ
  constructor
  · intro hcrit
    have hS : ∀ Q, (Φ e).2 Q = 1 → Q = P := by
      intro Q hQ
      by_contra hne
      have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
        hne (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx : x ≠ 0 := fun h => hxP (h ▸ P.asIdeal.zero_mem)
      exact hxP ((hcrit x hx).mpr ((key x hx).mpr ⟨Q, hQ, hxQ⟩))
    obtain ⟨x, hxP, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (key x hx).mp ((hcrit x hx).mp hxP)
    have hQP := hS Q hQ
    subst hQP
    refine ⟨ha, hQ, fun R hR => ?_⟩
    rcases hidem R with h | h
    · exact h
    · exact absurd (hS R h) hR
  · rintro ⟨-, hP, hQ⟩ x hx
    rw [key x hx]
    constructor
    · exact fun hxP => ⟨P, hP, hxP⟩
    · rintro ⟨Q, h, hxQ⟩
      by_cases hQP : Q = P
      · exact hQP ▸ hxQ
      · rw [hQ Q hQP] at h
        exact absurd h zero_ne_one

end GlobalTheory
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

section ConjIdem

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem conjIdem_sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (x : E) :
    sigR R σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl

theorem conjIdem_sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rw [conjIdem_sigR_tmul, conjIdem_sigR_tmul, h]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem conjIdem_sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  show sigR R σ (a ⊗ₜ[F] 1) = a ⊗ₜ[F] 1
  rw [conjIdem_sigR_tmul, map_one]

theorem conjIdem_sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := rfl

variable [NumberField F] [NumberField E]

omit [NumberField E] in
theorem conjIdem_finPart_cA (σ : E →ₐ[F] E) (y : AE F E) :
    finPart F E (cA σ y) = sigR (Af F) σ (finPart F E y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

omit [NumberField E] in
theorem conjIdem_sigR_mem_intAE (σ : E →ₐ[F] E) (h : ∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x)
    (y : Af F ⊗[F] E) (hy : y ∈ intAE F E) : sigR (Af F) σ y ∈ intAE F E := by
  unfold intAE at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    obtain ⟨z, hz⟩ := h x
    exact AddSubgroup.subset_closure ⟨a, ha, z, by rw [conjIdem_sigR_tmul, hz]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end ConjIdem

theorem cmConjugation_on_primes_adeles_idempotents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, normP (c P) = normP P) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ (∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P) ∧ (∀ y, cA σ (cA σ y) = y) ∧ (∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E) ∧ ∀ P e f, IsPrimeIdem σ P e f → IsPrimeIdem σ (c P) (cA σ e) f := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨h1, h2, h3, h4⟩ := hCM
  obtain ⟨hinv, c, hc1, hc2, hint, hc3, hc4⟩ := cmConjugation_on_primes F E σ h1 h2 h3 h4
  have hcc : ∀ y : AE F E, cA σ (cA σ y) = y := conjIdem_sigR_sigR (AF F) σ hinv
  have hfin : ∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E := by
    have key : ∀ y : AE F E, finPart F E y ∈ intAE F E → finPart F E (cA σ y) ∈ intAE F E := by
      intro y hy
      rw [conjIdem_finPart_cA]
      exact conjIdem_sigR_mem_intAE σ hint _ hy
    intro y
    exact ⟨fun h => by have := key _ h; rwa [hcc] at this, key y⟩
  have hcrit : ∀ (P : HeightOneSpectrum (𝓞 E)) (e : AE F E),
      (∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)) →
      ∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ (c P).asIdeal ↔ finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
    intro P e h x hx
    obtain ⟨z, hz⟩ := hint x
    have hxz : (x : E) = σ z := by rw [hz, hinv]
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hx
      apply RingOfIntegers.ext
      rw [hxz]
      simp
    have hm : cA σ e * incA F E ((x : E)⁻¹) = cA σ (e * incA F E ((z : E)⁻¹)) := by
      rw [map_mul, conjIdem_sigR_inclR, map_inv₀ σ, hxz]
    rw [(hc3 P z x hxz).1, h z hz0, hm, hfin]
  refine ⟨c, hc1, hc2, hc3, hc4, hcc, hfin, ?_⟩
  intro P e f h
  rcases h with ⟨⟨⟨he1, he2, v, ε, hv, he3⟩, hP⟩, hf⟩ | ⟨hf, ⟨v, ε, hv, he⟩, hP⟩
  · left
    refine ⟨⟨⟨?_, ?_, v, ε, hv, ?_⟩, hcrit P e hP⟩, ?_⟩
    · rw [← map_mul, he1]
    · rw [hcc, mul_comm, he2]
    · rw [hcc, add_comm, he3]
    · rw [hcc, add_comm, hf]
  · right
    have hce : cA σ e = e := by rw [he]; exact conjIdem_sigR_algebraMap _ σ ε
    exact ⟨by rw [hce, hf], ⟨v, ε, hv, by rw [hce, he]⟩, hcrit P e hP⟩

end GlobalTheory
end

section

open Matrix

theorem _root_.GlobalTheory.T.differentiable_exp_mul_of_annihilated' : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  first | exact @GlobalTheory.differentiable_exp_mul_of_annihilated | exact GlobalTheory.differentiable_exp_mul_of_annihilated | (intros; apply GlobalTheory.differentiable_exp_mul_of_annihilated <;> assumption)
end
