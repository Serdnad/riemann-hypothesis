module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementG
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramCompositum

theorem card_inertia (k N : Type) [Field k] [NumberField k] [Field N] [NumberField N]
    [Algebra k N] [IsGalois k N] (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    Nat.card (Q.inertia (N ≃ₐ[k] N)) = Q.ramificationIdx (𝓞 k) := by
  have : IsGaloisGroup (N ≃ₐ[k] N) (𝓞 k) (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ k N
  have hpr : (Q.under (𝓞 k)).IsPrime := Ideal.IsPrime.under _ Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[k] N) (Q.under (𝓞 k)) Q
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 k)) Q (N ≃ₐ[k] N)] at hcard

theorem ramificationIdx_eq_one_iff_fix (k E N : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field N] [NumberField N] [Algebra k E] [Algebra k N] [Algebra E N] [IsScalarTower k E N] [IsGalois k N]
    (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    (Q.under (𝓞 E)).ramificationIdx (𝓞 k) = 1 ↔
      ∀ τ : N ≃ₐ[k] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) → ∀ y : E, τ (algebraMap E N y) = algebraMap E N y := by
  haveI : IsGalois E N := IsGalois.tower_top_of_isGalois k E N
  have h1 := card_inertia k N Q
  have h2 := card_inertia E N Q
  have h3 : Q.ramificationIdx (𝓞 k) = (Q.under (𝓞 E)).ramificationIdx (𝓞 k) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (Q.under (𝓞 E)) Q
  have h4 : 0 < Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos (R := 𝓞 E) Q
  let f : Q.inertia (N ≃ₐ[E] N) → Q.inertia (N ≃ₐ[k] N) := fun σ =>
    ⟨σ.1.restrictScalars k, AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x⟩
  have hf : Function.Injective f := fun σ σ' h =>
    Subtype.ext (AlgEquiv.restrictScalars_injective k (congrArg Subtype.val h))
  constructor
  · intro h τ hτ y
    have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [h1, h2, h3, h, one_mul])
    obtain ⟨σ, hσ⟩ := hb.2 ⟨τ, AddSubgroup.mem_inertia.mpr hτ⟩
    have : σ.1.restrictScalars k = τ := congrArg Subtype.val hσ
    rw [← this]
    exact σ.1.commutes y
  · intro h
    have hs : Function.Surjective f := fun τ =>
      ⟨⟨{ τ.1.toRingEquiv with commutes' := h τ.1 (AddSubgroup.mem_inertia.mp τ.2) },
        AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp τ.2 x⟩, rfl⟩
    have hc := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    rw [h1, h2, h3] at hc
    exact Nat.eq_of_mul_eq_mul_right h4 (by rw [one_mul]; exact hc.symm)

theorem exists_galois_above (K : Type) [Field K] [NumberField K] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N), IsGalois ℚ N := by
  have : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  have : IsGalois ℚ (AlgebraicClosure K) := ⟨⟩
  have : NumberField (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := ⟨⟩
  exact ⟨IntermediateField.normalClosure ℚ K (AlgebraicClosure K), inferInstance, inferInstance, inferInstance,
    IsGalois.normalClosure ℚ K (AlgebraicClosure K)⟩

theorem exists_valuation_eq (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
    [NumberField K] [Algebra F K] [Algebra F' K]
    (hgen : ∀ (N : Type) [Field N] (f g : K →+* N), (∀ x : F, f (algebraMap F K x) = g (algebraMap F K x)) →
      (∀ x : F', f (algebraMap F' K x) = g (algebraMap F' K x)) → f = g)
    (q : ℕ) (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ discr F') (w : HeightOneSpectrum (𝓞 F))
    (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, 𝔭.valuation K (algebraMap F K a) = w.valuation F a := by
  obtain ⟨N, _, _, _, hN⟩ := exists_galois_above K
  letI : Algebra F N := ((algebraMap K N).comp (algebraMap F K)).toAlgebra
  letI : Algebra F' N := ((algebraMap K N).comp (algebraMap F' K)).toAlgebra
  have : IsScalarTower F K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois F N := IsGalois.tower_top_of_isGalois ℚ F N
  have := w.isMaximal
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) w.asIdeal
  have hqQ : ((q : ℕ) : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q w.asIdeal _).1 hw
    rwa [map_natCast] at this
  have hu : Algebra.IsUnramifiedAt ℤ (Q.under (𝓞 F')) :=
    (not_dvd_discr_iff_forall_mem F' (𝓞 F') (Nat.prime_iff_prime_int.1 hq)).1 hd _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast, Int.cast_natCast]; exact hqQ)
  have hu' : Algebra.IsUnramifiedAt (𝓞 ℚ) (Q.under (𝓞 F')) := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have hfix := (ramificationIdx_eq_one_iff_fix ℚ F' N Q).1 (Ideal.ramificationIdx_eq_one _ _)
  have he : (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = 1 := by
    refine (ramificationIdx_eq_one_iff_fix F K N Q).2 fun τ hτ y => ?_
    exact RingHom.congr_fun (hgen N ((τ : N →+* N).comp (algebraMap K N)) (algebraMap K N)
      (fun x => τ.commutes x) (fun x => hfix (τ.restrictScalars ℚ) hτ x)) y
  have hlo : (Q.under (𝓞 K)).LiesOver w.asIdeal := Ideal.LiesOver.tower_bot Q _ _
  let 𝔭 : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot _⟩
  have hlo' : 𝔭.asIdeal.LiesOver w.asIdeal := hlo
  refine ⟨𝔭, fun a => ?_⟩
  rw [← HeightOneSpectrum.valuation_liesOver K w 𝔭 a]
  change _ ^ (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = _
  rw [he, pow_one]


open Formalism.L2.Pj in
theorem exists_vLa_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K]
    (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F),
    ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  intro F F' K _ _ _ hF hK q hq hd w hw
  have hF' : F' ≤ K := hK ▸ le_sup_right
  letI : Algebra F K := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  letI : Algebra F' K := (IntermediateField.inclusion hF').toRingHom.toAlgebra
  obtain ⟨𝔭, h⟩ := exists_valuation_eq F F' K (fun N _ f g h1 h2 => by
    let T : Subfield ℂ := (RingHom.eqLocusField f g).map (K.val : K →+* ℂ)
    let S : IntermediateField ℚ ℂ := T.toIntermediateField fun x => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem T x
    have hle : K ≤ S := by
      refine hK.le.trans (sup_le (fun x hx => ⟨⟨x, hF hx⟩, h1 ⟨x, hx⟩, rfl⟩)
        (fun x hx => ⟨⟨x, hF' hx⟩, h2 ⟨x, hx⟩, rfl⟩))
    ext z
    obtain ⟨y, hy, hyz⟩ := hle z.2
    have hyz' : y = z := Subtype.ext hyz
    subst hyz'
    exact hy) q hq hd w hw
  exact ⟨𝔭, fun a => congrArg (fun t => -WithZero.log t) (h a)⟩

end GlobalTheory.UnramCompositum
end

section

set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.SkewDense

theorem exists_dual_coef (E : Type) [Field E] [NumberField E] [DecidableEq (E →+* ℂ)] :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → E) (a : (E →+* ℂ) → κ → ℂ),
      ∀ g₀ g : E →+* ℂ, ∑ k, a g₀ k * g (b k) = if g = g₀ then 1 else 0 := by
  classical
  let B := NumberField.canonicalEmbedding.latticeBasis E
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun k => NumberField.integralBasis E k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : E →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1
  exact ⟨_, inferInstance, b, a, ha⟩

theorem eq_zero_of_rat_comb {P G : Type} [Fintype G] (r : G → P → ℂ) (Q : MvPolynomial P ℂ)
    (hrat : ∀ t : G → ℚ, MvPolynomial.eval (fun p => ∑ g, (t g : ℂ) * r g p) Q = 0)
    (hspan : ∀ y : P → ℂ, ∃ z : G → ℂ, y = fun p => ∑ g, z g * r g p) : Q = 0 := by
  classical
  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p

    simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, map_zero]
  refine MvPolynomial.funext fun y => ?_
  obtain ⟨z, rfl⟩ := hspan y
  rw [← heval, hQ', map_zero, map_zero]

def gen {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (u v : Fin n) (x : E) : Matrix (Fin n) (Fin n) E :=
  Matrix.single u v x - Matrix.single v u (σ x)

theorem cT_gen {E : Type} [CommRing E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (u v : Fin n) (x : E) :
    Formalism.UG.cT σ (gen σ u v x) = -gen σ u v x := by
  ext i j
  simp only [Formalism.UG.cT, gen, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.single_apply, map_sub, apply_ite σ, map_zero, hσ, neg_sub, and_comm]

theorem sum_gen {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {κ : Type} [Fintype κ] (b : κ → E)
    (g : E →+* ℂ) (z : Fin n × Fin n × κ → ℂ) (i j : Fin n) :
    ∑ G : Fin n × Fin n × κ, z G * g (gen σ G.1 G.2.1 (b G.2.2) i j) =
      ∑ k, z (i, j, k) * g (b k) - ∑ k, z (j, i, k) * g (σ (b k)) := by
  have e : ∀ (f : Fin n → Fin n → κ → ℂ) (p q : Fin n),
      (∑ G : Fin n × Fin n × κ, if G.1 = p ∧ G.2.1 = q then f G.1 G.2.1 G.2.2 else 0) = ∑ k, f p q k := by
    intro f p q
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single p (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← e (fun u v k => z (u, v, k) * g (b k)) i j, ← e (fun u v k => z (u, v, k) * g (σ (b k))) j i,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [gen, Matrix.sub_apply, Matrix.single_apply, map_sub, apply_ite g, map_zero, mul_sub, mul_ite, mul_zero,
    and_comm]

theorem eq_zero_of_vanish_skew (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E) (_h2 : Module.finrank F E = 2)
    {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ))
    (hψ : Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)))
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0)
    (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) : Q = 0 := by
  classical
  set c : E →+* E := (σ : E →+* E) with hc
  have hcc : ∀ x, c (c x) = x := hσ
  obtain ⟨κ, _, b, a, ha⟩ := exists_dual_coef E
  have hU : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have hinj : ∀ τ τ₀, ψ τ = ψ τ₀ ↔ τ = τ₀ := fun τ τ₀ =>
    ⟨fun h => hψ (by simp only [h]), fun h => by rw [h]⟩
  have hne : ∀ τ τ₀, (ψ τ).comp c ≠ ψ τ₀ := by
    intro τ τ₀ h
    have h1 : τ = τ₀ := by
      apply hψ
      ext x
      have := DFunLike.congr_fun h (algebraMap F E x)
      simpa [hc] using this
    subst h1
    apply hσ1
    ext x
    exact (ψ τ).injective (DFunLike.congr_fun h x)
  let A : Fin n × Fin n × κ → Matrix (Fin n) (Fin n) E := fun G => gen c G.1 G.2.1 (b G.2.2)
  refine eq_zero_of_rat_comb (fun G p => ψ p.1 ((J⁻¹ * A G) p.2.1 p.2.2)) Q (fun t => ?_) (fun y => ?_)
  · have hA : Formalism.UG.cT c (∑ G, (t G : E) • A G) = -∑ G, (t G : E) • A G := by
      ext i j

      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun G _ => ?_
      have := congrFun (congrFun (cT_gen c hcc G.1 G.2.1 (b G.2.2)) i) j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at this
      simp only [A, this, mul_neg]
    have hJS : J * (J⁻¹ * ∑ G, (t G : E) • A G) = ∑ G, (t G : E) • A G :=
      Matrix.mul_nonsing_inv_cancel_left _ _ hU
    have h := hQ (J⁻¹ * ∑ G, (t G : E) • A G) (by
      have h1 : Formalism.UG.cT c (J⁻¹ * ∑ G, (t G : E) • A G) * J = -∑ G, (t G : E) • A G := by
        have h2 := Formalism.UG.cT_mul c J (J⁻¹ * ∑ G, (t G : E) • A G)
        rw [hJ, hJS, hA] at h2
        exact h2.symm
      rw [h1, hJS, neg_add_cancel])
    rw [← h]
    congr 2
    funext p
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, map_ratCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · let w : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => J.map (ψ τ) * Matrix.of fun i j => y (τ, i, j)
    let z : Fin n × Fin n × κ → ℂ := fun G => ∑ τ₀, w τ₀ G.1 G.2.1 * a (ψ τ₀) G.2.2
    have key : ∀ (g : E →+* ℂ) u v, ∑ k, z (u, v, k) * g (b k) =
        ∑ τ₀, w τ₀ u v * if g = ψ τ₀ then 1 else 0 := by
      intro g u v
      simp only [z, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ₀ _ => ?_
      rw [← ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hw : ∀ τ i j, ∑ G, z G * ψ τ (A G i j) = w τ i j := by
      intro τ i j
      have k2 := key ((ψ τ).comp c) j i
      simp only [RingHom.comp_apply, hne, if_false, mul_zero, Finset.sum_const_zero] at k2
      rw [sum_gen, key, k2]
      simp [hinj]
    refine ⟨z, ?_⟩
    funext ⟨τ, i, j⟩
    have e1 : (J⁻¹).map (ψ τ) * w τ = Matrix.of fun i j => y (τ, i, j) := by
      simp only [w]
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hU,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.of_apply, Matrix.mul_apply] at e2
    rw [← e2]

    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply, ← hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun l _ => ?_
    ring

end GlobalTheory.SkewDense
end
end

section

namespace GlobalTheory

theorem lift_forms_of_card_isUnit : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G)
    (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q]
    (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π →
    (∀ κ x, π x = 0 → π (ρ κ x) = 0) →
    (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧
      IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) →
    ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) →
    ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  intro O _ G _ Γ K B Q _ _ _ _ ρ π hπ _hker hfin f hf
  classical

  have hlift : ∀ s : G, ∃ y : B, π y = f s ∧
      ∀ (h : Γ) (hk : s⁻¹ * (h : G) * s ∈ K), ρ ⟨_, hk⟩ y = y := by
    intro s
    obtain ⟨hF, hu⟩ := hfin s
    haveI : Fintype {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} := Fintype.ofFinite _
    obtain ⟨y0, hy0⟩ := hπ (f s)
    obtain ⟨u, hu'⟩ := hu
    let kk : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} → K := fun h => ⟨_, h.2⟩
    refine ⟨(↑u⁻¹ : O) • ∑ h, ρ (kk h) y0, ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum]
      have hval : ∀ h, π (ρ (kk h) y0) = f s := by
        intro h
        have e := hf h.1 s (kk h)⁻¹ y0 hy0.symm
        rw [inv_inv] at e
        rw [← e]
        congr 1
        simp only [kk, Subgroup.coe_inv]
        group
      simp_rw [hval, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← Nat.card_eq_fintype_card, ← hu', Units.inv_mul,
        one_smul]
    · intro h hk

      rw [map_smul, map_sum]
      congr 1
      have hmul : ∀ x : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K},
          s⁻¹ * ((h * x.1 : Γ) : G) * s ∈ K := by
        intro x
        have : s⁻¹ * ((h * x.1 : Γ) : G) * s = (s⁻¹ * (h : G) * s) * (s⁻¹ * (x.1 : G) * s) := by
          push_cast; group
        rw [this]; exact K.mul_mem hk x.2
      have hinvm : ∀ x : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K},
          s⁻¹ * ((h⁻¹ * x.1 : Γ) : G) * s ∈ K := by
        intro x
        have : s⁻¹ * ((h⁻¹ * x.1 : Γ) : G) * s = (s⁻¹ * (h : G) * s)⁻¹ * (s⁻¹ * (x.1 : G) * s) := by
          push_cast; group
        rw [this]; exact K.mul_mem (K.inv_mem hk) x.2
      let e : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} ≃ {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} :=
        { toFun := fun x => ⟨h * x.1, hmul x⟩
          invFun := fun x => ⟨h⁻¹ * x.1, hinvm x⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun x => Subtype.ext (by simp) }
      refine Fintype.sum_equiv e _ _ (fun x => ?_)
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      apply Subtype.ext
      simp only [kk, e, Equiv.coe_fn_mk, Subgroup.coe_mul]
      push_cast
      group
  choose y hy hinv using hlift

  have hwd : ∀ (s : G) (γ γ' : Γ) (κ κ' : K), (γ : G) * s * κ = γ' * s * κ' →
      ρ κ⁻¹ (y s) = ρ κ'⁻¹ (y s) := by
    intro s γ γ' κ κ' e
    have hk : s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s = ((κ' * κ⁻¹ : K) : G) := by
      have h1 : (γ : G) * s = γ' * s * κ' * κ⁻¹ := by
        calc (γ : G) * s = (γ : G) * s * κ * (κ : G)⁻¹ := by group
          _ = γ' * s * κ' * (κ : G)⁻¹ := by rw [e]
      calc s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s = s⁻¹ * ((γ' : G)⁻¹ * ((γ : G) * s)) := by
            push_cast; group
        _ = ((κ' * κ⁻¹ : K) : G) := by rw [h1]; push_cast; group
    have hmem : s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s ∈ K := hk ▸ (κ' * κ⁻¹).2
    have hfix := hinv s (γ'⁻¹ * γ) hmem
    have heq : (⟨_, hmem⟩ : K) = κ' * κ⁻¹ := Subtype.ext hk
    rw [heq] at hfix
    calc ρ κ⁻¹ (y s) = ρ κ'⁻¹ (ρ (κ' * κ⁻¹) (y s)) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
      _ = ρ κ'⁻¹ (y s) := by rw [hfix]

  have hrep : ∃ rep : G → G, (∀ (γ : Γ) (g : G) (κ : K), rep ((γ : G) * g * κ) = rep g) ∧
      ∀ g : G, ∃ (γ : Γ) (κ : K), g = (γ : G) * rep g * κ := by
    refine ⟨fun g => (DoubleCoset.mk Γ K g).out, ?_, ?_⟩
    · intro γ g κ
      have : DoubleCoset.mk Γ K ((γ : G) * g * κ) = DoubleCoset.mk Γ K g :=
        (@DoubleCoset.eq _ _ Γ K _ _).2 ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (κ : G)⁻¹, K.inv_mem κ.2, by group⟩
      simp only [this]
    · intro g
      obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
      refine ⟨⟨h, hh⟩⁻¹, ⟨k, hk⟩⁻¹, ?_⟩
      simp only [e, Subgroup.coe_inv]
      group
  obtain ⟨rep, hrep1, hrep2⟩ := hrep
  choose γg κg hg using hrep2
  refine ⟨fun g => ρ (κg g)⁻¹ (y (rep g)), ?_, ?_⟩
  · intro γ g κ
    show ρ (κg ((γ : G) * g * κ))⁻¹ (y (rep ((γ : G) * g * κ))) = ρ κ⁻¹ (ρ (κg g)⁻¹ (y (rep g)))
    have e1 := hg ((γ : G) * g * κ)
    rw [hrep1] at e1 ⊢
    have e2 := hg g
    have key : ((γ * γg g : Γ) : G) * rep g * ((κg g * κ : K) : G) =
        (γg ((γ : G) * g * κ) : G) * rep g * (κg ((γ : G) * g * κ) : G) := by
      rw [← e1]
      conv_rhs => rw [e2]
      push_cast; group
    rw [← hwd (rep g) _ _ _ _ key, ← Module.End.mul_apply, ← map_mul, mul_inv_rev]
  · intro g
    calc π (ρ (κg g)⁻¹ (y (rep g))) = f ((γg g : G) * rep g * κg g) :=
          (hf (γg g) (rep g) (κg g) (y (rep g)) (hy (rep g)).symm).symm
      _ = f g := by rw [← hg g]

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.InertValRestr

theorem liesOver_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have hP : w.asIdeal.IsPrime := w.isPrime
  have hc : (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := inferInstance
  refine v.isMaximal.eq_of_le hc.ne_top ?_
  show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [← hin]
  exact Ideal.le_comap_map

theorem ramificationIdx'_eq_one_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hP : w.asIdeal.IsPrime := w.isPrime
  apply Ideal.ramificationIdx'_spec
  · rw [hin, pow_one]
  · rw [hin]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow w.ne_bot 1 |>.trans_eq (pow_one _))

theorem valuation_algebraMap_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  intro F E _ _ _ _ _ v w hin x
  have := liesOver_of_isInertAt v w hin
  rw [← HeightOneSpectrum.valuation_liesOver (K := F) E v w x,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    ramificationIdx'_eq_one_of_isInertAt v w hin, pow_one]

end GlobalTheory.InertValRestr
end
