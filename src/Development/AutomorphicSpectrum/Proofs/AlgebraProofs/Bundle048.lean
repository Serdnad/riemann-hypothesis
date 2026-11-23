module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle009
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeBaseChangeFree
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle043
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
public import Development.WeilBound.CoreStatements.HodgeTatePoints.BilinearPartAx3
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocalSum

theorem finsum_linear_combination_four {α : Type} {f g h i : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (hh : {x | h x ≠ 0}.Finite) (hi : {x | i x ≠ 0}.Finite)
    (a b c d : ℝ) :
    (∑ᶠ x, (a * f x + (b * g x + (c * h x + d * i x)))) =
      a * (∑ᶠ x, f x) + (b * (∑ᶠ x, g x) + (c * (∑ᶠ x, h x) + d * ∑ᶠ x, i x)) := by
  have sm : ∀ (c : ℝ) (u : α → ℝ), {x | u x ≠ 0}.Finite →
      (Function.support fun x => c * u x).Finite :=
    fun c u hu => hu.subset fun x hx h => hx (by simp [h])
  have sa : ∀ (u v : α → ℝ), (Function.support u).Finite → (Function.support v).Finite →
      (Function.support fun x => u x + v x).Finite :=
    fun u v hu hv => (hu.union hv).subset (Function.support_add u v)
  rw [finsum_add_distrib (sm a f hf) (sa _ _ (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi))),
    finsum_add_distrib (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi)),
    finsum_add_distrib (sm c h hh) (sm d i hi)]
  simp only [mul_finsum]

theorem two_log_norm {E A : Type} [Field E] [NormedField A] (j : E →+* A) {r : E} {d : ℕ}
    (hr : r ^ 2 = -(d : E)) : 2 * Real.log ‖j r‖ = Real.log ‖(d : A)‖ := by
  have h1 : (j r) ^ 2 = -(d : A) := by rw [← map_pow, hr]; simp
  have h2 : ‖j r‖ ^ 2 = ‖(d : A)‖ := by rw [← norm_pow, h1, norm_neg]
  rw [← h2, Real.log_pow]
  norm_num

theorem deg_of_local_formulas : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n x t t' hρ ha hd hr hx hinf htt' htt hfin hN
  have hm : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have he : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℝ := ((Module.finrank ℚ k : ℕ) : ℝ) with hmdef
  set e : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hedef

  have hloc : ∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖
      - ((p : ℝ) + q) * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
      + ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
    intro ℓ j
    have h1 := hN ℓ j
    have h2 : 2 * Real.log ‖j (τ r)‖ = Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := two_log_norm (j.comp τ) hr
    linear_combination h1 + (((p : ℝ) - q) / 2) * h2
  constructor
  · have S1 := GlobalTheory.T.log_norms_of_nonzero_adelic k ρ hρ
    have S4 := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
    have S3 := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
    refine (((S1.union S4).union S3).union hfin).subset ?_
    rintro ℓ ⟨j, hj⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at h
    obtain ⟨⟨⟨h1, h4⟩, h3⟩, h2⟩ := h
    apply hj
    have e1 : Real.log ‖j ρ‖ = 0 := h1 j
    have e2 : Real.log ‖j (τ (t ℓ))‖ = 0 := h2 (j.comp τ)
    have e3 := h3 ((j.comp τ).comp (algebraMap (𝓞 E) E))
    have e4 : Real.log ‖j (d : k)‖ = 0 := h4 j
    rw [map_natCast] at e4
    rw [hloc, e1, e2, e3, e4]
    simp
  ·
    have hcard : ∀ ℓ : Nat.Primes, ((Fintype.card (k →+* ℂ_[ℓ]) : ℕ) : ℝ) = m := fun ℓ => by
      rw [hmdef, Embeddings.card]
    have hcardC : ((Fintype.card (k →+* ℂ) : ℕ) : ℝ) = m := by rw [hmdef, Embeddings.card]
    have hDd : ∀ ℓ : Nat.Primes, (LogNorms.ofElt (d : k)).finSum ℓ = m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
      intro ℓ
      simp only [LogNorms.finSum, LogNorms.ofElt, map_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard]
    have hsum : ∀ ℓ : Nat.Primes, N.finSum ℓ = 1 * (LogNorms.ofElt ρ).finSum ℓ
        + (((m / e) * (1 / 2)) * (LogNorms.ofElt a).finSum ℓ
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (LogNorms.ofElt (d : k)).finSum ℓ)) := by
      intro ℓ
      have f1 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ (fun i => Real.log ‖i (t ℓ)‖)
      have f2 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ
        (fun i => logIdeal (i.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
      have g1 : ∑ j : E →+* ℂ_[ℓ], (Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖) =
          ∑ j : E →+* ℂ_[ℓ], -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
        Finset.sum_congr rfl fun j _ => htt ℓ j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htt' ℓ, ← Finset.mul_sum] at g1
      have h0 : N.finSum ℓ = (LogNorms.ofElt ρ).finSum ℓ - ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖
          - ((p : ℝ) + q) * ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
          + ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
        have c1 : ∑ j : k →+* ℂ_[ℓ], ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ =
            ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
        rw [← c1, Finset.mul_sum]
        simp only [LogNorms.finSum, LogNorms.ofElt, hloc, RingHom.comp_apply,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hT : ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f1
      have hD : ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f2
      have hae : (LogNorms.ofElt a).finSum ℓ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j a‖ := rfl
      rw [h0, hDd, hT, hD, hae]
      linear_combination (-(m / e) / 2) * g1
    have hA := GlobalTheory.T.product_formula_log_norms k ρ hρ
    have hE := GlobalTheory.T.product_formula_log_norms E a ha
    have hG := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
    have hΔ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hfs : ∑ᶠ ℓ, N.finSum ℓ = 1 * (∑ᶠ ℓ, (LogNorms.ofElt ρ).finSum ℓ)
        + (((m / e) * (1 / 2)) * (∑ᶠ ℓ, (LogNorms.ofElt a).finSum ℓ)
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ᶠ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (∑ᶠ ℓ, (LogNorms.ofElt (d : k)).finSum ℓ))) := by
      rw [finsum_congr hsum]
      exact finsum_linear_combination_four hA.1 hE.1 hΔ.1 hG.1 _ _ _ _
    have hlogn : ∑ s, Real.log (n s) = -(m * x) := by
      rw [← hx]; field_simp
    have hI : ∑ s, N.inf s = (∑ s : k →+* ℂ, Real.log ‖s ρ‖)
        + ((p : ℝ) - q) / 2 * ((∑ s, Real.log (n s)) + m * (Real.log d / 2))
        + (∑ s : k →+* ℂ, Real.log ‖s (τ a)‖) / 2 := by
      simp only [hinf]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC, ← Finset.sum_div]
    have hAτ : ∑ s : k →+* ℂ, Real.log ‖s (τ a)‖ = (m / e) * ∑ s : E →+* ℂ, Real.log ‖s a‖ := by
      rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
      exact GlobalTheory.T.sum_embeddings_base_change E k ℂ τ (fun i => Real.log ‖i a‖)
    have hdinf : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = m * Real.log d := by
      simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC]
    have h1 := hA.2
    have h2 := hE.2
    have h3 := hG.2
    have h4 := hΔ.2
    rw [hdinf] at h3
    have hme : m / e * e = m := div_mul_cancel₀ _ he
    have key : (∑ s, N.inf s) + ∑ᶠ ℓ, N.finSum ℓ =
        m * (((p : ℝ) - q) / 2 * (-x + Real.log d / 2) + ((p : ℝ) + q) / 2 * Real.log (rootDiscr E)
          - ((p : ℝ) + q) / 2 * Real.log d) := by
      rw [hI, hfs, hlogn, hAτ, h4]
      linear_combination h1 + (m / e / 2) * h2 + (((p : ℝ) + q) / 2) * h3
        + ((((p : ℝ) + q) / 2) * Real.log (rootDiscr E)) * hme
    have hdiv : ∀ Y : ℝ, -(m * Y) / m = -Y := fun Y => by field_simp
    rw [LogNorms.deg, key, hdiv, Real.log_sqrt hdR.le]
    ring

end GlobalTheory.CompanionTheory.Ar.Fl.LocalSum
end
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem _root_.GlobalTheory.T.hopf_order_induction_id : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem _root_.GlobalTheory.T.hopf_order_scalar_extension : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | exact GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.character_lattice_graph_comap_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.character_lattice_fibre_ideal_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.character_lattice_kernel_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.character_lattice_base_change_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.trivial_flag_at_prime : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay.main | exact GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelSeq

section Lattices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat (R : Subalgebra o Ω) {κ : Type} (v : κ → Ω) :
    v ∈ stdLat R κ ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem af_le_std (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af R p χ ≤ stdLat R (Fin n) := by
  have hl1 : D.l1 R p ≤ stdLat R _ := by
    refine sup_le hB.M_le ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (mem_stdLat R _).2 fun i => ?_
    have := (mem_stdLat R f).1 hf i
    simpa using R.mul_mem (natCast_mem R p) this
  intro l hl
  refine (mem_stdLat R l).2 fun i => ?_
  have h := (mem_stdLat R _).1 (hl1 hl) (Pi.single i 1)
  have e : (linMap n χ) l (Pi.single i 1) = l i := by
    simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  have e' : (linMap n χ).toAddMonoidHom l (Pi.single i 1) = l i := e
  rwa [e'] at h

theorem std_le_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : stdLat R (Fin n) ≤ D.hh R p χ := by
  intro v hv
  refine (mem_dotDual R _ v).2 fun l hl => ?_
  have hl' := (mem_stdLat R l).1 (af_le_std D R p w hB χ h0 h1 hl)
  have hv' := (mem_stdLat R v).1 hv
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std_of_mem_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (h : mulLat w (stdLat R _) ≤ D.af R p χ) {b : Fin n → Ω} (hb : b ∈ D.hh R p χ) :
    w • b ∈ stdLat R (Fin n) := by
  refine (mem_stdLat R _).2 fun i => ?_
  have hi : (Pi.single i 1 : Fin n → Ω) ∈ stdLat R (Fin n) := by
    refine (mem_stdLat R _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp [one_mem]
    · simp [Pi.single_eq_of_ne hj, zero_mem]
  have hm : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p χ := h ⟨_, hi, rfl⟩
  have := (mem_dotDual R _ b).1 hb _ hm
  simpa [smul_dotProduct, single_one_dotProduct] using this

theorem mem_kerH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (v : Fin (r τ) → Ω) :
    v ∈ D.kerH R p τ χ ↔ ∃ b, (v, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.kerH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_imH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (c : Fin (s τ) → Ω) :
    c ∈ D.imH R p τ χ ↔ ∃ b, (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.imH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

def gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin (r τ) → Ω) × (Fin n → Ω)) :=
  D.Gam τ ⊓ (⊤ : AddSubgroup (Fin (r τ) → Ω)).prod (D.hh R p χ)

def delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin n → Ω) × (Fin (s τ) → Ω)) :=
  D.Del τ ⊓ (D.hh R p χ).prod (⊤ : AddSubgroup (Fin (s τ) → Ω))

theorem mem_gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (a : Fin (r τ) → Ω) (b : Fin n → Ω) :
    (a, b) ∈ gamH D R p τ χ ↔ (a, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [gamH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (b : Fin n → Ω) (c : Fin (s τ) → Ω) :
    (b, c) ∈ delH D R p τ χ ↔ (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [delH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

end Lattices

section Families

variable (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem isLatFamily_inf_prod_right (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V₁} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (⊤ : AddSubgroup V).prod (H c) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨trivial, hH.1 c hc a ha _ h2⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨trivial, ?_⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

theorem isLatFamily_inf_prod_left (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (H c).prod (⊤ : AddSubgroup V₁) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨hH.1 c hc a ha _ h2, trivial⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

end Families

theorem relSeq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x hinj F _ _ _ n Sg _ r s p hp w χ φ D hD hG hF τ
  have hhfam := (((GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hD).2 τ).2.2.2.2 hG).1
  obtain ⟨-, -, -, -, hGam, hDel, -⟩ := hD.fam τ
  have h0 : χ τ 0 = 0 := (hD.char.2.2.2.2 τ).1
  have h1 : χ τ 1 = 1 := (hD.char.2.2.2.2 τ).2
  have h0' : algebraMap O Ω (χ τ 0) = 0 := by rw [h0, map_zero]
  have h1' : algebraMap O Ω (χ τ 1) = 1 := by rw [h1, map_one]
  have hstd : ∀ c, mseg x c ≠ 0 → stdLat (chartRing O (mseg x) c) (Fin n) ≤
      (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) :=
    fun c hc => std_le_hh (D c) _ p _ (hD.base c hc) _ h0' h1'
  refine ⟨fun c => gamH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    fun c => delH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    ⟨isLatFamily_inf_prod_right O x hGam hhfam, fun c hc => ?_⟩,
    ⟨isLatFamily_inf_prod_left O x hDel hhfam, fun c hc => ?_⟩, fun c hc => ?_⟩
  · have hB := hD.base c hc
    have hk := (hF c hc).ker τ
    refine ⟨fun v b hvb => ?_, fun v hv => ?_, fun b => ?_, fun v hv => ?_⟩
    · have h := (mem_gamH _ _ _ _ _ _ _).1 hvb
      refine ⟨?_, h.2⟩
      beta_reduce
      rw [← hk]
      exact (mem_kerH _ _ _ _ _ _).2 ⟨b, h⟩
    · beta_reduce at hv
      rw [← hk] at hv
      obtain ⟨b, h⟩ := (mem_kerH _ _ _ _ _ _).1 hv
      exact ⟨b, (mem_gamH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_gamH]
      exact ⟨fun h => ((hB.gam τ).2.1 b).1 h.1, fun h => ⟨((hB.gam τ).2.1 b).2 h, hstd c hc h⟩⟩
    · exact (mem_gamH _ _ _ _ _ _ _).2 ⟨((hB.gam τ).2.2 v).2 hv, zero_mem _⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun b e hbe => ?_, fun b hb => ?_, fun e => ?_, fun b hb => ?_⟩
    · have h := (mem_delH _ _ _ _ _ _ _).1 hbe
      refine ⟨h.2, ?_⟩
      beta_reduce
      rw [← hi]
      exact (mem_imH _ _ _ _ _ _).2 ⟨b, h⟩
    · obtain ⟨e, he⟩ := ((hB.del τ).1 b).2
        (smul_mem_std_of_mem_hh (D c) _ p _ _ ((hF c hc).le_af τ) hb)
      exact ⟨e, (mem_delH _ _ _ _ _ _ _).2 ⟨he, hb⟩⟩
    · rw [mem_delH]
      exact ⟨fun h => ((hB.del τ).2.2.1 e).1 h.1, fun h => ⟨((hB.del τ).2.2.1 e).2 h, zero_mem _⟩⟩
    · refine (mem_delH _ _ _ _ _ _ _).2 ⟨((hB.del τ).2.2.2 b).2 ⟨0, ((hB.gam τ).2.1 b).2 hb⟩, hstd c hc hb⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun v hv => ?_, fun e he => ?_, fun b => ?_⟩
    · exact ((hB.gam τ).2.2 v).1 ((mem_gamH _ _ _ _ _ _ _).1 hv).1
    · beta_reduce at he
      rw [← hi] at he
      obtain ⟨b, h⟩ := (mem_imH _ _ _ _ _ _).1 he
      exact ⟨b, (mem_delH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_delH]
      constructor
      · rintro ⟨h, hb⟩
        obtain ⟨a, ha⟩ := ((hB.del τ).2.2.2 b).1 h
        exact ⟨a, (mem_gamH _ _ _ _ _ _ _).2 ⟨ha, hb⟩⟩
      · rintro ⟨a, ha⟩
        have h := (mem_gamH _ _ _ _ _ _ _).1 ha
        exact ⟨((hB.del τ).2.2.2 b).2 ⟨a, h.1⟩, h.2⟩

end GlobalTheory.CompanionTheory.Ar.Num.RelSeq
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.alpha_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act | exact GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rhoH_hom_adjoint : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∃ ρH : O →+* Module.End R ((Fin d → R) × (Fin d → R)), ∀ a, ρH a = rhoH B a) ∧ (bil B.sy 1 1).transpose = - bil B.sy 1 1 ∧ ∀ a y y', pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') :=
  @PositivityTheory.HtPt.Ca.rhoH_hom

end GlobalTheory.CompanionTheory.Ar.Conj
end
