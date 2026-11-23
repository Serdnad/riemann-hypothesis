module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle060
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.RingHom.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.NumberTheory.NumberField.ProductFormula
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.SemistableReduction.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem linearIndependent_of_symbol_det_ne_zero :
    ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → (∀ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0) → LinearIndependent E (fun k : J => v k) → LinearIndependent E fun k : {k // k ∈ Set.range ix ∨ k ∈ J} => v k := by
  classical
  intro E A' _ _ _ r d I _ _ U sym hmono hker ix J v hv hJ hdet hJli
  have hle : ∀ b c : ℕ, b ≤ c → c ≤ r → U c ≤ U b := by
    intro b c hbc hcr
    induction c, hbc using Nat.le_induction with
    | base => exact le_rfl
    | succ c hbc ih => exact (hmono c (by omega)).trans (ih (by omega))
  let h : (Σ a, I a) ⊕ J → Fin d := Sum.elim ix (fun k => k.1)
  have hinj : Function.Injective h := by
    rintro (q|k) (q'|k') heq
    · exact congrArg Sum.inl (ix.injective heq)
    · exact ((hJ _ k'.2).1 ⟨q, heq⟩).elim
    · exact ((hJ _ k.2).1 ⟨q', heq.symm⟩).elim
    · exact congrArg Sum.inr (Subtype.ext heq)
  let e : (Σ a, I a) ⊕ J → {k // k ∈ Set.range ix ∨ k ∈ J} := fun x =>
    ⟨h x, by rcases x with q | k; exacts [Or.inl ⟨q, rfl⟩, Or.inr k.2]⟩
  have hb : Function.Bijective e := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨k, hk | hk⟩
    · obtain ⟨q, rfl⟩ := hk
      exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have key : LinearIndependent E (fun x : (Σ a, I a) ⊕ J => v (h x)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ q, g (Sum.inl q) • v (ix q)) + ∑ k : J, g (Sum.inr k) • v k = 0 := by
      rw [Fintype.sum_sum_type] at hg; exact hg
    have hA : ∀ n, ∀ a : Fin r, (a : ℕ) = n → ∀ i, g (Sum.inl ⟨a, i⟩) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro a ha i
      subst ha
      obtain ⟨G, hG⟩ := LinearMap.exists_extend (sym a)
      have hGv : ∀ x (hx : x ∈ U a), G x = sym a ⟨x, hx⟩ := fun x hx =>
        LinearMap.congr_fun hG ⟨x, hx⟩
      have hker' : ∀ x ∈ U ((a : ℕ) + 1), G x = 0 := fun x hx => by
        rw [hGv x (hmono a a.isLt hx)]
        exact (hker a ⟨x, _⟩).mpr hx
      have hJ0 : ∑ k : J, g (Sum.inr k) • G (v k) = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [hker' _ (hle ((a : ℕ) + 1) r (by have := a.isLt; omega) le_rfl (hJ k.1 k.2).2), smul_zero]
      have hS : ∑ q : (Σ b, I b), g (Sum.inl q) • G (v (ix q))
          = ∑ i : I a, g (Sum.inl ⟨a, i⟩) • sym a ⟨v (ix ⟨a, i⟩), hv ⟨a, i⟩⟩ := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single a]
        · exact Finset.sum_congr rfl fun i _ => by rw [hGv]
        · intro b _ hba
          apply Finset.sum_eq_zero
          intro i _
          rcases lt_or_gt_of_ne hba with hlt | hlt
          · rw [ih b (Fin.lt_iff_val_lt_val.mp hlt) b rfl i, zero_smul]
          · have h1 := Fin.lt_iff_val_lt_val.mp hlt
            have h2 := b.isLt
            rw [hker' _ (hle ((a : ℕ) + 1) (b : ℕ) (by omega) (by omega) (hv ⟨b, i⟩)), smul_zero]
        · intro hn; exact absurd (Finset.mem_univ a) hn
      have hGg := congrArg G hg'

      simp only [map_add (f := _), map_sum, map_smul, map_zero] at hGg
      rw [hS, hJ0, add_zero] at hGg
      have hM : Matrix.mulVec (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i)
          (fun i' => g (Sum.inl ⟨a, i'⟩)) = 0 := by
        funext j
        have hj := congrFun hGg j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [← hj]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet a) hM) i
    have hJs : ∑ k : J, g (Sum.inr k) • v k = 0 := by
      have h0 : ∑ q : (Σ a, I a), g (Sum.inl q) • v (ix q) = 0 :=
        Finset.sum_eq_zero fun ⟨b, i⟩ _ => by rw [hA _ b rfl i, zero_smul]
      rw [h0, zero_add] at hg'; exact hg'
    rintro (⟨b, i⟩ | k)
    · exact hA _ b rfl i
    · exact Fintype.linearIndependent_iff.mp hJli (fun k => g (Sum.inr k)) hJs k
  refine (linearIndependent_equiv (Equiv.ofBijective e hb)).mp ?_
  exact key

end GlobalTheory.HSShort
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.FracIdealIndex

theorem relIndex_smul_eq_absNorm : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  intro F _ _ I p hp hI ⟨c, hc0, hc⟩
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc0
  let f : F →ₗ[𝓞 F] F := c • LinearMap.id
  have hf : ∀ y, f y = c • y := fun y => rfl
  have hfi : Function.Injective f := fun y z h => by
    simp only [hf, Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using hc') h
  let g : 𝓞 F →ₗ[𝓞 F] F := Algebra.linearMap (𝓞 F) F
  have hgi : Function.Injective g := fun y z h => by
    simpa [g] using h
  have hle : Submodule.map f I ≤ LinearMap.range g := by
    rw [← Submodule.one_eq_range]
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  let J : Ideal (𝓞 F) := (Submodule.map f I).comap g
  have hJ : Submodule.map g J = Submodule.map f I := Submodule.map_comap_eq_of_le hle
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hI
    have : Submodule.map f I = ⊥ := by rw [← hJ, h, Submodule.map_bot]
    exact Submodule.map_injective_of_injective hfi (this.trans (Submodule.map_bot f).symm)
  have hpJ : Submodule.map g (p * J) = Submodule.map f (p • I) := by
    rw [← Ideal.smul_eq_mul, Submodule.map_smul'', Submodule.map_smul'', hJ]
  have e1 : (p • I).toAddSubgroup.relIndex I.toAddSubgroup =
      (p * J).toAddSubgroup.relIndex J.toAddSubgroup := by
    have a1 := AddSubgroup.relIndex_map_map_of_injective (p • I).toAddSubgroup I.toAddSubgroup
      (f := (f : F →+ F)) hfi
    have a2 := AddSubgroup.relIndex_map_map_of_injective (p * J).toAddSubgroup J.toAddSubgroup
      (f := (g : 𝓞 F →+ F)) hgi
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup] at a1 a2
    rw [← a1, ← a2, hpJ, hJ]
  have hle2 : p * J ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
  have hidx : (p * J).toAddSubgroup.relIndex J.toAddSubgroup * Ideal.absNorm J = Ideal.absNorm (p * J) :=
    by simpa only [Ideal.absNorm_eq_index] using
      AddSubgroup.relIndex_mul_index (H := (p * J).toAddSubgroup) (K := J.toAddSubgroup) hle2
  have hN : Ideal.absNorm J ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ0
  rw [e1]
  rw [map_mul] at hidx
  exact mul_right_cancel₀ hN hidx

end GlobalTheory.FracIdealIndex
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem relIndex_sup_span_singleton_eq_absNorm
    (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F))
    (hp : p.IsMaximal) (hu : u ∉ N₀) (hpu : ∀ π ∈ p, π • u ∈ N₀) :
    N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup
      = Ideal.absNorm p := by
  set M := N₀ ⊔ Submodule.span (𝓞 F) {u} with hM
  set K : Submodule (𝓞 F) M := N₀.comap M.subtype with hK
  have huM : u ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)

  let g : 𝓞 F →ₗ[𝓞 F] M := LinearMap.toSpanSingleton (𝓞 F) M ⟨u, huM⟩
  let f : 𝓞 F →ₗ[𝓞 F] M ⧸ K := K.mkQ ∘ₗ g
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := K.mkQ_surjective y
    obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨a, ?_⟩
    show K.mkQ (g a) = K.mkQ ⟨n + a • u, hx⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show (g a - ⟨n + a • u, hx⟩ : M).1 ∈ N₀
    simp [g, LinearMap.toSpanSingleton_apply]
    exact hn
  have hker : LinearMap.ker f = p := by
    have hmem : ∀ a, a ∈ LinearMap.ker f ↔ a • u ∈ N₀ := by
      intro a
      simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap, Submodule.subtype_apply, g,
        LinearMap.toSpanSingleton_apply, SetLike.val_smul]
    symm
    apply hp.eq_of_le
    · intro htop
      apply hu
      have : (1 : 𝓞 F) ∈ LinearMap.ker f := by
        change (1 : 𝓞 F) ∈ (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F))
        rw [show (LinearMap.ker f : Submodule (𝓞 F) (𝓞 F)) = ⊤ from htop]
        trivial
      simpa using (hmem 1).mp this
    · intro a ha
      exact (hmem a).mpr (hpu a ha)
  have e : (𝓞 F ⧸ p) ≃ₗ[𝓞 F] M ⧸ K := by
    have := f.quotKerEquivOfSurjective hf
    rw [hker] at this
    exact this
  have hidx : N₀.toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ K) := by
    rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    rfl
  rw [hidx, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.ProdFormula

theorem finsum_log_finitePlace_eq_neg_log_abs_norm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 →
      ∑ᶠ q : FinitePlace F, Real.log (q δ) = -Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
  intro F _ _ δ hδ
  have hpos : ∀ q : FinitePlace F, 0 < q δ := fun q => FinitePlace.pos_iff.2 hδ
  rw [← Real.log_finprod hpos, FinitePlace.prod_eq_inv_abs_norm hδ]
  push_cast
  rw [Real.log_inv]

end GlobalTheory.ProdFormula
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

open Polynomial

theorem not_dvd_den_of_padic_norm_le_one (p : ℕ) [Fact p.Prime] (c : ℚ)
    (hc : ‖(c : ℚ_[p])‖ ≤ 1) : ¬ p ∣ c.den := by
  intro hd
  have hden : ‖((c.den : ℤ) : ℚ_[p])‖ < 1 :=
    Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have hnum : ‖((c.num : ℤ) : ℚ_[p])‖ < 1 := by
    have h1 : ((c.num : ℤ) : ℚ_[p]) = (c : ℚ_[p]) * ((c.den : ℤ) : ℚ_[p]) := by
      have : (c.num : ℚ) = c * (c.den : ℤ) := by
        rw [Int.cast_natCast, Rat.mul_den_eq_num]
      exact_mod_cast congrArg (fun x : ℚ => (x : ℚ_[p])) this
    rw [h1, norm_mul]
    calc ‖(c : ℚ_[p])‖ * ‖((c.den : ℤ) : ℚ_[p])‖ ≤ 1 * ‖((c.den : ℤ) : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have hpn : (p : ℤ) ∣ c.num := Padic.norm_intCast_lt_one_iff.1 hnum
  have hcop := c.reduced
  have h2 : p ∣ c.num.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs]; exact (dvd_abs _ _).2 hpn
  have h3 := Nat.dvd_gcd h2 hd
  rw [hcop.gcd_eq_one] at h3
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 h3)

theorem padic_denom_coeff_of_roots_bounded :
    ∀ (p : ℕ) [Fact p.Prime] (q : Polynomial ℚ), q.Monic → ∀ k : ℕ,
      (∀ μ : PadicAlgCl p, (q.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      ∀ i, ∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ (k * q.natDegree) * m : ℕ) : ℚ) * q.coeff i = a := by
  intro p _ q hq k hroot i
  have hp : p.Prime := Fact.out
  by_cases hi : q.natDegree < i
  · refine ⟨1, Nat.coprime_one_left _, 0, ?_⟩
    rw [coeff_eq_zero_of_natDegree_lt hi]; simp
  push_neg at hi
  have hQm : (q.map (algebraMap ℚ (PadicAlgCl p))).Monic := hq.map _
  have hQd : (q.map (algebraMap ℚ (PadicAlgCl p))).natDegree = q.natDegree := natDegree_map _
  have hB := GlobalTheory.norm_coeff_natDegree_sub_le_pow_of_roots_le (PadicAlgCl p) _ hQm ((p : ℝ) ^ k)
    hroot (q.natDegree - i) (by omega)
  rw [hQd, Nat.sub_sub_self hi, coeff_map] at hB
  have hn : ‖((q.coeff i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (k * q.natDegree) := by
    have e : algebraMap ℚ (PadicAlgCl p) (q.coeff i) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((q.coeff i : ℚ) : ℚ_[p]) := by
      rw [eq_ratCast, map_ratCast]
    rw [e, PadicAlgCl.norm_extends] at hB
    refine hB.trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le)
      (Nat.mul_le_mul_left k (Nat.sub_le _ _))
  set c : ℚ := ((p ^ (k * q.natDegree) : ℕ) : ℚ) * q.coeff i with hcdef
  have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (k * q.natDegree) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    rw [hcdef]
    push_cast
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    calc ((p : ℝ) ^ (k * q.natDegree))⁻¹ * ‖((q.coeff i : ℚ) : ℚ_[p])‖
        ≤ ((p : ℝ) ^ (k * q.natDegree))⁻¹ * (p : ℝ) ^ (k * q.natDegree) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hp0.le)
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  refine ⟨c.den, ?_, c.num, ?_⟩
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_den_of_padic_norm_le_one p c hc))
  · rw [← Rat.den_mul_eq_num c, hcdef]
    push_cast
    ring

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCover

theorem cover : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  classical
  intro K _ _ A _ hA V hV
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let O : (𝟙_ (Over (Sp K)) ⟶ A) → A.left.Opens := fun a =>
    (𝟙 A * (toUnit A ≫ a)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a)⁻¹).left ⁻¹ᵁ V
  have key : ∀ y : 𝟙_ (Over (Sp K)) ⟶ A, ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, ∀ p, y.left p ∈ O a := by
    intro y
    have := GlobalTheory.AbelianProjective.isIso_transl_left y
    have : IsIso ((toUnit A ≫ y) * 𝟙 A).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit A ≫ y) * 𝟙 A)))
    have : IsIso (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A))))
    have h1 : ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h2 : (((ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h3 := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) h1 h2
    obtain ⟨a, ha⟩ := GlobalTheory.AbelianProjective.exists_point A
      ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V ⊓ (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V).isOpen).isLocallyClosed h3
    refine ⟨a, fun p => ?_⟩
    have e : y ≫ (𝟙 A * (toUnit A ≫ a)) = a ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have e' : y ≫ (𝟙 A * (toUnit A ≫ a)⁻¹) = a ≫ ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
      rfl
    have hp := ha p
    refine ⟨?_, ?_⟩
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)).left) p ∈ V
      rw [← Over.comp_left, e, Over.comp_left]
      exact hp.1
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)⁻¹).left) p ∈ V
      rw [← Over.comp_left, e', Over.comp_left]
      exact hp.2
  have htop : ⨆ a, O a = ⊤ := by
    by_contra hne
    have hc : ((⨆ a, O a : A.left.Opens) : Set A.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := GlobalTheory.AbelianProjective.exists_point A
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨a, ha⟩ := key y
    exact hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha _⟩)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun a => (O a : Set A.left))
    (fun a => (O a).isOpen) fun x _ => by
      have hx : x ∈ ⨆ a, O a := by rw [htop]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  refine ⟨F.card, fun i => (F.equivFin.symm i).1, top_unique fun x _ => ?_⟩
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨F.equivFin ⟨a, ha⟩, by simp only [Equiv.symm_apply_apply]; exact hx⟩

end GlobalTheory.AbCover
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

def IsSmallB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i) < 1

end GlobalTheory.AdicSpan
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_affine_etale_finite_free_nbhd : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  first | exact @GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | exact GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | (intros; apply GlobalTheory.GenFinEtField.exists_affine_finite_etale_free <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.card_ker_integralCombination_endo_le_pow : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  first | exact @GlobalTheory.OEndDegree.card_ker_le | exact GlobalTheory.OEndDegree.card_ker_le | (intros; apply GlobalTheory.OEndDegree.card_ker_le <;> assumption)
end
