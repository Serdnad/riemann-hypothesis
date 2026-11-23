module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionLatticeSeparatedComplete
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DvdOfForallSubMulMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicCompletion_lattice_separated_complete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → (∀ z : Fin n → RA F E, (∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧ ∀ x : ℕ → (Fin n → RA F E), (∀ N, x N ∈ (hat F (L : Set (Fin n → E)))) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (hat F (L : Set (Fin n → E))), x (N * m) = x N + N • w) → ∃ z ∈ (hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = x N + N • w := by
  first | exact @GlobalTheory.AdLat.Complete.hat_separated_complete | exact GlobalTheory.AdLat.Complete.hat_separated_complete | (intros; apply GlobalTheory.AdLat.Complete.hat_separated_complete <;> assumption)
end

section

open IsLocalRing MvPowerSeries

namespace GlobalTheory.CohenStructure

theorem isDomain_mvPowerSeries (R : Type) [CommRing R] [IsDomain R] (n : ℕ) :
    IsDomain (MvPowerSeries (Fin n) R) :=
  NoZeroDivisors.to_isDomain _

theorem isIntegrallyClosed_mvPowerSeries (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := isDomain_mvPowerSeries R n
    have := GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries (MvPowerSeries (Fin n) R)
    exact IsIntegrallyClosed.of_equiv (finSuccEquiv R n).toRingEquiv.symm

theorem isAdicComplete_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) [h : IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

theorem isAdicComplete_mvPowerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact isAdicComplete_of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := ReciprocityTheory.P1.isAdicComplete_ps (R := MvPowerSeries (Fin n) R)
    exact isAdicComplete_of_ringEquiv (finSuccEquiv R n).toRingEquiv.symm

theorem finite_quotient_of_pow_le {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (G : Set S), hF.sup (Submodule.fg_span G.finite_toSet), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨a, ha⟩ := h (c y)
      have : c y • y = a • y + y * (c y - algebraMap A S a) := by
        rw [Algebra.smul_def a, smul_eq_mul]; ring
      rw [this]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span hy)) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem injective_of_ringKrullDim_eq {A S : Type} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Module.Finite A S] {n : ℕ} (hA : ringKrullDim A = n) (hS : ringKrullDim S = n) :
    Function.Injective (algebraMap A S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have h1 := ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) (⊥ : Ideal S)
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk ((⊥ : Ideal S).comap (algebraMap A S))) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.2 hr)
  rw [← h1, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S), hA, hS] at h2
  norm_cast at h2
  omega

theorem exists_finite_injective_of_isAdicComplete :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (i : A →+* S),
        Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A ∧
          IsAdicComplete (maximalIdeal A) A := by
  intro S _ _ _ _ p hp h0 hn hc
  have hp0 : (p : S) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  obtain ⟨Λ, h1, h2, h3⟩ := CoeffSubring.exists_coeffSubring hp hp0 h0 hB hB'
  obtain ⟨_, hm, hΛ⟩ := GlobalTheory.isDVR_of_closed_subring_principal S Λ p (by simpa using hp0) (by simpa using h0) hc h1 h2 h3
  obtain ⟨n, x, hx, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S p hp0 h0
  let A := MvPowerSeries (Fin n) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ n
  have hA := isAdicComplete_mvPowerSeries Λ n
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hm, Ideal.mem_span_singleton] at h5
    obtain ⟨c, hc⟩ := h5
    have h6 : algebraMap Λ S (constantCoeff g) ∈ maximalIdeal S := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ h0
    have h7 := add_mem h4 h6
    rwa [sub_add_cancel] at h7
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · rw [← map_natCast (algebraMap A S)]
      refine Ideal.mem_map_of_mem _ (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_)
      rw [map_natCast, hm]
      exact Ideal.mem_span_singleton_self _
    · rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
      exact Ideal.mem_map_of_mem (algebraMap A S)
        (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ n, hA⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
    Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
  norm_cast

end GlobalTheory.CohenStructure
end

section

namespace GlobalTheory.ConjugateMembership

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_neg_of_sq {x : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) x = -x := by
  have hre : x.re * x.re - x.im * x.im = -d := by
    have := congrArg Complex.re hx
    simpa [sq] using this
  have him : x.re * x.im + x.im * x.re = 0 := by
    have := congrArg Complex.im hx
    simpa [sq] using this
  have h0 : x.re = 0 := by
    by_contra h
    have hi : x.im = 0 := by
      have h2 : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left h
    rw [hi] at hre
    nlinarith [mul_self_nonneg x.re]
  apply Complex.ext <;> simp [h0]

theorem eq_iff_conj_ne {x r : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) (hr : r ^ 2 = -(d : ℂ)) :
    x = r ↔ ¬ (starRingEnd ℂ) x = r := by
  rw [conj_eq_neg_of_sq hd hx]
  constructor
  · rintro rfl h
    have h0 : x = 0 := by linear_combination (-1 / 2 : ℂ) * h
    rw [h0] at hx
    have : (d : ℂ) = 0 := by linear_combination hx
    exact hd.ne' (by exact_mod_cast this)
  · intro h
    have : (x - r) * (-x - r) = 0 := by linear_combination hr - hx
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd (sub_eq_zero.1 h1) h

theorem mem_iff_conjugate_notMem {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hx : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [← map_pow, hE]; simp
  have hr : H.rt0 ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [H.sqrt_neg_disc_sq]; simp
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  exact eq_iff_conj_ne hd hx hr

end GlobalTheory.ConjugateMembership
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DatumSum

noncomputable section

def blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (f.prodMap g) ∘ₗ e.toLinearMap

theorem blockEnd_apply {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) (x : U) :
    e (blockEnd e f g x) = (f (e x).1, g (e x).2) := by
  simp [blockEnd, Prod.map]

theorem blockEnd_comp {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f f' : V →ₗ[ℝ] V) (g g' : W →ₗ[ℝ] W) :
    blockEnd e f g ∘ₗ blockEnd e f' g' = blockEnd e (f ∘ₗ f') (g ∘ₗ g') := by
  ext x
  apply e.injective
  simp [blockEnd_apply]

theorem trace_blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [Module.Finite ℝ V] [Module.Finite ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) :
    LinearMap.trace ℝ U (blockEnd e f g) = LinearMap.trace ℝ V f + LinearMap.trace ℝ W g := by
  have h1 : blockEnd e f g = e.symm.conj (f.prodMap g) := by
    ext x; simp [blockEnd, LinearEquiv.conj_apply]
  rw [h1, LinearMap.trace_conj', LinearMap.trace_prodMap']

def sumForm {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) : LinearMap.BilinForm ℤ (L × M) :=
  B.compl₁₂ (LinearMap.fst ℤ L M) (LinearMap.fst ℤ L M) + C.compl₁₂ (LinearMap.snd ℤ L M) (LinearMap.snd ℤ L M)

theorem sumForm_apply {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : L × M) : sumForm B C x y = B x.1 y.1 + C x.2 y.2 := by
  simp [sumForm]

theorem sumForm_bijective {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (hC : Function.Bijective C) :
    Function.Bijective (sumForm B C) := by
  constructor
  · intro x y h
    refine Prod.ext (hB.1 ?_) (hC.1 ?_)
    · ext z
      have := LinearMap.congr_fun h (z, 0)
      simpa [sumForm_apply] using this
    · ext z
      have := LinearMap.congr_fun h (0, z)
      simpa [sumForm_apply] using this
  · intro φ
    obtain ⟨x, hx⟩ := hB.2 (φ ∘ₗ LinearMap.inl ℤ L M)
    obtain ⟨y, hy⟩ := hC.2 (φ ∘ₗ LinearMap.inr ℤ L M)
    refine ⟨(x, y), LinearMap.ext fun z => ?_⟩
    rw [sumForm_apply, hx, hy]
    simp [← map_add (f := _)]

theorem sumForm_baseChange {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : ℝ ⊗[ℤ] (L × M)) :
    (sumForm B C).baseChange ℝ x y =
      B.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).1 (TensorProduct.prodRight ℤ ℝ ℝ L M y).1 +
      C.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).2 (TensorProduct.prodRight ℤ ℝ ℝ L M y).2 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Prod.fst_add, Prod.snd_add, ha, hb]; ring
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, ha, hb]; ring
    | tmul s v => simp [sumForm_apply, add_smul, add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sumDatum (D D' : Datum H) : Datum H where
  La := D.La × D'.La
  fin := by haveI := D.fin; haveI := D'.fin; infer_instance
  proj := by haveI := D.proj; haveI := D'.proj; infer_instance
  EF := sumForm D.EF D'.EF
  alt := fun x => by simp [sumForm_apply, D.alt, D'.alt]
  unimod := sumForm_bijective D.EF D'.EF D.unimod D'.unimod
  adj := fun a x y => by simp [sumForm_apply, D.adj, D'.adj]
  p := D.p + D'.p
  q := D.q + D'.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    haveI := D'.fin
    haveI := D'.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (D.La × D'.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h2' := (TensorProduct.isBaseChange (𝓞 E) D'.La E).finrank_eq
    have h3 := (TensorProduct.prodRight (𝓞 E) E E D.La D'.La).finrank_eq
    rw [← h1, h3, Module.finrank_prod, h2, h2', D.rank, D'.rank]
    ring
  dom := by
    haveI := D.fin
    haveI := D'.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    obtain ⟨J', h1', h2', h3', h4'⟩ := D'.dom
    set e := TensorProduct.prodRight ℤ ℝ ℝ D.La D'.La with he
    refine ⟨blockEnd e J J', ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      simp [blockEnd_apply, h1, h1', Prod.ext_iff]
    · intro x y
      simp only [sumForm_baseChange, ← he, blockEnd_apply, h2, h2']
    · intro x hx
      simp only [sumForm_baseChange, ← he, blockEnd_apply]
      have hne : e x ≠ 0 := fun hc => hx (e.injective (by rw [map_zero]; exact hc))
      by_cases ha : (e x).1 = 0
      · have hb : (e x).2 ≠ 0 := fun hb => hne (Prod.ext ha hb)
        simpa [ha] using h3' _ hb
      · by_cases hb : (e x).2 = 0
        · simpa [hb] using h3 _ ha
        · exact add_pos (h3 _ ha) (h3' _ hb)
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribSMul.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      let A1 : ℝ ⊗[ℤ] D'.La →ₗ[ℝ] ℝ ⊗[ℤ] D'.La :=
        ((DistribSMul.toAddMonoidHom D'.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      obtain ⟨k1', k2', k3'⟩ := h4' a A1 _ (fun x => by simp [A1]) rfl
      have hAA : A = blockEnd e A0 A1 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          rw [blockEnd_apply]
          simp [he, A0, A1]
      have ht' : t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) +
          ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D'.p : ℂ) * τ (a : E) + (D'.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, blockEnd_comp, blockEnd_comp, trace_blockEnd, trace_blockEnd, k1, ← k1, k1', ← k1', k2, k3, k2', k3',
        ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.add_re]; ring
      · rw [Complex.add_im]; ring

end

end GlobalTheory.DatumSum

namespace GlobalTheory

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CharacterFunction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem natCast_mem_half {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hM : l₂.M = l.M * pd)
    (hMb : l₂.Mb = l.Mb * I) : (pd : 𝓞 E) ∈ I := by
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} := by
    have h2 := l₂.prod
    rw [hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
      ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have : Ideal.span {(pd : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem nsmul_mem_smul_top {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] {I : Ideal R} {N : ℕ}
    (h : (N : R) ∈ I) (x : L) : N • x ∈ (I • ⊤ : Submodule R L) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul h trivial

end GlobalTheory.CharacterFunction
end
