module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.RingTheory.PowerSeries.Trunc

@[expose] public section

section

open Polynomial

namespace GlobalTheory

theorem charpoly_mulLeft_separable_of_adjoin_eq_top : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A]
    [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A →
    (LinearMap.mulLeft E y).charpoly.Separable := by
  intro E A _ _ _ _ _ y htop hred
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hfin : Module.finrank E A = (minpoly E y).natDegree := pb.finrank
  have hmin : minpoly E (LinearMap.mulLeft E y) = minpoly E y := by
    have h := minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective (R := E) (A := A)) y
    rw [← h]
    rfl
  have hdvd : minpoly E y ∣ (LinearMap.mulLeft E y).charpoly :=
    hmin ▸ LinearMap.minpoly_dvd_charpoly _
  have heq : (LinearMap.mulLeft E y).charpoly = minpoly E y :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hdvd
      (by rw [LinearMap.charpoly_natDegree, hfin])
  rw [heq]
  have hsq : Squarefree (minpoly E y) := (minpoly.isRadical E y).squarefree (minpoly.ne_zero hint)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory
end

section

namespace GlobalTheory

open QuotientGroup

theorem transfer_cocycle_formula :
    ∀ (R G X : Type) [CommRing R] [Group G] [AddCommGroup X] [Module R X]
      (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)],
      (fun tr : (G → X) → G → X =>
        (∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H) ∧
        (∀ f : G → X, (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ρ a (f b)) →
          ∀ a b, tr f (a * b) = tr f a + ρ a (tr f b)) ∧
        (∀ (f : G → X) (x : X), (∀ h ∈ H, f h = ρ h x - x) →
          ∀ g, tr f g = ρ g (∑ q : G ⧸ H, ρ q.out x) - ∑ q : G ⧸ H, ρ q.out x) ∧
        (∀ f : G → X, (∀ a b, f (a * b) = f a + ρ a (f b)) →
          ∀ g, tr f g = H.index • f g +
            (ρ g (∑ q : G ⧸ H, f q.out) - ∑ q : G ⧸ H, f q.out)))
        (fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))) := by
  intro R G X _ _ _ _ ρ H _
  have mem : ∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H := by
    intro g q
    have h1 : (((g • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rw [mul_assoc]
    exact QuotientGroup.eq.mp h1
  have reidx : ∀ (g : G) (F : G ⧸ H → X), ∑ q, F (g • q) = ∑ q, F q := fun g F =>
    Equiv.sum_comp (MulAction.toPerm g) F
  have rmul : ∀ (s t : G) (y : X), ρ s (ρ t y) = ρ (s * t) y := by
    intro s t y
    rw [map_mul, mul_apply_eq_comp]
  refine ⟨mem, ?_, ?_, ?_⟩
  · intro f hf a b
    have key : ∀ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
        = ρ (a • (b • q)).out (f ((a • (b • q)).out⁻¹ * a * (b • q).out))
          + ρ a (ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out))) := by
      intro q
      rw [mul_smul]
      have e : (a • b • q).out⁻¹ * (a * b) * q.out
          = ((a • b • q).out⁻¹ * a * (b • q).out) * ((b • q).out⁻¹ * b * q.out) := by group
      rw [e, hf _ (mem a (b • q)) _ (mem b q), map_add (f := _), rmul, rmul]
      congr 3
      group
    show ∑ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
      = ∑ q : G ⧸ H, ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out))
        + ρ a (∑ q : G ⧸ H, ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out)))

    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, map_sum,
    reidx b (fun q => ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out)))]
  · intro f x hf g
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = ρ g (ρ q.out x) - ρ (g • q).out x := by
      intro q
      rw [hf _ (mem g q), map_sub, rmul, rmul]
      congr 2
      group
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _

    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, map_sum,
    reidx g (fun q => ρ q.out x)]
  · intro f hf g
    have f1 : f 1 = 0 := by
      have := hf 1 1
      simp only [mul_one, map_one, one_apply_eq_self] at this
      exact left_eq_add.mp this
    have finv : ∀ s : G, ρ s (f s⁻¹) = - f s := by
      intro s
      have := hf s s⁻¹
      rw [mul_inv_cancel, f1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = (f g + ρ g (f q.out)) - f (g • q).out := by
      intro q
      rw [mul_assoc, hf, map_add (f := _), finv, rmul, mul_inv_cancel, map_one, one_apply_eq_self, hf]
      abel
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _

    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, reidx g (fun q => f q.out), Finset.sum_const, Finset.card_univ,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    abel

end GlobalTheory
end

section

namespace GlobalTheory

open scoped BigOperators

theorem corCoc_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * g * q.out ∈ H := by
  have h : (QuotientGroup.mk (g • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have := QuotientGroup.eq.mp h
  simpa [mul_assoc] using this

theorem exists_corestriction_cocycle : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → (∀ x, Continuous fun g => ρ g x) → ∀ f : G → X, ContinuousOn f H → (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + ρ g (f h)) → ∃ F : G → X, Continuous F ∧ (∀ g h, F (g * h) = F g + ρ g (F h)) ∧ (∃ x, ∀ h ∈ H, F h = (∑ᶠ q : G ⧸ H, ρ q.out (f (q.out⁻¹ * h * q.out))) + (ρ h x - x)) ∧ ∀ (Y : Submodule R X), (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → ∀ (f₀ : G → X) (x : X), (∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ Y) → (∀ h ∈ H, f h - f₀ h - (ρ h x - x) ∈ Y) → ∃ x', ∀ g, F g - H.index • f₀ g - (ρ g x' - x') ∈ Y := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ _ hH hρ _ f hf hc
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hmul : ∀ (a b : G) (x : X), ρ a (ρ b x) = ρ (a * b) x := by
    intro a b x
    rw [map_mul]; rfl
  refine ⟨fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)), ?_, ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun q _ => ?_
    rw [continuous_iff_continuousAt]
    intro g₀
    have hk : Continuous fun g : G => (g₀ • q).out⁻¹ * g * q.out := by fun_prop
    have hn : ∀ᶠ g in nhds g₀, (g₀ • q).out⁻¹ * g * q.out ∈ H :=
      hk.continuousAt.preimage_mem_nhds (hH.mem_nhds (corCoc_mem H g₀ q))
    have h1 : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
      refine (hρ _).continuousAt.comp ?_
      exact ContinuousAt.comp (g := f) (hf.continuousAt (hH.mem_nhds (corCoc_mem H g₀ q)))
        hk.continuousAt
    refine h1.congr ?_
    filter_upwards [hn] with g hg
    have : g • q = g₀ • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' (g₀ • q)]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk (g₀ • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hg)
    rw [this]
  · intro g h

    simp only [map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm h)
      (fun q : G ⧸ H => ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply, mul_smul]
    have e : (g • h • q).out⁻¹ * (g * h) * q.out =
        ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out) := by group
    rw [e, hc _ (corCoc_mem H g (h • q)) _ (corCoc_mem H h q), map_add (f := _), hmul, hmul]
    congr 3
    group
  · refine ⟨0, fun h hh => ?_⟩
    rw [finsum_eq_sum_of_fintype]
    simp only [map_zero, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : h • q = q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (h * q.out)
      refine QuotientGroup.eq.mpr ?_
      have := Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out
      simpa [mul_assoc] using this
    rw [this]
  · intro Y hY f₀ x h₀ hx
    refine ⟨∑ q : G ⧸ H, (f₀ q.out + ρ q.out x), fun g => ?_⟩
    have hidx : H.index • f₀ g = ∑ _q : G ⧸ H, f₀ g := by
      rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    have hre : ∑ q : G ⧸ H, (f₀ q.out + ρ q.out x) =
        ∑ q : G ⧸ H, (f₀ (g • q).out + ρ (g • q).out x) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f₀ q.out + ρ q.out x)).symm

    rw [hidx, map_sum, hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
    refine Y.sum_mem fun q _ => ?_
    set s' := (g • q).out
    set s := q.out
    have e : s' * (s'⁻¹ * g * s) = g * s := by group
    have a1 := hY s' _ (hx _ (corCoc_mem H g q))
    have a2 := h₀ s' (s'⁻¹ * g * s)
    have a3 := h₀ g s
    rw [e] at a2
    change ρ s' (f (s'⁻¹ * g * s) - f₀ (s'⁻¹ * g * s) - (ρ (s'⁻¹ * g * s) x - x)) ∈ Y at a1
    rw [map_sub, map_sub, map_sub, hmul, e] at a1
    have := Y.add_mem (Y.sub_mem a1 a2) a3
    convert this using 1
    rw [map_add (f := _), hmul]
    abel

end GlobalTheory
end

section

noncomputable section

open PowerSeries

namespace GlobalTheory.NB.LT

def F (R : Type) [CommRing R] (l : ℕ) : Polynomial R :=
  Polynomial.X * (Polynomial.X + Polynomial.C (l : R)) ^ (l - 1)

abbrev EE (R : Type) [CommRing R] (l : ℕ) : Type :=
  AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))

variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma subsingleton_of_isHausdorff_whole_ideal {I : Ideal R} [IsHausdorff I R] (h : I = ⊤) :
    Subsingleton R := by
  subst h
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : R, z = 0 := fun z =>
    IsHausdorff.haus ‹_› z fun n => by simp [Ideal.top_pow, SModEq.top]
  rw [key x, key y]

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma order_map_toNat_eq_natDegree_of_isDistinguishedAt {I : Ideal R} {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (hI : I ≠ ⊤) :
    ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat = p.natDegree := by
  have h1 : constantCoeff (1 : R⟦X⟧) ∉ I := by
    simpa [Ideal.eq_top_iff_one] using hI
  have := H.coe_natDegree_eq_order_map (p : R⟦X⟧) 1 h1 (by simp)
  rw [← this]
  simp


open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.exists_poly_mod [Nontrivial R] {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (a : R⟦X⟧) :
    ∃ r : Polynomial R, r.degree < p.degree ∧ (p : R⟦X⟧) ∣ a - r := by
  have hI : I ≠ ⊤ := by
    intro h
    have := subsingleton_of_isHausdorff_whole_ideal (I := I) h
    exact not_subsingleton R this
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hd := D.isWeierstrassDivisionAt_div_mod a
  refine ⟨D.mod a, ?_, D.div a, sub_eq_iff_eq_add.mpr hd.eq_mul_add⟩
  have hlt := hd.degree_lt
  rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI] at hlt
  rwa [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero H.monic)]


open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.poly_dvd_of_dvd {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) {r : Polynomial R} (h : (p : R⟦X⟧) ∣ (r : R⟦X⟧)) : p ∣ r := by
  by_cases hI : I = ⊤
  · have := subsingleton_of_isHausdorff_whole_ideal (I := I) hI
    rw [Subsingleton.elim r 0]
    exact dvd_zero p
  have hm := H.monic
  obtain ⟨h, hh⟩ := h
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hdeg : (r %ₘ p).degree < ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat := by
    rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI]
    by_cases hs : Nontrivial R
    · exact (Polynomial.degree_modByMonic_lt r hm).trans_le Polynomial.degree_le_natDegree
    · rw [not_nontrivial_iff_subsingleton] at hs
      rw [Subsingleton.elim (r %ₘ p) 0]
      simp
  have hmul : (p : R⟦X⟧) * (h - ((r /ₘ p : Polynomial R) : R⟦X⟧)) = ((r %ₘ p : Polynomial R) : R⟦X⟧) := by
    have e := Polynomial.modByMonic_add_div r p
    have e' : ((r %ₘ p : Polynomial R) : R⟦X⟧) + (p : R⟦X⟧) * ((r /ₘ p : Polynomial R) : R⟦X⟧)
        = (r : R⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_add, e]
    rw [mul_sub, ← hh, ← e']
    ring
  have := (D.eq_zero_of_mul_eq hdeg hmul).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp this

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.algHom_coe {B : Type} [CommRing B] [Algebra R B] (σ : R⟦X⟧ →ₐ[R] B) (r : Polynomial R) :
    σ (r : R⟦X⟧) = Polynomial.aeval (σ X) r := by
  have e : σ.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (σ X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun e r

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma X_pow_dvd_sub_aeval_trunc (ρ : R⟦X⟧ →ₐ[R] R⟦X⟧) (hρ : X ∣ ρ X) (n : ℕ)
    (f : R⟦X⟧) : X ^ n ∣ ρ f - Polynomial.aeval (ρ X) (trunc n f) := by
  obtain ⟨g, hg⟩ : X ^ n ∣ f - (trunc n f : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [coeff_trunc, hm]
  have e : ρ f - Polynomial.aeval (ρ X) (trunc n f) = ρ (X ^ n) * ρ g := by
    rw [← _root_.GlobalTheory.NB.LT.algHom_coe ρ, ← map_sub, hg, map_mul]
  rw [e, map_pow]
  exact (pow_dvd_pow_of_dvd hρ n).mul_right _


open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.algHom_ext_X (σ τ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h : σ X = τ X) (hX : X ∣ σ X) : σ = τ := by
  refine AlgHom.ext fun f => PowerSeries.ext fun m => ?_
  have h1 := X_pow_dvd_sub_aeval_trunc σ hX (m + 1) f
  have h2 := X_pow_dvd_sub_aeval_trunc τ (h ▸ hX) (m + 1) f
  rw [h] at h1
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := (X_pow_dvd_iff.mp h3) m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this

end GlobalTheory.NB.LT
end
end

section

open Polynomial

namespace GlobalTheory

theorem charpoly_mulLeft_eq_map_of_spanning_lattice (R F A S : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A]
    [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S]
    [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A) (hι : Function.Injective ι)
    (hspan : Submodule.span F (Set.range ι) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly =
      ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  classical
  have hRF : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  haveI : Module.IsTorsionFree R S := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      apply hι
      have h1 : algebraMap R F r • ι x = 0 := by
        rw [algebraMap_smul, ← map_smul, h, map_zero]
      have h2 : algebraMap R F r ≠ 0 := fun h0 => hr (hRF (by simpa using h0))
      rw [map_zero]
      exact (smul_eq_zero.mp h1).resolve_left h2
  haveI : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let b : Module.Basis (Fin (Module.finrank R S)) R S := Module.finBasis R S
  refine ⟨_, b, fun x => ?_⟩
  have hexp : ∀ y : S, ι y = ∑ i, algebraMap R F (b.repr y i) • ι (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]

    simp only [map_sum, map_smul, algebraMap_smul]
  have hliR : LinearIndependent R (fun i => ι (b i)) :=
    b.linearIndependent.map' ι.toLinearMap (LinearMap.ker_eq_bot.mpr hι)
  have hli : LinearIndependent F (fun i => ι (b i)) :=
    (LinearIndependent.iff_fractionRing R F).mp hliR
  have hsp : ⊤ ≤ Submodule.span F (Set.range (fun i => ι (b i))) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [hexp y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin (Module.finrank R S)) F A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = ι (b i) := fun i => by simp [b']
  have hM : LinearMap.toMatrix b' b' (LinearMap.mulLeft F (ι x)) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft R x)).map (algebraMap R F) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, hb', ← map_mul, hexp]
    simp only [← hb']
    rw [b'.repr_sum_self]
  rw [← LinearMap.charpoly_toMatrix _ b', hM, Matrix.charpoly_map]

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory

open Module

theorem card_subspaces_le_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (p : Submodule k V) (j : ℕ) :
    Nat.card {U : Submodule k V // U ≤ p ∧ finrank k U = j} =
      Nat.card {U : Submodule k p // finrank k U = j} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun U => ⟨U.1.map p.subtype, Submodule.map_subtype_le p U.1, ?_⟩) ⟨?_, ?_⟩)
  · rw [Submodule.finrank_map_subtype_eq]; exact U.2
  · intro U U' h
    exact Subtype.ext (Submodule.map_injective_of_injective p.injective_subtype
      (congrArg Subtype.val h))
  · rintro ⟨U, hU, hj⟩
    have h : (U.comap p.subtype).map p.subtype = U := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hU]
    refine ⟨⟨U.comap p.subtype, ?_⟩, Subtype.ext h⟩
    rw [← Submodule.finrank_map_subtype_eq, h, hj]

theorem card_subspaces_finrank_congr {k V V' : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] (e : V ≃ₗ[k] V') (j : ℕ) :
    Nat.card {U : Submodule k V // finrank k U = j} =
      Nat.card {U : Submodule k V' // finrank k U = j} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_)
  intro U
  have : finrank k (U.map (e : V →ₗ[k] V')) = finrank k U := LinearEquiv.finrank_map_eq e U
  change _ ↔ finrank k (U.map (e : V →ₗ[k] V')) = j
  rw [this]

end GlobalTheory
end
