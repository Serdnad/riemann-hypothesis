module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
public import GroundTheory.ProfiniteCohomology.Bundle001
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle001
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle003
public import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.NumberTheory.NumberField.Norm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

theorem _root_.GlobalTheory.T.generalLinear_integral_compact_open : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧ LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧ IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by
  first | exact @GlobalTheory.CompanionTheory.QLTop.gl_topology | exact GlobalTheory.CompanionTheory.QLTop.gl_topology | (intros; apply GlobalTheory.CompanionTheory.QLTop.gl_topology <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

theorem _root_.GlobalTheory.T.localField_uniformizer_norm_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by
  first | exact @GlobalTheory.CompanionTheory.QL.NormalisedValue.main | exact GlobalTheory.CompanionTheory.QL.NormalisedValue.main | (intros; apply GlobalTheory.CompanionTheory.QL.NormalisedValue.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.conormal_rank_one_of_locally_principal : ∀ {A : Type} [CommRing A] [IsDomain A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) → Module.rankAtStalk I.Cotangent P = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.locally_principal_of_conormal_rank_one : ∀ {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), Module.rankAtStalk I.Cotangent P = 1 → LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_notMem_support {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by
  rw [Scheme.IdealSheafData.mem_support_iff] at hx
  push_neg at hx
  obtain ⟨U, hU⟩ := hx
  rw [Scheme.mem_zeroLocus_iff] at hU
  push_neg at hU
  obtain ⟨f, hf, hxf⟩ := hU
  refine ⟨X.affineBasicOpen f, 1, hxf, Submonoid.one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← J.map_ideal_basicOpen U f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem exists_gen_of_map_eq_span {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (t : A)
    [IsLocalization.Away t B] (I : Ideal A) (b : B) (hb : b ≠ 0)
    (hI : I.map (algebraMap A B) = Ideal.span {b}) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f} := by
  have hbI : b ∈ I.map (algebraMap A B) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨⟨f, s⟩, hf⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers t) B).mp hbI
  refine ⟨f, f.2, ?_, ?_⟩
  · intro h0
    apply hb
    rw [h0, map_zero] at hf
    exact ((IsLocalization.map_units B s).mul_left_eq_zero).mp hf
  · intro g hg
    have hg' : algebraMap A B g ∈ Ideal.span {b} := by
      rw [← hI]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg'
    obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers t) c
    have key : algebraMap A B ((u : A) * (s : A) * g) = algebraMap A B (a * (f : A)) := by
      rw [map_mul, map_mul, map_mul, ← hc, ← hu, ← hf]
      ring
    obtain ⟨e, he⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) B).mp key
    obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp e.2
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    rw [← hl, ← hj, ← hk] at he
    refine ⟨l + j + k, Ideal.mem_span_singleton'.mpr ⟨t ^ l * a, ?_⟩⟩
    rw [pow_add, pow_add]
    linear_combination -he

theorem locPrincipal_of_cartAt : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) →
    LocPrincipal (Z.ideal U) q.asIdeal := by
  intro X _ Z U q hC
  obtain ⟨V, h, hxV, hh, hZV⟩ := hC
  have hxU : U.2.fromSpec q ∈ (U.1 : X.Opens) := by
    have hr : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rw [U.2.range_fromSpec] at hr
    exact hr
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter U.2 V.2 (U.2.fromSpec q) ⟨hxU, hxV⟩
  have hWU : X.basicOpen f ≤ U.1 := X.basicOpen_le f
  have hWV : X.basicOpen f ≤ V.1 := by
    rw [hfg]
    exact X.basicOpen_le g
  haveI : Nonempty (X.basicOpen f) := ⟨⟨_, hxf⟩⟩
  haveI : Nonempty (V.1 : X.Opens) := ⟨⟨_, hxV⟩⟩
  haveI : IsDomain Γ(X, V.1) := IsIntegral.component_integral V.1
  have hZW : Z.ideal (X.affineBasicOpen f) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    have hmap := Z.map_ideal (U := X.affineBasicOpen f) (V := V) hWV
    rw [hZV, Ideal.map_span, Set.image_singleton] at hmap
    first
      | exact hmap.symm
      | (rw [← hmap]; rfl)
      | (convert hmap.symm using 3)
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hb : (X.presheaf.map (homOfLE hWV).op).hom h ≠ 0 := by
    intro h0
    apply nonZeroDivisors.ne_zero hh
    apply map_injective_of_isIntegral X (homOfLE hWV)
    rw [map_zero]
    exact h0
  have hI : (Z.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    rw [← hZW]
    first
      | exact Z.map_ideal (U := X.affineBasicOpen f) (V := U) hWU
      | exact Z.map_ideal_basicOpen U f
  obtain ⟨f0, hf0, hf0ne, hgen⟩ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_gen_of_map_eq_span f (Z.ideal U) _ hb hI
  refine ⟨f, f0, ?_, hf0, hf0ne, hgen⟩
  have hq : q ∈ PrimeSpectrum.basicOpen f :=
    Eq.mp (congrArg (q ∈ ·) (U.2.fromSpec_preimage_basicOpen f)) hxf
  exact (PrimeSpectrum.mem_basicOpen f q).mp hq

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_locPrincipal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  intro X _ Z U q h
  obtain ⟨t, f, ht, hfI, hf0, hg⟩ := h
  have hx : U.2.fromSpec q ∈ X.basicOpen t := by
    have h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact ht
    exact h1
  have hxU : U.2.fromSpec q ∈ U.1 := X.basicOpen_le t hx
  have inst := U.2.isLocalization_basicOpen t
  let ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  have hu : IsUnit (ρ t) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t
  have hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U) :=
    (Z.map_ideal_basicOpen U t).symm
  have hne : Nonempty (X.basicOpen t : X.Opens) := ⟨⟨_, hx⟩⟩
  have hρf : ρ f ≠ 0 := by
    intro h0
    apply hf0
    apply germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU
    have h2 := congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0
    rw [map_zero] at h2 ⊢
    rw [← h2]
    simp [ρ]
  have hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t) := mem_nonZeroDivisors_of_ne_zero hρf
  suffices hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from
    ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hgI
    obtain ⟨n, hn⟩ := hg g hgI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨u, hu'⟩ := hu.pow n
    refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩
    have h3 : ρ c * ρ f = ρ t ^ n * ρ g := by
      rw [← map_mul, hc, map_mul, map_pow]
    rw [mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem ρ hfI

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finite_continuous_crossed_homomorphisms : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V → (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) → {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Cocycles.finite_cocycles | exact GlobalTheory.CompanionTheory.Cocycles.finite_cocycles | (intros; apply GlobalTheory.CompanionTheory.Cocycles.finite_cocycles <;> assumption)
end

section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Glob

theorem not_pow_dvd_different (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime]
    (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 E) ∈ P) (hPJ : ¬ P ∣ J)
    (hspan : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J) :
    ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  intro hdiv
  set d := Module.finrank ℚ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp0 hpP
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPbot
  have hpd : ((p : 𝓞 E)) ^ d ∈ P := Ideal.pow_mem_of_mem P hpP d hdpos
  have hspanP : Ideal.span {((p : 𝓞 E)) ^ d} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hpd
  have hJP : ¬ J ≤ P := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hspan
    exact hJP (hspan ▸ hspanP)
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hPmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hJP (h ▸ le_sup_right))
  obtain ⟨y, hy, x, hx, hyx⟩ := Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))
  have hxy : x * y ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    rw [hspan, mul_comm x y]
    exact Ideal.mul_mem_mul hy hx
  have hidem : x * x - x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    have : x * x - x = -(x * y) := by
      have : x = 1 - y := by rw [← hyx]; ring
      rw [this]; ring
    rw [this]
    exact neg_mem hxy
  have hnot : x ∉ Ideal.span {((p : 𝓞 E)) ^ d} := by
    intro h
    have h1 : x ∈ P := hspanP h
    have h2 : y ∈ P := Ideal.pow_le_self hk hy
    exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 (hyx ▸ add_mem h2 h1))
  have hlt : Module.finrank ℤ (𝓞 E) < p ^ d := by
    rw [RingOfIntegers.rank]
    exact Nat.lt_pow_self hp.one_lt
  refine GlobalTheory.T.trace_idempotent_not_divisible (𝓞 E) x p d hp hlt hidem hnot ?_

  have hpdE : ((p : E)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hD0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hz : (x : E) / ((p : E)) ^ d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
        ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
    rw [hdual, FractionalIdeal.mem_inv_iff hD0]
    intro w hw
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    have hδP : δ ∈ P ^ k := Ideal.dvd_iff_le.1 hdiv hδ
    have hmem : δ * x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
      rw [hspan]
      exact Ideal.mul_mem_mul hδP hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨a, ?_⟩
    have h2 : algebraMap (𝓞 E) E a * ((p : E)) ^ d = algebraMap (𝓞 E) E δ * (x : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      simpa using this
    field_simp
    rw [h2]
    ring
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have htr := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h10).1 hz 1 (FractionalIdeal.one_mem_one _)
  obtain ⟨n, hn⟩ := htr
  rw [Algebra.traceForm_apply, mul_one] at hn
  have hzs : (x : E) / ((p : E)) ^ d = (((p : ℚ) ^ d)⁻¹) • (x : E) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
  rw [hzs, map_smul, smul_eq_mul, ← Algebra.coe_trace_int] at hn
  have hpq : ((p : ℚ)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨n, ?_⟩
  have : ((Algebra.trace ℤ (𝓞 E) x : ℤ) : ℚ) = ((p : ℚ)) ^ d * (n : ℚ) := by
    have h3 : (algebraMap ℤ ℚ n) = (n : ℚ) := rfl
    rw [h3] at hn
    rw [hn]
    field_simp
  exact_mod_cast this

end GlobalTheory.CompanionTheory.Glob
end

section

open Matrix


theorem _root_.GlobalTheory.T.hermitian_form_change_of_basis_lie : ∀ {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ) (J : Matrix (Fin n) (Fin n') ℂ),
    Hᴴ = H → H'ᴴ = H' → IsUnit H.det → IsUnit H'.det → Jᴴ * H * J = H' →
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  first | exact @GlobalTheory.CompanionTheory.IsometricMatrix.main | exact GlobalTheory.CompanionTheory.IsometricMatrix.main | (intros; apply GlobalTheory.CompanionTheory.IsometricMatrix.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.KaehlerSpread

open KaehlerDifferential

noncomputable abbrev diffMap (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) : (Fin n →₀ A) →ₗ[A] Ω[A⁄K] :=
  Finsupp.linearCombination A fun i => D K A (x i)

theorem map_diffMap_eq (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [IsLocalization S B] :
    (IsLocalizedModule.mapExtendScalars S
      (Finsupp.mapRange.linearMap (Algebra.linearMap A B) : (Fin n →₀ A) →ₗ[A] (Fin n →₀ B))
      (map K K A B) B (diffMap K x)) =
      Finsupp.linearCombination B fun i => D K B (algebraMap A B (x i)) := by
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have h1 : (Finsupp.single i (1 : B) : Fin n →₀ B) =
      Finsupp.mapRange.linearMap (Algebra.linearMap A B) (Finsupp.single i (1 : A)) := by
    simp
  rw [h1, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  simp [diffMap]

theorem bijective_linearCombination_iff {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (v : ι → M) :
    Function.Bijective (Finsupp.linearCombination B v) ↔
      LinearIndependent B v ∧ Submodule.span B (Set.range v) = ⊤ := by
  rw [Function.Bijective, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  rfl

theorem spread : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  intro K A _ _ _ _ P _ n x hP
  classical
  let l₁ : (Fin n →₀ A) →ₗ[A] (Fin n →₀ Localization.AtPrime P) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime P))
  let l₂ : Ω[A⁄K] →ₗ[A] Ω[Localization.AtPrime P⁄K] :=
    KaehlerDifferential.map K K A (Localization.AtPrime P)
  have hP' : Function.Bijective (IsLocalizedModule.map P.primeCompl l₁ l₂ (diffMap K x)) := by
    have h := (bijective_linearCombination_iff _).mpr hP
    rw [← map_diffMap_eq K x P.primeCompl (Localization.AtPrime P)] at h
    exact h
  obtain ⟨s, hs, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective (diffMap K x) P l₁ l₂ hP'
  refine ⟨s, hs, ?_⟩
  intro B _ _ _ _ _
  rw [← bijective_linearCombination_iff, ← map_diffMap_eq K x (Submonoid.powers s) B]
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)) (KaehlerDifferential.map K K A B)).mpr hbij

end GlobalTheory.CompanionTheory.KaehlerSpread
end
