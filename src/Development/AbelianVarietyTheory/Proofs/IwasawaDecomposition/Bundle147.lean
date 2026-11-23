module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle145
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l), sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  first | exact @GlobalTheory.MemLoc.TAct.t_act | exact GlobalTheory.MemLoc.TAct.t_act | (intros; apply GlobalTheory.MemLoc.TAct.t_act <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, phiA l C.t = (l : Per.Acris l) * C.t := by
  first | exact @GlobalTheory.MemLoc.TPhi.t_phi | exact GlobalTheory.MemLoc.TPhi.t_phi | (intros; apply GlobalTheory.MemLoc.TPhi.t_phi <;> assumption)
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ), (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ := by
  first | exact @GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult | exact GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult | (intros; apply GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult <;> assumption)
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem half_int_coords {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (a b : ℚ)
    (hy : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    ∃ t u : ℤ, (2 : ℤ) ∣ t - u ∧ 2 * a = t ∧ 2 * b = u := by
  have hcy : IsIntegral ℤ ((a : E) - (b : E) * s) := by
    have := hy.map (c.toRingEquiv.toRingHom.toIntAlgHom)
    simpa [hc, sub_eq_add_neg] using this
  have key : ∀ q : ℚ, IsIntegral ℤ (q : E) → ∃ n : ℤ, q = n := by
    intro q hq
    have h1 : IsIntegral ℤ q := by
      have : (q : E) = algebraMap ℚ E q := by simp
      rw [this] at hq
      exact (isIntegral_algebraMap_iff ).1 hq
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    exact ⟨n, by simpa using hn.symm⟩
  obtain ⟨t, ht⟩ := key (2 * a) (by
    have e : ((2 * a : ℚ) : E) = ((a : E) + (b : E) * s) + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]; exact hy.add hcy)
  obtain ⟨n, hn⟩ := key (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E) = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast; linear_combination (b : E) ^ 2 * hs
    rw [e]; exact hy.mul hcy)
  have hm : (d : ℚ) * (2 * b) ^ 2 = ((4 * n - t ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [← ht, ← hn]; ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * b) = k := by
    have h1 : IsIntegral ℤ (((d : ℚ) * (2 * b)) ^ 2) := by
      have : ((d : ℚ) * (2 * b)) ^ 2 = algebraMap ℤ ℚ (d * (4 * n - t ^ 2)) := by
        rw [eq_intCast, Int.cast_mul, ← hm]; push_cast; ring
      rw [this]; exact isIntegral_algebraMap
    have h2 := IsIntegral.of_pow (by norm_num : 0 < 2) h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨n, by simpa using hn.symm⟩
  have hk2 : k ^ 2 = (d : ℤ) * (4 * n - t ^ 2) := by
    have : (k : ℚ) ^ 2 = (d : ℚ) * ((4 * n - t ^ 2 : ℤ) : ℚ) := by
      rw [← hm, ← hk]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (hk2 ▸ dvd_mul_right _ _)
  obtain ⟨u, rfl⟩ := hdk
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hu : 2 * b = u := by
    apply mul_left_cancel₀ hd0
    rw [hk]; push_cast; ring
  refine ⟨t, u, ?_, ht, hu⟩
  have h5 : (d : ℤ) * u ^ 2 = 4 * n - t ^ 2 := by
    rw [hu] at hm; exact_mod_cast hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e + 3 := ⟨(d : ℤ) / 4, by omega⟩
  have h6 : (2 : ℤ) ∣ (t - u) ^ 2 := ⟨2 * n - (2 * e + 1) * u ^ 2 - t * u, by
    rw [he] at h5; linear_combination h5⟩
  exact Int.prime_two.dvd_of_dvd_pow h6

theorem exists_rat_coords {E : Type} [Field E] [NumberField E] (d : ℕ)
    (s : E) (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ {s}) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s :=
  _root_.GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin d s hs hx

theorem normOne_iff_of_sqrt {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (M p : ℕ) :
    NormOne d M p ↔ ∃ π : 𝓞 E, (π : E) ∈ IntermediateField.adjoin ℚ {s} ∧ (π : E) * c (π : E) = (p : E) ∧
      (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)} := by
  have hsK : s ∈ IntermediateField.adjoin ℚ {s} := IntermediateField.mem_adjoin_simple_self ℚ _
  constructor
  · rintro ⟨A, B, hN, ⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) + 1 = 4 * e := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have heE : (d : E) + 1 = 4 * e := by exact_mod_cast congrArg (Int.cast : ℤ → E) he
    have hω : IsIntegral ℤ ((1 + s) / 2) := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C e, by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, eq_intCast]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * heE
    let ω : 𝓞 E := ⟨(1 + s) / 2, hω⟩
    have hA : (A : E) = 2 + M * u + 2 * M * v := by
      have : A = 2 + M * u + 2 * M * v := by linear_combination hv + hu
      rw [this]; push_cast; ring
    have hB : (B : E) = M * u := by rw [hu]; push_cast; ring
    have hπ : ((1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω) : 𝓞 E) : E) = ((A : E) + B * s) / 2 := by
      have h0 : algebraMap (𝓞 E) E ω = (1 + s) / 2 := rfl
      change algebraMap (𝓞 E) E _ = _
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_intCast]
      rw [h0, hA, hB]; ring
    refine ⟨1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω), ?_, ?_, ?_⟩
    · rw [hπ]
      exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hsK)) (ofNat_mem _ 2)
    · rw [hπ]
      have hNE : (A : E) ^ 2 + d * B ^ 2 = 4 * p := by exact_mod_cast congrArg (Int.cast : ℤ → E) hN
      rw [map_div₀, map_add (f := _), map_mul, map_intCast, map_intCast, hc, map_ofNat]
      linear_combination (1 / 4 : E) * hNE - (B : E) ^ 2 / 4 * hs
    · rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨π, hK, hN, hM⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hM
    have hyE : (π : E) = 1 + M * (y : E) := by
      have : π = 1 + M * y := by linear_combination hy
      rw [this]; push_cast; rfl
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · rw [hyE] at hN
      simp only [Nat.cast_zero, zero_mul, add_zero, map_one, mul_one] at hN
      have : p = 1 := by exact_mod_cast hN.symm
      exact ⟨2, 0, by simp [this], by simp, by simp⟩
    · have hME : (M : E) ≠ 0 := by exact_mod_cast hM0.ne'
      have hyK : (y : E) ∈ IntermediateField.adjoin ℚ {s} := by
        have : (y : E) = ((π : E) - 1) / M := by rw [hyE]; field_simp; ring
        rw [this]
        exact div_mem (sub_mem hK (one_mem _)) (natCast_mem _ _)
      obtain ⟨a, b, hab⟩ := exists_rat_coords d s hs hyK
      obtain ⟨t, u, ⟨w, hw⟩, ht, hu⟩ := half_int_coords d hd h4 s hs c hc a b (hab ▸ y.isIntegral_coe)
      have htE : 2 * (a : E) = t := by exact_mod_cast congrArg (Rat.cast : ℚ → E) ht
      have huE : 2 * (b : E) = u := by exact_mod_cast congrArg (Rat.cast : ℚ → E) hu
      refine ⟨2 + M * t, M * u, ?_, dvd_mul_right _ _, ⟨w, by linear_combination (M : ℤ) * hw⟩⟩
      rw [hyE, hab] at hN
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_ratCast, hc] at hN
      have : (2 + M * t : E) ^ 2 + d * (M * u) ^ 2 = 4 * p := by
        rw [← htE, ← huE]
        linear_combination 4 * hN + 4 * (M : E) ^ 2 * (b : E) ^ 2 * hs
      exact_mod_cast this

theorem normOne_iff_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), NormOne H.d M p ↔ ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)} := by
  intro R H M p
  have hs : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hc : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
    apply H.φ₀.injective
    have h1 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h2 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) :=
      H.conjE_apply _ _
    rw [h2, map_neg, h1]
    simp
  exact normOne_iff_of_sqrt H.d H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqrtMinusD hs H.conj hc M p

end GlobalTheory.Mem.An
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

theorem exists_unipB_mul_diagT_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  intro k _ _ _ _ m g
  obtain ⟨u, l, w, hw, h⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (points (Fin m)) g
  refine ⟨u, u.2, (leviTorus k (Fin m)).symm l, w, hw, ?_⟩
  rw [h]
  simp [diagT]

end GlobalTheory.SmGL
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem support_pushforward_subset_image_of_isClosedImmersion :
    ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules),
      support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  intro X Y g _ E y hy
  by_contra hyn
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hy
  apply hy
  have hemb := g.isClosedEmbedding
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t

  let Z0 : Set Y := {z | ∃ hz : z ∈ g ⁻¹ᵁ U, E.presheaf.germ (g ⁻¹ᵁ U) z hz s = 0}
  have hZ0 : IsOpen Z0 := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hz, hzs⟩
    obtain ⟨W, hzW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq E.presheaf z hz hz s 0
      (by rw [hzs, map_zero])
    refine ⟨W, fun z' hz' => ⟨(leOfHom iU) hz', ?_⟩, W.2, hzW⟩
    have := TopCat.Presheaf.germ_res_apply E.presheaf iU z' hz' s
    rw [he, map_zero, map_zero] at this
    exact this.symm
  obtain ⟨V', hV', hV'e⟩ := hemb.isInducing.isOpen_iff.1 hZ0
  let V : X.Opens := U ⊓ ⟨V' ∪ (Set.range g)ᶜ, hV'.union hemb.isClosed_range.isOpen_compl⟩
  have hyV : y ∈ V := by
    refine ⟨hyU, ?_⟩
    by_cases hr : y ∈ Set.range g
    · obtain ⟨z, rfl⟩ := hr
      have hzs : z ∉ support E := fun h => hyn ⟨z, h, rfl⟩
      have hz : z ∈ g ⁻¹ᵁ U := hyU
      refine Or.inl (show z ∈ g ⁻¹' V' from hV'e ▸ ⟨hz, (notMem_support_iff.1 hzs).elim _ _⟩)
    · exact Or.inr hr
  have hVU : V ≤ U := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV]
  have h0 : ((Scheme.Modules.pushforward g).obj E).presheaf.map (homOfLE hVU).op s = 0 := by
    refine section_eq_zero_of_germ (F := E) _ fun z hz => ?_
    have hz' : z ∈ Z0 := by
      rw [← hV'e]
      rcases hz.2 with h | h
      · exact h
      · exact absurd ⟨z, rfl⟩ h
    obtain ⟨hzU, hzs⟩ := hz'
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf ((Opens.map g.base).map (homOfLE hVU)) z hz s).trans hzs
  rw [h0, map_zero]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.exists_proj_map_proportional_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R), GeneratesAlong I σ g → FinalTheorems.EffCartier I → ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  first | exact @GlobalTheory.ProjBlowup.exists_proportional | exact GlobalTheory.ProjBlowup.exists_proportional | (intros; apply GlobalTheory.ProjBlowup.exists_proportional <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaCell

theorem exists_mem_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ g : GL (Fin m) k, ∃ a : Fin m → ℤ, g ∈ GlobalTheory.IwaCell.cell ϖ a := by
  intro k _ _ _ _ m ϖ hϖ g
  obtain ⟨k₀, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k m g⁻¹
  have hg' : g = b⁻¹ * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hg, inv_inv]
  set c := b⁻¹ with hc
  have hcT : c.val.BlockTriangular id := by
    have : c.val = b.val⁻¹ := by rw [hc, Matrix.coe_units_inv]
    rw [this]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdet : c.val.det = ∏ i, c.val i i := Matrix.det_of_upperTriangular hcT
  have hd : ∀ i, c.val i i ≠ 0 := fun i h => by
    have := Matrix.GeneralLinearGroup.det_ne_zero c
    rw [hdet] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let d : Fin m → kˣ := fun i => Units.mk0 _ (hd i)
  let a : Fin m → ℤ := fun i => ord k (d i)
  let e : Fin m → kˣ := fun i => d i / ϖ ^ a i
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => by
    apply ord_eq_zero_iff.1
    simp only [e, div_eq_mul_inv, ← _root_.zpow_neg, ord_mul, ord_zpow, hϖ, a]
    ring
  have hde : d = (fun i => ϖ ^ a i) * e := by
    funext i; simp [e]
  let u := c * (diagT k (Fin m) d)⁻¹
  have hu : u ∈ unipB k (Fin m) := by
    rw [mem_unipB]
    have hval : u.val = c.val * diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) := by
      simp only [u, ← map_inv, Units.val_mul, val_diagT, Pi.inv_apply]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval, mul_diagonal, hcT hij, zero_mul]
    · rw [hval, mul_diagonal]; simp [d, mul_inv_cancel₀ (hd i)]
  refine ⟨a, u, hu, diagT k (Fin m) e * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹,
    mul_mem (GlobalTheory.LocalCartan.diagT_mem_KO he) (inv_mem ⟨k₀, rfl⟩), ?_⟩
  rw [hg', tD, ← mul_assoc, mul_assoc u, ← map_mul, ← hde]
  simp [u]

end GlobalTheory.IwaCell
end
end

section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]

    simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]

    simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie


open GlobalTheory.AmbNormTie in
theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
end
