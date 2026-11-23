module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle024
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobianOrderMonotoneSemistableModel
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (q : X ⟶ Y) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map q).left q.left (pullback.fst Y.hom f) := by
  refine IsPullback.of_bot (h₃₁ := f) (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) ?_ ?_
    (IsPullback.of_hasPullback Y.hom f)
  · have h₁ : ((Over.pullback f).map q).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
      Over.w ((Over.pullback f).map q)
    have h₂ : q.left ≫ Y.hom = X.hom := Over.w q
    rw [h₁, h₂]
    exact IsPullback.of_hasPullback X.hom f
  · exact (pullback.lift_fst _ _ _).symm

theorem nonempty_torusExtension_pullback {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k)
    (G : Over (Sp k)) [GrpObj G] (h : Nonempty (TorusExtension G)) :
    Nonempty (TorusExtension ((Over.pullback f).obj G)) := by
  obtain ⟨T⟩ := h
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X
  have hq := isPullback_overPullback_map_left f T.q
  refine ⟨{ X := T.X
            addCommGroup := T.addCommGroup
            free := T.free
            finite := T.finite
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.hom ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

theorem exists_ringHom_comp_eq_of_isIntegral {W k Ω : Type} [CommRing W] [IsLocalRing W] [Field k] [Field Ω]
    [IsAlgClosed Ω] (ρ : W →+* k) (hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal W) (hi : ρ.IsIntegral)
    (φ : W →+* Ω) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal W) : ∃ ψ : k →+* Ω, ψ.comp ρ = φ := by
  let ρ' : IsLocalRing.ResidueField W →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) ρ fun a ha => (RingHom.mem_ker).1 (hρ ▸ ha)
  let φ' : IsLocalRing.ResidueField W →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ fun a ha => (RingHom.mem_ker).1 (hφ ▸ ha)
  letI := ρ'.toAlgebra
  letI := φ'.toAlgebra
  have hi' : ρ'.IsIntegral := RingHom.IsIntegral.tower_top (IsLocalRing.residue W) ρ' hi
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField W) k := ⟨hi'⟩
  let ψ : k →ₐ[IsLocalRing.ResidueField W] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom, RingHom.ext fun x => ?_⟩
  exact ψ.commutes (IsLocalRing.residue W x)

theorem isSemiAbelian_of_proper_generic_of_torusExtension : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  intro W L _ _ _ _ _ _ G _ hG hp k _ ρ hρ hi hT
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      Nonempty (TorusExtension ((Over.pullback (spMap a)).obj G)) →
      Nonempty (TorusExtension ((Over.pullback (spMap (ψ.comp a))).obj G)) := by
    intro Ω F _ _ a ψ h
    obtain ⟨E⟩ := nonempty_torusExtension_pullback (spMap ψ) _ h
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
    have : IsMonHom (pullCompIso (spMap ψ) (spMap a) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (spMap ψ) (spMap a) G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap ψ) (spMap a) G).symm E⟩
  have hA : IsAbelianScheme ((Over.pullback (spMap (algebraMap W L))).obj G) :=
    { comm := inferInstance
      smooth := by change Smooth (pullback.snd G.hom _); infer_instance
      proper := hp
      geomConnected := by change GeometricallyConnected (pullback.snd G.hom _); infer_instance }
  refine ⟨hc, hs, hsep, hqc, hgc, fun Ω _ _ q => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change Nonempty (TorusExtension ((Over.pullback (spMap φ.hom)).obj G))
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e]
    exact key Ω L _ _ ⟨GlobalTheory.torusExtensionOfAbelian _ hA⟩
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    obtain ⟨ψ, e⟩ := exists_ringHom_comp_eq_of_isIntegral ρ hρ hi φ.hom hm
    rw [← e]
    exact key Ω k _ _ hT

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  first | exact @GlobalTheory.SS.WtRat.wt_of_genericPoint | exact GlobalTheory.SS.WtRat.wt_of_genericPoint | (intros; apply GlobalTheory.SS.WtRat.wt_of_genericPoint <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem splits_of_monic_OO {q : (OO p)[X]} (hq : q.Monic) : q.Splits := by
  refine Splits.of_splits_map_of_injective (i := (OO p).subtype) Subtype.val_injective
    (IsAlgClosed.splits _) fun a ha => ?_
  have h : IsIntegral (OO p) a := ⟨q, hq, by
    have := isRoot_of_mem_roots ha
    rwa [IsRoot, Polynomial.eval_map] at this⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨y, hy⟩

theorem exists_root_residue_OO {q : (OO p)[X]} (hq : q.Monic) {b : kb p}
    (hb : q.eval₂ (residue (OO p)) b = 0) : ∃ a : OO p, q.eval a = 0 ∧ residue (OO p) a = b := by
  have h0 : q.map (residue (OO p)) ≠ 0 := (hq.map _).ne_zero
  have h : b ∈ (q.map (residue (OO p))).roots := by
    rw [mem_roots h0, IsRoot, Polynomial.eval_map, hb]
  rw [(splits_of_monic_OO hq).roots_map_of_ne_zero h0, Multiset.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, isRoot_of_mem_roots ha, rfl⟩

theorem isAlgClosed_kb : IsAlgClosed (kb p) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := OO p)) f) hf
  have hs : f.Splits := hq ▸ (splits_of_monic_OO hmon).map _
  exact hs.exists_eval_eq_zero (degree_pos_of_irreducible hirr).ne'

theorem charP_kb : CharP (kb p) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 GlobalTheory.ZH.natCast_residueField_OO

theorem exists_pow_eq_one_kb (x : kb p) (hx : x ≠ 0) : ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1 := by
  haveI := charP_kb (p := p)
  letI := ZMod.algebra (kb p) p
  have h : (algebraMap (ZMod p) (kb p)).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom (ZMod p)) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact GlobalTheory.ZH.isIntegral_int_residueField_OO
  have h' : IsIntegral (ZMod p) x := h x
  let K := IntermediateField.adjoin (ZMod p) {x}
  haveI : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional h'
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h0 => hx (congrArg Subtype.val h0)
  obtain ⟨n, hn, e⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  exact ⟨n, hn, by simpa [y] using congrArg (fun u : Kˣ => ((u : K) : kb p)) e⟩

theorem algEquiv_mem_OO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p} (hx : x ∈ OO p) :
    σ x ∈ OO p := by
  rw [GlobalTheory.ZH.mem_OO_iff, ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one] at hx ⊢
  exact hx.map (σ.toAlgHom.restrictScalars ℤ_[p])

noncomputable def restrictOO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : OO p ≃+* OO p where
  toFun x := ⟨σ x, algEquiv_mem_OO σ x.2⟩
  invFun x := ⟨σ.symm x, algEquiv_mem_OO σ.symm x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
  map_add' x y := Subtype.ext (map_add σ (x : PadicAlgCl p) y)

theorem exists_int_map_eq_kb (q : ℤ_[p][X]) : ∃ g : ℤ[X], g.map (Int.castRingHom (kb p)) =
    q.map ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro n
  rw [coeff_map]
  have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) hc
  rw [map_sub, map_mul, map_natCast, map_natCast, GlobalTheory.ZH.natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
  exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩

theorem exists_residue_restrictOO_eq (a : OO p) (b' : kb p)
    (h : ∀ g : ℤ[X], aeval (residue (OO p) a) g = 0 → aeval b' g = 0) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, residue (OO p) (restrictOO σ a) = b' := by
  have ha : IsIntegral ℤ_[p] (a : PadicAlgCl p) :=
    (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((GlobalTheory.ZH.mem_OO_iff _).1 a.2)
  set f := minpoly ℤ_[p] (a : PadicAlgCl p) with hf
  have key : ∀ c : OO p, (((f.map (GlobalTheory.ZH.padicIntToOO p)).eval c : OO p) : PadicAlgCl p) =
      aeval (c : PadicAlgCl p) f := fun c => by
    rw [Polynomial.eval_map]
    exact hom_eval₂ f (GlobalTheory.ZH.padicIntToOO p) (OO p).subtype c
  obtain ⟨g, hg⟩ := exists_int_map_eq_kb f
  have e : ∀ b : kb p, aeval b g = (f.map (GlobalTheory.ZH.padicIntToOO p)).eval₂ (residue (OO p)) b := fun b => by
    rw [eval₂_map, ← Polynomial.eval_map, ← hg, Polynomial.eval_map]
    rfl
  have h1 : aeval (residue (OO p) a) g = 0 := by
    have : (f.map (GlobalTheory.ZH.padicIntToOO p)).eval a = 0 := Subtype.ext ((key a).trans (minpoly.aeval _ _))
    rw [e, eval₂_hom, this, map_zero]
  obtain ⟨a', ha', rfl⟩ := exists_root_residue_OO ((minpoly.monic ha).map (GlobalTheory.ZH.padicIntToOO p))
    ((e b').symm.trans (h g h1))
  have h2 : aeval (a' : PadicAlgCl p) (minpoly ℚ_[p] (a : PadicAlgCl p)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] ha, aeval_map_algebraMap, ← hf, ← key, ha']
    rfl
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) h2
  exact ⟨σ, congrArg _ (Subtype.ext hσ)⟩

theorem exists_ringEquiv_residue_eq (F : Type) [Field F] [Finite F] (r r' : F →+* kb p) :
    ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), residue (OO p) a = r x → residue (OO p) (σ a) = r' x := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  obtain ⟨a₀, ha₀⟩ := residue_surjective (r u)
  obtain ⟨σ, hσ⟩ := exists_residue_restrictOO_eq a₀ (r' u) fun g hg => by
    rw [ha₀] at hg
    have h1 := aeval_algHom_apply r.toIntAlgHom (u : F) g
    have h2 := aeval_algHom_apply r'.toIntAlgHom (u : F) g
    have h3 : aeval (u : F) g = 0 := r.injective ((h1.symm.trans hg).trans (map_zero r).symm)
    exact h2.trans (by rw [h3, map_zero])
  refine ⟨restrictOO σ, fun x a ha => ?_⟩
  let τ := ResidueField.mapEquiv (restrictOO σ)
  have hτ : ∀ c : OO p, τ (residue (OO p) c) = residue (OO p) (restrictOO σ c) := fun c => rfl
  rw [← hτ, ha]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨n, hn⟩ := hu (Units.mk0 x hx)
  have hx' : x = (u : F) ^ n := by simpa using (congrArg Units.val hn).symm
  rw [hx', map_pow, map_pow, map_pow, ← ha₀, hτ, hσ]

theorem kb_isAlgClosed_and_conj : ∀ (p : ℕ) [Fact p.Prime], IsAlgClosed (kb p) ∧ (∀ x : kb p, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) ∧ ∀ (F : Type) [Field F] [Finite F] (r r' : F →+* kb p), ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), IsLocalRing.residue (OO p) a = r x → IsLocalRing.residue (OO p) (σ a) = r' x :=
  fun _ _ => ⟨isAlgClosed_kb, exists_pow_eq_one_kb, exists_ringEquiv_residue_eq⟩

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_inverse_extension_properClosure : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a := by
  first | exact @GlobalTheory.exists_inv_extension | exact GlobalTheory.exists_inv_extension | (intros; apply GlobalTheory.exists_inv_extension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_torusStableGoodOpen_of_weightUnits : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ χ : X, ∃ (U : G.left.Opens) (u : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit u ∧ Wt i U u χ) → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) := by
  first | exact @GlobalTheory.SS.exists_goodOpen_of_weight_units | exact GlobalTheory.SS.exists_goodOpen_of_weight_units | (intros; apply GlobalTheory.SS.exists_goodOpen_of_weight_units <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.jacobian_order_monotone_semistableModel : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [IsIntegral A.left] (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ (M N : Model R A) (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D π n → (∃ y ∈ M.sp, DefAt M N (𝟙 A) y) → m ≤ n ∧ (m = n → GenIso M N (𝟙 A)) := by
  first | exact @GlobalTheory.SS.OrdMono.ord_mono | exact GlobalTheory.SS.OrdMono.ord_mono | (intros; apply GlobalTheory.SS.OrdMono.ord_mono <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGrpPullback_of_dominant {W S Z : Scheme.{0}} (j : W ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {H : Over S} [GrpObj H] [Flat H.hom] {G : Over Z} [GrpObj G]
    [IsSeparated G.hom] {y : S ⟶ Z} {f : H.left ⟶ G.left} (hf : IsPullback f H.hom G.hom y)
    (h : IsGrpPullback ((Over.pullback j).obj H) G (j ≫ y) (pullback.fst H.hom j ≫ f)) :
    IsGrpPullback H G y f := by
  let e : H ≅ (Over.pullback y).obj G :=
    Over.isoMk hf.isoPullback hf.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom y = f := hf.isoPullback_hom_fst
  have hs : IsSeparated ((Over.pullback y).obj G).hom := by
    change IsSeparated (pullback.snd G.hom y)
    infer_instance
  have h₁ : IsGrpPullback ((Over.pullback j).obj H) ((Over.pullback y).obj G) j
      (pullback.fst H.hom j ≫ e.hom.left) :=
    (isGrpPullback_pullback G y).cancel (h.congr rfl (by rw [Category.assoc, he]))
      (by rw [Category.assoc, Over.w]; exact pullback.condition)
  have h₂ : IsMonHom e.hom :=
    ExtUnique.isMonHom_of_isGrpPullback (isGrpPullback_pullback H j) h₁ (𝟙 _) e.hom
      (by rw [Over.id_left, Category.id_comp])
  exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G y)).congr (Category.id_comp _) he

theorem Core.nonempty_law : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  rintro C hsm hcart ⟨m, hm⟩ ⟨i, hi⟩
  have := C.proper
  have hsep : IsSeparated C.GG.hom := by
    change IsSeparated (C.G.ι ≫ C.P.hom)
    infer_instance
  have hsmooth : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have hne : Nonempty C.U.toScheme := C.ne.to_subtype
  have hpb : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
    have w : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by
      rw [← C.cart.w, Category.assoc]; rfl
    refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by rw [Category.assoc]; exact s.condition))
      (fun s => ?_) (fun s => C.cart.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
    · rw [← cancel_mono C.G.ι, Category.assoc]
      exact C.cart.lift_fst _ _ _
    · apply C.cart.hom_ext
      · rw [C.cart.lift_fst, ← h₁, Category.assoc]
      · rw [C.cart.lift_snd, h₂]
  let e : 𝟙_ (Over C.Z) ⟶ C.GG := Over.homMk C.e C.e_sec
  obtain ⟨grp, -, hη, -, comm, pull⟩ :=
    grpObj_of_dense_open C.Z C.U.toScheme C.U.ι C.GG C.A C.a hpb m i e hm hi C.e_zero
  refine ⟨{ smooth := hsm, zero := congrArg (fun z => z.left) hη, pull := pull, test := fun p _ y τ => ?_ }⟩
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing τ.V (FractionRing τ.V)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  exact isGrpPullback_of_dominant (Out.jK τ.V) (hcart p y τ) ((τ.φ_cart.comp pull).congr τ.yK_fac τ.φ_f)

end GlobalTheory.ZJ
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a := by
  first | exact @GlobalTheory.ZJ.Core.exists_add_extension | exact GlobalTheory.ZJ.Core.exists_add_extension | (intros; apply GlobalTheory.ZJ.Core.exists_add_extension <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arcDatumMatch_length_symm_preimages : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) := by
  first | exact @GlobalTheory.LN.be_symm_eq_of_match | exact GlobalTheory.LN.be_symm_eq_of_match | (intros; apply GlobalTheory.LN.be_symm_eq_of_match <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.mem_supI_iff_and_HH_eq_ker :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) := by
  intro o Ω _ _ _ _ S M U₀ hO z p _ y y₀ τ hC hA
  have hw : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
    RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))
  have hξ : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hC.2 ⟨_, rfl⟩
  have hsp := RatModel.specializes_of_range_eq hw
  have hthO : ∀ j, S.th j ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j => RatModel.ringOn_le_O hξ (hO.le (S.th_mem j))
  have hinvO : ∀ j, S.th j ≠ 0 →
      (S.th j)⁻¹ ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j hj => RatModel.ringOn_le_O hξ (hO.th_unit j hj)
  have hmul : ∀ i j, S.th i ≠ 0 → M.val (gPt p ≫ y) (S.th j) =
      M.val (gPt p ≫ y) (S.th j / S.th i) * M.val (gPt p ≫ y) (S.th i) := by
    intro i j hi
    have hq : S.th j / S.th i ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
      rw [div_eq_mul_inv]; exact mul_mem (hthO j) (hinvO i hi)
    rw [← RatModel.val_mul hsp hq (hthO i), div_mul_cancel₀ _ hi]
  have hval : ∀ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = ‖M.val (gPt p ≫ y) (S.th x)‖ := fun x => by rw [hA]
  have hmax : IsGreatest (Set.range fun x => ‖M.val (gPt p ≫ y) (S.th x)‖) τ.δ := by
    simpa only [hval] using τ.δ_max
  have fwd : ∀ x, M.Div S.th x z → ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x hx
    apply le_antisymm (hmax.2 ⟨x, rfl⟩)
    obtain ⟨j, hj⟩ := hmax.1
    rw [← hj]
    dsimp only
    rw [hmul x j hx.1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.Cen.norm_val_le_one hC (hx.2 j))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    refine ⟨fun h => fwd x h, fun hx => ?_⟩
    obtain ⟨i, hi⟩ := hO.div z
    have h1 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ = 1 := by
      rw [hmul i x hi.1, norm_mul, fwd i hi] at hx
      have h2 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ * τ.δ = 1 * τ.δ := by rw [_root_.one_mul]; exact hx
      exact (mul_left_inj' τ.δ_pos.ne').mp h2
    show M.Div S.th x z
    exact (RatModel.Div.div_iff_isUnit hi x).mpr ((RatModel.norm_val_eq_one_iff hC.1 (hi.2 x)).mp h1)
  refine ⟨key, ?_⟩
  rw [← τ.supp]
  show AddSubgroup.closure (S.supI M z) = _
  congr 1
  ext x
  rw [key x, Set.mem_ofPred_eq, hval]

end GlobalTheory.ZH
end
