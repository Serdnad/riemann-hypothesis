module

import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec
import Development.EtaleCohomology.TateTwists.Bundle029
public import Development.EtaleCohomology.TateTwists.Bundle005
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.TateTwists.Bundle014
public import Development.EtaleCohomology.TateTwists.Bundle027
public import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle023
public import Development.EtaleCohomology.TateTwists.Bundle024
public import Development.EtaleCohomology.TateTwists.Bundle028
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.EtaleCohomology.TateTwists.Bundle012

@[expose] public section

section

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AlgPowPf

theorem root_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z : K)
    (hz : aeval z (cyclotomic q ℤ) = 0) : IsPrimitiveRoot z q := by
  have : NeZero (q : K) := ⟨hq⟩
  have h : (cyclotomic q K).IsRoot z := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    simpa [aeval_def] using hz
  exact (isRoot_cyclotomic_iff).1 h

theorem eq_pow_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (z x : K)
    (hz : IsPrimitiveRoot z q) (hx : IsPrimitiveRoot x q) : ∃ b : (ZMod q)ˣ, x = z ^ (b : ZMod q).val := by
  obtain ⟨i, hi, hzi⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hzi ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hzi]

theorem pow_ne_dom {K : Type} [CommRing K] (q : ℕ) [NeZero q] (z : K)
    (hz : IsPrimitiveRoot z q) (a b : (ZMod q)ˣ) (h : a ≠ b) :
    z ^ (a : ZMod q).val ≠ z ^ (b : ZMod q).val := by
  intro e
  apply h
  exact Units.ext (ZMod.val_injective q (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e))

theorem pow_q {A : Type} [CommRing A] (q : ℕ) (z : A) (hz : aeval z (cyclotomic q ℤ) = 0) : z ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval z) hp
  simp [hz] at this
  exact sub_eq_zero.1 this

theorem self_sq {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (x y : A)
    (hx : x ^ q = 1) (hy : y ^ q = 1) : ∃ w : A, x - y = (x - y) ^ 2 * w := by
  set d := x - y
  set u := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)
  have hdu : u * d = 0 := by
    have := geom_sum₂_mul x y q
    rw [hx, hy, sub_self] at this
    exact this
  have hyu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ (q - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q)), hy]⟩
  set c : A := (q : A) * y ^ (q - 1)
  have hc : IsUnit c := hq.mul (hyu.pow _)
  have hmem : u - c ∈ Ideal.span {d} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy : Ideal.Quotient.mk (Ideal.span {d}) x = Ideal.Quotient.mk (Ideal.span {d}) y := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl

    simp only [u, c, map_sub, map_sum, map_mul, map_pow, map_natCast, hxy]
    rw [geom_sum₂_self, sub_self]
  obtain ⟨w0, hw0⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨-(w0 * ↑cu⁻¹), ?_⟩
  have hdc : d * c = -(d ^ 2 * w0) := by
    have : c = u - w0 * d := by rw [hw0]; ring
    rw [this]; linear_combination hdu
  calc d = d * c * ↑cu⁻¹ := by rw [← hcu, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [hdc]; ring

theorem self_pow {A : Type} [CommRing A] (d w : A) (h : d = d ^ 2 * w) (k : ℕ) : d = d ^ (k + 1) * w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc d = d ^ (k + 1) * w ^ k := ih
      _ = d ^ k * d * w ^ k := by ring
      _ = d ^ k * (d ^ 2 * w) * w ^ k := by rw [← h]
      _ = _ := by ring

theorem AlgPow_of : LateralTheory.EtaleFoundations.TwSecLocPf.AlgPow := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.AlgPow_of <;> assumption

end LateralTheory.EtaleFoundations.AlgPowPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactIffPf

variable {R : Type} [CommRing R]

theorem inj_of_mono {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have : Mono φ.hom := inferInstance
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem ker_sec {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (b : Sec F U) (hb : Sec.map φ b = 0) :
    ∃ k : Sec (kernel φ) U, Sec.map (kernel.ι φ) k = b := by
  let E := sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
    (evaluation _ _).obj (op U)
  have hl : IsLimit (Fork.ofι (E.map (kernel.ι φ))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]) :
      Fork (E.map φ) 0) := isLimitOfHasKernelOfPreservesLimit E φ
  let M := LinearMap.ker (φ.hom.app (op U)).hom
  let s : ModuleCat.of (ULift.{1} R) M ⟶ E.obj F := ModuleCat.ofHom M.subtype
  have hs : s ≫ E.map φ = s ≫ 0 := by
    ext x
    simp [s, E]
  obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' hl s hs
  refine ⟨l.hom ⟨b, hb⟩, ?_⟩
  have := congrArg (fun m => m.hom (⟨b, hb⟩ : M)) hl'
  simpa [s, E] using this

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 →
    Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  apply LateralTheory.EtaleFoundations.acycIffPf.exact_iff <;> assumption

end LateralTheory.EtaleFoundations.ExactIffPf

theorem LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  intro R _ S
  exact LateralTheory.EtaleFoundations.ExactIffPf.exact_iff S
end

section

theorem LateralTheory.Fix.EtaleCochainSemilinearMapCompCompatible.intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible :=
  LateralTheory.EtaleFoundations.etale_cohomology_operation_comp_of_image_spec
    (LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_image_spec_of_hyp (by
      have h := LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses.intersectionNumber_baseChange
      unfold LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses at h
      exact h))
end

section

namespace LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
theorem etale_steenrod_acyclic_models_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of
theorem etale_steenrod_alexander_whitney_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  apply LateralTheory.EtaleFoundations.AwPf.leaf_aw_of
theorem etale_steenrod_whitney_alexander_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_wa := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of <;> first | exact etale_steenrod_alexander_whitney_compatibility_of_components
theorem etale_steenrod_power_operation_properties_of_components : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  apply LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney <;> first | exact etale_steenrod_acyclic_models_of_components | exact etale_steenrod_alexander_whitney_compatibility_of_components | exact etale_steenrod_whitney_alexander_compatibility_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := etale_steenrod_power_operation_properties_of_components
end LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (a : Sec (tw q i) U),
    Loc U fun V g => Sec.res g a = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g a = c • twGen i ζ

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange : Prop :=
  ∀ (q : ℕ) [NeZero q] (j : ℤ),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom)) ∧
    ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), Loc U fun _ g => ∃ c : ℕ, Sec.res g (twGen j ξ) = c • twGen j (ζ.map g.appTop.hom)

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf
theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp [Sec.res]

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := by
  simp [Sec.map]
end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally := by
  intro q _ i j k T μ hk φ hφ U a b
  refine loc_bind' (loc_mono' (loc_and' (hl q i U a) (hl q j U b)) fun V g hab => ?_)
  rcases hab with ⟨ha | ⟨ζ, c, ha⟩, hb | ⟨ξ, d, hb⟩⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res (F := tw q j), hb]; simp⟩
  · refine loc_mono' ((hr q j).2 V ζ ξ) fun W h ⟨e, he⟩ => ?_
    refine ⟨(c * (d * e)) • twGen k (ζ.map h.appTop.hom), ?_⟩
    rw [← res_res, ← res_res (F := tw q j), ha, hb, res_nsmul, res_nsmul, he, (hr q i).1, smul_smul,
      map_nsmul', map_nsmul', map_nsmul', map_nsmul', hφ]
    simp only [map_nsmul, LinearMap.smul_apply, smul_smul]
    ring_nf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_surjective_of_local_and_root (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally hl hr)
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_eval_degree_zero : EtaleCochainDifferentialEvaluationDegreeZero := by
  intro R _ E I n m hm α U x w w' h h'
  subst h h'
  have hz : IsZero (((chains R).obj E).X (-((0 : ℕ) : ℤ) + 1)) :=
    HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
      omega)
  have hd0 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 := hz.eq_of_tgt _ _
  unfold ev
  rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + m) rfl (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + 1)
    (by omega) rfl, hd0, zero_comp, smul_zero, add_zero, ← Category.assoc]
  rfl

theorem etale_cup_alexanderWhitney_leibniz_of_ext_and_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) :
    EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_alexander_whitney_leibniz_of_ext_degree_zero_succ h0 etale_cup_alexanderWhitney_leibniz_eval_degree_zero hs

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_succ_holds : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x
  subst hn hm
  obtain rfl : k₁ = k + 1 := by omega
  have e := LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing R μ hk α β γ γ₁ γ₂ ha h1 h2
  rw [e, ev_add', awleib_ev_smul]

end LateralTheory.EtaleFoundations
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

abbrev TensorDegreeIndex (w : ℤ) : Type := {p : ℤ × ℤ // p.1 + p.2 = w}

abbrev TensorDegreeSummand {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w : ℤ)
    (p : TensorDegreeIndex w) : Type 1 :=
  Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U

def stD {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') :
    Tens C J U w →ₗ[ULift.{1} R] Tens C J U w' :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
      ((p.1.1.negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

theorem stD_lof {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (a b : ℤ) (hab : a + b = w)
    (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    stD C J U w w' h (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w) (TensorDegreeSummand C J U w) ⟨(a, b), hab⟩ v) =
      DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a + 1, b), by omega⟩
          (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) +
        (a.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a, b + 1), by omega⟩
          (TensorProduct.map LinearMap.id ((J.d b (b + 1)).hom.app (op U)).hom v) := by
  unfold stD
  rw [DirectSum.toModule_lof]
  rfl

theorem lift_lof {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (p : TensorDegreeIndex w)
    (v : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) : τ.lift U w (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w) (TensorDegreeSummand C J U w) p v) =
      TensorProduct.lift (τ.mul U p.1.1 p.1.2 w p.2) v := by
  unfold Pair.lift
  rw [DirectSum.toModule_lof]

theorem stD_lift {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : τ.lift U w' (stD C J U w w' h y) = Sec.map (T.d w w') (τ.lift U w y) := by
  subst h
  have key : (τ.lift U (w + 1)).comp (stD C J U w (w + 1) rfl) =
      ((T.d w (w + 1)).hom.app (op U)).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [stD_lof, map_add (f := _), map_zsmul, lift_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
    have := τ.leibniz U a b w hab u v
    rw [Units.smul_def] at this
    exact this.symm
  exact LinearMap.congr_fun key y

theorem stD_res {R : Type} [CommRing R] (C J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : stD C J V w w' h (Tens.res g w y) = Tens.res g w' (stD C J U w w' h y) := by
  have key : (stD C J V w w' h).comp (Tens.res g w) = (Tens.res g w').comp (stD C J U w w' h) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    have n1 := stair_map_res (C.d a (a + 1)) g u
    have n2 := stair_map_res (J.d b (b + 1)) g v
    simp only [Sec.map, Sec.res] at n1 n2
    simp only [LinearMap.comp_apply]
    rw [Tens.res, Tens.res, DirectSum.lmap_lof, stD_lof, stD_lof, map_add (f := _), map_zsmul, DirectSum.lmap_lof, DirectSum.lmap_lof]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [n1, n2]
  exact LinearMap.congr_fun key y

theorem lift_res {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (y : Tens C J U w) : τ.lift V w (Tens.res g w y) = Sec.res g (τ.lift U w y) := by
  have key : (τ.lift V w).comp (Tens.res g w) = ((T.X w).obj.map g.op).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [Tens.res, DirectSum.lmap_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul]
    exact (τ.nat g _ _ _ p.2 u v).symm
  exact LinearMap.congr_fun key y

theorem lof_reidx {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w' a a' b : ℤ) (ha : a + 1 = a')
    (h1 : a + 1 + b = w') (h2 : a' + b = w') (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a + 1, b), h1⟩
        (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) =
      DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a', b), h2⟩
        (TensorProduct.map ((C.d a a').hom.app (op U)).hom LinearMap.id v) := by
  subst ha; rfl

theorem stD_low {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (n : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TensorDegreeIndex w, n < p.1.1 → y p = 0) :
    ∀ q : TensorDegreeIndex w', n + 1 < q.1.1 → stD C J U w w' h y q = 0 := by
  classical
  intro q hq

  rw [← DirectSum.sum_support_of y, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpn : p.1.1 ≤ n := by
    by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hpn
  rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
  · intro he; rw [he] at hq; simp only at hq; omega
  · intro he; rw [he] at hq; simp only at hq; omega

theorem stD_top {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (s : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TensorDegreeIndex w, s < p.1.1 → y p = 0) (h0 : s + (w - s) = w) (h1 : s + 1 + (w - s) = w') :
    stD C J U w w' h y ⟨(s + 1, w - s), h1⟩ =
      TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(s, w - s), h0⟩) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of y]

  rw [map_sum, DirectSum.sum_apply]
  have hz : ∀ p ∈ DFinsupp.support y, p ≠ ⟨(s, w - s), h0⟩ →
      stD C J U w w' h (DirectSum.of (TensorDegreeSummand C J U w) p (y p)) ⟨(s + 1, w - s), h1⟩ = 0 := by
    intro p hp hne
    have hps : p.1.1 < s := by
      have hle : p.1.1 ≤ s := by
        by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · exact absurd (Subtype.ext (Prod.ext h' (by have := p.2; simp only at this ⊢; omega))) hne
    obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at hps
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    · intro he; have := congrArg (fun q : TensorDegreeIndex w' => q.1.1) he; simp only at this; omega
    · intro he; have := congrArg (fun q : TensorDegreeIndex w' => q.1.1) he; simp only at this; omega
  by_cases hm : (⟨(s, w - s), h0⟩ : TensorDegreeIndex w) ∈ DFinsupp.support y
  · rw [Finset.sum_eq_single_of_mem _ hm hz]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    intro he; have := congrArg (fun q : TensorDegreeIndex w' => q.1.1) he; simp only at this; omega
  · rw [Finset.sum_eq_zero fun p hp => hz p hp (fun he => hm (he ▸ hp))]
    have : y ⟨(s, w - s), h0⟩ = 0 := by simpa [DFinsupp.mem_support_iff] using hm
    rw [this, map_zero]

theorem next_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {U : Scheme.{0}} (y : Sec (T.X w) U)
    (h : Sec.map (T.sc w).g y = 0) : Sec.map (T.d w (w + 1)) y = 0 := by
  change Sec.map (T.d w ((ComplexShape.up ℤ).next w)) y = 0 at h
  rwa [CochainComplex.next ℤ w] at h

theorem prev_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.X (w - 1)) V) :
    ∃ z' : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z' = Sec.map (T.d (w - 1) w) z := by
  change ∃ z' : Sec (T.X ((ComplexShape.up ℤ).prev w)) V, Sec.map (T.d ((ComplexShape.up ℤ).prev w) w) z' = _
  rw [CochainComplex.prev ℤ w]
  exact ⟨z, rfl⟩

theorem etale_tensor_cycle_locally_lowers_top_degree_of_row_exact : EtaleTensorCycleLocallyLowersTopDegree := by
  intro R _ C J T τ hτ hrow w s U x hx hc
  have hc' : τ.lift U (w + 1) (stD C J U w (w + 1) rfl x) = 0 := by
    rw [stD_lift]; exact next_fix T w _ hc
  refine stair_loc_bind U _ _ (hτ.2 U (w + 1) _ hc') ?_
  intro V g hV
  have hy : ∀ p : TensorDegreeIndex w, s < p.1.1 → Tens.res g w x p = 0 := by
    intro p hp; rw [Tens.res, DirectSum.lmap_apply, hx p hp, map_zero]
  have hrow0 : TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id
      (Tens.res g w x ⟨(s, w - s), by omega⟩) = 0 := by
    rw [← stD_top C J V w (w + 1) rfl s _ hy (by omega) (by omega), stD_res, hV]; rfl
  refine stair_loc_mono V _ _ (hrow s (w - s) V _ hrow0) ?_
  rintro W k ⟨e, he⟩
  have hlow : ∀ q : TensorDegreeIndex (w - 1), s - 1 < q.1.1 →
      (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex (w - 1)) (TensorDegreeSummand C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e) q = 0 := by
    intro q hq
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    intro he'; rw [he'] at hq; simp only at hq; omega
  refine ⟨Tens.res k w (Tens.res g w x) - stD C J W (w - 1) w (by omega)
      (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex (w - 1)) (TensorDegreeSummand C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e), ?_, ?_⟩
  · intro p hp
    rw [DFinsupp.sub_apply]
    rcases lt_or_eq_of_le (show s ≤ p.1.1 by omega) with hps | hps
    · rw [stD_low C J W (w - 1) w (by omega) (s - 1) _ hlow p (by omega), sub_zero,
        show Tens.res k w (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map k.op).hom
          ((J.X p.1.2).obj.map k.op).hom (Tens.res g w x p) from DirectSum.lmap_apply _ _ _, hy p hps, map_zero]
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at hps
      subst hps
      obtain rfl : b = w - s := by simp only at hab; omega
      rw [stD_lof, lof_reidx C J W w (s - 1) s (w - s) (by omega) _ (by omega), DFinsupp.add_apply, DFinsupp.smul_apply,
        DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero,
        sub_eq_zero]
      · exact he.symm
      · intro he'; have := congrArg (fun q : TensorDegreeIndex w => q.1.1) he'; simp only at this; omega
  · obtain ⟨z', hz'⟩ := prev_fix T w (τ.lift W (w - 1)
      (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex (w - 1)) (TensorDegreeSummand C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e))
    refine ⟨z', ?_⟩
    rw [map_sub, lift_res, lift_res, stair_res_res, stD_lift]
    exact congrArg (fun t => _ - t) hz'.symm

end LateralTheory.EtaleFoundations
end
end
