module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle017
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle018
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle024
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle016
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle020
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle025
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle015
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.Bundle028
import Development.EtaleCohomology.EtaleSheaves.Bundle055
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_middle_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₃ → Acy Q S.X₂ := by
  intro Q S hS h1 h3 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).1
  haveI := h1 P hP n hn
  haveI := h3 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₂ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_right_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₂ → Acy Q S.X₃ := by
  intro Q S hS h1 h2 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).2.1
  haveI := h1 P hP (n + 1) (by omega)
  haveI := h2 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₃ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers :
    ∀ (X : Scheme.{0}) [IsAffine X] (q : ℕ) [NeZero q] (ζ : Γ(X, ⊤)), GoodRoot q ζ →
      (∀ g : LocallyConstant X (ZMod q), ∃ w : Γ(X, ⊤), w ^ q = 1 ∧ ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ w : Γ(X, ⊤), w ^ q = 1 → ∃ g : LocallyConstant X (ZMod q), ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ (a b : ZMod q) (x : X), x ∉ X.basicOpen (ζ ^ a.val - ζ ^ b.val) → a = b) ∧
      ∀ x : X, ∃ P : Ideal Γ(X, ⊤), ∀ f, f ∈ P ↔ x ∉ X.basicOpen f := by
  intro X _ q _ ζ hζ
  have hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal := by
    intro x f
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact not_not
  let h := X.isoSpec.hom.homeomorph
  obtain ⟨h1, h2, h3⟩ := UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, hwq, hw⟩ := h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)
    refine ⟨w, hwq, fun x => ?_⟩
    rw [hb]
    have hx := hw (h x)
    change w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx
    rw [h.symm_apply_apply] at hx
    exact hx
  · intro w hw
    obtain ⟨g, hg⟩ := h2 w hw
    refine ⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩
    rw [hb]
    exact hg (h x)
  · intro a b x hx
    rw [hb] at hx
    exact h3 a b _ hx
  · intro x
    exact ⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_tensor_lift {k L K M : Type} [Field k] [Field L] [Field K] [CommRing M] [Algebra k L] [Algebra k K]
    (f : L →+* M) (g : K →+* M) (h : ∀ r : k, f (algebraMap k L r) = g (algebraMap k K r)) :
    ∃ θ : L ⊗[k] K →+* M, ∀ l a, θ (l ⊗ₜ[k] a) = f l * g a := by
  letI : Algebra k M := (g.comp (algebraMap k K)).toAlgebra
  let f' : L →ₐ[k] M := { f with commutes' := fun r => h r }
  let g' : K →ₐ[k] M := { g with commutes' := fun r => rfl }
  exact ⟨(Algebra.TensorProduct.productMap f' g').toRingHom, fun l a => by simp [f', g']⟩

private theorem core (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L)
    (hpb : IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [Algebra k C.functionField]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    {n : ℕ} (U : Fin n → C.Opens) (hUa : ∀ i, IsAffineOpen (U i)) [hne : ∀ i, Nonempty (U i)]
    (hUc : ∀ y : C, ∃ i, y ∈ U i) (hn : 0 < n)
    (B : Fin n → Subalgebra k C.functionField)
    (hB : ∀ i, (B i : Set C.functionField) = Set.range (C.germToFunctionField (U i)))
    (hfr : ∀ i, IsFractionRing (B i) C.functionField) :
    ∃ θ : L ⊗[k] C.functionField →+* X.functionField,
      Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c u x hpb
  obtain ⟨φ, hφgen, hφgerm⟩ := UpperTheory.exists_functionField_hom_germ_of_surjective u hsurj
  obtain ⟨f, hfk, hfx⟩ := UpperTheory.baseChange_functionField_hom_genericPoint_comp k L c u x hpb hK φ hφgen
  obtain ⟨θ, hθ⟩ := exists_tensor_lift f φ hfk
  have hne' : ∀ i, Nonempty (u ⁻¹ᵁ U i) := by
    intro i
    obtain ⟨⟨z, hz⟩⟩ := hne i
    obtain ⟨y, rfl⟩ := hsurj.surj z
    exact ⟨⟨y, hz⟩⟩
  have chart : ∀ i, IsAffineOpen (u ⁻¹ᵁ U i) ∧ ∃ e : L ⊗[k] B i ≃+* Γ(X, u ⁻¹ᵁ U i),
      ∀ s, θ (inc L (B i) s) = X.germToFunctionField (u ⁻¹ᵁ U i) (e s) := by
    intro i
    haveI := hne' i
    obtain ⟨hV, e, he1, he2⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c u x hpb hK (U i) (hUa i) (B i) (hB i)
    refine ⟨hV, e, fun s => ?_⟩
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul l b =>
      obtain ⟨a, ha⟩ : (b : C.functionField) ∈ Set.range (C.germToFunctionField (U i)) := by
        rw [← hB i]
        exact b.2
      have hsplit : l ⊗ₜ[k] b = (l ⊗ₜ[k] (1 : B i)) * ((1 : L) ⊗ₜ[k] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [show inc L (B i) (l ⊗ₜ[k] b) = l ⊗ₜ[k] (b : C.functionField) from rfl, hθ, hsplit,
        map_mul, map_mul, he1 a b ha.symm, he2 l, hfx, ← hφgerm (U i) a, ha]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hcomp : θ.comp Algebra.TensorProduct.includeRight.toRingHom = φ := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply, hθ]
  have hinj : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨hV0, e0, he0⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    obtain ⟨s, β, hβ, hs⟩ := UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator k L C.functionField (B ⟨0, hn⟩) (hfr _) t
    have h1 : θ (inc L (B ⟨0, hn⟩) s) = 0 := by rw [← hs, map_mul, ht, zero_mul]
    rw [he0] at h1
    have h2 : e0 s = 0 :=
      X.germToFunctionField_injective _ (h1.trans (map_zero _).symm)
    have h3 : s = 0 := e0.injective (h2.trans (map_zero e0).symm)
    rw [h3, map_zero] at hs
    have hβ' : (β : C.functionField) ≠ 0 := fun h => hβ (Subtype.ext h)
    have hu : IsUnit ((1 : L) ⊗ₜ[k] (β : C.functionField)) := by
      refine ⟨⟨1 ⊗ₜ[k] (β : C.functionField), 1 ⊗ₜ[k] (β : C.functionField)⁻¹, ?_, ?_⟩, rfl⟩
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hβ']
        rfl
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hβ']
        rfl
    exact hu.mul_left_eq_zero.mp hs
  refine ⟨θ, by rw [hcomp]; exact hφgen, hinj, ?_, ?_⟩
  · intro h
    obtain ⟨hV, e, he⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    haveI := functionField_isFractionRing_of_isAffineOpen X _ hV
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) h
    refine ⟨inc L (B ⟨0, hn⟩) (e.symm p), inc L (B ⟨0, hn⟩) (e.symm q), ?_, ?_⟩
    · intro h0
      have h4 := congrArg θ h0
      rw [he, map_zero, e.apply_symm_apply] at h4
      have h5 : (q : Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) = 0 :=
        X.germToFunctionField_injective _ (h4.trans (map_zero _).symm)
      exact nonZeroDivisors.coe_ne_zero q h5
    · rw [he, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hpq
  · intro y
    obtain ⟨i, hi⟩ := hUc (u y)
    haveI := hne' i
    obtain ⟨hV, e, he⟩ := chart i
    have hy : y ∈ u ⁻¹ᵁ U i := hi
    refine ⟨i, (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap e.toRingHom, inferInstance, fun s hs => ?_⟩
    have hsP : e s ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hs
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
    haveI := hV.isLocalization_stalk ⟨y, hy⟩
    refine ⟨(IsLocalization.map_units (X.presheaf.stalk y)
      (⟨e s, hsP⟩ : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)).unit, ?_⟩
    rw [he]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hy (e s)

theorem UpperTheory.isFunctionField_and_chart_cover_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ ∃ (n : ℕ) (B : Fin n → Subalgebra k C.functionField), (∀ i, IsChart (B i)) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], ∃ (X : Scheme.{0}) (_ : IsIntegral X) (u : X ⟶ C) (x : X ⟶ Sp L) (θ : L ⊗[k] C.functionField →+* X.functionField), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧ (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) ∧ Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  intro k _ _ C _ c hcurve _ hK
  have hprop : IsProper c := hcurve.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨n, U, hUa, hUne, hn, hUc⟩ := UpperTheory.exists_finite_nonempty_affine_cover_of_integral C
  haveI : ∀ i, Nonempty (U i) := hUne
  have hex : ∀ i, ∃ B : Subalgebra k C.functionField,
      (B : Set C.functionField) = Set.range (C.germToFunctionField (U i)) :=
    fun i => UpperTheory.exists_subalgebra_eq_range_germToFunctionField k c hK (U i)
  choose B hB using hex
  have hchart : ∀ i, IsChart (B i) :=
    fun i => UpperTheory.isChart_affine_sections_of_isCurve k c hcurve hK (U i) (hUa i) (B i) (hB i)
  refine ⟨UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing k C.functionField (B ⟨0, hn⟩) (hchart _).2.1 (hchart _).1
    (hchart _).2.2.1 (hchart _).2.2.2.1, n, B, hchart, ?_⟩
  intro L _ _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hpb : IsPullback (pullback.fst c g) (pullback.snd c g) c g := IsPullback.of_hasPullback c g
  have hcurve' := UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hcurve
  haveI hXint : IsIntegral (pullback c g) := hcurve'.1
  have hstalk := (UpperTheory.isDedekindDomain_affine_sections_of_isCurve L (pullback.snd c g) hcurve').2
  obtain ⟨θ, h1, h2, h3, h4⟩ := core k L c (pullback.fst c g) (pullback.snd c g) hpb hK U hUa hUc hn
    B hB (fun i => (hchart i).2.2.2.1)
  exact ⟨pullback c g, hXint, pullback.fst c g, pullback.snd c g, θ, hpb, hstalk, h1, h2, h3, h4⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

theorem UpperTheory.exists_cocycle_product_eq_pull_add_cup :
    ∀ (R : Type) [CommRing R] (W X : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I)
        (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {m n : ℤ} (h : m + 1 = n)
        (α₁ : Cocycle ((chains R).obj (sch.obj X)) I n) (α₂ : Cocycle ((chains R).obj (sch.obj X)) Q m),
        ∃ β : Cocycle ((chains R).obj (sch.obj (W ⨯ X))) I n,
          CohomologyClass.mk β =
              cpull ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X))) I n (CohomologyClass.mk α₁) +
                μ.cup (sch.obj (W ⨯ X)) h
                  (cpull ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X))) Q m (CohomologyClass.mk α₂))
                  (cpull ((chains R).map (sch.map (prod.fst : W ⨯ X ⟶ W))) P 1 (CohomologyClass.mk κ)) ∧
            sg β = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₁) +
              μ.mul (W ⨯ X) m 1 n h (Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₂))
                (Sec.res (prod.fst : W ⨯ X ⟶ W) (sg κ)) := by
  intro R _ W X I Q P μ κ m n h α₁ α₂
  let A := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X)))) α₂ (zero_add m)
  let B := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.fst : W ⨯ X ⟶ W)))) κ (zero_add 1)
  let C := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X)))) α₁ (zero_add n)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  refine ⟨C + γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_add, ← hc]
    rfl
  · have hadd : sg (C + γ) = sg C + sg γ :=
      ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj (W ⨯ X)) (I := I) (n := n)).1 C.1 γ.1 0 n (by simp) (W ⨯ X) (𝟙 _)).1
    have hC : sg C = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₁) := sg_pull _ α₁
    have hA : sg A = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₂) := sg_pull _ α₂
    have hB : sg B = Sec.res (prod.fst : W ⨯ X ⟶ W) (sg κ) := sg_pull _ κ
    have key : ∀ (d e : ℤ) (hd : -((0 : ℕ) : ℤ) + m = d) (he : -((0 : ℕ) : ℤ) + 1 = e) (hw : d + e = n),
        μ.mul (W ⨯ X) d e n hw (ev A.1 0 d hd (W ⨯ X) (𝟙 _)) (ev B.1 0 e he (W ⨯ X) (𝟙 _)) =
          μ.mul (W ⨯ X) m 1 n h (sg A) (sg B) := by
      intro d e hd he hw
      obtain rfl : m = d := by simpa using hd
      obtain rfl : (1 : ℤ) = e := by simpa using he
      rfl
    have hg : sg γ = μ.mul (W ⨯ X) m 1 n h (sg A) (sg B) := by
      have h0 := hγ 0 n (by simp) (W ⨯ X) (𝟙 _)
      rw [Fin.sum_univ_one] at h0
      refine h0.trans ?_
      have e : ((1 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow = 1 := by simp
      rw [e, one_smul]
      exact key _ _ rfl rfl _
    rw [hadd, hC, hg, hA, hB]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem sub_self_all {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e]
  simp

private theorem aw_conc {Q P I : Cx R} (μ : Pair Q P I) {X : Spc} {m n : ℤ} (h : m + 1 = n)
    (A : Cochain ((chains R).obj X) Q m) (B : Cochain ((chains R).obj X) P 1)
    (γ : Cochain ((chains R).obj X) I n) (hγ : μ.IsAW h A B γ)
    (hB : ∀ (p : ℕ) s hs U x, ev (R := R) B (p + 1) s hs U x = 0)
    (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + n = w) (U : Scheme.{0}) (x : Sx X N U) :
    ev (R := R) γ N w hw U x = (N : ℤ).negOnePow • μ.mul U (w + -1) 1 w (by omega) (ev (R := R) A N (w + -1) (by omega) U x)
      (ev (R := R) B 0 1 (by simp) U (x.sub N 0 (by omega))) := by
  have term : ∀ (r l : ℕ) (hrl : r + l = N) (t u : ℤ) (ht : -(r : ℤ) + m = t) (hu : -(l : ℤ) + 1 = u) (hw' : t + u = w),
      μ.mul U t u w hw' (ev (R := R) A r t ht U (x.sub 0 r (by omega))) (ev (R := R) B l u hu U (x.sub r l (by omega))) =
        if l = 0 then μ.mul U (w + -1) 1 w (by omega) (ev (R := R) A N (w + -1) (by omega) U x)
          (ev (R := R) B 0 1 (by simp) U (x.sub N 0 (by omega))) else 0 := by
    intro r l hrl t u ht hu hw'
    rcases l with _ | l
    · obtain rfl : r = N := by omega
      obtain rfl : u = 1 := by simpa using hu.symm
      obtain rfl : t = w + -1 := by omega
      simp only [if_true]
      rw [sub_self_all]
    · rw [hB]
      simp
  rw [hγ N w hw U x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · rw [term _ _ (by simp) _ _ rfl rfl]
    simp
  · intro i _
    rw [term _ _ (by simp <;> omega) _ _ rfl rfl, if_neg (by simp <;> omega)]
    simp

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem ev_rightShift {E : Spc} {Q : Cx R} {m n : ℤ} (h : m + 1 = n)
    (α : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    (ev (R := R) (α.rightShift (-1) n (by omega)).1 p s hs U x : Sec ((sh Q).X s) U) = (ev (R := R) α.1 p (s + -1) (by omega) U x : Sec (Q.X (s + -1)) U) := by
  have e : (α.rightShift (-1) n (by omega)).1.v (-(p : ℤ)) s hs =
      (show _ ⟶ (sh Q).X s from α.1.v (-(p : ℤ)) (s + -1) (by omega)) := by
    refine (Cochain.rightShift_v α.1 (-1) n (by omega) (-(p : ℤ)) s hs (s + -1) (by omega)).trans ?_
    simp [CochainComplex.shiftFunctorObjXIso]
  unfold ev
  rw [e]

private theorem ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (inL h α₁ α₂).1 p s hs U x =
      cc (ev (R := R) α₁.1 p s hs U x) (n.negOnePow • ev (R := R) α₂.1 p (s + -1) (by omega) U x) := by
  have b := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := LL I Q) (n := n)
  have e₁ : (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      ((n.negOnePow : ℤˣ) : ℤ) • (α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl
  rw [e₁, (b.1 _ _ p s hs U x).1, (b.1 ((α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)) 0 p s hs U x).2.2.2,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.2 _ α₁.1 p s hs U x,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := sh Q) (n := n)).2.2.2.2 _ _ p s hs U x, ev_rightShift h α₂ p s hs U x]
  unfold cc
  congr 1
  rw [Units.smul_def]
  exact (map_zsmul ((((biprod.inr : sh Q ⟶ LL I Q).f s).hom.app (op U)).hom) _ _).symm

private theorem c₁_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₁ (ev (R := R) (inL h α₁ α₂).1 p s hs U x) = ev (R := R) α₁.1 p s hs U x := by
  rw [ev_inL, c₁_cc]

private theorem c₂_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₂ (ev (R := R) (inL h α₁ α₂).1 p s hs U x) = n.negOnePow • ev (R := R) α₂.1 p (s + -1) (by omega) U x := by
  rw [ev_inL, c₂_cc]

private theorem sub_map_sch {W : Scheme.{0}} {X : Spc} (f : X ⟶ sch.obj W) {p : ℕ} {T : Scheme.{0}} (y : Sx X p T)
    (h : p + 0 ≤ p) : (show T ⟶ W from (y.sub p 0 h).map f) = (show T ⟶ W from y.map f) := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval p 0 h).op) (op T)) y

private theorem psi_read (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T : Scheme.{0}} (s : ℤ)
    (f : T ⟶ W) (a : Sec ((LL I Q).X s) T) :
    Sec.res (prod.lift f (𝟙 T)) (psi W μ z T s a) =
      c₁ a + s.negOnePow • μ.mul T (s + -1) 1 s (by omega) (c₂ a) (Sec.res f z) := by
  change Sec.res (prod.lift f (𝟙 T)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) = _
  rw [res_add, res_units, μ.nat, res_res, res_res, res_res, prod.lift_snd, prod.lift_fst, res_id, res_id]

end UpperTheory.Kun

theorem UpperTheory.exteriorCup_cocycle_exists_of_pairing :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {E : Spc} {m n : ℤ}
        (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n) (α₂ : Cocycle ((chains R).obj E) Q m)
        (β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n),
        (∀ (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
          ev (R := R) β.1 p s hs T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T))
            (psi W μ (sg κ) T s (ev (R := R) (inL h α₁ α₂).1 p s hs T (y.map prod.snd)))) →
        CohomologyClass.mk β = cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n (CohomologyClass.mk α₁) +
          μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m (CohomologyClass.mk α₂))
            (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
  intro R _ W I Q P μ κ E m n h α₁ α₂ β hβ
  have hS := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R W P 0 1 2 (by norm_num) (by norm_num)
  obtain ⟨z', hz0, hz1⟩ := hS.1 (sg κ) (hS.2 κ).1
  have hκ : CohomologyClass.mk κ = CohomologyClass.mk z' := by
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
    refine (hS.2 (κ - z')).2.2 ⟨0, ?_⟩
    have e : sg (κ - z') = 0 := by
      rw [sg_sub]
      have e' : sg z' = sg κ := by
        have := hz0 W (𝟙 W)
        rw [res_id] at this
        exact this
      rw [e', sub_self]
    exact (map_zero ((P.d 0 1).hom.app (op W)).hom).trans e.symm
  let A : Cocycle ((chains R).obj (sch.obj W ⨯ E)) Q m :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₂ (zero_add m)
  let B : Cocycle ((chains R).obj (sch.obj W ⨯ E)) P 1 :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _))) z' (zero_add 1)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  have evA : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev (R := R) A.1 p s hs T y = ev (R := R) α₂.1 p s hs T (y.map prod.snd) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := Q) (n := m)).2.2.2.1 prod.snd α₂.1 p s hs T y
  have evB : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev (R := R) B.1 p s hs T y = ev (R := R) z'.1 p s hs T (y.map prod.fst) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W) (I := P) (n := 1)).2.2.2.1 prod.fst z'.1 p s hs T y
  have hβ' : β = zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ := by
    apply Cocycle.ext
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).2.2.1 _ _ fun p s hs T y => ?_
    have e₁ : (zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ).1 =
        (Cochain.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))).comp α₁.1 (zero_add n) + γ.1 := rfl
    rw [e₁, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).1 _ _ p s hs T y).1,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.1 prod.snd α₁.1 p s hs T y,
      hβ p s hs T y, psi_read, c₁_ev_inL, c₂_ev_inL,
      aw_conc μ h A.1 B.1 γ.1 hγ (fun p s hs U x => by rw [evB]; exact hz1 p s hs U _) p s hs T y,
      evA, evB]
    congr 1
    have e₂ : ev (R := R) z'.1 0 1 (by simp) T ((y.sub p 0 (by omega)).map prod.fst) = Sec.res (show T ⟶ W from y.map prod.fst) (sg κ) := by
      rw [← sub_map_sch prod.fst y (by omega)]
      exact hz0 T _
    rw [e₂]
    have hsign : s.negOnePow * n.negOnePow = (p : ℤ).negOnePow := by
      rw [← hs, Int.negOnePow_add, Int.negOnePow_neg, mul_assoc, Int.units_mul_self, mul_one]
    have key : ∀ (ε : ℤˣ) (a : Sec (Q.X (s + -1)) T) (b : Sec (P.X 1) T),
        μ.mul T (s + -1) 1 s (by omega) (ε • a) b = ε • μ.mul T (s + -1) 1 s (by omega) a b := by
      intro ε a b
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
    rw [key, smul_smul, hsign]
  rw [hκ, hβ', CohomologyClass.mk_add, cpre_mk, cpre_mk, cpre_mk]
  exact congrArg (fun c => _ + c) hc.symm
end
