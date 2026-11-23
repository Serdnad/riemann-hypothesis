module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R), map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  first | exact @GlobalTheory.LawDer.map_invDer_iterate | exact GlobalTheory.LawDer.map_invDer_iterate | (intros; apply GlobalTheory.LawDer.map_invDer_iterate <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.LocalLefschetz

lemma two_le_of_add_one {x y : WithBot ℕ∞} (h : x + 1 = y) (hy : 3 ≤ y) : 2 ≤ x := by
  subst h
  induction x using WithBot.recBotCoe with
  | bot => simp at hy
  | coe n =>
    have h3 : (3 : ℕ∞) ≤ n + 1 := WithBot.coe_le_coe.mp hy
    have : (2 : ℕ∞) ≤ n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have : (3 : ℕ) ≤ m + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : 2 ≤ m)
    exact WithBot.coe_le_coe.mpr this

theorem depth_three : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  intro R _ _ hcomp hdim f hf hf2 _ hpur A _ _ _ hdep hEt
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (Ideal.zero_mem _)
  haveI : IsDomain R := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R
  have hreg : IsSMulRegular A f :=
    GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hdep) hEt f hf0
  haveI hRb : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
  have hdimb : 2 ≤ ringKrullDim (R ⧸ Ideal.span {f}) :=
    two_le_of_add_one
      (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2) hdim
  haveI : Module.Finite R (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R A))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hdepb := GlobalTheory.modDepthGE_quotient_map_span_singleton R A f hf hreg 1 hdep
  have hEtb := GlobalTheory.T.etale_quotient_of_etale_punctured' R A f hEt
  obtain ⟨A', _, _, hA'fin, ι, hι, hdep', hEt', k, hk⟩ := GlobalTheory.T.exists_finite_depth_two_hull_of_etale_punctured_spectrum _ hdimb _ hdepb hEtb
  have hfree : Module.Free (R ⧸ Ideal.span {f}) A' := hpur A' hdep' hEt'
  obtain ⟨_, _⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (R ⧸ Ideal.span {f})
  have hnf : ¬ IsField (R ⧸ Ideal.span {f}) := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [this] at hdimb
    exact absurd hdimb (by decide)
  have hEtA' : Algebra.Etale (R ⧸ Ideal.span {f}) A' := by
    refine GlobalTheory.T.etale_of_etale_at_height_one_primes _ A' hnf fun p _ hp => hEt' p ?_
    rintro rfl
    have h1 := maximalIdeal_height_eq_ringKrullDim (R := R ⧸ Ideal.span {f})
    rw [hp] at h1
    rw [← h1] at hdimb
    exact absurd hdimb (by decide)
  obtain ⟨B, _, _, hBfin, hBfree, hBet, ⟨e⟩⟩ := GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale R hcomp f hf A'
  let φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B) :=
    { toRingHom := e.symm.toRingHom.comp (ι.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := fun r => by
        have h1 : (Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) (algebraMap R A r)) =
            algebraMap (R ⧸ Ideal.span {f}) _ (algebraMap R (R ⧸ Ideal.span {f}) r) := by
          rw [← IsScalarTower.algebraMap_apply]; rfl
        show e.symm (ι (Ideal.Quotient.mk _ (algebraMap R A r))) = _
        rw [h1, ι.commutes, e.symm.commutes, ← IsScalarTower.algebraMap_apply] }
  have hφ : ∀ a, φ a = e.symm (ι (Ideal.Quotient.mk _ a)) := fun a => rfl
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_lift_algHom_of_etale_punctured R hcomp hdim f hf hf0 A hEt B φ
  have hψa : ∀ a, Ideal.Quotient.mk _ (ψ a) = φ a := fun a => by
    rw [← hψ]; rfl
  have hBreg : IsSMulRegular B f := fun x y h => smul_right_injective B hf0 h
  have hsat : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
      a ∈ (Ideal.span {f}).map (algebraMap R A) := by
    intro a ha
    have h1 : φ a = 0 := by
      rw [← hψa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hφ] at h1
    have h2 : ι (Ideal.Quotient.mk _ a) = 0 := by
      simpa using h1
    have h3 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) a = 0 :=
      hι (by rw [h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨hinj, hfsat⟩ := GlobalTheory.T.injective_and_saturated_of_injective_mod_regular' R A B f hf hBreg ψ hsat
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) ≤ maximalIdeal (R ⧸ Ideal.span {f}) := by
    rw [Ideal.map_le_iff_le_comap]
    have : (maximalIdeal (R ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      haveI := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ Ideal.span {f}))
      exact IsLocalRing.eq_maximalIdeal this
    rw [this]
  have hspan : ∀ z : B, z ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : B, z = f • c := by
    intro z hz
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hz
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, by rw [Algebra.smul_def, ← hc, mul_comm]⟩
  have hcok : ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c := by
    refine ⟨k, fun x hx b => ?_⟩
    have hx' : Ideal.Quotient.mk (Ideal.span {f}) x ∈ maximalIdeal (R ⧸ Ideal.span {f}) ^ k := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) hx
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap k this
    obtain ⟨abar, habar⟩ := hk _ hx' (e (Ideal.Quotient.mk _ b))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    refine ⟨a, ?_⟩
    have h1 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R B)) (x • b - ψ a) = 0 := by
      rw [map_sub, hψa, hφ]
      change Ideal.Quotient.mk _ (x • b) - e.symm (ι (Ideal.Quotient.mk _ a)) = 0
      have habar' : ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (Ideal.span {f}) x • e (Ideal.Quotient.mk _ b) := habar
      have h2 : ∀ z, e.symm (Ideal.Quotient.mk (Ideal.span {f}) x • e z) =
          Ideal.Quotient.mk (Ideal.span {f}) x • z := fun z => by
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, AlgEquiv.symm_apply_apply, ← Algebra.smul_def]
      rw [habar', h2]
      change Ideal.Quotient.mkₐ R _ (x • b) - _ = 0
      rw [map_smul, ← algebraMap_smul (R ⧸ Ideal.span {f}) x, Ideal.Quotient.algebraMap_eq]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc⟩ := hspan _ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    exact ⟨c, by rw [← hc]; abel⟩
  have hdim1 : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) := le_trans (by decide) hdimb
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element R f hdim1 A B ψ hcok
  have hEtB : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B) :=
    fun p _ _ => inferInstance
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum R A B hEt hEtB ψ hinj ⟨s, hs0, hs⟩
  have hdesc : ∀ (n : ℕ) (b : B), f ^ n • b ∈ ψ.range → b ∈ ψ.range := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      apply ih
      apply hfsat
      rwa [← mul_smul, ← pow_succ']
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨a, ha⟩ := hdesc k2 b (hk2 _ (Ideal.pow_mem_pow hf k2) b)
    exact ⟨a, ha⟩
  let eqv : A ≃ₐ[R] B := AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  haveI : Module.Free R A := Module.Free.of_equiv eqv.symm.toLinearEquiv
  haveI : Nontrivial A := by
    obtain ⟨rs, -, -, hr⟩ := hdep
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hr.top_ne_smul (Subsingleton.elim _ _)
  exact GlobalTheory.T.modDepthGE_three_of_free_regularLocal R hdim A

end GlobalTheory.LocalLefschetz
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw.Inj

variable (q : ℕ) [NeZero q]

theorem comp_appTop_apply' {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem eq_zero_of_pow_eq_one {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (C : ZMod q)
    (h : ζ.1 ^ C.val = 1) : C = 0 := by
  by_contra hC
  have hne : ¬ C.val ≡ 0 [MOD q] := by
    intro hm
    apply hC
    rw [← ZMod.val_eq_zero]
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt C), Nat.zero_mod] at hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 ζ C.val 0 hne
  rw [h, pow_zero, sub_self] at hu
  exact not_isUnit_zero hu

theorem mk_single_eq {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (c : ULift.{1} (ZMod q)) :
    (twRel q 1 A).mkQ (Finsupp.single ξ c) = (twRel q 1 A).mkQ (Finsupp.single ζ (c * ULift.up (a : ZMod q))) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 A :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have := (twRel q 1 A).smul_mem c hmem
  convert this using 1
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, zpow_one]

theorem mk_eq_single {A : Type} [CommRing A] (ζ : Prim q A) (f : Prim q A →₀ ULift.{1} (ZMod q))
    (h : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ C : ULift.{1} (ZMod q), (twRel q 1 A).mkQ f = (twRel q 1 A).mkQ (Finsupp.single ζ C) := by
  classical
  choose! a ha using h
  refine ⟨∑ ξ ∈ f.support, f ξ * ULift.up (a ξ : ZMod q), ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]

  rw [Finsupp.sum, map_sum, Finsupp.single_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun ξ hξ => mk_single_eq q ζ ξ (a ξ) (ha ξ hξ) (f ξ)

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj
variable (q : ℕ) [NeZero q]

theorem local_zero (V : Scheme.{0}) [IsAffine V] (m : (twF q 1).obj Γ(V, ⊤))
    (hm : ((eta q).app Γ(V, ⊤)).hom m = 0) (v : V) :
    ∃ (W : Scheme.{0}) (k : W ⟶ V), IsAffine W ∧ Etale k ∧ v ∈ Set.range k ∧ ((twF q 1).map k.appTop).hom m = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (twRel q 1 Γ(V, ⊤)) m
  by_cases hf : f = 0
  · refine ⟨V, 𝟙 V, inferInstance, inferInstance, ⟨v, rfl⟩, ?_⟩
    have h0 : ((twRel q 1 Γ(V, ⊤)).mkQ f : (twF q 1).obj Γ(V, ⊤)) = 0 := by rw [hf, map_zero]
    rw [h0]
    exact map_zero _
  obtain ⟨ζ₀, hζ₀⟩ := Finsupp.support_nonempty_iff.2 hf
  let P : f.support → ∀ W : Scheme.{0}, (W ⟶ V) → Prop := fun ξ W k =>
    ∃ a : (ZMod q)ˣ, k.appTop.hom ξ.1.1 = k.appTop.hom ζ₀.1 ^ (a : ZMod q).val
  have hL : Loc V fun W k => ∀ ξ, P ξ W k :=
    (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 V f.support P fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 ζ₀ ξ.1
  have hst : ∀ (W W' : Scheme.{0}) (g : W ⟶ V) (k : W' ⟶ W), (∀ ξ, P ξ W g) → ∀ ξ, P ξ W' (k ≫ g) := by
    intro W W' g k h ξ
    obtain ⟨a, ha⟩ := h ξ
    refine ⟨a, ?_⟩
    rw [comp_appTop_apply', comp_appTop_apply', ha, map_pow]
  obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hP⟩ := ((GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V _ hst).1 hL) v
  refine ⟨W, k, hWa, hk, ⟨w, hw⟩, ?_⟩
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨w, trivial⟩⟩
  haveI : Nontrivial Γ(W, ⊤) := Scheme.component_nontrivial W ⊤
  let φ := k.appTop.hom
  let ζ₁ : Prim q Γ(W, ⊤) := Prim.map φ ζ₀
  have hmap : ((twF q 1).map k.appTop).hom ((twRel q 1 Γ(V, ⊤)).mkQ f) =
      (twRel q 1 Γ(W, ⊤)).mkQ (Finsupp.mapDomain (Prim.map φ) f) := rfl
  obtain ⟨C, hC⟩ := mk_eq_single q ζ₁ (Finsupp.mapDomain (Prim.map φ) f) (by
    intro ξ' hξ'
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hξ')
    obtain ⟨a, ha⟩ := hP ⟨ξ, hξ⟩
    exact ⟨a, ha⟩)
  rw [hmap, hC]
  have he : ((eta q).app Γ(W, ⊤)).hom ((twF q 1).map k.appTop |>.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0 := by
    have := congrArg (fun g => g.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) ((eta q).naturality k.appTop)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
    refine this.trans ?_
    change ((muF q).map k.appTop).hom (((eta q).app Γ(V, ⊤)).hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0
    rw [hm, map_zero]
  rw [hmap, hC, Submodule.mkQ_apply, eta_mk] at he
  have h1 : ζ₁.1 ^ C.down.val = 1 := by
    have := congrArg (fun y : ULift.{1} (Additive (rootsOfUnity q Γ(W, ⊤))) =>
      (((Additive.toMul y.down : rootsOfUnity q Γ(W, ⊤)) : Γ(W, ⊤)ˣ) : Γ(W, ⊤))) he
    simp only [smul_eq, toMul_nsmul, toMul_ofMul] at this
    rw [root_pow_coe] at this
    exact this.trans rfl
  have hC0 : C = 0 := ULift.ext (eq_zero_of_pow_eq_one q ζ₁ C.down h1)
  rw [hC0, Finsupp.single_zero, map_zero]
  rfl

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj

theorem res_comp {q : ℕ} {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec (tw q 1) U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change ((tw q 1).obj.map (k ≫ g).op).hom x = ((tw q 1).obj.map k.op).hom (((tw q 1).obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem etaS_injective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Injective ((etaS q).hom.app (op U)).hom := by
  intro q _ U _
  refine (injective_iff_map_eq_zero ((etaS q).hom.app (op U)).hom).2 fun x hx => ?_
  have hst : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), Sec.res g x = 0 → Sec.res (k ≫ g) x = 0 := by
    intro V W g k h
    rw [res_comp, h]
    exact map_zero _
  have hloc : Loc U fun W g => Sec.res g x = 0 := by
    rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hst]
    intro u
    obtain ⟨V, j, v, m, hVa, hj, hjv, hm⟩ := (GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) U).1 x u
    have hem : ((eta q).app Γ(V, ⊤)).hom m = 0 := by
      have hm' : (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) = Sec.res (F := tw q 1) j x := hm
      rw [← etaS_sec, hm', etaS_res]
      change Sec.res j (((etaS q).hom.app (op U)).hom x) = 0
      rw [hx]
      exact map_zero _
    obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hmW⟩ := local_zero q V m hem v
    refine ⟨W, k ≫ j, hWa, inferInstance, ⟨w, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hw, hjv]
    · have hm' : Sec.res (F := tw q 1) j x = (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) := hm.symm
      rw [res_comp, hm']
      refine ((GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) V).2.2 W k m).trans ?_
      rw [hmW]
      exact map_zero _
  obtain ⟨S, hS, hSP⟩ := hloc
  have hF := (tw q 1).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hF
  refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
  have h1 := hSP V g hg
  change Sec.res g x = Sec.res g 0
  rw [h1]
  exact (map_zero _).symm

end GlobalTheory.EtC.MuTw.Inj
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR.AffLoc

section Lemmas

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem pt_comp {T T' : TT s} (φ : T ⟶ T') :
    pt T' = spMap (φ.hom.φ : T.obj.B →+* T'.obj.B) ≫ pt T := by
  have e : ((πe T').symm : T'.obj.B₀ →+* T'.obj.B).comp φ.hom.φ₀ =
      (φ.hom.φ : T.obj.B →+* T'.obj.B).comp ((πe T).symm : T.obj.B₀ →+* T.obj.B) := by
    ext b
    obtain ⟨b, rfl⟩ := T.obj.surj b
    change (πe T').symm (φ.hom.φ₀ (T.obj.π b)) = φ.hom.φ ((πe T).symm (πe T b))
    rw [φ.hom.comm, RingEquiv.symm_apply_apply]
    exact (πe T').symm_apply_apply (φ.hom.φ b)
  rw [pt, pt, ← φ.hom.pt, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, e, GlobalTheory.Cris.spMap_comp, Category.assoc]

theorem fv_of_comp (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T₁ T₂ T₃ : TT s} (a : T₁ ⟶ T₂)
    (c : T₂ ⟶ T₃) (d : T₁ ⟶ T₃) (h : ∀ x, c.hom.φ (a.hom.φ x) = d.hom.φ x) :
    fv f d = c.hom.φ (fv f a) + fv f c := by
  have e : a ≫ c = d := ObjectProperty.hom_ext _ (Thick.hom_ext h)
  rw [← e]
  exact f.2 a c

theorem ringHom_eq_of_spMap_eq {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

instance mono_affPt (s : X ⟶ Sp R) (U : X.affineOpens) : Mono (affPt s U) := by
  change Mono U.2.fromSpec
  have := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact IsOpenImmersion.mono _

theorem spMap_toSec (B : Type) [CommRing B] [Algebra R B] (V : (Sp B).affineOpens) :
    spMap (toSec R B V : B →+* Sec (algStr R B) V.1) = affPt (algStr R B) V :=
  (affPt_eq R B V).symm

end Lemmas

theorem fv_eq_sub_of_glued : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)),
    (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) →
    ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B),
    (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) →
    (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) →
    fv f φ = G' - φ.hom.φ G := by
  intro R _ X s f g _ T T' φ G G' hG hG'
  refine GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs T.obj.B T'.obj.B (pt T) (spMap (φ.hom.φ : T.obj.B →+* T'.obj.B)) _ _ ?_
  intro V' p hV'
  have hp' : V'.1 ≤ pt T' ⁻¹ᵁ p.1.2.1 := by
    rw [pt_comp φ]
    exact fun y hy ↦ p.2 (hV' hy)
  let p' : Pair (pt T') := ⟨(V', p.1.2), hp'⟩
  let q : Pair (spMap (φ.hom.φ : T.obj.B →+* T'.obj.B)) := ⟨(V', p.1.1), hV'⟩
  let χ := secPull (algStr R T.obj.B) (algStr R T'.obj.B) q
  have hw : spMap (φ.hom.φ : T.obj.B →+* T'.obj.B) ≫ algStr R T.obj.B =
      algStr R T'.obj.B ≫ spMap (RingHom.id R) := by
    rw [spMap_id, Category.comp_id, ← GlobalTheory.Cris.spMap_comp]
    exact congrArg spMap (φ.hom.φ.comp_algebraMap)
  let χA : Sec (algStr R T.obj.B) p.1.1.1 →ₐ[R] Sec (algStr R T'.obj.B) V'.1 :=
    { χ with commutes' := (semiHom_secPull (σ := RingHom.id R) hw q).map_algebraMap }

  let c : thk T p ⟶ thk T' p' := ⟨Thick.trivHom (T := (thk T' p').obj) χA (by
    change spMap χ ≫ _ = _
    rw [← Category.assoc, secPull_affPt, Category.assoc, ← pt_comp φ])⟩
  have h1 : ∀ u, χ (secPullA T p u) = secPullA T' p' u := by
    have e : χ.comp (secPull s (algStr R T.obj.B) p) = secPull s (algStr R T'.obj.B) p' := by
      refine ringHom_eq_of_spMap_eq ?_
      rw [← cancel_mono (affPt s p.1.2), GlobalTheory.Cris.spMap_comp, Category.assoc, secPull_affPt,
        ← Category.assoc, secPull_affPt, Category.assoc, ← pt_comp φ]
      exact (secPull_affPt s (algStr R T'.obj.B) p').symm
    exact fun u ↦ RingHom.congr_fun e u
  have h2 : ∀ b, χ (toSec R T.obj.B p.1.1 b) = toSec R T'.obj.B V' (φ.hom.φ b) := by
    have e : χ.comp (toSec R T.obj.B p.1.1 : T.obj.B →+* Sec (algStr R T.obj.B) p.1.1.1) =
        (toSec R T'.obj.B V' : T'.obj.B →+* Sec (algStr R T'.obj.B) V'.1).comp
          (φ.hom.φ : T.obj.B →+* T'.obj.B) := by
      refine ringHom_eq_of_spMap_eq ?_
      rw [GlobalTheory.Cris.spMap_comp, GlobalTheory.Cris.spMap_comp, spMap_toSec, spMap_toSec]
      exact secPull_affPt (algStr R T.obj.B) (algStr R T'.obj.B) q
    exact fun b ↦ RingHom.congr_fun e b
  have e1 : fv f (aM T' p') = χ (fv f (aM T p)) + fv f c := fv_of_comp f (aM T p) c (aM T' p') h1
  have e2 : χ (fv f (bM T p)) + fv f c = toSec R T'.obj.B V' (fv f φ) + fv f (bM T' p') :=
    (fv_of_comp f (bM T p) c (φ ≫ bM T' p') h2).symm.trans (f.2 φ (bM T' p'))
  change toSec R T'.obj.B V' (fv f φ) = toSec R T'.obj.B V' (G' - φ.hom.φ G)
  rw [map_sub, ← h2, hG p, hG' p']
  simp only [hSec, map_sub, map_add (f := _), h1]
  change _ = _ - (_ + χ (fv f (aM T p)) - χ (fv f (bM T p)))
  linear_combination -e1 - e2

end GlobalTheory.CechDR.AffLoc
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict (FormExt.omExt F) G).pull1 → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) := by
  first | exact @GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary | exact GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary | (intros; apply GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary <;> assumption)
end
