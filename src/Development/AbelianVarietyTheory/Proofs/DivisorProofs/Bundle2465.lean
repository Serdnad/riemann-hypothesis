module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle348
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.Poincare

theorem eq_zero_of_algebraMap_mem_rel {R G : Type} [CommRing R] [CommRing G] [Algebra R G] {J' : Ideal G}
    (δ' : DividedPowers J') (g : G) (hg : algebraMap G (DR R G) g ∈ rel R δ') : g = 0 := by
  have hle : rel R δ' ≤ RingHom.ker (ExteriorAlgebra.algebraMapInv (R := G) (M := Ω[G⁄R])).toRingHom := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨m, a, _, rfl⟩
    simp [ExteriorAlgebra.algebraMapInv]
  have := hle hg
  rw [RingHom.mem_ker] at this
  simpa [ExteriorAlgebra.algebraMap_leftInverse _ g] using this

theorem mDR_mDR {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
    {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
    (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ) (e : ∀ b, β (α b) = γ b) (x : DR R B) :
    h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.PDForm.Poincare


open GlobalTheory.PDForm.Poincare in
theorem GlobalTheory.PDForm.rq_truncPoly : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  intro R B _ _ _ J δ Q _ _ η G _ _ J' δ' q n hstd hlev hq hqd hqs hJ' hker α h hd hα

  obtain ⟨ε, hεs, hεd, hεb, hεe⟩ : ∃ ε : Q.P →+* B, SemiHom (RingHom.id R) ε ∧ IsDPMorphism η δ ε ∧
      (∀ b, ε (algebraMap B Q.P b) = b) ∧ ∀ k, ε (Q.e (k + 1)) = 0 := by
    obtain ⟨ε0, hε0⟩ := (GlobalTheory.PDA.PDPoly.exists_lift_and_aug B Q).2
    have hb : ∀ b, ε0 (algebraMap B Q.P b) = b := fun b ↦ ε0.commutes b
    refine ⟨ε0, fun r p ↦ ?_, ?_, hb, fun k ↦ (hε0 _).1 (Q.e_succ_mem_aug k)⟩
    · change ε0 (r • p) = r • ε0 p
      rw [← algebraMap_smul B r p, map_smul, algebraMap_smul]
    · refine GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd B J δ Q η hstd B J δ ε0 0 J.zero_mem ⟨?_, ?_⟩ ?_
      · intro x hx
        rw [Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b, hb b⟩)] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa [hb] using hy
      · intro k a _
        simp [hb]
      · intro k
        cases k with
        | zero => change ε0 (Q.e 0) = _; rw [Q.e_zero, map_one, δ.dpow_zero J.zero_mem]
        | succ k => change ε0 (Q.e (k + 1)) = _; rw [(hε0 _).1 (Q.e_succ_mem_aug k), δ.dpow_eval_zero (Nat.succ_ne_zero k)]
  have hi : SemiHom (RingHom.id R) (algebraMap B Q.P) := fun r b ↦ map_smul (IsScalarTower.toAlgHom R B Q.P) r b

  have hkε : ∀ p, q p = 0 → ε p = 0 := by
    intro p hp
    have h1 : ε p ∈ fil δ (n + 1) :=
      (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.2.2 B J δ ε hεd (n + 1) (Ideal.mem_map_of_mem _ ((hker p).1 hp))
    rw [hlev] at h1
    exact (Ideal.mem_bot).1 h1
  obtain ⟨eb, hebq⟩ : ∃ eb : G →+* B, ∀ p, eb (q p) = ε p :=
    ⟨q.liftOfRightInverse (Function.surjInv hqs) (Function.rightInverse_surjInv hqs) ⟨ε, fun p hp ↦ hkε p hp⟩,
      fun p ↦ RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  have hebα : ∀ b, eb (α b) = b := fun b ↦ by rw [hα, hebq, hεb]
  have heb : SemiHom (RingHom.id R) eb := by
    intro r g
    obtain ⟨p, rfl⟩ := hqs g
    have := hq r p
    simp only [RingHom.id_apply] at this ⊢
    rw [← this, hebq, hebq]
    simpa using hεs r p
  have hdeb : IsDPMorphism δ' δ eb := by
    have hc : eb.comp q = ε := RingHom.ext hebq
    refine ⟨?_, ?_⟩
    · rw [hJ', Ideal.map_map, hc]; exact hεd.1
    · intro k a ha
      rw [hJ', Ideal.mem_map_iff_of_surjective _ hqs] at ha
      obtain ⟨a, ha, rfl⟩ := ha
      rw [hebq, hqd.2 a ha, hebq, hεd.2 a ha]
  have hid : SemiHom (RingHom.id R) (RingHom.id B) := fun _ _ ↦ rfl
  have hdid : IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism
  have ret1 : ∀ x, km1 heb hdeb (km1 h hd x) = x := fun x ↦
    (divPowerCompatOneFormMap_comp h hd heb hdeb hid hdid hebα x).trans (divPowerCompatOneFormMap_id hid hdid (fun _ ↦ rfl) x)
  have ret : ∀ j x, km heb hdeb j (km h hd j x) = x := fun j x ↦
    (km_km h hd heb hdeb hid hdid hebα j x).trans (km_id hid hdid (fun _ ↦ rfl) j x)

  obtain ⟨v, hv0, hv1, hv2⟩ := GlobalTheory.PDA.PDPoly.exists_der R B J δ Q η hstd
  have he : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    rw [← hstd.var k]
    exact (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k _ (Q.e_one_mem_ext J)
  have hht := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e (n + 1) hv2 he
  have kq := GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms R Q.P (Q.ext J) η G J' δ' q hq n hqd hqs hJ' hker
  have kdr := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R Q.P G q hq hqs
  have key : ∀ X : DR R Q.P, hq.mDR (dDR R Q.P X) ∈ rel R δ' →
      hq.mDR X - h.mDR (hεs.mDR X) - dDR R G (hq.mDR (hot v Q.e (n + 1) X)) ∈ rel R δ' := by
    intro X hX
    have hT := hht.2.2.2.2 n _ (kq.1 _ hX)
    have hH := GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity R B J δ Q η v hi hstd hv0 hv1 hv2 ε hεs hεd hεb hεe (n + 1) X
    have h3 := add_mem hH hT
    rw [sub_add_cancel] at h3
    have := kq.2 _ h3
    rwa [map_sub, map_sub, mDR_mDR hi hq h (fun b ↦ (hα b).symm), hq.mDR_dDR] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x _ hx
    have hx' : α x = 0 := hx
    rw [← hebα x, hx', map_zero]
  ·
    intro y hy
    obtain ⟨p, rfl⟩ := hqs y
    have hy' : hq.mDR (dDR R Q.P (algebraMap Q.P (DR R Q.P) p)) ∈ rel R δ' := by
      rw [dDR_algebraMap, hq.mDR_ι, hq.m1_D]
      exact (Submodule.Quotient.mk_eq_zero (N1 R δ')).1 (by rw [← divPowerCompatFunctionDifferential_apply]; exact hy)
    have hk := key _ hy'
    rw [(hht.2.1 p), map_zero, map_zero, sub_zero, hq.mDR_algebraMap, hεs.mDR_algebraMap, h.mDR_algebraMap,
      ← map_sub] at hk
    have hp : q p = α (ε p) := sub_eq_zero.1 (eq_zero_of_algebraMap_mem_rel δ' _ hk)
    refine ⟨ε p, ?_, hp.symm⟩
    have h0 : km1 h hd (kd0 R δ (ε p)) = 0 := by rw [divPowerCompatOneFormMap_functionDifferential, ← hp]; exact hy
    rw [← ret1 (kd0 R δ (ε p)), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨eb y, ?_⟩
    rw [← divPowerCompatOneFormMap_functionDifferential heb hdeb, ← hxy, ret1]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.1 y
    have hy' : hq.mDR (dDR R Q.P (ι1 ω)) ∈ rel R δ' := by
      rw [hq.mDR_dDR, hq.mDR_ι]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 2)).1 (by rw [← divPowerCompatOneFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, algebraMap Q.P (DR R Q.P) c = hot v Q.e (n + 1) (ι1 ω) := by
      have := hht.2.2.1 0 _ (ι_mem ω)
      change _ ∈ LinearMap.range _ ^ 0 at this
      rwa [pow_zero, Submodule.mem_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_algebraMap, dDR_algebraMap, hq.mDR_ι, hεs.mDR_ι, h.mDR_ι, ← map_sub, ← map_sub] at hk
    set x : K1 R δ := Submodule.Quotient.mk (hεs.m1 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.m1 ω) : K1 R δ') = km1 h hd x + kd0 R δ' (q c) := by
      rw [divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, q c, ?_, heq⟩
    have h0 : km h hd 2 (kd1 R δ x) = 0 := by
      rw [divPowerCompatFormMap_oneFormDerivative, show km1 h hd x = Submodule.Quotient.mk (hq.m1 ω) - kd0 R δ' (q c) by rw [heq]; abel,
        map_sub, divPowerCompatOneFormDerivative_comp_differential, sub_zero]
      exact hy
    rw [← ret 2 (kd1 R δ x), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨km1 heb hdeb y, ?_⟩
    rw [← divPowerCompatFormMap_oneFormDerivative heb hdeb, ← hxy, ret]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.2.1 2 y
    have hy' : hq.mDR (dDR R Q.P (ω : DR R Q.P)) ∈ rel R δ' := by
      rw [hq.mDR_dDR]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 3)).1 (by rw [← divPowerCompatTwoFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, ι1 c = hot v Q.e (n + 1) (ω : DR R Q.P) := by
      have := hht.2.2.1 1 _ ω.2
      change _ ∈ LinearMap.range _ ^ 1 at this
      rwa [pow_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_ι] at hk
    set x : K R δ 2 := Submodule.Quotient.mk (hεs.mOm 2 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.mOm 2 ω) : K R δ' 2) = km h hd 2 x + kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) := by
      rw [km_mk, divPowerCompatOneFormDerivative_mk, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, Submodule.Quotient.mk (hq.m1 c), ?_, heq⟩
    have h0 : km h hd 3 (kd2 R δ x) = 0 := by
      rw [divPowerCompatFormMap_twoFormDerivative, show km h hd 2 x = Submodule.Quotient.mk (hq.mOm 2 ω) - kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) by
        rw [heq]; abel, map_sub, divPowerCompatTwoFormDerivative_comp_oneForm, sub_zero]
      exact hy
    rw [← ret 3 (kd2 R δ x), h0, map_zero]
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem isTranscendenceBasis_one_tmul {k K F W ι : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra K W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower K (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {x : ι → F}
    (hx : IsTranscendenceBasis k x) :
    IsTranscendenceBasis K fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ x i) := by
  let ψ : K ⊗[k] F →ₐ[K] W := IsScalarTower.toAlgHom K (K ⊗[k] F) W
  have hψ : Function.Injective ψ := IsFractionRing.injective (K ⊗[k] F) W
  have hy : AlgebraicIndependent K fun i => ψ (1 ⊗ₜ x i) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have h1 : Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K)
        (MvPolynomial.aeval (R := k) x).toLinearMap
        (algebraicIndependent_iff_injective_aeval.1 hx.1)
    have e : (MvPolynomial.aeval (R := K) fun i => ψ (1 ⊗ₜ x i)) =
        (ψ.comp (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x))).comp
          (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.toAlgHom := by
      ext i
      simp
    rw [e]
    exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.injective
  change IsTranscendenceBasis K fun i => ψ (1 ⊗ₜ x i)
  rw [hy.isTranscendenceBasis_iff_isAlgebraic, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  let E := IntermediateField.adjoin K (Set.range fun i => ψ (1 ⊗ₜ x i))
  let φ : F →+* W := (ψ : K ⊗[k] F →+* W).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := F)).toRingHom
  have hm : ∀ a ∈ Algebra.adjoin k (Set.range x), φ a ∈ E := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap k F r) = algebraMap K W (algebraMap k K r) := by
        rw [← ψ.commutes]
        change ψ (1 ⊗ₜ algebraMap k F r) = ψ (algebraMap k K r ⊗ₜ 1)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      rw [this]
      exact E.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let g : Algebra.adjoin k (Set.range x) →+* E :=
    (φ.comp (Algebra.adjoin k (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  have hT : ∀ a, ψ a ∈ algebraicClosure E W := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul l f =>
      have : l ⊗ₜ[k] f = algebraMap K _ l * ((1 : K) ⊗ₜ[k] f) := by simp
      rw [this, map_mul, ψ.commutes]
      refine mul_mem ((algebraicClosure E W).algebraMap_mem (algebraMap K E l)) ?_
      rw [mem_algebraicClosure_iff]
      exact (hx.isAlgebraic.isAlgebraic f).ringHom_of_comp_eq g φ hg rfl
  refine ⟨fun z => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[k] F) z
  exact mem_algebraicClosure_iff.1 (div_mem (hT a) (hT b))

theorem trBasis_append_tmul {k K F W : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra k W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower k (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {n m : ℕ} {x : Fin n → K}
    {y : Fin m → F} (hx : TrBasis (algebraMap k K) x) (hy : TrBasis (algebraMap k F) y) :
    TrBasis (algebraMap k W) (Fin.append (fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ y i))
      (fun i => algebraMap (K ⊗[k] F) W (x i ⊗ₜ 1))) := by
  have key : ∀ {A : Type} [Field A] [inst : Algebra k A] {l : ℕ} (u : Fin l → A),
      TrBasis (algebraMap k A) u ↔ IsTranscendenceBasis k u := by
    intro A _ inst l u
    have e : (algebraMap k A).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
  rw [key] at hx hy ⊢
  letI : Algebra K W := ((algebraMap (K ⊗[k] F) W).comp (algebraMap K (K ⊗[k] F))).toAlgebra
  haveI : IsScalarTower K (K ⊗[k] F) W := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k K W := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (K ⊗[k] F) W,
      IsScalarTower.algebraMap_apply k K (K ⊗[k] F), ← IsScalarTower.algebraMap_apply]
  have h := hx.sumElim_comp (isTranscendenceBasis_one_tmul (K := K) (W := W) hy)
  rw [← isTranscendenceBasis_equiv finSumFinEquiv]
  convert h using 1
  funext i
  rcases i with i | i
  · simp
  · simp
    rfl

theorem Place.le_ord_iff_div_mem {k K : Type} [Field k] [Field K] {c : k →+* K} (V : Place c)
    {f t : K} (hf : f ≠ 0) (ht : t ≠ 0) : V.ord t ≤ V.ord f ↔ f / t ∈ V.ring := by
  rw [← V.ord_nonneg_iff (div_ne_zero hf ht), div_eq_mul_inv, V.ord_mul hf (inv_ne_zero ht),
    V.ord_inv]
  omega

theorem exists_place_weighted_over_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ r : R, algebraMap (K ⊗[ℂ] κ') L ((r : K) ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = M * E.ord g) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    (fun ω => @dite ℤ (∃ a, V.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ M * ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ K) x) + 1) + k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE M hk hM
  obtain ⟨Q, hQ, z, hm, hdim, hEQ, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.exists_regular_localModel_graph_of_place (L := L) n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hw := trBasis_append_tmul (W := L) hx hτ
  let σ : Equiv.Perm (Fin (k + 1 + 1)) := Equiv.swap 0 1
  let wt : Fin (k + 1 + 1) → ℕ := fun i => if i = 1 then M else 1
  obtain ⟨V, hVQ, hV0, hVz, hVd, hVf⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ (k + 1) (k' + n)
    (z ∘ σ) wt (by rw [σ.surjective.range_comp]; exact hm) hdim (by simp [wt])
    (fun i => by simp only [wt]; split_ifs <;> omega) ⟨_, hw⟩
  have hz0 : V.ord (z 0) = M := by simpa [σ, wt] using hVz 1
  have hz0' : (z 0 : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hz0
    omega
  have hne : ∀ p : Q, IsUnit p → (p : L) ≠ 0 := fun p hp => (hp.map Q.subtype).ne_zero
  have hmul : ∀ (p : Q) (a : ℤ), IsUnit p → V.ord ((p : L) * (z 0 : L) ^ a) = M * a := by
    intro p a hp
    rw [V.ord_mul (hne p hp) (zpow_ne_zero _ hz0'), hV0 p hp, V.ord_zpow, hz0]
    ring
  refine ⟨V, fun r => hVQ _ (hEQ _ (hER _ r.2)), fun b hb0 => ?_, fun g hg0 => ?_,
    fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · obtain ⟨p, hp, e⟩ := hb b hb0
    rw [← e, hV0 p hp]
  · obtain ⟨p, hp, e⟩ := hg g hg0
    rw [e, hmul p _ hp]
  · obtain ⟨p, hp, e⟩ := hu l a b h
    rw [← e]
    exact ⟨hne p hp, hV0 p hp⟩
  · obtain ⟨p, e, hp⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [← hz0, V.le_ord_iff_div_mem h0 hz0']
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hz0']
    refine add_mem ?_ (hVQ _ u.2)
    by_cases hs0 : (s : L) = 0
    · rw [hs0, zero_div]
      exact zero_mem _
    · rw [← V.le_ord_iff_div_mem hs0 hz0', hz0]
      exact hVd M s hs0 hs
  · have hd : dForm (algebraMap ℂ L) (fun i => (y i : L)) ≠ 0 := by
      intro h
      have h1 := (isFreeGen_dForm_of_trBasis _ hw).1 (a₁ := 1) (a₂ := 0)
        (by simp only [hform, h, smul_zero])
      exact one_ne_zero h1
    have hs : ∑ i, (wt i : ℤ) = M + (k + 1) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have : ∀ i : Fin k, wt i.succ.succ = 1 := fun i =>
        if_neg (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))
      simp [this, wt]
      ring
    have h1 := hVf y hy
    change V.formOrd _ + 1 ≤ M * (E.formOrd _ + 1) + (k + 1)
    rw [hform, V.formOrd_smul hw hd (mul_ne_zero (hne q hq) (zpow_ne_zero _ hz0')), hmul q _ hq]
    rw [hs] at h1
    push_cast
    linarith

end GlobalTheory.FieldPair
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

def detPol (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.det (Matrix.of fun a s => X (a, s))

def liftPol {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial (Fin n × Fin n) C :=
  detPol C n ^ k * MvPolynomial.map e0 f

def Shift {ι : Type} {n : ℕ} (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) : Prop :=
  ∀ τ (a : Fin n), (lamW τ a : ℤ) = (lam τ).w a + c τ

def IsPhi {K C : Type} [Field K] [Field C] {ι : Type} [Fintype ι] {n : ℕ} (e0 : K →+* C) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ)
    (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW) : Prop :=
  ∀ (x : ι → MvPolynomial (Fin n × Fin n) K) (v : VV K lam), (∀ τ, x τ ∈ nablaSq K n (lam τ)) → (v : Pol K ι n) = ten x →
    ∃ y : ∀ τ, dualWeyl C n n (res n (lamW τ)),
      (∀ τ, (y τ : MvPolynomial (Fin n × Fin n) C) = liftPol e0 (lamW τ (n - 1)) (x τ)) ∧ Φ v = PiTensorProduct.tprod C y

def lamG (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) :
    (ι → GL (Fin n) C) →* Module.End C (NablaT C n lamW) where
  toFun g := ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g
  map_one' := by simp [grp]
  map_mul' g h := by
    simp only [grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

theorem lamG_apply (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ)
    (g : ι → GL (Fin n) C) (z : NablaT C n lamW) :
    lamG C n lamW c g z = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g z := rfl

def AtPlace {K : Type} [Field K] [NumberField K] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) : Prop :=
  ∀ x : 𝓞 K, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1

end GlobalTheory.FrameRead
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.chart_character_is_logarithm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ χ : PS X.O 1 (chD Ch.ch), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) χ → IsCharLog (fgl Ch X) (fun j => algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl χ j)) := by
  first | exact @GlobalTheory.CharLogOfChar.isCharLog_dl | exact GlobalTheory.CharLogOfChar.isCharLog_dl | (intros; apply GlobalTheory.CharLogOfChar.isCharLog_dl <;> assumption)
end
