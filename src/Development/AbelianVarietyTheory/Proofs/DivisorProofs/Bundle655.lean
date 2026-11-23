module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle628
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle615
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
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped TensorProduct

theorem GlobalTheory.PDivGroup.mulP_mem_sq_counit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  intro p hp O _ _ _ hp0 hpu hroot G n b hb

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpk
  haveI : ExpChar (IsLocalRing.ResidueField O) p := ExpChar.prime hp.out
  haveI : PerfectRing (IsLocalRing.ResidueField O) p :=
    PerfectRing.ofSurjective _ p (fun y => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := hroot a
      exact ⟨IsLocalRing.residue O c, by rw [frobenius_def, ← map_pow, hc]⟩)

  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower O (G.A n) (G.A (n + 1)) :=
    IsScalarTower.of_algebraMap_eq fun c => ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)).commutes c).symm
  haveI : Module.Flat (G.A n) (G.A (n + 1)) := GlobalTheory.T.mulP_flat' p O G n
  have hε : ∀ b : G.A n, Bialgebra.counitAlgHom O (G.A (n + 1)) (algebraMap (G.A n) (G.A (n + 1)) b) =
      Bialgebra.counitAlgHom O (G.A n) b := fun b => by
    rw [Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
    exact CoalgHomClass.counit_comp_apply (G.mulP n) b
  have hker : (RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1))) =
      RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hε]

  obtain ⟨ρ, hρ⟩ : ∃ ρ : G.A (n + 1) →+* IsLocalRing.ResidueField O ⊗[O] G.A 1,
      ∀ a, ρ a = 1 ⊗ₜ G.resOne n a :=
    ⟨(Algebra.TensorProduct.includeRight : G.A 1 →ₐ[O] IsLocalRing.ResidueField O ⊗[O] G.A 1).toRingHom.comp
      ((G.resOne n : G.A (n + 1) →ₐ[O] G.A 1) : G.A (n + 1) →+* G.A 1), fun _ => rfl⟩
  have hπs : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective
  have hπk : RingHom.ker (algebraMap O (IsLocalRing.ResidueField O)) = IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hfib := GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one p O (IsLocalRing.ResidueField O) hπs G n
  have hρs : Function.Surjective ρ := fun h => by
    obtain ⟨a, ha⟩ := hfib.1 h
    exact ⟨a, by rw [hρ]; exact ha⟩
  have hkerρ : RingHom.ker ρ = (RingHom.ker ((algebraMap O (IsLocalRing.ResidueField O)).comp
      ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))))).map
      (algebraMap (G.A n) (G.A (n + 1))) := by
    have hcomp : (algebraMap O (IsLocalRing.ResidueField O)).comp
        ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))) =
        (algebraMap O (IsLocalRing.ResidueField O)).comp (Bialgebra.counitAlgHom O (G.A n) : G.A n →+* O) :=
      RingHom.ext fun b => by
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hε]
    rw [hcomp]
    ext a
    rw [RingHom.mem_ker, hρ]
    exact hfib.2 a
  have hρalg : ∀ c : O, ρ (algebraMap O (G.A (n + 1)) c) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)
        (algebraMap O (IsLocalRing.ResidueField O) c) := fun c => by
    rw [hρ, AlgHomClass.commutes, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes c)
  have hεH : ∀ a, Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) (ρ a) =
      algebraMap O (IsLocalRing.ResidueField O) (Bialgebra.counitAlgHom O (G.A (n + 1)) a) := fun a => by
    rw [hρ, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def, mul_comm]
    simp

  have hlaws : (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.lid (IsLocalRing.ResidueField O) _
      (LinearMap.rTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) ∧
      (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.rid (IsLocalRing.ResidueField O) _
      (LinearMap.lTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) := by
    constructor
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.rTensor_counit_comul]
      simp
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.lTensor_counit_comul]
      simp
  obtain ⟨e, he1, hei, ε', Δ', hlaws', hnil⟩ := GlobalTheory.T.localFactor_at_augmentation_counital_comul _ _ _ _ hlaws
  have hpres := GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker p _ _ ε' Δ' hlaws' hnil

  obtain ⟨r, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType O (G.A (n + 1)))
  have hfa : f₀ = MvPolynomial.aeval (fun i => f₀ (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.aeval_X]
  have hmap : ∀ {τ : Type} (x : τ → G.A (n + 1)) (q : MvPolynomial τ O),
      MvPolynomial.aeval (fun j => ρ (x j)) (MvPolynomial.map (algebraMap O (IsLocalRing.ResidueField O)) q) =
        ρ (MvPolynomial.aeval x q) := by
    intro τ x q
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext fun c => (hρalg c).symm
  have haH : Function.Surjective (MvPolynomial.aeval (fun i => ρ (f₀ (MvPolynomial.X i))) :
      MvPolynomial (Fin r) (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O] _) := fun h => by
    obtain ⟨y, rfl⟩ := hρs h
    obtain ⟨q, rfl⟩ := hf₀ y
    exact ⟨_, (hmap (fun i => f₀ (MvPolynomial.X i)) q).trans (by rw [← hfa])⟩
  obtain ⟨s, y, g, hg0, hgker⟩ := GlobalTheory.T.exists_presentation_square_at_point_of_localFactor _ _ _ e he1 hei hpres r _ haH
  choose yt hyt using fun i => hρs (y i)
  obtain ⟨x, hxd⟩ : ∃ x : Fin s ⊕ Fin r → G.A (n + 1), x = Sum.elim yt (fun i => f₀ (MvPolynomial.X i)) := ⟨_, rfl⟩
  have hx : (fun j => ρ (x j)) = Sum.elim y (fun i => ρ (f₀ (MvPolynomial.X i))) := by
    funext j
    cases j <;> simp [hxd, hyt]
  have hxs : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1)) := by
    intro z
    obtain ⟨q, rfl⟩ := hf₀ z
    refine ⟨MvPolynomial.map (algebraMap O (G.A n)) (MvPolynomial.rename Sum.inr q), ?_⟩
    rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename, hfa, hxd]
    rfl
  haveI : Module.FinitePresentation O (G.A (n + 1)) := Module.finitePresentation_of_projective _ _
  haveI : Algebra.FinitePresentation O (G.A (n + 1)) := Algebra.FinitePresentation.of_finitePresentation _ _
  haveI : Algebra.FinitePresentation (G.A n) (G.A (n + 1)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O _ _
  have hFG : (RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1))).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective _ hxs
  obtain ⟨f, hf0, hfker⟩ := GlobalTheory.T.lift_square_presentation_of_flat_alt O (G.A n) (G.A (n + 1)) (IsLocalRing.ResidueField O) _ (Fin s ⊕ Fin r)
    (Bialgebra.counitAlgHom O (G.A (n + 1))) (algebraMap O (IsLocalRing.ResidueField O)) ρ
    (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)) x
    hπs hπk hρalg hεH hkerρ hxs hFG g (by rw [hx]; exact hg0) (by rw [hx]; exact hgker)
  have hpt : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))), (p : O) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 ⊔
        ((RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1)))).map
          (algebraMap (G.A n) (G.A (n + 1))) := by
    rw [hker]
    exact GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP p O G n
  have := GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point O (G.A n) (G.A (n + 1)) (Fin s ⊕ Fin r) (Bialgebra.counitAlgHom O (G.A (n + 1))) x f (p : O)
    hp0 hxs hf0 hfker hpt b hb
  rwa [hker] at this
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.TateResidue

open WithConv

theorem conv_eq_one_of_mul {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    {B : Type} [CommRing B] [Algebra O B] (n : ℕ) (a b : WithConv (G.A n →ₐ[O] B))
    (h : a * b = b) : a = 1 :=
  (IsUnit.of_pow_eq_one (G.pts_pow_self n b)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mul_right_cancel (h.trans (one_mul _).symm)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  set k := IsLocalRing.ResidueField O
  set π := G.tatePush (Algebra.ofId O k)

  have hlift : ∀ (n : ℕ) (c : G.A n →ₐ[O] k), ∃ t : G.Tate, (π t).pt n = c := by
    intro n c
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat p C v O hv (G.A n) c
    obtain ⟨t, ht⟩ := G.pt_surjective C n x
    refine ⟨t, AlgHom.ext fun a => ?_⟩
    rw [tatePush_pt]
    change IsLocalRing.residue O (t.pt n a) = c a
    rw [show t.pt n = x from ht]
    exact hx a
  refine ⟨fun n c => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hlift n c
    exact ⟨π t, ht⟩
  have := G.finite_tate C
  have hπ : Function.Surjective π := by
    refine TateFree.surjective_of_mod π TateOver.eq_zero_of_forall_pow_smul fun y => ?_
    obtain ⟨x, hx⟩ := hlift 1 (y.pt 1)
    obtain ⟨z, hz⟩ := (TateOver.conv_eq_one_iff (y - π x) 1).1 <| by
      have h1 : (y - π x + π x).conv 1 = y.conv 1 := by rw [sub_add_cancel]
      rw [TateOver.add_conv] at h1
      have h2 : (π x).conv 1 = y.conv 1 := congrArg toConv hx
      rw [h2] at h1
      exact conv_eq_one_of_mul G _ _ _ h1
    exact ⟨x, z, by rwa [pow_one] at hz⟩
  have : Module.Finite ℤ_[p] (G.TateOver k) := Module.Finite.of_surjective π hπ
  have : Module.Free ℤ_[p] (G.TateOver k) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨s, fun t => LinearMap.congr_fun hs t, fun n t t' h => ?_⟩
  have hd : (t - t').conv n = 1 := by
    have h1 : (t - t' + t').conv n = t.conv n := by rw [sub_add_cancel]
    rw [TateOver.add_conv, show t'.conv n = t.conv n from congrArg toConv h.symm] at h1
    exact conv_eq_one_of_mul G _ _ _ h1
  obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - t') n).1 hd
  have h3 : (s t - s t').conv n = 1 := by
    rw [← map_sub, ← hu, map_smul]
    exact (TateOver.conv_eq_one_iff _ n).2 ⟨_, rfl⟩
  have h4 : (s t - s t' + s t').conv n = (s t).conv n := by rw [sub_add_cancel]
  rw [TateOver.add_conv, h3, one_mul] at h4
  exact congrArg ofConv h4.symm

end GlobalTheory.TateResidue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix

namespace GlobalTheory.RiemannRel

theorem map_im_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.im = P.map Complex.re * Q.map Complex.im + P.map Complex.im * Q.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

theorem map_re_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.re = P.map Complex.re * Q.map Complex.re - P.map Complex.im * Q.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

theorem hermForm_cols {h : ℕ} (Hm P Q : Matrix (Fin h) (Fin h) ℂ) (i j : Fin h) :
    (Pᵀ * Hm * Q.map star) i j = hermForm Hm (fun k => P k i) (fun k => Q k j) := by
  rw [Matrix.mul_assoc]
  simp [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec]

theorem matrix_form {h : ℕ} (Hm L M : Matrix (Fin h) (Fin h) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hG : (Mᵀ * Hm * M.map star).map Complex.im = 0)
    (hA : (Lᵀ * Hm * M.map star).map Complex.im = 1)
    (hB : (Lᵀ * Hm * L.map star).map Complex.im = 0) :
    IsUnit M.det ∧ (M⁻¹ * L).IsSymm ∧ ((M⁻¹ * L).map Complex.im).PosDef := by
  set G := Mᵀ * Hm * M.map star with hGdef
  have hGh : G.IsHermitian := by
    have h1 : M.map star = (Mᵀ)ᴴ := by ext i j; simp
    rw [hGdef, h1]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hH
  set R := G.map Complex.re with hR
  have hRs : Rᵀ = R := by
    ext i j
    have := congrArg Complex.re (hGh.apply i j)
    simpa [hR] using this
  have hGR : G = R.map Complex.ofReal := by
    ext i j
    have := congrFun (congrFun hG i) j
    apply Complex.ext
    · simp [hR]
    · simpa [hR] using this
  have hRp : R.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hRs) fun x hx => ?_
    set xc : Fin h → ℂ := fun i => (x i : ℂ) with hxc
    have hst : star (M.mulVec xc) = (M.map star).mulVec xc := by
      funext i
      simp [Matrix.mulVec, dotProduct, hxc]
    have hne : M.mulVec xc ≠ 0 := by
      intro h0
      apply hx
      have h1 : (Lᵀ * Hm * M.map star).mulVec xc = 0 := by
        rw [← Matrix.mulVec_mulVec, ← hst, h0]; simp
      have h2 : ((Lᵀ * Hm * M.map star).map Complex.im).mulVec x = 0 := by
        funext i
        have := congrArg Complex.im (congrFun h1 i)
        simpa [Matrix.mulVec, dotProduct, hxc, Complex.im_sum] using this
      rwa [hA, Matrix.one_mulVec] at h2
    have h3 := hpos _ hne
    have h4 : M.mulVec xc ⬝ᵥ Hm.mulVec (star (M.mulVec xc)) = xc ⬝ᵥ G.mulVec xc := by
      rw [hst, hGdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec xc, Matrix.vecMul_transpose]
    rw [h4] at h3
    simpa [Matrix.mulVec, dotProduct, hxc, Complex.re_sum, hR] using h3
  have hRu : IsUnit R.det := hRp.det_pos.ne'.isUnit
  have hMu : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : G.det = 0 := by
      rw [hGdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; simp
    have h2 : G.det = (R.det : ℂ) := by
      rw [hGR]
      exact (Complex.ofRealHom.map_det R).symm
    rw [h1] at h2
    exact hRu.ne_zero (Complex.ofReal_eq_zero.1 h2.symm)
  set τ := M⁻¹ * L with hτ
  have hL : L = M * τ := by rw [hτ, Matrix.mul_nonsing_inv_cancel_left _ _ hMu]
  have hA' : Lᵀ * Hm * M.map star = τᵀ * G := by
    conv_lhs => rw [hL]
    rw [hGdef, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hB' : Lᵀ * Hm * L.map star = τᵀ * G * τ.map star := by
    have : L.map star = M.map star * τ.map star := by
      conv_lhs => rw [hL]
      exact Matrix.map_mul (f := starRingEnd ℂ)
    rw [this, ← Matrix.mul_assoc, hA']
  set X := τ.map Complex.re with hX
  set Y := τ.map Complex.im with hY
  have e1 : τᵀ.map Complex.re = Xᵀ := rfl
  have e2 : τᵀ.map Complex.im = Yᵀ := rfl
  have e3 : (τ.map star).map Complex.re = X := by ext i j; simp [hX]
  have e4 : (τ.map star).map Complex.im = -Y := by ext i j; simp [hY]
  rw [hB', map_im_mul, ← hA', hA, hA', map_re_mul, e1, e2, e3, e4, hG, ← hR] at hB
  rw [hA', map_im_mul, e1, e2, hG, ← hR, Matrix.mul_zero, zero_add] at hA
  have hRY : R * Y = 1 := by
    have := congrArg Matrix.transpose hA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.transpose_one] at this
  have hYi : R⁻¹ = Y := Matrix.inv_eq_right_inv hRY
  have hYi' : R⁻¹ = Yᵀ := Matrix.inv_eq_left_inv hA
  have hXs : Xᵀ = X := by
    rw [Matrix.mul_zero, sub_zero, Matrix.mul_neg, Matrix.mul_assoc, hRY, Matrix.mul_one, Matrix.one_mul] at hB
    exact (neg_add_eq_zero.1 hB)
  refine ⟨hMu, ?_, hYi ▸ hRp.inv⟩
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun hXs i) j
  · exact congrFun (congrFun (hYi'.symm.trans hYi) i) j

theorem exists_siegel_of_symplectic : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  intro h Hm v hH hpos hv
  let L : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inl i) k
  let M : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inr i) k
  obtain ⟨hM, hs, hp⟩ := matrix_form Hm L M hH hpos
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inr i) (.inr j)).trans ?_
      simp [omegaStd])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inr j)).trans ?_
      simp [omegaStd, Pi.single_apply, Matrix.one_apply, eq_comm])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inl j)).trans ?_
      simp [omegaStd])
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hM
  refine ⟨M⁻¹ * L, M.toLinearEquiv' inferInstance, hs, hp, fun a => ?_⟩
  change M.mulVec (per (M⁻¹ * L) a) = _
  rw [per, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hM]
  funext k
  simp [L, M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]

end GlobalTheory.RiemannRel
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem blockDiagPart_mul {L : Type} [Field L] {n : ℕ} (β : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L)
    (hA : A.BlockTriangular β) (hB : B.BlockTriangular β) (hAB : A * B = 1) :
    (Matrix.of fun a b => if β a = β b then A a b else 0) *
      (Matrix.of fun a b => if β a = β b then B a b else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h : β i = β j
  · rw [← hAB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
    · rw [hA h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hB (h ▸ h1 : β j < β l)]; simp
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e]))]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [if_neg (hl ▸ h : ¬ β l = β j), mul_zero]
    · rw [if_neg hl, zero_mul]

theorem leviPart : LeviPart := by
  intro L _ _ σ n β hβ g hg
  have hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev := fun a b =>
    ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩
  have h0 : (mat g⁻¹).BlockTriangular β := by
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h1 := blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM
  have h2 : antiJ L n * (cT σ M * antiJ L n) =
      Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0 := by
    ext a b
    rw [antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]
    by_cases h : β a = β b
    · rw [if_pos h, if_pos ((hβ' _ _).1 h.symm)]
    · rw [if_neg h, if_neg (fun e => h ((hβ' _ _).2 e).symm), map_zero]
  have h3 : cT σ M * antiJ L n * M = antiJ L n := by
    rw [← h2] at h1
    calc cT σ M * antiJ L n * M
        = antiJ L n * (antiJ L n * (cT σ M * antiJ L n) * M) := by
          rw [← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n),
            GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = antiJ L n := by rw [h1, Matrix.mul_one]
  obtain ⟨m, hm⟩ := exists_mat M h3
  have hmL : m ∈ leviU σ β := fun i j h => by rw [hm, hM, Matrix.of_apply, if_neg h]
  refine ⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, if_pos h], fun i j h => ?_⟩
  rw [← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : β i = β l
  · rw [hm, hM, Matrix.of_apply]
    split_ifs with h4
    · rfl
    · rw [hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]
  · rw [(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]

end GlobalTheory.SatakeWeyl
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO : ∀ {k O H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z), Z ≤ G → finrank k ((ksSub σ 0 G Z).map (cls G)) = finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := by
  first | exact @GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | exact GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | (intros; apply GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO <;> assumption)
end
