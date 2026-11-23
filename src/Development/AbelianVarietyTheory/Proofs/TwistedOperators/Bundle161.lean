module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Multilinear.Basis

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelCharacters_unramified_off_levelPlaces : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  first | exact @GlobalTheory.levCh_unramified_places | exact GlobalTheory.levCh_unramified_places | (intros; apply GlobalTheory.levCh_unramified_places <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isMultiplicityInner_of_unit_twist_shift : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  intro D V S θ M J χ μ 𝓕 hμ h𝓕 κ a ha hκ T hT T' hT' U U' hU hU' c hc
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold IsMultIP at hc ⊢
  intro v v'
  have haa : star a * a = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hfun : (fun g => star (U v g) * U' v' g) = fun g => star (T v (g * κ)) * T' v' (g * κ) := by
    funext g
    rw [hU, hU', star_mul']
    calc star a * star (T v (g * κ)) * (a * T' v' (g * κ))
        = (star a * a) * (star (T v (g * κ)) * T' v' (g * κ)) := by ring
      _ = star (T v (g * κ)) * T' v' (g * κ) := by rw [haa, one_mul]
  have hinv : ∀ γ ∈ GQ V, ∀ g, star (T v (γ * g)) * T' v' (γ * g) = star (T v g) * T' v' g := by
    intro γ hγ g
    rw [(GlobalTheory.mult_value_left_cont_level θ M J χ T hT v).1 γ hγ g,
      (GlobalTheory.mult_value_left_cont_level θ M J χ T' hT' v').1 γ hγ g]
  have key := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 κ hκ
    (fun g => star (T v g) * T' v' g) hinv (hc v v').1
  rw [hfun]
  exact ⟨key.1, key.2.trans (hc v v').2⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private lemma atTau_mem_GinfC_twisted_operators {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem isMultMap_rightTranslate_finite : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  intro D V S θ M J χ κ hκ hJ T hT
  refine ⟨(LinearMap.funLeft ℂ ℂ (fun g : GA D V => g * κ)).compMultilinearMap T,
    ⟨fun v => ?_, fun v => ?_, fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v => rfl⟩
  ·
    exact GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite θ V κ hκ (T v) (hT.aut v)
  ·
    intro r C hC μ 𝓕 hμ h𝓕 g
    have h := hT.cusp v r C hC μ 𝓕 hμ h𝓕 (g * κ)
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, Function.comp, mul_assoc] using h
  ·
    obtain ⟨hk1, hk2⟩ := hJ k hk
    show T v (g * k * κ) = χ k * T v (g * κ)
    have h := hT.lev v _ hk1 (g * κ)
    rw [hk2] at h
    rw [← h]
    congr 1
    group
  ·
    rw [LinearMap.compMultilinearMap_apply, hT.equiv τ g hg v w hw]
    funext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.T.mul_comm_of_mem_GfC_of_mem_GinfC V κ _ hκ (atTau_mem_GinfC_twisted_operators θ V τ g)]
  ·
    obtain ⟨ℓ, hℓ, hℓw⟩ := hT.cont τ v (x * κ)
    exact ⟨ℓ, hℓ, fun w => hℓw w⟩

end GlobalTheory
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.TensorKernel

theorem piTensor_map_surjective_and_ker :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : ι → Type) [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)] (π : ∀ τ, A τ →ₗ[ℂ] B τ), (∀ τ, Function.Surjective (π τ)) → Function.Surjective (PiTensorProduct.map π) ∧ ∀ l : Module.Dual ℂ (⨂[ℂ] τ, A τ), (∀ (τ : ι) (x : ∀ σ, A σ), π τ (x τ) = 0 → l (PiTensorProduct.tprod ℂ x) = 0) → ∀ z, PiTensorProduct.map π z = 0 → l z = 0 := by
  intro ι _ _ A B _ _ _ _ π hπ

  have hsec : ∀ τ, ∃ g : B τ →ₗ[ℂ] A τ, π τ ∘ₗ g = LinearMap.id := fun τ =>
    (π τ).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (hπ τ))
  choose s hs using hsec
  have hπs : ∀ τ b, π τ (s τ b) = b := fun τ b => by
    simpa using LinearMap.congr_fun (hs τ) b

  have back : ∀ b, PiTensorProduct.map π (PiTensorProduct.map s b) = b := by
    intro b
    induction b using PiTensorProduct.induction_on with
    | smul_tprod r f => simp [PiTensorProduct.map_tprod, hπs]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  refine ⟨fun b => ⟨_, back b⟩, ?_⟩
  intro l hl

  have key : ∀ x : ∀ σ, A σ, l (PiTensorProduct.tprod ℂ x) =
      l (PiTensorProduct.tprod ℂ (fun σ => s σ (π σ (x σ)))) := by
    intro x
    have step : ∀ S : Finset ι, l (PiTensorProduct.tprod ℂ x) =
        l (PiTensorProduct.tprod ℂ (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S ha ih =>
        rw [ih]
        have h1 : (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) =
            Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a (x a) := by
          funext σ
          by_cases h : σ = a
          · subst h; simp [ha]
          · rw [Function.update_of_ne h]
        have h2 : (fun σ => if σ ∈ insert a S then s σ (π σ (x σ)) else x σ) =
            Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a
              (s a (π a (x a))) := by
          funext σ
          by_cases h : σ = a
          · subst h; simp
          · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
        have h4 := hl a (Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a
          (x a - s a (π a (x a)))) (by simp [hπs])
        rw [MultilinearMap.map_update_sub, map_sub, sub_eq_zero, ← h1] at h4
        rw [h2, h4]
    simpa using step Finset.univ
  have hall : ∀ z, l z = l (PiTensorProduct.map s (PiTensorProduct.map π z)) := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r f => simp [PiTensorProduct.map_tprod, key f]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hp, ← hq]
  intro z hz
  rw [hall z, hz, map_zero, map_zero]

end GlobalTheory.TensorKernel
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

noncomputable section

namespace GlobalTheory.PolyTensor

theorem curry_sum_mapDomain {ι β : Type} [Fintype ι] (v : ι → (β →₀ ℕ)) (τ : ι) :
    (∑ σ, Finsupp.mapDomain (fun x => (σ, x)) (v σ)).curry τ = v τ := by
  classical
  ext x
  rw [Finsupp.curry_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.mk.inj h).2) (v τ) x
  · intro σ _ hσ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h
    exact absurd (Finset.mem_univ τ) h

def expEquiv (ι σ : Type) [Fintype ι] : (ι → (σ →₀ ℕ)) ≃ (ι × σ →₀ ℕ) :=
  Equiv.ofBijective (fun v => ∑ τ, Finsupp.mapDomain (fun x => (τ, x)) (v τ)) <| by
    classical
    refine ⟨fun v w h => funext fun τ => ?_, fun m => ⟨fun τ => m.curry τ, ?_⟩⟩
    · rw [← curry_sum_mapDomain v τ, ← curry_sum_mapDomain w τ]
      exact congrArg (fun m : ι × σ →₀ ℕ => m.curry τ) h
    · ext ⟨τ, x⟩
      have := DFunLike.congr_fun (curry_sum_mapDomain (fun τ => m.curry τ) τ) x
      simpa only [Finsupp.curry_apply] using this

theorem exists_piTensor_equiv : ∀ (ι σ : Type) [Fintype ι],
    ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ,
      ∀ f : ι → MvPolynomial σ ℂ,
        e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  intro ι σ _
  classical
  let bT := Basis.piTensorProduct (fun _ : ι => MvPolynomial.basisMonomials σ ℂ)
  let e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
    bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

  have key : e.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
        (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap) := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials σ ℂ) fun v => ?_
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, ← Basis.piTensorProduct_apply]
    change bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ) (bT v) = _
    rw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      MvPolynomial.rename_monomial, expEquiv, Equiv.ofBijective_apply]
    exact MvPolynomial.monomial_sum_one _ _
  refine ⟨e, fun f => ?_⟩
  simpa using MultilinearMap.congr_fun key f

end GlobalTheory.PolyTensor
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  first | exact @GlobalTheory.isMultiplicityInner_of_unit_twist_shift | exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift | (intros; apply GlobalTheory.isMultiplicityInner_of_unit_twist_shift <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isMultMap_rightTranslate_finiteAdelic_normalizer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  exact @GlobalTheory.isMultMap_rightTranslate_finite

end
end
