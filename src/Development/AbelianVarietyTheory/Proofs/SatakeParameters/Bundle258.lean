module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.Automorphisms.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


namespace GlobalTheory

theorem isSubquotient_of_exact_middle (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q]
    (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A)
    (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ) :
    τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ →
      IsSubquotient τ α ∨ IsSubquotient τ κ := by
  intro hτ hex ⟨T, f, hf⟩

  let W' : Subrepresentation τ :=
    ⟨(LinearMap.ker (q.toLinearMap ∘ₗ T.toSubmodule.subtype)).map f.toLinearMap, by
      rintro g _ ⟨t, ht, rfl⟩
      refine ⟨T.toRepresentation g t, ?_, (f.isIntertwining _ _ g t)⟩
      have ht' : q (t : V) = 0 := ht
      show q (ρ g (t : V)) = 0
      rw [q.isIntertwining, ht', map_zero]⟩
  rcases hτ.eq_bot_or_eq_top W' with h | h
  ·
    right
    have hvan : ∀ t : T.toSubmodule, q (t : V) = 0 → f t = 0 := by
      intro t ht
      have hm : f t ∈ W'.toSubmodule := ⟨t, ht, rfl⟩
      rw [h] at hm
      exact hm
    let S : Subrepresentation κ := ⟨T.toSubmodule.map q.toLinearMap, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨ρ g v, T.apply_mem_toSubmodule g hv, q.isIntertwining _ _ g v⟩⟩
    let q' : T.toSubmodule →ₗ[ℂ] S.toSubmodule :=
      LinearMap.codRestrict S.toSubmodule (q.toLinearMap ∘ₗ T.toSubmodule.subtype)
        (fun t => ⟨t, t.2, rfl⟩)
    have hq' : Function.Surjective q' := by
      rintro ⟨_, v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    have hker : LinearMap.ker q' ≤ LinearMap.ker f.toLinearMap := by
      intro t ht
      have : q (t : V) = 0 := congrArg Subtype.val (ht : q' t = 0)
      exact hvan t this
    let e := q'.quotKerEquivOfSurjective hq'
    let φ : S.toSubmodule →ₗ[ℂ] U := ((LinearMap.ker q').liftQ f.toLinearMap hker) ∘ₗ e.symm.toLinearMap
    have hφ : ∀ t, φ (q' t) = f t := by
      intro t
      show (LinearMap.ker q').liftQ f.toLinearMap hker (e.symm (q' t)) = f t
      have : e.symm (q' t) = Submodule.Quotient.mk t := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      rw [this]; rfl
    refine ⟨S, ⟨φ, fun g => ?_⟩, fun u => ?_⟩
    · ext s
      obtain ⟨t, rfl⟩ := hq' s
      have h1 : S.toRepresentation g (q' t) = q' (T.toRepresentation g t) :=
        Subtype.ext (q.isIntertwining _ _ g t).symm
      show φ (S.toRepresentation g (q' t)) = τ g (φ (q' t))
      rw [h1, hφ, hφ]
      exact f.isIntertwining _ _ g t
    · obtain ⟨t, rfl⟩ := hf u
      exact ⟨q' t, hφ t⟩
  ·
    left
    let R : Subrepresentation α := ⟨T.toSubmodule.comap i.toLinearMap, by
      intro g a ha
      show i (α g a) ∈ T.toSubmodule
      rw [i.isIntertwining]
      exact T.apply_mem_toSubmodule g ha⟩
    let j : R.toSubmodule →ₗ[ℂ] T.toSubmodule :=
      LinearMap.codRestrict T.toSubmodule (i.toLinearMap ∘ₗ R.toSubmodule.subtype) (fun a => a.2)
    refine ⟨R, ⟨f.toLinearMap ∘ₗ j, fun g => ?_⟩, fun u => ?_⟩
    · ext a
      show f (j (R.toRepresentation g a)) = τ g (f (j a))
      have h1 : j (R.toRepresentation g a) = T.toRepresentation g (j a) :=
        Subtype.ext (i.isIntertwining _ _ g a)
      rw [h1]
      exact f.isIntertwining _ _ g (j a)
    · have hu : u ∈ W'.toSubmodule := by rw [h]; trivial
      obtain ⟨t, ht, rfl⟩ := hu
      obtain ⟨a, ha⟩ := hex t ht
      have haR : a ∈ R.toSubmodule := by
        show i a ∈ T.toSubmodule
        rw [ha]; exact t.2
      refine ⟨⟨a, haR⟩, ?_⟩
      show f (j ⟨a, haR⟩) = f t
      congr 1
      exact Subtype.ext ha

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

open PiTensorProduct

theorem piTensor_isSubquotient_of_forall : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := by
  intro α _ _ Γ _ X Y _ _ _ _ ρ ρ' h
  choose S f hf using h
  let ι : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ') :=
    { toLinearMap := PiTensorProduct.map fun a => (S a).toSubmodule.subtype
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        rfl }
  let π : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ) :=
    { toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        congr 1
        funext a
        exact (f a).isIntertwining _ _ (g a) (x a) }
  have hι : Function.Injective ι := by
    choose r hr using fun a => LinearMap.exists_leftInverse_of_injective (S a).toSubmodule.subtype
      (S a).toSubmodule.ker_subtype
    have : (PiTensorProduct.map r) ∘ₗ (PiTensorProduct.map fun a => (S a).toSubmodule.subtype)
        = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hr]
      exact PiTensorProduct.map_id
    exact Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => LinearMap.congr_fun this z
  have hπ : Function.Surjective π := by
    show Function.Surjective (PiTensorProduct.map fun a => (f a).toLinearMap)
    rw [← LinearMap.range_eq_top]
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    choose y hy using fun a => hf a (x a)
    exact ⟨PiTensorProduct.tprod ℂ y, by
      show PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext a
      exact hy a⟩
  exact (IsSubquotient.of_surjective π hπ).trans (IsSubquotient.of_injective ι hι)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.EigenSubquot

open GlobalTheory.SmGL

theorem exists_irreducible_subquotient_eigen : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 →
    (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧
        ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  intro G _ V _ _ ρ S θ x hx hθ
  let S0 : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hS0 : ∀ (g : G) ⦃v : V⦄, v ∈ S0 → ρ g v ∈ S0 := by
    intro g v hv
    have : S0 ≤ S0.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩)
    exact this hv
  have hxS0 : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hgen : ∀ R : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ R → ρ g v ∈ R) → x ∈ R → S0 ≤ R := by
    intro R hR hxR
    exact Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hR h hxR)
  let P : Set (Submodule ℂ V) := {T | T ≤ S0 ∧ x ∉ T ∧ ∀ (g : G) ⦃v : V⦄, v ∈ T → ρ g v ∈ T}
  have hbot : (⊥ : Submodule ℂ V) ∈ P := ⟨bot_le, by simpa using hx, fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun hmem => ?_, fun g v hv => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hmem
      exact (hcP hz).2.1 hxz
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcP hz).2.2 g hvz⟩) ⊥ hbot
  obtain ⟨hTS, hxT, hTst⟩ := hT.prop
  let Sr : Subrepresentation ρ := ⟨S0, hS0⟩
  let Tr : Subrepresentation ρ := ⟨T, hTst⟩
  have hcov : Tr ⋖ Sr := by
    refine ⟨lt_of_le_of_ne (fun v hv => hTS hv) fun h => hxT ?_, fun R h1 h2 => ?_⟩
    · have : x ∈ Sr := hxS0
      rw [← h] at this
      exact this
    by_cases hxR : x ∈ R.toSubmodule
    · exact h2.not_ge fun v hv => hgen R.toSubmodule R.apply_mem_toSubmodule hxR hv
    · have hRP : R.toSubmodule ∈ P := ⟨fun v hv => h2.le hv, hxR, R.apply_mem_toSubmodule⟩
      have hle : T ≤ R.toSubmodule := fun v hv => h1.le hv
      exact h1.not_ge fun v hv => hT.2 hRP hle hv
  refine ⟨_, _, _, subQuot Sr Tr, isIrreducible_subQuot hcov,
    ⟨Sr, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩,
    Submodule.Quotient.mk ⟨x, hxS0⟩, ?_, fun g hg => ?_⟩
  · intro h0
    have h1 := (Submodule.Quotient.mk_eq_zero (T.comap S0.subtype) (x := (⟨x, hxS0⟩ : S0))).1 h0
    exact hxT h1
  · show Submodule.Quotient.mk (Sr.toRepresentation g ⟨x, hxS0⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hθ g hg)

end GlobalTheory.EigenSubquot
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.VecSubquot

theorem exists_irreducible_subquotient_of_ne_zero : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V), x ≠ 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (g : G) (c : ℂ), ρ g x = c • x → τ g y = c • y := by
  intro G V _ _ _ ρ x hx

  let s : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, ρ g v ∈ N) ∧ x ∉ N}
  have hbot : (⊥ : Submodule ℂ V) ∈ s := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], by simpa using hx⟩
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun hx' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcs hM).1 g v hvM)
    · obtain ⟨M, hM, hxM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hx'
      exact (hcs hM).2 hxM) ⊥ hbot
  obtain ⟨hNst, hxN⟩ := hmax.prop

  let O : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hOst : ∀ (g : G), ∀ v ∈ O, ρ g v ∈ O := by
    intro g v hv
    have : O.map (ρ g) ≤ O := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hxO : x ∈ O := Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
  let T : Subrepresentation ρ := ⟨N, fun g v hv => hNst g v hv⟩
  let S : Subrepresentation ρ := ⟨N ⊔ O, fun g v hv => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hNst g a ha) (hOst g b hb)⟩
  have hxS : x ∈ S.toSubmodule := Submodule.mem_sup_right hxO
  have hcov : T ⋖ S := by
    refine ⟨lt_of_le_of_ne (fun v hv => Submodule.mem_sup_left hv) fun h => hxN ?_, ?_⟩
    · have : x ∈ (S : Set V) := hxS
      rw [← h] at this
      exact this
    · intro T' h1 h2
      have hle : N ≤ T'.toSubmodule := h1.le
      have hxT' : x ∈ T'.toSubmodule := by
        by_contra hn
        have hmem : T'.toSubmodule ∈ s := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv, hn⟩
        have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hle) hle
        exact h1.ne (Subrepresentation.toSubmodule_injective heq.symm)
      have hST' : S.toSubmodule ≤ T'.toSubmodule := by
        refine sup_le hle ?_
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact T'.apply_mem_toSubmodule g hxT'
      exact h2.not_ge hST'
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot S T,
    Submodule.Quotient.mk (⟨x, hxS⟩ : S.toSubmodule), GlobalTheory.SmGL.isIrreducible_subQuot hcov,
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩, ?_, ?_⟩
  · intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact hxN h0
  · intro g c hgc
    show Submodule.Quotient.mk (S.toRepresentation g ⟨x, hxS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hgc

end GlobalTheory.VecSubquot
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjDense

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_of_agree : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, ξ u = μ (Units.map c.toMonoidHom u) := by
  intro L _ _ _ s c hc hci μ ξ hμ ⟨N, hN⟩ hglob d
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

end GlobalTheory.ConjDense
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.UnipRadProper

theorem blocks_lt_of_unipRad_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  intro k _ _ _ _ n s d e h a
  by_contra hle
  push_neg at hle
  apply h
  have hcard : ∑ b, d b = n := by simpa using (Fintype.card_congr e)
  have hzero : ∀ b, b ≠ a → d b = 0 := by
    intro b hb
    have h2 : d a + d b ≤ ∑ c, d c :=
      Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) (Ne.symm hb)
    omega
  have hblk : ∀ (b : Fin s) (j : Fin (d b)), b = a := by
    intro b j
    by_contra hb
    exact (hzero b hb ▸ j).elim0
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext i j
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  obtain rfl := hblk b i
  obtain rfl := hblk c j
  rw [(mem_unipRad.1 hg).2]
  simp [Matrix.one_apply]

end GlobalTheory.UnipRadProper
end

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp


end GlobalTheory.GalFirstClause
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) k) V) (β : Type) [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (j₀ : β) (ψ : kˣ →* ℂˣ), IsSmooth ρ → IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ) → InSupport (s j₀).ρ ψ → InSupport ρ ψ := by
  first | exact @GlobalTheory.SuppStage.main | exact GlobalTheory.SuppStage.main | (intros; apply GlobalTheory.SuppStage.main <;> assumption)
end
