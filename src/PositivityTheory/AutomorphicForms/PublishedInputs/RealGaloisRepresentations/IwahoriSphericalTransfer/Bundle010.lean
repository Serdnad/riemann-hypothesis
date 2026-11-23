module

public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsNormVEqPow
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle005
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal.TrInv

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω] [Normal F K]

def galoisConjugate (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (t : _root_.Formalism.ConjugateSelfDual.G K Ω) : _root_.Formalism.ConjugateSelfDual.G K Ω :=
  AlgEquiv.ofRingEquiv (f := ((g * res F Ω K t * g⁻¹ : _root_.Formalism.ConjugateSelfDual.G F Ω) : Ω ≃+* Ω)) (fun x => by
    obtain ⟨y, hy⟩ : ∃ y : K, (g⁻¹ : _root_.Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) = algebraMap K Ω y :=
      ⟨(g⁻¹ : _root_.Formalism.ConjugateSelfDual.G F Ω).restrictNormal K x, (AlgEquiv.restrictNormal_commutes _ K x).symm⟩
    change g ((res F Ω K t) ((g⁻¹ : _root_.Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x))) = algebraMap K Ω x
    rw [hy]
    change g (t (algebraMap K Ω y)) = algebraMap K Ω x
    rw [t.commutes, ← hy]
    change (g * g⁻¹) (algebraMap K Ω x) = _
    simp)

theorem restrict_galois_conjugate (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (t : _root_.Formalism.ConjugateSelfDual.G K Ω) : res F Ω K (galoisConjugate K g t) = g * res F Ω K t * g⁻¹ := by
  ext z; rfl

theorem galois_conjugate_apply (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (t : _root_.Formalism.ConjugateSelfDual.G K Ω) (z : Ω) : galoisConjugate K g t z = g (t (g⁻¹ z)) := rfl

def conj (g : _root_.Formalism.ConjugateSelfDual.G F Ω) : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G K Ω where
  toFun := galoisConjugate K g
  map_one' := by ext z; simp [galois_conjugate_apply]
  map_mul' s t := by ext z; simp [galois_conjugate_apply, AlgEquiv.mul_apply]

theorem res_conj (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (t : _root_.Formalism.ConjugateSelfDual.G K Ω) : res F Ω K (conj K g t) = g * res F Ω K t * g⁻¹ := restrict_galois_conjugate K g t

theorem conj_surjective (g : _root_.Formalism.ConjugateSelfDual.G F Ω) : Function.Surjective (conj K g) := by
  intro u
  refine ⟨conj K g⁻¹ u, ?_⟩
  ext z
  simp [conj, galois_conjugate_apply]

theorem res_injective : Function.Injective (res F Ω K) := AlgEquiv.restrictScalars_injective F

end GlobalTheory.RealGal.TrInv

end

noncomputable section

namespace GlobalTheory.RealGal.TrInv

theorem continuous_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [CharZero F] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] [Normal F K] (g : _root_.Formalism.ConjugateSelfDual.G F Ω) : Continuous (conj K g) := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := inferInstance
  haveI : T2Space (_root_.Formalism.ConjugateSelfDual.G F Ω) := krullTopology_t2
  have hc : Continuous (res F Ω K) := UpperTheory.V.Af.continuous_restrictScalarsHom F K Ω
  have he := hc.isClosedEmbedding (res_injective (F := F) (Ω := Ω) K)
  rw [he.isEmbedding.continuous_iff]
  have : (res F Ω K) ∘ (conj K g) = fun t => g * res F Ω K t * g⁻¹ := funext (res_conj K g)
  rw [this]
  exact (continuous_const.mul hc).mul continuous_const

theorem isSSRep_comp {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (r : Γ →* GL (Fin a) k) (c : Γ →* Γ)
    (hc : Function.Surjective c) (hr : IsSSRep r) : IsSSRep (r.comp c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro s v hv
    obtain ⟨t, rfl⟩ := hc s
    exact hW t v hv
  obtain ⟨W', h1, h2⟩ := hr W hW'
  exact ⟨W', fun t v hv => h1 (c t) v hv, h2⟩

end GlobalTheory.RealGal.TrInv

namespace GlobalTheory.RealGal


open TrInv in
theorem trace_conj_of_attRes : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r → AttRes π ι K r → ∀ (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (s s' : _root_.Formalism.ConjugateSelfDual.G K Ω), res F Ω K s' = g * res F Ω K s * g⁻¹ → ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ h2 l _ ι a π r hr hss hatt g s s' hs
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttRes π ι K (r.comp (conj K g)) :=
    GlobalTheory.T.attached_rep_conjugate_invariant F Ω K l ι a π r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := GlobalTheory.T.attached_galois_rep_unique F Ω K l ι a π r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp

end GlobalTheory.RealGal

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGalCompat

theorem mem_range_res_iff {K M Ω : Type} [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (x : _root_.Formalism.ConjugateSelfDual.G K Ω) :
    x ∈ (res K Ω M).range ↔ ∀ m : M, x (algebraMap M Ω m) = algebraMap M Ω m := by
  constructor
  · rintro ⟨y, rfl⟩ m
    exact y.commutes m
  · intro h
    refine ⟨{ x.toRingEquiv with commutes' := fun m => h m }, ?_⟩
    ext z
    rfl

theorem range_res_normal {F K M Ω : Type} [Field F] [Field K] [Field M] [Field Ω] [Algebra F K] [Algebra F M]
    [Algebra F Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower F K Ω] [IsScalarTower F M Ω]
    [IsScalarTower K M Ω] [Normal F M] : (res K Ω M).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_range_res_iff] at hn ⊢
  intro m
  obtain ⟨m', hm'⟩ : ∃ m' : M, algebraMap M Ω m' = g⁻¹ (algebraMap M Ω m) :=
    ⟨((AlgEquiv.restrictScalars F (g⁻¹ : _root_.Formalism.ConjugateSelfDual.G K Ω)).toAlgHom).restrictNormal M m,
      AlgHom.restrictNormal_commutes _ _ _⟩
  show g (n (g⁻¹ (algebraMap M Ω m))) = algebraMap M Ω m
  rw [← hm', hn m', hm', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end GlobalTheory.RealGalCompat

open GlobalTheory.RealGalCompat in
theorem GlobalTheory.RealGalCompat.trace_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : _root_.Formalism.ConjugateSelfDual.G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : _root_.Formalism.ConjugateSelfDual.G ↥Q'.K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι ↥Q.K r → AttRes π ι ↥Q'.K r' → ∀ (s : _root_.Formalism.ConjugateSelfDual.G ↥Q.K Ω) (s' : _root_.Formalism.ConjugateSelfDual.G ↥Q'.K Ω), res F Ω ↥Q.K s = res F Ω ↥Q'.K s' → ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ Q Q' l _ ι a π r r' hr hr' hs hs' ha ha' s s' hss
  let M : IntermediateField F Ω := Q.K ⊔ Q'.K
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [Q.two]; norm_num)
  haveI : FiniteDimensional F Q'.K := Module.finite_of_finrank_pos (by rw [Q'.two]; norm_num)
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F,
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩
  haveI : Algebra.IsQuadraticExtension F Q.K := { finrank_eq_two' := Q.two }
  haveI : Algebra.IsQuadraticExtension F Q'.K := { finrank_eq_two' := Q'.two }
  haveI : Normal F M := IntermediateField.normal_sup F Ω Q.K Q'.K
  letI : Algebra Q.K M := (IntermediateField.inclusion (le_sup_left : Q.K ≤ M)).toRingHom.toAlgebra
  letI : Algebra Q'.K M := (IntermediateField.inclusion (le_sup_right : Q'.K ≤ M)).toRingHom.toAlgebra
  haveI : IsScalarTower F Q.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower F Q'.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower Q'.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl

  have hA := GlobalTheory.T.galois_rep_tower_restriction F Ω Q.K M l ι a π r ha
  have hA' := GlobalTheory.T.galois_rep_tower_restriction F Ω Q'.K M l ι a π r' ha'
  have hS := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r (res Q.K Ω M) (range_res_normal (F := F)) hs
  have hS' := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r' (res Q'.K Ω M) (range_res_normal (F := F)) hs'
  have hC := hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q.K M Ω)
  have hC' := hr'.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q'.K M Ω)
  obtain ⟨g, hg⟩ := GlobalTheory.T.attached_galois_rep_unique F Ω M l ι a π _ _ hC hC' hS hS' hA hA'

  set σ : _root_.Formalism.ConjugateSelfDual.G F Ω := res F Ω Q.K s with hσ
  have hfix : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact s.commutes x
    · rw [hss]; exact s'.commutes x
  let t : _root_.Formalism.ConjugateSelfDual.G M Ω := IntermediateField.fixingSubgroupEquiv M ⟨σ, hfix⟩
  have ht : res Q.K Ω M t = s := by ext z; rfl
  have ht' : res Q'.K Ω M t = s' := by
    ext z
    exact congrArg (fun u : _root_.Formalism.ConjugateSelfDual.G F Ω => u z) hss
  have e := hg t
  simp only [MonoidHom.comp_apply, ht, ht'] at e
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]
end
