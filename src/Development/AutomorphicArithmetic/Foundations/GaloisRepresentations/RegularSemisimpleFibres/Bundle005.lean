module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle040
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll
public import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle022
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.stepSplit :
    StableOf → ResEmbCompat → LblIso → ∀ P₀, StepAt P₀ id := by
  intro hS hC hI P₀ K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp n hn π P hW A Θ hΘ v w hsplit hunr e e' he he' τ τ' hτ hτ' a hP ha
  refine ⟨a, Relation.ReflTransGen.refl, ?_⟩
  obtain ⟨-, hSL⟩ := hS K M hp n hn π P hW
  obtain ⟨r, j, h1, h2, h3⟩ := hC K M Ω A v w e e' he he'
  have hs : UpperTheory.ConvolutionTheory.GM.Split M v := hsplit
  let i : v.adicCompletion K ≃+* w.1.adicCompletion M :=
    RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs w⟩
  have hi : ∀ x, i x = completionMap v w.1 x := fun _ => rfl
  have hic : Continuous i := continuous_completionMap v w.1
  have hal : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x) := fun x => by
    rw [hi, completionMap_algebraMap, IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M)]
  obtain ⟨f, hf⟩ := hSL v w.1 i hic hal τ τ' hτ hτ'
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 K) w.1.asIdeal).ne'
  have hle : ∀ x y : w.1.adicCompletion M, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion M)) Valued.v x y
  have hle' : ∀ x y : v.adicCompletion K, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v x y
  have hv : ∀ x : v.adicCompletion K, valuation _ (i x) ≤ 1 ↔ valuation _ x ≤ 1 := fun x => by
    have a1 := hle (i x) (i 1)
    have a2 := hle' x 1
    rw [map_one (valuation (v.adicCompletion K))] at a2
    rw [map_one i, map_one (valuation (w.1.adicCompletion M))] at a1
    rw [a1, a2, ← map_one i, hi, hi, valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0
  have hcond : ∀ (x : 𝒪[v.adicCompletion K]) (y : 𝒪[w.1.adicCompletion M]), (y : w.1.adicCompletion M) = i x →
      j (algebraMap _ _ (IsLocalRing.residue _ x)) = algebraMap _ _ (IsLocalRing.residue _ y) :=
    fun x y hy => by rw [h2, h1 x y hy]
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom :=
    MonoidHom.ext fun x => congrArg Θ (h3 x)
  exact hI _ _ i hv j hcond (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ f hf a (by rw [hθ]; exact ha)
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.tameChars :
    TameChars := by
  intro k _ _ _ _ N V _ _ π ω h
  obtain ⟨μ, hμ, H⟩ := h
  have hs : ∀ j, IsSmoothChar (μ j) := fun j => isSmoothChar_of_isTame (hμ j).isTame
  refine ⟨μ, hs, fun j u hu => ?_, ?_, fun j u => hμ j u⟩
  · exact (hμ j).isTame u hu
  · have := hasSupport_of_isCuspSupport H
    exact this
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unifTower :
    LiftsFix → PlaceEx → UnrOfIne → UnifTower := by
  intro hF hP hU E Ω _ _ _ n X Y hXY
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro A _ v w hv hw g hg
    have hvw : v = w := by
      apply HeightOneSpectrum.ext
      ext x
      rw [← hv x, hw x]
    rw [← hvw]
    exact hg
  | @head X Z hs hZY ih =>
    intro A hI v w hv hw g hg
    obtain ⟨_, _, _, _, _⟩ := hs
    obtain ⟨u, hu, -⟩ := hP X.K Z.K Ω A v hv n Z.π
    have hfix : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht z
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY z
      have := hI t ht y
      rwa [hy] at this
    have hgu : ((g : ℕ) : 𝓞 Z.K) ∉ u.asIdeal ^ 2 := by
      have h3 := (hU X.K Z.K Ω A v u hv hu hfix).2.2 (g : 𝓞 X.K) hg
      rwa [map_natCast] at h3
    refine ih A (fun t ht => ?_) u w hu hw g hgu
    exact hI (AlgEquiv.restrictScalars X.K t) ht
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_map_eq_prod {s : ℕ} {W : Fin s → Type} [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] [∀ a, FiniteDimensional ℂ (W a)] (f : ∀ a, W a →ₗ[ℂ] W a) :
    LinearMap.trace ℂ (PiTensorProduct ℂ W) (PiTensorProduct.map f) =
      ∏ a, LinearMap.trace ℂ (W a) (f a) := by
  let b := fun a => Module.finBasis ℂ (W a)
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ a, LinearMap.trace ℂ (W a) (f a) = ∑ j, (b a).repr (f a (b a j)) j := by
    intro a
    rw [LinearMap.trace_eq_matrix_trace ℂ (b a), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem UpperTheory.Gal.InertialTypesAlt.tensTr :
    TensTr := by
  intro s Γ W _ _ _ _ κ
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun a => Module.finBasis ℂ (W a)), fun x => ?_⟩
  exact trace_map_eq_prod fun a => κ a (x a)
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sum_ne_iff {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (κ : Representation ℂ H W) :
    (∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0) ↔
      ∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (κ g x) = ρ g (f x) := by
  classical
  haveI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank κ ρ
  have hsum : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g * κ.character g⁻¹ :=
    Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hc : (Nat.card H : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hsum]
  constructor
  · intro h
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at key
      exact h ((mul_eq_zero.mp key).resolve_left hc)
    haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hpos)
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Representation.IntertwiningMap κ ρ)
    refine ⟨φ.toLinearMap, ?_, fun g x => Representation.IntertwiningMap.isIntertwining κ ρ φ g x⟩
    intro h0
    exact hφ (Representation.IntertwiningMap.ext (by simpa using h0))
  · rintro ⟨f, hf0, hf⟩
    let φ := f.intertwiningMap_of_isIntertwiningMap κ ρ hf
    have hφ : φ ≠ 0 := by
      intro h0
      apply hf0
      ext x
      have := congrArg (fun ψ : Representation.IntertwiningMap κ ρ => ψ x) h0
      simpa [φ] using this
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      rw [← (Representation.invariantsEquivIntertwiningMap κ ρ).finrank_eq]
      apply Nat.pos_iff_ne_zero.mp
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨(Representation.invariantsEquivIntertwiningMap κ ρ).symm φ, ?_⟩
      simpa using hφ
    intro hs
    rw [hs, mul_zero] at key
    exact hpos (by exact_mod_cast key.symm)

theorem UpperTheory.Gal.InertialTypesAlt.meetsIff :
    MeetsIff := by
  intro H V W _ _ _ _ _ _ _ _ ρ κ
  classical
  haveI := Fintype.ofFinite H
  have hstar : ∀ g : H, star (LinearMap.trace ℂ W (κ g)) = κ.character g⁻¹ := by
    intro g
    have hmem : (fun g => algebraMap ℂ ℂ (κ.character g)) ∈ GlobalTheory.BI.Virt ℂ ℂ H :=
      AddSubgroup.subset_closure (GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ H W κ).1
    have := GlobalTheory.T.star_virtualCharacter_eq_apply_inv H _ hmem g
    change star (κ.character g) = _
    simpa using this
  have hM : Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔
      ∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0 := by
    unfold Meets
    rw [finsum_eq_sum_of_fintype]
    simp only [hstar]
    rfl
  have hswap : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g⁻¹ * κ.character g :=
    Fintype.sum_equiv (Equiv.inv H) _ _ fun g => by simp [mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hM, hswap]
    exact sum_ne_iff κ ρ
  · rw [hM]
    exact sum_ne_iff ρ κ
end

section

noncomputable section

open GlobalTheory.SmGL GlobalTheory.Shin GlobalTheory.SplitWeil

namespace UpperTheory.Gal.InertialTypesAlt

private theorem blk_two {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i : Fin m) :
    (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i = 0 ↔ (i : ℕ) < a) := by
  obtain ⟨⟨b, j⟩, hbj⟩ : ∃ p, (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd).symm i = p := ⟨_, rfl⟩
  have hi := stdBlocks_val (![a, m - a] : Fin 2 → ℕ) hd b j
  rw [← hbj, Equiv.apply_symm_apply] at hi
  unfold blk
  rw [hbj]
  have hj := j.isLt
  fin_cases b
  · simp at hi hj ⊢
    omega
  · simp at hi hj ⊢
    omega

private theorem blk_lt_iff {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i j : Fin m) :
    blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i < blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j ↔
      (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  have hi := blk_two ha hd i
  have hj := blk_two ha hd j
  have h1 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i).isLt
  have h2 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j).isLt
  rw [Fin.lt_iff_val_lt_val]
  rw [Fin.ext_iff, Fin.val_zero] at hi hj
  omega

private theorem rad_le {F : Type} [Field F] {m a : ℕ} (h0 : 0 < a) (ha : a < m) (H : Subgroup (GL (Fin m) F))
    (hH : (H : Set (GL (Fin m) F)) = {u : GL (Fin m) F | ∀ i j : Fin m, (u : Matrix (Fin m) (Fin m) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)})
    (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (u : GL (Fin m) F)
    (hu : u ∈ unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd)) : u ∈ H := by
  have hu' := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.mp hu
  have hmem : u ∈ (H : Set (GL (Fin m) F)) := by
    rw [hH]
    intro i j
    by_cases h : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr h
    · left
      rw [hu' i j (by rwa [blk_lt_iff ha hd])]
      simp [Matrix.one_apply]
  exact hmem

theorem cuspChar : CuspChar := by
  intro F _ _ θ hθ m hm W _ _ _ κ hirr hcusp
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hc := GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ (GL (Fin m) F) W κ
  have hprim : GlobalTheory.CuspGL.IsPrimitive
      (GlobalTheory.CuspGL.extZero (fun g : GL (Fin m) F => algebraMap ℂ ℂ (κ.character g))) := by
    refine GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F m _ hc.1 fun a h0 ham => ?_
    obtain ⟨A, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F m a ham.le
    have hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m := by
      simp [Fin.sum_univ_two]
      omega
    have hne : unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) ≠ ⊥ := by
      rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
      refine ⟨⟨0, hm⟩, ⟨a, ham⟩, ?_⟩
      rw [blk_lt_iff ham hd]
      exact ⟨h0, le_refl a⟩
    have hfix : ∀ v : W, (∀ u ∈ H, κ u v = v) → v = 0 := fun v hv =>
      hcusp 2 _ _ hne v fun u hu => hv u (rad_le h0 ham H hH hd u hu)
    have hz := PositivityTheory.GreenCharacters.sum_char_eq_zero κ H hfix
    rw [← hH, finsum_mem_def, finsum_eq_sum_of_fintype]
    rw [← hz]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H <;> simp [Set.indicator_apply, hu]
  obtain ⟨k, hk, hx⟩ := GlobalTheory.CuspFormula.exists_regular F θ hθ m hm _ (hc.2 hirr) hprim
  refine ⟨k, hk, fun x => ?_⟩
  have := hx x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

end UpperTheory.Gal.InertialTypesAlt
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons' {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b n : ℕ) (h : (Y.map Sigma.fst).sum = b) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h; rfl

private theorem sum_fst_map {F : Type} [Field F] (f : ℕ × ℕ → (Σ m : ℕ, GL (Fin m) F → ℂ))
    (hf : ∀ p, (f p).1 = p.1) (L : List (ℕ × ℕ)) :
    ((L.map f).map Sigma.fst).sum = deg L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, ih, hf]
    rfl

private theorem J_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) :
    ∀ n, J θ L n = hcL (L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction L with
  | nil => intro n; rfl
  | cons p L ih =>
    intro n
    rw [J_cons, List.map_cons, hcL_cons' _ _ (deg L) n (sum_fst_map _ (fun _ => rfl) L), ih]

private theorem JD_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (D L : List (ℕ × ℕ)) :
    ∀ n, JD θ D L n =
      hcL (D.map (fun p => ⟨p.1, detc θ p.1 p.2⟩) ++ L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction D with
  | nil => intro n; simpa [JD_nil] using J_eq θ L n
  | cons p D ih =>
    intro n
    have hs : (((D.map (fun p : ℕ × ℕ => (⟨p.1, detc θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))) ++
        L.map (fun p : ℕ × ℕ => (⟨p.1, cusp θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).map Sigma.fst).sum =
        deg D + deg L := by
      rw [List.map_append, List.sum_append, sum_fst_map _ (fun _ => rfl) D, sum_fst_map _ (fun _ => rfl) L]
    rw [JD_cons, List.map_cons, List.cons_append, hcL_cons' _ _ (deg D + deg L) n hs, ih]

private theorem cusp_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) :
    cusp θ 1 k = detc θ 1 k := by
  haveI : Fintype F := Fintype.ofFinite F
  funext x
  have hcp : Matrix.charpoly (x : Matrix (Fin 1) (Fin 1) F) = X - C ((x : Matrix (Fin 1) (Fin 1) F) 0 0) := by
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin 1 → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
    (Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F))
    (by rw [Matrix.charpoly_toLin', hcp]; exact irreducible_X_sub_C _)
  rw [Matrix.charpoly_toLin', hcp] at hval
  simp only [cusp, psiG, detc, Nat.sub_self, pow_zero, one_mul]
  rw [hval, Matrix.det_fin_one]
  simp [GlobalTheory.CuspGL.rootSum]

theorem UpperTheory.Gal.InertialTypesAlt.jdEq :
    JDEq := by
  intro F _ _ θ
  refine ⟨fun D L n => JD_eq θ D L n, cusp_one θ, ?_⟩
  intro D L n
  cases D with
  | nil =>
    cases L with
    | nil => intro x y; rfl
    | cons p L => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
  | cons p D => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TameReduction

section Res

variable {Ω : Type} [Field Ω]

private noncomputable def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem residue_eq_toRes {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    (z : A) (x : 𝓞 F) (h : A.valuation ((z : Ω) - algebraMap F Ω (x : F)) < 1) :
    IsLocalRing.residue A z = toRes A F x := by
  unfold toRes
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 h

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : UpperTheory.Zero.LLC.Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

end UpperTheory.Gal.InertialTypesAlt.TameReduction

open UpperTheory.Gal.InertialTypesAlt.TameReduction in
theorem UpperTheory.Gal.InertialTypesAlt.tameRead :
    TameRead := by
  intro E Ω _ _ _ _ _ A v h g _ m hm D R hR
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  refine ⟨ι, fun t ϖ hϖ z hz => ?_⟩
  obtain ⟨t', x, ht, hx, hr⟩ := res_read hm D R hR t
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g m hm D.card
  have h1 := UpperTheory.Zero.LLC.tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' ϖ (by rw [D.card]; exact hϖ) t' x hx
  rw [hr, hι]
  refine (residue_eq_toRes z x ?_).symm
  rw [hz, ht]
  exact h1
end
