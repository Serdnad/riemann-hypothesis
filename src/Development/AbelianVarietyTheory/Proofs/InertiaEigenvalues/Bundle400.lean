module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle379
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle321
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ChiExtend

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem maximalIdeal_le_comap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {O₀ O₁ : Type}
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[p] O₀] [Module.Finite ℤ_[p] O₀]
    [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    (φ : O₀ →+* O₁) (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') :
    IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁) := by
  subst h
  have hc : φ.comp (algebraMap ℤ_[p] O₀) = algebraMap ℤ_[p] O₁ := by
    ext z
    exact hφ z z HEq.rfl
  haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (Ideal.comap (algebraMap ℤ_[p] O₀) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁))).IsMaximal := by
    rw [Ideal.comap_comap, hc]
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[p])
      (IsLocalRing.maximalIdeal O₁)
  have h2 := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := ℤ_[p]) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) h1
  rw [IsLocalRing.eq_maximalIdeal h2]

theorem continuous_of_le_comap {O₀ O₁ : Type} [CommRing O₀] [IsLocalRing O₀] [TopologicalSpace O₀]
    [IsTopologicalRing O₀] [CommRing O₁] [IsLocalRing O₁] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    (h₀ : IsAdic (IsLocalRing.maximalIdeal O₀)) (h₁ : IsAdic (IsLocalRing.maximalIdeal O₁))
    (φ : O₀ →+* O₁) (hφ : IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) :
    Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 h₁).2 s hs
  have ho := (isAdic_iff.1 h₀).1 n
  refine Filter.mem_map.2 <| Filter.mem_of_superset (ho.mem_nhds (Ideal.zero_mem _)) fun x hx => hn ?_
  exact (Ideal.pow_right_mono hφ n |>.trans (Ideal.le_comap_pow φ n)) hx

theorem cyc_heq (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q)
    (σ : G F Ω) : HEq ((cycZ F Ω p σ : ℤ_[p]ˣ) : ℤ_[p]) ((cycZ F Ω q σ : ℤ_[q]ˣ) : ℤ_[q]) := by
  subst h
  rfl

end GlobalTheory.ChiExtend

namespace GlobalTheory.ChiExtend

theorem iotaO_injective {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    Function.Injective (iotaO N A i) := by
  show Function.Injective (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).comp (algebraMap (N.O i) (FractionRing (N.O i))))
  simp only [RingHom.coe_comp]
  exact (A.iotaQC i).injective.comp ((A.iotaQ i).injective.comp (IsFractionRing.injective _ _))

theorem eq_of_dense {X O : Type*} [TopologicalSpace X] [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) (hH : IsHausdorff (IsLocalRing.maximalIdeal O) O)
    {f g : X → O} (hf : Continuous f) (hg : Continuous g) {s : Set X} (hs : Dense s) (he : ∀ x ∈ s, f x = g x) :
    f = g := by
  funext x
  rw [← sub_eq_zero]
  apply hH.haus' (f x - g x)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  have hcl : IsClosed ((fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)) := by
    refine IsClosed.preimage (hf.sub hg) ?_
    exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ n).toAddSubgroup
      ((isAdic_iff.1 h).1 n)
  have hsub : s ⊆ (fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
    intro y hy
    simp only [Set.mem_preimage, he y hy, sub_self, SetLike.mem_coe]
    exact Ideal.zero_mem _
  have := closure_minimal hsub hcl
  rw [hs.closure_eq] at this
  exact this (Set.mem_univ x)

end GlobalTheory.ChiExtend

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.Proof.CoefField

theorem exists_coefField {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ K : IntermediateField ℚ_[l] (Qbar l), (∀ z, z ∈ K ↔ ∃ x, ι x = z) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ x : FractionRing O, ‖ι x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let φ : O →+* Qbar l := ι.comp (algebraMap O (FractionRing O))
  have hφ : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hι
  have hQ : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Qbar l) q ∈ ι.fieldRange := by
    intro q
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    rw [map_div₀]
    refine div_mem ?_ ?_
    · exact ⟨_, hι a⟩
    · exact ⟨_, hι b⟩
  let K : IntermediateField ℚ_[l] (Qbar l) := ι.fieldRange.toIntermediateField hQ
  have hK : ∀ z, z ∈ K ↔ ∃ x, ι x = z := fun z => Iff.rfl
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  let S : Set (Qbar l) := φ '' (s : Set O)
  have hint : ∀ x ∈ S, IsIntegral ℚ_[l] x := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨p, hp, hy⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] ℚ_[l]), hp.map _, ?_⟩
    have := congrArg φ hy
    rw [map_zero, Polynomial.hom_eval₂] at this
    have e : (algebraMap ℚ_[l] (Qbar l)).comp (algebraMap ℤ_[l] ℚ_[l]) = φ.comp (algebraMap ℤ_[l] O) :=
      RingHom.ext fun z => (hφ z).symm
    rw [Polynomial.eval₂_map, e]
    exact this
  have : Finite S := (s.finite_toSet.image φ).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : K ≤ IntermediateField.adjoin ℚ_[l] S := by
    have hO : ∀ y : O, φ y ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro y
      have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Algebra.smul_def, map_mul, hφ]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀]
    exact div_mem (hO a) (hO b)
  refine ⟨K, hK, ?_, fun x => (GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι x).symm⟩
  have hge : IntermediateField.adjoin ℚ_[l] S ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have heq : K = IntermediateField.adjoin ℚ_[l] S := le_antisymm hle hge
  rw [heq]
  exact hfd

theorem coefField_range : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), ∃ K : IntermediateField ℚ_[N.l i] (Qbar (N.l i)), (∀ z, z ∈ K ↔ ∃ x, A.iotaQ i x = z) ∧ FiniteDimensional ℚ_[N.l i] K ∧ ∀ x : FractionRing (N.O i), ‖A.iotaQ i x‖ ≤ 1 ↔ x ∈ (algebraMap (N.O i) (FractionRing (N.O i))).range := by
  intro R H what₂ N A i
  exact exists_coefField (A.iotaQ i) (A.iotaQ_alg i)

end GlobalTheory.Proof.CoefField

end
end

section

noncomputable section

namespace GlobalTheory.DeRhamSplit

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finrank_split [inst : Fintype (K →ₐ[Qp] LL)]
    (hcard : Fintype.card (K →ₐ[Qp] LL) = Module.finrank Qp K)
    (ρ : Representation LL G V) [Module.Finite LL (DdR PD ρ)] :
    Module.finrank LL (DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (DdRE PD ρ τ) ∧
      ∀ a : ℤ, Module.finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
        ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (FildR PD ρ τ a) := by
  haveI := PD.finK
  obtain rfl : inst = minpoly.AlgHom.fintype Qp K LL := Subsingleton.elim _ _
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hst : ∀ c, ∀ x ∈ DdR PD ρ, m c x ∈ DdR PD ρ := fun c x hx =>
    (hD _).2 fun g => by rw [hc, (hD x).1 hx g]
  have hF : ∀ a c, ∀ x ∈ FilV PD (LL := LL) (V := V) a, m c x ∈ FilV PD (LL := LL) (V := V) a := by
    rintro a c _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      refine ⟨v ⊗ₜ ⟨c • (b : BdR), (PD.Fil a).smul_mem c b.2⟩, ?_⟩
      change v ⊗ₜ (c • (b : BdR)) = v ⊗ₜ (algebraMap K BdR c * (b : BdR))
      rw [Algebra.smul_def]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz
  have hE : ∀ (τ : K →ₐ[Qp] LL) x, x ∈ DdRE PD ρ τ ↔ x ∈ DdR PD ρ ∧ ∀ c, m c x = τ c • x := fun τ x => by
    simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  refine ⟨GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ) hst (DdRE PD ρ) hE, fun a => ?_⟩
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (FildR PD ρ τ a) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  refine GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨hst c x hx.1, hF a c x hx.2⟩)
    (fun τ => FildR PD ρ τ a) fun τ x => ?_
  simp only [FildR, Submodule.mem_inf, hE]
  tauto

end General

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), Module.Finite ↥LL.1 ↥(DdR (P.PD K) ρ) → Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ ∀ a : ℤ, Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  intro l _ P K LL _ hs V _ _ _ _ ρ hfin
  exact finrank_split (P.PD K) hs.2 ρ

end GlobalTheory.DeRhamSplit
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_frobenius_gen_degree_hom_to_Zl : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧ ν F = Multiplicative.ofAdd 1 ∧ (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  first | exact @GlobalTheory.UnramGen.exists_gen_degree | exact GlobalTheory.UnramGen.exists_gen_degree | (intros; apply GlobalTheory.UnramGen.exists_gen_degree <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem finrank_Ks_eq : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ), 0 < s → finrank ℚ_[l] ↥(Loc.Ks K s) = finrank ℚ_[l] ↥(Loc.K0 K) * (l ^ (s - 1) * (l - 1)) := by
  intro l _ K s hs
  rw [GlobalTheory.Cyc.finrank_Ks K s hs, mul_comm (l - 1)]

end GlobalTheory.HubLoc
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmissibleDictionary

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  exact GlobalTheory.TameFixedLift.main D.nd i

end GlobalTheory.AdmissibleDictionary
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.admissible_shape_and_epsilon_at_every_localisation

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  refine ⟨fun w hw => ?_, GlobalTheory.TameFixedLift.main D.nd i⟩
  exact UpperTheory.KStar.Cyc.kw_le_roots D.host.toHostRaw (D.nbr i w hw)

end GlobalTheory.admissible_shape_and_epsilon_at_every_localisation
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.theoremB_localDegree_sum_bounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  first | exact @GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge | exact GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge | (intros; apply GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.theoremB_ramifiedPrimes_ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  first | exact @GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes | exact GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes | (intros; apply GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.GoodLiftPoint

theorem good_of_lift : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  intro D h42 i σ P x hg hth hpt
  have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro h
    apply hth.1
    rw [h, Submodule.map_bot]
  obtain ⟨Sig, hW, hBC⟩ := (h42 i σ hne).2.1
  have hX : HasParamX D.nd D.naut i x Sig := ⟨P, hpt, hBC P hth⟩
  have hZ : x ∈ ZN D.nd D.naut i := by
    refine ⟨P, hpt, _, hBC P hth, ?_⟩
    unfold twistIso
    exact List.mem_map.2 ⟨muPart D.nd D.naut i, by simp, rfl⟩
  have hgood : x ∈ ZgoodN D.nd D.naut i :=
    ⟨hZ, Sig, hX, (GlobalTheory.LabelCompat.labCompat D i σ Sig hW).1 hg⟩
  exact ⟨hgood, GlobalTheory.LiftLeaf.atMOfParam D i x hgood Sig hX σ hW⟩

end GlobalTheory.GoodLiftPoint
end

section


theorem _root_.GlobalTheory.T.local_cohomology_seven_elementary_facts : ReciprocityTheory.ChartRestriction.T2.Elem := by
  first | exact @GlobalTheory.LocElem.elem | exact GlobalTheory.LocElem.elem | (intros; apply GlobalTheory.LocElem.elem <;> assumption)
end
