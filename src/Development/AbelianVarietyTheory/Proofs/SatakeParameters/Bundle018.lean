module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

noncomputable section
namespace GlobalTheory.LatHecke

def coordIncl (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) :
    (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.pi fun i => (Algebra.linearMap O K).comp (LinearMap.proj i)

theorem coordIncl_apply {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} (x : Fin r → O) :
    coordIncl O K r x = fun i => algebraMap O K (x i) := rfl

theorem coordIncl_injective {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] {r : ℕ} : Function.Injective (coordIncl O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

theorem std_eq_map_top (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (r : ℕ) :
    (std O K r).1 = (⊤ : Submodule O (Fin r → O)).map (coordIncl O K r) := by
  rw [← (Pi.basisFun O (Fin r)).span_eq, Submodule.map_span, ← Set.range_comp]
  show Submodule.span O (Set.range (Pi.basisFun K (Fin r))) = _
  congr 2
  funext i
  funext j
  simp [coordIncl_apply, Pi.single_apply]

theorem glMap_std_eq {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K)
    (hg : (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K)) :
    glMap g (std O K r).1 = (LinearMap.range A.mulVecLin).map (coordIncl O K r) := by
  rw [glMap, std_eq_map_top, ← Submodule.map_comp, LinearMap.range_eq_map,
    ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply, coordIncl_apply, hg]
  funext i
  exact (RingHom.map_mulVec (algebraMap O K) A x i).symm

end GlobalTheory.LatHecke


open GlobalTheory.LatHecke in
theorem GlobalTheory.LatHecke.relIndex_glMap_std_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  intro O K _ _ _ _ _ _ r A g hg
  rw [glMap_std_eq A g hg, std_eq_map_top]
  refine ⟨?_, ?_⟩
  · have h := AddSubgroup.relIndex_map_map_of_injective (f := (coordIncl O K r).toAddMonoidHom)
      (LinearMap.range A.mulVecLin).toAddSubgroup (⊤ : Submodule O (Fin r → O)).toAddSubgroup
      coordIncl_injective
    refine h.trans ?_
    rw [Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    rfl
  · intro h
    rw [← Submodule.map_smul''] at h
    exact (Submodule.map_le_map_iff_of_injective coordIncl_injective _ _).1 h
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.LatHecke

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem mem_std_of_coord {x : Fin r → K} (hx : ∀ i, ∃ a : O, algebraMap O K a = x i) :
    x ∈ (std O K r).1 := by
  choose a ha using hx
  have hsum : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
    ext j
    simp [Finset.sum_apply, Algebra.smul_def, Pi.single_apply, ha]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem entry_of_glMap_std_le {g : GL (Fin r) K} (h : glMap g (std O K r).1 ≤ (std O K r).1)
    (i j : Fin r) : ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j := by
  have hmem : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) (Pi.basisFun K (Fin r) j) ∈
      glMap g (std O K r).1 :=
    ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  obtain ⟨a, ha⟩ := coord_of_mem_std (h hmem) i
  exact ⟨a, by simpa [Matrix.toLin'_apply] using ha⟩

theorem glMap_std_le_of_entry {g : GL (Fin r) K}
    (h : ∀ i j, ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j) :
    glMap g (std O K r).1 ≤ (std O K r).1 := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_std_of_coord fun i => ?_
  choose a ha using h
  choose b hb using coord_of_mem_std hx
  refine ⟨∑ j, a i j * b j, ?_⟩
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, ha, hb]

theorem glMap_std_eq_iff_entry (g : GL (Fin r) K) :
    glMap g (std O K r).1 = (std O K r).1 ↔
      (∀ i j, ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j) ∧
      (∀ i j, ∃ a : O, algebraMap O K a = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j) := by
  constructor
  · intro h
    have h' : glMap g⁻¹ (std O K r).1 = (std O K r).1 := by
      have := congrArg (glMap g⁻¹) h
      rw [← glMap_mul, inv_mul_cancel, glMap_one] at this
      exact this.symm
    exact ⟨entry_of_glMap_std_le h.le, entry_of_glMap_std_le h'.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (glMap_std_le_of_entry h1) ?_
    have := Submodule.map_mono (f := (Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O)
      (glMap_std_le_of_entry h2)
    have e : glMap g (glMap g⁻¹ (std O K r).1) = (std O K r).1 := by
      rw [← glMap_mul, mul_inv_cancel, glMap_one]
    exact e.ge.trans this

end Dvr

section Sub

variable {L : Type} [Field L] {n : ℕ}

theorem mem_GLint_iff_entry (S : Subring L) (g : GL (Fin n) L) :
    g ∈ GLint (Fin n) S ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ S) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ S) := by
  constructor
  · have key : ∀ u : GL (Fin n) S, ∀ i j,
        ((bc (n := Fin n) S.subtype u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ S :=
      fun u i j => ((u : Matrix (Fin n) (Fin n) S) i j).2
    rintro ⟨u, rfl⟩
    refine ⟨key u, ?_⟩
    rw [← map_inv]
    exact key u⁻¹
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix S.subtype :
        Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) L) :=
      Matrix.map_injective Subtype.val_injective
    have hM : RingHom.mapMatrix S.subtype M = (g : Matrix (Fin n) (Fin n) L) := by
      ext i j; rfl
    have hN : RingHom.mapMatrix S.subtype N = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      ext i j; rfl
    refine ⟨⟨M, N, hinj ?_, hinj ?_⟩, Units.ext hM⟩
    · rw [map_mul, hM, hN, map_one]; exact Units.mul_inv g
    · rw [map_mul, hM, hN, map_one]; exact Units.inv_mul g

end Sub

theorem glMap_std_eq_iff_mem_GLint (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      g ∈ GLint (Fin n) (Ov E w) := by
  rw [glMap_std_eq_iff_entry, mem_GLint_iff_entry]
  have key : ∀ x : w.adicCompletion E,
      (∃ a : w.adicCompletionIntegers E,
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a = x) ↔ x ∈ Ov E w :=
    fun x => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simp only [key]

end GlobalTheory.LatHecke
end
end

section

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

namespace GlobalTheory.IdxRank

theorem mem_smul_top_of_forall_mem {O : Type} [CommRing O] (I : Ideal O) {r : ℕ}
    (z : Fin r → O) (hz : ∀ i, z i ∈ I) : z ∈ I • (⊤ : Submodule O (Fin r → O)) := by
  have h : z = ∑ i, z i • (Pi.single i (1 : O) : Fin r → O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) trivial

theorem card_quot_range (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O)
    (hA : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤
      LinearMap.range A.mulVecLin) :
    Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) =
      qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  classical
  set F := IsLocalRing.ResidueField O with hF
  set res : O →+* F := IsLocalRing.residue O with hres
  set Ab : Matrix (Fin r) (Fin r) F := A.map res with hAb
  set R : Submodule F (Fin r → F) := LinearMap.range Ab.mulVecLin with hR
  let π : (Fin r → O) →ₗ[O] (Fin r → F) := (Algebra.linearMap O F).compLeft (Fin r)
  have hπ : ∀ x i, π x i = res (x i) := fun x i => rfl
  have hπs : Function.Surjective π := by
    intro y
    refine ⟨fun i => (IsLocalRing.residue_surjective (y i)).choose, ?_⟩
    ext i
    exact (IsLocalRing.residue_surjective (y i)).choose_spec
  have hπA : ∀ x, π (A.mulVec x) = Ab.mulVec (π x) := by
    intro x
    ext i
    have h2 : π x = res ∘ x := rfl
    rw [h2, hπ]
    exact RingHom.map_mulVec res A x i
  let φ : (Fin r → O) →ₗ[O] ((Fin r → F) ⧸ R) := (R.mkQ.restrictScalars O).comp π
  have hφs : Function.Surjective φ :=
    (Submodule.mkQ_surjective R).comp hπs
  have hker : LinearMap.ker φ = LinearMap.range A.mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : π x ∈ R := by
        have : R.mkQ (π x) = 0 := hx
        simpa using this
      obtain ⟨y, hy⟩ := hx'
      obtain ⟨y', rfl⟩ := hπs y
      have hy2 : π (A.mulVec y') = π x := by
        rw [hπA]; exact hy
      have hz : x - A.mulVec y' ∈ LinearMap.range A.mulVecLin := by
        apply hA
        apply mem_smul_top_of_forall_mem
        intro i
        have h1 : π (x - A.mulVec y') i = 0 := by
          rw [map_sub, hy2, sub_self]; rfl
        rw [hπ] at h1
        exact (IsLocalRing.residue_eq_zero_iff _).1 h1
      have : x = (x - A.mulVec y') + A.mulVecLin y' := by
        simp
      rw [this]
      exact Submodule.add_mem _ hz ⟨y', rfl⟩
    · rintro ⟨y, rfl⟩
      show R.mkQ (π (A.mulVec y)) = 0
      rw [hπA]
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨π y, rfl⟩
  have e : ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≃ ((Fin r → F) ⧸ R) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hφs)).toEquiv
  rw [Nat.card_congr e]
  have hfin : Module.finrank F ((Fin r → F) ⧸ R) + Module.finrank F R = r := by
    have := Submodule.finrank_quotient_add_finrank R
    simpa using this
  have hrank : Ab.rank = Module.finrank F R := (Matrix.finrank_range_mulVecLin Ab).symm
  have hdim : Module.finrank F ((Fin r → F) ⧸ R) = r - Ab.rank := by
    omega
  have : Finite ((Fin r → F) ⧸ R) := Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
  rw [Module.natCard_eq_pow_finrank (K := F), hdim]
  rfl

end GlobalTheory.IdxRank
end

section

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  first | (exact @GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (exact GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (intros; apply GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f], IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ), GlobalTheory.EtC.Tr.FibrePointsLE f (n + 1) → GlobalTheory.EtC.Tr.FibrePointsLE (GlobalTheory.EtC.Tr.diagComplHom f) n := by
  first | (exact @GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (exact GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (intros; apply GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X], ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  first | (exact @GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (exact GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (intros; apply GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine  <;> assumption)
end

section

open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem gam_quot_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  intro L _ _ ϖ σ hϖ hR r e
  classical
  have hle1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  set K : ℕ := ∑ k, ∑ j, (e k + e j) with hK
  obtain ⟨R, -, hRc⟩ := hR K
  have hKge : ∀ k j, e k + e j ≤ K := by
    intro k j
    have h1 : e k + e j ≤ ∑ j', (e k + e j') :=
      Finset.single_le_sum (f := fun j' => e k + e j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j', (e k + e j') ≤ ∑ k', ∑ j', (e k' + e j') :=
      Finset.single_le_sum (f := fun k' => ∑ j', (e k' + e j')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    exact h1.trans h2
  have hint : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, (Γ : Matrix (Fin r) (Fin r) L) k j ∈ Formalism.UG.intL L := by
    intro Γ k j
    show Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j) ≤ 1
    exact (Γ.2.2 k j).trans (pow_le_one' hle1 _)
  have hch : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, ∃ x ∈ R, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - x) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => hRc _ (hint Γ k j)
  let g : ↥(gam σ ϖ e) → (Fin r → Fin r → ↥R) := fun Γ k j => ⟨(hch Γ k j).choose, (hch Γ k j).choose_spec.1⟩
  have hg : ∀ (Γ : ↥(gam σ ϖ e)) k j, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - (g Γ k j : L)) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => (hch Γ k j).choose_spec.2
  let h : (↥(gam σ ϖ e) ⧸ (gam0 σ ϖ e).addSubgroupOf (gam σ ϖ e)) → (Fin r → Fin r → ↥R) :=
    fun q => g (Quotient.out q)
  have hinj : Function.Injective h := by
    intro q1 q2 hq
    rw [← QuotientAddGroup.out_eq' q1, ← QuotientAddGroup.out_eq' q2, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    set a := Quotient.out q1
    set b := Quotient.out q2
    have hab : g a = g b := hq
    have hmem : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) ∈ gam σ ϖ e := (-a + b).2
    refine ⟨hmem.1, fun k j => ?_⟩
    have e1 : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) k j
        = ((b : Matrix (Fin r) (Fin r) L) k j - (g b k j : L)) - ((a : Matrix (Fin r) (Fin r) L) k j - (g a k j : L)) := by
      rw [hab]; simp; ring
    rw [e1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · exact (hg b k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
    · exact (hg a k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
  exact Finite.of_injective h hinj

end GlobalTheory.Hk3.GramSep
end

section

open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem trace_skewHermitian_gram_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam0 σ ϖ e →
  δ * Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ δ hv hδ n n' r JT a y M e Γ hJT hya haM hΓ
  have hmem : ∀ x : L, x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := fun _ => Iff.rfl
  set N := y * M with hNdef
  have hNe : N = (y * (a : Matrix (Fin n) (Fin n) L)) * (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) := by
    rw [hNdef, Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L)]
    have : (a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.one_mul]
  have hN : ∀ q k, N q k * ϖ ^ e k ∈ Formalism.UG.intL L := by
    intro q k
    rw [hNe, Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mul_assoc]
    exact Subring.mul_mem _ (hya q i) (haM i k)
  have hNσ : ∀ p j, σ (N p j) * ϖ ^ e j ∈ Formalism.UG.intL L := by
    intro p j
    have h := hN p j
    rw [hmem] at h ⊢
    rw [map_mul, hv]; rw [map_mul] at h; exact h
  have hG : ∀ j k, (Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k * ϖ ^ (e j + e k) ∈ Formalism.UG.intL L := by
    intro j k
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun q _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    refine Subring.sum_mem _ fun p _ => ?_
    have hc : Formalism.UG.cT σ N j p = σ (N p j) := rfl
    rw [hc, pow_add]
    have : σ (N p j) * (JT : Matrix (Fin n') (Fin n') L) p q * N q k * (ϖ ^ e j * ϖ ^ e k) =
        (σ (N p j) * ϖ ^ e j) * (JT : Matrix (Fin n') (Fin n') L) p q * (N q k * ϖ ^ e k) := by ring
    rw [this]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hNσ p j) (hJT p q)) (hN q k)
  refine Subring.mul_mem _ hδ ?_
  rw [Matrix.trace]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [hmem, map_mul]
  have h1 := hΓ.2 k j
  have h2 := hG j k
  rw [hmem, map_mul, map_pow] at h2
  calc Valued.v (Γ k j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k)
      ≤ Valued.v ϖ ^ (e k + e j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) :=
        mul_le_mul_of_nonneg_right h1 zero_le'
    _ = Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) * Valued.v ϖ ^ (e j + e k) := by
        rw [mul_comm, add_comm]
    _ ≤ 1 := h2

end GlobalTheory.Hk3.GramSep
end
