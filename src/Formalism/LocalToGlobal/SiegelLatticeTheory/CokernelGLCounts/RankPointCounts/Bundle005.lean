module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Mathlib.MeasureTheory.Constructions.Pi
public import Lemmata.GeneralBFactThirdBisForm.Imports
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.ZLattice.Covolume

@[expose] public section

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def SRLift : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R)
    (K : Submodule M.R (Fin (n + 1) → M.R)),
    (∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0) →
    (∀ v : Fin (n + 1) → M.R, ∃ x, v - A.mulVec x ∈ K) →
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      IsUnit (A + H).det

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

noncomputable section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.CovariantRepresentation

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem map_conj_of_mem (R : Subgroup G) (ν : Measure G) (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hi : ν.map (fun x => x⁻¹) = ν) {n : G} (hn : n ∈ R) : ν.map (fun x => n⁻¹ * x * n) = ν := by
  have hinv : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hr : ν.map (fun x => x * n) = ν := by
    have e : (fun x : G => x * n) = (fun x => x⁻¹) ∘ ((fun x => n⁻¹ * x) ∘ (fun x => x⁻¹)) := by
      funext x; simp [mul_inv_rev]
    rw [e, ← map_map hinv ((measurable_const_mul _).comp hinv), ← map_map (measurable_const_mul _) hinv, hi,
      hl _ (R.inv_mem hn), hi]
  have e : (fun x : G => n⁻¹ * x * n) = (fun x => x * n) ∘ (fun x => n⁻¹ * x) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul _), hl _ (R.inv_mem hn), hr]

theorem map_conj_of_bounded (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (h0 : ν ≠ 0)
    (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (k : G) (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R)
    (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) : ν.map (fun x => k⁻¹ * x * k) = ν := by
  obtain ⟨C, hCc, hCm⟩ := hC
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology _
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  set μ : Measure R := ν.comap Subtype.val with hμ
  have hν : μ.map Subtype.val = ν := by
    rw [hemb.map_comap, Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    exact hc
  have hcm : ∀ μ' : Measure R, (μ'.map Subtype.val).comap Subtype.val = μ' := fun μ' => hemb.comap_map μ'
  haveI : μ.IsMulLeftInvariant := ⟨fun r => by
    have h1 : (μ.map (r * ·)).map Subtype.val = μ.map Subtype.val := by
      rw [map_map hemb.measurable (measurable_const_mul r)]
      have e : (Subtype.val ∘ (r * ·) : R → G) = (fun x : G => (r : G) * x) ∘ Subtype.val := rfl
      rw [e, ← map_map (measurable_const_mul (r : G)) hemb.measurable, hν, hl _ r.2]
    rw [← hcm (μ.map (r * ·)), h1, hcm]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hKc => by
    rw [hμ, hemb.comap_apply]
    exact hK _ (hKc.image continuous_subtype_val)⟩
  haveI : NeZero μ := ⟨fun h => h0 (by rw [← hν, h, Measure.map_zero])⟩
  haveI : IsOpenPosMeasure μ := by
    obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering R n) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply NeZero.ne μ
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
      exact measure_iUnion_null hall
    exact isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering R n) hn
  haveI : IsHaarMeasure μ :=
    { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
      toIsOpenPosMeasure := inferInstance }
  let α : R ≃ₜ* R :=
    { toFun := fun r => ⟨k⁻¹ * r * k, (hk r).1 r.2⟩
      invFun := fun r => ⟨k * r * k⁻¹, (hk _).2 (by simpa [mul_assoc] using r.2)⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hit : ∀ (n : ℕ) (x : R), (((⇑α)^[n] x : R) : G) = k ^ (-(n : ℤ)) * x * k ^ (n : ℤ) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k⁻¹ * (((⇑α)^[n] x : R) : G) * k = _
      rw [ih]
      push_cast
      group
  have hit' : ∀ (n : ℕ) (x : R), (((⇑α.symm)^[n] x : R) : G) = k ^ (n : ℤ) * x * k ^ (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k * (((⇑α.symm)^[n] x : R) : G) * k⁻¹ = _
      rw [ih]
      push_cast
      group
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : R)
  have hL : IsCompact (Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) : Set R) :=
    hce.isCompact_preimage ((hCc.mul (hV.image continuous_subtype_val)).mul hCc)
  have hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) ∧
      (⇑α.symm)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) := by
    intro n
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α.symm)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit' n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
  have hμα : μ.map α = μ := haar_map_equiv_of_bounded μ α hV hV1 hL hb
  have hmc : Measurable (fun x : G => k⁻¹ * x * k) := (measurable_const_mul _).mul_const _
  have hma : Measurable (⇑α) := α.continuous.measurable
  calc ν.map (fun x => k⁻¹ * x * k) = (μ.map Subtype.val).map (fun x => k⁻¹ * x * k) := by rw [hν]
    _ = (μ.map α).map Subtype.val := by
        rw [map_map hmc hemb.measurable, map_map hemb.measurable hma]
        rfl
    _ = ν := by rw [hμα, hν]

theorem conj_of_decomp (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (_hs : SigmaFinite ν)
    (h0 : ν ≠ 0) (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (hi : ν.map (fun x => x⁻¹) = ν) (k n : G)
    (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R) (hn : n ∈ R) (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) :
    ν.map (fun x => (k * n)⁻¹ * x * (k * n)) = ν := by
  have e : (fun x : G => (k * n)⁻¹ * x * (k * n)) = (fun x => n⁻¹ * x * n) ∘ (fun x => k⁻¹ * x * k) := by
    funext x
    simp only [Function.comp]
    group
  rw [e, ← map_map ((measurable_const_mul _).mul_const _) ((measurable_const_mul _).mul_const _),
    map_conj_of_bounded R hR ν h0 hc hK hl k hk hC, map_conj_of_mem R ν hl hi hn]

end Conj

end Formalism.L2.SG.CovariantRepresentation
end
end

section

noncomputable section

open MeasureTheory MeasurableSpace Set

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem swap_mp {ι P β : Type} [Fintype ι] [Fintype P] [MeasurableSpace β] (μ0 : Measure β) [SigmaFinite μ0] :
    MeasurePreserving (fun (x : ι → P → β) (p : P) (v : ι) => x v p)
      (Measure.pi fun _ : ι => Measure.pi fun _ : P => μ0) (Measure.pi fun _ : P => Measure.pi fun _ : ι => μ0) := by
  first | exact Bl.general_b_fact_third_bis_form.goal1 .. | (apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption)

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem idealCovol (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : ℕ)
    (hk : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k)
    (hk0 : k ≠ 0) (s : ℝ) (hs : s ≠ 0) (F : Set (ι → ℂ)) (hF : MeasurableSet F)
    (hFd : ∀ v, ∃! a : Λ, (fun i => (s : ℂ) * φ i a) + v ∈ F) :
    volume F = ENNReal.ofReal ((k : ℝ) * (FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * |s| ^ (2 * Fintype.card ι)) := by
  set cj : ι → Prop := fun i => φ i ≠ (σ i).1.embedding
  have hψ : MeasurePreserving (phiMap σ cj (K := K)) volume volume := phiMap_mp σ cj
  have hψe : ∀ a : K, phiMap σ cj (mixedEmbedding K a) = fun i => φ i a := by
    intro a; funext i
    simp only [phiMap, mixedEmbedding_apply_isComplex]
    by_cases hi : cj i
    · rw [if_pos hi]
      rcases hφ i with h | h
      · exact absurd h hi
      · rw [h, ComplexEmbedding.conjugate_coe_eq]
    · rw [if_neg hi]
      have : φ i = (σ i).1.embedding := not_not.1 hi
      rw [this]
  set emb : K →+ mixedSpace K := (mixedEmbedding K).toAddMonoidHom
  have hinj : Function.Injective emb := mixedEmbedding_injective K
  set Λm := Λ.map emb
  set G := phiMap σ cj (K := K) ⁻¹' (s⁻¹ • F)
  have hGm : MeasurableSet G := hψ.measurable (hF.const_smul₀ (s⁻¹))
  have hmem : ∀ y : ι → ℂ, y ∈ s⁻¹ • F ↔ s • y ∈ F := by
    intro y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hs), inv_inv]
  have hsm : ∀ a : K, ∀ x : mixedSpace K, s • phiMap σ cj (emb a + x) = (fun i => (s : ℂ) * φ i a) + s • phiMap σ cj x := by
    intro a x
    rw [phiMap_add, smul_add, show emb a = mixedEmbedding K a from rfl, hψe]
    funext i
    simp [Complex.real_smul]
  have hdG : ∀ x, ∃! b : Λm, (b : mixedSpace K) + x ∈ G := by
    intro x
    obtain ⟨a, ha, hu⟩ := hFd (s • phiMap σ cj x)
    refine ⟨⟨emb a, AddSubgroup.mem_map_of_mem emb a.2⟩, ?_, ?_⟩
    · show phiMap σ cj (emb a + x) ∈ s⁻¹ • F
      rw [hmem, hsm]; exact ha
    · rintro ⟨b, hb⟩ hbG
      obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hb
      have h1 : (fun i => (s : ℂ) * φ i (⟨a', ha'⟩ : Λ)) + s • phiMap σ cj x ∈ F := by
        have : phiMap σ cj (emb a' + x) ∈ s⁻¹ • F := hbG
        rw [hmem, hsm] at this; exact this
      have := hu ⟨a', ha'⟩ h1
      apply Subtype.ext
      show emb a' = emb a
      rw [show a' = (a : K) from congrArg Subtype.val this]

  set L := (idealLattice K I).toAddSubgroup
  have hL : L = (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup).map emb := by
    ext x
    simp only [L, Submodule.mem_toAddSubgroup, mem_idealLattice, AddSubgroup.mem_map]
    rfl
  have hle : Λm ≤ L := by
    rw [hL]; exact AddSubgroup.map_mono (fun a ha => hΛ a ha)
  have hk' : Λm.relIndex L = k := by
    rw [hL, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hk]
  have hcount : Countable L := by
    have b := Module.Free.chooseBasis ℤ (idealLattice K I)
    exact (Module.Free.chooseBasis ℤ (idealLattice K I)).equivFun.injective.countable
  set b := Module.Free.chooseBasis ℤ (idealLattice K I)
  set b' := Module.Basis.ofZLatticeBasis ℝ (idealLattice K I) b
  set FL := ZSpan.fundamentalDomain b'
  have hFLm : MeasurableSet FL := ZSpan.fundamentalDomain_measurableSet b'
  have hspan := Module.Basis.ofZLatticeBasis_span ℝ (idealLattice K I) b
  have hdL : ∀ x, ∃! l : L, (l : mixedSpace K) + x ∈ FL := by
    intro x
    obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
    have hvL : (v : mixedSpace K) ∈ idealLattice K I :=
      (congrArg (fun S : Submodule ℤ (mixedSpace K) => (v : mixedSpace K) ∈ S) hspan).mp v.2
    refine ⟨⟨v, hvL⟩, hv, ?_⟩
    rintro ⟨l, hl⟩ hlF
    have hl' : l ∈ Submodule.span ℤ (Set.range b') :=
      (congrArg (fun S : Submodule ℤ (mixedSpace K) => l ∈ S) hspan).mpr hl
    have h3 := hu ⟨l, hl'⟩ hlF
    have h2 : l = (v : mixedSpace K) := by rw [← h3]
    exact Subtype.ext h2
  have hidx := fund_index (volume : Measure (mixedSpace K)) L Λm hle k hk' hk0 FL G hFLm hGm hdL hdG

  have hfd := ZLattice.isAddFundamentalDomain b (volume : Measure (mixedSpace K))
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain (idealLattice K I) volume hfd
  rw [covolume_idealLattice] at hcov
  have hfin : volume FL ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b').measure_lt_top.ne
  have hFLv : volume FL = ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)|) := by
    rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfin]
  have hr2 : InfinitePlace.nrComplexPlaces K = Fintype.card ι := by
    rw [InfinitePlace.nrComplexPlaces, Fintype.card_congr σ.symm]

  have hGv : volume G = volume (s⁻¹ • F) := hψ.measure_preimage (hF.const_smul₀ (s⁻¹)).nullMeasurableSet
  have hscale : volume F = ENNReal.ofReal |s ^ Module.finrank ℝ (ι → ℂ)| * volume (s⁻¹ • F) := by
    conv_lhs => rw [← smul_inv_smul₀ hs F]
    exact Measure.addHaar_smul volume s (s⁻¹ • F)
  have hdim : Module.finrank ℝ (ι → ℂ) = 2 * Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  rw [hscale, ← hGv, hidx, hFLv, hr2, hdim]
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_pow]
  ring

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end
