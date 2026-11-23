module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

namespace AENeighbourhoods

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

def intBasis (E : Type) [Field E] [NumberField E] (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : E :=
  algebraMap (𝓞 E) E (RingOfIntegers.basis E l)

theorem nhds_zero_finiteAdele {W : Set (FiniteAdeleRing (𝓞 F) F)} (hW : W ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v ∈ S, x v = 0) → (∀ v ∉ S, x v ∈ v.adicCompletionIntegers F) → x ∈ W := by
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  let W' : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := W
  have h2 : W' ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) =>
      v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite) (𝓝 0) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hopen 0]
    exact hW
  have h1 := Filter.mem_map.1 h2
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  refine ⟨hI.toFinset, fun x hx0 hxI => ?_⟩
  have hmem : ∀ v, x v ∈ v.adicCompletionIntegers F := fun v => by
    by_cases hv : v ∈ hI.toFinset
    · rw [hx0 v hv]; exact zero_mem _
    · exact hxI v hv
  let x' : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨x v, hmem v⟩
  have hx' : x' ∈ I.pi t := fun v hv => by
    have : x' v = 0 := Subtype.ext (hx0 v (hI.mem_toFinset.2 hv))
    rw [this]; exact mem_of_mem_nhds (ht v)
  have := hsub hx'
  exact this

theorem intAt_repr (v : HeightOneSpectrum (𝓞 F)) {z : Kv E v} (hz : z ∈ intAt E v) :
    ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ z = ∑ l, y l ⊗ₜ[F] intBasis E l := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, rfl⟩ := hx
    refine ⟨fun l => (RingOfIntegers.basis E).repr b l • a, fun l => zsmul_mem ha _, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr b]

    rw [map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, ← smul_tmul]
    rfl
  | zero => exact ⟨0, fun l => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    obtain ⟨y₂, h₂, rfl⟩ := hy
    exact ⟨y₁ + y₂, fun l => add_mem (h₁ l) (h₂ l), by simp [add_tmul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    exact ⟨-y₁, fun l => neg_mem (h₁ l), by simp [neg_tmul, Finset.sum_neg_distrib]⟩

theorem compAt_sum (v : HeightOneSpectrum (𝓞 F))
    (X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) :
    compAt E v (∑ l, X l ⊗ₜ[F] intBasis E l) = ∑ l, X l v ⊗ₜ[F] intBasis E l := by

  rw [map_sum]; rfl

theorem exists_repr (a : AE F E) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      a = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    refine ⟨fun l => algebraMap ℚ F ((integralBasis E).repr y l) • x, ?_⟩
    conv_lhs => rw [← (integralBasis E).sum_repr y]
    rw [tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integralBasis_apply, ← IsScalarTower.algebraMap_smul F, tmul_smul, smul_tmul']
    rfl
  | add x y hx hy =>
    obtain ⟨X₁, rfl⟩ := hx
    obtain ⟨X₂, rfl⟩ := hy
    exact ⟨X₁ + X₂, by simp [add_tmul, Finset.sum_add_distrib]⟩

theorem exists_repr_of_int
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {m : AE F E} (h0 : ∀ v ∈ S, compAt E v m = 0)
    (hI : ∀ v ∉ S, compAt E v m ∈ intAt E v) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      (∀ l, ∀ v ∈ S, X l v = 0) ∧ (∀ l, ∀ v ∉ S, X l v ∈ v.adicCompletionIntegers F) ∧
      m = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  classical
  have hr : ∀ v, v ∉ S → ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ compAt E v m = ∑ l, y l ⊗ₜ[F] intBasis E l :=
    fun v hv => intAt_repr v (hI v hv)
  choose y hyI hyeq using hr
  let Y : ∀ v : HeightOneSpectrum (𝓞 F), Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F :=
    fun v => if hv : v ∈ S then 0 else y v hv
  have hYI : ∀ v l, Y v l ∈ v.adicCompletionIntegers F := fun v l => by
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply]; exact zero_mem _
    · simp only [Y, dif_neg hv]; exact hyI v hv l
  let X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F :=
    fun l => ⟨fun v => Y v l, Filter.Eventually.of_forall fun v => hYI v l⟩
  refine ⟨X, fun l v hv => ?_, fun l v _ => hYI v l, hsep _ _ fun v => ?_⟩
  · change Y v l = 0
    simp only [Y, dif_pos hv, Pi.zero_apply]
  · rw [compAt_sum]
    change compAt E v m = ∑ l, Y v l ⊗ₜ[F] intBasis E l
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply, zero_tmul, Finset.sum_const_zero]; exact h0 v hv
    · simp only [Y, dif_neg hv]; exact hyeq v hv

theorem int_cofinite (a : AE F E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, compAt E v a ∈ intAt E v := by
  obtain ⟨X, rfl⟩ := exists_repr a
  have hev : ∀ᶠ v in Filter.cofinite, ∀ l, X l v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun l => (X l).2
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv => ?_⟩
  have hv' : ∀ l, X l v ∈ v.adicCompletionIntegers F := by
    by_contra h
    exact hv ((Filter.eventually_cofinite.1 hev).mem_toFinset.2 h)
  rw [compAt_sum]
  exact AddSubgroup.sum_mem _ fun l _ => AddSubgroup.subset_closure ⟨X l v, hv' l, _, rfl⟩

theorem nhds_of_sep [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)]
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b) (N : ℕ)
    (U : Set (Matrix (Fin N) (Fin N) (AE F E))) (hU : U ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : Matrix (Fin N) (Fin N) (AE F E),
      (∀ i j, (∀ v ∈ S, compAt E v (M i j) = 0) ∧ ∀ v ∉ S, compAt E v (M i j) ∈ intAt E v) →
      M ∈ U := by
  classical
  have := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let Ψ : (ι → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin N) (Fin N) (AE F E) :=
    fun X => Matrix.of fun i j => ∑ l, X (i, j, l) • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l)
  have hΨ : Continuous Ψ :=
    continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun l _ => (continuous_apply (i, j, l)).smul
        (continuous_const : Continuous fun _ : ι → FiniteAdeleRing (𝓞 F) F =>
          ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l))
  have hΨ0 : Ψ 0 = 0 := by ext i j; simp [Ψ]
  have hpre : Ψ ⁻¹' U ∈ 𝓝 (0 : ι → FiniteAdeleRing (𝓞 F) F) :=
    hΨ.continuousAt.preimage_mem_nhds (by rw [hΨ0]; exact hU)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  obtain ⟨S, hS⟩ := nhds_zero_finiteAdele (Filter.iInter_mem.2 fun k : ι => ht k)
  refine ⟨S, fun M hM => ?_⟩
  choose X hX0 hXI hXeq using fun i j => exists_repr_of_int hsep S (hM i j).1 (hM i j).2
  have hmem : (fun k : ι => X k.1 k.2.1 k.2.2) ∈ I.pi t := fun k _ =>
    Set.mem_iInter.1 (hS _ (hX0 _ _ _) (hXI _ _ _)) k
  have hM' : Ψ (fun k : ι => X k.1 k.2.1 k.2.2) = M := by
    ext i j
    rw [hXeq i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hfin := hsub hmem
  rw [Set.mem_preimage, hM'] at hfin
  exact hfin

theorem of_placeMaps (hP : PlaceMaps.Statement) : AENeighbourhoods.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  exact ⟨fun N U hU => nhds_of_sep (hP F E c h2 hc).1 N U hU, int_cofinite⟩

theorem proof (_hT : AETopologicalRing.Statement) (hP : PlaceMaps.Statement) :
    AENeighbourhoods.Statement :=
  of_placeMaps hP

end AENeighbourhoods

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem EDenseInAE.proof (hT : AETopologicalRing.Statement) : EDenseInAE.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  obtain ⟨-, -, ⟨δ, -, hδ⟩, -⟩ := hT F E c h2 hc
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let φ : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F → AE F E :=
    fun p => p.1 • (1 : AE F E) + p.2 • inclA F E δ
  have hφc : Continuous φ :=
    by unfold φ; fun_prop
  have hφs : Function.Surjective φ := fun a => by
    obtain ⟨p, hp, -⟩ := hδ a
    exact ⟨p, hp.symm⟩
  have hK : DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    denseRange_finiteAdele (R := 𝓞 F) (K := F)
  have hD : DenseRange (φ ∘ Prod.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))) :=
    hφs.denseRange.comp (hK.prodMap hK) hφc
  refine hD.mono ?_
  rintro _ ⟨⟨x, y⟩, rfl⟩
  refine ⟨algebraMap F E x + algebraMap F E y * δ, ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, φ, algebraMap_smul, map_add (f := _), map_mul]
  have hinc : ∀ z : F, inclA F E (algebraMap F E z) = z • (1 : AE F E) := fun z => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes z
  rw [hinc, hinc, smul_one_mul]

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem sigA_inclA_apply {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem OrthProjection.proof (hT : AETopologicalRing.Statement) : OrthProjection.Statement := by
  refine ⟨?_, ?_⟩
  · intro R _ σ hσ N J hJ e f hee hff hef
    have hfe : hf σ J f e = 1 := by rw [← hf_symm hσ hJ, hef, map_one]
    have perp : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0 := by
      intro u
      simp only [perpProj, hf_sub_left, hf_smul_left, hee, hff, hef, hfe]
      constructor <;> ring
    have fix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u := by
      intro u h1 h2
      simp [perpProj, h1, h2]
    refine ⟨⟨fun u v => ?_, fun a u => ?_⟩, fun u => fix _ (perp u).1 (perp u).2, perp, fix⟩
    · simp only [perpProj, hf_add_left, add_smul]
      abel
    · simp only [perpProj, hf_smul_left, smul_sub, mul_smul]
  · intro F E _ _ _ _ _ c h2 hc N J e f _ _
    have := (hT F E c h2 hc).1
    refine ⟨?_, fun u => ?_⟩
    · unfold perpProj hf
      fun_prop
    · have hmap : ∀ x y : Fin N → E, inclA F E (hf c.toRingHom J x y) =
          hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ x) (inclA F E ∘ y) := by
        intro x y

        simp [hf, map_sum, map_mul, sigA_inclA_apply]
      funext i
      simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
        map_mul, hmap]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem map_inclA_mem_SU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hform⟩ := hγ
  have hsig : ∀ y : E, sigA c (inclA F E y) = inclA F E (c y) := by
    intro y
    simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
  have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
    ext i j
    simp [hsig]
  refine ⟨?_, ?_⟩
  · rw [show (γ.map (inclA F E)).det = inclA F E γ.det from (RingHom.map_det _ _).symm, hdet, map_one]
  · rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hform]

theorem SAOpenHolds.proof (hSA : SAHolds.Statement) (hTop : AETopologicalRing.Statement) :
    SAOpenHolds.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ hdet hiso _ _ Kg hKsub h1 _ hinv hO x hx
  obtain ⟨O, hOopen, hOK⟩ := hO
  have hxdet : IsUnit x.det := by rw [hx.1]; exact isUnit_one

  have hcont : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) :=
    ((hTop F E c h2 hc).2.2.2 N (J.map (inclA F E))).1.comp
      (continuous_const.prodMk continuous_id)
  have hUopen : IsOpen ((fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O) :=
    hOopen.preimage hcont
  have h1O : (1 : Matrix (Fin N) (Fin N) (AE F E)) ∈ O := by
    rw [← hOK] at h1; exact h1.1
  have hxU : x ∈ (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O := by
    change x⁻¹ * x ∈ O
    rw [nonsing_inv_mul x hxdet]; exact h1O
  have hcl := hSA F E c h2 hc N J hJ hdet hiso hx
  obtain ⟨_, hyU, ⟨γ, hγ, rfl⟩⟩ := mem_closure_iff.1 hcl _ hUopen hxU
  have hγA := map_inclA_mem_SU c J hγ
  set k := x⁻¹ * γ.map (inclA F E) with hk
  have hkSU : k ∈ SU (sigA c) (J.map (inclA F E)) :=
    mul_mem_SU (inv_mem_SU _ _ hx) hγA
  have hkK : k ∈ Kg := by rw [← hOK]; exact ⟨hyU, hkSU⟩
  have hkdet : IsUnit k.det := by rw [hkSU.1]; exact isUnit_one
  refine ⟨γ, hγ, k⁻¹, hinv k hkK, ?_⟩
  have hxk : x * k = γ.map (inclA F E) := by
    rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv x hxdet, Matrix.one_mul]
  rw [← hxk, Matrix.mul_assoc, mul_nonsing_inv k hkdet, Matrix.mul_one]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end
