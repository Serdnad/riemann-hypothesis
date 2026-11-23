module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
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
public import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalSpans

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev sF (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) 𝔭.primeCompl

theorem closure_eq (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] :
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = sF K 𝔭 := by
  have : {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = (sF K 𝔭 : Set (𝓞 K)) := by
    ext s
    rfl
  rw [this, Submonoid.closure_eq]

theorem mem_locF {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [closure_eq]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, h⟩
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨_, ⟨t, ht, rfl⟩, h⟩

theorem sF_le (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : sF K 𝔭 ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ 𝔭.primeCompl_le_nonZeroDivisors

abbrev RP (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (sF K 𝔭) (sF_le 𝔭)

theorem mem_span_RP (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (RP K 𝔭) (N : Set V) ↔ x ∈ locF 𝔭 N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact (mem_locF 𝔭 N x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h, by simpa using hx⟩
    | zero => exact (locF 𝔭 N).zero_mem
    | add x y _ _ hx hy => exact (locF 𝔭 N).add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨a, s, ⟨t, ht, rfl⟩, hc⟩ := c.2
      obtain ⟨u, hu, hx⟩ := (mem_locF 𝔭 N x).1 hx
      refine (mem_locF 𝔭 N _).2 ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hu, ?_⟩
      have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
        intro h0
        have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
        have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
        exact ht (h2 ▸ 𝔭.zero_mem)
      have : algebraMap (𝓞 F) (𝓞 K) (t * u) • c • x = a • (algebraMap (𝓞 F) (𝓞 K) u • x) := by
        rw [Subalgebra.smul_def, hc, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t * u)),
          ← algebraMap_smul K a, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) u), smul_smul, smul_smul,
          map_mul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact N.smul_mem _ hx
  · intro hx
    obtain ⟨t, ht, hx⟩ := (mem_locF 𝔭 N x).1 hx
    have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro h0
      have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
      have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
      exact ht (h2 ▸ 𝔭.zero_mem)
    let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹,
      ⟨1, _, ⟨t, ht, rfl⟩, by simp⟩⟩
    have : x = c • (algebraMap (𝓞 F) (𝓞 K) t • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t), smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem exists_basis_locF {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  let M : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (L : Set V)
  have hMfg : M.FG := by
    obtain ⟨s, hs⟩ := hL.fg
    refine ⟨s, ?_⟩
    show _ = Submodule.span (RP K 𝔭) (L : Set V)
    rw [← hs, Submodule.span_span_of_tower]
  have : Submodule.IsFullLattice K M :=
    { toIsLattice := Submodule.IsLattice.of_fg K hMfg
      span_eq_top := by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono Submodule.subset_span }
  have : Module.Free (RP K 𝔭) M := Submodule.IsLattice.free K M
  have : Module.Finite (RP K 𝔭) M := Submodule.IsLattice.finite K M
  let b0 := Module.Free.chooseBasis (RP K 𝔭) M
  let b1 := b0.extendOfIsFullLattice K
  have hb1 : ∀ i, b1 i = (b0 i : V) := fun i => Basis.extendOfIsFullLattice_apply K b0 i
  have hmem : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b1 i ∈ L := fun i => by
    rw [← mem_locF, ← mem_span_RP, hb1]
    exact (b0 i).2
  choose t ht htL using hmem
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  let b2 := b1.unitsSMul fun i => Units.mk0 _ (ht0 i)
  have hb2 : ∀ i, b2 i = algebraMap (𝓞 F) (𝓞 K) (t i) • b1 i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b2).symm
  refine ⟨b2.reindex e, fun i => ?_, ?_⟩
  · rw [Basis.reindex_apply, hb2]
    exact htL _
  · ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Basis.range_reindex]
    have : Submodule.span (RP K 𝔭) (Set.range b2) = M := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [hb2]
        exact Submodule.subset_span (htL i)
      · have h1 : M = Submodule.map M.subtype (Submodule.span (RP K 𝔭) (Set.range b0)) := by
          rw [b0.span_eq, Submodule.map_top, Submodule.range_subtype]
        refine h1.le.trans ?_
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        have : M.subtype (b0 i) = c • b2 i := by
          rw [hb2, Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_smul,
            inv_mul_cancel₀ (ht0 i), one_smul, hb1]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [this]

end Formalism.HermitianLattices.Ext.L3.LocalSpans
end
end

section

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def rEmb (w : {w : InfinitePlace F // w.IsReal}) : 𝓞 F →+* ℝ :=
  (InfinitePlace.embedding_of_isReal w.2).comp (algebraMap (𝓞 F) F)

theorem rEmb_apply (w : {w : InfinitePlace F // w.IsReal}) (n : 𝓞 F) :
    rEmb w n = InfinitePlace.embedding_of_isReal w.2 (n : F) := rfl

theorem mem_boxSet_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F} :
    n ∈ boxSet K F T ↔ ∀ w : {w : InfinitePlace F // w.IsReal}, 0 < rEmb w n ∧ rEmb w n ≤ T := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  constructor
  · intro h w
    let _ : Algebra F ℂ := w.1.embedding.toAlgebra
    let φ : K →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h1 : φ (algebraMap F K (n : F)) = w.1.embedding (n : F) := φ.commutes _
    have h2 := h φ.toRingHom
    have h3 : (φ.toRingHom (algebraMap F K (n : F))).re = rEmb w n := by
      show (φ (algebraMap F K (n : F))).re = _
      rw [h1, rEmb_apply, ← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]
    rwa [h3] at h2
  · intro h φ
    have hw : (InfinitePlace.mk (φ.comp (algebraMap F K))).IsReal := IsTotallyReal.isReal _
    have h1 := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)
    have h3 : (φ (algebraMap F K (n : F))).re = rEmb ⟨_, hw⟩ n := by
      rw [rEmb_apply, ← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ _),
        InfinitePlace.embedding_of_isReal_apply hw, h1]
      rfl
    rw [h3]
    exact h _

theorem absNorm_eq_prod [IsTotallyReal F] (n : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n| := by
  have h1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) = |((Algebra.norm ℚ (n : F) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [h1, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  have h2 : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal) Finset.univ (by simp [h2])
    (fun w => w (n : F) ^ w.mult)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [w.2.mult_eq_one, pow_one, rEmb_apply, ← Real.norm_eq_abs,
    InfinitePlace.norm_embedding_of_isReal]

theorem absNorm_eq_prod_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, rEmb w n := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  rw [absNorm_eq_prod]
  exact Finset.prod_congr rfl fun w _ => abs_of_pos (((mem_boxSet_iff hK hF).1 hn) w).1

theorem card_real (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    Fintype.card {w : InfinitePlace F // w.IsReal} = Formalism.HermitianLatticesTheory.fDeg K := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h1 := (discrTower K F hK hF).2.1
  rw [← h1, IsTotallyReal.finrank]

theorem finite_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h0 := Embeddings.finite_of_norm_le F ℂ T
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => (n : F)) (h0.subset ?_)
    (RingOfIntegers.coe_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n.2, fun ψ => ?_⟩
  have hw : (InfinitePlace.mk ψ).IsReal := IsTotallyReal.isReal _
  have h1 := ((mem_boxSet_iff hK hF).1 hn) ⟨_, hw⟩
  have h2 : ‖ψ (n : F)‖ = |rEmb ⟨_, hw⟩ n| := by
    rw [rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]
    rfl
  rw [h2, abs_of_pos h1.1]
  exact h1.2

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [absNorm_eq_prod_of_mem hK hF hn, ← card_real hK hF, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).1.le)
    fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).2

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end
