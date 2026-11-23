module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle341
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem cosetFn_zero_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) :
    cosetFn t hc a (0 : Z) = 0 := by
  apply Subtype.ext
  funext v
  show (cosetSet t c a).indicator (fun _ => (0 : Z)) v = 0
  exact congrFun (Set.indicator_zero Z (cosetSet t c a)) v

theorem cosetFn_add_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z w : Z) :
    cosetFn t hc a (z + w) = cosetFn t hc a z + cosetFn t hc a w := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => z + w) v =
    (cosetSet t c a).indicator (fun _ => z) v + (cosetSet t c a).indicator (fun _ => w) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, add_zero]

theorem cosetFn_smul_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (r : ℂ) (z : Z) :
    cosetFn t hc a (r • z) = r • cosetFn t hc a z := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => r • z) v =
    r • (cosetSet t c a).indicator (fun _ => z) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, smul_zero]

def topCol (i t : ℕ) (x : Fin i → k) : Multiplicative (Fin (i + t) → k) :=
  Multiplicative.ofAdd (topV k i t x)

theorem topPart_topCol (i t : ℕ) (x : Fin i → k) : topP i t (topCol i t x).toAdd = x := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_topColumn (i t : ℕ) (x : Fin i → k) : middlePart i t (topCol i t x).toAdd = 0 := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_topCol {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    {c : k} (hc : c ≠ 0) (x : Multiplicative (Fin i → k)) (w : Z) :
    fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w) = cosetFn t hc 0 (ρ₀ x w) := by
  apply Subtype.ext
  funext v
  classical
  have h1 : (fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w)).1 v =
      ρ₀ (Multiplicative.ofAdd (topP i t (topCol i t x.toAdd).toAdd))
        ((cosetFn t hc 0 w).1 (v + middlePart i t (topCol i t x.toAdd).toAdd)) :=
    fibAct_apply t ρ₀ _ _ v
  have h2 : Multiplicative.ofAdd (topP i t (topCol (k := k) i t x.toAdd).toAdd) = x := by
    rw [topPart_topCol]
    rfl
  rw [h1, h2, middlePart_topColumn, add_zero]
  show ρ₀ x ((cosetSet t c 0).indicator (fun _ => w) v) =
    (cosetSet t c 0).indicator (fun _ => ρ₀ x w) v
  by_cases hv : v ∈ cosetSet t c 0
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, map_zero]

theorem cosetFn_mem_twKer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z)
    (hz : z ∈ twKer ρ₀ ⊤ 1) : cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩,
      cosetFn t hc 0 v, ?_⟩
    have hsub : ρ₀ (n : Multiplicative (Fin i → k)) v - ((1 : (⊤ : Subgroup (Multiplicative (Fin i → k))) →* ℂˣ) n : ℂ) • v =
        ρ₀ (n : Multiplicative (Fin i → k)) v + (-1 : ℂ) • v := by
      simp [sub_eq_add_neg]
    have hrhs : fibAct t ρ₀ (topCol i t (n : Multiplicative (Fin i → k)).toAdd) (cosetFn t hc 0 v) -
        ((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ) ⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩ : ℂ) • cosetFn t hc 0 v =
        cosetFn t hc 0 (ρ₀ (n : Multiplicative (Fin i → k)) v) + (-1 : ℂ) • cosetFn t hc 0 v := by
      rw [fibAct_topCol]
      simp [sub_eq_add_neg]
    rw [hsub, cosetFn_add_val, cosetFn_smul_val]
    exact hrhs.symm
  | zero => rw [cosetFn_zero_val]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [cosetFn_add_val]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [cosetFn_smul_val]; exact Submodule.smul_mem _ r ha

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem topPart_append_zero (i t : ℕ) (a : Fin t → k) : topP i t (Fin.append (0 : Fin i → k) a) = 0 := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_append_zero (i t : ℕ) (a : Fin t → k) : middlePart i t (Fin.append (0 : Fin i → k) a) = a := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_cosetFn_translate (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) :
    fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z) = cosetFn t hc 0 z := by
  apply Subtype.ext
  funext v
  have h1 : Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)) = 1 :=
    congrArg Multiplicative.ofAdd (topPart_append_zero i t a)
  have h2 : (fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z)).1 v
      = ρ₀ (Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)))
        ((cosetFn t hc a z).1 (v + middlePart i t (Fin.append (0 : Fin i → k) a))) := rfl
  rw [h2, h1, map_one, middlePart_append_zero]
  show (cosetSet t c a).indicator (fun _ => z) (v + a) = (cosetSet t c 0).indicator (fun _ => z) v
  have hs : (v + a ∈ cosetSet t c a) ↔ v ∈ cosetSet t c 0 := by
    have : v + a - a = v - 0 := by simp
    show Multiplicative.ofAdd (v + a - a) ∈ Lc t c ↔ Multiplicative.ofAdd (v - 0) ∈ Lc t c
    rw [this]
  classical
  by_cases hv : v ∈ cosetSet t c 0
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hs.2 hv)]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv (hs.1 h))]

theorem cosetFn_sub_cosetFn_zero_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  intro k _ _ _ _ i t Z _ _ ρ₀ c hc a z
  have hgen : cosetFn t hc 0 z - cosetFn t hc a z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩, cosetFn t hc a z, ?_⟩
    have h1 : (((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ)
        ⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩ : ℂˣ) : ℂ) = 1 := rfl
    rw [h1, one_smul]
    exact congrArg (· - cosetFn t hc a z) (fibAct_cosetFn_translate i t ρ₀ hc a z).symm
  have := Submodule.neg_mem _ hgen
  rwa [neg_sub] at this

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist

open ValuativeRel in
theorem mulH_inv_mem_Lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {c : k} {κ : GL (Fin n) k}
    (hκ : κ ∈ GlobalTheory.SplitWeil.KO k (Fin n)) {l : Multiplicative (Fin n → k)} (hl : l ∈ Lc n c) :
    mulH κ⁻¹ l ∈ Lc n c := by
  obtain ⟨g, rfl⟩ := hκ
  have hl' : ∀ i, c * l.toAdd i ∈ 𝒪[k] := hl
  have hent : ∀ a b, (((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b ∈ 𝒪[k] := by
    intro a b
    rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) a b).2
  show ∀ j, c * ((((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ l.toAdd) j ∈ 𝒪[k]
  intro j
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [mul_left_comm]
  exact mul_mem (hent j i) (hl' i)

theorem mulH_mulH_inv {k : Type} [Field k] {n : ℕ} (κ : GL (Fin n) k)
    (l : Multiplicative (Fin n → k)) : mulH κ (mulH κ⁻¹ l) = l := by
  show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec
    (((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec l.toAdd)) = l
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

theorem twKer_Lc_le_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ c κ hκ x hx
  unfold GlobalTheory.PRep.twKer at hx ⊢
  refine Submodule.span_le.2 ?_ hx
  rintro w ⟨m, v, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨mulH κ⁻¹ m, mulH_inv_mem_Lc hκ m.2⟩, v, ?_⟩
  simp [mulH_mulH_inv]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem tmul_mem_twKer_topRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) {w : V} (hw : w ∈ twKer τ (MirUin k i) 1) (b : W) :
    w ⊗ₜ[ℂ] b ∈ twKer (topRep τ W) ⊤ 1 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, a, rfl⟩ := hw
    obtain ⟨x, hx⟩ := exists_uM_of_mem k i n.2
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩, a ⊗ₜ[ℂ] b, ?_⟩
    have h1 : topRep τ W (Multiplicative.ofAdd x) (a ⊗ₜ[ℂ] b) = (τ (uM k i x) a) ⊗ₜ[ℂ] b := rfl
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [h1, hx, TensorProduct.sub_tmul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [TensorProduct.add_tmul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c hx

theorem mem_twKer_topRep_of_clT_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  intro k _ _ _ _ i V W _ _ _ _ τ z hz
  have hex : Function.Exact (twKer τ (MirUin k i) 1).subtype (twKer τ (MirUin k i) 1).mkQ :=
    LinearMap.exact_subtype_mkQ _
  obtain ⟨y, rfl⟩ := (rTensor_exact W hex (Submodule.mkQ_surjective _) z).1 hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => exact tmul_mem_twKer_topRep k i τ w.2 b
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

open _root_.Topology

theorem range_finite {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem exists_nhds_translation_invariant {A Z : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddCommGroup Z] {φ : A → Z} (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) : ∃ N ∈ 𝓝 (0 : A), ∀ w ∈ N, ∀ v, φ (v + w) = φ v := by
  letI := IsTopologicalAddGroup.rightUniformSpace A
  haveI := isUniformAddGroup_of_addCommGroup (G := A)
  letI : UniformSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  have hu : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hid : {p : Z × Z | p.1 = p.2} ∈ _root_.uniformity Z := by
    have : _root_.uniformity Z = Filter.principal {p : Z × Z | p.1 = p.2} := rfl
    rw [this]
    exact Filter.mem_principal_self _
  have h1 := hu hid
  rw [Filter.mem_map, uniformity_eq_comap_nhds_zero A, Filter.mem_comap] at h1
  obtain ⟨N, hN, hsub⟩ := h1
  refine ⟨N, hN, fun w hw v => ?_⟩
  have h2 : (v, v + w) ∈ (fun x : A × A => x.2 - x.1) ⁻¹' N := by
    show v + w - v ∈ N
    simpa using hw
  exact (hsub h2).symm

theorem isOpen_stabiliser {G V : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (h : {g | ρ g v = v} ∈ 𝓝 (1 : G)) :
    IsOpen {g | ρ g v = v} :=
  _root_.UpperTheory.Reformulated.B.Yhd4.main ρ v h

theorem isSmooth_fibAct (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (hρ : IsSmooth ρ₀) :
    IsSmooth (fibAct t ρ₀) := by
  intro φ
  refine isOpen_stabiliser (fibAct t ρ₀) φ ?_
  have hU : (⋂ z ∈ Set.range φ.1, {g : Multiplicative (Fin i → k) | ρ₀ g z = z}) ∈ 𝓝 1 :=
    (Filter.biInter_mem (range_finite φ.2.1 φ.2.2)).2 fun z _ =>
      (hρ z).mem_nhds (show ρ₀ 1 z = z by rw [map_one, Module.End.one_apply])
  obtain ⟨N, hN, hinv⟩ := exists_nhds_translation_invariant φ.2.1 φ.2.2
  have hT : Continuous fun y : Multiplicative (Fin (i + t) → k) =>
      Multiplicative.ofAdd (topP i t y.toAdd) :=
    continuous_ofAdd.comp ((continuous_topP i t).comp continuous_toAdd)
  have hM : Continuous fun y : Multiplicative (Fin (i + t) → k) => middlePart i t y.toAdd :=
    (continuous_midP i t).comp continuous_toAdd
  have h1 := hT.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hU
  have h2 := hM.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hN
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro y ⟨hy1, hy2⟩
  apply Subtype.ext
  funext v
  show ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) = φ.1 v
  rw [hinv _ hy2 v]
  exact Set.mem_iInter₂.1 hy1 (φ.1 v) ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

theorem measure_cosetSet_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k) (a : Fin t → k) :
    μ (cosetSet t c a) = μ (cosetSet t c 0) := by
  have h : cosetSet t c a = (fun v => (-a) + v) ⁻¹' cosetSet t c 0 := by
    ext v
    have e : v - a = (-a) + v - 0 := by abel
    show Multiplicative.ofAdd (v - a) ∈ Lc t c ↔ Multiplicative.ofAdd ((-a) + v - 0) ∈ Lc t c
    rw [e]
  rw [h]
  exact MeasureTheory.measure_preimage_add μ (-a) _

theorem smInt_sum_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → ∀ (A : Finset (Fin t → k)) (z : (Fin t → k) → Z), smInt μ (fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => z a) v) = (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) • ∑ a ∈ A, z a := by
  intro k _ _ _ _ t Z _ _ _ _ μ _ c hc A z
  classical
  have hmem : ∀ B : Finset (Fin t → k),
      (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) ∈ fibM (Fin t → k) Z := by
    intro B
    have h := Submodule.sum_mem (fibM (Fin t → k) Z) (t := B)
      (f := fun a => (cosetSet t c a).indicator (fun _ => z a))
      (fun a _ => (cosetFn t hc a (z a)).2)
    have e : (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) =
        ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) := by
      funext v
      rw [Finset.sum_apply]
    rw [e]
    exact h
  refine Finset.induction_on A ?_ ?_
  · have h := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator μ (∅ : Set (Fin t → k)) (0 : Z)
    simpa using h
  · intro a B ha ih
    have e : (fun v => ∑ b ∈ insert a B, (cosetSet t c b).indicator (fun _ => z b) v) =
        (cosetSet t c a).indicator (fun _ => z a) +
          fun v => ∑ b ∈ B, (cosetSet t c b).indicator (fun _ => z b) v := by
      funext v
      rw [Finset.sum_insert ha]
      rfl
    have l₁ : IsLocallyConstant ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.1
    have c₁ : HasCompactSupport ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.2
    rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_add μ l₁ c₁ (hmem B).1 (hmem B).2, ih, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator,
      measure_cosetSet_eq t μ c a, Finset.sum_insert ha, smul_add]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.tensor_lift_kernel_mod_prime : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W), Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 → z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  first | exact @GlobalTheory.CompanionTheory.TensOne.main | exact GlobalTheory.CompanionTheory.TensOne.main | (intros; apply GlobalTheory.CompanionTheory.TensOne.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_restrict_pull_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ConeZarCap.main | exact GlobalTheory.CompanionTheory.ConeZarCap.main | (intros; apply GlobalTheory.CompanionTheory.ConeZarCap.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.acris_level_one_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := by
  first | exact @GlobalTheory.CompanionTheory.ACrisMod.acr1 | exact GlobalTheory.CompanionTheory.ACrisMod.acr1 | (intros; apply GlobalTheory.CompanionTheory.ACrisMod.acr1 <;> assumption)
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.parahoric_levi_unipotent_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx | exact GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_compact_mod_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧ ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact | exact GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact <;> assumption)
end
