module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.SBTransl

theorem exists_nhds_zero_invariant {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {β : Type} [Zero β] (g : X → β) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ V ∈ 𝓝 (0 : X), ∀ x, ∀ u ∈ V, g (x + u) = g x := by
  have hW : ∀ x : X, {u : X | g (x + u) = g x} ∈ 𝓝 (0 : X) := fun x => by
    have h1 : IsOpen {y : X | g y = g x} := hg.isOpen_fiber _
    have h2 : Continuous fun u : X => x + u := continuous_const.add continuous_id
    exact (h2.isOpen_preimage _ h1).mem_nhds (by simp)
  choose W' hW' hW'h using fun x => exists_nhds_zero_half (hW x)
  have hU : ∀ x ∈ tsupport g, {y : X | y - x ∈ W' x} ∈ 𝓝 x := fun x _ => by
    have h2 : Continuous fun y : X => y - x := continuous_id.sub continuous_const
    exact h2.continuousAt.preimage_mem_nhds (by simpa using hW' x)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover _ hU
  set V0 : Set X := ⋂ x ∈ t, W' x
  have hV0 : V0 ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).2 fun x _ => hW' x
  have key : ∀ y ∈ tsupport g, ∀ u ∈ V0, g (y + u) = g y := fun y hy u hu => by
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hux : u ∈ W' x := Set.mem_iInter₂.1 hu x hx
    have e1 : g (x + ((y - x) + u)) = g x := hW'h x _ hyx _ hux
    have e2 : g (x + ((y - x) + 0)) = g x := hW'h x _ hyx _ (mem_of_mem_nhds (hW' x))
    rw [show x + ((y - x) + u) = y + u by abel] at e1
    rw [show x + ((y - x) + 0) = y by abel] at e2
    rw [e1, e2]
  refine ⟨V0 ∩ Neg.neg ⁻¹' V0, Filter.inter_mem hV0 (neg_mem_nhds_zero X hV0), fun x u hu => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact key x hx u hu.1
  by_cases hxu : x + u ∈ tsupport g
  · have := key (x + u) hxu (-u) hu.2
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem norm_absNorm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  simpa using this

theorem exists_nat_subset_nhds {F : Type} [Field F] [NumberField F] (V : Set (FiniteAdeleRing (𝓞 F) F))
    (hV : V ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ v, ‖Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v z‖ ≤ ‖(m : Fv F v)‖) → z ∈ V := by
  classical
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v => Valued.isOpen_integer _
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : IsOpenEmbedding f := RestrictedProduct.isOpenEmbedding_structureMap hopen
  have hV' : f ⁻¹' V ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := by
    rw [← Filter.mem_map, hf.map_nhds_eq]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at hV'
  obtain ⟨I, hI, t, ht, hsub⟩ := hV'
  have hk : ∀ v, ∃ k : ℕ, ∀ y : v.adicCompletionIntegers F,
      ‖(y : v.adicCompletion F)‖ ≤ ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ k → y ∈ t v := fun v => by
    have h1 := ht v
    rw [nhds_subtype, Filter.mem_comap] at h1
    obtain ⟨s, hs, hss⟩ := h1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_absNorm_lt_one v)
    refine ⟨k, fun y hy => hss (hball ?_)⟩
    rw [Metric.mem_ball, show ((0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) v : v.adicCompletion F) = 0 from rfl,
      dist_zero_right]
    exact lt_of_le_of_lt hy hk
  choose k hk using hk
  refine ⟨∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal ^ k v, Finset.prod_pos fun v _ =>
    pow_pos (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)) _, fun z hz => ?_⟩
  have hint : ∀ v, z v ∈ v.adicCompletionIntegers F := fun v =>
    Valued.toNormedField.norm_le_one_iff.1 ((hz v).trans (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _))
  have hz' : z = f (fun v => ⟨z v, hint v⟩) := by
    ext v; rfl
  rw [hz']
  refine hsub (fun v hv => hk v _ ?_)
  have hvI : v ∈ hI.toFinset := hI.mem_toFinset.2 hv
  refine (hz v).trans ?_
  rw [← Finset.mul_prod_erase _ _ hvI, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _)

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem exists_mulInt_invariant {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F,
      g (x + fun i => (a i).2) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  obtain ⟨V, hV, hinv⟩ := exists_nhds_zero_invariant g hlc hcs
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  obtain ⟨m, hm, hmV⟩ := exists_nat_subset_nhds (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨m, hm, fun a ha x => hinv x _ (hsub fun i _ => ?_)⟩
  exact Set.mem_iInter.1 (hmV _ fun v => ha.2 v i) i

theorem transInv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) → ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a →
      ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x :=
  fun g hg => exists_mulInt_invariant g hg

end GlobalTheory.SBTransl
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.PullInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_KGL_of_int {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_pullLat_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ} (ψ : B.A ≃+ (Fin n → w.adicCompletion E))
    (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (g : GLw n w) (y : B.A) :
    y ∈ pullLat w B ψ g ↔ ∀ i, ((g⁻¹ : GLw n w).val *ᵥ ψ y) i ∈ w.adicCompletionIntegers E := by
  constructor
  · intro h i
    simpa using h 1 i
  · intro h c i
    have hc : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (hB.2.1 _).1 ⟨c, rfl⟩
    have hc' : e (algebraMap K.O K.E c) ∈ w.adicCompletionIntegers E := hc
    change ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E
    rw [← algebraMap_smul K.E c y, hψ, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem hc' (h i)

theorem entries_int_of_le (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ} (ψ : B.A ≃+ (Fin n → w.adicCompletion E))
    (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (g g' : GLw n w)
    (h : pullLat w B ψ g' ≤ pullLat w B ψ g) (i j : Fin n) :
    (g⁻¹ * g').val i j ∈ w.adicCompletionIntegers E := by
  set y := ψ.symm (g'.val *ᵥ Pi.single j 1) with hy
  have hψy : ψ y = g'.val *ᵥ Pi.single j 1 := by simp [hy]
  have hy' : y ∈ pullLat w B ψ g' := by
    rw [mem_pullLat_iff w hB B ψ hψ, hψy]
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := (mem_pullLat_iff w hB B ψ hψ g y).1 (h hy') i
  rw [hψy, Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at this
  simpa using this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) →
    ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ _ w K e hB B n ψ hψ g g' h
  refine mem_KGL_of_int w _ (entries_int_of_le w hB B ψ hψ g g' h.ge) ?_
  intro a b
  have e1 : (g⁻¹ * g')⁻¹ = g'⁻¹ * g := by group
  rw [e1]
  exact entries_int_of_le w hB B ψ hψ g' g h.le a b

end GlobalTheory.KapOrb.PullInj
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.SDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_int {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (t : w.adicCompletion E) (ht : t ∈ w.adicCompletionIntegers E) : cj w t ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ⊢
  have h1 : e.symm t ∈ (algebraMap K.O K.E).range := (hB.2.1 _).2 (by simpa using ht)
  obtain ⟨o, ho⟩ := h1
  obtain ⟨o', ho'⟩ := K.c_int o
  have h2 : cj w t = e (algebraMap K.O K.E o') := by
    rw [← ho', ho, hB.1, RingEquiv.apply_symm_apply]
  rw [h2]
  exact (hB.2.1 _).1 ⟨o', rfl⟩

theorem cj_cj {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (t : w.adicCompletion E) : cj w (cj w t) = t := by
  obtain ⟨a, rfl⟩ := e.surjective t
  rw [← hB.1, ← hB.1, K.c_c]

theorem stdH_unitary {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hM : Formalism.UG.cT (cj w) M * 1 * M = 1)
    (v v' : Fin n → w.adicCompletion E) : stdH w (M *ᵥ v) (M *ᵥ v') = stdH w v v' := by
  have hM' : Mᵀ * M.map (cj w) = 1 := by
    have h := congrArg (fun X => X.map (cj w)) hM
    simp only [Formalism.UG.cT, Matrix.mul_one] at h
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
    have hid : (cj w) ∘ (cj w) = id := funext (cj_cj hB)
    rw [hid, Matrix.map_id, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hc : ∀ u : Fin n → w.adicCompletion E, (fun k => cj w ((M *ᵥ u) k)) = M.map (cj w) *ᵥ (fun k => cj w (u k)) := by
    intro u; funext k
    exact RingHom.map_mulVec (cj w) M u k
  have hs : ∀ u u' : Fin n → w.adicCompletion E, stdH w u u' = u ⬝ᵥ (fun k => cj w (u' k)) := fun _ _ => rfl
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hM', Matrix.vecMul_one]

theorem pullLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ g ∈ UL n w, GlobalTheory.UnitLemma.IsLat K.O K.E (pullLat w B ψ g) ∧ ∀ y, y ∈ pullLat w B ψ g ↔ ∀ z ∈ pullLat w B ψ g, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ w hw K e hB B x n ψ hlin hherm g hg
  set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (g⁻¹ : GLw n w).val with hMdef
  have hgi : g⁻¹ ∈ UL n w := inv_mem hg
  have hMu : Formalism.UG.cT (cj w) M * 1 * M = 1 := by
    have h := hgi
    unfold UL at h
    rw [if_neg hw] at h
    exact h
  have hMg : M * g.val = 1 := by rw [hMdef]; exact Units.inv_mul g
  have hgM : g.val * M = 1 := by rw [hMdef]; exact Units.mul_inv g
  have hint : ∀ a : K.E, a ∈ (algebraMap K.O K.E).range ↔ e a ∈ w.adicCompletionIntegers E := by
    intro a; rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hB.2.1 a
  let φ : B.A →+ (Fin n → w.adicCompletion E) :=
    (Matrix.mulVecLin M).toAddMonoidHom.comp ψ.toAddMonoidHom
  have hφ : ∀ y, φ y = M *ᵥ ψ y := fun y => rfl
  have hφs : ∀ (c : K.E) y, φ (c • y) = e c • φ y := by
    intro c y; rw [hφ, hφ, hlin, Matrix.mulVec_smul]
  have hφinj : ∀ y z, φ y = φ z → y = z := by
    intro y z h
    rw [hφ, hφ] at h
    apply ψ.injective
    have := congrArg (fun u => g.val *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec, hgM, Matrix.one_mulVec] using this
  let pre : (Fin n → w.adicCompletion E) → B.A := fun v => ψ.symm (g.val *ᵥ v)
  have hpre : ∀ v, φ (pre v) = v := by
    intro v; rw [hφ]; simp only [pre, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
  have hmem : ∀ y, y ∈ pullLat w B ψ g ↔ ∀ i, φ y i ∈ w.adicCompletionIntegers E := by
    intro y
    have key : y ∈ pullLat w B ψ g ↔ ∀ (c : K.O) (i : Fin n),
        ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E := Iff.rfl
    rw [key]
    constructor
    · intro h i
      have := h 1 i
      rwa [one_smul] at this
    · intro h c i
      rw [← algebraMap_smul K.E c y, ← hMdef, ← hφ, hφs, Pi.smul_apply, smul_eq_mul]
      exact mul_mem ((hint _).1 ⟨c, rfl⟩) (h i)
  let z : Fin n → B.A := fun i => pre (Pi.single i 1)
  have hz : ∀ i, z i ∈ pullLat w B ψ g := by
    intro i; rw [hmem]; intro j
    simp only [z, hpre, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hdecomp : ∀ (a : Fin n → K.E) y, (∀ i, e (a i) = φ y i) → y = ∑ i, a i • z i := by
    intro a y ha
    apply hφinj

    rw [map_sum]
    funext j
    rw [Finset.sum_apply]
    simp only [hφs, z, hpre, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (ha j).symm
  have hsd : ∀ y, (∀ i, φ y i ∈ w.adicCompletionIntegers E) ↔
      ∀ z' ∈ pullLat w B ψ g, B.herm x y z' ∈ (algebraMap K.O K.E).range := by
    intro y
    have hh : ∀ z', B.herm x y z' ∈ (algebraMap K.O K.E).range ↔ stdH w (φ y) (φ z') ∈ w.adicCompletionIntegers E := by
      intro z'
      rw [hint, ← hherm, hφ, hφ, SDual.stdH_unitary hB M hMu]
    constructor
    · intro hy z' hz'
      rw [hh]
      rw [hmem] at hz'
      unfold stdH
      exact sum_mem fun k _ => mul_mem (hy k) (SDual.cj_int hB _ (hz' k))
    · intro h i
      have := (hh _).1 (h (z i) (hz i))
      have hcalc : stdH w (φ y) (φ (z i)) = φ y i := by
        rw [show φ (z i) = Pi.single i 1 from hpre _]
        unfold stdH
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      rwa [hcalc] at this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.fg_def]
    refine ⟨Set.range z, Set.finite_range z, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩; exact hz i
    · intro y hy
      rw [hmem] at hy
      have hc : ∀ i, ∃ o : K.O, e (algebraMap K.O K.E o) = φ y i := by
        intro i
        obtain ⟨o, ho⟩ := (hint (e.symm (φ y i))).2 (by simpa using hy i)
        exact ⟨o, by rw [ho, RingEquiv.apply_symm_apply]⟩
      choose o ho using hc
      rw [hdecomp (fun i => algebraMap K.O K.E (o i)) y ho]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro y _
    rw [hdecomp (fun i => e.symm (φ y i)) y (fun i => by simp)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hz i))
  · intro y
    rw [hmem]
    exact hsd y

end GlobalTheory.KapOrb.SDual
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapTorus

theorem mul_of_comm_gen {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (hu : Algebra.adjoin K.E {u} = ⊤) (f : B.A → B.A) (hadd : ∀ y z, f (y + z) = f y + f z)
    (hsmul : ∀ (c : K.E) y, f (c • y) = c • f y) (hcomm : ∀ y, f (u * y) = u * f y) :
    ∀ y, f y = f 1 * y := by
  have key : ∀ s ∈ Algebra.adjoin K.E {u}, ∀ y, f (s * y) = s * f y := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hcomm
    | algebraMap c => intro y; rw [← Algebra.smul_def, hsmul, Algebra.smul_def]
    | add x y _ _ hx hy => intro z; rw [add_mul, hadd, hx, hy, add_mul]
    | mul x y _ _ hx hy => intro z; rw [mul_assoc, hx, hy, mul_assoc]
  intro y
  have := key y (hu ▸ Algebra.mem_top) 1
  rw [mul_one] at this
  rw [this, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stdH_unitary (w : Pl E) {n : ℕ} (h : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hh : cT (cj w) h * 1 * h = 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (h *ᵥ v) (h *ᵥ v') = stdH w v v' := by
  have e1 : ∀ y y' : Fin n → w.adicCompletion E, stdH w y y' = y ⬝ᵥ (fun k => cj w (y' k)) := fun _ _ => rfl
  have hmap : (fun k => cj w ((h *ᵥ v') k)) = (h.map (cj w)) *ᵥ (fun k => cj w (v' k)) := by
    funext k

    simp [Matrix.mulVec, dotProduct, map_sum]
  have ht : hᵀ * h.map (cj w) = 1 := by
    have := congrArg Matrix.transpose hh
    simpa [cT, Matrix.transpose_mul] using this
  rw [e1, e1, hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ht,
    Matrix.one_mulVec]

theorem stdH_single (w : Pl E) {n : ℕ} (v : Fin n → w.adicCompletion E) (i : Fin n) :
    stdH w v (Pi.single i 1) = v i := by
  simp [stdH, Pi.single_apply, apply_ite (cj w)]

theorem torusOf_mem_of_mem_UL_commute : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h : GLw n w, h ∈ UL n w → h * γ = γ * h → torusOf w B ψ h ∈ B.T ∧ ∀ y, ψ ((torusOf w B ψ h : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w hw K e B Q u x n γ ψ hfit hmod h hU hc
  obtain ⟨hsm, hu, hst⟩ := hmod
  have conj : ∀ g : GLw n w, g * γ = γ * g → ∀ y, ψ.symm (g.val *ᵥ ψ y) = ψ.symm (g.val *ᵥ ψ 1) * y := by
    intro g hg
    apply mul_of_comm_gen B u hfit.1 (fun y => ψ.symm (g.val *ᵥ ψ y))
    · intro y z; simp [map_add (f := _), Matrix.mulVec_add]
    · intro c y
      apply ψ.injective
      simp only [hsm, ψ.apply_symm_apply, Matrix.mulVec_smul]
    · intro y
      apply ψ.injective
      simp only [hu, ψ.apply_symm_apply, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, ← Units.val_mul, hg]
  have hc' : h⁻¹ * γ = γ * h⁻¹ := (Commute.inv_left (show Commute h γ from hc)).eq
  set a := ψ.symm (h.val *ᵥ ψ 1) with ha_def
  set b := ψ.symm ((h⁻¹ : GLw n w).val *ᵥ ψ 1) with hb_def
  have hab : a * b = 1 := by
    rw [← conj h hc b, hb_def, ψ.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, ψ.symm_apply_apply]
  let t : B.Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  have hspec : ∀ y, ψ ((t : B.A) * y) = h.val *ᵥ ψ y := by
    intro y
    show ψ (a * y) = _
    rw [← conj h hc y, ψ.apply_symm_apply]
  have htor : torusOf w B ψ h = t := torusOf_spec w B ψ h t hspec
  rw [htor]
  refine ⟨?_, hspec⟩

  have hUJ : cT (cj w) h.val * 1 * h.val = 1 := by
    have : h ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      unfold UL at hU; rwa [if_neg hw] at hU
    exact this
  have hinv : ∀ y z, B.herm x ((t : B.A) * y) ((t : B.A) * z) = B.herm x y z := by
    intro y z
    apply e.injective
    rw [← hst, ← hst, hspec, hspec, stdH_unitary w h.val hUJ]
  have hzero : ∀ y z, B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z = 0 := by
    intro y z
    have h1 : B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z =
        B.herm x ((t : B.A) * y) ((t : B.A) * z) - B.herm x y z := by
      unfold GlobalTheory.UnitLemma.InvAlg.herm
      rw [← map_sub]
      congr 1
      rw [map_mul]; ring
    rw [h1, hinv, sub_self]
  have hnd : ∀ m : B.A, (∀ z, B.herm x m z = 0) → m = 0 := by
    intro m hm
    apply ψ.injective
    rw [map_zero]
    funext i
    have := congrArg e (hm (ψ.symm (Pi.single i 1)))
    rw [← hst, ψ.apply_symm_apply, stdH_single, map_zero] at this
    simpa using this
  have := hnd _ (hzero 1)
  rw [mul_one, sub_eq_zero] at this
  exact this

end GlobalTheory.KapTorus
end
end
