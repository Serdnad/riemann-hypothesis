module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FactorFieldP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cj (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

theorem emb_cj (φ : E →+* ℂ) : φ.comp (cj E) = (starRingEnd ℂ).comp φ := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E φ x

theorem conj_eq_inv {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

abbrev Good (Q : E[X]) : Prop := ∀ τ : E →+* ℂ, ∀ z ∈ (Q.map τ).roots, ‖z‖ = 1

variable (Q : E[X]) [Fact (Irreducible Q)]

instance finL : Module.Finite E (AdjoinRoot Q) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finite

instance nfL : NumberField (AdjoinRoot Q) := NumberField.of_module_finite E (AdjoinRoot Q)

theorem root_norm (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) : ‖ψ (AdjoinRoot.root Q)‖ = 1 := by
  apply h (ψ.comp (AdjoinRoot.of Q))
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Fact.out : Irreducible Q).ne_zero), Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem csr (h : Good Q) :
    Polynomial.eval₂ ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ Q = 0 := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [Polynomial.hom_eval₂, map_zero, map_inv₀, ← conj_eq_inv (root_norm Q h ψ), ← RingHom.comp_assoc, emb_cj,
    ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero, map_zero]

def sig (h : Good Q) : AdjoinRoot Q →+* AdjoinRoot Q :=
  AdjoinRoot.lift ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ (csr Q h)

theorem sig_of (h : Good Q) (x : E) : sig Q h (AdjoinRoot.of Q x) = AdjoinRoot.of Q (IsCMField.complexConj E x) := by
  unfold sig
  erw [AdjoinRoot.lift_of]
  rfl

theorem sig_root (h : Good Q) : sig Q h (AdjoinRoot.root Q) = (AdjoinRoot.root Q)⁻¹ := by
  unfold sig
  exact AdjoinRoot.lift_root _

theorem emb_sig (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) (x : AdjoinRoot Q) :
    ψ (sig Q h x) = starRingEnd ℂ (ψ x) := by
  have e : ψ.comp (sig Q h) = (starRingEnd ℂ).comp ψ := by
    apply AdjoinRoot.ringHom_ext
    · ext y
      simp only [RingHom.coe_comp, Function.comp_apply, sig_of]
      exact IsCMField.complexEmbedding_complexConj E (ψ.comp (AdjoinRoot.of Q)) y
    · simp only [RingHom.coe_comp, Function.comp_apply, sig_root, map_inv₀]
      rw [conj_eq_inv (root_norm Q h ψ)]
  exact RingHom.congr_fun e x

theorem sig_sig (h : Good Q) (x : AdjoinRoot Q) : sig Q h (sig Q h x) = x := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [emb_sig, emb_sig, Complex.conj_conj]

theorem sig_alg (h : Good Q) (x : maximalRealSubfield E) :
    sig Q h (algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x) =
      algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x := by
  show sig Q h (AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)) =
    AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)
  rw [sig_of]
  congr 1
  exact (IsCMField.complexConj E).commutes x

def Kf (h : Good Q) : IntermediateField (maximalRealSubfield E) (AdjoinRoot Q) :=
  (RingHom.eqLocusField (sig Q h) (RingHom.id _)).toIntermediateField fun x => sig_alg Q h x

theorem mem_Kf (h : Good Q) {x : AdjoinRoot Q} : x ∈ Kf Q h ↔ sig Q h x = x := Iff.rfl

theorem totReal (h : Good Q) : IsTotallyReal (Kf Q h) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  letI : Algebra (Kf Q h) ℂ := w.embedding.toAlgebra
  let ψ : AdjoinRoot Q →ₐ[Kf Q h] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  ext x
  have hx : w.embedding x = ψ.toRingHom (x : AdjoinRoot Q) := (ψ.commutes x).symm
  rw [ComplexEmbedding.conjugate_coe_eq, hx, ← emb_sig Q h ψ.toRingHom, (mem_Kf Q h).1 x.2]

theorem decomp (h : Good Q) {S : AdjoinRoot Q} (hS : S ≠ 0) (hσS : sig Q h S = -S) (z : AdjoinRoot Q) :
    ∃ a b : Kf Q h, z = (a : AdjoinRoot Q) + S * (b : AdjoinRoot Q) := by
  have h2 : (2 : AdjoinRoot Q) ≠ 0 := two_ne_zero
  refine ⟨⟨(z + sig Q h z) / 2, ?_⟩, ⟨(z - sig Q h z) / (2 * S), ?_⟩, ?_⟩
  · rw [mem_Kf, map_div₀, map_add (f := _), sig_sig, map_ofNat]
    ring
  · rw [mem_Kf, map_div₀, map_sub, map_mul, sig_sig, map_ofNat, hσS]
    field_simp
    ring
  · show z = (z + sig Q h z) / 2 + S * ((z - sig Q h z) / (2 * S))
    field_simp
    ring

theorem finrank_KL (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (Kf Q h) (AdjoinRoot Q) = 2 := by
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q h (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  have hle : Module.finrank (Kf Q h) (AdjoinRoot Q) ≤ 2 := by
    have hspan : Submodule.span (Kf Q h) (Set.range ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]) = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨a, b, hz⟩ := decomp Q h hS hσS z
      have e : z = a • (1 : AdjoinRoot Q) + b • AdjoinRoot.of Q s := by
        rw [hz, Algebra.smul_def, Algebra.smul_def, mul_one]
        exact congrArg (fun t => (a : AdjoinRoot Q) + t) (mul_comm _ _)
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
    have := finrank_range_le_card (R := Kf Q h) ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
    exact this
  have hne1 : Module.finrank (Kf Q h) (AdjoinRoot Q) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot Q) one_ne_zero).1 h1 (AdjoinRoot.of Q s)
    rw [Algebra.smul_def, mul_one] at hc
    have hm : AdjoinRoot.of Q s ∈ Kf Q h := hc ▸ c.2
    rw [mem_Kf, hσS] at hm
    have h2 : (2 : AdjoinRoot Q) * AdjoinRoot.of Q s = 0 := by linear_combination (-1 : AdjoinRoot Q) * hm
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hS h3
  have hpos : 0 < Module.finrank (Kf Q h) (AdjoinRoot Q) := Module.finrank_pos
  omega

theorem finrank_Kf (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (maximalRealSubfield E) (Kf Q h) = Q.natDegree := by
  have h1 := Module.finrank_mul_finrank (maximalRealSubfield E) E (AdjoinRoot Q)
  haveI : IsScalarTower (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Free (maximalRealSubfield E) (Kf Q h) := Module.Free.of_divisionRing _ _
  have h2 := (letI : Module.Free (Kf Q h) (AdjoinRoot Q) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q))
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h1
  rw [finrank_KL Q h hs hsc] at h2
  omega

end PositivityTheory.Rg.BcB.G3.FactorFieldP

open PositivityTheory.Rg.BcB.G3.FactorFieldP in
theorem PositivityTheory.Rg.BcB.G3.factorField_pf : FactorField := by
  intro E _ _ _ s d hs hsc hd Q _ hmon hQ
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q hQ (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  refine ⟨Kf Q hQ, inferInstance, inferInstance, inferInstance, (Kf Q hQ).val.toRingHom, sig Q hQ,
    totReal Q hQ, finrank_Kf Q hQ hs hsc, fun x => rfl, fun x => sig_of Q hQ x, ?_, fun a => a.2, ?_⟩
  · rw [sig_root, inv_mul_cancel₀]
    intro h0
    let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have := root_norm Q hQ ψ
    rw [h0, map_zero, norm_zero] at this
    exact zero_ne_one this
  · intro z
    obtain ⟨a, b, hz⟩ := decomp Q hQ hS hσS z
    exact ⟨a, b, hz⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.AbsSumP
end PositivityTheory.Rg.BcB.G3.AbsSumP

theorem PositivityTheory.Rg.BcB.G3.absSum_pf : PositivityTheory.Rg.BcB.G3.AbsSum := by
  intro V C S L A o f D loc m N hA ho hf hD hN hcard
  set T : Set V := {v | ¬ ∀ l ∈ A v, f v l = if l = o v then 1 else 0} with hTdef
  have hT : T.Finite := Filter.eventually_cofinite.mp hf
  let _ : ∀ v, Fintype (A v) := fun v => (hA v).fintype
  obtain ⟨U, hUS, hgood⟩ : ∃ U : Finset V, (∀ v ∈ U, v ∈ S) ∧
      ∀ v, v ∈ S → v ∉ U → ∀ l ∈ A v, f v l = if l = o v then 1 else 0 := by
    refine ⟨hT.toFinset.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2, ?_⟩
    intro v hvS hvU
    by_contra h
    exact hvU (Finset.mem_filter.mpr ⟨hT.mem_toFinset.mpr h, hvS⟩)
  have hkey : ∀ c ∈ D, (∏ᶠ v ∈ S, f v (loc c v)) =
      if (∀ v ∈ S, v ∉ U → loc c v = o v) then ∏ v ∈ U, f v (loc c v) else 0 := by
    intro c hc
    obtain ⟨hcA, hcf⟩ := hD c hc
    have hW : {v | ¬ loc c v = o v}.Finite := Filter.eventually_cofinite.mp hcf
    obtain ⟨F, hUF, hFS, hWF⟩ : ∃ F : Finset V, U ⊆ F ∧ (↑F : Set V) ⊆ S ∧
        ∀ v ∈ S, ¬ loc c v = o v → v ∈ F := by
      refine ⟨U ∪ hW.toFinset.filter (fun v => v ∈ S), Finset.subset_union_left, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hv) with hv | hv
        · exact hUS v hv
        · exact (Finset.mem_filter.mp hv).2
      · intro v hvS hne
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW.mem_toFinset.mpr hne, hvS⟩)
    have hsupp : S ∩ Function.mulSupport (fun v => f v (loc c v)) ⊆ ↑F := by
      rintro v ⟨hvS, hv1⟩
      rw [Function.mem_mulSupport] at hv1
      rw [Finset.mem_coe]
      by_cases hvU : v ∈ U
      · exact hUF hvU
      · apply hWF v hvS
        intro heq
        apply hv1
        rw [hgood v hvS hvU _ (hcA v), if_pos heq]
    rw [finprod_mem_eq_prod_of_subset _ hsupp hFS]
    rw [← Finset.prod_sdiff hUF]
    have hrest : ∀ v ∈ F \ U, f v (loc c v) = if loc c v = o v then 1 else 0 := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      exact hgood v (hFS hv.1) hv.2 _ (hcA v)
    rw [Finset.prod_congr rfl hrest, Finset.prod_boole]
    have hiff : (∀ v ∈ F \ U, loc c v = o v) ↔ (∀ v ∈ S, v ∉ U → loc c v = o v) := by
      constructor
      · intro h v hvS hvU
        by_contra hne
        exact hne (h v (Finset.mem_sdiff.mpr ⟨hWF v hvS hne, hvU⟩))
      · intro h v hv
        rw [Finset.mem_sdiff] at hv
        exact h v (hFS hv.1) hv.2
    by_cases hc' : ∀ v ∈ S, v ∉ U → loc c v = o v
    · rw [if_pos (hiff.mpr hc'), if_pos hc', one_mul]
    · rw [if_neg (fun h => hc' (hiff.mp h)), if_neg hc', zero_mul]
  let zmap : C → ((v : U) → A v.1) := fun c v =>
    if h : loc c v.1 ∈ A v.1 then ⟨loc c v.1, h⟩ else ⟨o v.1, ho v.1⟩
  let yz : ((v : U) → A v.1) → (∀ v, L v) := fun z v => if h : v ∈ U then (z ⟨v, h⟩).1 else o v
  have hyz_ok : ∀ z, (∀ v, yz z v ∈ A v) ∧ (∀ᶠ v in cofinite, yz z v = o v) := by
    intro z
    refine ⟨fun v => ?_, ?_⟩
    · dsimp only [yz]
      split_ifs with h
      · exact (z ⟨v, h⟩).2
      · exact ho v
    · rw [Filter.eventually_cofinite]
      apply (U.finite_toSet).subset
      intro v hv
      by_contra hvU
      exact hv (by dsimp only [yz]; rw [dite_eq_right (fun h => hvU (Finset.mem_coe.mpr h))])
  have hfibfin : ∀ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}.Finite := by
    intro z
    have h := hcard (yz z) (hyz_ok z).1 (hyz_ok z).2
    have hne : Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact hN h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  set G : Set C := {c | c ∈ D ∧ ∀ v ∈ S, v ∉ U → loc c v = o v} with hGdef
  have hGsub : G ⊆ ⋃ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    rintro c ⟨hcD, hc⟩
    refine Set.mem_iUnion.mpr ⟨zmap c, hcD, fun v hvS => ?_⟩
    dsimp only [yz, zmap]
    by_cases hvU : v ∈ U
    · rw [dite_eq_left hvU, dite_eq_left ((hD c hcD).1 v)]
    · rw [dite_eq_right hvU]; exact hc v hvS hvU
  have hGfin : G.Finite := (Set.finite_iUnion hfibfin).subset hGsub
  have hsuppG : ∀ c, c ∈ D → (∏ᶠ v ∈ S, f v (loc c v)) ≠ 0 → c ∈ G := by
    intro c hcD hne
    rw [hkey c hcD] at hne
    by_contra hcG
    apply hne
    rw [if_neg]
    intro h; exact hcG ⟨hcD, h⟩
  refine ⟨hGfin.subset (fun c hc => hsuppG c hc.1 hc.2), ?_⟩
  have hsum1 : (∑ᶠ c : C, if c ∈ D then ∏ᶠ v ∈ S, f v (loc c v) else 0) =
      ∑ c ∈ hGfin.toFinset, ∏ v : U, f v.1 (zmap c v).1 := by
    rw [finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset) ?_]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨hcD, hcG⟩ := hc
      rw [if_pos hcD, hkey c hcD, if_pos hcG, ← Finset.prod_coe_sort U (fun v => f v (loc c v))]
      apply Finset.prod_congr rfl
      intro v _
      dsimp only [zmap]
      rw [dite_eq_left ((hD c hcD).1 v.1)]
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      by_cases hcD : c ∈ D
      · rw [if_pos hcD] at hc; exact hsuppG c hcD hc
      · rw [if_neg hcD] at hc; exact absurd rfl hc
  have hmem : ∀ z c, (c ∈ hGfin.toFinset ∧ zmap c = z) ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v) := by
    intro z c
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hcD, hcG⟩, hzc⟩
      refine ⟨hcD, fun v hvS => ?_⟩
      dsimp only [yz]
      by_cases hvU : v ∈ U
      · rw [dite_eq_left hvU, ← hzc]
        dsimp only [zmap]
        rw [dite_eq_left ((hD c hcD).1 v)]
      · rw [dite_eq_right hvU]; exact hcG v hvS hvU
    · rintro ⟨hcD, hc⟩
      refine ⟨⟨hcD, fun v hvS hvU => ?_⟩, ?_⟩
      · rw [hc v hvS]; dsimp only [yz]; rw [dite_eq_right hvU]
      · funext v
        apply Subtype.ext
        dsimp only [zmap]
        rw [dite_eq_left ((hD c hcD).1 v.1)]
        show loc c v.1 = (z v).1
        rw [hc v.1 (hUS v.1 v.2)]
        dsimp only [yz]
        rw [dite_eq_left v.2]
  have hcardfib : ∀ z (s' : Finset C), (∀ c, c ∈ s' ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)) →
      s'.card = Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    intro z s' hs'
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hs')
  rw [hsum1, ← Finset.sum_fiberwise hGfin.toFinset zmap (fun c => ∏ v : U, f v.1 (zmap c v).1),
    Finset.sum_mul]
  rw [Finset.sum_congr rfl (g := fun z => (N : ℂ) * ∏ v : U, f v.1 (z v).1) ?_, ← Finset.mul_sum]
  swap
  · intro z _
    rw [Finset.sum_congr rfl (g := fun _ => ∏ v : U, f v.1 (z v).1) ?_, Finset.sum_const, nsmul_eq_mul,
      mul_right_comm]
    swap
    · intro c hc
      rw [(Finset.mem_filter.mp hc).2]
    congr 1
    rw [← hcard (yz z) (hyz_ok z).1 (hyz_ok z).2, Nat.cast_mul,
      hcardfib z _ (fun c => Finset.mem_filter.trans (hmem z c))]
  congr 1
  have hR : ∀ v, (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = ∑ l : A v, f v l.1 := by
    intro v
    rw [finsum_eq_sum_of_support_subset _ (s := (A v).toFinset) ?_,
      Finset.sum_set_coe (f := fun l => f v l)]
    · exact Finset.sum_congr rfl (fun l hl => if_pos (Set.mem_toFinset.mp hl))
    · intro l hl
      rw [Function.mem_support] at hl
      rw [Set.coe_toFinset]
      by_contra h
      exact hl (if_neg h)
  have hR1 : ∀ v, v ∈ S → v ∉ U → (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = 1 := by
    intro v hvS hvU
    rw [hR, Finset.sum_set_coe (f := fun l => f v l),
      Finset.sum_congr rfl (fun l hl => hgood v hvS hvU l (Set.mem_toFinset.mp hl)), Finset.sum_ite_eq',
      if_pos (Set.mem_toFinset.mpr (ho v))]
  rw [← Fintype.prod_sum (fun (v : U) (l : A v.1) => f v.1 l.1)]
  rw [finprod_mem_eq_prod_of_subset _ (t := U) ?_ ?_]
  · rw [← Finset.prod_coe_sort U]
    exact Finset.prod_congr rfl (fun v _ => (hR v.1).symm)
  · rintro v ⟨hvS, hv1⟩
    by_contra hvU
    rw [Function.mem_mulSupport] at hv1
    exact hv1 (hR1 v hvS hvU)
  · intro v hv
    exact hUS v hv
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)
  have hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x) := by
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  exact ⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩

end PositivityTheory.Rg.BcB.G3

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.SuppP
end PositivityTheory.Rg.BcB.G3.SuppP

theorem PositivityTheory.Rg.BcB.G3.supp_pf : PositivityTheory.Rg.BcB.G3.Supp := by
  intro G _ _ θ K y f h
  by_contra hne
  push Not at hne
  apply h
  unfold twOrb avg
  simp only [hne, finsum_zero, mul_zero]
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end PositivityTheory.Rg.BcB.G3

end
end
