module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem lc_val {n : ℕ} {w : Pl E} (hs : IsSplitAt w) {g : GLw n w → ℂ} (hg : Lc (KGL w (n := n)) g) :
    Lc (KL n w) (fun x : UL n w => g x.1) := by
  obtain ⟨K', ho, hle, hc, hk⟩ := hg
  refine ⟨K'.subgroupOf (UL n w), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_subgroupOf]
    exact ho.preimage continuous_subtype_val
  · intro x hx
    exact hle hx
  · have hU : ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) = Set.univ := by
      simp [UL, hs]
    have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
      rw [hU]; exact isClosed_univ
    exact hc.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal
  · intro k hk' x
    exact ⟨(hk k.1 hk' x.1).1, (hk k.1 hk' x.1).2⟩

private theorem unit_eq (n : ℕ) (w : Pl E) :
    (KL n w : Set (UL n w)).indicator 1 = fun x : UL n w => fn1 n w Ex.one x.1 := by
  funext x
  have hx : x ∈ (KL n w : Set (UL n w)) ↔ x.1 ∈ (KGL w (n := n) : Set (GLw n w)) := Iff.rfl
  simp only [fn1, Ex.fn, Set.indicator_apply, hx]
  rfl

private theorem split_level {a b : ℕ} {w : Pl E} (hs : IsSplitAt w) {φ : GLw a w × GLw b w → ℂ}
    (hφ : Lc (K2 a b w) φ) : ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w)),
      IsLevel (thL a w) (KGL w (n := a)) K₁ ∧ IsLevel (thL b w) (KGL w (n := b)) K₂ ∧ IsHecke (K₁.prod K₂) φ := by
  obtain ⟨K', ho, hle, hc, hk⟩ := hφ
  refine ⟨K'.comap (MonoidHom.inl _ _), K'.comap (MonoidHom.inr _ _), ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hc, ?_⟩
  · exact ho.preimage (continuous_id.prodMk continuous_const)
  · intro x hx
    exact (hle hx).1
  · intro k hk'
    simpa [thL, hs] using hk'
  · exact ho.preimage (continuous_const.prodMk continuous_id)
  · intro x hx
    exact (hle hx).2
  · intro k hk'
    simpa [thL, hs] using hk'
  · rintro ⟨k₁, k₂⟩ ⟨h₁, h₂⟩ x
    have hm : ((k₁, k₂) : GLw a w × GLw b w) ∈ K' := by
      have := K'.mul_mem h₁ h₂
      simpa using this
    exact hk _ hm x

private theorem inv_un {μ : HChar E} {w : Pl E} (hm : μ.val (cPl w) = (μ.val w)⁻¹) (a b : ℕ)
    (B₁ B₂ : Multiset ℂˣ) : inv (un μ a b (cPl w) B₁ B₂) = un μ a b w (inv B₁) (inv B₂) := by
  simp only [inv, un, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, hm, mul_inv, inv_pow, inv_inv]

private theorem match_inert {n a b : ℕ} {w : Pl E} (hs : ¬ IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    {f : UL n w → ℂ} {φ : GLw a w × GLw b w → ℂ} (H : Match n a b w 1 f φ) : Match n a b w μ f φ := by
  intro Q₁ Q₂ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have := H Q₁ Q₂ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [this]
  simp only [delta, if_neg hs]

theorem rFamMatch : RFamMatch := by
  intro hUm hSp hPl hAct hH2 hCt hMu E _ _ _ hUnr n μ ε hμ S hS Z hZ hZμ f hf a b h
  obtain ⟨-, hPl2, -, hPl4⟩ := hPl E
  have hOff : ∀ w ∈ S, IsSplitAt w → w ∉ Z → Off Z w := fun w hw hs hwZ =>
    ⟨hwZ, fun hc => ((hPl2 w).2.1 hs) (((hPl4 S hS) w).2 hw (hZ _ hc).1)⟩
  have hT0 : ∀ w : Pl E, ∃ t : Fin (n + 1) → Ex (Fin (a + 1) × Fin (b + 1)), IsSplitAt w → μ.UnrAt w →
      (∀ e, (ctMu h w (μ.loc w) fun x : UL n w => fn1 n w e x.1) = fn2 a b w (e.bind t)) ∧
      ∀ e B₁ B₂, B₁.card = a → B₂.card = b → ev2 a b w (e.bind t) B₁ B₂ = ev1 n w e (un μ a b w B₁ B₂) := by
    intro w
    by_cases hc : IsSplitAt w ∧ μ.UnrAt w
    · obtain ⟨t, ht⟩ := hCt E w hc.1 μ hc.2 n a b h
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨fun _ => Ex.one, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose t ht using hT0
  have hLcZ : ∀ w ∈ Z, Lc (KL n w) (fun x : UL n w => f w x.1) := fun w hw => lc_val (hZ w hw).2 (hf w hw)
  have hCtLc : ∀ w ∈ Z, Lc (K2 a b w) (ct0 μ h f w) := fun w hw =>
    (hSp E w (hZ w hw).2 n a b h μ _ (hLcZ w hw)).1
  refine ⟨hCtLc, t, ?_⟩
  intro T hT hTZ e₁ e₂
  have hTnZ : ∀ w ∈ T, w ∉ Z := fun w hw hz => Finset.disjoint_left.1 hTZ hw hz
  have hbasic := fun (m : ℕ) (w : Pl E) => GlobalTheory.BCT.ThBasic.twist_basic E hUnr m w
  refine ⟨?_, ?_⟩
  · intro B₁ B₂ hB
    simp only [val, val1]
    refine Finset.prod_congr rfl fun w hw => ?_
    have hs := (hT w hw).2
    have hO := hOff w (hT w hw).1 hs (hTnZ w hw)
    have hu := hZμ w hO
    have hO' : Off Z (cPl w) := ⟨hO.2, by rw [(hPl2 w).1]; exact hO.1⟩
    have hm := hMu E μ ε hμ w hs hu
    have c1 := (ht w hs hu).2 (e₁ w) (B₁ w) (B₂ w) (hB w hO).1 (hB w hO).2
    have c2 := (ht w hs hu).2 (e₂ w) (inv (B₁ (cPl w))) (inv (B₂ (cPl w)))
      (by simp [inv, (hB _ hO').1]) (by simp [inv, (hB _ hO').2])
    rw [c1, c2, inv_un hm]
  · intro k
    have hfam : ∀ w ∈ S, fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t w)) (fun w => (e₂ w).bind (t w)) k w =
        if IsSplitAt w then ctMu h w (μ.loc w) (famU Z T f e₁ e₂ k w) else (K2 a b w : Set _).indicator 1 := by
      intro w hw
      by_cases hs : IsSplitAt w
      · rw [if_pos hs]
        by_cases hz : w ∈ Z
        · simp only [fam, famU, if_pos hz]
          rfl
        · have hu := hZμ w (hOff w hw hs hz)
          by_cases hwT : w ∈ T
          · simp only [fam, famU, if_neg hz, if_pos hwT]
            rw [(ht w hs hu).1 (((e₁ w).pow k).mul ((e₂ w).pow k))]
            simp only [Ex.bind, Ex.bind_pow]
          · simp only [fam, famU, if_neg hz, if_neg hwT]
            rw [unit_eq, (ht w hs hu).1 Ex.one]
            simp only [fn2, Ex.bind, Ex.fn]
      · have hz : w ∉ Z := fun hz => hs (hZ w hz).2
        have hwT : w ∉ T := fun hz => hs (hT w hz).2
        simp only [fam, if_neg hz, if_neg hwT, if_neg hs]
    have hLcU : ∀ w, IsSplitAt w → Lc (KL n w) (famU Z T f e₁ e₂ k w) := by
      intro w hs
      have hK : ∀ e, Lc (KGL w (n := n)) (fn1 n w e) := fun e =>
        ⟨KGL w (n := n), (hbasic n w).2.2.2.2.1, le_rfl, (hAct E n w e).1⟩
      by_cases hz : w ∈ Z
      · simp only [famU, if_pos hz]
        exact hLcZ w hz
      · by_cases hwT : w ∈ T
        · simp only [famU, if_neg hz, if_pos hwT]
          exact lc_val hs (hK _)
        · simp only [famU, if_neg hz, if_neg hwT]
          rw [unit_eq]
          exact lc_val hs (hK _)
    have hlev : ∀ w : Pl E, ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w)),
        IsLevel (thL a w) (KGL w (n := a)) K₁ ∧ IsLevel (thL b w) (KGL w (n := b)) K₂ ∧
        IsHecke (K₁.prod K₂) (fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t w)) (fun w => (e₂ w).bind (t w)) k w) ∧
        (w ∉ Z → K₁ = KGL w (n := a) ∧ K₂ = KGL w (n := b)) := by
      intro w
      by_cases hz : w ∈ Z
      · obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := split_level (hZ w hz).2 (hCtLc w hz)
        refine ⟨K₁, K₂, h₁, h₂, ?_, fun hn => absurd hz hn⟩
        simp only [fam, if_pos hz]
        exact h₃
      · refine ⟨KGL w (n := a), KGL w (n := b), ⟨(hbasic a w).2.2.2.2.1, le_rfl, (hbasic a w).2.2.1⟩,
          ⟨(hbasic b w).2.2.2.2.1, le_rfl, (hbasic b w).2.2.1⟩, ?_, fun _ => ⟨rfl, rfl⟩⟩
        by_cases hwT : w ∈ T
        · simp only [fam, if_neg hz, if_pos hwT]
          exact hH2 E a b w _
        · simp only [fam, if_neg hz, if_neg hwT]
          exact hH2 E a b w Ex.one
    choose K₁ K₂ hk1 hk2 hk3 hk4 using hlev
    have hev : ∀ᶠ w : Pl E in cofinite, w ∉ Z :=
      Filter.eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => by simpa using hw)
    have hev2 : ∀ᶠ w : Pl E in cofinite, w ∉ Z ∧ w ∉ T :=
      Filter.eventually_cofinite.2 ((Z ∪ T).finite_toSet.subset fun w hw => by
        by_contra hc
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hc
        exact hw hc)
    refine ⟨⟨K₁, K₂, ⟨hk1, hev.mono fun w hw => (hk4 w hw).1⟩, ⟨hk2, hev.mono fun w hw => (hk4 w hw).2⟩,
      hk3, hev2.mono fun w hw => ?_⟩, ?_⟩
    · simp only [fam, if_neg hw.1, if_neg hw.2]
    · intro w hw
      refine ⟨?_, hfam w hw⟩
      rw [hfam w hw]
      by_cases hs : IsSplitAt w
      · rw [if_pos hs]
        exact (hSp E w hs n a b h μ _ (hLcU w hs)).2
      · rw [if_neg hs]
        have hz : w ∉ Z := fun hz => hs (hZ w hz).2
        have hwT : w ∉ T := fun hz => hs (hT w hz).2
        have hU : famU Z T f e₁ e₂ k w = (KL n w : Set (UL n w)).indicator 1 := by
          simp only [famU, if_neg hz, if_neg hwT]
        rw [hU]
        exact match_inert hs _ (hUm E hUnr w hs n a b h)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

section

noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep Matrix
open UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem rStab_ind (K' : Subgroup G) :
    rStab ((K' : Set G).indicator (1 : G → ℂ)) = K' := by
  classical
  ext k
  constructor
  · intro hk
    have h := hk 1
    simp only [one_mul] at h
    by_contra hn
    rw [Set.indicator_of_notMem (by simpa using hn), Set.indicator_of_mem (by simp [K'.one_mem])] at h
    simp at h
  · intro hk x
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem (show x * k ∈ (K' : Set G) from K'.mul_mem hx hk),
        Set.indicator_of_mem (show x ∈ (K' : Set G) from hx)]
      rfl
    · have hxk : x * k ∉ K' := fun h => hx (by simpa using K'.mul_mem h (K'.inv_mem hk))
      rw [Set.indicator_of_notMem (show x * k ∉ (K' : Set G) from hxk),
        Set.indicator_of_notMem (show x ∉ (K' : Set G) from hx)]

private theorem ind_inv (K' : Subgroup G) :
    (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = (K' : Set G).indicator (1 : G → ℂ) := by
  classical
  funext y
  by_cases hy : y ∈ K'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (K' : Set G) from K'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (K' : Set G) from hy)]
    rfl
  · have : y⁻¹ ∉ K' := fun h => hy (by simpa using K'.inv_mem h)
    rw [Set.indicator_of_notMem (show y⁻¹ ∉ (K' : Set G) from this),
      Set.indicator_of_notMem (show y ∉ (K' : Set G) from hy)]

private theorem levOp_ind (ρ : Representation ℂ G V) (K K' : Subgroup G) (x : V) (hx : x ∈ fixed ρ K') :
    levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  classical
  have hfx : ∀ h ∈ K', ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ K', q.out ∈ K' ↔ q = (QuotientGroup.mk 1 : G ⧸ K') := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ K') = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using K'.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      have := QuotientGroup.mk_out_eq_mul K' (1 : G)
      obtain ⟨h, hh⟩ := this
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')]
  · rw [Set.indicator_of_mem (show (QuotientGroup.mk 1 : G ⧸ K').out ∈ (K' : Set G) from (hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [Set.indicator_of_notMem (show q.out ∉ (K' : Set G) from fun h => hq ((hout q).1 h))]
    simp

private theorem trc_ind_ne (ρ : Representation ℂ G V) (K K' : Subgroup G) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ K')) (hne : fixed ρ K' ≠ ⊥) :
    trc ρ K ((K' : Set G).indicator (1 : G → ℂ)) ≠ 0 := by
  have hlev : K ⊓ rStab ((K' : Set G).indicator (1 : G → ℂ)) ⊓
      rStab (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = K' := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [levOp_ind ρ K K' v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id).restrict hc =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K K' v v.2]
  unfold twTr
  rw [dite_eq_left hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ K') ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.levelFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.LevelFn := by
  intro E _ _ _ n w τ
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hnt : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (Subrepresentation τ.ρ) :=
      ⟨fun a b => by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _⟩
    haveI := τ.irred
    exact not_subsingleton (Subrepresentation τ.ρ) hs
  obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
  let U : Subgroup (GLw n w) :=
    { carrier := {g | τ.ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hU : IsOpen (U : Set (GLw n w)) := τ.smooth v
  let K' : Subgroup (GLw n w) := U ⊓ GlobalTheory.LFun.KGL w (n := n)
  have hKo : IsOpen (K' : Set (GLw n w)) := hU.inter ho
  have hKc : IsCompact (K' : Set (GLw n w)) := hc.inter_left (U.isClosed_of_isOpen hU)
  have hle : K' ≤ GlobalTheory.LFun.KGL w (n := n) := inf_le_right
  have hfd : FiniteDimensional ℂ (fixed τ.ρ K') := finiteDimensional_fixed_openSubgroup_GLw E n w τ K' hKo
  have hne : fixed τ.ρ K' ≠ ⊥ := by
    intro hb
    have hm : v ∈ fixed τ.ρ K' := fun h => by
      have h1 : τ.ρ h v = v := h.2.1
      simpa using h1
    rw [hb] at hm
    exact hv ((Submodule.mem_bot ℂ).1 hm)
  have hi : K'.relIndex (GlobalTheory.LFun.KGL w (n := n)) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w (n := n)) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
      Subgroup.quotient_finite_of_isOpen _ (hKo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)))).index_ne_zero
  refine ⟨(K' : Set (GLw n w)).indicator 1, ⟨K', hKo, hle, ?_, ?_⟩, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trc_ind_ne τ.ρ _ K' hle hi hfd hne⟩
  · exact HasCompactSupport.intro' hKc (K'.isClosed_of_isOpen hKo) fun x hx => Set.indicator_of_notMem hx _
  · classical
    intro k hk x
    have h1 : (k * x ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_left hk
    have h2 : (x * k ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_right hk
    show (K' : Set (GLw n w)).indicator 1 (k * x) = _ ∧ (K' : Set (GLw n w)).indicator 1 (x * k) = _
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [h1, h2, Pi.one_apply, and_self]
end
end
