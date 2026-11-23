module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

def onComp (M : TwoLevels E r U C) (c : C) : Submodule ℂ (C → M.dom → ℂ) where
  carrier := {v | ∀ c', c' ≠ c → v c' = 0}
  add_mem' := by
    intro a b ha hb c' hc
    simp [ha c' hc, hb c' hc]
  zero_mem' := by
    intro c' _
    rfl
  smul_mem' := by
    intro t a ha c' hc
    simp [ha c' hc]

def cut (M : TwoLevels E r U C) (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] (C → M.dom → ℂ) where
  toFun v := fun c' => if c' = c then v c' else 0
  map_add' := by
    intro a b
    funext c' x
    by_cases h : c' = c <;> simp [h]
  map_smul' := by
    intro t a
    funext c' x
    by_cases h : c' = c <;> simp [h]

theorem cut_apply (M : TwoLevels E r U C) (c : C) (v : C → M.dom → ℂ) (c' : C) :
    cut M c v c' = if c' = c then v c' else 0 := rfl

theorem cutF_mem_SS (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {F : C → Frame M.Ψ r → ℂ}
    (hF : F ∈ M.SS la) : (fun c' => if c' = c then F c' else 0) ∈ M.SS la := by
  intro c'
  by_cases h : c' = c
  · simpa [h] using hF c'
  · simp only [h, if_false]
    exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem cut_mem_cusp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) : cut M c v ∈ M.cusp la := by
  have : (M.cusp la).map (cut M c) ≤ M.cusp la := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, cutF_mem_SS M la c hF, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

theorem mem_span_of_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) (hc : v ∈ onComp M c) :
    v ∈ Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
  have hcut : cut M c v = v := by
    funext c' x
    by_cases h : c' = c
    · simp [cut_apply, h]
    · simp [cut_apply, h, hc c' h]
  rw [← hcut]
  have : (M.cusp la).map (cut M c) ≤
      Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, ⟨cutF_mem_SS M la c hF, fun c' hc' => by simp [hc']⟩, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

end GlobalTheory.ShareOn.Decomp

end

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

theorem pullRep_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la))
    (hρ : IsPullRep M la ρ) (g : U) (c : C) (w : M.cusp la) (hw : (w : C → M.dom → ℂ) ∈ onComp M c) :
    ((ρ g⁻¹ w : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) := by
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨w, hwc⟩ := w
  have hs := mem_span_of_onComp M la c hwc hw
  clear hw
  revert hwc
  suffices H : ∀ h' : w ∈ M.cusp la, ((ρ g⁻¹ ⟨w, h'⟩ : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) from fun h' => H h'
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, ⟨hF, hFc⟩, rfl⟩ := hy
    intro h' c' hc'
    funext x
    have hgc : g • c' ≠ c := fun h => hc' (eq_inv_smul_iff.2 h)
    have := ha g F hF c' x
    rw [this]
    simp [TwoLevels.pull, hFc _ hgc]
  | zero =>
    intro h'
    have : (⟨0, h'⟩ : M.cusp la) = 0 := rfl
    rw [this, map_zero]
    exact (onComp M (g⁻¹ • c)).zero_mem
  | add x y hx hy ihx ihy =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have hy' : y ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hy
    have : (⟨x + y, h'⟩ : M.cusp la) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add (f := _), Submodule.coe_add]
    exact (onComp M (g⁻¹ • c)).add_mem (ihx hx') (ihy hy')
  | smul t x hx ihx =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have : (⟨t • x, h'⟩ : M.cusp la) = t • ⟨x, hx'⟩ := rfl
    rw [this, map_smul, Submodule.coe_smul]
    exact (onComp M (g⁻¹ • c)).smul_mem t (ihx hx')

end GlobalTheory.ShareOn.Decomp


open GlobalTheory.ShareOn.Decomp in
theorem GlobalTheory.ShareOn.cusp_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C]
    [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧
      ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ
  have : Fintype C := Fintype.ofFinite C
  refine ⟨fun c => (onComp M c).comap (M.cusp ka).subtype, ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro x hx hx2
      have hle : (⨆ j, ⨆ (_ : j ≠ i), (onComp M j).comap (M.cusp ka).subtype) ≤
          LinearMap.ker ((LinearMap.proj i : (C → M.dom → ℂ) →ₗ[ℂ] (M.dom → ℂ)) ∘ₗ (M.cusp ka).subtype) := by
        refine iSup₂_le fun j hj => ?_
        intro y hy
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype]
        exact hy i (Ne.symm hj)
      have h0 := hle hx2
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype] at h0
      apply Subtype.ext
      funext c'
      by_cases h : c' = i
      · subst h; simpa using h0
      · simpa using hx c' h
    · rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      have hsum : (⟨v, hv⟩ : M.cusp ka) = ∑ c, ⟨GlobalTheory.ShareOn.Decomp.cut M c v, cut_mem_cusp M ka c hv⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext c' x
        simp only [Finset.sum_apply, GlobalTheory.ShareOn.Decomp.cut_apply]
        have hh : ∀ c, (if c' = c then v c' else 0) x = if c' = c then v c' x else 0 := fun c => by
          split_ifs <;> rfl
        simp only [hh]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsum]
      refine Submodule.sum_mem_iSup fun c => ?_
      intro c' hc'
      simp [GlobalTheory.ShareOn.Decomp.cut_apply, hc']
  · intro h c v hv
    have := pullRep_onComp M ka ρ hρ h⁻¹ c v hv
    simp only [inv_inv] at this
    exact this
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

def lowScalarPt (C CH : ℝ) : PtP := fun _ _ _ p => (p.S true).L6 (p.N C CH)

end GlobalTheory.Fc.Ind

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cj_cj (τ : E →+* PadicAlgCl l) : cj (cj τ) = τ := by
  ext x; simp [cj, IsCMField.complexConj_apply_apply]

theorem cj_injective : Function.Injective (cj : (E →+* PadicAlgCl l) → (E →+* PadicAlgCl l)) := fun a b h => by
  rw [← cj_cj a, h, cj_cj]


open Classical in
def glue {ι X : Type} [Inhabited X] (inc : ι → (E →+* PadicAlgCl l)) (f g : ι → X) (i : E →+* PadicAlgCl l) : X :=
  if h : ∃ τ, inc τ = i then f h.choose else if h' : ∃ τ, cj (inc τ) = i then g h'.choose else default

theorem glue_inc {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (inc τ) = f τ := by
  have h : ∃ τ', inc τ' = inc τ := ⟨τ, rfl⟩
  rw [glue, dite_eq_left h]
  exact congrArg f (hH.1 h.choose_spec)

theorem glue_cj {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (cj (inc τ)) = g τ := by
  have h : ¬ ∃ τ', inc τ' = cj (inc τ) := fun ⟨τ', h'⟩ => hH.2.1 τ τ' h'.symm
  have h' : ∃ τ', cj (inc τ') = cj (inc τ) := ⟨τ, rfl⟩
  rw [glue, dite_eq_right h, dite_eq_left h']
  exact congrArg g (hH.1 (cj_injective h'.choose_spec))

def labels {ι : Type} (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (mu : ι → ℕ → ℕ) :
    Formalism.CohomologicalDescent.WorkedExample.Labels (E →+* PadicAlgCl l) P.Nr where
  cc := cj
  Φ := Set.range inc
  U := glue inc (fun τ a => W.U P τ (a : ℕ)) (fun τ a => (h0 P : ℤ) - W.U P τ ((Fin.rev a : Fin P.Nr) : ℕ))
  U' := glue inc (fun τ a => Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) (a : ℕ))
    (fun τ a => (h0 P : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) ((Fin.rev a : Fin P.Nr) : ℕ))
  bot := glue inc (fun τ => W.bot P τ) (fun τ => (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1))

theorem U_block {ι : Type} {P : Par} {W : Wts ι} (hOk : W.Ok P) (τ : ι) (s : ℕ) (hs : s < P.t) :
    W.U P τ (kc P + W.j τ + P.t - 1 - s) = W.bot P τ + (s : ℤ) := by
  have h1 := hOk.block τ (kc P + W.j τ + P.t - 1 - s) (by omega) (by omega)
  have h2 := hOk.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  simp only [Wts.bot, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, h1, h2]
  omega

theorem latticeLink_of_blockFor : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc ι inc hH
  obtain ⟨σ, hσF, hσc⟩ := GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj E l hdisc
  choose hf hb using hH.2.2
  classical
  set fr : ℕ → ι → ι := fun _ τ => hf (σ (inc τ)) with hfr
  set cjj : ℕ → ι → Bool := fun _ τ => decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) with hcjj
  refine ⟨fr, cjj, ?_⟩
  intro P W hP hOk hbox mu hLk hBF τ
  obtain ⟨ep, J, bot, hep, hBP, hJ⟩ := hBF
  have hall : ∀ i, ∃ τ', i = ep (inc τ') ∨ i = ep (cj (inc τ')) := by
    intro i
    rcases hep with rfl | rfl
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inl h⟩
      · exact ⟨hf i, Or.inr h⟩
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inr (by rw [cj_cj]; exact h)⟩
      · exact ⟨hf i, Or.inl h⟩
  have hUN : ∀ τ' (a : Fin P.Nr), 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ≤ (h0 P : ℤ) := by
    intro τ' a
    have h1 := ((hLk τ').2.2.1 a).2
    have ha := a.2
    have h2 := hbox τ' 0 (by omega)
    simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN] at h2 ⊢
    constructor <;> omega
  have hJb : ∀ i a, 0 ≤ J i a ∧ J i a ≤ (h0 P : ℤ) := by
    intro i a
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [((hJ τ').1 a).1]; exact hUN τ' a
    · rw [((hJ τ').1 a).2]
      have := hUN τ' (Fin.rev a)
      constructor <;> linarith [this.1, this.2]
  have hbb : ∀ i (s : Fin P.t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h0 P : ℤ) := by
    intro i s
    have hs := s.2
    have hr := hOk.what₂
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [(hJ τ').2.1]
      have e := U_block hOk τ' s hs
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - s) (by have := hr τ'; omega)
      rw [e] at b; exact b
    · rw [(hJ τ').2.2]
      have e := U_block hOk τ' (P.t - 1 - s) (by omega)
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - (P.t - 1 - s)) (by have := hr τ'; omega)
      rw [e] at b
      constructor <;> omega
  obtain ⟨O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, kap, ζ, em, jj, hN⟩ :=
    GlobalTheory.T.crystalline_block_lattices_over_power_series_ring hBS E Ω l hl2 hdisc σ hσF P.Nr P.t (h0 P) J bot hJb hbb hBP
  have hn : kc P + (reFr W fr cjj).j τ + P.t + (reFr W fr cjj).q τ = P.Nr := hOk.what₂ τ
  unfold LatticeLink
  rw [hn]
  refine ⟨E →+* PadicAlgCl l, inferInstance, σ, ‹_›, O', F, L', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, I, ‹_›, Wl, u, c,
    labels inc P W mu, fun _ => 1 - (P.Nr : ℤ), ep, J, bot, kap, ζ, em, jj, inc, ?_⟩
  refine ⟨?_, ?_, ?_, hN, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨cj_cj, fun i => hσc i, ?_, ?_, ?_, ?_⟩
    · intro i
      rcases hb i with h | h
      · exact Or.inl ⟨hf i, h.symm⟩
      · exact Or.inr ⟨hf i, by show inc (hf i) = cj i; rw [← cj_cj (inc (hf i)), ← h]⟩
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj]; ring
  ·
    rintro _ ⟨τ', rfl⟩
    have hr := hOk.what₂ τ'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := hOk.anti τ' a b hab'.le b.2
      simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := (hLk τ').1 hab.le
      simp only [Formalism.CohomologicalDescent.LD.res] at h1
      simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro s
      have hs := s.2
      refine ⟨⟨kc P + W.j τ' + P.t - 1 - s, by omega⟩, ?_⟩
      simp only [labels, glue_inc hH]
      exact U_block hOk τ' s hs
    · have hp := congrArg (Polynomial.map (ZMod.castHom (dvd_refl l) F)) (hLk τ').2.2.2
      simp only [Polynomial.map_prod, Polynomial.map_add (f := _), Polynomial.map_X, Polynomial.map_C] at hp
      simp only [map_intCast] at hp
      have e1 : ∀ a : Fin P.Nr, (((W.U P τ' (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((W.lam τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      have e2 : ∀ a : Fin P.Nr, (((Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((mu τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      simp only [labels, glue_inc hH, e1, e2]
      exact hp
  ·
    refine ⟨hep, fun i => ?_, fun i => ?_⟩
    · funext a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact ((hJ τ').1 a).1
      · simp only [labels, glue_cj hH]; exact ((hJ τ').1 a).2
    · obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact (hJ τ').2.1
      · simp only [labels, glue_cj hH]; exact (hJ τ').2.2
  · intro τ' a
    simp only [labels, glue_inc hH]
    rfl
  · intro τ'
    simp only [labels, glue_inc hH]
    rfl
  ·
    show σ (inc τ) = if decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) = true then cj (inc (hf (σ (inc τ))))
      else inc (hf (σ (inc τ)))
    by_cases h : σ (inc τ) = inc (hf (σ (inc τ)))
    · rw [decide_eq_false (not_not.mpr h), if_neg Bool.false_ne_true]; exact h
    · rcases hb (σ (inc τ)) with h' | h'
      · exact absurd h' h
      · rw [decide_eq_true h, if_pos rfl]; exact h'
  · intro a a' haa'
    obtain rfl : a = a' := Fin.ext haa'
    simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN, Formalism.CohomologicalDescent.LD.res]
  · have hs := (hLk τ).2.1
    have h2 : (∑ a : Fin P.Nr, (mu τ a : ℤ)) = ∑ a : Fin P.Nr, (W.lam τ a : ℤ) := by exact_mod_cast hs
    simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith [h2]

end GlobalTheory.ExpLink
end
end

section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MeasRd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def ratAt : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)

def ExactAt : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
    nrmR p.R.toRealDat i σ ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) =
      Real.sqrt (ratAt p i) * petW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
        (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) f

theorem measAt_of (h : ExactAt p i) (hr : 0 < ratAt p i) {K₁ K₂ : ℝ} (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂)
    (hu : Real.log (ratAt p i) ≤ K₁ * unitE p) (hl : -(K₂ * unitE p) ≤ Real.log (ratAt p i)) :
    MeasAt p i ((K₁ + K₂) / 2) := by
  intro σ
  refine ⟨Real.sqrt (ratAt p i), Real.sqrt_pos.2 hr, ?_, fun f => h σ f⟩
  rw [Real.log_sqrt hr.le]
  have key : |Real.log (ratAt p i)| ≤ (K₁ + K₂) * unitE p := by
    rcases le_or_gt 0 (unitE p) with hu0 | hu0
    · rw [abs_le]; constructor <;> nlinarith
    · have hs : K₁ + K₂ = 0 := by nlinarith
      have e1 : K₁ = 0 := by linarith
      have e2 : K₂ = 0 := by linarith
      subst e1 e2
      have : Real.log (ratAt p i) = 0 := by
        apply le_antisymm <;> simp_all
      rw [this, hs]; simp
  rw [abs_div, abs_two]
  have : |Real.log (ratAt p i)| / 2 ≤ (K₁ + K₂) * unitE p / 2 := by linarith
  linarith [this, show (K₁ + K₂) * unitE p / 2 = (K₁ + K₂) / 2 * unitE p by ring]

end GlobalTheory.CovTop.MeasRd

end
end
