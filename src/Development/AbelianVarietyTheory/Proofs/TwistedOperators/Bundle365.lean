module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

def splitVar {n m σ : Type} (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s) :
    (n × {s // Q s}) ⊕ {ls : m × σ // P (Sum.inr ls.1, ls.2)} ≃ {rs // P rs} where
  toFun := Sum.elim (fun a => ⟨(Sum.inl a.1, a.2.1), (h _ _).2 a.2.2⟩) (fun a => ⟨(Sum.inr a.1.1, a.1.2), a.2⟩)
  invFun := fun a => match a with
    | ⟨(Sum.inl r, s), hs⟩ => Sum.inl (r, ⟨s, (h _ _).1 hs⟩)
    | ⟨(Sum.inr l, s), hs⟩ => Sum.inr ⟨(l, s), hs⟩
  left_inv := by rintro (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rfl
  right_inv := by rintro ⟨⟨r | r, s⟩, hs⟩ <;> rfl

theorem det_colwise_fromBlocks {k : Type} [CommRing k] {n m σ : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype σ] (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s)
    [Fintype {rs // P rs}] [DecidableEq {rs // P rs}] (κ : Matrix n n k)
    (M : Matrix {rs // P rs} {rs // P rs} k)
    (hM : ∀ a b, M a b = if a.1.2 = b.1.2 then (fromBlocks κ 0 0 1 : Matrix (n ⊕ m) (n ⊕ m) k) a.1.1 b.1.1 else 0) :
    M.det = κ.det ^ Fintype.card {s // Q s} := by
  rw [← det_submatrix_equiv_self (splitVar P Q h) M]
  have : M.submatrix (splitVar P Q h) (splitVar P Q h) =
      fromBlocks (blockDiagonal fun _ : {s // Q s} => κ) 0 0 1 := by
    ext a b
    rcases a with (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rcases b with (⟨r', s', hs'⟩ | ⟨⟨l', s'⟩, hs'⟩) <;>
      simp [hM, splitVar, blockDiagonal_apply, one_apply]
    by_cases h1 : s = s' <;> by_cases h2 : l = l' <;> simp [h1, h2, Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_fromBlocks_zero₂₁, det_blockDiagonal]
  simp

theorem valuation_det_stepLin_embX : ∀ {k : Type} [Field k] [ValuativeRel k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (κ : GL n k), valuation k (gdet κ : k) = 1 → valuation k (stepLin n' (embX c κ).val).det = 1 := by
  intro k _ _ n n' _ _ _ _ c κ hκ
  let Q : n' ⊕ Fin (c + 1) → Prop := Sum.elim (fun _ => False)
    (fun i => c / 2 + 1 < i.val + 1 ∨ (Even c ∧ i.val = c / 2))
  have h : ∀ (r : n) s, (Free (c := c) (c / 2 + 1) (Sum.inl r, s) ∨ Kept (c := c) (Sum.inl r, s)) ↔ Q s := by
    rintro r (s | s) <;> simp [Q, Free, Kept]
  rw [det_colwise_fromBlocks (fun rs => Free (c / 2 + 1) rs ∨ Kept rs) Q h κ.val _ (fun a b => by
    simp only [stepLin, of_apply]; split_ifs <;> rfl), map_pow]
  have : valuation k κ.val.det = 1 := hκ
  rw [this, one_pow]

end GlobalTheory.StepLeft
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.RealQuot.SemisimpleSpan

open GlobalTheory.RealQuot

theorem isStab_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] {σ : ι → Module.End ℂ M}
    (W : κ → Submodule ℂ M) (h : ∀ k, IsStab σ (W k)) : IsStab σ (⨆ k, W k) := by
  intro i
  have hle : (⨆ k, W k) ≤ (⨆ k, W k).comap (σ i) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (h k i x hx)
  exact fun x hx => hle hx

theorem exists_stab_compl_of_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (σ : ι → Module.End ℂ M)
    (W : κ → Submodule ℂ M) (hW : ∀ k, IsStab σ (W k))
    (hs : ∀ k (V : Submodule ℂ M), IsStab σ V → V ≤ W k → V = ⊥ ∨ V = W k) (htop : ⨆ k, W k = ⊤) :
    ∀ N : Submodule ℂ M, IsStab σ N → ∃ N' : Submodule ℂ M, IsStab σ N' ∧ IsCompl N N' := by
  letI : Module (FreeAlgebra ℂ ι) M :=
    Module.compHom M (FreeAlgebra.lift ℂ σ : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ M).toRingHom
  have smul_def : ∀ (a : FreeAlgebra ℂ ι) (x : M), a • x = FreeAlgebra.lift ℂ σ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ (FreeAlgebra ℂ ι) M := ⟨fun c a x => by
    rw [smul_def, smul_def, map_smul]
    rfl⟩
  have key : ∀ N : Submodule ℂ M, IsStab σ N →
      ∃ W' : Submodule (FreeAlgebra ℂ ι) M, W'.restrictScalars ℂ = N := by
    intro N hN
    have hst : ∀ a : FreeAlgebra ℂ ι, ∀ x ∈ N, FreeAlgebra.lift ℂ σ a x ∈ N := by
      intro a
      induction a using FreeAlgebra.induction with
      | grade0 r =>
        intro x hx
        rw [AlgHom.commutes, Module.algebraMap_end_apply]
        exact N.smul_mem r hx
      | grade1 i =>
        intro x hx
        rw [FreeAlgebra.lift_ι_apply]
        exact hN i x hx
      | mul a b ha hb =>
        intro x hx
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb x hx)
      | add a b ha hb =>
        intro x hx
        rw [map_add (f := _), LinearMap.add_apply]
        exact N.add_mem (ha x hx) (hb x hx)
    refine ⟨{ carrier := N
              add_mem' := N.add_mem
              zero_mem' := N.zero_mem
              smul_mem' := fun a x hx => hst a x hx }, ?_⟩
    ext x
    rfl
  have stabR : ∀ W' : Submodule (FreeAlgebra ℂ ι) M, IsStab σ (W'.restrictScalars ℂ) := by
    intro W' i x hx
    have : σ i x = (FreeAlgebra.ι ℂ i) • x := by rw [smul_def, FreeAlgebra.lift_ι_apply]
    rw [this]
    exact W'.smul_mem _ hx
  have hss : IsSemisimpleModule (FreeAlgebra ℂ ι) M := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, ← Submodule.restrictScalars_eq_top_iff ℂ,
      eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    obtain ⟨Wk, hWk⟩ := key (W k) (hW k)
    rw [← hWk]
    refine Submodule.restrictScalars_mono ℂ ?_
    by_cases h0 : Wk = ⊥
    · rw [h0]
      exact bot_le
    · refine le_sSup (isSimpleModule_iff_isAtom.2 ⟨h0, fun V hV => ?_⟩)
      rcases hs k (V.restrictScalars ℂ) (stabR V) (hWk ▸ Submodule.restrictScalars_mono ℂ hV.le) with h | h
      · exact (Submodule.restrictScalars_eq_bot_iff ℂ _ _).1 h
      · exact absurd ((Submodule.restrictScalars_injective ℂ _ _) (h.trans hWk.symm)) hV.ne
  intro N hN
  obtain ⟨WN, hWN⟩ := key N hN
  obtain ⟨W', hc⟩ := exists_isCompl WN
  refine ⟨W'.restrictScalars ℂ, stabR W', ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, ← hWN, ← Submodule.restrictScalars_inf, hc.inf_eq_bot]
    rfl
  · rw [codisjoint_iff, ← hWN, ← Submodule.restrictScalars_sup, hc.sup_eq_top]
    rfl

theorem exists_stab_compl : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  intro ι J Fm Q Pi _ _ _ _ ρ C σ τ β hH hint hker hτ hspan hirr
  obtain ⟨⟨L, hL⟩, -⟩ := hH
  have hcomm : ∀ f i x, β f (ρ i x) = σ i (β f x) := fun f i x => by
    rw [← LinearMap.comp_apply (β f) (ρ i), hint f i, LinearMap.comp_apply]
  let K : Submodule ℂ Q := ⨅ f, LinearMap.ker (β f)
  have hKf : ∀ f, K ≤ LinearMap.ker (β f) := fun f => iInf_le _ f
  have hKs : IsStab ρ K := by
    intro i x hx
    refine Submodule.mem_iInf _ |>.2 fun f => ?_
    rw [LinearMap.mem_ker, hcomm, LinearMap.mem_ker.1 (hKf f hx), map_zero]
  have hCK : C ≤ K := le_iInf hker

  have hmapS : ∀ S : Submodule ℂ Q, IsStab ρ S → ∀ f, IsStab σ (S.map (β f)) := by
    rintro S hS f i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, hS i x hx, hcomm f i x⟩
  have hNS : ∀ S : Submodule ℂ Q, IsStab ρ S → (⨆ f, S.map (β f)) = ⊥ ∨ (⨆ f, S.map (β f)) = ⊤ := by
    intro S hS
    refine hirr _ (isStab_iSup _ (hmapS S hS)) ?_
    intro j
    have hle : (⨆ f, S.map (β f)) ≤ (⨆ f, S.map (β f)).comap (τ j) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f', hf'⟩ := hτ j f
      show τ j (β f x) ∈ ⨆ f, S.map (β f)
      rw [← LinearMap.comp_apply, hf']
      exact Submodule.mem_iSup_of_mem f' ⟨x, hx, rfl⟩
    exact fun x hx => hle hx

  obtain ⟨S, hSst, hStop, hsimp⟩ : ∃ S : Submodule ℂ Q, IsStab ρ S ∧ (⨆ f, S.map (β f)) = ⊤ ∧
      ∀ f (V : Submodule ℂ Pi), IsStab σ V → V ≤ S.map (β f) → V = ⊥ ∨ V = S.map (β f) := by
    by_cases hK : K = ⊤
    · refine ⟨⊤, fun i x _ => Submodule.mem_top, by simpa [Submodule.map_top] using hspan, fun f V _ hV => Or.inl ?_⟩
      have h0 : (⊤ : Submodule ℂ Q).map (β f) = ⊥ := by
        rw [Submodule.map_top, LinearMap.range_eq_bot]
        exact LinearMap.ker_eq_top.1 (top_le_iff.1 (hK ▸ hKf f))
      exact le_bot_iff.1 (h0 ▸ hV)
    · let T : Type := {S : Submodule ℂ Q // IsStab ρ S ∧ C ≤ S}
      have wf : WellFounded (fun x y : T => x.1 < y.1) := by
        refine ⟨fun x => ?_⟩
        by_contra hx
        obtain ⟨g, -, hg⟩ := not_acc_iff_exists_descending_chain.1 hx
        have anti : StrictAnti fun n => (g n).1 := strictAnti_nat_of_succ_lt hg
        have mono : StrictMono fun k : Fin (L + 1) => (g (L - k.1)).1 := by
          intro a b hab
          exact anti (by have := a.2; have := b.2; simp only [Fin.lt_def] at hab; omega)
        have := hL (L + 1) _ mono fun k => (g (L - k.1)).2
        omega
      obtain ⟨M, hMK0, hMmin⟩ := wf.has_min {x : T | K < x.1}
        ⟨⟨⊤, fun i x _ => Submodule.mem_top, le_top⟩, lt_top_iff_ne_top.2 hK⟩
      have hMK : K < M.1 := hMK0
      refine ⟨M.1, M.2.1, ?_, ?_⟩
      · rcases hNS M.1 M.2.1 with h | h
        · exfalso
          refine hMK.2 (le_iInf fun f => ?_)
          intro x hx
          have h1 : β f x ∈ M.1.map (β f) := Submodule.mem_map_of_mem hx
          rw [iSup_eq_bot.1 h f] at h1
          exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h1)
        · exact h
      · intro f V hVs hV
        let U : Submodule ℂ Q := M.1 ⊓ V.comap (β f)
        have hUs : IsStab ρ U := by
          rintro i x ⟨hx1, hx2⟩
          refine ⟨M.2.1 i x hx1, ?_⟩
          show β f (ρ i x) ∈ V
          rw [hcomm]
          exact hVs i _ hx2
        have hKU : K ≤ U := fun x hx => ⟨hMK.le hx, by
          show β f x ∈ V
          rw [LinearMap.mem_ker.1 (hKf f hx)]
          exact V.zero_mem⟩
        by_cases hlt : K < U
        · right
          have hUM : U = M.1 := by
            by_contra hne
            exact hMmin ⟨U, hUs, hCK.trans hKU⟩ hlt (lt_of_le_of_ne inf_le_left hne)
          refine le_antisymm hV ?_
          rintro _ ⟨x, hx, rfl⟩
          have : x ∈ U := hUM ▸ hx
          exact this.2
        · left
          have hUK : U = K := (eq_of_le_of_not_lt hKU hlt).symm
          rw [eq_bot_iff]
          intro v hv
          obtain ⟨x, hx, rfl⟩ := hV hv
          have : x ∈ U := ⟨hx, hv⟩
          rw [hUK] at this
          exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hKf f this))
  exact exists_stab_compl_of_iSup σ (fun f => S.map (β f)) (hmapS S hSst) hsimp hStop

end GlobalTheory.RealQuot.SemisimpleSpan

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem simpleQuot_iso_of_intertwined : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  intro ι Fm Q Q' Pi _ _ _ _ _ _ ρ C ρ' C' σ β β₁ hβ hβ₁ hkβ hkβ₁ hβ₁0 hspan hQ hQ' hss
  set R := rad ρ C with hRdef
  set R' := rad ρ' C' with hR'def

  have kerStab : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : ι → Module.End ℂ X) (g : X →ₗ[ℂ] Pi),
      (∀ i, g ∘ₗ τ i = σ i ∘ₗ g) → IsStab τ (LinearMap.ker g) := by
    intro X _ _ τ g hg i x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hg i, LinearMap.comp_apply, hx, map_zero]
  set U := LinearMap.range β₁ with hUdef
  have hUs : IsStab σ U := by
    rintro i _ ⟨x, rfl⟩
    exact ⟨ρ' i x, by rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]⟩

  have hUsimple : ∀ Wm : Submodule ℂ Pi, IsStab σ Wm → Wm ≤ U → Wm ≠ ⊥ → Wm = U := by
    intro Wm hW hWU hW0
    have hcs : IsStab ρ' (Wm.comap β₁) := fun i x hx => by
      show β₁ (ρ' i x) ∈ Wm
      rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]
      exact hW i _ hx
    have hcR : R' ≤ Wm.comap β₁ := fun x hx => by
      show β₁ x ∈ Wm
      rw [LinearMap.mem_ker.1 (hkβ₁ hx)]
      exact Wm.zero_mem
    rcases hQ' _ hcs hcR with h | h
    · exfalso
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, rfl⟩ := hWU hw
      have : x ∈ Wm.comap β₁ := hw
      rw [h] at this
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hkβ₁ this))
    · refine le_antisymm hWU ?_
      rintro _ ⟨x, rfl⟩
      have : x ∈ Wm.comap β₁ := h ▸ Submodule.mem_top
      exact this
  obtain ⟨N', hN's, hc⟩ := hss U hUs
  let P : Pi →ₗ[ℂ] Pi := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U N' hc
  have hPU : ∀ y ∈ U, P y = y := fun y hy =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)
  have hPN : ∀ y ∈ N', P y = 0 := fun y hy => by
    exact (congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨y, hy⟩) :)
  have hPmem : ∀ y, P y ∈ U := fun y => (Submodule.linearProjOfIsCompl U N' hc y).2
  have hdec : ∀ y : Pi, ∃ u ∈ U, ∃ n ∈ N', y = u + n := by
    intro y
    have : y ∈ U ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, n, hn, h⟩ := Submodule.mem_sup.1 this
    exact ⟨u, hu, n, hn, h.symm⟩
  have hPσ : ∀ i y, P (σ i y) = σ i (P y) := by
    intro i y
    obtain ⟨u, hu, n, hn, rfl⟩ := hdec y
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hPU _ (hUs i u hu), hPN _ (hN's i n hn), hPU u hu, hPN n hn, add_zero, add_zero]

  obtain ⟨f, hf⟩ : ∃ f, P ∘ₗ β f ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : ∀ f, LinearMap.range (β f) ≤ N' := by
      rintro f _ ⟨x, rfl⟩
      obtain ⟨u, hu, n, hn, he⟩ := hdec (β f x)
      have h0 : P (β f x) = 0 := by rw [← LinearMap.comp_apply, hall f, LinearMap.zero_apply]
      rw [he, map_add (f := _), hPU u hu, hPN n hn, add_zero] at h0
      rw [he, h0, zero_add]; exact hn
    have hN'top : N' = ⊤ := eq_top_iff.2 (hspan ▸ iSup_le hle)
    have hU0 : U = ⊥ := by
      have := hc.inf_eq_bot
      rwa [hN'top, inf_top_eq] at this
    apply hβ₁0
    ext x
    have : β₁ x ∈ U := LinearMap.mem_range_self β₁ x
    rw [hU0, Submodule.mem_bot] at this
    exact this
  set γ := P ∘ₗ β f with hγdef
  have hγi : ∀ i, γ ∘ₗ ρ i = σ i ∘ₗ γ := by
    intro i; ext x
    show P (β f (ρ i x)) = σ i (P (β f x))
    have h := LinearMap.congr_fun (hβ f i) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hPσ]
  have hRγ : R ≤ LinearMap.ker γ := fun x hx => by
    rw [LinearMap.mem_ker, hγdef, LinearMap.comp_apply, LinearMap.mem_ker.1 (hkβ f hx), map_zero]
  have hkerγ : LinearMap.ker γ = R := by
    rcases hQ _ (kerStab ρ γ hγi) hRγ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf
  have hkerβ₁ : LinearMap.ker β₁ = R' := by
    rcases hQ' _ (kerStab ρ' β₁ hβ₁) hkβ₁ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hβ₁0
  have hrangeγ : LinearMap.range γ = U := by
    apply hUsimple
    · rintro i _ ⟨x, rfl⟩
      exact ⟨ρ i x, by rw [← LinearMap.comp_apply, hγi i, LinearMap.comp_apply]⟩
    · rintro _ ⟨x, rfl⟩; exact hPmem _
    · intro h
      apply hf
      ext x
      have : γ x ∈ LinearMap.range γ := LinearMap.mem_range_self γ x
      rw [h, Submodule.mem_bot] at this
      exact this
  let φ := R.liftQ γ hRγ
  let ψ := R'.liftQ β₁ hkβ₁
  have hφi : Function.Injective φ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerγ.le)
  have hψi : Function.Injective ψ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerβ₁.le)
  have hrφ : LinearMap.range φ = LinearMap.range ψ := by
    rw [Submodule.range_liftQ, Submodule.range_liftQ, hrangeγ]
  let e : (Q ⧸ R) ≃ₗ[ℂ] (Q' ⧸ R') :=
    (LinearEquiv.ofInjective φ hφi).trans ((LinearEquiv.ofEq _ _ hrφ).trans (LinearEquiv.ofInjective ψ hψi).symm)
  have he : ∀ x, ψ (e x) = φ x := by
    intro x
    have h1 := LinearEquiv.ofInjective_apply (f := ψ) (h := hψi)
      ((LinearEquiv.ofInjective ψ hψi).symm ((LinearEquiv.ofEq _ _ hrφ) (LinearEquiv.ofInjective φ hφi x)))
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨e, fun i => ?_⟩
  apply Submodule.linearMap_qext
  ext q
  apply hψi
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe]
  rw [he, radAct_mk]
  obtain ⟨q', hq'⟩ := Submodule.Quotient.mk_surjective R' (e (Submodule.Quotient.mk q))
  rw [← hq', radAct_mk]
  have h2 := he (Submodule.Quotient.mk q)
  rw [← hq'] at h2
  simp only [φ, ψ, Submodule.liftQ_apply] at h2 ⊢
  have hb := LinearMap.congr_fun (hβ₁ i) q'
  have hg := LinearMap.congr_fun (hγi i) q
  simp only [LinearMap.comp_apply] at hb hg
  rw [hb, h2]
  exact hg

end GlobalTheory.RealQuot
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower : ∀ (D : D7) (T T' : HSp D) (i : ℕ) (τ : D.what₂.Tau) (fr : Mn T.rank) (ε : Fin T.rank → Bool) (fr' : Mn T'.rank) (ε' : Fin T'.rank → Bool) (r s : ℕ) (e : Ix r s ≃ Fin T.rank), IsWittLower T T' i → frᴴ * Formalism.REAL.Jm ε * fr = gramAt D T τ → IsUnit fr → fr'ᴴ * Formalism.REAL.Jm ε' * fr' = gramAt D T' τ → IsUnit fr' → SignCompat ε e → i ≤ r ∧ i ≤ s ∧ ∃ e' : Ix (r - i) (s - i) ≃ Fin T'.rank, SignCompat ε' e' := by
  first | exact @GlobalTheory.WittSign.signCompat_of_isWittLower | exact GlobalTheory.WittSign.signCompat_of_isWittLower | (intros; apply GlobalTheory.WittSign.signCompat_of_isWittLower <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), (∀ τ, (v₀ τ : (MP R).H τ) ≠ 0) → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ S' : MMap (R.MY 0), S' = postOn (R.MY 0) R.e0 S - S → ((fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) =ᵐ[muX X] 0) → S' = 0 := by
  first | exact @GlobalTheory.TranslatedEvalInj.eq_zero | exact GlobalTheory.TranslatedEvalInj.eq_zero | (intros; apply GlobalTheory.TranslatedEvalInj.eq_zero <;> assumption)
end
