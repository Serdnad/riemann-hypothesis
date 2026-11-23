module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle187
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle112
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import GroundTheory.PAdicHodge.UnramifiedClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle323
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle314
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdCompat

theorem sum_castLE_eq_sum_filter {s : ℕ} (f : Fin s → ℕ) (c : Fin s) :
    ∑ b : Fin (c : ℕ), f (Fin.castLE c.2.le b) = ∑ j ∈ Finset.univ.filter (· < c), f j := by
  refine Finset.sum_bij (fun b _ => Fin.castLE c.2.le b) ?_ ?_ ?_ ?_
  · intro b _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b.2⟩
  · intro x _ y _ h
    exact Fin.castLE_injective _ h
  · intro j hj
    have hj' : (j : ℕ) < c := (Finset.mem_filter.1 hj).2
    exact ⟨⟨j, hj'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro _ _
    rfl

theorem partial_sum_drop_empty {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r)
    (ho : StrictMono o) (hr : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    ∑ b ∈ Finset.univ.filter (· < a), d (o b) = ∑ j ∈ Finset.univ.filter (· < o a), d j := by
  rw [← Finset.sum_image (s := Finset.univ.filter (· < a)) (g := o) (f := d)
    (fun x _ y _ h => ho.injective h)]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hj
    have hb' : b < a := (Finset.mem_filter.1 hb).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ho hb'⟩
  · intro j hj hj'
    by_contra hne
    obtain ⟨b, rfl⟩ := hr j hne
    have hlt : o b < o a := (Finset.mem_filter.1 hj).2
    exact hj' (Finset.mem_image.2
      ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, ho.lt_iff_lt.1 hlt⟩, rfl⟩)

theorem stdBlocks_drop_empty : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N)
    (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) →
    ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))),
      stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  intro r r' N d hd o ho hr hd' a t
  apply Fin.ext
  have h1 := stdBlocks_val (fun a => d (o a)) hd' a t
  have h2 := stdBlocks_val d hd (o a) t
  have h3 := sum_castLE_eq_sum_filter (fun a => d (o a)) a
  have h4 := sum_castLE_eq_sum_filter d (o a)
  have h5 := partial_sum_drop_empty d o ho hr a
  rw [h1, h2]
  rw [h3, h4, h5]

end GlobalTheory.CompanionTheory.StdCompat
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CosocleContra

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isIrreducible_quot_of_isCoatom {L : Subrepresentation π} (hL : IsCoatom L) :
    (ProjLine.quot L).IsIrreducible := by
  have h1 : L.toSubmodule ≠ ⊤ := fun e => hL.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (ProjLine.quot L)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π :=
    ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hLT : L ≤ T' := fun v hv => by
    have h0 : L.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
    show L.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [h0]
    exact zero_mem _
  rcases eq_or_lt_of_le hLT with e | e
  · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := hy
    rw [← e] at hv
    exact (Submodule.Quotient.mk_eq_zero _).2 hv
  · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := (hL.2 _ e) ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    exact hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullContra (S : Subrepresentation π) : (contra (ProjLine.quot S)).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show (ProjLine.quot S).dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v =>
          LinearMap.congr_fun (show (ProjLine.quot S).dual g l.1 = l.1 from hg) (S.toSubmodule.mkQ v))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem pullContra_injective (S : Subrepresentation π) : Function.Injective (pullContra S) := fun a b h =>
  Subtype.ext (LinearMap.ext fun y => by
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem pullContra_apply_eq_zero (S : Subrepresentation π) (l : smoothPart (ProjLine.quot S).dual) {v : V}
    (hv : v ∈ S) : (pullContra S l).1 v = 0 := by
  have h0 : S.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
  show l.1 (S.toSubmodule.mkQ v) = 0
  rw [h0, map_zero]

theorem eq_of_isCoatom_of_mem_range {S S' : Subrepresentation π} (hS : IsCoatom S) (hS' : IsCoatom S')
    {w : smoothPart π.dual} (hw : w ≠ 0) (h : w ∈ (pullContra S).range) (h' : w ∈ (pullContra S').range) :
    S = S' := by
  by_contra hne
  have top := hS.sup_eq_top_of_ne hS' hne
  obtain ⟨l, rfl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  refine hw (Subtype.ext (LinearMap.ext fun v => ?_))
  have hv : v ∈ (S ⊔ S').toSubmodule := by
    rw [top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have h1 := pullContra_apply_eq_zero S l ha
  have h2 := pullContra_apply_eq_zero S' l' hb
  have h3 : (pullContra S l).1 b = 0 := (congrArg (fun y : smoothPart π.dual => y.1 b) hl').symm.trans h2
  show (pullContra S l).1 (a + b) = 0
  rw [map_add (f := _), h1, h3, add_zero]

end General

theorem isCosocle_of_isSocle_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  intro k _ _ _ _ hA N V _ _ π hπ hfl τ' hτ
  obtain ⟨hi, f, hf, hat⟩ := hτ
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis (k := k) N
  have hat0 : IsAtom f.range := isAtom_range hi f hf
  have hsm : ∀ S : Subrepresentation π, IsSmooth (ProjLine.quot S) := fun S =>
    (IsSubquotient.of_surjective (ProjLine.quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, IsCoatom S → (pullContra S).range = f.range := fun S hS => by
    have hirr := isIrreducible_quot_of_isCoatom hS
    exact hat _ (isAtom_range (GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (hsm S) hirr) hirr) _
      (pullContra_injective S))
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    refine hat0.1 (eq_bot_iff.2 ?_)
    rintro _ ⟨x, rfl⟩
    exact (h x).symm ▸ zero_mem (⊥ : Subrepresentation (contra π)).toSubmodule
  haveI : WellFoundedGT (Subrepresentation π) := ((hasFiniteLength_iff_wellFounded π).1 hfl).1
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := fun e => hx (Subtype.ext (LinearMap.ext fun v => by
    have hv : v ∈ (⊥ : Subrepresentation π) := e ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
    rw [hv0, map_zero]
    rfl))
  obtain ⟨L, hL, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation π)).resolve_left hbt
  have huniq : ∀ S : Subrepresentation π, IsCoatom S → S = L := fun S hS =>
    eq_of_isCoatom_of_mem_range hS hL hx ((key S hS).symm ▸ ⟨x, rfl⟩) ((key L hL).symm ▸ ⟨x, rfl⟩)
  have hall : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤ := fun S => by
    rcases eq_top_or_exists_le_coatom S with h | ⟨M, hM, hSM⟩
    · exact Or.inr h
    · exact Or.inl (huniq M hM ▸ hSM)
  have hc := ProjLine.isCosocle_quot hL.1 hall
  exact ⟨⟨_, ProjLine.quot L, hsm L, hc.1⟩, hc⟩

end GlobalTheory.CompanionTheory.CosocleContra

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FineProd.TensorLine

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [Subsingleton.elim g 1, map_one]; exact hw⟩
  have hvS : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
  have hS : S = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with h | h
    · exfalso
      rw [h] at hvS
      exact hv ((Submodule.mem_bot ℂ).1 hvS)
    · exact h
  have htop : ∀ w : V, w ∈ Submodule.span ℂ {v} := fun w => by
    have : w ∈ S.toSubmodule := by
      rw [hS]
      exact (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ V))
    exact this
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ V v) ⟨?_, ?_⟩).symm⟩
  · exact LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop w)
    exact ⟨c, by simpa using hc⟩

theorem subsingleton_GL {k : Type} [Field k] {n : ℕ} (h : n = 0) : Subsingleton (GL (Fin n) k) := by
  subst h
  exact ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

variable {r r' : ℕ}

abbrev Off (o : Fin r' → Fin r) : Type := {j : Fin r // j ∉ Set.range o}

def blockEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) : Fin r' ⊕ Off o ≃ Fin r :=
  Equiv.ofBijective (Sum.elim o Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (ho h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro j
      by_cases hj : j ∈ Set.range o
      · obtain ⟨a, rfl⟩ := hj
        exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩)

variable {X : Fin r → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]


open scoped Classical in
def dropEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) :
    (⨂[ℂ] j, X j) ≃ₗ[ℂ] ⨂[ℂ] a, X (o a) :=
  (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm).trans <|
    ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv)).trans
        (TensorProduct.rid ℂ _)


open scoped Classical in
theorem dropEquiv_tprod (o : Fin r' → Fin r) (ho : Function.Injective o)
    (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) (x : ∀ j, X j) :
    dropEquiv o ho φ (PiTensorProduct.tprod ℂ x) =
      (∏ c : Off o, φ c (x c)) • PiTensorProduct.tprod ℂ fun a => x (o a) := by
  have h1 : PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun i => x (blockEquiv o ho i) :=
    PiTensorProduct.reindex_tprod _ _
  have h2 := PiTensorProduct.tmulEquivDep_symm_apply ℂ (fun i => X (blockEquiv o ho i))
    (fun i => x (blockEquiv o ho i))
  have h3 : (PiTensorProduct.congr fun c : Off o => φ c)
      (PiTensorProduct.tprod ℂ fun c : Off o => x c) = PiTensorProduct.tprod ℂ fun c : Off o => φ c (x c) :=
    PiTensorProduct.congr_tprod _ _
  have ht : ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
      (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c)) =
      (PiTensorProduct.tprod ℂ fun a => x (o a)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun c : Off o => x c) :=
    (congrArg _ h1).trans h2
  show (TensorProduct.rid ℂ _) ((TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv))
      ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
        (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c))) = _
  rw [ht, TensorProduct.congr_tmul, LinearEquiv.trans_apply, h3, TensorProduct.rid_tmul]
  congr 1
  exact PiTensorProduct.constantBaseRingEquiv_tprod _

theorem piTensor_drop_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  intro k _ _ _ _ r r' y o ho hy
  have hz : ∀ c : Off o, (y c).1 = 0 := fun c => by
    by_contra h
    exact c.2 (hy c h)
  have hφ : ∀ c : Off o, Nonempty ((y c).2.rep.V ≃ₗ[ℂ] ℂ) := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    exact exists_line (y c).2.rep.irr
  let φ : ∀ c : Off o, (y c).2.rep.V ≃ₗ[ℂ] ℂ := fun c => (hφ c).some
  refine ⟨Representation.Equiv.mk (dropEquiv o ho.injective φ) fun g => ?_⟩
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  have hc : ∀ c : Off o, (y c).rep (g c) (x c) = x c := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    rw [Subsingleton.elim (g c) 1, map_one]
    rfl
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, dropEquiv_tprod, hc, map_smul]
  congr 1
  exact (piTensor_tprod (fun a => (y (o a)).rep) (fun a => g (o a)) (fun a => x (o a))).symm

end GlobalTheory.CompanionTheory.FineProd.TensorLine

end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem summable_absNorm_rpow_neg (K : Type) [Field K] [NumberField K] {r : ℝ} (hr : 1 < r) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-r)) := by
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (r : ℂ)) (by simpa using hr))
  refine h.congr fun I => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

theorem sum_torsion_le (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) {r : ℝ} (hr : 1 < r)
    (S : Finset ((Fin m → K) ⧸ L)) :
    ∑ x ∈ S, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
      ≤ zetaR K r := by
  classical
  set τ : (Fin m → K) ⧸ L → Ideal (𝓞 K) := fun x => Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x
    with hτ
  have hg := summable_absNorm_rpow_neg K hr
  have hfib : ∀ 𝔞 ∈ S.image τ,
      ∑ x ∈ S.filter (fun x => τ x = 𝔞), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := by
    intro 𝔞 h𝔞
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp h𝔞
    have hne : τ x₀ ≠ ⊥ := GlobalTheory.T.lattice_quotient_torsion_nonzero K m L hL x₀
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow K m L hL (τ x₀) hne
    have hN : (0 : ℝ) < (Ideal.absNorm (τ x₀) : ℝ) := by
      have : Ideal.absNorm (τ x₀) ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hc : ((S.filter (fun x => τ x = τ x₀)).card : ℝ) ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m := by
      have hinj : (S.filter (fun x => τ x = τ x₀)).card ≤
          Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} := by
        haveI := Fintype.ofFinite {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0}
        rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun x => ⟨x.1, fun a ha => ?_⟩) (fun x y h => ?_)
        · have hx := (Finset.mem_filter.mp x.2).2
          rw [← hx] at ha
          exact (Ideal.mem_torsionOf_iff _ _).mp ha
        · have h' : (x : (Fin m → K) ⧸ L) = y :=
            congrArg (fun z : {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} => z.1) h
          exact Subtype.ext h'
      exact_mod_cast hinj.trans hcard
    have hsum : ∑ x ∈ S.filter (fun x => τ x = τ x₀), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        = ((S.filter (fun x => τ x = τ x₀)).card : ℝ) *
          (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) := by
      rw [Finset.sum_congr rfl (g := fun _ => (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)))
        (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      simp
    rw [hsum]
    calc _ ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m * (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN.le _)
      _ = (Ideal.absNorm (τ x₀) : ℝ) ^ (-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hN]
          congr 1
          ring
  calc ∑ x ∈ S, (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
      = ∑ 𝔞 ∈ S.image τ, ∑ x ∈ S.filter (fun x => τ x = 𝔞),
          (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r)) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem τ hx) _).symm
    _ ≤ ∑ 𝔞 ∈ S.image τ, (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := Finset.sum_le_sum hfib
    _ ≤ zetaR K r :=
        hg.sum_le_tsum _ (fun I _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_torsion (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) (r : ℝ) (hr : 1 < r) :
    Summable (fun x : (Fin m → K) ⧸ L =>
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧
    ∑' x : (Fin m → K) ⧸ L,
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ zetaR K r := by
  have hnn : ∀ x : (Fin m → K) ⧸ L,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_of_sum_le hnn (sum_torsion_le K m L hL hr)
  exact ⟨hs, hs.tsum_le_of_sum_le (sum_torsion_le K m L hL hr)⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi

theorem _root_.GlobalTheory.T.exists_induced_ball_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E), ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | exact GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | (intros; apply GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.lubin_tate_norm_cyclotomic : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  first | exact @GlobalTheory.CompanionTheory.LTNorm.norm_eq_cyclo | exact GlobalTheory.CompanionTheory.LTNorm.norm_eq_cyclo | (intros; apply GlobalTheory.CompanionTheory.LTNorm.norm_eq_cyclo <;> assumption)
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_cell_unipotent_uniqueness_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.unipU_open_cell | exact GlobalTheory.CompanionTheory.Rodier.unipU_open_cell | (intros; apply GlobalTheory.CompanionTheory.Rodier.unipU_open_cell <;> assumption)
end
