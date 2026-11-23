module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfRankEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
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
public import Mathlib.RingTheory.SimpleModule.Isotypic
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

@[expose] public section

section

noncomputable section

open GlobalTheory.CuspMult

namespace GlobalTheory.RepCount

variable {H W X : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

def modMap {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) : σ.asModule →ₗ[MonoidAlgebra ℂ H] ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
    (f.intertwiningMap_of_isIntertwiningMap σ ρ hf)

theorem modMap_apply {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) (x : σ.asModule) :
    ρ.asModuleEquiv (modMap f hf x) = f (σ.asModuleEquiv x) := rfl

def subEquiv {ρ : Representation ℂ H X} (U : Subrepresentation ρ) :
    U.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ H] U.asSubmodule :=
  LinearEquiv.ofBijective
    ((modMap (σ := U.toRepresentation) (ρ := ρ) U.toSubmodule.subtype (fun _ _ => rfl)).codRestrict
      U.asSubmodule (fun x => (U.toRepresentation.asModuleEquiv x).2))
    ⟨fun a b h => U.toRepresentation.asModuleEquiv.injective (Subtype.ext (congrArg Subtype.val h)),
     fun y => ⟨U.toRepresentation.asModuleEquiv.symm ⟨ρ.asModuleEquiv y.1, y.2⟩, rfl⟩⟩

variable [TopologicalSpace H]

theorem isAdmissible_of_injective {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (f : W →ₗ[ℂ] X) (hf : ∀ g s, f (σ g s) = ρ g (f s)) (hi : Function.Injective f)
    (h : GlobalTheory.PRep.IsAdmissible ρ) : GlobalTheory.PRep.IsAdmissible σ := by
  refine ⟨fun v => ?_, fun K hK hK' => ?_⟩
  · have : {g : H | σ g v = v} = {g : H | ρ g (f v) = f v} := by
      ext g
      simp only [Set.mem_setOf_eq, ← hf, hi.eq_iff]
    rw [this]
    exact h.1 _
  · haveI := h.2 K hK hK'
    refine FiniteDimensional.of_injective
      (f.restrict (p := GlobalTheory.PRep.fixed σ K) (q := GlobalTheory.PRep.fixed ρ K) (fun v hv k => ?_)) ?_
    · rw [← hf, hv k, map_smul]
    · intro a b hab
      exact Subtype.ext (hi (congrArg Subtype.val hab))

def pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) :=
  {m | ∃ U : Subrepresentation ρ, (U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation) ∧ U.asSubmodule = m}

theorem simple_of_mem_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule} (hm : m ∈ pieces ρ C) :
    IsSimpleModule (MonoidAlgebra ℂ H) m := by
  obtain ⟨U, ⟨-, hU, -⟩, rfl⟩ := hm
  exact IsSimpleModule.congr (subEquiv U).symm

theorem mem_sSup_pieces_of_mem {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : X}
    (hx : x ∈ irrSum ρ C) : ρ.asModuleEquiv.symm x ∈ sSup (pieces ρ C) := by
  have : irrSum ρ C ≤ ((sSup (pieces ρ C)).restrictScalars ℂ).comap
      ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun U hU y hy => ?_
    exact (le_sSup (s := pieces ρ C) ⟨U, hU, rfl⟩ : U.asSubmodule ≤ _) hy
  exact this hx

theorem mem_of_mem_sSup_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : ρ.asModule}
    (hx : x ∈ sSup (pieces ρ C)) : ρ.asModuleEquiv x ∈ C := by
  rw [sSup_eq_iSup'] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ρ.asModuleEquiv x ∈ C) hx ?_ ?_ ?_
  · rintro ⟨_, U, hU, rfl⟩ y hy
    exact hU.1 hy
  · simp
  · intro a b ha hb
    rw [map_add (f := _)]
    exact C.add_mem ha hb

theorem semisimple_sSup_pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)) := by
  rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => ?_
  haveI := simple_of_mem_pieces hm
  infer_instance

theorem apply_mem_irrSum {σ : Representation ℂ H W} {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) {f : W →ₗ[ℂ] X}
    (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf.2
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | h0
  · have hi' : Function.Injective f := hi
    let e : W ≃ₗ[ℂ] F.range.toSubmodule := LinearEquiv.ofInjective f hi'
    have he : ∀ g s, e (σ g s) = F.range.toRepresentation g (e s) :=
      fun g s => Subtype.ext (hf.2 g s)
    have he' : ∀ g s, e.symm (F.range.toRepresentation g s) = σ g (e.symm s) := by
      intro g s
      rw [LinearEquiv.symm_apply_eq, he, e.apply_symm_apply]
    have hirr : F.range.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact IsSimpleModule.congr
        (LinearEquiv.ofBijective (modMap e.symm.toLinearMap he') e.symm.bijective)
    have hle : F.range.toSubmodule ≤ irrSum ρ C :=
      le_iSup₂_of_le (f := fun (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧
        U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) =>
          U.toSubmodule) F.range ⟨by rintro _ ⟨t, rfl⟩; exact hf.1 t, hirr,
            isAdmissible_of_injective e.symm.toLinearMap he' e.symm.injective h2⟩ le_rfl
    exact hle ⟨s, rfl⟩
  · have : f s = 0 := DFunLike.congr_fun h0 s
    rw [this]
    exact Submodule.zero_mem _

theorem rank_homInto {σ : Representation ℂ H W} (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) :
    Module.rank ℂ (homInto σ ρ C) =
      Module.rank ℂ (σ.asModule →ₗ[MonoidAlgebra ℂ H] ↥(sSup (pieces ρ C))) := by
  refine LinearEquiv.rank_eq (LinearEquiv.ofBijective
    { toFun := fun f => (modMap f.1 f.2.2).codRestrict _
        (fun s => mem_sSup_pieces_of_mem (apply_mem_irrSum h1 h2 f.2 (σ.asModuleEquiv s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ⟨fun a b hab => ?_, fun g => ?_⟩)
  · ext s
    exact congrArg Subtype.val (LinearMap.congr_fun hab (σ.asModuleEquiv.symm s))
  · refine ⟨⟨ρ.asModuleEquiv.toLinearMap ∘ₗ
      (((sSup (pieces ρ C)).subtype ∘ₗ g).restrictScalars ℂ) ∘ₗ σ.asModuleEquiv.symm.toLinearMap,
      fun s => mem_of_mem_sSup_pieces (g _).2, fun x s => ?_⟩, rfl⟩
    change ρ.asModuleEquiv (g (σ.asModuleEquiv.symm (σ x s))).1 =
      ρ x (ρ.asModuleEquiv (g (σ.asModuleEquiv.symm s)).1)
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.coe_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

theorem exists_rep {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (U : Submodule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)))
    (hU : IsSimpleModule (MonoidAlgebra ℂ H) U) :
    ∃ V : Subrepresentation ρ, V.toRepresentation.IsIrreducible ∧
      GlobalTheory.PRep.IsAdmissible V.toRepresentation ∧
      Nonempty (U ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule) := by
  let e := Submodule.equivMapOfInjective _ (sSup (pieces ρ C)).injective_subtype U
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) (U.map (sSup (pieces ρ C)).subtype) :=
    IsSimpleModule.congr e.symm
  haveI : ∀ m : pieces ρ C, IsSimpleModule (MonoidAlgebra ℂ H) m :=
    fun m => simple_of_mem_pieces m.2
  obtain ⟨_, ⟨V, hV, rfl⟩, ⟨e'⟩⟩ := (U.map (sSup (pieces ρ C)).subtype).linearEquiv_of_le_sSup
    (pieces ρ C) (Submodule.map_subtype_le _ _)
  exact ⟨V, hV.2.1, hV.2.2, ⟨(e.trans e').trans (subEquiv V).symm⟩⟩

def killedEquiv {ρ : Representation ℂ H X} {C : Submodule ℂ X} (I : Set (MonoidAlgebra ℂ H))
    (hC : IsDecomp ρ C) (ho : ∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) :
    (C ⊓ killed ρ I : Submodule ℂ X) ≃ₗ[ℂ]
      GlobalTheory.SemisimpleCount.killed I ↥(sSup (pieces ρ C)) where
  toFun x := ⟨⟨ρ.asModuleEquiv.symm x.1, mem_sSup_pieces_of_mem (hC _ x.2.1 (ho _ x.2.2))⟩,
    fun r hr => Subtype.ext (mem_killed.1 x.2.2 r hr)⟩
  invFun y := ⟨ρ.asModuleEquiv y.1.1, mem_of_mem_sSup_pieces y.1.2,
    mem_killed.2 fun r hr => congrArg Subtype.val (y.2 r hr)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace H] in
theorem killed_ne_bot {σ : Representation ℂ H W} {I : Set (MonoidAlgebra ℂ H)} {S : Type}
    [AddCommGroup S] [Module (MonoidAlgebra ℂ H) S]
    (e : S ≃ₗ[MonoidAlgebra ℂ H] σ.asModule) {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    killed σ I ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨σ.asModuleEquiv (e s), mem_killed.2 fun r hr => ?_, by simpa using hs⟩
  rw [← Representation.asModuleEquiv_map_smul, ← map_smul, hI r hr, map_zero, map_zero]

theorem finrank_inf_killed_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  intro H _ _ X Y _ _ _ _ ρ ρ' C C' I hC hC' hm ho ho' f f'
  have e := killedEquiv I hC ho
  have e' := killedEquiv I hC' ho'
  rw [e.finrank_eq, e'.finrank_eq]
  refine GlobalTheory.SemisimpleCount.finrank_killed_eq (MonoidAlgebra ℂ H) _ _ I _ _
    (semisimple_sSup_pieces ρ C) (semisimple_sSup_pieces ρ' C') (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    e.finiteDimensional e'.finiteDimensional ?_ ?_
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))

end GlobalTheory.RepCount

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqCut

section Cosets

variable {Γ : Type} [Group Γ] {H J : Subgroup Γ}

theorem isDC_sub_iff (hJ : J ≤ H) (a : H) (R : Finset H) :
    Bridge.IsDC (J.subgroupOf H) a R ↔ Bridge.IsDC J (a : Γ) (R.map (Function.Embedding.subtype _)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨k₁, k₂, e⟩ := h1 b' hb'
      exact ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, congrArg Subtype.val e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, rfl⟩
      refine ⟨b.1, ⟨Finset.mem_map.2 ⟨b, hb, rfl⟩, hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
      exact congrArg Subtype.val (hu y' ⟨hy', hy2⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨k₁, k₂, e⟩ := h1 b.1 (Finset.mem_map.2 ⟨b, hb, rfl⟩)
      exact ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, Subtype.ext e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, rfl⟩
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      refine ⟨b', ⟨hb', hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      exact Subtype.ext (hu y.1 ⟨Finset.mem_map.2 ⟨y, hy, rfl⟩, hy2⟩)

theorem exists_lift_of_isDC (hJ : J ≤ H) (a : H) (R' : Finset Γ) (h : Bridge.IsDC J (a : Γ) R') :
    ∃ R : Finset H, R.map (Function.Embedding.subtype _) = R' := by
  classical
  refine ⟨R'.subtype (· ∈ H), Finset.subtype_map_of_mem fun b hb => ?_⟩
  obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
  exact H.mul_mem (H.mul_mem (hJ k₁.2) a.2) (hJ k₂.2)

end Cosets

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem levChi_flag {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  have hs' : (flagL L).s = 0 := hs
  have hQ' : (flagL L).Q = ∅ := hQ
  unfold levChi levFn
  rw [h2, hs', hQ']
  simp

theorem levChi_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flag1L L) κ = 1 := by
  rw [← levChi_flag (β := β) hs hQ κ]
  unfold levChi
  rw [levFn_flag1]

theorem hasType_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ)
    {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ h
  have e : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  have hm : κ ∈ levG V β (withP L P) := by
    refine ⟨hκ.1, hκ.2.1, ?_⟩
    show rTup β L (finE V κ) ∈ P.H
    rw [e]; exact P.H.one_mem
  rw [hF κ hm h]
  unfold levChi
  rw [levFn_withP, e, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem gaL_apply {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) (κ : G → GA D V) (hκ : ∀ g, IsLevelLift V β L (eG g) (κ g)) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * F (h * κ g) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := level_action_spec hF ⟨κ g, hκ g⟩ (κ g) (hκ g) h
  rw [levChi_flag hs hQ, inv_one, one_mul] at this
  rw [← this]
  rfl

theorem alg_sum (M : DSModel V S) {ι : Type} (s : Finset ι) (κ : ι → GfC V) (c : ι → ℂ) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (∑ i ∈ s, MonoidAlgebra.single (κ i) (c i) - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, ∑ i ∈ s, c i * T v (x * (κ i : GA D V)) = a * T v x := by

  rw [map_sub, map_sum, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, map_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [MultilinearMap.ext_iff]
  refine forall_congr' fun v => ?_
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem alg_one (M : DSModel V S) (k : GfC V) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, T v (x * (k : GA D V)) = a * T v x := by
  have := alg_sum M (Finset.univ : Finset Unit) (fun _ => k) (fun _ => 1) a T
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using this

theorem mem_hPart (M : DSModel V S) (J : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (T : MMap M) :
    T ∈ hPart M J ok pl q Sg ↔ ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α, IsHeckeAt V (pl P) k α → ∀ R, Bridge.IsDC J α⁻¹ R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T v x := by
  unfold hPart
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_hecke_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  intro D V S θ M β L G _ _ eG c P Pl0 ok pl q Sg hs hQ hlift
  have hJ : levG V β (flag1L L) ≤ GfC V := fun _ h => h.1
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_goodPart, mem_killed, mem_hPart, GlobalTheory.MultMem.mem_mult_iff,
    GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · rintro ⟨⟨hm, hg⟩, hh⟩
    refine ⟨⟨hm.aut, hm.cusp, fun _ _ h => h.elim, hm.equiv, hm.cont⟩, ?_⟩
    rintro x ((⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩)
    · exact (alg_one M k _ T).2 fun v x => hm.lev v k hk x
    · refine (alg_sum M _ κ c 1 T).2 fun v x => ?_
      have hF : HasType V β (flag1L L) (T v) := hasType_flag1 P fun k hk h => hm.lev v k hk h
      rw [← gaL_apply hs hQ eG c hF (fun g => κ g) hκ x, hg v, one_mul]
    · refine (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
      have := hh P0 hP0 k hk α hα _ ((isDC_sub_iff hJ α⁻¹ R).1 hR) v x
      rw [Finset.sum_map] at this
      simp only [one_mul]
      exact this
  · rintro ⟨hm, hk⟩
    have hlev : ∀ v, HasType V β (withP L P) (T v) := fun v k hkk x =>
      (alg_one M ⟨k, hkk.1⟩ _ T).1 (hk _ (Or.inl (Or.inl ⟨⟨k, hkk.1⟩, hkk, rfl⟩))) v x
    refine ⟨⟨⟨hm.aut, hm.cusp, fun v k hkk x => hlev v k hkk x, hm.equiv, hm.cont⟩, fun v => ?_⟩, ?_⟩
    · choose κ hκ using fun g => hlift (eG g)
      funext x
      rw [gaL_apply hs hQ eG c (hasType_flag1 P (hlev v)) κ hκ x]
      have := (alg_sum M Finset.univ (fun g => (⟨κ g, (hκ g).1⟩ : GfC V)) c 1 T).1
        (hk _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))) v x
      rw [one_mul] at this
      exact this
    · intro P0 hP0 k hkr α hα R' hR' v x
      have hαf : α ∈ GfC V := by
        obtain ⟨e, ϖ, -, -, -, h⟩ := hα
        exact h.1
      obtain ⟨R, rfl⟩ := exists_lift_of_isDC hJ (⟨α, hαf⟩ : GfC V)⁻¹ R' hR'
      have hR := (isDC_sub_iff hJ (⟨α, hαf⟩ : GfC V)⁻¹ R).2 hR'
      have := (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).1
        (hk _ (Or.inr ⟨P0, hP0, k, hkr, ⟨α, hαf⟩, R, hα, hR, rfl⟩)) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.EqCut

end
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem enlarge_good : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  have hF : GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA :=
    ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩
  obtain ⟨A₁, _, _, _, _, _, _, i₁, EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, act₁, hF₁,
    ⟨ρ₁, hR₁, -⟩, β₁, h₁, hβ₁, hh₁⟩ := GlobalTheory.T.enlarge_strictHenselisation_retract_mod T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF
  obtain ⟨A₂, _, _, _, _, _, _, i₂, EA₂, _, _, _, _, _, QA₂, _, jA₂, ψA₂, DA₂, _, _, act₂, hF₂,
    ⟨ρ₂, hR₂, hpt₂⟩, β₂, h₂, hβ₂, hh₂⟩ :=
    GlobalTheory.T.enlarge_base_separable_point_integralClosure T O hT P φ hφ hsh hP q hq0 hqT A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ act₁ hF₁ ρ₁ hR₁
  obtain ⟨A₃, _, _, _, _, _, _, i₃, EA₃, _, _, _, _, _, QA₃, _, jA₃, ψA₃, DA₃, _, _, act₃, hF₃,
    ⟨ρ₃, hR₃, hgood⟩, β₃, h₃, hβ₃, hh₃⟩ :=
    GlobalTheory.T.etale_enlarge_by_uniformiser_roots T O hT P φ hφ hsh hP q hq0 hqT A₂ i₂ EA₂ QA₂ jA₂ ψA₂ DA₂ act₂ hF₂ ρ₂ hR₂ hpt₂
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    EA₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₃, inferInstance,
    hF₃.2.2.2.1, hF₃.2.2.1, ρ₃, hR₃.1, hR₃.2.1, jA₃, ψA₃, hF₃.2.2.2.2.2.1, DA₃, inferInstance,
    inferInstance, act₃, hF₃.2.2.2.2.2.2, hgood, β₃.comp (β₂.comp β₁), h₃.comp (h₂.comp h₁), ?_, ?_⟩
  · ext x
    have a1 := RingHom.congr_fun hβ₁ x
    have a2 := RingHom.congr_fun hβ₂ (β₁ x)
    have a3 := RingHom.congr_fun hβ₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a3, a2, a1]
  · ext x
    have a1 := RingHom.congr_fun hh₁ x
    have a2 := RingHom.congr_fun hh₂ (β₁ x)
    have a3 := RingHom.congr_fun hh₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a1, a2, a3]

end GlobalTheory.KeyOriginEnlarge
end
