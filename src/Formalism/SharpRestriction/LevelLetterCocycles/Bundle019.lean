module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

section Gen

variable (S : Sit)

def oneT (T : LocLat S.G S.Qp S.LL S.O) : ↥T.L.T →ₗ[S.O] TW S.RW T :=
  TensorProduct.mk S.O S.RW ↥T.L.T 1

def OneInj : Prop := ∀ T : LocLat S.G S.Qp S.LL S.O, Function.Injective (oneT S T)

def GenFix : Prop :=
  ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T),
    (∀ g, S.W.resΓ g = S.W.gamK → T.actT g t = t) →
    (∀ g, S.W.resΓ g ∈ S.W.DelF → T.actT g t = t) →
    (∀ g, S.W.resΓ g = 1 → T.actT g t = t) → ∀ g, T.actT g t = t

variable {S}

theorem oneT_apply (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T) : oneT S T t = (1 : S.RW) ⊗ₜ[S.O] t := rfl

theorem TWact_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (g : S.G) (t : ↥T.L.T) : TWact f T g ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] T.actT g t := by
  simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem TWmap_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (t : ↥T.L.T) : TWmap f T ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] t := by
  simp only [TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]

theorem mem_H0Lat {T : LocLat S.G S.Qp S.LL S.O} (t : ↥T.L.T) : t ∈ invariantLattice T ↔ ∀ g, T.actT g t = t := by
  simp only [invariantLattice, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  first
  | rfl
  | exact Iff.rfl
  | (constructor <;> intro h g <;> exact h g)

theorem mem_fixDD {T : LocLat S.G S.Qp S.LL S.O} (x : S.W.DD T) : x ∈ fixDD S.W T ↔
    S.W.φD T x = x ∧ S.W.γD T S.W.gamK x = x ∧ ∀ δ ∈ S.W.DelF, S.W.γD T δ x = x := by
  simp only [fixDD, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, and_assoc]

private theorem nonempty_invariantLattice_equiv_fixDD (E : S.Comparison₂)
    (hin : ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T), (∀ g, T.actT g t = t) →
      (1 : S.RW) ⊗ₜ[S.O] t ∈ Set.range (E.jD T))
    (hfix : ∀ (T : LocLat S.G S.Qp S.LL S.O) (b : TW S.RW T), TWmap S.φR T b = b →
      ∃ t : ↥T.L.T, b = (1 : S.RW) ⊗ₜ[S.O] t)
    (hi : OneInj S) (hg : GenFix S) (T : LocLat S.G S.Qp S.LL S.O) :
    Nonempty (↥(invariantLattice T) ≃ₗ[S.O] ↥(fixDD S.W T)) := by

  have key : (invariantLattice T).map (oneT S T) = (fixDD S.W T).map (E.jD T) := by
    ext b
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_H0Lat] at ht
      obtain ⟨d, hd⟩ := hin T t ht
      refine ⟨d, ?_, ?_⟩
      · rw [mem_fixDD]
        refine ⟨?_, ?_, ?_⟩
        · apply E.jD_inj T
          rw [E.jD_φ, hd, TWmap_one]
        · obtain ⟨g, hgg⟩ := S.W.resΓ_onto S.W.gamK
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
        · intro δ _
          obtain ⟨g, hgg⟩ := S.W.resΓ_onto δ
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
      · rw [oneT_apply, hd]
    · rintro ⟨d, hd, rfl⟩
      rw [mem_fixDD] at hd
      obtain ⟨hφ, hγ, hδ⟩ := hd
      obtain ⟨t, ht⟩ := hfix T (E.jD T d) (by rw [← E.jD_φ, hφ])
      have hact : ∀ g : S.G, S.W.γD T (S.W.resΓ g) d = d → T.actT g t = t := by
        intro g hgd
        apply hi T
        rw [oneT_apply, oneT_apply, ← TWact_one (S.gR g), ← ht, ← E.jD_act, hgd]
      refine ⟨t, ?_, ?_⟩
      · rw [mem_H0Lat]
        apply hg T t
        · intro g hgK
          exact hact g (by rw [hgK, hγ])
        · intro g hgD
          exact hact g (hδ _ hgD)
        · intro g h1
          exact hact g (by rw [h1, S.W.γD_one])
      · rw [oneT_apply, ht]
  exact ⟨(Submodule.equivMapOfInjective (oneT S T) (hi T) (invariantLattice T)).trans
    ((LinearEquiv.ofEq _ _ key).trans
      (Submodule.equivMapOfInjective (E.jD T) (E.jD_inj T) (fixDD S.W T)).symm)⟩

end Gen

theorem invariants_iso_of_generators (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hi : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      OneInj (sit D.loc HW l (D.locA l) K 1 LL hA.2.2))
    (hg : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GenFix (sit D.loc HW l (D.locA l) K 1 LL hA.2.2)) :
    H0InvariantsTheorem D HW F := by
  intro hF l hl K LL hA T
  obtain ⟨hW, hD⟩ := hF l K 1 LL hA.2.2
  refine nonempty_invariantLattice_equiv_fixDD (S := sit D.loc HW l (D.locA l) K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie
    (fun T t ht => ?_) (fun T b hb => (hW T).2.1 b hb) (hi l K LL hA) (hg l K LL hA) T

  refine Set.mem_range.mpr (LinearMap.mem_range.mp ((hD T).2 _ ?_ ?_))
  · intro g _
    rw [TWact_one, ht g]
  · rw [TWmap_one, sub_self]
    exact Submodule.zero_mem _

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section C6

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end C6

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}



end All

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}


variable (Y) in
def goodTwistExistsAllCoprimePowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    ∀ a : ℤ, a.natAbs.Coprime (X.l i) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

end All

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

end Tame

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.N.TwAll

section DensityAveraging

variable {D : D7}

end DensityAveraging

end Formalism.MainNotions.N.KillingConditions

end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def B1 (l h η S : ℕ) : ℝ :=
  (2 * (aN l (h + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + lam l (h + η)

def B2 (l h η : ℕ) : ℝ := 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + 2

theorem bound_sum_eq (l h η S : ℕ) : B1 l h η S + B2 l h η = cocyclesToWachVectorsExponent l h η S := by
  unfold B1 B2 cocyclesToWachVectorsExponent; ring

def uOf (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N s₁ : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (μ ms : ZMod n → FF →ₗ[O] W.DD T) (c : ZMod n) (f : FF) : W.DD T :=
  ((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f

def Step1Out [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d a N s₁ : ℕ) {FF : Type}
    [AddCommGroup FF] [Module O FF] (z : FF →ₗ[O] W.DD T) (μ : ZMod n → FF →ₗ[O] W.DD T)
    (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  ∀ c ∈ evens n d, ∀ f : FF,
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (ms c f) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • z f) + (W.γ T (ms c f) - ms c f)) ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ a • uOf W T N s₁ μ ms c f ∈ W.N T ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (uOf W T N s₁ μ ms c f) - uOf W T N s₁ μ ms c f) ∧
    (f ∈ F₁ → uOf W T N s₁ μ ms c f ∈ W.N T)

def Step1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ s₁ : ℕ, (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S ∧
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∃ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) ⊤ F₁
          (evens n d).card 0 ∧
        (m = 0 → F₁ = ⊤) ∧
        Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms

def Step2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ sg : ℕ, (sg : ℝ) ≤ B2 PD.p (hpar n b S) η ∧
    ∀ (s₁ : ℕ) (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∀ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
      Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms →
      ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) F₁ F₂
          (evens n d).card 0 ∧
        (m = 0 → F₂ = F₁) ∧
        (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
        ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
          (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
            (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
          (((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) - (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
            ((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) + (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L)

theorem cocyclesToWachVectorsBound_of_extTool [NeZero n] (W : LocWach PD LL O v n) (hE : Sh.ExtTool W) (h1 : Step1 W)
    (h2 : Step2 W) : CocyclesToWachVectorsBound W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨s₁, hs₁, H1⟩ := h1 d T₁ T₂ F b S η m hS
  obtain ⟨sg, hsg, H2⟩ := h2 d T₁ T₂ F b S η m hS
  refine ⟨s₁ + sg, ?_, ?_⟩
  · have := bound_sum_eq PD.p (hpar n b S) η S
    push_cast
    linarith
  · intro FF _ _ _ _ g
    obtain ⟨N, y, z, μ, ν, hX⟩ := hE d T₁ T₂ F b S η m hS FF g
    obtain ⟨F₁, ms, hc1, hm1, ho⟩ := H1 FF g N y z μ ν hX
    obtain ⟨F₂, w, hc2, hm2, h36, hid⟩ := H2 s₁ FF g N y z μ ν hX F₁ ms ho
    refine ⟨F₂, w, ?_, ?_, h36, hid⟩
    · have hn : Even n := hS.2.2.1
      have := two_mul_card_evens_le hn d
      exact (hc1.trans hc2).mono (by omega) le_rfl
    · intro h0
      rw [hm2 h0, hm1 h0]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

private lemma exists_pow_eq_one_mul {Γ : Type} [CommGroup Γ] {a b : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1)
    (hb : ∃ k : ℕ, 0 < k ∧ b ^ k = 1) : ∃ k : ℕ, 0 < k ∧ (a * b) ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  obtain ⟨m, hm, hbm⟩ := hb
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbm, one_pow]

private lemma exists_pow_eq_one_inv {Γ : Type} [CommGroup Γ] {a : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ a⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  have hδt := (W.DelF_def δ).1 hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁

  simp only [Formalism.BasicNotions.LocWach.π₀₁, map_add (f := _), map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) ?_ ?_
  · intro g
    simp only [Equiv.coe_mulLeft]
    rw [W.DelF_def g, W.DelF_def (δ * g)]
    constructor
    · exact fun hg => exists_pow_eq_one_mul hδt hg
    · intro hg
      have h2 := exists_pow_eq_one_mul (exists_pow_eq_one_inv hδt) hg
      rwa [inv_mul_cancel_left] at h2
  · intro g _
    simp only [Equiv.coe_mulLeft, map_mul, AlgHom.mul_apply]

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
end
end
