module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OrbitFinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DetGaNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 → (Ga T T' Z).det ≠ 0

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnipotentIntegralIsGroup : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    LinearEquiv.refl D.host.E (VS D).V ∈ N0 F0 Λ ∧
    (∀ n ∈ N0 F0 Λ, n.symm ∈ N0 F0 Λ) ∧
    (∀ n ∈ N0 F0 Λ, ∀ m ∈ N0 F0 Λ, n.trans m ∈ N0 F0 Λ)

def OrbitReps : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂,
        ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
          ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def fr (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Fin (D.R.rS + 1) → (VS D).V :=
  Fin.snoc (α := fun _ => (VS D).V) x.1 x.2

def act (D : Formalism.BasicNotions.D7) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    (Fin D.R.rS → (VS D).V) × (VS D).V :=
  (fun a => n (x.1 a), n x.2)

def Good (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Prop :=
  (∀ b, fr D x b ∈ Λ) ∧ (∀ a b, brS (VS D) (fr D x b) (F0.fvec a) = Z a b) ∧
  (∀ a b, (VS D).hT (fr D x a) (fr D x b) =
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0)

def pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (D.sp.hypF a) v • D.sp.hypE a - ∑ a, (VS D).hT (D.sp.hypE a) v • D.sp.hypF a
    + ((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm

def pWf (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Fin (D.R.rS + 1) → (VS D).V :=
  fun b => pW D (fr D x b)

def alM (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E :=
  fun a b => (VS D).hT (D.sp.hypF a) (fr D x b)

def betaZ (D : Formalism.BasicNotions.D7) (Z : MatZ D) : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E :=
  Z.submatrix Fin.castSucc id

def RankG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 →
    ∃ R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E, betaZ D Z * R = 1

def FixedOK (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Prop :=
  Submodule.IsLattice D.host.E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ ∧ F0.e = D.sp.hypE ∧ (∀ a, F0.e a ∈ Λ) ∧
    ∃ c : D.host.E, c ≠ 0 ∧ F0.z = c • D.sp.zm

def GoodEZ : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D), ∀ F' ∈ EZ T' F0 Λ Z, Good D T' F0 Λ Z (F'.fl.e, F'.fl.z)

def Stage1 : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∃ Wf : Set (Fin (D.R.rS + 1) → (VS D).V), Wf.Finite ∧
      ∀ x, Good D T' F0 Λ Z x → ∃ n ∈ N0 F0 Λ, pWf D (act D n x) ∈ Wf

def Stage2 : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∀ Wf : Set (Fin (D.R.rS + 1) → (VS D).V), Wf.Finite →
    ∃ Af : Set (Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), Af.Finite ∧
      ∀ x, Good D T' F0 Λ Z x → pWf D x ∈ Wf →
        ∃ n ∈ N0 F0 Λ, pWf D (act D n x) = pWf D x ∧ alM D (act D n x) * R ∈ Af

def FinK : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∀ (Wf : Set (Fin (D.R.rS + 1) → (VS D).V)) (Af : Set (Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)),
      Wf.Finite → Af.Finite →
      {x | Good D T' F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af}.Finite

theorem fr_act (D : Formalism.BasicNotions.D7) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (Fin D.R.rS → (VS D).V) × (VS D).V)
    (b : Fin (D.R.rS + 1)) : fr D (act D n x) b = n (fr D x b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b <;> simp [fr, act]

theorem unipotentIntegral_fixes_flag (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    (a : Fin (D.R.rS + 1)) : n (F0.fvec a) = F0.fvec a := by
  obtain ⟨-, he, hz⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp [FlagG.fvec, he, hz]

theorem unipotentIntegral_isometry (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    (x y : (VS D).V) : (VS D).hT (n x) (n y) = (VS D).hT x y := by
  obtain ⟨hL, -, -⟩ := hn
  unfold NLam at hL
  obtain ⟨hA, -, -⟩ := hL
  unfold IsAutLam at hA
  exact hA.1 x y

theorem unipotentIntegral_preserves_lattice (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    {v : (VS D).V} (hv : v ∈ Λ) : n v ∈ Λ := by
  obtain ⟨hL, -, -⟩ := hn
  obtain ⟨⟨-, hg⟩, -, -⟩ := hL
  unfold Formalism.HermitianLatticesTheory.gmap at hg
  rw [← hg]
  exact Submodule.mem_map_of_mem hv

theorem good_move (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ) :
    Good D T' F0 Λ Z (act D n x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [fr_act]
    exact unipotentIntegral_preserves_lattice D F0 Λ hn (h1 b)
  · rw [fr_act, ← unipotentIntegral_fixes_flag D F0 Λ hn a]
    unfold brS
    rw [unipotentIntegral_isometry D F0 Λ hn]
    have h2' := h2 a b
    unfold brS at h2'
    exact h2'
  · rw [fr_act, fr_act, unipotentIntegral_isometry D F0 Λ hn]
    exact h3 a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GoodAt {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) : Prop :=
  (M p).split = none ∧ (L.H p).IsSelfDual (lattice₂ L p (VS D).L0) ∧
    (∀ a b, GaPlus M δ p T T' Z a b ∈ (M p).L.O) ∧
    ∃ y ∈ (M p).L.O, (GaPlus M δ p T T' Z).det * y = 1

def DensAtGood : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ (Z : MatZ D) (p : PlF D), GoodAt L δ (Tn u) (Tn u') Z p →
          ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
            densP L δ ϖ (Tn u) (Tn u') Z p =
              Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp]) η D.R.r (2 * (D.R.rS + 1)) 0

def ResCard : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D), Nat.card 𝓀[(D.s.atP p).Fp] = p.asIdeal.absNorm

def ModeLCofinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, (M p).split = none

theorem resChar_finite (D : Formalism.BasicNotions.D7) (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
  have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
      {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have hempty : {p : PlF D | Loc.resChar p = 0} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    rw [hempty]
    exact Set.finite_empty
  · refine (Ideal.finite_factors ?_).subset hsub
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ

theorem local_models_split_cofinite : ModeLCofinite := by
  intro D δ M hA
  have hfin : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)}.Finite := by
    have he : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)} =
        {p | Loc.resChar p = D.host.g 0} ∪ {p | Loc.resChar p = D.host.g 1} := by
      ext p
      simp
    rw [he]
    exact (resChar_finite D _).union (resChar_finite D _)
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [← D.s_split p]
  have hAp := (hA p).2.2.2.2.2
  cases hM : (M p).split with
  | none => exact absurd hM hp
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hAp
      exact hAp.elim
    | some sg => rfl

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Wb

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

abbrev nX : Submodule D.host.E (perpS (VS D) F0.X) := F0.X.comap (perpS (VS D) F0.X).subtype

theorem hT_X_perp {x y : (VS D).V} (hx : x ∈ F0.X) (hy : y ∈ perpS (VS D) F0.X) : (VS D).hT x y = 0 :=
  hy x hx

theorem hT_perp_X {x y : (VS D).V} (hx : x ∈ perpS (VS D) F0.X) (hy : y ∈ F0.X) : (VS D).hT x y = 0 := by
  rw [← (VS D).herm.eq y x, hx y hy, map_zero]

def hWbFun (x y : WbQ D F0) : D.host.E :=
  Quotient.liftOn₂' x y (fun a b => (VS D).hT a.1 b.1) (by
    intro a₁ b₁ a₂ b₂ ha hb
    have ha' : a₁.1 - a₂.1 ∈ F0.X := by
      have := (Submodule.quotientRel_def (nX D F0)).1 ha
      simpa using this
    have hb' : b₁.1 - b₂.1 ∈ F0.X := by
      have := (Submodule.quotientRel_def (nX D F0)).1 hb
      simpa using this
    have e1 : (VS D).hT (a₁.1 - a₂.1) b₁.1 = 0 := hT_X_perp D F0 ha' b₁.2
    have e2 : (VS D).hT a₂.1 (b₁.1 - b₂.1) = 0 := hT_perp_X D F0 a₂.2 hb'
    simp only [map_sub, LinearMap.sub_apply] at e1 e2
    show (VS D).hT a₁.1 b₁.1 = (VS D).hT a₂.1 b₂.1
    linear_combination e1 + e2)

theorem hWbFun_mk (a b : perpS (VS D) F0.X) :
    hWbFun D F0 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = (VS D).hT a.1 b.1 := rfl

def hWb : WbQ D F0 →ₗ⋆[D.host.E] WbQ D F0 →ₗ[D.host.E] D.host.E :=
  LinearMap.mk₂'ₛₗ (starRingEnd D.host.E) (RingHom.id D.host.E) (hWbFun D F0)
    (by
      intro x₁ x₂ y
      induction x₁ using Submodule.Quotient.induction_on with | H a₁ => ?_
      induction x₂ using Submodule.Quotient.induction_on with | H a₂ => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_add, hWbFun_mk, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro c x y
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_smul, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro x y₁ y₂
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y₁ using Submodule.Quotient.induction_on with | H b₁ => ?_
      induction y₂ using Submodule.Quotient.induction_on with | H b₂ => ?_
      rw [← Submodule.Quotient.mk_add, hWbFun_mk, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro c x y
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_smul, hWbFun_mk, hWbFun_mk]
      simp)

theorem hWb_mk (a b : perpS (VS D) F0.X) :
    hWb D F0 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = (VS D).hT a.1 b.1 := rfl

theorem z_mem_perp : F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F0.z_orth a
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def zbar : WbQ D F0 := Submodule.Quotient.mk ⟨F0.z, z_mem_perp D F0⟩

theorem hWb_zbar : hWb D F0 (zbar D F0) (zbar D F0) = -T := by
  rw [zbar, hWb_mk]
  exact F0.z_norm

def Mof (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (WbQ D F0) :=
  (Λ.comap ((perpS (VS D) F0.X).subtype.restrictScalars (𝓞 D.host.E))).map
    ((nX D F0).mkQ.restrictScalars (𝓞 D.host.E))

end Wb

def WbDef : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)),
    Formalism.HermitianLattices.Ext.L3.IsTotPosDef (hPerp (hWb D F0) (zbar D F0)) ∧
      finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) = D.R.k

def RowM : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsGlueLat (hWb D F0) (zbar D F0) (Mof D F0 Λ)

def RowSurj : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (M : Submodule (𝓞 D.host.E) (WbQ D F0)),
    IsGlueLat (hWb D F0) (zbar D F0) M → ∃ Λ, IsRowLat D F0 Λ ∧ Mof D F0 Λ = M

def RowClass : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
      ((∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ') ↔
        ∃ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ')

def RowWeight : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Nat.card (autLz D F0 Λ) = Nat.card (stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ))

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
