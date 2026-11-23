module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelSumOfClassData
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem vt_nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  exact Int.toNat_le_toNat (by have := h hab; omega)

theorem vt_deltaLTw_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    deltaLTw O Kf m lam g ≤ nablaLTw O Kf m lam g := by
  unfold deltaLTw nablaLTw
  apply Submodule.map_mono
  unfold deltaL nablaL
  apply Submodule.comap_mono
  apply Submodule.map_mono
  exact weylLeDual O (m + 1) (m + 1) le_rfl (nuOf lam) (vt_nuOf_antitone hlam)

theorem lowest_invariant_le_delta {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) ≤ deltaLTw O Kf m lam g := by
  unfold Dl0
  rw [if_pos hlam]
  exact iInf₂_le g ⟨hg, rfl⟩

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def vt_G (P : Places p O Kf) : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := PEmpty
  lev := fun x => x.elim
  e := 0

theorem vt_HtenW_le (P : Places p O Kf) (v : Fin P.nV) (Lv : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
    (hLv : IsLattice (P.W v) Lv) :
    ∀ z ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val Lv), z ∈ Vsp Kf (P.lam0 v) := by
  obtain ⟨g, hg, rfl⟩ := hLv
  have hle : HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) ≤
      (Vsp Kf (P.lam0 v)).restrictScalars O := by
    unfold HtenW tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone (P.lam0 v) (P.dom v) s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    have e : extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g) = colSpan O (la_tw (P.ι v) (P.σ v) s.val g) :=
      la_extO_G (vt_G P) v s.val g
    rw [e] at h1
    have hd := la_tw_det (P.ι v) (P.σ v) s.val g hg
    exact la_nablaLTw_le _ _ _ hd _ (vt_deltaLTw_le O Kf _ _ hanti _ (lowest_invariant_le_delta _ _ hanti _ hd h1))
  exact fun z hz => hle hz

theorem vt_HtupW_le (P : Places p O Kf) (L : P.Tup) (hL : P.IsLatTup L) : ∀ z ∈ P.HtupW L, z ∈ P.Vtup := by
  have hle : P.HtupW L ≤ P.Vtup.restrictScalars O := by
    unfold Places.HtupW Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, fun v => vt_HtenW_le P v (L v) (hL v) _ (hF v), rfl⟩
  exact fun z hz => hle hz

end Formalism.MainNotions.FormalGroupSystem.Pf

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem vt_FQ {p : ℕ} [Fact p.Prime] (X : Sys p) {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j)
    (L : (X.Pj j).Tup) : F c L ∈ (X.Pj j).Vtup := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    have h := (mem_Int_iff X j x).1 hx
    by_cases hL : (X.Pj j).IsLatTup L
    · exact vt_HtupW_le (X.Pj j) L hL _ (h.1 c L hL)
    · rw [h.2.1 c L hL]; exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem edges_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  apply Formalism.MainNotions.G.LatticeSystems.ef_edges_finite_gen
  apply Nat.finite_of_card_ne_zero
  rw [(P.setting v).res_card]
  exact pow_ne_zero _ (P.setting v).prime.ne_zero

def EE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (edges_fin P v i L).toFinset

theorem mem_EE {v : Fin P.nV} {i : ℕ} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    L'' ∈ EE P v i L ↔ IsEdge p (P.n' v) i ⟨L'', L⟩ :=
  Set.Finite.mem_toFinset _

theorem Tminus_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ EE P v i (L v), F (Function.update L v L'') :=
  finsum_mem_eq_finite_toFinset_sum _ (edges_fin P v i (L v))

def TminusLin (v : Fin P.nV) (i : ℕ) : (P.Tup → P.Xsp) →ₗ[Kf] (P.Tup → P.Xsp) where
  toFun := P.Tminus v i
  map_add' F F' := by
    funext L
    rw [Pi.add_apply, Tminus_eq, Tminus_eq, Tminus_eq, ← Finset.sum_add_distrib]
    rfl
  map_smul' c F := by
    funext L
    rw [RingHom.id_apply, Pi.smul_apply, Tminus_eq, Tminus_eq, Finset.smul_sum]
    rfl

theorem edge_zero_iff {v : Fin P.nV} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    IsEdge p (P.n' v) 0 ⟨L'', L⟩ ↔ IsLattice (P.W v) L ∧ L'' = L := by
  constructor
  · rintro ⟨_, h2, h3, _, h5⟩
    refine ⟨h2, le_antisymm h3 ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique] at h5
    have h6 := (Submodule.Quotient.subsingleton_iff).1 h5.1
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ Submodule.comap L.subtype L'' := by
      have h7 : Submodule.comap L.subtype L'' = ⊤ := h6
      rw [h7]
      exact Submodule.mem_top
    exact this
  · rintro ⟨h, rfl⟩
    refine ⟨h, h, le_rfl, fun x hx => Submodule.smul_mem _ _ hx, ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique]
    have h7 : Submodule.comap (L''.subtype) L'' = ⊤ := Submodule.comap_subtype_self L''
    refine ⟨(Submodule.Quotient.subsingleton_iff).2 h7, ⟨0⟩⟩

theorem Tminus_zero_lat (v : Fin P.nV) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : IsLattice (P.W v) (L v)) :
    P.Tminus v 0 F L = F L := by
  rw [Tminus_eq]
  have : EE P v 0 (L v) = {L v} := by
    ext A
    rw [mem_EE, edge_zero_iff, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨hL, h⟩⟩
  rw [this, Finset.sum_singleton]
  exact congrArg F (Function.update_eq_self v L)

theorem Tminus_not_lat (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : ¬ IsLattice (P.W v) (L v)) :
    P.Tminus v i F L = 0 := by
  rw [Tminus_eq]
  have : EE P v i (L v) = ∅ := by
    ext A
    rw [mem_EE]
    simp only [Finset.notMem_empty, iff_false]
    exact fun h => hL h.2.1
  rw [this, Finset.sum_empty]

end PlacesLevel

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def TmLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j where
  toFun := X.Tm v i j
  map_add' F F' := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_add (F c) (F' c)
  map_smul' a F := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_smul a (F c)

def TtLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  if i = 0 then LinearMap.id else ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j i)) • TmLin X v i j

@[simp] theorem TtLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : TtLin X v i j F = X.Tt v i j F := by
  unfold TtLin Sys.Tt
  split_ifs <;> rfl

theorem yv_eq (v : X.Pl) (F : X.Fm 0) : X.yv v F = ((p : X.G.Kf) ^ X.G.P.ArV v) • X.Tm v X.G.P.r 0 F := rfl

def yvLin (v : X.Pl) : X.Fm 0 →ₗ[X.G.Kf] X.Fm 0 := ((p : X.G.Kf) ^ X.G.P.ArV v) • TmLin X v X.G.P.r 0

theorem Int_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.Int j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  have h1 : F c ∈ (X.Lv.lev j c).M := hF c (Set.mem_univ c)
  unfold Level.M Level.funMod at h1
  have h2 : F c ∈ (⨅ (L : (X.Pj j).Tup) (_ : ¬ (X.Pj j).IsLatTup L),
      LinearMap.ker (LinearMap.proj (R := X.G.O) (φ := fun _ : (X.Pj j).Tup => (X.Pj j).Xsp) L)) := h1.1.2
  rw [Submodule.mem_iInf] at h2
  have h3 := h2 L
  rw [Submodule.mem_iInf] at h3
  exact h3 hL

theorem FQ_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx => exact Int_zero_off X hx c L hL
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, Pi.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [Pi.smul_apply, Pi.smul_apply, hx, smul_zero]

theorem Tm_zero {j : ℕ} (v : X.Pl) {F : X.Fm j} (hF : F ∈ X.FQ j) : X.Tm v 0 j F = F := by
  funext c L
  show (X.Pj j).Tminus (X.vJ j v) 0 (F c) L = F c L
  by_cases hL : IsLattice ((X.Pj j).W (X.vJ j v)) (L (X.vJ j v))
  · exact Tminus_zero_lat _ _ _ _ hL
  · rw [Tminus_not_lat _ _ _ _ _ hL, FQ_zero_off X hF c L fun h => hL (h _)]

end SysLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

section Loc

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem between_fin (p k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (L : Submodule W (Fin k → Qq))
    (hL : IsLattice W L) :
    {A : Submodule W (Fin k → Qq) | A ≤ L ∧ ∀ x ∈ L, (p : W) • x ∈ A}.Finite := by
  classical
  obtain ⟨g, -, hg⟩ := hL
  have hfg : L.FG := by
    rw [hg]; exact Submodule.fg_span (Set.finite_range _)
  have : Module.Finite W L := Module.Finite.iff_fg.mpr hfg
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have : Module.Finite (W ⧸ I) (↥L ⧸ I • (⊤ : Submodule W L)) :=
    Module.Finite.of_restrictScalars_finite W _ _
  have : Finite (↥L ⧸ I • (⊤ : Submodule W L)) := Module.finite_of_finite (W ⧸ I)
  let f : Submodule W (Fin k → Qq) → Set (↥L ⧸ I • (⊤ : Submodule W L)) :=
    fun A => ((A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ : Set _)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  have key : ∀ A : Submodule W (Fin k → Qq), (∀ x ∈ L, (p : W) • x ∈ A) →
      I • (⊤ : Submodule W L) ≤ A.comap L.subtype := by
    intro A hA
    rw [Submodule.smul_le]
    intro a ha x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [mul_smul]
    apply Submodule.smul_mem
    show (p : W) • (x : Fin k → Qq) ∈ A
    exact hA x x.2
  intro A hA B hB hAB
  have h1 : (A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ =
      (B.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ := SetLike.coe_injective hAB
  have h2 := congrArg (Submodule.comap (I • (⊤ : Submodule W L)).mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.mpr (key A hA.2),
    sup_eq_right.mpr (key B hB.2)] at h2
  have h3 := congrArg (Submodule.map L.subtype) h2
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hA.1,
    inf_eq_right.mpr hB.1] at h3
  exact h3

theorem up_fin_gen (p n' r k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (hp : algebraMap W Qq (p : W) ≠ 0)
    (A : Submodule W (Fin k → Qq)) :
    {A1 : Submodule W (Fin k → Qq) | IsEdge p n' r ⟨A, A1⟩}.Finite := by
  by_cases hA : IsLattice W A
  · let φ : (Fin k → Qq) →ₗ[W] (Fin k → Qq) := (p : W) • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : (p : W) • x = (p : W) • y := hxy
      rw [← algebraMap_smul Qq (p : W) x, ← algebraMap_smul Qq (p : W) y] at h1
      exact smul_right_injective _ hp h1
    refine Set.Finite.of_finite_image (f := fun A1 => A1.map φ) ((between_fin p k hfin A hA).subset ?_)
      (fun a _ b _ h => Submodule.map_injective_of_injective hφ h)
    rintro _ ⟨A1, hA1, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hA1.2.2.2.1 x hx
    · intro x hx
      exact ⟨x, hA1.2.2.1 hx, rfl⟩
  · apply Set.Finite.subset Set.finite_empty
    intro A1 h
    exact (hA h.1).elim

theorem count_fun (hC : CountLoc) (p n' : ℕ) [IsDomain W] [IsDiscreteValuationRing W] (h1 : IsFractionRing W Qq)
    (h2 : Irreducible (p : W)) (h3 : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (N N' g i : ℕ) (hN : N' = N + g)
    (A : Submodule W (Fin N → Qq)) (B : Submodule W (Fin N' → Qq)) (hA : IsLattice W A) (hB : IsLattice W B)
    (SB : Finset (Submodule W (Fin N' → Qq))) (hSB : ∀ B1, B1 ∈ SB ↔ IsEdge p n' i ⟨B1, B⟩)
    (SA : ℕ → Finset (Submodule W (Fin N → Qq))) (hSA : ∀ k A1, A1 ∈ SA k ↔ IsEdge p n' k ⟨A, A1⟩)
    (x : Matrix (Fin N') (Fin N) Qq) :
    (∑ B1 ∈ SB, (by classical exact if ∀ y ∈ A, x.mulVec y ∈ B1 then (1 : ℚ) else 0)) =
      ∑ l ∈ range (i + 1), (((p ^ n') ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (p ^ n') g l : ℕ) : ℚ) *
        ∑ A1 ∈ SA (i - l), (by classical exact if ∀ y ∈ A1, x.mulVec y ∈ B then (1 : ℚ) else 0) := by
  classical
  have e1 : ∀ (M : ℕ) (S : Finset (Submodule W (Fin M → Qq))) (E Pp : Submodule W (Fin M → Qq) → Prop)
      (_ : ∀ Z, Z ∈ S ↔ E Z), (∑ Z ∈ S, if Pp Z then (1 : ℚ) else 0) =
        (Nat.card {Z : Submodule W (Fin M → Qq) // E Z ∧ Pp Z} : ℚ) := by
    intro M S E Pp hS
    rw [Finset.sum_boole]
    congr 1
    rw [← Nat.card_eq_fintype_card.trans (Fintype.card_coe (S.filter Pp))]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun Z => by rw [Finset.mem_filter, hS]
  have := hC p n' W Qq h1 h2 h3 N N' g i hN A B hA hB x
  convert congrArg (fun n : ℕ => (n : ℚ)) this using 1
  · exact e1 N' SB _ _ hSB
  · push_cast
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    exact e1 N (SA (i - l)) _ _ (hSA (i - l))

end Loc

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem hk_pQ_ne (v : Fin P.nV) : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 := by
  have := (P.setting v).frac_alt
  exact (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 (P.setting v).p_unif.ne_zero

theorem up_fin (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨A, A1⟩}.Finite := by
  apply up_fin_gen
  · apply Nat.finite_of_card_ne_zero
    rw [(P.setting v).res_card]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  · exact hk_pQ_ne P v

def UP (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (up_fin P v i A).toFinset

theorem mem_UP {v : Fin P.nV} {i : ℕ} {A A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    A1 ∈ UP P v i A ↔ IsEdge p (P.n' v) i ⟨A, A1⟩ := by
  simp [UP]

theorem hk_latTup_update {L : P.Tup} (hL : P.IsLatTup L) (v : Fin P.nV)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) := by
  unfold Places.IsLatTup at *
  intro w
  by_cases h : w = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A w = A := by
      first
        | exact Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
        | exact Function.update_same (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A w = L w := Function.update_of_ne (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) h A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr (hL w)

theorem latTup_smul (C : Level P) (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  constructor
  · intro h u
    have h1 : IsLattice (P.W u) ((L u).map (nt_phi (P.W u) (C.act u γ))) := h u
    have h2 := nt_lat_map (C.act u γ)⁻¹ _ h1
    rw [nt_map_inv] at h2
    exact h2
  · intro h u
    exact nt_lat_map (C.act u γ) (L u) (h u)

end PlacesLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
