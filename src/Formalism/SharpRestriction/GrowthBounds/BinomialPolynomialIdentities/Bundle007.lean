module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.FormalSeriesConditionsB1ToB4
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle003
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SubProjectorProductMemStrict
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset
open scoped Pointwise

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints

theorem iInf_span_sup_smul_le {R M X κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] {b : X → M}
    (hb : LinearIndependent R b) (A : κ → Set X) [Nonempty κ] (q : R) :
    (⨅ i, (Submodule.span R (b '' A i) ⊔ q • Submodule.span R (Set.range b))) ≤
      (⨅ i, Submodule.span R (b '' A i)) ⊔ q • Submodule.span R (Set.range b) := by
  classical
  intro G hG
  rw [Submodule.mem_iInf] at hG
  have h1 : ∀ i, ∃ z h : X →₀ R, z ∈ Finsupp.supported R R (A i) ∧
      G = Finsupp.linearCombination R b (z + q • h) := by
    intro i
    obtain ⟨Z, hZ, Y, hY, hsum⟩ := Submodule.mem_sup.1 (hG i)
    obtain ⟨z, hz, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hZ
    obtain ⟨H, hH, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hY
    obtain ⟨h, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hH
    refine ⟨z, h, hz, ?_⟩
    rw [← hsum, map_add (f := _), map_smul]
    rfl
  choose z h hz hG' using h1
  obtain ⟨i0⟩ := (inferInstance : Nonempty κ)
  set c : X →₀ R := z i0 + q • h i0 with hc
  have hci : ∀ i, z i + q • h i = c := fun i => hb ((hG' i).symm.trans (hG' i0))
  have hdiv : ∀ x, (¬ ∀ i, x ∈ A i) → ∃ d, c x = q * d := by
    intro x hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    refine ⟨h i x, ?_⟩
    rw [← hci i, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : z i x = 0 := by
      by_contra hne
      exact hi ((Finsupp.mem_supported R (z i)).1 (hz i) (Finsupp.mem_support_iff.2 hne))
    rw [this, zero_add]
  choose! d hd using hdiv
  have hGc : G = ∑ x ∈ c.support, c x • b x := by
    rw [hG' i0, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [← Finset.sum_filter_add_sum_filter_not c.support (fun x => ∀ i, x ∈ A i)] at hGc
  rw [hGc]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [Submodule.mem_iInf]
    intro i
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
    exact (Finset.mem_filter.1 hx).2 i
  · rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨∑ x ∈ c.support.filter (fun x => ¬ ∀ i, x ∈ A i), d x • b x, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hd x (Finset.mem_filter.1 hx).2, mul_smul]

section

variable {O : Type} [CommRing O] {N n : ℕ} (LL : Letters (Fin N)) (B : Fin N → ℕ)

def wd (R : Type) [CommRing R] (x : WI n N LL B) : MvPolynomial (Fin N × Fin n) R := Psi R x.1.1.mu x.1.2

theorem span_standard_words_eq (R : Type) [CommRing R] (cond : PPath n N LL B → Prop) :
    Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I, IsSt P.mu I ∧ cond P ∧ G = Psi R P.mu I} =
      Submodule.span R (wd LL B R '' {x | cond x.1.1}) := by
  congr 1
  ext G
  constructor
  · rintro ⟨P, I, hI, hp, rfl⟩
    exact ⟨⟨(P, I), hI⟩, hp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1.1, x.1.2, x.2, hx, rfl⟩

theorem span_words_eq_polynomials (R : Type) [CommRing R] : Submodule.span R (Set.range (wd LL B R)) = Pol R n B := by
  rw [← (standardPath_basis_any_ring R N n LL B).2]
  congr 1
  ext G
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1.1, x.1.2, x.2, rfl⟩
  · rintro ⟨P, I, hI, rfl⟩
    exact ⟨⟨(P, I), hI⟩, rfl⟩

end

theorem saturatedLowerSetSpan_of_lowerSetTypesSpan (D : Formalism.BasicNotions.D7) (hN2 : LowerSetTypesSpan) : SaturatedLowerSetSpan D := by
  classical
  intro O _ _ _ _ N n LL B pi hpi
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  have hmapwd : ∀ x : WI n N LL B, MvPolynomial.map (algebraMap O (KK O)) (wd LL B O x) = wd LL B (KK O) x :=
    fun x => Formalism.MainNotions.LemmaBAlt.map_Psi' (algebraMap O (KK O)) x.1.1.mu x.1.2
  have hLIK : LinearIndependent (KK O) (wd LL B (KK O)) := (standardPath_basis_any_ring (KK O) N n LL B).1
  have hLIO : LinearIndependent O (wd LL B O) := (standardPath_basis_any_ring O N n LL B).1
  have hT : ∀ i : Fin (N + 1), Pol (KK O) n B ⊓ (⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam) =
      Submodule.span (KK O) (wd LL B (KK O) '' {x | x.1.1.mu i ∈ pi i}) := by
    intro i
    rw [hN2 (KK O) N n LL B i (pi i) (hpi i)]
    exact span_standard_words_eq LL B (KK O) (fun P => P.mu i ∈ pi i)
  have hmaplc : ∀ c : WI n N LL B →₀ O, MvPolynomial.map (algebraMap O (KK O)) (Finsupp.linearCombination O (wd LL B O) c) =
      Finsupp.linearCombination (KK O) (wd LL B (KK O)) (c.mapRange (algebraMap O (KK O)) (map_zero _)) := by
    intro c

    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmapwd, ← MvPolynomial.smul_eq_C_mul]
  constructor
  · intro Ix
    have hspan : nestSpan O N n LL B pi Ix = Submodule.span O (wd LL B O '' {x | ∀ i ∈ Ix, x.1.1.mu i ∈ pi i}) :=
      span_standard_words_eq LL B O (fun P => ∀ i ∈ Ix, P.mu i ∈ pi i)
    ext G
    constructor
    · rintro ⟨hG, hGi⟩
      rw [← span_words_eq_polynomials LL B O] at hG
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hG
      change (c.sum fun x a => a • wd LL B O x) ∈ nestSpan O N n LL B pi Ix
      rw [hspan]
      refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
      intro i hi
      have h1 : MvPolynomial.map (algebraMap O (KK O)) (Finsupp.linearCombination O (wd LL B O) c) ∈
          Submodule.span (KK O) (wd LL B (KK O) '' {x | x.1.1.mu i ∈ pi i}) := by
        rw [← hT i]
        refine ⟨?_, hGi i hi⟩
        rw [hmaplc, ← span_words_eq_polynomials LL B (KK O)]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩
      obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination (KK O)).1 h1
      rw [hmaplc] at hle
      have hlc := hLIK hle
      have hxl : x ∈ l.support := by
        rw [hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]
        intro h0
        exact (Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))
      exact (Finsupp.mem_supported (KK O) l).1 hl hxl
    · intro hG
      change G ∈ nestSpan O N n LL B pi Ix at hG
      rw [hspan] at hG
      induction hG using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        refine ⟨?_, fun i hi => ?_⟩
        · rw [← span_words_eq_polynomials LL B O]
          exact Submodule.subset_span ⟨x, rfl⟩
        · rw [hmapwd]
          have : wd LL B (KK O) x ∈ Pol (KK O) n B ⊓
              (⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam) := by
            rw [hT i]
            exact Submodule.subset_span ⟨x, hx i hi, rfl⟩
          exact this.2
      | zero => exact ⟨Submodule.zero_mem _, fun i _ => by rw [map_zero]; exact Submodule.zero_mem _⟩
      | add x y _ _ hx hy =>
        exact ⟨Submodule.add_mem _ hx.1 hy.1, fun i hi => by
          rw [map_add (f := _)]; exact Submodule.add_mem _ (hx.2 i hi) (hy.2 i hi)⟩
      | smul a x _ hx =>
        exact ⟨Submodule.smul_mem _ _ hx.1, fun i hi => by
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
          exact Submodule.smul_mem _ _ (hx.2 i hi)⟩
  · intro p E
    have hspan : ∀ i : Fin (N + 1), nestSpan O N n LL B pi {i} =
        Submodule.span O (wd LL B O '' {x | x.1.1.mu i ∈ pi i}) := by
      intro i
      have h1 : {x : WI n N LL B | ∀ i' ∈ ({i} : Set (Fin (N + 1))), x.1.1.mu i' ∈ pi i'} =
          {x | x.1.1.mu i ∈ pi i} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
      rw [← h1]
      exact span_standard_words_eq LL B O (fun P => ∀ i' ∈ ({i} : Set (Fin (N + 1))), P.mu i' ∈ pi i')
    simp only [hspan]
    rw [Submodule.ideal_span_singleton_smul, ← span_words_eq_polynomials LL B O]
    apply le_antisymm
    · exact iInf_span_sup_smul_le hLIO _ _
    · exact le_iInf fun i => sup_le_sup_right (iInf_le _ i) _

end Formalism.MainNotions.G.ColumnFamilies
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt

theorem disjoint_restrictSupport_of_disjoint {R σ : Type*} [CommRing R] {s t : Set (σ →₀ ℕ)} (h : Disjoint s t) :
    Disjoint (MvPolynomial.restrictSupport R s) (MvPolynomial.restrictSupport R t) := by
  rw [Submodule.disjoint_def]
  intro x hs ht
  rw [MvPolynomial.mem_restrictSupport_iff] at hs ht
  by_contra hx
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx
  exact (Set.disjoint_left.1 h) (hs (by simpa using hm)) (ht (by simpa using hm))

theorem linearIndependent_words_all_degrees (R : Type) [CommRing R] (N n : ℕ) (LL : Letters (Fin N)) :
    LinearIndependent R (fun x : (Σ b : Fin N → ℕ, WI n N LL b) => Psi R x.2.1.1.mu x.2.1.2) := by
  refine linearIndependent_iUnion_finite (f := fun (b : Fin N → ℕ) (x : WI n N LL b) => Psi R x.1.1.mu x.1.2)
    (fun b => (standardPath_basis_any_ring R N n LL b).1) ?_
  intro b t _ hb
  have h1 : ∀ b' : Fin N → ℕ, Submodule.span R (Set.range fun x : WI n N LL b' => Psi R x.1.1.mu x.1.2) ≤
      Pol R n b' := by
    intro b'
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact standardWord_mem_multihomogeneous R x.1.1 x.1.2 x.2
  have h2 : (⨆ i ∈ t, Submodule.span R (Set.range fun x : WI n N LL i => Psi R x.1.1.mu x.1.2)) ≤
      MvPolynomial.restrictSupport R {m : Fin N × Fin n →₀ ℕ | ∃ i ∈ t, ∀ j, multideg m j = i j} := by
    refine iSup₂_le fun i hi => (h1 i).trans ?_
    intro x hx
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hx
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    exact ⟨i, hi, hx hm⟩
  refine Disjoint.mono (h1 b) h2 (disjoint_restrictSupport_of_disjoint ?_)
  rw [Set.disjoint_left]
  rintro m hm ⟨i, hi, hmi⟩
  apply hb
  have : b = i := by
    funext j
    rw [← hm j, hmi j]
  rw [this]
  exact hi

section Theta

variable (R : Type) [CommRing R] (N r K : ℕ)

def towerToPolynomialHom : MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) →+*
    MvPolynomial (Fin N × Fin (r + K)) R :=
  MvPolynomial.eval₂Hom (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom
    (fun v => X (plVar (K := K) v))

def joinVarsRingHom : MvPolynomial (Fin N × Fin (r + K)) R →+*
    MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun v => Fin.addCases (motive := fun _ => MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R))
      (fun a => X (v.1, a)) (fun b => C (X (v.1, b))) v.2)

theorem towerToPolynomialHom_C_eq_rename_tan (s : MvPolynomial (Fin N × Fin K) R) : towerToPolynomialHom R N r K (C s) = rename (tanVar (r := r)) s := by
  simp [towerToPolynomialHom]

theorem towerToPolynomialHom_X_eq_X_pl (v : Fin N × Fin r) : towerToPolynomialHom R N r K (X v) = X (plVar (K := K) v) := by
  simp [towerToPolynomialHom]

theorem joinVarsRingHom_comp_towerToPolynomialHom_eq_id : (joinVarsRingHom R N r K).comp (towerToPolynomialHom R N r K) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro s
    have : ((joinVarsRingHom R N r K).comp (towerToPolynomialHom R N r K)).comp MvPolynomial.C = (RingHom.id _).comp MvPolynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [towerToPolynomialHom_C_eq_rename_tan, joinVarsRingHom]
      · intro w
        simp [towerToPolynomialHom_C_eq_rename_tan, joinVarsRingHom, tanVar]
    exact congrArg (fun f => f s) this
  · intro v
    simp [towerToPolynomialHom_X_eq_X_pl, joinVarsRingHom, plVar]

theorem towerToPolynomialHom_injective : Function.Injective (towerToPolynomialHom R N r K) := by
  intro x y h
  have := congrArg (joinVarsRingHom R N r K) h
  have e : ∀ z, joinVarsRingHom R N r K (towerToPolynomialHom R N r K z) = z := fun z => congrArg (fun f => f z) (joinVarsRingHom_comp_towerToPolynomialHom_eq_id R N r K)
  rwa [e, e] at this

theorem towerToPolynomialHom_map_C_eq_rename_pl (a : MvPolynomial (Fin N × Fin r) R) :
    towerToPolynomialHom R N r K (MvPolynomial.map MvPolynomial.C a) = rename (plVar (K := K)) a := by
  have : (towerToPolynomialHom R N r K).comp (MvPolynomial.map MvPolynomial.C) =
      (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [towerToPolynomialHom_C_eq_rename_tan]
    · intro v
      simp [towerToPolynomialHom_X_eq_X_pl]
  exact congrArg (fun f => f a) this

def towerToPolynomialLinearMap : MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) →ₗ[R]
    MvPolynomial (Fin N × Fin (r + K)) R where
  toFun := towerToPolynomialHom R N r K
  map_add' := map_add _
  map_smul' := by
    intro c x
    have h1 : c • x = C (C c) * x := by
      rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    rw [h1, map_mul, towerToPolynomialHom_C_eq_rename_tan, rename_C, RingHom.id_apply, MvPolynomial.smul_eq_C_mul]

end Theta

theorem linearIndependent_productBasis (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    LinearIndependent R (pvec R r K LL B) := by
  classical
  have hb := linearIndependent_words_all_degrees R N K LL
  have hc := linearIndependent_words_all_degrees (MvPolynomial (Fin N × Fin K) R) N r LL
  have hbc := linearIndependent_smul hb hc
  have hex : ∀ x : PIdx r K LL B, ∃ y : (Σ b : Fin N → ℕ, WI K N LL b) × (Σ b : Fin N → ℕ, WI r N LL b),
      y.1.2.1.1.mu = x.1.2.1 ∧ y.1.2.1.2 = x.1.2.2 ∧ y.2.2.1.1.mu = x.1.1.1 ∧ y.2.2.1.2 = x.1.1.2 := by
    rintro ⟨⟨⟨nu, I'⟩, ⟨ka, I''⟩⟩, ⟨b', b'', _, ⟨P1, e1⟩, ⟨P2, e2⟩⟩, h2, h3⟩
    have e1' : P1.mu = nu := e1
    have e2' : P2.mu = ka := e2
    have h2' : IsSt P1.mu I' := by rw [e1']; exact h2
    have h3' : IsSt P2.mu I'' := by rw [e2']; exact h3
    exact ⟨(⟨b'', ⟨(P2, I''), h3'⟩⟩, ⟨b', ⟨(P1, I'), h2'⟩⟩), e2', rfl, e1', rfl⟩
  choose io hio using hex
  have hinj : Function.Injective io := by
    intro x y hxy
    obtain ⟨a1, a2, a3, a4⟩ := hio x
    obtain ⟨c1, c2, c3, c4⟩ := hio y
    rw [hxy] at a1 a2 a3 a4
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rw [← a3, c3]
      · rw [← a4, c4]
    · apply Prod.ext
      · rw [← a1, c1]
      · rw [← a2, c2]
  have h1 := (hbc.comp io hinj).map' (towerToPolynomialLinearMap R N r K)
    (LinearMap.ker_eq_bot.2 (towerToPolynomialHom_injective R N r K))
  have h2 : (⇑(towerToPolynomialLinearMap R N r K) ∘ (fun p : (Σ b : Fin N → ℕ, WI K N LL b) × (Σ b : Fin N → ℕ, WI r N LL b) =>
      Psi R p.1.2.1.1.mu p.1.2.1.2 • Psi (MvPolynomial (Fin N × Fin K) R) p.2.2.1.1.mu p.2.2.1.2) ∘ io) =
      pvec R r K LL B := by
    funext x
    obtain ⟨a1, a2, a3, a4⟩ := hio x
    simp only [Function.comp_apply]
    rw [a1, a2, a3, a4]
    change towerToPolynomialHom R N r K _ = _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, towerToPolynomialHom_C_eq_rename_tan, ← map_Psi' (MvPolynomial.C : R →+* _), towerToPolynomialHom_map_C_eq_rename_pl]
    unfold pvec PsiPl PsiTan
    rw [mul_comm]
  rw [← h2]
  exact h1

end Formalism.MainNotions.G.ColumnFamilies
end
end

section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem adm_fourteen (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.JointComponentsPaths D :=
  joint_components_paths_of_joint_dimension D (isotypic_projections_commute_holds D) (lower_set_types_span D) restJointDim

end Formalism.MainNotions.G.ColumnFamilies
end
