module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle020
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem comb_entry {F G : Type} [Field F] {n m : ℕ} (r : G → Matrix (Fin n) (Fin n) F)
    (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (α β : Fin m → F) (c : G →₀ F) (i j : Fin n) :
    (c.sum fun g x => x • ((∑ k, α k • κ k g + ∑ k, β k • la k g) * r g)) i j =
      ∑ k, ((c.sum fun g x => x • (κ k g * r g)) i j * α k + (c.sum fun g x => x • (la k g * r g)) i j * β k) := by
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_mul, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.add_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm (s := c.support) (f := fun x k => c x * (α k * (κ k x * r x) i j)),
    Finset.sum_comm (s := c.support) (f := fun x k => c x * (β k * (la k x * r x) i j))]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem UpperTheory.V.Pa.Det.oddPart :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ k, ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, la k g = dTw D.χF D.r Y g := by
  intro F G _ _ n D m κ la s ph hK hT k
  classical
  by_cases ha : D.a < n
  · have hpos := D.a_pos
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨D.a, ha⟩
    have hij : ¬((i : ℕ) < D.a ↔ (j : ℕ) < D.a) := by
      intro h
      exact lt_irrefl D.a (h.mp (show (0 : ℕ) < D.a by omega))
    have hji : ¬((j : ℕ) < D.a ↔ (i : ℕ) < D.a) := fun h => hij h.symm
    have step1 : ∀ c' : G →₀ F, (∀ g ∈ c'.support, g ∈ D.G') → (c'.sum fun g x => x • D.r g) = 0 →
        ∀ k', (c'.sum fun g x => x • (la k' g * D.r g)) j i = 0 := by
      intro c' hc' hr'
      have hkill : D.KillsRel (fun g => ∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) i j := by
        intro c hc hr
        show (c.sum fun g x => x • ((∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) * D.r g)) i j = 0
        rw [comb_entry]
        exact Det.relPair D κ la s ph hK hT c c' hc hc' hr hr' i j hij
      have h := (Det.ann D κ la s ph hK hT _ _ i j hij hkill).1
      intro k'
      exact congrFun h k'
    have hkill2 : D.KillsRel (fun g => ∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) j i := by
      intro c hc hr
      show (c.sum fun g x => x • ((∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) * D.r g)) j i = 0
      rw [comb_entry]
      simp [step1 c hc hr]
    obtain ⟨_, Y, hY, hs, hg⟩ := Det.ann D κ la s ph hK hT 0 (Pi.single k 1) j i hji hkill2
    refine ⟨Y, hY, hs, fun g => ?_⟩
    rw [← hg g]
    simp [Pi.single_apply]
  · have han : D.a = n := le_antisymm D.a_le (not_lt.mp ha)
    refine ⟨0, Submodule.zero_mem _, by simp, fun g => ?_⟩
    have h0 : la k g = 0 := by
      ext i j
      have hm := (hT.od k g i j).1 (by rw [han]; exact iff_of_true i.2 j.2)
      exact (Submodule.mem_bot F).mp hm
    rw [h0]
    simp [dTw]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices
open UpperTheory.V.CA

private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  obtain ⟨-, -, hm, -⟩ := UpperTheory.V.CA.d_gmap D
  have e1 := (hm f (MonoidAlgebra.single g 1)).2 1
  have hs : (MonoidAlgebra.mapRingHom G f) (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    simp [MonoidAlgebra.mapRingHom]
  rw [hs, h] at e1
  have e2 : (GDet.ofRep ρ).tr (MonoidAlgebra.single g 1) = (ρ g).trace := by
    rw [← (UpperTheory.V.CA.d_toDet (GDet.ofRep ρ) _).2.2.1, (UpperTheory.V.CA.d_toDet_ofRep).1 ρ,
      ((UpperTheory.V.CA.d_ofRep _ _ _).2.2.1 (by simpa using hn))]
    simp [GDet.repAlg]
  unfold GDet.tr at e2
  unfold GDet.tr
  rw [← e1, e2]

private theorem span_of_gram {n : ℕ} {K : Type} [Field K] (s : Set (Matrix (Fin n) (Fin n) K))
    (x y : Fin (n * n) → Matrix (Fin n) (Fin n) K) (hx : ∀ a, x a ∈ s)
    (hdet : Matrix.det (Matrix.of fun a b => (x a * y b).trace) ≠ 0) : Submodule.span K s = ⊤ := by
  have hli : LinearIndependent K x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Matrix.vecMul c (Matrix.of fun a b => (x a * y b).trace) = 0 := by
      funext b
      have h0 : ((∑ a, c a • x a) * y b).trace = 0 := by rw [hc]; simp
      rw [Finset.sum_mul, Matrix.trace_sum] at h0
      simpa [Matrix.vecMul, dotProduct, Matrix.trace_smul, smul_mul_assoc] using h0
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    intro i
    simp [this]
  by_cases hn : n = 0
  · subst hn
    exact Subsingleton.elim _ _
  · haveI : Nonempty (Fin (n * n)) := ⟨⟨0, Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hn)⟩⟩
    have htop := hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact hx a

private theorem discSt_iff {n : ℕ} {A G K : Type} [CommRing A] [Group G] [Field K]
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ)
    (Q : Ideal A) (hQ : ∀ b, f b = 0 ↔ b ∈ Q) :
    DiscSt D Q ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : IsEmpty (Fin (0 * 0)) := ⟨fun i => Fin.elim0 i⟩
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      refine ⟨fun _ => 1, fun _ => 1, ?_⟩
      rw [Matrix.det_isEmpty, ← hQ, map_one]
      exact one_ne_zero
  · have key : ∀ g h' : Fin (n * n) → G,
        (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)).det ∉ Q ↔
          (Matrix.of fun i j => (ρ (g i) * ρ (h' j)).trace).det ≠ 0 := by
      intro g h'
      have hm : f.mapMatrix (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)) =
          Matrix.of fun i j => (ρ (g i) * ρ (h' j)).trace := by
        ext i j
        simp [tr_of_map hn D f ρ h, map_mul]
      have e := hQ (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)).det
      rw [RingHom.map_det, hm] at e
      exact not_congr e.symm
    unfold DiscSt
    constructor
    · rintro ⟨g, h', hd⟩
      rw [key] at hd
      exact span_of_gram _ (fun a => ρ (g a)) (fun b => ρ (h' b)) (fun a => ⟨g a, rfl⟩) hd
    · intro hs
      obtain ⟨x, hx, hd⟩ := (UpperTheory.V.CA.g_gram K (Fin n) _).1 hs
      choose gg hgg using hx
      refine ⟨fun i => gg (finProdFinEquiv.symm i), fun i => gg (finProdFinEquiv.symm i), ?_⟩
      rw [key]
      have hr : (Matrix.of fun i j => (ρ (gg (finProdFinEquiv.symm i)) * ρ (gg (finProdFinEquiv.symm j))).trace) =
          Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.of fun a b => (x a * x b).trace) := by
        ext i j
        simp [hgg]
      rw [hr, Matrix.det_reindex_self]
      exact hd

private theorem irr_iff_span {n : ℕ} {G K : Type} [Group G] [Field K] [IsAlgClosed K]
    (ρ : G →* Matrix (Fin n) (Fin n) K) :
    UpperTheory.V.U3.MatIrr ⊤ ρ ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  rw [← (UpperTheory.V.AlgebraTools.irred_iff_span (RingHom.id K) ρ).1]
  exact ⟨fun h N hN => h N fun g _ => hN g, fun h N hN => h N fun g => hN g (Subgroup.mem_top g)⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.discStIff :
    ∀ {n : ℕ} {R G κ : Type} [CommRing R] [Group G] [Field κ] [IsAlgClosed κ] (D : GDet n R G) (f : R →+* κ), DiscSt D (RingHom.ker f) ↔ ∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ := by
  intro n R G κ _ _ _ _ D f
  have hQ : ∀ b, f b = 0 ↔ b ∈ RingHom.ker f := fun b => RingHom.mem_ker.symm
  constructor
  · intro h
    obtain ⟨ρ, -, hρ, -⟩ := UpperTheory.V.CA.groupDet_exists_semisimple_representation (D.map f)
    exact ⟨ρ, (irr_iff_span ρ).2 ((discSt_iff D f ρ hρ.symm _ hQ).1 h), hρ.symm⟩
  · rintro ⟨ρ, hirr, hρ⟩
    exact (discSt_iff D f ρ hρ _ hQ).2 ((irr_iff_span ρ).1 hirr)
end
