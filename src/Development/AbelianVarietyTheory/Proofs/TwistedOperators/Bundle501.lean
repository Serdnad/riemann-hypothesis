module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.PathCut

variable {T : Type}

def height : Node → ℤ
  | .grid i j => (i : ℤ) - j
  | _ => 0

theorem height_tgt {m : ℕ} {t : T} {a : Arrow T} (h : IsGridArrow m t a) : height a.tgt = height a.src + 1 := by
  rcases h with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> simp [height] <;> push_cast <;> ring

theorem arrows_comp {X Y : Node} (p : Path T X Y) :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp p q]

theorem onGrid_snoc {m : ℕ} {t : T} {X : Node} {a : Arrow T} {p : Path T X a.src} :
    OnGrid m t (.snoc a p) ↔ OnGrid m t p ∧ IsGridArrow m t a := by
  simp [OnGrid, Path.arrows, or_imp, forall_and]

theorem height_le {m : ℕ} {t : T} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p → height X ≤ height Y
  | _, .nil, _ => le_rfl
  | _, .snoc a p, h => by
    rw [onGrid_snoc] at h
    have := height_le p h.1
    rw [height_tgt h.2]; omega

theorem height_arrows {m : ℕ} {t : T} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p →
    ∀ b ∈ p.arrows, height X ≤ height b.src ∧ height b.tgt ≤ height Y
  | _, .nil, _, b, hb => by simp [Path.arrows] at hb
  | _, .snoc a p, h, b, hb => by
    rw [onGrid_snoc] at h
    simp only [Path.arrows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl
    · have := height_arrows p h.1 b hb
      have h2 := height_tgt h.2
      exact ⟨this.1, by omega⟩
    · exact ⟨height_le p h.1, le_rfl⟩

theorem eq_down {m : ℕ} {t : T} {a : Arrow T} (h : IsGridArrow m t a) {i j : ℕ}
    (he : edgeOf a = .theta i j) : a = .down t i j := by
  rcases h with ⟨i', j', -, -, rfl⟩ | ⟨i', j', -, -, rfl⟩
  · simp [edgeOf] at he
  · simp only [edgeOf, GlobalTheory.SplitFlip.Edge.theta.injEq] at he
    rw [he.1, he.2]

theorem eq_right {m : ℕ} {t : T} {a : Arrow T} (h : IsGridArrow m t a) {i j : ℕ}
    (he : edgeOf a = .ex i j) : a = .right i j := by
  rcases h with ⟨i', j', -, -, rfl⟩ | ⟨i', j', -, -, rfl⟩
  · simp only [edgeOf, GlobalTheory.SplitFlip.Edge.ex.injEq] at he
    rw [he.1, he.2]
  · simp [edgeOf] at he

theorem edgeOf_ne {m : ℕ} {t : T} {b : Arrow T} (hb : IsGridArrow m t b) {i j : ℕ}
    (h : height b.tgt < (i : ℤ) - j ∨ (i : ℤ) - j < height b.src) :
    edgeOf b ≠ .theta i j ∧ edgeOf b ≠ .ex i j := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · obtain rfl := eq_down hb he
    (simp [height] at h) <;> omega
  · obtain rfl := eq_right hb he
    (simp [height] at h) <;> omega

theorem infix_concat' {α : Type*} {x y z : α} {l : List α} (h : [x, y] <:+: l ++ [z]) :
    [x, y] <:+: l ∨ ∃ l', l = l' ++ [x] ∧ z = y := by
  obtain ⟨s, u, hsu⟩ := h
  rcases List.eq_nil_or_concat u with rfl | ⟨u', w, rfl⟩
  · have h1 : (s ++ [x]) ++ [y] = l ++ [z] := by simpa using hsu
    obtain ⟨h2, h3⟩ := List.append_inj' h1 rfl
    exact Or.inr ⟨s, h2.symm, (List.singleton_inj.1 h3).symm⟩
  · have h1 : (s ++ [x, y] ++ u') ++ [w] = l ++ [z] := by simpa using hsu
    obtain ⟨h2, -⟩ := List.append_inj' h1 rfl
    exact Or.inl ⟨s, u', h2⟩

theorem exists_of_last {m : ℕ} {t : T} {i j : ℕ} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p →
    ∀ l, edges p = l ++ [.theta i j] → ∃ A : Path T X (.grid i (j + 1)), HEq p (Path.snoc (.down t i j) A)
  | _, .nil, _, l, h => by simp [edges, Path.arrows] at h
  | _, .snoc a q, hp, l, h => by
    rw [onGrid_snoc] at hp
    have h2 : edgeOf a = .theta i j := by
      have := congrArg List.getLast? h
      simpa [edges, Path.arrows] using this
    have ha : a = Arrow.down t i j := eq_down hp.2 h2
    subst a
    exact ⟨q, HEq.rfl⟩

theorem exists_cut {m : ℕ} {t : T} {i j : ℕ} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p →
    [GlobalTheory.SplitFlip.Edge.theta i j, GlobalTheory.SplitFlip.Edge.ex i j] <:+: edges p →
    ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp := by
  intro Y p
  induction p with
  | nil =>
    intro _ h
    simp [edges, Path.arrows] at h
  | snoc a q ih =>
    intro hp h
    rw [onGrid_snoc] at hp
    have he : edges (.snoc a q) = edges q ++ [edgeOf a] := by simp [edges, Path.arrows]
    rw [he] at h
    rcases infix_concat' h with h | ⟨l, hl, ha⟩
    · obtain ⟨A, Bq, rfl⟩ := ih hp.1 h
      exact ⟨A, .snoc a Bq, rfl⟩
    · have ha' : a = Arrow.right i j := eq_right (m := m) (t := t) hp.2 ha
      subst a
      obtain ⟨A, hA⟩ := exists_of_last (m := m) (t := t) q hp.1 l hl
      have hq : q = Path.snoc (Arrow.down t i j) A := eq_of_heq hA
      subst q
      exact ⟨A, .nil, rfl⟩

end GlobalTheory.PathCut

namespace GlobalTheory.PathCut

theorem cut_at_square : ∀ {T : Type} (m : ℕ) (t : T) (i j : ℕ), i < m → j < m → ∀ {X Y : Node} (p : Path T X Y),
    GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.SplitFlip.PassesThrough i j (GlobalTheory.FlipRun.edges p) →
    ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp ∧
      GlobalTheory.FlipRun.OnGrid m t A ∧ GlobalTheory.FlipRun.OnGrid m t Bp ∧
      GlobalTheory.FlipRun.OnGrid m t ((A.comp (routeBig t i j)).comp Bp) ∧
      GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp) = GlobalTheory.SplitFlip.flipPath i j (GlobalTheory.FlipRun.edges p) := by
  intro T m t i j hi hj X Y p hp hpass
  obtain ⟨A, Bp, rfl⟩ := exists_cut p hp hpass
  have harr : ((A.comp (routeSmall t i j)).comp Bp).arrows = A.arrows ++ [.down t i j, .right i j] ++ Bp.arrows := by
    simp [arrows_comp, Path.arrows, routeSmall, Path.one]
  have harr' : ((A.comp (routeBig t i j)).comp Bp).arrows =
      A.arrows ++ [.right i (j + 1), .down t (i + 1) j] ++ Bp.arrows := by
    simp [arrows_comp, Path.arrows, routeBig, Path.one]
  have hA : OnGrid m t A := fun b hb => hp b (by rw [harr]; simp [hb])
  have hB : OnGrid m t Bp := fun b hb => hp b (by rw [harr]; simp [hb])
  refine ⟨A, Bp, rfl, hA, hB, ?_, ?_⟩
  · intro b hb
    rw [harr'] at hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (hb | rfl | rfl) | hb
    · exact hA b hb
    · exact Or.inl ⟨i, j + 1, hi, hj, rfl⟩
    · exact Or.inr ⟨i + 1, j, hi, hj, rfl⟩
    · exact hB b hb
  · unfold edges GlobalTheory.SplitFlip.flipPath
    rw [harr, harr']
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    have hfA := fun b hb => height_arrows A hA b hb
    have hfB := fun b hb => height_arrows Bp hB b hb
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
    · refine List.map_congr_left fun b hb => ?_
      have h1 : height b.tgt ≤ (i : ℤ) - ((j + 1 : ℕ) : ℤ) := (hfA b hb).2
      obtain ⟨n1, n2⟩ := edgeOf_ne (hA b hb) (i := i) (j := j) (Or.inl (by push_cast at h1; omega))
      simp only [Function.comp, if_neg n1, if_neg n2]
    · simp [edgeOf]
    · refine List.map_congr_left fun b hb => ?_
      have h1 : ((i + 1 : ℕ) : ℤ) - (j : ℤ) ≤ height b.src := (hfB b hb).1
      obtain ⟨n1, n2⟩ := edgeOf_ne (hB b hb) (i := i) (j := j) (Or.inr (by push_cast at h1; omega))
      simp only [Function.comp, if_neg n1, if_neg n2]

end GlobalTheory.PathCut
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def colPure (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (q : ∀ j : Fin D.R.m, PolF D (G.pT (.mu t 0 j)).rank (G.pS (.mu t 0 j)).rank) : PureT G (downPath t 0 D.R.m) :=
  downFam t 0 D.R.m fun j => W.fock (.mu t 0 j) (f j) (q j)

def givenFin (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) : PureT G (givenPath t D.R.m) :=
  Path.Fam.append (downFam t 0 D.R.m f) (rowFam 0 D.R.m fun i => W.cosVec i (Φ i))

def gPol (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : PolE G
  | .ex i 0 => if h : i < D.R.m then ρ ⟨i, h⟩ else 0
  | .ex _ (_ + 1) => 0
  | .theta 0 j => q j
  | .theta (_ + 1) _ => 0

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def ChainVecs (ch : Choice R) (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) : Prop :=
  ∀ j : Fin D.R.m, ((j : ℕ) + 1 < D.R.m → HEq (f j) (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq (f j) (R.vX t))

def ChainPols (ch : Choice R) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank) : Prop :=
  ∀ j : ℕ, (j + 1 < D.R.m → HEq (q j) (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq (q j) ch.cv.polX)

theorem exists_heq_fun (Y Y' : LSp D) (S S' : HSp D) (Λ Λ') (hY : Y = ⟨S, Λ⟩) (hY' : Y' = ⟨S', Λ'⟩) (f : WO S S' → ℂ) :
    ∃ f' : WO Y.sp Y'.sp → ℂ, HEq f' f := by
  subst hY hY'; exact ⟨f, HEq.rfl⟩

theorem exists_heq_pol {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : PolF D a b) : ∃ P' : PolF D a' b', HEq P' P := by
  subst ha hb; exact ⟨P, HEq.rfl⟩

theorem rank_col_lt (L : LevCh D T) {j : ℕ} (h : j < D.R.m) : (columnBlock L j).sp.rank = (Yc D j).rank := by
  rw [colY_lt L h]

theorem rank_col_m (L : LevCh D T) : (columnBlock L D.R.m).sp.rank = D.sp.X'.rank := by
  rw [colY_m L]

theorem exists_chainVecs (ch : Choice R) (t : T) : ∃ f, ChainVecs ch t f := by
  have H : ∀ j : Fin D.R.m, ∃ f : Sch ch.G (.down t 0 j),
      ((j : ℕ) + 1 < D.R.m → HEq f (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq f (R.vX t)) := fun ⟨j, hj⟩ => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh j) (columnBlock R.toLevCh (j + 1)) _ _ _ _ (colY_lt _ (by omega))
        (colY_lt _ h) (R.vY t j)
      exact ⟨f, fun _ => e, fun h' => by simp at h'; omega⟩
    · have e1 : j = D.R.m - 1 := by omega
      subst e1
      have e2 : columnBlock R.toLevCh (D.R.m - 1 + 1) = ⟨D.sp.X', R.ΛX⟩ := by
        rw [Nat.sub_add_cancel (by omega)]; exact colY_m _
      obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh (D.R.m - 1)) (columnBlock R.toLevCh (D.R.m - 1 + 1)) _ _ _ _
        (colY_lt _ (by omega)) e2 (R.vX t)
      exact ⟨f, fun h' => absurd h' h, fun _ => e⟩
  choose f hf using H
  exact ⟨f, hf⟩

theorem exists_chainPols (ch : Choice R) : ∃ q, ChainPols ch q := by
  have H : ∀ j : ℕ, ∃ q : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank,
      (j + 1 < D.R.m → HEq q (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq q ch.cv.polX) := fun j => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨q, e⟩ := exists_heq_pol (rank_col_lt R.toLevCh h) (rank_col_lt R.toLevCh (by omega)) (ch.cv.polY j)
      exact ⟨q, fun _ => e, fun h' => by omega⟩
    · by_cases h' : j + 1 = D.R.m
      · have e1 : j = D.R.m - 1 := by omega
        subst e1
        have e2 : (columnBlock R.toLevCh (D.R.m - 1 + 1)).sp.rank = D.sp.X'.rank := by
          rw [Nat.sub_add_cancel (by omega)]; exact rank_col_m _
        obtain ⟨q, e⟩ := exists_heq_pol e2 (rank_col_lt R.toLevCh (by omega)) ch.cv.polX
        exact ⟨q, fun h'' => absurd h'' h, fun _ => e⟩
      · exact ⟨0, fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
  choose q hq using H
  exact ⟨q, hq⟩

end GlobalTheory.FlipStart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ListedTypeConj

open Matrix GlobalTheory.ConjDS GlobalTheory.ConjMult Formalism.IndefR.Mult

variable {D : D7}

theorem isUnit_det_gramAt (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  refine isUnit_iff_ne_zero.2 ?_
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)

theorem isTypeAt_star {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ}
    (h : IsTypeAt θ V τ S φ) : IsTypeAt θ V τ (dualPar S) fun g => star (φ g) := by
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hG, hx⟩ := h
  have hJ := isUnit_det_gramAt V τ
  have key : ∀ g, rv (P.submatrix Fin.revPerm (Equiv.refl _) * g * (P.submatrix Fin.revPerm (Equiv.refl _))⁻¹) =
      P * g * P⁻¹ := fun g => by
    rw [inv_submatrix_equiv]
    have : P.submatrix Fin.revPerm (Equiv.refl _) * g * P⁻¹.submatrix (Equiv.refl _) Fin.revPerm = rv (P * g * P⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  refine ⟨Cj H, inferInstance, inferInstance, fun g => cjOp (σ (rv g)), nr lam, fun a => ε a.rev,
    P.submatrix Fin.revPerm (Equiv.refl _), isEnum_dual hE, isDS_transfer (fun _ => rfl) (cj H) (fun _ _ => rfl) hD,
    (Matrix.isUnit_submatrix_equiv _ _).2 hP, ?_, ?_⟩
  · rw [← hG, ← rv_Jm (ε := fun a => ε a.rev) (ε' := ε) (fun a => by simp), rv, conjTranspose_submatrix,
      submatrix_mul_equiv, submatrix_mul_equiv]
    rfl
  simp only [key]
  intro x
  obtain ⟨v, hv, ℓ, hℓ, ⟨S0, C, hS0, hC, hsum, B, hB, hBb⟩, hhas⟩ := hx x
  have hc1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, (cj H) (cjOp (σ (P * g * P⁻¹)) w) = σ (P * g * P⁻¹) ((cj H) w) :=
    fun _ _ _ => rfl
  have hc2 : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w,
      (cj H).symm (σ (P * g * P⁻¹) w) = cjOp (σ (P * g * P⁻¹)) ((cj H).symm w) := fun _ _ _ => rfl
  have hfold : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w,
      l.foldr (dRep fun g => σ (P * g * P⁻¹)) (cj H w) = cj H (l.foldr (dRep fun g => cjOp (σ (P * g * P⁻¹))) w) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons X l ih =>
      intro hl w
      rw [List.foldr_cons, ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)),
        dRep_conj hJ (cj H) hc1 (hl X List.mem_cons_self), List.foldr_cons]
  have hnorm : ∀ l : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ m ∈ l, ∀ X ∈ m, X ∈ lieAt V τ) → ∀ w,
      (l.map fun m => ‖m.foldr (dRep fun g => cjOp (σ (P * g * P⁻¹))) w‖) =
        l.map fun m => ‖m.foldr (dRep fun g => σ (P * g * P⁻¹)) (cj H w)‖ :=
    fun l hl w => List.map_congr_left fun m hm => by rw [hfold m (hl m hm), (cj H).norm_map]
  choose ℓ' hℓ' hℓv using fun i => sobCont_conj hJ (cj H) hc1 (hℓ i)
  refine ⟨fun i => (cj H).symm (v i), fun i => smoothVec_conj hJ (cj H).symm hc2 (hv i), ℓ', hℓ',
    ⟨S0, C, hS0, fun i w hw => ?_, fun S' hS' => ?_, B, hB, fun g hg w hw => ?_⟩, fun g hg => ?_⟩
  · rw [hℓv, norm_star, hnorm S0 hS0]
    exact hC i _ (smoothVec_conj hJ (cj H) hc1 hw)
  · convert hsum S' hS' using 3 with i
    rw [hnorm S' hS']
    rfl
  · rw [hnorm S0 hS0, hnorm S0 hS0]
    exact hBb g hg _ (smoothVec_conj hJ (cj H) hc1 hw)
  · simp only [hℓv]
    exact (hhas g hg).star

end GlobalTheory.ListedTypeConj

noncomputable section

namespace GlobalTheory.ListedTypeConj

open Matrix Formalism.IndefR.Mult

variable {D : D7}

theorem isTypeAt_star_iff {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} :
    IsTypeAt θ V τ S (fun g => star (φ g)) ↔ IsTypeAt θ V τ (dualPar S) φ := by
  constructor
  · intro h
    simpa using isTypeAt_star h
  · intro h
    simpa [dualPar_dualPar] using isTypeAt_star h

theorem listed_iff_of_sameSp {θ : InfFam D} {V V' : HSp D} (h : GlobalTheory.GridJoin.SameSp V V') (e : GA D V' = GA D V)
    (P : D.what₂.Tau → SPar) (φ : GA D V → ℂ) :
    (IsAutFunSm θ V φ ∧ IsCuspFun V φ ∧ ∀ τ, IsTypeAt θ V τ (P τ) fun g => star (φ g)) ↔
      (IsAutFunSm θ V' (fun g => φ (cast e g)) ∧ IsCuspFun V' (fun g => φ (cast e g)) ∧
        ∀ τ, IsTypeAt θ V' τ (dualPar (P τ)) fun g => φ (cast e g)) := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  have hφ : (fun g => φ (cast e g)) = φ := funext fun g => rfl
  rw [hφ]
  simp only [isTypeAt_star_iff]
  refine and_congr ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
    fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩ (and_congr Iff.rfl Iff.rfl)

theorem grid_eq_num (D : D7) (τ : D.what₂.Tau) : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
  have hg := GlobalTheory.GridJoin.gap_eq_chiGap D
  have hc : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
    funext i
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [hg]
    rfl
  unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
  rw [hc, hg]
  rfl

theorem parV_eq (D : D7) (i j : ℕ) (τ : D.what₂.Tau) :
    GlobalTheory.Grid.parV D i j τ = dualPar (GlobalTheory.ChiGrid.parV D 1 i j τ) := by
  rw [GlobalTheory.Grid.parV, GlobalTheory.ChiGrid.parV, grid_eq_num]

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem nodeS_eq {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R} (hG : G.Is) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) :
    (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  cases i with
  | zero =>
    rw [GlobalTheory.Grid.parV_zero D hj]
    cases j with
    | zero => simp [GlobalTheory.Grid.GridPre.V, GlobalTheory.Grid.row0, GlobalTheory.Grid.nodeY]
    | succ j =>
      by_cases h : j + 1 < D.R.m
      · simp [GlobalTheory.Grid.GridPre.V, GlobalTheory.Grid.row0, GlobalTheory.Grid.nodeY, h, min_eq_left h.le]
      · have e : j + 1 = D.R.m := by omega
        simp only [GlobalTheory.Grid.GridPre.V, GlobalTheory.Grid.GridSp.vert, GlobalTheory.Grid.row0, if_neg h]
        rw [e]
  | succ i => exact (hG.spaces.vert i j (by omega) hj).par

end GlobalTheory.ListedTypeConj

namespace GlobalTheory.ListedTypeConj

open Formalism.IndefR.Mult

theorem isCuspListed_grid_iff : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (e : GA D (G.V i j).V = GA D (G'.V (.grid i j))) (φ : GA D (G'.V (.grid i j)) → ℂ),
      IsCuspListed W.θ (.grid i j) φ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (fun g => φ (cast e g)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F _ hc G' W hW G hG hM i j hi hj e φ
  have hθ : W.θ = R.θ := hW.θ
  have hS : (G.V i j).S = fun τ => dualPar (GlobalTheory.ChiGrid.Node.par D sc.cGap (.grid i j) τ) := by
    rw [nodeS_eq hG hi hj, hc]
    funext τ
    exact parV_eq D i j τ
  have hsp := (hM.1.vert i j hi hj).sp
  unfold IsCuspListed GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType
  simp only [GridData.IsListed]
  rw [hθ, hS]
  revert e
  generalize (G.V i j).V = V' at hsp ⊢
  intro e
  exact listed_iff_of_sameSp hsp e _ φ

end GlobalTheory.ListedTypeConj
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

theorem left_cast {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
      φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact hφ

theorem gen_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch =>
    (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
    ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  refine ⟨fun a ξ γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g, fun t y η => ?_⟩
  have hm := hS.core.models
  exact left_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
    (fun γ hγ g => congrArg η
      (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hm.HX t).2.1.le ⟨y, rfl⟩) γ hγ g))

end GlobalTheory.RowReal

end
end
