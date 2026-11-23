module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bridge
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle001
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.XFacts
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.WeylComplementDetCoeffSpan
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions.G.LatticeSystems

section Cast

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (N : ℕ) (hm : P.m + 1 = N)

def emC (b : GlobalTheory P) (v : Fin N × Fin N) : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) :=
  emP P b (Fin.cast hm.symm v.1, Fin.cast hm.symm v.2)

def gamC (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin N) (Fin N) Kf :=
  (gam P g b).submatrix (Fin.cast hm.symm) (Fin.cast hm.symm)

def nuC (b : GlobalTheory P) : Fin N → ℕ := fun t => nuB P b (Fin.cast hm.symm t)

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)

include hg in
theorem htupW_leC (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf,
      (∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) →
        (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  subst hm
  exact htupW_le P g hg hinj T hT

include hg in
theorem mem_htupWC (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) :
    (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈
      P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  subst hm
  exact mem_htupW P g hg hinj F hF

end Cast

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem branching_source_identity : XBrS := by
  intro p _ X hinj j L g hg hL T hT
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC X.G.P _ (rankJ X 0) g hg hinj T hT
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj T hT

theorem branching_target_identity : XBrT := by
  intro p _ X hinj j L g hg hL F hF
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC X.G.P _ (rankJ X 0) g hg hinj F hF
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj F hF

end Formalism.L2.PairingIndexBounds.Ent
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem evX_gX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) (a : Fin n) (i : ℕ) : evX x (gX K n a i) = C (x (i, a)) := by
  unfold evX gX
  rw [coe_eval₂Hom, eval₂_X]

theorem evX_gY {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : (gY K n).map (evX x) = yV K n := by
  ext a t
  rw [Matrix.map_apply]
  unfold evX gY yV
  rw [coe_eval₂Hom, eval₂_C]
  rfl

theorem evX_HgX (j : ℕ) (b : BX X) (x : ℕ × Fin (NJ X j) → X.G.Kf) :
    evX x (HgX X X.G.Kf j b) = srcN X j b fun a i => x (i, a) := by
  unfold HgX srcN
  split_ifs with ho
  · rw [map_hvO, evX_gY]
    simp only [evX_gX]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, evX_gY, map_pow, RingHom.map_det]
    simp only [evX_gX]
    congr 3
    ext a i
    simp [evX_gX]

theorem HgX_map (O K : Type) [CommRing O] [CommRing K] (f : O →+* K) (j : ℕ) (b : BX X) :
    map (map f) (HgX X O j b) = HgX X K j b := by
  have hx : ∀ a i, (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) (gX O (NJ X j) a i) = gX K (NJ X j) a i := by
    intro a i
    unfold gX
    rw [map_X]
  have hy : (gY O (NJ X j)).map (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) = gY K (NJ X j) := by
    ext a t
    rw [Matrix.map_apply]
    unfold gY
    rw [map_C, map_X]
  unfold HgX
  split_ifs with ho
  · rw [map_hvO, hy]
    simp only [hx]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, hy]
    simp only [hx]
    congr 3
    ext a i
    simp [hx]

theorem hQX (hS : XShape) (j : ℕ) (b : BX X) :
    (weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuM X j b)).map (toK X.G.O X.G.Kf) ≤
      Submodule.span X.G.O (Set.range fun m => AddMonoidAlgebra.coeff (HgX X X.G.Kf j b) m) := by
  obtain ⟨h1, -, hanti, hle, -, -, -, -, -, -⟩ := hS p X j b
  rw [h1]
  have key : weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuS X j b) ≤
      Submodule.span X.G.O (Set.range fun m => AddMonoidAlgebra.coeff (HgX X X.G.O j b) m) := by
    by_cases ho : IsOddPos b.2
    · have hn : nuS X j b = fun t => cX X j b - muX X j (NJ X j) b t.rev := if_pos ho
      unfold HgX
      rw [if_pos ho, hn]
      exact weyl_complement_det_coeff_span X.G.O (NJ X j) _ (hanti _) _ (hle _)
    · have hn : nuS X j b = fun t => muX X j (NJ X j) b t - eX X j b := if_neg ho
      unfold HgX
      rw [if_neg ho]
      refine weyl_lattice_det_coeff_span X.G.O (NJ X j) (nuS X j b) ?_ _ _ ?_
      · rw [hn]
        exact fun a c hac => Nat.sub_le_sub_right (hanti _ hac) _
      · rw [hn]
        exact fun t => (Nat.sub_le _ _).trans (hle _ t)
  refine (Submodule.map_mono key).trans ?_
  rw [Submodule.map_span, ← Set.range_comp]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨m, ?_⟩
  show _ = map (algebraMap X.G.O X.G.Kf) (AddMonoidAlgebra.coeff (HgX X X.G.O j b) m)
  rw [← HgX_map X X.G.O X.G.Kf (algebraMap X.G.O X.G.Kf) j b]
  exact coeff_map _ _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end
