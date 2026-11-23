module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle203
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle469
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle421
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle482
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommonVac

theorem latV_eq_of_moves {D : D7} {S : HSp D} {g : GA D S} {Λ M N : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : GlobalTheory.FinPl.Moves S g Λ M P) (hN : GlobalTheory.FinPl.Moves S g Λ N P) :
    GlobalTheory.FinPl.latV S M P = GlobalTheory.FinPl.latV S N P := by
  have h1 : GlobalTheory.FinPl.Moves S (g * g⁻¹) M N P := GlobalTheory.StMoves.moves_mul (GlobalTheory.StMoves.moves_inv hM) hN
  rw [mul_inv_cancel] at h1
  have e1 : ∀ y : Fin S.rank → AE D, mt S (1 : GA D S) *ᵥ y = y := fun y => by
    rw [show mt S (1 : GA D S) = 1 from rfl, Matrix.one_mulVec]
  ext y
  constructor
  · intro hy
    have := (h1 y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    rwa [e1] at this
  · intro hy
    have h2 := h1 y (fun i => by
      have := GlobalTheory.FinPl.FrameLat.latV_supp hy i
      exact this)
    rw [e1] at h2
    exact h2.2 hy

end GlobalTheory.CommonVac

namespace GlobalTheory.CommonVac

theorem exists_common_vacua : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (pk W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, VTie (⟨mkGeo m b, j, row, col⟩ : FamCh W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  intro D L hT Gi Gl Kc Yd cX ex W u hpk a y m b v hc hτ hNT hgP hTy hb hbT hLT hmT hN hvb hvbT htP

  have hQ : ∀ p ∈ v.gP, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) := by
    intro p hp
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact GlobalTheory.T.type_places_split_idempotents W hpk hTy PP hPP

  have hY : ∀ j, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, j + 1 < D.R.m →
      GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True)
        (comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)))) ∧
      comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (b j, b (j + 1))
        (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1)) ≠ 0 := by
    intro j
    by_cases hj : j + 1 < D.R.m
    · obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk j (by omega) (b j)
      obtain ⟨M', hM', hM'v⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk (j + 1) hj (b (j + 1))
      obtain ⟨hvac, hnz⟩ := GlobalTheory.T.self_dual_lattices_consecutive_step W hpk j hj (b j) (b (j + 1)) (hb j) (hb (j + 1)) M M' hM hM' hMv hM'v
      obtain ⟨o, ho, hoV⟩ := GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective D (pk W).ψ hc.std (Yc D j) (Yc D (j + 1)) M (v.N j) M' (v.N (j + 1)) v.gP hM
        (hN j (by omega)).1 hM' (hN (j + 1) hj).1 hQ (fun p hp =>
          ⟨latV_eq_of_moves (hMv (· = p)) ((hN j (by omega)).2 (· = p) (fun p' hp' => hp' ▸ hp)),
            latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp))⟩)
      have hv1 := hvac 1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      simp only [one_mul] at hv1
      exact ⟨o, fun _ => ⟨ho, fun P x hx x' hx' => (hoV _ (hvac P x hx x' hx')).1, (hoV _ hv1).2 hnz⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose O hO using hY

  have hTs : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ o : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True)
        (comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)))) ∧
      comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1)) ≠ 0 := by
    intro j h
    have hj : j + 1 < D.R.m := by omega
    obtain ⟨M', hM', hM'v⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk (j + 1) hj (b (j + 1))
    obtain ⟨hvac, hnz⟩ := GlobalTheory.T.self_dual_lattices_top_step W hpk j h (b (j + 1)) a.bT (hb (j + 1)) hbT M' a.LT hM' hLT hM'v hmT
    have hNT' : IsSelfDualC D.sp.X' v.NT := hNT ▸ hLT
    obtain ⟨o, ho, hoV⟩ := GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective D (pk W).ψ hc.std (Yc D (j + 1)) D.sp.X' M' (v.N (j + 1)) a.LT v.NT v.gP hM'
      (hN (j + 1) hj).1 hLT hNT' hQ (fun p hp =>
        ⟨latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp)), by rw [hNT]⟩)
    exact ⟨o, ho, fun P => (hoV _ (hvac P)).1, (hoV _ (hvac 1)).2 hnz⟩
  choose OT hOT using hTs
  refine ⟨fun j P x x' => comb (pk W).ψ _ _ (O j) ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)),
    fun j h P => comb (pk W).ψ _ _ (OT j h) (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)),
    fun j hj P x hx x' hx' => (hO j hj).2.1 P x hx x' hx', fun j h P => (hOT j h).2.1 P, ?_⟩
  intro j' row col
  exact {
    b := fun j => by rw [hvb]
    bT := ⟨hvbT, hNT⟩
    gP := hgP
    tP := htP
    moves := fun j hj P hP => (hN j hj).2 P hP
    movesT := hmT
    Ψ := fun j hj => ⟨O j, (hO j hj).1, fun P x x' => rfl⟩
    ΨT := fun j h => ⟨OT j h, (hOT j h).1, fun P => rfl⟩
    nz := ⟨fun j hj => ⟨1, by simpa only [one_mul] using (hO j hj).2.2⟩, fun j h => ⟨1, (hOT j h).2.2⟩⟩ }

end GlobalTheory.CommonVac
end

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.DoublingTheta

section Matrices

variable (R : Type) [CommRing R] (m n : ℕ)

def inL : Matrix (Fin (m + n)) (Fin m) R :=
  (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin n) (Fin m) R)).submatrix finSumFinEquiv.symm id

def inR : Matrix (Fin (m + n)) (Fin n) R :=
  (Matrix.fromRows (0 : Matrix (Fin m) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix finSumFinEquiv.symm id

variable {R m n}

theorem inL_map {R' : Type} [CommRing R'] (f : R →+* R') : (inL R m n).map f = inL R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.one_apply]
    split_ifs <;> simp
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, map_zero]

theorem inR_map {R' : Type} [CommRing R'] (f : R →+* R') : (inR R m n).map f = inR R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.zero_apply, map_zero]
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.one_apply]
    split_ifs <;> simp

theorem mul_inL {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inL R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inL, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem mul_inR {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inR R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inR, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem blkMat_inL (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inL R m n = inL R m n * a := by
  rw [blkMat, inL, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

theorem blkMat_inR (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inR R m n = inR R m n * b := by
  rw [blkMat, inR, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

variable [StarRing R]

theorem inL_inL : (inL R m n)ᴴ * inL R m n = 1 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inL, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inR : (inR R m n)ᴴ * inR R m n = 1 := by
  rw [mul_inR]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inL : (inR R m n)ᴴ * inL R m n = 0 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR]

end Matrices

variable {D : D7}

def sumDec (V W : HSp D) : GlobalTheory.MixModel.OrthDec (sumSp V W) V W where
  iA := inL D.host.E V.rank W.rank
  iB := inR D.host.E V.rank W.rank
  isoA := by
    change (inL D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = V.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inL_inL, Matrix.one_mul]
  isoB := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inR D.host.E V.rank W.rank = W.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inR, ← Matrix.mul_assoc, inR_inR, Matrix.one_mul]
  orth := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = 0
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inR_inL, Matrix.zero_mul]
  rank_add := rfl

theorem sumDec_jA (V W : HSp D) : (sumDec V W).jA = inL (AE D) V.rank W.rank := inL_map (incA D)

theorem sumDec_jB (V W : HSp D) : (sumDec V W).jB = inR (AE D) V.rank W.rank := inR_map (incA D)

theorem sumDec_emb (V W : HSp D) (g : GA D V) (g' : GA D W) : (sumDec V W).emb (g, g') = ioSum V W (g, g') := by
  refine GlobalTheory.MixModel.mt_injective _ ?_
  have hA : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jA = HMul.hMul (sumDec V W).jA (mt V g) := by
    rw [sumDec_jA]; exact blkMat_inL (mt V g) (mt W g')
  have hB : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jB = HMul.hMul (sumDec V W).jB (mt W g') := by
    rw [sumDec_jB]; exact blkMat_inR (mt V g) (mt W g')
  rw [GlobalTheory.MixModel.OrthDec.mt_emb, ← hA, ← hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
    GlobalTheory.MixModel.OrthDec.sum_eq_one, Matrix.mul_one]

theorem boxS_apply (A B : HSp D) (f : WO A B → ℂ) (f' : WO (negSp A) B → ℂ) (x : WO (dblSp A) B) :
    (sumDec A (negSp A)).boxS B f f' x = f (resL A B x) * f' (resR A B x) := by
  rw [GlobalTheory.MixModel.OrthDec.boxS, GlobalTheory.MixModel.OrthDec.resS_apply, sumDec_jA, sumDec_jB]
  exact congrArg₂ (· * ·) (congrArg f (mul_inL x)) (congrArg f' (mul_inR x))

theorem thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ThetaClause ψ A B χB om omh := by
  intro D ψ A B χA χB om omh hom homh f₁ f₂ h₁ h₂
  refine ⟨GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hom.std f₁ f₂ h₁ h₂, fun g₁ g₂ h => ?_⟩
  obtain ⟨hθ, om', hom', hact⟩ := GlobalTheory.T.exists_conjugate_weilDatum_hermitianSpaceNeg D ψ A B χA χB om hom
  have hT := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hom.std (sumSp A (negSp A)) A (negSp A) (sumDec A (negSp A)) B
  have hh : IsWeilDatumO ψ (sumSp A (negSp A)) B (χA * χA⁻¹) χB omh := by rw [mul_inv_cancel]; exact homh
  have key := hT.om_box χA χA⁻¹ χB omh om om' hh hom hom' g₁ ((negEquiv A).symm g₂) h f₁ _ h₁ (hθ f₂ h₂)
  rw [hact _ h f₂ h₂, sumDec_emb, io_eq_ioSum, MulEquiv.apply_symm_apply] at key
  have e : (sumDec A (negSp A)).boxS B f₁ (fun x => conj (f₂ (-x))) = delta A B f₁ f₂ :=
    funext fun x => boxS_apply A B _ _ x
  have main : omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
      (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) := by
    rw [← e]
    refine key.trans (funext fun x => (boxS_apply A B _ _ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨main, ?_⟩
  have zL : resL A B 0 = 0 := rfl
  have zR : resR A B 0 = 0 := rfl
  rw [thetaKO, main]
  simp only [thetaKO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul, zL, zR, neg_zero]
  ring

end GlobalTheory.DoublingTheta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.Rows

open GlobalTheory.FinPl

section Gen

variable {D : D7}

theorem idAt_le {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p) {z : AE D} (hz : z ∈ idAt D P) : z ∈ idAt D Q := by
  simp only [idAt, Submodule.mem_inf, idOff, Submodule.mem_iInf] at hz ⊢
  exact ⟨hz.1, fun w => hz.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem moves_mono {V : HSp D} {g : GA D V} {L : GlobalTheory.FinPl.Lat V} {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p)
    (H : GlobalTheory.FinPl.Moves V g L L Q) : GlobalTheory.FinPl.Moves V g L L P := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D Q := fun i => idAt_le h (hy i)
  rw [MovesSplit.mem_latV_iff_all V L P hy, MovesSplit.mem_latV_iff_all V L P (KOpen.supp_mulVec V P g hy),
    ← MovesSplit.mem_latV_iff_all V L Q hy', ← MovesSplit.mem_latV_iff_all V L Q (KOpen.supp_mulVec V Q g hy')]
  exact H y hy'

theorem st_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : GlobalTheory.FinPl.Lat V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ)
    (g : GA D V) : finE V g ∈ St β ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves V g Λ Λ (· = v) := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg D.host.E Λ
  rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
  exact forall_congr' fun v => (GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v _).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem moves_of_stab (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (t x : GA D V)
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (bas : GL Y k)
    (σ : Fin V.rank ≃ Y) (hM : MovedTo (ofSplit q) V t β ((F.β * bas.val).submatrix id σ))
    (m : GL Y k) (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hs : m ∈ stabLat bas) :
    GlobalTheory.FinPl.Moves V (t⁻¹ * x * t) Λ Λ (· = q.v) := by
  have h1 : (mt V t⁻¹).map q.pr * (mt V t).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', inv_mul_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (mt V t).map q.pr * (mt V t⁻¹).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', mul_inv_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  let F' : GlobalTheory.LocMod.Frame k V.rank Y := ⟨(mt V t⁻¹).map q.pr * F.β, F.γ * (mt V t).map q.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((mt V t).map q.pr), h2, Matrix.one_mul, F.γβ]⟩
  have hM' : MovedTo (ofSplit q) V 1 β ((F'.β * bas.val).submatrix id σ) := by
    intro b hb
    have h3 : (mt V t).map q.pr * b.map q.pr = (F.β * bas.val).submatrix id σ := by
      rw [← Matrix.map_mul]; exact hM b hb
    have h4 : (F'.β * bas.val).submatrix id σ = (mt V t⁻¹).map q.pr * (F.β * bas.val).submatrix id σ := by
      show ((mt V t⁻¹).map q.pr * F.β * bas.val).submatrix id σ = _
      rw [Matrix.mul_assoc]
      rfl
    rw [h4, ← h3, ← Matrix.mul_assoc, h1, Matrix.one_mul, LevRed.mt_one', Matrix.one_mul]
    rfl
  have h0 : GlobalTheory.FinPl.Moves V 1 Λ Λ (· = q.v) := fun y _ => by rw [LevRed.mt_one', Matrix.one_mulVec]
  have hl := LevMoves.isLat_moved q hq V Λ Λ β hβ 1 h0 F' bas σ hM'
  obtain ⟨gl, g1, g2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V _ F'.β F'.γ F'.βγ F'.γβ
  refine (GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes D k q V _ ⟨F'.β, F'.γ, F'.βγ, F'.γβ, gl, g1, g2⟩ Λ _ hΛ hl _).2 ?_
  have h5 : (mt V (t⁻¹ * x * t)).map q.pr = F'.β * m.val * F'.γ := by
    rw [LevRed.mt_mul', LevRed.mt_mul', Matrix.map_mul, Matrix.map_mul, hm]
    simp only [F', Matrix.mul_assoc]
  have h6 := (eq_coordHom_iff V q.pr F'.β F'.γ F'.βγ F'.γβ _ _).1 h5
  exact h6 ▸ LevMoves.smul_latOf hs

end Gen

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem red_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (β : GL (Fin V.rank) (Lev.EAf D)) (t x : GA D V) {s : ℕ} (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k)
    (F : GlobalTheory.LocMod.Frame k V.rank (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)))
    (e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) 0 ≃ Fin V.rank) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (hM : MovedTo (ofSplit q) V t β ((F.β * ((S.T (Fin D.R.t)).bas 0 (s + 1) (Nat.zero_add _)).val).submatrix id
      fun a => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _) (e.symm a)))
    (hr : D.R.r ≤ V.rank) (m : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)) k)
    (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hst : finE V (t⁻¹ * x * t) ∈ St β) :
    (∃ z : S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin (s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ c : 𝓞 D.host.E,
        Ideal.Quotient.mk PP.asIdeal c = (upperLeftBlock hr (redFn β PP (finE V (t⁻¹ * x * t)))).val a' b' →
        valuation k ((z : GL (Fin D.R.k ⊕ Fin (s + 1)) k).val a b - (ofSplit q).pr (c : D.host.E)) < 1) ↔
      m ∈ ((S.T (Fin D.R.t)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨w, hw⟩ := hst
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D _ q PP hq
  have h1 := RedLev.mul_moved (ofSplit q) hπ _ _ _ _ w hw hM
  have h3 := RedLev.conj_eq F ((S.T (Fin D.R.t)).bas 0 _ (Nat.zero_add _)) m
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) _
    ((congrArg (· * _) hm).symm.trans h1)
  have hk : D.R.k + (s + 1) = D.R.r := by
    unfold Ranks.r
    omega
  have hlt : ∀ i : Fin V.rank, i.val < D.R.r := fun i => by
    obtain ⟨i, rfl⟩ := e.surjective i
    rw [he, ← hk]
    rcases i with (i | i) | i
    · exact lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left i.2 _
    · exact i.1.elim0
  have htri : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) w ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) :=
    Formalism.L2.DIV.mem_blockTri.2 fun i j h => by simp [Formalism.L2.DIV.blk2, hlt] at h
  have hpos : ∀ i, (e (.inl i)).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i := fun i => by
    rw [he]
    rcases i with i | i <;> rfl
  let T := typeFrame S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _))
  let g := (reGL (ixZero _ (Fin D.R.t))).symm (T.conj.symm m)
  have hg : ∀ i j, g.val i j = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w.val (e (.inl i)) (e (.inl j))) :=
    fun i j => by
      have := congrFun (congrFun h3 (e (.inl i))) (e (.inl j))
      simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, Matrix.map_apply] at this
      exact this
  have h6 : ∀ i j (c : 𝓞 D.host.E),
      Ideal.Quotient.mk PP.asIdeal c = Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))) →
      valuation k (g.val i j - (ofSplit q).pr (c : D.host.E)) < 1 := fun i j c hc => by
    have h5 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E c) =
        (ofSplit q).pr (c : D.host.E) := hπ (incA D (c : D.host.E))
    rw [hg, ← h5, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, hc, sub_self]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨g', hg', e'⟩ := S.P.exists_of_congr z.2 (M := g.val) fun i j => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))))
      have h4 := hz i j ⟨_, hlt (e (.inl i))⟩ ⟨_, hlt (e (.inl j))⟩ (hpos i) (hpos j) c
        (by rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri]; exact hc)
      have := Valuation.map_sub_lt _ (h6 i j c hc) h4
      rwa [sub_sub_sub_cancel_right] at this
    obtain rfl : g' = g := Units.ext e'
    exact hg'
  · intro hJ
    refine ⟨⟨g, hJ⟩, fun i j a' b' ha hb c hc => h6 i j c ?_⟩
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri, Matrix.submatrix_apply] at hc
    have ea : Fin.castLE hr a' = e (.inl i) := Fin.ext (ha.trans (hpos i).symm)
    have eb : Fin.castLE hr b' = e (.inl j) := Fin.ext (hb.trans (hpos j).symm)
    rw [ea, eb] at hc
    exact hc

end Loc

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}


end Real

end GlobalTheory.FamTrace.Rows

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_each_place : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (Q : Finset (GlobalTheory.FinPl.Pl D)), (∀ v ∈ Q, GlobalTheory.FinPl.Moves S g L M (· = v)) → GlobalTheory.FinPl.Moves S g L M (· ∈ Q) := by
  first | exact @GlobalTheory.FinPl.MovesPl.moves_of_places | exact GlobalTheory.FinPl.MovesPl.moves_of_places | (intros; apply GlobalTheory.FinPl.MovesPl.moves_of_places <;> assumption)
end
