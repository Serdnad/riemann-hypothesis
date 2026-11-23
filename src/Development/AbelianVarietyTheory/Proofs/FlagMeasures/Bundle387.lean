module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle375
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle347
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarDensityConjUnitaryHermitianGroups
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle316
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle373
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
import Formalism.FormalDegreeBessel.FinalG
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.GrpCoord

theorem rat_iff (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G)
    {T₁ : D.host.E} (F₁ : LFlag (D.sp.Y 0) D.R.rS T₁) (g : ∀ p, Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ p a, g p a = (c.c p).e (scaled Z p (frame F₁) a)) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    γ ∈ NRat F₁ ↔ (c.e.symm.trans γ).trans c.e ∈ (placesOf Z).rat (fun p => (G.S p).Nof (g p)) := by
  have hgf : ∀ p, g p = fun a => (c.c p).e (scaled Z p (frame F₁) a) := fun p => funext (hg p)
  constructor
  · intro hγ p
    obtain ⟨h, hext, -, -, -, hNU⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ.1
    let k := ((c.c p).e.symm.trans h).trans (c.c p).e
    have hk : k ∈ (G.S p).Nof (g p) := by
      rw [hgf p]; exact (GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p) _ h).1 (hNU F₁ hγ)
    refine ⟨k, hk, ?_⟩
    · intro x
      obtain ⟨y, rfl⟩ := c.e.surjective x
      have h1 : (placesOf Z).bc p (c.e y) = (c.c p).e (baseChange₂ D p y) := (c.compat p y).symm
      have h2 : ((c.e.symm.trans γ).trans c.e) (c.e y) = c.e (γ y) := by simp
      rw [h2, h1, ← c.compat p (γ y), ← hext y]
      show (c.c p).e (h ((c.c p).e.symm ((c.c p).e (baseChange₂ D p y)))) = _
      rw [LinearEquiv.symm_apply_apply]
  · intro hγ
    have hne : Nonempty (PlF D) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField _)⟩⟩
    obtain ⟨p⟩ := hne
    obtain ⟨g₀, hg'N, hg'E⟩ := hγ p
    let g' : type_of% ((c.c p).e.symm.trans (c.c p).e) := g₀
    let h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p := ((c.c p).e.trans g').trans (c.c p).e.symm
    have hconj : ((c.c p).e.symm.trans h).trans (c.c p).e = g' := by
      ext x; simp [h]
    have hN : h ∈ NU (locH Z p) (scaled Z p (frame F₁)) := by
      rw [GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p), hconj, ← hgf p]; exact hg'N
    refine GlobalTheory.T.mem_rationalUnipotent_of_local_extension D Z p F₁ γ h ?_ hN
    intro y
    have h1 : (c.c p).e (baseChange₂ D p y) = (placesOf Z).bc p (c.e y) := c.compat p y
    have h3 : g₀ ((placesOf Z).bc p (c.e y)) = (placesOf Z).bc p (c.e (γ y)) :=
      (hg'E _).trans (by simp)
    show (c.c p).e.symm (g₀ ((c.c p).e (baseChange₂ D p y))) = baseChange₂ D p (γ y)
    rw [h1, h3, ← c.compat p (γ y), LinearEquiv.symm_apply_apply]

theorem grp_eq {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
    {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp σ n = (c.e.symm.trans (σ * n * σ⁻¹)).trans c.e := by
  ext x; simp [GCoord.grp]

theorem frame_mapLF (D : D7) {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) : frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF; rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast b => simp [frame, FlagG.fvec, mapFlag]

theorem grp_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (∀ n, n ∈ NRat (lf D (X.Fu u)) ↔ c.grp ρ n ∈ G.N) ∧ (∀ m, m ∈ NRat (lf D (X.Fu u')) ↔ c.grp (ρ * t₀.lin) m ∈ G.N') ∧ (∀ (σ n : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) Λ, c.lat (σ * n) Λ = (c.lat σ Λ).map (((c.grp σ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))) ∧ (∀ (σ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (x : G.GLV), ∃ n, c.grp σ n = x) ∧ (∀ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∀ (p : PlF D) g Λ, GlobalTheory.LocOver.Ext p σ g → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Y.M p) g (lattice₂ D Y.M p Λ))) ∧ ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ hAB G c t₀ ρ U U' hmv
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := hmv
  have hN : G.N = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F00) a))) := by
    unfold GFrames.N Frames.N
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f_eq, (hAB p).1.1]
  have hN' : G.N' = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F'0) a))) := by
    unfold GFrames.N' Frames.N'
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f'_eq, (hAB p).1.2.1]
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  refine ⟨fun n => ?_, fun m => ?_, fun σ n Λ => ?_, fun σ x => ?_, fun σ _ p g Λ hg => ?_, ?_⟩
  · refine (GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry D _ F00 ρ U hρ hU hF n).trans ?_
    rw [grp_eq, hN]
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · have hF2 : ∀ b, (ρ * t₀.lin) (frame (lf D (X.Fu u')) b) = ∑ a, U' a b • frame F'0 a := by
      intro b
      rw [← hF' b]
      show ρ (t₀.lin _) = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) b)
      rw [frame_mapLF D _ hlin]
    refine (GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry D _ F'0 (ρ * t₀.lin) U' (Subgroup.mul_mem _ hρ hlin) hU' hF2 m).trans ?_
    rw [grp_eq, hN']
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · unfold GCoord.lat
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp [GCoord.grp]
  · refine ⟨((σ.trans c.e).trans x).trans (σ.trans c.e).symm, ?_⟩
    ext y; simp [GCoord.grp]
  · exact GlobalTheory.T.completion_moved_lattice_eq_local_coordinates D _ F00 F'0 FP G c σ p g Λ hg
  · exact GlobalTheory.T.moves_to_determines_unipotent_factorisation D X Y u u' F00 F'0 t₀ ρ U U' ⟨hρ, hU, hU', hF, hF'⟩

end GlobalTheory.HL.GrpCoord
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T'), Submodule.IsLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → IsScalar Λ F F' F'' (n * m) := by
  first | exact @GlobalTheory.SnFam.CvScal.pair_scalar | exact GlobalTheory.SnFam.CvScal.pair_scalar | (intros; apply GlobalTheory.SnFam.CvScal.pair_scalar <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_cocycle_product_of_rational_unipotents : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T'), Submodule.IsFullLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → Th Λ F F' F'' (n * m) = Hp Λ F F' := by
  exact @GlobalTheory.DcosetCompl.th_eq_hp
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corank_one_scalar_pair_symmetric : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  first | exact @GlobalTheory.ScalSymm.scal_symm | exact GlobalTheory.ScalSymm.scal_symm | (intros; apply GlobalTheory.ScalSymm.scal_symm <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FdegDens

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  refine Finset.prod_pos fun i _ => ?_
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_pos (pow_pos h2π _) (by exact_mod_cast Nat.factorial_pos i)

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) : ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin n), p + q = n ∧
    (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  classical
  let A := {i : Fin n // ε i = true}
  let B := {i : Fin n // ¬ε i = true}
  let e : Fin (Fintype.card A) ⊕ Fin (Fintype.card B) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm).trans
      (Equiv.sumCompl fun i => ε i = true)
  refine ⟨Fintype.card A, Fintype.card B, e, ?_, fun i => ?_, fun j => ?_⟩
  · simpa using Fintype.card_congr e
  · exact ((Fintype.equivFin A).symm i).2
  · show ε (((Fintype.equivFin B).symm j : B) : Fin n) = false
    simpa using ((Fintype.equivFin B).symm j).2

theorem measurable_reindex {n p q : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n) :
    Measurable fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) := by
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  have hmat : Continuous (Formalism.BasicNotions.UpqT.mat : Formalism.BasicNotions.UpqT p q → _) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) :=
    hmat.matrix_reindex e e
  exact hc.measurable

theorem reindex_mem {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (g : Formalism.BasicNotions.UpqT p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
  obtain ⟨g0, hg0⟩ := g
  have hg : ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Formalism.UG.Jpq p q *
      (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hg0
  show (Matrix.reindex e e ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))ᴴ *
      Formalism.REAL.Jm ε * Matrix.reindex e e (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.REAL.Jm ε
  rw [GlobalTheory.OmegaFrobenius.jm_eq h1 h2, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem hasDens_unique {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c c' : ℝ≥0∞}
    (h : HasDens S μ c) (h' : HasDens S μ c') : c = c' := by
  unfold HasDens at h h'
  exact tendsto_nhds_unique h h'

theorem hasDens_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c : ℝ≥0∞}
    (h : HasDens S μ c) (t : NNReal) : HasDens S (t • μ) (t * c) := by
  unfold HasDens at h ⊢
  refine (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top) (a := (t : ℝ≥0∞))).congr fun ρ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem cd_dens {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n) (hpq : p + q = n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (cd : Formalism.BasicNotions.CDHaar) :
    PI.IsHaarOnM (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧
    HasDens (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)))
      (ENNReal.ofReal (volUn n)⁻¹) := by
  subst hpq
  obtain ⟨c0, -, -, hc1, hc2⟩ := cd.trick p q
  have hK := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) (fun _ => true) (p + q) 0 (Equiv.sumEmpty _ _) (fun _ => rfl)
    (fun j => j.elim0) (cd.cd (p + q) 0) c0 (cd.haar _ _) hc2
  have hJ : Formalism.REAL.Jm (fun _ : Fin (p + q) => true) = 1 := by
    unfold Formalism.REAL.Jm
    simp
  rw [hJ] at hK
  have hprob : ((cd.cd (p + q) 0).map fun g => Matrix.of.symm (Matrix.reindex
      (Equiv.sumEmpty (Fin (p + q)) (Fin 0)) (Equiv.sumEmpty (Fin (p + q)) (Fin 0))
      (Formalism.BasicNotions.UpqT.mat g))) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_reindex _) MeasurableSet.univ, Set.preimage_univ]
    haveI := cd.prob (p + q)
    exact measure_univ
  have hc0 : c0 = ENNReal.ofReal (volUn (p + q))⁻¹ :=
    hasDens_unique hK.2 (GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability (p + q) _ hK.1 hprob)
  have hM := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) ε p q e h1 h2 (cd.cd p q) c0 (cd.haar p q) hc1
  rw [hc0] at hM
  exact hM

theorem umat_emb {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n) := by
  have h : Topology.IsClosedEmbedding (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem conj_emb {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    MeasurableEmbedding fun x : PI.MtM n => (Matrix.of.symm (P⁻¹ * Matrix.of x * P) : PI.MtM n) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hm : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      Measurable fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) := by
    intro A B
    have hx : Continuous fun x : PI.MtM n => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    have hc : Continuous fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) :=
      (continuous_const.matrix_mul hx).matrix_mul continuous_const
    exact hc.measurable
  let φ : PI.MtM n ≃ PI.MtM n :=
    { toFun := fun x => Matrix.of.symm (P⁻¹ * Matrix.of x * P)
      invFun := fun y => Matrix.of.symm (P * Matrix.of y * P⁻¹)
      left_inv := fun x => by
        show Matrix.of.symm (P * (P⁻¹ * Matrix.of x * P) * P⁻¹) = x
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, ← Matrix.mul_assoc P P⁻¹,
          Matrix.mul_nonsing_inv_cancel_left _ _ hu]
      right_inv := fun y => by
        show Matrix.of.symm (P⁻¹ * (P * Matrix.of y * P⁻¹) * P) = y
        simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] }
  exact (MeasurableEquiv.mk φ (hm _ _) (hm _ _)).measurableEmbedding

theorem schur_of_dens : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  intro k r H _ _ _ σ ε cd sc P d c μG hcomp hP hF hc hμG hdG
  obtain ⟨p, q, e, hpq, h1, h2⟩ := exists_sort ε
  have hU := umat_emb ε
  have hC := conj_emb P hP.1

  have hν : ((sc : ℝ≥0∞) • Formalism.REAL.muG ε).map (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM (2 * r + k + 1))) =
      (cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
    ext B hB
    rw [Measure.map_apply hU.measurable hB, Measure.map_apply (measurable_reindex e) hB,
      hcomp p q e h1 h2 _ (hU.measurable hB)]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, hag⟩
      show Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) ∈ B
      rw [← hag]
      exact ha
    · intro hg
      have hmem : Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) ∈ Set.range
          (fun a : Formalism.REAL.UJ ε => ((a : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
            Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
        rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).2]
        exact reindex_mem ε e h1 h2 g
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_, ha⟩
      show Matrix.of.symm (umat a) ∈ B
      rw [show umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) from ha]
      exact hg
  have hcd := cd_dens ε e hpq h1 h2 cd
  rw [← hν] at hcd
  have hHk := Formalism.QuantumDeterminants.hpkFacts k r
  have hD := GlobalTheory.T.haar_density_conj_unitaryHermitianGroups (2 * r + k + 1) (Formalism.QuantumDeterminants.Hpk k r) (Formalism.REAL.Jm ε) P hHk.1 hHk.2.1
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) hP.1 hP.2 _ _ hcd.1 hcd.2
  obtain ⟨t, -, httop, hμt⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _
    (GlobalTheory.AdDens.isMatGroup_UH _ hHk.2.1) hD.1).1 μG hμG
  have hdt : HasDens (GG k r) μG (t * ENNReal.ofReal (volUn (2 * r + k + 1))⁻¹) := by
    have h := hasDens_smul hD.2 t.toNNReal
    rwa [ENNReal.smul_def, ENNReal.coe_toNNReal httop.ne, ← hμt] at h
  have hV := volUn_pos (2 * r + k + 1)
  have htr : t.toReal = c * volUn (2 * r + k + 1) := by
    have h := congrArg ENNReal.toReal (hasDens_unique hdG hdt)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal (inv_nonneg.mpr hV.le)] at h
    rw [h, mul_assoc, inv_mul_cancel₀ hV.ne', mul_one]
  rw [Measure.map_map hC.measurable hU.measurable] at hμt
  have hemb := hC.comp hU
  obtain ⟨hd, hFd⟩ := hF
  refine ⟨div_pos hd (mul_pos hc hV), fun v w v' w' => ?_⟩
  obtain ⟨hI, hE⟩ := hFd v w v' w'
  rw [hμt]
  refine ⟨Integrable.smul_measure ?_ httop.ne, ?_⟩
  · rw [hemb.integrable_map_iff]
    exact hI
  rw [integral_smul_measure, hemb.integral_map]
  refine (congrArg (fun z : ℂ => t.toReal • z) hE).trans ?_
  rw [htr, Complex.real_smul]
  push_cast
  rw [div_div_eq_mul_div]
  ring

end GlobalTheory.FdegDens
end
