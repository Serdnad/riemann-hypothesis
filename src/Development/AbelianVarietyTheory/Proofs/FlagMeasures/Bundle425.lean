module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle407
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle418
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle371
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.Bundle001
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowTermReal

variable {D : D7}

theorem gmap_one' (L : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) L = L := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul' (a b : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {i j : ℕ} (h : i ≤ j) :
    Xflag F i ≤ Xflag F j :=
  Submodule.span_mono (Set.image_mono fun a (ha : a.1 < i) => show a.1 < j by omega)

theorem adapt_map_xflag {T : D.host.E} {g : GV D} {A B : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g A B)
    (j : ℕ) {x : (VS D).V} (hx : x ∈ Xflag A j) : g x ∈ Xflag B j := by
  change x ∈ Submodule.span D.host.E (A.fl.e '' {i | i.1 < j}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    have ha' : a.1 < j := ha
    have h1 := hg.2 a.castSucc
    have e1 : frame A a.castSucc = A.fl.e a := by simp [frame, FlagG.fvec]
    have e2 : frame B a.castSucc = B.fl.e a := by simp [frame, FlagG.fvec]
    rw [e1, e2, Fin.val_castSucc] at h1
    have h2 : B.fl.e a ∈ Xflag B j := Submodule.subset_span ⟨a, ha', rfl⟩
    have h3 := xflag_mono B (le_of_lt ha') h1
    simpa using add_mem h3 h2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem adapt_mul {T : D.host.E} {g h : GV D} {A B C : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g B C)
    (hh : Adapt h A B) : Adapt (g * h) A C := by
  refine ⟨mul_mem hg.1 hh.1, fun a => ?_⟩
  have e : (g * h) (frame A a) - frame C a =
      g (h (frame A a) - frame B a) + (g (frame B a) - frame C a) := by
    simp only [mul_apply_eq_comp, map_sub]; abel
  rw [e]
  exact add_mem (adapt_map_xflag hg _ (hh.2 a)) (hg.2 a)

theorem adapt_of_nlam {T : D.host.E} {Λ : LV D} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D}
    (hn : n ∈ NLam Λ F) : Adapt n F F := by
  refine ⟨hn.1.1, fun a => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) = F.fl.z := by simp [frame, FlagG.fvec]
    rw [hz, Fin.val_last]
    have hzo : F.fl.z ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      change x ∈ Submodule.span D.host.E (Set.range F.fl.e) at hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
      | smul c x _ hx => simp [hx]
    have hX : Xsp F ≤ Xflag F D.R.rS :=
      Submodule.span_mono fun _ ⟨i, h⟩ => ⟨i, i.2, h⟩
    exact hX (hn.2.2 _ hzo)
  · have hi : frame F i.castSucc = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [hi, Fin.val_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem frame_mapLF' {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {g : GV D}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (a : Fin (D.R.rS + 1)) : frame (mapLF g F) a = g (frame F a) := by
  simp only [mapLF, dite_eq_left hg, frame, FlagG.fvec, mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp

end GlobalTheory.RowTermReal

namespace GlobalTheory.RowTermReal

theorem rowLat_first {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u)) F ∧ IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  GlobalTheory.T.rowLattice_of_locally_standard_frame D (Tu D u) (D.mem u).A.T_prime.ne_zero (X.Fu u) F Z
    (fun p => (FP p).A) (fun p => (hB p).1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L, (y p).hL, hlat.symm.trans hn.2.2⟩)

theorem rowLat_second {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u')) F' ∧ IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  GlobalTheory.T.rowLattice_of_locally_standard_frame D (Tu D u') (D.mem u').A.T_prime.ne_zero (X.Fu u') F' Z
    (fun p => (FP p).B) (fun p => (hB p).2.1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L', (y p).hL', hlat.symm.trans hn.2.2⟩)

theorem exists_term_of_locOver : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL
  obtain ⟨g0, hg0, hrow0⟩ := rowLat_first X F F' Z FP hB Λ y hL
  obtain ⟨g0', hg0', hrow0'⟩ := rowLat_second X F F' Z FP hB Λ y hL
  obtain ⟨Λ₁, hΛ₁, σ, hσ, hσΛ⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u u).1 _ hrow0
  obtain ⟨Λ₁', hΛ₁', σ', hσ', hσΛ'⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u' u').1 _ hrow0'
  have hg : Adapt (g0 * σ) (lf D (X.Fu u)) F := adapt_mul hg0 hσ
  have hg' : Adapt (g0' * σ') (lf D (X.Fu u')) F' := adapt_mul hg0' hσ'
  have hgΛ : Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ = Λ₁ := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ, ← gmap_mul', inv_mul_cancel, gmap_one']
  have hgΛ' : Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ = Λ₁' := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
  have hrow : IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ) := hgΛ ▸ (Y.rowsOK u).1 Λ₁ hΛ₁
  have hrow' : IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ) := hgΛ' ▸ (Y.rowsOK u').1 Λ₁' hΛ₁'
  have hPD := GlobalTheory.T.gluedTerm_frame_admissibleIntegral D X Y u u' F F' w hw hG Z FP hB hR Λ y hL _ _ hg hg' hrow hrow'
  rw [hgΛ] at hPD
  set g := g0 * σ with hgdef
  set g' := g0' * σ' with hg'def
  have hγ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg.1) hg'.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') Λ₁' = Λ₁ := by
    rw [← hgΛ, ← hgΛ', gmap_mul', ← gmap_mul' g' g'⁻¹, mul_inv_cancel, gmap_one']
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X (g⁻¹ * g') hγ
  let p : GCar X u u' (X.Fu u) (X.Fu u') Λ₁ Λ₁' := ⟨(x, g⁻¹ * g'), hx, hγ, hγΛ, hPD⟩
  let t : TauC Y u u' := ⟨Λ₁, hΛ₁, Λ₁', hΛ₁', Quot.mk _ p⟩
  refine ⟨t, ?_⟩
  obtain ⟨n, hn, n', hn', hrel⟩ := Formalism.L2.SG.Pf.SatGramRep.grel_rep t p rfl
  have hlin : t.lin = n⁻¹ * (g⁻¹ * g') * n'⁻¹ := by
    have h : g⁻¹ * g' = n * t.lin * n' := hrel
    rw [h]; group
  refine ⟨g * n, adapt_mul hg (adapt_of_nlam hn), ?_, ?_⟩
  · have hA : Adapt (g' * n'⁻¹) (lf D (X.Fu u')) F' :=
      adapt_mul hg' (adapt_of_nlam (Formalism.L2.SG.Pf.nlam_inv hn'))
    have htl : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
    have e : g * n * t.lin = g' * n'⁻¹ := by rw [hlin]; group
    refine ⟨mul_mem hg.1 hn.1.1, fun a => ?_⟩
    show (g * n) (frame (mapLF t.lin (lf D (X.Fu u'))) a) - frame F' a ∈ _
    rw [frame_mapLF' _ htl, ← mul_apply_eq_comp, e]
    exact hA.2 a
  · show Λ = Formalism.HermitianLatticesTheory.gmap (g * n) Λ₁
    have hn1 : Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₁ := hn.1.2
    rw [gmap_mul', hn1, ← hgΛ, ← gmap_mul', mul_inv_cancel, gmap_one']

end GlobalTheory.RowTermReal
end
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpOrbGap

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt

theorem ampKF : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  intro hH k r L h μG w l l' hOne γ μR νR ν hD b hb0 hb hint v v' hv hv' ξ ξ'
  have H := hH.1
  obtain ⟨⟨hgap, hok, -, hw, hμ, -, -⟩, hl, hl'⟩ := hOne
  obtain ⟨hγ, -, -, hrel, hR, hQ, hQG⟩ := hD
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  let R : Rep k r := ⟨L.Hs, L.σ⟩
  have hDS : R.IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  obtain ⟨hmul, hone, huni, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r L.ε L.lam R hDS
  have hsm := H.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw)
  obtain ⟨C, Ws, -, hC⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v' hv'
  have hw1 : ‖w‖ = 1 := hw.choose_spec.2.1
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H k r L.ε μG hμ
  have hDG : R.IsDG L.ε L.lam := ⟨L.hlam, hσ, h, hgap, hok⟩
  obtain ⟨hd, hS⟩ := hc L.lam R hDG
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  haveI : SigmaFinite μG := hμ.1
  haveI : SigmaFinite μR := hR.1
  haveI : SFinite (pairMeas L) := by
    have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
    have : SigmaFinite L.μW := L.hμW.1.1
    have : SigmaFinite L.μW' := L.hμW'.1.1
    unfold pairMeas; infer_instance
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  have aν := ae_quot L hR hQ
  haveI : SFinite ν := sfinite_of_lintegral ν (fun p => ‖pairMaj γ b p‖ₑ) hint.1.enorm
    (aν.mono fun p hp => by
      have : 0 < pairMaj γ b p :=
        Real.rpow_pos_of_pos (one_pos.trans_le (PI.PolynomialProperness.GN.gN_ge_one (point_mem L hγ hp))) _
      simpa using this.ne') hint.2.ne
  have hRc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (hG.unit _ hγ)
  have hinv : μR.map GlobalTheory.SgInf.invM = μR :=
    (GlobalTheory.UnipUnimod.isUnimod_of_subset_Nset (S := RStab k r γ)
      ⟨fun a ha => ha.1.1, hRc.closed, hRc.one_mem, hRc.mul_mem, hRc.inv_mem⟩ (fun a ha => ha.1) hR).2
  have mi : Measurable (GlobalTheory.SgInf.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  let cj : Mt k r → Mt k r := fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j
  have mc : Measurable cj :=
    meas_mul (g := fun _ => γ) (meas_mul (f := fun _ => (γ⁻¹ : MatKR k r)) measurable_const measurable_id)
      measurable_const
  let a₂ : Mt k r → Mt k r → Mt k r := fun a x => Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x)
  have m2 : Measurable fun q : Mt k r × Mt k r => a₂ q.2 q.1 :=
    meas_mul (mc.comp (mi.comp measurable_snd)) measurable_fst
  have hW2 : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ a, f (a₂ a x) ∂μR) ∂νR := by
    intro f hf
    rw [hQG f hf]
    refine lintegral_congr fun x => ?_
    have mf : Measurable fun s : Mt k r => f fun i j => (Matrix.of s * Matrix.of x) i j :=
      hf.comp (meas_mul measurable_id measurable_const)
    rw [lintegral_map mf mc]
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun s => f fun i j => (Matrix.of (cj s) * Matrix.of x) i j) (mf.comp mc) mi]
    rfl
  haveI : SFinite νR := sfinite_of_weil μG νR μR hR.2.1 a₂ m2 hW2
  have m1 : Measurable fun q : PairSp k r × Mt k r => stabAct γ (Matrix.of q.2) q.1 :=
    (measurable_fst.fst.fst.prodMk (meas_mul measurable_snd measurable_fst.fst.snd)).prodMk
      (measurable_fst.snd.fst.prodMk (meas_mul (mc.comp measurable_snd) measurable_fst.snd.snd))
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have aνR : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
    refine ae_of_weil μG νR μR a₂ _ hcl.measurableSet aG hR.2.1 hW2 ?_
    filter_upwards [aR] with a ha x hx
    have h1 := hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hγ) _ (hG.inv_mem _ ha.1.1)) _ hγ
    have h3 : γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x ∈ UH (Hpk k r) := hx
    have h2 := hG.mul_mem _ (hG.inv_mem _ h1) _ h3
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ h1)] at h2
    exact h2
  have hI := integrable_ker L hγ w v v' ξ ξ' hμ aν (e := Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hb0 (by linarith) hint
    (fun x hx => by rw [neg_sub]; exact hC w hsm x hx) (fun x hx => by rw [neg_sub]; exact hC' w hsm x hx)
  have key := double_weil (pairMeas L) ν μG νR μR (fun a p => stabAct γ (Matrix.of a) p) a₂
    (mp_of_weil _ _ _ (fun a p => stabAct γ (Matrix.of a) p) m1 hQ) (mp_of_weil _ _ _ a₂ m2 hW2)
    (ker L γ w v v' ξ ξ') (aesm_ker L hγ w v v' ξ ξ' _ _ (ae_pairMeas L) aνR) hI (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae aν).and
        (Measure.quasiMeasurePreserving_snd.ae aR))] with t ht
      exact ker_act L hγ hrel w v v' ξ ξ' ht.2 ht.1 t.2)
  unfold ampJ OrbInt
  rw [Complex.ofReal_one, inv_one, one_smul, ← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (key.trans (integral_congr_ae ?_))
  · filter_upwards [aνR] with x hx
    rw [integral_ker_pair L hok.1 hγ hmul w v v' ξ ξ' hx,
      hl _ (Submodule.subset_span ⟨_, hG.mul_mem _ hγ _ hx, rfl⟩) v hv,
      hl' _ (Submodule.subset_span ⟨_, hx, rfl⟩) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp

end GlobalTheory.AmpOrbGap

end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants PI.AmpRootCommon PI.AmpRelAtPt

variable {k r : ℕ}

theorem psi_rel (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : ℂ) (hc : star c = c)
    (p : Point ℂ (r + 1)) (g₀ : MatKR k r) (hg : g₀ ∈ UH (Hpk k r)) (hZ : ZhatO k r z z' g₀ = ptMat p)
    (a : MatKR k r) (ha : a ∈ RStab k r g₀) : psi k r z c a = psi k r z' c (g₀⁻¹ * a * g₀) := by
  have ha' : a ∈ Nset k r ∧ g₀⁻¹ * a * g₀ ∈ Nset k r := ha
  have hsum := sum_super (ptσ_invol p) (zhat_pt hZ) (ptζ_ne p) (fun i i1 h => pt_adj p i i1 h)
    (flagMat_upper (z := z) ha'.1) (flagMat_diag ha'.1) (flagMat_upper (z := z') ha'.2)
    (flagMat_diag ha'.2) (flag_rel hz hz' hg ha)
  have hell : ell k r z' (g₀⁻¹ * a * g₀) = star (ell k r z a) := by
    rw [ell_eq, ell_eq, hsum]
  have hcim : c.im = 0 := Complex.conj_eq_iff_im.mp hc
  have hre : (c * star (ell k r z a)).re = (c * ell k r z a).re := by
    simp [Complex.mul_re, hcim]
  simp only [Formalism.QuantumDeterminants.psi, hell, hre]

theorem psi_conj (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) {n m : MatKR k r}
    (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : psi k r z c (n⁻¹ * m * n) = psi k r z c m := by
  obtain ⟨hone, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have hni : n⁻¹ ∈ Nset k r := hinvN n hn
  have h1 : psi k r z c 1 = 1 := by
    have hmul := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hone hone
    rw [Matrix.one_mul] at hmul
    have hne : psi k r z c 1 ≠ 0 := Complex.exp_ne_zero _
    exact mul_left_cancel₀ hne (hmul.symm.trans (mul_one _).symm)
  have hinv : n⁻¹ * n = 1 := uh_inv_mul hn.1
  have hpair := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hn
  rw [hinv, h1] at hpair
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c (hmulN _ hni _ hm) hn,
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hm]
  calc psi k r z c n⁻¹ * psi k r z c m * psi k r z c n
      = psi k r z c m * (psi k r z c n⁻¹ * psi k r z c n) := by ring
    _ = psi k r z c m := by rw [← hpair, mul_one]

theorem psi_cell (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (c : ℂ) (hc : star c = c) (p : Point ℂ (r + 1)) (γ : MatKR k r)
    (hγ : γ ∈ UH (Hpk k r)) (hcell : IsInCell (ZhatO k r z z' γ) p) {m : MatKR k r} (hm : m ∈ Nset k r)
    (hm' : γ⁻¹ * m * γ ∈ Nset k r) : psi k r z c m = psi k r z' c (γ⁻¹ * m * γ) := by
  obtain ⟨n, hn, n', hn', g₀, hg₀, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep k r z z' γ p hz hz' hT hT' hγ hcell
  obtain ⟨_, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have e1 : n' * n'⁻¹ = 1 := uh_mul_inv hn'.1
  have key : n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹ = g₀⁻¹ * (n⁻¹ * m * n) * g₀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc n' n'⁻¹, e1, Matrix.one_mul, Matrix.mul_one]
  have hnmn : n⁻¹ * m * n ∈ Nset k r :=
    hmulN _ (hmulN _ (hinvN n hn) _ hm) _ hn
  have ha : n⁻¹ * m * n ∈ RStab k r g₀ := by
    refine ⟨hnmn, ?_⟩
    rw [← key]
    exact hmulN _ (hmulN _ hn' _ hm') _ (hinvN n' hn')
  have hback := psi_conj z' hz' c (hinvN n' hn') hm'
  rw [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse e1)] at hback
  calc psi k r z c m = psi k r z c (n⁻¹ * m * n) := (psi_conj z hz c hn hm).symm
    _ = psi k r z' c (g₀⁻¹ * (n⁻¹ * m * n) * g₀) := psi_rel z z' hz hz' c hc p g₀ hg₀ hZ _ ha
    _ = psi k r z' c (n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹) := by rw [key]
    _ = psi k r z' c ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) := hback

end GlobalTheory.StabInv

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf.WuDec Formalism.L2.SG.Pf.EquivPf Formalism.L2.SG.Pf.Choice

theorem wloc_n {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s x : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ Nloc X u v) :
    X.Wloc u v (s * x) = psiV X u v (uMat s) • X.Wloc u v x := by
  have h1H : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Hloc X u v := by
    intro y _
    rw [uMat_one', Matrix.one_mulVec]
  have h1N : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Nloc X u v := by
    refine ⟨?_, ?_⟩
    · rw [uMat_one']
      exact inS_one
    · intro y _
      rw [uMat_one', sub_self, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  have hA := locEquiv X u v s hs 1 h1H x
  have hB := locEquiv X u v 1 h1N 1 h1H x
  simp only [mul_one] at hA
  simp only [mul_one, one_mul, uMat_one', psiV_one, one_smul] at hB
  rw [hA, ← hB]

theorem uMat_mul_loc {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem stab_inv : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Point ℂ (D.R.rS + 1)), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) p → ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u'))) γ, ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) (s * x)) (X.Wloc u' (vOf X τ) (γ⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) x) (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) := by
  intro D X θ C _ u u' τ γ p _ hrel s hs x
  obtain ⟨hQiQ, hQQi, hgram, hcol⟩ := C.isT τ
  have hs1 : s ∈ Nloc X u (vOf X τ) := hs.1
  have hs2 : γ⁻¹ * s * γ ∈ Nloc X u' (vOf X τ) := hs.2
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := Formalism.L2.SG.Pf.Choice.n_eq' X
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 :=
    fun a => pow_ne_zero _ (Formalism.L2.SG.Pf.Choice.frS_ne D)
  have hcolE : ∀ a : Fin D.R.rS, C.Q τ *ᵥ Pi.single (eI D.R.k D.R.rS a) 1 =
      frS D ^ (D.R.rS - (a : ℕ)) • Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.eR a) :=
    fun a => (hcol a a rfl).1
  have hmN : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      C.Qi τ * uMat t * C.Q τ ∈ Nset D.R.k D.R.rS := by
    intro w t ht
    have hU : (uMat t)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat t = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := t.2
    exact nset_loc hn _ _ _ hQiQ hQQi hgram _ _ hc hcolE _ hU ht
  have hpsi : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      psiV X w (vOf X τ) (uMat t) = psiS D (zB X (C.Qi τ) w τ) (C.Qi τ * uMat t * C.Q τ) := by
    intro w t ht
    have hback : C.Q τ * (C.Qi τ * uMat t * C.Q τ) * C.Qi τ = uMat t := by
      simp only [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
    have h := Formalism.L2.SG.Pf.psiTr C w τ _ (hmN w t ht)
    rw [hback] at h
    exact h
  set g := Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ with hg
  have hginv : g⁻¹ = C.Qi τ * uMat γ⁻¹ * C.Q τ := by
    apply Matrix.inv_eq_left_inv
    rw [hg, Formalism.L2.SG.RealObj.trG]
    calc C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat γ * C.Q τ)
        = C.Qi τ * (uMat γ⁻¹ * (C.Q τ * C.Qi τ) * uMat γ) * C.Q τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_inv_mul, Matrix.mul_one, hQiQ]
  have hconj : C.Qi τ * uMat (γ⁻¹ * s * γ) * C.Q τ = g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g := by
    rw [hginv, hg, Formalism.L2.SG.RealObj.trG, uMat_mul_loc, uMat_mul_loc]
    calc C.Qi τ * (uMat γ⁻¹ * uMat s * uMat γ) * C.Q τ
        = C.Qi τ * (uMat γ⁻¹ * 1 * uMat s * 1 * uMat γ) * C.Q τ := by
          rw [Matrix.mul_one, Matrix.mul_one]
      _ = C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat s * C.Q τ) * (C.Qi τ * uMat γ * C.Q τ) := by
          rw [← hQQi]
          simp only [Matrix.mul_assoc]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hz', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hT' : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) := by
    rw [hTz']; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u'
  have hm' : g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g ∈ Nset D.R.k D.R.rS := by
    rw [← hconj]; exact hmN u' _ hs2
  have hkey : psiV X u (vOf X τ) (uMat s) = psiV X u' (vOf X τ) (uMat (γ⁻¹ * s * γ)) := by
    rw [hpsi u s hs1, hpsi u' _ hs2, hconj]
    exact psi_cell _ _ hz hz' hT hT' _ (Complex.conj_ofReal _) p g hrel.1 hrel.2.1 (hmN u s hs1) hm'
  have hx : γ⁻¹ * (s * x) = (γ⁻¹ * s * γ) * (γ⁻¹ * x) := by group
  rw [wloc_n X u (vOf X τ) s x hs1, hx, wloc_n X u' (vOf X τ) _ _ hs2, ← hkey]
  have hnorm : ‖psiV X u (vOf X τ) (uMat s)‖ = 1 := norm_psiR _ _ _ _ _ _
  have hcm : (starRingEnd ℂ) (psiV X u (vOf X τ) (uMat s)) * psiV X u (vOf X τ) (uMat s) = 1 := by
    rw [Complex.conj_mul', hnorm]; norm_num
  ext ξ
  rw [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  linear_combination (inner ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) ξ) * hcm

end GlobalTheory.StabInv
end
