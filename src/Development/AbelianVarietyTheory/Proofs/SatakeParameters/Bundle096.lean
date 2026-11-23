module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle075
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle003
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → (∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1) → ∀ w, TrivAt χ w := by
  first | exact @GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite | exact GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite | (intros; apply GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite <;> assumption)
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → ∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1 := by
  first | exact @GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne | exact GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne | (intros; apply GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).Box := by
  intro D L C j ε τ φ hR
  have hb := (GlobalTheory.T.roundedSizeBound_window L C hR).1
  have hw := (GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C hR).2.2
  have hnt := fun g => GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR
  have hth := fun g => GlobalTheory.T.floor_size_bounds_at_thick_embedding L g j
  obtain ⟨hC, h100, hroom, hwb, -, hCb⟩ := hR
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := L.t_win.1
  have ht' : 1 ≤ D.R.t := by exact_mod_cast ht
  have hLw : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : 0 ≤ L.sc.b' := by linarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by
    have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hb'
    linarith
  have hw0 : (0 : ℝ) ≤ wHat D := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
  have hE : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold etaHat
    push_cast
    have := Nat.floor_le hη.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ bHat L
    have : (1 : ℝ) ≤ bHat L := by linarith
    exact_mod_cast this
  · show 1 ≤ wHat D
    unfold wHat
    omega
  · show 20 * wHat D ≤ bHat L
    have : (20 : ℝ) * wHat D ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * etaHat L ≤ bHat L
    have : (20 : ℝ) * etaHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * sHat L ≤ bHat L
    have : (20 : ℝ) * sHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · intro i
    show ((etaHat L : ℕ) : ℤ) < szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
    generalize letter τ φ i = g
    have hsz : L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by
      by_cases hT : Thick D.host g
      · have := (hth g hT).1
        linarith
      · exact (hnt g hT).1
    have key : ((etaHat L : ℕ) : ℤ) + D.R.t + 1 < ⌊(hcAt D g).e j⌋ := by
      have : ((etaHat L : ℕ) : ℝ) + D.R.t + 1 < (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    unfold szT
    split_ifs <;> omega

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.pageWord_thick_iff | exact GlobalTheory.HTW.pageWord_thick_iff | (intros; apply GlobalTheory.HTW.pageWord_thick_iff <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem mul_small_le_bHat {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ) (hR : Roomy L C') (hC : 0 ≤ C)
    (hCC : 2 * C ≤ C') (hj : 2 * j + 2 ≤ D.host.Lw) :
    C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  have hlow := (GlobalTheory.T.roundedSizeBound_window L C' hR).1
  obtain ⟨-, hw2, hG⟩ := GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C' hR
  obtain ⟨h100, -, -, -, -, hbig⟩ := hR
  have hw0 : (0 : ℝ) ≤ (wHat D : ℝ) := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b' := by linarith
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hjN : (j + 1) * 2 ≤ D.host.Lw := by omega
  have hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  push_cast
  have s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1)
      ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)
  have s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b' := by
    have := mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)
    nlinarith
  have s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
    have hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1) := by nlinarith
    nlinarith
  linarith

end GlobalTheory.HTW
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.ColumnWeightComparison

theorem colGeTw_of_cmpLite {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} (Ch : Chain Lv) (h : CmpLite D c Tw u μ w hg Ch)
    (x : ((D.fm u).lat 0).V) (s : ℝ)
    (hx : vGeLat (D.gat u w hg) (Lv.Int D.R.m) (Ch.chainK D.R.m (c.cmp u w hg x)) s) :
    WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s := by
  obtain ⟨cmp, h0, hK, hrat, hval⟩ := h
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.Proof.LatticeValuationBound.exists_chain (Tw.fm u μ) Ch (c.embW u w hg) cmp hK hrat
    (Tw.e0 u μ x) D.R.m le_rfl
  refine ⟨y, ?_, hval y s (by rw [hy', h0]; exact hx)⟩
  rw [hy, Tw.embed_mul_block_embedding]
  rfl

theorem colGe0_of_colGeTw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (s : ℝ) (h0 : Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : WeilJacquetShalikaLaw.ColGeTw Tw u D.what₂.mu0 w x s) : WeilJacquetShalikaLaw.ColGe0 D u w x s := by
  obtain ⟨y, hy, hv⟩ := h
  refine ⟨(Tw.eMu0 u D.R.m le_rfl).symm y, ?_,
    GlobalTheory.Proof.LatticeValuationBound.VGe_symm _ _ _ (Tw.eMu0_lat u D.R.m le_rfl) hv⟩
  have h1 := Tw.eMu0_emb u D.R.m le_rfl ((Tw.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h1
  have h2 := Tw.eMu0_emb u 0 (Nat.zero_le _) x
  rw [← h0, Tw.embed_mul_block_embedding] at h2
  exact eq_of_heq (h1.symm.trans (GlobalTheory.Proof.LatticeValuationBound.col_heq (D.memberColumns_twistedChain_base u) h2))

theorem cmpV_of_cmpLite (D : D7) (Y : LatInst D) (c : LatCmp D) (Dx : DivX D) (Tw : TwForms D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv)
    (h0 : ∀ u, Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : ∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
      CmpLite D c Tw u μ w hg (LC μ u w hg).2) :
    WeilJacquetShalikaLaw.CmpV c Dx Tw (reW Y LC) := by
  intro u w hg μ hU hQ x s hx
  have key : WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s :=
    colGeTw_of_cmpLite c Tw u μ w hg (LC μ u w hg).2 (h μ hU u w hg hQ) x s hx
  refine ⟨?_, fun _ => key⟩
  rintro rfl
  exact colGe0_of_colGeTw Tw u w x s (h0 u) key

end GlobalTheory.Proof.ColumnWeightComparison
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

theorem _root_.GlobalTheory.T.jumpWindow_and_blockExponent_of_embeddings : ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  first | exact @GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings | exact GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings | (intros; apply GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

theorem _root_.GlobalTheory.T.glMap_diagUniformizer_elementarySublattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)), (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) → haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  first | exact @GlobalTheory.DiagElem.glMap_diag_mem_subElem | exact GlobalTheory.DiagElem.glMap_diag_mem_subElem | (intros; apply GlobalTheory.DiagElem.glMap_diag_mem_subElem <;> assumption)
end

section

open GlobalTheory.LatHecke GlobalTheory.RowSatakeBound

theorem _root_.GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (β : Multiset ℂ), IsUnitarySatake O K r β → IsUnitarySatake O K r (β.map (·⁻¹)) := by
  first | exact @GlobalTheory.SatakeInv.isUnitarySatake_map_inv | exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv | (intros; apply GlobalTheory.SatakeInv.isUnitarySatake_map_inv <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

namespace GlobalTheory.ExpFacOrbits

theorem expFactor_allOrbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  intro D p _ R M N N' eA be hbe
  classical
  set a : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y =>
    X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) with ha_def
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun y => constantCoeff_X _)
  have hlin : ∀ ab : Fin M × Fin N', (fun s : ZMod (nP D p) =>
      Formalism.DworkPowerSeriesWeights.linSub (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) (s, ab.1, ab.2)) =
      fun s => (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) := fun ab =>
    funext fun s => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM (s, ab.1, ab.2)
  have hX : ∀ ab : Fin M × Fin N', HasSubst (fun s : ZMod (nP D p) =>
      (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) := fun ab =>
    hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)
  have hB : Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be =
      ∑ ab : Fin M × Fin N', subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be := by
    unfold Formalism.DworkPowerSeriesWeights.bSum
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [hlin ab]
  have hcc : constantCoeff ((-1 : ℂ_[p]) •
      Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be) = 0 := by

    rw [hB, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    rw [MvPowerSeries.constantCoeff_smul, constantCoeff_subst_eq_zero (hX ab) (fun s => constantCoeff_X _) hbe,
      smul_zero]
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' ha hcc]
  show mvExp _ = mvExp _
  congr 1

  rw [hB, ← coe_substAlgHom ha, map_smul, map_sum, coe_substAlgHom ha]
  have hterm : ∀ ab : Fin M × Fin N', subst a (subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be) =
      subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p (eA ab.1).1 s, (eA ab.1).2, ab.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be := by
    intro ab
    rw [subst_comp_subst_apply (hX ab) ha]
    congr 1
    funext s
    rw [subst_X ha]
  simp_rw [hterm]
  unfold OrbitPlaces.beAll
  simp only [← Finset.smul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Equiv.sum_comp eA (fun x : R × Fin N => ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p x.1 s, x.2, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort R (fun r => ∑ a : Fin N, ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p r s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)

end GlobalTheory.ExpFacOrbits
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.HostKur.host_image_mem_Kur | exact GlobalTheory.HostKur.host_image_mem_Kur | (intros; apply GlobalTheory.HostKur.host_image_mem_Kur <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.VanishAtOver

theorem intAtA_mul_of_prV_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q →
    ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 →
    ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  intro F E _ _ _ _ _ v Q hv a ha c
  apply GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero
  intro w hw
  have hwv : w = v := HeightOneSpectrum.ext (hw.trans hv.symm)
  subst hwv
  rw [map_mul, ha, mul_zero]

end GlobalTheory.VanishAtOver
end
