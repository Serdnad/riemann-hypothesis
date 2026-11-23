module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle055
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle343
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalCoordinatesRationalFlagPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle338
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle243
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle234
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIntegralFramesFixedLiftLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.discrete_series_bessel_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B l : R.H → Wp) (w : R.H), R.IsDS ε mu → GapAtLeast ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → SideG k r z π u μW μN μG νq → IsBes R z π B → R.KFin w → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0 → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → IsBeL R z π μW μN l → ∃ v, R.KFin v ∧ l v ≠ 0 := by
  first | exact @GlobalTheory.BesselPeriodNonzero.exists_kFin_period_ne_zero | exact GlobalTheory.BesselPeriodNonzero.exists_kFin_period_ne_zero | (intros; apply GlobalTheory.BesselPeriodNonzero.exists_kFin_period_ne_zero <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StabIntCoord

theorem mem_maxUnramifiedSubfield_conj_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : Frames L r k)
    (x : S.GLV) (hx : x ∈ S.St) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (h1 : ∀ j, x (S.f j) = ∑ i, s i j • S.f i) (h2 : ∀ j, x (S.f' j) = ∑ i, s' i j • S.f' i) :
    x ∈ S.K0 ↔ IsIntM L s' := by
  have heq := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 s s' hs hs').2 ⟨x, hx, h1, h2⟩
  have hint := ((GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 s s' hs hs' heq).2
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hl1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  have e1 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f hl1 x s hs h1
  have e2 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f' hl2 x s' hs' h2
  unfold Frames.K0
  simp only [Subgroup.mem_inf]
  rw [e1, e2, hint]
  tauto

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

open IsDedekindDomain

theorem loc_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) {n r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (c : ((A.loc p).Fp)ˣ)
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E)) (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (hE : A.Ext p x g') (v : Fin (r + 1) → Fin n → E) (vl : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (hv : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • vl a = A.bc p (v a))
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ b : Fin (r + 1), x (v b) = ∑ a, M a b • v a) (b : Fin (r + 1)) :
    g' (vl b) = ∑ a : Fin (r + 1), (algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ)) /
      (c : (A.loc p).Fp) ^ (r - (b : ℕ))) * (A.loc p).ιE (M a b)) • vl a := by
  have hc : ∀ m : ℕ, ((c : (A.loc p).Fp) ^ m) ≠ 0 := fun m => pow_ne_zero _ c.ne_zero
  have hvl : ∀ a : Fin (r + 1), vl a = algebraMap (A.loc p).Fp (A.loc p).Ep (((c : (A.loc p).Fp) ^ (r - (a : ℕ)))⁻¹) • A.bc p (v a) := by
    intro a
    rw [← hv a, smul_smul, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_smul]
  have hbc : ∀ (l : Fin (r + 1) → E) (w : Fin (r + 1) → Fin n → E),
      A.bc p (∑ a, l a • w a) = ∑ a, (A.loc p).ιE (l a) • A.bc p (w a) := by
    intro l w
    funext i

    simp [Places.bc, Finset.sum_apply, map_sum, smul_eq_mul, map_mul]
  rw [hvl b, map_smul, hE, hM b, hbc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hv a, smul_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, map_mul]
  ring

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord



theorem integralStabiliser_iff_rational_coords_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ x ∈ G.St, ∀ B : Formalism.L2.SG.PairVal.MatR D, (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) → (x ∈ G.K0 ↔ ∀ a b : Fin (D.R.rS + 1), a < b → B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c x hx B hB
  obtain ⟨s, s', hs, hs', hsf, hsf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
  have key : ∀ p : PlF D, (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔
      ∀ a b : Fin (D.R.rS + 1), a < b → (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O := by
    intro p
    haveI := (D.s.atP p).lf
    haveI := (D.s.atP p).char0
    haveI : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).lf
    haveI : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).char0
    obtain ⟨xp, hxp, hExt⟩ := hx p
    have huniq := ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 x)
    have hK : (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔ xp ∈ (G.S p).K0 := by
      constructor
      · rintro ⟨g', hg', hgE⟩
        rwa [huniq.unique hExt hgE]
      · intro h; exact ⟨xp, h, hExt⟩
    rw [hK]
    have h1 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f (G.S p).f (G.f_eq p) s hsf
    have h2 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) s' hsf'
    have h3 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) B hB
    have hceq : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.c p).val = algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E) := c.c_eq p
    show _ ↔ ∀ a b : Fin (D.R.rS + 1), a < b → ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O
    have hcne : ∀ m : ℕ, ((G.c p).val ^ m) ≠ 0 := fun m => pow_ne_zero _ (G.c p).ne_zero
    have huni : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUni M →
        IsUni (fun a b : Fin (D.R.rS + 1) => algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (M a b)) := by
      intro M hM
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · simp [hM.1 i j hij]
      · simp [hM.2 i, div_self (hcne _)]
    rw [mem_maxUnramifiedSubfield_conj_iff _ _ _ (G.S p) xp hxp _ _ (huni s hs) (huni s' hs') h1 h2]
    have hli : LinearIndependent ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.S p).f' :=
      (GlobalTheory.FrameBasic.main _ _ _ (G.S p)).1.comp Sum.inr Sum.inr_injective
    have hsB : ∀ a b, ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) := by
      intro a b
      have e := (h2 b).symm.trans (h3 b)
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
      simp_rw [← sub_smul] at e
      have h0 := Fintype.linearIndependent_iff.1 hli _ e a
      have hu : IsUnit (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
        (isUnit_iff_ne_zero.2 (div_ne_zero (hcne _) (hcne _))).map _
      rw [← mul_sub, hu.mul_right_eq_zero, sub_eq_zero] at h0
      exact h0
    have hent : ∀ a b : Fin (D.R.rS + 1), a < b → algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
        ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
          ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) := by
      intro a b hab
      have hab' : (a : ℕ) < b := hab
      have hb := b.isLt
      rw [show D.R.rS - (a : ℕ) = (D.R.rS - b) + ((b : ℕ) - a) by omega, pow_add,
        mul_div_cancel_left₀ _ (hcne _), map_pow, hceq, hsB, mul_comm]
    constructor
    · intro h a b hab
      rw [← hent a b hab]
      exact h a b
    · intro h a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · beta_reduce
        rw [hent a b hab]
        exact h a b hab
      · show _ ∈ _
        simp [hs'.2 a, div_self (hcne _)]
      · show _ ∈ _
        simp [hs'.1 a b hab]
  have hK0 : x ∈ G.K0 ↔ ∀ p, ∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g' := Iff.rfl
  rw [hK0, forall_congr' key]
  have hI : ∀ a b : Fin (D.R.rS + 1), a < b → (B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔
      ∀ p : PlF D, (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O) := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hb := b.isLt
    have hn : (b : ℕ) - (a : ℕ) ≤ D.R.rS := by omega
    have e : (-((b : ℤ) - (a : ℤ))) = -((((b : ℕ) - (a : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hab'.le]
    rw [e]
    exact GlobalTheory.T.mem_inv_pow_different_iff_local D ⟨Y.δ, Y.M, Y.agree⟩ _ hn (B a b)
  constructor
  · intro h a b hab
    exact (hI a b hab).2 fun p => h p a b hab
  · intro h p a b hab
    exact (hI a b hab).1 (h a b hab) p

end GlobalTheory.HL.StabIntCoord
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), (∀ x ∈ G.St, ∃ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B ∧ (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) ∧ ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) ∧ ∀ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B → (∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) → ∃! x, x ∈ G.St ∧ ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a := by
  first | exact @GlobalTheory.HL.StCoord.stab_coords | exact GlobalTheory.HL.StCoord.stab_coords | (intros; apply GlobalTheory.HL.StCoord.stab_coords <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_global_coordinates_rational_flagPair : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∃ G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k, Nonempty (GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) := by
  first | exact @GlobalTheory.HL.GCoordEx.exists_global_coords | exact GlobalTheory.HL.GCoordEx.exists_global_coords | (intros; apply GlobalTheory.HL.GCoordEx.exists_global_coords <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unsignedLocalTerm_row_lattice_isTerm : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ p : PlF D, (locH Z p).IsTerm (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
  first | exact @GlobalTheory.LocOver.locU_isTerm | exact GlobalTheory.LocOver.locU_isTerm | (intros; apply GlobalTheory.LocOver.locU_isTerm <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimeAlmostAll

open Formalism.MainNotions.S.LocNG

theorem isUnitO_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} {x y : E} (hx : IsUnitO M x) (hy : IsUnitO M y) : IsUnitO M (x * y) := by
  obtain ⟨hx1, x', hx', hxx⟩ := hx
  obtain ⟨hy1, y', hy', hyy⟩ := hy
  refine ⟨mul_mem hx1 hy1, x' * y', mul_mem hx' hy', ?_⟩
  linear_combination (y * y') * hxx + hyy

theorem isUnitO_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} : IsUnitO M 1 :=
  ⟨one_mem _, 1, one_mem _, mul_one 1⟩

theorem isUnitO_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} {ι : Type} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, IsUnitO M (g i)) :
    IsUnitO M (∏ i ∈ s, g i) :=
  Finset.prod_induction g (IsUnitO M) (fun _ _ => isUnitO_mul) isUnitO_one h

theorem isUnitO_cj {D : D7} (Z : LocDat D) (p : PlF D) {x : (D.s.atP p).Ep} (hx : IsUnitO (Z.M p) x) :
    IsUnitO (Z.M p) ((Z.M p).L.cj x) := by
  obtain ⟨hx1, x', hx', hxx⟩ := hx
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : ∀ y ∈ (Z.M p).L.O, (Z.M p).L.cj y ∈ (Z.M p).L.O := by
    intro y hy
    rw [Z.hcj p, hO] at *
    exact Formalism.L2.SG.Pf.LocFacts.lf_cj_mem p y hy
  refine ⟨hc x hx1, (Z.M p).L.cj x', hc x' hx', ?_⟩
  rw [← map_mul, hxx, map_one]

end GlobalTheory.PrimeAlmostAll


open GlobalTheory.PrimeAlmostAll in
theorem GlobalTheory.PrimeAlmostAll.primeTo_finite : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Gval F00 F'0 ≠ 0 → ∀ FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS, (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p)) → {p : PlF D | ¬ (FP p).PrimeTo}.Finite := by
  intro D Z u u' F00 F'0 hG FP hFP
  let xs : Fin (D.R.rS + 2) → D.host.E := fun l => Formalism.MainNotions.S.Dl F00.fl F'0.fl (l : ℕ)
  have hfin : ({p : PlF D | (Z.M p).split ≠ none} ∪
      (⋃ a : Fin (D.R.rS + 1), {p : PlF D | ¬ LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}) ∪
      {p : PlF D | ¬ LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE (Gval F00 F'0))} ∪
      ⋃ l : Fin (D.R.rS + 2), {p : PlF D | xs l ≠ 0 ∧ ¬ LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE (xs l))}).Finite := by
    refine (((GlobalTheory.T.local_models_unsplit_almost_all D Z).union (Set.finite_iUnion fun a => GlobalTheory.T.frame_factors_local_units_almost_all D Z a)).union (GlobalTheory.T.nonzero_cm_element_local_unit_almost_all D Z _ hG)).union
      (Set.finite_iUnion fun l => ?_)
    by_cases h : xs l = 0
    · simp [h]
    · exact (GlobalTheory.T.nonzero_cm_element_local_unit_almost_all D Z _ h).subset (fun p hp => hp.2)
  refine hfin.subset ?_
  intro p hp
  by_contra hgood
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_not] at hgood
  obtain ⟨⟨⟨hsp, hfr⟩, hGv⟩, hD⟩ := hgood
  apply hp
  have hL4 := GlobalTheory.T.localised_base_frames_leading_minor_eq D Z p F00 F'0 (Tu D u) (Tu D u') (FP p) (hFP p)
  have hκ : ∀ l : ℕ, LocNG.IsUnitO (Z.M p)
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) := by
    intro l
    refine isUnitO_prod _ _ fun a _ => ?_
    split_ifs
    · exact isUnitO_mul (isUnitO_cj Z p (hfr a)) (hfr a)
    · exact isUnitO_one
  refine ⟨hsp, ?_, ?_⟩
  ·
    have hlast : ∀ a : Fin (D.R.rS + 1), ¬ a.val < D.R.rS → (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a = 1 := by
      intro a ha
      have h1 : a.val = D.R.rS := by omega
      have : frFac Z.δ p a = 1 := by
        unfold frFac
        rw [h1, Nat.sub_self, pow_zero, Ring.inverse_one]
      rw [this, map_one, one_mul]
    have hK : (∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS + 1 then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) =
        ∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1 := by
      refine Finset.prod_congr rfl fun a _ => ?_
      have ha : a.val < D.R.rS + 1 := a.2
      by_cases h : a.val < D.R.rS
      · rw [if_pos ha, if_pos h]
      · rw [if_pos ha, if_neg h, hlast a h]
    set K := ∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1 with hKdef
    have eG : (FP p).Gv = (FP p).Dm (D.R.rS + 1) * (Z.M p).L.cj ((FP p).Dm (D.R.rS + 1)) -
        algebraMap _ _ ((FP p).A.T * (FP p).B.T) * ((FP p).Dm D.R.rS * (Z.M p).L.cj ((FP p).Dm D.R.rS)) := rfl
    have hT := (hFP p).2.2
    rw [hT.1, hT.2, hL4 (D.R.rS + 1), hL4 D.R.rS, hK] at eG
    have eGv : (D.s.atP p).ιE (Gval F00 F'0) =
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F00.fl F'0.fl (D.R.rS + 1)) * (D.s.atP p).ιE (star (Formalism.MainNotions.S.Dl F00.fl F'0.fl (D.R.rS + 1))) -
        ((Tu D u : (D.s.atP p).Ep) * (Tu D u' : (D.s.atP p).Ep)) *
        ((D.s.atP p).ιE (Formalism.MainNotions.S.Dl F00.fl F'0.fl D.R.rS) * (D.s.atP p).ιE (star (Formalism.MainNotions.S.Dl F00.fl F'0.fl D.R.rS))) := by
      simp only [Gval, Formalism.MainNotions.S.Gflag, map_sub, map_mul, map_natCast, Tu]
    have hTT : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Tu D u : (D.s.atP p).Fp) * (Tu D u' : (D.s.atP p).Fp)) =
        (Tu D u : (D.s.atP p).Ep) * (Tu D u' : (D.s.atP p).Ep) := by
      rw [map_mul, map_natCast, map_natCast]
    rw [hTT, map_mul, map_mul, cj_iota (Z.hcj p), cj_iota (Z.hcj p)] at eG
    have : (FP p).Gv = (K * (Z.M p).L.cj K) * (D.s.atP p).ιE (Gval F00 F'0) := by
      rw [eG, eGv]; ring
    rw [this]
    exact isUnitO_mul (isUnitO_mul (hκ D.R.rS) (isUnitO_cj Z p (hκ D.R.rS))) hGv
  ·
    intro l hl
    simp only [LocNG.FPair.ends, Finset.mem_filter, Finset.mem_range] at hl
    obtain ⟨hlr, -, hu⟩ := hl
    rw [hL4 l] at hu ⊢
    by_cases h0 : xs ⟨l, hlr⟩ = 0
    · exfalso
      have h0' : Formalism.MainNotions.S.Dl F00.fl F'0.fl l = 0 := h0
      rw [h0', map_zero, mul_zero] at hu
      exact not_isUnit_zero hu
    · exact isUnitO_mul (hκ l) (hD ⟨l, hlr⟩ h0)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_integral_frames_fixed_lift_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → (∀ p, φ p ∈ XLam Λ (lf D F0)) → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (fixB D s (NT D u) De Q) := by
  first | exact @GlobalTheory.LoopC.FixedLift.card_frames_le | exact GlobalTheory.LoopC.FixedLift.card_frames_le | (intros; apply GlobalTheory.LoopC.FixedLift.card_frames_le <;> assumption)
end

section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

theorem _root_.GlobalTheory.T.besselModel_hyperbolicBasis_scaled : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS),
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  first | exact @GlobalTheory.TypeAsm.FramePf.phiV_frame | exact GlobalTheory.TypeAsm.FramePf.phiV_frame | (intros; apply GlobalTheory.TypeAsm.FramePf.phiV_frame <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicLattice_concreteData_eq_adelicSpan : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ w : Fin X.B.I.n → D.host.E ⊗[D.host.F] Ad D.host.F, w ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) ↔ (fun i => ιA.symm (w i)) ∈ X.B.I.Lf := by
  first | exact @GlobalTheory.St.G.latTransport | exact GlobalTheory.St.G.latTransport | (intros; apply GlobalTheory.St.G.latTransport <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integralFiniteAdeleIso_commutes_with_conjugation : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  first | exact @GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | exact GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | (intros; apply GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.projection_moves_typeVectors_modLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), (∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) := by
  first | exact @GlobalTheory.St.G.FrameClose.typeVec_close | exact GlobalTheory.St.G.FrameClose.typeVec_close | (intros; apply GlobalTheory.St.G.FrameClose.typeVec_close <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.St.G.psiEf_transport_rat | exact GlobalTheory.St.G.psiEf_transport_rat | (intros; apply GlobalTheory.St.G.psiEf_transport_rat <;> assumption)
end
