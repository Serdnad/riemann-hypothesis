module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTransitiveAdelicUnitLengthVectors
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle272
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle316
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpendicularRankIdealBound
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  first | exact @GlobalTheory.Dec.stepBoundAt_of_countHyp | exact GlobalTheory.Dec.stepBoundAt_of_countHyp | (intros; apply GlobalTheory.Dec.stepBoundAt_of_countHyp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.principalLevelFrame GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.RowFrameParts

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R F X0), StdPsi Y.hF Y.PY ∧ ∀ σ, R.HE.e (Y.eE (D.what₂.onb σ)) ∈ isotE R.θ Y.PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rowRepR R.θ (Y.eFT (D.what₂.ft σ))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y
  refine ⟨Y.stdPsi.1, fun σ => ?_⟩
  have h := Y.tied.sharp.ft σ
  have h1 := Y.prtE (D.what₂.ft σ)
  have h2 := Y.eE_read (D.what₂.onb σ)
  have h3 := h1 ▸ h
  obtain ⟨z, hz, hze⟩ := h3
  rw [h2] at hze
  have : z = R.HE.e (Y.eE (D.what₂.onb σ)) := LinearEquiv.injective _ hze
  rw [← this]
  exact hz

end GlobalTheory.Mem.R3.RowFrameParts
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocalBlockEntries

open Formalism.L2.SG.Pf.AtPt

theorem ptEntryL_eq' {S : Type} [CommRing S] (L : List (Sˣ × ℕ+)) : ∀ i j : ℕ,
    Formalism.MainNotions.S.Loc.ptEntryL L i j = ptEntry (L.map fun b => ((b.1 : S), (b.2 : ℕ))) i j := by
  induction L with
  | nil => intro i j; rfl
  | cons b L ih =>
    intro i j
    obtain ⟨t, s⟩ := b
    simp only [Formalism.MainNotions.S.Loc.ptEntryL, List.map_cons, ptEntry]
    split_ifs <;> first | rfl | exact ih _ _

theorem modBlocks_map' {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ) (L : List (Sˣ × ℕ+)),
    modBlocks f a l = some L → L.map (fun b => ((b.1 : S), (b.2 : ℕ))) = mapBlocks f a l := by
  intro l
  induction l with
  | nil =>
    intro a L h
    simp only [modBlocks, Option.some.injEq] at h
    subst L
    rfl
  | cons b l ih =>
    obtain ⟨t, s⟩ := b
    intro a L h
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨L1, hL1, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [List.map_cons, mapBlocks, ih (a + s) L1 hL1]
    rfl

theorem mapBlocks_snd' {A B : Type} (f : ℕ → ℕ → A → B) : ∀ (l : List (A × ℕ)) (a : ℕ),
    (mapBlocks f a l).map Prod.snd = l.map Prod.snd
  | [], _ => rfl
  | (t, s) :: l, a => by simp [mapBlocks, mapBlocks_snd' f l (a + s)]

theorem modBlocks_some {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ), (∀ b ∈ l, 0 < b.2) → (∀ b ∈ l, ∀ a' s, IsUnit (f a' s b.1)) →
      ∃ L, modBlocks f a l = some L := by
  intro l
  induction l with
  | nil =>
    intro a _ _
    exact ⟨[], rfl⟩
  | cons b l ih =>
    obtain ⟨t, s⟩ := b
    intro a h1 h2
    obtain ⟨L1, hL1⟩ := ih (a + s) (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
        (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    have hu : IsUnit (f a s t) ∧ 0 < s := ⟨h2 (t, s) List.mem_cons_self a s, h1 (t, s) List.mem_cons_self⟩
    rw [modBlocks, dite_eq_left hu, hL1]
    exact ⟨_, rfl⟩

end GlobalTheory.LocalBlockEntries

end

open Formalism.L2.SG.Pf.AtPt in
theorem GlobalTheory.LocOver.isPoint_of_scaled : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS), ZhatOM (ZhatL F F') = ptMat w → P.A.f = scaled Z p (frame F) → P.B.f = scaled Z p (frame F') → P.IsPoint := by
  intro D Z p T T' F F' w P hZ hA hB
  let fB : ℕ → ℕ → D.host.E → (D.s.atP p).Ep := fun a s t =>
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Z p)⁻¹ ^ nu D.R.rS a (a + s - 1)) * (D.s.atP p).ιE t
  have hunit : ∀ b ∈ w.1, ∀ a' s, IsUnit (fB a' s b.1) := fun b hb a' s =>
    (Formalism.L2.SG.Pf.BBTie.bt_alg_unit p (pow_ne_zero _ (inv_ne_zero (yP_ne Z p)))).mul
      (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p (w.2.1 b hb).1)
  obtain ⟨L, hL⟩ := GlobalTheory.LocalBlockEntries.modBlocks_some fB w.1 1 (fun b hb => (w.2.1 b hb).2) hunit
  have hLm := GlobalTheory.LocalBlockEntries.modBlocks_map' fB w.1 1 L hL
  have hsize : (L.map (fun b => (b.2 : ℕ))).sum = D.R.rS + 1 := by
    have := congrArg (List.map Prod.snd) hLm
    rw [List.map_map, GlobalTheory.LocalBlockEntries.mapBlocks_snd'] at this
    rw [← w.2.2, ← this]; rfl
  refine ⟨⟨L, hsize⟩, fun a b => ?_⟩
  have hR : (⟨L, hsize⟩ : Formalism.MainNotions.S.Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)).mat a b =
      if b = sgF w a then fB (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0 := by
    simp only [Formalism.MainNotions.S.Loc.Pt.mat]
    rw [GlobalTheory.LocalBlockEntries.ptEntryL_eq', hLm, ptEntry_eq, pSig_map, pTau_map _ _ _ _ (by rw [w.2.2]; exact a.2)]
    simp only [sgF, Fin.ext_iff]
  rw [hR]
  have hZab := congrFun (congrFun hZ a) b
  rw [zhatOM_eq, ptMat_apply'] at hZab
  simp only [Sg, Matrix.mul_diagonal] at hZab
  have hL1 : (locH Z p).Zhat P.A.f P.B.f a b =
      frFac Z.δ p b * (D.s.atP p).cj (frFac Z.δ p a) * (D.s.atP p).ιE (ZhatL F F' a b) := by
    simp only [Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, hA, hB, GlobalTheory.LocOver.scaled]
    rw [Formalism.L2.SG.Pf.BBTie.formP_bc, Z.hcj p]
    rfl
  rw [hL1, frFac_eq, frFac_eq, cj_alg]
  have key : ∀ (X Y : (D.s.atP p).Ep) (z : D.host.E), (-1 : (D.s.atP p).Ep) ^ (D.R.rS - b.val) * (X * Y * (D.s.atP p).ιE z) =
      X * Y * (D.s.atP p).ιE (z * (-1) ^ (D.R.rS - b.val)) := by
    intro X Y z; rw [map_mul, map_pow, map_neg, map_one]; ring
  rw [key, hZab]
  split_ifs with hb
  · subst hb
    simp only [fB]
    rw [nu_eq, pow_add, map_mul]
    ring
  · rw [map_zero, mul_zero]
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.level_char_match : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Λ Fr h0 hh0
  obtain ⟨Fr', hFr'⟩ := GlobalTheory.T.transport_frame_along_unitary_adelic F E n cm.sig J Λ (hat F S.Lb) (gp 0 * gp 1) k h0 hh0 Fr
  obtain ⟨κ, hκ, hκU⟩ := GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Fr'
  refine ⟨h0 * κ, ?_, ?_⟩
  · intro x
    have hκi : (κ⁻¹ : UPts cm.sig J (Ad F)).1 ∈ stabGL (hat F S.Lb) := by
      simpa using (stabGL (hat F S.Lb)).inv_mem hκ
    have e : ((h0 * κ)⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x = (κ⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ ((h0⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x) := by
      rw [_root_.mul_inv_rev]; simp [Matrix.mulVec_mulVec]
    rw [e, ← hκi _, hh0]
  · intro y
    have e : ((h0 * κ)⁻¹ * y * (h0 * κ) : UPts cm.sig J (Ad F)) = κ⁻¹ * (h0⁻¹ * y * h0) * κ := by group
    obtain ⟨h1, h2⟩ := hFr' y
    obtain ⟨h3, h4⟩ := hκU (h0⁻¹ * y * h0)
    refine ⟨?_, ?_⟩
    · rw [h1, h3, e]
    · intro hy
      rw [h2]
      have hy' : ((κ⁻¹ * (h0⁻¹ * y * h0) * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U := by rw [← e]; exact hy
      rw [h4 hy']
      have hx : (⟨_, hy'⟩ : S.U) = ⟨_, hy⟩ := Subtype.ext (congrArg (fun z : UPts cm.sig J (Ad F) => z.1) e.symm)
      rw [hx]
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegAsm.FixedForm.main | exact GlobalTheory.DegAsm.FixedForm.main | (intros; apply GlobalTheory.DegAsm.FixedForm.main <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselFunction_eq_scalar_sq_normalisedBessel_torusConjugate : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  first | exact @GlobalTheory.ThA.besselJ_changeFrame | exact GlobalTheory.ThA.besselJ_changeFrame | (intros; apply GlobalTheory.ThA.besselJ_changeFrame <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  first | exact @GlobalTheory.PerpInst.exists_isPerpInst | exact GlobalTheory.PerpInst.exists_isPerpInst | (intros; apply GlobalTheory.PerpInst.exists_isPerpInst <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.stabilizer_transitive_adelic_unit_length_vectors : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E) (xf g : I.Gf), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → x ∈ lamX I (1, xf) → x ∈ lamX I (1, g) → ∃ h : I.Gf, (I.fmat h *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∧ ∃ k ∈ I.Kset, g = h * xf * k := by
  first | exact @GlobalTheory.FinOrbit.exists_stab_mul_level | exact GlobalTheory.FinOrbit.exists_stab_mul_level | (intros; apply GlobalTheory.FinOrbit.exists_stab_mul_level <;> assumption)
end

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FundEq

open GlobalTheory.DegVol

theorem measurable_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) :
    Measurable (fun x : ι → Formalism.QuantumDeterminants.Mt k r => mulP m x) :=
  Measurable.of_eval fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.comp (measurable_pi_apply v)

theorem measure_eq_tsum {ι : Type} {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω S : Set (ι → Formalism.QuantumDeterminants.Mt k r)) [Countable Γ] (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω) :
    μ S = ∑' a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((measurable_mulP _ hΩ).inter hS).nullMeasurableSet

def invP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) : ι → Formalism.QuantumDeterminants.Mt k r :=
  fun v => Matrix.of.symm (Matrix.of (m v))⁻¹

theorem mulP_invP_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det)
    (x : ι → Formalism.QuantumDeterminants.Mt k r) : mulP (invP m) (mulP m x) = x := by
  funext v
  show (Matrix.of (m v))⁻¹ * (Matrix.of (m v) * Matrix.of (x v)) = x v
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm v), Matrix.one_mul]
  rfl

theorem pointwiseInv_pointwiseInv {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det) :
    invP (invP m) = m := by
  funext v
  show ((Matrix.of (m v))⁻¹)⁻¹ = m v
  rw [Matrix.nonsing_inv_nonsing_inv _ (hm v)]
  rfl

theorem measure_le {ι : Type} [Fintype ι] {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)) (hΓ : Γ.Countable) (hR : μ Rᶜ = 0)
    (hinv : ∀ m ∈ Γ, invP m ∈ Γ) (hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det)
    (hpres : ∀ m ∈ Γ, μ.map (fun x => mulP m x) = μ)
    (h₁ : IsFund Γ R Ω₁) (h₂ : IsFund Γ R Ω₂) : μ Ω₁ ≤ μ Ω₂ := by
  haveI : Countable Γ := hΓ.to_subtype
  have e1 := measure_eq_tsum μ R Γ Ω₂ Ω₁ hR h₂.1 h₁.1 h₂.2
  have e2 := measure_eq_tsum μ R Γ Ω₁ Ω₂ hR h₁.1 h₂.1 h₁.2
  have hterm : ∀ a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₂ ∩ Ω₁) =
      μ ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) := by
    intro a
    have hs : MeasurableSet ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) :=
      (measurable_mulP _ h₁.1).inter h₂.1
    conv_rhs => rw [← hpres a a.2, Measure.map_apply (measurable_mulP _) hs]
    congr 1
    ext x
    show (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂ ∧ x ∈ Ω₁) ↔
      (mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ∈ Ω₁ ∧ mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂)
    rw [mulP_invP_mulP _ (hu a a.2)]
    exact And.comm
  let f : Γ → Γ := fun a => ⟨invP a, hinv a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h' : invP (a : ι → Formalism.QuantumDeterminants.Mt k r) = invP b := congrArg Subtype.val hab
    apply Subtype.ext
    rw [← pointwiseInv_pointwiseInv _ (hu a a.2), ← pointwiseInv_pointwiseInv _ (hu b b.2), h']
  rw [e1, e2, tsum_congr hterm]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun b : Γ => μ ((fun x => mulP (b : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₁ ∩ Ω₂))

theorem measure_eq : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  intro ι _ k r Γ Ω₁ Ω₂ hΓ _ _ hinv hN h₁ h₂
  have hH := GlobalTheory.Amp.NHaar.isHaarOn_lebN k r
  haveI : SigmaFinite (GlobalTheory.Amp.lebN k r) := hH.1
  have hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det := fun m hm v =>
    GlobalTheory.DegVol.RealMat.isUnit_det (hN m hm v).1
  have hnull : Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) (GlobalTheory.DegVol.RP k r (fun _ => 1))ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v : ι, Function.eval v ⁻¹' {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ hH.2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    refine Set.mem_iUnion.2 ⟨v, ?_⟩
    intro hxN
    apply hv'
    refine ⟨hxN, ?_⟩
    simpa using hxN
  have hpres : ∀ m ∈ Γ, (Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r).map (fun x => mulP m x) =
      Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r := fun m hm => by
    have e : ∀ v, (GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) = GlobalTheory.Amp.lebN k r :=
      fun v => hH.2.2.2 _ (hN m hm v)
    haveI : ∀ v, SigmaFinite ((GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v)))) := fun v => by
      rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => GlobalTheory.Amp.lebN k r)
      (f := fun v => Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  exact le_antisymm
    (measure_le _ _ Γ Ω₁ Ω₂ hΓ hnull hinv hu hpres h₁ h₂)
    (measure_le _ _ Γ Ω₂ Ω₁ hΓ hnull hinv hu hpres h₂ h₁)

end GlobalTheory.FundEq
end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frames_same_gram_differ_by_skew_solution : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∀ F₁ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∀ F₂ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, (∀ b, ∃ w, IsWcomp D P (frame F₁ b) w ∧ IsWcomp D P (frame F₂ b) w) → ∃ x : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E, (∀ b, frame F₂ b = frame F₁ b + ∑ a, x a b • F0.e a) ∧ (∀ a b, x a b ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ xᴴ * Z.submatrix Fin.castSucc id + (Z.submatrix Fin.castSucc id)ᴴ * x = 0 := by
  first | exact @GlobalTheory.LoopC.FrameDiff.frame_diff | exact GlobalTheory.LoopC.FrameDiff.frame_diff | (intros; apply GlobalTheory.LoopC.FrameDiff.frame_diff <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linear_forms_bounded_representatives : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ M0 : LatW D, IsPrimitiveSub M0 (L0X D Λ (lf D F0)) → ∃ reps : Finset (M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (reps.card : ℝ) ≤ NT D u ^ 2 ∧ ∀ ψ : M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ reps, ∃ v ∈ L0X D Λ (lf D F0), ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v x := by
  first | exact @GlobalTheory.LoopC.FunIdx.funIdx | exact GlobalTheory.LoopC.FunIdx.funIdx | (intros; apply GlobalTheory.LoopC.FunIdx.funIdx <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.perpendicular_rank_ideal_bound : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s Q → rkW D (perpW D (L0X D Λ (lf D F0)) P) = s ∧ ∃ I : Ideal (𝓞 D.host.E), I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Q ^ 2 * NT D u ^ 2 ∧ I • dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P) ≤ perpW D (L0X D Λ (lf D F0)) P := by
  first | exact @GlobalTheory.LoopC.PerpDisc.main | exact GlobalTheory.LoopC.PerpDisc.main | (intros; apply GlobalTheory.LoopC.PerpDisc.main <;> assumption)
end
