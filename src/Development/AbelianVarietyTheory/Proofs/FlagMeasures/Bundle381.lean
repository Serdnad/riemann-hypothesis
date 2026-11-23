module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDatumOfTermInMovedLatticeOrbit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle367
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle373
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (d : LocNG.Datum (FP p)), Over (FP p) d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')) → ∀ δ : G.Dat, δ p = (c.c p).dat d → ∃ h ∈ (G.S p).H0, h • δ p = G.datOf (c.lat ρ t₀.lam) p := by
  first | exact @GlobalTheory.HL.TermOrbit.datum_in_orbit | exact GlobalTheory.HL.TermOrbit.datum_in_orbit | (intros; apply GlobalTheory.HL.TermOrbit.datum_in_orbit <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r), ∀ n ∈ Fr.N, Tri E Fr.f (fun b => n (Fr.f b)) := by
  first | exact @GlobalTheory.NFrameTri.tri_of_mem_N | exact GlobalTheory.NFrameTri.tri_of_mem_N | (intros; apply GlobalTheory.NFrameTri.tri_of_mem_N <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g) (hg' : Tri E f' g') (l : ℕ), H.Dl g g' l = H.Dl f f' l := by
  first | exact @GlobalTheory.MinorTri.Dl_eq_of_tri | exact GlobalTheory.MinorTri.Dl_eq_of_tri | (intros; apply GlobalTheory.MinorTri.Dl_eq_of_tri <;> assumption)
end

section

noncomputable section
open scoped Classical Pointwise
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm

namespace GlobalTheory.TypeAsm.LatticeOrthogonalComplement

section Gen
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : HermSpace K V} {HW : HermSpace K W} {r : ℕ}

theorem B_swap {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem X_B_e (F : FlagD H r) (a : Fin (r + 1)) (x : V) (hx : x ∈ F.X) : H.B x (F.e a) = 0 := by
  have key : ∀ b : Fin r, H.B (F.e b.castSucc) (F.e a) = 0 := by
    intro b
    induction a using Fin.lastCases with
    | last => exact F.zperp b
    | cast c => exact F.iso b c
  have : F.X ≤ LinearMap.ker (H.B.flip (F.e a)) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using key b
  simpa using this hx

theorem X_B_perp (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) (x : V) (hx : x ∈ F.X) :
    H.B x v = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip v) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  simpa using this hx

theorem flag_vector_mem_base_lattice (F : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F := by
  unfold V0
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  | cast c => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, c.2, rfl⟩))

theorem mem_wSp (F : FlagD H r) (v : V) : v ∈ wSp F F ↔ ∀ a, H.B (F.e a) v = 0 := by
  rw [wSp, mem_perp_iff]
  constructor
  · intro h a
    exact B_swap (h _ (flag_vector_mem_base_lattice F a))
  · intro h x hx
    apply B_swap
    have : V0 F F ≤ LinearMap.ker (H.B.flip v) := by
      unfold V0
      refine sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)
      · intro y hy; simpa using X_B_perp F h y hy
      · intro y hy; simpa using X_B_perp F h y hy
      · rintro _ (rfl | rfl) <;> simpa [FlagD.z] using h (Fin.last r)
    simpa using this hx

theorem mem_perp_lattice_flag_iff (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (v : V) :
    v ∈ flagPairDefinitePartLattice F F Λ ↔ v ∈ Λ ⊔ rs (𝓞 K) F.X ∧ v ∈ wSp F F := by
  simp only [flagPairDefinitePartLattice, latL, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rw [uPerp, mem_perp_iff]
    rw [wSp, mem_perp_iff] at h2
    exact fun x hx => h2 x ((le_sup_left : F.X ⊔ F.X ≤ V0 F F) hx)

variable {F : FlagD H r} {e : W →ₗ[K] V}

theorem e_perp (hE : IsEmb F HW e) (w : W) (a : Fin (r + 1)) : H.B (F.e a) (e w) = 0 :=
  (hE.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩) a

theorem e_wSp (hE : IsEmb F HW e) (w : W) : e w ∈ wSp F F := (mem_wSp F _).2 (e_perp hE w)

theorem X_wSp (x : V) (hx : x ∈ F.X) : x ∈ wSp F F :=
  (mem_wSp F _).2 fun a => B_swap (X_B_e F a x hx)

theorem decomp (hE : IsEmb F HW e) {v : V} (hv : v ∈ wSp F F) : ∃ w, v - e w ∈ F.X := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, h⟩ := Submodule.mem_sup.1 ((hE.2 v).1 ((mem_wSp F v).1 hv))
  exact ⟨w, by rw [← h]; simpa using hz⟩

theorem XB_e (hE : IsEmb F HW e) (x : V) (hx : x ∈ F.X) (w : W) : H.B x (e w) = 0 :=
  X_B_perp F (e_perp hE w) x hx

theorem memL_e (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V) (w : W) :
    e w ∈ flagPairDefinitePartLattice F F Λ ↔ w ∈ lat0 F e Λ :=
  (mem_perp_lattice_flag_iff F Λ _).trans ⟨fun h => h.1, fun h => ⟨h, e_wSp hE w⟩⟩

theorem X_L (Λ : Submodule (𝓞 K) V) (x : V) (hx : x ∈ F.X) : x ∈ flagPairDefinitePartLattice F F Λ :=
  (mem_perp_lattice_flag_iff F Λ x).2 ⟨Submodule.mem_sup_right hx, X_wSp x hx⟩

theorem quotEquiv (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V)
    (hspan : Submodule.span K (flagPairDefinitePartLattice F F Λ : Set V) = wSp F F) :
    Nonempty ((↥(Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)) ⧸
        (lat0 F e Λ).comap (Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)).subtype) ≃ₗ[𝓞 K]
      (↥(dual H (flagPairDefinitePartLattice F F Λ)) ⧸ (flagPairDefinitePartLattice F F Λ).comap (dual H (flagPairDefinitePartLattice F F Λ)).subtype)) := by
  set L := flagPairDefinitePartLattice F F Λ with hL
  set M := lat0 F e Λ with hM
  set DW := Formalism.HermitianLatticesTheory.dual HW.B.flip M with hDW
  set DV := dual H L with hDV
  have hmemW : ∀ w, w ∈ DW ↔ ∀ y ∈ M, HW.B w y ∈ (1 : Submodule (𝓞 K) K) := fun w => by
    rw [hDW, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    simp only [LinearMap.flip_apply]
  have hin : ∀ w : DW, e w ∈ DV := by
    rintro ⟨w, hw⟩
    rw [hDV, mem_dual_iff, hspan]
    refine ⟨e_wSp hE w, fun x hx => ?_⟩
    obtain ⟨w', hw'⟩ := decomp hE ((mem_perp_lattice_flag_iff F Λ x).1 hx).2
    have hw'M : w' ∈ M := (memL_e hE Λ w').1 (by simpa using L.sub_mem hx (X_L Λ _ hw'))
    have h1 : H.B (e w) x = HW.B w w' := by
      have e1 : x = e w' + (x - e w') := by abel
      rw [e1, map_add (f := _), B_swap (XB_e hE _ hw' w), add_zero, hE.1]
    rw [h1]
    exact (hmemW w).1 hw w' hw'M
  let f : DW →ₗ[𝓞 K] DV :=
    LinearMap.codRestrict DV ((e.restrictScalars (𝓞 K)).comp DW.subtype) (fun w => hin w)
  let Φ := (L.comap DV.subtype).mkQ ∘ₗ f
  have hker : LinearMap.ker Φ = M.comap DW.subtype := by
    ext w
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    exact memL_e hE Λ w
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hv' := (mem_dual_iff H L v).1 hv
    rw [hspan] at hv'
    obtain ⟨w, hw⟩ := decomp hE hv'.1
    have hwD : w ∈ DW := (hmemW w).2 fun y hy => by
      have h1 : HW.B w y = H.B v (e y) := by
        rw [← hE.1]
        have e1 : v = e w + (v - e w) := by abel
        conv_rhs => rw [e1]
        rw [map_add (f := _), LinearMap.add_apply, XB_e hE (v - e w) hw y, add_zero]
      rw [h1]
      exact hv'.2 _ ((memL_e hE Λ y).2 hy)
    refine ⟨⟨w, hwD⟩, ?_⟩
    show Submodule.Quotient.mk (f ⟨w, hwD⟩) = Submodule.Quotient.mk ⟨v, hv⟩
    rw [Submodule.Quotient.eq]
    show e w - v ∈ L
    have := L.neg_mem (X_L Λ _ hw)
    simpa using this
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩

end Gen

end GlobalTheory.TypeAsm.LatticeOrthogonalComplement

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm
open LatticeOrthogonalComplement
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lat0C : LatticeNormalizationCondition := by
  intro D large₂ X Y u hS W HW hE Λ hΛ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', -, hT, -, hTerm, -, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS Λ (Or.inl hΛ)
  have hg1 : 1 ≤ gS D := by omega
  obtain ⟨-, -, -, hLat, -, hNe⟩ := GlobalTheory.DegCnt.PrimPerp.main _ _ (HV D) hCM D.R.rS N (gS D) Λ hg1 hTerm
  rw [hF, hF'] at hLat hNe
  rw [hT] at hNe
  have hAd : Adapt (F0 X u) (F0 X u) N.𝔡 N := by
    have := adapt_self N
    rwa [hF, hF'] at this
  obtain ⟨⟨hInt, -⟩, -⟩ := GlobalTheory.DegAsm.isDat_datOf _ _ _ (HV D) HW W.subtype hCM D.R.rS (F0 X u) (F0 X u) N.𝔡 N
    (gS D) Λ hg1 hE hAd hTerm
  have hd : (datOf (F0 X u) (F0 X u) W.subtype (gS D) Λ).1 = lat0 (F0 X u) W.subtype Λ := by
    ext w
    change W.subtype w ∈ flagPairDefinitePartLattice (F0 X u) (F0 X u) Λ ⊔ rs _ (F0 X u).X ↔ w ∈ lat0 (F0 X u) W.subtype Λ
    rw [sup_eq_left.2 (fun x hx => X_L Λ x hx), memL_e hE Λ]
  refine ⟨hd ▸ hInt, ?_⟩
  obtain ⟨q⟩ := quotEquiv hE Λ hLat.2
  obtain ⟨i⟩ := hNe
  exact ⟨q.trans i⟩

end GlobalTheory.TypeAsm
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPlaces_frameMatrix_eq_rational_of_rational : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ (s : X.B.I.Ginf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), (∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * γ₀.map (X.B.I.φ v) * X.B.I.P v) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → sTil X wt s = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) := by
  first | exact @GlobalTheory.St.sTil_eq_atInf_of_rational | exact GlobalTheory.St.sTil_eq_atInf_of_rational | (intros; apply GlobalTheory.St.sTil_eq_atInf_of_rational <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  first | exact @GlobalTheory.St.CFrame.frame_of_type | exact GlobalTheory.St.CFrame.frame_of_type | (intros; apply GlobalTheory.St.CFrame.frame_of_type <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a)) → ∃ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) := by
  first | exact @GlobalTheory.frame_action_mulEquiv | exact GlobalTheory.frame_action_mulEquiv | (intros; apply GlobalTheory.frame_action_mulEquiv <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ}

theorem one_memG : (1 : Mat k r) ∈ GG k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem mul_memG {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) : x * y ∈ GG k r := by
  show (x * y)ᴴ * Hpk k r * (x * y) = Hpk k r
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  calc (x * y)ᴴ * Hpk k r * (x * y) = yᴴ * (xᴴ * Hpk k r * x) * y := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hx', hy']

section Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u u' : H} (hu : IsSmoothVec σ u) (hu' : IsSmoothVec σ u') :
    IsSmoothVec σ (u + u') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  obtain ⟨U', F', hU', hg', hF', hFe'⟩ := hu' g₀ hg₀
  refine ⟨U ∩ U', F + F', hU.inter hU', ⟨hg, hg'⟩, (hF.mono Set.inter_subset_left).add
    (hF'.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  have e1 := hFe g hg.1 hgH
  have e2 := hFe' g hg.2 hgH
  simp only at e1 e2
  simp only [map_add (f := _), Pi.add_apply, e1, e2]

theorem smooth_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u : H} (b : ℂ) (hu : IsSmoothVec σ u) :
    IsSmoothVec σ (b • u) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  refine ⟨U, b • F, hU, hg, hF.const_smul b, fun g hg hgH => ?_⟩
  have e1 := hFe g hg hgH
  simp only at e1
  simp only [map_smul, Pi.smul_apply, e1]

end Sm

theorem ae_rtrans {B : Type*} {μG : Measure (Mt k r)} (hU : IsUnimod (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (Matrix.of x * y)) =ᵐ[μG] fun x => g (Matrix.of x * y) := by
  have hmp : MeasurePreserving (rmulM y : Mt k r → Mt k r) μG μG :=
    ⟨(continuous_rmulM y).measurable, hU.1 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

theorem ae_ltrans {B : Type*} {μG : Measure (Mt k r)} (hH : IsHaarOn (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (y * Matrix.of x)) =ᵐ[μG] fun x => g (y * Matrix.of x) := by
  have hc : Continuous (lmulM y : Mt k r → Mt k r) :=
    (continuous_const (y := y)).matrix_mul (continuous_id (X := Mat k r))
  have hmp : MeasurePreserving (lmulM y : Mt k r → Mt k r) μG μG :=
    ⟨hc.measurable, hH.2.2.2 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

end GlobalTheory.SgInf.BesselExt

open GlobalTheory.SgInf.BesselExt in
theorem GlobalTheory.SgInf.exists_besselExt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ l : H → Wp, IsBesselMapSm z (psiGen k r z c) σ π l ∧ ∀ u ∈ DD σ w, l u = be (psiGen k r z c) π μS σ u v ξ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hw v hv ξ
  obtain ⟨T, hTD, hadd, hsmul, hloc, hR, hL⟩ := GlobalTheory.T.besselMatrixCoeff_extends_bounded_equivariant k r σ w a μG d z c π μS hStd hSide v hv ξ
  have hrep : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hUni : IsUnimod (GG k r) μG := GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar
  have hDDi := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hrep
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1
  obtain ⟨C, Ws, hWs, hreg⟩ := GlobalTheory.T.boundedEquivariantMap_smooth_continuous_seminorm_bound k r σ μG T hrep hHaar hadd hsmul hloc hR
  classical
  let F : H → Mat k r → Wp := fun u => if h : IsSmoothVec σ u then (hreg u h).choose else 0
  have hF : ∀ u, IsSmoothVec σ u → ContinuousOn (F u) (GG k r) ∧
      (fun x : Mt k r => F u (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧
      ‖F u 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
    intro u hu
    have := (hreg u hu).choose_spec
    simp only [F, dif_pos hu]
    exact this
  have hDDsm : ∀ u ∈ DD σ w, IsSmoothVec σ u := fun u hu => (hDDi.2.2.2.2 hw).1 u (hDDi.2.2.1 hu)
  refine ⟨fun u => F u 1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu u' hu'
    have hs := smooth_add hu hu'
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (u + u')) (fun x => F u x + F u' x) hHaar (hF _ hs).1
      ((hF u hu).1.add (hF u' hu').1) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hadd u u', (hF u hu).2.1, (hF u' hu').2.1] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  · intro b u hu
    have hs := smooth_smul b hu
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (b • u)) (fun x => b • F u x) hHaar (hF _ hs).1
      ((hF u hu).1.const_smul b) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hsmul b u, (hF u hu).2.1] with x h1 h2 h3
    rw [h1, h2, h3]
  · intro h hh m hm u hu
    have hhG : h ∈ GG k r := hh.1
    have hmG : m ∈ GG k r := hm.1
    have htG : h * m ∈ GG k r := mul_memG hhG hmG
    have htS : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
    have hsu : IsSmoothVec σ (σ (h * m) u) := ((hDDi.2.2.2.1 u hu).1 _ htG)

    have h1 : ∀ x ∈ GG k r, F (σ (h * m) u) x = F u (x * (h * m)) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG _ _ hHaar (hF _ hsu).1 ?_ ?_
      · exact (hF u hu).1.comp ((continuous_id.mul continuous_const).continuousOn)
          (fun x hx => mul_memG hx htG)
      · filter_upwards [(hF _ hsu).2.1, hR _ htG u, ae_rtrans hUni htG (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]

    have h2 : ∀ x ∈ GG k r, F u ((h * m) * x) = PiS (psiGen k r z c) π (h * m) (F u x) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (fun x => F u ((h * m) * x)) (fun x => PiS (psiGen k r z c) π (h * m) (F u x))
        hHaar ?_ ?_ ?_
      · exact (hF u hu).1.comp ((continuous_const.mul continuous_id).continuousOn)
          (fun x hx => mul_memG htG hx)
      · exact (PiS (psiGen k r z c) π (h * m)).continuous.comp_continuousOn (hF u hu).1
      · filter_upwards [ae_ltrans hHaar htG (hF u hu).2.1, hL _ htS u, (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]
    show F (σ (h * m) u) 1 = psiGen k r z c m • π h (F u 1)
    rw [h1 1 one_memG, Matrix.one_mul, ← Matrix.mul_one (h * m), h2 1 one_memG, (hPi.1 h hh m hm).2]
    rfl
  · refine ⟨C, Ws, hWs, fun u hu => (hF u hu).2.2⟩
  · intro u hu
    have hsu := hDDsm u hu
    have hcont : ContinuousOn (Afun (psiGen k r z c) π μS σ u v ξ) (GG k r) := by
      have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hDDi.1 hStd.2.2.2.2.2.2.2.1 u hu v hv
      exact (ContinuousLinearMap.apply ℂ Wp ξ).continuous.comp_continuousOn hD1.2.2.2
    have := GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F u) _ hHaar (hF u hsu).1 hcont
      (by rw [← hTD u hu]; exact (hF u hsu).2.1) 1 one_memG
    show F u 1 = _
    rw [this]
    simp only [Afun, hrep.1.1, ContinuousLinearMap.one_apply]
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.productMoment_firstLengths_lowestVector : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  first | exact @GlobalTheory.MomProdGap.product_moment_first_gap | exact GlobalTheory.MomProdGap.product_moment_first_gap | (intros; apply GlobalTheory.MomProdGap.product_moment_first_gap <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_row_of_unimodular_lattice_primitive_vector : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  first | exact @GlobalTheory.RowsOrb.exists_row_of_unimod | exact GlobalTheory.RowsOrb.exists_row_of_unimod | (intros; apply GlobalTheory.RowsOrb.exists_row_of_unimod <;> assumption)
end
