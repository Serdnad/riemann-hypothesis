module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle306
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle059
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle408
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedMeasureEqProdBesselRootMeasures
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle442
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle443
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle042
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.RepIndep

open GlobalTheory.LoopC.PairMove GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem xsp_map_of_frame {F₁ F₂ : LFlag S r T'} (f : S.V ≃ₗ[E] S.V) (h : ∀ a, frame F₂ a = f (frame F₁ a)) :
    (Xsp F₁).map (f : S.V →ₗ[E] S.V) = Xsp F₂ := by
  change (Submodule.span E (Set.range F₁.fl.e)).map _ = Submodule.span E (Set.range F₂.fl.e)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  have : (f : S.V →ₗ[E] S.V) ∘ F₁.fl.e = F₂.fl.e := by
    funext b
    have := h b.castSucc
    rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td] at this
    simp [this]
  rw [this]

theorem iota_of_dc {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (g : ℕ)
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = (n * m) (frame F₁ a)) :
    IotaCompat Λ F F₁ F₂ (n * m) g := by
  have hmX : (Xsp F₁).map (m : S.V →ₗ[E] S.V) = Xsp F₁ := nlam_map hm
  have hnmX := xsp_map_of_frame (n * m) hfr
  have hnX : (Xsp F₁).map (n : S.V →ₗ[E] S.V) = Xsp F₂ := by
    refine map_of_mem_iff fun x => ?_
    have e : n x = (n * m) (m.symm x) := by simp [LinearEquiv.mul_apply]
    rw [e, mem_iff_of_map hnmX, mem_iff_of_map (map_symm hmX)]
  have hi : n⁻¹ ∈ NLam Λ F := Formalism.L2.SG.Pf.nlamPf_inv hn
  intro x' hx' l hl
  have e : l - (n * m) x' = n (n⁻¹ l - m x') := by
    rw [map_sub]
    simp [LinearEquiv.mul_apply]
  rw [e, ngx_iff hn.1 (nlam_map hn) hnX g]
  have e2 : n⁻¹ l - m x' = (l - x') + ((n⁻¹ l - l) - (m x' - x')) := by abel
  rw [e2]
  refine (Submodule.add_mem_iff_left _ ?_).symm
  refine Submodule.sub_mem _ ?_ ?_
  · refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨?_, hi.2.2 l hl.2⟩)
    exact Λ.sub_mem ((aut_mem_iff hi.1 l).2 hl.1) hl.1
  · refine Submodule.mem_sup_right ⟨?_, hm.2.2 x' hx'.2⟩
    exact Λ.sub_mem ((aut_mem_iff hm.1 x').2 hx'.1) hx'.1

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rep_indep : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → DCRel Λ (lf D F0) F₁ F₂ → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) ↔ Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hΛ F₁ F₂ h1 h2 hG hdc p P hP d
  have key : ∀ A B : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' A → PD D Λ (lf D F0) u' B →
      Gval (lf D F0) A ≠ 0 → DCRel Λ (lf D F0) A B →
      Over P d (locU Z p Λ (lf D F0) A (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) B (Tu D u) (Tu D u')) := by
    intro A B hA hB hGA hAB
    obtain ⟨n, hn, m, hm, hfr, -⟩ := hAB
    exact GlobalTheory.T.global_terms_same_doubleCoset_same_local_data D Z u u' F0 Λ hΛ A B hA hB hGA n ⟨hn.1.1, hn.2.1, hn.2.2⟩ m ⟨hm.1.1, hm.2.1, hm.2.2⟩
      (Formalism.L2.SG.Pf.isAutLam_mul hn.1 hm.1).2 (fun a => hfr a) (iota_of_dc (gS D) hn hm (fun a => hfr a)) p P hP d
  refine ⟨key F₁ F₂ h1 h2 hG hdc, key F₂ F₁ h2 h1 ?_ (Formalism.L2.SG.Pf.dcrel_symm _ _ hdc)⟩
  rw [Formalism.L2.SG.Pf.gval_rel (h := hdc)]
  exact hG

end GlobalTheory.LocOver.RepIndep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open scoped TensorProduct

namespace GlobalTheory.LabPinAt

theorem mult_lev_left {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    (∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g) ∧ ∀ v, ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨hx.lev, fun v γ hγ g => (hx.aut v).left γ hγ g⟩
  | zero => exact ⟨fun v k _ g => by simp, fun v γ _ g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 v k hk g, hy.1 v k hk g]; ring
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2 v γ hγ g, hy.2 v γ hγ g]
  | smul c x _ hx =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 v k hk g]; ring
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2 v γ hγ g]

end GlobalTheory.LabPinAt

theorem GlobalTheory.LabPinAt.labTie_at : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (F : Face D A), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ y, ι (D.sEE y) = conjHH X G (j y)) → RowJ R eE X h G t j → LevelMatchA R F X h t → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → TypeLab D rep → GoodFTAll D → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep F hPsi hE hι hRJ hLev hIso hTL hGood
  have hM : ∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ Mult R.θ (R.MY 0) (JR R F) (chiR R F) := fun σ => (hIso σ).1.1
  refine GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries D X h t PY hF G' Pl0 T A Ks R eE G j ι rep (Minf R.θ PY (R.MY 0)) hPsi hE hι hRJ
    (fun σ => (hIso σ).2) ?_ ?_ hTL (fun σ => hGood (D.what₂.ft σ))
  · intro σ k hk v y
    obtain ⟨hk2, hc⟩ := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
    obtain ⟨hJ, hχ⟩ := hLev k hk2
    rw [(GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).1 v _ hJ y, show chiR R F (kap X h t k) = star (X.chi2 k) from hχ, hc,
      star_one, one_mul]
  · intro σ v γ hγ y
    exact (GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).2 v γ hγ y
end

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm

theorem locDatC_of_besselOfW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) : LocDatC := by
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  intro D X hne hG hT
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  refine ⟨C, hB, Formalism.L2.SG.Pf.LocF.locFactor_holds hG C, fun u τ => ⟨?_, ?_⟩⟩
  · exact goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  · exact goodS_of _ u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT _ u u τ)

end GlobalTheory.TypeAsm
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.DatEq

theorem row_eq_iff_datOf_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hA := GlobalTheory.T.doubleCoset_terms_same_innerLattices D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hI := GlobalTheory.T.identificationCompat_iff_localGraphs D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hD := Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t₀ t hl.symm hl'.symm
  have hrow : ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) ↔
      iotaOf Y.TR (Y.cs u) (Y.cs u') t₀ = iotaOf Y.TR (Y.cs u) (Y.cs u') t := by
    show ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t) : Rw _ _ Y.TR) =
        (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t₀) ↔ _
    constructor
    · intro h
      exact (congrArg (fun r => r.2.2) h).symm
    · intro h
      rw [h]
      ext <;> simp [hl, hl']
  rw [hrow, hD, hI]
  constructor
  · intro h
    funext p
    exact Prod.ext (hA p).1 (Prod.ext (hA p).2 (h p))
  · intro h p
    exact congrArg (fun d => (d p).2.2) h

end GlobalTheory.HL.DatEq
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.automorphismCovolume_eq_latticeMass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  first | exact @GlobalTheory.CovMass.covol_eq_mass | exact GlobalTheory.CovMass.covol_eq_mass | (intros; apply GlobalTheory.CovMass.covol_eq_mass <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (μR : Measure X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR s w μR → ∃ μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), μR = Measure.pi μl ∧ (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset s) μR ∧ ∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ)))))) := by
  first | exact @GlobalTheory.Amp.PinRoot.pinned_root | exact GlobalTheory.Amp.PinRoot.pinned_root | (intros; apply GlobalTheory.Amp.PinRoot.pinned_root <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stabiliserCovolume_le_rootCoordinateCover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  first | exact @GlobalTheory.LoopVol.covolume_le_cover | exact GlobalTheory.LoopVol.covolume_le_cover | (intros; apply GlobalTheory.LoopVol.covolume_le_cover <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  first | exact @GlobalTheory.AmpLoc.hsNormSq_amp_loc | exact GlobalTheory.AmpLoc.hsNormSq_amp_loc | (intros; apply GlobalTheory.AmpLoc.hsNormSq_amp_loc <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section
namespace GlobalTheory.MuSPi

theorem muNH_prod_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  intro D X θ C u κN κH hN hH
  have hsN : ∀ v, SigmaFinite (muNl C (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ _ rfl; exact sf_muNl C τ (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ)
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsH : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsM : ∀ v, SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl; exact (invOn_mulMap C u τ).1
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul _ (measurable_mul.aemeasurable)]
  congr 1
  have mp := Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurePreserving_piProd (fun v => muNl C (X.pl v) v) (fun v => muHl C u (X.pl v) v)
  rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
    mp.measurable]
  haveI : ∀ v, SigmaFinite (((muNl C (X.pl v) v).prod (muHl C u (X.pl v) v)).map
      (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hsM
  exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
    (fun v => measurable_mul.aemeasurable)

end GlobalTheory.MuSPi
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.MuHPi

theorem hloc_eq_HGv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.Pf.WuDec.Hloc X u v =
      (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) := by
  rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]
  rfl

theorem muH_eq_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muHl C u (X.pl v) v) (Formalism.L2.SG.Pf.WuDec.Hloc X u v) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muHl C u τ w) (Formalism.L2.SG.Pf.WuDec.Hloc X u w) := by
      rintro τ _ rfl; exact invOn_muHl C u τ
    intro v
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_coe] at hc hi
  refine Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG X u)
    (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG, Subgroup.coe_pi]
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_conc _ _ fun v => by rw [← hloc_eq_HGv]; exact (hloc v).2.2.1
  · intro g hg
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v)
      (by rw [hloc_eq_HGv]; exact hg v (Set.mem_univ v))
  · exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuHPi
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory.MuNPi

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem muN_eq_pi_muNl : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muNl C (X.pl v) v) (NGv X u v : Set _) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muNl C τ w) (NGv X u w : Set _) := by
      rintro τ _ rfl
      exact invOn_muNl C u τ
    exact fun v => h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muNl C (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  rw [← NinfG_coe] at hc hi
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [NinfG, Subgroup.coe_pi]
    exact PiM.pi_conc _ _ fun v => (hloc v).2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · exact PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuNPi
end
