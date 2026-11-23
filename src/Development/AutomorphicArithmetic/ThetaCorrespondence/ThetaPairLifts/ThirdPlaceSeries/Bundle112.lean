module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.WtShape
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem wtN_z : _root_.GlobalTheory.CovTop.LiftWeightNumerator := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)
end GlobalTheory.CovTop.WtShape
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.StepConst
variable {D : D7}
theorem cI_mul_idx_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → ∀ j, j < D.R.m → (f.t t).cI j * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = (f.t W.P.A3.A.μ0).cI j := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ hRow v hv hVT t w F hPins hQL j hj
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := W.Q.charW.base.lev
  have hQ0 := base_empty hL
  obtain ⟨pl, hpl⟩ := hQL.places
  have hq : ∀ i, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (F.Q i).q.v → PP' = (pl i).1 := fun i PP' h e => by
    have e1 := (hpl (pl.symm ⟨PP', h⟩)).2
    rw [Equiv.apply_symm_apply] at e1
    have e2 : pl.symm ⟨PP', h⟩ = i := hPins.inj (e1.trans e)
    rw [← e2, Equiv.apply_symm_apply]
  have hg : ∀ i, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (F.Q i).q.v := fun i PP' h => by
    rw [(hpl i).2]
    exact under_ne hL t (pl i).2 h
  have hgP : ∀ i, (F.Q i).q.v ∉ v.gP := fun i h => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP _).1 h
    exact hg i PP h1 h2.symm
  have hP : ∀ PP : Pl D.host.E, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 → ¬ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ w.Q := by
    rintro PP (h | h) h'
    · obtain ⟨i, hi⟩ := (hPins.places _).1 h'
      exact hg i PP h hi.symm
    · rw [hQ0] at h
      exact absurd h (Finset.notMem_empty _)
  have key : GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j * ∏ i, ((F.Q i).idx (j + 1) : ℝ) = GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g W.P.A3.A.μ0 j := by
    unfold GlobalTheory.Fam.volLev
    split_ifs with h1
    · generalize j + 1 = J at h1
      have hb : f.g.b J ∈ GfC (Yc D J) := by rw [← hVT.b J]; exact hv.b J
      have hΛ : ((_root_.GlobalTheory.Fam.pk_z W).ΛY J).FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY J h1)).1.fg
      have hβ : IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).ΛY J) := (hL.βY J h1).choose_spec.1
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := Yc D J) (N := v.N J) (P := (· ∈ w.Q)) hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 J (_root_.GlobalTheory.Fam.pk_z W).triv) hP hb
        (hVT.moves J h1 _ fun p hp => by
          obtain ⟨i, rfl⟩ := (hPins.places _).1 hp
          exact hgP i)
      have loc : ∀ i d hd (g : GA D (Yc D J)), finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY J) → ∀ x,
          (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY J d hd).β * x.val * ((F.Q i).FY J d hd).γ →
          (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY J) (pl i).1 (finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ ((F.Q i).T.lev J d hd).J) := fun i d hd g hS x hx => by
        refine red_iff_local (N := v.N J) (F.Q i).q ((F.Q i).FY J d hd) _ hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.complexLevelStructure W)) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hVT.moves J h1 _ fun p hp => hp ▸ hgP i) ((F.Q i).latY J d hd) (fun y hy c hc => ?_) hS hx
        obtain ⟨gl, -, -, hu⟩ := GlobalTheory.LocEmb.exists_gl D _ (F.Q i).q (Yc D J) _ ((F.Q i).FY J d hd)
        have e : c = (F.Q i).gl J d hd y :=
          (hu c y hc.1 hc.2).trans (hu _ y ((F.Q i).gl_loc J d hd y).1 ((F.Q i).gl_loc J d hd y).2).symm
        rw [e]
        exact (hQL.mid i J d hd h1 y hy).1
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).1 J h1 (hv.sd J h1) (f.g.μf J) (hRow.meas.μf J) _
        (moved (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.pk_z W).triv))) (f.g.b J) hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i d hd x hx => (loc i d hd g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          have hs := (F.Q i).hs
          have hd : J + ((F.Q i).s + 1 - J) = (F.Q i).s + 1 := by omega
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q ((F.Q i).FY J _ hd) g
          have := (loc i _ hd g hS x hx).2 (H i _ hd x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.pk_z W).triv))
      have e2 := moved_set (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 J (_root_.GlobalTheory.Fam.pk_z W).triv))
      rw [e1, e2] at hA
      exact hA
    · have hjm : j + 1 = D.R.m := by omega
      rw [hjm]
      have hb : f.g.bT ∈ GfC D.sp.X' := by rw [← hVT.bT.1]; exact hv.bT
      have hΛ : (_root_.GlobalTheory.Fam.pk_z W).ΛX.FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX).1.fg
      have hβ : IsFrame (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX := hL.βX.choose_spec.1
      have hm : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX v.NT P := fun P => by
        rw [hVT.bT.2]
        exact hVT.movesT P
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := D.sp.X') (N := v.NT) (P := (· ∈ w.Q)) hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datXt W.P.A3.A.μ0) hP hb (hm _)
      have loc : ∀ i (g : GA D D.sp.X'), finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT) ∈ St (_root_.GlobalTheory.Fam.pk_z W).βX → ∀ x : GL (F.Q i).Z (F.Q i).k,
          (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ →
          (redFn (_root_.GlobalTheory.Fam.pk_z W).βX (pl i).1 (finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ (F.Q i).T.levTop.J) := fun i g hS x hx =>
        red_iff_local (N := v.NT) (F.Q i).q (F.Q i).FT _ hβ hΛ (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hm _) (F.Q i).latT (hQL.top i) hS hx
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).2 hv.sdT (fun i => (F.Q i).openT) f.g.μT hRow.meas.μT _
        (moved f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))) f.g.bT hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i x hx => (loc i g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q (F.Q i).FT g
          have := (loc i g hS x hx).2 (H i x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))
      have e2 := moved_set f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt W.P.A3.A.μ0))
      rw [e1, e2] at hA
      exact hA
  show cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t j * _ = cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g W.P.A3.A.μ0 j
  unfold cIOf
  rw [← key]
  push_cast
  ring
end GlobalTheory.StepConst
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.RowLevel
theorem off_lev_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → ∀ j, j < D.R.m → ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → (f.g.b j)⁻¹ * κ * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ∧ levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((f.g.b j)⁻¹ * κ * f.g.b j) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
  have hlev := W.Q.charW.base.lev
  refine conj_mem_off (hlev.βY j hj) (hv.sd j hj) _ ?_ (hV.b j ▸ hv.b j)
    (fun p hp => hV.moves j hj _ fun q hq => hq ▸ hp.1) hκ
  rintro PP (h | h) ho
  · exact ho.1 ((hV.gP _).2 ⟨PP, h, rfl⟩)
  · obtain ⟨e, he⟩ := hQL.places
    obtain ⟨i, hi⟩ := e.surjective ⟨PP, h⟩
    refine ho.2 ((hFP.places _).2 ⟨i, ?_⟩)
    rw [(he i).2, hi]
theorem top_lev_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → ∀ κ, GlobalTheory.FinPl.InK f.c.T v.NT (· ∈ v.tP) κ → f.g.bT⁻¹ * κ * f.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ∧ levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (f.g.bT⁻¹ * κ * f.g.bT) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
  have hlev := W.Q.charW.base.lev
  refine conj_mem_off hlev.βX hv.sdT _ ?_ (hV.bT.1 ▸ hv.bT) (fun p _ => hV.bT.2 ▸ hV.movesT _) hκ
  rintro PP (h | h) ho
  · exact Finset.disjoint_left.1 hv.disj ((hV.gP _).2 ⟨PP, h, rfl⟩) ho
  · have h1 := (hV.tP _).1 ho
    refine (hlev.Q_off t PP h).2 u ?_
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := h1
    rwa [map_natCast] at h2
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc

theorem g_lev_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
    {v : VCom f.c} (hv : v.Is) (hV : _root_.GlobalTheory.Fam.CommutingVectorTie f v) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGP : GPin G)
    (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) (t : W.P.T) (j : ℕ) (hj : j < D.R.m) (k : GA D (Yc D j)) (hk : k ∈ v.JG j) (a : ℂ) (ha : GLam G j k a) :
    (f.g.b j)⁻¹ * k * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ∧
      levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((f.g.b j)⁻¹ * k * f.g.b j) = a := by
  have hlev := W.Q.charW.base.lev
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βY j hj)
  obtain ⟨c0, hfr, -⟩ := hlev.βY j hj
  obtain ⟨hkg, hkJ⟩ := (hGP.lev j hj k).1 hk
  obtain ⟨hkf, hkS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff _ _ k).1 hkg
  obtain ⟨c, hc, x, hxM, rfl⟩ := ha
  have hb : f.g.b j ∈ GfC (Yc D j) := hV.b j ▸ hv.b j
  choose e he hmv using fun i => hGR.frame i j (c i) (hc i)
  choose π h1 h2 h3 h4 using fun i => GlobalTheory.LocMod.LevBack.exists_chart (G i).q (hGR.idem i).1
  have hSt : Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY j) := by
    obtain ⟨h, hloc, hprod⟩ := GlobalTheory.LevelCut.prod_local_parts D f.c v n G hGP j k hkg
    rw [hprod, conj_list_prod, map_list_prod]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    simp only [List.mem_map] at hy
    obtain ⟨_, ⟨i, -, rfl⟩, rfl⟩ := hy
    obtain ⟨xk, hM, hL⟩ := hloc i (c i) (hc i)
    have hJ := hkJ i _ _ _ hM
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) xk hL.2
    obtain ⟨hyK, -⟩ := (GlobalTheory.SymChain.pattern_iter _ _ _ (G i).S (Fin D.R.t) j
      ((typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm xk)).1 hJ
    obtain ⟨Y, hY, -⟩ := GlobalTheory.LocMod.LevBack.exists_int (G i).q (π i) (h2 i) (Yc D j) hΛ hfr (t := f.g.b j) hL.1 (by
      erw [hγ]
      rw [mem_KO, ← map_inv]
      rw [mem_KO] at hyK
      exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
    exact ⟨Y, hY⟩
  have hQ : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = 1 := fun PP hPP => by
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D _ _ _ PP hSt ?_
    have hn : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.gP := fun hm => by
      obtain ⟨PP', hP', e'⟩ := (hV.gP _).1 hm
      obtain ⟨i, hi⟩ := (hlev.Pg PP').1 hP'
      obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hlev.Q_pl t PP hPP
      have g1 := Formalism.IndefR.Fin.g_mem_of_div _ hi
      have g2 : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')).asIdeal := by
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP'.asIdeal
        rwa [map_natCast]
      rw [← e'] at g2
      have g3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := g2
      rw [map_natCast] at g3
      exact Formalism.IndefR.Fin.not_two_primes PP.isPrime.ne_top (D.host.g_prime i) hq (fun h => hqg i h.symm) g3
        (Formalism.IndefR.Fin.char_mem hq hcard)
    rw [map_mul, map_mul, hkS _ hn, mul_one, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨Y, hY⟩ := id hSt
  have hYv : Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y =
      ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹ * Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) * (_root_.GlobalTheory.Fam.pk_z W).βY j := by
    rw [← hY]
    change _ = ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹ * ((_root_.GlobalTheory.Fam.pk_z W).βY j * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y * ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹) * (_root_.GlobalTheory.Fam.pk_z W).βY j
    group
  have hall := fun i => by
    haveI : Nontrivial (kP (pl i).1) := Ideal.Quotient.nontrivial_iff.2 (pl i).1.isPrime.ne_top
    have hs := (G i).hs
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) (x i).1 (hxM i)
    exact red_lam (G i).S (r := D.R.r) (by unfold Ranks.r; omega) (r_le_Y j) (he i) (resS D.host.F (pl i).1)
      ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (h3 i) (h4 i) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (fun c hc z y x' hy hx => chi_eq_mu (_root_.GlobalTheory.Fam.pk_z W).toLevCh hlev (G i).q (pl i).2 (hGR.idem i).1 (π i) (h1 i) (h3 i) (h4 i) c
        (by omega) _ (hGR.mu i (c + 1) (by omega) (by omega)) ((G i).S.tame _) z y x' hy hx) Y
      ⟨(typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm (x i).1, (x i).2⟩ (fun a b => by
        have e1 := congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hγ
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply] at e1
        refine Eq.trans ?_ e1
        exact congrArg (π i) (congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hYv))
  choose hbt x₀ hred hlam using hall
  have hr : ∀ PP, redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = Formalism.UG.bc (resS D.host.F PP) Y :=
    fun PP => by rw [← hY, redFn_frGL]
  obtain ⟨g, hg⟩ : ∃ g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1),
    ∀ PP, g PP = upperLeftBlock (r_le_Y j) (Formalism.UG.bc (resS D.host.F PP.1) Y) := ⟨_, fun _ => rfl⟩
  have hrT : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = g := by
    funext PP
    exact (congrArg (upperLeftBlock (r_le_Y j)) (hr PP.1)).trans (hg PP).symm
  have hR : ∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x₀ i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1 := by
    intro i a b a' b' ha hb z hz
    rw [hg] at hz
    have := hred i a b a' b' ha hb (oToS D.host.F D.host.E z) ((resS_oToS (pl i).1 z).trans hz)
    rwa [show ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
      (ofSplit (G i).q).pr (z : D.host.E) from h1 i (incA D (z : D.host.E))] at this
  have hgH : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hGR.lev g).1.2 fun i => ⟨x₀ i, hR i⟩
  have hchi := (hGR.lev g).2 hgH x₀ hR
  refine ⟨⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hb) hkf) hb, ?_⟩, ?_⟩
  · change Lev.finE (Yc D j) _ ∈ Formalism.L2.DIV.lev _ _ _ _
    refine ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
      obtain rfl : (pl i).1 = PP := congrArg Subtype.val hi
      rw [hr]
      exact hbt i
    · rw [hQ PP hPP]; exact one_mem _
    · rw [hrT]; exact hgH
  · unfold Lev.levChi levFn
    rw [hrT]
    have e1 : ext1 ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).P.H ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).P.chi g = ∏ i, (G i).S.P.lam (x₀ i) :=
      (extendOne_of_mem (P := (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (_root_.GlobalTheory.Fam.complexLevelStructure W).chi hgH).trans hchi
    have e2 : ∏ PP ∈ ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).Q, ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).xq PP (dBlk (blk2 ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).r) 1
        (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) = 1 :=
      Finset.prod_eq_one fun PP hPP => by rw [hQ PP hPP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
    have e3 : ∏ PP ∈ ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).Pg, ∏ c ∈ Finset.range ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).s,
        ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).cg (c + 1) PP (dBlk (blkOf ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).r ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).t) (c + 1)
          (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) =
        ∏ i, ∏ c ∈ Finset.range j, (_root_.GlobalTheory.Fam.pk_z W).chi (c + 1) (pl i).1
          (dBlk (blkOf D.R.r D.R.t) (c + 1) (Formalism.UG.bc (resS D.host.F (pl i).1) Y)) := by
      simp only [hr]
      rw [← Finset.prod_coe_sort]
      exact (Fintype.prod_equiv pl _ _ fun i => rfl).symm
    rw [e1, e2, e3, mul_one, ← Finset.prod_mul_distrib, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => congrArg Units.val (hlam i).symm
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → (∀ j, j < D.R.m → ∀ (X : (f.t t).CC j) x, ∀ a ∈ GinfC _, (∀ i, (F.Q i).Typed j (rTrans (a * v.b j) (X.1 x))) ∧ ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (X.1 x)) = rTrans (a * v.b j) (X.1 x)) ∧ (∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧ (∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) g → (f.t t).om j (1, k) (comb f.c.ψ _ _ (v.eG j) g) = a⁻¹ • comb f.c.ψ _ _ (v.eG j) g) ∧ (j + 1 + 1 < D.R.m → ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) g → (f.t t).om (j + 1) (k, 1) (comb f.c.ψ _ _ (v.eG (j + 1)) g) = a • comb f.c.ψ _ _ (v.eG (j + 1)) g) ∧ ∀ (X : (f.t t).CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x)) ∧ TopSph (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch
  have hθ : IsInfFam f.c.θ := W.Q.charW.base.models.inf
  have hc : IsStdChar D f.c.ψ (-1) := W.Q.stdChar
  have hGLv := fun j (hj : j + 1 < D.R.m) k hk a ha => _root_.GlobalTheory.RowLevel.g_lev_alt hv hV hGP hGR t (j + 1) hj k hk a ha
  refine ⟨fun j hj X x a ha => ⟨fun i => ?_, fun κ hκ => ?_⟩, fun j hj k hk => ?_, fun X x κ hκ => ?_⟩
  · intro d h y
    have hKO := (F.Q i).le j d h y.2
    have hm := (hQL.mid i j d h hj y.1 hKO)
    have hgf : (F.Q i).gl j d h y.1 ∈ GfC _ :=
      GlobalTheory.WeilProduct.mem_GfC_of_suppAt (F.Q i).q.split ((F.Q i).gl_loc j d h y.1).1
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hgf ((hm.1).2 y.2), hm.2 y.2]
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := _root_.GlobalTheory.RowLevel.off_lev_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hκf ho.1, ho.2, one_smul]
  · obtain ⟨r, hr⟩ := D.R.m_even
    have third : ∀ (X : (f.t t).CC (j + 1)) x (a : ℂ), GLam G (j + 1) k a →
        rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x) := by
      intro X x a hga
      have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG (j + 1) hj).1 hk)
      have ho := hGLv j hj k hk a hga
      rw [hV.b (j + 1), rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hkf ho.1, ho.2]
    have uniq : ∀ a a', GLam G (j + 1) k a → GLam G (j + 1) k a' → a = a' := fun a a' h h' =>
      (hGLv j hj k hk a h).2.symm.trans (hGLv j hj k hk a' h').2
    rcases Nat.even_or_odd j with ⟨q, hq⟩ | ⟨q, hq⟩
    · obtain ⟨σ, hσ⟩ : ∃ σ, j + 2 * σ + 2 = D.R.m := ⟨(D.R.m - j - 2) / 2, by omega⟩
      have LL := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch j σ hσ
      obtain ⟨a, ha0, hga, hlaw⟩ := LL.1 k hk
      refine ⟨a, ha0, hlaw, fun hj2 => ?_, fun X x => third X x a hga⟩
      obtain ⟨a', -, hga', hlaw'⟩ := (LL.2.2 (by omega)).2 k hk
      rw [uniq a a' hga hga']
      exact hlaw'
    · obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨2 * q, by omega⟩
      obtain ⟨σ, hσ⟩ : ∃ σ, j₀ + 2 * (σ + 1) + 2 = D.R.m := ⟨(D.R.m - j₀ - 4) / 2, by omega⟩
      have LL := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch j₀ (σ + 1) hσ
      obtain ⟨a, ha0, hga, hlaw⟩ := (LL.2.2 (by omega)).1 k hk
      refine ⟨a, ha0, hlaw, fun hj2 => ?_, fun X x => third X x a hga⟩
      have LL' := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch (j₀ + 1 + 1) σ (by omega)
      obtain ⟨a', -, hga', hlaw'⟩ := LL'.2.1 k hk
      rw [uniq a a' hga hga']
      exact hlaw'
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := _root_.GlobalTheory.RowLevel.top_lev_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
    rw [hV.bT.1, rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hκf ho.1, ho.2, one_smul]
end GlobalTheory.RowLevel
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
namespace GlobalTheory.TwistChr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field


section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
theorem twChr_of_twAdm_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := fun _ h =>
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r hm w hw j _ hρ hA =>
    have hw' := (p.tw_iff w).1 hw
    have h1 := chrEq_tw hm.2.2 hw' (H x hx h0 i p r hm w hw j).1 hρ hA
    ⟨h1, xi_eq hw' hA.1 j _ h1⟩⟩
end GlobalTheory.TwistChr
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ExpAlgAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ (n : ℕ) (a : Fin n → NX.KB p.Sx ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
        (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
        p.nexp.eF ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) (Nat.le_add_left _ _) j.2 f =
          ∑ k, a k ⊗ₜ[p.Sx.Ks] g k ∧
        ∀ k, IsAlgebraic ℚ (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k))
end GlobalTheory.BigOn.Exp
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem canEx_holds_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalExists :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p _ _ w _ j => canEx_at p w j⟩⟩⟩
end GlobalTheory.BigOn.Exp
end
end
end
