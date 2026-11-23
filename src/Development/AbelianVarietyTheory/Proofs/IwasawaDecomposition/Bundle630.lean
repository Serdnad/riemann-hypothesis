module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmLettersIsLieBasisAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle529
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CuspFromBasis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open Matrix GlobalTheory.LieEigen GlobalTheory.ConstBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem exists_comb_of_type {I : Type} {m : I → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : I, Fin (m τ)) (τ : I) {w : Fin g → ℂ}
    (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (m τ) → ℂ, w = ∑ k, cf k • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) := by
  refine ⟨fun k => w (e.symm ⟨τ, k⟩), funext fun j => ?_⟩
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  rw [Finset.sum_apply]
  by_cases h : τ' = τ
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (by simpa using hk.symm), smul_zero]) (by simp)]
    simp
  · have h₀ : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h₁
      exact h (by simpa using hw _ h₁)
    rw [h₀]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h₁ => h (congrArg Sigma.fst (e.symm.injective h₁))), smul_zero]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ArcBasis W (fun τ => σ.comp (embK c τ)) e := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw O _ β Y a χ W Ha e z hσ hz he
  have hG := GlobalTheory.ArcCM.known_holds.laws.globalFns
  obtain ⟨g, e₀, v, M, hev, hv, hu, hM⟩ := ConstLie.exists_const_basis hG E H Dw l Xo c O β Y ℂ _ a χ W
  have lin := ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y ℂ _ a χ W
  obtain ⟨an₁, an₂, an₃, an₄⟩ := ExpTan.anVec_bijective hG E H Dw l Xo c σ O β Y a χ W _ _ _ Ha
  have := flat_of_injective ℂ (PowerSeries ℂ) PowerSeries.C_injective
  let ρ : (E →+* ℂ) → 𝓞 E → ℂ := fun τ x => σ (embK c τ x)
  let M' : 𝓞 E → Matrix (Fin g) (Fin g) (PowerSeries ℂ) := fun x => (M x).map (PowerSeries.C (R := ℂ))
  have hM' : ∀ x i, IsLieComb (M' x i) v (v i ≫ W.t.act.act x) := hM
  choose zz hzz using fun i => (an₁ _ (hev i).1).exists
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin Uw.g → ℂ) := Fintype.linearCombination ℂ zz
  have comb : ∀ u ν, GtComb u e₀ ν ↔ AnVec Ha ν (L u) := fun u ν => an₄ g u e₀ zz ν hzz
  have img : ∀ u ν, AnVec Ha ν (L u) → LieImg W ν (prodPts (fun j => PowerSeries.C (R := ℂ) (u j)) v) :=
    fun u ν h => (lin g _ e₀ _ v _ (fun i => (hev i).2) ((comb u ν).2 h)).2 ((Chart.isLieComb_iff _ _ _).2 rfl)
  have inj : Function.Injective L := fun u u' h => by
    obtain ⟨ν, hν, -⟩ := an₂ (L u)
    exact (hu ν (an₃ _ _ hν)).unique ((comb _ _).2 hν) ((comb _ _).2 (h ▸ hν))
  have surj : Function.Surjective L := fun w => by
    obtain ⟨ν, hν, -⟩ := an₂ w
    obtain ⟨u, h, -⟩ := hu ν (an₃ _ _ hν)
    exact ⟨u, (an₁ ν (an₃ _ _ hν)).unique ((comb _ _).1 h) hν⟩
  have cm : ∀ x (u : Fin g → ℂ), (fun j => PowerSeries.C (R := ℂ) (u j)) ᵥ* M' x =
      fun j => PowerSeries.C (R := ℂ) ((u ᵥ* M x) j) := fun x u =>
    funext fun i => ((PowerSeries.C (R := ℂ)).map_vecMul (M x) u i).symm
  have act : ∀ (x : 𝓞 E) u, L (u ᵥ* M x) = fun k => Formalism.L2.PjFree.relab c σ (Uw.e k).1 (x : E) * L u k := fun x u => by
    by_cases hx : x = 0
    · subst hx
      obtain ⟨ρ', hρ'⟩ := exists_action hv W.t.act
      have h₁ := prodPts_injective hv ((hρ' 0 (fun j => PowerSeries.C (R := ℂ) (u j))).trans
        (prodPts_act hv hM' 0 _))
      rw [cm, map_zero] at h₁
      have h₂ : u ᵥ* M 0 = 0 := funext fun j => PowerSeries.C_injective (R := ℂ)
        ((congrFun h₁ j).symm.trans (map_zero _).symm)
      rw [h₂, map_zero]
      funext k
      simp
    · obtain ⟨ν, hν, -⟩ := an₂ (L u)
      obtain ⟨u₁, h₁⟩ := surj fun k => Formalism.L2.PjFree.relab c σ (Uw.e k).1 (x : E) * L u k
      obtain ⟨ν₁, hν₁, -⟩ := an₂ (L u₁)
      have h₂ := ArcType.act_eq Ha hx hν (img _ _ hν) (isTangent_prodPts hv.1 _) (h₁ ▸ hν₁) (img _ _ hν₁)
        (isTangent_prodPts hv.1 _)
      rw [prodPts_act hv hM', cm] at h₂
      have h₃ : u₁ = u ᵥ* M x := funext fun j => PowerSeries.C_injective (R := ℂ)
        (congrFun (prodPts_injective hv h₂) j)
      rw [← h₃, h₁]
  have typ : ∀ τ w, (∀ x, w ᵥ* M x = ρ τ x • w) ↔ ∀ j, L w j ≠ 0 → (Uw.e j).1 = τ := fun τ w => by
    refine ⟨fun h j hj => ?_, fun h x => inj ?_⟩
    · refine (GlobalTheory.Relab.relab_good E H l c σ hσ).1.1 ?_
      refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      have h₁ := congrFun (act x w) j
      rw [h x, map_smul] at h₁
      exact mul_right_cancel₀ hj h₁.symm
    · rw [act, map_smul]
      funext j
      by_cases hj : L w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
  choose u hu using fun τ k => surj (z τ k)
  have imgu : ∀ τ k, LieImg W (e τ k) (prodPts (fun j => PowerSeries.C (R := ℂ) (u τ k j)) v) := fun τ k =>
    img _ _ ((hu τ k).symm ▸ he τ k)
  have eig : ∀ τ k x, u τ k ᵥ* M x = ρ τ x • u τ k := fun τ k =>
    (typ τ _).2 ((hu τ k).symm ▸ (hz τ).2 k)
  have key : ∀ τ (w : Fin g → PowerSeries ℂ), (∀ x, w ᵥ* M' x = PowerSeries.C (R := ℂ) (ρ τ x) • w) →
      ∃! cf : Fin (Dw.mult τ) → PowerSeries ℂ, w = ∑ k, cf k • (fun j => PowerSeries.C (R := ℂ) (u τ k j)) := by
    intro τ
    refine (commonEigenvectors_flat_baseChange ℂ (𝓞 E) g _ M (ρ τ)).1 ℂ (u τ) (eig τ) ?_ (PowerSeries ℂ)
    have : ∀ w : Fin g → ℂ, (∀ x, w ᵥ* M x = ρ τ x • w) →
        ∃! cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • u τ k := fun w hw => by
      refine (existsUnique_congr fun cf => ?_).1 (LetterBasis.existsUnique_comb (hz τ).1
        (fun k => exists_comb_of_type Uw.e τ ((hz τ).2 k)) (exists_comb_of_type Uw.e τ ((typ τ w).1 hw)))

      rw [← inj.eq_iff, map_sum]
      simp only [map_smul, hu]
    simpa using this
  refine ⟨_, imgu, fun τ => ⟨fun k => ⟨isTangent_prodPts hv.1 _, fun x => ?_⟩, fun w hw he => ?_⟩⟩
  · rw [eig_iff hv hM']
    exact vecMul_map _ (eig τ k x)
  · obtain ⟨d, rfl⟩ := exists_prodPts hv hw
    refine (existsUnique_congr fun cf => ?_).1 (key τ d fun x => (eig_iff hv hM' _ _ _).1 (he x))
    rw [Chart.isLieComb_iff, prodPts_prodPts hv.1, (prodPts_injective hv).eq_iff]

end GlobalTheory.CuspFromBasis
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levels_kernelData_at_served_place : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg)) (KD : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv),
        KD.lam = E.lam v ∧
        ThAtServed (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) E ∧
        Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) ∧
        Formalism.L2.Herm.GIwPos u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.kerData_at_served | exact GlobalTheory.Mem.Top.KerOne.kerData_at_served | (intros; apply GlobalTheory.Mem.Top.KerOne.kerData_at_served <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St



theorem exists_rowsT : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w) (x : St P), (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) → ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW := by
  refine StepW.of_all fun K B f T w hK hF hw P x hη => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have h1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ h1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.T.F0K_eq_of_kapDef K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  let t : RowsT K w x.o.Z P.Wt x.s.p0 :=
    { hX := P.hX
      r := x.rowsAre hη
      exAt := x.m.exAt
      inGeo := x.m.inGeo
      grpAt := x.fits.grpAt
      grp := x.fits.grp
      mu :=
        { inj := w.ok.xi_inj
          range := w.xi_range
          mu0 := w.l.xi0
          star := by
            show w.I.xi w.I.muStar = f.del
            rw [w.ok.xi_star, w.C_eq]
          star' := by
            show w.I.xi w.I.muStar' = f.del'
            rw [w.ok.xi_star', w.C_eq]
          tw := P.q.mu.tw
          on := P.q.mu.on
          off := P.q.mu.off
          sub := P.sub
          supp := P.supp }
      exact := hex
      untw := GlobalTheory.T.index_zero_off_twistedPlaces K B f T w hK hF hw P x hη hex
      emt0 := GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing K B f T w hK hF hw P x hη
      emt := GlobalTheory.T.periodForms_isometry_columnPairing_at_state K B f T w hK hF hw P x hη
      etaF := x.etaF
      rowInt := GlobalTheory.T.periodRowLatticesIntegral_provisionalRows K B f T w P x.o
      idx := fun Y _ => (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Y }
  exact ⟨t, GlobalTheory.T.provisionalRows_furtherCompatibilities_at_state K B f T w hK hF hw P x hη t rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3.Rw.St

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

theorem residueCharacteristic_mem (v : HeightOneSpectrum (𝓞 F)) : ((resP v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem ioOf_le_one_iff (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (hv : (p : 𝓞 F) ∈ v.asIdeal) (ε : Ext v) :
    ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F (AlgebraicClosure F) v ε.O hv
    (GlobalTheory.TrueGeo.ExtConj.lies_over ε)
  have h : ∃ io : AlgebraicClosure F →+* ℂ_[p], ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O :=
    ⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp j, fun a => by
      rw [hj, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]⟩
  exact Classical.epsilon_spec h

theorem log_w_eq (p : ℕ) [hp : Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (io : AlgebraicClosure F →+* ℂ_[p]) (h : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (a : AlgebraicClosure F) :
    Real.log (ε.w a) = (-Real.log (ε.w p) / Real.log p) * Real.log ‖io a‖ := by
  let u : AbsoluteValue (AlgebraicClosure F) ℝ := (NormedField.toAbsoluteValue ℂ_[p]).comp io.injective
  have hu (x) : u x = ‖io x‖ := rfl
  have he : u.IsEquiv ε.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have h1 : u x⁻¹ ≤ 1 ↔ ε.w x⁻¹ ≤ 1 := by rw [hu, h, ε.mem_O]
      rw [map_inv₀, map_inv₀, inv_le_one₀ (u.pos hx), inv_le_one₀ (ε.w.pos hx)] at h1
      rw [← not_le, ← not_le, h1]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hw (x) : Real.log (ε.w x) = c * Real.log ‖io x‖ := by
    rw [← congrFun hce x, hu]
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hc.ne']
    · exact Real.log_rpow (norm_pos_iff.2 ((map_ne_zero io).2 hx)) c
  have hn : ‖io p‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [hw, hw, hn, Real.log_inv]
  field_simp

theorem ioOf_spec : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v), ∃ hp : (resP v).Prime, haveI := Fact.mk hp; (∀ a, ‖ioOf (resP v) ε a‖ ≤ 1 ↔ a ∈ ε.O) ∧ ∀ a, Real.log (ε.w a) = (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log ‖ioOf (resP v) ε a‖ := fun _ _ _ v ε =>
  ⟨residueCharacteristic_prime v, by
    haveI := Fact.mk (residueCharacteristic_prime v)
    exact ⟨ioOf_le_one_iff _ (residueCharacteristic_mem v) ε, log_w_eq _ ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)⟩⟩

end GlobalTheory.ShFam.Pad
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.Proof.LetterConjugation

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange a, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩⟩

theorem nodup_letters : (letters Dw).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · exact (List.nodup_finRange _).map fun i i' h => eq_of_heq (Sigma.mk.inj h).2
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (Sigma.mk.inj h).1).symm

theorem rt0_conj_neg_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, him] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem conj_ne {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h1
  exact rt0_conj_neg_ne_zero (H := H) (by simpa [conjEmb, h] using h1)

theorem conj_eq {τ : E →+* ℂ} (h : τ (H.rt : E) ≠ H.rt0) : conjEmb τ (H.rt : E) = H.rt0 := by
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
  have h2 : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left h
  have h3 : starRingEnd ℂ H.rt0 ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  have h4 : starRingEnd ℂ H.rt0 = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left rt0_conj_neg_ne_zero
  simp [conjEmb, h2, h4]

theorem mult_add (τ : E →+* ℂ) : Dw.mult τ + Dw.mult (conjEmb τ) = Dw.p + Dw.q := by
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (conj_ne h)]
  · rw [if_neg h, if_pos (conj_eq h), add_comm]

theorem two_mul_length : 2 * (letters Dw).length = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  classical
  have h1 : (letters Dw).length = ∑ τ, Dw.mult τ := by
    rw [← List.toFinset_card_of_nodup (nodup_letters Dw),
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_letters Dw x), Finset.card_univ, Fintype.card_sigma]
    simp
  have hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := fun τ => by
    ext x; simp [conjEmb]
  have h2 : ∑ τ, Dw.mult (conjEmb τ) = ∑ τ, Dw.mult τ := hinv.bijective.sum_comp Dw.mult
  rw [h1, two_mul]
  nth_rewrite 2 [← h2]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => mult_add Dw τ, Finset.sum_const, Finset.card_univ,
    Embeddings.card, smul_eq_mul]

end Free

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

end GlobalTheory.Proof.LetterConjugation
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

def IsTwInv (φ : InvFun (𝓞 E)) : Prop :=
  ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def IsPosFn (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Nontrivial X], ∀ be ∈ levelForms H 1 X,
    (∀ y, y ≠ 0 → 0 < be y y) → 0 < φ.evalZ be

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def polOf (Z : Model Xo c β) (m : ℕ) (BD : EffCartierData Z.X) : LB Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm Z) m) (GlobalTheory.CechPic.dual BD.lb)

def selfTor (Z : Model Xo c β) (h₁ : SmoothOfRelativeDimension D.dim (genStr Z)) (h₂ : FinalTheorems.Snc (genBdIdeal Z))
    (h₃ : ∀ x ∈ genBd Z, HasToricChart Z x) (BD : EffCartierData Z.X)
    (h₄ : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) (h₅ : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support)
    (m : ℕ) (hm : 0 < m) : TorModel Z where
  Z := Z
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Z.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Z.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := h₁
  snc := h₂
  toric := h₃
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := BD
  BD_supp := h₄
  BD_pos := h₅
  m0 := m
  torModel_multiplicity_pos := hm

end Defs

end GlobalTheory.TorRef
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Scale

variable {X : Scheme.{0}}

theorem idlAlong_nsmul (D : EffCartierData X) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (D.nsmul n).idealSheaf ξ = idlAlong D.idealSheaf ξ ^ n := by
  obtain ⟨i, hi⟩ := D.exists_mem (ξ (IsLocalRing.closedPoint R))
  have h1 := (D.nsmul n).stalkId_idealSheaf i _ hi
  have h2 := D.stalkId_idealSheaf i _ hi
  have h3 : (X.presheaf.germ ((D.nsmul n).U i) (ξ (IsLocalRing.closedPoint R)) hi).hom ((D.nsmul n).f i) =
      ((X.presheaf.germ (D.U i) (ξ (IsLocalRing.closedPoint R)) hi).hom (D.f i)) ^ n :=
    map_pow _ _ _
  unfold idlAlong
  rw [h1, h3, h2, ← Ideal.map_pow, Ideal.span_singleton_pow]

end GlobalTheory.TorRef.Scale
end
end
