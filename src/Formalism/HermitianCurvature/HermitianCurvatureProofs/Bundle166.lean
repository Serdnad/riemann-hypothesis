module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle030
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliTwoByTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.TopLevelPointwiseIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle155
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle154
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section eqv

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem psi_star_mul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : B.Mat k r) :
    star (psi k r z c x) * psi k r z c x = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (Complex.I * (((c * ell k r z x).re : ℝ) : ℂ)) +
      Complex.I * (((c * ell k r z x).re : ℝ) : ℂ) = 0 := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [h, Complex.exp_zero]

def oneP : B.SS k r := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), (1 : B.Mat k r)))

theorem oneP_inSS (D : B.RealPlaceData k r Wp Wq) : D.inSS oneP :=
  ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one⟩

theorem sgs_oneP (g : B.Mat k r) : B.sgs oneP g = g := by
  show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * g * 1 * 1 = g
  simp

theorem eqv_of_FFl (D : B.RealPlaceData k r Wp Wq) (X : B.Mat k r → (Wq →L[ℂ] Wp))
    (hX : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z'))
    {p : B.SS k r} (hp : D.inSS p) {y : B.Mat k r} (hy : y ∈ JF.Om k r D.z D.z') :
    JF.xiP D p • B.rho D p X y = X y := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hnN : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv h2
  have mem : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hg.1, hg.2⟩
  have nlev : ∀ m ∈ Nset k r, m ∈ Q.Nlev k r 0 := fun m hm => ⟨hm, (Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 m).2 hm.1⟩
  have hyn : y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)) y =
        y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  have hnyn : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h2, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)) y =
        (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  obtain ⟨_, hL, hR, hU⟩ := hX
  have e1 : X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) =
      (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) • X y := by
    rw [Matrix.mul_assoc, hL _ (mem _ hyn) _ (nlev _ hnN), hR _ (mem _ hy) _ (nlev _ h4), smul_smul]
  have e2 : X ((Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) *
      (Matrix.of p.2.1 : B.Mat k r)) =
      (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹).comp ((X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
        (Matrix.of p.2.2 : B.Mat k r))).comp (D.π' (Matrix.of p.2.1 : B.Mat k r))) :=
    hU _ (mem _ hnyn) _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3
  have hsgs : B.sgs p y = (Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
      (Matrix.of p.2.2 : B.Mat k r)) * (Matrix.of p.2.1 : B.Mat k r) := by
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) *
      (Matrix.of p.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  have hπ : ∀ w, D.π (Matrix.of p.1.1 : B.Mat k r) (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π_rep.2 _ h1 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1)
    rw [Matrix.mul_nonsing_inv _ hu1, D.π_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hπ' : ∀ w, D.π' (Matrix.of p.2.1 : B.Mat k r) (D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π'_rep.2 _ h3 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h3)
    rw [Matrix.mul_nonsing_inv _ hu3, D.π'_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hc : JF.xiP D p * (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ *
      psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) = 1 := by
    unfold JF.xiP
    have a1 := BesselUnipotentEquiv.star_psi_inv D.z cStd D.z_mem _ h2
    have a2 := psi_star_mul D.z cStd ((Matrix.of p.1.2 : B.Mat k r)⁻¹)
    have a3 := psi_star_mul D.z' cStd (Matrix.of p.2.2 : B.Mat k r)
    rw [a1] at a2
    calc psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) *
          (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r))
        = (psi k r D.z cStd (Matrix.of p.1.2) * psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹) *
          (star (psi k r D.z' cStd (Matrix.of p.2.2)) * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) := by ring
      _ = 1 := by rw [a2, a3, one_mul]
  unfold B.rho
  rw [hsgs, e2, e1]
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, hπ', hπ, smul_smul, hc, one_smul]

end eqv

theorem sAExh_of_avgCutoff (hA : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff) : SAExh := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v X hX Cs hCs hCsQ
  set Db := (T v).base with hDb
  have hplace : Q.IsPlace (D.parOf S v) Db.z Db.z' Db.π Db.π' := (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hX' : X ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (Q.OmPlus S.G.k S.G.r Db.z Db.z') := by
    have := hX
    unfold smoothFormsPositiveCone at this
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v] at this
  obtain ⟨K', hK'c, hCsK', hK'Q⟩ := exists_compact_between hCs (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open Db.z Db.z')
    (fun x hx => hQ x (hCsQ hx))
  obtain ⟨φ, hφ, ⟨C, hCc, hCO, hCφ⟩, hint⟩ := hA S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C := by
    refine closure_minimal (fun g hg => ?_) hCc.isClosed
    by_contra hgC
    exact hg (by simp [hCφ g hgC])
  refine ⟨fun g => φ g • X g, interior K', isOpen_interior, hCsK', ?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus S.G.k S.G.r Db.z Db.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨Cᶜ, fun _ => 0, hCc.isClosed.isOpen_compl, fun h => hO (hCO h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hCφ g hg]
  · exact hCc.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
    exact fun g hg => (hCO (hsuppC hg)).2
  · intro y hy
    have hgy : B.gq Db y ∈ JF.Om S.G.k S.G.r Db.z Db.z' :=
      Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db y (hQ y hy)
    have hJ : B.JF Db (fun g => φ g • X g) (B.gq Db y) =
        (∫ p, φ (B.sgs p (B.gq Db y)) ∂Db.μSS) • X (B.gq Db y) := by
      change ∫ p, JF.xiP Db p • B.rho Db p (fun g => φ g • X g) (B.gq Db y) ∂Db.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Db] with p hp
      have hr : B.rho Db p (fun g => φ g • X g) (B.gq Db y) =
          φ (B.sgs p (B.gq Db y)) • B.rho Db p X (B.gq Db y) := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, eqv_of_FFl Db X hX' hp hgy]
    refine ⟨fun hyU => ?_, fun h0 => ?_⟩
    · have h1 := hint oneP (oneP_inSS Db) y (interior_subset hyU)
      simp only [sgs_oneP] at h1
      rw [hJ, h1, one_smul]
    · rw [hJ, h0, smul_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

theorem gauge_right_line_holds : GLRight := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hpl hk he hQQ ζ hζ Fr hFr X hX Y X' hX' ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw : 0 < Gauge.wR P.k P.TT ζ := Gauge.GC.SSTr.wR_pos P hζ
  set a : M.Ty P → ℂ := fun σ => ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X) with hadef
  obtain ⟨Φs, -, hΦv⟩ := Gauge.GC.SSTr.exists_tr P Bs hpl hk e he (fun σ => algebraMap ℂ (MA.SmQ P.r P.TT) (a σ))
  set Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := (Φs : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) with hΦdef
  have hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φs.2
  have hval : Φ c0 g = X := by
    have h1 : Φ c0 g = _ := hΦv qq
    rw [h1]
    conv_rhs => rw [(he.2 ζ hζ).2.2 X hX]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    show (((Gauge.wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * ((algebraMap ℂ (MA.SmQ P.r P.TT) (a σ) : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) qq = _
    simp only [hadef, Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    field_simp
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq

  set Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r) := fun _ => Formalism.FourierDecayAlt.P.Qx5.Dp P.k P.r Bs.z Bs.z' with hDc
  have hFam : Gauge.FamR P Bs Dc Φ := by
    refine ⟨?_, fun c _ => Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_,
      fun c hc => Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ hc⟩
    · have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
        have : IsOpen (OmX P.r) := by
          have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
          rw [e]
          exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
        exact this.preimage continuous_fst
      have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
        isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
      exact h1.inter h2
    · have hq' : ((q.1.1, q.1.2) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
        ⟨q.2.1, by rw [hTz, hTz']; exact q.2.2⟩
      exact (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq').2.2
    · intro x₀ hx₀ hgl
      exact hΦ.2.1 x₀ ⟨hx₀.1, hgl, hx₀.2⟩
  have hG := hQQ Dc Φ hFam Y 1 1 ρ
  have hs1 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc _
    (Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hFam Y 1 1) ρ
  have hs0 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc Φ hFam ρ

  have hQ11 : MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ) := rfl
  rw [hQ11, Gauge.actA_mul, MA.ggA, Gauge.GC.SSC.actA_sc, MA.xA] at hG
  have hev := congrArg (fun s : MA.SmQ P.r P.TT => (s : MA.Qp P.r P.TT → ℂ) qq) hG
  rw [Gauge.GC.toSm_of_mem P hs1, Gauge.GC.actA_kap] at hev
  have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hGGv : Q.GGl P.k P.r Bs.z Bs.z' g = Complex.normSq ζ - P.TT := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hζ', hTz, hTz']
    rfl
  have hGG0 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Complex.normSq ζ - P.TT := by linarith
    exact_mod_cast this.ne'
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A; ext i; simp [B.hsVec]
  have hQLg : Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 Φ c0 g =
      (((Complex.normSq ζ - P.TT : ℝ) : ℂ)) • X' := by
    ext v
    have ht := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity Formalism.FourierDecayAlt.P.capelli_two_by_two Formalism.FourierDecayAlt.P.right_type_action hz hz'
      (Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z') Bs.π'_rep Bs.π'_cont
      (Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ (fun _ => one_ne_zero)) ⟨hx.2.1, hx.2.2⟩ (ne_of_gt hx.2.2) Fr hFr (Y : ℂ) v
    show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 (Φ c0) g v = _
    rw [ht, hval, ← hX', hGGv, ContinuousLinearMap.smul_apply]
  have hL : Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ) ρ qq =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ c0 g)) = _
    rw [hQLg, hsm, inner_smul_right]
  have h0 : Gauge.rawR P Bs.μsec e Φ ρ qq = ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Φ c0 g)) = _
    rw [hval]
  let Gq : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT
  let sq : MA.SmQ P.r P.TT := M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ)
  change _ = ((Gq * sq : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq at hev
  rw [Subalgebra.coe_mul, Pi.mul_apply] at hev
  have hgg : (Gq : MA.Qp P.r P.TT → ℂ) qq = ((Complex.normSq ζ - P.TT : ℝ) : ℂ) := by
    show MA.coordE M.vz qq.1 * MA.coordE M.vzb qq.1 - (P.TT : ℂ) = _
    simp [MA.coordE, MA.zE, M.vz, M.vzb, Complex.mul_conj, qq]
  have hsq : (sq : MA.Qp P.r P.TT → ℂ) qq = M.xC P ρ ↑Y * Gauge.rawR P Bs.μsec e Φ ρ qq := by
    show ((M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq = _
    rw [Subalgebra.coe_smul, Pi.smul_apply, Gauge.GC.toSm_of_mem P hs0, smul_eq_mul]
  rw [hgg, hsq, hL, h0] at hev
  have h3 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        (M.xC P ρ ↑Y * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) := by
    rw [hev]; ring
  exact mul_left_cancel₀ hGG0 (mul_left_cancel₀ hw' h3)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem castM_mul' {k a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem exp_castM {k a b : ℕ} (h : a = b) (M : B.Mat k a) :
    NormedSpace.exp (D.castM h M) = D.castM h (NormedSpace.exp M) := by
  unfold D.castM; exact exp_reindex _ M

theorem exp_block_three_diagonal {k j ρ : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) (Bm : B.Mat k ρ) (C : Matrix (Fin j) (Fin j) ℂ) :
    NormedSpace.exp (U.blk3 A 0 0 0 Bm 0 0 0 C) =
      U.blk3 (NormedSpace.exp A) 0 0 0 (NormedSpace.exp Bm) 0 0 0 (NormedSpace.exp C) := by
  unfold U.blk3
  rw [exp_reindex]
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext i l; rcases i with i | i <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext i l; rcases l with l | l <;> rfl
  rw [h1, h2, exp_fromBlocks, exp_fromBlocks]

theorem exp_block_two_diagonal {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dd : Matrix (Fin s) (Fin s) ℂ) :
    NormedSpace.exp (U.blk2 A 0 0 Dd) = U.blk2 (NormedSpace.exp A) 0 0 (NormedSpace.exp Dd) := by
  unfold U.blk2
  rw [exp_reindex, exp_fromBlocks]

theorem symmetricScalarBlockMatrix_one_zero {p s : ℕ} : U.blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [U.blk2]

theorem block_two_identity_conjTranspose {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) :
    (U.blk2 A 0 0 (1 : Matrix (Fin s) (Fin s) ℂ))ᴴ = U.blk2 Aᴴ 0 0 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, block_two_apply]
  split_ifs <;> simp [Matrix.one_apply, Fin.ext_iff, eq_comm]

theorem w_inv (d : ℕ) : (G.wMat d)⁻¹ = G.wMat d :=
  Matrix.inv_eq_left_inv (Ux4.wMat_mul_self d)

theorem exp_w_conj (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (G.wMat d * M * G.wMat d) = G.wMat d * NormedSpace.exp M * G.wMat d := by
  have hu : IsUnit (G.wMat d) := ⟨⟨G.wMat d, G.wMat d, Ux4.wMat_mul_self d, Ux4.wMat_mul_self d⟩, rfl⟩
  have e := Matrix.exp_conj (G.wMat d) M hu
  rw [w_inv] at e
  exact e

theorem block_two_exp_conjTranspose_inv {j : ℕ} (y : MJ j) :
    (U.blk2 (NormedSpace.exp y) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ⁻¹ = U.blk2 (NormedSpace.exp (-yᴴ)) 0 0 1 := by
  rw [block_two_identity_conjTranspose]
  apply Matrix.inv_eq_left_inv
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  have hu : IsUnit (NormedSpace.exp yᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  rw [Matrix.exp_neg, ← Matrix.exp_conjTranspose, Matrix.nonsing_inv_mul _ hu, symmetricScalarBlockMatrix_one_zero]

theorem exp_levi {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • levi k r j x) = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.muP k (j + 1) (r - (j + 1)) (U.blk2 (NormedSpace.exp ((t : ℂ) • x)) 0 0 1)) := by
  have hs : (t : ℂ) • levi k r j x = levi k r j ((t : ℂ) • x) := by
    ext p q
    simp only [levi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  rw [hs, levi_eq hj, exp_castM, exp_block_three_diagonal, exp_w_conj, exp_block_two_diagonal, exp_block_two_diagonal]
  simp only [NormedSpace.exp_zero]
  unfold U.muP
  rw [block_two_exp_conjTranspose_inv]

theorem zfull_mul {j : ℕ} (Z E : MJ j) (τ : ℂ) :
    zfull Z τ * U.blk2 E 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = zfull (Z * E) τ := by
  unfold zfull
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp

theorem curveLevi : CurveLevi := by
  intro k r j hj Z τ γ x t
  rw [exp_levi hj]
  unfold x0
  rw [← castM_mul', Ux4.mMap_mul_muP, zfull_mul]

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

theorem Formalism.FourierDecayAlt.P.levi_curve : Formalism.FourierDecayAlt.P.WirtingerOperators.CurveLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.curveLevi

theorem Formalism.FourierDecayAlt.P.hermitian_part_levi : Formalism.FourierDecayAlt.P.WirtingerOperators.HpartLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.hpartLevi
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

theorem graded_truncation_action_holds : GACutGraded := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs χ₀ hχ ε A Bg F hε hBg hF hFg
  obtain ⟨δ, -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hε
  exact Formalism.FourierDecayAlt.P.CutMP.JA.gcut_graded Bs.z Bs.z' (fun x => χ₀ (x / ε)) (δ * ε) hcut
    (by linarith) hF hFg

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end
