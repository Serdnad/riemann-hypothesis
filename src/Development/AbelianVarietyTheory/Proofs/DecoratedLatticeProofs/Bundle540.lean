module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle530
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle537
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
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

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem normSq_theta_modGrowth_big : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
    ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t →
    ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
    (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hSWF hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have h2ab : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  obtain ⟨hint, hEV⟩ := GlobalTheory.T.thetaIntegral_eq_siegelEisenstein_of_weilRange hSWF D ψ A B (by omega) h2ab hw χB omh homh ν 𝓕 hP.covol mH hmH
    (delta A B Φ Φ) hφ

  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hP.weil.om_aut 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hΦ.1)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hP.weil.om_cont Φ hΦ.1 0).comp (Continuous.prodMk_right g)
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩

  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hCt, hReg⟩ := hSEC D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem
  obtain ⟨k, hk⟩ := hReg (sZero A B)
  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast h2ab
    linarith
  have hF := hCt.1
  have hv0 := hF.eisValueAt hF.analyticOnNhd_flat hre
  have hv : GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (sZero A B)
      (ThetaMean.thetaMean omh mH (delta A B Φ Φ)) := by
    rw [hEV]; simpa only [flatH_self] using hv0
  obtain ⟨r, hr, -, -, C₁, N, hC₁⟩ := GlobalTheory.Eis.EisRegularAt.of_eisValueAt hk hv
  have hE : ∀ x, ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) x‖ ≤ C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have e := hv.eisCont_eq
    have := hC₁ (sZero A B) (Metric.mem_ball_self hr) x
    rw [e] at this
    exact this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (norm_nonneg _).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A
  have hvol := GlobalTheory.RallisIP.Model.vol_pos (B := B) mH
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ =
      (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖ := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul, ← measure_smul_average, norm_smul, ThetaMean.thetaMean,
      Real.norm_of_nonneg measureReal_nonneg]
  refine ⟨(autMeasure B mH).real Set.univ * C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  rw [hpet g]
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖
      ≤ (autMeasure B mH).real Set.univ * (C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N) :=
        mul_le_mul_of_nonneg_left (hE _) hvol.le
    _ ≤ (autMeasure B mH).real Set.univ * (C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁0) hvol.le
    _ = (autMeasure B mH).real Set.univ * C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.Core.Rk.IP
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.UnfKer

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem zEll_rat (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  rw [zEll, GlobalTheory.CharLaws.ell_eq]
  ext i j
  change incA D (_ * _) = _
  rw [map_mul]; rfl

theorem incAdj_rat {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) : d.incAdj S y ∈ ratMx D T.rank S.rank := by
  rw [d.incAdj_apply, d.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem jacT_rat (hψ : IsCharAF D.host.F ψ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) {n : GA D T} (hn : n ∈ GQ T) {f : WO S T₀ → ℂ} (hf : IsThetaFunO ψ S T₀ f) :
    jacT ψ d S y n f 0 = f 0 := by
  have h1 := incAdj_rat d S hy
  have h2 : mt T n⁻¹ ⬝ d.incAdj S y ∈ ratMx D T.rank S.rank := ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hn)) h1
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ h1 _ h2
  obtain ⟨δ, hδ⟩ : ptT d S y n ∈ ratMx D T₀.rank S.rank := ratMx_mul (rat_mem _) h2
  have h3 := hf.quasi δ 0
  rw [show ratW T₀ S δ = ptT d S y n from hδ, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul,
    add_zero] at h3
  rw [jacT, Pi.smul_apply, cenT, ha, hψ.2.2.1, one_smul, heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul,
    zero_add, h3]

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

theorem flatBF_eq (Ψ : WO B.V J.W → ℂ) : flatBF s Ψ =
    flatAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat J.d.e) (yZero B.V₀ ρ (vecB B.o B.ζ)) Ψ := rfl

theorem flatBF_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) : IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ) :=
  (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 _ Ψ hΨ).2

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

theorem flat_rat {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ₀ : GA D B.A} (h₀ : γ₀ ∈ GQ B.A) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) : flatBF s (s.om (embA B.d B.o γ₀, γ) Ψ) 0 = flatBF s Ψ 0 := by
  obtain ⟨n, hn, h', rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hγ.2
  obtain ⟨hnQ, hh'⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hγ.1
  have hψ := s.weil.std.1
  have hΞ := flatBF_theta s hΨ
  have hy : yZero B.V₀ ρ (vecB B.o B.ζ) ∈ ratMx D B.V₀.rank ρ := neg_mem (zEll_rat _ _ _)
  have e1 : flatBF s (s.om (embA B.d B.o 1, n * J.d.emb0 h') Ψ) 0 = flatBF s Ψ 0 := by
    rw [GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom Ψ hΨ 1 n hn h', psiFlag_eq, GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 hnQ,
      star_one, one_smul, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply, opA,
      jacT_rat hψ J.d B.V₀ hy hnQ (s.weil₀.om_pres _ _ hΞ), s.weil₀.om_aut 1 (one_mem _) h' hh' _ hΞ]
  have hΨ' := s.weil.om_pres (embA B.d B.o 1, n * J.d.emb0 h') Ψ hΨ
  have e2 : s.om (embA B.d B.o γ₀, n * J.d.emb0 h') Ψ =
      s.om (embA B.d B.o γ₀, 1 * J.d.emb0 1) (s.om (embA B.d B.o 1, n * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk, map_one, map_one, mul_one, mul_one, one_mul]
  rw [e2, GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom _ hΨ' γ₀ 1 (one_mem _) 1, psiFlag_eq,
    GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 (one_mem _), star_one, one_smul, opA, jacT_one, Prod.mk_one_one, map_one,
    Module.End.one_apply, id, s.weil₀.om_aut _ (B.o.emb_mem_GQ h₀ (one_mem _)) 1 (one_mem _) _ (flatBF_theta s hΨ'), e1]

theorem flat_left {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ₀ : GA D B.A} (h₀ : γ₀ ∈ GQ B.A) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) (g : GA D B.A) (h : GA D J.W) :
    flatBF s (s.om (embA B.d B.o (γ₀ * g), γ * h) Φ) 0 = flatBF s (s.om (embA B.d B.o g, h) Φ) 0 := by
  rw [map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  exact flat_rat s hom (s.weil.om_pres _ _ hΦ) h₀ hγ

end GlobalTheory.UnfKer

namespace GlobalTheory.Unf

theorem kerBF_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → Continuous (kerBF s φ G Φ) ∧ (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, kerBF s φ G Φ (γ * h) = kerBF s φ G Φ h) ∧ (∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 = flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) ∧ ∀ h h' (n : flagN J.d), kerBF s φ G Φ (n.1 * J.d.emb0 h' * h) = fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) h' n := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  have h3 : ∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 =
      flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0 := fun γ hγ h₀ h => by
    have := GlobalTheory.UnfKer.flat_left s hom hΦ hγ (one_mem _) h₀ h
    rwa [one_mul] at this
  refine ⟨?_, fun γ hγ h => ?_, h3, fun h h' n => ?_⟩
  · have hc := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e
      (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 Φ hΦ
    have he : Continuous (embA B.d B.o) :=
      B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
    have hq : Continuous fun p : GA D B.A × GA D J.W =>
        (((embA B.d B.o p.1, p.2), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((he.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have hF : Continuous fun p : GA D B.A × GA D J.W => flatBF s (s.om (embA B.d B.o p.1, p.2) Φ) 0 := by
      refine (hc.comp hq).congr fun p => ?_
      rw [Function.comp_apply, GlobalTheory.UnfKer.flatBF_eq]
    have hK : Continuous (Function.uncurry fun (h₀ : GA D B.A) (h : GA D J.W) =>
        φ h₀ * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) := by
      refine ((hφ.2.comp continuous_fst).mul hF).congr fun p => ?_
      rw [Function.uncurry, Pi.mul_apply, Function.comp_apply]
    exact hG.2.1.mul (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D B.A B.cpt B.vA (GA D J.W) _ hK
      (fun γ hγ g p => by rw [hφ.1 γ hγ, h3 γ hγ])).2.1
  · rw [kerBF, kerBF, hG.1 γ hγ.1]
    congr 2
    funext h₀
    have := GlobalTheory.UnfKer.flat_left s hom hΦ (one_mem _) hγ h₀ h
    rw [one_mul] at this
    rw [this]
  · rw [kerBF, fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _)]
    congr 2
    funext h₀
    have e : s.om (embA B.d B.o h₀, n.1 * J.d.emb0 h' * h) Φ =
        s.om (embA B.d B.o h₀, n.1 * J.d.emb0 h') (s.om (1, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk, mul_one]
    rw [e, GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΦ) h₀ n.1 n.2 h', Pi.smul_apply, smul_eq_mul, fjKer]
    ring

end GlobalTheory.Unf

end
end
