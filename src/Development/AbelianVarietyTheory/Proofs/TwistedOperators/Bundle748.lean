module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle536
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle510
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle502
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle501
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle732
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle745
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle680
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle483
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle575
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle637
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle746
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle412
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle672
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle629
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle735
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle415
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle747
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.ChainLifts

theorem chainEx (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hCW : GlobalTheory.Published.CasselmanWallach) (hDF : DepFixed) (hCM : CoreModels) : ChainEx := by
  intro D hq hsz T L μ0 hL sc hgap G W Mv hM v r₀ M₀ hr₀
  have hCom : (gridCom W).Is := GlobalTheory.T.testGridCommonData_properties_hold D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hStage := GlobalTheory.T.testGridStageLatticesProperties_proof D hq T L μ0 hL sc G W Mv hM
  have hPre := GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence hDF D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hCM' := hCM D hq T L μ0 hL sc G W Mv hM
  have hStep := GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step hDS hHC hCR hCW D
  have hConj := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCR D
  have hEx := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D

  have rapid : ∀ i, i ≤ D.R.m → ∀ r, IsCoreLat G i r → ∀ M (y : (gridStage G v i r M).CC (gridCom W)) w,
      GlobalTheory.Grow.RapidDec (G.V (.core i)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
    intro i hi r hr M y w
    have hs := (hStage i hi).2 r hr v M
    have h1 := (hConj (gridCom W) hCom i hi _ hs).1 y w
    exact ((hRL.2.1 _ r W.θ _ M ∅).2.2.2.2 _).1 h1.2.2.2.2

  have ext : ∀ k (F₀ : Fn G (.core 0)) (F : Fn G (.core (k + 1))) (f : Sch G (.coreDown k)), Dep W (.core k) f →
      GlobalTheory.Grow.RapidDec (G.V (.core (k + 1))) F → F₀ ∈ Below W v k (dn W v k f F) → F₀ ∈ Below W v (k + 1) F := by
    rintro k F₀ F f hf hF ⟨Ψ, h1, h2, h3, h4⟩
    refine ⟨Function.update Ψ (k + 1) F, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases eq_or_ne i (k + 1) with rfl | hne
      · rw [Function.update_self]; exact hF
      · rw [Function.update_of_ne hne]; exact h1 i (by omega)
    · intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨f', hf', e⟩ := h2 i hik
        refine ⟨f', hf', ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact e
      · obtain rfl : i = k := by omega
        refine ⟨f, hf, ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
        exact h4
    · rw [Function.update_of_ne (by omega)]; exact h3
    · exact Function.update_self _ _ _
  have key : ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧ ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k
      (gridStage G v k r M) Θ ∧ ∃ (I : Type) (N : I → SmT (gridStage G v k r M).M →ₗ[ℂ] SmT (gridStage G v 0 r₀ M₀).M),
      (∀ ι y w, GlobalTheory.EvenOnto.PiLocalization₂.val (Θ y) (N ι w) ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)) ∧
      (gridStage G v 0 r₀ M₀).KF ≤ Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w} := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨r₀, M₀, hr₀, LinearMap.id, GlobalTheory.EvenOnto.Reach.zero, PUnit, fun _ => LinearMap.id, ?_, ?_⟩
      · intro _ y w
        refine ⟨Function.update (fun i => (0 : Fn G (.core i))) 0 (GlobalTheory.EvenOnto.PiLocalization₂.val y w), ?_, ?_, ?_, ?_⟩
        · intro i hi
          obtain rfl : i = 0 := by omega
          show GlobalTheory.Grow.RapidDec _ (GlobalTheory.EvenOnto.PiLocalization₂.val y w)
          exact rapid 0 (Nat.zero_le _) r₀ hr₀ M₀ y w
        · intro i hi; omega
        · exact Function.update_self _ _ _
        · exact Function.update_self _ _ _
      · intro x hx
        exact Submodule.subset_span ⟨PUnit.unit, x, hx, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := ih (by omega)
      obtain ⟨r', hr'⟩ := (hStage (k + 1) hk).1
      obtain ⟨M', -⟩ := hCM' (k + 1) hk
      have hs := (hStage k (by omega)).2 r hr v M
      have hs' := (hStage (k + 1) hk).2 r' hr' v M'
      obtain ⟨ω, f, hpre, hexch, hdep⟩ := hPre k (by omega) r r' hr hr' v M M'
      have hkm : k < (gridCom W).m := by show k < D.R.m; omega
      obtain ⟨p, hpω, hpf, hp⟩ := hStep (gridCom W) hCom k hkm _ _ hs hs' ω f hpre
      subst hpω hpf
      refine ⟨r', M', hr', Θ ∘ₗ p.io, GlobalTheory.EvenOnto.Reach.step hΘ hs' p hp, I × PolF D _ _,
        fun q => N q.1 ∘ₗ p.It q.2, ?_, ?_⟩
      · rintro ⟨ι, P⟩ y w
        have h1 := ha ι (p.io y) (p.It P w)
        have hth : IsThetaFunO W.ψ (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P) :=
          ((hEx W.ψ (G.V (.core k)) (G.V (.core (k + 1))) W.ψ_std).1 _).2 (hdep P).1
        have heq : GlobalTheory.EvenOnto.PiLocalization₂.val (p.io y) (p.It P w) =
            dn W v k (exch (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
          funext g
          refine (hp.io.eq y P w g).symm.trans ?_
          simp only [Formalism.IndefR.Lift.liftInt, dn]
          congr 1
          funext h
          congr 1
          show _ = thetaKO (W.om (.core k)) (negGA _ h) g _
          unfold thetaKO
          rw [hexch _ hth g h]
          have hadj : GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0 = 0 := by
            simp [GlobalTheory.PairLift.adjO]
          show _ = (p.ω (g, h) (p.pt P)) (GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0)
          rw [hadj]
        rw [heq] at h1
        exact ext k _ _ _ (hdep P) (rapid (k + 1) hk r' hr' M' y w) h1
      · intro x hx
        have hx' := hb hx
        refine (Submodule.span_le.2 ?_) hx'
        rintro _ ⟨ι, w, hw, rfl⟩
        have hon := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ _ _ W.θ W.ψ ((gridCom W).a k) ((gridCom W).a k) p.ω p.f p.It
          hCom.inf ⟨(gridCom W).χ k, (gridCom W).χ k, hp.pre.weil, fun τ => ⟨hCom.exp k hkm τ, hCom.exp k hkm τ⟩⟩
          hp.pre.vac hp.it hw
        have hmap : (Submodule.span ℂ {w' | ∃ P, ∃ v' ∈ (gridStage G v (k + 1) r' M').KF, w' = p.It P v'}).map (N ι) ≤
            Submodule.span ℂ {x | ∃ q : I × PolF D _ _, ∃ w ∈ (gridStage G v (k + 1) r' M').KF, x = (N q.1 ∘ₗ p.It q.2) w} := by
          rw [Submodule.map_span]
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨P, v', hv', rfl⟩, rfl⟩
          exact Submodule.subset_span ⟨(ι, P), v', hv', rfl⟩
        exact hmap (Submodule.mem_map_of_mem hon)
  intro k hk
  obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := key k hk
  refine ⟨r, M, hr, Θ, hΘ, fun y x hx => ?_⟩
  let φ : SmT (gridStage G v 0 r₀ M₀).M →ₗ[ℂ] Fn G (.core 0) := (Θ y).1
  have hmap : (Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w}).map φ ≤
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)} := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨ι, w, -, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨w, ha ι y w⟩
  exact hmap (Submodule.mem_map_of_mem (hb hx))

end GlobalTheory.ChainLifts
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineDepthZero



theorem smul_mem_hatMx_of_mem_latO {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S B : HSp D}
    (LS : Lat S) (Λ₀ : Lat B) (hS : IsSelfDualC S LS)
    (hv : ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (e : AE D) (he : IsIdemSum e G.pl.W0) :
    ∀ z ∈ latO S B (LS : Set _) (idLat (shiftId G) Λ₀ : Set _) (fun _ => True),
      e • z ∈ hatMx (G.modul • homLat LS Λ₀) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ∀ t ∈ idLat (shiftId G) Λ₀, ∀ a ∈ D.host.AA,
        e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S B) ∈
          hatMx (G.modul • homLat LS Λ₀) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, y, hy, rfl⟩ := hx
        intro a ha
        have h1 := GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus G (homLat LS Λ₀) e he α hα (a * j)
          (fun w hw => hv w hw _ (FractionalIdeal.mul_mem_mul ha hj)) _
          (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs hy)
        convert h1 using 3
        ext i k
        simp only [Matrix.of_apply, GlobalTheory.LatVac.genMap, Pi.smul_apply, smul_eq_mul]
        ring_nf
      | zero =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (0 : Fin B.rank → D.host.E) i * ∑ k, star (s k) * S.gram k j) : WO S B) = 0 := by
          ext i j; simp
        rw [e0, smul_zero]; exact zero_mem _
      | add x y _ _ hx hy =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (x + y) i * ∑ k, star (s k) * S.gram k j) : WO S B) =
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i * ∑ k, star (s k) * S.gram k j)) +
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * y i * ∑ k, star (s k) * S.gram k j)) := by
          ext i j
          simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, TensorProduct.tmul_add]
        rw [e0, smul_add]; exact add_mem (hx a ha) (hy a ha)
      | smul o x _ hx =>
        intro a ha
        have ha' : a * algebraMap (𝓞 D.host.E) D.host.E o ∈ D.host.AA := by
          rw [mul_comm, ← Algebra.smul_def]; exact Submodule.smul_mem _ o ha
        convert hx _ ha' using 4
        ext i j
        simp only [Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
        ring_nf
    exact key t ht a ha
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LineDepthZero


open GlobalTheory.LineDepthZero in
theorem GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu e he
  have hx := GlobalTheory.T.bessel_step_line_component_mem_hom_lattice D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  have hy := GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _
    (idLat (shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) (G.Λ (.core (2 * 0 + 1))) (fun _ => True)
    (GlobalTheory.T.star_smul_mem_span_modulusDivConjugate_lattice G _) _ hx
  have sdC : IsSelfDualC (G.V (.core (2 * 0 + 1))) (G.Λ (.core (2 * 0 + 1))) := (G.sp.P_is (2 * 0 + 1) (by omega)).sd
  exact smul_mem_hatMx_of_mem_latO G _ _ sdC (GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent hD μ0 hL G) e he _ hy
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastGen

open GlobalTheory.SeeSaw GlobalTheory.SeeSaw.LastPrim

theorem incAdj_yZero_mulVec_gen {D : D7} {S A L T T₀ : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {ρ : ℕ}
    (d : HypDec T T₀ ρ) (hρ : 0 < ρ) (a : AE D) (y : Fin S.rank → AE D) :
    Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.incAdj S (a • yZero S ρ (vecB o ζ))) y =
      GlobalTheory.FinPl.colMul d.jY ⟨ρ - 1, by omega⟩ (incA D D.host.xi0⁻¹ * cA D a * (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) := by
  funext k
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | omega | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, adj_smul, adj_neg, GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]]
  simp only [if_true, mul_one, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring



theorem incAdj_yZero_mem_latO_iff_gen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L T T₀ : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (ρ : ℕ) (d : HypDec T T₀ ρ) (M : Lat S) (LW : Lat T) (LW₀ : Lat T₀) (𝔟 : ℕ → GlobalTheory.SeeSaw.FI D) (𝔠 : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC S M → IsSelfDualC T LW → GlobalTheory.SeeSaw.MonoId d LW LW₀ 𝔟 v → GlobalTheory.SeeSaw.LineId o ζ M 𝔠 v → 𝔠 ≠ 0 → 𝔟 (ρ - 1) ≠ 0 → (∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (𝔟 (ρ - 1))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔠⁻¹) v) → 0 < ρ → ∀ a ∈ idAt D (· = v), d.incAdj S (a • yZero S ρ (vecB o ζ)) ∈ latO S T (M : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  intro D ψ hψ S A L T T₀ o ζ ρ d M LW LW₀ 𝔟 𝔠 v hM hLW hmono hline hc hb0 hid hρ a ha
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hci : 𝔠⁻¹ ≠ 0 := inv_ne_zero hc
  have hb : 𝔟 ((⟨ρ - 1, by omega⟩ : Fin ρ) : ℕ) ≠ 0 := hb0
  have hL0 := colMul_jY_mem_latA_iff D ψ hψ T T₀ ρ d LW (𝔟 (ρ - 1)) v ⟨ρ - 1, by omega⟩ hb
    (GlobalTheory.T.dualIsotropicLine_mem_completion_iff D ψ hψ T T₀ ρ d LW LW₀ 𝔟 v hLW hmono ⟨ρ - 1, by omega⟩ hb)
  have hL : ∀ t ∈ idAt D (· = v), GlobalTheory.FinPl.colMul d.jY ⟨ρ - 1, by omega⟩ t ∈ latA T LW (· = v) ↔
      cA D t ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔠⁻¹) v :=
    fun t ht => (hL0 t ht).trans (hid _)
  have e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1 := by
    rw [← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]
  have key : ∀ y ∈ latV S M (· = v),
      (Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from
        d.incAdj S (a • yZero S ρ (vecB o ζ))) y ∈ latA T LW (· = v) ↔
        a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v) := by
    intro y hy
    have hzi : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
      sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)
    rw [incAdj_yZero_mulVec_gen o ζ d hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
      h3 _ _ (inv_ne_zero hξ)]
    have e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) =
        -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) := by
      rw [← mul_assoc, ← mul_assoc, e3]; ring
    rw [e4, neg_mem_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M LW hM hLW]
  constructor
  · rintro ⟨-, hu⟩
    obtain ⟨g, hg, g', -, hgg, hiff⟩ := h6 𝔠⁻¹ hci
    obtain ⟨y, hy, hyg⟩ := GlobalTheory.T.hermitianPairing_onto_inverseIdeal_at_place D ψ hψ S A L o ζ M 𝔠 v hM hline hc g hg
    have h7 := ((hiff _).1 ((key y hy).1 (hu y hy))).2
    rw [hyg] at h7
    rw [← hgg a ha]
    have e6 : g' * g * a = g' * (a * g) := by rw [mul_assoc, mul_comm g a]
    rw [e6]; exact h7
  · intro haI
    have hcA : cA D a ∈ idAt D (· = v) := by
      have := (h4 0 a).1 (by rw [zpow_zero]; exact (h1 a).2 haI)
      rw [zpow_zero] at this
      exact ((h1 _).1 this).1
    refine ⟨fun k l => ?_, fun y hy => (key y hy).2 ?_⟩
    · have e5 := congrFun (incAdj_yZero_mulVec_gen o ζ d hρ a (Pi.single l 1)) k
      rw [Matrix.mulVec_single_one] at e5
      refine (congrArg (· ∈ idAt D (· = v)) e5).mpr ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))
    · have hmul := (h2 𝔠⁻¹ 𝔠⁻¹ hci hci a ha).2 (by rw [mul_inv_cancel₀ hci]; exact (h1 a).2 haI)
      exact hmul _ (GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion D ψ hψ S A L o ζ M 𝔠 v hM hline hc y hy)

end GlobalTheory.LastGen

namespace GlobalTheory.AscFin

theorem incAdj_yBF_mem_latO_iff : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, 0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v hv hρ a ha
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hoff T L μ0 hL sc G W M hM F hF
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hsdJ := (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (by simp)).sd
  obtain ⟨hb0, hc0, hid⟩ := GlobalTheory.T.staircase_ideals_completion_eq_of_modulus_unit G.pl sc ρ v hρ (GlobalTheory.T.modulus_ideal_off_S0_trivial G.pl sc v hv)
  exact GlobalTheory.LastGen.incAdj_yZero_mem_latO_iff_gen D W.ψ hψ _ _ _ _ _ (F.oB ρ h) (F.ζ (ρ + 1)) ρ (F.dJ ρ h) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0))
    (G.Λ (.core (2 * ρ + 1)))
    (fun i => FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i) * (G.pl.stAbar sc ^ (i + 1))⁻¹))
    _ v (I.2.1 ρ h).1 hsdJ ⟨((I.2.1 ρ h).2.1 v).2, fun i b hb => GlobalTheory.T.staircase_lattice_isotropic_line_ideal_iff D hoff T L μ0 hL sc G W M hM F hF ρ h v i b hb⟩
    (GlobalTheory.T.lineId_oB_lat0_of_pl D hoff T L μ0 hL sc G W M hM F hF ρ h v) hc0 hb0 hid hρ a ha

end GlobalTheory.AscFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

theorem pcFB_dualA : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h'
  have hi : 2 * σ + 2 < D.R.m := by omega
  refine pieces_dualA (d := F.dJ (σ + 1) h) (ψ := W.ψ) (Γ := latRow G (2 * σ + 2)) (F.dB σ h') (latBig G (2 * σ + 2))
    (GlobalTheory.T.jacobi_depth_lattice_keeps_isotropic_hom_part D hD T L μ0 hL sc G W M hM F hF σ h) (GlobalTheory.AscFin.RowAnn.annRow_isCompact D hD T L μ0 hL sc G W M hM _ hi) (GlobalTheory.AscFin.AnnOpen.latRow_ann_open D hD T L μ0 hL sc G W M hM _ hi)
    (fun u hu hb => GlobalTheory.T.depthLatticeFirstRow_eq_doubleAnnihilator D hD T L μ0 hL sc G W M hM _ hi u hu fun u' hu' hv => hb u' ⟨hu', hv⟩)

end GlobalTheory.AscFin.AnnPieces

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  first | exact @GlobalTheory.LineAdjZero.adj_lineComp_mem_latO | exact GlobalTheory.LineAdjZero.adj_lineComp_mem_latO | (intros; apply GlobalTheory.LineAdjZero.adj_lineComp_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)), (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) → W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h')) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  first | exact @GlobalTheory.CharXFB.charx_fb | exact GlobalTheory.CharXFB.charx_fb | (intros; apply GlobalTheory.CharXFB.charx_fb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansionPairing_invariant_parabolic_basePoint : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.TopZeroInv.pairPts_update_top_zero | exact GlobalTheory.TopZeroInv.pairPts_update_top_zero | (intros; apply GlobalTheory.TopZeroInv.pairPts_update_top_zero <;> assumption)
end
