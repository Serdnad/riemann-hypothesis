module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle147
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle149
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle054
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.LvT.TrueStep0.step0Tie_trueCols | exact GlobalTheory.LvT.TrueStep0.step0Tie_trueCols | (intros; apply GlobalTheory.LvT.TrueStep0.step0Tie_trueCols <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_opU_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Formalism.L2.Th1.H.Sesq V) (x : V) {F : V → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU H x F) := by
  have h1 : ContDiff ℂ ⊤ F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := fun z => H z x
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hl : ContDiff ℂ ⊤ (fun z => H z x) := (LinearMap.toContinuousLinearMap f).contDiff
  have h2 : ContDiff ℂ ⊤ (fun z => F (z + x)) := h1.comp (contDiff_id.add contDiff_const)
  have h3 : ContDiff ℂ ⊤ (fun z => Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) :=
    ((contDiff_const.mul hl).sub contDiff_const).cexp
  exact h2.mul h3

theorem latInt_U_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hP N N' s hs
  have hS := B.stdOK hcc hδ
  have han : AnalyticOnNhd ℂ B.thMM Set.univ := (B.thMM_spec hS).1.1
  have hLat : La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have hA : area (lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  set G : Fin N' → Fin N → (D.what₂.Tau → ℂ) → ℂ := fun i j =>
    Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ i j) B.thMM with hG
  have hU : U D B.tor s (B.thZero N N') = fun z => ∏ i, ∏ j, G i j (entry D.what₂.Tau N N' i j z) := by
    funext z
    rw [U_eq]
    show Formalism.L2.Th1.H.opU (formV (area (lamOf D cc δ)) D.what₂.Tau N N') s (tensPow B.thMM N N') z = _
    rw [hA, opU_tensPow]
    rfl
  have hGc : ∀ i j, ContDiff ℂ ⊤ (G i j) := fun i j => contDiff_opU_of_analytic _ _ han
  have hEc : ∀ i j, ContDiff ℂ ⊤ (fun z : VC D N N' => G i j (entry D.what₂.Tau N N' i j z)) :=
    fun i j => (hGc i j).comp (entry D.what₂.Tau N N' i j).contDiff
  obtain ⟨n, -, hnq, hns⟩ := hs
  rw [hLat] at hns
  have hF : ∀ i j, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (fun z => G i j (entry D.what₂.Tau N N' i j z)) := by
    intro i j
    have hm : LatInt ι (Ω / ι δ₀) B.lamM (G i j) := by
      refine GlobalTheory.T.cmTheta_baseVector_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hP (fun τ => s τ i j) n hnq ?_
      have := hns i j
      convert this using 1
      funext τ
      simp [nsmul_eq_mul]
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (D.what₂.Tau → ℂ) (VC D N N') (Ω / ι δ₀) B.lamM
      (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (entry D.what₂.Tau N N' i j) (G i j) (hGc i j) ?_ hm
    intro x hx
    rw [hLat] at hx
    exact ⟨1, Nat.coprime_one_left q, by rw [one_smul]; exact hx i j⟩
  rw [hU]
  refine (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N')
    (fun i z => ∏ j, G i j (entry D.what₂.Tau N N' i j z)) (fun i => ?_) (fun i => ?_)
  · exact contDiff_prod fun j _ => hEc i j
  · exact (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N)
      (fun j z => G i j (entry D.what₂.Tau N N' i j z)) (hEc i) (hF i)

end GlobalTheory.MomN
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.EX.DQ NumberField IsDedekindDomain

namespace GlobalTheory.EX.DQ



theorem twGoodOne_setDiv (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b))
    (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (p : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (H : TwGoodOne D ⟨twEOf O.xd, N0, S⟩ i b Q k p) :
    TwGoodOne (setDiv D N h) ⟨twEOf (O.tr N h).xd, N0, S⟩ i b Q k p := by
  unfold TwGoodOne at H ⊢
  have e1 : AvRec (setDiv D N h) = AvRec D := rfl
  have e2 : twEps (setDiv D N h) i = twEps D i := rfl
  rw [e1, e2]
  unfold IntegralHeckeForms.GoodTw at H ⊢
  obtain ⟨h1, ⟨eB, h2, h3, h4⟩, h5, h6, h7, h8⟩ := H
  exact ⟨h1, ⟨eB, h2, h3, h4⟩, fun j hj c => ⟨(h5 j hj c).1, (h5 j hj c).2⟩, h6, h7, h8⟩

theorem qd_setDiv : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    QD D O → QD (setDiv D N h) (O.tr N h) := by
  rintro D O N h ⟨h1, ⟨hc, N0, S, hS⟩, h3⟩
  refine ⟨h1, ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, fun a ha => ?_⟩⟩, h3⟩
  exact twGoodOne_setDiv D O N h N0 S _ _ _ _ _ ((hS w hw).2 a ha)

end GlobalTheory.EX.DQ
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.PoissonSum

theorem countable_F (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem rat_add (ξ η : Fin N → F) : (rat (ξ + η) : Fin N → AF F) = rat ξ + rat η := by
  funext l; simp [rat]

theorem rat_neg (ξ : Fin N → F) : (rat (-ξ) : Fin N → AF F) = -rat ξ := by
  funext l; simp [rat]

theorem Bd_add_left (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.add_apply]; ring

theorem Bd_neg_right (a : Fin N → F) (u w : Fin N → AF F) :
    Bd (AF F) a u (-w) = -Bd (AF F) a u w := by
  simp only [Bd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.neg_apply]; ring

theorem Bd_zero_left (a : Fin N → F) (w : Fin N → AF F) : Bd (AF F) a 0 w = 0 := by
  simp [Bd]

theorem Bd_rat (a : Fin N → F) (ξ η : Fin N → F) :
    Bd (AF F) a (rat ξ) (rat η) = algebraMap F (AF F) (Bd F a ξ η) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Bd, rat, map_sum, map_mul]

theorem continuous_Bd_right (a : Fin N → F) (w : Fin N → AF F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u w := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.PoissonSum

open GlobalTheory.SWQ.PoissonSum in
theorem GlobalTheory.SWQ.poisson_summation : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → th (Fo ψ ν a Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ
  haveI := countable_F F
  have hψ := hC.2.1
  obtain ⟨hHaar, hmem, hinj, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  haveI := hHaar
  obtain ⟨hint, hsum, hcont⟩ := GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 Φ hΦ
  obtain ⟨-, hsumF, -⟩ := GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 _ hFΦ
  set P : (Fin N → AF F) → ℂ := fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) with hP
  have hper : ∀ ξ u, P (rat ξ + u) = P u := by
    intro ξ u
    simp only [hP]
    refine Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => Φ (rat η + u)))
    simp [rat_add, add_assoc]
  have hcoef : ∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = Fo ψ ν a Φ (rat (-ξ)) := by
    intro ξ
    set G := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
    let e : (Fin N → F) ≃ G := Equiv.ofBijective (fun η => ⟨rat η, (hmem _).2 ⟨η, rfl⟩⟩)
      ⟨fun η η' h => hinj (congrArg Subtype.val h), fun γ => by
        obtain ⟨η, hη⟩ := (hmem γ.1).1 γ.2
        exact ⟨η, Subtype.ext hη.symm⟩⟩
    haveI : Countable G := e.surjective.countable
    set g : (Fin N → AF F) → ℂ := fun u => Φ u * ψ (-(Bd (AF F) a u (rat ξ))) with hg
    have hgc : Continuous g :=
      hΦ.1.mul (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)
    have hgn : ∀ u, ‖g u‖ = ‖Φ u‖ := fun u => by simp [hg, hψ.2.1]
    have hgi : Integrable g (muV N ν) :=
      (hint _ hHaar).norm.mono' hgc.aestronglyMeasurable (Eventually.of_forall fun u => (hgn u).le)
    have hshift : ∀ η u, g (rat η + u) = Φ (rat η + u) * ψ (-(Bd (AF F) a u (rat ξ))) := by
      intro η u
      simp only [hg, Bd_add_left, Bd_rat, neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ.2.2.1, one_mul]
    have hFo : Fo ψ ν a Φ (rat (-ξ)) = ∫ u, g u ∂(muV N ν) := by
      simp only [Fo, hg, rat_neg, Bd_neg_right]
    rw [hFo, hD.integral_eq_tsum'' g hgi, ← e.tsum_eq]
    have hvadd : ∀ η u, (e η +ᵥ u : Fin N → AF F) = rat η + u := fun η u => rfl
    simp_rw [hvadd, hshift]
    simp only [hP]
    simp_rw [← tsum_mul_right]
    refine integral_tsum (fun η => ?_) ?_
    · exact ((hΦ.1.comp (continuous_const.add continuous_id)).mul
        (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)).aestronglyMeasurable
    · have hl := hD.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)
      rw [← e.tsum_eq] at hl
      simp_rw [hvadd] at hl
      have hfin : ∫⁻ u, ‖Φ u‖ₑ ∂(muV N ν) ≠ ∞ := (hint _ hHaar).2.ne
      simp only [← ofReal_norm_eq_enorm] at hl ⊢
      simp only [norm_mul, hψ.2.1, mul_one]
      rw [← hl]
      simpa [ofReal_norm_eq_enorm] using hfin
  have hsc : Summable (fun ξ : Fin N → F => ‖Fo ψ ν a Φ (rat (-ξ))‖) := by
    have h := hsumF 0
    simp only [add_zero] at h
    exact (Equiv.neg (Fin N → F)).summable_iff.2 h
  have key := GlobalTheory.T.adelic_fourierSeries_of_summable_coefficients F N ψ lam ν a hC D hD hD1 P _ hcont hper hcoef hsc 0
  have h0 : P 0 = th Φ := by simp [hP, th]
  rw [h0] at key
  rw [key, th]
  refine ((Equiv.neg (Fin N → F)).tsum_eq (fun ξ => Fo ψ ν a Φ (rat ξ))).symm.trans (tsum_congr fun ξ => ?_)
  simp [Bd_zero_left]
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem perDecTwT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) (Y : DivX (I.rec7 l Z)), I.StdTw l Z l0 t → ∀ u a ha, GlobalTheory.PerQ.PerDecTwT Y t u a ha := by
  intro B X I hI l Z l0 hR cf nch tp C t Y hS u a ha x hx F hF c
  have hP := (t.ptE.per u a ha).2.2
  classical
  have hres : ∀ z, GlobalTheory.PerQ.resCTw t u a ha c z = fun c' => if c' = c then z c' else 0 := by
    intro z
    apply (t.pt.val u a ha).eW.injective
    rw [GlobalTheory.PerQ.resCTw, LinearEquiv.apply_symm_apply]
    funext c' s
    have e1 := hS.2.2.eW u a ha (fun c' => if c' = c then z c' else 0) c' s s rfl
    have e2 := hS.2.2.eW u a ha z c' s s rfl
    refine Eq.trans ?_ e1.symm
    split_ifs
    all_goals first | exact e2 | rfl | (exfalso; contradiction)
  obtain ⟨y, hy, hyv⟩ := hR.tw u a F hF c
  have hyQ : y ∈ nabAt B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c)) := by
    have := GlobalTheory.PeriodOnStep.Lsh_eq_N ((I.stX a).rep c).1.1.deco
    show y ∈ nabAt _ _ (((I.stX a).rep c).1.1.deco.1.Lsh)
    rw [this]; exact hy
  obtain ⟨b, hb⟩ := @GlobalTheory.T.classPairing_integral_form_row_isIntegral _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL _ _ (I.perIn u a) (l.ch u a) (l.per u a) (B.hcW u)
    (l.fmL u a).famP (((I.rec7 l Z).eMtTw u a).symm F) (t.ptE.jM u a (((I.rec7 l Z).eMtTw u a).symm F))
    (fun w => hP w _) c (fun p q => Classical.propDecidable (p = q)) y hyQ hyv x hx
  refine ⟨(b : B.fields.K), ?_, fun w _ => ?_⟩
  · show B.embLL (b : B.fields.K) = _
    rw [hb, GlobalTheory.PerQ.pcLTw, hres, hres]
    rfl
  · by_cases h0 : (b : B.fields.K) = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      unfold vAdd
      have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := (I.rec7 l Z).what₂.LL) ((I.rec7 l Z).plEq w) b
      have h2 := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 h0) one_ne_zero).2 h
      rw [WithZero.log_one] at h2
      exact neg_nonneg.mpr h2

end GlobalTheory.PerTwClose
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerQ.ptT_forms_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), (∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi B.R.m, GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ ∈ ((I.tw l l0 Z).fm u a).ptC) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I hI l Z l0 u a
  have hW := fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ
  refine ⟨?_, ?_⟩
  swap
  · have ⟨τ⟩ : Nonempty B.fields.Tau := inferInstance
    exact (hW τ).2.2.2.2
  intro φ hφ
  set M := I.fm l u a with hM
  have key : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
      (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x)) := by
    intro x hx
    obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := I.perIn u a) B.fields.emb B.embLL (B.hcW u)
      GlobalTheory.LvT.BuiltChain.branching_ok (l.ch u a) (l.per u a)
      (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
    exact ⟨y, hy⟩
  have rat : ∀ x, ∃ y, M.ptEmb y = (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x)) := by
    intro x
    have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
      rw [(M.lat_good B.R.m).2.2]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, e⟩ := ha
      obtain ⟨z, e'⟩ := hb
      exact ⟨y + z, by rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), e, e']⟩
    | smul r a _ ha =>
      obtain ⟨y, e⟩ := ha
      refine ⟨r • y, ?_⟩
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, LinearMap.map_smul, LinearMap.map_smul]
  have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
    intro y

    rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hφ' : φ ∈ M.Fi B.R.m := hφ
  rw [← (M.emb_basis B.R.m).2] at hφ'
  have hle : Submodule.span ℂ (Set.range fun a => M.emb B.R.m ((M.lat B.R.m).b a)) ≤
      M.ptC.comap ((I.per l u a).lowerMap ∘ₗ (I.per l u a).evz) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    obtain ⟨y, e⟩ := rat ((M.lat B.R.m).b b)
    show (I.per l u a).lowerMap ((I.per l u a).evz _) ∈ M.ptC
    rw [← e]
    exact ptMem y
  exact hle hφ'
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem _root_.GlobalTheory.T.lowerTwistedCompatible_of_evaluationBranching : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_to_lib | exact GlobalTheory.PerQ.lowerTieTwAt_to_lib | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_to_lib <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerDecAtRef


open Formalism.BasicNotions in
theorem vAdd_nonneg_of_int {K : Type} [Field K] [NumberField K] (la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) : 0 ≤ vAdd la (a : K) := by
  have h : la.valuation K (a : K) ≤ 1 := la.valuation_le_one a
  unfold vAdd
  rcases eq_or_ne (la.valuation K (a : K)) 0 with h0 | h0
  · rw [h0, WithZero.log_zero]; simp
  · have h1 : WithZero.log (la.valuation K (a : K)) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp h0]
      simpa using h
    exact neg_nonneg.mpr h1

end GlobalTheory.PerDecAtRef



theorem GlobalTheory.PerDecAtRef.perDec0At_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → Formalism.MainNotions.RT.PeriodPointConditions.PerDec0At F := by
  intro B X I hI l Z hZ u Ch chOf F hF
  intro x hx G hG c
  classical
  obtain ⟨y0, hy0, hrd⟩ := hZ.ref u G hG c
  have hpr : ∀ w, ((I.perIn u I.mu0).per B.fields.emb B.embLL (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)).period w
      (((I.rec7 l Z).eMt u).symm G) = (I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0)
      (F.jM (((I.rec7 l Z).eMt u).symm G)) w := by
    intro w
    have hper := F.per
    unfold Formalism.L2.Forms.PerTie at hper
    exact hper.2.2 w _
  have key := GlobalTheory.T.classPairing_integral_form_row_isIntegral B.fields.emb B.embLL (I.perIn u I.mu0) (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)
    (l.fmL u I.mu0).famP (((I.rec7 l Z).eMt u).symm G) (F.jM (((I.rec7 l Z).eMt u).symm G)) hpr c y0 ?ha ?hb
  case ha =>
    clear hpr hZ hI hx hG hrd hF
    have hL : (I.perIn u I.mu0).S'.Lsh c.fst ((I.perIn u I.mu0).S'.rep c) = (((I.stX I.mu0).rep c).1.1.deco).1.N :=
      GlobalTheory.PeriodOnStep.Lsh_eq_N _
    rw [hL]
    exact hy0
  case hb =>
    clear hpr hZ hI hx hG hy0 hF
    convert hrd using 2
  obtain ⟨a, ha⟩ := key x hx
  refine ⟨(a : B.fields.K), ?_, ?_⟩
  · have hw := hF.eW
    have hsingle : ∀ (dec : ∀ c' : ((I.rec7 l Z).fm u).clsP, Decidable (c' = c)) (v : ((I.rec7 l Z).mem u).P.Wrow),
        F.valP.eW.symm (fun c' => @ite _ (c' = c) (dec c') (F.valP.eW v c') 0) =
          fun (c' : (I.perIn u I.mu0).S'.Cl) => if c' = c then v c' else 0 := by
      intro dec v
      apply F.valP.eW.injective
      rw [LinearEquiv.apply_symm_apply]
      funext c' s
      erw [hw _ c' s ⟨s.1, s.2⟩ rfl]
      by_cases h : c' = c
      · rw [if_pos h, if_pos (show @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        erw [hw v c' s ⟨s.1, s.2⟩ rfl]
      · rw [if_neg h, if_neg (show ¬ @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        rfl
    unfold Formalism.MainNotions.RT.PeriodPointConditions.pcL Formalism.MainNotions.RT.PeriodPointConditions.resC
    rw [hsingle, hsingle]
    clear key hpr hrd hy0 hG hZ hI hx hsingle hw hF
    refine ha.trans ?_
    congr! 4
    exact congrArg (fun f => ⇑((I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0) f))
      (funext fun c' => by by_cases h : c' = c <;> simp [h])
  · intro w
    right
    exact GlobalTheory.PerDecAtRef.vAdd_nonneg_of_int _ a
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem _root_.GlobalTheory.T.twistedPeriodDecomposition_of_classwiseTwistedPairingIntegral : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  first | exact @GlobalTheory.PerRedTw.reduction_perDecTw | exact GlobalTheory.PerRedTw.reduction_perDecTw | (intros; apply GlobalTheory.PerRedTw.reduction_perDecTw <;> assumption)
end
