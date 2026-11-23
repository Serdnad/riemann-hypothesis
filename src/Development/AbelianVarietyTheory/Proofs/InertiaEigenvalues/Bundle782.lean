module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle772
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle771
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle774
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem wseedRec_ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem wseedRec_ρ₀_lt_one (bk : BK K) : bk.ρ₀ < 1 := by
  unfold BK.ρ₀
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0:ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith

theorem wseedRec_frobS_norm (bk : BK K) :
    ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
  rw [frobS_X]
  refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l (wseedRec_ρ₀_pos bk)).trans ?_
  exact pow_le_of_le_one bk.ρ₀.coe_nonneg (by exact_mod_cast (wseedRec_ρ₀_lt_one bk).le) hl.out.ne_zero

theorem wseedRec_comm (bk : BK K) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hj : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j)
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ)
    (ΦS : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (hΦS : IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) ΦS) (x : bk.DS bk.ρ₀) :
    Φ (j x) = j (ΦS x) := by
  have h1 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (Φ.comp j) :=
    ⟨fun a => by simp [hj.ext, hΦ.ext, bk.ev_frob], fun x => (hΦ.norm_le _).trans (hj.norm_le x)⟩
  have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (j.comp ΦS) :=
    ⟨fun a => by simp [hj.ext, hΦS.ext], fun x => (hj.norm_le _).trans (hΦS.norm_le x)⟩
  exact RingHom.congr_fun (h1.unique h2) x

theorem wseedRec_frobS_E_ne_zero (bk : BK K) : frobS l bk.a bk.E ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff (l * bk.Ep.natDegree)) h
  simp [frobS, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at this

theorem wseedRec_ev_injective (bk : BK K) {ι : Type} (TB : TopBasis bk.ev bk.J ι) : Function.Injective bk.ev := by
  have hb : TB.c TB.i₀ 1 = 1 := by rw [← TB.b_i₀]; exact TB.c_self _
  have hev : ∀ x, TB.c TB.i₀ (bk.ev x) = x := fun x => by simpa [hb] using TB.c_mul TB.i₀ x 1
  intro x y h
  rw [← hev x, h, hev]

theorem wseed_coeff_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  intro l _ K bk τ hτ d ρ hρ s ι TB j hj cD hc hcm hsum hnorm Φ hΦ i₁ a b
  have h0 := wseedRec_ρ₀_pos bk
  have h1 := wseedRec_ρ₀_lt_one bk
  obtain ⟨hdom, -, -⟩ := GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1
  let ΦS := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (X : bk.S)) (ρ' := bk.ρ₀)
    (frobS l bk.a) (wseedRec_frobS_norm bk)
  have hΦS : IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) ΦS := isDiscMap_map _ _
  have hcomm : ∀ x, Φ (j x) = j (ΦS x) := wseedRec_comm bk j hj Φ hΦ ΦS hΦS
  have hjS : ∀ t, j (toDisc l (X : bk.S) bk.ρ₀ t) = bk.iS t := fun t => hj.ext t
  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := fun x => hΦ.ext x
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound (cD i) 1 (fun y => by rw [one_mul]; exact hnorm i y)
  have hΦc : Continuous Φ :=
    AddMonoidHomClass.continuous_of_bound Φ 1 (fun y => by rw [one_mul]; exact hΦ.norm_le y)
  have hjc : Continuous j :=
    AddMonoidHomClass.continuous_of_bound j 1 (fun y => by rw [one_mul]; exact hj.norm_le y)
  let c : ι → bk.DA bk.ρ₀ := fun i => bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))
  let L : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀ := (j : bk.DS bk.ρ₀ →+ bk.DA bk.ρ₀).comp (cD i₁)
  have hLa : ∀ y, L y = j (cD i₁ y) := fun y => rfl
  have hLc : Continuous L := hjc.comp (hcont i₁)
  have hL : ∀ t y, L (bk.iS t * y) = bk.iS t * L y := by
    intro t y
    rw [hLa, hLa, ← hjS, hcm, map_mul]
  have key : ∀ y, HasSum (fun i => Φ (j (cD i y)) * c i) (L (Φ y)) := by
    intro y
    have h := ((hsum y).map (Φ : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀) hΦc).map L hLc
    convert (preTransparency := .reducible) h using 1
    · funext i
      simp only [Function.comp_apply, AddMonoidHom.coe_coe]
      rw [map_mul Φ, hΦA, hcomm, hLa, hcm, hc, map_mul, hjS]
    · rfl
  have stepA : HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * c i)
      ((s.W.map Φ * (s.W'.map Φ).map L) a b) := by

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    refine hasSum_sum fun k _ => ?_
    simp_rw [mul_assoc]
    exact (key (s.W' k b)).mul_left (Φ (s.W a k))
  haveI := hdom
  have hphi := GlobalTheory.T.frobenius_matrix_relation_discrete l K bk τ hτ d ρ hρ s Φ hΦ
  have hwp := GlobalTheory.T.semistablePeriod_frobenius_of_scaled_inverse l K bk τ hτ d ρ hρ s Φ hΦ
  have hmapL : ∀ (M : Matrix (Fin d) (Fin d) bk.S) (Y : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (M.map bk.iS * Y).map L = M.map bk.iS * Y.map L := by
    intro M Y
    ext k m

    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hL]
  have hμ : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N * bk.iS bk.E ^ (2 * s.N) =
      bk.iS ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N * bk.E ^ (2 * s.N)) := by
    simp only [map_mul, map_pow, map_natCast]
  have hBL : (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS *
      (s.W'.map Φ).map L = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N *
        bk.iS bk.E ^ (2 * s.N)) • s.W'.map L := by
    rw [← hmapL, hwp]
    ext k m
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul, hμ, hL]
  have hWJ : s.W'.map L = (s.W'.map (cD i₁)).map j := by ext; rfl
  have heq : ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (s.W.map Φ * (s.W'.map Φ).map L) = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (bk.iS bk.E ^ (2 * s.N) • (s.W * (s.W'.map (cD i₁)).map j)) := by
    conv_lhs => rw [← Matrix.smul_mul, hphi, Matrix.mul_assoc, hBL, Matrix.mul_smul]
    rw [smul_smul, hWJ]
  have hE0 : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    intro h
    apply wseedRec_frobS_E_ne_zero bk
    apply wseedRec_ev_injective bk TB
    rw [map_zero]
    apply (toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1).1
    rw [map_zero]
    exact h
  have hlam : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero) (pow_ne_zero _ hE0)
  have hab := congrFun (congrFun heq a) b
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hab
  have h2 := mul_left_cancel₀ hlam hab
  rw [Matrix.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  exact stepA

end GlobalTheory.BSP
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open scoped GlobalTheory.GaugeEx

noncomputable section
namespace GlobalTheory.RallisCusp

theorem nonGraph_sum_eq_zero : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  intro D hEis hMove hInv hKill hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI : Countable (Lag W) := lag_countable D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  haveI := hS.haarW
  have hw := hS.weil
  have hpres : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hw.om_pres
  have hom : ∀ (g h : GA D W) f, om (1, g) (om (1, h) f) = om (1, g * h) f := by
    intro g h f
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

  have hmove : ∀ (γ : GQ W) (Y : Lag W) (g : GA D W) (F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₂ →
      lagTerm μ 𝓕 (fr (lagAct W γ Y)) (om (1, g) f₁) F₂ = lagTerm μ 𝓕 (fr Y) (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ := by
    intro γ Y g F₂ hF₂
    have h1 := (hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, g) f₁) F₂ (hpres _ _ hf₁) hF₂).1
      (lagAct W γ Y) _ (isLagFrame_lagAct W γ Y (fr Y) (hS.frame Y))
    have h2 := ((hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ (hpres _ _ hf₁) hF₂).2
      γ γ.2 (gqMat W γ) (gqMat_map W γ).symm).1 (fr Y)
    rw [← h1, ← h2, hom, mul_inv_cancel_left]

  have hslice : ∀ g₂ : GA D W, ∑' Y : NGLag W, ∫⁻ g in 𝓖, ‖star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)‖ₑ ∂νW ≠ ⊤ →
      ∑' Y : NGLag W, ∫ g in 𝓖, star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) ∂νW = 0 := by
    intro g₂ hfin
    have hF₂ := hpres (1, g₂) f₂ hf₂
    have hGQ : Countable (GQ W) := by
      haveI : Countable (Matrix (Fin W.rank) (Fin W.rank) D.host.E) :=
        inferInstanceAs (Countable (Fin W.rank → Fin W.rank → D.host.E))
      refine Function.Injective.countable (f := fun γ : GQ W => gqMat W γ) ?_
      intro γ δ h
      apply Subtype.ext
      apply GlobalTheory.MixModel.mt_injective W
      have := congrArg (fun c => c.map (incA D)) h
      simpa only [gqMat_map] using this
    refine GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals νW inferInstance (GQ W) hGQ 𝓖 hS.fdW (ngAct W) (ngAct_one W) (ngAct_mul W)
      (fun Y g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) ?_ ?_ hfin ?_
    · intro γ Y g
      show star (φ₁ g) * lagTerm μ 𝓕 (fr (lagAct W γ Y.1)) _ _ = _
      rw [hmove γ Y.1 g _ hF₂, ha₁.left _ (inv_mem γ.2) g]
    · intro Y
      exact ((continuous_star.comp ha₁.cont).mul (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2)).aestronglyMeasurable
    · intro Y Γ hΓ 𝓓 h𝓓 hint
      obtain ⟨s, I, hI, hspan⟩ := GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand D W Y.1 Y.2
      have hle : Γ ≤ GQ W := fun g hg => ((hΓ g).1 hg).1
      have hfix : ∀ g (hg : g ∈ Γ), lagAct W ⟨g, hle hg⟩ Y.1 = Y.1 := by
        intro g hg
        obtain ⟨h, e⟩ := (hΓ g).1 hg
        exact congrArg Subtype.val e
      have key := hKill W νW hS.haarW s I hI Γ hle
        (fun n hn => (hΓ n).2 ⟨hn.2, Subtype.ext (GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent D W Y.1 s I hI hspan ⟨n, hn.2⟩ hn.1)⟩)
        (fun γ hγ n hn => GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent D W Y.1 s I hI hspan ⟨γ, hle hγ⟩ (hfix γ hγ) n hn) 𝓓 h𝓓
        (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) (fun g => star (φ₁ g))
        (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2) ?_ ?_ ?_ ?_ ?_
      · rw [← key]
        congr 1
        funext g
        ring
      · intro γ hγ g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, γ * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        have := hmove ⟨γ, hle hγ⟩ Y.1 (γ * g) _ hF₂
        rw [hfix γ hγ] at this
        rw [this]
        congr 3
        exact congrArg (Prod.mk 1) (inv_mul_cancel_left γ g)
      · intro n hn g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, n * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        rw [← hom]
        exact hInv ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y.1 s I hI hspan n hn _ _ (hpres _ _ hf₁) hF₂
      · exact ⟨fun γ hγ g => by show star (φ₁ (γ * g)) = star (φ₁ g); rw [ha₁.left γ hγ g],
          by
            obtain ⟨U, hU, hk⟩ := ha₁.level
            exact ⟨U, hU, fun k hk1 hk2 g => by show star (φ₁ (g * k)) = star (φ₁ g); rw [hk k hk1 hk2 g]⟩,
          continuous_star.comp ha₁.cont⟩
      · intro r C hC μ' 𝓕' hμ' h𝓕' g
        have := hc₁ r C hC μ' 𝓕' hμ' h𝓕' g
        show ∫ n in 𝓕', (starRingEnd ℂ) (φ₁ ((n : GA D W) * g)) ∂μ' = 0
        rw [integral_conj, this, map_zero]
      · have e : (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) =
            fun g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) := funext fun g => mul_comm _ _
        show IntegrableOn (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) 𝓓 νW
        rw [e]
        exact hint
  have hφ₁c : Continuous φ₁ := ha₁.cont
  refine GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' (X := NGLag W) inferInstance νW inferInstance 𝓖
    (fun Y p => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂)) ?_ ?_ ?_
  · intro Y
    have hm := GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hw hS.covol f₁ f₂ hf₁ hf₂ (fr Y.1)
    exact (((continuous_star.comp hφ₁c).comp continuous_fst).mul (ha₂.cont.comp continuous_snd)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable
  · have h0 := hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂
    refine ne_top_of_le_ne_top h0 (lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_)
    have e : ∀ Y : NGLag W, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ =
        (fun Y : Lag W => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ) Y.1 := by
      intro Y
      have hs : ‖star (φ₁ g₁)‖ₑ = ‖φ₁ g₁‖ₑ := by simp [enorm_eq_nnnorm]
      simp only
      rw [enorm_mul, enorm_mul, hs]
      ring
    rw [tsum_congr e]
    exact (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
  · intro g₂ hfin
    by_cases h0 : φ₂ g₂ = 0
    · simp [h0]
    · have e1 : ∀ Y : NGLag W, ∫ g₁ in 𝓖, star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW =
          φ₂ g₂ * ∫ g₁ in 𝓖, star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW := by
        intro Y
        rw [← integral_const_mul]
        congr 1
        funext g₁
        ring
      have e2 : ∀ Y : NGLag W, ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW =
          ‖φ₂ g₂‖ₑ * ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW := by
        intro Y
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        congr 1
        funext g₁
        rw [enorm_mul, enorm_mul, enorm_mul]
        ring
      simp only at hfin ⊢
      rw [tsum_congr e2, ENNReal.tsum_mul_left] at hfin
      rw [tsum_congr e1, tsum_mul_left, hslice g₂ ?_, mul_zero]
      intro htop
      rw [htop, ENNReal.mul_top (enorm_ne_zero.2 h0)] at hfin
      exact hfin rfl

end GlobalTheory.RallisCusp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.SWAbsInv

open GlobalTheory.RallisCusp

variable {D : D7}

def lagSwap (W : HSp D) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (LinearEquiv.prodComm D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)).toLinearMap, by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    exact (Y.2.2 y hy y' hy').symm⟩

theorem lagSwap_lagSwap (W : HSp D) (Y : Lag W) : lagSwap W (lagSwap W Y) = Y := by
  apply Subtype.ext
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨y.swap, ⟨y, hy, rfl⟩, rfl⟩

theorem isLagFrame_lagSwap (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) : IsLagFrame W (lagSwap W Y) (C.2, C.1) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (LinearEquiv.prodComm D.host.E _ _).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem lagTerm_swap {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) :
    lagTerm μ 𝓕 (C.2, C.1) f₂ f₁ = star (lagTerm μ 𝓕 C f₁ f₂) := by
  unfold lagTerm
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [mul_comm]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}

theorem tsum_comm (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₂ f₁‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let e : Lag W ≃ Lag W := ⟨lagSwap W, lagSwap W, lagSwap_lagSwap W, lagSwap_lagSwap W⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₂ f₁ h₂ h₁).1 (lagSwap W Y) _
    (isLagFrame_lagSwap W Y (fr Y) (hS.frame Y))
  change ‖lagTerm μ 𝓕 (fr (lagSwap W Y)) f₂ f₁‖ₑ = _
  rw [← h, lagTerm_swap, ← ofReal_norm_eq_enorm, norm_star, ofReal_norm_eq_enorm]

theorem tsum_left (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ) f₁) f₂‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let g : GQ W := ⟨γ, hγ⟩
  let e : Lag W ≃ Lag W := ⟨lagAct W g, lagAct W g⁻¹,
    fun Y => by rw [← lagAct_mul, inv_mul_cancel, lagAct_one],
    fun Y => by rw [← lagAct_mul, mul_inv_cancel, lagAct_one]⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ f₂ (hS.weil.om_pres (1, γ) f₁ h₁) h₂).1
    (lagAct W g Y) _ (isLagFrame_lagAct W g Y (fr Y) (hS.frame Y))
  have h' := ((Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂).2 γ hγ (gqMat W g)
    (gqMat_map W g).symm).1 (fr Y)
  change ‖lagTerm μ 𝓕 (fr (lagAct W g Y)) (om (1, γ) f₁) f₂‖ₑ = _
  rw [← h, h']

end

theorem tsum_enorm_lagTerm_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS F₁ F₂ h₁ h₂ γ₁ hγ₁ γ₂ hγ₂
  have p₂ := hS.weil.om_pres (1, γ₂) F₂ h₂
  rw [tsum_left hS h₁ p₂ hγ₁, tsum_comm hS p₂ h₁, tsum_left hS h₂ h₁ hγ₂, tsum_comm hS h₁ h₂]

end GlobalTheory.SWAbsInv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  first | exact @GlobalTheory.RawLift.rallis_graphs | exact GlobalTheory.RawLift.rallis_graphs | (intros; apply GlobalTheory.RawLift.rallis_graphs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  first | exact @GlobalTheory.RallisExch.eisAbs_exchange | exact GlobalTheory.RallisExch.eisAbs_exchange | (intros; apply GlobalTheory.RallisExch.eisAbs_exchange <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_crystalline_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  first | exact @GlobalTheory.CrysPrism.exists_crys_prisms | exact GlobalTheory.CrysPrism.exists_crys_prisms | (intros; apply GlobalTheory.CrysPrism.exists_crys_prisms <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  first | exact @GlobalTheory.BSP.iA_per_mem_nonZeroDivisors | exact GlobalTheory.BSP.iA_per_mem_nonZeroDivisors | (intros; apply GlobalTheory.BSP.iA_per_mem_nonZeroDivisors <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type), TopBasis bk.ev bk.J ι → ∀ (w : ι → Ainf l) (z t : Ainf l), HasSum (fun i => bk.iA (w i)) (bk.iA t) → (∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → z - ∑ i ∈ G, w i ∈ (bk.J ^ n).map bk.ev) → z = t := by
  first | exact @GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic | exact GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic | (intros; apply GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic <;> assumption)
end
