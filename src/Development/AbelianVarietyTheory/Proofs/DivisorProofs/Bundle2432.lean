module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle623
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.ConjSchr

variable {D : D7}

theorem symplO_negS (S T : HSp D) (x y : WO S T) :
    symplO (GlobalTheory.ChiGrid.negSp S) T x y = -symplO S T x y := by
  simp only [symplO, hO, GlobalTheory.ChiGrid.negSp_gram, GlobalTheory.CjNeg.inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

def cjF {X : Type} (g : X → ℂ) : X → ℂ := fun w => starRingEnd ℂ (g w)

theorem heisO_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ S T x (cjF g) = cjF (heisO ψ (GlobalTheory.ChiGrid.negSp S) T x g) := by
  funext w
  simp only [cjF, heisO, map_mul, GlobalTheory.CjNeg.conj_psi hψ, GlobalTheory.CjNeg.symplOH_negS, neg_neg]

theorem cjF_cjF {X : Type} (g : X → ℂ) : cjF (cjF g) = g := by
  funext w; simp [cjF]

def conjLin {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g := cjF (T (cjF g))
  map_add' g h := by
    have : cjF (g + h) = cjF g + cjF h := by funext w; simp [cjF]
    funext w; simp [this, cjF]
  map_smul' c g := by
    have : cjF (c • g) = starRingEnd ℂ c • cjF g := by funext w; simp [cjF]
    funext w; simp [this, cjF]

theorem conjLin_apply {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (g : X → ℂ) :
    conjLin T g = cjF (T (cjF g)) := rfl

theorem isSBHalf_cjF {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (cjF Φ) := by
  obtain ⟨hs, k, hk, hinv, hsupp⟩ := h
  refine ⟨fun t ht => hs t ?_, k, hk, fun u hu hue t => ?_, fun t ht => hsupp t ?_⟩
  · intro h0; apply ht; simp [cjF, h0]
  · simp only [cjF, hinv u hu hue t]
  · intro h0; apply ht; simp [cjF, h0]

theorem isPlaceModel_conjLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {e : AE D}
    {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO (GlobalTheory.ChiGrid.negSp S) T) (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) e Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (cjF f₀) (conjLin T₀) := by
  constructor
  · intro Φ hΦ x hx
    have e1 := h.trans _ (isSBHalf_cjF hΦ) x hx
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => Φ (t + x)) = fun t => cjF Φ (t + x) := rfl
    rw [e2, e1]
  · intro Φ hΦ y hy
    have e1 := h.modul _ (isSBHalf_cjF hΦ) y hy
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO (GlobalTheory.ChiGrid.negSp S) T t y) * cjF Φ t := by
      funext t; simp only [cjF, map_mul, GlobalTheory.CjNeg.conj_psi hψ, symplO_negS]
    rw [e2, e1]
  · have e2 : cjF ((1 : ℂ) • halfInd e Λ) = (1 : ℂ) • halfInd e Λ := by
      funext t; simp only [cjF, one_smul, halfInd]; split_ifs <;> simp
    rw [conjLin_apply, e2, h.vac]

end GlobalTheory.ConjSchr

open GlobalTheory.ConjSchr in
theorem GlobalTheory.ConjSchr.conj_schroedinger_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  intro D ψ hψ A WW e ΛA ΛW vac Φ f hT
  have hL : latO (GlobalTheory.Grid.neg A) WW ΛA ΛW (fun _ => True) = latO A WW ΛA ΛW (fun _ => True) :=
    GlobalTheory.CoreRowLat.latO_negSp A WW ΛA ΛW _
  obtain ⟨⟨T₀, h0⟩, hall⟩ := hT
  have hf : f = T₀ Φ := hall T₀ h0
  rw [hL] at h0
  refine ⟨conjLin T₀, isPlaceModel_conjLin hψ h0, ?_⟩
  show cjF f = conjLin T₀ (cjF Φ)
  rw [conjLin_apply, cjF_cjF, hf]
end
end

section

set_option synthInstance.maxHeartbeats 400000

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.CovGminTop

section Abstract

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem norm_sum_le_of_gram {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    {ι : Type} (s : Finset ι) (f : ι → V) (σ : K →+* ℂ) : N σ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N σ (f i) := by
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, h⟩ := hG
  have e : ∀ x, N σ x = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk σ) x := fun x => by
    rw [(h _).2]
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e]; exact (hc σ x).symm
  simp only [e]
  exact PI.Dv.Tr.normAt_sum_le' b X _ s f

theorem char_val {H : Type} [Group H] [Finite H] (χ : H →* Kˣ) (h : H) :
    IsIntegral ℤ ((χ h : Kˣ) : K) ∧ ∀ σ : K →+* ℂ, ‖σ ((χ h : Kˣ) : K)‖ = 1 := by
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : ((χ h : Kˣ) : K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isIntegral_one), fun σ => ?_⟩
  have : ‖σ ((χ h : Kˣ) : K)‖ ^ Nat.card H = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_short_eigen {H : Type} [Group H] [Finite H] (st : H → V →ₗ[K] V)
    (hst : ∀ h h' x, st (h * h') x = st h' (st h x)) (χ : H →* Kˣ) (Λ : Submodule (𝓞 K) V) (hΛ : ∀ h, ∀ x ∈ Λ, st h x ∈ Λ)
    {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hs : ∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) (hi : ∀ h σ x, N σ (st h x) = N σ x)
    (s : Set V) (hsΛ : s ⊆ Λ) (hsp : Submodule.span K s = ⊤) (B : ℝ) (hB : ∀ y ∈ s, ∀ σ, N σ y ≤ B) :
    ∃ s' : Set V, (∀ y ∈ s', (y ∈ Λ ∧ ∀ h, st h y = ((χ h : Kˣ) : K) • y) ∧ ∀ σ, N σ y ≤ Nat.card H * B) ∧
      ∀ x, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K s' := by
  classical
  letI := Fintype.ofFinite H
  refine ⟨_, ?_, GlobalTheory.eigenvector_mem_span_twistedTrace_image H K V st hst χ s hsp⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨Λ.sum_mem fun h _ => ?_, fun g => ?_⟩, fun σ => ?_⟩
  · rw [← map_inv]
    let a : 𝓞 K := ⟨_, (char_val χ h⁻¹).1⟩
    have := Λ.smul_mem a (hΛ h y (hsΛ hy))
    rwa [← algebraMap_smul K a] at this
  · beta_reduce

    rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight g) fun h => _ • _ • st h y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, ← hst, smul_smul, Equiv.coe_mulRight, map_mul, mul_inv, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  · refine (norm_sum_le_of_gram hG hc _ _ σ).trans ?_
    rw [Nat.card_eq_fintype_card, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    rw [hs, hi, ← map_inv, (char_val χ h⁻¹).2, one_mul]
    exact hB y hy σ

end Abstract

section Point

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem half_lt_laOf (τ : Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)) (hk : (k : ℕ) < (dat p i).p) :
    (((p.κ i).n / 2 : ℕ) : ℤ) < laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k := by
  have h := GlobalTheory.HolRead.lastPos_wtA_of_kapIs D p.T p.κ p.fw.laws p.fw.kap i τ.1 τ.2
  have hm : (dat p i).mult τ.1 = (dat p i).p := by
    unfold Datum.mult
    exact if_pos τ.2
  rw [hm] at h
  have h2 : wtA (p.κ i) (τ.1, (dat p i).p - 1) ≤ wtA (p.κ i) (τ.1, k) := (dom_wtA (p.κ i)).1 τ.1 (show (k : ℕ) ≤ _ by omega)
  have h3 := h (by omega)
  unfold laOf weightOf
  rw [if_pos hk]
  beta_reduce
  omega

theorem one_le_kap (hp : 1 ≤ (dat p i).p) : 1 ≤ kap p i := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.two_le_m
    have := D.R.m_le_f
    omega
  have hne : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [WtShape.card_psi p]; exact hf)).1
  obtain ⟨τ⟩ := hne
  have h := half_lt_laOf p i τ ⟨0, by omega⟩ hp
  have h1 : (1 : ℤ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by omega
  have h2 : (1 : ℝ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by exact_mod_cast h1
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact (h2.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun k => |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem gminAt_of_gens (Y : Cov p i) (hpq : 1 ≤ (dat p i).p + (dat p i).q) (hA : Y.d.l₂.A.Coprime Y.d.l₂.M)
    (hC : KeepsCusp Y.U (Gk p i))
    (hk : ∀ (γ : LevelAut (dat p i) Y.d.l₂) (f g : Y.V (Gk p i)), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f →
      (f ∈ latW Y.U (Gk p i) → g ∈ latW Y.U (Gk p i)) ∧ ∀ σ, Y.nrm (Gk p i) σ g = Y.nrm (Gk p i) σ f)
    (hG : Y.GoodAt (Gk p i)) (S : Subgroup (LevelAut (dat p i) Y.d.l₂)) (χ : S →* (Y.d.c₂.F)ˣ)
    (hN : latDeep p i Y = chiLat S Y.U (Gk p i) χ) (s : Set (Y.V (Gk p i))) (hs : s ⊆ latW Y.U (Gk p i))
    (hsp : Submodule.span Y.d.c₂.F s = ⊤) (B PP : ℝ) (hB : ∀ y ∈ s, ∀ σ, Y.nrm (Gk p i) σ y ≤ Real.exp B)
    (hPP : Real.log (Nat.card S) + B ≤ PP * kap p i) : GminAt p i Y PP := by
  let st : S → Y.V (Gk p i) →ₗ[Y.d.c₂.F] Y.V (Gk p i) := fun h =>
    (pull Y.d.Xo₂ Y.d.c₂ (h : LevelAut (dat p i) Y.d.l₂)).toLinearMap.restrict (hC h)
  obtain ⟨s', h1, h2⟩ := exists_short_eigen st
    (fun h h' x => Subtype.ext ((isRightAct_pull (Xo := Y.d.Xo₂) (c := Y.d.c₂) hpq hA).2 h h' x)) χ (latW Y.U (Gk p i))
    (fun h x hx => (hk h x _ rfl).1 hx) hG.1
    (fun σ f => by rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ])
    (fun σ a x => petW_smul _ _ _ _ _ σ a _) (fun h σ x => (hk h x _ rfl).2 σ) s hs hsp _ hB
  refine ⟨s', fun y hy => ?_, fun y hy σ => ((h1 y hy).2 σ).trans ?_, fun x hx => h2 x fun h => Subtype.ext ?_⟩
  · rw [hN]
    exact (mem_chiLat S Y.U _).2 ⟨(h1 y hy).1.1, fun h => congrArg Subtype.val ((h1 y hy).1.2 h)⟩
  · have hc : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
    rw [← Real.exp_log hc, ← Real.exp_add]
    exact Real.exp_le_exp.2 hPP
  · rw [hN] at hx
    exact ((mem_chiLat S Y.U _).1 hx).2 h

end Point

theorem num_step {C Z l k PP : ℝ} (hC : 0 ≤ C) (hl : C + 45 ≤ Z) (hk : 1 ≤ k) (hPP : Z ^ 12 ≤ PP) (h : l ≤ 45 * Z ^ 2) :
    l + C * Z ^ 2 * k ≤ PP * k := by
  have h1 : 1 ≤ Z := by linarith
  have h2 : Z ^ 3 ≤ Z ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : (C + 45) * Z ^ 2 ≤ Z ^ 3 := by
    rw [pow_succ' Z 2]; exact mul_le_mul_of_nonneg_right hl (by positivity)
  have h4 : (C + 45) * Z ^ 2 * k ≤ PP * k := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 45 * Z ^ 2 ≤ 45 * Z ^ 2 * k := le_mul_of_one_le_right (by positivity) hk
  linarith

end GlobalTheory.CovGminTop
end

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CoreSlope

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)


set_option maxHeartbeats 1000000 in
theorem coreAt_of (C : ℝ) (hg : GramAt p i) (hm : MeasAt p i C) (hr : RatAt p i) : CoreAt p i (2 * C) := by
  obtain ⟨ι, hι, hli, himg⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hTC : IsTotallyComplex p.T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hc : ∀ σ x, nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := fun σ x => by
    simp only [nrmK]
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hfg : (latTypeK p.fw p.F.lv2 i).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ hg.2.2.2.2.1
    exact Submodule.FG.of_le_of_isNoetherian (T := latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n)) inf_le_left
  have hN : ∀ σ' x, nrmR p.R.toRealDat i σ' (ι x) ≤ Real.exp (C * unitE p) * nrmK p.fw i (σ'.comp (algebraMap p.T.Q.c.F D.what₂.LL)) x := by
    intro σ' x
    obtain ⟨c, hc0, hcl, hcf⟩ := hm σ'
    obtain ⟨h, hx⟩ := hι x
    rw [hx, hcf ⟨x, h⟩]
    have hce : c ≤ Real.exp (C * unitE p) := by
      calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
        _ ≤ Real.exp (C * unitE p) := Real.exp_le_exp.2 ((le_abs_self _).trans hcl)
    exact mul_le_mul_of_nonneg_right hce (petAt_nonneg _ _ _ _ _ _ _)
  have hS : latType p.R.toRealDat p.F.lv2 i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latTypeK p.fw p.F.lv2 i : Set (VK p.fw i))) := by
    rw [hr]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ (ι '' (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i))) := by
        rw [himg]; exact hy1
      obtain ⟨x, hx, rfl⟩ := hy1'
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      show (x : p.T.R _) ∈ Submodule.span _ (typeK p.fw p.F.lv2 i)
      obtain ⟨h, hx'⟩ := hι x
      exact Submodule.subset_span ⟨h, hx' ▸ hy2⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨(show ι x ∈ ((p.R.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) by rw [← himg]; exact ⟨x, hx1, rfl⟩), ?_⟩
      have hsp : Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i) ≤
          ((spType p.R.toRealDat p.F.lv2 i).comap ι).map (VK p.fw i).subtype := by
        rw [Submodule.span_le]
        rintro f ⟨h, hf⟩
        have hfV : f ∈ VK p.fw i := by rw [VK, cuspW_wtZ]; exact h
        refine ⟨⟨f, hfV⟩, ?_, rfl⟩
        obtain ⟨h', e⟩ := hι ⟨f, hfV⟩
        show ι ⟨f, hfV⟩ ∈ spType p.R.toRealDat p.F.lv2 i
        rw [e]
        exact hf
      obtain ⟨z, hz, hzx⟩ := hsp hx2
      have : z = x := Subtype.ext hzx
      subst this
      exact hz
  have h0 : latTypeK p.fw p.F.lv2 i ≠ ⊥ := by
    intro h0
    apply hg.2.2.1
    rw [eq_bot_iff]
    refine (latGood_le _ _ _).trans ?_
    rw [hS, h0]
    simp
  have key := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    (nrmK p.fw i) (nrmR p.R.toRealDat i) ι (latTypeK p.fw p.F.lv2 i) (C * unitE p) hg.2.2.2.1 hg.1 hc hli hfg h0 hN
  unfold CoreAt muCore
  rw [hS]
  linarith

theorem coreLe_of_gram_meas_rat : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  intro hg hm hr
  unfold Gram Meas GlobalTheory.CovTop.Rat CoreLe Lifts at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩

end GlobalTheory.CoreSlope
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

theorem _root_.GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) → letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) → ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  first | exact @GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | exact GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | (intros; apply GlobalTheory.NefCuspGrowth.topSelf_le_growthOn <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  first | exact @GlobalTheory.MulIsogeny.mul_isogeny | exact GlobalTheory.MulIsogeny.mul_isogeny | (intros; apply GlobalTheory.MulIsogeny.mul_isogeny <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_regular_localModel_graph_of_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_locModel_graph | exact GlobalTheory.GraphLocal.exists_locModel_graph | (intros; apply GlobalTheory.GraphLocal.exists_locModel_graph <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.HSShort

theorem hsClaimS_component_geo : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k Λ₀ hH
  have hp := CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hb : (h.data f₁ f₂ th k).Birational := hH.bir
  have hd := ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ (h.data f₁ f₂ th k).geom hb hp.2
  have hh := GlobalTheory.T.height_birationalImage_eq_tuple_height hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ hH.totallyComplex (h.data f₁ f₂ th k).geom hb hp.2
  have hc := GlobalTheory.T.arithmeticHilbertSamuelBound hQ c.F (h.data f₁ f₂ th k) Λ₀ hH _ hh
  have hm := GlobalTheory.T.degree_supLattice_component_eq E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k P.T le_rfl
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  obtain ⟨-, eT, -, en, eL, eb, eD, eT', -⟩ := h.data_numbers f₁ f₂ th k
  rw [← hd, h.d_eq f₁ f₂ th k, eT, en, eL, eb, eD, eT', hm, hD, Int.cast_natCast] at hc
  exact hc

end GlobalTheory.HSShort
end
