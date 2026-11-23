module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle201
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  first | exact @GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow | exact GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow | (intros; apply GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.VB

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.coe_lt_top n))
    | coe m =>
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem suppDim_lt_of_genRank_eq_zero {n : ℕ} (hd : topologicalKrullDim Z ≤ (n : WithBot ℕ∞))
    {F : Z.Modules} [QCoh.IsFiniteQC F] (h : genRank F = 0) : QCoh.suppDim F < (n : WithBot ℕ∞) := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z := by
    rw [← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact lt_of_add_one_le_natCast (this.trans hd)

variable {κ : Type} [Field κ] [Algebra κ Γ(Z, ⊤)]

theorem interNum_of_genRank_eq (hp : IsProjOver (strHom κ (X := Z))) {ι : Type} [Fintype ι]
    (hd : topologicalKrullDim Z ≤ (Fintype.card ι : ℕ)) {P : ι → LB Z} (hP : ∀ i, (P i).IsLB)
    (r : ℕ) : ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    rw [interNum_eq_zero_of_isProjOver hf G hp (suppDim_lt_of_genRank_eq_zero hd h) hP]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := Fintype.card ι) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist le_rfl hP hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hP h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

end GlobalTheory.VB

theorem GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver : ∀ (κ : Type) [Field κ] (Z : Scheme.{0})
    [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → ∀ (ι : Type) [Fintype ι],
    topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G]
    (P : ι → LB Z), (∀ i, (P i).IsLB) →
    interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P :=
  fun _ _ _ _ _ hp _ _ hd G _ _ hP => GlobalTheory.VB.interNum_of_genRank_eq hp hd hP _ G rfl
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_sec_of_ample_sub_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hp d hd L B M hL hB hM e hlt
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  obtain ⟨s, hs⟩ := IsGenerated.exists_mono_cutHom k (GlobalTheory.structureModule X) hB
  set G := cut (GlobalTheory.structureModule X) hB.isLB s with hG
  haveI : IsFiniteQC G := isFiniteQC_cut (GlobalTheory.structureModule X) hB.isLB s
  obtain ⟨t, ht⟩ := IsGenerated.exists_mono_cutHom k G hB
  have hGd : suppDim G ≤ (d : ℕ) := suppDim_cut_le _ hB.isLB s hsd
  have hcut := interNum_cons_eq_interNum_cut hB.isLB s (P := fun _ : Fin d => L) (fun _ => hL.isLB) hfin
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp (d + 1) (GlobalTheory.structureModule X) hsd L hL
  obtain ⟨C', m₁, hC'⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp d G hGd L hL
  rw [hcut] at hlt
  obtain ⟨m, hm1, hm⟩ := GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds d (topSelfIntersection k L (d + 1)) (interNum k G (fun _ : Fin d => L))
    (fun m => hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0)
    (fun m => hdim k (twist G (lbPow L m)) 0) C C' m₀ m₁ hC hC' hlt
  have hcl : cls (lbPow L m) (isLB_lbPow hL.isLB m) =
      cls (lbPow M m) (isLB_lbPow hM m) + m • cls B hB.isLB := by
    rw [cls_lbPow hL.isLB, cls_lbPow hM, e, smul_add]
  have hmono : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist G M') 0 ≤ hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G (isLB_lbPow hL.isLB m) hM' h
      exact (hdim_congr k 0 e).ge
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h2 := ih _ (isLB_tens hM' hB.isLB) (by rw [h1, h, succ_nsmul']; abel)
      exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp G B _ M' hB.isLB _ hM' t ht h1).2.2).trans h2
  have hch : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + j * hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB m) hM' h
      rw [hdim_congr k 0 e]
      omega
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h0 : cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls (tens M' B) (isLB_tens hM' hB.isLB) + j • cls B hB.isLB := by
        rw [h1, h, succ_nsmul']; abel
      have h2 := ih _ (isLB_tens hM' hB.isLB) h0
      have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp (GlobalTheory.structureModule X) B _ M' hB.isLB _ hM' s hs h1).1 0
      change hdim k (twist (GlobalTheory.structureModule X) (tens M' B)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + hdim k (twist G (tens M' B)) 0 at h3
      have h4 := hmono j _ (isLB_tens hM' hB.isLB) h0
      rw [Nat.succ_mul]
      omega
  have hch' : hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
      hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0 + m * hdim k (twist G (lbPow L m)) 0 := hch m (lbPow M m) (isLB_lbPow hM m) hcl
  refine ⟨m, hm1, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
  show 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0
  have : m * hdim k (twist G (lbPow L m)) 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 := hm
  omega

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutOutSections

theorem sec_eq_zero_of_nonzeroLocus_eq_bot {Y : Scheme.{0}} [IsReduced Y] {M : LB Y} (s : M.Sec)
    (h : nonzeroLocus s = ⊥) : s = 0 := by
  apply DVR.SecOps.sec_ext
  intro k
  have hk : Y.basicOpen (s.f k) = ⊥ := le_bot_iff.1 ((basicOpen_le_nonzeroLocus s k).trans h.le)
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hk
  rw [hk]
  rfl

theorem eventually_isGenerated_lbPow {X : Scheme.{0}} {N : LB X} (hN : IsAmpleLB N) :
    ∀ᶠ k in atTop, IsGenerated (lbPow N k) := by
  refine (hN.eventually_isGenerated_tens_lbPow (LB.isLB_triv X)).mono fun k hk => ?_
  obtain ⟨c, u, hu⟩ := hk
  have hP := isLB_lbPow hN.isLB k
  have hT := isLB_tens (LB.isLB_triv X) hP
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq X _ _ hT hP
    (by simp only [CechPic.cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]) (Fin c) u hu
  exact ⟨c, v, hv⟩

theorem eventually_exists_secs_cutting_out : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  intro X _ _ p hp N Z hN
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  let U : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
  have hloc : ∀ y : U, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow N n).Sec, (y : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := fun y => hN.exists_affine_le y.2
  choose n hn s hys hle _ using hloc
  have hc : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun y : U => (nonzeroLocus (s y) : Set X))
    (fun y => (nonzeroLocus (s y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys ⟨y, hy⟩⟩)
  obtain ⟨m, -, t, ht⟩ := exists_common_pow (fun y : T => n y) (fun y => hn y) (fun y => s y)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_isGenerated_lbPow hN)
  refine eventually_atTop.2 ⟨K + m, fun l hl => ?_⟩
  obtain ⟨c, g, hg⟩ := hK (l - m) (by omega)
  have hml : m + (l - m) = l := by omega
  let κ' : T × Fin c → (lbPow N l).Sec := fun q => secCast hml (secMul (t q.1) (g q.2))
  have hκ' : ∀ q, nonzeroLocus (κ' q) = nonzeroLocus (s q.1) ⊓ nonzeroLocus (g q.2) := fun q => by
    simp only [κ', nonzeroLocus_secCast, nonzeroLocus_secMul, ht]
  have hb : ∀ q, ∀ y ∈ Z, y ∉ nonzeroLocus (κ' q) := fun q y hy h => by
    rw [hκ'] at h
    exact hle _ h.1 hy
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (T × Fin c)
  refine ⟨r, fun i => κ' (e.symm i), fun i => ?_, fun i => hb _, fun y hy => ?_⟩
  · have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
    apply sec_eq_zero_of_nonzeroLocus_eq_bot
    rw [GlobalTheory.nonzeroLocus_secPull]
    refine le_bot_iff.1 fun z hz => ?_
    have hz' : redι Z z ∈ (Z : Set X) := by
      rw [← range_redι Z]
      exact Set.mem_range_self z
    exact hb _ _ hz' hz
  · obtain ⟨a, ha', hya'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hg.ge (Set.mem_univ y))
    refine ⟨e (⟨a, ha'⟩, j), ?_⟩
    show y ∈ nonzeroLocus (κ' (e.symm (e (⟨a, ha'⟩, j))))
    rw [e.symm_apply_apply, hκ']
    exact ⟨hya', hj⟩

end GlobalTheory.CutOutSections
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftClosed
open GlobalTheory.QCoh GlobalTheory.Twist

theorem res_eq {X : Scheme.{0}} (I : X.IdealSheafData) {V W : X.Opens} (h : W ≤ V)
    (x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W)
      (resM ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) h
        ((structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ V)).symm x)) =
      (I.subscheme.presheaf.map (homOfLE (fun _ hz => h hz :
        I.subschemeι ⁻¹ᵁ W ≤ I.subschemeι ⁻¹ᵁ V)).op).hom x := rfl

theorem smul_eq {X : Scheme.{0}} (I : X.IdealSheafData) {W : X.Opens} (r : Γ(X, W))
    (m : Γ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme), W)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) (r • m) =
      (I.subschemeι.app W).hom r * structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) m := rfl

theorem epi_toSubscheme {X : Scheme.{0}} (I : X.IdealSheafData) : Epi (toSubscheme I) := by
  rw [epi_iff_forall_affine]
  intro U hU y
  obtain ⟨f, hf⟩ := I.subschemeι_app_surjective ⟨U, hU⟩ ((structureModuleSectionsEquiv _) y)
  refine ⟨(structureModuleSectionsEquiv U).symm f, ?_⟩
  apply (structureModuleSectionsEquiv _).injective
  rw [← hf]
  rfl

theorem exists_twistSec_of_sec {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec) :
    ∃ b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤),
    ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)) := by
  refine ⟨mkSec (fun i => (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).symm
    ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))) ?_,
    fun i => ?_⟩
  · intro i j
    apply (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j))).injective
    dsimp only
    rw [smul_eq, res_eq, res_eq]
    have hi : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => i) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.1.2
    have hj : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => j) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.2
    refine fn_ext fun z hz => ?_
    have e1 := gs_res (𝟙 I.subscheme) z (fun _ hz => hz.1 : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    have e1' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i)) hz.1 (σ.f (fun _ => i))
    have e2 := gs_res (𝟙 I.subscheme) z (fun _ hz => ⟨hz.1.1, hz.2⟩ : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j))).op).hom (σ.f (fun _ => j)))
    have e2' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j)) ⟨hz.1.1, hz.2⟩ (σ.f (fun _ => j))
    have hz' : I.subschemeι z ∈ M.U i ⊓ M.U j := ⟨hz.1.2, hz.2⟩
    have e3 := gs_pull (𝟙 I.subscheme) I.subschemeι z (⊤ ⊓ M.U i ⊓ M.U j) hz (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g i j : Γ(X, M.U i ⊓ M.U j)))
    have e4 := gs_res (𝟙 I.subscheme ≫ I.subschemeι) z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ⊤ ⊓ M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j) hz (M.g i j : Γ(X, M.U i ⊓ M.U j))
    have e5 := gs_unit (𝟙 I.subscheme ≫ I.subschemeι) z _ hz' (M.g i j)
    have e6 := gs_compat σ (𝟙 _) z (hi z hz) (hj z hz)
    have e7 := gm_pull_g M I.subschemeι (𝟙 _) z (fun _ => i) (fun _ => j) (hi z hz) (hj z hz)
    rw [gs_mul _ z _ hz]
    erw [e1, e1', e2, e2', e3, e4, e5, e6, e7]
  · exact LinearEquiv.apply_symm_apply _ _

theorem secPull_secOfTwist_eq {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec)
    (b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤))
    (hb : ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    (a : Γ(twist (QCoh.structureModule X) M, ⊤)) (ha : (Twist.map M (toSubscheme I)).app ⊤ a = b) :
    GlobalTheory.secPull (Twist.secOfTwist (𝟙 _) a) I.subschemeι = σ := by
  refine DVR.SecOps.sec_ext fun J => ?_
  have h1 := hb (J PUnit.unit)
  rw [← ha, coord_map_app] at h1
  change (I.subschemeι.appLE _ _ _).hom (resG X _ (structureModuleSectionsEquiv _ (coord a (J PUnit.unit)))) = _

  set i := J PUnit.unit
  have h2 : (I.subschemeι.app (⊤ ⊓ M.U i)).hom (structureModuleSectionsEquiv _ (coord a i)) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f J) := h1
  have e3 : ∀ y : Γ(X, ⊤ ⊓ M.U i), (I.subschemeι.appLE (M.U i) ((M.pull I.subschemeι).U J)
      (fun z hz => (mem_pull (F := I.subschemeι)).1 hz)).hom (resG X (le_inf le_top le_rfl) y) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => ⟨trivial, (mem_pull (F := I.subschemeι)).1 hz⟩ :
        (M.pull I.subschemeι).U J ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).op).hom ((I.subschemeι.app _).hom y) := by
    intro y
    rw [← CommRingCat.comp_apply]
    erw [Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  refine (e3 _).trans ?_
  rw [h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact (congrArg (fun q => (I.subscheme.presheaf.map q).hom (σ.f J)) (Subsingleton.elim _ (𝟙 _))).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem exists_secPull_eq_of_subsingleton {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (hM : M.IsLB)
    (h : Subsingleton (coh (twist (idealModule I) M) 1)) (σ : (M.pull I.subschemeι).Sec) :
    ∃ s : M.Sec, GlobalTheory.secPull s I.subschemeι = σ := by
  haveI := epi_toSubscheme I
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (idealModuleι I) (toSubscheme I) (Limits.kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hsurj := cohOn.app_surjective (Twist.shortExact_map hM hS) ⊤ h
  obtain ⟨b, hb⟩ := exists_twistSec_of_sec I M σ
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨_, secPull_secOfTwist_eq I M σ b hb a ha⟩

theorem eventually_exists_secPull_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  intro X _ _ p hp N Z hN
  letI := algebraΓOfHom p
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  refine (hN.eventually_subsingleton_coh_twist (f := p) (fun _ => rfl)
    (idealModule (Scheme.IdealSheafData.vanishingIdeal Z))).mono fun l hl σ => ?_
  exact exists_secPull_eq_of_subsingleton _ _ (isLB_lbPow hN.isLB l) (hl 1 one_pos) σ

end GlobalTheory.LiftClosed
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.DimRed.abelianUnobstructed_of_unobDim | exact GlobalTheory.DimRed.abelianUnobstructed_of_unobDim | (intros; apply GlobalTheory.DimRed.abelianUnobstructed_of_unobDim <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  first | exact @GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | exact GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | (intros; apply GlobalTheory.CptPartRestr.mem_cptPart_iff_forall <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → ∀ (δ x : X), x ∈ twCent θ δ ↔ ∀ v, pf v x ∈ twCent (θv v) (pf v δ) := by
  first | exact @GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp | exact GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp | (intros; apply GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp <;> assumption)
end
