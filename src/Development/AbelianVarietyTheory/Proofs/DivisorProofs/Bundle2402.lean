module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorReadsAsTranslateCurveTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

noncomputable section

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

namespace GlobalTheory.StdRead

variable {D : D7}

theorem xiN_eq {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {δ : ℂ} {ι : Type} (R : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

def IsPh (u : ℂ) : Prop := ‖u‖ = 1 ∧ u ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam u‖ = 1

theorem IsPh.mul {u v : ℂ} (hu : IsPh u) (hv : IsPh v) : IsPh (u * v) :=
  ⟨by rw [norm_mul, hu.1, hv.1, mul_one], mul_mem hu.2.1 hv.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam hu.2.1 hv.2.1, norm_mul, hu.2.2, hv.2.2, mul_one]⟩

theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dite_eq_left (one_mem _)]
  exact map_one lam

theorem IsPh.conj {u : ℂ} (hu : IsPh u) : IsPh (starRingEnd ℂ u) := by
  have h0 : u ≠ 0 := fun h => by simpa [h] using hu.1
  have e : starRingEnd ℂ u = u⁻¹ := (Complex.inv_eq_conj hu.1).symm
  refine ⟨by rw [Complex.norm_conj, hu.1], e ▸ inv_mem hu.2.1, fun p _ lam => ?_⟩
  have h := GlobalTheory.BotFormula.lamC_mul lam hu.2.1 (inv_mem hu.2.1)
  rw [mul_inv_cancel₀ h0, lamC_one] at h
  have h2 := congrArg norm h
  rw [norm_mul, hu.2.2, norm_one, one_mul] at h2
  rw [e, ← h2]

theorem isPh_of_pow {u : ℂ} {m : ℕ} (hm : 0 < m) (h : u ^ m = 1) : IsPh u := by
  have hQ : u ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow hm (h ▸ isIntegral_one)).isAlgebraic
  refine ⟨(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, h, norm_one]), hQ, fun p _ lam => ?_⟩
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
  unfold lamC
  rw [dite_eq_left hQ, ← norm_pow, ← map_pow, show (⟨u, hQ⟩ : Qbar) ^ m = 1 from Subtype.ext h, map_one, norm_one]

theorem exists_const (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) {a d : ℕ} (G : VC D a d → ℂ)
    (hG : G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (h0 : G ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e0, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ u, IsPh u ∧ G = (κ * u) • e0 := by
  by_cases hex : ∃ e1, Crv D ⊤ δ ∧ oddE0 D ⊤ δ t0 a d e1 ∧ e1 ≠ 0
  · obtain ⟨e1, hC, h1, hne⟩ := hex
    have k0 := GlobalTheory.NormSum.VacMove.klat (D := D) (tor0 D ⊤ δ) (GlobalTheory.NormSum.VacMove.moves_one D a)
      (GlobalTheory.NormSum.VacMove.moves_one D d)
    obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ k0
    obtain ⟨κ, hκ⟩ := hline G hG e1 h1.1 hne
    refine ⟨κ, fun h => h0 (by rw [hκ, h, zero_smul]), fun e0 _ ht he hn => ?_⟩
    obtain ⟨u, hu, e⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC he h1 hn
    obtain ⟨a1, a2⟩ := GlobalTheory.T.odd_eisenstein_ratio_algebraic_unit hI hC ht he h1 hn u e
    exact ⟨u, ⟨hu, a1, a2⟩, by rw [hκ, e, smul_smul]⟩
  · exact ⟨1, one_ne_zero, fun e0 hC _ he hn => absurd ⟨e0, hC, he, hn⟩ hex⟩

theorem reads_std (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} (hS : S.rank = P.a) (hT : T.rank = P.d) (hcc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) v)
    {c : ℂ} (hc : c • P.e0 ∈ Th D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d)) (hr : Reads ψ θ hS hT ⊤ δ 1 (c • P.e0) v)
    {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hm : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hν : HasFinPart ν⁻¹ P.W.chV' P.W.ep')
    (hk : KillsCong ν 𝔪) {β : GL (Fin S.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β (stdL D S.rank))
    (hstd : GlobalTheory.FunObj.SqNum.IsStdDatum P 𝔪 0) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm)
    (hf : f = Tm fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) :
    ∃ u, IsPh u ∧ Reads ψ θ hS hT ⊤ δ 1 ((c * u) • P.F) f := by
  obtain ⟨R, hR1, hR2, hF⟩ := hstd
  obtain ⟨b1, b2⟩ := GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice β hβ
  obtain ⟨m, hm0, hpow⟩ := GlobalTheory.T.unitDetCharacter_integralFrame_pow_eq_one e 𝔪 hm ν hk β b1 b2
  choose! z hz using fun (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (hk : k ∈ intG D P.a) => exists_approx hm.ne_bot 0 P.d hk
  have hz' : ∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r) := fun r hr => hz r (hR1 r hr)
  have h0 := GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm
  have h1 := GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm h0
  refine ⟨_, (isPh_of_pow hm0 hpow).conj, ?_⟩

  rw [hf, GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators S T hS hT P.a_le e 𝔪 hm ν hk β b1 b2 R hR1 hR2 z hz', map_smul, map_sum, mul_comm c, mul_smul, hF,
  Finset.smul_sum]
  refine Reads.smul (reads_sum R _ _ fun r hr => ?_) _
  rw [GlobalTheory.T.weilAction_integralPoint_cosetVector_eq hI P hm.ne_bot 0 r (hR1 r hr) _ (GlobalTheory.T.integral_action_unit_character_eigen hI P e 𝔪 hm ν hν hk r (hR1 r hr)) (z r) (hz' r hr).1 (hz' r hr).2,
    map_smul, smul_comm c, ← cosV_smul]
  exact (h1 (z r) (hz' r hr).1).smul _

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open GlobalTheory.FunObj.SqNum GlobalTheory.FunObj.StdDatum GlobalTheory.Mem.Col2.SplitChar in
theorem killsCong {μ₀ : T} (hL : L.Is μ₀) (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) (i j : Fin D.R.m) :
    KillsCong (G.nu t i (j + 1)) (GlobalTheory.SqTop.modT G t) := by
  intro x u hxu hu hm
  have hle := Ideal.mul_mono (TwBig.modT_le_condE G t) (TwBig.conj_smul_mono (TwBig.modT_le_condE G t))
  have h1 := TwBig.nuInv_base_eq_one hL G i j u hu (TwBig.hatId_mono hle hm)
  have h2 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t
    rw [hL.xi_base, mul_one, mul_div_right_comm]
  have h3 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G t i j hL) x u hxu
  have e1 : (nuH G μ₀ i j * L.xiH t).1 (finIdl D u) = (nuH G μ₀ i j).1 (finIdl D u) * (L.xiH t).1 (finIdl D u) := rfl
  have e2 : (nuH G μ₀ i j).1 (finIdl D u) = 1 := inv_eq_one.1 h1
  rw [e, e1, e2, h2, mul_one] at h3
  exact Circle.coe_injective (by simpa using h3)

end GlobalTheory.StdRead

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

end GlobalTheory.StdRead

end
end
end

section

set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem mem_lat_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG barE hbar d hd
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image d)
  have hsq : ((y.natAbs ^ 2 : ℕ) : ℤ) = y * y := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
  have hint : ∀ a, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * d a) := fun a => by
    have h1 := hyi (d a) (Finset.mem_image_of_mem d (Finset.mem_univ a))
    have e : ((y.natAbs ^ 2 : ℕ) : E) * d a = (algebraMap ℤ E y) * (y • d a) := by
      rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, ← _root_.mul_assoc]
      congr 1
      rw [← Int.cast_natCast (R := E), hsq]
      try push_cast
      try ring
    rw [e]
    exact isIntegral_algebraMap.mul h1
  set n : ℕ := y.natAbs ^ 2 with hn_def
  have hn : 0 < n := pow_pos (Int.natAbs_pos.2 hy0) 2
  let x : Fin p → 𝓞 E := fun a => ⟨(n : E) * d a, hint a⟩
  have hx : ∀ a, (x a : E) = n * d a := fun a => rfl
  have hψ := GlobalTheory.FlatCM.HomLat.isLinearHom_prod X x
  have hk := GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible E H hH K ρ σ₁ p X _ hψ n hn (fun f hf ⟨m, hm, z, hfz⟩ => by
    have hm' : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    have hc : (fun a => (z a : E) / m) ∈ GlobalTheory.FlatCM.HomLat.lat X := Submodule.subset_span
      ⟨m, hm, z, fun a => by field_simp, f, hf, hfz⟩
    obtain ⟨w, hw⟩ := hd _ hc
    refine ⟨w, GlobalTheory.T.weilPairing_linearHom_span_gramForm E H hH K ρ σ₁ p X gP gQ hG m hm z f hf hfz x _ ?_⟩
    have hb : ∀ b, ((H.bar (x b) : 𝓞 E) : E) = n * barE (d b) := fun b => by
      rw [← hbar, hx, map_mul, map_natCast]
    have key : (m : E) * ((n : E) * (w : E)) =
        ∑ a, ∑ b, (z a : E) * (gP a b : E) * ((H.bar (x b) : 𝓞 E) : E) := by
      simp_rw [hb]
      rw [hw]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    apply RingOfIntegers.coe_injective
    push_cast
    exact key)
  obtain ⟨χ, hχ, hχn⟩ := GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion E H K σ₁ (X.A true) X.B _ hψ n hn hk
  exact Submodule.subset_span ⟨n, hn, x, hx, χ, hχ, hχn⟩

end GlobalTheory.FlatCM.HomLat
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

theorem lat_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, hG, hdet⟩ := GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite E H hH K ρ σ₁ p X
  set N : 𝓞 E := H.bar.symm gP.det with hNdef
  have hN0 : N ≠ 0 := fun h => hdet (by simpa [hNdef] using congrArg H.bar h)
  have hN : (N : E) ≠ 0 := by exact_mod_cast hN0
  have key : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ b, ∃ z : 𝓞 E, (z : E) = (N : E) * c b := by
    rintro c ⟨n, hn, x, hx, f, hf, hfx⟩ b
    choose y hy using GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow E H hH K ρ σ₁ p 0 X gP gQ hG n x f hn hf hfx
    have hmv : gP.mulVec (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * y a := by
      funext a; simp [Matrix.mulVec, dotProduct, hy]
    have hadj : gP.det • (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * gP.adjugate.mulVec y a := by
      have := congrArg gP.adjugate.mulVec hmv
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [this]; funext a; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    have hb := congrArg H.bar.symm (congrFun hadj b)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply, map_natCast] at hb
    refine ⟨H.bar.symm (gP.adjugate.mulVec y b), ?_⟩
    have hnE : ((n : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hnE
    have h2 : ((N : 𝓞 E) : E) * ((x b : 𝓞 E) : E) =
        (n : E) * ((H.bar.symm (gP.adjugate.mulVec y b) : 𝓞 E) : E) := by
      rw [hNdef]; exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hb
    push_cast
    rw [← h2, hx b]; ring
  let incl : (Fin p → 𝓞 E) →ₗ[𝓞 E] (Fin p → E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)
  let scal : (Fin p → E) →ₗ[𝓞 E] (Fin p → E) := N • LinearMap.id
  have hscal : Function.Injective scal := by
    intro v w h
    funext i
    have := congrFun h i
    simp only [scal, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ hN this
  apply Submodule.fg_of_fg_map_injective scal hscal
  refine Submodule.FG.of_le (T := LinearMap.range incl) ?_ ?_
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map incl
  · rw [GlobalTheory.FlatCM.HomLat.lat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    choose z hz using key c hc
    refine ⟨z, ?_⟩
    funext b
    simp [incl, scal, hz, Algebra.smul_def]

end GlobalTheory.FlatCM.HomLat

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

theorem _root_.GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₁ → (h.geo f₁ f₂ th k).Birational := by
  first | exact @GlobalTheory.HSApp.birational_of_ratGen | exact GlobalTheory.HSApp.birational_of_ratGen | (intros; apply GlobalTheory.HSApp.birational_of_ratGen <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.exists_extend_mul_simplePole_of_vanishing : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) → ∃ G : H0 p N ⊤, H0.restr le_top G = C.mul ω (H0.restr le_top g) := by
  first | exact @GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole | exact GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole | (intros; apply GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.extends_vanishing_of_simplePole_mul_extends : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ (G : H0 p N ⊤) (f : H0 p B O), H0.restr le_top G = C.mul ω f → ∃ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ∧ H0.restr le_top g = f := by
  first | exact @GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul | exact GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul | (intros; apply GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ u : X.functionFieldˣ,
    (∀ γ, fnAct ρ γ u = u) → ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  first | exact @GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | exact GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | (intros; apply GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.isUnipotentModIdeal_liftLa_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  first | exact @GlobalTheory.OrbitSep.unipAt_inv_liftLa | exact GlobalTheory.OrbitSep.unipAt_inv_liftLa | (intros; apply GlobalTheory.OrbitSep.unipAt_inv_liftLa <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.fromSpecResidueField_comp_aut_eq_of_fixes : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ : Γ) (x : X),
    (ρ γ).asIso.hom x = x → (∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) →
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  first | exact @GlobalTheory.OrbitSep.fromSpecResidueField_comp_eq_of_fixes | exact GlobalTheory.OrbitSep.fromSpecResidueField_comp_eq_of_fixes | (intros; apply GlobalTheory.OrbitSep.fromSpecResidueField_comp_eq_of_fixes <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.componentStabilizer_acts_by_levelChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  first | exact @GlobalTheory.CompLevelStab.stab_acts | exact GlobalTheory.CompLevelStab.stab_acts | (intros; apply GlobalTheory.CompLevelStab.stab_acts <;> assumption)
end
