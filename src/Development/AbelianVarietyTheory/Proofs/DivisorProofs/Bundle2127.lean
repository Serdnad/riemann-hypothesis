module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001

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

namespace GlobalTheory.StdRead.Move

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

variable {D : D7}



theorem eig_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    {g' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) (hH : H ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) : P.W.Om k 1 H = s • H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) = k := mul_one k
  have f2 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = s • P.W.Om 1 g' P.e0 := by
    rw [← e1, e2, he, P.W.smul _ _ _ _ hT]
  rw [hc', P.W.smul _ _ _ _ hH, smul_comm s c H] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_eig (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) :
    P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      s • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact eig_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)
    (GlobalTheory.FunObj.CosetFix.iop_facts hI P h𝔪).1 k s he

theorem exists_close {𝔪 : Ideal (𝓞 D.host.E)} (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a)
    (z : Matrix (Fin d) (Fin a) D.host.E) (hz : Approx 𝔪 o k z) (m : ℕ) (hm : 0 < m) :
    ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧
      CloseTo D ⊤ m (k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
        (unitBlock D o a d) (z + w) := by
  choose b hb y hy hby using fun i j => GlobalTheory.CongApprox.exists_mem_approx D 𝔪 m hm _ (neg_mem (hz i j))
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have e1 : (((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := by
    simp
  unfold CloseTo
  refine fun i j => ⟨y i j, hy i j, Eq.trans ?_ (hby i j)⟩
  rw [e1, Matrix.one_mul, Matrix.map_add _ (map_add (inc D))]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply]
  ring

theorem wd_smul (δ : ℂ) {a d : ℕ} (x : VC D a d) (c : ℂ) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
  funext y
  simp only [Wd, Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_cosetVec : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  intro D hD δ t0 Q P 𝔪 h𝔪 o k hk c hc z hzi hz
  have h1 := hD.g1
  have he := P.vac.1
  have hIT := (GlobalTheory.FunObj.CosetFix.iop_facts hD P h𝔪).1
  have hfix := iop_eig hD P h𝔪 k c hc
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) :=
    VacMove.klat _ (VacMove.moves_one D P.a) (VacMove.moves_one D P.d)
  have kB : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D P.a), GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d, rfl⟩
  have hHB := (hD.uni ⊤ δ P.crv P.a P.d _ _ k0 kB P.e0 he).2.1
  obtain ⟨m, hm, hl⟩ := P.W.lift k 1 (unitBlock D o P.a P.d) _ hIT
  obtain ⟨w, hw, hclose⟩ := exists_close o k z hz m hm
  have hmain := hl _ hclose
  rw [hfix, wd_smul] at hmain
  obtain ⟨hw0, hwB⟩ := GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ 𝔪 w hw
  have hx0 := (GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ ⊤ z
    (fun i j => (hzi i j).imp fun b hb => ⟨Submodule.mem_top, hb⟩)).1
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hφ1 : φ = 1 := by
    have h2 := hφ P.e0
    rw [VacMove.wd_fix h1 P.crv k0 he hw0, VacMove.wd_fix h1 P.crv k0 he hx0,
      VacMove.wd_fix h1 P.crv k0 he (add_mem hx0 hw0)] at h2
    by_contra hne
    apply P.W.nz
    have : (φ - 1) • P.e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h3 := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)
  rw [VacMove.wd_fix h1 P.crv kB hHB hwB, hφ1, one_smul, ← VacMove.pt_add] at h3
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hIT
  unfold cosetVec cosV
  rw [P.W.smul _ _ _ _ hWT, hmain, ← h3, smul_comm]

end GlobalTheory.StdRead.Move
end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.dualLattice_correspondingLattices : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [Fintype D] [Fintype D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.dualLat_latCorr | exact GlobalTheory.PureMatch.Transport.dualLat_latCorr | (intros; apply GlobalTheory.PureMatch.Transport.dualLat_latCorr <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂], IsLocIso j → ∀ (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → ∀ (Z : Matrix A D k), IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  first | exact @GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | exact GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | (intros; apply GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.correspondingLattices_blockLattice : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.latCorr_blockLat | exact GlobalTheory.PureMatch.Transport.latCorr_blockLat | (intros; apply GlobalTheory.PureMatch.Transport.latCorr_blockLat <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.zetaFunction_transport_localFieldIso : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  first | exact @GlobalTheory.PureMatch.Transport.fFun_trM | exact GlobalTheory.PureMatch.Transport.fFun_trM | (intros; apply GlobalTheory.PureMatch.Transport.fFun_trM <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem ratRowAt_big : BigC fun _ ch _ _ => RatRowAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c i
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).2 i
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k l
    have h := hr k l
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj

namespace GlobalTheory.KerConjMean

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_of_ext (D : D7) (δ t0 : ℂ) (σ : D.what₂.LL →+* ℂ) (hfin : (ext D δ t0 σ).Finite) (hne : (ext D δ t0 σ).Nonempty)
    (a n G a' n' G' : ℝ) (ha : a ≤ a') (hn : n ≤ n') (hG : G ≤ G') (x B : ℝ) (hB : 0 ≤ B)
    (h : ∀ ρ ∈ ext D δ t0 σ, x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B) :
    x ≤ Real.exp (a' + n' * avg D δ t0 σ (hArea D δ t0) + G' * avg D δ t0 σ (hTh D δ t0)) * B := by
  obtain ⟨ρ, hρ, h1⟩ := (exists_avg _ hfin hne a' n' G' (hArea D δ t0) (hTh D δ t0)).1
  have hA : 0 ≤ hArea D δ t0 ρ := by unfold hArea; exact Real.posLog_nonneg
  have hT : 0 ≤ hTh D δ t0 ρ := by unfold hTh; exact Real.posLog_nonneg
  calc x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B := h ρ hρ
    _ ≤ Real.exp (a' + n' * hArea D δ t0 ρ + G' * hTh D δ t0 ρ) * B :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) hB

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem mapVV_conj_embLL {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (x : VV D.what₂.LL lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam x) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL lam (mapF (starRingEnd D.what₂.LL) lam x) := by
  rw [mapVV_mapF, embLL_comp_star, mapVV_mapVV]

theorem pairStdAt_of (C b C1 : ℝ)
    (hmA : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hmT : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hfin : ∀ σ : D.what₂.LL →+* ℂ, (ext D ch.S.Z.δ ch.S.Z.t0 σ).Finite ∧ (ext D ch.S.Z.δ ch.S.Z.t0 σ).Nonempty)
    (hRT : RatTopAt ch) (hCT : ConjTopAt ch (C / 2) b C1) (hRR : RatRowAt ch) (hCR : ConjRowAt ch (C / 2) b C1) :
    PairStdAt ch C b := by
  obtain ⟨a1, n1, G1, ha1, hn1, hG1, hs1, hb1⟩ := hCT
  obtain ⟨a2, n2, G2, ha2, hn2, hG2, hs2, hb2⟩ := hCR
  refine ⟨fun p => (a1 + a2) + (n1 + n2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    (G1 + G2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · have eA : aOne ch.G (C / 2) b + aOne ch.G (C / 2) b = aOne ch.G C b := by unfold aOne; ring
    refine (meanInf_affine _ (a1 + a2) (n1 + n2) (G1 + G2) _ _ (by linarith)).trans ?_
    have e1 := mul_le_mul_of_nonneg_left hmA (add_nonneg hn1 hn2)
    have e2 := mul_le_mul_of_nonneg_left hmT (add_nonneg hG1 hG2)
    nlinarith
  · intro p Φ β d hO c
    obtain ⟨hf0, hne⟩ := hfin p.embedding
    refine ⟨fun j B v hv => ?_, fun i B v hv => ?_⟩
    · obtain ⟨f, hf⟩ := hRT Φ β d hO c j
      obtain ⟨u, rfl, hu⟩ := hv
      refine ⟨f u, (hf u).symm, ?_⟩
      exact le_of_ext D _ _ p.embedding hf0 hne a1 n1 G1 _ _ _ (by linarith) (by linarith) (by linarith) _ B
        ((nrm_one_nonneg _ _).trans hu) (fun ρ hρ => hb1 Φ β d hO c j f hf p.embedding ρ hρ u B hu)
    · obtain ⟨f, hf⟩ := hRR Φ β d hO c i
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨mapF (starRingEnd D.what₂.LL) _ (f (mapF (starRingEnd D.what₂.LL) _ w)), ?_, ?_⟩
      · rw [conjMap, mapVV_conj_embLL, hf, mapVV_conj_embLL]
      · have hu : nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (p.embedding.comp (starRingEnd D.what₂.LL)) _
            (mapF (starRingEnd D.what₂.LL) _ w)) ≤ B := by
          rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
        rw [mapVV_mapF]
        exact le_of_ext D _ _ p.embedding hf0 hne a2 n2 G2 _ _ _ (by linarith) (by linarith) (by linarith) _ B
          ((nrm_one_nonneg _ _).trans hw) (fun ρ hρ => hb2 Φ β d hO c i f hf p.embedding ρ hρ _ B hu)

end Std

end GlobalTheory.KerConjMean

end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

theorem _root_.GlobalTheory.T.isFundamentalDomain_saturated_fundamentalSet_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  first | exact @GlobalTheory.FundFrames.isFundamentalDomain_satFrames | exact GlobalTheory.FundFrames.isFundamentalDomain_satFrames | (intros; apply GlobalTheory.FundFrames.isFundamentalDomain_satFrames <;> assumption)
end

section

open NumberField


theorem _root_.GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  first | exact @GlobalTheory.VacRead.rl_div_scale | exact GlobalTheory.VacRead.rl_div_scale | (intros; apply GlobalTheory.VacRead.rl_div_scale <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchCoords


open GlobalTheory.FockVacuum in
theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]

    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_cplx_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoords
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg : ∀ (p : ℕ) (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)), p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  first | exact @GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | exact GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | (intros; apply GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j <;> assumption)
end
