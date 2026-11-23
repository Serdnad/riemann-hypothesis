module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle424
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn

theorem rowTest_setting_dat : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L →
    GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  refine Ev.mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK B f T w Z hX Wt z hOv hG hEx L hsz
  obtain ⟨hHost, hF, -, -, -, -, -, hstdX⟩ := hK (w.st Z) hOv
  have hC := z.pins.char
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hC hEx).1
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  exact
    { size := hsz
      eser := hG.eSerTie Z.V Z.S Z.G
      host := hHost
      hF := hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := z.pins.keep.guard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := z.pins.keep.std
      stdX := hstdX
      betaX := z.pins.keep.beta.2 }

end GlobalTheory.PrimIn
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

variable {D : D7}

theorem exists_F_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∉ P.asIdeal := by
  classical
  choose! x hx hxP using hP
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ v ∈ S, x v) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hv := hS Q hJ
    have hxv : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hv
    rw [map_prod, ← Finset.prod_erase_mul _ _ hv]
    exact Ideal.mul_mem_left J _ hxv
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ v ∈ S, x v) ^ K, by rwa [map_pow], fun h => ?_⟩
  rw [map_pow] at h
  have h1 := P.isPrime.mem_of_pow_mem K h
  rw [map_prod] at h1
  obtain ⟨v, hv, h2⟩ := (P.isPrime.prod_mem_iff).1 h1
  exact hxP v hv _ rfl h2

theorem oToS_smul_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    oToS F E a • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Subring.smul_def, oToS_coe]
    simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx

end GlobalTheory.CongMember

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_sub_one {R : Type} [CommRing R] (u : R) (hu : u * u = u) (A B K : Matrix (Fin n) (Fin n) R)
    (hA : u • (A - 1) = A - 1) (hB : (1 - u) • (B - 1) = B - 1) (hK : K = A * B ∨ K = B * A) : A - 1 = u • (K - 1) := by
  have e1 : u • B = u • 1 := by
    rw [← sub_eq_zero, ← smul_sub, ← hB, smul_smul, mul_sub, mul_one, hu, sub_self, zero_smul]
  have e2 : u • K = u • A := by
    rcases hK with rfl | rfl
    · rw [← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]
    · rw [← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]
  rw [smul_sub, e2, ← smul_sub, hA]

theorem cong_of_eq (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    (u : Formalism.L2.Herm.intAf F E) (A K : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (e : A - 1 = ((u * oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • (K - 1))
    (hK : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, K *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, A *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  intro y hy
  have e1 : A *ᵥ y - y = (A - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e2 : K *ᵥ y - y = (K - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e' : A *ᵥ y - y = (u * oToS F E a) • (K *ᵥ y - y) := by
    rw [e1, e2, e, Matrix.smul_mulVec, Subring.smul_def]
  rw [e', mul_smul]
  exact Submodule.smul_mem _ u (oToS_smul_mem_hatL Λ ha (Submodule.sub_mem _ (hK y hy) hy))

theorem hatL_smul_le (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) :
    Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) ≤ Formalism.L2.Herm.hatL (F := F) Λ :=
  Submodule.span_mono (Set.image_mono Submodule.smul_le_right)

theorem mem_congLev_of [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hU : x ∈ UA hc J)
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ))
    (h2 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    x ∈ congLev hc J Λ 𝔪 := by
  refine ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, h1⟩
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h1 y hy)) hy
    rwa [sub_add_cancel] at this
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h2 _ hy)) hy
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec, sub_add_cancel] at this

theorem stab_of_mem_congLev [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {𝔪 : Ideal (𝓞 E)} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ congLev hc J Λ 𝔪) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  ⟨fun y hy => (hx.2.1 y).1 hy, fun y hy => ((Subgroup.inv_mem _ hx).2.1 y).1 hy⟩

end General

variable {D : D7}

theorem exists_idem_eq {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) {e f : Formalism.L2.Theta.AE D} (hi : IsPrimeIdem P e f) :
    ∃ a ∈ 𝔪, ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      ((u * oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = GlobalTheory.LevSplit.finSw D f := by
  obtain ⟨X, hX𝔪, hXP⟩ := exists_F_mem h𝔪 hS hP
  obtain ⟨u, hu⟩ := GlobalTheory.LevSplit.idem_div_int hi _ _ ((D.sp.cm.fixed _).2 ⟨(X : D.host.F), rfl⟩).symm hXP hXP
  exact ⟨_, hX𝔪, u, hu⟩

end GlobalTheory.CongMember
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree


theorem _root_.GlobalTheory.T.weilRep_commute_at_good_places_algebraic_vectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωB : WRep W₁ X), IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, ∀ z : GA D W₁ →₀ ℂ,
      (∀ k ∈ z.support, k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) → ∀ i, ∃ u' ∈ GfC W₁,
        (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) = ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  first | exact @GlobalTheory.GoodComm.comm_at_good_place | exact GlobalTheory.GoodComm.comm_at_good_place | (intros; apply GlobalTheory.GoodComm.comm_at_good_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareComm.AlgDeriv

open Complex GlobalTheory.FockIndep GlobalTheory.ArchRec.DerFock
open scoped Real

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem exists_dRho_pure_all (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS frS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (εS : D.what₂.Tau → Fin S.rank → Bool)
    (sT frT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (εT : D.what₂.Tau → Fin T.rank → Bool)
    (hfS : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D S ρ) (sS ρ) (εS ρ) (frS ρ))
    (hfT : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D T ρ) (sT ρ) (εT ρ) (frT ρ))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ L : Module.End ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ), ∀ f, IsThetaFunO ψ S T f →
      IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f → ∀ P,
      Datum.dRho (heisO ψ S T) θ τ z (pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f P) =
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f (L P) := by
  classical
  have hS := fun ρ => isCartanInv_of_isFrameOf (hfS ρ)
  have hT := fun ρ => isCartanInv_of_isFrameOf (hfT ρ)
  let A : FVar D T.rank S.rank → (WO S T → ℂ) → (WO S T → ℂ) :=
    aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ)) (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)
  let u : Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun k => unitMap (frS τ)⁻¹ (frT τ)⁻¹ k.1 k.2
  let α : Fin T.rank × Fin S.rank → ℂ := fun k =>
    if (εT τ k.1 == εS τ k.2) then (frT τ * z * (frS τ)⁻¹) k.1 k.2
    else starRingEnd ℂ ((frT τ * z * (frS τ)⁻¹) k.1 k.2)
  let c : FVar D T.rank S.rank → ℂ := fun k => if k.1 = τ then (fockScale D τ : ℂ)⁻¹ * (-(4 * π * I) *
    ((omDir S T τ z τ (u k.2) : ℝ) + I * (omDir S T τ (cplxO (sS τ) (sT τ) z) τ (u k.2) : ℝ))) else 0
  refine ⟨(1 / 2 : ℂ) • ((∑ k, c k • (MvPolynomial.pderiv k).toLinearMap) +
    (fockScale D τ : ℂ) • ∑ k : Fin T.rank × Fin S.rank,
      α k • LinearMap.mulLeft ℂ (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank))), fun f hf hv P => ?_⟩
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A k g) := fun k _ h => aPlus_theta hψ hθ k.1 _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → A i (A j g) = A j (A i g) := by
    rintro ⟨ρ, a, b⟩ ⟨ρ', a', b'⟩ g h
    by_cases e : ρ = ρ'
    · subst e
      exact aPlus_comm (hS ρ) (hT ρ) _ _ hψ hθ h
    · exact GlobalTheory.TwoPlaceComm.aPlus_comm_ne hψ hθ e _ _ _ _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hm := pure_mem hadd hsm hA hf P
  have hBA : ∀ j g, IsThetaFunO ψ S T g → Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (A j g) =
      A j (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) + c j • g := by
    rintro ⟨ρ, a, b⟩ g h
    by_cases e : ρ = τ
    · subst e
      refine (annih_aPlus (hS ρ) (hT ρ) z (u (a, b)) hψ hθ h).trans ?_
      congr 2
      exact (if_pos rfl).symm
    · rw [show c (ρ, a, b) = 0 from if_neg e, zero_smul, add_zero]
      exact GlobalTheory.TwoPlaceComm.annih_aPlus_ne hψ hθ (Ne.symm e) _ _ _ _ h
  have h1 := pure_deriv (B := Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z) (c := c) hadd hsm hA hc Aadd Asm
    (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h) hBA hf (hv z) P
  have h2 : Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (pureTensorL A f P) =
      pureTensorL A f (∑ k : Fin T.rank × Fin S.rank,
        α k • (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank) * P)) := by
    conv_lhs => rw [eq_sum_unitMap (hfS τ).1 (hfT τ).1 z]

    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hm _ _ (cplxO_unitMap (hfS τ) (hfT τ) k.1 k.2), map_smul,
      pure_X_mul hadd hsm hA hc Aadd Asm hf]
    rfl
  have h3 : ∀ g, Datum.dRho (heisO ψ S T) θ τ z g =
      (1 / 2 : ℂ) • (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g +
        (fockScale D τ : ℂ) • Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) := fun g => by
    rw [Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero τ), one_smul, Datum.annih, Datum.crea]
    module
  change Datum.dRho (heisO ψ S T) θ τ z (pureTensorL A f P) = pureTensorL A f _
  rw [h3, h1, h2, ← map_smul, ← map_add (f := _), ← map_smul]
  congr 1
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
  rfl

end GlobalTheory.SquareComm.AlgDeriv


open GlobalTheory.SquareComm.AlgDeriv in
theorem GlobalTheory.SquareComm.dRho_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε S X A B f hf τ z
  have hth : ∀ g ∈ algF ψ θ ε A B, IsThetaFunO ψ (sgn ε S) X g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₀, P, hf₀, rfl⟩ := hx
      exact GlobalTheory.FockIndep.pure_mem (A := aPlusAll (heisO ψ (sgn ε S) X) θ
          (fun ρ => cplxO ((frSgn ε A).cart ρ) (B.cart ρ)) A.onb B.onb) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
        (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun k _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 _ _ h) hf₀.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul a x _ hx => exact GlobalTheory.OrientedHeis.theta_smul a hx
  obtain ⟨L, hL⟩ := exists_dRho_pure_all (S := sgn ε S) (T := X) hψ hθ (frSgn ε A).cart (frSgn ε A).fr (frSgn ε A).ε
    B.cart B.fr B.ε (fun ρ => ⟨(frSgn ε A).fr_unit ρ, (frSgn ε A).fr_gram ρ, rfl⟩)
    (fun ρ => ⟨B.fr_unit ρ, B.fr_gram ρ, rfl⟩) τ z
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, P, hf₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨f₀, L P, hf₀, hL f₀ hf₀.1 (hf₀.2 τ) P⟩
  | zero =>
    have h0 := GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε S) (T := X))
    rw [zero_smul, zero_smul] at h0
    rw [h0]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [GlobalTheory.FockIndep.dRho_add (S := sgn ε S) (T := X) hψ hθ τ z (hth x hx) (hth y hy)]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z a (hth x hx)]
    exact Submodule.smul_mem _ a ih

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorFin

theorem isLocOp_of_mem_span {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (p : Place D)
    {x : WO S T → ℂ} (hx : x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt p w) f₀)) :
    IsThetaFunO ψ S T x ∧ IsLocOp ψ S T μ 𝓕 f₀ p x := by
  have hh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have ip := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨hh _ _ h₀, fun φ => φ w, fun _ _ => rfl, fun f hf => ⟨_, hh (wAt p w) f hf, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  | zero =>
    have hz : ∀ g, ipO μ 𝓕 (0 : WO S T → ℂ) g = 0 := fun g => by simp [ipO]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun _ => 0, fun _ _ => by simp,
      fun f _ => ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun g _ => hz g⟩, fun g _ => hz g⟩
  | add y z _ _ hy hz =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    obtain ⟨tz, M, M1, M2, M3⟩ := hz
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add ty tz, fun φ => L φ + M φ, fun c φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1, M1, mul_add]
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      obtain ⟨b, tb, hb⟩ := M2 f hf
      refine ⟨a + b, GlobalTheory.WeilVacMove.isTheta_add ta tb, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.2.1 b tb).1, ha g hg, hb g hg]
    · rw [((ip y g ty hg).2.2.2.1 z tz).1, L3 g hg, M3 g hg]
  | smul c y _ hy =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul c ty, fun φ => c * L φ, fun d φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1]
      ring
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      refine ⟨c • a, GlobalTheory.WeilVacMove.isTheta_smul c ta, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.1 c).1, ha g hg]
    · rw [((ip y g ty hg).2.2.1 c).1, L3 g hg]

theorem isLocOp_of_isLocal_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x :=
  fun D ψ θ S T sS sT ΛS ΛT f₀ _ _ hb hμ v x hx =>
    (isLocOp_of_mem_span (base_std hb) hμ (base_theta hb) (.inl v)
      (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)).2

end GlobalTheory.PlaceTensorFin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ bddAut V, f ≠ 0 → (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → ∃ B : Fam D.host.E, IsParamFunV V Sb f B ∧ Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B V.rank (((V.rank : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.FinZeta.ParamBound.exists_param_bounded | exact GlobalTheory.FinZeta.ParamBound.exists_param_bounded | (intros; apply GlobalTheory.FinZeta.ParamBound.exists_param_bounded <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  first | exact @GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent | exact GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent | (intros; apply GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent <;> assumption)
end
