module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle355
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.IsoTrace

theorem intertwining_sum_apply {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ G N} {ρ : Representation ℂ G X} {ι : Type} (t : Finset ι)
    (c : ι → ℂ) (φ : ι → π.IntertwiningMap ρ) (n : N) : (∑ j ∈ t, c j • φ j) n = ∑ j ∈ t, c j • φ j n := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => simp [Finset.sum_insert ha, ih]

theorem trace_mul_isotypic : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur hiso H hH ⟨s, hs⟩
  let S := Submodule.span ℂ (s : Set (π.IntertwiningMap ρ))
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s
  let bS := Module.finBasis ℂ S
  let φ : Fin (Module.finrank ℂ S) → π.IntertwiningMap ρ := fun j => (bS j : π.IntertwiningMap ρ)
  have hli : LinearIndependent ℂ φ := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hinj := GlobalTheory.T.injective_sum_of_linIndep_intertwiners G N X π ρ hirr hschur _ φ hli
  have hY : LinearMap.range H ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
    refine hs.trans (iSup₂_le fun ψ hψ => ?_)
    have hψS : ψ ∈ S := Submodule.subset_span hψ
    have e : ψ = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j := by
      have := congrArg Subtype.val (bS.sum_repr ⟨ψ, hψS⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rintro _ ⟨n, rfl⟩
    have hn : ψ n = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j n := by
      rw [← intertwining_sum_apply, ← e]
    change ψ n ∈ _
    rw [hn]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨n, rfl⟩)
  have hcoef : ∀ ψ : π.IntertwiningMap ρ, ∃ c : Fin (Module.finrank ℂ S) → ℂ,
      ∀ n, H (ψ n) = ∑ j, c j • φ j n := by
    intro ψ
    let Hψ : π.IntertwiningMap ρ := (H ∘ₗ ψ.toLinearMap).intertwiningMap_of_isIntertwiningMap π ρ
      (fun g v => by simp [ψ.isIntertwining, hH])
    have hr : LinearMap.range Hψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
      rintro _ ⟨n, rfl⟩
      exact hY ⟨ψ n, rfl⟩
    exact GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range G N X π ρ hschur _ φ hinj Hψ hr
  choose hc hhc using fun j => hcoef (φ j)
  refine ⟨∑ j, hc j j, fun A B hB b hb => ?_⟩
  obtain ⟨hfin, htr⟩ := hb
  let R := LinearMap.range A
  let Φ' : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] X :=
    ∑ j, (φ j).toLinearMap ∘ₗ R.subtype ∘ₗ LinearMap.proj j
  have hΦ' : ∀ w, Φ' w = ∑ j, φ j (w j : N) := by
    intro w
    simp [Φ', LinearMap.sum_apply]
  have hinj' : Function.Injective Φ' := by
    intro w w' e
    rw [hΦ', hΦ'] at e
    have := hinj e
    funext j
    exact Subtype.ext (congrFun this j)
  let Z := LinearMap.range Φ'
  have hBφ : ∀ (ψ : π.IntertwiningMap ρ) n, B (ψ n) = ψ (A n) := fun ψ n =>
    DFunLike.congr_fun (hB ψ) n
  have hrange : LinearMap.range (H ∘ₗ B) ≤ Z := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ f : π.IntertwiningMap ρ, LinearMap.range f.toLinearMap := by
      have : x ∈ isoPartAlg π ρ := hiso ▸ Submodule.mem_top
      exact this
    refine Submodule.iSup_induction _ (motive := fun x => (H ∘ₗ B) x ∈ Z) hx ?_ ?_ ?_
    · rintro ψ _ ⟨n, rfl⟩
      obtain ⟨c, hc'⟩ := hcoef ψ
      refine ⟨fun j => c j • ⟨A n, LinearMap.mem_range_self A n⟩, ?_⟩
      rw [hΦ']
      simp only [LinearMap.comp_apply, Pi.smul_apply, SetLike.val_smul, map_smul]
      rw [show ψ.toLinearMap n = ψ n from rfl, hBφ, hc']
    · simp
    · intro x y hx hy
      simpa using Z.add_mem hx hy
  haveI : FiniteDimensional ℂ Z := LinearMap.finiteDimensional_range Φ'
  have hT1 := GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional X (H ∘ₗ B) Z hrange
  let e : (Fin (Module.finrank ℂ S) → R) ≃ₗ[ℂ] Z := LinearEquiv.ofInjective Φ' hinj'
  let A' : R →ₗ[ℂ] R := A.restrict (p := R) (q := R) fun v _ => LinearMap.mem_range_self A v
  let h : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ := Matrix.of fun k j => hc j k
  let M : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → R) :=
    ∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ => R) k ∘ₗ A' ∘ₗ LinearMap.proj j)
  have hM : ∀ w k, (M w k : N) = ∑ j, hc j k • A (w j) := by
    intro w k
    simp [M, h, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, A']
  have hconj : (H ∘ₗ B).restrict (p := Z) (q := Z) (fun x _ => hrange (LinearMap.mem_range_self _ x)) =
      e.conj M := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change H (B (Φ' w)) = Φ' (M w)

    rw [hΦ', hΦ', map_sum, map_sum]

    simp_rw [hBφ, hhc, hM, map_sum, map_smul]
    rw [Finset.sum_comm]
  have key : LinearMap.trace ℂ Z ((H ∘ₗ B).restrict (p := Z) (q := Z)
      fun x _ => hrange (LinearMap.mem_range_self _ x)) = (∑ j, hc j j) * b := by
    rw [hconj, LinearMap.trace_conj', GlobalTheory.T.trace_sum_single_comp_proj_eq R _ h A', ← htr]
    simp [h, Matrix.trace, A', R]
  rw [← key]
  exact hT1

end GlobalTheory.IsoTrace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.AAUnit

theorem natCast_notMem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (h : Nat.Coprime n p) (hp : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ w.asIdeal := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hn) (w.asIdeal.mul_mem_left v hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem absNorm_cmIdeal_not_mem_gridPlaces {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  rcases P.mem_S0_of_sum_eq.mp hv with h | h
  ·
    subst h
    have hq := GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (D := D)
    exact natCast_notMem_of_coprime P.v0 ((Nat.Prime.coprime_iff_not_dvd hq.1).mpr hq.2.2).symm P.basePlace_over_qZero
  ·
    have hcop : ∀ p ∈ D.host.levelPrimes, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
        ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal :=
      fun p hp hpv => natCast_notMem_of_coprime v (D.host.ccK_coprime p (by simp [hp])) hpv
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF (D := D)).mp h with h' | h' | h' | h'
    · exact hcop _ (D.host.g_level 0) h'
    · exact hcop _ (D.host.g_level 1) h'
    · exact hcop _ D.host.pde_level.1 h'
    · exact hcop _ D.host.pde_level.2 h'

theorem exists_valuation_one_element_at_grid_places : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.SepRows.OffQ D → L.Is μ₀ → ∀ (G : GridData L sc), ∀ w ∈ G.pl.W0, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1 := by
  intro D T L sc μ₀ _ _ G w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw

  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := by
    intro hin
    apply absNorm_cmIdeal_not_mem_gridPlaces G.pl hv
    have hc : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈ ((G.pl.w v).under (𝓞 D.host.F)).asIdeal := by
      show ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈
        Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (G.pl.w v).asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hin
    rw [G.pl.under_w hv] at hc
    exact hc
  refine ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩
  have key := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) (v := G.pl.w v)).mpr hN
  rw [map_natCast] at key
  first
  | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := G.pl.w v) _).trans key
  | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact key)

end GlobalTheory.AAUnit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.KerTrans

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_fin (p : Pair T) (k : FinPt G p.small) :
    (G.toPair p k.1 1).1 ∈ GfC (G.pS p) ∧ (G.toPair p k.1 1).2 ∈ GfC (G.pT p) := by
  cases p <;> simp [GridData.toPair]

theorem ker_mul_fin (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h : GA D (G.V p.big)) : W.ker p F (g * k) h = W.ker p (W.om p (G.toPair p k 1) F) g h := by
  have e : G.toPair p (g * k) h = G.toPair p g h * G.toPair p k 1 := by
    rw [← GlobalTheory.RowClaim.toPair_mul, mul_one]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G)
    {p : Pair T}, p.InRange D.R.m → ∀ (f : WO (G.pS p) (G.pT p) → ℂ), IsThetaFunO W.ψ (G.pS p) (G.pT p) f →
    ∀ (g k : FinPt G p.small) (h : FinPt G p.big),
      fockComp W B p f (g * k) h = fockComp W B p (W.om p (G.toPair p k.1 1) f) g h := by
  intro D T L sc G W B p hp f hf g k h
  have hk := toPair_fin p k
  unfold fockComp
  congr 1
  funext m
  unfold jetTab kerFin
  rw [Subgroup.coe_mul, ker_mul_fin]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) (W.om_is p hp) W.θ W.θ_is _ hk.1 _ hk.2 _ _ _ _ f _ hf

end GlobalTheory.KerTrans

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
        invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  first | exact @GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | exact GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | (intros; apply GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.partialFourierSum_firstBlock_blockDiagonal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ Y : Matrix A (D₁ ⊕ D₂) k,
      fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) Y =
        fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) := by
  first | exact @GlobalTheory.BlockSubst.fourierSum_blockDiag_one | exact GlobalTheory.BlockSubst.fourierSum_blockDiag_one | (intros; apply GlobalTheory.BlockSubst.fourierSum_blockDiag_one <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SmoothAvg

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}


open Classical in
theorem norm_apply_eq (hπ : IsUnitaryRep π) {Ψ : ContinuousMultilinearMap ℂ M.H H} (hΨ : Ψ ∈ homDS M π ⊤)
    (y : ∀ τ, M.H τ) : ‖Ψ y‖ = ‖Ψ (fun τ => unitVec (H := M.H τ))‖ * ∏ τ, ‖y τ‖ := by
  have h := inner_eq_bePi (isIrrUnitary_dsRep M) hπ hΨ hΨ y y
  rw [bePi] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Ψ y‖ ^ 2 = (‖Ψ (fun τ => unitVec (H := M.H τ))‖ * ∏ τ, ‖y τ‖) ^ 2 := by
    rw [mul_pow, ← Finset.prod_pow]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) two_ne_zero).1 h2


open Classical in
theorem isClosed_homDS : IsClosed (homDS M π ⊤ : Set (ContinuousMultilinearMap ℂ M.H H)) := by
  refine isClosed_of_closure_subset fun Φ hΦ => ⟨fun _ => trivial, fun i g y => ?_⟩
  have hc : IsClosed {Ψ : ContinuousMultilinearMap ℂ M.H H |
      Ψ (Function.update y i (dsRep M i g (y i))) = π (embW V (placeOf D i) g) (Ψ y)} :=
    isClosed_eq (continuous_eval_const _) ((π _).continuous.comp (continuous_eval_const _))
  exact closure_minimal (fun Ψ (hΨ : Ψ ∈ homDS M π ⊤) => hΨ.2 i g y) hc hΦ

end GlobalTheory.SmoothAvg

namespace GlobalTheory.SmoothAvg

theorem nonarchimedeanGroup_GfC (D : D7) (V : HSp D) : NonarchimedeanGroup (GfC V) :=
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig V.gram
  NonarchimedeanGroup.nonarchimedean_of_emb (finPtsEquiv D.sp.cm.sig V.gram).toMonoidHom
    (finPtsEquiv D.sp.cm.sig V.gram).toHomeomorph.isOpenEmbedding

theorem exists_smooth_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ (hU : IsSubrep π ⊤) (Φ : homDS M π ⊤), Φ ≠ 0 → ∃ Ψ ∈ GlobalTheory.PRep.smoothPart (finPartDS M hU), Ψ ≠ 0 := by
  intro D V S M H _ _ _ π hπ hU Φ hΦ
  let u : ∀ τ, M.H τ := fun τ => unitVec (H := M.H τ)
  let f : homDS M π ⊤ →L[ℂ] H :=
    (ContinuousMultilinearMap.apply ℂ M.H H u).comp (homDS M π ⊤).subtypeL
  have hnorm : ∀ Ψ : homDS M π ⊤, ‖Ψ‖ ≤ ‖f Ψ‖ := fun Ψ => by
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun y => ?_
    exact (norm_apply_eq hπ Ψ.2 y).le
  have hinj : Function.Injective f := fun a b h => by
    have h0 : ‖a - b‖ ≤ 0 := by simpa [map_sub, h] using hnorm (a - b)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  haveI : CompleteSpace (homDS M π ⊤) := (isClosed_homDS (π := π)).completeSpace_coe
  have hclosed : IsClosed (Set.range f) :=
    (f.antilipschitz_of_bound (K := 1) fun x => by simpa using hnorm x).isClosed_range f.uniformContinuous
  have hequiv : ∀ (g : GfC V) (Ψ : homDS M π ⊤), f (finPartDS M hU g Ψ) = π g (f Ψ) := fun g Ψ => rfl
  have hv : f Φ ≠ 0 := fun h => hΦ (hinj (by rw [h, map_zero]))
  haveI := nonarchimedeanGroup_GfC D V
  have hcont : Continuous fun g : GfC V => π g (f Φ) := (hπ.continuous_apply _).comp continuous_subtype_val
  have hN : {g : GfC V | dist (π g (f Φ)) (f Φ) < ‖f Φ‖ / 2} ∈ nhds (1 : GfC V) :=
    (isOpen_lt (hcont.dist continuous_const) continuous_const).mem_nhds (by simp [norm_pos_iff.2 hv])
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean _ hN
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let O : Set H := Set.range fun k : K => π ((k : GfC V) : GA D V) (f Φ)
  let C : Set H := closure (convexHull ℝ O)
  have hCconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hvO : f Φ ∈ O := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨f Φ, subset_closure (subset_convexHull ℝ O hvO)⟩
  obtain ⟨w, hwC, hw⟩ := exists_norm_eq_iInf_of_complete_convex hCne isClosed_closure.isComplete hCconv 0
  have hmin : ∀ x ∈ C, ‖w‖ ≤ ‖x‖ := fun x hx => by
    have h1 := ciInf_le (f := fun z : C => ‖0 - (z : H)‖)
      ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ ⟨x, hx⟩
    rw [← hw] at h1
    simpa using h1
  have hball : C ⊆ Metric.closedBall (f Φ) (‖f Φ‖ / 2) :=
    closure_minimal (convexHull_min (by rintro _ ⟨k, rfl⟩; exact Metric.mem_closedBall.2 (hK k.2).le)
      (convex_closedBall _ _)) Metric.isClosed_closedBall
  have hw0 : w ≠ 0 := by
    rintro rfl
    have h1 := Metric.mem_closedBall.1 (hball hwC)
    rw [dist_zero_left] at h1
    exact hv (norm_le_zero_iff.1 (by linarith))
  have hRconv : Convex ℝ (Set.range f) := by
    have h1 := ((LinearMap.range (f : homDS M π ⊤ →ₗ[ℂ] H)).restrictScalars ℝ).convex
    rw [Submodule.coe_restrictScalars, LinearMap.coe_range, ContinuousLinearMap.coe_coe] at h1
    exact h1
  have hOR : O ⊆ Set.range f := by
    rintro _ ⟨k, rfl⟩
    exact ⟨finPartDS M hU k Φ, hequiv _ _⟩
  obtain ⟨Ψ, hΨ⟩ : w ∈ Set.range f := closure_minimal (convexHull_min hOR hRconv) hclosed hwC
  have hinv : ∀ k : K, π ((k : GfC V) : GA D V) w = w := by
    intro k
    let T : H →L[ℝ] H := (π ((k : GfC V) : GA D V)).restrictScalars ℝ
    have hTO : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨k * j, ?_⟩
      simp [T]
    have hTC : T '' C ⊆ C := by
      refine (image_closure_subset_closure_image T.continuous).trans (closure_mono ?_)
      exact (T.toLinearMap.image_convexHull O).trans_subset (convexHull_mono hTO)
    have hx : π ((k : GfC V) : GA D V) w ∈ C := hTC ⟨w, hwC, rfl⟩
    have hn : ‖π ((k : GfC V) : GA D V) w‖ = ‖w‖ := hπ.norm_apply _ _
    have hmid : (1 / 2 : ℝ) • (w + π ((k : GfC V) : GA D V) w) ∈ C := by
      have h1 := hCconv hwC hx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using h1
    have h1 := hmin _ hmid
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    have hp := parallelogram_law_with_norm ℂ w (π ((k : GfC V) : GA D V) w)
    rw [hn] at hp
    have h2 : ‖w - π ((k : GfC V) : GA D V) w‖ ^ 2 ≤ 0 := by
      nlinarith [norm_nonneg w, norm_nonneg (w + π ((k : GfC V) : GA D V) w)]
    have h3 : ‖w - π ((k : GfC V) : GA D V) w‖ = 0 := by nlinarith [norm_nonneg (w - π ((k : GfC V) : GA D V) w)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
  refine ⟨Ψ, GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (K.isOpen.mem_nhds K.one_mem) fun g hg => ?_),
    fun h => hw0 (by rw [← hΨ, h, map_zero])⟩
  exact hinj (by rw [hequiv, hΨ]; exact hinv ⟨g, hg⟩)

end GlobalTheory.SmoothAvg
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.LocFinComp

theorem prV_swap_snd {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (u : HeightOneSpectrum (𝓞 F)) (x : AF F ⊗[F] E) :
    Formalism.UG.prV (E := E) u (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x)) =
    Algebra.TensorProduct.comm F (Fv F u) E (Algebra.TensorProduct.map (evFin F u) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact Eq.refl _
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem finE_locFin_map_prV_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  intro D V v u huv g
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (locFin V v g : GA D V) = 1 :=
    GlobalTheory.AdelicU.proj_emb_ne D.sp.cm.sig V.gram huv g
  have hm := congrArg (fun y => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram y).val) hp
  simp only [GlobalTheory.AdelicU.matHom_proj, map_one, Units.val_one] at hm
  ext i j
  have hij := congrFun (congrFun hm i) j
  have key := prV_swap_snd (F := D.host.F) (E := D.host.E) u
    ((Formalism.L2.Theta.matHom V (locFin V v g : GA D V)).val i j)
  refine key.trans ((congrArg (Algebra.TensorProduct.comm _ _ _) hij).trans ?_)
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

end GlobalTheory.LocFinComp
end
