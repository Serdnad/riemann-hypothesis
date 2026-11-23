module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPiProdSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdContr
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle629
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.RowShape.OffLat

variable {D : D7}

theorem latV_le_of_smul (S : HSp D) (L M : GlobalTheory.FinPl.Lat S) {v : GlobalTheory.FinPl.Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (h : ∀ x ∈ L, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x ∈ M) :
    GlobalTheory.FinPl.latV S L (· = v) ≤ GlobalTheory.FinPl.latV S M (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, e, he, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at he
  subst he
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ v.asIdeal.zero_mem)
  have htF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hval : v.intValuation t = 1 :=
    le_antisymm (v.intValuation_le_one t) (not_lt.mp fun h => ht ((v.intValuation_lt_one_iff_mem t).mp h))
  have hcv : evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
    rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((((t : D.host.F)⁻¹ : D.host.F)) : v.adicCompletion D.host.F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      show (t : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F t from rfl,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval, inv_one]
  apply AddSubgroup.subset_closure
  refine ⟨α * algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹, ?_, ?_, 1, rfl, _, h x hx, ?_⟩
  · intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact Subring.mul_mem _ (hα w) hcv
    · rw [hsupp w hw, zero_mul]
      exact Subring.zero_mem _
  · intro w hw
    rw [map_mul, hsupp w hw, zero_mul]
  · funext i
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x i = (t : D.host.F) • x i := by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
    rw [Pi.smul_apply, one_mul, one_mul, hx', ← TensorProduct.smul_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : InfiniteAdeleRing D.host.F) = (t : D.host.F) • (0 : InfiniteAdeleRing D.host.F)
      rw [smul_zero]
    · change α = (t : D.host.F) • (α * algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹)
      rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ htF, map_one, mul_one]

theorem smul_mem_lat {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (r : 𝓞 D.host.E) (h : ∀ p, ∀ u ∈ 𝔟 p, r • u ∈ 𝔟' p) : ∀ x ∈ d.lat Λ 𝔟, r • x ∈ d.lat Λ 𝔟' := by
  intro x hx
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  refine ⟨r • y, Λ.smul_mem r hy, r • u, fun p => h p _ (hu p), ?_⟩
  rw [smul_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem smul_mem_of_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (𝔟 : FractionalIdeal R⁰ K) {I J : Ideal R} {s : R} (hJ0 : J ≠ ⊥) (hJ : s ∈ J) {a b n : ℕ} (hn : b ≤ n) {u : K}
    (hu : u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹) : s ^ n • u ∈ 𝔟 := by
  have hJb : ((J : FractionalIdeal R⁰ K) ^ b) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hsb : algebraMap R K (s ^ b) ∈ (J : FractionalIdeal R⁰ K) ^ b := by
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨s ^ b, Ideal.pow_mem_pow hJ b, rfl⟩
  have hprod := FractionalIdeal.mul_mem_mul hsb hu
  have hcancel : (J : FractionalIdeal R⁰ K) ^ b * (𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹)
      = 𝔟 * (I : FractionalIdeal R⁰ K) ^ a := by
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hJb, mul_one]
  have hle : 𝔟 * (I : FractionalIdeal R⁰ K) ^ a ≤ 𝔟 :=
    mul_le_of_le_one_right' (pow_le_one' FractionalIdeal.coeIdeal_le_one _)
  have hb : s ^ b • u ∈ 𝔟 := by
    rw [Algebra.smul_def]
    exact hle (hcancel ▸ hprod)
  have hsplit : s ^ n • u = s ^ (n - b) • s ^ b • u := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  exact Submodule.smul_mem (𝔟 : Submodule R K) _ hb

theorem smul_mem_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (𝔟 : FractionalIdeal R⁰ K) {I J : Ideal R} {s : R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : s ∈ I) {a b n : ℕ} (hn : a ≤ n)
    {u : K} (hu : u ∈ 𝔟) :
    s ^ n • u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
  have hsa : algebraMap R K (s ^ a) ∈ (I : FractionalIdeal R⁰ K) ^ a := by
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨s ^ a, Ideal.pow_mem_pow hI a, rfl⟩
  have hJb : ((J : FractionalIdeal R⁰ K) ^ b) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hone : (1 : FractionalIdeal R⁰ K) ≤ ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
    have := FractionalIdeal.inv_anti_mono hJb (pow_le_one' FractionalIdeal.coeIdeal_le_one _)
    simpa using this
  have hle : 𝔟 * (I : FractionalIdeal R⁰ K) ^ a ≤ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ :=
    le_mul_of_one_le_right' hone
  have ha : s ^ a • u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
    rw [Algebra.smul_def, mul_comm (algebraMap R K (s ^ a)) u]
    exact hle (FractionalIdeal.mul_mem_mul hu hsa)
  have hsplit : s ^ n • u = s ^ (n - a) • s ^ a • u := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  exact Submodule.smul_mem ((𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ :
    FractionalIdeal R⁰ K) : Submodule R K) _ ha

end GlobalTheory.RowShape.OffLat


open GlobalTheory.RowShape.OffLat in
theorem GlobalTheory.RowShape.latV_grid_iff_rowN_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = v) ↔ y ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = v)) := by
  intro D T L sc G v hv y _
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hgrid : G.Λ (.grid D.R.m 0) =
      (G.rowDec 0 hm).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m hm le_rfl
  have hrow : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 hm).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    rw [GlobalTheory.RowShape.rowN, dite_eq_left hm]
  obtain ⟨s, hs, hsI⟩ := GlobalTheory.ModulUnit.exists_mem_modul G.pl sc hv
  obtain ⟨s', hs', hsJ⟩ := GlobalTheory.ModulUnit.exists_mem_modulBar G.pl sc hv
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    exact FaithfulSMul.algebraMap_injective _ _
  have hne : ∀ (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.F), r ∉ v.asIdeal →
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r ∈ I → I ≠ ⊥ := by
    intro I r hr hrI hI
    rw [hI, Ideal.mem_bot, ← map_zero (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))] at hrI
    exact hr (hinj hrI ▸ v.asIdeal.zero_mem)
  have hI0 := hne _ s hs hsI
  have hJ0 := hne _ s' hs' hsJ
  have hodd : ¬ Odd (0 : ℕ) := by simp
  have hid : ∀ p : Fin (D.R.m - 1 - 0), stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) p =
      GlobalTheory.RowShape.rowId D 0 p * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (p.1 + 1) *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (D.R.m - 1 - 0 - p.1))⁻¹ := by
    intro p
    simp only [stairId, GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, if_neg hodd, FractionalIdeal.spanSingleton_one,
      Places.stA, Places.stAbar, mul_pow, inv_pow, mul_inv, inv_inv, one_mul]
    ac_rfl
  have hA : ∀ x ∈ G.Λ (.grid D.R.m 0),
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (s' ^ (D.R.m - 1 - 0)) • x ∈ GlobalTheory.RowShape.rowN G 0 := by
    intro x hx
    rw [hgrid] at hx
    rw [hrow, map_pow]
    refine smul_mem_lat (G.rowDec 0 hm) (G.Λ (.top 0)) (𝔟 := stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0))
      (𝔟' := GlobalTheory.RowShape.rowId D 0) _ ?_ x hx
    intro p u hu
    rw [hid p] at hu
    exact smul_mem_of_mul _ hJ0 hsJ (a := p.1 + 1) (b := D.R.m - 1 - 0 - p.1) (n := D.R.m - 1 - 0) (Nat.sub_le _ _) hu
  have hB : ∀ x ∈ GlobalTheory.RowShape.rowN G 0,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (s ^ (D.R.m - 1 - 0)) • x ∈ G.Λ (.grid D.R.m 0) := by
    intro x hx
    rw [hrow] at hx
    rw [hgrid, map_pow]
    refine smul_mem_lat (G.rowDec 0 hm) (G.Λ (.top 0)) (𝔟 := GlobalTheory.RowShape.rowId D 0)
      (𝔟' := stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) _ ?_ x hx
    intro p u hu
    rw [hid p]
    have hp := p.isLt
    exact smul_mem_mul _ hI0 hJ0 hsI (a := p.1 + 1) (b := D.R.m - 1 - 0 - p.1) (n := D.R.m - 1 - 0) (by omega) hu
  have hpow : ∀ r : 𝓞 D.host.F, r ∉ v.asIdeal → r ^ (D.R.m - 1 - 0) ∉ v.asIdeal :=
    fun r hr h => hr (v.isPrime.mem_of_pow_mem _ h)
  have h1 := latV_le_of_smul _ _ _ (hpow s' hs') hA
  have h2 := latV_le_of_smul _ _ _ (hpow s hs) hB
  exact ⟨fun h => h1 h, fun h => h2 h⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul' (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem map_eq_one_of_off {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = w.under (𝓞 D.host.F))) : (Formalism.L2.Theta.mt V g).map p.π = 1 := by
  ext i k
  have h0 := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ g).1 hg i k _ rfl
  have h1 : p.π ((Formalism.L2.Theta.mt V g - 1) i k) = 0 := by
    rw [hp.2.1]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt _ _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero _ _ h0) w rfl
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1, ← Matrix.map_apply (f := p.π), Matrix.map_one _ (map_zero _) (map_one _)]

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem suppAt_mul' {e : AE D} {V : HSp D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) : SuppAt e V (a * b) := by
  rw [suppAt_iff'] at ha hb ⊢
  have : Formalism.L2.Theta.mt V (a * b) - 1 = (Formalism.L2.Theta.mt V a - 1) * Formalism.L2.Theta.mt V b + (Formalism.L2.Theta.mt V b - 1) := by
    rw [mt_mul', Matrix.sub_mul, Matrix.one_mul]; abel
  rw [this, smul_add, ← smul_mul_assoc, ha, hb]

theorem suppAt_inv' {e : AE D} {V : HSp D} {a : GA D V} (ha : SuppAt e V a) : SuppAt e V a⁻¹ := by
  rw [suppAt_iff'] at ha ⊢
  have : Formalism.L2.Theta.mt V a⁻¹ - 1 = -(Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a - 1)) := by
    rw [Matrix.mul_sub, mt_inv_mul', Matrix.mul_one]; abel
  rw [this, smul_neg, ← mul_smul_comm, ha]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem isLoc_mul' {S : HSp D} {F : Frame k S.rank Y} {a b : GA D S} {x y : GL Y k} (ha : p.IsLoc F a x)
    (hb : p.IsLoc F b y) : p.IsLoc F (a * b) (x * y) := by
  refine ⟨suppAt_mul' ha.1 hb.1, ?_⟩
  rw [mt_mul', Matrix.map_mul, ha.2, hb.2, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

theorem isLoc_inv' {S : HSp D} {F : Frame k S.rank Y} {a : GA D S} {x : GL Y k} (ha : p.IsLoc F a x) :
    p.IsLoc F a⁻¹ x⁻¹ := by
  refine ⟨suppAt_inv' ha.1, ?_⟩
  have h1 : (Formalism.L2.Theta.mt S a⁻¹).map p.π * (F.β * x.val * F.γ) = 1 := by
    rw [← ha.2, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  calc (Formalism.L2.Theta.mt S a⁻¹).map p.π = (Formalism.L2.Theta.mt S a⁻¹).map p.π * ((F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ)) := by
        rw [h2, Matrix.mul_one]
    _ = F.β * (x⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

omit p in
theorem frOf_conj {n N : ℕ} (h : N = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (x : GL (Fin n) (Lev.EAf D)) :
    (frOf h β w).β * (GlobalTheory.FunObj.inBasis h β w x).val * (frOf h β w).γ = (loc w x).val := by
  subst h
  have e1 : (frOf rfl β w).β = (loc w β).val := by ext i j; rfl
  have e2 : (frOf rfl β w).γ = ((loc w β)⁻¹).val := by ext i j; rfl
  have e3 : GlobalTheory.FunObj.inBasis rfl β w x = (loc w β)⁻¹ * loc w x * loc w β := by
    have e4 : GlobalTheory.FunObj.inBasis rfl β w x = GlobalTheory.StepData.reGL (finCongr rfl) (loc w (β⁻¹ * x * β)) := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e5 : ∀ g : GL (Fin N) (Kw w), GlobalTheory.StepData.reGL (finCongr rfl) g = g := fun g => Units.ext (by ext i j; rfl)
    rw [e4, e5, map_mul, map_mul, map_inv]
  rw [e1, e2, e3, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.FlatPlaceLoc

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem loc_finE {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} (g : GA D V) :
    (loc w (Lev.finE V g)).val = (Formalism.L2.Theta.mt V g).map p.π := by
  ext i j
  rw [Matrix.map_apply, hp.2.1]
  rfl

theorem isLoc_of_inBasis {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {N : ℕ} (h : N = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (gk : GL (Fin N) (Kw w)) (hs : SuppAt p.e V g)
    (hb : GlobalTheory.FunObj.inBasis h β w (Lev.finE V g) = gk) : p.IsLoc (frOf h β w) g gk :=
  ⟨hs, by rw [← hb, frOf_conj, loc_finE hp]⟩

theorem elt_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)) :
    (repsAt G t w).elt β (D.R.m, 0) = stair (locGrid G t w) (unifAt w) (cosExp G w) 0 :=
  (onColumn_apply (G := locGrid G t w) _ 0).trans rfl


open Classical in
theorem localization₂ : Big fun ch => LocP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp β r r₀ h hpts j hj
  obtain ⟨hr, hr₀, hh⟩ := hpts
  have L1 : p.IsLoc (frRow ch.S.B t w j hj) (r j) _ := isLoc_of_inBasis hp _ _ _ _ (hr j hj).1 (hr j hj).2
  have L0 : p.IsLoc (frRow ch.S.B t w j hj) (r₀ j) _ := isLoc_of_inBasis hp _ _ _ _ (hr₀ j hj).1 (hr₀ j hj).2
  refine ⟨?_, fun he => ?_, fun ho => ?_⟩
  · convert isLoc_mul' p (isLoc_inv' p L0) L1 using 1
    beta_reduce
    rw [Pi.mul_apply]
    by_cases h0 : j = 0
    · subst h0
      have hn : (0 : ℕ) ∉ idx D := by rw [mem_idx]; omega
      rw [if_pos rfl, if_neg hn, epsV_apply, if_neg hn, one_mul, elt_zero]
      exact (inv_inv _).symm.trans (mul_one _).symm
    · by_cases hi : j ∈ idx D
      · rw [if_neg h0, if_pos hi, inv_one, one_mul, epsV_apply, if_pos hi]
      · have hm : D.R.m ≤ j + 1 := by rw [mem_idx] at hi; omega
        rw [if_neg h0, if_neg hi, inv_one, mul_one, epsV_eq_one t w hm, elt_eq_one t w β hm, mul_one]
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    rw [hδ.2.1 he, inv_one, one_mul] at hoff
    rw [mt_mul', Matrix.map_mul, map_eq_one_of_off hp hoff, Matrix.one_mul, L0.2, Matrix.mul_assoc,
      (frRow ch.S.B t w j hj).γβ, Matrix.mul_one]
    rfl
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    refine ⟨δ, hδ, ?_⟩
    have h0 : j ≠ 0 := by rintro rfl; simp at ho
    have hr0 : (Formalism.L2.Theta.mt _ (r₀ j)).map p.π = 1 := by
      rw [L0.2]
      simp only [if_neg h0, Units.val_one, Matrix.mul_one, (frRow ch.S.B t w j hj).βγ]
    rw [mt_mul', Matrix.map_mul, hr0, Matrix.mul_one, ← mul_inv_cancel_left δ (h j), mt_mul', Matrix.map_mul,
      map_eq_one_of_off hp hoff, Matrix.mul_one]

end GlobalTheory.FlatPlaceLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

open GlobalTheory.SplitFlip (Grid Edge)

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem flCol_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flCol ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flCol ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem flRow_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flRow ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flRow ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem stepDatum_eq_datC (G : Grid k) (hs : 1 ≤ G.s) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (j : Fin (G.m - 1)) :
    stepDatum hs φ j = datC (c := G.m - 2 - j) (c' := G.m - 2 - j + 1)
      (by have := topRank_add hs (j + 1); have := j.2; show _ = G.rank (G.m, j + 1); omega)
      (by have := topRank_add hs j; have := j.2; show _ = G.rank (G.m, j); omega) (φ (.theta G.m j)) := rfl

theorem theta_sub_congr (G : Grid k) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G)
    {i i' : ℕ} (h : i = i') (p₁ : G.rank (G.m, i + 1) ≤ topRank G (i + 1)) (p₂ : G.rank (G.m, i) = topRank G i)
    (p₃ : G.rank (G.m, i' + 1) ≤ topRank G (i' + 1)) (p₄ : G.rank (G.m, i') = topRank G i') :
    φ (.theta G.m i) ((x i).submatrix (Fin.castLE p₁) (Fin.cast p₂))ᵀ =
      φ (.theta G.m i') ((x i').submatrix (Fin.castLE p₃) (Fin.cast p₄))ᵀ := by
  subst h; rfl

theorem prod_fin_even (n : ℕ) (g : ℕ → ℂ) :
    (∏ j ∈ Finset.range (2 * n), if Even j then g j else 1) = ∏ i ∈ Finset.range n, g (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, if_pos (even_two_mul n), if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one n), mul_one]

theorem locA_last (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (j : ℕ) (hj : j + 2 = G.m) :
    locA G hs ψ ν φ j (x j, x (j + 1)) =
      φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u =>
        GlobalTheory.LocFlat.flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r)))
        (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1))) := by
  obtain rfl : j = G.m - 2 := by omega
  rw [locA, dite_eq_left (by omega), stepDatum_eq_datC]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact theta_sub_congr G φ x (by omega) _ _ _ _
  · congr 1
    funext u
    exact congrFun (flCol_datC_congr ψ ν _ (by simp) rfl _ _ _ _) _

theorem locA_double (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hm : Even G.m) (j : ℕ) (he : Even j)
    (hj : j < G.m - 2) (q) :
    locA G hs ψ ν φ j q =
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩))
        (GlobalTheory.LocFlat.flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) q := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hm
  rw [locA, dite_eq_right (by omega), dite_eq_left (by omega), stepDatum_eq_datC, stepDatum_eq_datC]
  exact congrArg₂ (fun A B => GlobalTheory.LocFlat.contr ψ ν A B q)
    (flCol_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)
    (flRow_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)

end

theorem flatTensor_pureTensor_eq_prod_locA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s), 2 ≤ G.m → Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (GlobalTheory.SplitFlip.oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * ∏ n ∈ Finset.range (G.m / 2), locA G hs ψ ν φ (2 * n) (x (2 * n), x (2 * n + 1)) := by
  intro k _ _ _ _ _ _ G hs hm hme ψ ν hψ hψ1 hν φ hφ x y
  rw [GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr k G hs hm hme ψ ν hψ hψ1 hν φ hφ x y, mul_assoc]
  congr 1
  obtain ⟨n, hn⟩ : ∃ n, G.m = 2 * n + 2 := by obtain ⟨b, hb⟩ := hme; exact ⟨b - 1, by omega⟩
  have hr : G.m / 2 = n + 1 := by omega
  rw [hr, Finset.prod_range_succ, mul_comm, locA_last G hs ψ ν φ x (2 * n) (by omega)]
  congr 1
  have h2 : G.m - 2 = 2 * n := by omega
  rw [← prod_fin_even n (fun j => locA G hs ψ ν φ j (x j, x (j + 1)))]
  rw [← Fin.prod_univ_eq_prod_range (fun j => if Even j then locA G hs ψ ν φ j (x j, x (j + 1)) else 1) (2 * n)]
  rw [← h2]
  refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
  exact (locA_double G hs ψ ν φ ⟨n + 1, by omega⟩ j hj j.2 _).symm

end GlobalTheory.FlatPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.isIdemSum_eq_sum_singlePlaces : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ (eL : P → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → e = ∑ w, eL w ∧ (∀ S : Finset P, IsIdemSum (∑ w ∈ S, eL w) (S.map (Function.Embedding.subtype _))) ∧ ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := by
  first | exact @GlobalTheory.IdemSingleSum.sum_single | exact GlobalTheory.IdemSingleSum.sum_single | (intros; apply GlobalTheory.IdemSingleSum.sum_single <;> assumption)
end
