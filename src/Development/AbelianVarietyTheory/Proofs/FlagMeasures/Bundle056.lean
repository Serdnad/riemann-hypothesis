module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle051
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.NumberTheory.NumberField.ProductFormula
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

def hq {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E := ∑ i, ∑ j, x i * Hm i j * sig (y j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_add_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (a + b) y = _root_.GlobalTheory.HL.SAN.hq sig Hm a y + _root_.GlobalTheory.HL.SAN.hq sig Hm b y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_smul_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (c • a) y = c * _root_.GlobalTheory.HL.SAN.hq sig Hm a y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def eQ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun v := v + hq sig Hm v u • x - hq sig Hm v x • (u + s • x)
  map_add' a b := by
    simp only [hq_add_l]; module
  map_smul' c a := by
    simp only [hq_smul_l, RingHom.id_apply]; module

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.mem_coord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} (x : Fin N → E) :
    x ∈ Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin N → E)) ↔ ∀ j, x j ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i
      · subst h; simp [L.O.one_mem]
      · simp [Pi.single_apply, h, L.O.zero_mem]
    | zero => intro j; exact L.O.zero_mem
    | add y z _ _ hy hz => intro j; exact add_mem (hy j) (hz j)
    | smul c y _ hy =>
      intro j
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hy j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : L.O) • (Pi.single j 1 : Fin N → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem hf_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x y : Fin N → E} (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    hf L Hm x y ∈ L.O :=
  L.O.sum_mem fun i _ => L.O.sum_mem fun j _ =>
    L.O.mul_mem (L.O.mul_mem (hx i) (hI i j)) (GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem hf_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) (x y : Fin n → E) (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    _root_.GlobalTheory.HL.hf L H x y ∈ L.O := by
  unfold _root_.GlobalTheory.HL.hf
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hx i) (hI i j)) (_root_.GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem eich_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) {x u : Fin n → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) {v : Fin n → E} (hv : ∀ j, v j ∈ L.O) (j : Fin n) :
    _root_.GlobalTheory.HL.eich L H x u s v j ∈ L.O := by
  unfold _root_.GlobalTheory.HL.eich
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact sub_mem (add_mem (hv j) (mul_mem (hf_mem_O L hI v u hv hu) (hx j)))
    (mul_mem (hf_mem_O L hI v x hv hx) (add_mem (hu j) (mul_mem hs (hx j))))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.int_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (m : ℕ) (X u : Fin m → Fin N → E) (s : Fin m → E)
    (e : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, u i j ∈ L.O) →
    (∀ i, s i ∈ L.O) → (∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v) →
    ∀ x : Fin N → E, (∀ j, x j ∈ L.O) → ∀ j, (List.ofFn e).prod x j ∈ L.O := by
  intro m
  induction m with
  | zero =>
    intro X u s e _ _ _ _ x hx j
    simpa using hx j
  | succ m ih =>
    intro X u s e hX hu hs he x hx j
    rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply, he 0]
    exact eich_mem_O L hI (hX 0) (hu 0) (hs 0)
      (fun j' => ih (fun i => X i.succ) (fun i => u i.succ) (fun i => s i.succ) (fun i => e i.succ)
        (fun i => hX i.succ) (fun i => hu i.succ) (fun i => hs i.succ) (fun i => he i.succ) x hx j') j

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.ext_prod {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ} : ∀ (m : ℕ)
    (a : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (b : Fin m → (Fin N → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin N → (A.loc p).Ep)),
    (∀ i, A.Ext p (a i) (b i)) →
      A.Ext p (List.ofFn a).prod (List.ofFn b).prod := by
  intro m
  induction m with
  | zero =>
    intro a b _
    simp only [_root_.GlobalTheory.HL.Places.Ext]
    intro x
    simp
  | succ m ih =>
    intro a b h
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)
    simp only [_root_.GlobalTheory.HL.Places.Ext] at h ih' ⊢
    intro x
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, ih', h 0]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.bc_eQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (x u : Fin N → E) (s : E) (v : Fin N → E) :
    A.bc p (_root_.GlobalTheory.HL.SAN.eQ sig Hm x u s v) =
      _root_.GlobalTheory.HL.eich (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p u) ((A.loc p).ιE s) (A.bc p v) := by
  have h5 := (_root_.GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm
  have hu := h5 v u
  have hx := h5 v x
  unfold _root_.GlobalTheory.HL.eich
  rw [hu, hx]
  funext i
  simp [_root_.GlobalTheory.HL.Places.bc, _root_.GlobalTheory.HL.SAN.eQ, _root_.GlobalTheory.HL.SAN.hq]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.exists_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField F)).ne'⟩⟩

end GlobalTheory.HL.SAN
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.ResProd

theorem vE_eq_neg_log {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {E : Type} [CommRing E] [Algebra K E] [TopologicalSpace E] (L : LocE K E)
    (ι : F →+* K) (hd : DenseRange ι)
    (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
    {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap K E (ι x)) = -WithZero.log (p.valuation F x) := by
  have hιx : ι x ≠ 0 := (map_ne_zero ι).mpr hx
  obtain ⟨k, u, hku⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hιx
  rw [hku, GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ k u]

  obtain ⟨g, hg⟩ := p.valuation_exists_uniformizer F
  obtain ⟨q, hq, hqg⟩ := GlobalTheory.LocSplit.exists_irreducible p ι hd hv g hg
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hϖ hq
  have h0 : p.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set n := WithZero.log (p.valuation F x) with hn
  have hvx : p.valuation F x = WithZero.exp n := (WithZero.exp_log h0).symm

  have hone : p.valuation F (x * g ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hvx, hg, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hunit : ∀ v : (𝒪[K])ˣ, valuation K ((v : 𝒪[K]) : K) = 1 := fun v =>
    (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp v.isUnit
  have hϖ0 : valuation K (ϖ : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hvq : valuation K (ι g) = valuation K (ϖ : K) := by
    rw [← hqg, ← hw]
    push_cast
    rw [map_mul, hunit, mul_one]

  have hvz : valuation K (ι (x * g ^ n)) = 1 := by
    apply le_antisymm
    · simpa using (hv (x * g ^ n) 1).mpr (by rw [hone, map_one])
    · simpa using (hv 1 (x * g ^ n)).mpr (by rw [hone, map_one])
  simp only [map_mul, map_zpow₀, hku, hunit, mul_one, hvq] at hvz
  rw [← zpow_add₀ hϖ0] at hvz

  have hle := (GlobalTheory.UnramVal.zpow_mul_unit_mem_iff hϖ (k + n) 1).mp (by
    rw [Valuation.mem_integer_iff]
    simp only [Units.val_one, OneMemClass.coe_one, mul_one, map_zpow₀, hvz, le_refl])
  have hge := (GlobalTheory.UnramVal.zpow_mul_unit_mem_iff hϖ (-(k + n)) 1).mp (by
    rw [Valuation.mem_integer_iff]
    simp only [Units.val_one, OneMemClass.coe_one, mul_one, map_zpow₀, zpow_neg, map_inv₀, hvz, inv_one,
      le_refl])
  omega

theorem place_eq_zpow {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {x : F} (hx : x ≠ 0) :
    FinitePlace.equivHeightOneSpectrum.symm p x =
      (Ideal.absNorm p.asIdeal : ℝ) ^ WithZero.log (p.valuation F x) := by
  have h0 : p.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
    NumberField.FinitePlace.norm_embedding', WithZeroMulInt.toNNReal_neg_apply _ h0,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem prod_resQ_zpow : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → ∀ x : F, x ≠ 0 → {p | vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) ≠ 0}.Finite ∧ ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  intro F E _ _ _ _ _ sig A ϖ hϖ x hx

  have key : ∀ p, vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) =
      -WithZero.log (p.valuation F x) := fun p => by
    haveI := (A.loc p).lf
    exact vE_eq_neg_log p (A.L p) (A.loc p).ιF (A.loc p).dense
      (GlobalTheory.HL.PlacesInt.val_le_iff (A.loc p)) (hϖ p) hx
  have hterm : ∀ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p)
      (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) =
      (NumberField.FinitePlace.equivHeightOneSpectrum.symm p x)⁻¹ := fun p => by
    rw [key, GlobalTheory.HL.PlacesInt.resQ_eq_absNorm (A.loc p) (ϖ p) (hϖ p), place_eq_zpow p hx, zpow_neg]
  have hfin : (Function.mulSupport fun w : NumberField.FinitePlace F => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  constructor
  · refine (hfin.image NumberField.FinitePlace.equivHeightOneSpectrum).subset ?_
    intro p hp
    refine ⟨NumberField.FinitePlace.equivHeightOneSpectrum.symm p, ?_, by simp⟩
    simp only [Set.mem_setOf_eq, key] at hp
    rw [Function.mem_mulSupport, place_eq_zpow p hx]
    intro h1
    have hgt : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
    rw [zpow_eq_one_iff_right₀ (by positivity) hgt.ne'] at h1
    exact hp (by rw [h1, neg_zero])
  · simp_rw [hterm]
    rw [finprod_inv_distrib,
      finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm (f := fun w => w x),
      NumberField.FinitePlace.prod_eq_inv_abs_norm hx]
    push_cast
    simp

end GlobalTheory.ResProd
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.SnMass.SkewVol

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_map_of_unramified (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) :
    differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu, Ideal.top_mul]

theorem dInv_eq_inv_coe (K : Type) [Field K] [NumberField K] (j : ℕ) :
    dInv K j = ((↑(differentIdeal ℤ (𝓞 K) ^ j) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [dInv, FractionalIdeal.coeIdeal_pow, inv_pow]

theorem algebraMap_mem_inv_map_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (y : F) :
    algebraMap F E y ∈ ((↑(I.map (algebraMap (𝓞 F) (𝓞 E))) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ ↔
      y ∈ ((↑I : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  have hIE : I.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hIE),
    FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)]
  have key : ∀ a : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) =
      algebraMap F E (algebraMap (𝓞 F) F a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have h1 := h (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a))
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_map_of_mem _ ha, rfl⟩)
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [key, ← map_mul] at hc
    have hint : IsIntegral ℤ (y * algebraMap (𝓞 F) F a) := by
      rw [← isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective]
      show IsIntegral ℤ (algebraMap F E (y * algebraMap (𝓞 F) F a))
      rw [← hc]
      exact c.2
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    let T : Ideal (𝓞 E) := Submodule.comap
      ((LinearMap.mulLeft (𝓞 E) (algebraMap F E y)) ∘ₗ Algebra.linearMap (𝓞 E) E)
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) ≤ T := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
        (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩))
      show algebraMap F E y * algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) ∈
        (1 : FractionalIdeal (𝓞 E)⁰ E)
      rw [key, ← map_mul, ← hc]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨algebraMap (𝓞 F) (𝓞 E) c, key c⟩
    exact hle hb

theorem cm_sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem mem_range_of_cm_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hne := cm_sigma_ne_id h
  have hxS : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
  have hle : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) ≤ 2 := by
    rw [← Subalgebra.finrank_toSubmodule, ← h.2.2.1]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) := Module.finrank_pos
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    rcases (by omega : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 1 ∨
        Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 2) with h1 | h2
    · exact Subalgebra.finrank_eq_one_iff.1 h1
    · exfalso
      apply hne
      have htop : Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h2, h.2.2.1])
      ext z
      have hz : z ∈ Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) :=
        htop ▸ Submodule.mem_top
      exact hz
  rw [hS] at hxS
  exact Algebra.mem_bot.1 hxS

theorem imV_eq_zero_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : imV x = 0 ↔ σ x = x := by
  constructor
  · intro hx
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    let w : InfinitePlace E := InfinitePlace.mk τ
    have him : (w.embedding x).im = 0 := congrFun hx w
    apply w.embedding.injective
    rw [h.2.2.2]
    exact Complex.conj_eq_iff_im.2 him
  · intro hx
    funext w
    show (w.embedding x).im = 0
    have := h.2.2.2 w.embedding x
    rw [hx] at this
    exact Complex.conj_eq_iff_im.1 this.symm

end Fixed

theorem mem_dInv_imV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
    ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  intro F E _ _ _ _ _ σ h hu j x
  have hIne : differentIdeal ℤ (𝓞 F) ^ j ≠ ⊥ := pow_ne_zero _ differentIdeal_ne_bot
  have hE : dInv E j = ((↑((differentIdeal ℤ (𝓞 F) ^ j).map (algebraMap (𝓞 F) (𝓞 E))) :
      FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    rw [dInv_eq_inv_coe, differentIdeal_eq_map_of_unramified hu, Ideal.map_pow]
  constructor
  · rintro ⟨hx, him⟩
    obtain ⟨y, rfl⟩ := mem_range_of_cm_fixed h ((imV_eq_zero_iff h x).1 him)
    refine ⟨y, ?_, rfl⟩
    rw [dInv_eq_inv_coe]
    rw [hE] at hx
    exact (algebraMap_mem_inv_map_iff _ hIne y).1 hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (imV_eq_zero_iff h _).2 (σ.commutes y)⟩
    rw [hE]
    rw [dInv_eq_inv_coe] at hy
    exact (algebraMap_mem_inv_map_iff _ hIne y).2 hy

end GlobalTheory.SnMass.SkewVol
end
end

section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ Formalism.HermitianLatticesTheory.fDeg K ∧ (3 / 2 : ℝ) ≤ 2 * Formalism.HermitianLatticesTheory.vInv K ∧ Real.sqrt |(discr K : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  first | exact @GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex | exact GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex | (intros; apply GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FrameGram

theorem std_frame_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ r P T hP
  obtain ⟨he, _, hf, hez, _, hz, hT⟩ := hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := frame_gram_snoc hσ hJ P.e P.f P.z T hT he hez hz hf
    (F0 P) rfl (tupH P) rfl
  exact ⟨h1, h2, h3, h4, fun v => h5 _⟩

end GlobalTheory.FrameGram
end
