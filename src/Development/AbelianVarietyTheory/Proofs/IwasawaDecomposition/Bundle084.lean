module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle074
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.KummerIndep

variable {l : ℕ} [Fact l.Prime]

theorem eventually_integral (x : ℚ_[l]) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ y : ℤ_[l], (y : ℚ_[l]) = (l : ℚ_[l]) ^ N * x := by
  have h : Filter.Tendsto (fun N : ℕ => ‖(l : ℚ_[l]) ^ N * x‖) Filter.atTop (nhds 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (Padic.norm_p_lt_one (p := l))).mul_const x).norm
    simpa using this
  filter_upwards [h.eventually (ge_mem_nhds zero_lt_one)] with N hN
  exact ⟨⟨_, hN⟩, rfl⟩

theorem exists_root (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℤ_[l])
    (h : ∀ g : GQ l, (α : ℚ_[l]) * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1))
    (k A B : ℕ) (hA : PadicInt.toZModPow k α = A) (hB : PadicInt.toZModPow k β = B) :
    ∃ q : ℚ_[l], q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsGalois ℚ_[l] (Om l) := {}
  obtain ⟨S, hS⟩ : ∃ S : ℕ, PadicInt.toZModPow k (-r) = S := ⟨_, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l])
    (lRoot l k ^ A * μ k ^ B * P.ζQ k ^ S)).2 fun g => by
      have hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
        obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
        have e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a := by ring
        rw [e]
        refine (Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)
        exact_mod_cast Padic.norm_int_le_one (p := l) (a : ℤ)
      let x : ℤ_[l] := ⟨P.χQ g, hx⟩
      obtain ⟨a, ha, hg⟩ := P.χQ_cyc g k (P.ζQ k) (isPrimitiveRoot_zeta P k).pow_eq_one
      have hxa : PadicInt.toZModPow k x = a := by
        rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow k), ← map_sub, ← RingHom.mem_ker,
          PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
        exact ha
      have h1 : α * kummer P g + β * d g + (-r) * x = -r := by
        apply Subtype.ext
        have e : (x : ℚ_[l]) = P.χQ g := rfl
        have := h g
        push_cast
        rw [e]
        linear_combination this
      have h2 := congrArg (PadicInt.toZModPow k) h1
      rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_mul, hA, hB, hS, hxa] at h2
      have h3 : P.ζQ k ^ ((PadicInt.toZModPow k (kummer P g)).val * A +
          (PadicInt.toZModPow k (d g)).val * B + a * S) = P.ζQ k ^ S := by
        rw [zeta_pow_eq_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination h2
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hg, isKummer_kummer P g k, hd g k, ← h3]
      simp only [mul_pow, ← pow_mul, pow_add]
      ring
  refine ⟨x, (algebraMap ℚ_[l] (Om l)).injective ?_⟩
  rw [map_pow, hx, mul_pow, mul_pow, pow_right_comm (lRoot l k), pow_right_comm (μ k),
    pow_right_comm (P.ζQ k), lRoot_pow, hμ, (isPrimitiveRoot_zeta P k).pow_eq_one]
  simp

theorem norm_succ : ‖((l + 1 : ℕ) : ℚ_[l])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  simp

theorem dvd_of_root {k A B : ℕ} {q : ℚ_[l]}
    (h : q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B) : l ^ k ∣ A := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hl1 : ((l + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hv : ((l + 1 : ℕ) : ℚ_[l]).valuation = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd]
    · simp
    · rw [Nat.dvd_add_right dvd_rfl]
      exact (Fact.out : l.Prime).not_dvd_one
  have h2 := congrArg Padic.valuation h
  rw [Padic.valuation_mul (pow_ne_zero _ hl) (pow_ne_zero _ hl1), Padic.valuation_pow,
    Padic.valuation_pow, Padic.valuation_pow, Padic.valuation_p, hv, mul_one, mul_zero,
    add_zero] at h2
  exact Int.natCast_dvd_natCast.mp ⟨_, h2.symm⟩

theorem not_forall_root {B : ℕ} (hB : B ≠ 0)
    (h : ∀ k, ∃ q : ℚ_[l], q ^ (l ^ k) = ((l + 1 : ℕ) : ℚ_[l]) ^ B) : False := by
  have hp : l.Prime := Fact.out
  have key : ((((l + 1) ^ B) ^ (l - 1) : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    cases n with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    | succ k =>
      obtain ⟨q, hq⟩ := h k
      have hn : ‖q‖ ≤ 1 := by
        have := congrArg norm hq
        rw [norm_pow, norm_pow, norm_succ, one_pow] at this
        exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).mp this.le
      let y : ℤ_[l] := ⟨q, hn⟩
      have hy : y ^ (l ^ k) = (((l + 1) ^ B : ℕ) : ℤ_[l]) := by
        apply Subtype.ext
        have e : (y : ℚ_[l]) = q := rfl
        push_cast at hq ⊢
        rw [e, hq]
      have hu : IsUnit y := by
        rw [← isUnit_pow_iff (pow_ne_zero k hp.ne_zero), hy, PadicInt.isUnit_iff]
        have := norm_succ (l := l)
        rw [Nat.cast_pow, norm_pow]
        have e : ‖((l + 1 : ℕ) : ℤ_[l])‖ = 1 := by
          rw [PadicInt.norm_def, PadicInt.coe_natCast, this]
        rw [e, one_pow]
      obtain ⟨u, hu⟩ := hu.map (PadicInt.toZModPow (k + 1))
      have h1 := congrArg Units.val (ZMod.pow_totient u)
      rw [Nat.totient_prime_pow_succ hp, Units.val_pow_eq_pow_val, hu, pow_mul, ← map_pow, hy,
        ← map_pow] at h1
      rw [Nat.cast_pow, h1]
      simp
  have h2 : ((l + 1) ^ B) ^ (l - 1) = 1 := Nat.cast_injective key
  have := hp.two_le
  rw [← pow_mul, Nat.pow_eq_one] at h2
  rcases h2 with h2 | h2
  · omega
  · rcases Nat.mul_eq_zero.mp h2 with h3 | h3 <;> omega

theorem kummer_indep (l : ℕ) [Fact l.Prime] (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℚ_[l])
    (h : ∀ g : GQ l, α * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1)) : α = 0 ∧ β = 0 := by
  have hp : l.Prime := Fact.out
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hα : α = 0 := by
    obtain ⟨N, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := ((eventually_integral α).and
      ((eventually_integral β).and (eventually_integral r))).exists
    have h0 : a = 0 := by
      refine PadicInt.ext_of_toZModPow.mp fun k => ?_
      have : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
      obtain ⟨q, hq⟩ := exists_root P μ d hμ hd a b c
        (fun g => by rw [ha, hb, hc]; linear_combination (l : ℚ_[l]) ^ N * h g) k _ _
        (ZMod.natCast_zmod_val _).symm (ZMod.natCast_zmod_val _).symm
      rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow k a), map_zero, ZMod.natCast_eq_zero_iff]
      exact dvd_of_root hq
    rw [h0] at ha
    exact (mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hl)
  refine ⟨hα, by_contra fun hβ => ?_⟩
  obtain ⟨N, c, hc⟩ := (eventually_integral (r / β)).exists
  refine not_forall_root (l := l) (B := l ^ N) (pow_ne_zero _ hp.ne_zero) fun k => ?_
  have := exists_root P μ d hμ hd 0 ((l ^ N : ℕ) : ℤ_[l]) c (fun g => by
    have h1 := h g
    rw [hα] at h1
    rw [hc]
    push_cast
    field_simp
    linear_combination (l : ℚ_[l]) ^ N * h1) k 0 (l ^ N) (by simp) (map_natCast _ _)
  simpa only [pow_zero, one_mul] using this

end GlobalTheory.Pst.KummerIndep
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.vectorTupleProductMeasure_two_sided_action : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  first | exact @GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | exact GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | (intros; apply GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.haarModulus_product_formula_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  first | exact @GlobalTheory.GaugeProdFormula.prod_modu_eq_one | exact GlobalTheory.GaugeProdFormula.prod_modu_eq_one | (intros; apply GlobalTheory.GaugeProdFormula.prod_modu_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.haarModulus_tensor_eq_modulus_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  first | exact @GlobalTheory.GaugeEx.modu_eq_modu_norm | exact GlobalTheory.GaugeEx.modu_eq_modu_norm | (intros; apply GlobalTheory.GaugeEx.modu_eq_modu_norm <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions : ∀ (F : Type) [Field F] [NumberField F], Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  first | exact @GlobalTheory.GaugeEx.nice_ainf_fv | exact GlobalTheory.GaugeEx.nice_ainf_fv | (intros; apply GlobalTheory.GaugeEx.nice_ainf_fv <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

theorem tsfin_compact_lift {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X] (x : X)
    (hc : IsClosed (MulAction.orbit G x)) {K : Set X} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ y ∈ K, (∃ g : G, g • x = y) → ∃ g ∈ C, g • x = y := by
  haveI : LocallyCompactSpace (MulAction.orbit G x) := hc.locallyCompactSpace
  haveI : ContinuousSMul G (MulAction.orbit G x) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  let x₀ : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
  have ho : IsOpenMap fun g : G => g • x₀ := isOpenMap_smul_of_sigmaCompact x₀
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit G x)) :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let ex := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := hK'.elim_directed_cover (fun n : ℕ => (fun g : G => g • x₀) '' interior (ex n))
    (fun n => ho _ isOpen_interior)
    (by
      rintro ⟨y, g, rfl⟩ _
      obtain ⟨n, hn⟩ := ex.exists_mem g
      exact Set.mem_iUnion.2 ⟨n + 1, g, ex.subset_interior_succ n hn, rfl⟩)
    (Monotone.directed_le fun a b hab => Set.image_mono (interior_mono (ex.subset hab)))
  refine ⟨ex n, ex.isCompact n, fun y hy hg => ?_⟩
  obtain ⟨g, hg1, hg2⟩ := hn (a := ⟨y, hg⟩) hy
  exact ⟨g, interior_subset hg1, congrArg Subtype.val hg2⟩

theorem tsfin_hform_mulVec {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin n) (Fin n) A)
    (hg : Formalism.UG.cT σ g * J * g = J) (x : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec x) = Formalism.UG.hform σ J x x := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A),
      Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ J.mulVec y := by
    intro J x y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : σ ∘ g.mulVec x = (g.map σ).mulVec (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  rw [key, key, h2]
  conv_rhs => rw [← hg]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec (M := Formalism.UG.cT σ g), Matrix.dotProduct_mulVec (σ ∘ x),
    Formalism.UG.cT, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tsfin_q_smul (g : HA R σ J) (y : Fin 1 → Fin M → R ⊗[F] E) :
    qR R σ J ((g • y) 0) = qR R σ J (y 0) := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  unfold qR hR
  rw [← tsfin_hform_mulVec _ _ _ hg (y 0)]
  rfl

theorem tsfin_q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin 1 → Fin M → E) (a : F)
    (hx : hE σ J (x 0) (x 0) = algebraMap F E a) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R a := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have h : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      (1 : R) ⊗ₜ[F] algebraMap F E a := by
    rw [← hx]
    simp [hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, TensorProduct.tmul_sum]
  rw [qR, h, qloc_trace_tmul, Algebra.trace_algebraMap, h2, one_mul, ← map_mul]
  congr 1
  simp

theorem tsfin_q_cont [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun y : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (y 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  unfold qR hR Formalism.UG.hform
  fun_prop

end

theorem twoStep_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR M J x a B J' m m' N hS hO hm hm' _ hT
  classical
  obtain ⟨hJ, ha, hx, -, hJ', hJ'nd⟩ := hS
  have hq := tsfin_q_rat R σ J hcm.2.2.1 x a hx
  have hu : IsUnit (algebraMap F R a) := (IsUnit.mk0 a ha).map _
  have hc : IsClosed (MulAction.orbit (HA R σ J) (ratTup (F := F) R x)) := by
    have : MulAction.orbit (HA R σ J) (ratTup (F := F) R x) =
        {y | qR R σ J (y 0) = algebraMap F R a} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact (tsfin_q_smul R σ J g _).trans hq
      · intro hy
        exact GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hcm R hR (M + 1) J hJ _ _ y hu hq hy
    rw [this]
    exact isClosed_eq (tsfin_q_cont R σ J) continuous_const
  refine ⟨fun K hK => ?_⟩
  let K₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) := (fun X _ => X 0) '' K
  have hK₁ : IsCompact K₁ := hK.image (by fun_prop)
  obtain ⟨C, hC, hCK⟩ := tsfin_compact_lift _ hc hK₁
  let L : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)
  have hL : L * B = 1 := by
    rw [Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hJ'nd.2)
  have hL' : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let K' : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    (fun p : HA R σ J × (Fin 2 → Fin (M + 1) → R ⊗[F] E) => fun _ =>
      (L.map (inclR (F := F) R)).mulVec ((p.1⁻¹ • p.2) 1)) '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (continuous_pi fun _ =>
    continuous_const.matrix_mulVec ((continuous_apply 1).comp (continuous_fst.inv.smul continuous_snd)))
  let s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J := fun y =>
    if h : ∃ g ∈ C, g • ratTup (F := F) R x = y then h.choose
    else if h' : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h'.choose else 1
  have hs : IsSec R σ J x s := by
    intro y hy
    by_cases h : ∃ g ∈ C, g • ratTup (F := F) R x = y
    · simp only [s, dif_pos h]
      exact h.choose_spec.2
    · simp only [s, dif_neg h, dif_pos hy]
      exact hy.choose_spec
  have hsC : ∀ y ∈ K₁, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y ∈ C := by
    intro y hy hg
    have h := hCK y hy hg
    simp only [s, dif_pos h]
    exact h.choose_spec.1
  have h1 := hT (K.indicator 1) (measurable_one.indicator hK.measurableSet) s hs
  rw [lintegral_indicator_one hK.measurableSet] at h1
  rw [h1]
  have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := hO
  calc _ ≤ ∫⁻ y, K₁.indicator (fun _ => m' K') y ∂m := by
        refine lintegral_mono_ae (hae.mono fun y hy => ?_)
        by_cases hyK : y ∈ K₁
        · rw [Set.indicator_of_mem hyK, ← lintegral_indicator_one hK'.measurableSet]
          refine lintegral_mono fun y' => ?_
          by_cases hp : pairOf R σ J B y (s y) y' ∈ K
          · have : y' ∈ K' := by
              refine ⟨(s y, pairOf R σ J B y (s y) y'), ⟨hsC y hyK hy, hp⟩, ?_⟩
              funext i
              have e : ((s y)⁻¹ • pairOf R σ J B y (s y) y') 1 =
                  ((s y)⁻¹ • s y • fun _ : Fin 1 => (B.map (inclR (F := F) R)).mulVec (y' 0)) 0 := rfl
              simp only
              rw [e, inv_smul_smul, Matrix.mulVec_mulVec, hL', Matrix.one_mulVec,
                Subsingleton.elim i 0]
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem this]
          · simp [Set.indicator_of_notMem hp]
        · have : ∀ y', pairOf R σ J B y (s y) y' ∉ K := fun y' hp =>
            hyK ⟨_, hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩
          simp [Set.indicator_of_notMem (this _)]
    _ < ⊤ := by
        rw [lintegral_indicator_const hK₁.measurableSet]
        exact ENNReal.mul_lt_top hK'.measure_lt_top hK₁.measure_lt_top

end GlobalTheory.GaugeEx
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  first | exact @GlobalTheory.GaugeEx.nice_tensor | exact GlobalTheory.GaugeEx.nice_tensor | (intros; apply GlobalTheory.GaugeEx.nice_tensor <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (Γ : Type) [CommGroup Γ] (c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) → Matrix (Fin (M + 1)) (Fin M) E → Γ), (∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E), 2 ≤ M → StepData σ J x a B J' → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → c M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E)) x₂ B₂ = c M J x B) → (∀ (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → c (M + 1) J x₁ B₁ * c M J₁ y₁ C₁ = c (M + 1) J x₂ B₂ * c M J₂ y₂ C₂) → ∃ α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → Γ, (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J → α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) = α M J) ∧ ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x a B J' → α (M + 1) J = c M J x B * α M J' := by
  first | exact @GlobalTheory.GaugeAlg.exists_coboundary | exact GlobalTheory.GaugeAlg.exists_coboundary | (intros; apply GlobalTheory.GaugeAlg.exists_coboundary <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.integralPointsFinitePlaceTensor_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (intV b v) ∧ IsOpen (intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : Fv F v ⊗[F] E) ∈ intV b v ∧ (∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) ∧ ∀ y ∈ intV b v, sigR (Fv F v) σ y ∈ intV b v) ∧ (∀ z : AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, prV v z ∈ intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, intV b v = intV b' v := by
  first | exact @GlobalTheory.GaugeEx.IntBasis.main | exact GlobalTheory.GaugeEx.IntBasis.main | (intros; apply GlobalTheory.GaugeEx.IntBasis.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ainf_isDomain_and_injective : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧
    Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  intro l _
  have : IsDomain (Per.Fl l) := inferInstance
  have h : IsDomain (Per.Ainf l) := inferInstance
  have hp : (l : Per.Ainf l) ≠ 0 := WittVector.p_nonzero l _
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hp
  exact ⟨h, IsLocalization.isDomain_of_le_nonZeroDivisors (Per.AinfP l) hle, IsLocalization.injective _ hle⟩

end GlobalTheory.MemLoc
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

theorem _root_.GlobalTheory.T.omegaDensity_upq_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal), OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧ ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  first | exact @GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | exact GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | (intros; apply GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul <;> assumption)
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (χ : G → K), IsAbsIrrChar χ → ∀ g : G, χ g ∈ Subring.closure ({z} : Set K) := by
  first | exact @GlobalTheory.absIrrChar_mem_closure_primitiveRoot | exact GlobalTheory.absIrrChar_mem_closure_primitiveRoot | (intros; apply GlobalTheory.absIrrChar_mem_closure_primitiveRoot <;> assumption)
end
