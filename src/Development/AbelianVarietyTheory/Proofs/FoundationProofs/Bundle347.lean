module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbeddingClosedIntegral
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne

def decRingHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω)
    (hs : s ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨s x, (apply_mem_iff_of_mem_Dec hs (x : Ω)).2 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def TwDiff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (_τ : A →+* A) : Type :=
  KaehlerDifferential (fixA A) A

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    AddCommGroup (TwDiff A τ) :=
  inferInstanceAs (AddCommGroup (KaehlerDifferential (fixA A) A))

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    Module A (TwDiff A τ) :=
  Module.compHom (KaehlerDifferential (fixA A) A) τ

theorem transp_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω),
    s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b →
    (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  intro Ω _ _ A s hs a b a' b' c d c' d' hc hd hc' hd' h
  set τ := decRingHom A s (Ine_le_Dec A hs) with hτ
  have hτc : τ a = c := Subtype.ext hc.symm
  have hτd : τ b = d := Subtype.ext hd.symm
  have hτc' : τ a' = c' := Subtype.ext hc'.symm
  have hτd' : τ b' = d' := Subtype.ext hd'.symm
  obtain ⟨T, hT⟩ := kaehler_rel_local (fixA A) A 2 ![a, -a'] ![b, b']
    (by simp [Fin.sum_univ_two, h])
  let D : A → TwDiff A τ := fun x => (dA A (τ x) : KaehlerDifferential (fixA A) A)
  have hD : IsDerOn (⊤ : Subalgebra (fixA A) A) D :=
    { add := fun x _ y _ => by
        show dA A (τ (x + y)) = dA A (τ x) + dA A (τ y)
        rw [map_add (f := _), map_add (f := _)]
      mul := fun x _ y _ => by
        show dA A (τ (x * y)) = τ x • dA A (τ y) + τ y • dA A (τ x)
        rw [map_mul, Derivation.leibniz]
      alg := fun r => by
        show dA A (τ (algebraMap (fixA A) A r)) = 0
        have e : τ (algebraMap (fixA A) A r) = algebraMap (fixA A) A r :=
          Subtype.ext (r.2 s hs)
        rw [e, Derivation.map_algebraMap] }
  have key := hT ⊤ (by simp) (by simp) (TwDiff A τ) D hD
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  change τ a • dA A (τ b) + τ (-a') • dA A (τ b') = (0 : KaehlerDifferential (fixA A) A) at key
  rw [map_neg, hτc, hτd, hτc', hτd', neg_smul, ← sub_eq_add_neg, sub_eq_zero] at key
  exact key

end GlobalTheory.RecOne
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory

theorem hasWeight_neg_of_pow_cyc_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ),
    Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m →
    (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) →
    Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  intro l _ κ hκ e m hm h
  have hcyc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  have hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l)) :=
    Units.continuous_val.comp
      ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)
  set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def
  have hf : Continuous f := by
    have : f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e := by
      funext σ
      simp only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [this]
    exact hκ.mul (hA.pow e)
  have hf1 : f 1 = 1 := by simp [hf_def]
  have hm0 : 0 < m := hm
  have hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_
    exact (Polynomial.mem_nthRoots hm0).2 hz.1
  have ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hf
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (fun hx => hx.2 hf1)
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩
  have hgI' : g ∈ Loc.Iq l := hgI
  have hpow : f g ^ m = 1 := by
    have := congrArg Units.val (h g hgI')
    simpa [hf_def, Units.val_pow_eq_pow_val] using this
  have hone : f g = 1 := by
    by_contra hne
    exact hU hg ⟨hpow, hne⟩
  have hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1 := Units.ext hone
  simp only [MonoidHom.id_apply, zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

theorem exists_dotProduct_eq_of_approx_pow {K : Type*} [NormedField K] (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (X : Type*) (m : ℕ) (M : X → Fin m → K) (z : X → K)
    (h : ∀ n : ℕ, ∃ y : Fin m → K, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ r ^ n) :
    ∃ y : Fin m → K, ∀ x, z x = M x ⬝ᵥ y := by
  classical
  let T : (X →₀ K) →ₗ[K] (Fin m → K) := Finsupp.linearCombination K M
  let φ : Module.Dual K (X →₀ K) := Finsupp.linearCombination K z
  have hker : φ ∈ (LinearMap.ker T).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro c hc
    have hc' : ∑ x ∈ c.support, c x • M x = 0 := by
      simpa [T, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    have hφ : φ c = ∑ x ∈ c.support, c x * z x := by
      simp [φ, Finsupp.linearCombination_apply, Finsupp.sum]
    have hb : ∀ n : ℕ, ‖φ c‖ ≤ (∑ x ∈ c.support, ‖c x‖) * r ^ n := by
      intro n
      obtain ⟨y, hy⟩ := h n
      have h0 : ∑ x ∈ c.support, c x * (M x ⬝ᵥ y) = 0 := by
        have := congrArg (· ⬝ᵥ y) hc'
        simpa [sum_dotProduct, smul_dotProduct] using this
      have : φ c = ∑ x ∈ c.support, c x * (z x - M x ⬝ᵥ y) := by
        simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero, hφ]
      rw [this, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hy x) (norm_nonneg _)
    have hlim : Filter.Tendsto (fun n : ℕ => (∑ x ∈ c.support, ‖c x‖) * r ^ n) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
        (∑ x ∈ c.support, ‖c x‖)
    exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hb)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), fun x => ?_⟩
  have h1 := congrArg (fun f : Module.Dual K (X →₀ K) => f (Finsupp.single x 1)) hg
  simp only [LinearMap.dualMap_apply, T, φ, Finsupp.linearCombination_single, one_smul,
    smul_eq_mul, one_mul] at h1
  rw [← h1, LinearMap.pi_apply_eq_sum_univ g (M x)]
  simp [dotProduct]

theorem exists_dotProduct_eq_of_approx_prime_pow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  intro l _ X m M z h
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine exists_dotProduct_eq_of_approx_pow _ (norm_nonneg _) hl X m M z fun n => ?_
  simpa only [norm_pow] using h n

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharAnn

theorem approx_candidate {K : Type} [NormedField K] {Γ : Type} (k a : Γ → K) {s₀ : Γ}
    (hk : k s₀ ≠ 1) {X : K} {ε : ℝ}
    (h0 : ‖a s₀ - (k s₀ * X - X)‖ ≤ ε) (s : Γ) (hs : ‖a s - (k s * X - X)‖ ≤ ε) :
    ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤
      (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by
  have hk' : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hk'
  set X₀ := a s₀ / (k s₀ - 1)
  have hX : X₀ - X = (a s₀ - (k s₀ * X - X)) / (k s₀ - 1) := by
    simp only [X₀]; field_simp
  have hXn : ‖X₀ - X‖ ≤ ε / ‖k s₀ - 1‖ := by
    rw [hX, norm_div]; exact div_le_div_of_nonneg_right h0 hpos.le
  have hid : a s - (k s * X₀ - X₀) = (a s - (k s * X - X)) - (k s - 1) * (X₀ - X) := by ring
  rw [hid]
  calc ‖(a s - (k s * X - X)) - (k s - 1) * (X₀ - X)‖
      ≤ ‖a s - (k s * X - X)‖ + ‖(k s - 1) * (X₀ - X)‖ := norm_sub_le _ _
    _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
        rw [norm_mul]; gcongr
    _ = (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by field_simp

theorem exists_depth_of_not_coboundary : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} (H : Set Γ) (k a : Γ → Qbar l), (∃ s ∈ H, k s ≠ 1) → (¬ ∃ X : Qbar l, ∀ s ∈ H, a s = k s * X - X) → ∃ r : ℕ, ∀ (n : ℕ) (x y : Qbar l), ‖x‖ ≤ 1 → (∀ s ∈ H, ‖x * a s - (k s * y - y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ (n - r)‖ := by
  intro l _ Γ H k a ⟨s₀, hs₀, hk⟩ hna
  by_contra hcon
  push_neg at hcon
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := GlobalTheory.CoefEmbed.norm_prime_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have happrox : ∀ r : ℕ, ∃ X : Qbar l, ∀ t ∈ H, ‖a t - (k t * X - X)‖ ≤ q ^ r := by
    intro r
    obtain ⟨n, x, y, hx1, hb, hx⟩ := hcon r
    rw [norm_pow] at hx hb
    by_cases hnr : n < r
    · rw [Nat.sub_eq_zero_of_le hnr.le, pow_zero] at hx
      exact absurd hx (not_lt.mpr hx1)
    push_neg at hnr
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (pow_nonneg hq0 _) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    refine ⟨y / x, fun t ht => ?_⟩
    have hid : x * a t - (k t * y - y) = x * (a t - (k t * (y / x) - y / x)) := by
      field_simp
    have h1 := hb t ht
    rw [hid, norm_mul] at h1
    have hsplit : q ^ n = q ^ (n - r) * q ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hnr]
    rw [hsplit] at h1
    by_contra hlt
    push_neg at hlt
    have : q ^ (n - r) * q ^ r < ‖x‖ * ‖a t - (k t * (y / x) - y / x)‖ :=
      mul_lt_mul'' hx hlt (pow_nonneg hq0 _) (pow_nonneg hq0 _)
    linarith
  apply hna
  refine ⟨a s₀ / (k s₀ - 1), fun s hs => ?_⟩
  set C : ℝ := 1 + ‖k s - 1‖ / ‖k s₀ - 1‖
  have hbound : ∀ r : ℕ, ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤ C * q ^ r := by
    intro r
    obtain ⟨X, hX⟩ := happrox r
    exact approx_candidate k a hk (hX s₀ hs₀) s (hX s hs)
  have hlim : Filter.Tendsto (fun r : ℕ => C * q ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hle := ge_of_tendsto' hlim hbound
  have h0 : ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

end GlobalTheory.LocCharAnn
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm

noncomputable section

open Polynomial

namespace GlobalTheory.TwAtt

theorem normV_eq (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem mem_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1
  · rintro ⟨c, rfl⟩
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (normV v).Prime := by
  have h1 : 1 < normV v := by
    rw [normV_eq]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem eq_of_normV {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : ((normV v : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := by
    intro x hx
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x := ⟨Rat.ringOfIntegersEquiv x, by
      apply Rat.ringOfIntegersEquiv.injective; simp⟩
    have key : ∀ I : Ideal (𝓞 ℚ), (m : 𝓞 ℚ) ∈ I ↔ ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ I := fun I => by
      rcases Int.natAbs_eq m with e | e
      · conv_lhs => rw [e]
        rw [Int.cast_natCast]
      · conv_lhs => rw [e]
        rw [Int.cast_neg, Int.cast_natCast, neg_mem_iff]
    rw [key, mem_iff] at hx ⊢
    exact ((mem_iff _ _).1 h).trans hx
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm

theorem normV_injective : Function.Injective (normV : HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v v' h
  refine (eq_of_normV (v := v') (v' := v) ?_)
  rw [← h]
  exact (mem_iff v _).2 dvd_rfl

end GlobalTheory.TwAtt

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lam_small_of_deep_congruence : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  intro l _ Γ _ _ _ r lam hr hlam hker ε hε
  have hl : ‖((l:ℕ) : Qbar l)‖ = (l:ℝ)⁻¹ := by
    have : ((l:ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    simp [Padic.norm_p]
  have hl1 : ‖((l:ℕ) : Qbar l)‖ < 1 := by
    rw [hl]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  by_contra hcon
  push_neg at hcon
  set F : ℕ → Set Γ := fun N => {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} ∩ {g | ε ≤ ‖(lam g).toAdd‖} with hF
  have hcm : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := (Units.continuous_val.comp hr).sub continuous_const
  have hclosed : ∀ N, IsClosed (F N) := by
    intro N
    refine IsClosed.inter ?_ ?_
    · have : {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} = ⋂ i, ⋂ j, {g | ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_le (continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp hcm))) continuous_const
    · exact isClosed_le continuous_const (continuous_norm.comp (continuous_toAdd.comp hlam))
  have hmono : ∀ N, F (N+1) ⊆ F N := by
    intro N g hg
    refine ⟨fun i j => (hg.1 i j).trans ?_, hg.2⟩
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ N)
  have hne : ∀ N, (F N).Nonempty := by
    intro N
    obtain ⟨g, hg1, hg2⟩ := hcon N
    exact ⟨g, hg1, hg2.le⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hg
  have hzero : ∀ i j, ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j = 0 := by
    intro i j
    by_contra hx
    have hpos : 0 < ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ := norm_pos_iff.mpr hx
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hl1
    have := (hg N).1 i j
    rw [norm_pow] at this
    linarith
  have hrg : r g = 1 := by
    apply Units.ext
    have : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1 = 0 := by
      ext i j; exact hzero i j
    simpa [sub_eq_zero] using this
  have hlg : lam g = 1 := hker (MonoidHom.mem_ker.mpr hrg)
  have h2 : ε ≤ ‖(lam g).toAdd‖ := (hg 0).2
  rw [hlg] at h2
  simp at h2
  linarith
end
