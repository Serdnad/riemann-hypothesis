module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def coPtSb (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d a b : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) b s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a (d * b) s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) *
        GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) (d * b) s

theorem coPtSb_one (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) :
    coPtSb N p m k ψ c d x 1 s = GlobalTheory.KummerEisensteinGalois.coPtS N p m k ψ c d x s := by
  simp [coPtSb, GlobalTheory.KummerEisensteinGalois.coPtS]

def chiAvg (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s


omit [CharZero K] in
theorem ffMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' : ℤ} (h : a ≡ a' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a = GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ a [ZMOD N] ↔ z ≡ a' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.ffMu, h']


omit [CharZero K] in
theorem eeMu_congr (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) {b b' : ℤ} (h : b ≡ b' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b = GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ b [ZMOD N] ↔ z ≡ b' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.eeMu, h']


omit [CharZero K] in
theorem coPtMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b = GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a' b' := by
  simp only [GlobalTheory.KummerEisensteinGalois.coPtMu, ffMu_congr N p m k ψ ha, eeMu_congr N p m ψ hb]


omit [CharZero K] in
theorem coPtSb_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : coPtSb N p m k ψ c d a b = coPtSb N p m k ψ c d a' b' := by
  funext s
  simp only [coPtSb, coPtMu_congr N p m k ψ ha hb, coPtMu_congr N p m k ψ (ha.mul_left c) hb,
    coPtMu_congr N p m k ψ ha (hb.mul_left d), coPtMu_congr N p m k ψ (ha.mul_left c) (hb.mul_left d)]






end GlobalTheory.LambdaValuationPowers
end
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ.SiegelModel

open GlobalTheory.Sieg GlobalTheory.Sieg.Model

theorem isOpen_Hs : IsOpen Hs :=
  isOpen_lt continuous_const Complex.continuous_im

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hloc : nhdsWithin Complex.I (Hs \ {Complex.I}) = nhdsWithin Complex.I {Complex.I}ᶜ := by
    rw [Set.sdiff_eq]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI))
  have hne : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [hloc]
    infer_instance
  refine hne.mono ?_
  unfold Filter.codiscreteWithin
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => h z hz)

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  unfold sgC
  rw [UpperHalfPlane.ofComplex_apply]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε)

theorem an_injective : Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {c : ℕ} {x : Fin 2 → ℚ} {f : T.K} (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) :
    siegel T c x = f := by
  have hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  unfold siegel
  rw [dite_eq_left hex]
  exact an_injective T (hex.choose_spec.trans hf.symm)

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem an_siegel {c : ℕ} {x : Fin 2 → ℚ} (M : ℕ) (hM : 0 < M) (hd : DifferentiableOn ℂ (sgC c x) Hs)
    (hmod : ∀ (γ : SL(2, ℤ)) (τ : ℍ), sg c x (γ • τ) = sg c (act x γ) τ)
    (hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ)
    (hexp : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c (act x γ) τ)) :
    T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by

  have hγz : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : z ∈ Hs), sgC c x (mob (ofSL γ) z) = sg c (act x γ) ⟨z, hz⟩ := by
    intro γ z hz
    rw [mob_ofSL γ ⟨z, hz⟩, sgC_coe, hmod]
  have hlev' : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, sgC c x (mob (ofSL γ) z) = sgC c x z := by
    intro γ hγ z hz
    rw [hγz γ z hz, hlev γ hγ, ← sgC_coe]
  have hexp' : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M))
        (sgC c x (mob (ofSL γ) z)) := by
    intro γ
    obtain ⟨a, n0, ha, hs⟩ := hexp γ
    refine ⟨a, n0, ha, fun z hz => ?_⟩
    rw [hγz γ z hz]
    exact hs ⟨z, hz⟩
  obtain ⟨f, hf⟩ := T.mem_q (sgC c x) M hM hd hlev' hexp'
  rw [siegel_eq T hf]
  exact hf

end GlobalTheory.KZ.SiegelModel
end
end

section

noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

open GlobalTheory.KZ

section Hahn

variable {Ω : Type} [Field Ω]

theorem hahn_pow_order_leadingCoeff (s : HahnSeries ℚ Ω) (hs : s ≠ 0) (n : ℕ) :
    (s ^ n).order = n • s.order ∧ (s ^ n).leadingCoeff = s.leadingCoeff ^ n := by
  refine ⟨HahnSeries.order_pow s n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

private theorem hahnSeries_algebraMap_mul_coeff (c : Ω) (x : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c * x).coeff r = c * x.coeff r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem hahn_transcendental {s : HahnSeries ℚ Ω} (hs : s ≠ 0) (ho : s.order < 0) : Transcendental Ω s := by
  rintro ⟨P, hP, hPs⟩
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
  have hls : s.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.2 hs
  have key : (Polynomial.aeval s P).coeff (P.natDegree • s.order) =
      P.coeff P.natDegree * s.leadingCoeff ^ P.natDegree := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
    · rw [zero_add]
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [← (hahn_pow_order_leadingCoeff s hs P.natDegree).1,
        ← HahnSeries.leadingCoeff_eq, (hahn_pow_order_leadingCoeff s hs P.natDegree).2]
    · intro k hk
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahn_pow_order_leadingCoeff s hs k).1, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_lt_mul_of_neg_right (by exact_mod_cast Finset.mem_range.1 hk) ho
  rw [hPs] at key
  exact mul_ne_zero hlead (pow_ne_zero _ hls) (by simpa using key.symm)

end Hahn

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem mem_lev_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (f : X.K) :
    f ∈ lev X Γ' ↔ ∀ γ ∈ Γ', X.sl (ofSL γ) f = f := by
  unfold lev
  simp only [Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (c : Ω) : algebraMap Ω X.K c ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => (X.sl (ofSL γ)).commutes c

theorem jK_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : X.jK ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => X.j_inv γ

theorem mdl_le_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : mdl X Γ' S ≤ lev X Γ' := by
  unfold mdl
  exact inf_le_left

theorem jK_transcendental (X : Tower Ω ε) : Transcendental Ω X.jK := by
  have h1 : (X.exp X.jK).coeff (-1) ≠ 0 := by rw [X.j_exp.1]; exact one_ne_zero
  have hne : X.exp X.jK ≠ 0 := fun h => h1 (by rw [h]; rfl)
  have hord : (X.exp X.jK).order < 0 :=
    lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h1) (by norm_num)
  exact fun h => hahn_transcendental hne hord (h.algHom X.exp)

def levConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Ω →+* lev X Γ' :=
  (algebraMap Ω X.K).codRestrict (lev X Γ') (algebraMap_mem_lev X Γ')

def jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Polynomial Ω →+* lev X Γ' :=
  Polynomial.eval₂RingHom (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩

theorem coe_jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    ((jPoly X Γ' P : lev X Γ') : X.K) = Polynomial.aeval X.jK P := by
  change (lev X Γ').subtype (Polynomial.eval₂ (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩ P) = _
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def]
  rfl

theorem jPoly_injective (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Function.Injective (jPoly X Γ') := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
  have h : Polynomial.aeval X.jK P = 0 := by
    rw [← coe_jPoly, hP]; rfl
  by_contra hne
  exact jK_transcendental X ⟨P, hne, h⟩

def jRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : RatFunc Ω →+* lev X Γ' :=
  RatFunc.liftRingHom (jPoly X Γ') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (jPoly_injective X Γ'))

theorem jRat_algebraMap (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    jRat X Γ' (algebraMap (Polynomial Ω) (RatFunc Ω) P) = jPoly X Γ' P := RatFunc.liftRingHom_algebraMap _ _ P

theorem exp_injective (X : Tower Ω ε) : Function.Injective X.exp := (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem exp_algebraMap_coeff (X : Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C]
  change (HahnSeries.single (0 : ℚ) c).coeff r = _
  split_ifs with h
  · rw [h]
    exact HahnSeries.coeff_single_same _ _
  · exact HahnSeries.coeff_single_of_ne h

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_injective X
  ext r
  rw [X.gal_exp, exp_algebraMap_coeff, exp_algebraMap_coeff]
  split_ifs <;> simp

theorem gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_injective X
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

theorem mem_mdl_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (f : X.K) :
    f ∈ mdl X Γ' S ↔ f ∈ lev X Γ' ∧ ∀ s ∈ S, X.gal s f = f := by
  unfold mdl
  simp only [Subfield.mem_inf, Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (c : Ω)
    (hc : ∀ s ∈ S, s c = c) : algebraMap Ω X.K c ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨algebraMap_mem_lev X Γ' c, fun s hs => by rw [gal_algebraMap, hc s hs]⟩

theorem jK_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : X.jK ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨jK_mem_lev X Γ', fun s _ => gal_jK X s⟩

theorem coe_jRat_X (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : ((jRat X Γ' RatFunc.X : lev X Γ') : X.K) = X.jK := by
  rw [← RatFunc.algebraMap_X, jRat_algebraMap, coe_jPoly, Polynomial.aeval_X]

def algConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra Ω (lev X Γ') := (levConst X Γ').toAlgebra

def algPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (Polynomial Ω) (lev X Γ') := (jPoly X Γ').toAlgebra

def algRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (RatFunc Ω) (lev X Γ') := (jRat X Γ').toAlgebra

def algMdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Algebra (mdl X Γ' S) (lev X Γ') :=
  (Subfield.inclusion (mdl_le_lev X Γ' S)).toAlgebra

section Instances

attribute [local instance] algConst algPoly algRat algMdl

theorem isScalarTower_poly_rat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    IsScalarTower (Polynomial Ω) (RatFunc Ω) (lev X Γ') := IsScalarTower.of_algebraMap_eq fun P => (jRat_algebraMap X Γ' P).symm

theorem isScalarTower_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    IsScalarTower (mdl X Γ' S) (lev X Γ') X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl

end Instances

end GlobalTheory.K4
end
end

section

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ

section Global

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def CgA (A : ValuationSubring Ω) (l n : ℕ) (x y : Ω) : Prop := ∃ z ∈ A, x - y = (l : Ω) ^ n * z

def theta (s : ℚ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := algebraMap ℚ Ω (s * r) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def Prim (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ r, φ.coeff r ≠ 0 ∧ (φ.coeff r)⁻¹ ∈ A

def IsDl (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ (a b : X.K) (κ : Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
    ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r)

def Inv (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (f : X.K) : Prop := ∀ γ ∈ H, X.sl (ofSL γ) f = f

def IsThB (X : Tower Ω ε) (A : ValuationSubring Ω) (N l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) : Prop :=
  ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧
    AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧
    (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n)) ∧
    IsDl X A l n 1 f φ

def nrmT (X : Tower Ω ε) (M : ℕ) (f : X.K) : X.K := ∏ b ∈ Finset.range M, X.sl (ofSL (ModularGroup.T ^ b)) f

def sgN (X : Tower Ω ε) (c N M : ℕ) (a : ℤ × ℤ) : X.K :=
  X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])

def coefQ (M : ℕ) (f : ℕ → Ω) (r : ℚ) : Ω := if 0 ≤ r ∧ (r * M).den = 1 then f (r * M).num.toNat else 0

def IsLamG (ε : Ω →+* ℂ) (l n m : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (t : ZMod (l ^ n)) : Prop :=
  (s ^ (l ^ (n - m))) (eOm ε (1 / (l : ℚ) ^ (2 * n))) = eOm ε (1 / (l : ℚ) ^ n) ^ t.val * eOm ε (1 / (l : ℚ) ^ (2 * n))

end Global

section Local

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

structure IsReb (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω) : Prop where
  inj : Function.Injective ψ
  par : ψ (qO p) = T.qq n
  sub : ∀ a b : Lau p, (∀ i : ℤ, b.coeff ((p : ℤ) ^ n * i) = a.coeff i) → (∀ r : ℤ, ¬ (p : ℤ) ^ n ∣ r → b.coeff r = 0) →
    ψ (algebraMap (Lau p) (O0 p) b) = algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) a)
  rng : ψ.range = (Algebra.adjoin (O0 p) {T.qq n}).toSubring

def thL (a : Lau p) : Lau p where
  coeff r := (r : ℤ_[p]) * a.coeff r
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def zp (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] (z : ℤ_[p]) : Ω :=
  algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z))

def Ev (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) ∧
    (∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r)) ∧ x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) ∧
    x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))

end Local

end GlobalTheory.Glue
end
end
