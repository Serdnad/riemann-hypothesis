module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle085
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle008
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.SymbolEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem four_values (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Δ x : F)
    (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hx : ∀ σ : F →+* ℝ, 0 < σ x) :
    x ≠ 0 ∧ ∃ a b c d : F, x = a ^ 2 - Δ * b ^ 2 + (c ^ 2 - Δ * d ^ 2) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hx0 : x ≠ 0 := fun h => by simpa [h] using hx σ
  have hΔ0 : Δ ≠ 0 := fun h => by simpa [h] using hΔ σ
  refine ⟨hx0, ?_⟩
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.LocalQuad.isotropic_of_indefinite GlobalTheory.T.hasse_norm_theorem_quadratic_extension F (ι := Fin 5) ![1, -Δ, 1, -Δ, -x]
    (by simp) (fun i => by fin_cases i <;> simp [hx0, hΔ0])
    (fun s => ⟨4, 0, by simpa using hx s, by simp⟩)
  simp [Fin.sum_univ_succ] at hy
  have hy' : y 0 ^ 2 - Δ * y 1 ^ 2 + (y 2 ^ 2 - Δ * y 3 ^ 2) = x * y 4 ^ 2 := by
    linear_combination hy
  have he : y 4 ≠ 0 := by
    intro h
    apply hy0
    have h1 := congrArg σ hy'
    simp only [h, map_add (f := _), map_sub, map_mul, map_pow, map_zero] at h1
    have hn := hΔ σ
    have p1 : 0 ≤ -σ Δ * σ (y 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p3 : 0 ≤ -σ Δ * σ (y 3) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p0 := sq_nonneg (σ (y 0))
    have p2 := sq_nonneg (σ (y 2))
    have e0 : σ (y 0) ^ 2 = 0 := by nlinarith
    have e2 : σ (y 2) ^ 2 = 0 := by nlinarith
    have e1 : -σ Δ * σ (y 1) ^ 2 = 0 := by nlinarith
    have e3 : -σ Δ * σ (y 3) ^ 2 = 0 := by nlinarith
    have z0 : y 0 = 0 := by simpa using e0
    have z2 : y 2 = 0 := by simpa using e2
    have z1 : y 1 = 0 := by simpa [hΔ0] using e1
    have z3 : y 3 = 0 := by simpa [hΔ0] using e3
    funext i
    fin_cases i
    exacts [z0, z1, z2, z3, h]
  refine ⟨y 0 / y 4, y 1 / y 4, y 2 / y 4, y 3 / y 4, ?_⟩
  field_simp
  linear_combination -hy'

private theorem ex_DX {K : Type} [Field K] (Δ x : K) (hx : x ≠ 0) (a b : Lsq K Δ)
    (h : a * star a + b * star b = algebraMap K _ x) : ∃ g : DX Δ, (mt g).det = algebraMap K _ x := by
  have hd : (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = algebraMap K _ x := by
    rw [det_fin_two_of, ← h]; ring
  have hu : IsUnit (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]
    exact (IsUnit.mk0 x hx).map _
  refine ⟨⟨hu.unit, ?_⟩, hd⟩
  show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) hu.unit = (wJ Δ)⁻¹ * hu.unit * (wJ Δ)⁻¹⁻¹
  rw [inv_inv]
  apply Units.ext
  show (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd (Lsq K Δ)) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

theorem UpperTheory.V.Z.Sym.Glob.normD :
    UpperTheory.V.Z.Sym.Glob.NormD := by
  intro F _ _ Δ D hD x hx
  haveI := hD.real
  obtain ⟨hx0, a, b, c, d, h⟩ := four_values F Δ x hD.neg hx
  refine ex_DX Δ x hx0 ⟨a, b⟩ ⟨c, d⟩ ?_
  ext
  · simp; linear_combination -h
  · simp; ring
end

section

open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem mk_el {K : Type} [Field K] {Δ : K} (a b : Lsq K Δ) (h : a * star a + b * star b = 1) :
    ∃ γ : DX Δ, mt γ = !![a, b; -star b, star a] := by
  let g : GL (Fin 2) (Lsq K Δ) := ⟨!![a, b; -star b, star a], !![star a, -b; star b, a], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext1 i; fin_cases i <;> (ext1 j; fin_cases j) <;> simp <;> first | ring1 | linear_combination h, by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext1 i; fin_cases i <;> (ext1 j; fin_cases j) <;> simp <;> first | ring1 | linear_combination h⟩
  refine ⟨⟨g, ?_⟩, rfl⟩
  change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * ((wJ Δ)⁻¹)⁻¹
  rw [inv_inv]
  refine Units.ext ?_
  change (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  ext1 i j
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

private theorem el_shape {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    mt γ 1 1 = star (mt γ 0 0) ∧ mt γ 1 0 = -star (mt γ 0 1) := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) γ.1 = (wJ Δ)⁻¹ * γ.1 * ((wJ Δ)⁻¹)⁻¹ := γ.2
  rw [inv_inv] at h
  have h' : (mt γ).map (starRingEnd _) = !![0, -1; 1, 0] * mt γ * !![0, 1; -1, 0] := congrArg Units.val h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h0 h1
  exact ⟨h0.symm, by rw [h1, neg_neg]⟩

private theorem loc_neg_one {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) (h0 : Δ ≠ 0) (v : Pl F) :
    ∃ a b : Kv v, -1 = a ^ 2 - cv v Δ * b ^ 2 := by
  by_cases hv : v ∈ D.Sg
  · have : CharZero (Kv v) := charZero_of_injective_algebraMap (cv v).injective
    exact GlobalTheory.Published.HasseNormSt.of_isSquare ((map_ne_zero _).2 h0) (hD.split v hv) _
  · obtain ⟨ν, -, hν⟩ := Loc.normEx _ _ _ (hD.off v hv) (-1)
    refine ⟨ν.re, ν.im, ?_⟩
    rw [QuadraticAlgebra.norm_def] at hν
    simp only [Units.val_neg, Units.val_one, map_neg, map_one] at hν
    linear_combination -hν

private theorem glob_neg_one {F : Type} [Field F] [NumberField F] {Δ d : F} (h0 : Δ ≠ 0)
    (hl : ∀ v : Pl F, ∃ a b : Kv v, -1 = a ^ 2 - cv v Δ * b ^ 2) (σ₀ : F →+* ℝ) (hd : ∀ σ : F →+* ℝ, σ d < 0) :
    ∃ p₀ p₁ q₀ q₁ : F, p₀ ^ 2 + d * p₁ ^ 2 - Δ * (q₀ ^ 2 + d * q₁ ^ 2) = -1 ∧ p₀ * p₁ = Δ * q₀ * q₁ :=
  _root_.UpperTheory.Reformulated.B.NormIndexQuadratic.glob_neg_one h0 hl σ₀ hd

theorem UpperTheory.V.Z.Sym.Glob.embEx :
    UpperTheory.V.Z.Sym.Glob.EmbEx := by
  intro F _ _ Δ D hD τ
  have := hD.real
  obtain ⟨σ₀⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  have h0 : Δ ≠ 0 := fun h => by simpa [h] using hD.neg σ₀
  refine ⟨fun hτ => ?_, fun γ hγ hτ σ => ?_⟩
  · obtain ⟨p₀, p₁, q₀, q₁, e₁, e₂⟩ := glob_neg_one h0 (loc_neg_one D hD h0) σ₀ hτ
    have hA : p₁ ^ 2 - Δ * q₁ ^ 2 ≠ 0 := fun h => by
      have h1 : p₀ ^ 2 + 1 - Δ * q₀ ^ 2 = 0 := by linear_combination e₁ - (τ ^ 2 - 4) * h
      have h2 := congrArg σ₀ h1
      simp only [map_sub, map_add (f := _), map_mul, map_pow, map_one, map_zero] at h2
      nlinarith [hD.neg σ₀, sq_nonneg (σ₀ p₀), sq_nonneg (σ₀ q₀)]
    obtain ⟨A, hAe⟩ : ∃ A, A = p₁ ^ 2 - Δ * q₁ ^ 2 := ⟨_, rfl⟩
    rw [← hAe] at hA
    have key : p₁ ^ 2 - Δ * (p₀ * q₁ - q₀ * p₁) ^ 2 - Δ * q₁ ^ 2 = -(τ ^ 2 - 4) * A ^ 2 := by
      rw [hAe]
      linear_combination (p₁ ^ 2 - Δ * q₁ ^ 2) * e₁ - (p₀ * p₁ - Δ * q₀ * q₁) * e₂
    let a : Lsq F Δ := ⟨τ / 2, (p₀ * q₁ - q₀ * p₁) / (2 * A)⟩
    let b : Lsq F Δ := ⟨p₁ / (2 * A), q₁ / (2 * A)⟩
    have hab : a * star a + b * star b = 1 := by
      ext
      · simp [a, b, QuadraticAlgebra.re_one]
        field_simp
        linear_combination key
      · simp [a, b, QuadraticAlgebra.im_one]
        ring
    obtain ⟨γ, hγ⟩ := mk_el a b hab
    refine ⟨γ, ?_, ?_⟩
    · rw [hγ, Matrix.det_fin_two_of]
      linear_combination hab
    · rw [hγ, Matrix.trace_fin_two_of]
      ext <;> simp [a]
  · obtain ⟨s₁, s₂⟩ := el_shape γ
    obtain ⟨hd, ht⟩ := hγ
    rw [Matrix.det_fin_two, s₁, s₂] at hd
    rw [Matrix.trace_fin_two, s₁] at ht
    generalize mt γ 0 0 = a at hd ht
    generalize mt γ 0 1 = b at hd
    have h1 := congrArg (fun x => σ (QuadraticAlgebra.re x)) hd
    have h2 := congrArg (fun x => σ (QuadraticAlgebra.re x)) ht
    simp [QuadraticAlgebra.re_one] at h1 h2
    refine lt_of_le_of_ne ?_ ((map_ne_zero σ).2 hτ)
    simp only [map_sub, map_pow, map_ofNat]
    rw [← h2]
    nlinarith [mul_nonneg (neg_pos.2 (hD.neg σ)).le (mul_self_nonneg (σ a.im)),
      mul_nonneg (neg_pos.2 (hD.neg σ)).le (mul_self_nonneg (σ b.im)), mul_self_nonneg (σ b.re)]
end

section

open QuadraticAlgebra NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

private theorem sq_of_norm {K R : Type} [Field K] [Field R] (f : K →+* R) {Δ τ : K} (a : R) (ha : a ^ 2 = f τ * a - 1)
    (d : EL Δ τ) (hd : d * sigL d = ofE Δ (ω : Etau K τ)) : ∃ x y : R, x ^ 2 - f Δ * y ^ 2 = a := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := d
  have h1 : p0 ^ 2 - Δ * q0 ^ 2 - (p1 ^ 2 - Δ * q1 ^ 2) = 0 := by
    have := congrArg (fun z : EL Δ τ => z.re.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have h2 : 2 * (p0 * p1 - Δ * q0 * q1) + τ * (p1 ^ 2 - Δ * q1 ^ 2) = 1 := by
    have := congrArg (fun z : EL Δ τ => z.im.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have g1 := congrArg f h1
  have g2 := congrArg f h2
  simp only [map_sub, map_add (f := _), map_mul, map_pow, map_zero, map_one, map_ofNat] at g1 g2
  exact ⟨f p0 + f p1 * a, f q0 + f q1 * a, by linear_combination g1 + a * g2 + (f p1 ^ 2 - f Δ * f q1 ^ 2) * ha⟩

private theorem norm_of_sq {K : Type} [Field K] {Δ τ : K} (x y : Etau K τ)
    (h : x ^ 2 - algebraMap K (Etau K τ) Δ * y ^ 2 = ω) : ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau K τ) := by
  obtain ⟨p0, p1⟩ := x
  obtain ⟨q0, q1⟩ := y
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  refine ⟨⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩, ?_⟩
  ext <;> simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination h1
  · ring
  · linear_combination h2
  · ring

private theorem hasse {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (hΔ : Δ ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (a : E) (ha : a ^ 2 = algebraMap F E τ * a - 1) :
    ∃ x y : E, x ^ 2 - algebraMap F E Δ * y ^ 2 = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have key : hs (algebraMap F E Δ) a = 1 := by
    refine hsHasse E _ a ((map_ne_zero _).2 hΔ) ha0 (fun σ => ?_) fun w => ?_
    · exfalso
      have h1 := hτ (σ.comp (algebraMap F E))
      have h2 := congrArg σ ha
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, RingHom.comp_apply] at h1 h2
      nlinarith [sq_nonneg (2 * σ a - σ (algebraMap F E τ))]
    · let v : Pl F := w.under (𝓞 F)
      haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
      have hf : ∀ x : F, KStar.Choice.complMap v w (cv v x) = cv w (algebraMap F E x) :=
        KStar.Choice.complMap_algebraMap v w
      unfold hs
      rw [if_pos]
      by_cases hv : v ∈ D.Sg
      · obtain ⟨s, hs⟩ := h.split v hv
        have e := congrArg (KStar.Choice.complMap v w) hs
        rw [hf, map_mul] at e
        set r := KStar.Choice.complMap v w s
        have hr : r ≠ 0 := by
          rintro h0
          rw [h0, mul_zero, map_eq_zero, map_eq_zero] at e
          exact hΔ e
        haveI : CharZero (Kv w) := algebraRat.charZero _
        refine ⟨(cv w a + 1) / 2, (cv w a - 1) / (2 * r), ?_⟩
        rw [e]
        field_simp
        ring
      · obtain ⟨d, hd⟩ := locNorm (Ov v) (Kv v) (cv v Δ) (cv v τ) (h.off v hv) (hi v hv)
        rw [← hf]
        refine sq_of_norm _ _ ?_ d hd
        rw [hf, ← map_pow, ha, map_sub, map_mul, map_one]
  unfold hs at key
  by_contra hn
  rw [if_neg hn] at key
  norm_num at key

private theorem d_ex {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (σ : F →+* ℝ) :
    ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau F τ) := by
  have hΔ : Δ ≠ 0 := fun h0 => by simpa [h0] using h.neg σ
  haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + τ * r) := ⟨fun r hr => by
    have h1 := hτ σ
    have h2 := congrArg σ hr
    simp only [map_sub, map_add (f := _), map_neg, map_mul, map_pow, map_one, map_ofNat] at h1 h2
    nlinarith [sq_nonneg (2 * σ r - σ τ)]⟩
  haveI : NumberField (Etau F τ) := NumberField.of_module_finite F _
  obtain ⟨x, y, hxy⟩ := hasse D h τ hτ hi hΔ (Etau F τ) ω (by ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
  exact norm_of_sq x y hxy

private theorem tr_re {K : Type} [Field K] {Δ τ : K} (y : EL Δ τ) :
    (QuadraticAlgebra.trace (y * star (sigL y))).re =
      2 * (y.re.re ^ 2 + τ * y.re.re * y.im.re + y.im.re ^ 2) - 2 * Δ * (y.re.im ^ 2 + τ * y.re.im * y.im.im + y.im.im ^ 2) := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := y
  simp [sigL, QuadraticAlgebra.trace_def, two_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

private theorem q_nonneg {t : ℝ} (ht : t ^ 2 - 4 < 0) (p q : ℝ) : 0 ≤ p ^ 2 + t * p * q + q ^ 2 := by
  nlinarith [sq_nonneg (2 * p + t * q), mul_nonneg (sub_nonneg.2 (show t ^ 2 ≤ 4 by linarith)) (sq_nonneg q)]

private theorem q_zero {t : ℝ} (ht : t ^ 2 - 4 < 0) {p q : ℝ} (h : p ^ 2 + t * p * q + q ^ 2 = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    nlinarith [sq_nonneg (2 * p + t * q), mul_pos (sub_pos.2 (show t ^ 2 < 4 by linarith)) (sq_pos_of_ne_zero hq)]
  subst hq
  exact ⟨by simpa using h, rfl⟩

private theorem tr_pos {K : Type} [Field K] {Δ τ : K} (σ : K →+* ℝ) (hΔ : σ Δ < 0) (hτ : σ (τ ^ 2 - 4) < 0) (y : EL Δ τ) :
    0 ≤ σ (QuadraticAlgebra.trace (y * star (sigL y))).re ∧ (y ≠ 0 → 0 < σ (QuadraticAlgebra.trace (y * star (sigL y))).re) := by
  rw [tr_re]
  simp only [map_sub, map_add (f := _), map_mul, map_pow, map_ofNat] at hτ ⊢
  have h1 := q_nonneg hτ (σ y.re.re) (σ y.im.re)
  have h2 := q_nonneg hτ (σ y.re.im) (σ y.im.im)
  have h3 := mul_nonneg (neg_pos.2 hΔ).le h2
  refine ⟨by linarith, fun hy => ?_⟩
  by_contra hn
  have e1 := q_zero hτ (le_antisymm (by linarith) h1)
  have e2 := q_zero hτ ((mul_eq_zero.1 (le_antisymm (by linarith) h3)).resolve_left (neg_pos.2 hΔ).ne')
  simp only [map_eq_zero] at e1 e2
  exact hy (by ext <;> simp [e1.1, e1.2, e2.1, e2.2])

private theorem sig_mul {K : Type} [Field K] {Δ τ : K} (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sig_sig {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sig_star {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

private theorem sig_one_add {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (1 + x) = 1 + sigL x := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem posF {F : Type} [Field F] {Δ τ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hτ : IsCM τ) (d : EL Δ τ) :
    PosF 1 (1 + sigL d * star d) := by
  rintro ⟨⟨p, q⟩, x⟩ hx σ
  have e : (1 + sigL d * star d) * x * star (sigL x) = x * star (sigL x) + (sigL d * x) * star (sigL (sigL d * x)) := by
    rw [sig_mul, sig_sig, star_mul]
    ring
  have e2 : (herm 1 (1 + sigL d * star d) (⟨p, q⟩, x) (⟨p, q⟩, x)).re = p ^ 2 - Δ * q ^ 2 +
      ((QuadraticAlgebra.trace (x * star (sigL x))).re + (QuadraticAlgebra.trace ((sigL d * x) * star (sigL (sigL d * x)))).re) := by
    simp only [herm]
    rw [e, map_add (f := _), map_one, one_mul]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  rw [e2]
  have h1 := tr_pos σ (hΔ σ) (hτ σ) x
  have h2 := (tr_pos σ (hΔ σ) (hτ σ) (sigL d * x)).1
  simp only [map_add σ, map_sub σ, map_mul σ, map_pow σ]
  have h3 := mul_nonneg (neg_pos.2 (hΔ σ)).le (sq_nonneg (σ q))
  have h4 := sq_nonneg (σ p)
  by_cases h0 : x = 0
  · by_contra hn
    have hp : σ p ^ 2 = 0 := le_antisymm (by linarith [h1.1]) h4
    have hq : σ q ^ 2 = 0 := (mul_eq_zero.1 (le_antisymm (by linarith [h1.1]) h3)).resolve_left (neg_pos.2 (hΔ σ)).ne'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, map_eq_zero] at hp hq
    exact hx (by rw [hp, hq, h0]; rfl)
  · linarith [h1.2 h0]

end UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

open UpperTheory.V.Z.Sym.Glob.GlobalDataExistence in
theorem UpperTheory.V.Z.Sym.Glob.datEx :
    UpperTheory.V.Z.Sym.Glob.DatEx := by
  intro F _ _ Δ D h τ hτ hi
  haveI := h.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  obtain ⟨d, hd⟩ := d_ex D h τ hτ hi σ
  have hp := posF h.neg hτ d
  refine ⟨d, _, ⟨fun h0 => by simpa [h0] using hτ σ, one_ne_zero, hd, ?_, ?_, ?_⟩, hp⟩
  · haveI : Module.Finite F (EL Δ τ) := Module.Finite.trans (Lsq F Δ) _
    haveI : IsArtinianRing (EL Δ τ) := IsArtinianRing.of_finite F _
    refine IsArtinianRing.isUnit_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_iff_left.2 fun x hx => ?_)
    by_contra h0
    have := hp (0, x) (fun e => h0 (congrArg Prod.snd e)) σ
    simp [herm, hx] at this
  · rw [sig_one_add, sig_mul, sig_sig, sig_star, star_add, star_one, star_mul, star_star]
  · have e : (d * sigL d) * star (d * sigL d) = 1 := by
      rw [hd]
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    rw [star_mul] at e
    rw [sig_one_add, sig_mul, sig_sig, sig_star]
    linear_combination -e
end

section

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem hs_cast {F A : Type} [Field F] [NumberField F] [Field A] (φ : F →+* A) (p : GlobalTheory.HilbertRecip.Place F) (x d : Fˣ)
    (h : x ∈ GlobalTheory.HilbertRecip.nrm p d ↔ ∃ a b : A, φ x = a ^ 2 - φ d * b ^ 2) :
    Loc.hs (φ d) (φ x) = (((GlobalTheory.HilbertRecip.hs p x d : ℤˣ) : ℤ) : ℂ) := by
  unfold Loc.hs
  by_cases hx : x ∈ GlobalTheory.HilbertRecip.nrm p d
  · obtain ⟨a, b, e⟩ := h.1 hx
    rw [if_pos ⟨a, b, e.symm⟩, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hx]
    simp
  · rw [if_neg fun ⟨a, b, e⟩ => hx (h.2 ⟨a, b, e.symm⟩), GlobalTheory.HilbertRecip.hs_eq_neg_one_iff.2 hx]
    simp

theorem UpperTheory.V.Z.Sym.Glob.recip :
    UpperTheory.V.Z.Sym.Glob.Recip := by
  intro F _ _ d x hd hx
  classical
  lift d to Fˣ using hd.isUnit
  lift x to Fˣ using hx.isUnit
  have h1 : ∀ v : Pl F, Loc.hs (cv v d) (cv v x) = (((GlobalTheory.HilbertRecip.hs (.inl v) x d : ℤˣ) : ℤ) : ℂ) :=
    fun v => hs_cast (cv v) (.inl v) x d Iff.rfl
  have h2 : ∀ σ : F →+* ℝ, Loc.hs (σ d) (σ x) = (((GlobalTheory.HilbertRecip.hs (.inr σ) x d : ℤˣ) : ℤ) : ℂ) :=
    fun σ => hs_cast σ (.inr σ) x d Iff.rfl
  have hfin : {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d}.Finite :=
    (GlobalTheory.HilbertRecip.finite_not_mem_nrm x d).preimage (f := Sum.inl) Sum.inl_injective.injOn
  have hsub : {v : Pl F | Loc.hs (cv v d) (cv v x) ≠ 1} ⊆ {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d} := by
    intro v hv hm
    refine hv ?_
    rw [h1, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hm]
    simp
  refine ⟨hfin.subset hsub, ?_⟩
  have h := GlobalTheory.HilbertRecip.prod_hs x d (hfin.toFinset.disjSum Finset.univ) (by
    rintro (v | σ) hv
    · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      exact hv
    · simp)
  rw [Finset.prod_disjSum, mul_eq_one_iff_eq_inv, Int.units_inv_eq_self] at h
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset]; exact hsub)]
  simp only [h1, h2]
  have h' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) h
  simpa only [Units.coe_prod, Int.cast_prod] using h'
end
