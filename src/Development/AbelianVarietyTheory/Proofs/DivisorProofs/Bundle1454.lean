module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem invT_invT (h : GLw m w) : invT m _ (invT m _ h) = h :=
  Units.ext (by change (h.val)ᵀᵀ = h.val; exact transpose_transpose _)

theorem invT_injective : Function.Injective (invT m (w.adicCompletion E)) := fun x y hxy => by
  rw [← invT_invT x, hxy, invT_invT]

theorem dlt_eq_iff (hw : ¬ IsSplitAt w) (β β' : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (hβ' : IsUnit (GlobalTheory.TwLat.gram e b β'))
    (g : GLw m w) :
    GlobalTheory.TwLat.dlt e b β' = g⁻¹ * GlobalTheory.TwLat.dlt e b β * thL m w g ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β' := by
  unfold GlobalTheory.TwLat.dlt
  rw [dite_eq_left hβ, dite_eq_left hβ']
  have hth : thL m w g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    simp only [thL, if_neg hw]; rfl
  have hinv : g⁻¹ = invT m _ (invT m _ g⁻¹) := (invT_invT _).symm
  have key : g⁻¹ * (invT m _ hβ.unit * (PhiU m _)⁻¹) * thL m w g =
      invT m _ (invT m _ g⁻¹ * hβ.unit * GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    rw [hth, map_mul, map_mul, ← hinv]; group
  rw [key, mul_left_inj, invT_injective.eq_iff, Units.ext_iff, eq_comm]
  rfl

theorem herm_sum_left (β z : B.A) (f : Fin m → B.A) : B.herm β (∑ i, f i) z = ∑ i, B.herm β (f i) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm

  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (β y : B.A) (f : Fin m → B.A) : B.herm β y (∑ i, f i) = ∑ i, B.herm β y (f i) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm

  rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_sub_left (β y y' z : B.A) : B.herm β (y - y') z = B.herm β y z - B.herm β y' z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_sub, sub_mul, map_sub]

theorem herm_crd (he : ∀ x, e (K.c x) = cj w (e x)) (β y z : B.A) :
    e (B.herm β y z) = crd e b y ⬝ᵥ (GlobalTheory.TwLat.gram e b β *ᵥ fun l => cj w (crd e b z l)) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]

  simp only [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, map_sum,
  map_mul, he]
  simp only [dotProduct, mulVec, crd, GlobalTheory.TwLat.gram, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cj_cj (he : ∀ x, e (K.c x) = cj w (e x)) (z : w.adicCompletion E) : cj w (cj w z) = z := by
  obtain ⟨k, rfl⟩ := e.surjective z
  rw [← he, ← he, K.c_c]

theorem eq_zero_of_herm (he : ∀ x, e (K.c x) = cj w (e x)) (β : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (d : B.A)
    (hd : ∀ t, B.herm β d t = 0) : d = 0 := by
  have h1 : ∀ v, (crd e b d ᵥ* GlobalTheory.TwLat.gram e b β) ⬝ᵥ v = 0 := by
    intro v
    have h := congrArg e (hd (ofCrd e b fun l => cj w (v l)))
    rw [herm_crd e b he, map_zero, dotProduct_mulVec] at h
    have hv : (fun l => cj w (crd e b (ofCrd e b fun l => cj w (v l)) l)) = v := by
      funext l; rw [crd_ofCrd, cj_cj e he]
    rwa [hv] at h
  have h2 : crd e b d ᵥ* GlobalTheory.TwLat.gram e b β = 0 := by
    funext j
    have := h1 (Pi.single j 1)
    simpa [dotProduct_single] using this
  have h3 : crd e b d = 0 := by
    have : crd e b d = (crd e b d ᵥ* (hβ.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E))) ᵥ*
        ((hβ.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
    rw [this, IsUnit.unit_spec, h2, zero_vecMul]
  apply crd_injective e b
  rw [h3]; funext i; simp [crd]

end GlobalTheory.TwLatInj

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

theorem dlt_twConj_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) →
    ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u : B.A,
    Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) →
    (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ x x' : B.Aˣ, B.σ (x : B.A) = x →
    B.σ (x' : B.A) = x' →
    ((∃ g : GLw m w, GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x') = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g) ↔
      ∃ a : B.Aˣ, (x' : B.A) = x * (a * B.σ a)) := by
  intro E _ _ _ _ w hw K e he _ _ B m b u hu β₀ hβ₀ hG x x' hx hx'
  obtain ⟨ε, hε⟩ : ∃ ε : B.A, ε = (-1) ^ (m - 1) := ⟨_, rfl⟩
  rw [← hε] at hβ₀
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hεa : ε = algebraMap K.E B.A ((-1) ^ (m - 1)) := by rw [hε]; simp

  have hasym : ∀ t : B.A, B.σ t = t → ∀ y z, K.c (B.herm ((β₀ : B.A) * t) y z) =
      B.herm ((β₀ : B.A) * t) (ε * u * z) y := by
    intro t ht y z
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    rw [← GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, map_mul B.σ, hβ₀, ht, B.σ_σ]
    congr 1; ring
  constructor
  · rintro ⟨g, hg⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x') g] at hg
    let φ : B.A → B.A := fun a => ofCrd e b (g.val *ᵥ crd e b a)
    have hcφ : ∀ a, crd e b (φ a) = g.val *ᵥ crd e b a := fun a => crd_ofCrd e b _
    have hφs : ∀ (k : K.E) (a : B.A), φ (k • a) = k • φ a := by
      intro k a; apply crd_injective e b; rw [hcφ, crd_smul, crd_smul, hcφ, mulVec_smul]
    have hφadd : ∀ a a', φ (a + a') = φ a + φ a' := by
      intro a a'; apply crd_injective e b; rw [hcφ, crd_add, crd_add, hcφ, hcφ, mulVec_add]
    have hφsurj : ∀ t, φ (ofCrd e b ((g⁻¹ : GLw m w).val *ᵥ crd e b t)) = t := by
      intro t; apply crd_injective e b
      rw [hcφ, crd_ofCrd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

    have hiso : ∀ y z, B.herm ((β₀ : B.A) * x) (φ y) (φ z) = B.herm ((β₀ : B.A) * x') y z := by
      intro y z; apply e.injective
      rw [herm_crd e b he, herm_crd e b he, hcφ, hcφ, ← hg]
      have hc : (fun l => cj w ((g.val *ᵥ crd e b z) l)) = g.val.map (cj w) *ᵥ fun l => cj w (crd e b z l) := by
        funext l; exact RingHom.map_mulVec (cj w) g.val (crd e b z) l
      have ht : g.val *ᵥ crd e b y = crd e b y ᵥ* g.valᵀ := (vecMul_transpose _ _).symm
      rw [hc, ht]
      simp only [dotProduct_mulVec, vecMul_vecMul]

    have hv : ∀ z, φ (ε * u * z) = ε * u * φ z := by
      intro z
      have key : ∀ y, B.herm ((β₀ : B.A) * x) (φ (ε * u * z) - ε * u * φ z) (φ y) = 0 := by
        intro y
        rw [herm_sub_left, hiso, ← hasym x' hx', ← hiso, hasym x hx, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_herm e b he _ (hG x) _ fun t => by rw [← hφsurj t]; exact key _)
    have hφu : ∀ z, φ (u * z) = u * φ z := by
      intro z
      have h1 : φ (ε * u * z) = ε * φ (u * z) := by
        rw [mul_assoc, hεa, ← Algebra.smul_def, ← Algebra.smul_def, hφs]
      have h2 := (hv z).symm.trans h1
      linear_combination (-ε) * h2 - (φ (u * z) - u * φ z) * hε2
    have hφmul : ∀ a c, φ (a * c) = a * φ c := by
      intro a
      have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hu]; trivial
      induction ha using Algebra.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
      | algebraMap r =>
        intro c; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
      | add a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [add_mul, hφadd, h₁, h₂, add_mul]
      | mul a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [mul_assoc, h₁, h₂, mul_assoc]
    have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := ⟨_, hφsurj 1⟩
    let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
    refine ⟨c, ?_⟩
    have hc : (c : B.A) = φ 1 := rfl
    have hxx : (x : B.A) * ((x⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv x
    have hd : ∀ t, B.herm ((β₀ : B.A) * x) (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) t = 0 := by
      intro t
      have h1 := hiso 1 t
      rw [hφ t, ← hc] at h1
      unfold GlobalTheory.UnitLemma.InvAlg.herm at h1 ⊢
      have h3 : (β₀ : B.A) * x * (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) * B.σ t =
          (β₀ : B.A) * x' * 1 * B.σ t - (β₀ : B.A) * x * c * B.σ (t * c) := by
        rw [map_mul B.σ]
        linear_combination ((β₀ : B.A) * (x' - x * (c * B.σ c)) * B.σ t) * hxx
      rw [h3, map_sub, h1, sub_self]
    have h0 := eq_zero_of_herm e b he _ (hG x) _ hd
    have : (x' : B.A) - x * (c * B.σ c) = 0 := by
      rw [← one_mul ((x' : B.A) - _), ← hxx, mul_assoc, h0, mul_zero]
    exact sub_eq_zero.1 this
  · rintro ⟨a, ha⟩
    refine ⟨mulGL e b a, ?_⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x')]
    ext i j
    have h1 : GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x') i j = e (B.herm ((β₀ : B.A) * x) (a * b i) (a * b j)) := by
      simp only [GlobalTheory.TwLat.gram, Matrix.of_apply]
      rw [ha, ← mul_assoc, GlobalTheory.UnitLemma.Basic.herm_norm]
    rw [h1, herm_crd e b he]
    have hcol : ∀ i, crd e b ((a : B.A) * b i) = fun k => (mulGL e b a).val k i := by
      intro i; funext k; rw [mulGL_val, ← mulHom_eq, mulHom_apply]; rfl
    rw [hcol, hcol]
    congr 1
    simp only [dotProduct, mulVec, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

end GlobalTheory.TwLatInj
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.StdPairSB

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (p : 𝒪[k])
    (hAB : ∀ i j, valuation k (B i j - A i j) ≤ valuation k (p : k)) :
    valuation k (B.det - A.det) ≤ valuation k (p : k) := by
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hA' : A = (algebraMap 𝒪[k] k).mapMatrix A' := by ext i j; rfl
  have hB' : B = (algebraMap 𝒪[k] k).mapMatrix B' := by ext i j; rfl
  have hdvd : ∀ x y : 𝒪[k], valuation k (x : k) ≤ valuation k (y : k) ↔ y ∣ x :=
    fun x y => Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))
  have key : (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix B' =
      (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix A' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← hdvd]
    simpa [A', B'] using hAB i j
  have h2 : B'.det - A'.det ∈ Ideal.span {p} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, key]
  rw [Ideal.mem_span_singleton, ← hdvd] at h2
  rw [hA', hB', ← RingHom.map_det, ← RingHom.map_det]
  exact h2


open Classical in
def gfun (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) : ℂ :=
  if h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

theorem prop_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c m r : ℕ} {A : Matrix (Fin m) (Fin m) k}
    {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
  by_contra hP
  exact h (by unfold gfun; rw [dite_eq_right hP])

theorem stable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) {m r : ℕ} {A A' : Matrix (Fin m) (Fin m) k}
    {B B' : Matrix (Fin m) (Fin r) k}
    (hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c))
    (hA : ∀ i j, valuation k (A' i j - A i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k))
    (hB : ∀ i j, valuation k (B' i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k)) :
    (A'.det ≠ 0 ∧ IsGLO A' ∧ ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ∧
      gfun ν ϖ c A' B' = gfun ν ϖ c A B := by
  obtain ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩ := hP
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have hγc : valuation k ((ϖ ^ max c 1 : kˣ) : k) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right_of_le_one' hu.le (le_max_left _ _)
  have hγ1 : valuation k ((ϖ ^ max c 1 : kˣ) : k) < 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' hu (by omega)
  have hA'int : ∀ i j, A' i j ∈ 𝒪[k] := by
    intro i j
    have h1 : valuation k (A i j) ≤ 1 := hAint i j
    rw [Valuation.mem_integer_iff, ← sub_add_cancel (A' i j) (A i j)]
    exact Valuation.map_add_le _ ((hA i j).trans hγ1.le) h1
  have hB'c : ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    intro i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (B' i j) (B i j)]
    exact Valuation.map_add_le _ ((hB i j).trans hγc) (hBc i j)
  have hdiff := det_sub_le A A' hAint hA'int ⟨((ϖ ^ max c 1 : kˣ) : k), hγ1.le⟩ hA
  have hdiff1 : valuation k (A'.det - A.det) < valuation k A.det := by
    rw [hAdet]; exact lt_of_le_of_lt hdiff hγ1
  have hdet' : valuation k A'.det = 1 := by
    rw [← sub_add_cancel A'.det A.det, Valuation.map_add_eq_of_lt_right _ hdiff1, hAdet]
  have hd0' : A'.det ≠ 0 := by
    intro h; rw [h, map_zero] at hdet'; exact zero_ne_one hdet'
  refine ⟨⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, ?_⟩
  unfold gfun
  rw [dite_eq_left ⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, dite_eq_left ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩]
  set u := Units.mk0 A.det hd0
  set u' := Units.mk0 A'.det hd0'
  have hr : ν (u⁻¹ * u') = 1 := by
    apply hν
    refine ⟨?_, ?_⟩
    · simp [u, u', hAdet, hdet']
    · have : ((u⁻¹ * u' : kˣ) : k) - 1 = A.det⁻¹ * (A'.det - A.det) := by
        simp only [u, u', Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [mul_sub, inv_mul_cancel₀ hd0]
      rw [this, map_mul, map_inv₀, hAdet, inv_one, one_mul]
      exact hdiff.trans hγc
  have hu' : u' = u * (u⁻¹ * u') := by group
  rw [hu', map_mul, hr, mul_one]

theorem isLocallyConstant_gfun {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ max c 1))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      (∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).1 i j - A i j) ≤
        valuation k ((ϖ ^ max c 1 : kˣ) : k)) ∧
      ∀ i j, valuation k (q.2 i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_fst.matrix_elem i j).tendsto (A, B)).eventually (hnh (A i j))
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev] with q hq
  by_cases hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · exact (stable hϖ hν hP hq.1 hq.2).2
  · have h0 : gfun ν ϖ c A B = 0 := by unfold gfun; rw [dite_eq_right hP]
    show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
    rw [h0]
    by_contra hne
    refine hP (stable hϖ hν (prop_of_ne hne) (fun i j => ?_) (fun i j => ?_)).1
    · rw [Valuation.map_sub_swap]; exact hq.1 i j
    · rw [Valuation.map_sub_swap]; exact hq.2 i j

theorem integral_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {m r : ℕ}
    {A : Matrix (Fin m) (Fin m) k} {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    (∀ i j, A i j ∈ 𝒪[k]) ∧ ∀ i j, B i j ∈ 𝒪[k] := by
  obtain ⟨-, ⟨hA, -⟩, hB⟩ := prop_of_ne h
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  refine ⟨hA, fun i j => ?_⟩
  rw [Valuation.mem_integer_iff]
  refine (show valuation k (B i j) ≤ valuation k ((ϖ ^ c : kˣ) : k) from hB i j).trans ?_
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one₀ zero_le' hu.le

end Local

end GlobalTheory.StdPairSB

theorem GlobalTheory.StdPairSB.stdPair_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ)
    (c a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SplitFlip.CondLE ϖ c ν →
      stdA ν ϖ c a a' ∈ SB (Matrix (Fin a) (Fin (a + a')) k) ∧ stdB ν ϖ c a a' ∈ SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
end
end

section

open scoped TensorProduct Matrix Classical

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

theorem polMap_index_injective (W Λ : Type) [Fintype W] :
    Function.Injective (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
  have key : ∀ (f : W → (Λ →₀ ℕ)) (w : W) (l : Λ),
      (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) (w, l) = f w l := by
    intro f w l
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective w) _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Prod.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (W × Λ) →₀ ℕ => F (w, l)) h

theorem polMap_tprod_monomial (W Λ : Type) [Fintype W] [DecidableEq W] (f : W → (Λ →₀ ℕ)) :
    polMap W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial Λ ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMap_injective (W Λ : Type) [Fintype W] [DecidableEq W] :
    Function.Injective (polMap W Λ) := by
  let B := Basis.piTensorProduct (fun _ : W => basisMonomials Λ ℂ)
  have hli : LinearIndependent ℂ (polMap W Λ ∘ B) := by
    have h := (basisMonomials (W × Λ) ℂ).linearIndependent.comp _ (polMap_index_injective W Λ)
    have e : polMap W Λ ∘ B = (basisMonomials (W × Λ) ℂ) ∘
        (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMap_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMap W Λ ∘ₗ Finsupp.linearCombination ℂ B = Finsupp.linearCombination ℂ (polMap W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

end GlobalTheory.CCRFock
end
end
