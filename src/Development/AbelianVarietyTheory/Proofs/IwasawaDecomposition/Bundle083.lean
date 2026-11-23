module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_eq_mk_rootT {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (n : ℕ) :
    PreTilt.coeff n e = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) := by
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) e)
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e
  rw [zero_add] at h3
  rw [← h3, ← h2]
  rfl

theorem eps_coeff : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (n : ℕ),
    PreTilt.coeff n C.ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT C.ε n) :=
  fun _ _ C n => coeff_eq_mk_rootT C.ε n

end GlobalTheory.MemLoc
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtMul

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def substL (A : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.C (A v.1 v.2.1 m) * MvPolynomial.X (v.1, m, v.2.2)

def substR (B : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.X (v.1, v.2.1, m) * MvPolynomial.C (B v.1 m v.2.2)

theorem eval_bind_substL (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q) =
      MvPolynomial.eval (upt (fun σ => A σ * Y σ)) Q := by
  calc MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt Y) (substL A v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt Y) (substL A v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt Y) (substL A v)) = upt (fun σ => A σ * Y σ) := by
        funext v
        simp [substL, upt, Matrix.mul_apply]
      rw [hf]

theorem eval_bind_substR (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q) =
      MvPolynomial.eval (upt (fun σ => X σ * B σ)) Q := by
  calc MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt X) (substR B v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt X) (substR B v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt X) (substR B v)) = upt (fun σ => X σ * B σ) := by
        funext v
        simp [substR, upt, Matrix.mul_apply]
      rw [hf]

theorem defectL_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt A) i m) * P m j) =
      evM P (upt (fun σ => A σ * Y σ)) i j - (evM P (upt A) * evM P (upt Y)) i j := by
  rw [map_sub, eval_bind_substL]
  simp [evM, Matrix.mul_apply]

theorem defectR_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) (P i j) -
        ∑ m, P i m * MvPolynomial.C (evM P (upt B) m j)) =
      evM P (upt (fun σ => X σ * B σ)) i j - (evM P (upt X) * evM P (upt B)) i j := by
  rw [map_sub, eval_bind_substR]
  simp [evM, Matrix.mul_apply]

theorem evM_ratPt (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hA : Agrees a b P)
    (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
  rw [hA γ γ₀ h]
  ext i j
  rfl

theorem ratPt_one :
    ratPt ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
  funext σ
  simp [ratPt]

theorem ratPt_mul (γ₀ γ₁ : GL (Fin n) L) :
    ratPt ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ := by
  funext σ
  simp [ratPt, Matrix.map_mul]

theorem evM_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧
      ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y →
        evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  intro L _ _ _ n a ι _ _ b P hA
  have h1 : evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 := by
    have hm : ((((1 : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [OneMemClass.coe_one, Units.val_one]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    rw [← ratPt_one, evM_ratPt a b P hA 1 1 hm, map_one, LinearMap.toMatrix_one]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ γ₁ : GL (Fin n) L, γ₁ ∈ GQ0 L n →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt (ratPt (γ₁ : Matrix (Fin n) (Fin n) L))) := by
    intro γ₀ h₀ γ₁ h₁
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h₀
    obtain ⟨γ', hγ'⟩ := exists_gq γ₁ h₁
    have hm : ((((γ * γ' : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [Subgroup.coe_mul, Units.val_mul, hγ, hγ', Matrix.map_mul]
    rw [← ratPt_mul, evM_ratPt a b P hA _ _ hm, evM_ratPt a b P hA _ _ hγ, evM_ratPt a b P hA _ _ hγ', map_mul,
      LinearMap.toMatrix_mul]
  have hL : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt Y →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * Y σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt Y) := by
    intro γ₀ h₀ Y hY
    ext i j
    have e := GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n (MvPolynomial.bind₁ (substL (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) i m) * P m j)
      (fun γ₁ h₁ => by rw [defectL_eval, hrat γ₀ h₀ γ₁ h₁, sub_self]) Y hY
    rw [defectL_eval, sub_eq_zero] at e
    exact e
  refine ⟨h1, fun X Y hX hY => ?_⟩
  ext i j
  have e := GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n (MvPolynomial.bind₁ (substR Y) (P i j) -
      ∑ m, P i m * MvPolynomial.C (evM P (upt Y) m j))
    (fun γ₀ h₀ => by rw [defectR_eval, hL γ₀ h₀ Y hY, sub_self]) X hX
  rw [defectR_eval, sub_eq_zero] at e
  exact e

end GlobalTheory.AlgWtMul
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E), Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  first | exact @GlobalTheory.GaugeEx.continuous_pairOf_joint | exact GlobalTheory.GaugeEx.continuous_pairOf_joint | (intros; apply GlobalTheory.GaugeEx.continuous_pairOf_joint <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  first | exact @GlobalTheory.GaugeEx.FibBasic.fibAt_basic | exact GlobalTheory.GaugeEx.FibBasic.fibAt_basic | (intros; apply GlobalTheory.GaugeEx.FibBasic.fibAt_basic <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.nonempty_standardLocalHaarMeasures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Nonempty (StdMeas b) := by
  first | exact @GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | exact GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | (intros; apply GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Subst

theorem consCol_mulVec_map {E S : Type} [Field E] [CommRing S] (φ : E →+* S) {M : ℕ}
    (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (t : S) (w : Fin M → S) :
    ((Matrix.of fun i => Fin.cons (α := fun _ => E) (x 0 i) (B i) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) E).map φ).mulVec (Fin.cons t w) =
      t • (fun i => φ (x 0 i)) + (B.map φ).mulVec w := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

theorem det_consCol_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (h : StepData σ J x a B J') : (consCol x B).det ≠ 0 := by
  obtain ⟨-, ha, hx, hB, hJ', -, hd⟩ := h
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e := consCol_mulVec_map (RingHom.id E) x B (v 0) (Fin.tail v)
  rw [Fin.cons_self_tail] at e
  have e' : v 0 • x 0 + B.mulVec (Fin.tail v) = 0 := by
    rw [← hPv]
    exact e.symm
  let r : Fin (M + 1) → E := Matrix.vecMul (fun i => σ (x 0 i)) J
  have hr : ∀ y, hE σ J (x 0) y = r ⬝ᵥ y := by
    intro y
    simp only [hE, Formalism.UG.hform, r, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have h1 : r ⬝ᵥ B.mulVec (Fin.tail v) = 0 := by
    rw [Matrix.dotProduct_mulVec]
    have : Matrix.vecMul r B = 0 := by
      funext j
      exact (hr _).symm.trans (hB j)
    rw [this, zero_dotProduct]
  have h2 : v 0 = 0 := by
    have := congrArg (fun y => r ⬝ᵥ y) e'
    simp only [dotProduct_add, h1, dotProduct_smul, ← hr (x 0), hx, add_zero, dotProduct_zero,
      smul_eq_mul, mul_eq_zero] at this
    rcases this with h | h
    · exact h
    · exact absurd ((map_eq_zero _).1 h) ha
  rw [h2, zero_smul, zero_add] at e'
  have h3 : J'.mulVec (Fin.tail v) = 0 := by
    rw [hJ', ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero]
  have h4 : Fin.tail v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd h3
  apply hv
  rw [← Fin.cons_self_tail v, h2, h4]
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem lintegral_subst (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (h1 : IsArtinianRing S) (h2 : IsReduced S) (lam : Measure S) (hl : lam.IsAddHaarMeasure) (M : ℕ)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) S) (hG : IsUnit G.det)
    (f : (Fin (M + 1) → S) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(Measure.pi fun _ => lam) =
      (modu S G.det : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (G.mulVec (Fin.cons t (y' 0))) ∂(tupMeas lam 1 M) ∂lam := by
  have key := GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct S h1 h2 lam hl 1 (M + 1) G 1 hG (by simp)
  have hm1 : modu S 1 = 1 := (GlobalTheory.GaugeEx.modu_basic S).2.2.1
  rw [Matrix.det_one, hm1, pow_one, one_pow, mul_one] at key
  have hU : ∀ K : ℕ, MeasurePreserving (fun X : Fin 1 → Fin K → S => X 0) (tupMeas lam 1 K)
      (Measure.pi fun _ => lam) := fun K =>
    measurePreserving_funUnique (Measure.pi fun _ : Fin K => lam) (Fin 1)
  have hGc : Continuous fun z : Fin (M + 1) → S => G.mulVec z :=
    continuous_const.matrix_mulVec continuous_id
  have hlr : lrAct G (1 : Matrix (Fin 1) (Fin 1) S) = fun X _ => G.mulVec (X 0) := by
    funext X a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [lrAct]
  have hlrm : Measurable (lrAct G (1 : Matrix (Fin 1) (Fin 1) S)) := by
    rw [hlr]
    exact Measurable.of_eval fun _ => hGc.measurable.comp (measurable_pi_apply 0)
  have hfG : Measurable fun z : Fin (M + 1) → S => f (G.mulVec z) := hf.comp hGc.measurable
  have hP := (measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => lam) 0).symm
  have hc : ∀ p : S × (Fin M → S),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => S) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  calc ∫⁻ z, f z ∂(Measure.pi fun _ => lam)
      = ∫⁻ X, f (X 0) ∂(tupMeas lam 1 (M + 1)) := ((hU _).lintegral_comp hf).symm
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ X, f (G.mulVec (X 0)) ∂(tupMeas lam 1 (M + 1)) := by
        conv_lhs => rw [key]
        rw [lintegral_smul_measure, lintegral_map (f := fun X : Fin 1 → Fin (M + 1) → S => f (X 0))
          (hf.comp (measurable_pi_apply 0)) hlrm, hlr]
        rfl
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ z, f (G.mulVec z) ∂(Measure.pi fun _ => lam) := by
        rw [(hU _).lintegral_comp hfG]
    _ = _ := by
        congr 1
        rw [← hP.lintegral_comp hfG]
        refine (lintegral_prod _ (hfG.comp hP.measurable).aemeasurable).trans ?_
        refine lintegral_congr fun t => ?_
        have hm : Measurable fun w : Fin M → S => f (G.mulVec (Fin.cons t w)) := by
          have := (hfG.comp hP.measurable).comp (measurable_prodMk_left (x := t))
          convert this using 2 with w
          simp only [Function.comp, hc]
        rw [(hU M).lintegral_comp hm]
        simp only [Function.comp, hc]

theorem subst : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ (lam : Measure (R ⊗[F] E)), lam.IsAddHaarMeasure → ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E), g • ratTup (F := F) R x = y → ∀ f : (Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ z, f z ∂(Measure.pi fun _ => lam) = (modu (R ⊗[F] E) (inclR R (consCol x B).det) : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (t • y 0 + pairOf R σ J B y g y' 1) ∂(tupMeas lam 1 M) ∂lam := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hR M J x a B J' hS lam hl g y hy f hf
  obtain ⟨n1, n2, -⟩ := GlobalTheory.GaugeEx.nice_tensor F E R hR
  have hP : IsUnit (inclR (F := F) R (consCol x B).det) :=
    (IsUnit.mk0 _ (det_consCol_ne_zero σ J x a B J' hS)).map _
  have hJ : IsUnit (JR (F := F) R J).det := by
    have : IsUnit (inclR (F := F) R J.det) := (IsUnit.mk0 _ hS.1.2).map _
    rwa [RingHom.map_det] at this
  set A : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) :=
    (HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)).val with hA
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have hU : Formalism.UG.cT (sigR R σ) A * JR R J * A = JR R J := (show HR R σ J from g).2
  have hN : A.det * sigR R σ A.det = 1 := by
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply hJ.mul_left_cancel
    rw [mul_one]
    conv_rhs => rw [← this]
    ring
  have hmA : modu (R ⊗[F] E) A.det = 1 := by
    rw [(GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ hCM R A.det 1 hAu (by rw [map_one, hN])).2]
    exact (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  have hdet : (A * (consCol x B).map (inclR (F := F) R)).det =
      A.det * inclR (F := F) R (consCol x B).det := by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [lintegral_subst (R ⊗[F] E) n1 n2 lam hl M (A * (consCol x B).map (inclR (F := F) R))
    (by rw [hdet]; exact hAu.mul hP) f hf, hdet,
    (GlobalTheory.GaugeEx.modu_basic (R ⊗[F] E)).2.1 _ _ hAu hP, hmA, one_mul]
  congr 1
  refine lintegral_congr fun t => lintegral_congr fun y' => congrArg f ?_
  rw [← Matrix.mulVec_mulVec, consCol, consCol_mulVec_map, Matrix.mulVec_add, Matrix.mulVec_smul]
  subst hy
  rfl

end GlobalTheory.GaugeEx.Subst
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.hermitianQuadratic_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  first | exact @GlobalTheory.GaugeEx.q_and_unitary_local_components | exact GlobalTheory.GaugeEx.q_and_unitary_local_components | (intros; apply GlobalTheory.GaugeEx.q_and_unitary_local_components <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0) (r : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsProd b ν mi mv → (Function.mulSupport r).Finite → IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  first | exact @GlobalTheory.GaugeEx.ProdScale.isProd_smul | exact GlobalTheory.GaugeEx.ProdScale.isProd_smul | (intros; apply GlobalTheory.GaugeEx.ProdScale.isProd_smul <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.tailProd_mul_of_lattice_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  first | exact @GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | exact GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | (intros; apply GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.GaugeEx.LocComp

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
  (π : R ⊗[F] E →+* R' ⊗[F] E) (σ : E →ₐ[F] E)

theorem map_mulVec_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) (R ⊗[F] E)) (z : Fin n → R ⊗[F] E) :
    (fun i => π (A.mulVec z i)) = (A.map π).mulVec (fun i => π (z i)) := by
  funext i
  exact RingHom.map_mulVec π A z i

theorem map_smul_ratTup (hπ : ∀ e : E, π (inclR R e) = inclR R' e) {N n : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (x : Fin n → Fin N → E) (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π) :
    (fun a i => π ((g • ratTup (F := F) R x) a i)) = g' • ratTup (F := F) R' x := by
  funext a
  change (fun i => π ((HA.mat R σ J g).val.mulVec (fun j => inclR R (x a j)) i)) =
    (HA.mat R' σ J g').val.mulVec (fun j => inclR R' (x a j))
  rw [map_mulVec_eq, h]
  simp only [hπ]

theorem map_pairOf (hπ : ∀ e : E, π (inclR R e) = inclR R' e) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π)
    (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) :
    (fun a i => π (pairOf R σ J B y g y' a i)) =
      pairOf R' σ J B (fun a i => π (y a i)) g' (fun a i => π (y' a i)) := by
  have hB : (B.map (inclR (F := F) R)).map π = B.map (inclR (F := F) R') := by
    ext i j
    exact hπ _
  funext a
  fin_cases a
  · rfl
  · change (fun i => π ((HA.mat R σ J g).val.mulVec ((B.map (inclR (F := F) R)).mulVec (y' 0)) i)) =
      (HA.mat R' σ J g').val.mulVec ((B.map (inclR (F := F) R')).mulVec (fun i => π (y' 0 i)))
    rw [map_mulVec_eq, map_mulVec_eq, h, hB]

theorem map_inv {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π) :
    (HA.mat R' σ J g'⁻¹).val = (HA.mat R σ J g⁻¹).val.map π := by
  change ((HA.mat R' σ J g')⁻¹).val = ((HA.mat R σ J g)⁻¹).val.map π
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]

end BaseMap

theorem exists_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  intro F E _ _ _ _ _ σ d b M J x B g
  obtain ⟨⟨gi, hgi⟩, hv⟩ := (q_and_unitary_local_components F E σ (M + 1) J).2 g
  choose gv hgv using hv
  have hI : ∀ e : E, prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e :=
    qloc_incl (fstA F) prInf fun r e => rfl
  have hV : ∀ v (e : E), prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := fun v =>
    qloc_incl ((evalV F v).comp (sndA F)) (prV v) fun r e => rfl
  have hint := (GlobalTheory.GaugeEx.IntBasis.main F E σ d b).2.2.1
  refine ⟨gi, gv, map_smul_ratTup prInf σ hI J x g gi hgi,
    fun v => map_smul_ratTup (prV v) σ (hV v) J x g (gv v) (hgv v),
    fun y y' => map_pairOf prInf σ hI J B g gi hgi y y',
    fun v y y' => map_pairOf (prV v) σ (hV v) J B g (gv v) (hgv v) y y', ?_⟩
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  filter_upwards [hint ((HA.mat (AF F) σ J g).val i j), hint ((HA.mat (AF F) σ J g⁻¹).val i j)]
    with v h1 h2
  rw [map_inv (prV v) σ J g (gv v) (hgv v), hgv v]
  exact ⟨h1, h2⟩

end GlobalTheory.GaugeEx.LocComp
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  first | exact @GlobalTheory.GaugeWittLoc.exists_smul_eq | exact GlobalTheory.GaugeWittLoc.exists_smul_eq | (intros; apply GlobalTheory.GaugeWittLoc.exists_smul_eq <;> assumption)
end
