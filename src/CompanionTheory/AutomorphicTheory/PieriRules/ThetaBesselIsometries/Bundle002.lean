module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

lemma eq_of_capP {n : ℕ} (mu mu' : Fin n → ℝ) (h : StrictAnti mu) (h' : StrictAnti mu')
    (e : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y) :
    mu = mu' := by
  have key : ∀ (a b : Fin n → ℝ),
      (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) →
      Set.range a ⊆ Set.range b := by
    rintro a b e _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp ((e _).symm.trans h0)
    exact ⟨t, by exact_mod_cast (by linear_combination ht : (b t : ℂ) = a s)⟩
  exact (h.range_inj_of_wellFoundedGT h').mp ((key _ _ e).antisymm (key _ _ fun Y => (e Y).symm))

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (V : H ≃L[ℂ] H') : H ≃L[ℝ] H' :=
  { V.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := V.continuous
    continuous_invFun := V.symm.continuous }

lemma dsig_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inG ε X) (v : H) :
    V (PI.PhMeasCore.dsig τ X v) = PI.PhMeasCore.dsig τ' X (V v) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (V v)) =
      (toReal V) ∘ (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    exact (hV _ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t) v).symm
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

lemma dsigC_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : V (dsigC ε τ Y v) = dsigC ε τ' Y (V v) := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hH := Formalism.REAL.Jm_conjTranspose ε
  have hJ' := Formalism.REAL.f1alg_JJ_left ε
  unfold dsigC
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  have hs' : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [map_add (f := _), map_smul, dsig_equiv V hV, dsig_equiv V hV] <;> rw [Formalism.REAL.f1alg_inG_iff] <;>
    simp only [thetaJ, conjTranspose_smul, hs, hs', conjTranspose_add, conjTranspose_sub, conjTranspose_neg,
      conjTranspose_mul, hH, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ',
      Matrix.mul_one] <;>
    module

lemma dsigCW_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : V (dsigCW ε τ w v) = dsigCW ε τ' w (V v) := by
  induction w with
  | nil => rfl
  | cons Y w ih => simp only [dsigCW]; rw [dsigC_equiv V hV, ih]

lemma actU_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : V (actU ε τ p v) = actU ε τ' p (V v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [actU, Finsupp.sum, map_sum, map_smul, dsigCW_equiv V hV]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma smooth_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) :
    V v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv g₀ hg₀
  exact ⟨U, fun g => V (F g), hU, hm, (toReal V).contDiff.comp_contDiffOn hF,
    fun g hg hg' => (hV g hg' v).symm.trans (congrArg V (hE g hg hg'))⟩

private lemma dsParamUniq_conjT (a b M : Matrix (Fin n) (Fin n) ℂ) :
    (a * b)ᴴ * M * (a * b) = bᴴ * (aᴴ * M * a) * b := by
  rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]

private lemma dsParamUniq_conj_mem {A B P g : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hA : Pᴴ * A * P = B)
    (hg : gᴴ * A * g = A) : (P⁻¹ * g * P)ᴴ * B * (P⁻¹ * g * P) = B := by
  rw [← hA, ← dsParamUniq_conjT, Matrix.mul_assoc P⁻¹,
    Matrix.mul_nonsing_inv_cancel_left P _ ((Matrix.isUnit_iff_isUnit_det P).mp hP), dsParamUniq_conjT, hg]

lemma smooth_conj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hA : Pᴴ * A * P = B) {v : H}
    (hv : PI.UpqRep.SmoothOnH B (fun g => τ g v)) :
    v ∈ PI.PhMeasCore.smoothVecs A (fun g => τ (P⁻¹ * g * P)) := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun g => P⁻¹ * g * P
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by simp }
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv _ (dsParamUniq_conj_mem hP hA hg₀)
  exact ⟨L ⁻¹' U, F ∘ L, hU.preimage L.continuous, hm, hF.comp_continuousLinearMap L,
    fun g hg hg' => hE _ hg (dsParamUniq_conj_mem hP hA hg')⟩

lemma eq_of_equiv {mu mu' : Fin n → ℝ} (hm : Formalism.QuantumDeterminants.IsHCParam mu) (hm' : Formalism.QuantumDeterminants.IsHCParam mu')
    (h : ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ, ∀ Y : ℂ,
      actU ε τ (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v = Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y • v)
    (h' : ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ', ∀ Y : ℂ,
      actU ε τ' (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y • v)
    (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) (h0 : v ≠ 0) : mu = mu' := by
  refine eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := h v hv Y
  have e2 := h' (V v) (smooth_equiv V hV hv) Y
  rw [← actU_equiv V hV, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using h0) e2

lemma inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ PI.UpqRep.UJset ε) (hb : b ∈ PI.UpqRep.UJset ε) :
    a * b ∈ PI.UpqRep.UJset ε := by
  have ha' : aᴴ * PI.UpqRep.Jm ε * a = PI.UpqRep.Jm ε := ha
  exact (dsParamUniq_conjT a b _).trans (by rw [ha']; exact hb)

lemma cayley_quot {B P Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hP : Pᴴ * PI.UpqRep.Jm ε * P = B)
    (hQ' : Qᴴ * PI.UpqRep.Jm ε * Q = B) : P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  show (P * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  rw [dsParamUniq_conjT, hP, ← hQ', ← dsParamUniq_conjT, Matrix.mul_nonsing_inv _ hd]; simp

end

lemma exists_kfin {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : Rep k r)
    {P : Mx k r} (hP : PI.UpqRep.IsCayleyU k r ε P) (h : PI.UpqRep.IsDS ε mu (fun g => R.σ (P⁻¹ * g * P))) :
    ∃ v, R.KFin v ∧ v ≠ 0 := by
  obtain ⟨S, hfin, hst, -, ⟨v, hvS, hv0, -⟩, -⟩ := h.2.2.2.2.2.1
  refine ⟨v, ⟨S, hfin, hvS, ?_⟩, hv0⟩
  rintro g ⟨hg, hgu⟩ x hx
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : star P * P = 1 := Unitary.star_mul_self_of_mem hP.2
  have hPP' : P * star P = 1 := Unitary.mul_star_self_of_mem hP.2
  have hu : P * g * star P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hgu) (Unitary.star_mem hP.2)
  have hJ : (P * g * star P)ᴴ * PI.UpqRep.Jm ε * (P * g * star P) = PI.UpqRep.Jm ε := by
    have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
    rw [dsParamUniq_conjT, dsParamUniq_conjT, hP.1.2, hg', ← hP.1.2, ← dsParamUniq_conjT, hPP']; simp
  have hK : P * g * star P ∈ PI.UpqRep.Kset ε := by
    refine ⟨hu, ?_⟩
    have h1 : (P * g * star P) * (P * g * star P)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    generalize P * g * star P = m at hJ h1
    conv_lhs => rw [← hJ]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e : P⁻¹ * (P * g * star P) * P = g := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left P _ hd, hPP, Matrix.mul_one]
  simpa only [e] using hst _ hK x hx

theorem param_eq_of_equiv : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, ⟨P, hP, h⟩, hgp⟩ := hR
  obtain ⟨hm', ⟨Q, hQ, h'⟩, hgp'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := smooth_conj (A := Formalism.REAL.Jm ε) hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 := fun B : Mx k r => Matrix.nonsing_inv_mul_cancel_left P B hdP
  have q3 := fun B : Mx k r => Matrix.nonsing_inv_mul_cancel_left Q B hdQ
  have p4 := fun B : Mx k r => Matrix.mul_nonsing_inv_cancel_left P B hdP
  have ha := cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x :=
    fun a ha b hb x => (DFunLike.congr_fun (hmul a ha b hb) x).symm
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.equivOfInverse (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (fun x => by rw [hmul' _ hb _ ha, hba, hone]; rfl) (fun x => by rw [hmul' _ ha _ hb, hab, hone]; rfl)
  refine eq_of_equiv hm hm' (hy.2.2.1 k r ε mu _ _ ⟨P, hP⟩ hgp hm h) (hy.2.2.1 k r ε mu' _ _ ⟨P, hP⟩ hgp' hm' h') (U.toContinuousLinearEquiv.trans A) ?_ hs' hv0
  intro g hg x
  have hg' : g ∈ PI.UpqRep.UJset ε := hg
  have hG : P⁻¹ * g * P ∈ GG k r := dsParamUniq_conj_mem hP.1.1 hP.1.2 hg
  show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
  have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
    simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
  rw [hU _ hG, e, hmul' _ ha _ (inUJ_mul (inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
  simp only [Matrix.mul_assoc, q3, p4]

end DSInequiv
end GlobalTheory
end
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyChoice

open PI.UpqRep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma Kset_sub {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have hg1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]

lemma UJ_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

lemma symm_inter (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) :
    ∀ g ∈ UJset ε, ∀ v, T.symm (σ g v) = σ' g (T.symm v) := by
  intro g hg v
  apply T.injective
  rw [h g hg]; simp

lemma wt_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ' μ v) : IsWtOn (Kset ε) σ μ (T v) := by
  intro θ hθ
  rw [← h _ (Kset_sub hθ), hv θ hθ, map_smul]

lemma ktype_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : IsKTypeOf ε σ' Λ S) :
    IsKTypeOf ε σ Λ (S.map (T.toLinearEquiv : H →ₗ[ℂ] H)) := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ⟨T v, ⟨v, hv, rfl⟩, by simpa using hv0, wt_transfer T h hvw⟩, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ' g x, h2 g hg x hx, h g (Kset_sub hg) x⟩
  · intro S' hle hst
    rcases h3 (S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H)) (by
        intro x hx
        obtain ⟨y, hy, e⟩ := hle hx
        have : y = x := T.injective e
        exact this ▸ hy) (by
        intro g hg x hx
        show T (σ' g x) ∈ S'
        rw [h g (Kset_sub hg)]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T.symm x ∈ S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H) := by
        show T (T.symm x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← e] at hx
      exact hx
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hw
    have := wt_transfer T.symm (symm_inter T h) hw
    refine h5 μ x hx (by rintro rfl; simp at h0) ?_
    simpa using this

theorem isDS_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {lam : Fin n → ℝ}
    (hσ : IsDS ε lam σ) : IsDS ε lam σ' := by
  obtain ⟨c1, c2, ⟨⟨r1, r2⟩, r3, r4⟩, c4, c5, ⟨S, hS⟩, c7⟩ := hσ
  have h' := symm_inter T h
  have e : ∀ g ∈ UJset ε, ∀ v, σ' g v = T.symm (σ g (T v)) := by
    intro g hg v; rw [← h g hg]; simp
  have one : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  refine ⟨c1, c2, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, ktype_transfer T.symm h' hS⟩,
    fun μ S' hS' => c7 μ _ (ktype_transfer T h hS')⟩
  · ext v; rw [e 1 one, r1]; simp
  · intro a ha b hb
    ext v
    rw [ContinuousLinearMap.comp_apply, e _ (UJ_mul ha hb), e a ha, e b hb, r2 a ha b hb]; simp
  · intro g hg v
    rw [e g hg]; simp [r3 g hg]
  · intro v
    exact (T.symm.continuous.comp_continuousOn (r4 (T v))).congr fun g hg => e g hg v
  · intro S' hcl hst
    rcases c4 (S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H)) (hcl.preimage T.symm.continuous) (by
        intro g hg x hx
        show T.symm (σ g x) ∈ S'
        rw [h' g hg]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T x ∈ S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H) := by
        show T.symm (T x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      rw [eq_top_iff]
      intro x _
      have : T x ∈ S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H) := by rw [e]; trivial
      have h2 : T.symm (T x) ∈ S' := this
      simpa using h2
  · intro v w
    have : coefOn (ε := ε) σ' v w = coefOn (ε := ε) σ (T v) (T w) := by
      funext g
      show ⟪w, σ' (umat g) v⟫_ℂ = ⟪T w, σ (umat g) (T v)⟫_ℂ
      rw [← h _ g.2, T.inner_map_map]
    rw [this]; exact c5 _ _

theorem isDS_conj {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) {u u' : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ UJset ε) (hu' : u' ∈ UJset ε) (h1 : u * u' = 1) :
    IsDS ε lam (fun g => σ (u' * g * u)) := by
  obtain ⟨⟨r1, r2⟩, r3, -⟩ := hσ.2.2.1
  have hs : ∀ v, σ u (σ u' v) = v := by
    intro v
    have := r2 u hu u' hu'
    rw [h1, r1] at this
    simpa using (congrArg (fun A : H →L[ℂ] H => A v) this).symm
  let T : H ≃ₗᵢ[ℂ] H := LinearIsometryEquiv.ofSurjective
    { toLinearMap := (σ u : H →ₗ[ℂ] H), norm_map' := r3 u hu } (fun v => ⟨σ u' v, hs v⟩)
  refine isDS_transfer T ?_ hσ
  intro g hg v
  show σ u (σ (u' * g * u) v) = σ g (σ u v)
  rw [r2 _ (UJ_mul hu' hg) u hu, r2 u' hu' g hg]
  simp [hs]

lemma card_even (r : ℕ) : ((range (2 * r + 2)).filter fun m => m % 2 = 0).card = r + 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 2 * (r + 1) + 2 = 2 * r + 2 + 1 + 1 by ring, range_add_one, range_add_one, filter_insert,
      filter_insert, if_neg (by omega), if_pos (by omega), card_insert_of_notMem (by simp), ih]

lemma card_signs (k r : ℕ) (hk : 1 ≤ k) :
    (univ.filter fun i => PI.BesselPeriodGGP.eps48 k r i = true).card = k + r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [card_filter]
  have h : ∀ i : Fin (2 * r + (j + 1) + 1), (if PI.BesselPeriodGGP.eps48 (j + 1) r i = true then 1 else 0) =
      (fun m : ℕ => if m < j ∨ (m - j) % 2 = 0 then 1 else 0) i.val := by
    intro i
    by_cases h1 : i.val < j <;> simp [PI.BesselPeriodGGP.eps48, h1]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < j ∨ (m - j) % 2 = 0 then 1 else 0),
    show 2 * r + (j + 1) + 1 = j + (2 * r + 2) by ring, sum_range_add]
  have a : ∑ m ∈ range j, (if m < j ∨ (m - j) % 2 = 0 then 1 else 0) = j := by
    rw [sum_congr rfl (g := fun _ => 1) (fun m hm => if_pos (Or.inl (mem_range.1 hm)))]; simp
  have b : ∑ m ∈ range (2 * r + 2), (if j + m < j ∨ (j + m - j) % 2 = 0 then 1 else 0) = r + 1 := by
    rw [← card_even r, card_filter]
    refine sum_congr rfl fun m _ => ?_
    simp
  rw [a, b]; ring

theorem cayley_exists_and_any : ∀ (k r : ℕ), (1 ≤ k → ∃ Q, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q) ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q, PI.UpqRep.IsCayleyU k r ε Q → PI.UpqRep.IsDS ε mu (fun g => R.σ (Q⁻¹ * g * Q)) := by
  intro k r
  refine ⟨fun hk => (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff k r _).2 (card_signs k r hk), ?_⟩
  rintro ε mu R ⟨-, ⟨P, ⟨⟨-, hP⟩, hPu⟩, hD⟩, -⟩ Q ⟨⟨-, hQ⟩, hQu⟩
  have p1 : Pᴴ * P = 1 := (Matrix.mem_unitaryGroup_iff').1 hPu
  have p2 : P * Pᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hPu
  have q1 : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQu
  have q2 : Q * Qᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hQu
  have pi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv p1
  have qi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have gen : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, B * Bᴴ = 1 →
      Aᴴ * Jm ε * A = Bᴴ * Jm ε * B → A * Bᴴ ∈ UJset ε := by
    intro A B hB hAB
    show (A * Bᴴ)ᴴ * Jm ε * (A * Bᴴ) = Jm ε
    calc (A * Bᴴ)ᴴ * Jm ε * (A * Bᴴ) = B * (Aᴴ * Jm ε * A) * Bᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (B * Bᴴ) * Jm ε * (B * Bᴴ) := by rw [hAB]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hB]; simp
  have key := isDS_conj hD (gen Q P p2 (hQ.trans hP.symm)) (gen P Q q2 (hP.trans hQ.symm)) (by
    calc Q * Pᴴ * (P * Qᴴ) = Q * (Pᴴ * P) * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [p1, Matrix.mul_one, q2])
  have e : (fun g => R.σ (Q⁻¹ * g * Q)) = fun g => R.σ (P⁻¹ * (P * Qᴴ * g * (Q * Pᴴ)) * P) := by
    funext g
    congr 1
    rw [pi, qi]
    calc Qᴴ * g * Q = (Pᴴ * P) * Qᴴ * g * Q * (Pᴴ * P) := by rw [p1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact key

end GlobalTheory.CayleyChoice
end
end Gp91
end
