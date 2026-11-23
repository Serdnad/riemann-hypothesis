module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle001
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LowKAddStrictAnti
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def matRep (n n' : ℕ) :
    Representation ℂ (GL (Fin n) ℂ × GL (Fin n') ℂ) (MvPolynomial (Fin n' × Fin n) ℂ) where
  toFun p := (sub ((p.2 : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (p.1 : Matrix (Fin n) (Fin n) ℂ))ᵀ).toLinearMap
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, Units.val_one, Matrix.one_kronecker_one, Matrix.transpose_one,
      LFocks_sub_one]
    rfl
  map_mul' p q := by
    simp only [Prod.snd_mul, Prod.fst_mul, Units.val_mul, Matrix.mul_kronecker_mul, Matrix.transpose_mul]
    rw [← LFocks_sub_comp]
    rfl

theorem matRep_apply {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (g, h) f = sub ((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ f := rfl

theorem matRep_X {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (a : Fin n') (s : Fin n) :
    matRep n n' (g, h) (X (a, s)) = ∑ b, ∑ t, C (h b a * g t s) * X (b, t) := by
  simp [matRep_apply, sub, Fintype.sum_prod_type]

theorem eval_matRep {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (x : Matrix (Fin n') (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    eval (fun v => x v.1 v.2) (matRep n n' (g, h) f) =
      eval (fun v => ((h : Matrix (Fin n') (Fin n') ℂ)ᵀ * x * (g : Matrix (Fin n) (Fin n) ℂ)) v.1 v.2) f := by
  rw [matRep_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, eval_X]
    congr 1

    simp only [sub, aeval_X, map_sum, map_mul, eval_C, eval_X, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem matRep_one_left {n n' : ℕ} (h : GL (Fin n') ℂ) (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (1, h) f = rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f := by
  have : sub ((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ ((1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ =
      rowAct ℂ (n := n) (h : Matrix (Fin n') (Fin n') ℂ)ᵀ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply, this]

abbrev Part (m : ℕ) : Type := {a : Fin m → ℕ // Antitone a}

def pad {m : ℕ} (N : ℕ) (a : Part m) : DomWeight N where
  w i := (rowNu (r := N) a.1 i : ℕ)
  anti i j hij := by
    have hij' : i.val ≤ j.val := hij
    simp only [rowNu, Nat.cast_le]
    split_ifs with h1 h2
    · exact a.2 (show (⟨i.val, h2⟩ : Fin m) ≤ ⟨j.val, h1⟩ from hij')
    · omega
    · exact Nat.zero_le _
    · exact le_rfl

theorem pad_w_of_lt {m N : ℕ} (a : Part m) (i : Fin N) (hi : i.val < m) : (pad N a).w i = a.1 ⟨i.val, hi⟩ := by
  simp [pad, rowNu, hi]

theorem pad_w_of_le {m N : ℕ} (a : Part m) (i : Fin N) (hi : m ≤ i.val) : (pad N a).w i = 0 := by
  simp [pad, rowNu, Nat.not_lt.2 hi]

theorem pad_injective {m N : ℕ} (h : m ≤ N) : Function.Injective (pad (m := m) N) := by
  intro a b e
  refine Subtype.ext (funext fun i => ?_)
  have h1 := pad_w_of_lt a (Fin.castLE h i) i.2
  have h2 := pad_w_of_lt b (Fin.castLE h i) i.2
  rw [e, h2] at h1
  exact_mod_cast h1.symm

section Along

variable {H H' : Type} [Group H] [Group H'] {n n' : ℕ} (ι : H →* GL (Fin n) ℂ) (ι' : H' →* GL (Fin n') ℂ)

def polyRep : Representation ℂ (H × H') (MvPolynomial (Fin n' × Fin n) ℂ) := (matRep n n').comp (ι.prodMap ι')

def pieceRep (a : Part (min n n')) :
    Representation ℂ (H × H') (nablaSq ℂ n (pad n a) ⊗[ℂ] nablaSq ℂ n' (pad n' a)) :=
  Representation.tprod ((smallRep ι (pad n a)).comp (MonoidHom.fst H H'))
    ((smallRep ι' (pad n' a)).comp (MonoidHom.snd H H'))

@[simp] theorem pieceRep_tmul (a : Part (min n n')) (p : H × H') (v : nablaSq ℂ n (pad n a))
    (w : nablaSq ℂ n' (pad n' a)) :
    pieceRep ι ι' a p (v ⊗ₜ w) = smallRep ι (pad n a) p.1 v ⊗ₜ smallRep ι' (pad n' a) p.2 w := by
  simp [pieceRep]

def IrreducibleDistinct (m : ℕ) : Prop :=
  (∀ a : Part m, (smallRep ι (pad n a)).IsIrreducible) ∧
    ∀ a b : Part m, Nonempty ((smallRep ι (pad n a)).Equiv (smallRep ι (pad n b))) → a = b

def DualAlong : Prop :=
  Nonempty ((Representation.directSum fun a : Part (min n n') => pieceRep ι ι' a).Equiv (polyRep ι ι')) ∧
    IrreducibleDistinct ι (min n n') ∧ IrreducibleDistinct ι' (min n n')

end Along

theorem irreducibleDistinct_unitary {m n : ℕ} (h : m ≤ n) : IrreducibleDistinct (unitaryIncl n) m := by
  refine ⟨fun a => isIrreducible_smallRep_unitary n _, fun a b ⟨e⟩ => ?_⟩
  by_contra hne
  let φ : (sqRep ℂ n (pad n a)).IntertwiningMap (sqRep ℂ n (pad n b)) :=
    ⟨e.toLinearMap, fun g => LinearMap.ext fun f => intertwining_gl_of_unitary n _ _ e.toIntertwiningMap g f⟩
  obtain ⟨f, hf, h0⟩ := exists_ne_zero_map_eq_zero_of_weight_ne n _ _ (fun e' => hne (pad_injective h e')) φ
  exact hf (e.toLinearEquiv.map_eq_zero_iff.1 h0)

theorem irreducibleDistinct_gl {m n : ℕ} (h : m ≤ n) : IrreducibleDistinct (MonoidHom.id (GL (Fin n) ℂ)) m := by
  refine ⟨fun a => ?_, fun a b ⟨e⟩ => (irreducibleDistinct_unitary h).2 a b
    ⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl n u)⟩⟩
  have hU := isIrreducible_smallRep_unitary n (pad n a)
  have hnt : Nontrivial (Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) (pad n a))) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation (smallRep (unitaryIncl n) (pad n a)) :=
    ⟨S.toSubmodule, fun u _ hv => S.apply_mem_toSubmodule (unitaryIncl n u) hv⟩
  rcases eq_bot_or_eq_top T with e | e
  · exact Or.inl (Subrepresentation.ext (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.ext (congrArg Subrepresentation.toSubmodule e :))

end GlobalTheory.GLDuality

namespace GlobalTheory.Published

open GlobalTheory.GLDuality

def GLHoweDuality : Prop :=
  ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' →
    DualAlong (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) ∧
      DualAlong (unitaryIncl n) (unitaryIncl n')

theorem glHoweDuality_of_equiv
    (h : ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → Nonempty ((Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).Equiv
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))))) : GLHoweDuality := by
  intro n n' hn hn'
  obtain ⟨e⟩ := h n n' hn hn'
  refine ⟨⟨⟨e⟩, irreducibleDistinct_gl (min_le_left _ _), irreducibleDistinct_gl (min_le_right _ _)⟩,
    ⟨⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl n u.1, unitaryIncl n' u.2)⟩,
      irreducibleDistinct_unitary (min_le_left _ _), irreducibleDistinct_unitary (min_le_right _ _)⟩⟩

end GlobalTheory.Published
end
end

section

open Matrix Finset Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesHermitianUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (J P P' : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' →
      Pᴴ * Formalism.REAL.Jm ε * P = J → P'ᴴ * Formalism.REAL.Jm ε * P' = J →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w,
        U (σ' (P' * g * P'⁻¹) w) = σ (P * g * P⁻¹) (U w)

namespace HermitianUnique

variable {n : ℕ} {ε : Fin n → Bool} {J P P' : Matrix (Fin n) (Fin n) ℂ}

theorem frame_mem (hP' : IsUnit P') (h : Pᴴ * Formalism.REAL.Jm ε * P = J) (h' : P'ᴴ * Formalism.REAL.Jm ε * P' = J)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) : P * g * P'⁻¹ ∈ UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP'
  have e1 : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * J * g = J := hg
  show (P * g * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P'⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P'⁻¹)
      = P'⁻¹ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P'⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P'⁻¹ᴴ * (P'ᴴ * Formalism.REAL.Jm ε * P') * P'⁻¹ := by rw [h, hg', h']
    _ = (P' * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P' * P'⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e1]; simp

theorem isHCParam_of_isDS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {lam : Fin n → ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hl : StrictAnti lam) (h : IsDS ε lam σ) :
    Formalism.QuantumDeterminants.IsHCParam lam := by
  refine ⟨hl, fun a => ?_⟩
  obtain ⟨-, -, ⟨⟨h1, -⟩, -, -⟩, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩ := h
  obtain ⟨m, hm⟩ := GlobalTheory.DiscreteSeriesTest.wt_int (ε := ε) (μ := PI.UpqRep.lowK ε lam) h1 hv0 hv a
  have h2 := GlobalTheory.DiscreteSeriesTest.lowK_add ε lam a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, PI.UpqRep.rhoC] at h2
  refine ⟨m + (univ.filter fun b => a < b ∧ ε b = ε a).card - (univ.filter fun b => b < a ∧ ε b = ε a).card
    - (n - 1) + a, ?_⟩
  push_cast
  linarith

end HermitianUnique


open HermitianUnique in
theorem discreteSeriesHermitianUnique_iff : DiscreteSeriesHermitianUnique ↔ DiscreteSeriesUpqUnique := by
  constructor
  · intro h n ε lam hl H H' _ _ _ _ σ σ' hσ hσ'
    obtain ⟨U, hU⟩ := h n ε lam hl (Formalism.REAL.Jm ε) 1 1 isUnit_one isUnit_one (by simp) (by simp) H' H σ' σ hσ' hσ
    refine ⟨U, fun g hg v => ?_⟩
    simpa using hU g hg v
  · intro h n ε lam hl J P P' hP hP' hJ hJ' H H' _ _ _ _ σ σ' hσ hσ'
    obtain ⟨U, hU⟩ := h n ε lam hl H' H σ' σ hσ' hσ
    obtain ⟨-, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
    have e : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
    have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
    have e' : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP')
    have one : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH J := by
      show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J * 1 = J
      simp
    have ha : P * 1 * P'⁻¹ ∈ UJset ε := frame_mem hP' hJ hJ' one
    have hb : P' * 1 * P⁻¹ ∈ UJset ε := frame_mem hP hJ' hJ one
    rw [Matrix.mul_one] at ha hb
    have hsurj : Function.Surjective
        (⟨(σ (P * P'⁻¹) : H →ₗ[ℂ] H), hiso _ ha⟩ : H →ₗᵢ[ℂ] H) := by
      intro v
      refine ⟨σ (P' * P⁻¹) v, ?_⟩
      have e3 : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹, e', Matrix.one_mul, e2]
      have := hmul _ ha _ hb
      rw [e3, h1] at this
      exact (congrArg (fun T : H →L[ℂ] H => T v) this).symm
    refine ⟨U.trans (LinearIsometryEquiv.ofSurjective _ hsurj), fun g hg w => ?_⟩
    show σ (P * P'⁻¹) (U (σ' (P' * g * P'⁻¹) w)) = σ (P * g * P⁻¹) (σ (P * P'⁻¹) (U w))
    have hg' := frame_mem hP' hJ' hJ' hg
    have hg1 := frame_mem hP hJ hJ hg
    have k1 := congrArg (fun T : H →L[ℂ] H => T (U w)) (hmul _ ha _ hg')
    have k2 := congrArg (fun T : H →L[ℂ] H => T (U w)) (hmul _ hg1 _ ha)
    have k3 : P * P'⁻¹ * (P' * g * P'⁻¹) = P * g * P⁻¹ * (P * P'⁻¹) := by
      calc P * P'⁻¹ * (P' * g * P'⁻¹) = P * (P'⁻¹ * P') * g * P'⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * g * (P⁻¹ * P) * P'⁻¹ := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
        _ = P * g * P⁻¹ * (P * P'⁻¹) := by simp only [Matrix.mul_assoc]
    rw [hU _ hg']
    rw [k3] at k1
    exact k1.symm.trans k2

theorem discreteSeriesHermitianUnique_of_classification (h : GlobalTheory.DSId.DSClass) : DiscreteSeriesHermitianUnique :=
  discreteSeriesHermitianUnique_iff.2 (discreteSeriesUpqUnique_of_classification h)

theorem DiscreteSeriesHermitianUnique.exists_intertwiner (h : DiscreteSeriesHermitianUnique) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M M' : DSModel V S) :
    ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U τ (M'.rep τ g w) = M.rep τ g (U τ w) := by
  have key : ∀ τ, ∃ U : M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U (M'.rep τ g w) = M.rep τ g (U w) := by
    intro τ
    obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) (M'.enum τ)
    exact h _ (M.ε τ) (M.lam τ) (HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) (M'.fr τ)
      (M.fr_unit τ) (M'.fr_unit τ) (M.fr_gram τ) (he ▸ M'.fr_gram τ) _ _ (M.σ τ) (M'.σ τ) (M.ds τ)
      (hl ▸ he ▸ M'.ds τ)
  choose U hU using key
  exact ⟨U, hU⟩

theorem DiscreteSeriesUpqUnique.exists_intertwiner (h : DiscreteSeriesUpqUnique) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M M' : DSModel V S) :
    ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U τ (M'.rep τ g w) = M.rep τ g (U τ w) :=
  (discreteSeriesHermitianUnique_iff.2 h).exists_intertwiner M M'

end GlobalTheory.Published
end
end
