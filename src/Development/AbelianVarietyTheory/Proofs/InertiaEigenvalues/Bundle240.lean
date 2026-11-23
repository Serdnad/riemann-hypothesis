module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle230
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle227
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem charpoly_coeff_mem_of_charPolyIn {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (h : CharPolyIn T rep) (g : Γ) (j : ℕ) :
    (fun x => (mat (rep x) g).charpoly.coeff j) ∈ T := by
  unfold CharPolyIn at h
  rcases subsingleton_or_nontrivial O with hO | hO
  · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact T.zero_mem
  · by_cases hj : j ≤ n
    · have e : (fun x => (mat (rep x) g).charpoly.coeff j) =
          fun x => (mat (rep x) g).charpolyRev.coeff (n - j) := by
        funext x
        rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin, Polynomial.revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
      rw [e]
      exact h g (n - j)
    · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := by
        funext x
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        omega
      rw [hz]
      exact T.zero_mem

private theorem coeff_det_generic_sum_eval {X O : Type} [CommRing O] {n m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O) (x : X) (d : Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d =
    (AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) d : X → O) x := by
  set φ : MvPolynomial (Fin m) (X → O) →+* MvPolynomial (Fin m) O :=
    MvPolynomial.map (Pi.evalRingHom (fun _ => O) x) with hφ
  have h1 : φ.mapMatrix (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Matrix.ext fun i j => ?_
    simp [hφ]
  rw [← h1, ← RingHom.map_det, hφ, MvPolynomial.coeff_map]
  rfl

theorem coeff_det_generic_sum_mem_of_inRing :
    ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O))
      (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep →
      ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) →
      ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T := by
  intro Γ X O _ _ n T rep hT m a ha d
  classical

  let T' : Subring (MvPolynomial (Fin m) (X → O)) := (MvPolynomial.map T.val.toRingHom).range
  have hmemT : ∀ p ∈ T', ∀ e, AddMonoidAlgebra.coeff p e ∈ T := by
    intro p hp e
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hp
    rw [MvPolynomial.coeff_map]
    exact (AddMonoidAlgebra.coeff q e).2
  have hC : ∀ f ∈ T, (MvPolynomial.C f : MvPolynomial (Fin m) (X → O)) ∈ T' := fun f hf =>
    RingHom.mem_range.2 ⟨MvPolynomial.C ⟨f, hf⟩, by simp⟩
  have hX : ∀ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) ∈ T' := fun k =>
    RingHom.mem_range.2 ⟨MvPolynomial.X k, by simp⟩

  let M : Γ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)) :=
    fun h => Matrix.of fun i j => MvPolynomial.C (fun y => mat (rep y) h i j)
  have hmul : ∀ A ∈ Set.range M, ∀ B ∈ Set.range M, A * B ∈ Set.range M := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    refine Matrix.ext fun i j => ?_

    simp only [M, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← map_sum]
    congr 1
    funext y
    simp [mat, Matrix.mul_apply, Finset.sum_apply]
  have hchar : ∀ A ∈ Set.range M, ∀ j, A.charpoly.coeff j ∈ T' := by
    rintro _ ⟨h, rfl⟩ j
    have hP : M h = (Matrix.of fun i j => fun y => mat (rep y) h i j).map MvPolynomial.C := by
      refine Matrix.ext fun i j => ?_
      rfl
    rw [hP, Matrix.charpoly_map, Polynomial.coeff_map]
    apply hC
    have e : (Matrix.of fun i j => fun y => mat (rep y) h i j).charpoly.coeff j =
        fun y => (mat (rep y) h).charpoly.coeff j := by
      funext y
      have hm : (Matrix.of fun i j => fun y => mat (rep y) h i j).map (Pi.evalRingHom (fun _ => O) y) =
          mat (rep y) h := by
        refine Matrix.ext fun i j => ?_
        rfl
      have e' := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j)
        (Matrix.charpoly_map (Matrix.of fun i j => fun y => mat (rep y) h i j) (Pi.evalRingHom (fun _ => O) y))
      rw [hm] at e'
      simp only [Polynomial.coeff_map] at e'
      exact e'.symm
    rw [e]
    exact charpoly_coeff_mem_of_charPolyIn T rep hT h j

  have hlift : ∀ b : X → Matrix (Fin n) (Fin n) O, b ∈ Submodule.span O (gens T rep) →
      (Matrix.of fun i j => MvPolynomial.C (fun y => b y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)))
        ∈ Submodule.span T' (Set.range M) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, hf, h, rfl⟩ := hb
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (fun x => f x • mat (rep x) h) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C f, hC f hf⟩ : T') • M h := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, M, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
    | zero =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (0 : X → Matrix (Fin n) (Fin n) O) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = 0 := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
        exact map_zero _
      rw [e]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (b + c) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) +
            Matrix.of (fun i j => MvPolynomial.C (fun y => c y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Matrix.add_apply, ← map_add (f := _)]
        rfl
      rw [e]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (r • b) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C (algebraMap O (X → O) r), hC _ (T.algebraMap_mem r)⟩ : T') •
            Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ hb
  have hB : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) ∈ Submodule.span T' (Set.range M) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    have := Submodule.smul_mem (Submodule.span T' (Set.range M)) (⟨MvPolynomial.X k, hX k⟩ : T')
      (hlift (a k) ((inRing_iff_mem_span T rep (a k)).1 (ha k)))
    exact this
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.1 hB
  have hdet := Amitsur.det_sum_smul_mem T' (Set.range M) hmul hchar Finset.univ
    (fun i => (f i : MvPolynomial (Fin m) (X → O))) (fun i => (g i).1)
    (fun i => (f i).2) (fun i => (g i).2)
  have hsum : (∑ i ∈ Finset.univ, (f i : MvPolynomial (Fin m) (X → O)) • (g i).1) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)) := by
    rw [← hfg]
    rfl
  rw [hsum] at hdet
  have key : (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) =
      AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) d :=
    funext fun x => coeff_det_generic_sum_eval a x d
  rw [key]
  exact hmemT _ hdet d

end GlobalTheory.SpanRing
end

section

noncomputable section

namespace GlobalTheory.SpanBlockAction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section

variable {O : Type} [CommRing O] {n r t : ℕ}

def ActsAs (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (M : Matrix (Fin n) (Fin n) O) (P : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Prop :=
  ∀ u, e ((M.map (toFr O)).mulVec u) =
    ((P.map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (d c) * (e u).2 c)

theorem map_smul_toFr {k : ℕ} (c : O) (M : Matrix (Fin k) (Fin k) O) :
    (c • M).map (toFr O) = toFr O c • M.map (toFr O) := by
  ext i j
  simp [smul_eq_mul]

theorem map_sum_toFr {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) O) :
    (∑ i, M i).map (toFr O) = ∑ i, (M i).map (toFr O) := by
  ext i j
  simp [Matrix.sum_apply]

private theorem sum_mulVec_eq {K : Type} [CommRing K] {k m : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (∑ i, A i).mulVec v = ∑ i, (A i).mulVec v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem smul_mulVec_eq' {K : Type} [CommRing K] {k : ℕ} (a : K) (A : Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (a • A).mulVec v = a • A.mulVec v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem actsAs_sum
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    {m : ℕ} (c : Fin m → O) (M : Fin m → Matrix (Fin n) (Fin n) O) (P : Fin m → Matrix (Fin r) (Fin r) O)
    (d : Fin m → Fin t → O) (h : ∀ k, ActsAs e (M k) (P k) (d k)) :
    ActsAs e (∑ k, c k • M k) (∑ k, c k • P k) (fun j => ∑ k, c k * d k j) := by
  unfold ActsAs at h ⊢
  intro u
  rw [map_sum_toFr, map_sum_toFr]

  simp only [map_smul_toFr, sum_mulVec_eq, smul_mulVec_eq', map_sum, map_smul, h]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Algebra.smul_def]

theorem ActsAs.unique
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    {M : Matrix (Fin n) (Fin n) O} {P P' : Matrix (Fin r) (Fin r) O} {d d' : Fin t → O}
    (h : ActsAs e M P d) (h' : ActsAs e M P' d') : P = P' := by
  have hv : ∀ v : Fin r → FractionRing O, (P.map (toFr O)).mulVec v = (P'.map (toFr O)).mulVec v := by
    intro v
    have h1 := h (e.symm (v, 0))
    have h2 := h' (e.symm (v, 0))
    rw [h1] at h2
    simpa using congrArg Prod.fst h2
  have hm : P.map (toFr O) = P'.map (toFr O) := by
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v
  ext i j
  apply IsFractionRing.injective O (FractionRing O)
  have := congrFun (congrFun hm i) j
  simpa [toFr] using this

end

theorem actsAs_mat {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    {σ : Γ →* GL (Fin n) O} {ρ : Γ →* GL (Fin r) O} {χ : ℕ → (Γ →* Oˣ)}
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    (h : IsDecomp (t := t) σ ρ χ e) (g : Γ) :
    ActsAs e (mat σ g) (mat ρ g) (fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)) := by
  unfold ActsAs
  intro u
  simpa [overK, matRep, mapM, mat] using h g u

theorem exists_block_action {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ))
    (π : X)
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (hspan : Submodule.span O (Set.range (mat ρ)) = ⊤) (hdec : IsDecomp (t := t) (rep π) ρ χ e) :
    ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O)
      (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O),
      (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) =
        (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧
      ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  classical
  have hact : ∀ M ∈ Submodule.span O (Set.range (mat (rep π))),
      ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e M p.1 p.2 := by
    intro M hM
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.mp hM
    have hg : ∀ k, ∃ γ, mat (rep π) γ = (g k : Matrix (Fin n) (Fin n) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), ?_⟩
    have := actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
      (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
    simpa only [hγ] using this
  refine ⟨fun a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.1 else 0,
    fun j a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.2 j else 0, ?_, ?_⟩
  · intro a ha u
    have hex := hact (a π) (eval_mem_span ha π)
    simp only [dif_pos hex]
    exact hex.choose_spec u
  · intro P
    have hP : P ∈ Submodule.span O (Set.range (mat ρ)) := hspan ▸ Submodule.mem_top
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hP
    have hg : ∀ k, ∃ γ, mat ρ γ = (g k : Matrix (Fin r) (Fin r) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨∑ k, c k • (fun x => mat (rep x) (γ k)), ?_, ?_⟩
    · exact inRing_sum _ fun k _ => inRing_smul (c k) (inRing_mat (γ k))
    · have hev : (∑ k, c k • (fun x => mat (rep x) (γ k))) π = ∑ k, c k • mat (rep π) (γ k) := by
        simp [Finset.sum_apply]
      have hA : ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) (∑ k, c k • mat ρ (γ k))
          (fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) := by
        rw [hev]
        exact actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
          (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
      have hex : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O),
          ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) p.1 p.2 :=
        ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), hA⟩
      simp only [dif_pos hex]
      rw [ActsAs.unique hex.choose_spec hA, ← hsum]
      simp only [hγ]

end GlobalTheory.SpanBlockAction

end
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem ker_of_linApprox : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l))
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), IsSSRep r → LinApprox r C → ∀ s : Γ, (∀ ρ ∈ C, ρ s = 1) → r s = 1 := by
  intro l _ Γ _ a r C hss hC s hs
  have htr : ∀ g, trc r (s * g) = trc r g := by
    intro g
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨t, c, ht, hb⟩ := hC (ε / 2) (by positivity)
    have hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g := by
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp [trc, map_mul, hs ρ (ht hρ)]
    rw [dist_eq_norm]
    calc ‖trc r (s * g) - trc r g‖
        = ‖(trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)) - (trc r g - ∑ ρ ∈ t, c ρ * trc ρ g)‖ := by
          rw [hsum]; congr 1; ring
      _ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)
      _ = ε := by ring
  set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR
  have hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R) := by
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_
    have : R 1 = 1 := by simp [hR]
    rw [← this]; exact Submodule.subset_span ⟨1, rfl⟩
  have h0 := GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by
    have := htr g
    simp only [trc, map_mul, Units.val_mul] at this
    rw [sub_mul, one_mul, Matrix.trace_sub]
    simpa [hR] using sub_eq_zero.2 this)
  ext i j
  have := congrFun (congrFun (sub_eq_zero.1 h0) i) j
  simpa [hR] using this

end GlobalTheory.Cong
end

section

open GlobalTheory.UnitLemma Polynomial Filter Topology

namespace GlobalTheory.UnitLemma

theorem unitaryLimit : UnitaryLimit := by
  have L0 := GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
  have S1 := GlobalTheory.T.fullLattice_sandwich_between_integral_elements
  have S2 := GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho
  have S3 := GlobalTheory.T.UU_eq_sum_over_torus_orbits
  have S4 := GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality
  have S5 := GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box
  have S6 := GlobalTheory.T.tendsto_ratio_box_counts_prod_one

  intro K B hB a ha x hx
  classical
  obtain ⟨r, φ, c, hsurj, hker, hc, hint⟩ := S4 K B hB a ha
  have hrho : ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) :=
    S5 K B a r φ c hsurj hker hint
  have hpos : ∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j) := fun j => by
    rw [hrho]; exact Finset.prod_pos fun i _ => by omega
  obtain ⟨hfin, hstab⟩ := L0 K B hB.2 x hx.1 hx.2
  choose m hm using fun o : Orb K.O B.T (B.X x) => S1 K B hB a ha _ (Quot.out o).2.1
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  set M := Finset.univ.sup m with hMdef
  have hmM : ∀ o, m o ≤ M := fun o => Finset.le_sup (Finset.mem_univ o)
  have key := fun (k : ℕ) (hk : M ≤ k) (o : Orb K.O B.T (B.X x)) =>
    S2 K B _ (hstab _ (Quot.out o).2).1 (hstab _ (Quot.out o).2).2 a hpos M k hk
      (hm o M (hmM o)).1 (hm o M (hmM o)).2
  have hUU : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) =
      ∑ o : Orb K.O B.T (B.X x), (Nat.card {L' : Submodule K.O B.A // (∃ t ∈ B.T, L' = mulLat K.O (t : B.A) (Quot.out o).1) ∧
        algebraMap K.O B.A a ^ k ∈ L'} : ℝ) := by
    intro k hk
    rw [S3 K B x _ hfin (fun o => (key k hk o).1), finsum_eq_sum_of_fintype]
    push_cast; rfl
  have hN : (B.N x : ℝ) = ∑ o : Orb K.O B.T (B.X x),
      (((stabLat K.O (Quot.out o).1 ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℝ) := by
    unfold InvAlg.N orbSum
    rw [finsum_eq_sum_of_fintype]
    push_cast
    simp
  have hlo : ∀ k, M ≤ k → (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) ≤ B.UU x (algebraMap K.O B.A a ^ k) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.1
  have hhi : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) ≤ (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.2
  have hposR : ∀ j, (0 : ℝ) < B.rho (algebraMap K.O B.A a ^ j) := fun j => by exact_mod_cast hpos j
  have hup : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have := (S6 r c M).const_mul (B.N x : ℝ)
    rw [mul_one] at this
    refine this.congr fun k => ?_
    rw [hrho, hrho, mul_div_assoc]
  have hdown : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have h1 := ((S6 r c M).inv₀ one_ne_zero).comp (tendsto_sub_atTop_nat M)
    have h2 := h1.const_mul (B.N x : ℝ)
    rw [inv_one, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    simp only [Function.comp_apply, inv_div]
    rw [Nat.sub_add_cancel hk, hrho, hrho, mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdown hup ?_ ?_
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hlo k hk) (hposR k).le
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hhi k hk) (hposR k).le

end GlobalTheory.UnitLemma
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) → (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  first | exact @GlobalTheory.BK.PhiMod.mem_MM_of_series | exact GlobalTheory.BK.PhiMod.mem_MM_of_series | (intros; apply GlobalTheory.BK.PhiMod.mem_MM_of_series <;> assumption)
end
