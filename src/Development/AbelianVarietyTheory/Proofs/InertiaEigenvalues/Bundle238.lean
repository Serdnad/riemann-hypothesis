module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Mathlib.LinearAlgebra.Charpoly.Basic

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.IdemConstRank

theorem charpoly_of_idem {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M * M = M) :
    ∃ b : ℕ, M.charpoly = (X - 1) ^ M.rank * X ^ b := by
  classical
  have hf : IsIdempotentElem (Matrix.toLin' M) := by
    have h2 : Matrix.toLin' (M * M) = Matrix.toLin' M := by rw [h]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  let e := Submodule.prodEquivOfIsCompl _ _ hc
  have key : e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M)))) = Matrix.toLin' M := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add (f := _),
      LinearMap.mem_ker.mp y.2.2, (LinearMap.IsIdempotentElem.mem_range_iff hf).mp y.1.2]
    simp
  refine ⟨Module.finrank K (LinearMap.ker (Matrix.toLin' M)), ?_⟩
  have hcp : M.charpoly = (e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M))))).charpoly := by
    rw [key, Matrix.charpoly_toLin']
  rw [hcp, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap,
    LinearMap.charpoly_one, LinearMap.charpoly_zero, ← Matrix.finrank_range_mulVecLin, ← Matrix.toLin'_apply']

theorem residue_eq {X O : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O))
    [IsLocalRing T] (f : X → O) (hf : f ∈ T) (x y : X) :
    IsLocalRing.residue O (f x) = IsLocalRing.residue O (f y) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  by_contra hne
  have hu : IsUnit (f x - f y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
    exact hne
  have ev : ∀ z : X, ∀ t : T, IsUnit t → IsUnit ((t : X → O) z) := fun z t ht =>
    ht.map ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  let g : T := ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _)⟩
  let g' : T := algebraMap O T (f x - f y) - g
  have hg : g ∈ nonunits T := fun hg => by
    have := ev y g hg
    simp [g] at this
  have hg' : g' ∈ nonunits T := fun hg => by
    have := ev x g' hg
    simp [g', g] at this
  have hsum : g + g' = algebraMap O T (f x - f y) := by
    simp [g']
  exact IsLocalRing.nonunits_add hg hg' (hsum ▸ hu.map (algebraMap O T))

theorem rootMultiplicity_one {k : Type} [Field k] (a b : ℕ) :
    rootMultiplicity (1 : k) ((X - 1) ^ a * X ^ b) = a := by
  have h1 : ((Polynomial.X : k[X]) - 1) ^ a = (Polynomial.X - Polynomial.C 1) ^ a := by
    rw [map_one]
  have hne : ((Polynomial.X : k[X]) - Polynomial.C 1) ^ a * Polynomial.X ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1)) (pow_ne_zero _ X_ne_zero)
  rw [h1, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero, add_zero]
  simp [IsRoot]

theorem rank_eq_rootMultiplicity {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) O) (h : M * M = M) :
    (M.map (toFr O)).rank = rootMultiplicity 1 (M.charpoly.map (IsLocalRing.residue O)) := by
  obtain ⟨b, hb⟩ := charpoly_of_idem (M.map (toFr O)) (by rw [← Matrix.map_mul, h])
  rw [Matrix.charpoly_map] at hb
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  have hM : M.charpoly = ((Polynomial.X : O[X]) - 1) ^ (M.map (toFr O)).rank * Polynomial.X ^ b := by
    apply Polynomial.map_injective _ hinj
    rw [hb]
    simp
  rw [hM]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one]
  exact (rootMultiplicity_one _ _).symm

theorem rank_const : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (T : Subalgebra O (X → O)) (e : X → Matrix (Fin n) (Fin n) O), IsLocalRing T → e * e = e → (∀ j : ℕ, (fun x => (e x).charpoly.coeff j) ∈ T) → ∀ x y, ((e x).map (toFr O)).rank = ((e y).map (toFr O)).rank := by
  intro X O _ _ _ n T e hT he hc x y
  have hx := rank_eq_rootMultiplicity (e x) (congrFun he x)
  have hy := rank_eq_rootMultiplicity (e y) (congrFun he y)
  have hp : (e x).charpoly.map (IsLocalRing.residue O) = (e y).charpoly.map (IsLocalRing.residue O) := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact residue_eq T (fun z => (e z).charpoly.coeff j) (hc j) x y
  rw [hx, hy, hp]

end GlobalTheory.IdemConstRank
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BlockCharpoly

open Polynomial

theorem exists_factor_of_idempotent {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e := by
  classical
  set V := LinearMap.range e.mulVecLin with hV
  have hd : Module.finrank K V = t := (Matrix.finrank_range_mulVecLin e).trans hr
  let bs := Module.finBasisOfFinrankEq K V hd
  let P : (Fin n → K) →ₗ[K] V := e.mulVecLin.rangeRestrict
  let fa : (Fin t → K) →ₗ[K] (Fin n → K) := V.subtype ∘ₗ bs.equivFun.symm.toLinearMap
  let fb : (Fin n → K) →ₗ[K] (Fin t → K) := bs.equivFun.toLinearMap ∘ₗ P

  have hP : ∀ v : V, P v = v := by
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show e.mulVecLin (e.mulVecLin w) = e.mulVecLin w
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
  refine ⟨LinearMap.toMatrix' fa, LinearMap.toMatrix' fb, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, hP,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← LinearMap.toMatrix'_comp]
    have hc : fa ∘ₗ fb = Matrix.toLin' e := by
      refine LinearMap.ext fun x => ?_
      simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.coe_subtype, P, Matrix.toLin'_apply]
      rfl
    rw [hc, LinearMap.toMatrix'_toLin']

theorem blockPol_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (M : Matrix (Fin n) (Fin n) K) :
    blockPol (a * b) (a * b * M * (a * b)) = (b * M * a).charpoly := by
  unfold blockPol
  set A := a.map (C : K →+* K[X]) with hA
  set B := b.map (C : K →+* K[X]) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Matrix.map_mul, hba, Matrix.map_one _ C.map_zero C.map_one]

  have hmat : (X : K[X]) • (a * b).map (C : K →+* K[X]) - (a * b * M * (a * b)).map (C : K →+* K[X])
        + 1 - (a * b).map (C : K →+* K[X])
      = 1 + (A * ((X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - B * M.map (C : K →+* K[X]) * A - 1)) * B := by
    simp only [Matrix.map_mul, ← hA, ← hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hmat, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul, add_sub_cancel]
  have hBMA : B * M.map (C : K →+* K[X]) * A = (b * M * a).map (C : K →+* K[X]) := by
    rw [hA, hB, Matrix.map_mul, Matrix.map_mul]
  rw [hBMA, Matrix.charpoly]
  congr 1
  ext i j
  simp only [Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem blockPol_eq_charpoly {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧
      ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  obtain ⟨a, b, hba, hab⟩ := exists_factor_of_idempotent e he hr
  refine ⟨a, b, hba, hab, fun M => ?_⟩
  subst hab
  exact blockPol_factor a b hba M

end GlobalTheory.BlockCharpoly
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.MatCorner

variable {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ}

def pairOf (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (g : Γ) :
    Matrix (Fin r) (Fin r) A × (ℕ → A) :=
  (mat ρ g, fun c => ((χ c g : Aˣ) : A))

theorem pairOf_mul (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (g h : Γ) :
    pairOf ρ χ (g * h) = pairOf ρ χ g * pairOf ρ χ h := by
  refine Prod.ext ?_ ?_
  · simp [pairOf, mat]
  · funext c
    simp [pairOf]

theorem mul_mem_span (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    {a b : Matrix (Fin r) (Fin r) A × (ℕ → A)}
    (ha : a ∈ Submodule.span A (Set.range (pairOf ρ χ)))
    (hb : b ∈ Submodule.span A (Set.range (pairOf ρ χ))) :
    a * b ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  induction hb using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [← pairOf_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hz
    | smul c x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c hx
  | zero => simp
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hy

theorem exists_lift (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (P : Matrix (Fin r) (Fin r) A) :
    ∃ v, (P, v) ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  have hfst : (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) ∘ pairOf ρ χ = mat ρ := by
    funext g
    rfl
  have hP : P ∈ (Submodule.span A (Set.range (pairOf ρ χ))).map
      (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) := by
    rw [Submodule.map_span, ← Set.range_comp, hfst, hs]
    exact Submodule.mem_top
  obtain ⟨x, hx, rfl⟩ := hP
  exact ⟨x.2, by simpa using hx⟩

theorem pair_zero_mem (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (hr : 2 ≤ r)
    (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (P : Matrix (Fin r) (Fin r) A) :
    (P, (0 : ℕ → A)) ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  set I := Submodule.span A (Set.range (pairOf ρ χ)) with hI

  have sand : ∀ M X Y : Matrix (Fin r) (Fin r) A, (M, (0 : ℕ → A)) ∈ I →
      (X * M * Y, (0 : ℕ → A)) ∈ I := by
    intro M X Y hM
    obtain ⟨v, hv⟩ := exists_lift ρ χ hs X
    obtain ⟨w, hw⟩ := exists_lift ρ χ hs Y
    have hXMY := mul_mem_span ρ χ (mul_mem_span ρ χ hv hM) hw
    simpa using hXMY
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin r, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩

  have hE : (Matrix.single i0 i1 (1 : A), (0 : ℕ → A)) ∈ I := by
    obtain ⟨v, hv⟩ := exists_lift ρ χ hs (Matrix.single i0 i0 1)
    obtain ⟨w, hw⟩ := exists_lift ρ χ hs (Matrix.single i0 i1 1)
    have hc := I.sub_mem (mul_mem_span ρ χ hv hw) (mul_mem_span ρ χ hw hv)
    have hz : Matrix.single i0 i1 (1 : A) * Matrix.single i0 i0 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : A) i0 i1 i0 h01.symm 1
    simpa [hz, mul_comm w v] using hc

  have key : ∀ (i j : Fin r) (c : A), (Matrix.single i j c, (0 : ℕ → A)) ∈ I := by
    intro i j c
    have hij := sand _ (Matrix.single i i0 c) (Matrix.single i1 j 1) hE
    simpa using hij
  let J := I.comap (LinearMap.inl A (Matrix (Fin r) (Fin r) A) (ℕ → A))
  have hPJ : P ∈ J := by
    rw [Matrix.matrix_eq_sum_single P]
    exact J.sum_mem fun i _ => J.sum_mem fun j _ => key i j (P i j)
  exact hPJ

theorem exists_comb_kills_chars :
    ∀ {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)), 2 ≤ r →
      Submodule.span A (Set.range (mat ρ)) = ⊤ → ∀ P : Matrix (Fin r) (Fin r) A,
      ∃ (m : ℕ) (f : Fin m → A) (h : Fin m → Γ), ∑ k, f k • mat ρ (h k) = P ∧
        ∀ c : ℕ, ∑ k, f k * ((χ c (h k) : Aˣ) : A) = 0 := by
  intro Γ A _ _ r ρ χ hr hs P
  obtain ⟨m, f, g, hg⟩ := Submodule.mem_span_set'.mp (pair_zero_mem ρ χ hr hs P)
  choose h hh using fun k => Set.mem_range.mp (g k).2
  have hsum : ∑ k, f k • pairOf ρ χ (h k) = (P, 0) := by simpa [hh] using hg
  refine ⟨m, f, h, ?_, fun c => ?_⟩
  · have h1 := congrArg Prod.fst hsum
    simpa [Prod.fst_sum, pairOf] using h1
  · have h2 := congrFun (congrArg Prod.snd hsum) c
    simpa [Prod.snd_sum, Finset.sum_apply, pairOf] using h2

end GlobalTheory.MatCorner
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharBlock

open Polynomial Matrix

theorem rank_blockPol_of_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (d : Fin t → K) (hba : b * a = 1) :
    (a * b).rank = t ∧
      blockPol (a * b) (a * Matrix.diagonal d * b) = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  constructor
  · apply le_antisymm
    · exact (Matrix.rank_mul_le_left a b).trans (by simpa using Matrix.rank_le_width a)
    · have h1 : b * (a * b) * a = 1 := by
        rw [← Matrix.mul_assoc b a b, hba, Matrix.one_mul, hba]
      have h2 : (b * (a * b) * a).rank ≤ (a * b).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      rw [h1, Matrix.rank_one] at h2
      simpa using h2
  · unfold blockPol
    have hba' : b.map (C (R := K)) * a.map (C (R := K)) = 1 := by
      rw [← Matrix.map_mul, hba]
      simp
    set D : Matrix (Fin t) (Fin t) K[X] := Matrix.diagonal (fun c => (X : K[X]) - C (d c)) with hD
    have hD' : D = (X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - (Matrix.diagonal d).map (C (R := K)) := by
      ext1 i j
      by_cases h : i = j
      · subst h; simp [hD]
      · simp [hD, h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    have key : (X : K[X]) • (a * b).map (C (R := K)) - (a * Matrix.diagonal d * b).map (C (R := K)) + 1
        - (a * b).map (C (R := K)) = 1 + a.map (C (R := K)) * ((D - 1) * b.map (C (R := K))) := by
      rw [hD', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [key, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hba', Matrix.mul_one, add_sub_cancel, hD,
      Matrix.det_diagonal]

theorem rank_blockPol_proj : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  intro K _ n r t e E M d hE hM
  let a : Matrix (Fin n) (Fin t) K :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K (Fin r → K) (Fin t → K))
  let b : Matrix (Fin t) (Fin n) K :=
    LinearMap.toMatrix' (LinearMap.snd K (Fin r → K) (Fin t → K) ∘ₗ e.toLinearMap)
  have ha : ∀ w, a.mulVec w = e.symm (0, w) := by
    intro w
    simp [a, LinearMap.toMatrix'_mulVec]
  have hb : ∀ u, b.mulVec u = (e u).2 := by
    intro u
    simp [b, LinearMap.toMatrix'_mulVec]
  have hba : b * a = 1 := by
    apply Matrix.toLin'.injective
    ext1 w
    ext1
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb,
      LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hE' : E = a * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    rw [← hE, LinearEquiv.symm_apply_apply]
  have hM' : M = a * Matrix.diagonal d * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    apply e.injective
    rw [hM, LinearEquiv.apply_symm_apply]
    congr 1
    funext c
    rw [Matrix.mulVec_diagonal]
  rw [hE', hM']
  exact rank_blockPol_of_factor a b d hba

end GlobalTheory.CharBlock
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem exists_injective_roots_of_ncard_rootSet {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O)
    (hinj : Function.Injective (algebraMap A O))
    (hcard : ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t)
    (hP : P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c))) :
    ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  have hO : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hA : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective _ _
  set g : A →+* FractionRing O := (algebraMap O (FractionRing O)).comp (algebraMap A O) with hg
  have hgi : Function.Injective g := hO.comp hinj
  change P.map g = _ at hP
  change ((P.map (algebraMap A (FractionRing A))).rootSet _).ncard = t at hcard
  have hmon' : (P.map g).Monic := by
    rw [hP]; exact Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)
  have hmon : P.Monic := Polynomial.monic_of_injective hgi hmon'
  have hdeg : P.natDegree = t := by
    rw [← hmon.natDegree_map g, hP, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
    simp
  have hsep : (P.map (algebraMap A (FractionRing A))).Separable := by
    have hne : P.map (algebraMap A (FractionRing A)) ≠ 0 := (hmon.map _).ne_zero
    rw [← Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := AlgebraicClosure (FractionRing A)) hne (IsAlgClosed.splits _), hmon.natDegree_map, hdeg, ← hcard, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  obtain ⟨φ, hφ⟩ : ∃ φ : FractionRing A →+* FractionRing O, φ.comp (algebraMap A (FractionRing A)) = g :=
    ⟨IsFractionRing.lift hgi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := FractionRing A) hgi a⟩
  have hsep2 : (P.map g).Separable := by
    rw [← hφ, ← Polynomial.map_map]; exact hsep.map
  have hα : Function.Injective α := by
    rw [hP] at hsep2
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep2
  have hint : ∀ c, ∃ b : O, algebraMap O (FractionRing O) b = α c := by
    intro c
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨P.map (algebraMap A O), hmon.map _, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_map, ← hg, hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp)
  choose β hβ using hint
  refine ⟨β, fun c d h => hα (by rw [← hβ, ← hβ, h]), ?_⟩
  apply Polynomial.map_injective _ hO
  rw [Polynomial.map_map, ← hg, hP, Polynomial.map_prod]
  simp [hβ]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.complement_of_characters_unique_up_to_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  first | exact @GlobalTheory.CharCancel.main | exact GlobalTheory.CharCancel.main | (intros; apply GlobalTheory.CharCancel.main <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.weighted_count_stable_lattices_product_descent_GL : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  first | exact @GlobalTheory.UnitLemma.DescentGL.countGL_prod | exact GlobalTheory.UnitLemma.DescentGL.countGL_prod | (intros; apply GlobalTheory.UnitLemma.DescentGL.countGL_prod <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧ ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧ lam h j (x ^ l) = lam h (j + 1) x := by
  first | exact @GlobalTheory.PSer.lam_hasSum_norm_le_frob | exact GlobalTheory.PSer.lam_hasSum_norm_le_frob | (intros; apply GlobalTheory.PSer.lam_hasSum_norm_le_frob <;> assumption)
end
