module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianArithmeticVariety

theorem det_submatrix_sign {R : Type*} [CommRing R] {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (g h : Fin j → Fin N) (hg : Function.Injective g) (hh : Function.Injective h)
    (hr : Set.range h = Set.range g) :
    ∃ s : ℤˣ, (A.submatrix id h).det = ((s : ℤ) : R) * (A.submatrix id g).det := by
  let σ : Equiv.Perm (Fin j) :=
    (Equiv.ofInjective h hh).trans ((Equiv.subtypeEquivRight (fun x => by rw [hr])).trans (Equiv.ofInjective g hg).symm)
  have hσ : ∀ i, g (σ i) = h i := by
    intro i
    simp [σ, Equiv.apply_ofInjective_symm]
  refine ⟨Equiv.Perm.sign σ, ?_⟩
  have : A.submatrix id h = (A.submatrix id g).submatrix id σ := by
    ext r i; simp [hσ]
  rw [this, det_permute']

def col {j m : ℕ} (a : Fin j) (b : Fin m) (i : Fin j) : Fin (j + m) :=
  if i = a then Fin.natAdd j b else Fin.castAdd m i

theorem col_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (col a b) := by
  intro x y hxy
  simp only [col] at hxy
  split_ifs at hxy with h1 h2 h2
  · exact h1.trans h2.symm
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)

def idx {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨col a b, col_injective a b⟩, by simp⟩

theorem minor_idx {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by
  obtain ⟨s, hs⟩ := det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b)
    ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by
      rw [Finset.range_orderEmbOfFin]; simp [idx])
  refine ⟨s, ?_⟩
  have hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r i
    by_cases hi : i = a
    · simp [col, onePipe, hi]
    · simp [col, onePipe, hi]
  rw [colsOf, hs, hcol, ← cramer_apply, cramer_one]
  rfl

theorem colsOf_anchor {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by
  have he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) =
      Fin.castAdd m :=
    (Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm
  ext r i
  simp [colsOf, onePipe, he]

end GrassmannianArithmeticVariety


open GrassmannianArithmeticVariety in
theorem GrassArithVar.proof (h : CoordConeArithVar.Statement) : GrassArithVar.Statement := by
  intro f j m hf
  let e : Fin (f * j * m) ≃ Fin f × Fin j × Fin m :=
    finProdFinEquiv.symm.trans
      ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  let φ := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)
  let t : Fin (f * j * m) → GrassField f j m := fun i => φ (X (e i))
  have anchor : ∀ τ, grassCoord f j m ⟨τ, plAnchor j m⟩ = 1 := by
    intro τ
    have hp : grassPolyCoord f j m ⟨τ, plAnchor j m⟩ = 1 :=
      (congrArg Matrix.det (colsOf_anchor _)).trans det_one
    rw [grassCoord, hp, map_one]
  have hmem : ∀ q : MvPolynomial (Fin f × Fin j × Fin m) ℚ,
      algebraMap _ (GrassField f j m) q ∈ IntermediateField.adjoin ℚ (Set.range t) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨e.symm i, by simp [t, φ]⟩)
  refine h (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) (fun _ => plAnchor j m)
    (f * j * m) t ⟨⟨0, hf⟩⟩ (fun τ => by rw [anchor]; exact one_ne_zero) ?_ ?_ ?_
  · exact ((MvPolynomial.algebraicIndependent_X _ ℚ).map' (f := φ)
      (IsFractionRing.injective _ _)).comp e e.injective
  · intro i
    rcases hi : e i with ⟨τ, a, b⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤˣ, grassPolyCoord f j m ⟨τ, idx a b⟩ =
        ((s : ℤ) : MvPolynomial (Fin f × Fin j × Fin m) ℚ) * X (τ, a, b) :=
      minor_idx _ a b
    have hr : grassCoord f j m ⟨τ, idx a b⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (coneRatios (grassCoord f j m) fun _ => plAnchor j m) :=
      IntermediateField.subset_adjoin _ _ ⟨⟨τ, idx a b⟩, rfl⟩
    have hy : grassCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : GrassField f j m) * t i := by
      rw [grassCoord, hs, map_mul, map_intCast]
      simp [t, φ, hi]
    rw [anchor, div_one, hy] at hr
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hr
    · simpa using neg_mem hr
  · rintro r ⟨⟨τ, I⟩, rfl⟩
    have hr : grassCoord f j m ⟨τ, I⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (Set.range t) := by
      rw [anchor, div_one]; exact hmem _
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range t))
      (A := GrassField f j m) ⟨_, hr⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootAnchorNonzeroAlt

theorem anchorMinor_eq_one {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 =
      Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

theorem rootCoord_isIntegral {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  classical
  apply IsIntegral.det
  intro a b
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize p.2.1.orderEmbOfFin p.2.2 b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left]
    by_cases h : a = c
    · subst h; rw [Matrix.one_apply_eq]; exact isIntegral_one
    · rw [Matrix.one_apply_ne h]; exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hpow⟩ := hζ p.1 a c
    exact IsIntegral.of_pow hk (by rw [hpow]; exact isIntegral_one)

def homForm {f j m : ℕ} (q : Polynomial ℤ) (τ : Fin f) (I : PlIdx j m) : MRing (plBlocks f j m) :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    C (q.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (q.natDegree - k)

theorem homForm_mem {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (q : Polynomial ℤ) (τ : Fin f)
    (I : PlIdx j m) (hq : Polynomial.aeval (rootCoord ζ ⟨τ, I⟩) q = 0) :
    homForm q τ I ∈ rootPointIdeal ζ := by
  show mConeMap (rootCoord ζ) (homForm q τ I) = 0
  have hA : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchorMinor_eq_one j m (ζ τ)

  simp only [homForm, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_C, hA, map_one, one_mul]
  rw [Polynomial.aeval_eq_sum_range] at hq
  calc _ = ∑ k ∈ Finset.range (q.natDegree + 1),
        C (q.coeff k • rootCoord ζ ⟨τ, I⟩ ^ k) * (X τ : MvPolynomial (Fin f) ℂ) ^ q.natDegree := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [← pow_mul_pow_sub (X τ : MvPolynomial (Fin f) ℂ) hk', zsmul_eq_mul, map_mul, map_pow,
          eq_intCast, map_intCast, mul_pow]
        ring
    _ = 0 := by rw [← Finset.sum_mul, ← map_sum, hq, map_zero, zero_mul]

theorem eval_homForm {f j m : ℕ} {q : Polynomial ℤ} (hq : q.Monic) {τ : Fin f} {I : PlIdx j m}
    {z : (Σ _ : Fin f, PlIdx j m) → ℂ} (hz : z ⟨τ, plAnchor j m⟩ = 0) :
    eval z (map (Int.castRingHom ℂ) (homForm q τ I)) = z ⟨τ, I⟩ ^ q.natDegree := by

  simp only [homForm, map_sum, map_mul, map_pow, map_C, map_X, eval_C, eval_X, hz]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [hq.coeff_natDegree]
  · intro k hk
    have : q.natDegree - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow this]

end RootAnchorNonzeroAlt

theorem RootAnchorNonzero.proof : RootAnchorNonzero.Statement := by
  intro f j m ζ hζ z hz τ h0
  obtain ⟨I, hI⟩ := hz.1 τ
  obtain ⟨q, hqm, hq⟩ := RootAnchorNonzeroAlt.rootCoord_isIntegral hζ ⟨τ, I⟩
  have hmem := RootAnchorNonzeroAlt.homForm_mem ζ q τ I (by rwa [Polynomial.aeval_def])
  have h := hz.2 _ hmem
  rw [RootAnchorNonzeroAlt.eval_homForm hqm h0] at h
  exact hI (pow_eq_zero_iff'.mp h).1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace MultiHomogMemCoordinate

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mapDomain_fst_eq (m : (Σ k, ι k) →₀ ℕ) (a : K → ℕ) (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm a := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [hm]
  · intro b _ hb
    simp [hb]
  · simp

theorem cone_monomial (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  have hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) =
      m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp only [map_pow, rename_X]
  rw [← mapDomain_fst_eq m a hm, hX]
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd,
    map_pow, map_mul]
  ring

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ) (hg : IsMultiHomog g a) :
    mConeMap y g = C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]

  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm => cone_monomial y m _ a (hg m hm)

end MultiHomogMemCoordinate


open MultiHomogMemCoordinate in
theorem MultiHomogMemCoord.proof : MultiHomogMemCoord.Statement := by
  intro K _ ι _ Ω _ y g a hg
  rw [mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one,
    monomial_eq_zero]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianRootBound

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def cone {R : Type*} [CommRing R] (y : (Σ k, ι k) → R) : MRing ι →ₐ[ℤ] MvPolynomial K R :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem map_cone {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (y : (Σ k, ι k) → R)
    (g : MRing ι) : MvPolynomial.map φ (cone y g) = cone (fun p => φ (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [cone]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [cone]

theorem eval_grassPolyCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval (fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2) (grassPolyCoord f j m p) =
      rootCoord ζ p := by
  let φ : MvPolynomial (Fin f × Fin j × Fin m) ℚ →+* ℂ :=
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom
  show φ _ = _
  rw [grassPolyCoord, RingHom.map_det, rootCoord]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, colsOf, onePipe, submatrix_apply, of_apply, id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (p.2.1.orderEmbOfFin p.2.2 b)
  · simp [Fin.append_left, Matrix.one_apply, apply_ite φ]
  · simp [Fin.append_right, φ]

end GrassmannianRootBound


open GrassmannianRootBound in
theorem GrassLeRoot.proof : GrassLeRoot.Statement := by
  intro f j m ζ g hg
  have h0 : mConeMap (grassCoord f j m) g = 0 := hg
  have h1 : cone (grassPolyCoord f j m) g = 0 := by
    apply MvPolynomial.map_injective (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m))
      (IsFractionRing.injective _ _)
    rw [map_cone, map_zero]
    exact h0
  have h2 := congrArg (MvPolynomial.map
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom) h1
  rw [map_cone, map_zero] at h2
  show (aeval fun p => MvPolynomial.C (rootCoord ζ p) * MvPolynomial.X p.1) g = 0
  simpa [cone, eval_grassPolyCoord] using h2

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootDenseAlt

theorem aeval_grassPolyCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval x (grassPolyCoord f j m p) = rootCoord (fun τ a b => x (τ, a, b)) p := by
  simp only [grassPolyCoord, rootCoord]
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [colsOf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  induction c using Fin.addCases with
  | left c => simp [Fin.append_left, Matrix.one_apply, apply_ite]
  | right c => simp [Fin.append_right]

theorem aeval_rootCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ) (g : MRing (plBlocks f j m)) :
    aeval (rootCoord (fun τ a b => x (τ, a, b))) g = aeval x (aeval (grassPolyCoord f j m) g) := by
  rw [show aeval x (aeval (grassPolyCoord f j m) g) =
      ((aeval x).restrictScalars ℤ).comp (aeval (grassPolyCoord f j m)) g from rfl, comp_aeval]
  exact congrArg (fun y => aeval y g) (funext fun p => (aeval_grassPolyCoord x p).symm)

theorem aeval_comp_ringHom {σ τ Ω : Type*} [Field Ω] (φ : MvPolynomial σ ℚ →+* Ω)
    (P : τ → MvPolynomial σ ℚ) (g : MvPolynomial τ ℤ) :
    aeval (fun i => φ (P i)) g = φ (aeval P g) := by
  have : (aeval (fun i => φ (P i)) : MvPolynomial τ ℤ →ₐ[ℤ] Ω).toRingHom =
      φ.comp (aeval P).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  exact congrArg (fun ψ : MvPolynomial τ ℤ →+* Ω => ψ g) this

end RootDenseAlt

theorem RootDense.proof (h₁ : MultiHomogMemCoord.Statement) (h₂ : RootsOfUnityDense.Statement) :
    RootDense.Statement := by
  intro f j m g ⟨a, ha⟩ hg
  have hQ0 : aeval (grassPolyCoord f j m) g ≠ 0 := by
    intro h0
    apply hg
    rw [grassIdeal, h₁ (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) g a ha]
    exact (RootDenseAlt.aeval_comp_ringHom
      (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)) _ g).trans
      (by rw [h0, map_zero])
  let e := Fintype.equivFin (Fin f × Fin j × Fin m)
  have hP : rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g)) ≠ 0 := by
    intro h
    apply hQ0
    apply map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    apply rename_injective e e.injective
    simpa using h
  obtain ⟨z, hz, hzQ⟩ : ∃ z : Fin (Fintype.card (Fin f × Fin j × Fin m)) → ℂ,
      (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) ∧
        eval z (rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g))) ≠ 0 := by
    by_contra! H
    exact hP (h₂ _ _ H)
  refine ⟨rootPointIdeal (fun τ a b => (z ∘ e) (τ, a, b)), ⟨_, fun τ a b => hz _, rfl⟩, ?_⟩
  show g ∉ mCoordIdeal _
  rw [h₁ (Fin f) (plBlocks f j m) ℂ _ g a ha]
  refine fun h => hzQ ?_
  rw [eval_rename, eval_map, ← aeval_def, ← RootDenseAlt.aeval_rootCoord]
  exact h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GrassHeightBound.proof (hArith : GrassArithVar.Statement) (hRoot : RootArithVar.Statement)
    (hSemi : FsLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : FsConjInvariant.Statement) (hLe : GrassLeRoot.Statement) (hHt : RootHeight.Statement)
    (hDense : RootDense.Statement) : GrassHeightBound.Statement := by
  intro hZ2 f j m hf II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    (grassConst f j m) (rootFamily f j m) II hII (hArith f j m hf) bot_le (hSemi _ _ _)
    (hNef _ _ _ _ fun _ => ?_) (hConj _ _) ?_ (hDense f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨hRoot f j m ζ hf hζ, hLe f j m ζ, hHt f j m ζ hf hζ II hII⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FsLineSemipositive.proof (h₁ : FsLineSmooth.Statement) (h₂ : FsLineLevi.Statement) :
    FsLineSemipositive.Statement := by
  intro K _ ι _ P
  exact ⟨h₁ K ι, fun z hz w _ => h₂ K ι z w hz.1⟩

end GroundTheory.Heights₂.Heights
end
