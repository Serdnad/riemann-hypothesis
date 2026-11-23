module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Mathlib.Basic.PEquiv

@[expose] public section

section

noncomputable section

namespace GlobalTheory.DefPt

open Matrix

section Char

variable {K : Type} [Field K] {n : ℕ} (χ : Matrix (Fin n) (Fin n) K →* K)

theorem matChar_submatrix (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) K) :
    χ (M.submatrix σ σ) = χ M := by
  have h1 : ∀ N : Matrix (Fin n) (Fin n) K,
      σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ := by
    intro N
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    rfl
  have h2 := congrArg χ (h1 1)
  rw [submatrix_one_equiv, Matrix.mul_one, map_mul, map_one] at h2
  rw [← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]

theorem matChar_transvection [CharZero K] {i j : Fin n} (hij : i ≠ j) (c : K) :
    χ (transvection i j c) = 1 := by
  set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)
  set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have hD : χ D ≠ 0 := fun h => by
    have := congrArg χ hDD
    rw [map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hT : χ (transvection i j c) ≠ 0 := fun h => by
    have := congrArg χ (transvection_mul_transvection_same i j hij c (-c))
    rw [add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hcomm : D * transvection i j c = transvection i j (c + c) * D := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    have hdi : Function.update (1 : Fin n → K) i 2 i = 2 := by simp
    have hdj : Function.update (1 : Fin n → K) i 2 j = 1 := by simp [Ne.symm hij]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hij, hdi, hdj]
      simp only [and_self, ite_true]
      ring
    · have h' : ¬(i = a ∧ j = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg h', if_neg h']
      simp only [add_zero]
      by_cases hab : a = b
      · subst hab; ring
      · rw [Matrix.one_apply_ne hab]; ring
  have e := congrArg χ hcomm
  rw [map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)] at e
  have e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c) := by
    rw [mul_one]
    exact mul_right_cancel₀ hD e
  exact (mul_left_cancel₀ hT e2).symm

theorem matChar_mulSingle (k k' : Fin n) (a : K) :
    χ (diagonal (Pi.mulSingle k a)) = χ (diagonal (Pi.mulSingle k' a)) := by
  rw [← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]
  apply congrArg χ
  apply congrArg diagonal
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x = k
  · subst hx; simp
  · by_cases hx' : x = k'
    · subst hx'; rw [Equiv.swap_apply_right]; simp [hx, Ne.symm hx]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; simp [hx, hx']

theorem matChar_diagonal_pow (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m) (d : Fin n → K) :
    χ (diagonal d) ^ n = (diagonal d).det ^ m := by
  let ψ : (Fin n → K) →* K := χ.comp (diagonalRingHom (Fin n) K).toMonoidHom
  have hψ : ∀ v, ψ v = χ (diagonal v) := fun v => rfl
  have hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m := by
    intro k a
    calc χ (diagonal (Pi.mulSingle k a)) ^ n = ∏ k' : Fin n, ψ (Pi.mulSingle k' a) := by
          rw [Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]
  calc χ (diagonal d) ^ n = (∏ k, ψ (Pi.mulSingle k (d k))) ^ n := by
        rw [← map_prod, Finset.univ_prod_mulSingle, hψ]
    _ = ∏ k, d k ^ m := by
        rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun k _ => hone k (d k)
    _ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]

theorem matChar_pow_eq_det_pow [CharZero K] (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m)
    (g : Matrix (Fin n) (Fin n) K) : χ g ^ n = g.det ^ m := by
  refine diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g
    (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)
  · show χ t.toMatrix ^ n = t.toMatrix.det ^ m
    rw [show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij,
      det_transvection_of_ne _ _ t.hij]
    simp
  · show χ (A * B) ^ n = (A * B).det ^ m
    have hA' : χ A ^ n = A.det ^ m := hA
    have hB' : χ B ^ n = B.det ^ m := hB
    rw [map_mul, det_mul, mul_pow, mul_pow, hA', hB']

end Char

end GlobalTheory.DefPt

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine MvPolynomial
open scoped Matrix

def rhoDetHom {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : Matrix (Fin n) (Fin n) K →* K where
  toFun g := (GlobalTheory.DefPt.rhoMat la g).det
  map_one' := by rw [Model.rhoMat_one, Matrix.det_one]
  map_mul' g h := by rw [Model.rhoMat_mul, Matrix.det_mul, mul_comm]

theorem det_rhoMat_pow : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la →
    ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) := by
  intro K _ _ n la _ g
  have hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la) := by
    intro t
    show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _
    rw [Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]
  exact matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g

end GlobalTheory.DefPt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_sub_root_eq {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z z' : Pt A D') (hz : z ^ n = spOver φ ≫ x) (hz' : z' ^ n = spOver φ ≫ x) :
    s D' φ z' - s' D' φ z' = s D' φ z - s' D' φ z := by
  have hw : (z⁻¹ * z') ^ n = 1 := by rw [mul_pow, inv_pow, hz, hz', inv_mul_cancel]
  have e : z' = z * (z⁻¹ * z') := (mul_inv_cancel_left z z').symm
  rw [e, hs.2 D' φ z _ hz hw, hs'.2 D' φ z _ hz hw]
  abel

theorem isSec_sub_natural {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) :
    s D'' (ψ.comp φ) (spOver ψ ≫ z) - s' D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z - s' D' φ z) := by
  rw [hs.1 D' D'' φ ψ z hz, hs'.1 D' D'' φ ψ z hz, map_sub]

theorem root_spOver {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) : (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow z n (spOver ψ), hz, ← Category.assoc, spOver_comp]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isSec_sub_existsUnique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ (b : Fn0 A) (D : Type) [CommRing D] [Algebra R D] (x : Pt A D) (s s' : RootFn A D),
    IsSec n b x s → IsSec n b x s' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e := by
  intro R _ A _ _ n hR b D _ _ x s s' hs hs'
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  have hdesc := GlobalTheory.ff_descent_pairs R D D₁ ψ hψ (s D₁ ψ z₀ - s' D₁ ψ z₀) (fun E _ _ α β hαβ ↦ by
    rw [← isSec_sub_natural hs hs' ψ α z₀ hz₀, ← isSec_sub_natural hs hs' ψ β z₀ hz₀]
    have hα := root_spOver ψ α z₀ hz₀
    have hβ := root_spOver ψ β z₀ hz₀
    rw [hαβ] at hα ⊢
    exact isSec_sub_root_eq hs hs' (β.comp ψ) (spOver β ≫ z₀) (spOver α ≫ z₀) hβ hα)
  obtain ⟨e, he, heu⟩ := hdesc
  have key : ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x →
      s D' φ z - s' D' φ z = φ e := by
    intro D' _ _ φ z hz
    obtain ⟨E', _, _, ψ', φ', hψ', hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
    have hinj : Function.Injective ψ' := by
      letI : Algebra D' E' := (ψ' : D' →+* E').toAlgebra
      haveI : Module.FaithfullyFlat D' E' := hψ'
      exact FaithfulSMul.algebraMap_injective D' E'
    apply hinj
    have h1 := root_spOver φ ψ' z hz
    have h2 := root_spOver ψ φ' z₀ hz₀
    rw [← isSec_sub_natural hs hs' φ ψ' z hz]
    rw [hsq] at h1 ⊢
    rw [isSec_sub_root_eq hs hs' _ _ _ h2 h1, isSec_sub_natural hs hs' ψ φ' z₀ hz₀, ← he]
    exact (congrArg (fun f : D →ₐ[R] E' ↦ f e) hsq).symm
  exact ⟨e, key, fun e' he' ↦ heu e' ((he' D₁ ψ z₀ hz₀).symm)⟩

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecMul

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (f : T' ⟶ T)
    (x : T ⟶ A) (n : ℕ) : f ≫ x ^ n = (f ≫ x) ^ n :=
  MonObj.comp_pow x n f

end GlobalTheory.SecMul

namespace GlobalTheory

theorem sec_mul_diff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D)
    (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D,
    ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  intro R _ A _ _ n hR b hb D _ _ x y s s' s'' hs hs' hs''
  have hroot : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (p : Pt A D) (z : Pt A E), z ^ n = spOver φ ≫ p →
      (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ p := by
    intro E _ _ E' _ _ φ ψ p z hz
    rw [← SecMul.comp_pow_pt, hz, ← Category.assoc, spOver_comp]
  have hmul : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z w : Pt A E), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → (z * w) ^ n = spOver φ ≫ (x * y) := by
    intro E _ _ φ z w hz hw
    rw [mul_pow, hz, hw, comp_mul]
  have hinv : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z z' w w' : Pt A E),
      z ^ n = spOver φ ≫ x → z' ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → w' ^ n = spOver φ ≫ y →
      s'' E φ (z' * w') - s E φ z' - s' E φ w' = s'' E φ (z * w) - s E φ z - s' E φ w := by
    intro E _ _ φ z z' w w' hz hz' hw hw'
    obtain ⟨t, rfl⟩ : ∃ t, z' = z * t := ⟨z⁻¹ * z', (mul_inv_cancel_left z z').symm⟩
    obtain ⟨u, rfl⟩ : ∃ u, w' = w * u := ⟨w⁻¹ * w', (mul_inv_cancel_left w w').symm⟩
    have ht : t ^ n = 1 := by rw [mul_pow, hz] at hz'; exact mul_eq_left.mp hz'
    have hu : u ^ n = 1 := by rw [mul_pow, hw] at hw'; exact mul_eq_left.mp hw'
    rw [_root_.mul_mul_mul_comm, hs''.2 E φ _ _ (hmul E φ z w hz hw) (by rw [mul_pow, ht, hu, _root_.one_mul]),
      hb.2 E t u ht hu, hs.2 E φ z t hz ht, hs'.2 E φ w u hw hu]
    ring
  have hnat : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (z w : Pt A E), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y →
      s'' E' (ψ.comp φ) (spOver ψ ≫ z * spOver ψ ≫ w) - s E' (ψ.comp φ) (spOver ψ ≫ z) -
        s' E' (ψ.comp φ) (spOver ψ ≫ w) = ψ (s'' E φ (z * w) - s E φ z - s' E φ w) := by
    intro E _ _ E' _ _ φ ψ z w hz hw
    rw [← comp_mul, hs''.1 E E' φ ψ _ (hmul E φ z w hz hw), hs.1 E E' φ ψ z hz, hs'.1 E E' φ ψ w hw,
      map_sub, map_sub]
  obtain ⟨D2, _, _, ψ, z0, w0, hf, hz0, hw0⟩ : ∃ (D2 : Type) (_ : CommRing D2) (_ : Algebra R D2)
      (ψ : D →ₐ[R] D2) (z0 w0 : Pt A D2), (ψ : D →+* D2).FaithfullyFlat ∧ z0 ^ n = spOver ψ ≫ x ∧
      w0 ^ n = spOver ψ ≫ y := by
    obtain ⟨D1, _, _, ψ1, z1, hf1, hz1⟩ := hR D x
    obtain ⟨D2, _, _, ψ2, w2, hf2, hw2⟩ := hR D1 (spOver ψ1 ≫ y)
    refine ⟨D2, inferInstance, inferInstance, ψ2.comp ψ1, spOver ψ2 ≫ z1, w2,
      RingHom.FaithfullyFlat.stableUnderComposition ψ1.toRingHom ψ2.toRingHom hf1 hf2,
      hroot D1 D2 ψ1 ψ2 x z1 hz1, ?_⟩
    rw [hw2, ← Category.assoc, spOver_comp]
  have hinjψ : Function.Injective ψ := RingHom.FaithfullyFlat.injective hf
  obtain ⟨e, he, -⟩ := ff_descent_pairs R D D2 ψ hf
    (s'' D2 ψ (z0 * w0) - s D2 ψ z0 - s' D2 ψ w0) (fun E _ _ α β hαβ ↦ by
      rw [← hnat D2 E ψ α z0 w0 hz0 hw0, ← hnat D2 E ψ β z0 w0 hz0 hw0]
      have h1 := hroot D2 E ψ α x z0 hz0
      have h2 := hroot D2 E ψ α y w0 hw0
      rw [hαβ] at h1 h2 ⊢
      exact hinv E (β.comp ψ) _ _ _ _ (hroot D2 E ψ β x z0 hz0) h1 (hroot D2 E ψ β y w0 hw0) h2)
  refine ⟨e, fun E _ _ φ z w hz hw ↦ ?_, fun e' he' ↦ hinjψ ((he' D2 ψ z0 w0 hz0 hw0).symm.trans he.symm)⟩
  obtain ⟨E', _, _, ψ', φ', hf', hcomm⟩ := exists_pushout_faithfullyFlat R D D2 E ψ φ hf
  apply RingHom.FaithfullyFlat.injective hf'
  have hR2 : ψ' (φ e) = s'' E' (φ'.comp ψ) (spOver φ' ≫ z0 * spOver φ' ≫ w0) - s E' (φ'.comp ψ) (spOver φ' ≫ z0) -
      s' E' (φ'.comp ψ) (spOver φ' ≫ w0) := by
    rw [hnat D2 E' ψ φ' z0 w0 hz0 hw0, ← he]
    change (ψ'.comp φ) e = (φ'.comp ψ) e
    rw [hcomm]
  change ψ' (s'' E φ (z * w) - s E φ z - s' E φ w) = ψ' (φ e)
  rw [← hnat E E' φ ψ' z w hz hw, hR2]
  have h1 := hroot E E' φ ψ' x z hz
  have h2 := hroot E E' φ ψ' y w hw
  rw [hcomm] at h1 h2 ⊢
  exact hinv E' (φ'.comp ψ) _ _ _ _ (hroot D2 E' ψ φ' x z0 hz0) h1 (hroot D2 E' ψ φ' y w0 hw0) h2

end GlobalTheory
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatBasis

variable {K : Type} [Field K] [NumberField K]

theorem exists_notMem_mul_le (P u : HeightOneSpectrum (𝓞 K)) (y : K) (h : u ≠ P ∨ u.valuation K y ≤ 1) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ u.valuation K ((s : K) * y) ≤ 1 := by
  have h1 : (1 : 𝓞 K) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  by_cases hy : u.valuation K y ≤ 1
  · exact ⟨1, h1, by simpa using hy⟩
  have hne : u ≠ P := h.resolve_right hy
  have hy0 : u.valuation K y ≠ 0 := fun h0 => hy (by rw [h0]; exact zero_le_one)
  have hnle : ¬ u.asIdeal ≤ P.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le P.isPrime.ne_top hle))
  obtain ⟨π, hπu, hπP⟩ := SetLike.not_le_iff_exists.1 hnle
  have hlt : u.valuation K (π : K) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem u π).2 hπu
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hy0)⁻¹
  refine ⟨π ^ N, fun hm => hπP (P.isPrime.mem_of_pow_mem N hm), ?_⟩
  have e : ((π ^ N : 𝓞 K) : K) = (π : K) ^ N := by simp
  rw [e, map_mul, map_pow]
  have hN' : u.valuation K (π : K) ^ N ≤ (u.valuation K y)⁻¹ := by simpa using hN.le
  calc _ ≤ (u.valuation K y)⁻¹ * u.valuation K y := by gcongr
    _ = 1 := inv_mul_cancel₀ hy0

theorem exists_denom_notMem {ι : Type} [Fintype ι] (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (h : {w | ¬ IntAt w (B w)}.Finite) (P : HeightOneSpectrum (𝓞 K)) (hP : IntAt P (B P)) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ ∀ w, IntAt w ((s : K) • B w) := by
  classical
  haveI : Fintype {w | ¬ IntAt w (B w)} := h.fintype
  have hex : ∀ p : {w | ¬ IntAt w (B w)} × ι × ι, ∃ s : 𝓞 K, s ∉ P.asIdeal ∧
      p.1.1.valuation K ((s : K) * B p.1.1 p.2.1 p.2.2) ≤ 1 := fun p =>
    exists_notMem_mul_le P _ _ (Or.inl fun e => p.1.2 (by rw [e]; exact hP))
  choose s hs hv using hex
  refine ⟨∏ p, s p, fun hm => ?_, fun w i j => ?_⟩
  · obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact hs p hp
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hw i j)
  · rw [Matrix.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨w, hw⟩, i, j))]
    have e : ∀ a b : 𝓞 K, ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := fun a b => by simp
    rw [e, mul_assoc, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hv (⟨w, hw⟩, i, j))

theorem intAt_mul {ι : Type} [Fintype ι] {w : HeightOneSpectrum (𝓞 K)} {M N : Matrix ι ι K}
    (hM : IntAt w M) (hN : IntAt w N) : IntAt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i k) (hN k j)

theorem finite_not_intAt {ι : Type} [Fintype ι] (M : Matrix ι ι K) :
    {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w M}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => HeightOneSpectrum.Support.finite (𝓞 K) (M p.1 p.2)).subset ?_
  intro w hw
  simp only [IntAt, Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨i, j, hij⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), hij⟩

theorem exists_locBasis_inv : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  intro K _ _ n A hA P
  classical
  obtain ⟨hdet, hfin⟩ := hA
  have hu : IsUnit (A P).det := isUnit_iff_ne_zero.2 (hdet P)
  have hone : ∀ (w : HeightOneSpectrum (𝓞 K)) (j k : Fin n), w.valuation K ((Pi.single j 1 : Fin n → K) k) ≤ 1 :=
    fun w j k => by by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  obtain ⟨s, hs, hint⟩ := exists_denom_notMem (fun w => A w * (A P)⁻¹)
    ((hfin.union (finite_not_intAt (A P)⁻¹)).subset fun w hw => by
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
      exact hw (intAt_mul hn.1.1 hn.2)) P (by
      intro i j
      rw [Matrix.mul_nonsing_inv _ hu]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
  have hs0 : (s : K) ≠ 0 := fun h0 => hs (by
    have : s = 0 := by exact_mod_cast h0
    rw [this]; exact P.asIdeal.zero_mem)
  refine ⟨s, hs, fun j w i => ?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
    exact GlobalTheory.LocMatLat.mulVec_le w (hint w) (hone w j) i
  · have h1 : LinearIndependent K (A P)⁻¹.col :=
      Matrix.linearIndependent_cols_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))
    have h2 : LinearIndependent K (fun j => (s : K) • (A P)⁻¹.col j) :=
      h1.units_smul fun _ => Units.mk0 (s : K) hs0
    convert h2 using 3 with j
    simp
  · have hex := fun j => P.exists_primeCompl_mul_eq_of_integer _ (hx P j)
    choose c d hcd using hex
    have hd : (∏ j, (d j : 𝓞 K)) ∉ P.asIdeal := fun hm => by
      obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact (d p).2 hp
    refine ⟨(∏ j, (d j : 𝓞 K)) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hd hs, ?_⟩
    have hx' : x = ∑ j, (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) := by
      simp_rw [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mulVec]
    rw [hx', Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    have e : ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * (d j : 𝓞 K) * s) •
        (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) =
        ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * c j) •
          ((s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
      rw [← algebraMap_smul K, ← algebraMap_smul K (_ * c j), smul_smul, smul_smul, map_mul, map_mul, map_mul,
        ← hcd j]
      congr 1
      change _ = _ * algebraMap (𝓞 K) K s
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.LocMatBasis
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.formallySmooth_stalk_unit_smooth_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → π.FormallySmooth := by
  first | exact @GlobalTheory.Nef.stalk_formallySmooth_of_smooth | exact GlobalTheory.Nef.stalk_formallySmooth_of_smooth | (intros; apply GlobalTheory.Nef.stalk_formallySmooth_of_smooth <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.groupSchemeUnitStalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  first | exact @GlobalTheory.Nef.stalkData_germ | exact GlobalTheory.Nef.stalkData_germ | (intros; apply GlobalTheory.Nef.stalkData_germ <;> assumption)
end
