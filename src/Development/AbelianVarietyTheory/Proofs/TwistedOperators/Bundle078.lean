module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOne
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.MatBd

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

theorem assoc_sigR (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] (x : (P ⊗[F] E) ⊗[F] R) :
    Algebra.TensorProduct.assoc F F F P E R (sigR (tConj P σ) R x) =
      tConj3 P σ R (Algebra.TensorProduct.assoc F F F P E R x) := by
  induction x with
  | tmul a r =>
    induction a with
    | tmul p e => simp [sigR, tConj, tConj3]
    | add a b ha hb => rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

def entry (σ : E →ₐ[F] E) (J γ : Matrix n n E) (i j : n) : plusAlg σ J γ ⊗[F] E →ₗ[F] E where
  toFun x := (plusTensor σ J γ x : Matrix n n E) i j
  map_add' a b := by rw [map_add (f := _)]; rfl
  map_smul' c a := by rw [map_smul]; rfl

theorem toMat_assoc_apply (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (x : (plusAlg σ J γ ⊗[F] E) ⊗[F] R) (i j : n) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R x) i j =
      LinearMap.rTensor R (entry σ J γ i j) x := by
  induction x with
  | tmul a r =>
    induction a with
    | tmul p e =>
      have h : (plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) =
          e • ((p : genAlg γ) : Matrix n n E) := by
        rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
        exact (Algebra.smul_def e ((p : genAlg γ) : Matrix n n E)).symm
      rw [Algebra.TensorProduct.assoc_tmul, LinearMap.rTensor_tmul]
      change (((p : genAlg γ) : Matrix n n E).map (inclE (F := F) R) *
        algebraMap (E ⊗[F] R) (Matrix n n (E ⊗[F] R)) (e ⊗ₜ r)) i j =
        ((plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) i j) ⊗ₜ r
      rw [h, ← Algebra.commutes, ← Algebra.smul_def]
      simp [inclE]
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), Matrix.add_apply, ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), Matrix.add_apply, ha, hb]

theorem toMat_assoc_inclE (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (β : plusAlg σ J γ ⊗[F] E) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R (inclE (F := F) R β)) =
      (plusTensor σ J γ β : Matrix n n E).map (inclE (F := F) R) := by
  ext i j
  rw [toMat_assoc_apply]
  rfl

theorem exists_centRat {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E} (h : IsRegular σ J γ)
    (β : plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (hβ : β * tConj _ σ β = 1) :
    ∃ δ ∈ centRat σ J γ, (δ : Matrix n n E) = plusTensor σ J (γ : Matrix n n E) β := by
  have h1 : (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) *
      adj (σ : E →+* E) J (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) = 1 := by
    rw [← plusTensor_tConj h, ← Subalgebra.coe_mul, ← map_mul, hβ, map_one]
    rfl
  refine ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, ⟨(mem_UJ_iff_mul_adj _ h.nondeg _).2 h1, ?_⟩, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
  exact (commute_of_mem_genAlg rfl (plusTensor σ J (γ : Matrix n n E) β).2).symm

theorem matOfNormBounded : MatOfNormBounded := by
  intro F E _ _ _ _ n _ _ σ J γ h _ _ hP hN
  obtain ⟨D, hD, hu⟩ := hN
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  letI : TopologicalSpace ((plusAlg σ J (γ : Matrix n n E) ⊗[F] E) ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (AdeleRing (𝓞 F) F)
  let a := Algebra.TensorProduct.assoc F F F (plusAlg σ J (γ : Matrix n n E)) E (AdeleRing (𝓞 F) F)
  have hc : Continuous fun x => toMat σ J (γ : Matrix n n E) (AdeleRing (𝓞 F) F) (a x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [a, toMat_assoc_apply]
    exact continuous_rTensor _ _
  refine ⟨_, hD.image hc, fun g hg => ?_⟩
  obtain ⟨u, hu1, hug⟩ := ((hP (AdeleRing (𝓞 F) F)).2.2 g).1 hg
  obtain ⟨x, hx⟩ := a.surjective u
  obtain ⟨β, hβ, hxβ⟩ := hu x (a.injective (by
    rw [map_mul, map_one, assoc_sigR]
    change a x * tConj3 _ σ _ (a x) = 1
    rw [hx]
    exact hu1))
  obtain ⟨δ, hδ, hδβ⟩ := exists_centRat h β hβ
  refine ⟨δ, hδ, _, hxβ, ?_⟩
  beta_reduce
  rw [map_mul, map_mul, hx, hug, toMat_assoc_inclE, hδβ]

end GlobalTheory.RegSS.MatBd
end
end

section

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem productMap_bijective_of_involution {F E L : Type} [Field F] [CharZero F] [CommRing E]
    [Algebra F E] [CommRing L] [Algebra F L] (f : E →ₐ[F] L) (τ : L ≃ₐ[F] L)
    (hτ : ∀ l, τ (τ l) = l) (P : Subalgebra F L) (hP : ∀ l, l ∈ P ↔ τ l = l)
    (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1) (h1 : τ (f (b 1)) = - f (b 1))
    (hd : d ≠ 0) (hsq : b 1 * b 1 = algebraMap F E d) :
    Function.Bijective (Algebra.TensorProduct.productMap P.val f) := by
  have hδ : f (b 1) * f (b 1) = algebraMap F L d := by rw [← map_mul, hsq, AlgHom.commutes]
  have hinv : algebraMap F L d⁻¹ * (f (b 1) * f (b 1)) = 1 := by
    rw [hδ, ← map_mul, inv_mul_cancel₀ hd, map_one]
  have h2 : algebraMap F L 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F L) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hval : ∀ a c : P, Algebra.TensorProduct.productMap P.val f (a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1) =
      (a : L) + (c : L) * f (b 1) := fun a c => by
    simp [Algebra.TensorProduct.productMap_apply_tmul]
  constructor
  · have hrep : ∀ x : P ⊗[F] E, ∃ a c : P, x = a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1 := by
      intro x
      induction x with
      | tmul p e =>
        refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
        conv_lhs => rw [← b.sum_repr e, Fin.sum_univ_two, h0]
        rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      | add x y hx hy =>
        obtain ⟨a, c, rfl⟩ := hx
        obtain ⟨a', c', rfl⟩ := hy
        exact ⟨a + a', c + c', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := hrep x
    rw [hval] at hx
    have hx' := congrArg τ hx
    rw [map_add (f := _), map_mul, map_zero, (hP _).1 a.2, (hP _).1 c.2, h1] at hx'
    have ha : (a : L) = 0 := by
      linear_combination (algebraMap F L 2⁻¹) * (hx + hx') - (a : L) * h2
    have hc : (c : L) = 0 := by
      linear_combination (algebraMap F L d⁻¹ * f (b 1)) * (hx - ha) - (c : L) * hinv
    rw [show a = 0 from Subtype.ext ha, show c = 0 from Subtype.ext hc]
    simp
  · intro l
    refine ⟨(⟨algebraMap F L 2⁻¹ * (l + τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] 1 +
      (⟨algebraMap F L 2⁻¹ * algebraMap F L d⁻¹ * f (b 1) * (l - τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] b 1,
      ?_⟩
    · rw [map_mul, map_add (f := _), hτ, AlgEquiv.commutes, add_comm]
    · rw [map_mul, map_mul, map_mul, map_sub, hτ, AlgEquiv.commutes, AlgEquiv.commutes, h1]
      ring
    · rw [hval]
      dsimp only
      linear_combination l * h2 + algebraMap F L 2⁻¹ * (l - τ l) * hinv

theorem plusTensorBijective : PlusTensorBijective := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  obtain ⟨τ, -, hτ, hE, hP⟩ := exists_adjEquiv h hA
  obtain ⟨b, d, h0, h1, hd, hsq⟩ := quad_exists_basis h.quad
  refine productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq
  rw [IsScalarTower.toAlgHom_apply, hE, h1, map_neg]

end GlobalTheory.RegSS
end

section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

private lemma cT_mul_mul_eq_iff_mul_adj_eq_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J g : Matrix n n A} (hJ : IsUnit J.det) :
    cT s g * J * g = J ↔ g * adj s J g = 1 := by
  rw [mul_eq_one_comm, adj]
  constructor
  · intro h
    calc J⁻¹ * cT s g * J * g = J⁻¹ * (cT s g * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have key : J * (J⁻¹ * cT s g * J * g) = J := by rw [h, Matrix.mul_one]
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul] using key

theorem pointsCentraliser_of_commutant_of_adjoint :
    PointsCommutant → PointsAdjoint → PointsCentraliser := by
  intro hC hA F E _ _ _ _ n _ _ σ J γ hreg hAlg hPlus R _ _
  obtain ⟨hinj, hcomm⟩ := hC F E n σ J γ hreg hAlg hPlus R
  refine ⟨hinj, fun u => hA F E n σ J γ hreg R u, fun g => ?_⟩
  have hJ : IsUnit (J.map (inclE (F := F) R)).det := by
    have h := hreg.nondeg.map (inclE (F := F) R)
    rw [RingHom.map_det] at h
    exact h
  have hb : ((bc (inclE (F := F) R) γ : GL n (E ⊗[F] R)) : Matrix n n (E ⊗[F] R)) =
      (γ : Matrix n n E).map (inclE (F := F) R) := rfl
  simp only [centPts, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  unfold UPts UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Units.ext_iff, Units.val_mul, hb]
  rw [cT_mul_mul_eq_iff_mul_adj_eq_one _ hJ]
  constructor
  · rintro ⟨hunit, hc⟩
    have hc' := congrArg Units.val hc.eq
    simp only [Units.val_mul, hb] at hc'
    obtain ⟨u, hu⟩ := (hcomm g).1 hc'
    have h1 : u * lConj σ J (γ : Matrix n n E) R u = 1 := by
      apply hinj
      rw [map_mul, hA F E n σ J γ hreg R u, hu, map_one, hunit]
    exact ⟨Units.mkOfMulEqOne u _ h1, h1, hu⟩
  · rintro ⟨u, hu, hg⟩
    have hu' : (u : LPts σ J (γ : Matrix n n E) R) * lConj σ J (γ : Matrix n n E) R u = 1 := hu
    refine ⟨?_, ?_⟩
    · rw [← hg, ← hA F E n σ J γ hreg R, ← map_mul, hu', map_one]
    · change g * _ = _ * g
      apply Units.ext
      simpa only [Units.val_mul, hb] using (hcomm g).2 ⟨u, hg⟩

end GlobalTheory.RegSS
end

section

open GlobalTheory.RegSS Matrix

namespace GlobalTheory.RegSS.Semilocal


open Matrix in
theorem _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A) :
    (_root_.GlobalTheory.RegSS.krylov M v).map f = _root_.GlobalTheory.RegSS.krylov (M.map f) (f ∘ v) := by
  ext i j
  simp only [_root_.GlobalTheory.RegSS.krylov, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec]
  congr 2
  exact RingHom.map_pow f.mapMatrix M _


open Matrix in
theorem _root_.GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField :
    _root_.GlobalTheory.RegSS.CyclicField → _root_.GlobalTheory.RegSS.CyclicSemilocal := by
  intro hF A _ _ n _ _ M hM
  have hw : ∀ p : MaximalSpectrum A, ∃ w : n → A ⧸ p.asIdeal,
      IsUnit (_root_.GlobalTheory.RegSS.krylov (M.map (Ideal.Quotient.mk p.asIdeal)) w).det := by
    intro p
    haveI := p.isMaximal
    letI := Ideal.Quotient.field p.asIdeal
    exact hF _ n _ (by rw [Matrix.charpoly_map]; exact hM.map)
  choose w hw using hw
  have hcop : Pairwise (Function.onFun IsCoprime fun p : MaximalSpectrum A => p.asIdeal) :=
    fun p q hpq => Ideal.isCoprime_iff_sup_eq.mpr
      (p.isMaximal.coprime_of_ne q.isMaximal (mt MaximalSpectrum.ext hpq))
  have hs : ∀ y : ∀ p : MaximalSpectrum A, A ⧸ p.asIdeal,
      ∃ a : A, ∀ p, Ideal.Quotient.mk p.asIdeal a = y p := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, fun p => by rw [← hx]; rfl⟩
  choose v hv using fun j => hs fun p => w p j
  refine ⟨v, ?_⟩
  by_contra h
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let p : MaximalSpectrum A := ⟨I, hI⟩
  have hvp : (Ideal.Quotient.mk p.asIdeal) ∘ v = w p := funext fun j => hv j p
  have hzero : Ideal.Quotient.mk p.asIdeal (_root_.GlobalTheory.RegSS.krylov M v).det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [RingHom.map_det, RingHom.mapMatrix_apply, _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hvp] at hzero
  haveI := p.isMaximal
  exact (hw p).ne_zero hzero

end GlobalTheory.RegSS.Semilocal
end

section

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS.CptQuot

theorem continuous_adj {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ) (J : Matrix n n A) :
    Continuous (adj σ J) := by
  unfold adj
  have hc : Continuous (fun l : Matrix n n A => cT σ l) := by
    unfold Formalism.UG.cT
    exact (continuous_id.matrix_map hσ).matrix_transpose
  exact (continuous_const.matrix_mul hc).matrix_mul continuous_const

theorem exists_isCompact {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    {J : Matrix n n A} (hJ : IsUnit J.det) (γ : GL n A) {D : Set (Matrix n n A)}
    (hD : IsCompact D) :
    ∃ K : Set (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)), IsCompact K ∧
      ∀ g : (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)),
        ((g : GL n A) : Matrix n n A) ∈ D → g ∈ K := by
  have hca := continuous_adj σ hσ J
  let C : Set (Matrix n n A) := D ∩ {M | M * adj σ J M = 1 ∧ adj σ J M * M = 1 ∧
    M * (γ : Matrix n n A) = (γ : Matrix n n A) * M}
  have hCc : IsCompact C := by
    refine hD.inter_right ?_
    exact (isClosed_eq (continuous_id.matrix_mul hca) continuous_const).inter
      ((isClosed_eq (hca.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const)
          (continuous_const.matrix_mul continuous_id)))
  let u : C → GL n A := fun M => ⟨M.1, adj σ J M.1, M.2.2.1, M.2.2.2.1⟩
  have hu : ∀ M : C, u M ∈ (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := by
    intro M
    refine Subgroup.mem_inf.2 ⟨(mem_UJ_iff_adj_mul σ hJ (u M)).2 M.2.2.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact M.2.2.2.2.symm
  let f : C → (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := fun M => ⟨u M, hu M⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, hca.comp continuous_subtype_val⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro g hg
  have hg' := Subgroup.mem_inf.1 g.2
  have h1 := (mem_UJ_iff_mul_adj σ hJ (g : GL n A)).1 hg'.1
  have h2 := (mem_UJ_iff_adj_mul σ hJ (g : GL n A)).1 hg'.1
  have h3 : ((g : GL n A) : Matrix n n A) * γ = γ * (g : GL n A) := by
    have hc := congrArg Units.val (Subgroup.mem_centralizer_iff.1 hg'.2 γ (Set.mem_singleton γ))
    rw [Units.val_mul, Units.val_mul] at hc
    exact hc.symm
  refine ⟨⟨_, hg, h1, h2, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

theorem compactOfMatBounded (hL : TensorLattice) : CompactOfMatBounded := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hM
  have := quad_finite hreg.quad
  obtain ⟨hTR, -, hT2, -⟩ := hL F E
  obtain ⟨D, hD, hDg⟩ := hM
  let : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  have : IsTopologicalRing (E ⊗[F] AdeleRing (𝓞 F) F) := hTR
  have : T2Space (E ⊗[F] AdeleRing (𝓞 F) F) := hT2
  have hD' : IsCompact D := hD
  have hσ' : Continuous (sigR σ (AdeleRing (𝓞 F) F)) := continuous_sigR σ (AdeleRing (𝓞 F) F)
  have hJ' : IsUnit (J.map (inclE (F := F) (AdeleRing (𝓞 F) F))).det :=
    isUnit_det_map (inclE (F := F) (AdeleRing (𝓞 F) F)) hreg.nondeg
  have key : ∃ K : Set (centPts σ J γ (AdeleRing (𝓞 F) F)), IsCompact K ∧
      ∀ g : centPts σ J γ (AdeleRing (𝓞 F) F),
        ((g : GL n (E ⊗[F] AdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) ∈ D →
          g ∈ K :=
    exists_isCompact (sigR σ (AdeleRing (𝓞 F) F)) hσ' hJ'
      (bc (inclE (F := F) (AdeleRing (𝓞 F) F)) γ) hD'
  obtain ⟨K, hK, hKD⟩ := key
  have hδc : ∀ δ ∈ centRat σ J γ,
      bc (inclE (F := F) (AdeleRing (𝓞 F) F)) δ ∈ centPts σ J γ (AdeleRing (𝓞 F) F) := by
    intro δ hδ
    have hδ' := Subgroup.mem_inf.1 (show δ ∈ UJ (σ : E →+* E) J ⊓ Subgroup.centralizer {γ} from hδ)
    have hadj := (mem_UJ_iff_adj_mul (σ : E →+* E) hreg.nondeg δ).1 hδ'.1
    have hcomm := Subgroup.mem_centralizer_iff.1 hδ'.2 γ (Set.mem_singleton γ)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show _ ∈ UJ (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
      rw [mem_UJ_iff_adj_mul _ hJ']
      show adj (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
          ((δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F))) *
          (δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F)) = 1
      rw [adj_map (σ : E →+* E) (sigR σ (AdeleRing (𝓞 F) F)) (inclE (F := F) (AdeleRing (𝓞 F) F))
        (fun x => inclE_conj σ (AdeleRing (𝓞 F) F) x) hreg.nondeg, ← Matrix.map_mul, hadj,
        Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hcomm]
  refine ⟨?_⟩
  have himg : (QuotientGroup.mk '' K : Set (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
      ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
        (centPts σ J γ (AdeleRing (𝓞 F) F)))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨δ, hδ, hgδ⟩ := hDg g g.2
    refine ⟨g * ⟨_, hδc δ hδ⟩, hKD _ hgδ, ?_⟩
    exact QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hδ, rfl⟩))
  rw [← himg]
  exact hK.image QuotientGroup.continuous_mk

end GlobalTheory.RegSS.CptQuot
end
end

section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem pointsAdjoint_toMat_tmul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (c : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ c) = c • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l c

theorem pointsAdjoint : PointsAdjoint := by
  intro F E _ _ _ _ n _ _ σ J γ h R _ _ u
  induction u using TensorProduct.induction_on with
  | zero => simp [adj_zero]
  | tmul a b =>
    have ha := (adj_eq_iff _ h.nondeg _ _).2 a.2
    have hc : lConj σ J (γ : Matrix n n E) R (a ⊗ₜ b) = a ⊗ₜ sigR σ R b := rfl
    rw [hc, pointsAdjoint_toMat_tmul,
      pointsAdjoint_toMat_tmul, adj_smul,
      adj_map (σ : E →+* E) (sigR σ R) (inclE (F := F) R) (inclE_conj σ R) h.nondeg, ha]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), adj_add, ha, hb]

end GlobalTheory.RegSS
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict : ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  first | exact @GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | exact GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | (intros; apply GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding <;> assumption)
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F), x * y = 1 → ‖(x : Fv F v)‖ = 1 := by
  first | exact @GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one | exact GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one | (intros; apply GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one <;> assumption)
end
