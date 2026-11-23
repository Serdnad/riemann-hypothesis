module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle573
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.HTDiag

theorem theta_zero_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] (θ : R →+* S)
    {t w v : R} {n m : ℕ} (ht : t ≠ 0) (hθt : θ t = 0) (hv : θ v = 0 → v = 0)
    (h : t ^ n * w = t ^ m * v) (hnm : n ≠ m) : θ w = 0 := by
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e : t ^ (n + k + 1) = t ^ n * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hw : w = t ^ (k + 1) * v := mul_left_cancel₀ (pow_ne_zero n ht) h
    rw [hw, map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have e : t ^ (m + k + 1) = t ^ m * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hv' : v = t ^ (k + 1) * w := (mul_left_cancel₀ (pow_ne_zero m ht) h).symm
    have hv0 : v = 0 := hv (by rw [hv', map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul])
    rw [hv0, mul_zero] at h
    have h' : t ^ (k + 1) * w = 0 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ ht)
    have hw : w = 0 := (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ ht)
    rw [hw, map_zero]

end GlobalTheory.BKLim.HTDiag


open GlobalTheory.BKLim.HTDiag in
theorem GlobalTheory.BKLim.isHT_iff_diag : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  intro l _ K K' C hI ξ hξ a ρ H z u hKK'
  constructor
  · intro hm K'' p q x y hfix hxy
    obtain ⟨hdom, hinj, hF, -⟩ := BdRField.bdR_isField l
    haveI := hdom
    set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have hXu : IsUnit (ι (aDp l ξ)) := by
      have h1 := TiedUnif.isUnit_xi (core_isEps l C)
      rw [← hc0, map_mul, map_mul] at h1
      exact isUnit_of_mul_isUnit_right h1
    set e := ι (aDp l ξ) with he
    obtain ⟨i0, hie⟩ : ∃ i0, i0 * e = 1 := ⟨_, hXu.val_inv_mul⟩
    have ht0 : aDp l ξ ≠ 0 := by
      intro h0
      rw [he, h0, map_zero, mul_zero] at hie
      exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hie))

    have hVdet : IsUnit H.V.det := (Matrix.isUnit_iff_isUnit_det _).1 H.unit
    set W := H.V⁻¹ with hW
    have hVW : H.V * W = 1 := Matrix.mul_nonsing_inv _ hVdet
    have hWV : W * H.V = 1 := Matrix.nonsing_inv_mul _ hVdet
    have hWVι : W.map ι * H.V.map ι = 1 := by
      rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero _) (map_one _)]

    set d : Fin a → Per.BdR l := fun k => i0 ^ H.q * e ^ H.p k with hd
    set d' : Fin a → Per.BdR l := fun k => e ^ H.q * i0 ^ H.p k with hd'
    have hdd : ∀ k, d' k * d k = 1 := fun k => by
      calc d' k * d k = (i0 * e) ^ H.q * (i0 * e) ^ H.p k := by simp only [hd, hd']; ring
        _ = 1 := by rw [hie, one_pow, one_pow, one_mul]
    have hQ : H.Q = H.V.map ι * Matrix.diagonal d := by
      ext i k
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      have h := H.Q_eq i k
      simp only [map_mul, map_pow] at h
      rw [← he] at h
      calc H.Q i k = (i0 * e) ^ H.q * H.Q i k := by rw [hie, one_pow, one_mul]
        _ = i0 ^ H.q * (e ^ H.q * H.Q i k) := by ring
        _ = ι (H.V i k) * d k := by rw [h]; simp only [hd]; ring
    set Qi := Matrix.diagonal d' * W.map ι with hQi
    have hQiQ : Qi * H.Q = 1 := by
      rw [hQi, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (W.map ι), hWVι, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; exact hdd k
    have hQQi : H.Q * Qi = 1 := mul_eq_one_comm.1 hQiQ
    set av := Qi *ᵥ x with hav
    have hxa : x = H.Q *ᵥ av := by rw [hav, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    let K3 : FinExt l := ⟨K'.1 ⊔ K''.1, by
      haveI := K'.2; haveI := K''.2; exact IntermediateField.finiteDimensional_sup _ _⟩
    have hmono : ∀ {A B : FinExt l}, A.1 ≤ B.1 → ∀ g, g ∈ GK B → g ∈ GK A := fun h g hg =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (h hx)
    have h3' : K'.1 ≤ K3.1 := le_sup_left
    have h3'' : K''.1 ≤ K3.1 := le_sup_right
    have h3 : K.1 ≤ K3.1 := hKK'.trans h3'

    have hinv : ∀ g : GQ l, g ∈ GK K3 → ∀ j, Per.σD g (av j) = av j := by
      intro g hg
      let g' : ↥(GK K) := ⟨g, hmono h3 g hg⟩
      have h1 := hfix g' (hmono h3'' g hg)
      have h2 := H.inv g' (hmono h3' g hg)
      have hσx : (fun i => Per.σD (g' : GQ l) (x i)) =
          H.Q.map (Per.σD (g' : GQ l)) *ᵥ (fun k => Per.σD (g' : GQ l) (av k)) := by
        funext i
        rw [hxa]
        exact RingHom.map_mulVec _ _ _ i
      rw [hσx, Matrix.mulVec_mulVec, h2] at h1
      have h4 : av = (fun k => Per.σD (g' : GQ l) (av k)) := by
        calc av = Qi *ᵥ x := hav
          _ = Qi *ᵥ (H.Q *ᵥ (fun k => Per.σD (g' : GQ l) (av k))) := by rw [h1]
          _ = _ := by rw [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
      intro j
      exact (congrFun h4 j).symm
    choose c hcK hc using fun j => hI K3 (av j) (fun g hg => hinv g hg j)

    have hWx : ∀ k, e ^ q * (W.map ι *ᵥ x) k = e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k := by
      have hv : e ^ q • x = e ^ p • (fun i => ι (y i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hxy i, map_mul, map_pow]
      intro k
      have := congrFun (congrArg (fun v => W.map ι *ᵥ v) hv) k
      simpa [Matrix.mulVec_smul] using this
    have hD : ∀ k, aDp l ξ ^ (H.q + p) * (W *ᵥ y) k = aDp l ξ ^ (q + H.p k) * C.o (c k) := by
      intro k
      apply hinj
      have hck : ι (C.o (c k)) = av k := hc k
      rw [map_mul, map_mul, map_pow, map_pow, hck, RingHom.map_mulVec]
      have hak : av k = d' k * (W.map ι *ᵥ x) k := by
        rw [hav, hQi, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      rw [hak]
      calc e ^ (H.q + p) * (W.map ι *ᵥ (fun i => ι (y i))) k = e ^ H.q * (e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k) := by ring
        _ = e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k) := by rw [hWx k]
        _ = (i0 * e) ^ H.p k * (e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k)) := by rw [hie, one_pow, one_mul]
        _ = e ^ (q + H.p k) * (d' k * (W.map ι *ᵥ x) k) := by simp only [hd']; ring

    have hθξ : Per.θD l (aDp l ξ) = 0 := by
      rw [(thetaD_props l).2.2.2.1 ξ]
      have : Per.θ l ξ = 0 := RingHom.mem_ker.1 (hξ ▸ Ideal.mem_span_singleton_self ξ)
      rw [this]; rfl
    have hkey : ∀ k, z ^ ((H.p k : ℤ) - H.q) * Per.θD l ((W *ᵥ y) k) =
        z ^ ((p : ℤ) - q) * Per.θD l ((W *ᵥ y) k) := by
      intro k
      by_cases hk : (H.p k : ℤ) - H.q = (p : ℤ) - q
      · rw [hk]
      · have hz : Per.θD l ((W *ᵥ y) k) = 0 := by
          refine theta_zero_of_pow_eq (Per.θD l) ht0 hθξ ?_ (hD k) ?_
          · intro h0
            rw [C.o_sec.th] at h0
            have : c k = 0 := by
              first
                | exact (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
                | exact UniformSpace.Completion.coe_injective _ (by simpa using h0)
            rw [this, map_zero]
          · intro hn; apply hk; omega
        rw [hz, mul_zero, mul_zero]

    have hyw : y = H.V *ᵥ (W *ᵥ y) := by rw [Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]
    have hθy : (fun i => Per.θD l (y i)) = H.V.map (Per.θD l) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext i
      conv_lhs => rw [hyw]
      exact RingHom.map_mulVec _ _ _ i
    have hdiag : Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) =
        z ^ ((p : ℤ) - q) • (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext k
      rw [Matrix.mulVec_diagonal, hkey k]; rfl
    rw [hθy, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul]
  · intro hHT
    ext i j
    have h := hHT K' (H.p j) H.q (fun i => H.Q i j) (fun i => H.V i j) ?_ ?_
    · have := congrFun h i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.mul_apply]
      simp only [Matrix.map_apply]
      rw [this, mul_comm]
    · intro g hg
      funext i
      have := congrFun (congrFun (H.inv g hg) i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · intro i; exact H.Q_eq i j
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BCCancel

variable {R S T X Y : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

theorem cancel_comm (f : X →ₗ[R] Y) (z : T ⊗[S] (S ⊗[R] X)) :
    AlgebraTensorModule.cancelBaseChange R S T T Y ((f.baseChange S).lTensor T z) =
      f.baseChange T (AlgebraTensorModule.cancelBaseChange R S T T X z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem bij_up (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange S)) :
    Function.Bijective (f.baseChange T) := by
  have hl : Function.Bijective ((f.baseChange S).lTensor T) := by
    exact (LinearEquiv.lTensor T (LinearEquiv.ofBijective _ hf)).bijective
  have hfun : ⇑(f.baseChange T) = AlgebraTensorModule.cancelBaseChange R S T T Y ∘
      (f.baseChange S).lTensor T ∘ (AlgebraTensorModule.cancelBaseChange R S T T X).symm := by
    funext z
    simp only [Function.comp_apply, cancel_comm, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).bijective.comp
    (hl.comp (AlgebraTensorModule.cancelBaseChange R S T T X).symm.bijective)

theorem bij_down [Module.FaithfullyFlat S T] (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange T)) :
    Function.Bijective (f.baseChange S) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective S T]
  have hfun : ⇑((f.baseChange S).lTensor T) = (AlgebraTensorModule.cancelBaseChange R S T T Y).symm ∘
      f.baseChange T ∘ AlgebraTensorModule.cancelBaseChange R S T T X := by
    funext z
    simp only [Function.comp_apply, ← cancel_comm, LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).symm.bijective.comp
    (hf.comp (AlgebraTensorModule.cancelBaseChange R S T T X).bijective)

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP.BCCancel

theorem bij_lin {A B C N N' N'' : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    [Module B N'] [IsScalarTower A B N'] [AddCommGroup N''] [Module A N''] [Module B N''] [Module C N'']
    [IsScalarTower B C N''] [IsScalarTower A B N''] [IsScalarTower A C N'']
    (u : N →ₗ[A] N') (v : N' →ₗ[B] N'') (hv : IsBaseChange C v)
    (hw : IsBaseChange C ((v.restrictScalars A).comp u)) :
    Function.Bijective ((u.liftBaseChange B).baseChange C) := by
  set L := u.liftBaseChange B
  have h0 := TensorProduct.isBaseChange A N B
  have hc : IsBaseChange C ((v ∘ₗ L : B ⊗[A] N →ₗ[B] N'').restrictScalars A ∘ₗ TensorProduct.mk A B N 1) := by
    convert hw using 1
    ext x
    simp [L, LinearMap.liftBaseChange_tmul]
  have h1 : IsBaseChange C (v ∘ₗ L) := IsBaseChange.of_comp h0 hc
  have hfun : ⇑(L.baseChange C) = hv.equiv.symm ∘ h1.equiv := by
    funext z
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c p => simp [IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [hfun]
  exact hv.equiv.symm.bijective.comp h1.equiv.bijective

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP

theorem semiBC_of_cover : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h →
    ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N']
    [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N')
    (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w →
    SemiBC u := by
  intro l _ R _ B C h hc A _ k N _ _ _ _ N' _ _ _ _ N'' _ _ u v w hw hv hwb
  letI : Algebra A B.A := k.toAlgebra
  letI : Algebra B.A C.A := h.f.toAlgebra
  letI : Algebra A C.A := (h.f.comp k).toAlgebra
  haveI : IsScalarTower A B.A C.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module A N' := Module.compHom N' k
  haveI : IsScalarTower A B.A N' := ⟨fun a b x => mul_smul (k a) b x⟩
  letI : Module B.A N'' := Module.compHom N'' h.f
  letI : Module A N'' := Module.compHom N'' (h.f.comp k)
  haveI : IsScalarTower B.A C.A N'' := ⟨fun a b x => mul_smul (h.f a) b x⟩
  haveI : IsScalarTower A C.A N'' := ⟨fun a b x => mul_smul (h.f (k a)) b x⟩
  haveI : IsScalarTower A B.A N'' := ⟨fun a b x => by
    show h.f (k a * b) • x = h.f (k a) • (h.f b • x)
    rw [map_mul, mul_smul]⟩
  let u' : N →ₗ[A] N' := { toFun := u, map_add' := u.map_add, map_smul' := fun a x => u.map_smulₛₗ a x }
  let v' : N' →ₗ[B.A] N'' := { toFun := v, map_add' := v.map_add, map_smul' := fun a x => v.map_smulₛₗ a x }
  let w' : N →ₗ[A] N'' := { toFun := w, map_add' := w.map_add, map_smul' := fun a x => w.map_smulₛₗ a x }
  have hv' : IsBaseChange C.A v' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A N' N'' v v' fun _ => rfl).1 hv
  have hw' : IsBaseChange C.A ((v'.restrictScalars A).comp u') := by
    have := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A C.A N N'' w w' fun _ => rfl).1 hwb
    convert this using 1
    ext x
    exact (hw x).symm
  set L := u'.liftBaseChange B.A
  have hC : Function.Bijective (L.baseChange C.A) := BCCancel.bij_lin u' v' hv' hw'
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := hc.ff 1
  have hQ : Function.Bijective (L.baseChange (C.A ⧸ adI C ^ 1)) := BCCancel.bij_up (S := C.A) L hC
  have hB : Function.Bijective (L.baseChange (B.A ⧸ adI B ^ 1)) :=
    BCCancel.bij_down (T := C.A ⧸ adI C ^ 1) L hQ
  haveI : IsAdicComplete (adI B) B.A := B.complete
  have hJ : adI B ^ 1 ≤ Ideal.jacobson ⊥ := (pow_one (adI B)).le.trans (IsAdicComplete.le_jacobson_bot (adI B))
  have hL : Function.Bijective L := GlobalTheory.T.bijective_of_bijective_baseChange_quotient_jacobson B.A (adI B ^ 1) hJ (B.A ⊗[A] N) N' L hB
  have hu' : IsBaseChange B.A u' :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective L hL) fun x => by
      simp [L, LinearMap.liftBaseChange_tmul]
  exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B.A N N' u u' fun _ => rfl).2 hu'

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eq_zero_of_mem_adI_pow {l : ℕ} {R : Type} [CommRing R] (B : Obj l R) (x : B.A)
    (hx : ∀ n : ℕ, x ∈ adI B ^ n) : x = 0 := by
  refine B.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact hx n

theorem cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C),
    Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q →
      ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  intro l _ R _ B C h hc

  have hinj : ∀ m : ℕ, Function.Injective (qmap h m) := fun m =>
    RingHom.FaithfullyFlat.injective (hc.ff m)

  have hlev : ∀ (m : ℕ) (b : B.A), h.f b ∈ adI C ^ m → b ∈ adI B ^ m := fun m b hb => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj m
    rw [qmap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  refine ⟨fun x y hxy => ?_, fun D p q hpo c hpq => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow B _ fun n => hlev n _ ?_
    rw [map_sub, hxy, sub_self]; exact Ideal.zero_mem _
  ·
    have happ : ∀ m : ℕ, ∃ b : B.A, h.f b - c ∈ adI C ^ m := fun m => by
      have hd := (GlobalTheory.T.faithfullyFlat_descent_elements_pushout _ _ _ (qmap h m) (qmap p m) (qmap q m) (hc.ff m) (hpo.po m)).2
        (Ideal.Quotient.mk _ c) (by rw [qmap_mk, qmap_mk, hpq])
      obtain ⟨b', hb'⟩ := hd
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      refine ⟨b, ?_⟩
      rw [qmap_mk, Ideal.Quotient.eq] at hb'
      exact hb'
    choose b hb using happ
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (adI B ^ m • ⊤ : Submodule B.A B.A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine hlev m _ ?_
      have e : h.f (b m - b n) = (h.f (b m) - c) - (h.f (b n) - c) := by rw [map_sub]; ring
      rw [e]
      exact Ideal.sub_mem _ (hb m) (Ideal.pow_le_pow_right hmn (hb n))
    obtain ⟨L, hL⟩ := B.complete.toIsPrecomplete.prec' b hcauchy
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow C _ fun n => ?_
    have h1 : b n - L ∈ adI B ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    have h2 : h.f (b n - L) ∈ adI C ^ n := adI_pow_le h n h1
    have e : h.f L - c = (h.f (b n) - c) - h.f (b n - L) := by rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (hb n) h2

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem int_frob_lift (l : ℕ) [hl : Fact l.Prime] (a : ℤ) :
    ∃ b : ℤ, (RingHom.id ℤ) a = a ^ l + (l : ℤ) * b := by
  have h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l) := by
    push_cast; exact ZMod.pow_card _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩

def intDelta (l : ℕ) [hl : Fact l.Prime] : Delta l ℤ :=
  Delta.ofLift l (RingHom.id ℤ)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (int_frob_lift l)

theorem poly_δ_φ (l : ℕ) [hl : Fact l.Prime] (x : MvPolynomial ℕ ℤ) :
    (polyDelta (intDelta l)).δ ((polyDelta (intDelta l)).φ x) =
      (polyDelta (intDelta l)).φ ((polyDelta (intDelta l)).δ x) := by
  set D := polyDelta (intDelta l)
  have hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine mul_left_cancel₀ hl0 ?_
  have h1 := D.φ_eq (D.φ x)
  have h2 := D.φ_eq x
  have h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x) := by
    rw [map_mul, map_natCast]
  have h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) := by
    rw [← map_add (f := _), ← h2]
  rw [map_pow] at h4
  linear_combination -h1 + h4 + h3

theorem Delta.δ_φ_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A),
    D.δ (D.φ a) = D.φ (D.δ a) := by
  intro l hl A _ D a
  set D₀ := polyDelta (intDelta l)
  let g : MvPolynomial ℕ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)
  have hg : ∀ p, p ∈ δLocus D₀ D g := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      have : MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ) := by simp
      rw [this]; exact intCast_mem _ n
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp (mem_δLocus.2 ?_)
      rw [polyDelta_X]
      simp only [g, MvPolynomial.eval₂Hom_X']
      rw [Function.iterate_succ_apply']
  have hgδ : ∀ p, g (D₀.δ p) = D.δ (g p) := fun p => mem_δLocus.1 (hg p)
  have hgφ : ∀ p, g (D₀.φ p) = D.φ (g p) := Delta.map_φ_of_map_δ D₀ D g hgδ
  have hX : g (MvPolynomial.X 0) = a := by simp [g]
  have := congrArg g (poly_δ_φ l (MvPolynomial.X 0))
  rw [hgδ, hgφ, hgφ, hgδ, hX] at this
  exact this

end GlobalTheory.BSP
end
end
