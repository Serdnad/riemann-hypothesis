module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Normed.Field.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open Matrix UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}

private theorem entIn_mul_left (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem entIn_thetaLie {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (thetaLie X) := by
  intro a b
  have h1 : EntIn I (Jmat C m * Xᵀ) := entIn_mul_left _ (fun a b => hX b a)
  have h2 : EntIn I (Jmat C m * Xᵀ * Jmat C m) := entIn_mul_right _ h1
  unfold thetaLie
  rw [Matrix.neg_apply]
  exact I.neg_mem (h2 a b)

private theorem entIn_mul_zero (hI : I * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hm : X a c * Y c b ∈ I * I := Ideal.mul_mem_mul (hX a c) (hY c b)
  rw [hI] at hm
  exact (Submodule.mem_bot C).1 hm

private def onePlus (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) : GL (Fin m) C where
  val := 1 + X
  inv := 1 - X
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h]

private theorem act_onePlus (s : ℤˣ) (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) :
    ((sgnAct m C s (onePlus X h) : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [onePlus]
  · rw [sgnAct_neg_one, theta_val, if_neg (by decide)]
    show Jmat C m * (1 - X)ᵀ * Jmat C m = _
    rw [Matrix.transpose_sub, Matrix.transpose_one, mul_sub, sub_mul, mul_one, Jmat_mul_Jmat]
    unfold thetaLie
    rw [sub_eq_add_neg]

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.exists_isDeform :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C)
      (r : G →* GG (m := m) (R := C)) (γ : G → Matrix (Fin m) (Fin m) C), I * I = ⊥ →
      (∀ g, EntIn I (γ g)) → IsCoc r γ → ∃ r' : G →* GG (m := m) (R := C), IsDeform r γ r' := by
  intro G C _ _ m I r γ hI hγ hc
  have hsq : ∀ g, γ g * γ g = 0 := fun g => entIn_mul_zero hI (hγ g) (hγ g)
  let P : G → GG (m := m) (R := C) := fun g => SemidirectProduct.inl (onePlus (γ g) (hsq g)) * r g
  have hPr : ∀ g, (P g).right = (r g).right := fun g => by simp [P]
  have hPlG : ∀ g, (P g).left = onePlus (γ g) (hsq g) * (r g).left := fun g => by
    simp [P, SemidirectProduct.mul_left]
  have hPl : ∀ g, ((P g).left : Matrix (Fin m) (Fin m) C) = (1 + γ g) * (r g).mat := fun g => by
    rw [hPlG, Units.val_mul]
    rfl
  have h1 : γ 1 = 0 := by
    have := hc 1 1
    simpa using this
  refine ⟨{ toFun := P, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨hPr g, hPl g⟩⟩
  · apply SemidirectProduct.ext
    · apply Units.ext
      rw [hPl, h1]
      simp [GG.mat]
    · rw [hPr]
      simp
  · intro g h
    show P (g * h) = P g * P h
    apply SemidirectProduct.ext
    · apply Units.ext
      have had : adRep r g (γ h) = (r g).mat * (if (r g).right = 1 then γ h else thetaLie (γ h)) * ((r g).left⁻¹ : GL (Fin m) C) := rfl
      have hE : EntIn I (if (r g).right = 1 then γ h else thetaLie (γ h)) := by
        split_ifs
        · exact hγ h
        · exact entIn_thetaLie (hγ h)
      have hE2 := entIn_mul_right (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) (entIn_mul_left (r g).mat hE)
      have hMiMg : (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (r g).mat = 1 := by
        simp [GG.mat]
      have hz : γ g * ((r g).mat * (if (r g).right = 1 then γ h else thetaLie (γ h))) = 0 := by
        have h0 := entIn_mul_zero hI (hγ g) hE2
        calc _ = γ g * ((r g).mat * (if (r g).right = 1 then γ h else thetaLie (γ h)) * ((r g).left⁻¹ : GL (Fin m) C)) * (r g).mat := by
              rw [mul_assoc (γ g), mul_assoc _ (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C), hMiMg, mul_one]
          _ = 0 := by rw [h0, zero_mul]
      rw [hPl, SemidirectProduct.mul_left, Units.val_mul, hPl, hPr, hPlG h, map_mul ((sgnAct m C) (r g).right), Units.val_mul, act_onePlus, hc, had, map_mul r]
      simp only [GG.mat, SemidirectProduct.mul_left, Units.val_mul]
      simp only [GG.mat] at hMiMg hz
      generalize (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = Mi at hMiMg hz ⊢
      generalize (if (r g).right = 1 then γ h else thetaLie (γ h)) = Z at hz ⊢
      generalize ((r g).left : Matrix (Fin m) (Fin m) C) = Mg at hMiMg hz ⊢
      generalize (((sgnAct m C (r g).right) (r h).left : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = N
      have e1 : Mg * Z * Mi * (Mg * N) = Mg * Z * N := by
        rw [mul_assoc (Mg * Z), ← mul_assoc Mi, hMiMg, one_mul]
      have e2 : γ g * Mg * (Z * N) = 0 := by
        rw [mul_assoc (γ g), ← mul_assoc Mg, ← mul_assoc (γ g), hz, zero_mul]
      rw [add_mul, add_mul, e1]
      simp only [one_mul, add_mul, mul_add, mul_one, mul_assoc] at e2 ⊢
      rw [e2, add_zero]
      abel
    · rw [hPr, SemidirectProduct.mul_right, hPr, hPr, map_mul, SemidirectProduct.mul_right]
end

section

open Matrix UpperTheory.V.U3

private theorem sgnAct_tor {R : Type} [CommRing R] (s : ℤˣ) (t : Rˣ) :
    sgnAct (m := 3) (R := R) s (tor R t) = tor R t := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [theta_tor]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).left = tor R t * (r g).left * tor R t⁻¹ := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, sgnAct_tor, map_inv]

private theorem conj_right {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]

private theorem conj_mat {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G)
    (a b : Fin 3) :
    (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b := by
  show (((conjBy (tor R t) r g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = _
  rw [conj_left, Units.val_mul, Units.val_mul, tor_val, tor_val, mul_diagonal, diagonal_mul]
  have key : ((t ^ wt1 a : Rˣ) : R) * ((t⁻¹ ^ wt1 b : Rˣ) : R) = ((t ^ wt a b : Rˣ) : R) := by
    rw [← Units.val_mul, wt, _root_.zpow_sub, _root_.inv_zpow]
  rw [← key, GG.mat]
  ring

private theorem conj_zmat {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (c g₁ : G)
    (a b : Fin 3) :
    zmat c g₁ (conjBy (tor R t) r) a b = ((t ^ wt a b : Rˣ) : R) * zmat c g₁ r a b := by
  simp only [zmat, Matrix.sub_apply, conj_mat, mul_sub]

theorem UpperTheory.V.U3.conjBy_tor :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ),
    (∀ g a b, (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b) ∧ (∀ g, (conjBy (tor R t) r g).right = (r g).right) ∧
    (∀ c g₁, Normalised c g₁ r → Normalised c g₁ (conjBy (tor R t) r)) ∧ (∀ c g₁, zeta c g₁ (conjBy (tor R t) r) = zeta c g₁ r) ∧
    ∀ (η : G →* ℤˣ) (Ψ : G →* Rˣ), conjBy (tor R t) (r0 η Ψ) = r0 η Ψ := by
  intro G R _ _ r t
  refine ⟨conj_mat r t, conj_right r t, ?_, ?_, ?_⟩
  · intro c g₁ h
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      rw [conj_mat, h.atc]
      by_cases hab : a = b
      · subst hab
        simp [wt]
      · simp [Matrix.one_apply_ne hab]
    · rw [conj_zmat, h.z12, mul_zero]
    · rw [conj_zmat, h.z21, mul_zero]
  · intro c g₁
    unfold zeta
    rw [conj_zmat]
    simp [wt]
  · intro η Ψ
    refine MonoidHom.ext fun g => ?_
    refine SemidirectProduct.ext ?_ (conj_right _ t g)
    rw [conj_left, unitaryThreeReflection_left, ← map_mul, ← map_mul, mul_inv_cancel_comm]
end

section

open Matrix UpperTheory.V.U3

private theorem UpperTheory.V.U3.defcob_mul_zero {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}
    (hI : I * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) (hY : EntIn I Y)
    (A : Matrix (Fin m) (Fin m) C) : X * A * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h1 : (X * A) i k ∈ I := by
    rw [Matrix.mul_apply]
    exact I.sum_mem fun l _ => I.mul_mem_right _ (hX i l)
  have h2 := Ideal.mul_mem_mul h1 (hY k j)
  rw [hI] at h2
  exact h2

private theorem UpperTheory.V.U3.defcob_entIn {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}
    {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (A B : Matrix (Fin m) (Fin m) C) : EntIn I (A * Xᵀ * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine I.sum_mem fun k _ => I.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact I.sum_mem fun l _ => I.mul_mem_left _ (hX k l)

theorem UpperTheory.V.U3.isDeform_cob :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C)
      (r : G →* GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C), I * I = ⊥ → EntIn I X →
      ∃ h : GL (Fin m) C, (h : Matrix (Fin m) (Fin m) C) = 1 + X ∧ IsDeform r (cob r X) (conjBy h r) := by
  intro G C _ _ m I r X hI hX
  have hXX : X * X = 0 := by simpa using defcob_mul_zero hI hX hX 1
  let h : GL (Fin m) C := ⟨1 + X, 1 - X, by
    rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul, hXX]; simp, by
    rw [Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul, hXX]; simp⟩
  have hv : (h : Matrix (Fin m) (Fin m) C) = 1 + X := rfl
  have hi : ((h⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := rfl
  refine ⟨h, rfl, fun g => ⟨by simp [conjBy], ?_⟩⟩
  have hl : (conjBy h r g).mat = (1 + X) * (r g).mat *
      ((sgnAct (m := m) (R := C) (r g).right h⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp [conjBy, GG.mat, hv]
  have hc : cob r X g = X - (r g).adFun X := rfl
  have ha : (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (r g).mat = 1 :=
    Units.inv_mul _
  rw [hl, hc, GG.adFun]
  rcases Int.units_eq_one_or (r g).right with hs | hs
  · rw [hs, sgnAct_one, hi, ite_eq_left rfl]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    rw [defcob_mul_zero hI hX hX, Matrix.mul_assoc _ _ (r g).mat, ha, Matrix.mul_one]
    abel
  · have hJ : Jmat (R := C) m * (1 + X)ᵀ * Jmat (R := C) m =
        1 + Jmat (R := C) m * Xᵀ * Jmat (R := C) m := by
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Jmat_mul_Jmat]
    rw [hs, sgnAct_neg_one, theta_val, inv_inv, hv, hJ, ite_eq_right (by decide), thetaLie]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    rw [defcob_mul_zero hI hX (defcob_entIn hX _ _), Matrix.mul_assoc _ _ (r g).mat, ha,
      Matrix.mul_one, Matrix.mul_neg]
    abel
end

section

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.isDeform_normalised_iff :
    ∀ {G C : Type} [Group G] [CommRing C] (r r' : G →* GG (m := 3) (R := C))
      (γ : G → Matrix (Fin 3) (Fin 3) C) (c g₁ : G),
      Normalised c g₁ r → IsDeform r γ r' → (Normalised c g₁ r' ↔ NormCoc c g₁ r γ) := by
  intro G C _ _ r r' γ c g₁ hn hd
  have hc : (r' c).mat = 1 + γ c := by rw [(hd c).2, hn.atc, Matrix.mul_one]
  have hz : zmat c g₁ r' = zmat c g₁ r + zvar c g₁ r γ := by
    simp only [zmat, zvar, (hd _).2, Matrix.add_mul, Matrix.one_mul]
    abel
  have h12 : zmat c g₁ r' 0 1 = zvar c g₁ r γ 0 1 := by
    rw [hz, Matrix.add_apply, hn.z12, zero_add]
  have h21 : zmat c g₁ r' 1 0 = zvar c g₁ r γ 1 0 := by
    rw [hz, Matrix.add_apply, hn.z21, zero_add]
  constructor
  · intro h
    refine ⟨?_, h12 ▸ h.z12, h21 ▸ h.z21⟩
    have := h.atc
    rw [hc] at this
    exact add_eq_left.mp this
  · intro h
    exact ⟨by rw [hc, h.atc, add_zero], h12.trans h.z12, h21.trans h.z21⟩
end

section

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Emb

variable {m : ℕ} {R : Type*} [CommRing R]

def emb : GG (m := m) (R := R) →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R where
  toFun x := if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : GL (Fin m) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : GL (Fin m) R) 0
  map_one' := by
    have h : theta (1 : GL (Fin m) R) = 1 := map_one (thetaAut (m := m) (R := R))
    simp [GG.mat, h]
  map_mul' x y := by
    have h : ((-1 : ℤˣ) = 1) = False := by decide
    obtain ⟨a, s⟩ := x
    obtain ⟨b, t⟩ := y
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
      simp [GG.mat, h, theta_mul, theta_theta, Matrix.fromBlocks_multiply]

def wt6 : Fin 3 ⊕ Fin 3 → ℤ := Sum.elim wt1 wt1

end Emb

section Lift

variable (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]

def barChar (Ψ : Γ →* Oˣ) : Γ →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ

variable (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

def rbar : Γ →* GG (m := 3) (R := ResidueField O) := r0 η (barChar O Ψ)

@[ext] structure GLift (R : Type) [CommRing R] [Algebra O R] [IsCO O R] where
  hom : Γ →* GG (m := 3) (R := R)
  cont : ∀ a b, AdicCont (maximalIdeal R) fun g => (hom g).mat a b
  red : ∀ g, GG.map (res O R : R →+* ResidueField O) (hom g) = rbar O η Ψ g

variable {O η Ψ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']

theorem GLift.hasMult (r : GLift O η Ψ R) : HasMult η r.hom := fun g => congrArg SemidirectProduct.right (r.red g)

theorem GG.map_map {m : ℕ} {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C)
    (x : GG (m := m) (R := A)) : GG.map f' (GG.map f x) = GG.map (f'.comp f) x := rfl

def GLift.map (f : R →ₐ[O] R') (r : GLift O η Ψ R) : GLift O η Ψ R' where
  hom := (GG.map (f : R →+* R')).comp r.hom
  cont a b N := by
    have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
      show f y ∈ maximalIdeal R'
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    exact (r.cont a b N).comp (Ideal.quotientMap _ (f : R →+* R') hle)
  red g := by
    have e : (res O R' : R' →+* ResidueField O).comp (f : R →+* R') = (res O R : R →+* ResidueField O) :=
      RingHom.ext fun x => res_map (O := O) (R := R) (R' := R') f x
    rw [MonoidHom.comp_apply, GG.map_map, e, r.red]

def GLift.comap {H : Type} [Group H] [TopologicalSpace H] (φ : H →* Γ) (hφ : Continuous φ) (r : GLift O η Ψ R) :
    GLift O (η.comp φ) (Ψ.comp φ) R where
  hom := r.hom.comp φ
  cont a b N := (r.cont a b N).comp_continuous hφ
  red g := r.red (φ g)


variable (O η Ψ) in
def GCond (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) : Type 1 := ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], GLift O η Ψ R → Prop


variable (O η Ψ) in
def GCond.noCondition (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) : GCond O η Ψ := fun _ _ _ _ _ => True

def GRepresents (P : GCond O η Ψ) (r : GLift O η Ψ R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'],
    (∀ f : R →ₐ[O] R', P R' (r.map f)) ∧ ∀ r' : GLift O η Ψ R', P R' r' → ∃! f : R →ₐ[O] R', r.map f = r'

structure Univ (P : GCond O η Ψ) : Type 1 where
  R : Type
  [cr : CommRing R]
  [al : Algebra O R]
  [co : IsCO O R]
  r : GLift O η Ψ R
  rep : GRepresents P r

attribute [instance] Univ.cr Univ.al Univ.co

def OnI (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) : GCond O η Ψ :=
  fun R _ _ _ r => ∃ f : U.R →ₐ[O] R, U.r.map f = r ∧ I ≤ RingHom.ker f

def Kills (N : Set Γ) : GCond O η Ψ := fun _ _ _ _ r => ∀ g ∈ N, r.hom g = 1

def BoxCond (N : Set Γ) {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Γ) (hι : Continuous ι)
    (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) : GCond O η Ψ :=
  fun R _ _ _ r => Kills N R r ∧ OnI U I R (r.comap ι hι)

def NormCond (c g₁ : Γ) (P : GCond O η Ψ) : GCond O η Ψ :=
  fun R _ _ _ r => Normalised c g₁ r.hom ∧ P R r

end Lift

section Points

variable (O : Type) [CommRing O] {Γ R : Type} [Group Γ] [CommRing R] [Algebra O R]

def entAlg (r : Γ →* GG (m := 3) (R := R)) : Subalgebra O R := Algebra.adjoin O {x | ∃ g a b, x = (r g).mat a b}

def entMon (r : Γ →* GG (m := 3) (R := R)) (j : ℤ) : Set R :=
  {x | ∃ L : List (Γ × Fin 3 × Fin 3), (L.map fun s => wt s.2.1 s.2.2).sum = j ∧
    x = (L.map fun s => (r s.1).mat s.2.1 s.2.2).prod}

def weightZeroSubalgebra (r : Γ →* GG (m := 3) (R := R)) : Subalgebra O R := Algebra.adjoin O (entMon r 0)

variable {O} {κ : Type} [CommRing κ] [Algebra O κ]

def push (f : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) : Γ →* GG (m := 3) (R := κ) := (GG.map (f : R →+* κ)).comp r

def IsPush {A : Subalgebra O R} (ξ : A →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) (r' : Γ →* GG (m := 3) (R := κ)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, ∃ h : (r g).mat a b ∈ A, (r' g).mat a b = ξ ⟨_, h⟩

def tanCoc (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG (m := 3) (R := R)) (g : Γ) : Matrix (Fin 3) (Fin 3) κ :=
  ((r g).mat.map fun x => (F x).snd) *
    (((r g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map fun x => (F x).fst

def dualFst (F : R →ₐ[O] DualNumber κ) : R →ₐ[O] κ := (TrivSqZeroExt.fstHom O κ κ).comp F

def Rigid (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] κ) : Prop :=
  ∀ F : R →ₐ[O] DualNumber κ, dualFst F = f → ∃ X, tanCoc F r = cob (push f r) X

def RigidWt (j : ℤ) (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] κ) : Prop :=
  ∀ F : R →ₐ[O] DualNumber κ, dualFst F = f → (∀ g, tanCoc F r g ∈ gw (R := κ) j) → ∃ X, tanCoc F r = cob (push f r) X

def IsLocPt [IsLocalRing R] {κ : Type} [NormedField κ] [Algebra O κ] (f : R →ₐ[O] κ) : Prop :=
  ∀ x ∈ maximalIdeal R, ‖f x‖ < 1

end Points

section Base

variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

def baseLift (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) : GLift O η Ψ O where
  hom := r0 η Ψ
  cont a b := by
    by_cases h : a = b
    · subst h
      simpa [GG.mat, tor_val] using hΨ (wt1 a)
    · intro N
      simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ h]
      exact IsLocallyConstant.const _
  red g := by
    have e : ∀ x : O, res O O x = residue O x := fun x => (res O O).commutes x
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    show (tor (R := O) (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (res O O) = tor (R := ResidueField O) (barChar O Ψ g)
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [e]
    exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

end Base

end UpperTheory.V.U3
end
end
