module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
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
public import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcris_teichmuller_tilt_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l), ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  first | exact @GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | exact GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | (intros; apply GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.PolyInertia

theorem matKO_smul_one {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (s : O) (z : KOG O k) :
    matKO (s • (1 : Matrix (Fin k) (Fin k) O)) z = s • z := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul]
  unfold matKO
  rw [Submodule.mapQ_apply]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, Algebra.smul_def, Matrix.algebraMap_matrix_apply]

theorem aeval_map_eq_sum {T O A : Type} [CommRing T] [CommRing O] [Ring A] [Algebra O A]
    (f : T →+* O) (P : Polynomial T) (a : A) :
    Polynomial.aeval a (P.map f) = ∑ k : Fin (P.natDegree + 1), f (P.coeff k) • a ^ (k : ℕ) := by
  rw [Polynomial.aeval_eq_sum_range' (n := P.natDegree + 1)
    (Nat.lt_succ_of_le Polynomial.natDegree_map_le), Finset.sum_range]
  simp only [Polynomial.coeff_map]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  intro D i r ρ π Xs S _ hG _ v hv hP c
  obtain ⟨P, hP0, hPu⟩ := hP
  obtain ⟨-, hdec, hψ, -, -, -, -, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  set γ0 := D.nd.gam0 i v with hγ0
  let a : S.X' → MatN D.nd i := fun x' =>
    Polynomial.aeval (rO D.nd i r (S.p x') γ0) (P.map (evT D.nd i (S.p x')))
  have ha_eq : ∀ x', a x' = ∑ k : Fin (P.natDegree + 1),
      evT D.nd i (S.p x') (P.coeff k) • rO D.nd i r (S.p x') (γ0 ^ (k : ℕ)) := by
    intro x'
    simp only [a, aeval_map_eq_sum, map_pow]
  have ha : InR' D.nd r S a := by
    refine ⟨P.natDegree + 1, fun k x' => evT D.nd i (S.p x') (P.coeff k), fun k => γ0 ^ (k : ℕ),
      fun k => hT _ (P.coeff k).2, ?_⟩
    funext x'
    rw [ha_eq, Finset.sum_apply]
  have h1 : InR' D.nd r S 1 := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
    funext x'
    simp
  have hchi : chiU D.nd i ((c : ℕ) + 1) γ0 = chiU D.nd i 1 γ0 :=
    (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v (D.nd.SQ_l i v (Or.inl hv)) γ0 (D.nd.locNd_chebotarevPlace_mem i v)).2 _
      (Nat.le_add_left _ _) c.2
  have hval : S.ψχ c a = (P.map (evT D.nd i π)).eval (D.nd.zeta i v) := by
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    let u := S.e.symm (0, Pi.single c 1)
    have hu : (S.e u).2 c = 1 := by simp [u]
    have e1 := congrArg (fun z => z.2 c) (hψ a ha u)
    simp only [hu, mul_one] at e1
    have e2 : ((a S.π').map (toK D.nd i)).mulVec u = ∑ k : Fin (P.natDegree + 1),
        toK D.nd i (evT D.nd i π (P.coeff k)) •
          (mapM (toK D.nd i) (rO D.nd i r π) (γ0 ^ (k : ℕ))).mulVec u := by
      rw [ha_eq, hπ]
      change ((toK D.nd i).mapMatrix _).mulVec u = _

      rw [map_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.smul_mulVec]
      congr 1
      ext p q
      simp [mapM]

    rw [e2, map_sum, Prod.snd_sum, Finset.sum_apply] at e1
    change toK D.nd i _ = toK D.nd i _

    rw [← e1, ← Polynomial.coe_aeval_eq_eval, aeval_map_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hdec]
    simp only [Prod.smul_snd, Pi.smul_apply, hu, mul_one, map_pow, hchi, smul_eq_mul, map_mul,
      Units.val_pow_eq_pow_val]
    rfl
  rw [resIne, cocChi, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, hφ, hφ0, rfl⟩, rfl⟩
  funext γ
  change φ (yg D.nd r S γ) = 0
  have hy : InY D.nd r S (yg D.nd r S γ) :=
    ⟨1, fun _ => 1, fun _ => γ, fun _ => h1, by simp⟩
  have hay : InY D.nd r S (a * yg D.nd r S γ) :=
    ⟨1, fun _ => a, fun _ => γ, fun _ => ha, by simp⟩
  have hz : φ (a * yg D.nd r S γ) = 0 := by
    refine hφ0 _ hay fun x' hx' => ?_
    have h := hP0 (S.p x') hx' γ γ.2
    have : yg D.nd r S γ x' = (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) *
          Eel D.nd S x') := by
      rw [yg, sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [Pi.mul_apply, this, mul_smul_comm, ← mul_assoc]
    simp only [a]
    rw [h, zero_mul, smul_zero]
  rw [hφ a ha _ hy, matKO_smul_one, hval] at hz
  exact hPu.smul_eq_zero.mp hz

end GlobalTheory.Cut.PolyInertia
end

section

noncomputable section

namespace GlobalTheory.GLq.LabelDet

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Formalism.CyclotomicNorms Polynomial
open scoped Classical ComplexOrder

variable {g : ℕ} [hg : Fact g.Prime]


open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.isIrr_hom {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ) :
    _root_.GlobalTheory.GLq.IsIrr (fun x : G => ((φ x : ℂˣ) : ℂ)) := by
  have hchar : ∀ x : G, (FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ)).character x = φ x := by
    intro x
    have : _root_.GlobalTheory.GLp.Model.chRep φ x = (φ x : ℂ) • LinearMap.id := by
      ext; simp [_root_.GlobalTheory.GLp.Model.chRep_apply]
    simp [FDRep.character, FDRep.of_ρ, this]
  refine ⟨FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ), ?_, hchar⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hchar, Nat.card_eq_fintype_card]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.theta_gen_pow (L : _root_.GlobalTheory.GLq.LabelDatum g) {x : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hx : x ^ (g ^ 1 - 1) = 1) (n : ℕ) :
    _root_.GlobalTheory.GLq.thetaOf L 1 x (L.gen 1 ^ n) =
      L.teich x ^ n :=
  _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos hx n


open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.gen_one_mem (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 := by
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.GLp.Model.exists_gen L
  exact ⟨u, hu⟩


open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_inPar (a b : ℕ) (M : _root_.GlobalTheory.GLq.Mt g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a M) :
    M.det = (_root_.GlobalTheory.GLq.tl a M).det * (_root_.GlobalTheory.GLq.br a b M).det := by
  have key : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (_root_.GlobalTheory.GLq.tl a M)
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a)) 0 (_root_.GlobalTheory.GLq.br a b M) := by
    ext (i | i) (j | j)
    · show M (Fin.castAdd b i) (Fin.castAdd b j) = _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j
      have hi := i.isLt
      have hj := j.isLt
      unfold _root_.Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dite_eq_left ⟨by omega, by omega⟩]
      rfl
    · simp
    · exact h _ _ (by simp) (by simp)
    · simp [_root_.GlobalTheory.GLq.br, _root_.Formalism.MainNotions.ArithmeticCylinders.entN, Fin.natAdd]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, key, Matrix.det_fromBlocks_zero₂₁]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_toG {n : ℕ} (M : _root_.GlobalTheory.GLq.Mt g n) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG M) : (ZMod g)ˣ) : ZMod g) = M.det := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dite_eq_left ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))]
  simp [Matrix.GeneralLinearGroup.val_det_apply]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_par (a b : ℕ) (p : _root_.GlobalTheory.GLq.Gn g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a (p : _root_.GlobalTheory.GLq.Mt g (a + b))) :
    Matrix.GeneralLinearGroup.det p =
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) *
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) := by
  have hdet := _root_.GlobalTheory.GLq.LabelDet.det_inPar a b _ h
  have hp := (Matrix.GeneralLinearGroup.det p).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hp
  rw [hdet] at hp
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
  apply Units.ext
  rw [Units.val_mul, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h1, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h2,
    Matrix.GeneralLinearGroup.val_det_apply, ← hdet]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.toG_one {n : ℕ} : _root_.GlobalTheory.GLq.toG (1 : _root_.GlobalTheory.GLq.Mt g n) = 1 := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dite_eq_left isUnit_one]
  exact Units.ext (by simp)

end GlobalTheory.GLq.LabelDet
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.FrobRecHC

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem inPar_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
  obtain ⟨P, hP⟩ := (par_basic g a b (a + b) rfl).1
  exact (hP _).1 (P.inv_mem ((hP x).2 h))

theorem inPar_inv_iff (x : Gn g (a + b)) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) ↔ InPar a (x : Mt g (a + b)) :=
  ⟨fun h => by simpa using inPar_inv x⁻¹ h, inPar_inv x⟩

theorem tl_one : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [tl_apply]
  simp [Matrix.one_apply]

theorem br_one : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [br_apply]
  simp [Matrix.one_apply]

theorem toG_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    (toG (tl a (x : Mt g (a + b))))⁻¹ = toG (tl a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) ∧
    (toG (br a b (x : Mt g (a + b))))⁻¹ = toG (br a b ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) := by
  have hi := inPar_inv x h
  have hm := blocks_mul (x : Mt g (a + b)) ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) h hi
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, tl_one, br_one] at hm
  have u1 := isUnit_blocks x h
  have u2 := isUnit_blocks _ hi
  constructor
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.1, toG_val u2.1, ← hm.2.1, Units.val_one]
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.2, toG_val u2.2, ← hm.2.2, Units.val_one]

def fz (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (z : Gn g (a + b)) : ℂ :=
  χ z * (if InPar a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)) then
    Φ (toG (tl a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)))) (toG (br a b ((z⁻¹ : Gn g (a + b)) : Mt g (a + b))))
    else 0)

theorem lhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (hχ : IsClass χ) :
    ip χ (hcT a b Φ (a + b)) =
      ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
        ∑ z, fz χ Φ z := by
  have key : ∀ y : Gn g (a + b), (∑ x : Gn g (a + b), χ x *
      (if InPar a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)) then
        Φ (toG (tl a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b))))
          (toG (br a b ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)))) else 0)) = ∑ z, fz χ Φ z := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ fun z => ?_
    have e : y⁻¹ * ((MulAut.conj y).toEquiv z)⁻¹ * y = z⁻¹ := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e, fz]
    congr 1
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    exact (hχ z y).symm
  unfold ip hcT
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hN : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc _ = (Fintype.card (Gn g (a + b)) : ℂ)⁻¹ * ∑ y : Gn g (a + b),
        ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
          ∑ z, fz χ Φ z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← key y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul, Finset.mul_sum]

theorem fz_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    fz χ Φ x = if InPar a (x : Mt g (a + b)) then
      χ x * Φ (toG (tl a (x : Mt g (a + b))))⁻¹ (toG (br a b (x : Mt g (a + b))))⁻¹ else 0 := by
  rw [fz, inPar_inv_iff]
  split_ifs with h
  · rw [(toG_inv x h).1, (toG_inv x h).2]
  · rw [mul_zero]

theorem fibre_sum (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    (∑ p : Gn g a × Gn g b, if InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b) then χ x * Φ p.1⁻¹ p.2⁻¹ else 0) = fz χ Φ x := by
  rw [fz_eq]
  by_cases h : InPar a (x : Mt g (a + b))
  · have hu := isUnit_blocks x h
    rw [if_pos h]
    have hc : ∀ p : Gn g a × Gn g b, (InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b)) ↔ (toG (tl a (x : Mt g (a + b))), toG (br a b (x : Mt g (a + b)))) = p := by
      intro p
      rw [Prod.ext_iff, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
      simp [h]
    simp_rw [hc]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

theorem rhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) :
    ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) =
      ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ * ∑ z, fz χ Φ z := by
  unfold ip res
  simp only [Prod.fst_inv, Prod.snd_inv, Fintype.card_prod]
  simp_rw [← fibre_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> push_cast <;> ring

theorem hcT_adjoint : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ),
    IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  intro g _ a b n hn χ Φ hχ
  subst hn
  rw [lhs_eq χ Φ hχ, rhs_eq, card_par]

end GlobalTheory.GLq.FrobRecHC
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.ZSumOne

open CategoryTheory

variable {G : Type} [Group G] [Fintype G]

theorem zOf_coeff (χ : G → ℂ) (y : G) : (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem irr_one_eq_finrank {χ : G → ℂ} {V : FDRep ℂ G} (hV : ∀ x, V.character x = χ x) :
    χ 1 = (Module.finrank ℂ V : ℂ) := by
  rw [← hV 1, FDRep.char_one]

theorem zOf_eq_zIdem (χ : G → ℂ) (V : FDRep ℂ G) (hV : ∀ x, V.character x = χ x) :
    zOf χ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem V := by
  have h1 := irr_one_eq_finrank hV
  unfold zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, ← hV x⁻¹]
  rfl

theorem zOf_injOn : Set.InjOn (zOf (G := G)) {χ | IsIrr χ} := by
  intro χ hχ χ' hχ' h
  obtain ⟨V, hs, hV⟩ := hχ
  obtain ⟨V', hs', hV'⟩ := hχ'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 := irr_one_eq_finrank hV
  have h1' := irr_one_eq_finrank hV'
  have e1 := congrArg (fun a => a.coeff 1) h
  simp only [zOf_coeff, inv_one] at e1
  rw [h1, h1'] at e1
  have e2 : ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) =
      ((Module.finrank ℂ V' * Module.finrank ℂ V' : ℕ) : ℂ) := by
    push_cast
    field_simp at e1
    linear_combination e1
  have hn : Module.finrank ℂ V = Module.finrank ℂ V' := Nat.mul_self_inj.mp (by exact_mod_cast e2)
  have h11 : χ 1 = χ' 1 := by rw [h1, h1', hn]
  haveI := PI.GreenLabelSurjWork.nontrivial_of_simple V hs
  have hpos : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hk : χ 1 / (Fintype.card G : ℂ) ≠ 0 := div_ne_zero (h1 ▸ hpos) hc
  funext y
  have e3 := congrArg (fun a => a.coeff y⁻¹) h
  simp only [zOf_coeff, inv_inv] at e3
  rw [← h11] at e3
  exact mul_left_cancel₀ hk e3

theorem zOf_image :
    zOf '' {χ : G → ℂ | IsIrr χ} =
      {z : MonoidAlgebra ℂ G | ∃ τ : FDRep ℂ G, Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z} := by
  ext z
  constructor
  · rintro ⟨χ, ⟨V, hs, hV⟩, rfl⟩
    exact ⟨V, hs, (zOf_eq_zIdem χ V hV).symm⟩
  · rintro ⟨τ, hs, rfl⟩
    exact ⟨τ.character, ⟨τ, hs, fun _ => rfl⟩, zOf_eq_zIdem _ τ fun _ => rfl⟩

end GlobalTheory.GLq.ZSumOne

namespace GlobalTheory.GLq

theorem irr_finite_and_finsum_zOf_eq_one : ∀ (G : Type) [Group G] [Fintype G],
    {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  intro G _ _
  have hZ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one G
  rw [← ZSumOne.zOf_image] at hZ
  refine ⟨Set.Finite.of_finite_image hZ.1 ZSumOne.zOf_injOn, ?_⟩
  have himg := finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) (ZSumOne.zOf_injOn (G := G))
  rw [← himg]
  exact hZ.2

end GlobalTheory.GLq
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.reducible_of_stable_rational_rowSubspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  first | exact @GlobalTheory.PMon.splits_of_stable_rat_subspace | exact GlobalTheory.PMon.splits_of_stable_rat_subspace | (intros; apply GlobalTheory.PMon.splits_of_stable_rat_subspace <;> assumption)
end
