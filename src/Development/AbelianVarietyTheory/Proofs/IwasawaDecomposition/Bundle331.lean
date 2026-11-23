module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle314
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RootUnip

open GlobalTheory.BesselCompare (hA_add hA_smul hA_smul_right)

variable {D : D7} {B : HSp D}

def kMat (B : HSp D) (v y : Fin B.rank → AE D) : Matrix (Fin B.rank) (Fin B.rank) (AE D) :=
  1 + vecMulVec v ((fun i => cA D (y i)) ᵥ* B.gram.map (incA D)) -
    vecMulVec y ((fun i => cA D (v i)) ᵥ* B.gram.map (incA D))

theorem kMat_mulVec (v y x : Fin B.rank → AE D) :
    (kMat B v y).mulVec x = x + hA B x y • v - hA B x v • y := by
  rw [kMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, hA_eq, hA_eq, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  simp only [op_smul_eq_smul]

theorem continuous_rankTwo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    {c : R → R} (hc : Continuous c) (J : Matrix (Fin n) (Fin n) R) (v w : Fin n → R) :
    Continuous fun y : Fin n → R => 1 + vecMulVec v ((fun i => c (y i)) ᵥ* J) - vecMulVec y w := by
  have hc' : Continuous fun y : Fin n → R => fun i => c (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  have h1 := continuous_const (y := v).matrix_vecMulVec (hc'.matrix_vecMul (continuous_const (y := J)))
  have h2 := (continuous_id (X := Fin n → R)).matrix_vecMulVec (continuous_const (y := w))
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (continuous_const.add (h1.matrix_elem i j)).sub (h2.matrix_elem i j)

theorem continuous_kMat (v : Fin B.rank → AE D) : Continuous (kMat B v) :=
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  continuous_rankTwo GlobalTheory.FockCompare.ThetaCont.continuous_conj _ _ _

section

variable {η : AE D} (hη : η * cA D η = 0) {v y : Fin B.rank → AE D} (hy : η • y = y) (hv : hA B v y = 0)

include hη hy in
theorem hA_smul_self (x : Fin B.rank → AE D) : hA B x y • y = 0 := by
  have e : hA B x y = cA D η * hA B x y := by rw [← hA_smul_right, hy]
  rw [e, ← hy, smul_smul, hy, mul_assoc, mul_comm (hA B x y), ← mul_assoc, mul_comm (cA D η), hη, zero_mul,
    zero_smul]

include hη hy in
theorem hA_mul_hA (x x' : Fin B.rank → AE D) : hA B x y * hA B y x' = 0 := by
  rw [← hA_smul, hA_smul_self hη hy, hA_zero]

include hη hy in
theorem hA_self : hA B y y = 0 := by
  have e : hA B y y = η * (cA D η * hA B y y) := by rw [← hA_smul_right, ← hA_smul, hy]
  rw [e, ← mul_assoc, hη, zero_mul]

include hv in
theorem hA_yv : hA B y v = 0 := by rw [← hA_herm, hv, map_zero]

include hη hy hv in
theorem kMat_neg_mul : kMat B v (-y) * kMat B v y = 1 := by
  refine Matrix.mulVec_injective (funext fun x => ?_)
  show (kMat B v (-y) * kMat B v y).mulVec x = (1 : Matrix _ _ _).mulVec x
  rw [← Matrix.mulVec_mulVec, kMat_mulVec, kMat_mulVec, Matrix.one_mulVec, hA_neg_right]
  simp only [hA_sub, hA_add, hA_smul, hv, hA_yv hv, hA_self hη hy, mul_zero, add_zero, sub_zero]
  have h0 : (hA B x y * hA B v v) • y = 0 := by
    rw [mul_comm, mul_smul, hA_smul_self hη hy, smul_zero]
  rw [smul_neg, add_smul, h0, neg_smul]
  abel

include hη hy hv in
theorem kMat_mul_neg : kMat B v y * kMat B v (-y) = 1 := by
  have := kMat_neg_mul (y := -y) (v := v) hη (by rw [smul_neg, hy]) (by rw [hA_neg_right, hv, neg_zero])
  rwa [neg_neg] at this

include hη hy hv in
theorem hA_kMat (x x' : Fin B.rank → AE D) :
    hA B ((kMat B v y).mulVec x) ((kMat B v y).mulVec x') = hA B x x' := by
  rw [kMat_mulVec, kMat_mulVec]
  simp only [hA_sub, hA_add, hA_smul, hA_sub_right, hA_add_right, hA_smul_right, hA_herm, hv, hA_yv hv,
    hA_self hη hy]
  linear_combination hA B v v * hA_mul_hA hη hy x x'

end

theorem unitary_of_hA {M : Matrix (Fin B.rank) (Fin B.rank) (AE D)}
    (h : ∀ x y, hA B (M.mulVec x) (M.mulVec y) = hA B x y) :
    (M.map (cA D))ᵀ * B.gram.map (incA D) * M = B.gram.map (incA D) := by
  have key : ∀ x y : Fin B.rank → AE D,
      (fun i => cA D (y i)) ⬝ᵥ ((M.map (cA D))ᵀ * B.gram.map (incA D) * M).mulVec x =
        (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := fun x y => by
    have e : (fun i => cA D (M.mulVec y i)) = (M.map (cA D)).mulVec fun i => cA D (y i) :=
      funext fun i => RingHom.map_mulVec (cA D) _ y i
    have := h x y
    rwa [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at this
  refine Matrix.mulVec_injective (funext fun x => funext fun i => ?_)
  have := key x (Pi.single i 1)
  rwa [show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct, single_one_dotProduct] at this

theorem exists_continuous_isK (D : D7) (B : HSp D) (η : AE D) (hη : η * cA D η = 0) (v : Fin B.rank → AE D) :
    ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B,
      Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  refine ⟨fun y => ⟨⟨kMat B v y.1, kMat B v (-y.1), kMat_mul_neg hη y.2.1 y.2.2, kMat_neg_mul hη y.2.1 y.2.2⟩,
    unitary_of_hA (hA_kMat hη y.2.1 y.2.2)⟩, ?_, fun y x => kMat_mulVec v y.1 x⟩
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_kMat v).comp continuous_subtype_val
  · exact (continuous_kMat v).comp continuous_subtype_val.neg

end GlobalTheory.RootUnip

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselDecomp

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hD_basis_dual (d : BesselDatum A B ι) (i l) : B.hD (d.aux l) (dual d i) = if l = i then 1 else 0 := by
  have hz : star (B.hT d.z d.z) = B.hT d.z d.z := (hT_swap rfl).symm
  have zz : B.hT d.z d.z ≠ 0 := d.zz
  unfold BesselDatum.aux dual
  refine Fin.lastCases ?_ (fun j => ?_) i <;> refine Fin.lastCases ?_ (fun k => ?_) l
  · simp [HSpace.hD, starRingEnd_apply, hz, zz]
  · have : B.hT d.z (d.e k) = 0 := d.ez k
    simp [HSpace.hD, this, Fin.castSucc_ne_last]
  · rw [Fin.snoc_last, Fin.snoc_castSucc, hD_swap_zero (d.fz j), if_neg (Fin.castSucc_ne_last j).symm]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, d.ef]
    simp

theorem f_dual (d : BesselDatum A B ι) (i l) : B.hD (d.f l) (dual d i) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have : B.hT d.z (d.f l) = 0 := d.fz l
    simp [HSpace.hD, this]
  · rw [Fin.snoc_castSucc, d.ff]

theorem hD_basis_e (d : BesselDatum A B ι) (i l) : B.hD (d.aux i) (d.e l) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, hD_swap_zero (d.ez l)]
  · rw [Fin.snoc_castSucc, d.ee]

theorem f_e (d : BesselDatum A B ι) (k l) : B.hD (d.f k) (d.e l) = if k = l then 1 else 0 := by
  have h : B.hT (d.e l) (d.f k) = star (if l = k then 1 else 0) := hT_swap (d.ef l k)
  unfold HSpace.hD
  rw [h]
  by_cases e : k = l
  · simp [e]
  · simp [e, Ne.symm e]

def comb (d : BesselDatum A B ι) :
    (A.V × (Fin (d.ρ + 1) → D.host.E) × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
  ι.coprod ((Fintype.linearCombination D.host.E d.aux).coprod (Fintype.linearCombination D.host.E d.f))

theorem comb_inj (d : BesselDatum A B ι) : Function.Injective (comb d) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s, r⟩ h
  simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
  have h1 : ∀ i l, B.hT (dual d i) (d.aux l) = if l = i then 1 else 0 := hD_basis_dual d
  have h2 : ∀ i l, B.hT (dual d i) (d.f l) = 0 := f_dual d
  have h3 : ∀ i l, B.hT (d.e l) (d.aux i) = 0 := hD_basis_e d
  have h4 : ∀ k l, B.hT (d.e l) (d.f k) = if k = l then 1 else 0 := f_e d
  have h5 : ∀ i, B.hT (dual d i) (ι a) = 0 := fun i => hD_swap_zero (dual_perp d i a)
  have h6 : ∀ l, B.hT (d.e l) (ι a) = 0 := fun l => hD_swap_zero (d.eA l a)
  have hs : s = 0 := by
    funext i

    simpa [map_sum, h1, h2, h5] using congrArg (B.hT (dual d i)) h
  have hr : r = 0 := by
    funext l

    simpa [map_sum, h3, h4, h6] using congrArg (B.hT (d.e l)) h
  subst hs hr
  have ha : ι a = 0 := by simpa using h
  have : a = 0 := by
    refine A.nondeg.1 a fun y => ?_
    rw [← d.isom a y, ha]; simp
  subst this
  rfl

theorem comb_surj (d : BesselDatum A B ι) : Function.Surjective (comb d) := by
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (comb_inj d)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, A.rank_eq, B.rank_eq,
    d.rank_eq]
  omega

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {n : ℕ} (c : Fin n → D.host.E) (v : Fin n → B.V) :
    vecA B (∑ i, c i • v i) = ∑ i, incA D (c i) • vecA B (v i) := by
  funext k; simp [vecA, map_sum, Finset.sum_apply]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]

  conv_lhs => rw [← A.frame.sum_repr a, map_sum]
  simp only [map_smul]
  rw [vecA_sum]
  rfl

theorem exists_comb (d : BesselDatum A B ι) (x : Fin B.rank → AE D) :
    ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      x = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l) := by
  have hx : x = ∑ k, x k • vecA B (B.frame k) := by
    funext j
    simp [vecA, Finset.sum_apply, Finsupp.single_apply, apply_ite (incA D)]
  rw [hx]
  refine Finset.sum_induction _ (fun y => ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      y = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l)) ?_ ?_ ?_
  · rintro _ _ ⟨t, s, r, rfl⟩ ⟨t', s', r', rfl⟩
    refine ⟨t + t', s + s', r + r', ?_⟩
    simp only [iA_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  · exact ⟨0, 0, 0, by simp [iA]⟩
  · intro k _
    obtain ⟨⟨a, s, r⟩, h⟩ := comb_surj d (B.frame k)
    simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
    refine ⟨x k • vecA A a, fun i => x k * incA D (s i), fun l => x k * incA D (r l), ?_⟩
    rw [← h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota, iA_smul]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_assoc]

theorem iA_vec {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (iA ι t) (vecA B v) = 0 := by
  rw [← hA_herm, hA_vec_iA h, map_zero]

theorem decomp : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧
    ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) +
      ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  intro D A B ι d
  refine ⟨hD_basis_dual d, f_dual d, fun x => ?_⟩
  obtain ⟨t, s, r, h⟩ := exists_comb d x
  have hs : ∀ i, hA B x (vecA B (dual d i)) = s i := fun i => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (dual_perp d i)]
    simp [hA_smul, hA_vec, hD_basis_dual, f_dual, apply_ite (incA D)]
  have hr : ∀ l, hA B x (vecA B (d.e l)) = r l := fun l => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (d.eA l)]
    simp [hA_smul, hA_vec, hD_basis_e, f_e, apply_ite (incA D)]
  exact ⟨t, by simp only [hs, hr]; exact h⟩

end GlobalTheory.BesselDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocWeil.PlaceIdem

section General

variable (F : Type) [Field F] [NumberField F]

theorem evalV_single_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_single_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : evalV F u (singleV F v 1) = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem af_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b :=
  DFunLike.ext _ _ h

def eFin (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (singleV F v 1)

def eInf (v : InfinitePlace F) : AF F := pairA F (Pi.single v 1) 0

theorem eFin_mul_eFin {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : eFin F u * eFin F v = 0 := by
  refine Prod.ext (mul_zero _) ?_
  change singleV F u 1 * singleV F v 1 = 0
  refine af_ext F fun w => ?_
  rw [map_mul, map_zero]
  by_cases hw : w = u
  · subst hw
    rw [evalV_single_ne F h, mul_zero]
  · rw [evalV_single_ne F hw, zero_mul]

theorem eFin_mul_eInf (u : HeightOneSpectrum (𝓞 F)) (v : InfinitePlace F) : eFin F u * eInf F v = 0 :=
  Prod.ext (zero_mul _) (mul_zero _)

theorem eInf_mul_eInf {u v : InfinitePlace F} (h : u ≠ v) : eInf F u * eInf F v = 0 := by
  refine Prod.ext ?_ (mul_zero _)
  funext w
  change (Pi.single u 1 : ∀ w : InfinitePlace F, w.Completion) w *
    (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) w = 0
  by_cases hw : w = u
  · subst hw
    rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hw, zero_mul]

theorem eq_zero_of_idem (a : AF F) (h1 : ∀ v, eFin F v * a = 0) (h2 : ∀ v, eInf F v * a = 0) : a = 0 := by
  refine Prod.ext ?_ ?_
  · funext w
    have h : (Pi.single w 1 : ∀ w : InfinitePlace F, w.Completion) w * a.1 w = 0 :=
      congrFun (congrArg Prod.fst (h2 w)) w
    rw [Pi.single_eq_same, one_mul] at h
    exact h
  · refine af_ext F fun w => ?_
    have h : singleV F w 1 * sndA F a = 0 := congrArg Prod.snd (h1 w)
    have h' := congrArg (evalV F w) h
    rw [map_mul, evalV_single_same, one_mul] at h'
    exact h'

theorem tensor_eq_zero {K E R I : Type} [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] (e : I → R)
    (he : ∀ a : R, (∀ i, e i * a = 0) → a = 0) (x : R ⊗[K] E)
    (hx : ∀ i, algebraMap R (R ⊗[K] E) (e i) * x = 0) : x = 0 := by
  let b := Algebra.TensorProduct.basis R (Module.Free.chooseBasis K E)
  refine b.ext_elem fun j => ?_
  rw [map_zero]
  refine he _ fun i => ?_
  have h := hx i
  rw [← Algebra.smul_def] at h
  have h' := congrArg (fun y => b.repr y j) h
  simpa using h'

theorem sum_single_one : (∑ v : InfinitePlace F, fstA F (eInf F v)) = 1 := by
  change (∑ v : InfinitePlace F, (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion)) = fun _ => 1
  exact Finset.univ_sum_single (fun w : InfinitePlace F => (1 : w.Completion))

theorem ext_eInf (σ : F →+* ℂ) (v : InfinitePlace F) :
    GlobalTheory.InfAdeleCM.ext σ (fstA F (eInf F v)) = if InfinitePlace.mk σ = v then 1 else 0 := by
  rw [GlobalTheory.InfAdeleCM.ext_apply]
  change InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
    ((Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) (InfinitePlace.mk σ)) = _
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, map_zero]

end General

def plc (D : D7) (τ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))

theorem plc_bijective (D : D7) : Function.Bijective (plc D) := GlobalTheory.CMTypePlaces.places_bijective D

theorem idem_inl (D : D7) (v : FinF D) :
    idem D (.inl v) = algebraMap (AF D.host.F) (AE D) (eFin D.host.F v) := rfl

theorem idem_inr (D : D7) (τ : D.what₂.Tau) :
    idem D (.inr τ) = algebraMap (AF D.host.F) (AE D) (eInf D.host.F (plc D τ)) := rfl

theorem infPart_algebraMap (D : D7) (a : AF D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) a) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem finPart_algebraMap (D : D7) (a : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) a) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem idem_props : ∀ D : D7, (∀ v v' : Pl D, v ≠ v' → idem D v * idem D v' = 0) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ τ τ', θ τ' (infPart D (idem D (.inr τ))) = if τ' = τ then 1 else 0) ∧ (∀ τ, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ, idem D (.inr τ)) = 1 ∧ (∀ v : FinF D, ∃ a, IsPlaceIdem D v a ∧ idem D (.inl v) = algebraMap (AF D.host.F) (AE D) a) ∧ ∀ x : AE D, (∀ v, idem D v * x = 0) → x = 0 := by
  intro D
  have hb := plc_bijective D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (v | τ) (v' | τ') h
    · rw [idem_inl, idem_inl, ← RingHom.map_mul, eFin_mul_eFin _ fun e => h (congrArg _ e), RingHom.map_zero]
    · rw [idem_inl, idem_inr, ← RingHom.map_mul, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inl, ← RingHom.map_mul, mul_comm, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inr, ← RingHom.map_mul, eInf_mul_eInf _ fun e => h (congrArg _ (hb.1 e)), RingHom.map_zero]
  · intro θ hθ τ τ'
    haveI := D.sp.cm.totReal
    have h := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ') (θ τ') (hθ τ').1 (hθ τ').2
      (fstA D.host.F (eInf D.host.F (plc D τ))) 1
    rw [RingHom.map_one, mul_one, ext_eInf] at h
    rw [idem_inr, infPart_algebraMap]
    refine h.trans ?_
    exact if_congr (hb.1.eq_iff (a := τ') (b := τ)) rfl rfl
  · intro τ
    rw [idem_inr, finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  · have h : (∑ τ, idem D (.inr τ)) =
        algebraMap (AF D.host.F) (AE D) (∑ v : InfinitePlace D.host.F, eInf D.host.F v) := by

      rw [← hb.sum_comp, map_sum (algebraMap (AF D.host.F) (AE D))]
      rfl

    rw [h, infPart_algebraMap, map_sum (fstA D.host.F), sum_single_one]
    rfl
  · intro v
    exact ⟨eFin D.host.F v, ⟨singleV D.host.F v 1, rfl, evalV_single_same _ v, fun v' h => evalV_single_ne _ h⟩, rfl⟩
  · intro x hx
    refine tensor_eq_zero (Sum.elim (eFin D.host.F) fun τ => eInf D.host.F (plc D τ)) (fun a ha => ?_) x ?_
    · refine eq_zero_of_idem _ a (fun v => ha (.inl v)) fun w => ?_
      obtain ⟨τ, rfl⟩ := hb.2 w
      exact ha (.inr τ)
    · rintro (v | τ)
      · exact hx (.inl v)
      · exact hx (.inr τ)

end GlobalTheory.LocWeil.PlaceIdem

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ ∃ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ := by
  first | exact @GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | exact GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | (intros; apply GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S := by
  first | exact @GlobalTheory.Mem.Ksph.exists_subgroup_ksph | exact GlobalTheory.Mem.Ksph.exists_subgroup_ksph | (intros; apply GlobalTheory.Mem.Ksph.exists_subgroup_ksph <;> assumption)
end
