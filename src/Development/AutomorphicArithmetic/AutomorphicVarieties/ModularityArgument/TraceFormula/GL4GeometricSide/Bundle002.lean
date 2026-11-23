module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle411
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle544

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL GlobalTheory.UnitaryBC
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

private theorem adj_of_skew {M : Type} [AddCommGroup M] [Module ℂ M] (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (A B : Module.End ℂ M)
    (h : ∀ (z : ℂ) (φ ψ : M), H ((z • A + star z • B) φ) ψ + H φ ((z • A + star z • B) ψ) = 0)
    (φ ψ : M) : H (A φ) ψ = - H φ (B ψ) := by
  have h1 := h 1 φ ψ
  have hI := h Complex.I φ ψ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smulₛₗ, one_smul, star_one,
    Complex.star_def, Complex.conj_I, map_neg, neg_smul, map_one, RingHom.id_apply, smul_eq_mul,
    Complex.conj_conj, LinearMap.neg_apply] at h1 hI
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI +
    ((H (A φ) ψ + H φ (B ψ) - H (B φ) ψ - H φ (A ψ)) / 2) * Complex.I_sq

private theorem lie_single {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (z : ℂ) :
    lieOp π (fun i j => atEmb τ (Matrix.single a b z i j)) =
      z • cx τ (lieOp π) a b + star z • cx (PositivityTheory.Rg.Cz.barE E τ) (lieOp π) a b := by
  rw [PositivityTheory.Rg.Cz.GK.lieOp_atEmb, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Matrix.single_apply, hj.symm]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, hi.symm]
  · simp

private theorem cx_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (ψ : π.V) : (cx τ (lieOp π) a b ψ).1 = Eop τ a b ψ.1 := by
  rw [← GlobalTheory.WigCap.res_Eop]
  rfl

private theorem emb_ne {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc : w.IsComplex := IsTotallyComplex.isComplex w
  exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)

private theorem gl_pull {U M : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (J : U →ₗ[ℂ] M) (hJ : Function.Injective J) (e : Fin n → Fin n → Module.End ℂ U)
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) (h : ∀ a b u, J (e a b u) = F a b (J u)) : GlRel e := by
  intro a b c d
  refine LinearMap.ext fun u => hJ ?_
  have key := LinearMap.congr_fun (hF a b c d) (J u)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, map_sub, h, h, h, h, key]
  split_ifs <;> simp [h]

private theorem gl_neg_swap {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) : GlRel (fun a b => -F b a) := by
  intro a b c d
  have key := hF b a d c
  simp only [neg_mul_neg]
  rw [key]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp; abel
  · have h2' : ¬ a = d := fun h => h2 h.symm
    subst h1
    simp [h2, h2']
  · subst h2
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1']
  · have h2' : ¬ a = d := fun h => h2 h.symm
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1', h2, h2']

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlPair :
    RlPair := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := emb_ne w
  let A : Fin n → Fin n → Module.End ℂ π.V := cx w.embedding (lieOp π)
  let B : Fin n → Fin n → Module.End ℂ π.V := cx (PositivityTheory.Rg.Cz.barE E w.embedding) (lieOp π)
  have v1 : ∀ a b u, (D.i (D.E1 w a b u)).1 = Eop w.embedding a b (D.i u).1 := fun a b u => D.hE1 w a b u
  have v2 : ∀ a b u, (D.i (D.E2 w a b u)).1 = -Eop (ComplexEmbedding.conjugate w.embedding) b a (D.i u).1 :=
    fun a b u => D.hE2 w a b u
  have iE1 : ∀ a b u, D.i (D.E1 w a b u) = A a b (D.i u) := fun a b u =>
    Subtype.ext ((v1 a b u).trans (cx_val π _ a b _).symm)
  have iE2 : ∀ a b u, D.i (D.E2 w a b u) = -B b a (D.i u) := fun a b u =>
    Subtype.ext ((v2 a b u).trans (congrArg Neg.neg (cx_val π _ b a _).symm))
  have adjA : ∀ a b φ ψ, D.H (A a b φ) ψ = -D.H φ (B a b ψ) := fun a b =>
    adj_of_skew D.H _ _ fun z φ ψ => by
      rw [← lie_single]
      exact D.pet.2.2.1 _ φ ψ
  have adjB : ∀ a b φ ψ, D.H (B a b φ) ψ = -D.H φ (A a b ψ) := fun a b φ ψ => by
    have h := congrArg (starRingEnd ℂ) (adjA a b ψ φ)
    rw [map_neg, D.pet.1, D.pet.1] at h
    rw [h, neg_neg]
  have hJ : Function.Injective (π.V.subtype ∘ₗ D.i) := π.V.injective_subtype.comp D.inj
  refine { gl1 := ?_, gl2 := ?_, comm := ?_, unitK := ?_, unitP := ?_ }
  · exact gl_pull _ hJ _ _ (glRel_Eop w.embedding) v1
  · exact gl_pull _ hJ _ _ (gl_neg_swap _ (glRel_Eop (ComplexEmbedding.conjugate w.embedding))) v2
  · intro a b c d
    refine LinearMap.ext fun u => D.inj (Subtype.ext ?_)
    change (D.i (D.E1 w a b (D.E2 w c d u))).1 = (D.i (D.E2 w c d (D.E1 w a b u))).1
    rw [v1, v2, v2, v1, map_neg]
    exact congrArg Neg.neg (LinearMap.congr_fun (Eop_comm hne a b d c) (D.i u).1)
  · intro a b x y
    simp only [kF, LinearMap.add_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_add (f := _), iE1, iE2, map_neg, LinearMap.add_apply, LinearMap.neg_apply, adjA, adjB]
    ring
  · intro a b x y
    simp only [pF, LinearMap.sub_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_sub, iE1, iE2, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, adjA, adjB]
    ring
end

section

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TwY.ThInv
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem along_unitary (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (k : Un n) :
    Bridge.along w g φ k.1 = φ (g * kAt w k) := by
  classical
  have e : Bridge.atW (E := E) w k.1 = toL (locInf w (Unitary.toUnits k)).val := by
    funext i j v
    rw [Bridge.atW]
    exact (locInf_apply w (Unitary.toUnits k) i j v).symm
  rw [Bridge.along, e, chart_val]
  rfl

private theorem eop_theta (w : InfinitePlace E) (a b : Fin n) {φ φ' : Sm E n}
    (h : ∀ x, φ'.1 x = φ.1 (thetaA E n x)) (x : GA E n) :
    (Bridge.eopW w true a b φ).1 (thetaA E n x) = -(Bridge.eopW w false b a φ').1 x := by
  open Matrix in
  let adjH : Lie E n →L[ℝ] Lie E n :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => toL (Matrix.of X)ᴴ
        map_add' := fun X Y => by
          rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
        map_smul' := fun t X => by
          rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

  have adjH_apply (X : Lie E n) (i j : Fin n) : adjH X i j = star (X j i) := rfl

  have map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
      (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
      GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
    ext i j
    change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
    rw [h, ← map_inv]
    rfl

  have thetaA_infGL (y : GL (Fin n) (Cinf E)) :
      thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
      (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

  have thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
      (by rw [pFin_finGL]; rfl)

  have thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
    classical
    have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
    rw [e, thetaA_infGL]
    congr 1
    refine Units.ext ?_
    ext i j v
    rw [thetaR_val, ← map_inv, ← map_inv]
    change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
    rw [locInf_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
      simp [Matrix.star_apply]
    · simp only [hv, if_false]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

  have toL_thetaR (y : GL (Fin n) (Cinf E)) :
      toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
    rw [thetaR_val]
    ext i j : 2
    change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
    rw [Matrix.coe_units_inv]
    rfl

  have chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
      chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

  have lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
      lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
    have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
        chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
      Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
    have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
      (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
    have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
      (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
      (adjH.hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
    unfold lieD
    rw [e.fderiv_eq, h2.fderiv]
    simp


  have atEmb_conjugate (w : InfinitePlace E) (z : ℂ) :
      atEmb (ComplexEmbedding.conjugate w.embedding) z = atEmb w.embedding (conj z) := by
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
      (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
    unfold atEmb
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne, if_pos rfl]


  have star_atEmb (w : InfinitePlace E) (z : ℂ) : star (atEmb w.embedding z) = atEmb w.embedding (conj z) := by
    funext v
    simp only [atEmb, InfinitePlace.mk_embedding, if_true, Pi.star_apply]
    by_cases hv : v = w
    · subst hv; simp
    · classical
      rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, star_zero]

  let sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : Lie E n := toL (Matrix.single a b (atEmb w.embedding z))

  have adjH_sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : adjH (sg w a b z) = sg w b a (conj z) := by
    funext i j
    rw [adjH_apply]
    change star (Matrix.single a b (atEmb w.embedding z) j i) = Matrix.single b a (atEmb w.embedding (conj z)) i j
    rw [Matrix.single_apply, Matrix.single_apply]
    by_cases h : a = j ∧ b = i
    · rw [if_pos h, if_pos h.symm, star_atEmb]
    · rw [if_neg h, if_neg fun h' => h h'.symm, star_zero]

  have Eop_apply (τ : E →+* ℂ) (a b : Fin n) (φ : Sm E n) (g : GA E n) :
      (Eop τ a b φ).1 g = (1 / 2 : ℂ) * (lieD (toL (Matrix.single a b (atEmb τ 1))) φ.1 g -
        Complex.I * lieD (toL (Matrix.single a b (atEmb τ Complex.I))) φ.1 g) := rfl
  have e : φ'.1 = fun x => φ.1 (thetaA E n x) := funext h
  have e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y) := fun f y => by
    simp only [Bridge.eopW, if_true]
    exact Eop_apply _ a b f y
  have e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y) := fun f y => by
    simp only [Bridge.eopW, Bool.false_eq_true, if_false]
    rw [Eop_apply, atEmb_conjugate, atEmb_conjugate]
    simp [sg]
  rw [e1, e2, e]
  simp only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]
  ring

end

theorem rlTheta : RlTheta := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D
  open Matrix in
  have map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
      (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
      GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
    ext i j
    change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
    rw [h, ← map_inv]
    rfl

  have thetaA_infGL (y : GL (Fin n) (Cinf E)) :
      thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
      (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

  have thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
      (by rw [pFin_finGL]; rfl)

  have thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
    classical
    have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
    rw [e, thetaA_infGL]
    congr 1
    refine Units.ext ?_
    ext i j v
    rw [thetaR_val, ← map_inv, ← map_inv]
    change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
    rw [locInf_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
      simp [Matrix.star_apply]
    · simp only [hv, if_false]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y := fun x y h =>
    D.inj (Subtype.ext (Subtype.ext (funext h)))
  refine ⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w =>
    ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩
  · change (D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g
    rw [D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · rw [D.inner_eq, D.inner_eq]
    exact D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)
  · change (D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g
    rw [D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]
  · change (D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g
    rw [D.hΘ, D.hE1, D.hE2]
    exact eop_theta w a b (D.hΘ u) g

end UpperTheory.V.Z.GSp4Splitting
end
end
