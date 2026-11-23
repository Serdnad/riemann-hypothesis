module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle528
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle531
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.CompIsoProof

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) (a : ℕ) :
    Continuous (GeneralLinearGroup.map f : GL (Fin a) R →* GL (Fin a) S) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) (a : ℕ) :
    Continuous (cornerGL a s) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

variable {E : Type} [Field E] {a : ℕ}

def glOf (y : InfinitePlace E → GL (Fin a) ℂ) : GL (Fin a) (Cinf E) where
  val := Matrix.of fun i j v => (y v).val i j
  inv := Matrix.of fun i j v => (y v).inv i j
  val_inv := by
    ext i j v
    have h := congrFun (congrFun (y v).val_inv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h
  inv_val := by
    ext i j v
    have h := congrFun (congrFun (y v).inv_val i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h

theorem map_eval_glOf (y : InfinitePlace E → GL (Fin a) ℂ) (v : InfinitePlace E) :
    GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (glOf y) = y v := by
  ext i j
  rfl

theorem continuous_glOf : Continuous (glOf : (InfinitePlace E → GL (Fin a) ℂ) → GL (Fin a) (Cinf E)) := by
  have h2 : Continuous fun x : GL (Fin a) ℂ => ((x⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) :=
    (Units.continuous_iff.1 (continuous_id (X := GL (Fin a) ℂ))).2
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => continuous_pi fun v => ?_,
    continuous_matrix fun i j => continuous_pi fun v => ?_⟩
  · exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply v)
  · exact (h2.matrix_elem i j).comp (continuous_apply v)

variable [NumberField E]

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

variable [_root_.NumberField.IsTotallyComplex E]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coordinate (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (continuous_apply v).comp continuous_pInf

theorem map_cV (v : InfinitePlace E) (g : GA E a) :
    GeneralLinearGroup.map (cV v) g =
      GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (GeneralLinearGroup.map (pInf E) g) := by
  ext i j
  rfl

def parts (g : GA E a) : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E) :=
  (fun v => GeneralLinearGroup.map (cV v) g, GeneralLinearGroup.map (pFin E) g)

def glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : GA E a :=
  infGL E a (glOf p.1) * finGL E a p.2

theorem glue_parts (g : GA E a) : glue (parts g) = g := by
  have h : glOf (fun v => GeneralLinearGroup.map (cV v) g) = GeneralLinearGroup.map (pInf E) g := by
    ext i j v
    rfl
  rw [glue, parts]
  simp only [h]
  exact infGL_mul_finGL g

theorem parts_glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : parts (glue p) = p := by
  refine Prod.ext (funext fun v => ?_) ?_
  · change GeneralLinearGroup.map (cV v) (glue p) = p.1 v
    rw [map_cV, glue, map_mul, pInf_infGL, pInf_finGL, mul_one, map_eval_glOf]
  · change GeneralLinearGroup.map (pFin E) (glue p) = p.2
    rw [glue, map_mul, pFin_infGL, pFin_finGL, one_mul]

theorem continuous_parts : Continuous (parts : GA E a → _) :=
  (continuous_pi fun v => continuous_glMap (cV v) (continuous_coordinate v) a).prodMk
    (continuous_glMap (pFin E) continuous_snd a)

theorem continuous_glue : Continuous (glue : _ → GA E a) :=
  ((continuous_cornerGL (sInf E) continuous_sInf a).comp (continuous_glOf.comp continuous_fst)).mul
    ((continuous_cornerGL (sFin E) continuous_sFin a).comp continuous_snd)

theorem compIso : CompIso := by
  intro E _ _ _ a b
  refine ⟨{ toFun := comps
            invFun := fun p => (glue (fun v => (p.1 v).1, p.2.1), glue (fun v => (p.1 v).2, p.2.2))
            left_inv := fun x => Prod.ext (glue_parts x.1) (glue_parts x.2)
            right_inv := fun p => ?_
            map_mul' := fun x y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ => rfl⟩
  · have h1 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))) v
    have h2 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))) v
    have h3 := congrArg Prod.snd (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))
    have h4 := congrArg Prod.snd (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))
    exact Prod.ext (funext fun v => Prod.ext (h1 v) (h2 v)) (Prod.ext h3 h4)
  · refine Prod.ext (funext fun v => Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> exact map_mul _ _ _
  · have p1 : Continuous fun x : GA E a × GA E b => parts x.1 := continuous_parts.comp continuous_fst
    have p2 : Continuous fun x : GA E a × GA E b => parts x.2 := continuous_parts.comp continuous_snd
    exact (continuous_pi fun v => ((continuous_apply v).comp p1.fst).prodMk ((continuous_apply v).comp p2.fst)).prodMk
      (p1.snd.prodMk p2.snd)
  · have q1 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).1, p.2.1) :
        (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).fst).prodMk continuous_snd.fst
    have q2 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).2, p.2.2) :
        (InfinitePlace E → GL (Fin b) ℂ) × GL (Fin b) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).snd).prodMk continuous_snd.snd
    exact (continuous_glue.comp q1).prodMk (continuous_glue.comp q2)

end GlobalTheory.CompanionTheory.CompIsoProof

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.NormPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    (d * u⁻¹) * thE E n (d * u⁻¹) = nrm d := by
  obtain ⟨h1, h2⟩ := hu
  have hθ : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h1, map_mul, map_inv, hθ, inv_inv, nrm]
  group

theorem polE_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    polE (d * u⁻¹) = (nrm d).val.charpoly := by
  rw [polE, norm_translate hu]

theorem map_thetaE (τ : E →+* ℂ) (d : GL (Fin n) E) :
    GeneralLinearGroup.map τ (thetaE E n d) =
      thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d) := by
  apply Units.ext
  ext i j
  have hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ := fun _ => rfl
  rw [hv, thetaR_val, thetaR_val, ← map_inv, hv]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  exact IsCMField.complexEmbedding_complexConj E τ _

theorem charpoly_map_nrm (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (GeneralLinearGroup.map τ d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d)).val.charpoly =
      (nrm d).val.charpoly.map τ := by
  rw [← map_thetaE, ← map_mul, ← Matrix.charpoly_map]
  rfl

theorem isRegEll_iff_mem_Ell (d : GL (Fin n) E) : IsRegEll d ↔ (nrm d).val.charpoly ∈ Ell E n := by
  have hm : (nrm d).val.charpoly.Monic := Matrix.charpoly_monic _
  constructor
  · intro h
    refine ⟨hm, by simp, h.1, fun τ z hz => ?_⟩
    exact h.2 τ z (Polynomial.isRoot_of_mem_roots hz)
  · rintro ⟨-, -, hs, hr⟩
    exact ⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩

theorem polEq : PolEq := by
  intro E _ _ _ n u hu d
  rw [polE_translate hu]
  refine ⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩
  unfold EllC
  rw [charpoly_map_nrm]
  exact ⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩

end GlobalTheory.CompanionTheory.NormPoly
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.AdelEqProof

theorem map_thetaR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  change f (σ ((g⁻¹ : GL (Fin n) A).val j i)) = τ (((GeneralLinearGroup.map f g)⁻¹ : GL (Fin n) B).val j i)
  rw [← map_inv]
  exact h _

theorem map_PhiU {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n A) = PhiU n B := by
  apply Units.ext
  ext i j
  change f ((PhiU n A).val i j) = (PhiU n B).val i j
  rw [phiU_val, phiU_val]
  simp [GlobalTheory.Tw.Phi, apply_ite f]

theorem map_thetaGL {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaGL n σ g) = thetaGL n τ (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_PhiU, map_thetaR f σ τ h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

theorem pFin_conjAd (x : Ad E) :
    pFin E (conjAd E x) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E x) := rfl

theorem cV_conjAd (v : InfinitePlace E) (x : Ad E) :
    cV v (conjAd E x) = starRingEnd ℂ (cV v x) := by
  have h : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) := by
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) ((infEq E).symm x.1))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change pInf E (conjAd E x) v = _
  rw [h]
  rfl

theorem cV_algebraMap (v : InfinitePlace E) (y : E) : cV v (algebraMap E (Ad E) y) = v.embedding y :=
  pInf_algebraMap y v

theorem map_cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = GeneralLinearGroup.map v.embedding d := by
  apply Units.ext
  ext i j
  exact cV_algebraMap v _

theorem map_pFin_ratGL (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  apply Units.ext
  ext i j
  rfl

theorem map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  apply Units.ext
  ext i j
  rfl

theorem map_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) :=
  map_thetaGL _ _ _ pFin_conjAd n g

theorem map_cV_twConj (v : InfinitePlace E) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (twConj (thetaA E n) x (ratGL E n d)) =
      twConj (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map (cV v) x) (GeneralLinearGroup.map v.embedding d) := by
  simp only [twConj, map_mul, map_inv, map_cV_ratGL]
  rw [map_thetaR (cV v) (conjAd E) (starRingEnd ℂ) (cV_conjAd v) n x]

theorem map_pFin_twConj (hT : TranslAd) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := hT E n u hu x
  have h2 : twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹ =
      x⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) x := by
    rw [h, map_mul, map_inv]
    simp only [twConj]
    group
  rw [h2, map_mul, map_mul, map_inv, map_pFin_ratGL, map_pFin_thetaGL]

theorem cpt_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x)) := by
  rw [cpt, map_cW, map_pFin_twConj hT u hu]

theorem cpt'_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt' w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w) (thF E n
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x))) := by
  rw [cpt', map_cW, map_pFin_thetaGL, map_pFin_twConj hT u hu]

theorem adelEqOf : AdelEqOf := by
  intro hT E _ _ _ a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [adel, orbFn, finFn]
  refine congr_arg₂ (· * ·) (Finset.prod_congr rfl fun v _ => ?_)
    (finprod_congr fun w => finprod_congr fun _ => ?_)
  · rw [map_cV_twConj, map_cV_twConj]
    rfl
  · rw [cpt_twConj hT w u₁ h₁, cpt_twConj hT w u₂ h₂, cpt'_twConj hT w u₁ h₁, cpt'_twConj hT w u₂ h₂]
    rfl

end GlobalTheory.CompanionTheory.AdelEqProof

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj twConj_mul_left mem_twCent)

namespace GlobalTheory.CompanionTheory.OrbInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  have h : ∀ g : GL (Fin n) E, (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := fun _ => rfl
  apply Units.ext
  rw [thetaR_val, ← map_inv, h, h, thetaR_val]
  ext i j
  exact conjAd_algebraMap _

theorem twConj_ratGL (g d : GL (Fin n) E) (x : GA E n) :
    twConj (thetaA E n) x (ratGL E n (twConj (thetaE E n) g d)) =
      twConj (thetaA E n) (ratGL E n g * x) (ratGL E n d) := by
  simp only [twConj, map_mul, map_inv, thetaA_ratGL]
  group

theorem mem_ratCent_twConj (g d : GL (Fin n) E) (x : GA E n) :
    x ∈ ratCent (twConj (thetaE E n) g d) ↔ ratGL E n g * x * (ratGL E n g)⁻¹ ∈ ratCent d := by
  simp only [ratCent, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (mem_twCent _ _ _).1 hc
    simp only [twConj] at hc'
    refine ⟨g * c * g⁻¹, (mem_twCent _ _ _).2 ?_, by simp only [map_mul, map_inv]⟩
    simp only [map_mul, map_inv]
    calc (g * c * g⁻¹)⁻¹ * d * (thetaE E n g * thetaE E n c * (thetaE E n g)⁻¹)
        = g * (c⁻¹ * (g⁻¹ * d * thetaE E n g) * thetaE E n c) * (thetaE E n g)⁻¹ := by group
      _ = g * (g⁻¹ * d * thetaE E n g) * (thetaE E n g)⁻¹ := by rw [hc']
      _ = d := by group
  · rintro ⟨c, hc, h⟩
    have hc' := (mem_twCent _ _ _).1 hc
    refine ⟨g⁻¹ * c * g, (mem_twCent _ _ _).2 ?_, ?_⟩
    · simp only [twConj, map_mul, map_inv]
      calc (g⁻¹ * c * g)⁻¹ * (g⁻¹ * d * thetaE E n g) *
            ((thetaE E n g)⁻¹ * thetaE E n c * thetaE E n g)
          = g⁻¹ * (c⁻¹ * d * thetaE E n c) * thetaE E n g := by group
        _ = g⁻¹ * d * thetaE E n g := by rw [hc']
    · simp only [map_mul, map_inv, h]
      group

theorem twConj_ratCent (d : GL (Fin n) E) {h : GA E n} (hh : h ∈ ratCent d) (x : GA E n) :
    twConj (thetaA E n) (h * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
  have hc' := (mem_twCent _ _ _).1 hc
  refine twConj_mul_left _ _ ((mem_twCent _ _ _).2 ?_) x
  rw [thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul, hc']

theorem countable_ratCent [Countable (GL (Fin n) E)] (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)).Countable :=
  (Set.countable_range (ratGL E n)).mono (by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩)

theorem orbInvOf : OrbInvOf := by
  intro hQ hT E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ φ d₁ g₁ d₂ g₂ hc
  obtain ⟨⟨lc₁, sc₁, t₁⟩, -, -, cn₁, -, -⟩ := hT E a
  obtain ⟨⟨lc₂, sc₂, t₂⟩, -, -, cn₂, -, -⟩ := hT E b
  have hcnt : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) :
      Set (GA E a × GA E b)).Countable := by
    rw [Subgroup.coe_prod]
    exact (countable_ratCent d₁).prod (countable_ratCent d₂)
  have : Countable ((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) := hcnt.to_subtype
  set F : GA E a × GA E b → ℂ := fun x =>
    φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) with hF
  letI : T1Space (GA E a) := @T2Space.t1Space _ _ t₁
  letI : T1Space (GA E b) := @T2Space.t1Space _ _ t₂
  letI : MeasurableSingletonClass (GA E a) := OpensMeasurableSpace.toMeasurableSingletonClass
  letI : MeasurableSingletonClass (GA E b) := OpensMeasurableSpace.toMeasurableSingletonClass
  letI : MeasurableSingletonClass (GA E a × GA E b) := Prod.instMeasurableSingletonClass
  letI : SigmaCompactSpace (GA E a) := @sigmaCompactSpace_of_locallyCompact_secondCountable _ _ lc₁ sc₁
  letI : SigmaCompactSpace (GA E b) := @sigmaCompactSpace_of_locallyCompact_secondCountable _ _ lc₂ sc₂
  letI : SigmaFinite μ₁ := Measure.IsHaarMeasure.sigmaFinite μ₁
  letI : SigmaFinite μ₂ := Measure.IsHaarMeasure.sigmaFinite μ₂
  letI : (μ₁.prod μ₂).IsMulLeftInvariant := Measure.prod.instIsMulLeftInvariant
  letI : SFinite (μ₁.prod μ₂) := Measure.prod.instSFinite
  have key := hQ (GA E a × GA E b) (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
    ((ratCent (twConj (thetaE E a) g₁ d₁)).prod (ratCent (twConj (thetaE E b) g₂ d₂))) F
    (ratGL E a g₁, ratGL E b g₂) hc.measurable
    (fun h hh x => by
      simp only [hF, Prod.fst_mul, Prod.snd_mul]
      rw [twConj_ratCent d₁ hh.1, twConj_ratCent d₂ hh.2])
    (fun x => by
      simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mem_ratCent_twConj])
  simp only [hF, Prod.fst_mul, Prod.snd_mul] at key
  simp only [orbTerm2, twConj_ratGL]
  exact key

end GlobalTheory.CompanionTheory.OrbInv

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

theorem _root_.GlobalTheory.T.finite_K_type_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRep.exists_rep | exact GlobalTheory.CompanionTheory.SiegelRep.exists_rep | (intros; apply GlobalTheory.CompanionTheory.SiegelRep.exists_rep <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.side_term_identity : StdGood → BdetLaw → SideOf := by
  first | exact @GlobalTheory.CompanionTheory.MirSides.sideOf | exact GlobalTheory.CompanionTheory.MirSides.sideOf | (intros; apply GlobalTheory.CompanionTheory.MirSides.sideOf <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_theta_kernel_components : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection | exact GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection | (intros; apply GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection <;> assumption)
end
