module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle280
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Mem.Chr

namespace GlobalTheory.DefU.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjPl_self (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ConjPl (IsCMField.complexConj E).toRingEquiv w w := fun k => by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
      w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
  have h3 := hv (algebraMap E (w.adicCompletion E) k)
  rw [hs, h1, h2] at h3
  exact h3

theorem eq_of_under_eq {w u : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  rcases (under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one E) w u).1 hu with h | h
  · exact h
  · exact (existsUnique_conjPl _ w).unique h hw

theorem continuous_finGL : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem mat_ext {A B : Matrix (Fin n) (Fin n) (Ad E)} (h1 : A.map (pInf E) = B.map (pInf E))
    (h2 : ∀ v, A.map ((pLoc E v).comp (pFin E)) = B.map ((pLoc E v).comp (pFin E))) : A = B := by
  ext i j
  refine ad_ext (congrFun (congrFun h1 i) j) (FiniteAdeleRing.ext _ fun v => ?_)
  exact congrFun (congrFun (h2 v) i) j

theorem map_finGL (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n k) = GeneralLinearGroup.map (pLoc E v) k :=
  Units.ext (congrArg (fun g : GL (Fin n) (v.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (v.adicCompletion E)))
    (congrArg (GeneralLinearGroup.map (pLoc E v)) (pFin_finGL k)))

theorem pInf_conjAd (x : Ad E) : pInf E (conjAd E x) = star (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem finGL_mem (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E))
    (hg : g ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  have hg' : cT s g.val * g.val = 1 := by
    have h : cT s g.val * 1 * g.val = 1 := hg
    rwa [Matrix.mul_one] at h
  have hw := conjPl_self w s hs hv
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  generalize hh : finGL E n (locGL E n w g) = h
  have hI : h.val.map (pInf E) = 1 := by
    rw [← hh]
    exact congrArg Units.val (pInf_finGL (locGL E n w g))
  have hL : ∀ v, h.val.map ((pLoc E v).comp (pFin E)) =
      (GeneralLinearGroup.map (pLoc E v) (locGL E n w g)).val := fun v => by
    rw [← hh]
    exact congrArg Units.val (map_finGL v (locGL E n w g))
  refine mat_ext ?_ fun v => ?_
  · have hc : (cT (conjAd E) h.val).map (pInf E) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 : pInf E (h.val j i) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) j i := congrFun (congrFun hI j) i
      change pInf E (conjAd E (h.val j i)) = _
      rw [pInf_conjAd, h1]
      by_cases e : i = j
      · subst e; simp
      · simp [Matrix.one_apply, e, Ne.symm e]
    rw [Matrix.map_mul, hc, hI, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases eq_or_ne v w with rfl | hvw
    · have h0 := hL v
      rw [pLoc_locGL] at h0
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = cT s g.val := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E v (pFin E (h.val j i)) = g.val j i := congrFun (congrFun h0 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = s (g.val j i)
        rw [pLoc_conjFin_eq _ v s hs hv, h1]
      rw [Matrix.map_mul, hc, h0, hg', Matrix.map_one _ (map_zero _) (map_one _)]
    · have h0 := hL v
      rw [pLoc_locGL_of_ne hvw] at h0
      have hne : conjSrc (IsCMField.complexConj E).toRingEquiv v ≠ w := fun e =>
        hvw ((existsUnique_conjPl _ w).unique (e ▸ conjPl_conjSrc _ v) hw)
      have h2 := hL (conjSrc (IsCMField.complexConj E).toRingEquiv v)
      rw [pLoc_locGL_of_ne hne] at h2
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = 1 := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv v) (pFin E (h.val j i)) =
            (1 : Matrix (Fin n) (Fin n) _) j i := congrFun (congrFun h2 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = _
        rw [pLoc_conjFin, h1]
        by_cases e : i = j
        · subst e; simp
        · simp [Matrix.one_apply, e, Ne.symm e]
      have h0' : h.val.map ((pLoc E v).comp (pFin E)) = 1 := h0
      rw [Matrix.map_mul, hc, h0', Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mem_locU {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (g : GL (Fin n) (w.adicCompletion E)) (hU : finGL E n (locGL E n w g) ∈ UA E n) :
    (⟨_, hU⟩ : UA E n) ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨pInf_finGL _, ?_⟩
  simp only [Subgroup.mem_iInf]
  intro u hu
  have hne : u ≠ w := fun e => hu (by rw [e])
  exact (map_finGL u _).trans (pLoc_locGL_of_ne hne g)

theorem finGL_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (x : locU n w) : finGL E n (locGL E n w (cLoc w (x : UA E n))) = (x : UA E n).1 := by
  have hx := Subgroup.mem_inf.1 x.2
  have hx2 := hx.2
  simp only [Subgroup.mem_iInf] at hx2
  refine Units.ext (mat_ext ?_ fun v => ?_)
  · have h1 : GeneralLinearGroup.map (pInf E) (x : UA E n).1 = 1 := hx.1
    have h2 := pInf_finGL (locGL E n w (cLoc w (x : UA E n)))
    exact congrArg Units.val (h2.trans h1.symm)
  · have h1 : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n (locGL E n w (cLoc w (x : UA E n)))) =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (x : UA E n).1 := by
      refine (map_finGL v _).trans ?_
      rcases eq_or_ne v w with rfl | hvw
      · exact pLoc_locGL v _
      · rw [pLoc_locGL_of_ne hvw]
        have := hx2 v fun e => hvw (eq_of_under_eq hw e)
        exact (MonoidHom.mem_ker.1 this).symm
    exact congrArg Units.val h1

theorem locU_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) →
    ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  intro E _ _ _ n w s hs hv
  have hw := conjPl_self w s hs hv
  have hf : ∀ x : locU n w, cLoc w (x : UA E n) ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := fun x => by
    change cT s _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact cT_cLoc w s hs hv _
  refine ⟨{ toFun := fun x => ⟨cLoc w (x : UA E n), hf x⟩
            invFun := fun g => ⟨⟨finGL E n (locGL E n w g.1), finGL_mem w s hs hv g.1 g.2⟩,
              finGL_mem_locU hw g.1 _⟩
            left_inv := fun x => Subtype.ext (Subtype.ext (finGL_cLoc hw x))
            right_inv := fun g => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext (map_mul (cLoc w) (x : UA E n) y)
            continuous_toFun := Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
              (continuous_finGL.comp ((CuspSub.continuous_locGL w).comp continuous_subtype_val)) _) _ }, fun _ => rfl⟩
  exact (map_finGL w _).trans (pLoc_locGL w _)

end GlobalTheory.DefU.Inert

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def evGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℂ) w)

theorem gl_ext_evGL {a b : GL (Fin n) (Cinf E)} (h : ∀ w, evGL w a = evGL w b) : a = b := by
  ext i j w
  exact congrArg (fun x : GL (Fin n) ℂ => x i j) (h w)


open Classical in
def atPlace (v : InfinitePlace E) : Cinf E →ₙ+* Cinf E where
  toFun x := Pi.single v (x v)
  map_mul' x y := Pi.single_mul (α := fun _ : InfinitePlace E => ℂ) v (x v) (y v)
  map_zero' := Pi.single_zero (M := fun _ : InfinitePlace E => ℂ) v
  map_add' x y := Pi.single_add (f := fun _ : InfinitePlace E => ℂ) v (x v) (y v)

theorem atPlace_self (v : InfinitePlace E) (x : Cinf E) : atPlace v x v = x v := by
  classical
  exact Pi.single_eq_same (M := fun _ : InfinitePlace E => ℂ) v (x v)

theorem atPlace_of_ne {v w : InfinitePlace E} (h : w ≠ v) (x : Cinf E) : atPlace v x w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun _ : InfinitePlace E => ℂ) h (x v)

def cutGL (v : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) (Cinf E) := cornerGL n (atPlace v)

theorem evGL_cutGL_self (v : InfinitePlace E) (y : GL (Fin n) (Cinf E)) : evGL v (cutGL v y) = evGL v y :=
  map_cornerGL_of_hom _ _ _ (fun x => atPlace_self v x) y

theorem evGL_cutGL_of_ne {v w : InfinitePlace E} (h : w ≠ v) (y : GL (Fin n) (Cinf E)) :
    evGL w (cutGL v y) = 1 :=
  map_cornerGL_of_zero _ _ (fun x => atPlace_of_ne h x) y

theorem unitary_iff_evGL (y : GL (Fin n) (Cinf E)) :
    y.valᴴ * y.val = 1 ↔ ∀ w, (evGL w y).valᴴ * (evGL w y).val = 1 := by
  have key : ∀ (w : InfinitePlace E) i j, ((evGL w y).valᴴ * (evGL w y).val) i j = (y.valᴴ * y.val) i j w := by
    intro w i j
    simp [evGL, Matrix.mul_apply, Finset.sum_apply]
  constructor
  · intro h w
    ext i j
    rw [key, h]
    rcases eq_or_ne i j with rfl | e <;> simp [*]
  · intro h
    ext i j w
    rw [← key, h w]
    rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem cInf_unitary (g : UA E n) : (cInf g).valᴴ * (cInf g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [mul_one] at hg
  have h1 : (cInf g).val = g.1.val.map (pInf E) := rfl
  have h3 : (cT (conjAd E) g.1.val).map (pInf E) = (cInf g).valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, h1]
    exact (infEq E).symm_apply_apply _
  have h5 := congrArg (fun m => m.map (pInf E)) hg
  simp only [Matrix.map_mul, h3, ← h1] at h5
  rw [h5]
  ext1 i j
  rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem continuous_pInfComp : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_cInf : Continuous (cInf : UA E n → GL (Fin n) (Cinf E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map continuous_pInfComp)).comp continuous_subtype_val

theorem continuous_cutGL (v : InfinitePlace E) : Continuous (cutGL v : GL (Fin n) (Cinf E) → _) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (atPlace v : Cinf E → Cinf E) :=
    continuous_pi fun w => by
      by_cases h : w = v
      · subst h
        exact (show Continuous fun x : Cinf E => x w from continuous_apply w).congr
          fun x => (atPlace_self w x).symm
      · exact continuous_const.congr fun x => (atPlace_of_ne h x).symm
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem continuous_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) :=
    (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem coord_embedding (w : InfinitePlace E) : coord w.embedding = Pi.evalRingHom (fun _ => ℂ) w := by
  have h := InfinitePlace.mk_embedding w
  unfold coord
  rw [if_pos (by rw [h]), h]

theorem map_coord_of_evGL (τ : E →+* ℂ) {y : GL (Fin n) (Cinf E)} (h : evGL (InfinitePlace.mk τ) y = 1) :
    GeneralLinearGroup.map (coord τ) y = 1 := by
  unfold coord
  split_ifs
  · exact h
  · have : GeneralLinearGroup.map ((starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))) y =
        GeneralLinearGroup.map (starRingEnd ℂ) (evGL (InfinitePlace.mk τ) y) := by
      ext i j
      rfl
    rw [this, h, map_one]

theorem evGL_cInf_of_mem {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) {w : InfinitePlace E}
    (h : w ≠ InfinitePlace.mk τ) : evGL w (cInf x) = 1 := by
  have h1 : x ∈ (cEmb (n := n) w.embedding).ker :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) (by rwa [InfinitePlace.mk_embedding])
  have h2 : GeneralLinearGroup.map (coord w.embedding) (cInf x) = 1 := MonoidHom.mem_ker.1 h1
  rwa [coord_embedding] at h2

def cutGA (τ : E →+* ℂ) : UA E n →* GA E n := (infGL E n).comp ((cutGL (InfinitePlace.mk τ)).comp cInf)

theorem cutGA_mem_UA (τ : E →+* ℂ) (g : UA E n) : cutGA τ g ∈ UA E n := by
  refine infGL_mem_UA (cutGL (InfinitePlace.mk τ) (cInf g)) ((unitary_iff_evGL _).2 fun w => ?_)
  by_cases h : w = InfinitePlace.mk τ
  · subst h
    rw [evGL_cutGL_self]
    exact (unitary_iff_evGL _).1 (cInf_unitary g) _
  · rw [evGL_cutGL_of_ne h]
    simp

theorem cInf_cutGA (τ : E →+* ℂ) (g : UA E n) :
    cInf (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) :=
  pInf_infGL _

theorem cutGA_mem_embU (τ : E →+* ℂ) (g : UA E n) : (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) ∈ embU n τ := by
  refine ⟨pFin_infGL _, Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_⟩
  change GeneralLinearGroup.map (coord τ') (cInf _) = 1
  rw [cInf_cutGA]
  exact map_coord_of_evGL τ' (evGL_cutGL_of_ne h _)

def embRet (τ : E →+* ℂ) : UA E n →* embU n τ where
  toFun g := ⟨⟨cutGA τ g, cutGA_mem_UA τ g⟩, cutGA_mem_embU τ g⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (cutGA τ)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (cutGA τ) a b))

theorem cInf_embRet (τ : E →+* ℂ) (g : UA E n) :
    cInf (embRet τ g : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) := cInf_cutGA τ g

theorem continuous_embRet (τ : E →+* ℂ) : Continuous (embRet (n := n) τ) :=
  Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_infGL.comp ((continuous_cutGL _).comp continuous_cInf)) _) _

theorem embRet_apply (τ : E →+* ℂ) (x : embU n τ) : embRet τ (x : UA E n) = x := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · refine (cInf_embRet τ x.1).trans (gl_ext_evGL fun w => ?_)
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      exact evGL_cutGL_self _ _
    · rw [evGL_cutGL_of_ne h]
      exact (evGL_cInf_of_mem x.2 h).symm
  · exact (pFin_infGL _).trans (MonoidHom.mem_ker.1 x.2.1).symm

theorem commute_embRet (τ : E →+* ℂ) (g : UA E n) (y : embU n τ) :
    Commute ((embRet τ g : UA E n)⁻¹ * g) (y : UA E n) := by
  have h2 : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2.1
  have h1 : evGL (InfinitePlace.mk τ) (cInf ((embRet τ g : UA E n)⁻¹ * g)) = 1 := by
    rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, evGL_cutGL_self, inv_mul_cancel]
  generalize (embRet τ g : UA E n)⁻¹ * g = a at h1 ⊢
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * y.1) = cInf (y.1 * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      rw [h1, one_mul, mul_one]
    · rw [evGL_cInf_of_mem y.2 h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]

theorem exists_embRet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧
      ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  fun _ _ _ _ _ τ => ⟨embRet τ, continuous_embRet τ, embRet_apply τ, commute_embRet τ⟩

end GlobalTheory.DefU

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VecP


open scoped ComplexOrder in
theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hε1 : ∀ a, ε a = 1 := fun a =>
    ((hε a).resolve_right fun h' => absurd h'.2 (not_le.mpr a.2)).1
  have hB1 : Bᴴ * G * B = 1 := by simpa [hε1] using hB
  have hBC : B * (Bᴴ * G) = 1 := mul_eq_one_comm.mp hB1
  have hGB : G * B = (Bᴴ * G)ᴴ := by
    calc G * B = (B * (Bᴴ * G))ᴴ * (G * B) := by rw [hBC, conjTranspose_one, Matrix.one_mul]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ := by rw [hB1, Matrix.mul_one]
  have hG : G = (Bᴴ * G)ᴴ * (Bᴴ * G) := by
    calc G = G * (B * (Bᴴ * G)) := by rw [hBC, Matrix.mul_one]
      _ = G * B * (Bᴴ * G) := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G) := by rw [hGB]
  have hinj : Function.Injective (Bᴴ * G).mulVec := by
    intro v w hvw
    have h2 := congrArg (fun x => B *ᵥ x) hvw
    simpa only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec] using h2
  unfold IsCartanInv
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end GlobalTheory.OneMapRef.VecP
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.JIota

theorem heq_iota_iff_eq_trans_castAdelicGroup (D : D7) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) :
    HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ↔
      ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  rw [heq_iff_eq]
  constructor
  · intro e; subst e; rfl
  · intro e; subst e; rfl

theorem heq_iota_iff : ∀ (D : D7) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA), HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ↔ ι = (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv :=
  fun D St h ι => heq_iota_iff_eq_trans_castAdelicGroup D St.B.I h ι

end GlobalTheory.Mem.JIota
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.localComponents_nontrivial_adelic_character : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  first | exact @GlobalTheory.GaugeEx.CharLoc.char_local | exact GlobalTheory.GaugeEx.CharLoc.char_local | (intros; apply GlobalTheory.GaugeEx.CharLoc.char_local <;> assumption)
end
