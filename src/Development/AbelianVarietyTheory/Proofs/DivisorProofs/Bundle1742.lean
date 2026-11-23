module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eq_of_toSub_eq {G : Type} [Group G] {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H)
    (e : toSub H g = toSub H h) : g = h := by
  unfold toSub at e
  rw [dite_eq_left hg, dite_eq_left hh] at e
  exact congrArg Subtype.val e

theorem under_conjSrc (w : Pl E) :
    (conjSrc (GlobalTheory.SplitPts.conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
    (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  by_contra h
  exact hw ⟨_, h, under_conjSrc w⟩

theorem ext_cj (w : Pl E) (a : Af E) : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
    Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      f (pLoc E v a) = cj w (pLoc E w a) := by
  rintro v rfl f hf h
  have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
  have hcj : cj v = hex.choose := by unfold cj; rw [dite_eq_left hex]
  rw [hcj]
  exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
    (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _

theorem cLoc_mem_UL {w : Pl E} (hw : ¬ IsSplitAt w) (x : UA E n) : cLoc w x ∈ UL n w := by
  have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
  rw [hUL]
  show cT (cj w) (cLoc w x).val * 1 * (cLoc w x).val = 1
  have hc := GlobalTheory.SplitPts.comp_eq x w
  have e : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) =
      (cLoc w x).val.map (cj w) := by
    refine Matrix.ext fun i j => ?_
    exact ext_cj w (pFin E (x.1.val i j)) _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec _ w).1
      (conjLoc_spec _ w).2.1
  rw [e] at hc
  rw [Matrix.mul_one]
  exact hc

theorem cLoc_conj_eq (w : Pl E) (x y : UA E n) (h : cLoc w x = cLoc w y) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y := by
  have hx := GlobalTheory.SplitPts.comp_eq x w
  have hy := GlobalTheory.SplitPts.comp_eq y w
  rw [h] at hx
  have e : ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ := by
    have h1 := mul_eq_one_comm.1 hx
    have h2 := mul_eq_one_comm.1 hy
    calc _ = ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
            ((cLoc w y).val * ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map
              (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ) := by rw [← Matrix.mul_assoc, hy, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective ?_)
  have := congrFun (congrFun e j) i
  simpa using this

end GlobalTheory.LocInj

open GlobalTheory.LocInj in
theorem GlobalTheory.BCT.finU_eq_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ S : Set (Pl E), IsSection S → ∀ x y : finU (E := E) (n := n),
      (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  intro E _ _ _ _ n S hS x y hxy

  have hS' : ∀ w ∈ S, cLoc w (x : UA E n) = cLoc w (y : UA E n) := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have hUL : ∀ g, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hsp]; trivial
      exact eq_of_toSub_eq (hUL _) (hUL _) (hxy w hw)
    · exact eq_of_toSub_eq (_root_.GlobalTheory.LocInj.cLoc_mem_UL hsp _) (_root_.GlobalTheory.LocInj.cLoc_mem_UL hsp _) (hxy w hw)

  have hall : ∀ u : Pl E, cLoc u (x : UA E n) = cLoc u (y : UA E n) := by
    intro u
    obtain ⟨s, ⟨hsS, hsu⟩, -⟩ := hS u
    by_cases hus : u = s
    · subst hus; exact hS' u hsS
    · have hsp : IsSplitAt s := ⟨u, hus, hsu.symm⟩
      obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
      rcases hover u hsu.symm with h | h
      · exact absurd h hus
      · subst h; exact cLoc_conj_eq s _ _ (hS' s hsS)
  have hxi : cInf (x : UA E n) = 1 := MonoidHom.mem_ker.1 x.2
  have hyi : cInf (y : UA E n) = 1 := MonoidHom.mem_ker.1 y.2
  refine Subtype.ext (Subtype.ext (ga_ext (hxi.trans hyi.symm) ?_))
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
  exact congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobLev

open GlobalTheory.SplitPts GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem mem_KGL_iff_val (w : Pl E) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have hO : GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w (n := n) := by
    have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
      Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
    rw [GlobalTheory.LFun.KGL, ← h]; rfl
  rw [← hO, GLnLocal.mem_integralGL_iff]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
  rfl

theorem eq_or_eq_conjSrc {w u : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    u = w ∨ u = conjSrc (conjE E) w := by
  by_cases huw : u = w
  · exact Or.inl huw
  · exact (over_split ⟨u, huw, h⟩).2.2 u h

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (conjE E) w = w := by
  by_contra hne
  exact hw ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (conjPl_self_conjSrc w))⟩

theorem conjLoc_eq_cj {w : Pl E} (hw : ¬ IsSplitAt w) (a : Af E) :
    conjLoc (conjE E) w (pLoc E (conjSrc (conjE E) w) a) = cj w (pLoc E w a) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = cj w (pLoc E w a) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [cj, dite_eq_left hex]
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
      (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _
  exact key _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem cLoc_mem_UL (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have h := comp_eq x w
    have e : (cLoc (conjSrc (conjE E) w) x).val.map (conjLoc (conjE E) w) = (cLoc w x).val.map (cj w) :=
      Matrix.ext fun i j => conjLoc_eq_cj hw _
    rw [e] at h
    change ((cLoc w x).val.map (cj w))ᵀ * 1 * (cLoc w x).val = 1
    rw [Matrix.mul_one]
    exact h

theorem val_inv_entry (x : UA E n) (u : Pl E) (i j : Fin n) :
    Valued.v (((cLoc u x)⁻¹).val i j) = Valued.v ((cLoc (conjSrc (conjE E) u) x).val j i) := by
  have h := comp_eq x u
  have e : ((cLoc u x)⁻¹).val = ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ :=
    (Units.eq_inv_of_mul_eq_one_right h).symm
  rw [e]
  exact (conjLoc_spec (conjE E) u).2.2 _

theorem integral_conjSrc (x : UA E n) (u : Pl E) (h : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) :
    cLoc (conjSrc (conjE E) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) (n := n) := by
  rw [mem_KGL_iff_val] at h ⊢
  refine ⟨fun i j => (val_inv_entry x u j i) ▸ h.2 j i, fun i j => ?_⟩
  have h2 := val_inv_entry x⁻¹ u j i
  rw [map_inv, map_inv, inv_inv] at h2
  exact h2 ▸ h.1 j i

theorem mem_globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU (E := E) (n := n)) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w) ∈ K' w := by
  simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => ⟨?_, fun h => ⟨_, h, rfl⟩⟩
  rintro ⟨a, ha, e⟩
  have : a = ⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ := Subtype.ext e
  exact this ▸ ha


variable (E n) in
def finPart : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)

theorem continuous_finPart : Continuous (finPart E n) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem globLev_KL_eq {S : Set (Pl E)} (hS : IsSection S) :
    globLev S (KL n) = (AdelicGLn.integralFiniteGL E n).comap (finPart E n) := by
  ext k
  have e : k ∈ (AdelicGLn.integralFiniteGL E n).comap (finPart E n) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := n) := by
    rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  rw [e, mem_globLev]
  refine ⟨fun h u => ?_, fun h w _ => h w⟩
  obtain ⟨w, ⟨hw, hwu⟩, -⟩ := hS u
  rcases eq_or_eq_conjSrc hwu.symm with rfl | rfl
  · exact h u hw
  · exact integral_conjSrc k.1 w (h w hw)

theorem continuous_pInf_ad : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_conj_ad : Continuous (conjAd E) :=
  ((continuous_infEq E).comp (continuous_star.comp continuous_pInf_ad)).prodMk
    ((continuous_conjFin _).comp continuous_snd)

theorem isClosedEmbedding_finU : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  haveI : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  have h1 : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
    show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 *
      (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
    exact isClosed_eq (((Units.continuous_val.matrix_map continuous_conj_ad).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  have h2 : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc : Continuous (cInf (E := E) (n := n)) :=
      (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
    exact isClosed_eq hc continuous_const
  exact h1.isClosedEmbedding_subtypeVal.comp h2.isClosedEmbedding_subtypeVal

theorem continuous_finGL_ad : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : Pl E) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem globLev_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧
      IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  intro E _ _ _ _ n _ S hS K' hK
  have hO : IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  have hle : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => (hK.1 w).2.1 ((mem_globLev S _ k).1 hk w hw)
  refine ⟨hO, ?_, ?_, hle, fun k hk => hk⟩
  · refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
    · rw [globLev_KL_eq hS] at hx
      exact hx
    · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  · have hfin : {w | w ∈ S ∧ K' w ≠ KL n w}.Finite := (Filter.eventually_cofinite.1 hK.2).subset fun w hw => hw.2
    have e : (globLev S K' : Set (finU (E := E) (n := n))) = (globLev S (KL n) : Set (finU (E := E) (n := n))) ∩
        ⋂ w ∈ {w | w ∈ S ∧ K' w ≠ KL n w},
          (fun k : finU (E := E) (n := n) => (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w)) ⁻¹' (K' w : Set (UL n w)) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      refine ⟨fun hk => ⟨hle hk, fun w hw => (mem_globLev S _ k).1 hk w hw.1⟩, fun hk => ?_⟩
      refine (mem_globLev S _ k).2 fun w hw => ?_
      by_cases h : K' w = KL n w
      · rw [h]; exact (mem_globLev S _ k).1 hk.1 w hw
      · exact hk.2 w ⟨hw, h⟩
    rw [e]
    exact hO.inter (hfin.isOpen_biInter fun w _ => (hK.1 w).1.preimage
      (Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _))

end GlobalTheory.BCT.GlobLev
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem loc_fields_near : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ (x : A.Pt) (k : ℕ), ∀ᶠ v in 𝓝 x.crd, A.loc (fld A (powFld A G k)) x.1.1 v = powAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (fld A (chernFld A G k)) x.1.1 v = chernAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (transFld A G G' k) x.1.1 v = transAt (fun u => G x.pt (x.ch.symm u)) (fun u => G' x.pt (x.ch.symm u)) v k := by
  intro M _ n A r _ _ G G' hG x k
  obtain ⟨⟨i, y⟩, hy⟩ := x
  have hyt : A.e i y ∈ (A.e i).target := (A.e i).map_source hy
  have hsymm : (A.e i).symm (A.e i y) = y := (A.e i).left_inv hy
  have hcont : Tendsto (A.e i).symm (𝓝 (A.e i y)) (𝓝 y) := by
    have := (A.e i).continuousAt_symm hyt
    rwa [ContinuousAt, hsymm] at this
  obtain ⟨⟨hGu, hGs⟩, ⟨hG'u, hG's⟩⟩ := hG.smooth y
  have e1 := hGs i hy
  have e2 := hG's i hy
  have u1 := e1.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hGu)
  have u2 := e2.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hG'u)
  filter_upwards [(A.e i).open_target.mem_nhds hyt, hcont.eventually (hG.trans y), e1, e2, u1, u2]
    with v hv htr h1 h2 h3 h4
  obtain ⟨T, K, K', hT, hK, hK', hw⟩ := htr
  have hz : (A.e i).symm v ∈ (A.e i).source := (A.e i).map_target hv
  have hzv : A.e i ((A.e i).symm v) = v := (A.e i).right_inv hv
  have hct : Tendsto (A.e i).symm (𝓝 v) (𝓝 ((A.e i).symm v)) := (A.e i).continuousAt_symm hv
  have dT := hT.2 i hz
  have dK := hK.2 i hz
  have dK' := hK'.2 i hz
  rw [hzv] at dT dK dK'
  have key := GlobalTheory.T.chernTransgression_forms_frame_invariant n r (fun u => G y ((A.e i).symm u)) (fun u => G' y ((A.e i).symm u))
    (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
    (fun u => T ((A.e i).symm u)) (fun u => K ((A.e i).symm u)) (fun u => K' ((A.e i).symm u)) v
    h1 h3 h2 h4 dT hT.1 dK hK.1 dK' hK'.1 (hct.eventually hw) k
  refine ⟨?_, ?_, ?_⟩
  · rw [HolAtlas.loc, dite_eq_left hv]
    show ((powAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.1]
  · rw [HolAtlas.loc, dite_eq_left hv]
    show ((chernAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.2.1]
  · rw [HolAtlas.loc, dite_eq_left hv]
    show transAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
      (A.e i ((A.e i).symm v)) k = _
    rw [hzv, key.2.2]

end GlobalTheory.ChernCalc
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first | exact @GlobalTheory.ChernCalc.grWeight_frame_indep | exact GlobalTheory.ChernCalc.grWeight_frame_indep | (intros; apply GlobalTheory.ChernCalc.grWeight_frame_indep <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.PowCurv

def Good (n : ℕ) (v : V n) (f : V n → Ev n) : Prop :=
  (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((f x : Alt n)) S) v) ∧ dbarAt (fun x => (f x : Alt n)) v = 0

variable {n : ℕ} {v : V n}

theorem diff_of_smooth {α : V n → Alt n} (h : ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) (S) :
    DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v := by
  have h1 := h S
  exact h1.differentiableAt (by simp)

theorem good_const (c : Ev n) : Good n v (fun _ => c) := by
  refine ⟨fun S => (GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).1 (c : Alt n) S, ?_⟩
  exact (GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.1 (c : Alt n)

theorem good_sum {J : Type} (s : Finset J) (f : J → V n → Ev n) (h : ∀ j ∈ s, Good n v (f j)) :
    Good n v (fun x => ∑ j ∈ s, f j x) := by
  have hfun : ∀ x, ((∑ j ∈ s, f j x : Ev n) : Alt n) = ∑ j ∈ s, (f j x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.1 J s (fun j x => (f j x : Alt n)) (fun j hj => (h j hj).1), ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.1 J s (fun j x => (f j x : Alt n))
    (fun j hj S => diff_of_smooth (α := fun x => (f j x : Alt n)) (h j hj).1 S)]
  exact Finset.sum_eq_zero fun j hj => (h j hj).2

theorem good_mul (f g : V n → Ev n) (hf : Good n v f) (hg : Good n v g) : Good n v (fun x => f x * g x) := by
  have hfun : ∀ x, ((f x * g x : Ev n) : Alt n) = (f x : Alt n) * (g x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.2.2 (fun x => (f x : Alt n)) (fun x => (g x : Alt n)) hf.1 hg.1, ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.2 f (fun x => (g x : Alt n))
    (diff_of_smooth (α := fun x => (f x : Alt n)) hf.1) (diff_of_smooth (α := fun x => (g x : Alt n)) hg.1)]
  rw [hf.2, hg.2]
  simp

variable {r : Type} [Fintype r] [DecidableEq r]

theorem goodM_mul (M N : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j))
    (hN : ∀ i j, Good n v (fun x => N x i j)) (i j : r) : Good n v (fun x => (M x * N x) i j) := by
  have hfun : (fun x => (M x * N x) i j) = fun x => ∑ k ∈ Finset.univ, M x i k * N x k j := by
    funext x
    rw [Matrix.mul_apply]
  rw [hfun]
  exact good_sum Finset.univ (fun k x => M x i k * N x k j) fun k _ => good_mul _ _ (hM i k) (hN k j)

theorem goodM_pow (M : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j)) (k : ℕ) (i j : r) :
    Good n v (fun x => (M x ^ k) i j) := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    exact good_const _
  | succ k ih =>
    simp only [pow_succ]
    exact goodM_mul (fun x => M x ^ k) M (fun a b => ih a b) hM i j

theorem goodM_curv (G : V n → Matrix r r ℂ) (hG : MContDiffAt ∞ G v) (hd : IsUnit (G v).det) (i j : r) :
    Good n v (fun x => curvEv G x i j) := ⟨((GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients n r G v hG hd) i j).2, GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero n r G v hG hd i j⟩

end GlobalTheory.PowCurv


open GlobalTheory.PowCurv in
theorem GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  intro n r _ _ G G' v hG hd hG' hd' k l i j
  exact goodM_mul (fun x => curvEv G x ^ k) (fun x => curvEv G' x ^ l)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G hG hd c d) k a b)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G' hG' hd' c d) l a b) i j
end
