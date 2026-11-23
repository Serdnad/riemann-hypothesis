module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle425
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle513
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV

@[expose] public section

section

noncomputable section

namespace GlobalTheory.JSW

open Finset

theorem cauchy_local {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) α * schurAt l.1 β‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i j, 1 - α i * β j * T ≠ 0) ∧
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} =>
      schurAt (padTo hmn l.1) α * schurAt l.1 β * T ^ (∑ i, l.1 i))
      (∏ i, ∏ j, (1 - α i * β j * T)⁻¹) := by
  set G : (Fin m → ℕ) → ℂ := fun l => schurAt (padTo hmn l) α * schurAt l β * T ^ (∑ i, l i) with hGdef
  have hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖ := by
    refine hs.congr fun l => ?_
    simp [G, norm_pow]
  obtain ⟨hsum, htrans⟩ := GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree G hG
  have hc : (fun d => ∑ l ∈ antiParts m d, G l) = fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
      ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
    funext d
    rw [← GlobalTheory.T.cauchy_identity_schur_formal_degree hmn α β d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [G]; rw [(mem_antiParts.1 hl).1]; ring
  have h5 := GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one α β T
  rw [← hc] at h5
  obtain ⟨hne, hhas⟩ := GlobalTheory.T.eulerInverse_powerSeries_eval_one _ hsum (fun p : Fin n × Fin m => α p.1 * β p.2 * T) h5
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Fintype.prod_prod_type] at hne
    exact Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne i (mem_univ _)) j (mem_univ _)
  · have := htrans _ hhas
    rw [← Finset.prod_inv_distrib, Fintype.prod_prod_type] at this
    exact this

theorem multiset_prod_map_product_eq_prod_prod {X Y : Type} (A : Multiset X) (B : Multiset Y) (f : X × Y → ℂ) :
    ((A ×ˢ B).map f).prod = (A.map fun a => (B.map fun b => f (a, b)).prod).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [Multiset.cons_product, ih]

theorem locL_univ (q : ℕ) {m n : ℕ} (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (s : ℂ) :
    locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s =
      ∏ i, ∏ j, (1 - (α i : ℂ) * β j * (q : ℂ) ^ (-s))⁻¹ := by
  rw [locL, multiset_prod_map_product_eq_prod_prod, Multiset.map_map]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

theorem cauchy_locL {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (q : ℕ) (s : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β j : ℂ))‖ *
        ‖(q : ℂ) ^ (-s)‖ ^ (∑ i, l.1 i)) :
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} => schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) *
      schurAt l.1 (fun j => (β j : ℂ)) * ((q : ℂ) ^ (-s)) ^ (∑ i, l.1 i))
      (locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s) := by
  rw [locL_univ]; exact (cauchy_local hmn _ _ _ hs).2

end GlobalTheory.JSW
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem exists_lifts_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  intro l _ P AI T K c hc
  obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity l K c c.2 hc
  have h1 : ∀ i, ∃ w : Ainf l, Lifts AI K w ⟨ω i, (hω i).1⟩ := by
    intro i
    obtain ⟨hK, m, hm, hl, hx⟩ := hω i
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (ω i) m hm hl hx
    exact ⟨_, AI.ιA_teich ⟨ω i, hK.2⟩ m hm hl hx xb hxb⟩
  choose w hw using h1
  have h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩ := by
    apply Subtype.ext
    rw [hsum]
    push_cast
    rfl
  refine ⟨∑ i, algebraMap ℤ_[l] (Ainf l) (z i) * w i, ?_⟩
  unfold Lifts at hw ⊢

  rw [h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hw, ιA_zl AI T, ← IsScalarTower.algebraMap_apply]

end GlobalTheory.ExpImage
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

def idxAt {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : w.under (𝓞 D.host.F) = v) (g : GlobalTheory.FinZeta.Gv T v) : ℕ :=
  ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
    (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).relIndex
    (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup

end GlobalTheory.LocKerMod
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG

namespace GlobalTheory.UnitaryBC.NonSplit

variable {E : Type} [Field E] [NumberField E]

theorem matrix_ext_pLoc {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Af E)}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), A.map (pLoc E u) = B.map (pLoc E u)) : A = B :=
  Matrix.ext fun i j => FiniteAdeleRing.ext E fun u => congrFun₂ (H u) i j

theorem continuous_finGL' (n : ℕ) : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem eq_conjSrc_self (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) :
    w = conjSrc c w := by
  refine eq_conjSrc fun k => ?_
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
    w.valuedAdicCompletion_eq_valuation' _
  rw [← h1, ← h2, ← hs, hv]

theorem cT_locGL_mul (c : E ≃+* E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E) (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    cT (conjFin c) (locGL E n w g).val * (locGL E n w g).val = 1 := by
  refine matrix_ext_pLoc fun u => ?_
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  by_cases hu : u = w
  · subst hu
    have e1 : (locGL E n u g).val.map (pLoc E u) = g.val := congrArg Units.val (pLoc_locGL u g)
    have e2 : (cT (conjFin c) (locGL E n u g).val).map (pLoc E u) = cT s g.val := by
      ext1 i j
      change pLoc E u (conjFin c ((locGL E n u g).val j i)) = s (g.val j i)
      rw [← e1]
      exact pLoc_conjFin_eq c u s hs hv _
    rw [e1, e2, hg]
  · have hne : conjSrc c u ≠ w := fun e =>
      hu (conjSrc_injective c (e.trans (eq_conjSrc_self c w s hs hv)))
    have e1 : (locGL E n w g).val.map (pLoc E u) = 1 := congrArg Units.val (pLoc_locGL_of_ne hu g)
    have e3 : (locGL E n w g).val.map (pLoc E (conjSrc c u)) = 1 := congrArg Units.val (pLoc_locGL_of_ne hne g)
    have e2 : (cT (conjFin c) (locGL E n w g).val).map (pLoc E u) = 1 := by
      ext1 i j
      change conjLoc c u (((locGL E n w g).val.map (pLoc E (conjSrc c u))) j i) = _
      rw [e3]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij, Ne.symm hij]
    rw [e1, e2, Matrix.mul_one]

variable [IsCMField E]

theorem finGL_locGL_mem_UA {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  have h1 : (finGL E n (locGL E n w g)).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL (locGL E n w g))
  have h2 : (finGL E n (locGL E n w g)).val.map (pFin E) = (locGL E n w g).val :=
    congrArg Units.val (pFin_finGL (locGL E n w g))
  have h3 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pInf E) = 1 := by
    ext1 i j
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) (pInf E ((finGL E n (locGL E n w g)).val j i)))) = _
    rw [RingEquiv.symm_apply_apply]
    change starRingEnd (Cinf E) (((finGL E n (locGL E n w g)).val.map (pInf E)) j i) = _
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  have h4 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pFin E) =
      cT (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E n w g).val := by
    ext1 i j
    change conjFin _ (((finGL E n (locGL E n w g)).val.map (pFin E)) j i) = _
    rw [h2]
    rfl
  have h5 := cT_locGL_mul (IsCMField.complexConj E).toRingEquiv w s hs hv g hg
  have h6 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pInf E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) := by
    rw [Matrix.map_mul, h3, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have h7 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pFin E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) := by
    rw [Matrix.map_mul, h4, h2, h5, Matrix.map_one _ (map_zero _) (map_one _)]
  ext1 i j
  exact ad_ext (congrFun₂ h6 i j) (congrFun₂ h7 i j)

end GlobalTheory.UnitaryBC.NonSplit


open GlobalTheory.UnitaryBC.NonSplit in
theorem GlobalTheory.UnitaryBC.exists_locUnitary_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w →
    ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧
      (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧
      ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  intro E _ _ _ n w s hs hv hns
  have hU : ∀ g : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      finGL E n (locGL E n w g.1) ∈ UA E n := fun g => by
    refine finGL_locGL_mem_UA w s hs hv g.1 ?_
    have h : cT s g.1.val * 1 * g.1.val = 1 := g.2
    rwa [Matrix.mul_one] at h
  refine ⟨((finGL E n).comp ((locGL E n w).comp (Formalism.UG.UJ s 1).subtype)).codRestrict (UA E n) hU,
    Continuous.subtype_mk (((continuous_finGL' n).comp (CuspSub.continuous_locGL w)).comp continuous_subtype_val) _,
    fun g => ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, ?_⟩, fun x hx h1 => ?_, fun x g h1 => ?_⟩
  · change GeneralLinearGroup.map (pInf E) (finGL E n (locGL E n w g.1)) = 1
    exact pInf_finGL _
  · change GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = 1
    rw [pFin_finGL]
    exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = g.1
    rw [pFin_finGL, pLoc_locGL]
  · obtain ⟨hxf, hxi⟩ := Subgroup.mem_inf.1 hx
    have hinf : GeneralLinearGroup.map (pInf E) x.1 = 1 := MonoidHom.mem_ker.1 hxf
    have hloc : ∀ u, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) x.1) = 1 := fun u => by
      by_cases hu : u = w
      · subst hu; exact h1
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hns ⟨u, hu, e⟩
        exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxi u) hu')
    refine Subtype.ext (ga_ext (hinf.trans (map_one _).symm) ?_)
    change _ = GeneralLinearGroup.map (pFin E) 1
    rw [map_one]
    exact LocUniq.gl_ext fun u => by rw [hloc u, map_one]
  · have hk : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x.1) = 1 := h1
    apply Subtype.ext
    change x.1 * finGL E n (locGL E n w g.1) = finGL E n (locGL E n w g.1) * x.1
    obtain ⟨y, k, hx, hk'⟩ : ∃ y k, x.1 = infGL E n y * finGL E n k ∧ GeneralLinearGroup.map (pLoc E w) k = 1 :=
      ⟨_, _, (infGL_mul_finGL x.1).symm, hk⟩
    rw [hx, mul_assoc, ← map_mul, LocUniq.comm_locGL w hk' g.1, map_mul, ← mul_assoc, infGL_comm, mul_assoc]

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.conductor_rec_compatible : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → ∀ x : IrrGL (k := w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  first | exact @GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD | exact GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD | (intros; apply GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.linearIndependent_cyclotomicEigenvectors_weights : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n ℂ_[l]) (ι : Type) [Fintype ι] (v : ι → n → ℂ_[l]) (w : ι → ℤ), (∀ (g : ↥(GK K)) j, (A g).mulVec (fun i => Formalism.Per.σC (g : GQ l) (v j i)) = algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) • v j) → (∀ (a : ℤ) (c : ι → Om l), (∀ j, c j ∈ K.1) → (∀ j, w j ≠ a → c j = 0) → ∑ j, (c j : ℂ_[l]) • v j = 0 → c = 0) → LinearIndependent ℂ_[l] v := by
  first | exact @GlobalTheory.PMon.linIndep_of_eigen_weights | exact GlobalTheory.PMon.linIndep_of_eigen_weights | (intros; apply GlobalTheory.PMon.linIndep_of_eigen_weights <;> assumption)
end

section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpRestrict

open GlobalTheory.DRFil

theorem jump_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  intro l _ P AI T K K' LL hle V _ _ _ _ _ ρ hc τ' a hj
  have := K.2
  have := K'.2
  have := LL.2
  set τ := τ'.comp (IntermediateField.inclusion hle) with hτ
  have hF := isField_dR T
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) hF ρ (filSpans T K LL ρ (crys T K LL ρ hc).1) τ
  set e' := idem (K := ↥K'.1) P.R.BdR (LL := ↥LL.1) τ' with he'
  set e := idem (K := ↥K.1) P.R.BdR (LL := ↥LL.1) τ with he
  have hee : e' * e = e' := by
    obtain ⟨n, x, c, hc1, hc2⟩ := idem_repr (K := ↥K.1) P.R.BdR τ
    rw [he, hc1]
    have := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ' n x (fun i => IntermediateField.inclusion hle (c i))
    exact (this.trans (by rw [← hc2]; rfl)).trans (one_smul _ _)
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ'
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V e' (d i)) k := by
    refine ⟨fun i => ⟨?_, ?_⟩, fun r hr i => ?_, fun n y hy => ?_⟩
    · exact sm_idem_mem_DdRE (P.PD K') _ τ' (GlobalTheory.Per.TiedRestrict.ddR_le hle ρ (hA.mem i).1.1)
    · refine sm_idem_mem_FilV (P.PD K') τ' ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (hA.mem i).2
    · have h1 := hA.indep (fun i => r i * e') (by
        rw [← hr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_mul])
      calc e' * r i = (e' * e) * r i := by rw [hee]
        _ = e * (r i * e') := by ring
        _ = 0 := h1 i
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']
        exact hr i
      · have h2 : sm ℚ_[l] P.R.BdR ↥LL.1 V e' y =
            sm ℚ_[l] P.R.BdR ↥LL.1 V e' (sm ℚ_[l] P.R.BdR ↥LL.1 V e y) := by
          rw [← sm_mul, hee]

        rw [h2, hy', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_comm]
  rw [hA'.isJumpV_iff] at hj
  exact hA.isJumpV_iff a |>.2 hj

end GlobalTheory.Per.JumpRestrict
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.cyc_zpow_crys_dR_jump_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  first | exact @GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | exact GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | (intros; apply GlobalTheory.CycPow.cyc_zpow_crys_dR_jump <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.finrank_dcrisLetter_deRhamComponent_eq_dim : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  first | exact @GlobalTheory.Per.LetterDim.tied_letter_component_finrank | exact GlobalTheory.Per.LetterDim.tied_letter_component_finrank | (intros; apply GlobalTheory.Per.LetterDim.tied_letter_component_finrank <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.restrict_crystalline_deRham_finiteExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (IsCrys (P.PD K) ρ → IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) ∧ (IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  first | exact @GlobalTheory.Per.TiedRestrict.restrict_crys_deRham | exact GlobalTheory.Per.TiedRestrict.restrict_crys_deRham | (intros; apply GlobalTheory.Per.TiedRestrict.restrict_crys_deRham <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.galois_representation_hom_finite_dimensional : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  first | exact @GlobalTheory.DRDual.twisted_dual_deRham | exact GlobalTheory.DRDual.twisted_dual_deRham | (intros; apply GlobalTheory.DRDual.twisted_dual_deRham <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.deRham_subrep_quotient_and_strictness : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  first | exact @GlobalTheory.DRSubQuot.deRham_sub_quot | exact GlobalTheory.DRSubQuot.deRham_sub_quot | (intros; apply GlobalTheory.DRSubQuot.deRham_sub_quot <;> assumption)
end
