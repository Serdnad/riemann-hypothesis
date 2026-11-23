module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)

include h hj

theorem esec_mem_C {w : WeightFamilies.Wt D j} {f : T.R j} : f ∈ cutR T.C j w ↔ f ∈ T.C j w := by
  rw [cutR_eq T.C hj]

theorem esec_mul_mem {w w' : WeightFamilies.Wt D j} {f g : T.R j} (hf : f ∈ cutR T.C j w) (hg : g ∈ cutR T.C j w') :
    f * g ∈ cutR T.C j (wadd w w') := by
  rw [esec_mem_C h hj] at hf hg ⊢
  exact h.toLawsCore.mul j hj w w' f hf g hg

def esecMul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w) (F' : (recB h.toLawsCore).Cusp j w') :
    (recB h.toLawsCore).Cusp j (wadd w w') :=
  ⟨(F : T.R j) * (F' : T.R j), esec_mul_mem h hj F.2 F'.2⟩

theorem esecMul_coe {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    ((esecMul h hj F F' : (recB h.toLawsCore).Cusp j (wadd w w')) : T.R j) = (F : T.R j) * (F' : T.R j) := rfl

theorem esec_inc_mul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    (recPJ h j hj).inc (wadd w w') (esecMul h hj F F') = (recPJ h j hj).inc w F * (recPJ h j hj).inc w' F' :=
  (incG_mul deg (cutR T.C j) (deg_wadd w w') F F' (esec_mul_mem h hj F.2 F'.2)).symm

def esecW (wL : WeightFamilies.Wt D j) : ℕ → WeightFamilies.Wt D j
  | 0 => wL
  | n + 1 => wadd wL (esecW wL n)

omit h hj in
theorem esecW_eq (wL : WeightFamilies.Wt D j) (n : ℕ) : esecW wL n = addL (wt0 D j) wL (n + 1) := by
  induction n with
  | zero => exact (add_zero_weight_one_eq wL).symm
  | succ n ih => rw [esecW, ih, wadd_addL]

def esecPow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) :
    (n : ℕ) → (recB h.toLawsCore).Cusp j (esecW wL n)
  | 0 => F
  | n + 1 => esecMul h hj F (esecPow F n)

theorem esec_inc_pow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) (n : ℕ) :
    (recPJ h j hj).inc (esecW wL n) (esecPow h hj F n) = (recPJ h j hj).inc wL F ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one]; rfl
  | succ n ih =>
    show (recPJ h j hj).inc (wadd wL (esecW wL n)) (esecMul h hj F (esecPow h hj F n)) = _
    rw [esec_inc_mul, ih, pow_succ' _ (n + 1)]

theorem esec_mem_mulL {wL : WeightFamilies.Wt D j} {a b : ℕ} {f g : T.R j}
    (hf : f ∈ cutR T.C j (addL (wt0 D j) wL a)) (hg : g ∈ cutR T.C j (addL (wt0 D j) wL b)) :
    f * g ∈ cutR T.C j (addL (wt0 D j) wL (a + b)) := by
  have := esec_mul_mem h hj hf hg
  rwa [wadd_addL_addL, zero_weight_add] at this

theorem esec_pow_mem {wL : WeightFamilies.Wt D j} {f : T.R j} (hf : f ∈ cutR T.C j wL) (n : ℕ) :
    f ^ (n + 1) ∈ cutR T.C j (addL (wt0 D j) wL (n + 1)) := by
  induction n with
  | zero => rw [zero_add, pow_one, add_zero_weight_one_eq]; exact hf
  | succ n ih =>
    rw [pow_succ]
    have hf' : f ∈ cutR T.C j (addL (wt0 D j) wL 1) := by rw [add_zero_weight_one_eq]; exact hf
    exact esec_mem_mulL h hj ih hf'

theorem esec_monomial_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (α : Fin N →₀ ℕ) :
    α = 0 ∨ (α.prod fun i k => x i ^ k) ∈ cutR T.C j (addL (wt0 D j) wL (α.sum fun _ k => k)) := by
  classical
  induction α using Finsupp.induction with
  | zero => exact Or.inl rfl
  | single_add a b f ha hb ih =>
    right
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.prod_single_index (h := fun i k => x i ^ k) (pow_zero _),
      Finsupp.sum_single_index rfl]
    rcases ih with h0 | hmem
    · subst h0
      simp only [Finsupp.prod_zero_index, Finsupp.sum_zero_index, mul_one, add_zero]
      exact esec_pow_mem h hj (hx a) b
    · exact esec_mem_mulL h hj (esec_pow_mem h hj (hx a) b) hmem

theorem esec_hom_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (P : MvPolynomial (Fin N) T.Q.c.F) {k : ℕ} (hP : P.IsHomogeneous (k + 1)) :
    MvPolynomial.aeval x P ∈ cutR T.C j (addL (wt0 D j) wL (k + 1)) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : (α.sum fun _ k => k) = k + 1 := by
    have := hP (MvPolynomial.mem_support_iff.mp hα)
    rw [Finsupp.weight_apply] at this
    simpa using this
  rcases esec_monomial_mem h hj x hx α with h0 | hmem
  · subst h0
    simp at hdeg
  · rwa [hdeg] at hmem

theorem esec_evC_aeval (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (Z : Comp (T.Q.Xo j) T.Q.c) {N : ℕ} (x : Fin N → T.R j) (P : MvPolynomial (Fin N) T.Q.c.F) :
    evC hG Z (MvPolynomial.aeval x P) = MvPolynomial.aeval (fun i => evC hG Z (x i)) P := by
  rw [← evCAlg_apply hG hT Z]
  exact DFunLike.congr_fun (MvPolynomial.comp_aeval x (evCAlg hG hT Z)) P

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parameterOfRecord (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : Par D where
  H := hostOf D (unramBridge D.host.E (cmUnram_conj D))
  l := levelG D (hU := unramBridge D.host.E (cmUnram_conj D))
  c := coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz
  Dw := datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat
  Xo := fun j => Classical.choice (hN D.host.E (hostOf D (unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat j) (levelG D (hU := unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift_pq_pos D (unramBridge D.host.E (cmUnram_conj D)) hDat j))
  eO := eOf D hF

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def kfW (V : HSp D) (N : ℕ) : Subgroup (GA D V) := Subgroup.closure (levSet V N)

def LevGrp (V : HSp D) (N : ℕ) : Prop := ∀ k ∈ kfW V N, k ∈ levSet V N

section One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdIndep1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))

def HolFD1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional ℂ (holSub U.X (laU U a n))

def RdDomInj1 (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, rdU U f ∈ holSub U.X (laU U a n) →
    (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0

def AdelMeas1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), P ∈ holSub U.X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0

end One

abbrev PkgT (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Type 1 :=
  Σ U : Unf (Q.Xo j) Q.c σ D.R.r, (GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) × (GA D (D.sp.W j) → ℂ)

structure PkgOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (U : Unf (Q.Xo j) Q.c σ D.R.r)
    (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (mu : GA D (D.sp.W j) → ℂ) : Prop where

  unf : IsUnf U

  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (U.un k x)

  chiTriv : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1

  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) dict (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr

  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (U.X k).ξ0‖ = xiR D

  muUnit : MuUnit (D.sp.W j) dict mu
  muCont : Continuous mu

  rdIndep : RdIndep1 U
  holFD : HolFD1 U

  rdDomInj : RdDomInj1 U

  adelMeas : AdelMeas1 U (D.sp.W j) dict mu

  aeDom : AeDom1 U (D.sp.W j) dict mu

  latZ : FJ.LatZ U.X (WeightFamilies.rho D j)
  cuNe : FJ.CuNeF U.X (WeightFamilies.rho D j)
  expo : FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

def FamOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)), IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty →
    Nonempty (FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) ty)

def HalfPb (Q : Par D) : Prop :=
  ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧
    Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

structure LawsRest (Q : Par D) : Prop where

  evalWD : ∀ j, InR D j → EvalWD (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z)

  wtField : ∀ j, InR D j → WtField (Q.Xo j) Q.c
  intDiagUnit : ∀ j, InR D j → IntDiagUnit (Q.Xo j) Q.c

  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c
  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c

  m5 : SiegelSpaceAlgebra (E := D.host.E)

  volTie : VolTieG D

  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)

  half : HalfPb Q

  pkg : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ → ∃ U dict mu, PkgOK Q j σ U dict mu

  dataAll : ∀ j σ, Nonempty (PkgT Q j σ)

section Build

variable {Q : Par D}

theorem pkgEx (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : ∃ p : PkgT Q j σ, InR D j → GoodEmb Q.c σ → PkgOK Q j σ p.1 p.2.1 p.2.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · obtain ⟨U, dict, mu, h⟩ := hRs.pkg j hj σ hσ (hfam j hj σ hσ)
      exact ⟨⟨U, dict, mu⟩, fun _ _ => h⟩
    · exact ⟨Classical.choice (hRs.dataAll j σ), fun _ h => absurd h hσ⟩
  · exact ⟨Classical.choice (hRs.dataAll j σ), fun h => absurd h hj⟩

def pkgOf (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : PkgT Q j σ := (pkgEx hRs hfam j σ).choose

end Build

theorem datHolds (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T)

theorem combAlg_of_combBound (j : ℕ) (hj : InR D j) (hjm : j < D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (cb / (2 * (G.iet : ℝ))) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨T', io, e, ho, z, hz, eta, heta, hq⟩ := y0.2
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la T' io e ho z hz
  let y : T.PtA j la := PtV.mk la ho z hz η hη
  have hyv : vAtV y = vAtV y0 := funext fun g => by
    show y.1.1 g = y0.1.1 g
    rw [hq]
    rfl
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hyv]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  obtain ⟨h0, h1⟩ := (hX la y).1 hjm
  rw [hv] at h0 h1
  rw [hd] at h1
  refine ⟨h0, fun htop => ?_⟩
  have h2 := h1 htop
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_toReal htop (vAtV_ne_bot y0 _)] at h2
  exact h2

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Full (D : D7) : Type 1 extends Top D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)
  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  half₂ : Ideal (𝓞 D.host.E)

variable {D : D7}

def Full.J (T : Full D) : CoreJ D :=
  { toCore := T.toTop.toCore, cE := T.cE, chiW := T.chiW, x₀ := T.x₀, iota := T.iota }

def Full.XiVal (T : Full D) (j n : ℕ) : Prop :=
  ∃ (hr : (T.V j T.σ₀).rank = D.R.r) (U₂ : _) (dict₂ : _),
    CXiVal (T.V j T.σ₀) hr T.σ₀ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j T.σ₀) fun _ => T.xi

structure LawsFull (T : Full D) : Prop where
  p : LawsP T.toTop
  j : LawsJ T.J
  sh : LawsSh T.toTop

  canon : T.Q.Canon

  lvA : ∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1

  halfI : ∀ j, InR D j → ∀ n, (T.dδ j n).I = T.half₂

  shUniq : ∀ j, InR D j → ∀ n (_ : StarRing (𝓞 D.host.E)) (nab' : NabV (T.dδ j n).Xo₂ (T.dδ j n).c₂),
    IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ nab' → ∀ a, Dom a n →
      shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n { T.dδ j n with nab₂ := nab' } =
        shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)

  xiVal : ∀ j, InR D j → ∀ n, T.XiVal j n

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
  (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def EtCusp : Prop := η ≠ 0 ∧ (recPJ h j hj).NonZeroComp _ η

def EtVal : Prop :=
  ∀ la (y : (recPJ h j hj).Pt la),
    ((2 * i * (recPJ h j hj).phiC la y : ℝ) : EReal) ≤ (recPJ h j hj).vAt la y ((recPJ h j hj).inc _ η)

def EtSup (P : ℝ) : Prop := ∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ η) / i ≤ P

variable (P : ℝ) (Arch : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop)

def ETEx : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧ ∃ η : (recB h.toLawsCore).Cusp j (wEt D j i),
    EtCusp h j ⟨h1, h2.le⟩ i η ∧ EtVal h j ⟨h1, h2.le⟩ i η ∧ EtSup h j i η P ∧ Arch j i η

variable {h P Arch}

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def rdR {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u) :=
  rdU (T.U j T.σ₀) F.1

def TieReadSt : Prop :=
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp),
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k)) ∧
  ∀ u : WeightFamilies.Wt D j, ReciprocityTheory.ChartRestriction.G.PullbackSections.JInjRd T j (wtA u) u.n

abbrev KT (T : Top D) (j N : ℕ) : Type := FractionRing (MvPolynomial (Idx D j N) T.Q.c.F)

def TieMaxCuspSt (CR Tt c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : (recB h.toLawsCore).Cusp j ka,
    F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt c j ka ↔
      ∀ k, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt c j)

end Formalism.L2.Pj
end
end
