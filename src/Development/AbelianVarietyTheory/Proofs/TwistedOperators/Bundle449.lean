module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle412
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle414
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
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMeas

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frame_sub_eq (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ v - v) = ((intGL F E n y).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ v) := by
  have e3 : (frGL β y).1 = β.1 * (intGL F E n y).1 * (β⁻¹).1 := rfl
  rw [e3, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

theorem mem_princGL_iff {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ GlobalTheory.Grid.princGL β I ↔ x ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v - v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  rw [GlobalTheory.Grid.mem_princGL, ← stabilizer_eq_stabilizer_lattice F E n Λ β hfr]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨⟨y, rfl⟩, fun v hv => ?_⟩
    rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I, frame_sub_eq]
    intro i
    have hw := (hfr v).1 hv
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun k => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hw k) ⟨_, hy i k, GlobalTheory.LevRedTriv.coe_sub_one_apply y i k⟩
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, rfl, fun i j => ?_⟩
    have h1 := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I _).1 (h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hfr j)) i
    have e : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [frame_sub_eq, e, Matrix.mulVec_single_one] at h1
    obtain ⟨s, hs, e⟩ := h1
    have : s = (y.1 - 1) i j := Subtype.ext (e.trans (GlobalTheory.LevRedTriv.coe_sub_one_apply y i j).symm)
    exact this ▸ hs

theorem princ_eq_congLev [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) :
    UA hc J ⊓ GlobalTheory.Grid.princGL β I = congLev hc J Λ I := by
  ext x
  rw [Subgroup.mem_inf, mem_princGL_iff hfr, mem_congLev]

end General

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

open GlobalTheory.GridJoin

theorem exists_measDat {D : D7} (N : GlobalTheory.Grid.Node D) {V : HSp D} (hsp : SameSp V N.V)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hlat : HEq N.Λ Λ) (hfr : IsFrame N.β N.Λ)
    (I : Ideal (𝓞 D.host.E)) {ν : Measure (GA D V)} {fd : Set (GA D V)}
    (hm : Lev.IsMeasFD V (congLev D.sp.cm V.gram Λ I) ν fd) :
    ∃ md : N.MeasDat, HEq md.ν ν ∧ HEq md.fd fd ∧ md.Is False (N.princ I) := by
  obtain ⟨L, h1, h2, e⟩ := hsp
  obtain ⟨V', S, M, Λ', β⟩ := N
  simp only at e hlat hfr ⊢
  subst e
  obtain rfl := eq_of_heq hlat
  refine ⟨⟨ν, fd⟩, HEq.rfl, HEq.rfl, fun h => h.elim, fun _ => ?_⟩
  unfold GlobalTheory.Grid.Node.princ
  rw [princ_eq_congLev _ _ hfr]
  exact hm

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

theorem measCol_of_choice : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
    (G : GlobalTheory.Grid.GridPre R), G.IsMeas → GlobalTheory.GridJoin.SpMatch G ch.W →
    (∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ) → ch.M.IsRow →
    ∃ (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat),
      (GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).IsMeas ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).ν (ch.M.ν (.grid i 0))) ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).fd (ch.M.fd (.grid i 0))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch G hG hsp hfr hrow
  have H : ∀ i, ∃ md : (G.V i 0).MeasDat, i ≤ D.R.m → HEq md.ν (ch.M.ν (.grid i 0)) ∧
      HEq md.fd (ch.M.fd (.grid i 0)) ∧ md.Is False ((G.V i 0).princ (G.lvl R)) := by
    intro i
    by_cases hi : i ≤ D.R.m
    · have hN := hsp.vert i 0 hi (Nat.zero_le _)
      have hr := hrow.row i hi
      have hne : GlobalTheory.ChiGrid.Node.neg D.R.m (.grid i 0) ≠ 0 := by
        simp only [GlobalTheory.ChiGrid.Node.neg, Nat.sub_zero]
        have := D.R.two_le_m
        omega
      unfold Vol.IsAt at hr
      rw [if_neg hne] at hr
      obtain ⟨md, h1, h2, h3⟩ := exists_measDat (G.V i 0) hN.sp hN.lat (hfr i hi) _ hr
      exact ⟨md, fun _ => ⟨h1, h2, hsp.lvl ▸ h3⟩⟩
    · exact ⟨G.measCol i, fun h => absurd h hi⟩
  choose f hf using H
  refine ⟨f 0, fun i j => match j with | 0 => f (i + 1) | j + 1 => G.mV i (j + 1),
    ⟨fun i hi => ?_, fun i j hi hj => hG.vert i j hi hj, hG.P, hG.X⟩, fun i hi => ?_, fun i hi => ?_⟩
  · cases i <;> exact (hf _ hi).2.2
  · cases i <;> exact (hf _ hi).1
  · cases i <;> exact (hf _ hi).2.1

end GlobalTheory.ColMeas

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinBumpAdj

variable {D : D7}

theorem infPart_conj_eq_zero {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
  rw [e, h, map_zero]

theorem adj_fin {m n : ℕ} {x : Mx D m n} (h : x.map (infPart D) = 0) : (adj x).map (infPart D) = 0 := by
  funext i j
  exact infPart_conj_eq_zero (a := x j i) (congrFun (congrFun h j) i)

theorem smul_fin {m n : ℕ} (c : AE D) {x : Mx D m n} (h : x.map (infPart D) = 0) : (c • x).map (infPart D) = 0 := by
  funext i j
  show infPart D (c * x i j) = 0
  rw [map_mul, show infPart D (x i j) = 0 from congrFun (congrFun h i) j, mul_zero]

theorem continuous_smul_mx {X : Type} [TopologicalSpace X] {m n : ℕ} (c : AE D) {f : X → Mx D m n} (hf : Continuous f) :
    Continuous fun x => c • f x :=
  continuous_matrix fun i j => continuous_const.mul (hf.matrix_elem i j)

variable (S : HSp D) (σ : ℕ)

def adjMap : Mx D S.rank σ →+ Mx D σ S.rank where
  toFun y := incA D (-D.host.xi0⁻¹) • (adj y * gA S)
  map_zero' := by rw [adj_zero, Matrix.zero_mul, smul_zero]
  map_add' _ _ := by rw [adj_add, Matrix.add_mul, smul_add]

def adjInv (η : Mx D σ S.rank) : Mx D S.rank σ := incA D D.host.xi0 • (giA S * adj η)

theorem adjMap_apply (y : Mx D S.rank σ) : adjMap S σ y = incA D (-D.host.xi0⁻¹) • (adj y * gA S) := rfl

theorem adjInv_adjMap (y : Mx D S.rank σ) : adjInv S σ (adjMap S σ y) = y := by
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_gA, Matrix.mul_smul, giA_gA_cancel, smul_smul,
    HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv, one_smul]

theorem adjMap_adjInv (η : Mx D σ S.rank) : adjMap S σ (adjInv S σ η) = η := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    have h1 := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
    rw [map_mul, map_one, GlobalTheory.DualPairCheck.cA_cA] at h1
    rw [mul_comm, h1]
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_giA, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA,
    Matrix.mul_one, smul_smul, h, one_smul]

theorem continuous_adjMap : Continuous (adjMap S σ) :=
  continuous_smul_mx _ (f := fun y : Mx D S.rank σ => (adj y * gA S : Mx D σ S.rank))
    (continuous_adj.matrix_mul continuous_const)

theorem continuous_adjInv : Continuous (adjInv S σ) :=
  continuous_smul_mx _ (f := fun η : Mx D σ S.rank => (giA S * adj η : Mx D S.rank σ))
    (continuous_const.matrix_mul continuous_adj)

theorem adjMap_fin {y : Mx D S.rank σ} (h : y.map (infPart D) = 0) : (adjMap S σ y).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.zero_mul])

theorem adjInv_fin {η : Mx D σ S.rank} (h : η.map (infPart D) = 0) : (adjInv S σ η).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.mul_zero])

theorem finLat_comap {B : AddSubgroup (Mx D σ S.rank)} (hB : FinLat B) : FinLat (B.comap (adjMap S σ)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← adjInv_adjMap S σ a]
    exact (GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjInv_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hB.fin _ ha)))
  · have e : ((B.comap (adjMap S σ) : AddSubgroup _) : Set (Mx D S.rank σ)) = adjInv S σ '' (B : Set _) := by
      ext a
      constructor
      · intro ha
        exact ⟨_, ha, adjInv_adjMap S σ a⟩
      · rintro ⟨η, hη, rfl⟩
        show adjMap S σ (adjInv S σ η) ∈ B
        rw [adjMap_adjInv]
        exact hη
    rw [e]
    exact hB.cpt.image (continuous_adjInv S σ)
  · obtain ⟨U, hU, h0, hUB⟩ := hB.opn
    refine ⟨adjMap S σ ⁻¹' U, hU.preimage (continuous_adjMap S σ), by rw [Set.mem_preimage, map_zero]; exact h0,
      fun a ha hf => ?_⟩
    exact hUB _ ha ((GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjMap_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 hf)))

theorem exists_bump_adj : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  intro D V₀ W W₀ σ dW B₂ hB y
  obtain ⟨b, hb, hby, -, hs, hp⟩ := exists_bump_le y (B₂.comap (adjMap V₀ σ)) (finLat_comap V₀ σ hB) Set.univ Filter.univ_mem
  refine ⟨fun z => (b z : ℂ), hb, by simp [hby], fun η hη c hc z => ?_, fun z hz => ?_⟩
  · have h1 : dW.pY * (dW.jY * adjMap V₀ σ c) = dW.pY * (dW.jY * η) := congrArg (fun w : WO V₀ W => dW.pY * (show Mx D W.rank V₀.rank from w)) hc
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dW.pY_jY, Matrix.one_mul, Matrix.one_mul] at h1
    have h2 : c ∈ B₂.comap (adjMap V₀ σ) := by
      rw [AddSubgroup.mem_comap, h1]; exact hη
    beta_reduce
    rw [hp c h2 z]
  · obtain ⟨r, hr, -, hz'⟩ := hs z (fun h => hz (by simp [h]))
    exact ⟨r, hr, _, hz', rfl⟩

end GlobalTheory.AscFinBumpAdj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinSupp

theorem eq_zero_of_parts {D : D7} {m n : ℕ} (z : Mx D m n) (h1 : z.map (infPart D) = 0) (h2 : z.map (finPart D) = 0) : z = 0 := by
  apply (GlobalTheory.AscFinInhab.coordH D m n).injective
  rw [GlobalTheory.AscFinInhab.coordH_apply, GlobalTheory.AscFinInhab.coordH_apply, (GlobalTheory.AscFinInhab.RCh_eq_zero_iff z).2 h1,
    (GlobalTheory.AscFinInhab.FCh_eq_zero_iff z).2 h2, map_zero, map_zero]

theorem smul_eInf_eq_zero {D : D7} {m n : ℕ} (a : Mx D m n) (h : a.map (infPart D) = 0) :
    GlobalTheory.FinTranslate.eInf D • a = 0 := by
  apply eq_zero_of_parts
  · ext i j
    have h0 : infPart D (a i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]
  · ext i j
    exact GlobalTheory.ThetaClosed.finPart_eInf_smul (a i j)

theorem smul_one_sub_eInf_eq_zero {D : D7} {m n : ℕ} (r : Mx D m n) (h : r.map (finPart D) = 0) :
    (1 - GlobalTheory.FinTranslate.eInf D) • r = 0 := by
  apply eq_zero_of_parts
  · ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (r i j)
  · ext i j
    have h0 : finPart D (r i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]

theorem upper_of_UX {D : D7} {ρ : ℕ} (u : UX D ρ) : ∀ i j, j ≤ i → ((u.1.1 : Mx D ρ ρ) - 1) i j = 0 := by
  have hU : (u.1 : GL (Fin ρ) (AE D)) ∈ GlobalTheory.UniIndexPrime.uniSub ρ (AE D) := u.2
  rw [GlobalTheory.UniIndexPrime.mem_uniSub] at hU
  obtain ⟨h1, h2⟩ := hU
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · have e1 : (u.1.1 : Mx D ρ ρ) i j = 0 := h1 i j h
    have e2 : (1 : Mx D ρ ρ) i j = 0 := Matrix.one_apply_ne (ne_of_gt h)
    rw [Matrix.sub_apply, e1, e2, sub_zero]
  · subst h
    have e1 : (u.1.1 : Mx D ρ ρ) j j = 1 := h2 j
    rw [Matrix.sub_apply, e1, Matrix.one_apply_eq, sub_self]

theorem split_parts {D : D7} {m ρ : ℕ} (x : Mx D m ρ) (N : Mx D ρ ρ) (r a : Mx D m ρ) (hxN : x ⬝ N = r + a)
    (hr : r.map (finPart D) = 0) (ha : a.map (infPart D) = 0) :
    x ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • N) = a ∧ x ⬝ (GlobalTheory.FinTranslate.eInf D • N) = r := by
  have hea := smul_eInf_eq_zero a ha
  have her := smul_one_sub_eInf_eq_zero r hr
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, hxN, smul_add, her, zero_add, sub_smul, one_smul, hea, sub_zero]
  · rw [Matrix.mul_smul, hxN, smul_add, hea, add_zero]
    have h := her
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h.symm

theorem main_part {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (u : UX D ρ) (N : Mx D ρ ρ) (hN : (u.1.1 : Mx D ρ ρ) = 1 + N)
    (h1 : psiE ψ (upSum ((1 - GlobalTheory.FinTranslate.eInf D) • N)) = 1) :
    psiUni ψ u.1 = psiE ψ (upSum (GlobalTheory.FinTranslate.eInf D • N)) := by
  have hsplit : N = GlobalTheory.FinTranslate.eInf D • N + (1 - GlobalTheory.FinTranslate.eInf D) • N := by
    rw [sub_smul, one_smul, add_sub_cancel]
  show psiE ψ (upSum u.1.1) = _
  rw [hN, GlobalTheory.AscFinInhab.upSum_add', GlobalTheory.AscFinInhab.upSum_one', zero_add, hsplit,
    GlobalTheory.AscFinInhab.upSum_add', psiE_add, h1, mul_one, ← hsplit]

theorem charOnSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (L : Matrix (Fin ρ) (Fin W.rank) D.host.E), L * x₀ = 1 → p.Is dV dW (rat x₀) ψ → ∀ (u : UX D ρ) (r : Mx D W.rank ρ), r.map (finPart D) = 0 → rat x₀ ⬝ u.1.1 - (rat x₀ + r) ∈ p.A₁ → psiUni ψ u.1 = psiE ψ (upSum (rat L ⬝ r)) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr ha
  have haInf : (rat x₀ ⬝ u.1.1 - (rat x₀ + r)).map (infPart D) = 0 :=
    (GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hp.a₁.fin _ ha)
  have hxN : rat x₀ ⬝ ((u.1.1 : Mx D ρ ρ) - 1) = r + (rat x₀ ⬝ u.1.1 - (rat x₀ + r)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]; abel
  obtain ⟨h1e, he⟩ := split_parts _ _ _ _ hxN hr haInf
  have hLr : rat L ⬝ r = GlobalTheory.FinTranslate.eInf D • ((u.1.1 : Mx D ρ ρ) - 1) := by
    rw [← he, ← Matrix.mul_assoc, ← rat_mul, hL, rat_one, Matrix.one_mul]
  have hfin : MxAt (fun _ => True) ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) := by
    rw [GlobalTheory.AscFinInhab.mxAt_true_iff]
    ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have hup' : ∀ i j, j ≤ i → ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) i j = 0 := by
    intro i j hij
    rw [Matrix.smul_apply, upper_of_UX u i j hij, smul_zero]
  have hmem : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ ⬝ (rat x₀ ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1))) ∈ p.A₁ := by
    rw [inv_one, GlobalTheory.AscFinInhab.mt_one_, Matrix.one_mul, h1e]; exact ha
  have hshift := (GlobalTheory.AscFin.cond_one hp (0 : Mx D V₀.rank σ)).shift _ hfin hup' hmem
  rw [hLr]
  exact main_part ψ u _ (by rw [add_sub_cancel]) hshift

end GlobalTheory.AscFinSupp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB

variable {D : D7}

theorem hA_smul_left (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T (c • y) z = c * hA T y z := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hA_smul_right (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T y (c • z) = cA D c * hA T y z := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratV_smul' {n : ℕ} (c : D.host.E) (v : Fin n → D.host.E) : ratV (c • v) = incA D c • ratV v := by
  funext i; simp [ratV, map_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem xFB_col (F : GlobalTheory.Asc.Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (p : Fin (σ + 1)) :
    (fun k => xFB F σ h' k p) = incA D ((-D.host.xi0) ^ (p.1 + 1)) •
      ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
  obtain ⟨h2, he, -⟩ := hF.hB σ h'
  induction p using Fin.lastCases with
  | last =>
    have hc : (Fin.castLE (by omega) (Fin.last σ) : Fin (2 * σ + 2 - 1)) = ⟨σ, by omega⟩ := Fin.ext (by simp)
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_last, vecB, HypDec.j0, ← ratV_mulVec, Matrix.mulVec_mulVec,
      hF.ζ (σ + 1), Matrix.mulVec_smul, hF.zB' σ h', ratV_smul', Fin.val_last, hc]
  | cast i =>
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, rat, Matrix.map_apply, he, colsOf,
      Pi.smul_apply, smul_eq_mul, ratV, map_mul, Fin.val_castSucc]
    rfl

theorem extY_col (F : GlobalTheory.Asc.Frames G) (hF : Std F) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)) :
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
        ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
          (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) =
      incA D (star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => a' k p := by
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hq := ProjTgt.qY_mul_a (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)) (F.dJ (σ + 1) h) (by omega) h2 he

  rw [HypDec.extY_apply, ← Matrix.mulVec_mulVec, HypDec.pY, ← ratV_mulVec]
  have hv : ∀ (M : Matrix (Fin (σ + 1)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) D.host.E)
      (N : Matrix (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (Fin (2 * (σ + 1) + 1 - 1)) D.host.E) (q : Fin (2 * (σ + 1) + 1 - 1)),
      M *ᵥ (fun k => N k q) = fun r => (M * N) r q := fun M N q => by
    funext r; simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hv, hq]
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ratV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, mul_one]; ring
  · intro r _ hr
    have : ¬ ((Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev = (Fin.castLE (by omega) r).rev) := by
      intro e; apply hr; rw [Fin.rev_inj] at e; exact Fin.ext (by simpa [Fin.ext_iff] using e.symm)
    simp only [this, ite_false, mul_zero, map_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem hA_xFB_col : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)),
    hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) =
      hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
          ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
            (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  intro D _ T L _ _ sc G _ _ _ F hF σ h h' a' p
  rw [xFB_col F hF σ h' p, extY_col F hF σ h a' p, hA_smul_left, hA_smul_right, GlobalTheory.DualPairCheck.cA_incA, star_star]

end GlobalTheory.CharXFB
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 → (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  first | exact @GlobalTheory.idLat_isSelfDualC | exact GlobalTheory.idLat_isSelfDualC | (intros; apply GlobalTheory.idLat_isSelfDualC <;> assumption)
end
