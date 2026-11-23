module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle436
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfSplit

def kIdx (k : ℕ) (A : Type) [AddCommGroup A] : ℕ := (nsmulAddMonoidHom k : A →+ A).range.index

theorem relIndex_eq_kIdx {G : Type} [AddCommGroup G] (H : AddSubgroup G) (k : ℕ) :
    (AddSubgroup.map (nsmulAddMonoidHom k) H).relIndex H = kIdx k H := by
  unfold kIdx AddSubgroup.relIndex
  congr 1
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩

theorem kIdx_congr {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (k : ℕ) :
    kIdx k A = kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_map_equiv _ e]
  congr 1
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨k • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩

theorem kIdx_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] (k : ℕ) :
    kIdx k (A × B) = kIdx k A * kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [AddSubgroup.mem_prod, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    exact ⟨⟨x, congrArg Prod.fst hxy⟩, ⟨y, congrArg Prod.snd hxy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), Prod.ext hx hy⟩

theorem kIdx_subsingleton {A : Type} [AddCommGroup A] [Subsingleton A] (k : ℕ) : kIdx k A = 1 :=
  AddSubgroup.index_eq_one.2 (eq_top_iff.2 fun x _ => ⟨0, Subsingleton.elim _ _⟩)

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

section split

variable (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M) {e f : R}

include hmem in
theorem smul_mem_inf (he : e * e = e) (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) {u : M} (hu : u ∈ Λ) : e • u ∈ Λ ⊓ h e :=
  AddSubgroup.mem_inf.2 ⟨hΛe u hu, (hmem _ _).2 (by rw [smul_smul, he])⟩

def splitEquiv (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) (hΛf : ∀ u ∈ Λ, f • u ∈ Λ) :
    ↥(Λ ⊓ h (e + f)) ≃+ ↥(Λ ⊓ h e) × ↥(Λ ⊓ h f) where
  toFun u := (⟨e • u.1, smul_mem_inf h hmem Λ he hΛe (AddSubgroup.mem_inf.1 u.2).1⟩,
    ⟨f • u.1, smul_mem_inf h hmem Λ hf hΛf (AddSubgroup.mem_inf.1 u.2).1⟩)
  invFun p := ⟨p.1.1 + p.2.1, AddSubgroup.mem_inf.2 ⟨add_mem (AddSubgroup.mem_inf.1 p.1.2).1
      (AddSubgroup.mem_inf.1 p.2.2).1, (hmem _ _).2 (by
        have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
        have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
        have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
        have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
        rw [smul_add, add_smul, add_smul, h1, h2, h3, h4, add_zero, zero_add])⟩⟩
  left_inv u := by
    apply Subtype.ext
    change e • (u : M) + f • (u : M) = u
    rw [← add_smul]
    exact (hmem _ _).1 (AddSubgroup.mem_inf.1 u.2).2
  right_inv p := by
    have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
    have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
    have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
    have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((p.1 : M) + p.2) = p.1
      rw [smul_add, h1, h4, add_zero]
    · change f • ((p.1 : M) + p.2) = p.2
      rw [smul_add, h2, h3, zero_add]
  map_add' u v := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((u : M) + v) = e • (u : M) + e • (v : M)
      exact smul_add _ _ _
    · change f • ((u : M) + v) = f • (u : M) + f • (v : M)
      exact smul_add _ _ _

end split

theorem sum_idem {ι : Type} (s : Finset ι) (cs : ι → R) (hid : ∀ i ∈ s, cs i * cs i = cs i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji)) (fun h => absurd hi h), hid i hi]

theorem kIdx_half_sum (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M)
    {ι : Type} (P : Finset ι) (cs : ι → R) (hid : ∀ i ∈ P, cs i * cs i = cs i)
    (horth : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) (hΛ : ∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) (k : ℕ) :
    kIdx k ↥(Λ ⊓ h (∑ i ∈ P, cs i)) = ∏ i ∈ P, kIdx k ↥(Λ ⊓ h (cs i)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    haveI : Subsingleton ↥(Λ ⊓ h 0) := ⟨fun a b => by
      have ha := (hmem _ _).1 (AddSubgroup.mem_inf.1 a.2).2
      have hb := (hmem _ _).1 (AddSubgroup.mem_inf.1 b.2).2
      rw [zero_smul] at ha hb
      exact Subtype.ext (ha.symm.trans hb)⟩
    exact kIdx_subsingleton k
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hne : ∀ j ∈ s, a ≠ j := fun j hj haj => ha (haj ▸ hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj))
        (fun i hi => hΛ i (hs i hi)),
      kIdx_congr (splitEquiv h hmem Λ (hid a ha')
        (sum_idem s cs (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj)))
        (by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun j hj => horth a ha' j (hs j hj) (hne j hj))
        (by rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun j hj => horth j (hs j hj) a ha' (hne j hj).symm)
        (hΛ a ha')
        (fun u hu => by rw [Finset.sum_smul]; exact AddSubgroup.sum_mem _ fun i hi => hΛ i (hs i hi) u hu)),
      kIdx_prod]

theorem relIndex_nsmul_half_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  intro D S T Λ ι P cs hid horth hΛ k
  rw [relIndex_eq_kIdx]
  simp only [relIndex_eq_kIdx]
  exact kIdx_half_sum (GlobalTheory.PlaceModel.half S T) (fun e u => GlobalTheory.PlaceModel.mem_half S T) Λ P cs hid horth hΛ k

end GlobalTheory.HalfSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FourierRealPart

variable {D : D7}

theorem exists_section (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ s : (D.what₂.Tau → ℂ) → AE D, Continuous s ∧ (∀ w, finPart D (s w) = 0) ∧
      (∀ w τ, θ τ (infPart D (s w)) = w τ) ∧ (∀ a, infPart D (s fun τ => θ τ (infPart D a)) = infPart D a) ∧
      ∀ τ, Continuous fun a : AE D => θ τ (infPart D a) := by
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig D.what₂.Tau
    (tauE D) θ (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D) hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ a : AE D, (e1 a).1 = infPart D a := fun a => (he1 a).1
  have hfin : ∀ a : AE D, (e1 a).2 = finPart D a := fun a => (he1 a).2
  refine ⟨fun w => e1.symm (e.symm w, 0), hc1'.comp (hc'.prodMk continuous_const), fun w => ?_, fun w τ => ?_,
    fun a => ?_, fun τ => ?_⟩
  · rw [← hfin, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply]
    apply e.injective
    funext τ
    rw [RingEquiv.apply_symm_apply, he]
  · have h : (fun a : AE D => θ τ (infPart D a)) = fun a => e (e1 a).1 τ := by
      funext a
      rw [he, hinf]
    rw [h]
    exact (continuous_apply τ).comp (hc.comp (continuous_fst.comp hc1))

theorem dualPt_finPart {T : HSp D} {ρ : ℕ} {b : Mx D ρ T.rank} (hb : b.map (finPart D) = 0) :
    (GlobalTheory.Unf.DoubleSum.dualPt T ρ b).map (finPart D) = 0 := by
  have h : (b ⬝ giA T).map (finPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine GlobalTheory.OrientedChar.finPart_cA_eq_zero (z := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show finPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]



theorem psi_dualPt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (z : Mx D W.rank ρ) {b : Mx D ρ W.rank}
    (hb : b.map (finPart D) = 0) :
    ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ τ, ((2 * (∑ i, ∑ j,
        θ τ (infPart D (z i j)) * θ τ (infPart D (b j i))).re : ℝ) : ℂ)) := by
  rw [GlobalTheory.Unf.DoubleSum.symplO_dualPt]
  have hfin : finPart D (z * b).trace = 0 := GlobalTheory.PhaseReal.finPart_trace z b hb
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  have h1 : ψ (Algebra.trace (AF D.host.F) (AE D) (z * b).trace) =
      psiInf D.host.F ψ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) (z * b).trace)) := congrArg ψ hT
  rw [h1, hψ.2.2 θ hθ]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [GlobalTheory.PhaseReal.theta_trace θ hθ τ]
  congr 3

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]

theorem linear_expand {K : Type} [Fintype K] [DecidableEq K] (l : (K → ℂ) →L[ℝ] ℝ) (Z : K → ℂ) :
    l Z = ∑ k, ((Z k).re * l (Pi.single k 1) + (Z k).im * l (Pi.single k Complex.I)) := by
  conv_lhs => rw [← Finset.univ_sum_single Z]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : Pi.single k (Z k) = (Z k).re • (Pi.single k (1 : ℂ) : K → ℂ) + (Z k).im • (Pi.single k Complex.I : K → ℂ) := by
    ext k'
    by_cases h : k' = k
    · subst h
      simp [Complex.ext_iff]
    · simp [h]
  rw [e, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.FourierRealPart


open GlobalTheory.FourierRealPart in
theorem GlobalTheory.FourierRealPart.integral_preimage_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  intro D ψ hψ V V₀ W ρ d Y _ m F hF x hx hc S hS hsat
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨s, hsc, hsf, hsθ, hsinf, hcθ⟩ := exists_section θ hθ
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  classical
  let P : Mx D W.rank ρ → (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) := fun z k => θ k.2.2 (infPart D (z k.1 k.2.1))
  let sec : (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) → Mx D W.rank ρ := fun w i j => s fun τ => w (i, j, τ)
  have hP : Continuous P :=
    continuous_pi fun k => (hcθ k.2.2).comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  have hsec : Continuous sec :=
    continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun τ => continuous_apply _)
  have hmem : ∀ z, z ∈ S ↔ sec (P z) ∈ S := fun z => hsat _ _ (by
    funext i j
    exact (hsinf (z i j)).symm)
  have hpre : x ⁻¹' S = (P ∘ x) ⁻¹' (sec ⁻¹' S) := by
    ext y
    exact hmem (x y)
  rw [hpre]
  refine GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero Y m F hF _ (P ∘ x) (hP.measurable.comp hx) ?_ _ (hsec.measurable hS)
  intro l
  let B : Fin W.rank × Fin ρ × D.what₂.Tau → ℂ := fun k =>
    ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) * ((l (Pi.single k 1) : ℂ) - (l (Pi.single k Complex.I) : ℂ) * Complex.I)
  let b : Mx D ρ W.rank := fun j i => s fun τ => B (i, j, τ)
  have hb : b.map (finPart D) = 0 := by
    funext j i
    exact hsf _
  have key := hc (GlobalTheory.Unf.DoubleSum.dualPt W ρ b) (dualPt_finPart hb)
  have hpt : ∀ z : Mx D W.rank ρ, Complex.exp ((l (P z) : ℂ) * Complex.I) =
      ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) := by
    intro z
    rw [psi_dualPt hψ θ hθ d z hb]
    congr 1
    have hbθ : ∀ i j τ, θ τ (infPart D (b j i)) = B (i, j, τ) := fun i j τ => hsθ _ τ
    simp only [hbθ]
    have hterm : ∀ k, (P z k).re * l (Pi.single k 1) + (P z k).im * l (Pi.single k Complex.I) =
        -(4 * Real.pi) * (P z k * B k).re := by
      intro k
      have hπ := Real.pi_ne_zero
      simp only [B, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.sub_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    have h1 : l (P z) = ∑ i, ∑ j, ∑ τ, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [linear_expand l (P z), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => hterm _
    have h2 : -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re =
        ∑ τ, ∑ i, ∑ j, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      simp only [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hr : l (P z) = -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [h1, h2]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    rw [hr]
    push_cast
    ring
  simp only [Function.comp_apply, hpt]
  exact key
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end GlobalTheory.BottomRealAct
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.ChartPlaces

variable {D : D7}

theorem mul_eq_zero_of_ne {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) {Q Q' : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (hQ' : Q' ∈ P)
    (hne : Q ≠ Q') : es Q * es Q' = 0 := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]

theorem chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  intro D e P es hes hsum hec v hπ
  have hsplit : ∀ Q ∈ P, Formalism.L2.Theta.IsSplitIdem D (es Q) := fun Q hQ => (hes Q hQ).1
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → es Q * es Q' = 0 :=
    fun Q hQ Q' hQ' hne => mul_eq_zero_of_ne hes hQ hQ' (Ne.symm hne)

  have habs : ∀ Q ∈ P, es Q * e = es Q := fun Q hQ => by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth hsplit horth hQ

  have hcross : ∀ Q ∈ P, ∀ Q' ∈ P, es Q' * cA D (es Q) = 0 := fun Q hQ Q' hQ' => by
    have h1 : cA D (es Q) * cA D e = cA D (es Q) := by rw [← map_mul, habs Q hQ]
    calc es Q' * cA D (es Q) = (es Q' * e) * (cA D e * cA D (es Q)) := by
          rw [habs Q' hQ', mul_comm (cA D e), h1]
      _ = es Q' * (e * cA D e) * cA D (es Q) := by ring
      _ = 0 := by rw [hec, mul_zero, zero_mul]
  intro Q Q' hvv
  by_contra hne
  have hne' : (Q : Formalism.L2.DIV.Pl D.host.E) ≠ Q' := fun h => hne (Subtype.ext h)
  obtain ⟨π, hπc⟩ := hπ Q
  obtain ⟨π', hπc'⟩ := hπ Q'
  have hs' : Formalism.L2.Theta.IsSplitIdem D (cA D (es Q')) := GlobalTheory.PlaceModelSum.isSplitIdem_cA (hsplit Q' Q'.2)
  obtain ⟨hid', hort', v', ε', ⟨α', rfl, hα1, hα0⟩, hsum'⟩ := hs'

  have hπ'1 : π' (cA D (es Q')) = 1 := by
    have := (hπc'.2.1 (1 - cA D (es Q'))).2 (by rw [mul_sub, mul_one, hid', sub_self])
    rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this
  have hπ'0 : π' (cA D (cA D (es Q'))) = 0 := (hπc'.2.1 _).2 hort'
  have hw1 : evalV D.host.F (v Q') α' = 1 := by
    have := hπc'.2.2.1 (pairA D.host.F 0 α')
    rw [← hsum', map_add (f := _), hπ'1, hπ'0, add_zero] at this
    exact this.symm
  have hwv : v Q' = v' := by
    by_contra h
    rw [hα0 _ h] at hw1
    exact zero_ne_one hw1

  have hA : π (cA D (es Q')) = 0 := (hπc.2.1 _).2 (by
    rw [← map_mul, mul_eq_zero_of_ne hes Q.2 Q'.2 hne', map_zero])
  have hB : π (cA D (cA D (es Q'))) = 0 := (hπc.2.1 _).2 (by
    rw [cA_cA, mul_comm]; exact hcross Q Q.2 Q' Q'.2)
  have hC := hπc.2.2.1 (pairA D.host.F 0 α')
  rw [← hsum', map_add (f := _), hA, hB, add_zero] at hC
  have h0 : evalV D.host.F (v Q) α' = 0 := hC.symm
  rw [hvv.trans hwv, hα1] at h0
  exact one_ne_zero h0

end GlobalTheory.ChartPlaces
end
end
