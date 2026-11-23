module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem roinf_eq_nocol {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (ρ : (Y.cs u).Cl)
    (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (hl : t.lam = (Y.cs u).lamOf ρ)
    (hl' : t.lam' = (Y.cs u).lamOf ρ) (hγ : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))) :
    ROinf t = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
  ext y
  unfold ROinf ROset Formalism.L2.SG.TermOp.KExpCut.NOcol
  rw [hl, hl']
  constructor
  · rintro ⟨x, n, hx, hy, hn, -⟩
    exact ⟨x, n, hx, hy, hn⟩
  · rintro ⟨x, n, hx, hy, hn⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    let H := NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
    exact H.mul_mem (H.mul_mem (H.inv_mem hγ) hn) hγ

theorem idMeetVolC_of (hK : IdMeetKeyC) (hV : VolColC) : IdMeetVolC := by
  intro D X Y u hN hF ρ t ht hm
  obtain ⟨-, hlin⟩ := hK D X Y u hN ρ ρ t ht hm
  have hR := roinf_eq_nocol Y ρ t hm.1.symm hm.2.1.symm hlin
  have hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω := hF t
  unfold FundOf
  rw [dite_eq_left hex]
  apply hV D X Y u ρ
  rw [← hR]
  exact hex.choose_spec

end Formalism.L2.SG.Pf.IdMeet
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ker_mat {E : Type*} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ (k : ℕ) (B : Matrix (Fin k) (Fin n) E), ∀ w, B *ᵥ w = 0 ↔ w ∈ W := by
  classical
  let b := Module.finBasis E ((Fin n → E) ⧸ W)
  refine ⟨Module.finrank E ((Fin n → E) ⧸ W), Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1)),
    fun w => ?_⟩
  have key : ∀ i, ((Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1))) *ᵥ w) i =
      b.coord i (W.mkQ w) := by
    intro i
    conv_rhs => rw [show w = ∑ j, w j • Pi.single j 1 by
      funext x; simp [Finset.sum_apply, Pi.single_apply]]

    simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  constructor
  · intro h
    rw [← Submodule.Quotient.mk_eq_zero]
    apply b.repr.injective
    ext i
    have e := congrFun h i
    rw [key] at e
    simpa using e
  · intro hw
    funext i
    rw [key]
    simp [(Submodule.Quotient.mk_eq_zero W).2 hw]

theorem rv_desc {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (T : Set (Fin X.B.I.n → X.B.I.E))
    (w : Fin X.B.I.n → X.B.I.E) (h : rv X.B.I v w ∈ Submodule.span ℂ (rv X.B.I v '' T)) :
    w ∈ Submodule.span X.B.I.E T := by
  classical
  obtain ⟨k, B, hB⟩ := exists_ker_mat (Submodule.span X.B.I.E T)
  rw [← hB w]
  have hφ : ∀ y : Fin X.B.I.n → X.B.I.E,
      (B.map (X.B.I.φ v)) *ᵥ (fun i => X.B.I.φ v (y i)) = fun i => X.B.I.φ v ((B *ᵥ y) i) := by
    intro y
    funext i

    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hrv : ∀ y, (fun i => X.B.I.φ v (y i)) = X.B.I.P v *ᵥ rv X.B.I v y := by
    intro y
    rw [rv, Matrix.mulVec_mulVec, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mulVec]
  let M : (Fin X.B.I.n → ℂ) →ₗ[ℂ] (Fin k → ℂ) := Matrix.mulVecLin (B.map (X.B.I.φ v) * X.B.I.P v)
  have hM : ∀ y, M (rv X.B.I v y) = fun i => X.B.I.φ v ((B *ᵥ y) i) := by
    intro y
    simp only [M, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← hrv, hφ]
  have hT : ∀ t ∈ T, M (rv X.B.I v t) = 0 := by
    intro t ht
    rw [hM, (hB t).2 (Submodule.subset_span ht)]
    funext i
    simp
  have hle : Submodule.span ℂ (rv X.B.I v '' T) ≤ LinearMap.ker M := by
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hT t ht
  have hw0 : M (rv X.B.I v w) = 0 := hle h
  rw [hM] at hw0
  funext i
  have e := congrFun hw0 i
  exact (map_eq_zero_iff _ (X.B.I.φ v).injective).1 e

def toVHom {D : D7} (X : HidaSetting D) : (Fin X.B.I.n → X.B.I.E) →+ (VS D).V where
  toFun := toV X
  map_zero' := by
    have h := toV_add X 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := toV_add X

theorem toV_span {D : D7} (X : HidaSetting D) {S : Set (Fin D.R.rS)} {w : Fin X.B.I.n → X.B.I.E}
    (hw : w ∈ Submodule.span X.B.I.E (X.eR '' S)) : toV X w ∈ Submodule.span D.host.E (X.eX '' S) := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    show toV X (X.crd (X.eX a)) ∈ _
    rw [toV_crd]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    rw [show toV X 0 = 0 from (toVHom X).map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [toV_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [toV_smul]
    exact Submodule.smul_mem _ _ hx

theorem nilradical_rational_lattice : NRatLam := by
  intro D X Y u ρ ν hKL hν h1 _ hK2
  obtain ⟨γ, hγU, hγinf, hγfin⟩ := hν

  have hrvg : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E),
      rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) =
        uMat (ν.1 v) *ᵥ rv X.B.I v y := by
    intro v y
    rw [hγinf v, rv, rv]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i

    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hsub : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E),
      (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v y =
        rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y - y) := by
    intro v y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hrvg]
    exact (map_sub (Formalism.L2.SG.Pf.Level.rvHom X v) _ _).symm

  have hdesc : ∀ (S : Set (Fin D.R.rS)) (x : (VS D).V),
      (∀ v, (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v (X.crd x) ∈
        Submodule.span ℂ ((fun a => rv X.B.I v (X.eR a)) '' S)) →
      matEC X γ x - x ∈ Submodule.span D.host.E (X.eX '' S) := by
    intro S x hx
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have h := hx v
    rw [hsub, ← Set.image_image (fun w => rv X.B.I v w) X.eR S] at h
    have hw := rv_desc X v _ _ h
    have e : matEC X γ x - x =
        toV X ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd x - X.crd x) := by
      rw [← matE_crdC X γ x, ← crd_sub', toV_crd]
    rw [e]
    exact toV_span X hw
  show ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ ν.1 = x.1 ∧
    n ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
  refine ⟨ν, matEC X γ, ⟨γ, hγU, hγinf, hγfin, fun y => matE_crdC X γ y⟩, rfl, ?_⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [isAutLam_iff]
    refine ⟨fun x y => matE_isomC X γ hγU x y, fun y => ?_⟩
    rw [(Y.cs u).lat_eq ρ (matEC X γ y), (Y.cs u).lat_eq ρ y, matE_inclC, ← hγfin, Matrix.mulVec_mulVec]
    have hk : ∀ w, w ∈ X.B.I.Lf ↔ X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 *
        (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *ᵥ w ∈ X.B.I.Lf := hKL.2.1 _ hK2
    have e : X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat ν.2 =
        X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
          X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ := by
      simp [AutInst.fmat, Matrix.mul_assoc]
    rw [e, ← Matrix.mulVec_mulVec]
    exact (hk _).symm
  · intro j x hx
    change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
    change matEC X γ x - x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
    rw [X.Fu_e u] at hx ⊢
    let Lm : (VS D).V →ₗ[D.host.E] (VS D).V :=
      (matEC X γ : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id
    have hL : ∀ y, Lm y = matEC X γ y - y := fun y => rfl
    rw [← hL]
    refine (Submodule.span_le (p := (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm)).2 ?_ hx
    rintro _ ⟨i, hi, rfl⟩
    show X.eX i ∈ (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm
    rw [Submodule.mem_comap, hL]
    refine Submodule.span_mono (Set.image_mono fun b hb => ?_)
      (hdesc {b | b.1 < i.1} (X.eX i) fun v => (h1 v).1.1 i)
    simp only [Set.mem_setOf_eq] at hb hi ⊢
    omega
  · intro x hx
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ a, (VS D).hT (X.eX a) x = 0 := by
      intro a
      refine hx (X.eX a) ?_
      change X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e u]
      exact Submodule.subset_span ⟨a, rfl⟩
    change matEC X γ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
    rw [X.Fu_e u]
    have hsp : Submodule.span D.host.E (X.eX '' {b : Fin D.R.rS | b.1 < D.R.rS}) =
        Submodule.span D.host.E (Set.range X.eX) := by
      congr 1
      ext y
      simp
    rw [← hsp]
    refine hdesc _ x fun v => (h1 v).2 _ fun a => ?_
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd x)) = 0
    rw [hJ_crd, hx' a, map_zero]

end Formalism.L2.SG.Pf.SlabCoverPf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem muN_preimage (a : X.B.I.Ginf) (ha : a ∈ X.NinfU u) {A : Set X.B.I.Ginf} (hA : MeasurableSet A) :
    X.muN u {y | a * y ∈ A} = X.muN u A := by
  have h := Measure.map_apply (μ := X.muN u) (measurable_const_mul a) hA
  rw [(X.muN_haar u).2.2.2 a ha] at h
  exact h.symm

end Gen

theorem fundMeasEqC_holds : FundMeasEqC := by
  intro D X u Γ Ω Ω' hsub hc hΩ hΩ'
  have hcs : (Γ : Set X.B.I.Ginf).Countable := Set.countable_coe_iff.1 hc
  have hun : ∀ (P : Set X.B.I.Ginf), IsSFund X.B.I Γ P → ∀ n, ∀ a ∈ (Γ : Set X.B.I.Ginf), ∀ a' ∈ (Γ : Set X.B.I.Ginf),
      a * n ∈ P → a' * n ∈ P → a = a' := by
    intro P hP n a ha a' ha' h1 h2
    have h3 : (a' * a⁻¹) * (a * n) ∈ P := by simpa [mul_assoc] using h2
    have := hP.2.2 _ h1 _ (Γ.mul_mem ha' (Γ.inv_mem ha)) h3
    exact (mul_inv_eq_one.1 this).symm
  rw [Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω Ω' (X.muN u) hcs hΩ.1 hΩ'.1 hΩ'.2.1
      (hun Ω' hΩ'),
    Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω' Ω (X.muN u) hcs hΩ'.1 hΩ.1 hΩ.2.1 (hun Ω hΩ)]
  have hterm : ∀ a : (Γ : Set X.B.I.Ginf),
      X.muN u (Ω ∩ {n | (a : X.B.I.Ginf) * n ∈ Ω'}) =
        X.muN u (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) := by
    intro a
    have hS : MeasurableSet (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) :=
      hΩ'.1.inter ((measurable_const_mul _) hΩ.1)
    rw [← muN_preimage X u (a : X.B.I.Ginf) (hsub a.2) hS]
    congr 1
    ext n
    simp [and_comm]
  simp_rw [hterm]
  let e : (Γ : Set X.B.I.Ginf) ≃ (Γ : Set X.B.I.Ginf) :=
    ⟨fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩, fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩,
      fun a => by simp, fun a => by simp⟩
  exact e.tsum_eq (fun b : (Γ : Set X.B.I.Ginf) => X.muN u (Ω' ∩ {m | (b : X.B.I.Ginf) * m ∈ Ω}))

theorem indexVolC_holds : IndexVolC := by
  intro D X u Γ Γ' Ω hle hsub hc hk hΩ
  set H : Subgroup Γ := Γ'.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hk⟩
  have : Finite (Γ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let r : Γ ⧸ H → Γ := fun q => Quotient.out q
  have hr : ∀ q, ((r q : Γ) : Γ ⧸ H) = q := fun q => Quotient.out_eq q
  let A : Γ ⧸ H → Set X.B.I.Ginf := fun q => {y | ((r q : Γ) : X.B.I.Ginf) * y ∈ Ω}
  have hA : ∀ q, MeasurableSet (A q) := fun q => (measurable_const_mul _) hΩ.1

  have key : ∀ (a b : Γ) (y : X.B.I.Ginf), (a : X.B.I.Ginf) * y ∈ Ω → (b : X.B.I.Ginf) * y ∈ Ω → a = b := by
    intro a b y ha hb
    have h3 : ((b : X.B.I.Ginf) * (a : X.B.I.Ginf)⁻¹) * ((a : X.B.I.Ginf) * y) ∈ Ω := by
      simpa [mul_assoc] using hb
    have := hΩ.2.2 _ ha _ (Γ.mul_mem b.2 (Γ.inv_mem a.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  refine ⟨⋃ q, A q, ⟨MeasurableSet.iUnion hA, ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
    let sΓ : Γ := ⟨s, hs⟩
    have hq : (r (sΓ : Γ ⧸ H))⁻¹ * sΓ ∈ H := QuotientGroup.eq.1 (hr _)
    refine ⟨(((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf), Subgroup.mem_subgroupOf.1 hq, ?_⟩
    refine Set.mem_iUnion.2 ⟨(sΓ : Γ ⧸ H), ?_⟩
    show ((r (sΓ : Γ ⧸ H) : Γ) : X.B.I.Ginf) * ((((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf) * x) ∈ Ω
    simpa [mul_assoc, sΓ] using hsx
  · intro x hx s hs hsx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hsx
    let sΓ : Γ := ⟨s, hle hs⟩
    have hp0 : ((r p : Γ) : X.B.I.Ginf) * (s * x) ∈ Ω := hp
    have hp' : ((r p * sΓ : Γ) : X.B.I.Ginf) * x ∈ Ω := by
      simpa [mul_assoc, sΓ] using hp0
    have e1 : r p * sΓ = r q := key _ _ x hp' hq
    have e2 : sΓ = (r p)⁻¹ * r q := by rw [← e1]; group
    have hmem : (r p)⁻¹ * r q ∈ H := by
      rw [← e2]; exact Subgroup.mem_subgroupOf.2 hs
    have hpq : p = q := by
      have := QuotientGroup.eq.2 hmem
      rw [hr, hr] at this
      exact this
    subst hpq
    have : sΓ = 1 := by rw [e2]; group
    exact congrArg Subtype.val this
  · have hdisj : Pairwise (Function.onFun Disjoint A) := by
      intro p q hpq
      refine Set.disjoint_left.2 fun y hy1 hy2 => hpq ?_
      have := key _ _ y hy1 hy2
      rw [← hr p, ← hr q, this]
    rw [measure_iUnion hdisj hA, tsum_fintype]
    have hterm : ∀ q, X.muN u (A q) = X.muN u Ω := fun q =>
      muN_preimage X u _ (hsub (r q).2) hΩ.1
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Formalism.L2.SG.Pf.IdMeet
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RegroupPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ColUniqPf

theorem colUniq_of {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')
    (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs') : ColUniq cs cs' := by
  intro ρ ρ₁ ρ₂ γ₁ γ₂ h₁ h₂ hs
  have hB : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') ∈ X.K2 := by
    have e : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') =
        (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₁ : X.B.I.Gf) γ₁)⁻¹ *
          kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₂ : X.B.I.Gf) γ₂ := by
      simp only [kOf, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.2.1 _ h₁.2) _ h₂.2
  obtain ⟨hsI, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hs
  obtain ⟨ν, η, hνη, -, -, hνf, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hs).1 hsI hsf
  have hs2 : (γ₁⁻¹ * γ₂).2 = ν.2 * η.2 := by rw [hνη, Prod.snd_mul]
  have hio : ((iotaF X u' ⟨η, hη⟩ : Hfin X u') : X.B.I.Gf) = η.2 := rfl
  have hn := ((Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u') (cs'.h ρ₁)⁻¹ ν.2 hνf).1
  have hlev := Formalism.L2.SG.Pf.levelDec_holds X u' _ hn
    ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂) (by
      have e : (X.xu u')⁻¹ * ((((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf) * ν.2 *
          (((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf)⁻¹ *
          (((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂ : Hfin X u') : X.B.I.Gf)) * X.xu u' =
          ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') := by
        rw [hs2]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hio]
        group
      rw [e]
      exact hB)
  obtain ⟨ρ0, -, huniq⟩ := hR (cs'.h ρ₂)
  have e1 := huniq ρ₂ ⟨1, 1, by simp⟩
  have e2 := huniq ρ₁ ⟨(⟨η, hη⟩ : Gam X u')⁻¹,
    ⟨(cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂, hlev.1⟩, by
      show cs'.h ρ₂ = iotaF X u' (⟨η, hη⟩ : Gam X u')⁻¹ * cs'.h ρ₁ *
        ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂)
      rw [map_inv]
      group⟩
  exact e2.trans e1.symm

end ColUniqPf

theorem column_uniqueness : ColUniqC := by
  intro D X Y u u' _
  exact ColUniqPf.colUniq_of (Y.cs u) (Y.cs u') Y.hK (Y.colReps u')

end Formalism.L2.SG.Pf.RegroupPf
end
end

section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

theorem phase_well_defined_all_words : PhWellDefC := fun _ X _ u _ => Formalism.L2.SG.Pf.phWellDef_holds X u

end Formalism.L2.SG.Pf.RegroupPf
end
