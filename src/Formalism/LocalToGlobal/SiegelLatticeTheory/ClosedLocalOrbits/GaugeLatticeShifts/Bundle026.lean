module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNHomPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle022
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_unique {x y : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x γ)
    (hy : RatLink X y γ) : x = y := by
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  obtain ⟨N, -, k1, k2, k3⟩ := hy
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    obtain ⟨w, hw⟩ : ∃ w, X.crd w = Pi.single j 1 :=
      ⟨Formalism.L2.SG.Pf.LatDictK.vOf X (Pi.single j 1), Formalism.L2.SG.Pf.LatDictK.crd_vOf X _⟩
    have e := (h3 w).symm.trans (k3 w)
    rw [hw] at e
    have := congrFun e i
    simpa [Matrix.mulVec_single_one] using this
  have hMN' : M = N := Units.ext hMN
  subst hMN'
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1 v).trans (k1 v).symm))
  · exact Subtype.ext (Units.ext (h2.trans k2.symm))

variable {X} (TR : TypedRed X)

theorem levi_eq_one_of {a : X.B.I.Gf} (ga : Good X a)
    (hb : ∀ j, (X.B.I.fmat a - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)) : levi TR a = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR ga]
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have hI := hA_int X.B.I (hbwd i) (K_mv X.B.I ga.1.1 (hbw j))
  have hZ1 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat a - 1) *ᵥ X.bw j)) :=
    Z_pair_Mo X (hbwd i) (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b) _ (hb j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right] at hZ1
  have hZ := Z_add X.B.I X.B.g hZ1 (X.bw_dual i j)
  rw [show hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - hA X.B.I (X.bwd i) (X.bw j) +
    (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) =
    hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - if i = j then X.ew else 0 by ring] at hZ
  show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j)) = _
  rw [resT_of_mem TR v hI, res_of_Z_delta TR v hI (i = j) hZ, Pi.one_apply, Units.val_one, Matrix.one_apply]

theorem rep_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u') (p q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ')
    (hpq : GRel X u u' (X.Fu u) (X.Fu u') Λ Λ' p q) :
    ∃ (n n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (xn xn' : X.B.I.GA),
      n ∈ NLam Λ (lf D (X.Fu u)) ∧ n' ∈ NLam Λ' (lf D (X.Fu u')) ∧ RatLink X xn n ∧ RatLink X xn' n' ∧
      q.1.2 = n * p.1.2 * n' ∧ q.1.1 = xn * p.1.1 * xn' := by
  obtain ⟨n, hn, n', hn', hq⟩ := hpq
  obtain ⟨xn, hxn⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hn.1.1
  obtain ⟨xn', hxn'⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n' hn'.1.1
  refine ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, ?_⟩
  have h1 : RatLink X q.1.1 q.1.2 := q.2.1
  have h2 : RatLink X (xn * p.1.1 * xn') (n * p.1.2 * n') := ratLink_mul X (ratLink_mul X hxn p.2.1) hxn'
  rw [← hq] at h2
  exact ratLink_unique X h1 h2

end Formalism.L2.SG.Pf.AmpIota

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaRepC_holds : Formalism.L2.SG.Pf.SatGramRep.IotaRepC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', -, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, -⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, -⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have ga : Good X a := good_of_ncong X ha1.1 ⟨ha1.2.1, ha1.2.2.1⟩
  have ga' : Good X a' := good_of_ncong X ha1'.1 ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have gκ := good_of_ncong X hκK
    (adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X) hΛ hΛ' p hκK)
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group

  have hlev : ∀ (w : D.what₂.Word) (Lw : Submodule (𝓞 D.host.E) (VS D).V) (hh : Hfin X w) (m : X.B.I.GA)
      (nm : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X m nm → nm ∈ NLam Lw (lf D (X.Fu w)) →
      ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset →
      Good X (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) →
      levi Y.TR (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) = 1 := by
    intro w Lw hh m nm hm hnm hK gA
    obtain ⟨C, hC⟩ := Formalism.L2.SG.Pf.exists_goodC X w
    have hN0 := Formalism.L2.SG.Pf.nLamNfin_holds D X w Lw m nm hm hnm
    have hN1 := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X w hh⁻¹ m.2 hN0).1
    simp only [Subgroup.coe_inv, inv_inv] at hN1
    have e : ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) =
        (X.xu w)⁻¹ * ((hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf)) * X.xu w := by group
    have hK1 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) ∈ X.B.I.Kset := by
      have e2 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) =
          X.xu w * (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) * (X.xu w)⁻¹ := by group
      rw [e2]
      exact K_mul X.B.I (K_mul X.B.I (X.xu_K w) hK) (K_inv X.B.I (X.xu_K w))
    refine levi_eq_one_of Y.TR gA (fun j => ?_)
    rw [e]
    exact Formalism.L2.SG.Pf.cong_b hC hN1 hK1 j
  have hla := hlev u Λ ((Y.cs u).h ((Y.cs u).base Λ)) xn n hxn hn ha1.1 ga
  have hla' := hlev u' Λ' ((Y.cs u').h ((Y.cs u').base Λ')) xn' n' hxn' hn' ha1'.1 ga'
  show levi Y.TR (kOf X u u' hb hb' q.1.1) = levi Y.TR (kOf X u u' hb hb' p.1.1)
  rw [hk, levi_mul Y.TR (good_mul X ga gκ) ga', levi_mul Y.TR ga gκ, hla, hla', one_mul, mul_one]

theorem ampRepNC_holds : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq Ωp Ωq hΩp hΩq _
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, ha3⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, ha3'⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have hκN := adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X)
    hΛ hΛ' p hκK
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group
  have haN : NCong X a := ⟨ha1.2.1, ha1.2.2.1⟩
  have haN' : NCong X a' := ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hχ : chiN X (kOf X u u' hb hb' q.1.1) =
      X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 := by
    rw [hk, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I ha1.1 hκK) (ncong_mul X ha1.1 haN hκN) haN',
      Formalism.L2.SG.Pf.ChiNMul.chiN_mul X ha1.1 haN hκN]
    have e1 := (ha3 1 Y.hK.1).1
    have e2 := (ha3' 1 Y.hK.1).1
    rw [mul_one, Formalism.L2.SG.Pf.ChiNMul.chiN_one, mul_one] at e1 e2
    rw [e1, e2]
  have hΩq' : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (n * p.1.2 * n')) Ωq := by
    rw [← hq]; exact hΩq
  have hoo := oo_rel Formalism.L2.SG.Pf.nLamNinf_holds chiTrivialC_outright Y hΛ hΛ' p hn hn' hxn hxn' hΩp hΩq'
  have hP1 := Formalism.L2.SG.Pf.psiProd_all D X u xn (ratLink_mem X hxn)
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u _ xn n hxn hn) (Formalism.L2.SG.Pf.nLamNfin_holds D X u _ xn n hxn hn)
  have hP2 := Formalism.L2.SG.Pf.psiProd_all D X u' xn' (ratLink_mem X hxn')
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u' _ xn' n' hxn' hn') (Formalism.L2.SG.Pf.nLamNfin_holds D X u' _ xn' n' hxn' hn')
  rw [hχ, hq1]
  rw [hoo, smul_smul]
  have hc : X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 *
      (X.psiInfU u xn.1 * X.psiInfU u' xn'.1) = chiN X (kOf X u u' hb hb' p.1.1) := by
    linear_combination (chiN X (kOf X u u' hb hb' p.1.1)) *
      (X.psiInfU u xn.1 * X.psiFinU u xn.2 * hP2 + hP1)
  rw [hc]

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by simp [uMat]

theorem eN_single (i0 : Fin k) (z : ℂ) : eN (Pi.single i0 z) = ‖z‖ := by
  unfold eN
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same,
    Real.sqrt_sq (norm_nonneg _)]

theorem single_last_smul (L : Fin (r + 1)) (d : ℂ) : Pi.single L d = d • Pi.single L (1 : ℂ) := by
  funext j
  by_cases hj : j = L
  · subst hj; simp
  · simp [hj]

theorem realize (A B : Fr ε r k) (i0 : Fin k) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det)
    (σ : ℝ) (hσ2 : σ ^ 2 = (A.T)⁻¹ - B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2) :
    ∃ g : Formalism.REAL.UJ ε, ∃ y : Fin (r + 1) → Fin n → ℂ, ∃ t : Fin (r + 1) → ℂ,
      t ⬝ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) = σ ∧
      (∀ b, uMat g *ᵥ fam B.e B.z b = y b) ∧ (∀ i, i ≠ i0 → uMat g *ᵥ B.wb i = A.wb i) ∧
      (∀ a b, hJ ε (fam A.e A.z a) (y b) = Z a b) ∧
      (∀ i b, hJ ε (A.wb i) (y b) = if i = i0 then t b else 0) := by
  classical
  set L := Fin.last r with hL
  set c := Z⁻¹ *ᵥ Pi.single L 1 with hcdef
  have hZc : Z *ᵥ c = Pi.single L 1 := by rw [hcdef, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hZc
    have := congrFun hZc L
    simp at this
  obtain ⟨N, hNdef⟩ : ∃ N : ℂ, N = star c ⬝ᵥ c := ⟨_, rfl⟩
  have hN : N ≠ 0 := by rw [hNdef]; exact fun h => hc0 (dotProduct_star_self_eq_zero.1 h)
  obtain ⟨t, htdef⟩ : ∃ t : Fin (r + 1) → ℂ, t = ((σ : ℂ) / N) • star c := ⟨_, rfl⟩
  have htc : t ⬝ᵥ c = σ := by rw [htdef, smul_dotProduct, smul_eq_mul, ← hNdef, div_mul_cancel₀ _ hN]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Γ = Matrix.of fun b c' => if b = L then (if c' = L then -(B.T : ℂ) else 0) else 0 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Q = Γ + ((A.T : ℂ)⁻¹) • vecMulVec (star (Z L)) (Z L) - vecMulVec (star t) t := ⟨_, rfl⟩
  have hAstar : star ((A.T : ℂ)⁻¹) = (A.T : ℂ)⁻¹ := by rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hBstar : star (-(B.T : ℂ)) = -(B.T : ℂ) := by rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  have hQ : Qᴴ = Q := by
    ext b c'
    simp only [hQdef, hΓ, conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, of_apply,
      vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_mul', star_star, hAstar]
    by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc, hBstar] <;> ring
  have hzc : Z L ⬝ᵥ c = 1 := by
    have := congrFun hZc L
    simpa [mulVec] using this
  have hΓv : Γ *ᵥ c = Pi.single L (-(B.T : ℂ) * c L) := by
    funext b
    by_cases hb : b = L
    · subst hb; simp [hΓ, mulVec, dotProduct, Finset.sum_ite_eq']
    · simp [hΓ, mulVec, dotProduct, hb]
  have hcQ : star c ⬝ᵥ (Q *ᵥ c) = 0 := by
    rw [hQdef, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dot_vmv,
      dot_vmv, hΓv, dotProduct_single, star_dotProduct_star, star_dotProduct_star, hzc, htc, smul_eq_mul,
      star_one, mul_one, mul_one]
    have h1 : star (c L) * c L = ((‖c L‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    have h2 : star (σ : ℂ) * σ = ((σ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [h2, hσ2, Pi.star_apply, show star (c L) * (-(B.T : ℂ) * c L) = -(B.T : ℂ) * (star (c L) * c L) by ring, h1]
    push_cast
    ring
  obtain ⟨Aα, hAlast, hAeq⟩ := solveHerm Z Q hZ hQ hcQ
  set y := A.yv i0 Z Aα t with hydef
  have hgram : ∀ b c', hJ ε (y b) (y c') = hJ ε (fam B.e B.z b) (fam B.e B.z c') := by
    intro b c'
    rw [hydef, A.gram i0 Z Aα t hAlast, B.gf]
    have hq := congrFun (congrFun hAeq b) c'
    rw [Matrix.add_apply] at hq
    have hQbc : Q b c' = Γ b c' + (A.T : ℂ)⁻¹ * (star (Z L b) * Z L c') - star (t b) * t c' := by
      simp [hQdef, vecMulVec_apply]
    have hΓbc : Γ b c' = if b = L ∧ c' = L then -(B.T : ℂ) else 0 := by
      rw [hΓ, of_apply]
      by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc]
    rw [← hΓbc]
    linear_combination hq + hQbc
  let s : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim (fam B.e B.z) (fun i => B.wb i.1)
  let tt : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim y (fun i => A.wb i.1)
  have hs : LinearIndependent ℂ s :=
    li_of_pair ε s (Sum.elim B.Fv (fun i => B.wb i.1)) 1 (by simp) (by
      rintro (a|j) (b|i)
      · simp [s, B.Fv_fam, Matrix.one_apply]
      · simp [s, B.Fv_w]
      · simp [s, B.w_fam]
      · simp [s, B.ww, Matrix.one_apply, Subtype.coe_inj])
  have ht : LinearIndependent ℂ tt :=
    li_of_pair ε tt (Sum.elim (fam A.e A.z) (fun i => A.wb i.1)) (Matrix.fromBlocks Z 0 0 1)
      (by rw [det_fromBlocks_zero₂₁, det_one, mul_one]; exact hZ) (by
      rintro (a|j) (b|i)
      · simp [tt, hydef, A.p1]
      · simp [tt, A.fam_w]
      · simp [tt, hydef, A.p4, j.2]
      · simp [tt, A.ww, Matrix.one_apply, Subtype.coe_inj])
  have hG : ∀ i j, hJ ε (tt i) (tt j) = hJ ε (s i) (s j) := by
    rintro (b|i) (c'|j)
    · exact hgram b c'
    · show hJ ε (y b) (A.wb j.1) = hJ ε (fam B.e B.z b) (B.wb j.1)
      rw [swapJ (A.p4 i0 Z Aα t j.1 b), if_neg j.2, star_zero, B.fam_w]
    · show hJ ε (A.wb i.1) (y c') = hJ ε (B.wb i.1) (fam B.e B.z c')
      rw [hydef, A.p4, if_neg i.2, B.w_fam]
    · show hJ ε (A.wb i.1) (A.wb j.1) = hJ ε (B.wb i.1) (B.wb j.1)
      rw [A.ww, B.ww]
  obtain ⟨g, hg⟩ := wittFam ε s tt hs ht hG
  exact ⟨g, y, t, htc, fun b => hg (Sum.inl b), fun i hi => hg (Sum.inr ⟨i, hi⟩), A.p1 i0 Z Aα t,
    A.p4 i0 Z Aα t⟩

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
end
end

section

open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inNuX {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ) : InNuX X u u' sc := by
  have hC : 0 ≤ DisintegrationConstant X u u' sc := by
    unfold DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hO : ∀ c, 0 ≤ hilbertSchmidtSqGram X u u' sc c := fun c => by
    unfold hilbertSchmidtSqGram hs2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : Measurable (fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (InfCut.wt_cont X u u').measurable)
  unfold InNuX intOOe intCe nuM
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr fun c => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul' (hO c), ← ENNReal.ofReal_mul hC, mul_assoc]

end Formalism.L2.SG.Pf
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.RealObj.SpanPreservation

open Formalism.L2.SG.HidaSetting

theorem span_pres {n r : ℕ} (e : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) {y : Fin n → ℂ} (hy : y ∈ spanLt e r) :
    g *ᵥ y ∈ spanLt e r := by
  have hmono : ∀ a : Fin r, spanLt e a.1 ≤ spanLt e r := fun a =>
    Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a.1) => lt_trans hb a.2)
  have hgen : ∀ a : Fin r, g *ᵥ e a ∈ spanLt e r := by
    intro a
    have e1 : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨a, a.2, rfl⟩) (hmono a (hg a))
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem w hw => obtain ⟨b, -, rfl⟩ := hw; exact hgen b
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ ha

theorem inN_inv {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (h1 : gi * g = 1) (hg : InN ε e z g) : InN ε e z gi := by
  have hS : InS e z gi := Formalism.L2.SG.RealObj.InfCut.inS_inv e z g gi h1 hg.1
  refine ⟨hS, fun y hy => ?_⟩
  have key : (gi - 1) *ᵥ y = -(gi *ᵥ ((g - 1) *ᵥ y)) := by
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1]
  rw [key]
  exact Submodule.neg_mem _ (span_pres e gi hS.1 (hg.2 y hy))

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ninfU_inv (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : s⁻¹ ∈ X.NinfU u := fun v =>
  inN_inv _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)) (hs v)

end Formalism.L2.SG.RealObj.SpanPreservation
end
end
