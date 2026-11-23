module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgre
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle302
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle235
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Formalism.LocalToGlobal.Columns.QthExistsBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle314
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplCoset

theorem sameCoset_local {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (e₀ e D : ℕ) (c g : Sp E n ≃ₗ[E] Sp E n) (k : GLint E n P) (hc : c ∈ GLint E n P) (hg : g ∈ GLint E n P)
    (hk : k ∈ GlobalTheory.TopStep.prinCong n P D) (hck : c⁻¹ = g * k.1) (hD : e + e₀ ≤ D) (y₀ : Sp E n)
    (hy₀ : ∀ l, IntAt P ((qOf P : E) ^ e * y₀ l)) (hgy : ∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (g y₀ - y₀) l)) (y : Sp E n) :
    (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (c y - y₀) l)) ↔ (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (y - y₀) l)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set q : E := ((qOf P : ℕ) : E) with hqdef
  have hsm : ∀ (a : E) (v : Sp E n), (∀ l, IntAt P (a * v l)) ↔ a • v ∈ stdAt E n P := by
    intro a v
    rw [GlobalTheory.TopStep.mem_stdAt]
    rfl
  have hpow : ∀ (m : ℕ) (v : Sp E n), v ∈ stdAt E n P → q ^ m • v ∈ stdAt E n P := by
    intro m v hv
    have : q ^ m • v = ((qOf P : 𝓞 E) ^ m) • v := by
      rw [← algebraMap_smul E ((qOf P : 𝓞 E) ^ m) v]
      congr 1 <;> simp [hqdef]
    rw [this]
    exact Submodule.smul_mem _ _ hv
  have hw : q ^ e • y₀ ∈ stdAt E n P := (hsm _ _).1 hy₀
  have hkw := hk _ hw
  have hky : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) ∈ stdAt E n P := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + e + e₀ := ⟨D - e - e₀, by omega⟩
    have e1 : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) = q ^ d • ((q ^ D)⁻¹ • (k.1 (q ^ e • y₀) - q ^ e • y₀)) := by
      rw [map_smul, ← smul_sub, smul_smul, smul_smul]
      congr 1
      rw [hd, pow_add, pow_add]
      field_simp
    rw [e1]
    exact hpow _ _ hkw
  have hcy : (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀) ∈ stdAt E n P := by
    have e2 : c⁻¹ y₀ - y₀ = g (k.1 y₀ - y₀) + (g y₀ - y₀) := by
      rw [hck, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e2, smul_add, ← map_smul]
    exact add_mem ((hg _).2 hky) ((hsm _ _).1 hgy)
  have hcc : ∀ x, c (c⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [hsm, hsm]
  have e3 : (q ^ e₀)⁻¹ • (c y - y₀) = c ((q ^ e₀)⁻¹ • (y - y₀) - (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀)) := by
    rw [← smul_sub, map_smul]
    simp only [map_sub, hcc]
    congr 1
    abel
  rw [e3, hc]
  exact Submodule.sub_mem_iff_left _ hcy

end GlobalTheory.CplCoset

namespace GlobalTheory.CplCoset

theorem sameCoset_kappa : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∀ P (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P ((κ'' P).1 y) (A.y0 β' P) ↔
      SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 β' P)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H β' κ' κ'' hF P y
  have hok := t.idx_ok μ
  have hU := (((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U_eq κ'.1).1 κ'.2
  obtain ⟨g, z, ⟨hmid, hsame⟩, hfr⟩ := (H.levCpl β').1 P (vUnder (t := t) P.1) (isOver_vUnder P.1) κ'.1 hU.1 (hU.2 _)
  have hgC := (exists_midLev_iff _ _ _ _ _ _ _ g).1 ⟨z, hmid⟩
  have hg : g ∈ GLint t.X.E _ P.1 := hok.int _ _ P hgC
  have hD1 := hok.cst_ok.D_pos P
  set k := g⁻¹ * ((κ'' P)⁻¹).1 with hk
  have hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N (t.m2 + 1))) l)) := by
    intro s l
    have hc := GlobalTheory.FrameAway.frame_core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD1 _ _ _ _ hfr (hF P) (fun _ _ => rfl) l s
    rw [← map_inv, ← map_mul, GlobalTheory.FrameAway.qOf_seamP, ← hk] at hc
    refine GlobalTheory.FrameAway.intAt_of_seamP t.seam P.1 _ ?_
    convert hc using 1
    have hm := congrFun (seamGL_mulVec t.seam k (Pi.single s 1)) l
    have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N (t.m2 + 1))) j)) = Pi.single s (1 : D.host.E) := by
      funext j
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hs1, Matrix.mulVec_single_one] at hm
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : l = s
    · subst h; simp [Matrix.col_apply]
    · simp [h, Matrix.col_apply]
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 ((t.cst μ).D P) k hD1 hcol
  have hy₀ := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H β' P
  unfold SameCoset
  refine sameCoset_local P.1 _ _ ((t.cst μ).D P) (κ'' P).1 g ⟨k, hkG⟩ (κ'' P).2 hg hkC ?_ ?_ (A.y0 β' P) hy₀ hsame y
  · show ((κ'' P).1)⁻¹ = g * (g⁻¹ * ((κ'' P)⁻¹).1)
    rw [mul_inv_cancel_left]
    rfl
  · by_cases h : P.1 ∈ t.Pr.vGs
    · simp only [h, if_true]
      have := hok.depthG P h
      omega
    · simp only [h, if_false]
      have := hok.depthQ P h
      omega

end GlobalTheory.CplCoset

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.LevFrames

open Matrix

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem intAtA_neg' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

theorem intAtA_pow' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact GlobalTheory.CplPt.intAtA_mul ih h

theorem core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y⁻¹ * ratA F G₁)) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = 1 + Bm := by
    rw [hMh', hAm, hBm, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hB i j))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hA i j))))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_sum _ _ fun l _ => GlobalTheory.CplPt.intAtA_mul (hA i l) (hm l j)))
  have desc : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by
    intro m
    induction m with
    | zero => intro hm i j; simpa using hm i j
    | succ m ih => intro hm; exact ih (step m hm)
  obtain ⟨J, hJ⟩ := qth_bound Q Mm
  have hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ) := by
    have h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem _
    have := (Q.intValuation_le_pow_iff_mem _ 1).2 h0
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
    simpa using this
  have hbig : ∀ i j, IntAtA (F := F) Q (d ^ (J + 1) * (qi * Mh i j)) := by
    intro i j
    have e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j) := by
      rw [hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]
    rw [e]
    refine GlobalTheory.CplPt.intAtA_of_intAt ((qth_intAt_iff Q _).2 ?_)
    rw [map_mul, map_pow]
    calc Q.valuation E ((qOf Q : ℕ) : E) ^ (n * J) * Q.valuation E (Mm i j) ≤ WithZero.exp (-1 : ℤ) ^ (n * J) * WithZero.exp (J : ℤ) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hqv _) (hJ i j)
      _ ≤ 1 := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          have : (J : ℤ) ≤ (n : ℤ) * J := by exact_mod_cast Nat.le_mul_of_pos_left J hn
          rw [nsmul_eq_mul]
          push_cast
          linarith
  have hfin := desc (J + 1) hbig a b
  show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)
  refine GlobalTheory.RatInt.intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open Formalism.L2.Ker Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

theorem intAt_of_seamP (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E) (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

end Seam

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem frames_lev : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A a j hj β x x₁ κ hx p p₁ hp hp₁ P g hg
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  set F₀ := frsF t.sel (t.tup μ) p P with hF₀
  set F₁ := frsF t.sel (t.tup μ) p₁ P with hF₁
  have hX : NearAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)))
      (seamGL t.seam F₀ * seamGL t.seam g.1) :=
    GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) hg (GlobalTheory.CplPt.seamGL_int t.seam g)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 * ratA D.host.F (A.fb j hj β P) =
      (ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)) := by
    rw [hx]; group
  have hX₁ := hp₁.frame P
  rw [e, ← hF₁] at hX₁
  have hc := core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ hX hX₁
  set C₀ := g.1⁻¹ * F₀⁻¹ * F₁ with hC₀
  have hM : (seamGL t.seam F₀ * seamGL t.seam g.1)⁻¹ * seamGL t.seam F₁ = seamGL t.seam C₀ := by
    rw [hC₀, map_mul, map_mul, map_inv, map_inv, _root_.mul_inv_rev]
  simp only [hM] at hc
  have hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (C₀ (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N j)) l)) := by
    intro s l
    have hc' := hc l s
    rw [GlobalTheory.TwU.MidIndep.qOf_seamP] at hc'
    refine intAt_of_seamP t.seam P.1 _ ?_
    convert hc' using 1
    have hm := congrFun (seamGL_mulVec t.seam C₀ (Pi.single s 1)) l
    have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N _)) j)) = Pi.single s (1 : D.host.E) := by
      funext j
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hs1, Matrix.mulVec_single_one] at hm
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : l = s
    · subst h; simp [Matrix.col_apply]
    · simp [h, Matrix.col_apply]
  obtain ⟨hk, hpc⟩ := GlobalTheory.CongOne.mem_glint_prinCong_of_cols P.1 ((t.cst μ).D P) C₀ hD hcol
  refine ⟨⟨C₀, hk⟩, hpc, fun a' b' => ?_, ?_⟩
  · have h1 := GlobalTheory.CplPt.intAtA_of_intAt (F := D.host.F) (hc a' b')
    convert h1 using 2
    rw [map_mul (iA D.host.F D.host.E), Matrix.sub_apply, Matrix.sub_apply, map_sub (iA D.host.F D.host.E), GlobalTheory.CplPt.ratA_apply,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · show F₁ = F₀ * (g.1 * C₀)
    rw [hC₀]
    group

end GlobalTheory.LevFrames
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  first | exact @GlobalTheory.CplCosetPt.cosetOf_frames_vG | exact GlobalTheory.CplCosetPt.cosetOf_frames_vG | (intros; apply GlobalTheory.CplCosetPt.cosetOf_frames_vG <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

theorem _root_.GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  first | exact @GlobalTheory.ZDual.pullV_dual_mem_latS | exact GlobalTheory.ZDual.pullV_dual_mem_latS | (intros; apply GlobalTheory.ZDual.pullV_dual_mem_latS <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  first | exact @GlobalTheory.TwV.funMoved_ptAd_rat | exact GlobalTheory.TwV.funMoved_ptAd_rat | (intros; apply GlobalTheory.TwV.funMoved_ptAd_rat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepCoords_conj_unitary_and_carries_companion : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  first | exact @GlobalTheory.TwV.conj_crd_unitary_carries | exact GlobalTheory.TwV.conj_crd_unitary_carries | (intros; apply GlobalTheory.TwV.conj_crd_unitary_carries <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  have hi0 : i ≤ D.R.m := Nat.le_of_succ_le hi
  have hlt : i < D.R.m := hi
  have h1 : (1 : GL (Fin (D.R.N i)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi0) := one_mem _
  have h1' : (1 : GL (Fin (D.R.N (i + 1))) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) := one_mem _
  have hx : ((St i hi0).y c).1 = ratA D.host.F (1 : GL (Fin (D.R.N i)) D.host.E) * ((St i hi0).y c).1 * (1 : ((St i hi0).K ((St i hi0).chOf c)).lev.U).1 := by
    simp
  have hx' : ((St (i + 1) hi).y c').1 = ratA D.host.F (1 : GL (Fin (D.R.N (i + 1))) D.host.E) * ((St (i + 1) hi).y c').1 * (1 : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U).1 := by
    simp
  have hu' := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hTie (i + 1) hi 1 h1'
  have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hTie i hi0 1 h1
  have hl := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hTie i hi0 c ((St i hi0).y c) 1 h1 1 hx
  have hl' := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hTie (i + 1) hi c' ((St (i + 1) hi).y c') 1 h1' 1 hx'
  have hd := GlobalTheory.T.adelicDatum_rational_translates_vs_classes A dtU a hP hTie Xi muT hL i hi c c' ((St i hi0).y c) ((St (i + 1) hi).y c') 1 h1 1 h1' 1 1 hx hx' hu'
  have hloc := hL.loc i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c')
  rw [hl, hl'] at hloc
  refine GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes D t.cc (ssRec t u μ) (t.rd u μ).lev _ _ (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x)) _ _ hu hu' ?_
  have hE : Xi i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c') = _ := funext fun z => by
    have := hd z
    simpa [(hL.mu_mul i hlt).1, -Matrix.toLin'_toMatrix'] using this
  rw [hE] at hloc
  exact hloc

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.stepCharacter_det_coupled_eq_prod_local : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU → ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ'.1) =
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'' P).1 : t.X.Eˣ) : t.X.E))) := by
  first | exact @GlobalTheory.CplMuDet.muOf_det_cpl | exact GlobalTheory.CplMuDet.muOf_det_cpl | (intros; apply GlobalTheory.CplMuDet.muOf_det_cpl <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

theorem _root_.GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  first | exact @GlobalTheory.FrameAway.frame_away | exact GlobalTheory.FrameAway.frame_away | (intros; apply GlobalTheory.FrameAway.frame_away <;> assumption)
end
