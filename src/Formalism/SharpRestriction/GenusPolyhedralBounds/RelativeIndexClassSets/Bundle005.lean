module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.DiscriminantPowEightLeSqrt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.BaseDegreeAtLiftIndex
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle004

@[expose] public section

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    0 ≤ X.phiC la y := by
  unfold PJ.phiC
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
    refine Real.sInf_nonneg ?_
    rintro x ⟨l, -, h2, rfl⟩
    by_cases hb : (P.loc X.dat (resCh la)).beS (X.pt66 la y) = 0
    · rw [hb]; simp
    · refine (h2 _ ?_ hb).le
      intro a
      by_cases ha : a = 0
      · subst ha; simp
      · exact ((P.loc X.dat (resCh la)).be_pos (X.pt66 la y) a ha).le
  · exact le_rfl

namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

variable {L}

end LocDat

end Formalism.MainNotions.Gaps.T0
end
end

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem dm_eq (T : ParamsT D L P) : WeightFamilies.dimY D D.R.m = T.Dp := by
  rw [T.Dp_eq]
  unfold WeightFamilies.dimY Ranks.sigW Ranks.r
  simp [Nat.choose_two_right]

theorem order_le_modulus (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : T.TO ≤ q0N T := by
  unfold q0N
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hZ' : (1 : ℝ) ≤ zBase L := by
    have h : (1 : ℝ) ≤ 10 ^ 60 := by norm_num
    linarith
  have hPP : 1 ≤ T.PP := by
    rw [T.PP_eq]
    exact one_le_mul_of_one_le_of_one_le T.one_le_CP (Real.one_le_rpow hZ' (by linarith [T.eP_ge]))
  have hbpos : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have h1 : (T.TO : ℝ) ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_right hTpos.le hPP) T.TO_PP'
  have h2 := mul_self_le_mul_self hTpos.le h1
  rw [← Real.rpow_add hbpos] at h2
  norm_num at h2
  have hq : (T.TO : ℝ) ≤ L.sc.b / (T.TO : ℝ) := by
    rw [le_div_iff₀ hTpos]
    linarith
  exact_mod_cast le_trans hq (Nat.le_ceil _)

abbrev runOf (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : RunN D where
  T := T.TO
  nW := T.nWn
  nP := T.nP
  Q0 := q0N T
  T_pos := by have := T.TO_40; omega
  nW_even := T.nW_even
  even_nP₂ := T.even_nP₂
  split := T.split
  nP_le_nW := T.nW_lo.2.2
  hQ0 := by
    rw [dm_eq T]
    have := T.TO_nW; have := order_le_modulus T S hZ
    omega

def Kc0 : KAdm := ⟨1, 1, 1, 1, 1, 1, 1, 1, 2⟩

def NonvanishingSectionCondition (T : ParamsT D L P) : KHyp := ⟨10, 20, 1000, 12, T.CP, T.eP, 2⟩

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

theorem eTq : ((runOf T S hZ).Tq : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) := by
  unfold RunN.Tq Tp
  dsimp only [runOf]
  rw [dm_eq T]
  push_cast
  ring

theorem eQ : ((runOf T S hZ).Q : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r := by
  unfold RunN.Q
  push_cast
  linarith [eTq T S hZ]

theorem ekl : ((runOf T S hZ).kl : ℝ) =
    ((T.Dp : ℝ) + 2) * T.nWn + 2 * D.R.r + ((T.TO : ℝ) + ((T.Dp : ℝ) + 2)) * (q0N T : ℝ) := by
  unfold RunN.kl
  push_cast
  rw [eTq T S hZ]
  have hd : (Dm D : ℝ) = (T.Dp : ℝ) := by
    first
    | (unfold Dm; exact_mod_cast dm_eq T)
    | (simp only [Dm]; exact_mod_cast dm_eq T)
    | exact_mod_cast dm_eq T
  rw [hd]

theorem enV : (D.R.nV : ℝ) = (T.nP : ℝ) + (T.TO : ℝ) * T.nWn := by
  have h := T.split
  unfold Ranks.nV
  exact_mod_cast h

theorem ka_le : (runOf T S hZ).ka.size ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sK ?_
  have h := (runOf T S hZ).ka_size_le
  rw [ekl, eTq, eQ, enV T] at h
  exact h

theorem b_le_kl : L.sc.b ≤ ((runOf T S hZ).kl : ℝ) := by
  rw [ekl T S hZ]
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hq : L.sc.b / (T.TO : ℝ) ≤ (q0N T : ℝ) := by unfold q0N; exact Nat.le_ceil _
  have hq' : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ) := by
    rw [div_le_iff₀ hTpos] at hq
    linarith
  have h0 : (0 : ℝ) ≤ (T.Dp : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (T.nWn : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (q0N T : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) := by positivity
  nlinarith [mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h1,
    mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h2]

theorem b_le_ka : L.sc.b ≤ (runOf T S hZ).ka.size := (b_le_kl T S hZ).trans (runOf T S hZ).ka_size_ge

theorem dF_le : (DF (runOf T S hZ).wL : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).dL ?_
  have h := (runOf T S hZ).DF_wL_le
  rw [eQ] at h
  exact h

theorem g_ge (P : ParameterChoice' D L) (i : Fin 2) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
  exact h1.trans (h2 i).1

theorem qq_ge (P : ParameterChoice' D L) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (qq D : ℝ) := by
  unfold qq
  first
  | (rw [Nat.cast_min]; exact le_min (g_ge P 0) (g_ge P 1))
  | (push_cast; exact le_min (g_ge P 0) (g_ge P 1))

theorem eRR : WeightFamilies.RRv D 2 = D.host.rdE ^ 2 := by
  unfold WeightFamilies.RRv
  first
  | rfl
  | simp

theorem eg0 : (g0 D : ℝ) = 1250 * D.R.r := by
  unfold g0
  push_cast
  ring

theorem third_hypothesis_of_params : H3 L (NonvanishingSectionCondition T) T.CP T.eP 2 0 (runOf T S hZ).wL T.TO := by
  have hR := rn_of T S hZ
  have hd0 : (0 : ℝ) ≤ (DF (runOf T S hZ).wL : ℝ) := Nat.cast_nonneg _
  have hd := dF_le T S hZ
  have hq := qq_ge P
  have hq0 : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq
  have hb := hR.h3b hd0 hd hq
  have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T]
    exact hR.h3a hd0 hd hq
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T, eg0]
    exact hb
  · rw [Real.rpow_zero, one_mul, WeightFamilies.PPv_rec T, dm_eq T]
    refine le_trans ?_ T.TO_ge
    have hden : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    apply div_le_div_of_nonneg_right _ hden.le
    have hP := hR.PP_pos
    exact le_mul_of_one_le_right (by positivity) hx1
  · show (T.TO : ℝ) * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1
    rw [eRR, WeightFamilies.PPv_rec T, eg0]
    have e : (T.TO : ℝ) * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * (1250 * D.R.r) =
        ((T.TO : ℝ) * (1250 * D.R.r) * D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    rw [e, div_le_one hq0]
    exact hb
  · show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 2 ^ 2 *
      (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2
    rw [eRR, WeightFamilies.PPv_rec T]
    have hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 := by
      have : (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ hm0.le hmk 3
      calc (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 3 :=
            mul_le_mul hfk this (by positivity) (by positivity)
        _ = (D.R.k : ℝ) ^ 4 := by ring
    have he := hR.h3e hd0 hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm
    have e : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) =
        ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2)) / (qq D : ℝ) := by ring
    rw [e, div_le_iff₀ hq0]
    linarith
  · rw [dm_eq T]
    have := hR.h3f hd0 hd hq
    have e : (T.Dp : ℝ) + 2 + 2 = (T.Dp : ℝ) + 4 := by ring
    rw [e] at this
    exact this

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def etWt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  wscalar D j (g0 D * i) (by unfold g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

def a0 (D : D7) (j T : ℕ) : ℕ := T - WeightFamilies.dimY D j

structure GlobalFamilyData (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) where
  N : ℕ
  w : Fin N → B.Cusp j wL
  del : ℕ
  th' : Fin del → B.Cusp j wF
  rz : ℕ
  alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ
  th0 : Fin rz → B.Cusp j (X.wF0 wL wF)
  zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka
  rq : ℕ
  th : Fin rq → B.Mlat j ka
  iet : ℕ
  et : B.Cusp j (etWt D j iet)

  mx : (B.KO →+* ℂ) → ℝ

namespace GlobalFamilyData

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF)

def Tied (large₂ : SizeData₂ D) (S : Scal B) (CRm : ℝ) (T : ℕ) (c Gc Prw Ch Ah Cf Af : ℝ) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL ∧ (∀ k, G.w k ∈ B.Mlat j wL) ∧
  Real.log G.N ≤ Prw * (wL.size - 1) ∧
  (∀ σ k, Real.log (B.supN j wL σ (G.w k)) ≤ G.mx σ) ∧
  (∑ σ, G.mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ Gc * wL.size ∧
  (∀ i, G.th' i ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size) ∧
  (∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ G.th0 k ∈ B.Mlat j (X.wF0 wL wF) ∧
    WeightFamilies.meanLogSup B (G.th0 k) ≤ Gc * (X.wF0 wL wF).size ∧ ∑ i, G.alz k i = a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0) ∧
  G.rq = WeightFamilies.rhoP B CRm T c j ka ∧
  (∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka) ∧
  Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
    WeightFamilies.MggK B CRm T c j ka = ⊤ ∧
  (∀ i, WeightFamilies.meanLogSup B ((G.th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) ∧
  (j < D.R.m → 0 < G.iet ∧ G.et ≠ 0 ∧ X.NonZeroComp _ G.et ∧
    (∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) ∧
    ∀ σ, Real.log (B.supN j _ σ G.et) / G.iet ≤ WeightFamilies.PPv D large₂ Cf Af)

end GlobalFamilyData

def Shares (D : D7) {j : ℕ} (wL : WeightFamilies.Wt D j) (del rz rq d T : ℕ) (CRm c : ℝ) : Prop :=
  (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ d ∧
  (rz : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T ∧
  (rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def PolyDom (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end
