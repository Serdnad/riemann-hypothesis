module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.DenOne

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LBGerm

variable {X : Scheme.{0}} [IsIntegral X]

theorem isRatSec_lbPow {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) (τ : ℕ) :
    IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ := fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem res_mem_secOn (L : LB X) (V : X.Opens) (a : Γ(X, V)) :
    (fun J : PUnit → L.ι => resG X (inf_le_left : V ⊓ powChart L J ≤ V) a) ∈ secOn (lbPow L 0) V :=
  mem_secOn_of_germ _ fun y i j hV hi hj => by
    rw [gm_lbPow_g 0 (𝟙 X) y i j hi hj, pow_zero, Units.val_one, one_mul]
    exact (gs_res (𝟙 X) y _ (⟨hV, hi⟩ : y ∈ V ⊓ (lbPow L 0).U i) a).trans
      (gs_res (𝟙 X) y _ (⟨hV, hj⟩ : y ∈ V ⊓ (lbPow L 0).U j) a).symm

theorem unitAt_ne_zero {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) : f ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact (hc.map (algebraMap _ X.functionField)).ne_zero

theorem exists_den_one : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField),
    ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  intro k _ X _ p D _ P hA f
  haveI := hA.compactSpace
  haveI := hA.quasiSeparatedSpace
  have hL := hA.isLB
  obtain ⟨n, hn, s, hgs, haff⟩ := hA.exists_affine (genericPoint X)
  haveI : Nonempty (nonzeroLocus s) := ⟨⟨_, hgs⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X (nonzeroLocus s) haff
  obtain ⟨a, b, hb, hf⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus s)) f
  change fnOf _ hgs a / fnOf _ hgs b = f at hf
  have hβ : fnOf _ hgs b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨Na, ha⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) a)
  obtain ⟨Nb, hb'⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) b)
  obtain ⟨u, hu⟩ := ha (max Na Nb + 1) (by omega)
  obtain ⟨v, hv⟩ := hb' (max Na Nb + 1) (by omega)
  have hρ := isRatSec_lbPow P.hr' (0 + n * (max Na Nb + 1))
  obtain ⟨e, he⟩ := RepDict.exists_quot (isLB_lbPow hL (0 + n * (max Na Nb + 1))) hρ
  have hmem : ∀ w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec,
      e w ∈ P.H 0 ((0 + n * (max Na Nb + 1) : ℕ) : ℤ) := by
    intro w x i j _ hj
    have hJ : x ∈ (lbPow P.A.B (0 + n * (max Na Nb + 1))).U (fun _ => j) := mem_powChart.2 hj
    have h1 := he w (fun _ => j) (gen_mem hJ)
    simp only [Pair.loc, zpow_zero, mul_one, zpow_natCast]
    rw [← Units.val_pow_eq_pow_val, h1]
    exact regAt_fnOf hJ _ _
  obtain ⟨j₀, hj₀⟩ := exists_chart hL (genericPoint X)
  have hJ₀ : genericPoint X ∈ powChart P.A.B (fun _ => j₀) := mem_powChart.2 hj₀
  have hVJ : genericPoint X ∈ nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) := ⟨hgs, hJ₀⟩
  have key : ∀ (w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec) (a' : Γ(X, nonzeroLocus s)),
      resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn w (fun _ => j₀)) =
        resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) *
        resG X (inf_le_left : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ nonzeroLocus s) a' →
      e w * (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) =
        fnOf _ hJ₀ (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) * fnOf _ hgs a' := by
    intro w a' h
    have h' := congrArg (fnOf _ hVJ) h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at h'
    rw [← Units.val_pow_eq_pow_val]
    exact (he w _ hJ₀).trans h'
  have eu := key u a (hu _)
  have ev := key v b (hv _)
  have hS : fnOf _ hJ₀ (powFn s (fun _ => j₀)) ≠ 0 := by
    exact unitAt_ne_zero ((unitAt_fnOf_iff hJ₀ hJ₀ _).2 ((mem_nonzeroLocus_iff_basicOpen s hJ₀).1 hgs))
  have hR : (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) ≠ 0 := pow_ne_zero _ (P.r' j₀).ne_zero
  refine ⟨0 + n * (max Na Nb + 1), e v, by positivity, fun h0 => ?_, hmem v, ?_⟩
  · rw [h0, zero_mul] at ev
    exact mul_ne_zero (pow_ne_zero _ hS) hβ ev.symm
  · have e1 : e u = _ := eq_div_of_mul_eq hR eu
    have e2 : e v = _ := eq_div_of_mul_eq hR ev
    have : e v * f = e u := by
      rw [e1, e2, ← hf]
      field_simp
    rw [this]
    exact hmem u

end GlobalTheory.HSNef.DenOne
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VolBr

theorem Pair.div_pow_mem_H_of_mul_pow_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ,
    ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N (m - c) → u * t ^ N / s ^ m ∈ P.H 0 (b * N - c) →
    u / s ^ m ∈ P.H N (-c) := by
  intro k _ X _ p D _ P b s t hG c N m u hu hut x i j hi hj
  let O : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hO : ∀ f, RegAt x f ↔ f ∈ O := fun f => Iff.rfl
  have hri : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have hrj : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  have hs : P.loc 0 1 s i j ∈ O := (hO _).1 (hG.s_mem.1 x i j hi hj)
  have ht : P.loc (-1) b t i j ∈ O := (hO _).1 (hG.t_mem.1 x i j hi hj)
  have hs0 : P.loc 0 1 s i j ≠ 0 := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one]
    exact mul_ne_zero hG.s_ne hrj
  have hreg : ∀ g ∈ O, g * P.loc (-1) b t i j / P.loc 0 1 s i j ∈ O → g / P.loc 0 1 s i j ∈ O :=
    fun g hg h => (hO _).1 (hG.reg x i j hi hj g ((hO _).2 hg) ((hO _).2 h))
  have hg : P.loc N ((m : ℤ) - c) u i j ∈ O := (hO _).1 (hu x i j hi hj)
  have e1 : P.loc N ((m : ℤ) - c) u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m =
      P.loc 0 ((b : ℤ) * N - c) (u * t ^ N / s ^ m) i j := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one, zpow_sub₀ hrj, zpow_neg, mul_pow, inv_pow, zpow_natCast]
    rw [show ((b : ℤ) * N) = ((b * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    field_simp
  have e2 : P.loc N ((m : ℤ) - c) u i j / P.loc 0 1 s i j ^ m = P.loc N (-c) (u / s ^ m) i j := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one, zpow_sub₀ hrj, zpow_neg, mul_pow, zpow_natCast]
    field_simp
  have hgN : P.loc N ((m : ℤ) - c) u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m ∈ O := by
    rw [e1]
    exact (hO _).1 (hut x i j hi hj)
  have := regularPair_pow X.functionField O _ _ hs ht hs0 hreg m N _ hg hgN
  rw [e2] at this
  exact (hO _).2 this

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.ChangePair
open GlobalTheory.VolBr.NuEq
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_chart (M : HermLB p) (x : X) : ∃ c, x ∈ M.B.U c := by
  have h : x ∈ (⨆ c, M.B.U c) := by rw [M.isLB.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem loc_eq (P : Pair p) (a b a' b' i j : ℤ) (f : X.functionField) (ρ ρ' : X.functionFieldˣ) (e g) :
    f * (ρ : X.functionField) ^ i * (ρ' : X.functionField) ^ j =
      P.loc (i * a + j * a') (i * b + j * b') f e g *
        (((ρ : X.functionField) / P.loc a b 1 e g) ^ i * ((ρ' : X.functionField) / P.loc a' b' 1 e g) ^ j) := by
  have hs : (P.r e : X.functionField) ≠ 0 := (P.r e).ne_zero
  have ht : (P.r' g : X.functionField) ≠ 0 := (P.r' g).ne_zero
  simp only [Pair.loc, one_mul]
  rw [div_zpow, div_zpow, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    zpow_add₀ hs, zpow_add₀ ht, mul_comm a i, mul_comm b i, mul_comm a' j, mul_comm b' j]
  have h1 := zpow_ne_zero (i * a) hs
  have h2 := zpow_ne_zero (i * b) ht
  have h3 := zpow_ne_zero (j * a') hs
  have h4 := zpow_ne_zero (j * b') ht
  field_simp

end GlobalTheory.HSNef.ChangePair

namespace GlobalTheory.HSNef


open GlobalTheory.VolBr.NuEq ChangePair in
theorem change_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  intro k _ X _ p P a b a' b' M N ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  let Q : Pair p := ⟨M, N, ρ, ρ', hρ, hρ'⟩
  have hw : ∀ (i j : ℤ) (x : X) c d e g, x ∈ M.B.U c → x ∈ N.B.U d → x ∈ P.L.B.U e → x ∈ P.A.B.U g →
      UnitAt x (((ρ c : X.functionField) / P.loc a b 1 e g) ^ i *
        ((ρ' d : X.functionField) / P.loc a' b' 1 e g) ^ j) :=
    fun i j x c d e g hc hd he hg =>
      (NuEq.unitAt_zpow (hu x c e g hc he hg) i).mul (NuEq.unitAt_zpow (hu' x d e g hd he hg) j)
  have hH : ∀ i j : ℤ, Q.H i j = P.H (i * a + j * a') (i * b + j * b') := by
    intro i j
    ext f
    constructor
    · intro hf x e g he hg
      obtain ⟨c, hc⟩ := exists_chart M x
      obtain ⟨d, hd⟩ := exists_chart N x
      have hW := hw i j x c d e g hc hd he hg
      have h := hf x c d hc hd
      change RegAt x (f * _ ^ i * _ ^ j) at h
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g] at h
      have h' := h.mul hW.inv.regAt
      rwa [mul_assoc, mul_inv_cancel₀ hW.ne_zero, mul_one] at h'
    · intro hf x c d hc hd
      obtain ⟨e, he⟩ := exists_chart P.L x
      obtain ⟨g, hg⟩ := exists_chart P.A x
      change RegAt x (f * _ ^ i * _ ^ j)
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g]
      exact (hf x e g he hg).mul (hw i j x c d e g hc hd he hg).regAt
  have hnu : ∀ (i j : ℤ) (f : X.functionField), f ∈ P.H (i * a + j * a') (i * b + j * b') →
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), Q.nu i j σ y f = P.nu (i * a + j * a') (i * b + j * b') σ y f := by
    intro i j f hf σ y
    have hc := mem_pick (M.φ σ).isLB y
    have hd := mem_pick (N.φ σ).isLB y
    have he := mem_pick (P.L.φ σ).isLB y
    have hg := mem_pick (P.A.φ σ).isLB y
    set c := pick (M.φ σ).isLB y
    set d := pick (N.φ σ).isLB y
    set e := pick (P.L.φ σ).isLB y
    set g := pick (P.A.φ σ).isLB y
    have hfQ : f ∈ Q.H i j := (hH i j).symm ▸ hf
    rw [nu_eq k X p Q i j f hfQ σ y c d hc hd, nu_eq k X p P _ _ f hf σ y e g he hg]
    have hU := hu _ c e g (mem_ptsIn.1 hc) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hU' := hu' _ d e g (mem_ptsIn.1 hd) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hreg : RegAt (under y) (P.loc (i * a + j * a') (i * b + j * b') f e g) :=
      hf _ e g (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have eU : ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 e g) y‖ =
        Real.exp ((M.φ σ).φ c y / 2 - (a * (P.L.φ σ).φ e y + b * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU))]
      congr 1
      linarith [hn σ y c e g hc he hg]
    have eU' : ‖ratVal ((ρ' d : X.functionField) / P.loc a' b' 1 e g) y‖ =
        Real.exp ((N.φ σ).φ d y / 2 - (a' * (P.L.φ σ).φ e y + b' * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU'))]
      congr 1
      linarith [hn' σ y d e g hd he hg]
    change ‖ratVal (f * _ ^ i * _ ^ j) y‖ * _ = _
    rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g,
      ratVal_mul hreg ((NuEq.unitAt_zpow hU i).mul (NuEq.unitAt_zpow hU' j)).regAt,
      ratVal_mul (NuEq.unitAt_zpow hU i).regAt (NuEq.unitAt_zpow hU' j).regAt,
      ratVal_zpow' hU, ratVal_zpow' hU', norm_mul, norm_mul, norm_zpow, norm_zpow, eU, eU',
      ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨Q, rfl, rfl, fun i j R => ?_⟩
  ext f
  constructor
  · rintro ⟨hf, hR⟩
    have hf' : f ∈ P.H (i * a + j * a') (i * b + j * b') := hH i j ▸ hf
    exact ⟨hf', fun σ y => hnu i j f hf' σ y ▸ hR σ y⟩
  · rintro ⟨hf, hR⟩
    exact ⟨(hH i j).symm ▸ hf, fun σ y => (hnu i j f hf σ y).symm ▸ hR σ y⟩

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  first | exact @GlobalTheory.VolBr.nu_eq | exact GlobalTheory.VolBr.nu_eq | (intros; apply GlobalTheory.VolBr.nu_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.isSeminormBallFamily_sectionBalls : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  first | exact @GlobalTheory.VolBr.Pair.isBallFam | exact GlobalTheory.VolBr.Pair.isBallFam | (intros; apply GlobalTheory.VolBr.Pair.isBallFam <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.representedBundle_sections_rationalFunctions_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∃ e : M.B.Sec → X.functionField, Function.Injective e ∧ Set.range e = (P.H a b : Set X.functionField) ∧ (∀ u (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y (e u) ^ 2 = (M.φ σ).nsq (secVal p σ u) y) ∧ ∀ u (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j)) := by
  first | exact @GlobalTheory.VolBr.RepDict.rep_dict | exact GlobalTheory.VolBr.RepDict.rep_dict | (intros; apply GlobalTheory.VolBr.RepDict.rep_dict <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  first | exact @GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul | exact GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul | (intros; apply GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.represents_hermitianLineBundle_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → P.Rep (-a) (-b) M.dual := by
  first | exact @GlobalTheory.VolBr.Pair.rep_dual | exact GlobalTheory.VolBr.Pair.rep_dual | (intros; apply GlobalTheory.VolBr.Pair.rep_dual <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  first | exact @GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | exact GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | (intros; apply GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.represents_base_bundles_and_trivial : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), P.Rep 1 0 P.L ∧ P.Rep 0 1 P.A ∧ P.Rep 0 0 (HermLB.triv p) := by
  first | exact @GlobalTheory.VolBr.Pair.rep_base | exact GlobalTheory.VolBr.Pair.rep_base | (intros; apply GlobalTheory.VolBr.Pair.rep_base <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.represents_hermitianLineBundle_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (n : ℕ), P.Rep a b M → P.Rep (n * a) (n * b) (M.pow n) := by
  first | exact @GlobalTheory.VolBr.Pair.rep_pow | exact GlobalTheory.VolBr.Pair.rep_pow | (intros; apply GlobalTheory.VolBr.Pair.rep_pow <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  first | exact @GlobalTheory.SmoothMultilinear.smooth_map | exact GlobalTheory.SmoothMultilinear.smooth_map | (intros; apply GlobalTheory.SmoothMultilinear.smooth_map <;> assumption)
end
