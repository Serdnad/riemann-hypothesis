module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle008
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.NVRules

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem unitAt_zpow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℤ) : UnitAt x (f ^ n) := by
  have hm : Units.mk0 f h.ne_zero ∈ unitsAt x := by
    change UnitAt x ((Units.mk0 f h.ne_zero : X.functionFieldˣ) : X.functionField)
    rwa [Units.val_mk0]
  have := zpow_mem hm n
  change UnitAt x (((Units.mk0 f h.ne_zero ^ n : X.functionFieldˣ)) : X.functionField) at this
  rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0] at this

theorem regAt_pow {x : X} {f : X.functionField} (h : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n)
    (h : UnitAt x (f ^ n)) : UnitAt x f := by
  have hne : f ≠ 0 := fun e => h.ne_zero (by rw [e, zero_pow (by omega)])
  refine (unitAt_iff hne).2 ⟨hf, ?_⟩
  have e : f⁻¹ = f ^ (n - 1) * (f ^ n)⁻¹ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), one_mul]
  rw [e]
  exact (regAt_pow hf _).mul h.inv.regAt

theorem unitAt_pow_iff {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n) :
    UnitAt x (f ^ n) ↔ UnitAt x f :=
  ⟨unitAt_of_pow hf hn, fun h => by simpa using unitAt_zpow h (n : ℤ)⟩

theorem unitAt_ratio {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {x : X} {i j : L.ι}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : UnitAt x ((r i : X.functionField) / r j) := by
  have h := gen_mem (memInf hi hj)
  rw [hr i j h, mul_div_cancel_right₀ _ (Units.ne_zero _)]
  exact unitAt_fnOf (memInf hi hj) h (L.g i j)

theorem loc_eq_mul (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i j = P.loc a b f i' j' *
      (((P.r i : X.functionField) / P.r i') ^ a * ((P.r' j : X.functionField) / P.r' j') ^ b) := by
  have h1 : ((P.r i' : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j' : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_loc_of (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hi' : x ∈ P.L.B.U i') (hj : x ∈ P.A.B.U j) (hj' : x ∈ P.A.B.U j')
    (h : UnitAt x (P.loc a b f i' j')) : UnitAt x (P.loc a b f i j) := by
  rw [loc_eq_mul P a b f i i' j j']
  exact h.mul ((unitAt_zpow (unitAt_ratio P.hr hi hi') a).mul (unitAt_zpow (unitAt_ratio P.hr' hj hj') b))

theorem mem_NV_iff (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i : P.L.B.ι} {j : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hj : x ∈ P.A.B.U j) : x ∈ NV P a b f ↔ UnitAt x (P.loc a b f i j) :=
  ⟨fun h => h i j hi hj, fun h _ _ hi' hj' => unitAt_loc_of P a b f hi' hi hj' hj h⟩

theorem div_eq_loc_div (P : Pair p) (a b : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    f / g = P.loc a b f i j / P.loc a b g i j := by
  have h1 : ((P.r i : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc]
  rw [mul_assoc f, mul_assoc g, mul_div_mul_right _ _ (mul_ne_zero h1 h2)]

theorem loc_pow (P : Pair p) (a b : ℤ) (g : X.functionField) (n : ℕ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (n * a) (n * b) (g ^ n) i j = P.loc a b g i j ^ n := by
  simp only [Pair.loc, mul_pow]
  rw [mul_comm (n : ℤ) a, mul_comm (n : ℤ) b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

end GlobalTheory.HSAmp.NVRules


open GlobalTheory.HSAmp.NVRules in
theorem GlobalTheory.HSAmp.nv_rules : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  intro k _ X _ p P a b g hg
  have cL := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB x
  have cA := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB x
  have h4 : ∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g)) := by
    intro f hf z hz
    obtain ⟨i, hi⟩ := cL z
    obtain ⟨j, hj⟩ := cA z
    have hu := (mem_NV_iff P a b g hi hj).1 hz
    rw [div_eq_loc_div P a b f g i j, mem_NV_iff P a b f hi hj]
    refine ⟨(hf z i j hi hj).mul hu.inv.regAt, fun h => h.mul hu.inv, fun h => ?_⟩
    have := h.mul hu
    rwa [div_mul_cancel₀ _ hu.ne_zero] at this
  refine ⟨?_, ?_, ?_, h4, ?_⟩
  · refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    obtain ⟨V, hV, hVu⟩ := ((mem_NV_iff P a b g hi hj).1 hx).exists_nhds
    refine ⟨((V ⊓ P.L.B.U i ⊓ P.A.B.U j : X.Opens) : Set X), fun y hy => ?_, Opens.isOpen _, ⟨⟨hV, hi⟩, hj⟩⟩
    obtain ⟨⟨hyV, hyi⟩, hyj⟩ := hy
    exact (mem_NV_iff P a b g hyi hyj).2 (hVu y hyV)
  · obtain ⟨i, hi⟩ := cL (genericPoint X)
    obtain ⟨j, hj⟩ := cA (genericPoint X)
    rw [mem_NV_iff P a b g hi hj]
    refine ⟨fun h e => h.ne_zero (by rw [e]; simp [Pair.loc]), fun h => unitAt_genericPoint ?_⟩
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
  · intro n hn
    ext x
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    rw [mem_NV_iff P _ _ _ hi hj, mem_NV_iff P a b g hi hj, loc_pow]
    exact unitAt_pow_iff (hg x i j hi hj) hn
  · intro f hf σ y hy
    have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    have hu := (mem_NV_iff P a b g hi hj).1 hy
    have hq := (h4 f hf _ hy).1
    have e : P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
        f / g * P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
      rw [div_eq_loc_div P a b f g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y), div_mul_cancel₀ _ hu.ne_zero]
    refine ⟨?_, ?_⟩
    · rw [Pair.nu, Pair.nu, e, ratVal_mul hq hu.regAt, norm_mul, mul_assoc]
    · rw [Pair.nu]
      exact mul_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) (Real.exp_pos _)
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ExtPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem compactSpace_of_projOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace Y := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem unitAt_zpow {z : X} {u : X.functionField} (h : UnitAt z u) (n : ℤ) : UnitAt z (u ^ n) := by
  have hu : u ≠ 0 := h.ne_zero
  induction n using Int.induction_on with
  | zero => rw [zpow_zero]; exact unitAt_one z
  | succ n ih => rw [zpow_add_one₀ hu]; exact ih.mul h
  | pred n ih => rw [zpow_sub_one₀ hu]; exact ih.mul h.inv

theorem loc_change (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i' j' = P.loc a b f i j *
      (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) := by
  have h1 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_quot (P : Pair p) (a b : ℤ) {z : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : z ∈ P.L.B.U i) (hi' : z ∈ P.L.B.U i') (hj : z ∈ P.A.B.U j) (hj' : z ∈ P.A.B.U j') :
    UnitAt z (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) :=
  (unitAt_zpow (germOf_eq_iff.1 (P.hr.germOf_eq hi' hi)) a).mul
    (unitAt_zpow (germOf_eq_iff.1 (P.hr'.germOf_eq hj' hj)) b)

theorem loc_pow_mul (P : Pair p) (e a b : ℤ) (c : ℕ) (x f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (e * c + a) b (x ^ c * f) i j = P.loc e 0 x i j ^ c * P.loc a b f i j := by
  have h0 : (P.r i : X.functionField) ≠ 0 := Units.ne_zero _
  simp only [Pair.loc, zpow_zero, mul_one, zpow_add₀ h0, zpow_mul, zpow_natCast, mul_pow]
  ring

theorem exists_pow_mul_regAt {W : X.Opens} (hW : IsAffineOpen W) (s : Γ(X, W)) (hg : genericPoint X ∈ X.basicOpen s)
    {g : X.functionField} (h : ∀ z ∈ X.basicOpen s, RegAt z g) :
    ∃ N : ℕ, ∀ z ∈ W, RegAt z (fnOf W (X.basicOpen_le s hg) s ^ N * g) := by
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg h
  have := hW.isLocalization_basicOpen s
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) a
  obtain ⟨N, hN⟩ := m.2
  refine ⟨N, fun z hz => ?_⟩
  have e := congrArg (fnOf _ hg) hm
  simp only [map_mul] at e
  change fnOf _ hg a * fnOf _ hg (resG X (X.basicOpen_le s) (m : Γ(X, W))) =
    fnOf _ hg (resG X (X.basicOpen_le s) b) at e
  rw [fnOf_resG, fnOf_resG, ha, ← hN, map_pow] at e
  rw [mul_comm, e]
  exact regAt_fnOf hz _ b

end GlobalTheory.HSAmp.ExtPow


open GlobalTheory.HSAmp.ExtPow in
theorem GlobalTheory.HSAmp.eventually_pow_mul_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e a b : ℤ) (x f : X.functionField), x ∈ P.H e 0 → x ≠ 0 → (∀ z ∈ NV P e 0 x, ∀ i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j → RegAt z (P.loc a b f i j)) → ∀ᶠ c : ℕ in atTop, x ^ c * f ∈ P.H (e * c + a) b := by
  intro k _ X _ p D hD P e a b x f hx hx0 hf
  haveI : CompactSpace X := compactSpace_of_projOver hD.isProjOver
  have loc_ok : ∀ z : X, ∃ W : X.Opens, z ∈ W ∧ ∃ N : ℕ, ∀ c : ℕ, N ≤ c → ∀ w ∈ W, ∀ i j, w ∈ P.L.B.U i →
      w ∈ P.A.B.U j → RegAt w (P.loc (e * c + a) b (x ^ c * f) i j) := by
    intro z
    obtain ⟨i, hi⟩ := exists_chart P.L.isLB z
    obtain ⟨j, hj⟩ := exists_chart P.A.isLB z
    obtain ⟨W, hW, hzW, hWle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show z ∈ P.L.B.U i ⊓ P.A.B.U j from ⟨hi, hj⟩)
    have hgW : genericPoint X ∈ W := gen_mem hzW
    have hsW : ∀ w ∈ W, RegAt w (P.loc e 0 x i j) := fun w hw => hx w i j (hWle hw).1 (hWle hw).2
    obtain ⟨s, hs⟩ := exists_fnOf_eq hgW hsW
    have hbas : ∀ w ∈ X.basicOpen s, w ∈ NV P e 0 x := by
      intro w hw i' j' hi' hj'
      have hwW := X.basicOpen_le s hw
      have hu : UnitAt w (P.loc e 0 x i j) := hs ▸ (unitAt_fnOf_iff hwW hgW s).2 hw
      rw [loc_change P e 0 x i i' j j']
      exact hu.mul (unitAt_quot P e 0 (hWle hwW).1 hi' (hWle hwW).2 hj')
    have hne : P.loc e 0 x i j ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx0 (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
    have hg0 : genericPoint X ∈ X.basicOpen s := by
      have hu : UnitAt (genericPoint X) (fnOf W hgW s) := by rw [hs]; exact unitAt_genericPoint hne
      exact (unitAt_fnOf_iff hgW hgW s).1 hu
    obtain ⟨N, hN⟩ := exists_pow_mul_regAt hW s hg0 (g := P.loc a b f i j) fun w hw =>
      hf w (hbas w hw) i j (hWle (X.basicOpen_le s hw)).1 (hWle (X.basicOpen_le s hw)).2
    refine ⟨W, hzW, N, fun c hc w hw i' j' hi' hj' => ?_⟩
    rw [loc_change P (e * c + a) b (x ^ c * f) i i' j j', loc_pow_mul, ← hs]
    refine RegAt.mul ?_ (unitAt_quot P _ b (hWle hw).1 hi' (hWle hw).2 hj').regAt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    have hd := regAt_fnOf hw hgW (s ^ d)
    rw [map_pow] at hd
    rw [pow_add, mul_comm (_ ^ N) (_ ^ d), mul_assoc]
    exact hd.mul (hN w hw)
  choose W hzW N hN using loc_ok
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z => (W z : Set X)) (fun z => (W z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hzW z⟩)
  refine eventually_atTop.2 ⟨t.sup N, fun c hc w i j hi hj => ?_⟩
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  exact hN z c ((Finset.le_sup hz).trans hc) w hwz i j hi hj
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.IntFib

section Dim

variable {S : Type} [TopologicalSpace S]

theorem dim_le_of_ne_univ [IrreducibleSpace S] {C : Set S} (hC : IsClosed C) (hne : C ≠ Set.univ) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim C ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : C → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  let top : IrreducibleCloseds S := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
  have hlt : q'.last < top := by
    have hsub : (q'.last : Set S) ⊆ C := by
      show closure (Subtype.val '' (q.last : Set C)) ⊆ C
      exact closure_minimal (by rintro _ ⟨t, -, rfl⟩; exact t.2) hC
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
    refine Set.eq_univ_of_univ_subset fun x _ => hsub ?_
    rw [heq]
    exact Set.mem_univ x
  have h1 := Order.LTSeries.length_le_krullDim (q'.snoc top hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

theorem dim_le_of_closedPoint_notMem [T0Space S] [CompactSpace S] {T : Set S}
    (hT : ∀ s : S, IsClosed ({s} : Set S) → s ∉ T) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim T ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : T → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  obtain ⟨t, ht⟩ := q.head.isIrreducible.nonempty
  have htm : (t : S) ∈ (q'.head : Set S) := subset_closure ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hsc⟩ := q'.head.isClosed.exists_closed_singleton ⟨_, htm⟩
  let bot : IrreducibleCloseds S := ⟨{s}, isIrreducible_singleton, hsc⟩
  have hlt : bot < q'.head := by
    refine lt_of_le_of_ne (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) fun heq => ?_
    have : (t : S) ∈ (bot : Set S) := by rw [heq]; exact htm
    have hts : (t : S) = s := this
    exact hT s hsc (hts ▸ t.2)
  have h1 := Order.LTSeries.length_le_krullDim (q'.cons bot hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

end Dim

variable {X : Scheme.{0}}

theorem ringChar_eq_zero_or_prime (x : X) :
    ringChar (X.residueField x) = 0 ∨ (ringChar (X.residueField x)).Prime :=
  (CharP.char_is_prime_or_zero (X.residueField x) _).symm

theorem natCast_eq_zero_iff (ℓ : ℕ) (x : X) :
    (ℓ : X.residueField x) = 0 ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen X x (show x ∈ (⊤ : X.Opens) from trivial)]
  simp

theorem notMem_basicOpen_of_mem_fib {ℓ : ℕ} {x : X} (hx : x ∈ fib X ℓ) :
    x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← natCast_eq_zero_iff, ringChar.spec]
  exact (show ringChar (X.residueField x) = ℓ from hx) ▸ dvd_refl _

theorem mem_fib_iff_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : X) :
    x ∈ fib X ℓ ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  refine ⟨notMem_basicOpen_of_mem_fib, fun h => ?_⟩
  rw [← natCast_eq_zero_iff, ringChar.spec] at h
  rcases hℓ.eq_one_or_self_of_dvd _ h with h1 | h1
  · have h2 : ((1 : ℕ) : X.residueField x) = 0 := (ringChar.spec _ 1).2 (by rw [h1])
    simp at h2
  · exact h1

theorem isClosed_fib {ℓ : ℕ} (hℓ : ℓ ≠ 0) : IsClosed (fib X ℓ) := by
  by_cases hp : ℓ.Prime
  · have e : fib X ℓ = ((X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) : Set X))ᶜ :=
      Set.ext fun x => mem_fib_iff_of_prime hp x
    rw [e]
    exact (X.basicOpen _).isOpen.isClosed_compl
  · have e : fib X ℓ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => by
      have hx' : ringChar (X.residueField x) = ℓ := hx
      rcases ringChar_eq_zero_or_prime x with h | h
      · exact hℓ (hx'.symm.trans h)
      · exact hp (hx' ▸ h)
    rw [e]
    exact isClosed_empty

theorem mem_fib_zero_of_specializes {x y : X} (h : x ⤳ y) (hy : y ∈ fib X 0) : x ∈ fib X 0 := by
  rcases ringChar_eq_zero_or_prime x with h0 | hp
  · exact h0
  · have hx : x ∈ fib X (ringChar (X.residueField x)) := rfl
    have hy' : ringChar (X.residueField y) = ringChar (X.residueField x) :=
      h.mem_closed (isClosed_fib hp.ne_zero) hx
    exact absurd (hy'.symm.trans hy) hp.ne_zero

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {D : ℕ}

theorem fib_ne_univ [IsIntegral X] (hX : IsArithVar p D) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : fib X ℓ ≠ Set.univ := by
  intro h
  have hb : X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) = ⊥ :=
    eq_bot_iff.2 fun x hx => (notMem_basicOpen_of_mem_fib (h.symm ▸ Set.mem_univ x : x ∈ fib X ℓ) hx).elim
  have h0 := (AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hb
  have := hX.charZero
  exact hℓ (Nat.cast_eq_zero.1 h0)

theorem closedPoint_notMem_fib_zero (hX : IsArithVar p D) (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∉ fib X 0 := by
  intro h0
  have := hX.finite_residueField hx
  exact CharP.char_ne_zero_of_finite (X.residueField x) (ringChar (X.residueField x)) h0

theorem fib_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧
      (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧
      (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧
      ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧
        W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  intro k _ X _ p D hX
  have := hX.isNoetherian
  refine ⟨fun x => ?_, fun ℓ hℓ => isClosed_fib hℓ, fun x y h hy => mem_fib_zero_of_specializes h hy,
    fun ℓ => ?_, fun W hW => ?_⟩
  · rcases ringChar_eq_zero_or_prime x with h | h
    · exact .inl h
    · exact .inr ⟨_, h, rfl⟩
  · rcases eq_or_ne ℓ 0 with rfl | hℓ
    · exact dim_le_of_closedPoint_notMem (fun s hs => closedPoint_notMem_fib_zero hX s hs) hX.dim_eq.le
    · exact dim_le_of_ne_univ (isClosed_fib hℓ) (fib_ne_univ hX hℓ) hX.dim_eq.le
  · classical
    obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hW
    let ch : Set X → ℕ := fun t =>
      if h : IsIrreducible t then ringChar (X.residueField (IsIrreducible.genericPoint h)) else 0
    refine ⟨(hTf.toFinset.image ch).filter Nat.Prime, fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2, ?_⟩
    rintro x ⟨t, ht, hxt⟩
    have hct : ch t = ringChar (X.residueField (IsIrreducible.genericPoint (hTi t ht))) := dif_pos (hTi t ht)
    have hg := IsIrreducible.isGenericPoint_genericPoint (hTi t ht) (hTc t ht)
    have hsp := hg.specializes hxt
    rcases ringChar_eq_zero_or_prime (IsIrreducible.genericPoint (hTi t ht)) with h0 | hp
    · left
      exact hsp.mem_closed isClosed_closure (subset_closure ⟨⟨t, ht, hg.mem⟩, h0⟩)
    · right
      refine Set.mem_iUnion₂.2 ⟨ch t, Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨t, hTf.mem_toFinset.2 ht, rfl⟩, hct ▸ hp⟩, ?_⟩
      exact hsp.mem_closed (isClosed_fib (hct ▸ hp.ne_zero)) hct.symm

end GlobalTheory.IntFib
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem semiPos_up_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p)
    (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  intro k _ X p D L u t h0 h1 hL hLu σ i c y hy ξ
  set f : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => (L.φ σ).φ i (c.e.symm v) with hfdef
  set g : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => u.u σ (c.e.symm v) with hgdef
  have hf : ContDiffAt ℝ 2 f (c.e y) := (L.cInf σ).contDiffAt c hy.1 hy.2
  have hfg : ContDiffAt ℝ 2 (fun v => f v + g v) (c.e y) := ((up L u).cInf σ).contDiffAt c hy.1 hy.2
  have a : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (f v : ℂ)) (c.e y) ξ).re := hL σ i c y hy ξ
  have b : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((f v + g v : ℝ) : ℂ)) (c.e y) ξ).re := hLu σ i c y hy ξ
  have e : (fun v => (((up L (u.smul t)).φ σ).φ i (c.e.symm v) : ℂ)) =
      fun v => ((((1 - t) * f v + 0) + (t * (f v + g v) + 0) : ℝ) : ℂ) := by
    funext v
    show ((((L.φ σ).φ i (c.e.symm v) + t * u.u σ (c.e.symm v)) : ℝ) : ℂ) = _
    congr 1
    simp only [hfdef, hgdef]
    ring
  rw [e, ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add, ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hf,
    ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (f := fun v => f v + g v) hfg]
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (hf.const_smul (1 - t)).add contDiffAt_const
  · exact (hfg.const_smul t).add contDiffAt_const

end GlobalTheory.HSAmp
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.projArith_residueCharFibre_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧ (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧ (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧ ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧ W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  first | exact @GlobalTheory.IntFib.fib_structure | exact GlobalTheory.IntFib.fib_structure | (intros; apply GlobalTheory.IntFib.fib_structure <;> assumption)

end
end
