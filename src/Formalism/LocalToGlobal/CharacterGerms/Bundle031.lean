module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.AbstractGermZeroCondition
public import Formalism.LocalToGlobal.CharacterGerms.Bundle013
public import Formalism.LocalToGlobal.CharacterGerms.Bundle028
import Formalism.LocalToGlobal.CharacterGerms.Bundle027
import Formalism.LocalToGlobal.CharacterGerms.Bundle009
import Formalism.LocalToGlobal.CharacterGerms.Bundle011
public import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
public import Formalism.LocalToGlobal.CharacterGerms.Bundle030
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.LocalToGlobal.CharacterGerms.GeneralGermZero
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import Formalism.LocalToGlobal.CharacterGerms.Bundle016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I0 : Type} [Fintype I0]

def SelfData.yOf {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) (χ : Fin 2 → PS C 1 dd) (x : I0) : C :=
  ∑ col, ∑ i, dlogC (χ col) i * (Y.rawSelf p).u g x (col, i)

def CharGermSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (χ : Fin 2 → PS C 1 dd), (∀ col, Y.IsChar (χ col)) →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ _ : Fin 2, I0 → MvPowerSeries I0 C),
      (∀ g, (S g).IsT (t g)) →
      upG (I := fun _ => I0) g (mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C))) ∈ IntGerm V t

namespace ChG

open VP

theorem subst_linU_linF {ι : Type} [Fintype ι] (U : ι → Fin dd → C) (y : Fin dd → C) :
    MvPowerSeries.subst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) (linF y) =
      ∑ x : ι, (∑ i, y i * U x i) • (MvPowerSeries.X x : MvPowerSeries ι C) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) :=
    VP.hs (fun i => by

      rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])

  rw [linF, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem cc_linU {ι κ : Type} [Fintype ι] (U : ι → κ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by

  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

end ChG

theorem SelfData.yOf_int {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) {χ : Fin 2 → PS C 1 dd}
    (h : ∀ col, Y.IsChar (χ col)) (x : I0) : V.Ge 0 (p.yOf g χ x) := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.Ge 0 (f i)) → V.Ge 0 (∑ i ∈ s, f i) :=
    fun s f hf => Finset.sum_induction f (fun z => V.Ge 0 z) (fun _ _ ha hb => VF.Ge.add ha hb)
      (VF.Ge.zero 0) hf
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨M, hM⟩ := p.gm_lim 0
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := VF.Ge.add h1 (p.em_int a (M r s))
    simpa using h2
  unfold SelfData.yOf
  refine hsum _ _ fun col _ => hsum _ _ fun i _ => ?_
  refine VF.Ge.mul_int ((h col).1 _) ?_
  exact VF.Ge.mul_int (hgm _ _ _) (p.e_int _ _)

open ChG VP in
theorem charGermSelf_holds : CharGermSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := GeneralGermZero.sysK_P (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y)
    (SelfConjugateGermZero.lgS_add Y p) (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  set U : I0 → Fin 2 × Fin dd → C := fun c' i => (Y.rawSelf p).u g c' i with hU
  set γ0 : MvPowerSeries I0 C := ∏ col : Fin 2, MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col)) with hγ0
  have hI : IntS V γ0 := IntS_prod _ fun col _ =>
    IntS.subst (fun i => hP0 (col, i)) (fun i => hPI (col, i)) (integralSeries_uncurry_one (hχ col).1)
  have hcol : ∀ col : Fin 2, MvPowerSeries.subst (t g) (MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col))) =
      mvExp (∑ x : I0, (∑ i, dlogC (χ col) i * U x (col, i)) • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    intro col
    rw [subst_subst (fun i => hP0 (col, i)) (ht0 g)]
    have h1 : (fun i => MvPowerSeries.subst (t g) (P (col, i))) = fun i =>
        MvPowerSeries.subst (fun k : Fin dd => ∑ c', U c' (col, k) • (MvPowerSeries.X c' : MvPowerSeries I0 C)) (e Y i) := by
      funext i
      rw [hPt (t g) (ht g) (col, i)]
      show MvPowerSeries.subst (fun k : Fin 2 × Fin dd => ∑ c', U c' k • (MvPowerSeries.X c' : MvPowerSeries I0 C))
        (MvPowerSeries.subst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.ex i))) = _
      rw [subst_subst (fun _ => cc_X _) (cc_linU U)]
      congr 1
      funext k
      rw [subst_X (cc_linU U)]
    rw [h1, ← subst_subst (cc_e Y) (fun k => cc_linU U (col, k))]
    show MvPowerSeries.subst _ (Psi Y (χ col)) = _
    rw [chi_exp Y (hχ col), subst_exp (fun k => cc_linU U (col, k)) (constantCoeff_linF _),
      subst_linU_linF (fun c' k => U c' (col, k))]
  have key : MvPowerSeries.subst (t g) γ0 =
      mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    rw [hγ0, subst_prod (ht0 g), Finset.prod_congr rfl fun col _ => hcol col,
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum Finset.univ _ (fun col _ => cc_linU (fun x (_ : Unit) => ∑ i, dlogC (χ col) i * U x (col, i)) ()),
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul]
    rfl
  refine ⟨upG (I := fun _ => I0) g γ0, ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst (I := fun _ => I0) t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section RR

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem isUnit_RR {x : V.RR} (hx : V.v (x : C) = 0) : IsUnit x := by
  have hx0 : (x : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at hx
    exact WithTop.top_ne_zero hx
  have hi : V.Ge 0 ((x : C)⁻¹) := by
    have h1 : V.v ((x : C) * (x : C)⁻¹) = 0 := by rw [mul_inv_cancel₀ hx0, V.v.map_one]
    rw [V.v.map_mul, hx, zero_add] at h1
    unfold VF.Ge
    rw [h1]
    rfl
  exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, hi⟩ : V.RR) (Subtype.ext (mul_inv_cancel₀ hx0))

theorem v_of_isUnit_RR {x : V.RR} (hx : IsUnit x) : V.v (x : C) = 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : V.v ((x : C) * (y : C)) = 0 := by
    have : (x : C) * (y : C) = 1 := congrArg Subtype.val hy
    rw [this, V.v.map_one]
  rw [V.v.map_mul] at h1
  have hx0 : (0 : WithTop ℝ) ≤ V.v (x : C) := x.2
  have hy0 : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
  exact le_antisymm (by calc V.v (x : C) ≤ V.v (x : C) + V.v (y : C) := le_add_of_nonneg_right hy0
                          _ = 0 := h1) hx0

theorem not_isUnit_l {T : Type} [CommRing T] (i0 : T →+* C) (hint : ∀ t, V.Ge 0 (i0 t)) :
    ¬ IsUnit ((V.l : ℕ) : T) := by
  intro h
  have h1 := v_of_isUnit_RR (h.map (i0.codRestrict V.RR hint))
  have h2 : (((i0.codRestrict V.RR hint) ((V.l : ℕ) : T) : V.RR) : C) = (V.l : C) := map_natCast i0 _
  rw [h2, V.v_l] at h1
  exact one_ne_zero h1

end RR

section Chart

open Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem vV_pos (T : CDVR) {t : T.V} (ht : ¬ IsUnit t) (h0 : t ≠ 0) : 0 < vV T.V (algebraMap T.V T.Fr t) := by
  unfold vV
  have hne : valV T.V (algebraMap T.V T.Fr t) ≠ 0 :=
    valV_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 h0)
  have h1 : valV T.V (algebraMap T.V T.Fr t) < 1 := by
    unfold valV
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ t).2 ((mem_maximalIdeal t).2 ht)
  have h2 : WithZero.log (valV T.V (algebraMap T.V T.Fr t)) < 0 :=
    (WithZero.log_lt_iff_lt_exp hne).2 (by simpa using h1)
  omega


variable {Xo c} in
theorem chart_ties {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hie : EmbOK T V ie)
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y) :
    (∀ t, V.Ge 0 ((ie.comp (algebraMap T.V T.Fr)) t)) ∧
    (∀ t, V.v ((ie.comp (algebraMap T.V T.Fr)) t) = 0 → IsUnit t) ∧
    (∀ i, Y.B.G.F i = MvPowerSeries.map (ie.comp (algebraMap T.V T.Fr)) (C3.FT i)) ∧
    (∀ a i, Y.B.A.act a i = MvPowerSeries.map (ie.comp (algebraMap T.V T.Fr)) (C3.actT a i)) := by
  have hl0 : ((V.l : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
  have hvl : (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) ≠ 0 := by
    intro h0
    have := hie _ hl0
    rw [map_natCast, V.v_l, h0, div_zero] at this
    simp at this
  have hvl' : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have := vV_algebraMap_nonneg T (V.l : T.V)
    rw [map_natCast] at this
    exact lt_of_le_of_ne (by exact_mod_cast this) (Ne.symm hvl)
  refine ⟨fun t => embIntSt_holds T C V ie hie t, fun t ht => ?_, fun i => ?_, fun a i => ?_⟩
  · by_contra hu
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [map_zero, V.v.map_zero] at ht
      exact WithTop.top_ne_zero ht
    have hne : algebraMap T.V T.Fr t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 ht0
    have h1 := hie _ hne
    rw [RingHom.comp_apply] at ht
    rw [ht] at h1
    have h2 : (0 : ℝ) = (vV T.V (algebraMap T.V T.Fr t) : ℝ) / (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) :=
      WithTop.coe_injective (by simpa using h1)
    have h3 : (0 : ℝ) < (vV T.V (algebraMap T.V T.Fr t) : ℝ) := by exact_mod_cast vV_pos T hu ht0
    have := div_pos h3 hvl'
    linarith
  · rw [hY.F i]
    have e : (a3B C3).G.F i = MvPowerSeries.map (algebraMap T.V T.Fr) (C3.FT i) := C3.gen.1.1 i
    rw [e]
    ext mu
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [hY.act a i]
    have e : (a3B C3).A.act a i = MvPowerSeries.map (algebraMap T.V T.Fr) (C3.actT a i) := C3.gen.1.2.1 a i
    rw [e]
    ext mu
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]




end Chart

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def EndoLogSt (Y : FBChart C V O dd) : Prop :=
  ∀ ε : Pt C 1 dd, (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)) →
    ∀ (τ : Type) [Finite τ] (a : Fin dd → MvPowerSeries τ C), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => VP.exAt Y a q.2) (ε i) =
      VP.exAt Y (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • a j) i

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

abbrev AA (r : T → ℕ) (tau : Orb → ZMod 2 → T) (N : ℕ) : Type := Fin N × Σ o, IIs r tau o

def eW (N : ℕ) : (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ≃ AA r tau N × Fin 2 where
  toFun y := ((y.1, ⟨y.2.1, y.2.2.2⟩), y.2.2.1)
  invFun z := (z.1.1, ⟨z.1.2.1, ⟨z.2, z.1.2.2⟩⟩)
  left_inv := by rintro ⟨ρ, ⟨o, ⟨g, c⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨ρ, ⟨o, c⟩⟩, g⟩; rfl

def lam (z : AA r tau N × Fin 2) : Letter T r n := ⟨tau z.1.2.1 z.1.2.2.1, z.1.2.2.2, plc (z.1.1, z.2)⟩

variable {r tau}

theorem lam_inj (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by
  rintro ⟨⟨ρ, ⟨o, ⟨t, i⟩⟩⟩, col⟩ ⟨⟨ρ', ⟨o', ⟨t', i'⟩⟩⟩, col'⟩ h
  simp only [lam, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := inj (a₁ := (o, t)) (a₂ := (o', t')) h1
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have h4 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h4
  obtain ⟨rfl, h5⟩ := h4
  have h6 := plc.injective h5
  simp only [Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rfl

variable (r tau)

def Gm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 α.2.2.1 col g

def Mm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 (α.2.2.1 + 1) col (1 - g)

variable {r tau gm}

theorem gram_matrix_mul_right (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (g g' : Fin 2) : ∑ col, Mm r tau gm α col g' * Gm r tau gm α col g = if g' = g then 1 else 0 := by
  have h := gm_hyp α.2.1 α.2.2.1 (1 - g') g
  unfold Mm Gm
  rw [h]
  clear h
  fin_cases g <;> fin_cases g' <;> simp

theorem gram_matrix_mul_left (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm r tau gm α col g = if col' = col then 1 else 0 := by
  have hAB : (Matrix.of fun g col => Mm r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1 := by
    ext g' g
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact gram_matrix_mul_right gm_hyp α g g'
  have hBA := mul_eq_one_comm.1 hAB
  have := congrFun (congrFun hBA col') col
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

variable (r tau gm)

def coS (ℓ : Letter T r n) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) : C :=
  ∑ col, if ℓ = lam r tau plc ((eW r tau N y).1, col) then Mm r tau gm (eW r tau N y).1 col (eW r tau N y).2 else 0

variable {r tau gm}

theorem coS_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α α' : AA r tau N) (col g : Fin 2) :
    coS r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm (α', g)) = if α = α' then Mm r tau gm α col g else 0 := by
  unfold coS
  rw [Equiv.apply_symm_apply]
  simp only [(lam_inj plc inj).eq_iff, Prod.mk.injEq]
  by_cases h : α = α'
  · subst h
    simp
  · simp [h]

theorem sum_coS (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm r tau gm α col g) ((eW r tau N).symm (α, g)) := by
  rw [← Equiv.sum_comp (eW r tau N).symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single α]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [coS_lam plc inj, if_pos rfl]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [coS_lam plc inj, if_neg (Ne.symm hne), h0]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem subG_X (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    subG r tau gm plc (MvPolynomial.X y) = ∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
      MvPolynomial.X (lam r tau plc ((eW r tau N y).1, col)) := by
  unfold subG
  rw [MvPolynomial.aeval_X]
  rfl

theorem back_subG (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) * MvPolynomial.X x) (subG r tau gm plc Q) = Q := by
  have h : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) *
      (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))).comp (subG r tau gm plc) =
      AlgHom.id C _ := by
    apply MvPolynomial.algHom_ext
    intro y

    rw [AlgHom.comp_apply, subG_X, map_sum, AlgHom.id_apply]
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hs : ∀ col, (∑ x, MvPolynomial.C (coS r tau gm plc (lam r tau plc ((eW r tau N y).1, col)) x) *
        (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C)) =
        ∑ g, MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :=
      fun col => sum_coS plc inj (eW r tau N y).1 col (fun c x => MvPolynomial.C c * MvPolynomial.X x) (by simp)
    simp only [hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ g, (∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
        (MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) *
          (MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :
            MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))) =
        MvPolynomial.C (if g = (eW r tau N y).2 then 1 else 0) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) := by
      intro g

      rw [← gram_matrix_mul_right gm_hyp (eW r tau N y).1 (eW r tau N y).2 g, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [map_mul]; ring
    simp only [h2]
    rw [Finset.sum_eq_single (eW r tau N y).2]
    · simp
    · intro g _ hg; simp [hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact congrArg (fun φ => φ Q) h

end Formalism.L2.FormalSeriesBounds.RF
end
end
