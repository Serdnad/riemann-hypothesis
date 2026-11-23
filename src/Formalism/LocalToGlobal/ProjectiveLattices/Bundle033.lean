module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle002

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True

theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by

  unfold valSet
  rintro v ⟨⟨x, hx⟩, rfl⟩
  refine ⟨⟨x, ?_⟩, rfl⟩
  obtain ⟨T, io, e, h1, y, -, h2⟩ := hx
  exact ⟨T, io, e, h1, y, trivial, h2⟩

def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}

def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0

abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}

def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)

variable {Xo c}

theorem regular₂.int {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (h : regular₂ Xo c U) {a n} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n)
    (h0 : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro la v hv
  have h1 := h.1
  unfold ReciprocityTheory.ChartRestriction.G.T0.RegLaw at h1
  exact (h1.1 ⟨(a, n), hd⟩ ⟨f, hf⟩ (fun la' y => h0 la' y.1 y.2)).1 la ⟨v, hv⟩

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

namespace CurveModel

variable (M : CurveModel G la g0)

def JA : Ideal ↥M.A' :=
  Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) => (⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ : ↥M.A'))

theorem map_JA : M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) = Jid (xplus X E hM) la G.w := by
  rw [JA, Ideal.map_span, ← Set.range_comp]
  rfl

theorem bij_quot : Function.Bijective (Ideal.quotientMap (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
    (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) Ideal.le_comap_map) := by
  refine ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc M.h M.JA M.h_one (fun b => ?_) Subtype.val_injective
  obtain ⟨m, a, ha⟩ := M.loc b
  exact ⟨m, a, by rw [map_pow]; exact ha⟩

def quotEquiv : (↥M.A' ⧸ M.JA) ≃ₐ[Kp (xplus X E hM) la G.N] OsK (xplus X E hM) la G.w :=
  AlgEquiv.ofBijective
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).toAlgHom.comp
      (Ideal.quotientMapₐ (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
        (IsScalarTower.toAlgHom (Kp (xplus X E hM) la G.N) ↥M.A' ↥(Frac0 (xplus X E hM) la G.w))
        Ideal.le_comap_map))
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).bijective.comp M.bij_quot)

theorem toOsK_h : toOsK (xplus X E hM) la G.w (M.h : ↥(Frac0 (xplus X E hM) la G.w)) = 1 := by
  have h1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) - 1) ∈ Jid (xplus X E hM) la G.w := by
    rw [← M.map_JA]
    let f := algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)
    change f M.h - 1 ∈ Ideal.map f M.JA
    rw [← f.map_one, ← f.map_sub]
    exact Ideal.mem_map_of_mem f M.h_one
  have h2 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 h1
  rw [map_sub, map_one, sub_eq_zero] at h2
  exact h2

theorem fractionToIntegralSection_smul_eq (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) :
    toA0K (xplus X E hM) la G.w wF (b • n) = toOsK (xplus X E hM) la G.w b • toA0K (xplus X E hM) la G.w wF n := by
  rw [map_smul]
  exact (algebraMap_smul (OsK (xplus X E hM) la G.w) b _).symm

theorem coe_smul_base_cusp_form (b : ↥(Frac0 (xplus X E hM) la G.w)) :
    ((b • toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) =
      (b : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) := by
  rw [Submodule.coe_smul, coe_toHK0]
  rfl

theorem coe_smul' (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) : ((b • n : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) = (b : Lw (xplus X E hM) la G.w) * (n : Lw (xplus X E hM) la G.w) := by
  rw [Submodule.coe_smul]
  rfl



theorem JH_mem (z : ↥(HK (xplus X E hM) la G.w wF)) (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w wF))) :
    ∃ m : ℕ, ∃ a' ∈ M.JA, ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • z) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) •
      toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have key : ∀ r ∈ Jid (xplus X E hM) la G.w, ∀ n : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a' ∈ M.JA,
      ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • (r • n)) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro n
      obtain ⟨m, a, ha⟩ := M.base_form_local n
      refine ⟨m, ⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ * a, Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩), ?_⟩
      apply Subtype.ext
      rw [coe_smul', coe_smul', he0, coe_smul_base_cusp_form]
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_left_comm, ha]
      ring
    | zero => intro n; exact ⟨0, 0, Ideal.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx n
      obtain ⟨m', a', ha', he'⟩ := hy n
      refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
        (Ideal.mul_mem_left _ _ ha'), ?_⟩
      have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (x • n) = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
      have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (y • n) = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
      rw [add_smul, smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]
    | smul c x _ hx =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx ((c • n : ↥(HK (xplus X E hM) la G.w wF)))
      refine ⟨m, a, ha, ?_⟩
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact he
  refine Submodule.smul_induction_on hz (fun r hr n _ => key r hr n) ?_
  rintro x y ⟨m, a, ha, he⟩ ⟨m', a', ha', he'⟩
  refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
    (Ideal.mul_mem_left _ _ ha'), ?_⟩
  have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • x = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
  have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • y = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
  rw [smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]

theorem isGen (M : CurveModel G la g0) : IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have hres : resF G la g0 = toA0K (xplus X E hM) la G.w wF e0 := rfl
  unfold IsGen
  rw [hres]
  constructor
  · intro u v huv
    rw [← sub_eq_zero]
    have hw : (u - v) • toA0K (xplus X E hM) la G.w wF e0 = 0 := by rw [sub_smul]; exact sub_eq_zero.2 huv
    obtain ⟨b, hb⟩ := toOsK_surjective (xplus X E hM) la G.w (u - v)
    obtain ⟨m, a, ha⟩ := M.loc b
    have hta : toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) = u - v := by
      rw [← ha, map_mul, map_pow, M.toOsK_h, one_pow, one_mul, hb]
    rw [← hta, ← fractionToIntegralSection_smul_eq] at hw
    obtain ⟨m', a', ha', he'⟩ := M.JH_mem _ ((reduction_eq_zero_iff_mem_ideal_smul (xplus X E hM) la G.w wF _).1 hw)
    have hinj : M.h ^ m' * a = a' := by
      apply M.base_form_injective
      have := congrArg (fun n : ↥(HK (xplus X E hM) la G.w wF) => (n : Lw (xplus X E hM) la G.w)) he'
      rw [he0] at this
      simp only [coe_smul', coe_toHK0, SubmonoidClass.coe_pow] at this
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_assoc]
      exact this
    have hJ : ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
      rw [hinj, ← M.map_JA]; exact Ideal.mem_map_of_mem _ ha'
    have h0 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 hJ
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, M.toOsK_h, one_pow, one_mul] at h0
    rw [← hta]
    exact h0
  · intro n
    obtain ⟨x, rfl⟩ := reductionMap_surjective (xplus X E hM) la G.w wF n
    obtain ⟨m, a, ha⟩ := M.base_form_local x
    refine ⟨toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)), ?_⟩
    have hx : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • x) = ((a : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
      apply Subtype.ext
      rw [coe_smul', he0, coe_smul_base_cusp_form]
      simpa only [Subalgebra.coe_pow, SubmonoidClass.coe_pow] using ha
    show toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) • toA0K (xplus X E hM) la G.w wF e0 = toA0K (xplus X E hM) la G.w wF x
    rw [← fractionToIntegralSection_smul_eq, ← hx, fractionToIntegralSection_smul_eq, map_pow, M.toOsK_h, one_pow, one_smul]

end CurveModel

theorem inCurveSec (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : InCurveSecSt (E := E) G la := by
  intro y hs g0 hMod _
  obtain ⟨M⟩ := hMod
  refine ⟨?_, ?_, M.isGen⟩
  · haveI : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥M.A' ⧸ M.JA) := M.fin
    exact LinearEquiv.finiteDimensional M.quotEquiv.toLinearEquiv
  · haveI : IsReduced (↥M.A' ⧸ M.JA) := M.red
    exact isReduced_of_injective M.quotEquiv.symm.toRingHom M.quotEquiv.symm.injective

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAlg (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

theorem intAlg_zero : IntAlg (0 : Rul Xo c) := by
  intro la v hv
  simp only [valSet, Set.mem_setOf_eq] at hv
  obtain ⟨y, rfl⟩ := hv
  unfold vAtV
  obtain ⟨⟨w, q⟩, T, io, e, ho, z, hz, eta, -, hw⟩ := y
  unfold profI at hw
  obtain ⟨rfl, -⟩ := Prod.mk.inj hw
  simp [evI, evR, evalAt, nval]

theorem intAlg_add {f g : Rul Xo c} (hf : IntAlg f) (hg : IntAlg g) : IntAlg (f + g) := fun la v hv =>
  (le_min (hf la v hv) (hg la v hv)).trans ((isVal_valSet la v hv).add f g)

theorem intAlg_smul (a : 𝓞 c.F) {f : Rul Xo c} (hf : IntAlg f) : IntAlg (a • f) := fun la v hv => by
  have e : (a • f : Rul Xo c) = (a : c.F) • f := rfl
  rw [e]
  by_cases ha : (a : c.F) = 0
  · set_option synthInstance.maxHeartbeats 200000 in
      rw [ha, zero_smul, (isVal_valSet la v hv).zero]
    exact le_top
  · rw [(isVal_valSet la v hv).smul _ _ ha]
    exact add_nonneg (by exact_mod_cast vAdd_int_nonneg la ha) (hf la v hv)

theorem intAlg_span {s : Set (Rul Xo c)} (hs : ∀ f ∈ s, IntAlg f) {f : Rul Xo c}
    (hf : f ∈ Submodule.span (𝓞 c.F) s) : IntAlg f := by
  induction hf using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => exact intAlg_zero
  | add x y _ _ hx hy => exact intAlg_add hx hy
  | smul a x _ hx => exact intAlg_smul a hx


variable (Xo c) in
def RegularityR1ValuedPoints (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, IntAlg f →
    ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f

theorem ramIdx_nonneg {Ω : Type} [Field Ω] [Algebra c.F Ω] {v : AddValuation Ω (WithTop ℤ)}
    {la : HeightOneSpectrum (𝓞 c.F)} (ho : IsOver (K := c.F) v la) : 0 ≤ ramIdx (K := c.F) v la := by
  unfold ramIdx
  have hpos : ∀ n ∈ {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n}, 0 ≤ n := by
    rintro n ⟨a, ha, -, hv⟩
    have h := (ho a).mpr ha
    rw [hv] at h
    exact_mod_cast h.le
  rcases Set.eq_empty_or_nonempty
      {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n} with he | hne
  · rw [he, Int.csInf_empty]
  · exact hpos _ (Int.csInf_mem hne ⟨0, hpos⟩)

variable (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
  (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
  (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)

theorem ord_nonneg_of [Nonempty (HeightOneSpectrum (𝓞 c.F))]
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hR1 : RegularityR1ValuedPoints Xo c C cls PY lies) (hR1Q : RegularityR1Quotient Xo c C)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c} (hFs : F ∈ sec Xo c a n) (hFC : F ∈ C a n) (hF : IntAlg F)
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hd : IsNormDiscrete v)
    (hv : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    rcases hv with ⟨la, ho⟩ | ht
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho) (hR1 a n F hFC hF la y)
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      obtain ⟨la⟩ := ‹Nonempty (HeightOneSpectrum (𝓞 c.F))›
      exact hR1Q a n F hFC ⟨la, hF la⟩ q
  exact_mod_cast key

theorem mem_of_mem_span_int (S : Submodule c.F (Rul Xo c)) {s : Set (Rul Xo c)} (hs : s ⊆ S) {F : Rul Xo c}
    (hF : F ∈ Submodule.span (𝓞 c.F) s) : F ∈ S := by
  induction hF using Submodule.span_induction with
  | mem x h => exact hs h
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul a x _ hx => exact S.smul_mem (a : c.F) hx


omit δ C cls PY lies in
theorem exists_of_mem_span_valG {u : WtR E} {ι : Type} {R : ι → Rul Xo c} {x : ∀ Z : Comp Xo c, AC Z}
    (hx : x ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun _ => Algebra.toModule
      Submodule.span (𝓞 c.F) (Set.range fun k => valG h u (R k)))) :
    ∃ F ∈ Submodule.span (𝓞 c.F) (Set.range R), x = valG h u F := by
  try dsimp only at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact ⟨R k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  | zero => exact ⟨0, zero_mem _, funext fun Z => (valC_zero h u.1 u.2 Z).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨F, hF, rfl⟩ := hy
    obtain ⟨G, hG, rfl⟩ := hz
    exact ⟨F + G, add_mem hF hG, funext fun Z => (valC_add h u.1 u.2 F G Z).symm⟩
  | smul a y _ hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    refine ⟨a • F, Submodule.smul_mem _ a hF, funext fun Z => ?_⟩
    refine (Algebra.smul_def a (valG h u F Z)).trans ?_
    rw [IsScalarTower.algebraMap_apply (𝓞 c.F) c.F (AC Z)]
    exact (valC_smul_ct h u.1 u.2 (a : c.F) F Z).symm

section LawA2Of

variable [Fintype (Comp Xo c)]
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end LawA2Of

end Formalism.L2.Pj
end
end
