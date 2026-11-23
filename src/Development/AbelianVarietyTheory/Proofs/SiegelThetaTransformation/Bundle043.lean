module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle040
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_ex_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (ptO Xo x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧
      (∀ z, ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, ex (fun j => ty j (a : E) * z j) = ex z ≫ Xo.univ.t.act.act a) ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo x0 a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  refine ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, F.ex_onto i P hP, F.ex_ker i P hP, F.ex_lin i P hP, ?_⟩
  intro a ha
  exact F.ex_eta i P hP a ha



theorem uw_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = _root_.Formalism.L2.PjFree.perFr (U.X k) x v (_root_.Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = _root_.Formalism.L2.PjFree.relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hS hpv hrow x hxu
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Pm, hPm, hPer, hux, hder, hfr⟩ := W.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, hHm, -, hIm, hfrhol, hfrne, hfrg, hfr0, hfrper, hread, hFd, hmean⟩ := hfr hxu
  obtain ⟨ex, hexl, hadd, honto, hker, hlin, hmark⟩ :=
    exists_ex_transport W.F (W.ik k) Pm hPer (U.un k x).x hux

  have hPv : ∀ a, Pm a = pv (U.X k) idx x.1 (W.φ k a : Fin r → E) := fun a => funext fun j => by
    rw [hPm, hpv]
  have hφs : ∀ u ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = u := fun u hu =>
    ⟨(W.φ k).symm ⟨u, hu⟩, by simp⟩
  have hembφ : ∀ a, W.emb k a = (W.φ k a : Fin r → E) := fun a => rfl
  have hrange : ∀ z, z ∈ Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := by
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, SetLike.coe_mem _, hPv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hPv a⟩
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k
  have hrng : Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [hembφ]
      exact SetLike.coe_mem _
    · intro hv
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hembφ a⟩
  obtain ⟨-, -, -, -, hsm, -, hL, -⟩ := hx_laws E r (U.X k) W.g bas idx 0 hS ⟨0, rfl⟩ x.1 x.2

  have him : ∀ u ∈ (U.X k).Λ, ∀ v ∈ (U.X k).Λ,
      (hermForm Hm (pv (U.X k) idx x.1 u) (pv (U.X k) idx x.1 v)).im = (EF (U.X k) u v : ℝ) := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hφs u hu
    obtain ⟨b, rfl⟩ := hφs v hv
    rw [← hPv, ← hPv, hIm, ← hembφ, ← hembφ, ← hEF a b]
    norm_cast
  have hH : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w :=
    (hL (U.X k).Λ (hrng ▸ hspan)).2 Hm hHm him
  have hfun : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm z).left := funext hexl
  refine ⟨{ ex := ex
            ex_add := hadd
            ex_onto := honto
            ex_ker := fun z => (hker z).trans (hrange z)
            ex_lin := fun a z => by
              have e : (fun j => rowType (U.X k) (idx j) (a : E) * z j) =
                  fun j => _root_.Formalism.L2.PjFree.relab c σ (W.e j).1 (a : E) * z j := funext fun j => by rw [hrow]
              rw [e]
              exact hlin a z
            hol := by
              intro V f
              simp only [Set.sep_univ, hexl]
              exact ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm hPer V f
            der := fun ℓ => by
              rw [hfun]
              exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hexl]; exact hfrhol j
            fr_ne := fun j z => by simp only [hexl]; exact hfrne j z
            fr_g := fun j j' z => by simp only [hexl]; exact hfrg j j' z
            fr_0 := fun j => by simp only [hexl]; exact hfr0 j
            χ := fun v => if ‖χl (pv (U.X k) idx x.1 v)‖ = 1 then χl (pv (U.X k) idx x.1 v) else 1
            χ_norm := fun v _ => by
              try dsimp only
              split_ifs with h
              · exact h
              · simp
            fr_per := fun v hv j z hz => by
              obtain ⟨a, rfl⟩ := hφs v hv
              obtain ⟨hn, hp⟩ := hfrper a j z
              try dsimp only
              rw [← hPv, if_pos hn, ← hH, ← hH]
              exact hp (by simpa only [hexl] using hz) }, ?_, θ, ?_, ?_⟩
  · intro a ha
    have hM : pv (U.X k) idx x.1 (((l.M : E)⁻¹) • W.mark k a) = (l.M : ℂ)⁻¹ • Pm (W.F.t (W.ik k) a) := by
      funext j
      simp only [hsm, hrow, hPv, Pi.smul_apply, smul_eq_mul, map_inv₀, map_natCast]
      rfl
    exact (hmark a ha).trans (congrArg ex hM.symm)
  · intro j z pt h1 h2 h3
    rw [zpow_one]
    exact hread j z pt (h1.trans (hexl z)) h2 (by simpa only [hexl] using h3)
  · refine ⟨Pm.range, Fd, hrange, hFd, ?_⟩
    simpa only [hH] using hmean

end GlobalTheory.Dict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section Cast

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}

theorem SameSp.dmin_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (castFr h.psi x) τ i = dmin X'.Gm x ⟨τ.1, h.psi.ge τ.2⟩ i := by
  rw [← h.gm]
  rfl

theorem SameSp.castFr_mem_dom (h : SameSp X' X) {x : Frame X'.Ψ r} (hx : x ∈ X'.dom) :
    castFr h.psi x ∈ X.dom := by
  have hx' : ∀ τ : X'.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X'.p0 i * (dmin X'.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (castFr h.psi x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (castFr h.psi x) τ i).re
  intro τ
  obtain ⟨hdet, hpos⟩ := hx' ⟨τ.1, h.psi.ge τ.2⟩
  refine ⟨hdet, fun i => ?_⟩
  rw [h.dmin_castFr, ← h.p0]
  exact hpos i

theorem SameSp.EF_eq (h : SameSp X' X) (u v : Fin r → E) : EF X' u v = EF X u v := by
  rw [EF_def, EF_def, h.gm, h.ka]

private theorem GL_inv_mulVec_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    ((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((ga : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem GL_mulVec_inv_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    (ga : Matrix (Fin n) (Fin n) K) *ᵥ (((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem mem_mapL_iff (ga : GL (Fin r) E) (L : Lt E r) (v : Fin r → E) :
    v ∈ mapL ga L ↔ ∃ u ∈ L, v = (ga : Matrix (Fin r) (Fin r) E) *ᵥ u := by
  unfold mapL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩

private theorem EF_mulVec_of_isUn {Y : Data E r} {ga : GL (Fin r) E} (hga : IsUn Y ga) (u v : Fin r → E) :
    EF Y ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF Y u v := by
  rw [EF_def, EF_def, hga u v]

end Cast

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X' X : Data E r) (h : SameSp X' X) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X'.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X' bas' idx' e x L y) (ga : GL (Fin r) E), IsSympl X' bas' → IsSympl X bas → x ∈ X'.dom → SelfD X' L → IsUn X ga → (∀ v, pv X' idx' x v = pv X idx (castFr h.psi x) v) → (∀ j, rowType X' (idx' j) = rowType X (idx j)) → lact ga (castFr h.psi x) ∈ X.dom ∧ (IsUnitFr X' x → IsUnitFr X (lact ga (castFr h.psi x))) ∧ SelfD X (mapL ga L) ∧ ∃ A' : AnFib X bas idx e (lact ga (castFr h.psi x)) (mapL ga L) y, (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y.s θ) ∧ (∀ θ, MeanOne X' bas' idx' x L θ → MeanOne X bas idx (lact ga (castFr h.psi x)) (mapL ga L) θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mvMap ga mk) := by
  intro E _ _ _ H Dw l Xo c _ r g X' X h bas' idx' bas idx e x L y A ga hs' hs hxm hL hga hpv hrow
  have hx₀ : castFr h.psi x ∈ X.dom := h.castFr_mem_dom hxm
  obtain ⟨-, -, L3, -, -, -, -, L8⟩ := hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ _ hx₀
  obtain ⟨-, -, L3', -, -, -, -, -⟩ := hx_laws E r X' g bas' idx' 0 hs' ⟨0, rfl⟩ x hxm
  obtain ⟨hdom1, hpv1, hunit1, hhx1⟩ := L8 ga hga
  have pvT : ∀ u, pv X idx (lact ga (castFr h.psi x)) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) =
      pv X' idx' x u := fun u => (hpv1 u).trans (hpv u).symm
  have hxeq : ∀ z w, hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x z w := by
    intro z w
    rw [hx_eq_hermForm idx, hx_eq_hermForm idx']
    have key := hermForm_eq_of_im (ThFr.Hm X bas idx (castFr h.psi x)) (ThFr.Hm X' bas' idx' x) 1 1
      (Set.range (pv X idx (castFr h.psi x))) (span_range_pv idx hs hx₀) ?_ z w
    · simpa only [_root_.one_mul] using key
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [_root_.one_mul]
      rw [← hx_eq_hermForm idx, ← hx_eq_hermForm idx', L3 a b, ← hpv a, ← hpv b, L3' a b, h.EF_eq]
  have hxT : ∀ z w, hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x z w :=
    fun z w => (hhx1 z w).trans (hxeq z w)
  have unit0 : IsUnitFr X' x → IsUnitFr X (castFr h.psi x) := by
    unfold IsUnitFr
    intro hu τ i
    rw [h.dmin_castFr]
    exact hu _ i
  have hSD : SelfD X (mapL ga L) := by
    unfold SelfD at hL ⊢
    obtain ⟨hfg, hmem⟩ := hL
    refine ⟨hfg.map _, fun v => ?_⟩
    rw [mem_mapL_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩ w hw
      obtain ⟨u', hu', rfl⟩ := (mem_mapL_iff ga L w).1 hw
      obtain ⟨k, hk⟩ := (hmem u).1 hu u' hu'
      exact ⟨k, by rw [EF_mulVec_of_isUn hga, ← h.EF_eq]; exact hk⟩
    · intro hv
      refine ⟨((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, ?_, (GL_mulVec_inv_mulVec ga v).symm⟩
      rw [hmem]
      intro u' hu'
      obtain ⟨k, hk⟩ := hv _ ((mem_mapL_iff ga L _).2 ⟨u', hu', rfl⟩)
      refine ⟨k, ?_⟩
      rw [h.EF_eq, ← EF_mulVec_of_isUn hga (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) u',
        GL_mulVec_inv_mulVec]
      exact hk
  have hT : ∀ z, (∃ v ∈ L, z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (mem_mapL_iff ga L _).2 ⟨u, hu, rfl⟩, (pvT u).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
      exact ⟨u, hu, pvT u⟩
  refine ⟨hdom1, fun hu => hunit1 (unit0 hu), hSD, ?_⟩
  have hlin : ∀ (a : 𝓞 E) (z : Fin g → ℂ),
      A.ex (fun j => rowType X (idx j) (a : E) * z j) = A.ex z ≫ Xo.univ.t.act.act a := by
    intro a z
    have hfun : (fun j => rowType X (idx j) (a : E) * z j) =
        (fun j => rowType X' (idx' j) (a : E) * z j) := funext fun j => by rw [hrow]
    rw [hfun]
    exact A.ex_lin a z
  have hnorm : ∀ v ∈ mapL ga L, ‖A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)‖ = 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    rw [GL_inv_mulVec_mulVec]
    exact A.χ_norm u hu
  refine ⟨
    { ex := A.ex
      ex_add := A.ex_add
      ex_onto := A.ex_onto
      ex_ker := fun z => (A.ex_ker z).trans (hT z)
      ex_lin := hlin
      hol := A.hol
      der := A.der
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ := fun v => A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      χ_norm := hnorm
      fr_per := ?_ }, fun θ hθ => hθ, ?_, ?_⟩
  · intro v hv j z hz
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    simp only [GL_inv_mulVec_mulVec, pvT, hxT]
    exact A.fr_per u hu j z hz
  · intro θ hθ
    unfold MeanOne at hθ ⊢
    obtain ⟨Ag, Fd, hA, hFd, hint⟩ := hθ
    refine ⟨Ag, Fd, fun z => (hA z).trans (hT z), hFd, ?_⟩
    simp only [hxT]
    exact hint
  · intro mk hmk
    unfold AnFib.Marked at hmk ⊢
    intro a ha
    rw [hmk a ha]
    show A.ex _ = A.ex _
    congr 1
    have hmv : mvMap ga mk a = (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk a := by
      simp [mvMap, Matrix.toLin'_apply]
    rw [hmv, ← Matrix.mulVec_smul, pvT]

end GlobalTheory.Dict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.hermitianFormAtFrame_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  first | exact @GlobalTheory.Dict.hx_laws | exact GlobalTheory.Dict.hx_laws | (intros; apply GlobalTheory.Dict.hx_laws <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ip_smul_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
    {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hc : IsSB fun x => conj (ψ x) :=
    (isSB_algebra_haar_linear K κ ι ψ ψ hψ hψ).2.2.2.1
  have hp : IsSB (φ * fun x => conj (ψ x)) :=
    (isSB_algebra_haar_linear K κ ι φ _ hφ hc).2.2.1
  have hs := (isSB_algebra_haar_linear K κ ι _ _ hp hp).2.2.2.2.2.1 (a * conj b)
  have key : (fun x => (a • φ) x * conj ((b • ψ) x)) =
      (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  unfold ip
  rw [key, hs]
  rfl

theorem classSum_eq_sum {M : ℕ} [Fintype (Cls E n M)] (f : Lt E n → ℂ) :
    classSum M f = ∑ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1 := by
  unfold classSum
  exact finsum_eq_sum_of_fintype _

theorem exists_mass {M : ℕ} (hM : 0 < M) : ∃ m : ℝ, 0 < m ∧
    (∀ (f : Lt E n → ℂ) (a : ℂ), (∀ Λ ∈ Vset E n M, f Λ = a) → classSum M f = m * a) ∧
    ∀ (f : Lt E n → ℂ) (b : ℝ), (∀ Λ ∈ Vset E n M, ‖f Λ‖ ≤ b) → ‖classSum M f‖ ≤ m * b := by
  classical
  obtain ⟨hfin, hstd, hwt, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  refine ⟨∑ c : Cls E n M, wt M (Quot.out c).1, ?_, ?_, ?_⟩
  · apply Finset.sum_pos
    · intro c _
      exact (hwt _ (Quot.out c).2).2
    · exact ⟨(Quot.mk _ ⟨stdL E n, hstd⟩ : Cls E n M), Finset.mem_univ _⟩
  · intro f a hf
    rw [classSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hf _ (Quot.out c).2]
  · intro f b hf
    rw [classSum_eq_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hw := (hwt _ (Quot.out c).2).2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact mul_le_mul_of_nonneg_left (hf _ (Quot.out c).2) hw.le

theorem classSum_mul {M : ℕ} (hM : 0 < M) (f : Lt E n → ℂ) (a : ℂ) :
    classSum M f * a = classSum M fun Λ => f Λ * a := by
  classical
  have := (finite_cls_and_stab E n M hM).1
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  rw [classSum_eq_sum, classSum_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => mul_assoc _ _ _

end GlobalTheory.SW.Coef

namespace GlobalTheory.SW

open Coef

private theorem classSum_congr_of_eqOn_Vset {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n M : ℕ} {f g : Lt E n → ℂ} (h : ∀ Λ ∈ Vset E n M, f Λ = g Λ) :
    classSum M f = classSum M g := by
  unfold classSum
  exact finsum_congr fun c => by rw [h _ (Quot.out c).2]

theorem lattice_operator_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ (a θ : ℝ), 0 < a ∧ θ < 1 ∧ (∀ L ∈ 𝓛, classSum M (fun Λ => ip (Φ L Λ) (Φ L Λ)) = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ θ * a) ∧ ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, classSum M (fun Λ => ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ)) * μ γ L * conj (μ γ L') = classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) := by
  intro E _ _ _ r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hsys
  obtain ⟨m, hm, hconst, hbd⟩ := Coef.exists_mass (E := E) (n := n) hM
  obtain ⟨a, ha, hdiag, b, θ, hθ, hoff, hbt⟩ := hsys.norm
  have hma : 0 < m * a := mul_pos hm ha
  refine ⟨m * a, θ, hma, hθ, fun L hL => ?_, ?_⟩
  · have hb : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
        ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ m * a * b L L'.1 := fun L' => by
      rw [mul_assoc]
      exact hbd _ (a * b L L'.1) fun Λ hΛ => hoff L hL L'.1 L'.2.1 Λ hΛ
    have hS : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => m * a * b L L'.1 :=
      (hbt L hL).1.mul_left (m * a)
    have hT := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hS
    refine ⟨?_, hT, ?_⟩
    · rw [hconst _ (a : ℂ) fun Λ hΛ => hdiag L hL Λ hΛ]
      exact (Complex.ofReal_mul m a).symm
    · calc _ ≤ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, m * a * b L L'.1 :=
            Summable.tsum_le_tsum hb hT hS
        _ = m * a * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, b L L'.1 := tsum_mul_left
        _ ≤ m * a * θ := mul_le_mul_of_nonneg_left (hbt L hL).2 hma.le
        _ = θ * (m * a) := mul_comm _ _
  · intro γ hγ L hL L' hL'
    have hun := hsys.un γ hγ
    have key : ∀ Λ ∈ Vset E n M, ip (Φ L Λ) (Φ L' Λ) =
        ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ) * (μ γ L * conj (μ γ L')) := by
      intro Λ hΛ
      have hw := wG_laws E r X g bas idx n hs hn γ hun (Φ L Λ) (hsys.sb L hL Λ hΛ)
      rw [← (hw.2.2.1 (Φ L' Λ) (hsys.sb L' hL' Λ hΛ)).1, (hsys.mu γ hγ L hL).2 Λ hΛ,
        (hsys.mu γ hγ L' hL').2 Λ hΛ,
        Coef.ip_smul_smul (hsys.sb _ (hsys.stab γ hγ L hL) Λ hΛ)
          (hsys.sb _ (hsys.stab γ hγ L' hL') Λ hΛ)]
      ring
    rw [mul_assoc, Coef.classSum_mul hM]
    exact classSum_congr_of_eqOn_Vset fun Λ hΛ => (key Λ hΛ).symm

end GlobalTheory.SW
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.exists_symplectic_doubled_hermitian_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ), IsSympl X bas → ∃ F : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ] ((QI E r → ℚ) × (QI E r → ℚ)), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) ∧ ∀ (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) (y₁ y₂ : Fin r → E), y₁ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) → y₂ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) → (∀ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = ∑ j, (F u).2 (a, j) • Module.finBasis ℚ E j) ∧ ∀ a j, (F u).1 (a, j) = Algebra.trace ℚ E ((Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc (Module.finBasis ℚ E j)) := by
  first | exact @GlobalTheory.SW.DblLat.dbl_lat | exact GlobalTheory.SW.DblLat.dbl_lat | (intros; apply GlobalTheory.SW.DblLat.dbl_lat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completedTensorLattice_lattice_vacuum_transport : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  first | exact @GlobalTheory.TensLatMove.hatA_move | exact GlobalTheory.TensLatMove.hatA_move | (intros; apply GlobalTheory.TensLatMove.hatA_move <;> assumption)
end
