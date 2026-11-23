module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountableConjSub
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem oSmulW {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (o : 𝓞 E) (w : W) : o • w = (o : E) • w := by
  first
  | exact (algebraMap_smul E o w).symm
  | rfl
  | simp [Algebra.smul_def]

private theorem coe_ne_zero_of_ne_zero (o : 𝓞 E) (h : o ≠ 0) : (o : E) ≠ 0 := by
  intro h'
  apply h
  first
  | exact_mod_cast h'
  | exact RingOfIntegers.ext h'
  | simpa using h'

private theorem inv_smul_apply_smul_eq_of_smul_mem {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (P : Submodule (𝓞 E) S.V) (f : P →ₗ[𝓞 E] W) (u : S.V) (a b : 𝓞 E) (ha : a ≠ 0) (hb : b ≠ 0)
    (hau : a • u ∈ P) (hbu : b • u ∈ P) :
    ((a : E))⁻¹ • f ⟨a • u, hau⟩ = ((b : E))⁻¹ • f ⟨b • u, hbu⟩ := by
  have ha' := coe_ne_zero_of_ne_zero a ha
  have hb' := coe_ne_zero_of_ne_zero b hb
  have h1 : (b : E) • f ⟨a • u, hau⟩ = (a : E) • f ⟨b • u, hbu⟩ := by
    rw [← oSmulW, ← oSmulW, ← map_smul, ← map_smul]
    congr 1
    apply Subtype.ext
    exact smul_comm b a u
  calc ((a : E))⁻¹ • f ⟨a • u, hau⟩ = (((a : E))⁻¹ * ((b : E))⁻¹) • ((b : E) • f ⟨a • u, hau⟩) := by
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ hb', mul_one]
    _ = (((a : E))⁻¹ * ((b : E))⁻¹) • ((a : E) • f ⟨b • u, hbu⟩) := by rw [h1]
    _ = ((b : E))⁻¹ • f ⟨b • u, hbu⟩ := by
        rw [smul_smul, mul_comm ((a : E))⁻¹, mul_assoc, inv_mul_cancel₀ ha', mul_one]

theorem ext_lat {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (U : Submodule E S.V) (P : Submodule (𝓞 E) S.V) (hPU : ∀ x ∈ P, x ∈ U)
    (hfull : ∀ u ∈ U, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ P) (f : P →ₗ[𝓞 E] W) :
    ∃ F : U →ₗ[E] W, ∀ (x : S.V) (hx : x ∈ P), F ⟨x, hPU x hx⟩ = f ⟨x, hx⟩ := by
  classical
  choose d hd0 hdP using hfull
  have hmul : ∀ (u : S.V) (a b : 𝓞 E), a • u ∈ P → (b * a) • u ∈ P := by
    intro u a b h
    rw [mul_smul]
    exact P.smul_mem b h
  have hal : ∀ o : 𝓞 E, algebraMap (𝓞 E) E o = (o : E) := fun o => by first | rfl | simp
  refine ⟨{ toFun := fun x => ((d x.1 x.2 : E))⁻¹ • f ⟨d x.1 x.2 • x.1, hdP x.1 x.2⟩,
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    have e0 : d y.1 y.2 * d x.1 x.2 ≠ 0 := mul_ne_zero (hd0 _ _) (hd0 _ _)
    have hex : (d y.1 y.2 * d x.1 x.2) • x.1 ∈ P := hmul _ _ _ (hdP x.1 x.2)
    have hey : (d y.1 y.2 * d x.1 x.2) • y.1 ∈ P := by
      rw [mul_comm]
      exact hmul _ _ _ (hdP y.1 y.2)
    have hexy : (d y.1 y.2 * d x.1 x.2) • (x + y).1 ∈ P := by
      rw [Submodule.coe_add, smul_add]
      exact P.add_mem hex hey
    rw [inv_smul_apply_smul_eq_of_smul_mem S P f (x + y).1 _ _ (hd0 _ _) e0 (hdP _ _) hexy,
      inv_smul_apply_smul_eq_of_smul_mem S P f x.1 _ _ (hd0 _ _) e0 (hdP _ _) hex,
      inv_smul_apply_smul_eq_of_smul_mem S P f y.1 _ _ (hd0 _ _) e0 (hdP _ _) hey, ← smul_add, ← map_add]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_add, smul_add]
  · intro c x
    simp only [RingHom.id_apply]
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq' := coe_ne_zero_of_ne_zero q hq0
    have ha' := coe_ne_zero_of_ne_zero _ (hd0 x.1 x.2)
    have e0 : q * d x.1 x.2 ≠ 0 := mul_ne_zero hq0 (hd0 _ _)
    have hcq : (q * d x.1 x.2) • ((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x.1) =
        p • (d x.1 x.2 • x.1) := by
      rw [oSmulW, oSmulW, oSmulW (o := d x.1 x.2), smul_smul, smul_smul, hal, hal]
      congr 1
      push_cast
      field_simp
    have hmem : (q * d x.1 x.2) • (((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x : U) : S.V) ∈ P := by
      rw [Submodule.coe_smul, hcq]
      exact P.smul_mem p (hdP x.1 x.2)
    rw [inv_smul_apply_smul_eq_of_smul_mem S P f _ _ _ (hd0 _ _) e0 (hdP _ _) hmem]
    have hsub : (⟨(q * d x.1 x.2) • (((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x : U) : S.V), hmem⟩ : P) =
        p • ⟨d x.1 x.2 • x.1, hdP x.1 x.2⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_smul]
      exact hcq
    rw [hsub, map_smul, oSmulW (o := p), smul_smul, smul_smul, hal, hal]
    congr 1
    push_cast
    field_simp
  · intro x hx
    have h1 : (1 : 𝓞 E) • x ∈ P := by
      rw [one_smul]
      exact hx
    refine (inv_smul_apply_smul_eq_of_smul_mem S P f x _ 1 (hd0 _ _) one_ne_zero (hdP _ _) h1).trans ?_
    have h2 : (⟨(1 : 𝓞 E) • x, h1⟩ : P) = ⟨x, hx⟩ := Subtype.ext (one_smul _ x)
    rw [h2]
    simp

theorem ext_top {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (P : Submodule (𝓞 E) S.V) (hfull : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ P) (f : P →ₗ[𝓞 E] W) :
    ∃ F : S.V →ₗ[E] W, ∀ (x : S.V) (hx : x ∈ P), F x = f ⟨x, hx⟩ := by
  obtain ⟨G, hG⟩ := ext_lat S ⊤ P (fun _ _ => Submodule.mem_top) (fun u _ => hfull u) f
  refine ⟨G.comp (LinearMap.codRestrict ⊤ LinearMap.id (fun _ => Submodule.mem_top)), fun x hx => ?_⟩
  exact hG x hx

theorem dual_sum (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hSD : SD S Λ) (U : Submodule E S.V)
    (v : S.V) (hv : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ (S.hT m v)) : ∃ w ∈ Λ, v - w ∈ orth S U := by
  have hfull : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ := by
    intro u
    obtain ⟨s, hs⟩ := hΛ.fg
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s (fun x => S.hT x u)
    let P : Submodule (𝓞 E) S.V := {
      carrier := {x | IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x u)}
      zero_mem' := by simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
      add_mem' := by
        intro x y hx hy
        simpa [map_add, LinearMap.add_apply, mul_add] using hx.add hy
      smul_mem' := by
        intro c x hx
        have hc : IsIntegral ℤ (star (c : E)) := isInt_star c.2
        have := hc.mul hx
        change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT (c • x) u)
        rw [oSmul, hT_smulL]
        convert this using 1 <;> ring }
    have hsP : (s : Set S.V) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x u)
      rw [← show (b : E) = ((a : 𝓞 E) : E) * S.hT x u by simpa [Algebra.smul_def] using hb]
      exact b.2
    refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
    apply (hSD _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x u) at hxP
    rw [oSmul, map_smul, smul_eq_mul]
    exact hxP
  obtain ⟨π, hπ, hπU⟩ := retract S Λ hΛ.fg U
  let g : Λ →ₗ[𝓞 E] E := ((S.hT v).restrictScalars (𝓞 E)) ∘ₗ π
  obtain ⟨G, hG⟩ := ext_top S (W := E) Λ (fun u => hfull u) g
  obtain ⟨w, hw⟩ := riesz S G
  have hgw : ∀ (m : S.V) (hm : m ∈ Λ), S.hT m w = star (S.hT v (π ⟨m, hm⟩)) := fun m hm => by
    rw [hsw S w m, hw, hG m hm]
    rfl
  refine ⟨w, (hSD w).2 fun y hy => ?_, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => ?_⟩
  · rw [hgw y hy, hsw S (π ⟨y, hy⟩) v, star_star]
    exact hv _ (hπ ⟨y, hy⟩).1 (hπ ⟨y, hy⟩).2
  · have hm : ∀ m ∈ Λ, m ∈ U → S.hT m (v - w) = 0 := fun m hmΛ hmU => by
      rw [map_sub, hgw m hmΛ, hπU ⟨m, hmΛ⟩ hmU, hsw S m v, star_star]
      simp
    obtain ⟨d, hd, hdu⟩ := hfull u
    have h1 := hm _ hdu (by rw [oSmul]; exact U.smul_mem _ hu)
    rw [oSmul, hT_smulL] at h1
    have hd' : star ((d : E)) ≠ 0 := by
      rw [star_ne_zero]; exact coe_ne_zero hd
    exact (mul_eq_zero.1 h1).resolve_left hd'

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

section

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n r : ℕ}

theorem hJ_unitary (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = hJ ε x y := by
  delta hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem fix_span (e : Fin r → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, Q *ᵥ e a = e a) (k : ℕ) :
    ∀ x ∈ spanLt e k, Q *ᵥ x = x := by
  delta spanLt
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact he a
  | zero => exact Matrix.mulVec_zero Q
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

theorem inN_conj (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (P Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε) (he : ∀ a, P *ᵥ e a = e a) (hz : P *ᵥ z = z)
    (hg : InN ε e z g) : InN ε e z (Q * g * P) := by
  have hQv' : ∀ v, Q *ᵥ (P *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hQv : ∀ v, P *ᵥ v = v → Q *ᵥ v = v := fun v hv =>
    calc Q *ᵥ v = Q *ᵥ (P *ᵥ v) := by rw [hv]
      _ = v := hQv' v
  have hQe : ∀ a, Q *ᵥ e a = e a := fun a => hQv (e a) (he a)
  have key : ∀ (v : Fin n → ℂ) (k : ℕ), P *ᵥ v = v → (g - 1) *ᵥ v ∈ spanLt e k →
      (Q * g * P - 1) *ᵥ v ∈ spanLt e k := by
    intro v k hv hw
    have h : (Q * g * P - 1) *ᵥ v = Q *ᵥ ((g - 1) *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_sub, hQv v hv]
    rw [h, fix_span e Q hQe k _ hw]
    exact hw
  obtain ⟨⟨h1a, h1b⟩, h2⟩ := hg
  refine ⟨⟨fun a => key (e a) a (he a) (h1a a), key z r hz h1b⟩, fun y hy => ?_⟩
  have hy' : ∀ a, hJ ε (e a) (P *ᵥ y) = 0 := fun a =>
    calc hJ ε (e a) (P *ᵥ y) = hJ ε (P *ᵥ e a) (P *ᵥ y) := by rw [he a]
      _ = hJ ε (e a) y := hJ_unitary ε P hU (e a) y
      _ = 0 := hy a
  have hw := h2 (P *ᵥ y) hy'
  have h : (Q * g * P - 1) *ᵥ y = Q *ᵥ ((g - 1) *ᵥ (P *ᵥ y)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hQv' y]
  rw [h, fix_span e Q hQe r _ hw]
  exact hw

end Mat

section Grp

variable {D : D7} (X : HidaSetting D)

theorem fix_inv (s : X.B.I.Ginf) {v : InfinitePlace X.B.I.F} {x : Fin X.B.I.n → ℂ} (hx : uMat (s v) *ᵥ x = x) :
    uMat (s⁻¹ v) *ᵥ x = x := by
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  calc uMat (s⁻¹ v) *ᵥ x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ x) := by rw [hx]
    _ = x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem ninf_conj (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u))
    {r : X.B.I.Ginf} (hr : r ∈ X.NinfU u) : s⁻¹ * r * s ∈ X.NinfU u := by
  dsimp [HidaSetting.NinfU, Ninf] at hr ⊢
  intro v
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  have hmul : uMat ((s v)⁻¹ * r v * s v) = uMat (s⁻¹ v) * uMat (r v) * uMat (s v) := by
    delta uMat
    simp
  have hU : (uMat (s v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (s v) = Formalism.REAL.Jm (X.B.I.ε v) := by
    delta uMat
    first
    | exact (s v).2
    | exact (s v).1.2
    | simpa using (s v).2
  rw [hmul]
  exact inN_conj _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (uMat (r v)) h1 hU (he v) (hz v) (hr v)

theorem ninf_conj_iff (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) (r : X.B.I.Ginf) :
    r ∈ X.NinfU u ↔ s⁻¹ * r * s ∈ X.NinfU u := by
  constructor
  · exact ninf_conj X u s he hz
  · intro h
    have he' : ∀ v a, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => fix_inv X s (he v a)
    have hz' : ∀ v, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => fix_inv X s (hz v)
    have h2 := ninf_conj X u s⁻¹ he' hz' h
    simpa [mul_assoc] using h2

end Grp


open Formalism.L2.SG.TermOp.Vanish in
theorem fixNormC : FixNormC := by
  intro D X Y u u' t h hh r
  have hfe : ∀ v a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix_rv hh (basis_mem_fixedSubspace t.rep a) v
  have hfz : ∀ v, uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
    fun v => fix_rv hh (zu_mem_fixedSubspaceOfRepresentative t.rep) v
  have hfe' : ∀ v a, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix'_rv hh (ge_mem_fixedSubspace t.rep a) v
  have hfz' : ∀ v, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u') :=
    fun v => fix'_rv hh (gz_mem_fixedSubspace t.rep) v
  have e : t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 =
      (t.pt.1⁻¹ * h * t.pt.1)⁻¹ * (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * h * t.pt.1) := by group
  show (r ∈ X.NinfU u ∧ t.pt.1⁻¹ * r * t.pt.1 ∈ X.NinfU u') ↔
    (h⁻¹ * r * h ∈ X.NinfU u ∧ t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 ∈ X.NinfU u')
  rw [e, ← ninf_conj_iff X u h hfe hfz r, ← ninf_conj_iff X u' _ hfe' hfz' (t.pt.1⁻¹ * r * t.pt.1)]

end Formalism.L2.SG.CovariantRepresentation
end
end

section

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.CovariantRepresentation

theorem shiftCore : ShiftCore := by
  intro G _ _ _ _ _ _ μ _ _ R Γ _ V _ _ f Ω h ν _ hΓR hK hn hσ hne hcon hfin hleft hinv hconj hf hΩ hfi
  by_cases hV : CompleteSpace V
  · exact Formalism.L2.SG.MeasureShiftInvariance.shift_general μ R Γ f Ω h ν hΓR hK hn hσ hne hcon hfin hleft hinv hconj
      hf hΩ hfi
  · rw [integral_of_not_completeSpace hV, integral_of_not_completeSpace hV]

end Formalism.L2.SG.CovariantRepresentation
end
end
