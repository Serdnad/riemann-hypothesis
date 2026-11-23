module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle030
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle040
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalRealTrivialAtCongruentFactor
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
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

theorem exists_lift_of_projective {R P V Q : Type} [CommRing R] [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup V] [Module R V] [Group Q] (act : R → Q → Q) (L : Submodule R V) (ev : P → Q) (φ : V → Q)
    (ev_add : ∀ a b, ev (a + b) = ev a * ev b) (ev_lin : ∀ (s : R) a, ev (s • a) = act s (ev a))
    (φ_add : ∀ a b, φ (a + b) = φ a * φ b) (φ_lin : ∀ (s : R) a, φ (s • a) = act s (φ a))
    (onto : ∀ a, ∃ v ∈ L, ev a = φ v) : ∃ mk : P →ₗ[R] V, ∀ a, mk a ∈ L ∧ ev a = φ (mk a) := by
  have hev0 : ev 0 = 1 := mul_left_cancel (a := ev 0) (by rw [_root_.mul_one, ← ev_add, add_zero])
  have hφ0 : φ 0 = 1 := mul_left_cancel (a := φ 0) (by rw [_root_.mul_one, ← φ_add, add_zero])

  let W : Submodule R (P × L) :=
    { carrier := {x | ev x.1 = φ (x.2 : V)}
      add_mem' := by
        rintro ⟨a, v⟩ ⟨b, w⟩ ha hb
        simp only [Set.mem_ofPred_eq, Prod.mk_add_mk, Submodule.coe_add] at *
        rw [ev_add, φ_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero]
        rw [hev0, hφ0]
      smul_mem' := by
        rintro s ⟨a, v⟩ ha
        simp only [Set.mem_ofPred_eq, Prod.smul_mk, Submodule.coe_smul] at *
        rw [ev_lin, φ_lin, ha] }
  let f : W →ₗ[R] P := (LinearMap.fst R P L).comp W.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv, he⟩ := onto a
    exact ⟨⟨(a, ⟨v, hv⟩), he⟩, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨L.subtype.comp ((LinearMap.snd R P L).comp (W.subtype.comp h)), fun a => ⟨((h a : W) : P × L).2.2, ?_⟩⟩
  have h1 : ((h a : W) : P × L).1 = a := LinearMap.congr_fun hh a
  have h2 : ev ((h a : W) : P × L).1 = φ (((h a : W) : P × L).2 : V) := (h a).2
  rw [h1] at h2
  exact h2

private theorem pv_add_siegel_theta_transformation {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (u v : Fin r → E) :
    pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  have hemb : ∀ τ : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (u + v) =
      ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u + ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := fun τ => by
    funext a
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  funext j
  simp only [pv, Function.comp_apply, Pi.add_apply, GlobalTheory.ThFr.per, hemb]
  split_ifs
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  · rw [Matrix.mulVec_add, Pi.add_apply]

theorem exists_mark : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk ∧ A.Marked mk := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  have := Dw.proj
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom ℂ y.x _ y.x_over

  obtain ⟨m, hm, c0, hc0, hmc⟩ : ∃ m ∈ l.Mb, ∃ c0 ∈ Mfr l, m + c0 = 1 := by
    have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hMC : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hex0 : A.ex 0 = 1 := mul_left_cancel (a := A.ex 0) (by rw [_root_.mul_one, ← A.ex_add, add_zero])
  have hexn : ∀ (n : ℕ) z, A.ex (n • z) = A.ex z ^ n := by
    intro n z
    induction n with
    | zero => rw [zero_smul, hex0, pow_zero]
    | succ n ih => rw [succ_nsmul, A.ex_add, ih, pow_succ]
  have hpvs : ∀ (a : E) (v : Fin r → E), pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
    fun a v => pv_smul idx x a v
  have hinj : Function.Injective (pv X idx x) := (hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.2.1
  have hsv : ∀ (s : 𝓞 E) (v : Fin r → E), s • v = (s : E) • v := fun _ _ => rfl

  let φ : (Fin r → E) → (ptO Xo y.x ⟶ Xo.univ.t.G) := fun v => A.ex (pv X idx x ((l.M : E)⁻¹ • v))
  have hφadd : ∀ u v, φ (u + v) = φ u * φ v := fun u v => by
    simp only [φ, smul_add, pv_add_siegel_theta_transformation, A.ex_add]
  have hφlin : ∀ (s : 𝓞 E) v, φ (s • v) = φ v ≫ Xo.univ.t.act.act s := fun s v => by
    simp only [φ]
    rw [← A.ex_lin, ← hpvs, hsv, smul_comm]

  have heta : ∀ a, Xo.univ.eta a = Xo.univ.eta (c0 • a) := by
    intro a
    have h1 : a = c0 • a + m • a := by rw [← add_smul, add_comm, hmc, one_smul]
    conv_lhs => rw [h1]
    rw [Xo.univ.eta_add, Xo.univ.eta_ker (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top),
      _root_.mul_one]
  have hlev : ∀ a, levPt Xo y.x a = I.ev l.M (c0 • a) := by
    intro a
    rw [levPt, heta a]
    exact hI _ (Submodule.smul_mem_smul hc0 Submodule.mem_top)
  obtain ⟨mk, hmk⟩ := exists_lift_of_projective (fun s q => q ≫ Xo.univ.t.act.act s) L
    (fun a => I.ev l.M (c0 • a)) φ (fun a b => by rw [smul_add, I.add])
    (fun s a => by rw [smul_comm c0 s a, I.lin]) hφadd hφlin (by
      intro a
      obtain ⟨z, hz⟩ := A.ex_onto (I.ev l.M (c0 • a))
      have hp : A.ex z ^ l.M = 1 := by
        rw [hz]
        exact (I.onto l.M hM0 _).mpr ⟨_, rfl⟩
      rw [← hexn] at hp
      obtain ⟨v, hv, hzv⟩ := (A.ex_ker _).mp hp
      refine ⟨v, hv, ?_⟩
      rw [← hz]
      show A.ex z = A.ex (pv X idx x ((l.M : E)⁻¹ • v))
      congr 1
      rw [hpvs, ← hzv]
      funext j
      simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
      rw [inv_mul_cancel_left₀ hMC])

  have hevmk : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), I.ev l.M a = φ (mk a) := by
    intro a ha
    rw [← hI a ha, ← (hmk a).2]
    exact hlev a

  have hdiff : ∀ u v, φ u = φ v → ∃ w ∈ L, u - v = l.M • w := by
    intro u v huv
    have h1 : φ (u - v) = 1 := by
      have h2 := hφadd (u - v) v
      rw [sub_add_cancel, huv] at h2
      exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
    obtain ⟨w, hw, hw'⟩ := (A.ex_ker _).mp h1
    refine ⟨w, hw, ?_⟩
    have h3 := hinj hw'
    rw [← h3, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hME]

  have hML : ∀ v ∈ Mfr l • L, ∃ u ∈ L, m • v = l.M • u := by
    intro v hv
    have h1 : m • v ∈ (l.Mb * Mfr l) • L := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hm hv
    rw [Mfr, l.prod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨u, hu, by rw [← hu', Nat.cast_smul_eq_nsmul]⟩
  refine ⟨mk, ⟨fun a => (hmk a).1, ?_, ?_⟩, fun a _ => (hlev a).trans (hmk a).2⟩
  · intro a ha hau
    obtain ⟨u, hu, hau⟩ := hau
    apply (I.ker l.M hM0 a).mp
    rw [hevmk a ha]
    show A.ex (pv X idx x ((l.M : E)⁻¹ • mk a)) = 1
    rw [hau, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hME]
    exact (A.ex_ker _).mpr ⟨u, hu, rfl⟩
  · intro v hv
    have hvL : v ∈ L := Submodule.smul_le_right hv
    have hp : φ v ^ l.M = 1 := by
      have h1 : l.M • pv X idx x ((l.M : E)⁻¹ • v) = pv X idx x v := by
        rw [hpvs]
        funext j
        simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
        rw [mul_inv_cancel_left₀ hMC]
      show A.ex (pv X idx x ((l.M : E)⁻¹ • v)) ^ l.M = 1
      rw [← hexn, h1]
      exact (A.ex_ker _).mpr ⟨v, hvL, rfl⟩
    obtain ⟨a0, ha0⟩ := (I.onto l.M hM0 (φ v)).mp hp
    have haM : c0 • a0 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hc0 Submodule.mem_top
    have h3 : φ (mk (c0 • a0)) = φ (c0 • v) := by
      rw [← hevmk _ haM, I.lin, ha0, hφlin]
    obtain ⟨w, hw, hw'⟩ := hdiff _ _ h3.symm
    obtain ⟨u', hu', hmv⟩ := hML v hv
    refine ⟨c0 • a0, haM, u' + w, L.add_mem hu' hw, ?_⟩
    calc v = m • v + c0 • v := by rw [← add_smul, hmc, one_smul]
      _ = mk (c0 • a0) + (l.M • u' + l.M • w) := by rw [hmv, ← hw']; abel
      _ = mk (c0 • a0) + l.M • (u' + w) := by rw [smul_add]

end GlobalTheory.Dict
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.VacEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {n : ℕ}

theorem row_mul_transpose (y : Matrix (Fin n) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (k : Fin n) : (y * γᵀ) k = γ *ᵥ y k := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem epsW_mul_transpose (w : E) (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by

  have key : ∀ k, EF X ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) (w • (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) =
      EF X (y k) (w • y k) := by
    intro k
    rw [row_mul_transpose, ← Matrix.mulVec_smul, EF_def, EF_def, hγ (y k) (w • y k)]
  unfold epsW
  simp only [key]

end GlobalTheory.SW.VacEx

namespace GlobalTheory.SW

open VacEx

theorem exists_vacua_and_multipliers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : Level X, ∃ (v₀ : Lt E r → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) ∧ ∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L) := by
  intro E _ _ _ r X g bas idx n hs hn D

  obtain ⟨-, huniq, hgrp, hlats, -, -, -⟩ :=
    GlobalTheory.T.level_structure_properties E r X g bas idx (2 * r) hs ⟨r, two_mul r⟩ D (by omega)
  obtain ⟨-, hstd, -⟩ := GlobalTheory.SW.finite_cls_and_stab E n 1 one_pos

  have hvac : ∀ L, SelfD X L → (∃ v, IsVac X bas D.w (tens (stdL E n) L) v) ∧
      ∀ v v', IsVac X bas D.w (tens (stdL E n) L) v → IsSB v' →
        (∀ y ∈ tens (stdL E n) L, epsW X D.w y • heisG X bas y v' = v') → ∃ c : ℂ, v' = c • v := by
    intro L hL
    obtain ⟨h1, h2, -, -⟩ :=
      GlobalTheory.SW.TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr L hL 1 (stdL E n) hstd
    exact ⟨h1, fun v v' hv hv' hfix => ⟨_, h2 v v' hv hv' hfix⟩⟩
  classical
  let v₀ : Lt E r → TF n g := fun L =>
    if h : ∃ v, IsVac X bas D.w (tens (stdL E n) (D.sh L)) v then h.choose else 0
  have hv₀ : ∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L) := by
    intro L hL
    have h := (hvac _ (hlats L hL).1).1
    rw [show v₀ L = h.choose from dif_pos h]
    exact h.choose_spec

  let μ : GL (Fin r) E → Lt E r → ℂ := fun γ L =>
    if h : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
        ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L)
    then h.2.choose * (((D.lam h.1.choose)⁻¹ : ℂˣ) : ℂ) else 0
  refine ⟨v₀, μ, hv₀, ?_⟩
  intro γ hγ L hL k hk
  obtain ⟨hγu, -⟩ := (hgrp γ).1 hγ
  obtain ⟨-, -, -, hmove⟩ := hlats L hL
  obtain ⟨hL', hsh⟩ := hmove γ hγ
  obtain ⟨hSB, -, hfix⟩ := hv₀ L hL
  have hv' := hv₀ _ hL'
  rw [hsh] at hv'
  have hSD' : SelfD X (mapL γ (D.sh L)) := by
    rw [← hsh]
    exact (hlats _ hL').1
  have hlaw := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu (v₀ L) hSB

  have himg : ∀ y ∈ tens (stdL E n) (mapL γ (D.sh L)),
      epsW X D.w y • heisG X bas y (wG X bas idx γ (v₀ L)) = wG X bas idx γ (v₀ L) := by
    intro y hy
    set y₀ : Matrix (Fin n) (Fin r) E := y * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ with hy₀
    have hyy : y₀ * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y := by
      rw [hy₀, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
        Matrix.mul_one]
    have hy₀m : y₀ ∈ tens (stdL E n) (D.sh L) := by
      rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
      intro k
      obtain ⟨x, hx, hxk⟩ := Submodule.mem_map.mp (hy k)
      rw [hy₀, VacEx.row_mul_transpose, ← hxk]
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
      exact hx
    have hSB0 : IsSB (heisG X bas y₀ (v₀ L)) := (GlobalTheory.SW.TensVac.laws idx hs hn y₀ hSB).1
    have hlaw0 := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu _ hSB0
    rw [← hyy, ← hlaw.2.2.2.2.2.2 y₀, VacEx.epsW_mul_transpose X D.w γ hγu y₀, ← hlaw0.2.2.2.1,
      hfix y₀ hy₀m]
  have hex : ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) :=
    (hvac _ hSD').2 _ _ hv' hlaw.1 himg
  have hcond : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
      ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) := ⟨⟨k, hk⟩, hex⟩

  have hk' : hcond.1.choose = k := Subtype.ext (huniq _ _ _ hcond.1.choose_spec hk)
  have hμ : μ γ L = hcond.2.choose * (((D.lam hcond.1.choose)⁻¹ : ℂˣ) : ℂ) := dif_pos hcond
  rw [hμ, hk', mul_assoc, Units.inv_mul, mul_one]
  exact hcond.2.choose_spec

end GlobalTheory.SW
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPoints_classicalModel_realVectorSpace : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  first | exact @GlobalTheory.KerReal.real_points | exact GlobalTheory.KerReal.real_points | (intros; apply GlobalTheory.KerReal.real_points <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completedTensorLattice_strongApprox_open_compact : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank), (Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤) → (L.FG ∧ Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤) → (∀ u, IsFinPt u → ∃ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, u - finW S T y ∈ hatA S T (tens Λ L)) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T y ∈ hatA S T (tens Λ L) ↔ y ∈ tens Λ L) ∧ (∀ u ∈ hatA S T (tens Λ L), IsFinPt u ∧ ∀ N : ℕ, 0 < N → ∃ y ∈ tens Λ L, ∃ u' ∈ hatA S T (tens Λ L), u = finW S T y + N • u') ∧ (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens Λ L), N • u ∈ U) ∧ (∀ N : ℕ, 0 < N → IsOpen {w : WO S T | ∃ u ∈ hatA S T (tens Λ L), IsRealPt (w - N • u)}) ∧ IsCompact (hatA S T (tens Λ L) : Set (WO S T)) := by
  first | exact @GlobalTheory.Ker.HatLat.hatA_tens | exact GlobalTheory.Ker.HatLat.hatA_tens | (intros; apply GlobalTheory.Ker.HatLat.hatA_tens <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_real_trivialAt_congruent_factor : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (I : Ideal (𝓞 D.host.F)) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → I ≠ ⊥ → 0 < M → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ g' ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * g' * k ∧ TrivAt V I g' ∧ TrivOff V I k ∧ CongK V L M k ∧ ∀ J : Ideal (𝓞 D.host.E), (M : 𝓞 D.host.E) ∈ J → ∀ u ∈ hatV L, fmt V k *ᵥ u - u ∈ hatV (J • L) := by
  first | exact @GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong | exact GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong | (intros; apply GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticCharacter_real_finite_points_match : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (t : D.host.F), symplO S T (ratW T S yᵀ) (ratW T S y'ᵀ) = algebraMap D.host.F (AF D.host.F) t → ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F t) ∧ (∀ w w' : WO S T, IsRealPt w → IsRealPt w' → C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ))) ∧ (∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.ψ (symplOH S T (finW S T y) (finW S T y')) = cexp (-(π * I * ((∑ k, EF C.X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ w u : WO S T, IsRealPt w → IsFinPt u → symplO S T w u = 0 ∧ symplO S T u w = 0) ∧ (∀ w : WO S T, symplO S T w w = 0) ∧ (∀ w w' w'' : WO S T, symplO S T (w + w') w'' = symplO S T w w'' + symplO S T w' w'' ∧ symplO S T w w' = -symplO S T w' w) ∧ (∀ (h : GA D S) (g : GA D T) (w w' : WO S T), symplO S T (actO S T h g w) (actO S T h g w') = symplO S T w w') ∧ ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.realPt (ratW T S yᵀ) = embR C.X y ∧ IsFinPt (finW S T y) ∧ IsRealPt (ratW T S yᵀ - finW S T y) ∧ ∀ y', finW S T (y + y') = finW S T y + finW S T y' := by
  first | exact @GlobalTheory.FormMatch.forms_match | exact GlobalTheory.FormMatch.forms_match | (intros; apply GlobalTheory.FormMatch.forms_match <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFunction_fundamentalDomain_innerProduct_basic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f, C.IsTh f → (∃ b : ℝ, ∀ w, ‖f w‖ ≤ b) ∧ (ipO μ 𝓕 f f = 0 → f = 0) ∧ ipO μ 𝓕 f f = nrm2 μ 𝓕 f ∧ ∀ f', C.IsTh f' → IntegrableOn (fun w => f w * conj (f' w)) 𝓕 μ ∧ ipO μ 𝓕 f' f = conj (ipO μ 𝓕 f f') ∧ (∀ a : ℂ, ipO μ 𝓕 (a • f) f' = a * ipO μ 𝓕 f f') ∧ (∀ f'', C.IsTh f'' → ipO μ 𝓕 (f + f') f'' = ipO μ 𝓕 f f'' + ipO μ 𝓕 f' f'') ∧ (∀ w, ipO μ 𝓕 (C.rho w f) (C.rho w f') = ipO μ 𝓕 f f') ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ p, ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f' := by
  first | exact @GlobalTheory.Ker.ScalarProduct.ip_basic | exact GlobalTheory.Ker.ScalarProduct.ip_basic | (intros; apply GlobalTheory.Ker.ScalarProduct.ip_basic <;> assumption)
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

theorem AnFib.exists_anPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  obtain ⟨-, -, -, hadj, -, hinj, hsp, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let lat : AddSubgroup (Fin g → ℂ) :=
    { carrier := {z | ∃ v ∈ L, z = pv X idx x v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, add_mem hu hv, by rw [pv, pv, pv, per_add]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by rw [pv, per_zero]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨-u, neg_mem hu, by rw [pv, pv, per_neg]; rfl⟩ }
  have hχ (v) : Function.invFun (pv X idx x) (pv X idx x v) = v := Function.leftInverse_invFun hinj v
  let Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e :=
    { e := A.ex
      lat := lat
      span := by
        rw [← (hsp L (SW.TensLat.span_of_selfD X hL)).1]
        congr 1
        ext z
        exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩⟩
      e_add := A.ex_add
      e_onto := A.ex_onto
      e_ker := A.ex_ker
      hol := fun U f => by
        obtain ⟨h1, h2⟩ := A.hol U f
        simp only [Set.mem_univ, true_and] at h1 h2
        exact ⟨h1, h2⟩
      Hm := ThFr.Hm X bas idx x
      herm := Hm_isHermitian idx hs hx
      χ := fun z => A.χ (Function.invFun (pv X idx x) z)
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ_norm := by
        rintro _ ⟨v, hv, rfl⟩
        rw [hχ]
        exact A.χ_norm v hv
      fr_per := by
        rintro _ ⟨v, hv, rfl⟩ j z hz
        rw [hχ, ← hx_eq_hermForm, ← hx_eq_hermForm]
        exact A.fr_per v hv j z hz
      lin := A.ex_lin
      adj := fun a z w => by
        rw [← hx_eq_hermForm, ← hx_eq_hermForm]
        have hb : cc (a : E) = ((H.bar a : 𝓞 E) : E) := (H.bar_eq a).symm
        have h := hadj (a : E) z w
        rw [hb] at h
        exact h
      der := A.der }
  refine ⟨Φ, fun _ => rfl, rfl, fun _ => Iff.rfl, fun z w => (hx_eq_hermForm idx x z w).symm,
    fun v _ => congrArg A.χ (hχ v), fun _ _ _ => Iff.rfl, fun k a θ => ?_⟩
  funext z
  change cexp _ * θ (z + a) = cexp _ * θ (z + a)
  congr 2
  rw [hx_eq_hermForm]
  change _ - _ * _ * hermForm (ThFr.Hm X bas idx x) a a / 2 = _
  change -(_ * _ * hermForm (ThFr.Hm X bas idx x) z a) - _ = _
  simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul, Int.cast_natCast]
  ring

end GlobalTheory.Dict
end
