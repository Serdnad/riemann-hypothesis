module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private lemma isIntegral_crd_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) {v : Fin r → E}
    (hv : v ∈ X.Λ) (j : Fin g ⊕ Fin g) : IsIntegral ℤ (crd X bas v j) := by

  obtain ⟨m, rfl⟩ : ∃ m, (bas m : Fin r → E) = v := ⟨bas.symm ⟨v, hv⟩, by simp⟩
  rw [← vecQ_intCast X bas m, crd_vecQ hs]
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := m j)

theorem heisG_fix_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ : TF n g, IsSB φ → ∃ N : ℕ, 0 < N ∧ ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ j : ℕ, heisG X bas (((j * N : ℕ) : E) • y) φ = φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn φ hφ
  obtain ⟨R, hR, hlev⟩ := hφ
  refine ⟨2 * R, by omega, fun y hy j => ?_⟩

  have hmem : ∀ k, (j • y) k ∈ X.Λ := fun k => nsmul_mem (hy k) j
  have hsc : (((j * (2 * R) : ℕ) : E) • y) = (2 * R) • (j • y) := by
    rw [Nat.cast_smul_eq_nsmul, smul_smul]
    congr 1
    ring
  rw [hsc, GlobalTheory.SW.TensVac.heisG_eq hs, map_nsmul, Prod.smul_fst, Prod.smul_snd,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).1,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).2]
  exact GlobalTheory.SW.TensVac.heisS_fix hlev (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inl i))
    (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inr i))

end GlobalTheory.Ker
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.TensLatMove

variable {D : D7}

def emb (D : D7) : AfE D →ₗ[D.host.F] AE D :=
  TensorProduct.map (GlobalTheory.AdelicLatMove.finIncl D) LinearMap.id

theorem emb_tmul (e : D.host.E) (α : Af D.host.F) :
    emb D (α ⊗ₜ[D.host.F] e) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e := rfl

theorem finPart_tmul (x : AF D.host.F) (e : D.host.E) :
    Formalism.L2.Theta.finPart D (x ⊗ₜ[D.host.F] e) = (sndA D.host.F x) ⊗ₜ[D.host.F] e := rfl

theorem emb_mul (a : AE D) (x : AfE D) : emb D (Formalism.L2.Theta.finPart D a * x) = a * emb D x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add (f := _), add_mul, ha, hb]
  | tmul y e =>
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add (f := _), mul_add, ha, hb]
    | tmul α f =>
      rw [finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, emb_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      exact Prod.ext (mul_zero y.1).symm rfl

def outer (S T : HSp D) (v : Fin S.rank → AfE D) (u : Fin T.rank → AfE D) : WO S T :=
  Matrix.of fun a k => emb D (u a * v k)

def outerHom (S T : HSp D) : (Fin S.rank → AfE D) →+ (Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun u => outer S T v u) (fun u u' => by
      ext i j
      simp only [outer, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]))
    (fun v v' => AddMonoidHom.ext fun u => by
      ext i j
      simp only [outer, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Matrix.of_apply, Matrix.add_apply,
        Pi.add_apply, map_add, mul_add])

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    α * β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem intAf_one : (1 : Af D.host.F) ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem outer_pure (S T : HSp D) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (α β : Af D.host.F) :
    outer S T (fun i => α ⊗ₜ[D.host.F] s i) (fun i => β ⊗ₜ[D.host.F] t i) =
      Matrix.of fun a k => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] (vecMulVec s t k a) := by
  ext a k
  simp only [outer, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, vecMulVec_apply, mul_comm (t a)]

theorem outer_mem (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank)
    (v : Fin S.rank → AfE D) (hv : v ∈ hatV Λ) (u : Fin T.rank → AfE D) (hu : u ∈ hatV L) :
    outer S T v u ∈ hatA S T (tens Λ L) := by
  change outerHom S T v u ∈ _
  induction hv using AddSubgroup.closure_induction with
  | mem s hs =>
    induction hu using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      apply AddSubgroup.subset_closure
      exact ⟨β * α, intAf_mul hβ hα, vecMulVec x y, AddSubgroup.subset_closure ⟨x, hx, y, hy, rfl⟩,
        outer_pure S T x y α β⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem hatA_le (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank) (K : AddSubgroup (WO S T))
    (hK : ∀ v ∈ hatV Λ, ∀ u ∈ hatV L, outer S T v u ∈ K) : hatA S T (tens Λ L) ≤ K := by
  rw [hatA, AddSubgroup.closure_le]
  rintro _ ⟨α, hα, y, hy, rfl⟩
  change _ ∈ K
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hy
    have e := outer_pure S T s t 1 α
    rw [mul_one] at e
    rw [← e]
    exact hK _ (AddSubgroup.subset_closure ⟨1, intAf_one, s, hs, rfl⟩) _
      (AddSubgroup.subset_closure ⟨α, hα, t, ht, rfl⟩)
  | zero =>
    convert zero_mem K using 1
    ext a k
    simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext a k
    simp [TensorProduct.tmul_add]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext a k
    simp [TensorProduct.tmul_neg]

theorem actO_outer (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (v : Fin S.rank → AfE D)
    (u : Fin T.rank → AfE D) :
    actO S T h g (outer S T v u) = outer S T (fmtC S h *ᵥ v) (fmt T g *ᵥ u) := by
  have key := GlobalTheory.AdelicLatMove.gram_mul_inv S h
  have h1 : S.gram.map (incA D) = 1 := by rw [hS, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.mul_one] at key
  ext i j
  simp only [actO, key, outer, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]

  simp only [← emb_mul, ← map_sum, mul_comm (emb D _)]
  congr 1
  simp only [fmt, fmtC, Formalism.L2.Theta.cM, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

def actHom (S T : HSp D) (h : GA D S) (g : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T h g) (fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul])

theorem mem_hatA_iff (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank)
    (L L' : Lt D.host.E T.rank) (h1 : IsMov (fmtC S h) Λ Λ') (h2 : IsMov (fmt T g) L L') (u : WO S T) :
    u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀ := by
  constructor
  · intro hu
    have := hatA_le S T Λ' L' ((hatA S T (tens Λ L)).map (actHom S T h g)) (fun v hv w hw => by
      obtain ⟨v₀, hv₀, rfl⟩ := (h1 v).1 hv
      obtain ⟨w₀, hw₀, rfl⟩ := (h2 w).1 hw
      exact ⟨_, outer_mem S T Λ L v₀ hv₀ w₀ hw₀, actO_outer S T hS h g v₀ w₀⟩) hu
    obtain ⟨u₀, hu₀, e⟩ := this
    exact ⟨u₀, hu₀, e.symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    refine hatA_le S T Λ L ((hatA S T (tens Λ' L')).comap (actHom S T h g)) (fun v hv w hw => ?_) hu
    change actO S T h g _ ∈ hatA S T (tens Λ' L')
    rw [actO_outer S T hS]
    exact outer_mem S T Λ' L' _ ((h1 _).2 ⟨v, hv, rfl⟩) _ ((h2 _).2 ⟨w, hw, rfl⟩)

theorem hatA_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  intro D S T C h g Λ Λ' L L' h1 h2
  have hΛ := mem_hatA_iff S T C.m.gS h g Λ Λ' L L' h1 h2
  refine ⟨hΛ, fun om hW f hth hlat => ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hW.om_heis h g _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e h⁻¹ g⁻¹ hh
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hW.om_heis h g _ f hth, hlat.2 e he u₀ hu₀ h0]

end GlobalTheory.TensLatMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerReal

open GlobalTheory.FockCompare

variable {D : D7}

theorem infPart_eq_zero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (a : AE D)
    (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by

  let e0 : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let e : AE D := e0 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hi : infPart D e = 1 := by
    simp only [infPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    rfl
  have hf : finPart D e = 0 := by
    simp only [finPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    exact TensorProduct.zero_tmul _ _
  have he : e * a = 0 :=
    h.ext _ (by rw [map_mul, hf, zero_mul]) fun τ => by rw [map_mul, hi, one_mul]; exact ha τ
  calc infPart D a = infPart D (e * a) := by rw [map_mul, hi, one_mul]
    _ = 0 := by rw [he, map_zero]

variable {S T : HSp D}

def realOf (C : Ctx S T) (σ : (D.what₂.Tau → ℂ) →+ AE D) : WR C.X S.rank →+ WO S T where
  toFun v := Matrix.of fun a k => σ fun τ => conj (v (C.m.e τ) k a)
  map_zero' := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((0 : WR C.X S.rank) (C.m.e τ) k a)) = 0 := by
      funext τ; simp
    show σ _ = 0
    rw [this, σ.map_zero]
  map_add' x y := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((x + y) (C.m.e τ) k a)) =
        (fun τ => conj (x (C.m.e τ) k a)) + fun τ => conj (y (C.m.e τ) k a) := by
      funext τ; simp
    show σ _ = σ _ + σ _
    rw [this, map_add σ]

theorem realPt_apply (C : Ctx S T) (w : WO S T) (s : C.X.Ψ) (k : Fin S.rank) (a : Fin T.rank) :
    C.realPt w s k a = conj (C.θ (C.m.e.symm s) (infPart D (w a k))) := rfl

theorem realPt_add (C : Ctx S T) (w w' : WO S T) : C.realPt (w + w') = C.realPt w + C.realPt w' := by
  funext s k a
  simp only [realPt_apply, Matrix.add_apply, map_add (f := _), Pi.add_apply]

theorem map_actO {B : Type} [CommRing B] (f : AE D →+* B) (h : GA D S) (g : GA D T) (w : WO S T) :
    (actO S T h g w).map f = (mt T g).map f * w.map f * (mt S h⁻¹).map f := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul]

private theorem isLineAt_apply_unique {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) {m n : ℕ}
    {τ : D.what₂.Tau} {z : Matrix (Fin m) (Fin n) ℂ} {L L' : ℝ →+ Mx D m n}
    (hL : IsLineAt θ τ z L) (hL' : IsLineAt θ τ z L') (t : ℝ) : L t = L' t := by
  unfold IsLineAt at hL hL'
  refine Matrix.ext fun a k => sub_eq_zero.mp (h.ext _ ?_ fun τ' => ?_)
  · have h1 := congrFun (congrFun (hL.2.1 t) a) k
    have h2 := congrFun (congrFun (hL'.2.1 t) a) k
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
    rw [map_sub, h1, h2, sub_zero]
  · have h1 := congrFun (congrFun (hL.2.2 t τ') a) k
    have h2 := congrFun (congrFun (hL'.2.2 t τ') a) k
    simp only [compAt, Matrix.map_apply] at h1 h2
    rw [map_sub, map_sub, h1, h2, sub_self]

theorem real_points : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  intro D S T C
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf

  have hRfin : ∀ v a k, finPart D (realOf C σ v a k) = 0 := fun v a k =>
    hσ.fin fun τ => conj (v (C.m.e τ) k a)
  have hRcomp : ∀ v a k τ, C.θ τ (infPart D (realOf C σ v a k)) = conj (v (C.m.e τ) k a) :=
    fun v a k τ => hσ.comp (fun τ => conj (v (C.m.e τ) k a)) τ
  have hRreal : ∀ v, IsRealPt (realOf C σ v) := by
    intro v
    show (realOf C σ v).map (finPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, hRfin]
    rfl
  have hReal : ∀ v, C.realPt (realOf C σ v) = v := by
    intro v
    funext s k a
    rw [realPt_apply, hRcomp]
    simp
  have hRcont : Continuous (realOf C σ) := by
    refine continuous_pi fun a => continuous_pi fun k => ?_
    exact hσ.cont.comp (continuous_pi fun τ => Complex.continuous_conj.comp
      ((continuous_apply a).comp ((continuous_apply k).comp (continuous_apply (C.m.e τ)))))
  refine ⟨realOf C σ, hRcont, ?_, fun w w' => realPt_add C w w', fun v => ⟨hRreal v, hReal v⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine continuous_pi fun s => continuous_pi fun k => continuous_pi fun a => ?_
    simp only [realPt_apply]
    exact Complex.continuous_conj.comp ((GlobalTheory.FockCompare.continuous_comp C.inf _).comp
      ((continuous_apply k).comp (continuous_apply a)))
  ·
    intro w hw
    have hw' : w.map (finPart D) = 0 := hw
    refine Matrix.ext fun a k => sub_eq_zero.mp (hσ.ext _ ?_ fun τ => ?_)
    · have h1 : finPart D (w a k) = 0 := congrArg (fun M => M a k) hw'
      rw [map_sub, hRfin, h1, sub_zero]
    · rw [map_sub, map_sub, hRcomp, realPt_apply]
      simp
  ·
    intro w
    show (w - realOf C σ (C.realPt w)).map (infPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply]
    refine infPart_eq_zero hσ _ fun τ => ?_
    rw [map_sub, map_sub, hRcomp, realPt_apply]
    simp
  ·
    intro u hu
    have hu' : u.map (infPart D) = 0 := hu
    funext s k a
    have h1 : infPart D (u a k) = 0 := by simpa using congrFun (congrFun hu' a) k
    simp [realPt_apply, h1]
  ·
    intro τ z t
    have hL : IsLineAt C.θ τ z ((realOf C σ).comp
        ((smulAddHom ℝ (WR C.X S.rank)).flip (Pi.single (C.m.e τ) fun k a => conj (z a k)))) := by
      unfold IsLineAt
      refine ⟨hRcont.comp (continuous_id.smul continuous_const), fun t => hRreal _, fun t τ' => ?_⟩
      refine Matrix.ext fun a k => ?_
      simp only [compAt, Matrix.map_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      rw [hRcomp]
      by_cases hτ : τ' = τ
      · subst hτ
        simp [Complex.real_smul]
      · simp [hτ]
    have hE : IsLineAt C.θ τ z (lineAt C.θ τ z) := by
      unfold lineAt
      exact Classical.epsilon_spec ⟨_, hL⟩
    exact isLineAt_apply_unique hσ hE hL t
  ·
    intro h g w
    refine ⟨fun hw => ?_, fun hw => ?_, fun τ => map_actO ((C.θ τ).comp (infPart D)) h g w⟩
    · have hw' : w.map (finPart D) = 0 := hw
      show (actO S T h g w).map (finPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]
    · have hw' : w.map (infPart D) = 0 := hw
      show (actO S T h g w).map (infPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.KerReal

end
end
