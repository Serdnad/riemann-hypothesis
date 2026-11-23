module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecay
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle244
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem translations_strongly_continuous :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod →
      ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧
        Continuous (fun y : G n => lT μ V y x) := by
  intro n _ _ μ _ V _ _ _ hU x
  have := (hU n μ).1
  constructor
  · let g : G n → C(G n, G n) := fun h => ⟨fun y => y * h, continuous_id.mul continuous_const⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.mul continuous_fst)
    have hm : ∀ h, MeasurePreserving (g h) μ μ := fun h => measurePreserving_mul_right μ h
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    refine key.congr fun h => ?_
    have hm' : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
    simp only [rR, dif_pos hm']
    rfl
  · let g : G n → C(G n, G n) := fun y => ⟨fun z => y⁻¹ * z, continuous_const.mul continuous_id⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)
    have hm : ∀ y, MeasurePreserving (g y) μ μ := fun y => measurePreserving_mul_left μ y⁻¹
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    exact key

end GlobalTheory.CompanionTheory.PresSobA
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem Mol_rR_eq (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hU : Unimod) (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n) :
    Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have he : MeasurableEmbedding (fun y : G n => y * h) := (Homeomorph.mulRight h).measurableEmbedding
  have h1 : Mol μ φ (⇑(rR μ V h x)) z = ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x (u * h) ∂μ := by
    unfold Mol
    refine integral_congr_ae ?_
    filter_upwards [rR_coe μ hU h x] with u hu
    rw [hu]
  rw [h1]
  unfold Mol
  rw [← hm.integral_comp he (fun u : G n => φ (z * h.val * (u⁻¹ : G n).val) • x u)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have : z * h.val * ((u * h)⁻¹ : G n).val = z * (u⁻¹ : G n).val := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [this]

end GlobalTheory.CompanionTheory.PresSobA
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Glue

variable {K : Type} [Field K]

abbrev Bi (C : Cx.{1} K) (i : ℕ) : Type 1 := Module.Basis.ofVectorSpaceIndex K (C.H i)

abbrev bas (C : Cx.{1} K) (i : ℕ) : Module.Basis (Bi C i) K (C.H i) := Module.Basis.ofVectorSpace K (C.H i)

def rep (C : Cx.{1} K) (i : ℕ) (β : Bi C i) : C.Z i :=
  (Submodule.Quotient.mk_surjective _ (bas C i β)).choose

theorem rep_cls (C : Cx.{1} K) (i : ℕ) (β : Bi C i) :
    C.cls (rep C i β).1 (rep C i β).2 = bas C i β :=
  (Submodule.Quotient.mk_surjective _ (bas C i β)).choose_spec

structure Tup (P : ℕ → Cx.{1} K) (c : ℕ) : Type 1 where
  a : ℕ
  a' : ℕ
  ha : a + a' = c
  i : ℕ
  β : Bi (P a) i

instance (P : ℕ → Cx.{1} K) (c : ℕ) : DecidableEq (Tup P c) := Classical.decEq _

def tupEquiv (P : ℕ → Cx.{1} K) (c n : ℕ) :
    {v : Tup P c × ℕ // v.2 + v.1.i = n} ≃ Σ t : Idx c n, Bi (P t.a) t.i where
  toFun v := ⟨⟨v.1.1.a, v.1.1.i, v.1.1.a', v.1.2, v.1.1.ha, by have := v.2; omega⟩, v.1.1.β⟩
  invFun u := ⟨(⟨u.1.a, u.1.a', u.1.ha, u.1.i, u.2⟩, u.1.j), by have := u.1.h; simp only; omega⟩
  left_inv := by rintro ⟨⟨⟨a, a', ha, i, β⟩, m⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, i, a', j, ha, h⟩, β⟩; rfl

theorem reidx {V U : Type 1} [DecidableEq V] [DecidableEq U] (σ : V ≃ U) (W : U → Type 1)
    [∀ u, AddCommGroup (W u)] [∀ u, Module K (W u)] :
    ∃ r : (⨁ v, W (σ v)) ≃ₗ[K] ⨁ u, W u,
      ∀ v x, r (DirectSum.lof K V (fun v => W (σ v)) v x) = DirectSum.lof K U W (σ v) x := by
  let f : (⨁ v, W (σ v)) →ₗ[K] ⨁ u, W u :=
    DirectSum.toModule K V _ fun v => DirectSum.lof K U W (σ v)
  let g : (⨁ u, W u) →ₗ[K] ⨁ v, W (σ v) :=
    DirectSum.toModule K U _ fun u =>
      (DirectSum.lof K V (fun v => W (σ v)) (σ.symm u)).comp
        ((LinearEquiv.cast (R := K) (M := W) (σ.apply_symm_apply u).symm).toLinearMap)
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, fun v x => ?_⟩
  · refine DirectSum.linearMap_ext K fun u => LinearMap.ext fun x => ?_
    have key : ∀ (u' : U) (hu : u' = u) (hh : u = u'),
        DirectSum.lof K U W u' (LinearEquiv.cast (R := K) (M := W) hh x) = DirectSum.lof K U W u x := by
      rintro _ rfl hh
      rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, g, DirectSum.toModule_lof, LinearEquiv.coe_coe]
    exact key _ (σ.apply_symm_apply u) _
  · refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun x => ?_
    have key : ∀ (v' : V) (hv : v' = v) (hh : σ v = σ v'),
        DirectSum.lof K V (fun v => W (σ v)) v' (LinearEquiv.cast (R := K) (M := W) hh x) =
          DirectSum.lof K V (fun v => W (σ v)) v x := by
      rintro _ rfl hh
      rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, g, DirectSum.toModule_lof, LinearEquiv.coe_coe]
    exact key _ (σ.symm_apply_apply v) _
  · simp only [LinearEquiv.ofLinear_apply, f, DirectSum.toModule_lof]

def KunC {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c n : ℕ) : Prop :=
  ∃ e : (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K] (T c).H n,
    ∀ (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0) (hy : (Q t.a').d t.j y = 0)
      (hz : (T c).d n ((pr t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
        (T c).cls ((pr t.ha).μ t.h x y) hz

def MvC {I : Type 1} [DecidableEq I] (k : I → ℕ) (A : I → Cx.{1} K) (T : Cx.{1} K)
    (g : ∀ (u : I) {m n : ℕ}, m + k u = n → (A u).X m →ₗ[K] T.X n) (n : ℕ) : Prop :=
  ∃ e : (⨁ v : {v : I × ℕ // v.2 + k v.1 = n}, (A v.1.1).H v.1.2) ≃ₗ[K] T.H n,
    ∀ (v : {v : I × ℕ // v.2 + k v.1 = n}) (x : (A v.1.1).X v.1.2) (hx : (A v.1.1).d v.1.2 x = 0)
      (hz : T.d n (g v.1.1 v.2 x) = 0),
      e (DirectSum.lof K _ (fun v : {v : I × ℕ // v.2 + k v.1 = n} => (A v.1.1).H v.1.2) v ((A v.1.1).cls x hx)) =
        T.cls (g v.1.1 v.2 x) hz

def gmap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c : ℕ)
    (u : Tup P c) {m n : ℕ} (h : m + u.i = n) : (Q u.a').X m →ₗ[K] (T c).X n :=
  (pr u.ha).μ (show u.i + m = n by omega) (rep (P u.a) u.i u.β).1

theorem mu_closed {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (x : C.X i) (y : D.X j)
    (hx : C.d i x = 0) (hy : D.d j y = 0) : E.d n (p.μ h x y) = 0 := by
  rw [p.leib, hx, hy]; simp

def sec (C : Cx.{1} K) (i : ℕ) : C.H i →ₗ[K] C.Z i := (bas C i).constr K (rep C i)

theorem sec_bas (C : Cx.{1} K) (i : ℕ) (β : Bi C i) : sec C i (bas C i β) = rep C i β :=
  (bas C i).constr_basis K _ _

theorem cls_sec (C : Cx.{1} K) (i : ℕ) (ξ : C.H i) : C.cls (sec C i ξ).1 (sec C i ξ).2 = ξ := by
  have : (Submodule.mkQ _ : C.Z i →ₗ[K] C.H i).comp (sec C i) = LinearMap.id := by
    refine (bas C i).ext fun β => ?_
    simp only [LinearMap.comp_apply, sec_bas, LinearMap.id_apply]
    exact rep_cls C i β
  exact LinearMap.congr_fun this ξ

def prodR {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (y : D.X j) (hy : D.d j y = 0) :
    C.H i →ₗ[K] E.H n :=
  (Submodule.mkQ _ : E.Z n →ₗ[K] E.H n).comp
    (LinearMap.codRestrict (E.Z n)
      (((p.μ h).flip y).comp ((C.Z i).subtype.comp (sec C i)))
      (fun ξ => mu_closed p h _ y (sec C i ξ).2 hy))

theorem prodR_apply {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (y : D.X j) (hy : D.d j y = 0)
    (ξ : C.H i) :
    prodR p h y hy ξ = E.cls (p.μ h (sec C i ξ).1 y) (mu_closed p h _ y (sec C i ξ).2 hy) := rfl

theorem prodR_cls {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (x : C.X i) (hx : C.d i x = 0)
    (y : D.X j) (hy : D.d j y = 0) (hz : E.d n (p.μ h x y) = 0) :
    prodR p h y hy (C.cls x hx) = E.cls (p.μ h x y) hz := by
  rw [prodR_apply, ← CrystallineSemistableComparison.P.cxcup_cls p h _ y (sec C i _).2 hy, ← CrystallineSemistableComparison.P.cxcup_cls p h x y hx hy, cls_sec]

theorem kun_iff_mv {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c n : ℕ) :
    KunC pr c n ↔ MvC (I := Tup P c) (fun u => u.i) (fun u => Q u.a') (T c) (fun u {m n} h => gmap pr c u h) n := by
  classical
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.tensor_direct_sum_basis_equiv (K := K) (J := Idx c n) (fun t => (P t.a).H t.i) (fun t => (Q t.a').H t.j)
    (fun t => Bi (P t.a) t.i) (fun t => bas (P t.a) t.i)
  obtain ⟨r, hr⟩ := reidx (K := K) (tupEquiv P c n) (fun u : (Σ t : Idx c n, Bi (P t.a) t.i) => (Q u.1.a').H u.1.j)
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(r.trans e₁.symm).trans e, ?_⟩
    rintro ⟨⟨⟨a, a', ha, i, β⟩, m⟩, h⟩ x hx hz
    have h' : i + m = n := by simpa [add_comm] using h
    have step := he ⟨a, i, a', m, ha, h'⟩ (rep (P a) i β).1 x (rep (P a) i β).2 hx hz
    have e1 := he₁ ⟨a, i, a', m, ha, h'⟩ β ((Q a').cls x hx)
    have r1 := hr ⟨(⟨a, a', ha, i, β⟩, m), h⟩ ((Q a').cls x hx)
    simp only [LinearEquiv.trans_apply]
    refine Eq.trans ?_ step
    refine congrArg e ?_
    rw [rep_cls]
    refine Eq.trans (congrArg e₁.symm r1) ?_
    exact (LinearEquiv.symm_apply_eq _).2 e1.symm
  · rintro ⟨E, hE⟩
    refine ⟨(e₁.trans r.symm).trans E, ?_⟩
    rintro ⟨a, i, a', j, ha, h⟩ x y hx hy hz
    have h' : j + i = n := by omega
    let L : (P a).H i →ₗ[K] (T c).H n :=
      ((E.toLinearMap.comp r.symm.toLinearMap).comp e₁.toLinearMap).comp
        ((DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ⟨a, i, a', j, ha, h⟩).comp
          ((TensorProduct.mk K _ _).flip ((Q a').cls y hy)))
    have hL : L = prodR (pr ha) h y hy := by
      refine (bas (P a) i).ext fun β => ?_
      have e1 := he₁ ⟨a, i, a', j, ha, h⟩ β ((Q a').cls y hy)
      have r1 := hr ⟨(⟨a, a', ha, i, β⟩, j), h'⟩ ((Q a').cls y hy)
      have hz' := mu_closed (pr ha) h _ y (rep (P a) i β).2 hy
      have E1 := hE ⟨(⟨a, a', ha, i, β⟩, j), h'⟩ y hy hz'
      have r2 := (LinearEquiv.symm_apply_eq r).2 r1.symm
      have hLb : L (bas (P a) i β) = E (r.symm (e₁ (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j)
          ⟨a, i, a', j, ha, h⟩ (bas (P a) i β ⊗ₜ (Q a').cls y hy)))) := rfl
      rw [hLb, e1]
      refine Eq.trans (congrArg E r2) (Eq.trans E1 ?_)
      rw [prodR_apply]
      simp only [sec_bas]
      rfl
    have := LinearMap.congr_fun hL ((P a).cls x hx)
    rw [prodR_cls (pr ha) h x hx y hy hz] at this
    exact this

end GlobalTheory.CompanionTheory.KunGlue.Glue

open GlobalTheory.CompanionTheory.KunGlue.Glue in
theorem GlobalTheory.CompanionTheory.KunGlue.kun_glue : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  intro hmv K _ ι _ _ P Q T pr hnat hQ hT hK c n
  have main := GlobalTheory.T.mvE_empty_of_mvE_nonempty hmv (K := K) (ι := ι) (I := Tup P c) (fun u => u.i) (fun u => (-1 : ℤˣ) ^ u.i)
    (fun u => Q u.a') (T c) (fun u S {m n} h => gmap (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha) c u h)
    ?_ ?_ (fun u => hQ _) (hT c)
    (fun S hS n => (kun_iff_mv (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha) c n).1 (hK S hS c n)) n
  · exact (kun_iff_mv (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) c n).2 main
  · intro u S m n h h' x
    simp only [gmap]
    rw [(pr S u.ha).leib, (rep (P u.a) u.i u.β).2]
    simp
  · intro u S S' hS m n h x
    exact hnat hS u.ha _ _ x
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.gelfand_value_negation : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ), (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq | exact GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq | (intros; apply GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis


theorem _root_.GlobalTheory.T.theta_sub_value_zero_rapid_decay : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℕ), ∃ M : ℝ, ∀ h ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaC F (scalC (moduleSection w t) * h) - F 0‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  first | exact @GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le | exact GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le | (intros; apply GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem crystalline_filtration_l_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0),
    (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  intro l _ A r
  induction r with
  | zero =>
    intro z _
    rw [(GlobalTheory.T.crystalline_filtration_multiplicative A).1]
    exact Submodule.mem_top
  | succ r ih =>
    intro z hz
    have hzr : z ∈ A.Fil0 r := ih z (Fil0_succ_le A r hz)
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.crystalline_graded_pieces_description A r
    obtain ⟨w, hw⟩ := h1 z hzr
    have hlw : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r ∈ A.Fil0 (r + 1) := by
      have e : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r =
          (l : A.Acr0) * z - (l : A.Acr0) * (z - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
        rw [map_mul, map_natCast]; ring
      rw [e]
      exact sub_mem hz (Ideal.mul_mem_left _ _ hw)
    have hmem : (l : A.W) * w ∈ Ideal.span {A.xi} := (h2 _).1 hlw
    have hth : (l : A.U) * A.th w = 0 := by
      rw [← map_natCast A.th, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
    have hth0 : A.th w = 0 :=
      (mem_nonZeroDivisors_iff_left.1 (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1) _ hth
    have hwx : w ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hth0
    have := add_mem hw ((h2 w).2 hwx)
    simpa using this

end GlobalTheory.CompanionTheory.PerfFil
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.existsUnique_idempotent_lift_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U), IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | exact GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogMulPf

def ratHom {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) : ℚ →+* S :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom S) (fun y => by
    have hy : (y : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    have h := hu _ (Int.natAbs_ne_zero.2 hy)
    rcases Int.natAbs_eq (y : ℤ) with e | e
    · rw [e]; simpa using h
    · rw [e]; simpa using h)

theorem inv_smul_eq {S : Type} [CommRing S] [Algebra ℚ S] (m : ℕ) (hm : m ≠ 0) (x : S) :
    ((m : ℚ)⁻¹) • x = Ring.inverse (m : S) * x := by
  have h1 : (m : S) * algebraMap ℚ S (m : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ S), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]
  have h : IsUnit (m : S) := IsUnit.of_mul_eq_one _ h1
  apply h.mul_left_cancel
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, h1, Ring.mul_inverse_cancel _ h]

theorem core (hLA : LogAlg) {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) (T : Subring S) (x y : S)
    (hx : ∀ k : ℕ, Ring.inverse (k.factorial : S) * x ^ k ∈ T)
    (hy : ∀ k : ℕ, Ring.inverse (k.factorial : S) * y ^ k ∈ T) :
    (∀ k : ℕ, Ring.inverse (k.factorial : S) * (x + y + x * y) ^ k ∈ T) ∧ ∀ N : ℕ, ∃ c ∈ T,
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) *
          (Ring.inverse ((k + 1).factorial : S) * (x + y + x * y) ^ (k + 1)) =
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * x ^ (k + 1)) +
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * y ^ (k + 1)) +
          (N.factorial : S) * c := by
  letI : Algebra ℚ S := (ratHom hu).toAlgebra
  have e : ∀ (k : ℕ) (z : S), ((k.factorial : ℚ)⁻¹) • z ^ k = Ring.inverse (k.factorial : S) * z ^ k :=
    fun k z => inv_smul_eq _ k.factorial_ne_zero _
  have := hLA S T (fun k z => ((k.factorial : ℚ)⁻¹) • z ^ k) (fun _ _ => rfl) x y
    (fun k => by simp only [e]; exact hx k) (fun k => by simp only [e]; exact hy k)
  simpa only [e] using this

theorem sum_eq_of_coe {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (T : Subalgebra R S) (f f' f'' : ℕ → T)
    (N : ℕ) (c : T)
    (e : ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f'' (k + 1) : S) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f (k + 1) : S) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f' (k + 1) : S) + (N.factorial : S) * (c : S)) :
    ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f'' (k + 1) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f (k + 1) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f' (k + 1) + (N.factorial : T) * c := by
  apply Subtype.ext
  push_cast
  exact e

variable {l : ℕ} [Fact l.Prime]

theorem factorial_acr (A : PAlg l) (n : ℕ) : (((l * n).factorial : ℕ) : A.Acr n) = 0 := by
  obtain ⟨d, hd⟩ := ACris.pow_dvd_factorial (p := l) (le_refl (l * n))
  rw [hd, Nat.cast_mul, Nat.cast_pow, A.pow_l_acr, zero_mul]

theorem isLog_mul (hLA : LogAlg) (A : PAlg l) (n : ℕ) (w w' : A.W) (y y' : A.Acr n)
    (hy : IsLog A n w y) (hy' : IsLog A n w' y') : IsLog A n (w * w') (y + y') := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have hab : algebraMap A.W (WL l A.A) (w * w' - 1) =
      algebraMap A.W (WL l A.A) (w - 1) + algebraMap A.W (WL l A.A) (w' - 1) +
        algebraMap A.W (WL l A.A) (w - 1) * algebraMap A.W (WL l A.A) (w' - 1) := by
    simp only [map_sub, map_mul, map_one]; ring
  obtain ⟨hT, hN⟩ := core hLA (fun m hm => A.isUnit_natCast hm) A.Acr0.toSubring
    (algebraMap A.W (WL l A.A) (w - 1)) (algebraMap A.W (WL l A.A) (w' - 1))
    (fun k => by have h := (g k).2; rw [hg k] at h; exact h)
    (fun k => by have h := (g' k).2; rw [hg' k] at h; exact h)
  have hmem : ∀ k, dpw k (w * w' - 1) ∈ A.Acr0 := fun k => by
    rw [dpw, hab]; exact hT k
  obtain ⟨c, hc, e⟩ := hN (l * n)
  refine ⟨fun k => ⟨dpw k (w * w' - 1), hmem k⟩, fun _ => rfl, ?_⟩
  have e0 := sum_eq_of_coe A.Acr0 g g' (fun k => ⟨dpw k (w * w' - 1), hmem k⟩) (l * n) ⟨c, hc⟩ (by
    simp only [hg, hg']
    simp only [dpw, hab]
    exact e)
  have e1 := congrArg (A.mkAcr n) e0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at e1
  rw [e1, factorial_acr, zero_mul, add_zero]

theorem logMul : CrystallineSemistableComparison.E.LogAlg → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul :=
  fun h _ _ _ A n w w' y y' _ _ hy hy' => isLog_mul h A n w w' y y' hy hy'

end GlobalTheory.CompanionTheory.LogMulPf
end
end
