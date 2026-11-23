module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.Bundle002
public import Development.EtaleCohomology.EtaleTrace.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.EtaleCohomology.EtaleTrace.LKunnethCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem tors_of {l : ℕ} [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (b : ℤ_[l]) (hb : b ≠ 0)
    (w : M) (h : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] w = 0) : ∃ c : ℤ_[l], c ≠ 0 ∧ c • w = 0 := by
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] w = 0 := by
    have h2 := congrArg (fun t => (b : ℚ_[l]) • t) h
    simpa [TensorProduct.smul_tmul', hb'] using h2
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) := inferInstance
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1)).1 h1
  exact ⟨c, nonZeroDivisors.ne_zero c.2, hc⟩

theorem UpperTheory.Gal.KunnethLefschetz.qOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.QOnto := by
  unfold QOnto
  intro hI hLim l _ k _ _ hl G d e Z X p ι h n m hn U hU hprop z hz
  obtain ⟨b, x, hb, rfl⟩ := H0LimitCoherence.tensor_form l z
  have hz' : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] (pullHl l (sch.map U.ι) m 0 x) = 0 := by
    simpa [pb, pullHQ, LinearMap.baseChange_tmul] using hz
  obtain ⟨c, hc, hcx⟩ := tors_of b hb _ hz'
  have hunit : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := fun j => by
    push_cast
    exact (IsUnit.mk0 _ hl).pow j
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin : ∀ j : ℕ, Finite (Ht (l ^ j) (sch.obj Z) n 0) := fun j => by
    haveI := hne j
    haveI := hprop
    exact hI.e4 (l ^ j) k (hunit j) (ι ≫ p) n 0
  set x' : Hl l (sch.obj X) m 0 := c • x with hx'
  have hpull : pullHl l (sch.map U.ι) m 0 x' = 0 := by
    rw [hx', map_smul]; exact hcx
  have hlev : ∀ j, ∃ a, G.g j h hn a = x'.1 j := fun j => by
    have h0 : pull _ (sch.map U.ι) (tw (l ^ j) 0) m (x'.1 j) = 0 := by
      have := congrArg (fun t : Hl l (sch.obj U) m 0 => t.1 j) hpull
      exact this
    exact (G.exact j h hn U hU _).1 h0
  obtain ⟨a, ha, hfa⟩ := hLim (fun j => Ht (l ^ j) (sch.obj Z) n 0) (fun j => Ht (l ^ j) (sch.obj X) m 0)
    (fun j => red (l ^ (j + 1)) (l ^ j) _ n 0) (fun j => red (l ^ (j + 1)) (l ^ j) _ m 0)
    (fun j => G.g j h hn) (fun j a => G.red j h hn a) (fun j => x'.1 j) (fun j => x'.2 j) hlev
  let a' : Hl l (sch.obj Z) n 0 := ⟨a, ha⟩
  have hga : G.hl h hn a' = x' := Subtype.ext (funext hfa)
  refine ⟨(((b * c : ℤ_[l]) : ℚ_[l]))⁻¹ ⊗ₜ a', ?_⟩
  have hc' : (c : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  change (G.hl h hn).baseChange ℚ_[l] _ = _
  rw [LinearMap.baseChange_tmul, hga, hx', ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  have hal : algebraMap ℤ_[l] ℚ_[l] c = (c : ℚ_[l]) := rfl
  rw [hal, PadicInt.coe_mul]
  field_simp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

structure Steps : Prop where
  offEx : OffEx
  pairs : Pairs
  pn : PnFacts
  hyp : HypEmb
  cov : FinCov
  fib : FinFib
  comps : Comps
  ring : RingL
  lowT : LowTL
  ptVan : PtVanT
  low : LowL
  tower : TowerL
  aff : AffVan
  twBij : TwBij
  gysT : GysTL
  gys0 : GysinCondition
  qEasy : QEasy
  lim : LimOnto
  qOnto : QOnto
  qProj : QProj
  kunBij : KunBij
  kun : KunL
  swap : Swap
  slice : Slice
  ptInt : PtInt
  detect : DetectL
  dual : DualL
  supp : FinSupp
  cls : PnCls
  inj : InjL
  trComp : TrComp
  div : DivL
  basis : BasisOne
  top : TopPart

namespace Steps
variable (H : Steps) (hI : In) (hT : TrIn) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0)
include H hI hl

theorem low' : Low l k := H.low hI H.ptVan l k hl (H.ring hI l) (H.lowT hI l k hl)

theorem gysQ : Nonempty (GysQ k l) := by
  obtain ⟨G⟩ := H.gys0 hI H.twBij l k hl (H.tower hI l k hl) (H.gysT hI H.offEx k)
  obtain ⟨h1, h2, h3⟩ := H.qEasy l k G
  exact ⟨⟨fun h _ _ hn => G.q h hn, h1, H.qOnto hI H.lim l k hl G, h2, h3, H.qProj hI l k G⟩⟩

theorem kun' (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) : Kun l k d p :=
  H.kun l k d p (H.kunBij hI l k hl (H.ring hI l) d p hp)

theorem int_pt (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0) (hΛ : IsInt l p lam (add_zero _) Λ) (y : Pt p) :
    pb l y.1 0 (Λ (G.diag d p)) = lam (G.pt d y) • oneV l (S k) := by
  rw [H.ptInt l k hl d p hp (H.ring hI l) (H.low' hI l k hl) (H.kun' hI l k hl d p hp) lam Λ hΛ y,
    H.slice H.pairs l k hl d p hp (H.ring hI l) G y]

theorem int_one (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0)
    (hΛ : IsInt l p lam (add_zero _) Λ) : Λ (G.diag d p) = oneV l X := by
  rw [← sub_eq_zero]
  refine (H.low' hI l k hl).pts p hp.1 _ fun y => ?_
  rw [map_sub, H.int_pt hI l k hl G d p hp lam Λ hΛ y, h1, one_smul,
    (H.ring hI l).one_nat y.1 (LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)), sub_self]

include hT

theorem pt_ne (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ y : Pt p, G.pt d y ≠ 0 := by
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have := hp.1
  obtain ⟨t, U, z, hU, hz, hzU⟩ := H.cls hI H.pn H.hyp H.offEx l k hl hR hL (fun j d n hn => by
    have : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact H.aff hI H.ptVan k (l ^ j) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) d n 0 hn) ⟨G⟩ d
  obtain ⟨π, hπ, hf, hs⟩ := H.cov k d p hp hP hX
  obtain ⟨s, hs'⟩ := H.fib k p _ π hπ hf t U hU
  have hinj := H.inj hT l π hf hs (H.pn k d).2.1 (H.pn k d).2.2.1
    (LPdCut.unit_of (PNto k d) (isUnit_iff_ne_zero.2 hl)) (2 * d)
  have h0 : pb l (π ⁻¹ᵁ U).ι _ (pb l π (2 * d) z) = 0 := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply, hzU, map_zero]
  have hm := H.supp H.offEx H.pairs l k hl hR hL G d p inferInstance hp.2 s _ hs' _ h0
  by_contra hc
  have hc' : ∀ y : Pt p, G.pt d y = 0 := fun y => by_contra fun h => hc ⟨y, h⟩
  rw [Submodule.span_eq_bot.2 (by rintro _ ⟨y, rfl⟩; exact hc' y), Submodule.mem_bot] at hm
  exact hz (hinj (hm.trans (map_zero _).symm))

theorem tr_int (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam ≠ 0 ∧ ∀ y : Pt p, lam (G.pt d y) = 1 := by
  have hL := H.low' hI l k hl
  obtain ⟨y, hy⟩ := H.pt_ne hI hT l k hl G d p hp hP hX
  obtain ⟨lam, hlam⟩ : ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam (G.pt d y) = 1 := by
    obtain ⟨f, hf⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ_[l] _).1 hy)
    exact ⟨(f (G.pt d y))⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  refine ⟨lam, fun h => by simp [h] at hlam, fun y' => ?_⟩
  obtain ⟨Λ, hΛ⟩ := (H.kun' hI l k hl d p hp).int lam 0 (2 * d) (add_zero _)
  have h := hL.conn p hp.1 inferInstance (Λ (G.diag d p)) y y'
  rw [H.int_pt hI l k hl G d p hp lam Λ hΛ, H.int_pt hI l k hl G d p hp lam Λ hΛ, hlam] at h
  exact ((hL.line _).unique h rfl)

theorem detect' (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) : Detect l d X lam :=
  H.detect l k hl d p hp (H.ring hI l) (H.kun' hI l k hl d p hp) lam (G.diag d p)
    (H.swap H.pairs l k hl d p hp (H.ring hI l) G) (H.int_one hI l k hl G d p hp lam h1)

omit hl [IsAlgClosed k] in
theorem qDual : QDual := by
  intro l _ k _ _ hl d X p hp hP hX
  obtain ⟨G⟩ := H.gysQ hI l k hl
  obtain ⟨lam, h0, h1⟩ := H.tr_int hI hT l k hl G d p hp hP hX
  exact H.dual l k hl d p hp hX (H.ring hI l) (H.low' hI l k hl) lam (H.detect' hI hT l k hl G d p hp lam h1) h0

end Steps

theorem Detect.finite {l : ℕ} [Fact l.Prime] {d : ℕ} {X : Scheme.{0}} {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]}
    (h : Detect l d X lam) (n : ℤ) : FiniteDimensional ℚ_[l] (V l X n) := by
  classical
  obtain ⟨s, c, a, h⟩ := h
  refine FiniteDimensional.of_injective (LinearMap.pi fun t : Fin s =>
    if hn : n + c t = 2 * d then lam ∘ₗ (cupV l X hn).flip (a t) else 0) ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
  refine h n x fun t hn => ?_
  have := congrFun hx t
  simpa [dif_pos hn] using this

theorem Steps.qDiag (H : Steps) (hI : In) (hT : TrIn) : QDiag := by
  intro l _ k _ _ hl d X p hp hP W E π i r c hpb hi hr U hU e he hPB
  obtain ⟨G⟩ := H.gysQ hI l k hl
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have hK := H.kun' hI l k hl _ p hp
  have := hp.1
  obtain ⟨lam, h1⟩ := H.trComp H.comps H.offEx H.pairs l k hl hR G (d + 1) (fun p hp hP hX => by
    obtain ⟨lam, -, h⟩ := H.tr_int hI hT l k hl G _ p hp hP hX
    exact ⟨lam, h⟩) p hp hP
  have hD := H.detect' hI hT l k hl G _ p hp lam h1
  have := hD.finite (2 * ((d + 1 : ℕ) : ℤ))
  obtain ⟨s, a, ha⟩ := H.basis ℚ_[l] _ lam fun h0 => by
    obtain ⟨s, c, a, h⟩ := hD
    exact subsingleton_of_forall_eq 0 fun x => h _ x fun t hn => by rw [h0]; rfl
  obtain ⟨Λ, hΛ⟩ := hK.int lam 0 _ (add_zero _)
  obtain ⟨b, hb, hδ⟩ := H.top l k hl _ p hp hR hL hK lam s a ha Λ hΛ (G.diag (d + 1) p)
  rw [H.int_one hI l k hl G _ p hp lam h1 Λ hΛ] at hb
  have hr' : i ≫ π ≫ pullback.fst p p = r := by rw [← Category.assoc, hpb.w, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hΔ := (H.pairs k (d + 1) p inferInstance hp.2).1
  obtain ⟨U₀, hU₀⟩ := H.offEx.1 _ hΔ.cl
  have hUU : U = π ⁻¹ᵁ U₀ := TopologicalSpace.Opens.ext (hU.trans (H.offEx.2 _ _ _ _ hpb U₀ hU₀).symm)
  have h0 : pb l U.ι _ (pb l π _ (G.diag (d + 1) p)) = 0 := by
    rw [hUU, ← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply]
    unfold GysQ.diag GysQ.cls
    rw [dif_pos hΔ, G.off hΔ _ U₀ hU₀, map_zero]
  have hw : (2 : ℤ) + 2 * d = 2 * ((d + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨m, hm⟩ := H.div l k hl hR G p i (π ≫ pullback.fst p p) c (by rwa [Category.assoc])
    (by rw [← Category.assoc, hr']; infer_instance) U hU e he (by rwa [hr']) (2 * d) _ hw _ h0
  have key : ∀ (w : ℤ) (hw : 2 + 2 * d = w) (δ : V l (pullback p p) w) (a : Fin s → V l X w),
      pb l π _ δ = cupV l W hw e m → LinearIndependent ℚ_[l] a →
      δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w |
        ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v} →
      ∃ (δ : V l (pullback p p) (2 + 2 * d)) (m : V l W (2 * d)) (s : ℕ) (a : Fin s → V l X (2 + 2 * d)) (b : Fin s → V l X 0),
        pb l π _ δ = cupV l W rfl e m ∧ LinearIndependent ℚ_[l] a ∧ ∑ t, b t = oneV l X ∧
        δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {w : V l (pullback p p) (2 + 2 * d) |
          ∃ (n n' : ℤ) (h : n + n' = 2 + 2 * d) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ w = ext2 l p h u v} := by
    rintro _ rfl δ a h1 h2 h3
    exact ⟨δ, m, s, a, b, h1, h2, hb, h3⟩
  exact key _ hw _ a hm a.linearIndependent hδ

end UpperTheory.Gal.KunnethLefschetz
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id' (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem slice_gen {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    (y : Pt p) {a b n : ℤ} (h : a + b = n) (u : V l X a) (v : V l X b) :
    pb l (slice y) n (ext2 l p h u v) = cupV l X h u (pb l p b (pb l y.1 b v)) := by
  simp only [ext2]
  rw [R.nat (slice y) a b n h]
  have e1 : pb l (slice y) a (pb l (pullback.fst p p) a u) = u := by
    rw [← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_fst]
    exact pb_id' l X a u
  have e2 : pb l (slice y) b (pb l (pullback.snd p p) b v) = pb l p b (pb l y.1 b v) := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_snd]
  rw [e1, e2]

theorem ptInt_holds : PtInt := by
  intro l _ k _ _ hl d X p hSP R L K lam Λ hΛ y w
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunitS : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  have key : (pb l y.1 0) ∘ₗ Λ =
      (lam ∘ₗ pb l (slice y) (2 * d)).smulRight (oneV l (S k)) := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply]
    rw [slice_gen R y hab u v]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      obtain ⟨r, hr, -⟩ := L.line (pb l y.1 0 v)
      rw [hΛ.1, map_smul, hr]
      simp only [map_smul, R.one_nat p hunitS, R.mul_one X hunitX, smul_smul, smul_eq_mul]
      rw [mul_comm]
    · have hz : pb l y.1 b v = 0 := by
        rcases lt_or_gt_of_ne hb with hneg | hpos
        · haveI := L.neg (S k) b hneg
          exact Subsingleton.elim _ _
        · haveI := L.pos b hpos
          exact Subsingleton.elim _ _
      rw [hΛ.2 a b hab hb u v, map_zero, hz, map_zero, map_zero, map_zero, zero_smul]
  exact LinearMap.congr_fun key w

end UpperTheory.Gal.KunnethLefschetz
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_self (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (n : ℤ) (x : V l X n) : pb l (𝟙 X) n x = x := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem pb_comp_apply (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.swap_holds :
    UpperTheory.Gal.KunnethLefschetz.Swap := by
  intro hP l _ k _ _ hl d X p hSP hR G n w h h' x
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  have hpair := (hP k d p inferInstance hsm).1
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hu := hR.mul_one X hunit
  have key : ∀ f : pullback p p ⟶ X, pullback.diagonal p ≫ f = 𝟙 X →
      cupV l (pullback p p) h (pb l f n x) (G.diag d p) = G.g hpair h x := by
    intro f hf
    have hd : G.diag d p = G.g hpair (show (0 : ℤ) + 2 * d = 2 * d by simp) (oneV l X) := by
      simp only [GysQ.diag, GysQ.cls, dif_pos hpair]
    rw [hd, ← G.proj hpair (show n + 0 = n by simp) h (show (0 : ℤ) + 2 * d = 2 * d by simp) h,
      ← pb_comp_apply, hf, pb_self, hu]
  rw [key _ (by simp), hR.comm (pullback p p) (2 * d) n w h' h,
    key _ (by simp), Int.negOnePow_even _ ⟨d * n, by ring⟩, one_smul]
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc {l : ℕ} [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem powV_pull {l : ℕ} [Fact l.Prime] (R : Ring l) {Y X : Scheme.{0}} (f : Y ⟶ X) (hu : IsUnit (l : Γ(X, ⊤)))
    (x : V l X 2) (j : ℕ) : pb l f _ (powV l x j) = powV l (pb l f 2 x) j := by
  induction j with
  | zero => exact R.one_nat f hu
  | succ j ih =>
    change pb l f _ (cupV l X _ (powV l x j) x) = cupV l Y _ (powV l (pb l f 2 x) j) (pb l f 2 x)
    rw [R.nat, ih]

private theorem pull_onto {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (hu : IsUnit (l : Γ(W, ⊤))) (e : V l W 2) (hP : PBQ l (i ≫ s) (pb l i 2 e)) (n : ℤ) (b : V l E n) :
    ∃ m, pb l i n m = b := by
  have hle : (⊤ : Submodule ℚ_[l] (V l E n)) ≤ LinearMap.range (pb l i n) := by
    rw [← hP.span n, Submodule.span_le]
    rintro z ⟨j, a, h, u, rfl⟩
    refine ⟨cupV l W h (pb l s a u) (powV l e j), ?_⟩
    rw [R.nat, pbc, powV_pull R i hu]
  exact hle (Submodule.mem_top (x := b))

private theorem unit_eq {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (uX : IsUnit (l : Γ(X, ⊤))) (uE : IsUnit (l : Γ(E, ⊤))) (e ε : V l W 2) (u0 a v : _)
    (he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε)
    (hP : PBQ l (i ≫ s) (pb l i 2 e))
    (hav : pb l i 2 ε = pb l (i ≫ s) 2 a + cupV l E (zero_add 2) (pb l (i ≫ s) 0 v) (pb l i 2 e)) :
    cupV l X (add_zero 0) v u0 = oneV l X := by
  set ξ := pb l i 2 e with hξdef
  have h0 : ξ = cupV l E (zero_add 2) (pb l (i ≫ s) 0 u0) (pb l i 2 ε) := by
    rw [hξdef, he, R.nat, pbc]
  have h1 : ξ = pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v)) ξ := by
    conv_lhs => rw [h0, hav]
    rw [map_add (f := _), ← R.nat,
      ← R.assoc E 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat]
  have h2 : cupV l E (zero_add 2) (pb l (i ≫ s) 0 (oneV l X)) ξ = ξ := by
    rw [R.one_nat _ uX, R.one_mul E uE]
  have h3 : pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v - oneV l X)) ξ = 0 := by
    rw [map_sub, map_sub, LinearMap.sub_apply, h2, ← add_sub_assoc, ← h1, sub_self]
  have h4 := hP.indep _ _ h3
  rw [sub_eq_zero] at h4
  rw [R.comm X 0 0 0 (add_zero 0) (add_zero 0) v u0, h4]
  simp

theorem divL_holds : DivL := by
  intro l _ k _ _ hl R G W E X px i s c hpair hprop U hoff e he0 hP n w h z hz
  have hk : IsUnit (l : k) := isUnit_iff_ne_zero.2 hl
  have uX := LPdCut.unit_of px hk
  have uW := LPdCut.unit_of (s ≫ px) hk
  have uE := LPdCut.unit_of (i ≫ s ≫ px) hk
  have h02 : (0 : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 := by norm_num
  have hnw : n + 2 * ((1 : ℕ) : ℤ) = w := by push_cast; omega
  have hn2 : n + 2 = w := by omega
  obtain ⟨ε, hε⟩ : ∃ ε, G.g hpair h02 (oneV l E) = ε := ⟨_, rfl⟩
  obtain ⟨ε0, hε0⟩ := G.onto hpair h02 U hoff hprop e he0
  obtain ⟨u0, rfl⟩ := hP.zero ε0
  have he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε := by
    rw [← hε, ← G.proj hpair (add_zero 0) h02 h02 (zero_add 2), R.mul_one E uE, ← pbc, hε0]
  obtain ⟨a, v, hav⟩ := hP.two (pb l i 2 ε)
  have hunit := unit_eq R i s uX uE e ε u0 a v he hP hav
  have hε' : cupV l W (add_zero 2) e (pb l s 0 v) = ε := by
    rw [R.comm W 2 0 2 (add_zero 2) (zero_add 2), he,
      ← R.assoc W 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat, hunit,
      R.one_nat _ uX, R.one_mul W uW]
    simp
  obtain ⟨b, hb⟩ := G.onto hpair hnw U hoff hprop z hz
  obtain ⟨m', rfl⟩ := pull_onto R i s uW e hP n b
  have hz' : z = cupV l W hn2 m' ε := by
    rw [← hb, ← hε, ← G.proj hpair (add_zero n) hnw h02 hn2, R.mul_one E uE]
  refine ⟨cupV l W (zero_add n) (pb l s 0 v) m', ?_⟩
  rw [hz', ← R.assoc W 2 0 n 2 n w (add_zero 2) h (zero_add n) h, hε',
    R.comm W n 2 w hn2 h, Int.negOnePow_even _ ⟨n, by ring⟩, one_smul]

end UpperTheory.Gal.KunnethLefschetz
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem kunBij_holds : KunBij := by
  intro hIn l _ k _ _ hl hR d X p hp n
  obtain ⟨hprop, hsm⟩ := hp
  haveI := hprop
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  apply kun_bijective_of_kunIso l p p n (fun a m r h => hR.isCup _ a m r h)
  exact hIn.kun hIn.a2 hIn.a6nat hIn.a6ring hIn.a7 hIn.a8 hIn.a9 hIn.a10 hIn.a11 hIn.b1 hIn.b2
    hIn.b3 hIn.e2 hIn.e3 hIn.e4 l k (Ne.isUnit hl) p p n 0

end UpperTheory.Gal.KunnethLefschetz

end
end
