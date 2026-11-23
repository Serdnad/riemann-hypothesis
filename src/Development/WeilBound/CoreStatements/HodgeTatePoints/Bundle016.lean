module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

variable {R : Type} [CommRing R] {d : ℕ}

def Z {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

def ZZ {m n : ℕ} (b : Fin m → Pt R n d) : Prop := ∀ j i, constantCoeff (b j i) = 0

def evP {m n : ℕ} (b : Fin m → Pt R n d) (a : Pt R m d) : Pt R n d := fun i => ev b (a i)

def evV {l m n : ℕ} (b : Fin m → Pt R n d) (a : Fin l → Pt R m d) : Fin l → Pt R n d := fun j => evP b (a j)

theorem ZZ_nil {n : ℕ} : ZZ (![] : Fin 0 → Pt R n d) := fun j => j.elim0

theorem ZZ_cons {m n : ℕ} {p : Pt R n d} {u : Fin m → Pt R n d} (hp : Z p) (hu : ZZ u) :
    ZZ (Matrix.vecCons p u) := fun j => Fin.cases hp (fun j => hu j) j

theorem Z_pt {n : ℕ} (j : Fin n) : Z (pt R d j) := fun i => by simp [pt]

theorem Z_zero {n : ℕ} : Z (0 : Pt R n d) := fun i => by simp

theorem cc_ev {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) {f : PS R m d}
    (hf : constantCoeff f = 0) : constantCoeff (ev b f) = 0 :=
  constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => b p.1 p.2) (hasSubst_ev b hb)
    (fun p => hb p.1 p.2) hf

theorem Z_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : Z φ) (ha : Z a) : Z (comp1 φ a) :=
  fun i => cc_ev (ZZ_cons ha ZZ_nil) (hφ i)

theorem Z_add {n : ℕ} (G : FGLaw R d) {a b : Pt R n d} (ha : Z a) (hb : Z b) : Z (addOf G.F a b) :=
  fun i => cc_ev (ZZ_cons ha (ZZ_cons hb ZZ_nil)) (G.const i)

theorem Z_act {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (a : O) : Z (A.act a) := A.const a

theorem ev_ev {l m n : ℕ} {b : Fin m → Pt R n d} {a : Fin l → Pt R m d} (hb : ZZ b) (ha : ZZ a)
    (f : PS R l d) : ev b (ev a f) = ev (evV b a) f :=
  subst_comp_subst_apply (hasSubst_ev a ha) (hasSubst_ev b hb) f

theorem evV_cons {l m n : ℕ} (b : Fin m → Pt R n d) (p : Pt R m d) (u : Fin l → Pt R m d) :
    evV b (Matrix.vecCons p u) = Matrix.vecCons (evP b p) (evV b u) :=
  funext fun j => Fin.cases rfl (fun _ => rfl) j

theorem evV_nil {m n : ℕ} (b : Fin m → Pt R n d) : evV b (![] : Fin 0 → Pt R m d) = ![] :=
  funext fun j => j.elim0

theorem evalPoints_coordinatePoint {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (j : Fin m) : evP b (pt R d j) = b j :=
  funext fun i => ev_X b hb j i

theorem ev_mul' {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (f g : PS R m d) :
    ev b (f * g) = ev b f * ev b g := ev_mul b hb f g

theorem ev_zero' {m n : ℕ} (b : Fin m → Pt R n d) : ev b (0 : PS R m d) = 0 := by
  simpa using ev_C b (0 : R)

theorem evalPoints_zero {m n : ℕ} (b : Fin m → Pt R n d) : evP b (0 : Pt R m d) = 0 :=
  funext fun _ => ev_zero' b

theorem evalPoints_comp {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (φ : Pt R 1 d) {a : Pt R m d} (ha : Z a) :
    evP b (comp1 φ a) = comp1 φ (evP b a) := by
  funext i
  change ev b (ev ![a] (φ i)) = ev ![evP b a] (φ i)
  rw [ev_ev hb (ZZ_cons ha ZZ_nil), evV_cons, evV_nil]

theorem evalPoints_add {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (F : Fin d → PS R 2 d) {x y : Pt R m d}
    (hx : Z x) (hy : Z y) : evP b (addOf F x y) = addOf F (evP b x) (evP b y) := by
  funext i
  change ev b (ev ![x, y] (F i)) = ev ![evP b x, evP b y] (F i)
  rw [ev_ev hb (ZZ_cons hx (ZZ_cons hy ZZ_nil)), evV_cons, evV_cons, evV_nil]

theorem comp1_eq_evalPoint {n : ℕ} (φ : Pt R 1 d) (x : Pt R n d) : comp1 φ x = evP ![x] φ := rfl

theorem germComp1_germComp1_eq_substitute {n : ℕ} (φ : Pt R 1 d) {ψ : Pt R 1 d} (hψ : Z ψ) {x : Pt R n d} (hx : Z x) :
    comp1 (comp1 φ ψ) x = comp1 φ (comp1 ψ x) :=
  evalPoints_comp (ZZ_cons hx ZZ_nil) φ hψ

theorem eval_identity_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f :=
  ev_pt_self _ (fun j => by fin_cases j <;> rfl) f

section Laws

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {n : ℕ}

theorem act_zero_at (x : Pt R n d) : comp1 (B.A.act ((0 : ℕ) : O)) x = 0 := by
  have ha : B.A.act 0 = 0 := by
    have hc := B.A.const 0
    have h1 : B.A.act 0 = B.G.add (B.A.act 0) (B.A.act 0) := by rw [← B.A.add_act, add_zero]
    have h2 : B.A.act 0 = comp1 (B.A.act 0) (B.A.act 0) := by rw [← B.A.mul_act, mul_zero]
    have h3 : ReciprocityTheory.ChartRestriction.G.TB.dLin (B.A.act 0) = 0 := by
      have := GlobalTheory.FormalMulN.dLin_add B.G hc hc
      rw [← h1] at this
      exact left_eq_add.mp this
    have h4 : ∀ i, 2 ≤ (B.A.act 0 i).order := fun i =>
      GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
        obtain ⟨j0, j⟩ := j
        obtain rfl : j0 = 0 := Subsingleton.elim _ _
        exact congrFun (congrFun h3 i) j⟩
    have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (B.A.act 0 i).order := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro i
        have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
          (a := fun p : Fin 1 × Fin d => (![B.A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
          (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
          (fun p => by simpa using ih p.2) (h4 i)
        rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
        rw [congrFun h2 i]
        exact this
    funext i
    exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i
  rw [Nat.cast_zero, ha, comp1_eq_evalPoint]
  exact evalPoints_zero _

theorem act_succ_at (k : ℕ) {x : Pt R n d} (hx : Z x) :
    comp1 (B.A.act ((k + 1 : ℕ) : O)) x = addOf B.G.F (comp1 (B.A.act (k : O)) x) x := by
  rw [Nat.cast_succ, B.A.add_act, B.A.one_act, comp1_eq_evalPoint, comp1_eq_evalPoint,
    evalPoints_add (ZZ_cons hx ZZ_nil) _ (Z_act _ _) (Z_pt _), evalPoints_coordinatePoint (ZZ_cons hx ZZ_nil)]
  rfl

theorem first_power_succ_at (k : ℕ) {x z : Pt R n d} (hx : Z x) (hz : Z z) :
    ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, x, z] B.ph1 := by
  have h : ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k *
      ev (n := 2) ![comp1 (B.A.act (k : O)) (pt R d 0), pt R d 0, pt R d 1] B.ph1) := by
    rw [pow1, Finset.prod_range_succ, pow1]
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem second_power_succ_at (k : ℕ) {x z : Pt R n d} (hx : Z x) (hz : Z z) :
    ev ![x, z] (pow2 B (k + 1)) = ev ![x, z] (pow2 B k) * ev ![x, comp1 (B.A.act (k : O)) z, z] B.ph2 := by
  have h : ev ![x, z] (pow2 B (k + 1)) = ev ![x, z] (pow2 B k *
      ev (n := 2) ![pt R d 0, comp1 (B.A.act (k : O)) (pt R d 1), pt R d 1] B.ph2) := by
    rw [pow2, Finset.prod_range_succ, pow2]
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem first_power_zero : pow1 B 0 = 1 := by simp [pow1]

theorem second_power_zero : pow2 B 0 = 1 := by simp [pow2]

theorem sy_law_at {x z w : Pt R n d} (hx : Z x) (hz : Z z) (hw : Z w) :
    ev ![x, z, w] B.ph2 * ev ![x, z] B.sy * ev ![x, w] B.sy =
      ev ![x, addOf B.G.F z w] B.sy * ev ![z, w, x] B.ph1 := by
  have h := congrArg (ev ![x, z, w]) B.sy_law
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem symmetric_zero_right_at {x : Pt R n d} (hx : Z x) : ev ![x, 0] B.sy = 1 := by
  have h := congrArg (ev ![x]) B.symmetry_zero_snd
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem second_form_zero_left_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![0, x, z] B.ph2 = 1 := by
  have h := congrArg (ev ![x, z]) B.cocycleRight_zero_fst
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem first_form_zero_right_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![x, z, 0] B.ph1 = 1 := by
  have h := congrArg (ev ![x, z]) B.cocycleLeft_zero_thd
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem interchange_at {x y z w : Pt R n d} (hx : Z x) (hy : Z y) (hz : Z z) (hw : Z w) :
    ev ![x, y, z] B.ph1 * ev ![x, y, w] B.ph1 * ev ![addOf B.G.F x y, z, w] B.ph2 =
      ev ![x, z, w] B.ph2 * ev ![y, z, w] B.ph2 * ev ![x, y, addOf B.G.F z w] B.ph1 := by
  have h := congrArg (ev ![x, y, z, w]) B.interchange
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

end Laws

end PositivityTheory.HtPt.Cc
end
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

theorem mem_eig {K O V : Type} [Field K] [AddCommGroup V] [Module K V] {ρ : O → V →ₗ[K] V} {χ : O → K} {x : V} :
    x ∈ eig ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eig, sub_eq_zero]

theorem eig_frob : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  intro K _ p _ _ d O ρ χ
  apply le_antisymm
  · classical
    intro y hy
    rw [mem_eig] at hy
    set K0 := (frobenius K p).fieldRange with hK0
    let β := Module.Basis.ofVectorSpace K0 K
    have hpow : ∀ c : K, c ^ p ∈ K0 := fun c => RingHom.mem_fieldRange.2 ⟨c, frobenius_def p c⟩
    have hrepr : ∀ (c u : K) ι, (β.repr (c ^ p * u) ι : K) = c ^ p * β.repr u ι := by
      intro c u ι
      have h0 : c ^ p * u = (⟨c ^ p, hpow c⟩ : K0) • u := rfl
      rw [h0, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hsum : ∀ ι (f : Fin d → K), (β.repr (∑ j, f j) ι : K) = ∑ j, (β.repr (f j) ι : K) := by
      intro ι f

      simp [map_sum, Finsupp.finsetSum_apply]
    let z : _ → Fin d → K := fun ι j => (β.repr (y j) ι : K)
    have hz : ∀ ι a r, ∑ j, ρ a r j ^ p * z ι j = χ a ^ p * z ι r := by
      intro ι a r
      have h1 := congrFun (hy a) r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      have h2 := congrArg (fun u => (β.repr u ι : K)) h1
      simp only [hsum, hrepr] at h2
      exact h2
    have hex : ∀ ι j, ∃ x : K, x ^ p = z ι j := by
      intro ι j
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (β.repr (y j) ι).2
      exact ⟨x, by rw [← frobenius_def]; exact hx⟩
    choose x hx using hex
    have hxE : ∀ ι, x ι ∈ eig (fun a => Matrix.toLin' (ρ a)) χ := by
      intro ι
      rw [mem_eig]
      intro a
      funext r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      apply frobenius_inj K p
      rw [frobenius_def, frobenius_def, sum_pow_char, mul_pow]
      simp only [mul_pow, hx]
      exact hz ι a r
    let T := Finset.univ.biUnion fun j => (β.repr (y j)).support
    have hT : y = ∑ ι ∈ T, β ι • frobVec p (x ι) := by
      funext j
      rw [Finset.sum_apply]
      conv_lhs => rw [← β.linearCombination_repr (y j)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem
          (fun j => (β.repr (y j)).support) (Finset.mem_univ j)) (fun i (a : K0) => a • β i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun ι _ => ?_
      show (β.repr (y j) ι : K) * β ι = β ι * x ι j ^ p
      rw [hx ι j, mul_comm]
    rw [hT, frobSub]
    exact Submodule.sum_mem _ fun ι _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x ι, hxE ι, rfl⟩)
  · rw [frobSub, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eig]
    rw [SetLike.mem_coe, mem_eig] at hx
    intro a
    have hxa := hx a
    simp only [Matrix.toLin'_apply] at hxa ⊢
    funext r
    have h1 := congrFun hxa r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, frobVec, Matrix.map_apply] at h1 ⊢
    rw [← mul_pow, ← h1, sum_pow_char]
    simp only [mul_pow]

theorem eig_dual : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C d L O k S _ _ _ _ _ χ hχ hv ρ hL hρ s
  let ρL : O →+* Module.End K (Fin d → K) :=
    (Matrix.toLinAlgEquiv'.toRingEquiv : Matrix (Fin d) (Fin d) K ≃+* Module.End K (Fin d → K)).toRingHom.comp ρ
  obtain ⟨e, he_hom, he_mem, he_id, -, he_comb⟩ :=
    GlobalTheory.T.eigen_projectors_split_action K C (Fin d → K) L O k S χ hχ hv ρL hL hρ
  obtain ⟨m, c, b, hc, hes⟩ := he_comb s
  set W := eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a)) with hW
  set W' := eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a)) with hW'
  set E : Matrix (Fin d) (Fin d) K := ∑ j, algebraMap k K (c j) • ρ (b j) with hE
  have hlin : Matrix.toLin' E = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)) := by

    rw [hE, map_sum]
    simp only [map_smul]
  have hlinT : Matrix.toLin' E.transpose =
      ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)).transpose := by

    rw [hE, Matrix.transpose_sum, map_sum]
    simp only [Matrix.transpose_smul, map_smul]
  have heE : ∀ x, e s x = E.mulVec x := by
    intro x
    rw [← Matrix.toLin'_apply, hlin, hes]
    rfl
  have hEW : ∀ x, E.mulVec x ∈ W := fun x => heE x ▸ he_mem s x
  have hEL : ∀ i, ∀ x ∈ L i, E.mulVec x ∈ L i := fun i x hx => heE x ▸ he_hom s i x hx
  have hEid : ∀ x ∈ W, E.mulVec x = x := fun x hx => (heE x).symm.trans (he_id s x hx)
  have hETid : ∀ y ∈ W', E.transpose.mulVec y = y := by
    intro y hy
    simp only [hW', mem_eig, Matrix.toLin'_apply] at hy
    rw [← Matrix.toLin'_apply, hlinT, LinearMap.sum_apply]

    simp only [LinearMap.smul_apply, Matrix.toLin'_apply, hy, smul_smul, ← map_mul,
    ← Finset.sum_smul, ← map_sum]
    rw [hc s, if_pos rfl, map_one, one_smul]
  have hETW : ∀ z, E.transpose.mulVec z ∈ W' := by
    intro z
    rw [hW', mem_eig]
    intro a
    have hmat : ρ a * E = algebraMap k K (χ s a) • E := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec]
      have h1 := (mem_eig.1 (hEW w)) a
      simpa only [Matrix.toLin'_apply] using h1
    have h2 : (ρ a).transpose * E.transpose = algebraMap k K (χ s a) • E.transpose := by
      have hcm : E * ρ a = ρ a * E := by
        rw [hE, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, mul_comm]
      rw [← Matrix.transpose_mul, hcm, hmat, Matrix.transpose_smul]
    show Matrix.toLin' (ρ a).transpose (E.transpose.mulVec z) =
      algebraMap k K (χ s a) • E.transpose.mulVec z
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, ← Matrix.toLin'_apply, map_smul,
      LinearMap.smul_apply, Matrix.toLin'_apply]
  have hadj : ∀ x y, x ⬝ᵥ E.transpose.mulVec y = E.mulVec x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  let B : W →ₗ[K] W' →ₗ[K] K := (dotProductBilin K K).compl₁₂ W.subtype W'.subtype
  have hB : ∀ x y, B x y = (x : Fin d → K) ⬝ᵥ (y : Fin d → K) := fun x y => rfl
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun x hx => ?_
    have h0 : ∀ z, (x : Fin d → K) ⬝ᵥ z = 0 := by
      intro z
      have h1 : B x ⟨_, hETW z⟩ = 0 := by rw [hx]; rfl
      rw [hB] at h1
      change (x : Fin d → K) ⬝ᵥ E.transpose.mulVec z = 0 at h1
      rwa [hadj, hEid _ x.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hinj2 : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    have h0 : ∀ z, z ⬝ᵥ (y : Fin d → K) = 0 := by
      intro z
      have h1 : B.flip y ⟨_, hEW z⟩ = 0 := by rw [hy]; rfl
      rw [LinearMap.flip_apply, hB] at h1
      change E.mulVec z ⬝ᵥ (y : Fin d → K) = 0 at h1
      rwa [← hadj, hETid _ y.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hd1 : Module.finrank K (W' →ₗ[K] K) = Module.finrank K W' := Subspace.dual_finrank_eq
  have hd2 : Module.finrank K (W →ₗ[K] K) = Module.finrank K W := Subspace.dual_finrank_eq
  have hle1 := LinearMap.finrank_le_finrank_of_injective hinj
  have hle2 := LinearMap.finrank_le_finrank_of_injective hinj2
  have hfr : Module.finrank K W = Module.finrank K (W' →ₗ[K] K) := by omega
  have hbij : Function.Bijective B :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj⟩
  obtain ⟨-, hdeg, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C W W' (sub C L W) B (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1 hbij
  have hident : dualLat C (sub C L W) B = sub C (dotDual C L) W' := by
    funext i
    ext y
    show (∀ x ∈ sub C L W i, C.v i (B x y) ≤ 1) ↔ ∀ x ∈ L i, C.v i (dotProductBilin K K x y) ≤ 1
    constructor
    · intro h x hx
      have hxy : dotProductBilin K K x y = B ⟨_, hEW x⟩ y := by
        rw [hB]
        show x ⬝ᵥ (y : Fin d → K) = E.mulVec x ⬝ᵥ (y : Fin d → K)
        rw [← hadj, hETid _ y.2]
      rw [hxy]
      exact h _ (hEL i x hx)
    · intro h x hx
      exact h x hx
  show deg C (sub C (dotDual C L) W') = -deg C (sub C L W)
  rw [← hident]
  exact hdeg

end PositivityTheory.HtPt.Ci
end
