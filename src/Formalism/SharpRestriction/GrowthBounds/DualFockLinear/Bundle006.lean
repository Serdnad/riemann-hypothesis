module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneMemH0WeightZero
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeAdaptedBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle001

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

theorem Ed_comm_eq (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) (X : Module.End K (VV K m d)) :
    Ed K (m + 1) d a b * X - X * Ed K (m + 1) d a b =
      if vec = true then letterRowOperator K m vec d a b * X - X * letterRowOperator K m vec d a b
      else -(letterRowOperator K m vec d b a * X - X * letterRowOperator K m vec d b a) := by
  cases vec
  · simp only [Bool.false_eq_true, if_false, letterRowOperator]
    split_ifs
    · rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
      abel
    · rw [zero_sub, neg_mul, mul_neg]
      abel
  · simp [letterRowOperator]



theorem onePos_of (hOB : OpBound) (hAdj : RestAdj) (hSt : RestStab) (hT : RestTheta) (hW : RestWt) (hR : RestRep)
    (hR2 : RestRep2) : OnePos := by
  intro K _ _ m hm vec d c ν hν hνc β hβ s hs
  obtain ⟨A, hA⟩ := exists_A (K := K) hR hR2 hm vec d
  have huniq : ∀ T T' : Module.End K (VV K m d),
      (∀ P Q, fockR (thV K m vec d (T P)) (thV K m vec d Q) =
        fockR (thV K m vec d (T' P)) (thV K m vec d Q)) → T = T' := by
    intro T T' h
    refine LinearMap.ext fun P => ?_
    have h0 := uniqV hR hm vec d (T P - T' P) (fun Q => by rw [map_sub, fR_sub_left, h P Q, sub_self])
    exact sub_eq_zero.1 h0
  have hadd1 : ∀ x x' y, A (x + x') y = A x y + A x' y := by
    intro x x' y
    apply huniq
    intro P Q
    rw [LinearMap.add_apply, map_add (f := _), fR_add_left, hA, hA, hA, mul_add, fR_add_right]
  have hsmul1 : ∀ (t : K) x y, A (t • x) y = t • A x y := by
    intro t x y
    apply huniq
    intro P Q
    rw [LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_right]
  have hadd2 : ∀ x y y', A x (y + y') = A x y + A x y' := by
    intro x y y'
    apply huniq
    intro P Q
    rw [LinearMap.add_apply, map_add (f := _), fR_add_left, hA, hA, hA, mul_add, fR_add_left]
  have hsmul2 : ∀ (t : K) x y, A x (t • y) = t • A x y := by
    intro t x y
    apply huniq
    intro P Q
    rw [LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_left]
  let Aₗ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] Module.End K (VV K m d) :=
    LinearMap.mk₂ K A hadd1 hsmul1 hadd2 hsmul2
  obtain ⟨J, bs, μ, hspan, hRE, hμ⟩ := hW K m ν hν
  let WW := Submodule.map₂ Aₗ (dualWeyl K (m + 1) (m + 1) ν) (dualWeyl K (m + 1) (m + 1) ν)
  let Sg := Set.image2 (fun x y => Aₗ x y) (Set.range bs) (Set.range bs)
  have hWWspan : WW = Submodule.span K Sg := by
    show Submodule.map₂ Aₗ _ _ = _
    rw [← hspan, Submodule.map₂_span_span]
  have hbmem : ∀ i, bs i ∈ dualWeyl K (m + 1) (m + 1) ν := fun i => by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hAmem : ∀ x y, x ∈ dualWeyl K (m + 1) (m + 1) ν → y ∈ dualWeyl K (m + 1) (m + 1) ν →
      A x y ∈ WW := fun x y hx hy => Submodule.apply_mem_map₂ Aₗ hx hy
  have hcomm : ∀ x y (a a' : Fin (m + 1)), x ∈ dualWeyl K (m + 1) (m + 1) ν →
      y ∈ dualWeyl K (m + 1) (m + 1) ν →
      Ed K (m + 1) d a a' * A x y - A x y * Ed K (m + 1) d a a' ∈ WW := by
    intro x y a a' hx hy
    rw [Ed_comm_eq K m vec d a a' (A x y)]
    split_ifs
    · rw [comm_A hAdj hT hR hm vec d A hA a a' x y]
      exact WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a a' y hy)) (hAmem _ _ (hSt K (m + 1) ν a' a x hx) hy)
    · rw [comm_A hAdj hT hR hm vec d A hA a' a x y]
      exact WW.neg_mem (WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a' a y hy))
        (hAmem _ _ (hSt K (m + 1) ν a a' x hx) hy))
  have hstab : ∀ A' ∈ WW, ∀ a a' : Fin (m + 1),
      Ed K (m + 1) d a a' * A' - A' * Ed K (m + 1) d a a' ∈ WW := by
    intro A' hA' a a'
    rw [hWWspan] at hA'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ := hx
      exact hcomm _ _ a a' (hbmem i) (hbmem j)
    | zero => simp
    | add x y _ _ hx hy =>
      have e : Ed K (m + 1) d a a' * (x + y) - (x + y) * Ed K (m + 1) d a a' =
          (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') +
            (Ed K (m + 1) d a a' * y - y * Ed K (m + 1) d a a') := by
        rw [mul_add, add_mul]
        abel
      rw [e]
      exact WW.add_mem hx hy
    | smul t x _ hx =>
      have e : Ed K (m + 1) d a a' * (t • x) - (t • x) * Ed K (m + 1) d a a' =
          t • (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]
      exact WW.smul_mem t hx
  have hwt : ∀ A' ∈ Sg, ∃ ω : Fin (m + 1) → ℤ,
      (∀ a, Ed K (m + 1) d a a * A' - A' * Ed K (m + 1) d a a = (ω a : K) • A') ∧ ∀ a, ω a ≤ c := by
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    refine ⟨fun a => if vec then (μ j a : ℤ) - μ i a else (μ i a : ℤ) - μ j a, fun a => ?_, fun a => ?_⟩
    · show Ed K (m + 1) d a a * A (bs i) (bs j) - A (bs i) (bs j) * Ed K (m + 1) d a a = _
      rw [Ed_comm_eq K m vec d a a (A (bs i) (bs j)), comm_A hAdj hT hR hm vec d A hA a a (bs i) (bs j),
        hRE j a, hRE i a, hsmul1, hsmul2]
      dsimp only
      rw [show (Aₗ (bs i)) (bs j) = A (bs i) (bs j) from rfl]
      split_ifs <;> push_cast <;> rw [sub_smul] <;> abel
    · dsimp only
      have h1 := hμ j a
      have h2 := hμ i a
      split_ifs <;> omega
  have hmain := hOB K (m + 1) d c WW Sg hstab hWWspan hwt (A β s) (hAmem β s hβ hs)
  have hset : {B | ∃ l : List (Fin (m + 1) × Fin (m + 1)), l.length ≤ c ∧ B = EdWord K (m + 1) d l} =
      EdWord K (m + 1) d '' {l | l.length ≤ c} := by
    ext B
    simp [eq_comm]
  rw [hset, Finsupp.mem_span_image_iff_linearCombination] at hmain
  obtain ⟨f, hf, hfA⟩ := hmain
  refine ⟨f.support, f, fun l hl => (Finsupp.mem_supported K f).1 hf hl, ?_⟩
  intro P hP Q hQ
  have hP' : P ∈ homogeneousSubmodule (Fin (m + 1)) K d := (mem_Hd_iff P).1 hP
  have hQ' : Q ∈ homogeneousSubmodule (Fin (m + 1)) K d := (mem_Hd_iff Q).1 hQ
  have h1 := hA β s ⟨P, hP'⟩ ⟨Q, hQ'⟩
  have hcoe : ((A β s ⟨P, hP'⟩ : VV K m d) : MvPolynomial (Fin (m + 1)) K) =
      ∑ l ∈ f.support, f l • word1 l P := by
    rw [← hfA, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, EdWord_coe]
  calc fockR (theta K m vec P * s) (theta K m vec Q * β)
      = fockR (thV K m vec d ⟨P, hP'⟩ * s) (thV K m vec d ⟨Q, hQ'⟩ * β) := rfl
    _ = fockR (thV K m vec d (A β s ⟨P, hP'⟩)) (thV K m vec d ⟨Q, hQ'⟩) := h1.symm
    _ = fockR (theta K m vec (∑ l ∈ f.support, f l • word1 l P)) (theta K m vec Q) := by
      rw [← hcoe]
      rfl

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det)

section Ext

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem exists_ext (G : Module.Dual Kf (Vsp Kf X)) :
    ∃ γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf, ∀ Q : Vsp Kf X, γ (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q := by
  obtain ⟨γ, hγ⟩ := LinearMap.exists_extend G
  exact ⟨γ, fun Q => by rw [← hγ]; rfl⟩

def extD (G : Module.Dual Kf (Vsp Kf X)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf := (exists_ext G).choose

theorem extD_spec (G : Module.Dual Kf (Vsp Kf X)) (Q : Vsp Kf X) : extD G (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q :=
  (exists_ext G).choose_spec Q

def peelMap (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) : Vsp Kf X →ₗ[Kf] Vsp Kf XT :=
  (c • slice A (extD G)).restrict (fun u hu => Submodule.smul_mem _ _ (slice_V hP _ u hu))

theorem peelMap_coe (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) (u : Vsp Kf X) :
    ((peelMap hP c G u : Vsp Kf XT) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = c • slice A (extD G) (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := rfl

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem peel_Hten (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Qv : Vsp Kf sp, (Qv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O sp Λ → ∃ a : O, G Qv = c * algebraMap O Kf a)
    (u : Vsp Kf X) (hu : (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X Λ) :
    ∃ yv : Vsp Kf XT, (yv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O XT Λ ∧ peelMap hP c0 G u = (c0 * c) • yv := by
  obtain ⟨y, hy, he⟩ := slice_Hten hP Λ (extD G) c (fun Q hQ => by
      obtain ⟨a, ha⟩ := hG ⟨Q, Hten_le_V hdsp Λ hΛ Q hQ⟩ hQ
      exact ⟨a, by rw [← ha]; exact extD_spec G ⟨Q, _⟩⟩) u hu
  refine ⟨⟨y, Hten_le_V hdT Λ hΛ y hy⟩, hy, Subtype.ext ?_⟩
  rw [peelMap_coe, he, smul_smul]
  rfl

end Ext

section Lat

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Re'_le_scale (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant X) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r X ≤ M) :
    Re' p ι σ w r X e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (dualLat O Kf (HL (O := O) ι σ X e.tgt)) := by
  obtain ⟨I, hI, x, π, _, c2, _, c4, c4', _, c7⟩ := edge_lattice_adapted_basis h m r X hd e he
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  rw [← c7, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine mem_scale.2 ⟨w ^ ((M : ℤ) - order r X (π i)).toNat • (((p : Kf) ^ π i)⁻¹ • x.coord i), ?_, ?_⟩
  · rw [← c2, Formalism.L2.G.Model.dualLat_span x (fun i => (p : Kf) ^ π i) (fun i => zpow_ne_zero _ hp0)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have h1 := c4' i
    rw [← algebraMap_smul Kf (w ^ ((M : ℤ) - order r X (π i)).toNat), smul_smul, smul_smul, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_add₀ hw]
    show _ = ((algebraMap O Kf) w ^ (-order r X (π i)) * (p : Kf) ^ (-π i)) • x.coord i
    rw [zpow_neg (p : Kf)]
    congr 3
    ring

variable {m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem p_zpow (h : HidaSetting p n' W Qq O Kf ι σ j w) (z : ℤ) : (p : Kf) ^ z = algebraMap O Kf w ^ (2 * z) := by
  rw [Formalism.L2.G.Model.p_eq h, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem peel_Re (h : HidaSetting p n' W Qq O Kf ι σ j w) (hP : Peel A X XT sp) (hX : X = XT + sp) (hdT : IsDominant XT)
    (hdsp : IsDominant sp) (r : ℕ) (e' : Edge W Qq (m + 1)) (he' : IsEdge p n' r e') (N : ℤ)
    (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ Re p ι σ w r sp e', ∃ a : O, be p r sp Q G = algebraMap O Kf w ^ N * algebraMap O Kf a) :
    ∀ u ∈ Re p ι σ w r X e',
      peelMap hP ((p : Kf) ^ Ar r sp) G u ∈ scale (algebraMap O Kf w ^ N) (Re p ι σ w r XT e') := by
  intro u hu
  have hw := w_ne_zero h
  have hAr : Ar r X = Ar r XT + Ar r sp := by rw [hX]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e' he'
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e' = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  obtain ⟨u0, hu0, rfl⟩ := mem_scale.1 hu
  have hu0' : ((u0 : Vsp Kf X) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X (fun s => LeAt p ι σ w s.val e') := hu0
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => LeAt p ι σ w s.val e') hΛ ((p : Kf) ^ Ar r sp)
    (algebraMap O Kf w ^ (N - Ar r sp)) G (by
      intro Qv hQv
      obtain ⟨a, ha⟩ := hG (algebraMap O Kf w ^ (-Ar r sp) • Qv) (mem_scale.2 ⟨Qv, hQv, rfl⟩)
      refine ⟨a, ?_⟩
      rw [be_smulK_left] at ha
      unfold be at ha
      rw [map_smul, smul_eq_mul, p_zpow h, ← mul_assoc, ← zpow_add₀ hw] at ha
      have e1 : -Ar r sp + 2 * Ar r sp = Ar r sp := by ring
      rw [e1] at ha
      rw [zpow_sub₀ hw, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hw), mul_comm]
      exact ha) u0 hu0'
  rw [map_smul, he]
  refine mem_scale.2 ⟨algebraMap O Kf w ^ (-Ar r XT) • yv, mem_scale.2 ⟨yv, hy, rfl⟩, ?_⟩
  rw [smul_smul, smul_smul, p_zpow h, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hAr]
  congr 2
  ring

theorem peel_HL (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (L : Submodule W (Fin (m + 1) → Qq))
    (hL : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ extO O ι σ s.val L = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ HL (O := O) ι σ sp L, ∃ a : O, G Q = c * algebraMap O Kf a) :
    ∀ u ∈ HL (O := O) ι σ X L, peelMap hP c0 G u ∈ scale (c0 * c) (HL (O := O) ι σ XT L) := by
  intro u hu
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => extO O ι σ s.val L) hL c0 c G (fun Qv hQv => hG Qv hQv) u hu
  exact mem_scale.2 ⟨yv, hy, he.symm⟩

end Lat

theorem dualWeyl_zero_const {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R)
    (hF : F ∈ dualWeyl R r n 0) : F = C (AddMonoidAlgebra.coeff F 0) := by
  classical
  have h1 : IsWeightedHomogeneous (colW r n) F 0 := (mem_dualWeyl_iff.1 hF).1
  ext e
  rw [coeff_C]
  split_ifs with he
  · rw [he]
  · apply h1.coeff_eq_zero
    intro hwt
    apply he
    symm
    ext v
    have h2 := congrFun hwt v.2
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h2
    by_contra hv
    have h3 := (Finset.sum_eq_zero_iff.1 h2) v (Finsupp.mem_support_iff.2 (by simpa using hv))
    simp [colW] at h3
    exact hv (by simpa using h3)

end Formalism.MainNotions.TestSideCounting
end
end
