module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Adjoin
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem exists_act {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG (m := 3) (R := R)) (W : WPres O ℤ R)
    (hW : ∀ j, W.part j = wpart O u j) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K) (t : Kˣ) :
    ∃ ξt : Sring (O := O) u →ₐ[O] K, ∀ (j : ℤ) x (hx : x ∈ wpart O u j),
      ξt ⟨x, mem_Sring u hx⟩ = ((t ^ j : Kˣ) : K) * ξ ⟨x, mem_Sring u hx⟩ := by
  have hA : W.A = Sring (O := O) u := by
    ext x
    show x ∈ ⨆ j, W.part j ↔ x ∈ ⨆ j, wpart O u j
    simp only [hW]
  refine ⟨(act W.gr (zpowersHom Kˣ t) (ξ.comp (Subalgebra.inclusion hA.le))).comp
    (Subalgebra.inclusion hA.ge), fun j x hx => ?_⟩
  have hx' : Subalgebra.inclusion hA.ge ⟨x, mem_Sring u hx⟩ ∈ W.gr j := by
    show x ∈ W.part j
    rwa [hW]
  rw [AlgHom.comp_apply, act_of_mem W.gr _ _ hx']
  rfl

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_act :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
      (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) →
    ∀ (ξ : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r →
    ∀ (ξ' : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (t : (PadicAlgCl l)ˣ), IsPtHom u ξ' (conjBy (tor (PadicAlgCl l) t) r) ↔
      ∀ (j : ℤ) x (hx : x ∈ wpart O u j), ξ' ⟨x, mem_Sring u hx⟩ = ((t ^ j : (PadicAlgCl l)ˣ) : (PadicAlgCl l)) * ξ ⟨x, mem_Sring u hx⟩ := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr ξ' t
  obtain ⟨hm, hri, -⟩ := conjBy_tor r t
  constructor
  · intro h
    obtain ⟨W, hW, -⟩ := exists_adapted F hF g₁ hg u hu
    obtain ⟨ξt, hξt⟩ := exists_act u W hW.part ξ t
    have e : ξ' = ξt := by
      refine AlgHom.ext_of_eq_adjoin (sring_eq_adjoin F hF g₁ hg u hu hfin).1 ?_
      rintro _ ⟨g, a, b, -, rfl⟩
      refine Eq.trans ?_ (hξt _ _ (entry_mem u g a b)).symm
      have h1 := congrFun (congrFun (h g).2 a) b
      rw [hm, (hr g).2] at h1
      exact h1.symm
    rw [e]
    exact hξt
  · intro h g
    refine ⟨(hri g).trans (hr g).1, ?_⟩
    ext a b
    rw [hm, (hr g).2]
    exact (h _ _ (entry_mem u g a b)).symm
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem dvr_norm {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) :
    (∀ u : A, IsUnit u → ‖f u‖ = 1) ∧
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : A), x ∈ maximalIdeal A ^ n → ‖f x‖ ≤ q ^ n := by
  have hu : ∀ u : Aˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f ((u⁻¹ : Aˣ) : A)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Aˣ)
    have h4 := norm_nonneg (f u)
    nlinarith
  refine ⟨fun u ⟨v, hv⟩ => hv ▸ hu v, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hl0 : (l : A) ≠ 0 := by
    intro h
    have h' : f l = 0 := by rw [h, map_zero]
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖f l‖ < 1 := by
    have : f l = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨‖f ϖ‖, norm_nonneg _, ?_, fun n x hx => ?_⟩
  · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h, map_mul, norm_mul, hu, one_mul, map_pow, norm_pow] at hl
    by_contra hc
    exact absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle y)

private theorem conjBy_conjBy {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (h k : GL (Fin 3) R) :
    conjBy h (conjBy k r) = conjBy (h * k) r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy, mul_assoc]

private theorem conjBy_one {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) :
    conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy]

private theorem aux {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra O (PadicAlgCl l)]
    {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) (hg : F.Marked g₁) (r : Γ →* GG (m := 3) (R := PadicAlgCl l))
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra O A]
    (f : A →ₐ[O] PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) (t : (PadicAlgCl l)ˣ) (r' : Γ →* GG (m := 3) (R := A))
    (hpt : F.IsPt g₁ r') (hp : _root_.UpperTheory.V.UnitaryThreeInertia.push f r' = conjBy (tor _ t) r) :
    HasMult F.η r ∧ Normalised F.c g₁ r ∧ Continuous (mats r) ∧
      ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 ∧ ‖zeta F.c g₁ r‖ = 1 ∧
      (∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1) := by
  obtain ⟨hu, q, hq0, hq1, hq⟩ := dvr_norm (f : A →+* PadicAlgCl l) hle
  simp only [RingHom.coe_coe] at hu hq
  have hr : r = conjBy (tor _ t⁻¹) (_root_.UpperTheory.V.UnitaryThreeInertia.push f r') := by
    rw [hp, conjBy_conjBy, ← map_mul, inv_mul_cancel, map_one, conjBy_one]
  obtain ⟨c1, c2, c3, -, -⟩ := conjBy_tor (_root_.UpperTheory.V.UnitaryThreeInertia.push f r') t⁻¹
  rw [← hr] at c1 c2 c3
  have hent : ∀ g a b, (_root_.UpperTheory.V.UnitaryThreeInertia.push f r' g).mat a b = f ((r' g).mat a b) := fun _ _ _ => rfl
  have hrz : ∀ g a b, (F.rz (PadicAlgCl l) g).mat a b = algebraMap O _ ((r0 F.η F.Ψ g).mat a b) := fun _ _ _ => rfl
  have hdiag : ∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1 := by
    intro g a
    have h := hq 1 _ (by rw [pow_one]; exact hpt.red g a a)
    rw [pow_one, Matrix.sub_apply, map_sub, Matrix.map_apply, AlgHom.commutes] at h
    rw [c1, hent, hrz]
    simp only [wt, sub_self, zpow_zero, Units.val_one, one_mul]
    exact lt_of_le_of_lt h hq1
  have hz : ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 := by
    have e : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) =
        ((r g₁).mat 0 0 - (F.rz (PadicAlgCl l) g₁).mat 0 0) +
          -((r (gstar F.c g₁)).mat 0 0 - (F.rz (PadicAlgCl l) (gstar F.c g₁)).mat 0 0) := by
      simp only [zeta, zmat, Matrix.sub_apply]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hdiag _ _) ?_)
    rw [norm_neg]; exact hdiag _ _
  have hz0 : ‖zeta F.c g₁ (F.rz (PadicAlgCl l))‖ = 1 := by
    have h0 := (zeta_reducible_rep_eq_sub_inv_and_isUnit F.η F.Ψ F.c g₁ ⟨hF.csq, hF.ηc, hF.Ψc, hg.1, hg.2⟩).2
    rw [← hu _ (h0.map (algebraMap O A)), AlgHom.commutes]
    simp only [zeta, zmat, Matrix.sub_apply, map_sub, hrz]
  refine ⟨fun g => (c2 g).trans (hpt.mult g), c3 _ _ ⟨?_, ?_, ?_⟩, ?_, hz, ?_, hdiag⟩
  · ext a b
    rw [hent, hpt.norm.atc]
    simp [Matrix.one_apply, apply_ite f]
  · have h := congrArg f hpt.norm.z12
    simpa only [zmat, Matrix.sub_apply, map_sub, map_zero, hent] using h
  · have h := congrArg f hpt.norm.z21
    simpa only [zmat, Matrix.sub_apply, map_sub, map_zero, hent] using h
  · refine continuous_matrix fun a b => ?_
    simp only [mats, c1, hent]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun g => ?_)
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
    filter_upwards [(hpt.cont n).eventually_eq g] with g' hg'
    have h := congrFun (congrFun hg' a) b
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq] at h
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (hq n _ h) hn
  · have e : zeta F.c g₁ r = (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))) + zeta F.c g₁ (F.rz (PadicAlgCl l)) := by
      ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hz0]; exact hz.ne), hz0]
    exact max_eq_right hz.le

theorem UpperTheory.V.UnitaryThreeInertia.isCharZeroPt_basic :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), F.IsCharZeroPt g₁ r → HasMult F.η r ∧ Normalised F.c g₁ r ∧ Continuous (mats r) ∧ ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 ∧ ‖zeta F.c g₁ r‖ = 1 ∧
      (∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1) ∧ ∀ t, F.IsCharZeroPt g₁ (conjBy (tor (PadicAlgCl l) t) r) := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr
  obtain ⟨A, hA, hfin, t, r', hpt, hp⟩ := hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := aux F hF g₁ hg r A.val (fun x =>
    norm_le_one_of_int l _ (isIntegral_trans (A := O) _ ((Algebra.IsIntegral.isIntegral (R := O) x).map A.val)))
    t r' hpt hp
  refine ⟨h1, h2, h3, h4, h5, h6, fun s => ⟨A, hA, hfin, t * s⁻¹, r', hpt, ?_⟩⟩
  rw [conjBy_conjBy, ← map_mul, inv_mul_cancel_right, hp]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private def affPairs (N : Type) [AddCommGroup N] : Subgroup (Equiv.Perm N × Equiv.Perm N) where
  carrier := {p | ∀ x y, p.2 (x + y) = p.1 x + p.2 y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x y => by
    show a.2 (b.2 (x + y)) = a.1 (b.1 x) + a.2 (b.2 y)
    rw [hb, ha]
  inv_mem' := fun {a} ha x y => by
    show a.2.symm (x + y) = a.1.symm x + a.2.symm y
    apply a.2.injective
    rw [ha]
    simp

private theorem zhat_lift :
    ∀ {D E E' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group E] [Finite E] [Group E'] (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      ∀ (q : E →* E') (w' : D →* E') (e : E), IsLocallyConstant w' → (∀ s ∈ I, w' s = 1) → q e = w' φ →
      ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ q.comp w = w' ∧ w φ = e ∧ ∀ g, w g ∈ Subgroup.zpowers e := by
  intro D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hI hq
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hwl : IsLocallyConstant (f.comp d) := hdl.comp f
  have hwI : ∀ s ∈ I, (f.comp d) s = 1 := by
    intro s hs
    simp [hdI s hs]
  refine ⟨f.comp d, hwl, hwI, ?_, ?_, ?_⟩
  · have h1 : IsLocallyConstant (q.comp (f.comp d)) := hwl.comp q
    have h2 := (h1.prodMk hw').comp (fun p : E' × E' => p.1 = p.2)
    have hclosed : IsClosed (((q.comp (f.comp d)).eqLocus w' : Subgroup D) : Set D) := by
      have := h2.isClosed_fiber True
      convert this using 1
      ext x
      simp [MonoidHom.eqLocus]
      rfl
    have hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp (f.comp d)).eqLocus w' := by
      refine sup_le ?_ ?_
      · intro s hs
        show q ((f.comp d) s) = w' s
        rw [hwI s hs, hI s hs, map_one]
      · rw [Subgroup.zpowers_le]
        show q (f (d φ)) = w' φ
        rw [hdφ, hf1, hq]
    have := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at this
    ext x
    exact this (Subgroup.mem_top x)
  · show f (d φ) = e
    rw [hdφ, hf1]
  · intro g
    exact Subgroup.npow_mem_zpowers e _

theorem UpperTheory.finrank_unramified_cocycles_eq_finrank_invariants :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (I : Subgroup D) (W : Submodule k (D → M)), ContAction ρ → I.Normal → (∃ φ : D, (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
        (∀ y, y ∈ W ↔ y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0) → finrank k W = finrank k (H0 (ρ.comp I.subtype : Representation k I M)) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ I W hρ hI ⟨φ, hcl, hd⟩ hW
  set N : Submodule k M := H0 (ρ.comp I.subtype : Representation k I M) with hNdef
  have hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m := fun m =>
    ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩
  have hev : ∀ y ∈ W, y φ ∈ N := by
    intro y hy
    obtain ⟨⟨-, hc⟩, h0⟩ := (hW y).1 hy
    rw [hN]
    intro s hs
    have h1 := hc s φ
    have h2 := hc φ (φ⁻¹ * s * φ)
    rw [h0 _ (hI.conj_mem' s hs φ), map_zero, add_zero] at h2
    rw [h0 s hs, zero_add] at h1
    rw [← h1, ← h2]
    congr 1
    group
  let ev : W →ₗ[k] N := ((LinearMap.proj φ).comp W.subtype).codRestrict N (fun y => hev y.1 y.2)
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have hyφ : y.1 φ = 0 := congrArg Subtype.val hy
    obtain ⟨⟨hcont, hc⟩, h0⟩ := (hW y.1).1 y.2
    have h1 : y.1 1 = 0 := h0 1 I.one_mem
    let Z : Subgroup D :=
      { carrier := {g | y.1 g = 0}
        one_mem' := h1
        mul_mem' := fun {a b} ha hb => by
          show y.1 (a * b) = 0
          rw [hc, show y.1 a = 0 from ha, show y.1 b = 0 from hb, map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          have := hc a⁻¹ a
          rw [inv_mul_cancel, h1, show y.1 a = 0 from ha, map_zero, add_zero] at this
          exact this.symm }
    have hZ : IsClosed (Z : Set D) := isClosed_eq hcont continuous_const
    have hle : I ⊔ Subgroup.zpowers φ ≤ Z := sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)
    have := Subgroup.topologicalClosure_minimal _ hle hZ
    rw [hcl] at this
    ext g
    exact this (Subgroup.mem_top g)
  have hst : ∀ g : D, ∀ m : N, ρ g m ∈ N := by
    intro g m
    rw [hN]
    intro s hs
    have h := (hN m).1 m.2 _ (hI.conj_mem' s hs g)
    calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ g m := by rw [h]
  let a0 : D →* Function.End N :=
    { toFun := fun g m => ⟨ρ g m, hst g m⟩
      map_one' := by
        funext m
        apply Subtype.ext
        show ρ 1 m = m
        simp
      map_mul' := fun g h => by
        funext m
        apply Subtype.ext
        show ρ (g * h) m = ρ g (ρ h m)
        simp }
  let a : D →* Equiv.Perm N := a0.toHomPerm
  have ha : ∀ g m, (a g m : M) = ρ g m := fun _ _ => rfl
  have hal : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a (fun (p : Equiv.Perm N) (m : N) => (p m : M)) ?_ ?_
    · rw [IsLocallyConstant.iff_continuous]
      exact continuous_pi fun m => hρ.comp (continuous_id.prodMk continuous_const)
    · intro p q h
      ext m
      exact congrFun h m
  have haI : ∀ s ∈ I, a s = 1 := by
    intro s hs
    ext m
    exact (hN m).1 m.2 s hs
  have hsurj : Function.Surjective ev := by
    intro m
    obtain ⟨w, hwl, hwI, hq, hwφ, hw⟩ := zhat_lift I φ hcl hd (MonoidHom.fst _ (Equiv.Perm N)) a
      (a φ, Equiv.addRight m * a φ) hal haI rfl
    have hP : ∀ g, w g ∈ affPairs N := by
      intro g
      refine (Subgroup.zpowers_le.2 ?_ : _ ≤ affPairs N) (hw g)
      intro x y
      apply Subtype.ext
      show ρ φ (x + y : M) + m = ρ φ x + (ρ φ y + m)
      rw [map_add (f := _), add_assoc]
    have hw1 : ∀ g, (w g).1 = a g := fun g => DFunLike.congr_fun hq g
    refine ⟨⟨fun g => ((w g).2 0 : M), (hW _).2 ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
    · exact (hwl.comp (fun p : Equiv.Perm N × Equiv.Perm N => (p.2 0 : M))).continuous
    · intro g h
      have := hP g ((w h).2 0) 0
      rw [add_zero, hw1] at this
      show (((w (g * h)).2 0 : N) : M) = (w g).2 0 + ρ g ((w h).2 0)
      rw [map_mul, Prod.snd_mul, Equiv.Perm.mul_apply, this, Submodule.coe_add, ha, add_comm]
    · intro s hs
      show (((w s).2 0 : N) : M) = 0
      rw [hwI s hs]
      rfl
    · apply Subtype.ext
      show (((w φ).2 0 : N) : M) = m
      rw [hwφ]
      show ρ φ 0 + m = m
      simp
  exact (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq
end
