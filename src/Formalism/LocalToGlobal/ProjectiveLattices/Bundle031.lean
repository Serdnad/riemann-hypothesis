module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Formalism.LocalToGlobal.ProjectiveLattices.NormalizedValuationMul
public import Formalism.LocalToGlobal.ProjectiveLattices.SecPtOrd
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle026
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_pos (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (ρ : X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) :
    perFr X x v ρ.1 i = ((mat x ρ)⁻¹ *ᵥ ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) ⟨X.p0 + i, hi⟩ := by
  unfold perFr
  rw [dite_eq_left ρ.2, dite_eq_left hi]

theorem perFr_neg (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (hτ : τ ∉ X.Ψ) (ρ : X.Ψ) (hρ : ρ.1 = conjEmb τ) (i : ℕ) (hi : X.p0 - 1 - i < r) :
    perFr X x v τ i = hermC ρ.1 X.Gm (col (mat x ρ) ⟨X.p0 - 1 - i, hi⟩) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) := by
  obtain ⟨ρ1, hρ1⟩ := ρ
  simp only at hρ
  subst hρ
  unfold perFr
  rw [dite_eq_right hτ, dite_eq_left hρ1, dite_eq_left hi]

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb]

theorem conjEmb_eq (τ : E →+* ℂ) : conjEmb τ = ComplexEmbedding.conjugate τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]

end Mat

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Fam

section Final

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Final

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def offZero {Comp : Type} (X : Comp → Data E r) : Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' _ _ _ := rfl
  add_mem' hP hQ k x hx := by simp [hP k x hx, hQ k x hx]
  smul_mem' a P hP k x hx := by simp [hP k x hx]

def holSub0 {Comp : Type} (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) : Submodule ℂ (FDSec X) :=
  holSub X la ⊓ offZero X

variable {Xo c} in
theorem rdU_mem_offZero {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f : Rul Xo c) : rdU V f ∈ offZero V.X :=
  fun _ _ hx => dif_neg hx


end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def OrdTie (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f

def OrdTieQ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
      (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Ev

variable (Xr : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {K2 : Type} [Field K2] (ev : Rp Xr la N →+* K2) (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0)))

lemma liftEv_alg (r : Rp Xr la N) :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (algebraMap (Rp Xr la N) (Lw Xr la w) r) = ev r :=
  IsLocalization.lift_eq _ r

lemma liftEv_w0inv :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (w0inv Xr la w) = (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0))⁻¹ := by
  have := congrArg (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu) (section_mul_inverse_eq_one Xr la w)
  rw [map_mul, liftEv_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma liftEv_frac (k : ℕ) (g : Rp Xr la N) :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (frac Xr la w k g) = ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, liftEv_alg, liftEv_w0inv]

end Ev

section Std

variable {Xr : PJ D B P j} {la : HeightOneSpectrum (𝓞 B.KO)} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData Xr ka wL wF}

theorem isUnif_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) :
    IsUnif (OsK Xr la G.w) (unifO Xr la G.N) := by
  have : Algebra.IsIntegral (Kp Xr la G.N) (OsK Xr la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp Xr la G.N)
    (Op.irreducible_map Xr la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Xr.Ol la))))

theorem kp_charZero' : CharZero (Kp Xr la G.N) := by
  have := Kl_charZero Xr la
  exact charZero_of_injective_algebraMap (algebraMap (Xr.Kl la) (Kp Xr la G.N)).injective

theorem isDVRAt_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) (hred : IsReduced (OsK Xr la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero' (la := la) (G := G)
  exact (integralClosure_dvr' (Op Xr la G.N) (Kp Xr la G.N) (OsK Xr la G.w)).2 ζ

theorem loc_charZero (h : IsUnif (OsK Xr la G.w) (unifO Xr la G.N)) (ζ : PtsG G la) [IsDVRAt ζ] :
    CharZero (Loc ζ) := by
  have hK := kp_charZero' (la := la) (G := G)
  have hO : CharZero (Op Xr la G.N) :=
    (RingHom.charZero_iff (IsFractionRing.injective (Op Xr la G.N) (Kp Xr la G.N))).2 hK
  refine charZero_of_injective_algebraMap (R := Op Xr la G.N) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.irreducible
  rw [map_mul, map_pow] at ha
  have hb : algebraMap (Op Xr la G.N) (Loc ζ) (unifO Xr la G.N) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Op Xr la G.N) ↥(As (Op Xr la G.N) (OsK Xr la G.w)) (Loc ζ)]
    intro h0
    exact vL_ne_top ζ (unif_mem_nonZeroDivisors h) ((vL_eq_top_iff ζ _).2 h0)
  exact (mul_ne_zero ((u.isUnit.map (algebraMap (Op Xr la G.N) (Loc ζ))).ne_zero) (pow_ne_zero n hb)) ha

end Std

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem addVal_map_of_unr {W V : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : W →+* V) (hunr : ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)) (r : W) :
    IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal W r := by
  obtain ⟨ϖ, hϖ, hιϖ⟩ := hunr
  by_cases hr : r = 0
  · subst hr
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow]
  exact IsDiscreteValuationRing.addVal_def' ((u.isUnit.map ι).unit) hιϖ n

theorem fromW_of {ζ : PtsG G la} [IsDVRAt ζ] {y : E.Pt' la}
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
    (T : CDVR) (ι : Loc ζ →+* T.V) (hloc : IsLocalHom ι) (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ))
    (ev : Rp (xplus X E hM) la G.N →+* T.Fr) (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)))
    (hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F))))
    (hdeg : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)) :
    Nonempty (FromW ζ y) := by
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  have honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w i.succ) = 0 := by
    intro i
    have h1 := hdeg (sfr (xplus X E hM) la G.w i.succ)
    rw [(toOsK_eq_zero_iff _ _ _ _).2 (sfr_succ_mem_Jid _ _ _ i), map_zero, coe_sfr, liftEv_frac] at h1
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hu.ne_zero))
  have hord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
        nval T.V 1 (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w)) := by
    intro x
    rw [hdeg x]
    exact toE_ord_eq T.Fr h hι _
  let sp : SecPt ζ y :=
    { T := T, ep_pos := ep_pos ζ h, ev := ev, hv := hv, onS := honS, s0 := hu, ord := hord }
  have hevW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w))
      (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
      toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a)) := by
    intro x a hxa
    rw [hdeg x, hxa]
    exact phiAt_coe T.Fr h hι a
  exact ⟨{ toSecPt := sp
           ι := ι
           loc := hloc
           unr := hunr
           evW := hevW }⟩

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

structure CurveModel (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF) where

  A' : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)
  sA : ∀ i : Fin (WeightFamilies.dimY D j), sfr (xplus X E hM) la G.w i.succ ∈ A'

  h : ↥A'
  h_one : h - 1 ∈ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A'))
  fin : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥A' ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A')))
  red : IsReduced (↥A' ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A')))

  loc : ∀ b : ↥(Frac0 (xplus X E hM) la G.w), ∃ m : ℕ, ∃ a : ↥A', (h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * b = a

  base_form_injective : Function.Injective fun a : ↥A' =>
    ((a : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
      (emb (xplus X E hM) la G.N (X.inc wF g0))

  base_form_local : ∀ x : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a : ↥A',
    ((h : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ m * (x : Lw (xplus X E hM) la G.w) =
      ((a : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
        (emb (xplus X E hM) la G.N (X.inc wF g0))

def InCurveSecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    (secQ y hs g0).InCurve

structure LiftModel (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (y : PtsG G la → E.Pt' la)
    (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ) where

  Λ : Type
  [cr : CommRing Λ]

  ι : Lw (xplus X E hM) la G.w →+* Λ

  hd : (Idx D j G.N →₀ ℕ) → Λ →+ Λ
  hd_zero : ∀ x, hd 0 x = x
  hd_ι : ∀ β x, hd β (ι x) = ι (hasse (xplus X E hM) la G.w β x)
  hd_mul : ∀ β x z, hd β (x * z) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, hd q.1 x * hd q.2 z

  ev : ∀ ζ, Λ →+* (hs ζ).T.Fr
  ev_ι : ∀ ζ x, ev ζ (ι x) = (hs ζ).lift x

  RG : Subring Λ
  RG_hd : ∀ β, ∀ r ∈ RG, hd β r ∈ RG
  RG_int : ∀ ζ, ∀ r ∈ RG, 0 ≤ nval (hs ζ).T.V 1 (ev ζ r)

  e' : Λ
  e'_hd : ∀ β, β ≠ 0 → hd β e' = 0
  e'_int : ∀ ζ, 0 ≤ nval (hs ζ).T.V 1 (ev ζ e')

  res_ker : ∀ x : ↥(HK (xplus X E hM) la G.w wF), ι (x : Lw (xplus X E hM) la G.w) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) →
    toA0K (xplus X E hM) la G.w wF x = 0

  ball : ∀ a ∈ (secQ y hs g0).A0, ∃ r ∈ RG, ∃ x : ↥(HK (xplus X E hM) la G.w wF),
    toA0K (xplus X E hM) la G.w wF x = a ∧
    ι (x : Lw (xplus X E hM) la G.w) - r * e' ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

  approx : ∀ r ∈ RG, ∃ x : ↥(HK (xplus X E hM) la G.w wF),
    ι (x : Lw (xplus X E hM) la G.w) - r * e' ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) ^ (a0 D j T)

attribute [instance] LiftModel.cr

def InLiftSecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (Gc Prw : ℝ) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ),
    Nonempty (LiftModel G la y hs g0 T) →
    G.TiedW S Gc Prw → (secQ y hs g0).InCurve → (secQ y hs g0).InTie S → (secQ y hs g0).InLift T

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

section Up

variable {j : ℕ} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) {ka wL wF : WeightFamilies.Wt D j}

theorem hypC_xplus (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    HypC large₂ (xplus X E hM) H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus ↔
      HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := Iff.rfl

variable {X} (G : GlobalFamilyData X ka wL wF)

end Up

section N

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (n0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (n1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (n2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (n3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (n4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

section UpN

variable {j : ℕ} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) {ka wL wF : WeightFamilies.Wt D j}

theorem latAt_N : LatAt (withNorm B N n0 n1 n2 n3 n4) j ka ↔ LatAt B j ka := Iff.rfl

theorem lamwAt_N (large₂ : SizeData₂ D) (C A : ℝ) : LAMwAt large₂ (withNorm B N n0 n1 n2 n3 n4) j ka C A ↔ LAMwAt large₂ B j ka C A :=
  Iff.rfl


theorem qAt_N (large₂ : SizeData₂ D) (CR Ck Ch Ah Cc Ac T c : ℝ) :
    QAt large₂ (withNorm B N n0 n1 n2 n3 n4) j ka CR Ck Ch Ah Cc Ac T c ↔ QAt large₂ B j ka CR Ck Ch Ah Cc Ac T c := Iff.rfl

variable {X} (G : GlobalFamilyData X ka wL wF)

end UpN

end N

end Formalism.L2.Pj
end
end
