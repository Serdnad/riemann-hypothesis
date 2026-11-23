module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.IsPairFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Formalism.LocalToGlobal.AlgebraicTheory.Bundle001
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

open TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.Generic

variable {N : ℕ}

def lin (c : Fin (N + 1) → ℂ) : MvPolynomial (Fin (N + 1)) ℂ := ∑ l, c l • MvPolynomial.X l

theorem lin_mem (c : Fin (N + 1) → ℂ) : lin c ∈ ProjSpace.grading ℂ N 1 := by
  unfold lin
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (ProjSpace.X_mem ℂ N l)

theorem exists_X_notMem (z : PSpace ℂ N) :
    ∃ l, (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∉ z.asHomogeneousIdeal.toIdeal := by
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) ≤
      z.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact h l
  apply ProjectiveSpectrum.not_irrelevant_le z
  intro x hx
  exact hle (ProjSpace.irrelevant_le_span_X ℂ N hx)

theorem exists_finite_gen {Y : Scheme.{0}} [NoetherianSpace Y] (Z : Set Y) (hZ : IsClosed Z) :
    ∃ T : Set Y, T.Finite ∧ T ⊆ Z ∧ ∀ x ∈ Z, ∃ t ∈ T, t ⤳ x := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  haveI : Finite S := hSf.to_subtype
  refine ⟨Set.range fun s : S => (hSi s.1 s.2).genericPoint, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    exact Set.mem_sUnion_of_mem ((hSi s hs).isGenericPoint_genericPoint (hSc s hs)).mem hs
  · rintro x ⟨s, hs, hx⟩
    exact ⟨_, ⟨⟨s, hs⟩, rfl⟩, ((hSi s hs).isGenericPoint_genericPoint (hSc s hs)).specializes hx⟩

theorem coheight_step {Y : Scheme.{0}} {t x : Y} (h : t ⤳ x) (W : Set Y) (hW : IsOpen W) (ht : t ∈ W)
    (hx : x ∉ W) : Order.coheight t + 1 ≤ Order.coheight x := by
  apply Order.coheight_add_one_le
  exact lt_iff_le_not_ge.2 ⟨h, fun h' => hx (Specializes.mem_open h' hW ht)⟩

section Cot

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (ι : X ⟶ PSpace ℂ N) (g₀ : MvPolynomial (Fin (N + 1)) ℂ)
  (hg₀ : g₀ ∈ ProjSpace.grading ℂ N 1) {y : CxPts p (RingHom.id ℂ)}
  (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀))

def ev₀ : Sec p (fOpen ι g₀) →+* ℂ := CxPts.evHom hy

def sqQ : Submodule ℂ (Sec p (fOpen ι g₀)) := ((RingHom.ker (ev₀ ι g₀ hy)) ^ 2).restrictScalars ℂ

def rr (l : Fin (N + 1)) : Sec p (fOpen ι g₀) := fRatio ι (MvPolynomial.X l) g₀ (ProjSpace.X_mem ℂ N l) hg₀

def fr (c : Fin (N + 1) → ℂ) : Sec p (fOpen ι g₀) := fRatio ι (lin c) g₀ (lin_mem c) hg₀

def vv (l : Fin (N + 1)) : Sec p (fOpen ι g₀) :=
  rr ι g₀ hg₀ l - algebraMap ℂ (Sec p (fOpen ι g₀)) (ev₀ ι g₀ hy (rr ι g₀ hg₀ l))

def Lm : (Fin (N + 1) → ℂ) →ₗ[ℂ] Sec p (fOpen ι g₀) ⧸ sqQ ι g₀ hy :=
  (sqQ ι g₀ hy).mkQ ∘ₗ Fintype.linearCombination ℂ (vv ι g₀ hg₀ hy)

theorem ev₀_algebraMap (z : ℂ) : ev₀ ι g₀ hy (algebraMap ℂ (Sec p (fOpen ι g₀)) z) = z := by
  first
  | exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy z)
  | exact CxPts.ev_algX hy z

theorem ev₀_smul (z : ℂ) (a : Sec p (fOpen ι g₀)) : ev₀ ι g₀ hy (z • a) = z * ev₀ ι g₀ hy a := by
  rw [Algebra.smul_def, map_mul, ev₀_algebraMap]

theorem mkQ_eq_mkQ (a b : Sec p (fOpen ι g₀)) :
    (sqQ ι g₀ hy).mkQ a = (sqQ ι g₀ hy).mkQ b ↔ a - b ∈ RingHom.ker (ev₀ ι g₀ hy) ^ 2 := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Iff.rfl

theorem Lm_apply' (c : Fin (N + 1) → ℂ) :
    Lm ι g₀ hg₀ hy c = (sqQ ι g₀ hy).mkQ (∑ l, c l • vv ι g₀ hg₀ hy l) := by
  simp only [Lm, LinearMap.coe_comp, Function.comp_apply, Fintype.linearCombination_apply]

theorem Lm_apply (hp : ι ≫ PSpace.str ℂ N = p) (c : Fin (N + 1) → ℂ) :
    Lm ι g₀ hg₀ hy c = (sqQ ι g₀ hy).mkQ
      (fr ι g₀ hg₀ c - algebraMap ℂ (Sec p (fOpen ι g₀)) (ev₀ ι g₀ hy (fr ι g₀ hg₀ c))) := by
  rw [Lm_apply']
  have hfr : fr ι g₀ hg₀ c = ∑ l, c l • rr ι g₀ hg₀ l :=
    fRatio_linear X p N ι hp g₀ hg₀ c (lin_mem c)
  rw [hfr]
  congr 1

  simp only [vv, smul_sub, Finset.sum_sub_distrib, map_sum, ev₀_smul, map_mul, Algebra.smul_def,
  ev₀_algebraMap, mul_sub]

end Cot

section Range

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (ι : X ⟶ PSpace ℂ N) (g₀ : MvPolynomial (Fin (N + 1)) ℂ)
  (hg₀ : g₀ ∈ ProjSpace.grading ℂ N 1) {y : CxPts p (RingHom.id ℂ)}
  (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀))

end Range

end GlobalTheory.EtProj.Generic
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem mem_of_algebraMap_mem_map_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (s : R)
    [IsLocalization.Away s S] {I m : Ideal R} (hm : m.IsMaximal) (hI : m ^ 2 ≤ I) (hs : s ∉ m) {x : R}
    (hx : algebraMap R S x ∈ I.map (algebraMap R S)) : x ∈ I := by
  obtain ⟨⟨y, t⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) S).1 hx
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) S).1 e
  have hw : ((c : R) * t) * x ∈ I := by
    have : (c : R) * y ∈ I := I.mul_mem_left _ y.2
    rw [← hc] at this
    convert this using 1; ring
  have hwm : (c : R) * t ∉ m := by
    obtain ⟨k, hk⟩ := c.2
    obtain ⟨l, hl⟩ := t.2
    rw [← hk, ← hl, ← pow_add]
    exact fun h => hs (hm.isPrime.mem_of_pow_mem _ h)
  obtain ⟨u, i, hi, h1⟩ := hm.exists_inv hwm
  have hi2 : i ^ 2 ∈ I := hI (Ideal.pow_mem_pow hi 2)
  have hx' : x = (u ^ 2 * ((c : R) * t) + 2 * u * i) * (((c : R) * t) * x) + x * i ^ 2 := by
    linear_combination (-x * (u * ((c : R) * t) + i + 1)) * h1
  rw [hx']
  exact I.add_mem (I.mul_mem_left _ hw) (I.mul_mem_left _ hi2)

theorem ker_le_map_ker_away {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] (s : R)
    [IsLocalization.Away s S] (evR : R →+* K) (evS : S →+* K) (h : ∀ x, evS (algebraMap R S x) = evR x) :
    RingHom.ker evS ≤ (RingHom.ker evR).map (algebraMap R S) := by
  intro w hw
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) w
  dsimp only at hw ⊢
  have hx : evR x = 0 := by
    have := congrArg evS (IsLocalization.mk'_spec S x t)
    rw [map_mul, RingHom.mem_ker.1 hw, zero_mul, h] at this
    exact this.symm
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

theorem span_ratio_of_span_ratio (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N)
    (hι : IsClosedImmersion ι) (n : ℕ) (hn : 0 < n) (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ)
    (a b : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
    (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
    (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
    (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b))
    (h : RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2) :
    RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  haveI := hι
  set 𝒜 := ProjSpace.grading ℂ N
  set D := Proj.basicOpen 𝒜 a ⊓ Proj.basicOpen 𝒜 b with hDdef
  set W : X.Opens := ι ⁻¹ᵁ D with hWdef
  have hWa : W ≤ fOpen ι a := fun x hx => hx.1
  have hWb : W ≤ fOpen ι b := fun x hx => hx.2
  have hzW : z ∈ CxPts.ptsIn p (RingHom.id ℂ) W :=
    CxPts.mem_ptsIn.2 ⟨CxPts.mem_ptsIn.1 hza, CxPts.mem_ptsIn.1 hzb⟩
  have hUa : IsAffineOpen (fOpen ι a) := (Proj.isAffineOpen_basicOpen 𝒜 a ha hn).preimage ι
  have hUb : IsAffineOpen (fOpen ι b) := (Proj.isAffineOpen_basicOpen 𝒜 b hb hn).preimage ι
  have hres : ∀ {c d : MvPolynomial (Fin (N + 1)) ℂ} (hc : c ∈ 𝒜 n) (hd : d ∈ 𝒜 n) (hW : W ≤ fOpen ι d)
      (hD : D ≤ Proj.basicOpen 𝒜 d),
      resG X hW (fRatio ι c d hc hd) = (ι.app D).hom (ProjFrac.frac 𝒜 D c d hc hd hD) := by
    intro c d hc hd hW hD
    have := congrArg (fun φ => φ.hom (ProjFrac.frac 𝒜 _ c d hc hd le_rfl)) (ι.naturality (homOfLE hD).op)
    simp only [CommRingCat.comp_apply] at this
    rw [← ProjFrac.resG_frac hD]
    exact this.symm

  have hratio : ∀ j, resG X hWa (fRatio ι (f j) a (hf j) ha) =
      resG X hWb (fRatio ι (f j) b (hf j) hb) * (ι.app D).hom (ProjFrac.frac 𝒜 D b a hb ha inf_le_left) := by
    intro j
    rw [hres _ _ hWa inf_le_left, hres _ _ hWb inf_le_right, ← map_mul]
    congr 1
    exact (ProjFrac.frac_mul_eq (by ring)).symm

  set sa := fRatio ι b a hb ha
  set sb := fRatio ι a b ha hb
  have eA : W = X.basicOpen sa := by
    rw [show sa = (ι.app _).hom (ProjFrac.frac 𝒜 _ b a hb ha le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
  have eB : W = X.basicOpen sb := by
    rw [show sb = (ι.app _).hom (ProjFrac.frac 𝒜 _ a b ha hb le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
    exact congrArg (fun U => ι ⁻¹ᵁ U) (inf_comm _ _)
  letI algA : Algebra Γ(X, fOpen ι a) Γ(X, W) := (resG X hWa).toAlgebra
  letI algB : Algebra Γ(X, fOpen ι b) Γ(X, W) := (resG X hWb).toAlgebra
  haveI locA : IsLocalization.Away sa Γ(X, W) := hUa.isLocalization_of_eq_basicOpen sa (homOfLE hWa) eA
  haveI locB : IsLocalization.Away sb Γ(X, W) := hUb.isLocalization_of_eq_basicOpen sb (homOfLE hWb) eB
  have evA : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι a) Γ(X, W) g) = CxPts.evHom hza g := fun g => by
    change CxPts.evHom hzW (resG X hWa g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWa hzW g
  have evB : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι b) Γ(X, W) g) = CxPts.evHom hzb g := fun g => by
    change CxPts.evHom hzW (resG X hWb g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWb hzW g
  have h1A := ker_le_map_ker_away sa _ _ evA
  have h1B := ker_le_map_ker_away sb _ _ evB
  have h2A : (RingHom.ker (CxPts.evHom hza)).map (algebraMap Γ(X, fOpen ι a) Γ(X, W)) ≤ RingHom.ker (CxPts.evHom hzW) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, evA]; exact hx
  have h3 : RingHom.ker (CxPts.evHom hzW) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ⊔
        RingHom.ker (CxPts.evHom hzW) ^ 2 := by
    intro x hx
    have := Ideal.map_mono h (h1A hx)
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span] at this
    exact sup_le_sup le_rfl (Ideal.pow_right_mono h2A 2) this
  have h4 : Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι b) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) b (hf j) hb) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change resG X hWa _ ∈ _
    rw [hratio j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩)

  have hsurj : Function.Surjective (CxPts.evHom hzb) := fun c =>
    ⟨ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι b) c, by rw [← CxPts.ev_eq]; exact CxPts.ev_algX hzb c⟩
  have hmax : (RingHom.ker (CxPts.evHom hzb)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hs : sb ∉ RingHom.ker (CxPts.evHom hzb) := by
    rw [RingHom.mem_ker, ← CxPts.ev_eq]
    exact (CxPts.mem_ptsIn_basicOpen hzb sb).1 (eB ▸ hzW)
  intro g hg
  refine mem_of_algebraMap_mem_map_away (S := Γ(X, W)) sb hmax le_sup_right hs ?_
  have hgW : algebraMap Γ(X, fOpen ι b) Γ(X, W) g ∈ RingHom.ker (CxPts.evHom hzW) := by
    rw [RingHom.mem_ker, evB]; exact hg
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span]
  exact sup_le_sup h4 (Ideal.pow_right_mono h1B 2) (h3 hgW)

end GlobalTheory.EtProj
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dualFrame_columns_scaled_standard_vectors : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  first | exact @GlobalTheory.DFrame.frameM_coef_eq_chgB | exact GlobalTheory.DFrame.frameM_coef_eq_chgB | (intros; apply GlobalTheory.DFrame.frameM_coef_eq_chgB <;> assumption)
end

section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_eq_of_split_factor (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : DegOne v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hm : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hq, hq2⟩ := hv
  constructor
  · have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
      rw [← h2]
      exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
    have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) v.asIdeal
    rw [hm, hr, map_mul] at h1
    have hP : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    have hP' : Ideal.absNorm P'.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P'.isPrime.ne_top
    obtain ⟨k, hk, e⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ h1)
    interval_cases k
    · exact absurd (by simpa using e) hP
    · simpa using e
    · rw [e] at h1
      exact absurd ((Nat.mul_eq_left (pow_pos hq.pos 2).ne').1 h1) hP'
  · intro hmem
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem _
    have h3 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hI
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, hm, mul_assoc] at h3
    have h4 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * I.map (algebraMap (𝓞 F) (𝓞 E))) := by
      rw [← h3, ← sq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have h5 := (mul_dvd_mul_iff_left P.ne_bot).1 h4
    rcases P.prime.dvd_or_dvd h5 with h6 | h6
    · rw [Ideal.dvd_iff_le] at h6
      exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h6).symm)
    · rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h6
      have h7 : v.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
        rw [← Ideal.map_le_iff_le_comap, hm]
        exact (Ideal.mul_le_inf).trans inf_le_left
      rw [← v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h7] at h6
      apply hq2
      rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
      exact Ideal.mul_mono_right h6

theorem absNorm_eq_of_splitAt (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hv : DegOne v) {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  obtain ⟨P, P', hne, hm⟩ := hs
  have h1 : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hQ]
  rcases Q.isPrime.mul_le.1 h1 with h | h
  · obtain rfl : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne hm
  · obtain rfl : P' = Q := HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne.symm (hm.trans (mul_comm _ _))


omit [NumberField E] [Field E] [Algebra F E] in
theorem plc_eq_absNorm {v : HeightOneSpectrum (𝓞 F)} (hq : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have := v.isPrime
  rcases (Nat.dvd_prime hq).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · exact h7

end Split

theorem degOneUnram_of_mem_vG {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vG i) : DegOneUnram P := by
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have hn : qOf P = Pr.g i := hPr.vG_norm i P hP
  refine ⟨hn ▸ hPr.g_prime i, ?_⟩
  rw [hn]
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (X.conjO (Pr.piG i)) (Pr.g i) hcc (hPr.g_prime i) ?_ ?_ ?_
    (hPr.vG_norm i) P hP
  · rw [hcc, mul_comm]; exact hPr.piG_norm i
  · rw [hcc]; exact (hPr.piG_cop i).symm
  · rw [hE, ← hPr.vG_card i]; rfl

theorem levelPrimes : LevelPrimes := by
  classical
  intro X Pr sel S mu hX hPr hsel P
  by_cases hP : P.1 ∈ Pr.vGs
  · refine ⟨?_, fun h => absurd hP h⟩
    rcases Finset.mem_union.1 hP with h | h
    exacts [degOneUnram_of_mem_vG hX hPr 0 h, degOneUnram_of_mem_vG hX hPr 1 h]
  · rcases Finset.mem_union.1 P.2 with h1 | h1
    · exact absurd h1 hP
    unfold QE at h1
    split_ifs at h1 with h2
    · obtain ⟨v0, hv0, e⟩ := Finset.mem_image.1 h1
      have hv1 : v0 ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv0
      have hgood : GoodPl X.E S v0 := by
        by_contra hn
        have h4 := (Subgroup.mem_inf.1 mu.2).2
        exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v0) hn)
      obtain ⟨h3, h4⟩ := absNorm_eq_of_splitAt hX.rankE hgood.1 hgood.2.1 (Q := P.1) (e ▸ hsel v0)
      have h5 : qOf P.1 = Ideal.absNorm v0.asIdeal := h3
      refine ⟨⟨h5 ▸ hgood.2.1.1, h5 ▸ h4⟩, fun _ => ?_⟩
      rw [h5, ← plc_eq_absNorm hgood.2.1.1]
      exact hgood.2.2
    · simp at h1

end GlobalTheory.ColPeriod
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameSum

theorem isTameWD_of_lpSum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h}
    (hxy : IsTameWD (x.lpSum y)) : IsTameWD x ∧ IsTameWD y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  obtain ⟨k, c, hc, hw⟩ := hxy
  rw [WD.lpSum_mk, WD.mk_eq_mk] at hc
  have H : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → (a.ρ σ).prodMap (b.ρ σ) = 1 :=
    fun σ hσ => hc.ρ_eq_one (hw σ hσ)
  refine ⟨⟨n, a, rfl, fun σ hσ => LinearMap.ext fun u => ?_⟩, ⟨m, b, rfl, fun σ hσ => LinearMap.ext fun u => ?_⟩⟩
  · simpa using congrArg Prod.fst (LinearMap.congr_fun (H σ hσ) (u, 0))
  · simpa using congrArg Prod.snd (LinearMap.congr_fun (H σ hσ) (0, u))

theorem isTameWD_of_mem_sumList : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (l : List (WD h)), IsTameWD (sumList l) → ∀ y ∈ l, IsTameWD y := by
  intro E Ω _ _ _ _ _ A w h l
  induction l with
  | nil => intro _ y hy; simp at hy
  | cons z l ih =>
    intro H y hy
    have H2 := isTameWD_of_lpSum (x := z) (y := sumList l) H
    rcases List.mem_cons.1 hy with rfl | hy
    · exact H2.1
    · exact ih H2.2 y hy

end GlobalTheory.TameSum
end
end

section

namespace GlobalTheory

theorem locNormPow_tensorPowers : Formalism.L2.AlgTh.LocNormPow := Formalism.L2.AlgTh.local_norm_power

end GlobalTheory
end
