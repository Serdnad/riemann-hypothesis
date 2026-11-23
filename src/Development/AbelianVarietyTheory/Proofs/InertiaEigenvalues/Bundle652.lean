module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle562
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle615
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle578
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle598
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CoefExtC

section General

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.AdTh.CoefExt

variable {K : Type} [Field K] {σ : K →+* ℂ} {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n}
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_ext (c' : VV K lam →ₛₗ[σ] W) (hs : Submodule.span ℂ (Set.range c') = ⊤)
    (hli : LinearIndependent ℂ fun j => c' (bVV K lam j)) :
    ∃ c : VV ℂ lam →ₗ[ℂ] W, (∀ v, c (up σ lam v) = c' v) ∧ Function.Bijective c ∧
      ∀ d : VV ℂ lam →ₗ[ℂ] W, (∀ v, d (up σ lam v) = c' v) → d = c := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun j => up σ lam (bVV K lam j)) := by
    intro v _
    obtain ⟨a, rfl⟩ := exists_coord σ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcard : Fintype.card (VVIdx lam) = Module.finrank ℂ (VV ℂ lam) := (Module.finrank_eq_card_basis (bVV ℂ lam)).symm
  let b : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) := basisOfTopLeSpanOfCardEqFinrank _ hsp hcard
  have hb : ∀ j, b j = up σ lam (bVV K lam j) := fun j => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hsp hcard) j
  have hsw : ⊤ ≤ Submodule.span ℂ (Set.range fun j => c' (bVV K lam j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨v, rfl⟩

    rw [← (bVV K lam).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let w : Module.Basis (VVIdx lam) ℂ W := Module.Basis.mk hli hsw
  have hc : ∀ j, (b.equiv w (Equiv.refl _)) (up σ lam (bVV K lam j)) = c' (bVV K lam j) := by
    intro j
    rw [← hb, Module.Basis.equiv_apply]
    exact Module.Basis.mk_apply hli hsw j
  refine ⟨(b.equiv w (Equiv.refl _)).toLinearMap, fun v => ?_, (b.equiv w (Equiv.refl _)).bijective, fun d hd => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr v, up_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smulₛₗ, LinearEquiv.coe_coe, hc]
  · refine b.ext fun j => ?_
    rw [hb, hd, LinearEquiv.coe_coe, hc]

theorem li_basis (c' : VV K lam →ₛₗ[σ] W)
    (h : ∀ (m : ℕ) (b : Fin m → VV K lam), LinearIndependent K b → LinearIndependent ℂ fun j => c' (b j)) :
    LinearIndependent ℂ fun j => c' (bVV K lam j) := by
  let e := Fintype.equivFin (VVIdx lam)
  have h1 := h _ (bVV K lam ∘ e.symm) ((bVV K lam).linearIndependent.comp _ e.symm.injective)
  have h2 := h1.comp e e.injective
  simpa [Function.comp_def] using h2

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



theorem exists_extC_bijective_unique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨-, h2, h3⟩ := hT.mapL i
  obtain ⟨c, h4, h5, h6⟩ := exists_ext (W := (R.cV i).W) O.c0' (GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3)
    (li_basis (W := (R.cV i).W) O.c0' fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb)
  refine ⟨c, fun v v' hv => ?_, h5, fun d hd => h6 d fun v => hd v _ rfl⟩
  rw [show v' = GlobalTheory.AdTh.CoefExt.up (inC O.c') (lamV D i) v from Subtype.ext hv]
  exact h4 v

end GlobalTheory.CoefExtC

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.ZNotRoot

theorem pow_sub_one_sub {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∃ t : R, q ^ n - 1 - (n : R) * (q - 1) = (q - 1) ^ 2 * t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨q * t + n, ?_⟩
    push_cast
    linear_combination q * ht

theorem eval_mul_sub {R : Type*} [CommRing R] (P : Polynomial R) (x q : R) :
    ∃ r : R, P.eval (q * x) - P.eval x = (q - 1) * x * (Polynomial.derivative P).eval x + (q - 1) ^ 2 * r := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨r', hr'⟩ := hQ
    refine ⟨r + r', ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add]
    linear_combination hr + hr'
  | monomial n c =>
    obtain ⟨t, ht⟩ := pow_sub_one_sub q n
    refine ⟨c * x ^ n * t, ?_⟩
    have hd : x * (Polynomial.derivative (Polynomial.monomial n c)).eval x = c * n * x ^ n := by
      rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]; push_cast; ring
    simp only [Polynomial.eval_monomial]
    linear_combination c * x ^ n * ht - (q - 1) * hd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ev_coe (bk : BK K) (Q : Polynomial (Wq l bk.a)) :
    bk.ev (Q : bk.S) = (Q.map (wA l bk.a : Wq l bk.a →+* Ainf l)).eval (WittVector.teichmuller l bk.flat) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Polynomial.coe_add, map_add (f := _), hP, hQ, Polynomial.map_add (f := _), Polynomial.eval_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
      map_mul, map_pow, bk.ev_C, bk.ev_X]
    simp

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem theta_deriv_ne (bk : BK K) : Per.θ l (bk.ev (Polynomial.derivative bk.Ep : bk.S)) ≠ 0 := by
  obtain ⟨c, A, B, h⟩ := GlobalTheory.BSP.bezout_Ep_derivative l K bk
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h2 := congrArg (fun P : Polynomial (Wq l bk.a) => Per.θ l (bk.ev (P : bk.S))) h
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, map_add (f := _), map_mul, bk.ev_C] at h2
  intro h0
  change Per.θ l (bk.ev (A : bk.S)) * Per.θ l (bk.ev bk.E) + Per.θ l (bk.ev (B : bk.S)) * Per.θ l (bk.ev _) = _ at h2
  rw [hE, h0, mul_zero, mul_zero, add_zero, map_pow, map_natCast, map_pow, map_natCast] at h2
  have h3 := congrArg (fun x : OC l => (x : ℂ_[l])) h2
  simp only [ZeroMemClass.coe_zero] at h3
  push_cast at h3
  exact pow_ne_zero c (GlobalTheory.RingBasics.p_ne_zero (p := l)) h3.symm

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

abbrev Θ (l : ℕ) [Fact l.Prime] : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l)

theorem Θ_apply (x : Ainf l) : Θ l x = ((Per.θ l x : OC l) : ℂ_[l]) := (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 x

theorem Θ_E (bk : BK K) : Θ l (bk.ev bk.E) = 0 := by
  rw [Θ_apply]
  have : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [this]; rfl

theorem Θ_flat (bk : BK K) : Θ l (WittVector.teichmuller l bk.flat) ≠ 0 := by
  rw [Θ_apply, WittVector.fontaineTheta_teichmuller, ← (GlobalTheory.BSP.BK.prime_unif l K bk).2, coe_intToOC]
  intro h
  have h1 := congrArg norm h
  rw [PadicComplex.norm_extends, norm_zero, norm_eq_zero] at h1
  apply (GlobalTheory.BSP.BK.prime_unif l K bk).1.ne_zero
  exact Subtype.ext (Subtype.ext h1)

end GlobalTheory.BKLim.ZNotRoot

open GlobalTheory.BKLim.ZNotRoot in
theorem GlobalTheory.BKLim.exists_isZ_not_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z ∧ ∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1 := by
  intro l _ K bk
  obtain ⟨τ, hτ⟩ := GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨hφ, ε, η, hε, hη⟩ := id hτ
  set u : Ainf l := WittVector.teichmuller l bk.flat with hu_def
  set D : Ainf l := bk.ev (Polynomial.derivative bk.Ep : bk.S) with hD_def
  set a : ℂ_[l] := Θ l ((↑η⁻¹ : Ainf l) * τ * u * D) with ha_def
  have ha : a ≠ 0 := by
    rw [ha_def, map_mul, map_mul, map_mul]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) (Θ_flat bk)) ?_
    · exact ((Units.isUnit η⁻¹).map (Θ l)).ne_zero
    · simpa using GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    · rw [Θ_apply]; intro h
      apply theta_deriv_ne bk
      exact Subtype.ext h
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_one_add_primePow_mul_not_rootOfUnity l a ha
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_moves_flat_by_unit_root l (GlobalTheory.T.rootOfUnity_padicComplex_mem_range_algClosure l) K bk (ε ^ (l ^ k)) (by rw [map_pow, hε.1, one_pow])
  set μ : Ainf l := WittVector.teichmuller l ε - 1 with hμ_def
  set E : Ainf l := bk.ev bk.E with hE_def
  set P : Polynomial (Ainf l) := bk.Ep.map (wA l bk.a : Wq l bk.a →+* Ainf l) with hP_def
  have hEP : E = P.eval u := ev_coe bk bk.Ep
  have hDP : D = (Polynomial.derivative P).eval u := by
    rw [hD_def, ev_coe, hP_def, Polynomial.derivative_map]
  have hσu : Per.σA (g : GQ l) u = WittVector.teichmuller l ε ^ (l ^ k) * u := by
    rw [hu_def, GlobalTheory.RingIface.sigA_teich, hg, map_mul, map_pow]
  have hσE : Per.σA (g : GQ l) E = P.eval (WittVector.teichmuller l ε ^ (l ^ k) * u) := by
    rw [hEP, hP_def, Polynomial.eval_map, Polynomial.hom_eval₂, hσu, ← Polynomial.eval_map]
    congr 2
    exact RingHom.ext fun w => bk.gal_w g w
  obtain ⟨r, hr⟩ := eval_mul_sub P u (WittVector.teichmuller l ε ^ (l ^ k))
  obtain ⟨s, hs⟩ := pow_sub_one_sub (WittVector.teichmuller l ε) (l ^ k)
  have hμE : μ = (↑η⁻¹ : Ainf l) * E * τ := by
    have h1 : (η : Ainf l) * μ = E * τ := by rw [hμ_def, ← hη, hφ]
    calc μ = (↑η⁻¹ : Ainf l) * ((η : Ainf l) * μ) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [h1]; ring
  set L : Ainf l := ((l ^ k : ℕ) : Ainf l) with hL_def
  have hq : WittVector.teichmuller l ε ^ (l ^ k) - 1 = (↑η⁻¹ : Ainf l) * E * τ * (L + μ * s) := by
    rw [← hμE, hμ_def]; linear_combination hs
  set w : Ainf l := 1 + (↑η⁻¹ : Ainf l) * τ * (L + μ * s) * u * D +
    E * ((↑η⁻¹ : Ainf l) * τ) ^ 2 * (L + μ * s) ^ 2 * r with hw_def
  have hw : Per.σA (g : GQ l) E = E * w := by
    rw [hσE, hw_def, hDP]
    rw [hq] at hr
    linear_combination hr - hEP
  have hΘw : Θ l w = 1 + (l : ℂ_[l]) ^ k * a := by
    have hΘE : Θ l E = 0 := Θ_E bk
    rw [hw_def, ha_def, hL_def, hμE]
    simp only [map_add (f := _), map_mul, map_pow, map_one, hΘE, map_natCast]
    push_cast
    ring
  refine ⟨g, (Θ l w)⁻¹, ⟨w, hw, ?_⟩, fun i hi => ?_⟩
  · change (Θ l w)⁻¹ * Θ l w = 1
    rw [hΘw]; exact inv_mul_cancel₀ hk0
  · rw [inv_pow, Ne, inv_eq_one, hΘw]
    exact hk i hi

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_ext {P P' : Obj l R} {a b : Hom P P'} (h : a.f = b.f) : a = b := by
  cases a; cases b; cases h; rfl

theorem comp_assoc {P₁ P₂ P₃ P₄ : Obj l R} (c : Hom P₃ P₄) (b : Hom P₂ P₃) (a : Hom P₁ P₂) :
    (c.comp b).comp a = c.comp (b.comp a) := hom_ext rfl

theorem qmap_comp {P₁ P₂ P₃ : Obj l R} (g : Hom P₂ P₃) (f : Hom P₁ P₂) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem of_isPushout {P : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange @P)
    {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (h : P φ) : P φ' := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  exact hP A B A' B' h

end GlobalTheory.BSP.CoverBC

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem flat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'} {h' : Hom B' C'}
    (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).Flat) (m : ℕ) : (qmap h' m).Flat :=
  of_isPushout RingHom.Flat.isStableUnderBaseChange (H.po m) (hf m)

theorem faithfullyFlat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'}
    {h' : Hom B' C'} (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).FaithfullyFlat) (m : ℕ) :
    (qmap h' m).FaithfullyFlat :=
  of_isPushout RingHom.FaithfullyFlat.isStableUnderBaseChange (H.po m) (hf m)

end GlobalTheory.BSP.CoverBC


open GlobalTheory.BSP.CoverBC in
theorem GlobalTheory.BSP.stable_cover_of_isPO : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R)
    (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'),
    IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  intro l _ R _ B C B' C' h k k' h' H
  have st : Stable h → Stable h' := by
    intro hs
    refine ⟨flat_of_isPO H hs.flat, fun B'' k₂ => ?_⟩
    obtain ⟨C'', k₀, h'', H₂⟩ := hs.po B'' (k₂.comp k)
    have e : k₀.comp h = (h''.comp k₂).comp k := by rw [H₂.comm, comp_assoc]
    obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.T.prismPushoutModAdicPow_universal l R B C B' C' h k k' h' H C'' k₀ (h''.comp k₂) e
    refine ⟨C'', c, h'', ⟨hc₂, fun m => ?_⟩⟩
    have s := H₂.po m
    rw [← hc₁, qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp] at s
    refine IsPushout.of_top s ?_ (H.po m)
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← qmap_comp, ← qmap_comp, hc₂]
  exact ⟨st, fun hc => ⟨st hc.stable, faithfullyFlat_of_isPO H hc.ff⟩⟩
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevH

open CategoryTheory

theorem lev_ring {A B D T : Type} [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B]
    (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T)
    (hff : (algebraMap A B).FaithfullyFlat)
    (hpo1 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q))
    (hpo2 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B)))
      (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂))
    (e1 : q₂₃.comp p = q₁₂.comp q) (e2 : q₂₃.comp q = q₃) (e3 : q₁₃.comp p = q₁₂.comp p) (e4 : q₁₃.comp q = q₃)
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) D) (hε : IsUnit ε) (hc : ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃) :
    ∃ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) ∧
      Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hw : p.comp (algebraMap A B) = q.comp (algebraMap A B) := by
    have := congrArg CommRingCat.Hom.hom hpo1.w
    simpa using this
  have hr : ∀ c, p (algebraMap A B c) = q (algebraMap A B c) := fun c => RingHom.congr_fun hw c
  let N : Submodule A (Fin d → B) :=
    { carrier := {z | (fun i => p (z i)) = ε.mulVec fun i => q (z i)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        have e : (fun i => q ((a + b) i)) = (fun i => q (a i)) + fun i => q (b i) := by
          funext i; simp [map_add (f := _)]
        rw [e, Matrix.mulVec_add, ← ha, ← hb]
        funext i; simp [map_add (f := _)]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
        exact (Matrix.mulVec_zero ε).symm
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        have e1 : (fun i => p ((c • z) i)) = q (algebraMap A B c) • fun i => p (z i) := by
          funext i; simp [Algebra.smul_def, map_mul, hr]
        have e2 : (fun i => q ((c • z) i)) = q (algebraMap A B c) • fun i => q (z i) := by
          funext i; simp [Algebra.smul_def, map_mul]
        rw [e1, e2, Matrix.mulVec_smul, hz] }
  exact ⟨N, fun z => Iff.rfl, GlobalTheory.T.descent_free_module_cocycle A B D T p q q₁₂ q₂₃ q₁₃ q₃ hff hpo1 hpo2 e1 e2 e3 e4 d ε hε hc N
    fun z => Iff.rfl⟩

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_comp_assoc {B C D E : Obj l R} (h : Hom D E) (g : Hom C D) (f : Hom B C) :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem lev_prism [Fact l.Prime] {B C D : Obj l R} (h : Hom B C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (m : ℕ) (d : ℕ) (ε : Matrix (Fin d) (Fin d) D.A) (hε : IsUnit ε)
    (hcoc : ∀ (T : Obj l R) (q₁₂ q₂₃ q₁₃ : Hom D T) (q₃ : Hom C T), q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ →
      q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ε.map q₁₂.f * ε.map q₂₃.f = ε.map q₁₃.f) :
    letI := (qmap h m).toAlgebra
    ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m),
      (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = (ε.map (Ideal.Quotient.mk (adI D ^ m))).mulVec
        fun i => qmap q m (z i)) ∧
      Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧
        IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  let := (qmap h m).toAlgebra
  have c1 : p.comp h = q.comp h := hpo.comm
  refine Exists.elim (hc.stable.po D (p.comp h)) fun T hT => Exists.elim hT fun q₃ hT => Exists.elim hT
    fun q₁₂ hT => ?_
  have c2 : q₃.comp h = q₁₂.comp (p.comp h) := hT.comm
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp q) q₃ (by
      rw [hom_comp_assoc, ← c1, c2])) fun q₂₃ h23 => ?_
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp p) q₃ (by
      rw [hom_comp_assoc, c2])) fun q₁₃ h13 => ?_
  have hpo2 := hT.po m
  have hq : qmap (p.comp h) m = (qmap p m).comp (qmap h m) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  rw [hq] at hpo2
  have hq2 : ∀ (k k' : Hom D T) (k'' : Hom C T), k.comp p = k'.comp q → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap q m) :=
    fun k k' k'' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq3 : ∀ (k : Hom D T) (k' : Hom C T), k.comp q = k' → (qmap k m).comp (qmap q m) = qmap k' m :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq4 : ∀ (k : Hom D T) (k' : Hom D T), k.comp p = k'.comp p → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap p m) :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  refine lev_ring (qmap p m) (qmap q m) (qmap q₁₂ m) (qmap q₂₃ m) (qmap q₁₃ m) (qmap q₃ m) (hc.ff m) (hpo.po m) hpo2
    (hq2 q₂₃ q₁₂ q₃ h23.1.1) (hq3 q₂₃ q₃ h23.1.2) (hq4 q₁₃ q₁₂ h13.1.1) (hq3 q₁₃ q₃ h13.1.2) d _
    (hε.map (Ideal.Quotient.mk (adI D ^ m)).mapMatrix) ?_
  have := congrArg (fun M : Matrix (Fin d) (Fin d) T.A => M.map (Ideal.Quotient.mk (adI T ^ m)))
    (hcoc T q₁₂ q₂₃ q₁₃ q₃ h23.1.1 h23.1.2 h13.1.1 h13.1.2)
  simp only [Matrix.map_mul] at this
  exact this

end GlobalTheory.BSP.LevH

namespace GlobalTheory.BSP.LevH

theorem descent_at_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ m : ℕ, letI := (qmap h m).toAlgebra; ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m), (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ m))).mulVec fun i => qmap q m (z i)) ∧ Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧ IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  intro l _ K bk d S B C D h f p q hc hpo m
  refine lev_prism h p q hc hpo m d (S.ε (p.comp f) (q.comp f))
    ⟨⟨S.ε (p.comp f) (q.comp f), S.ε (q.comp f) (p.comp f), by rw [S.ε_trans, S.ε_refl],
      by rw [S.ε_trans, S.ε_refl]⟩, rfl⟩ ?_
  intro T q₁₂ q₂₃ q₁₃ q₃ e1 e2 e3 e4
  have a1 : q₂₃.comp (p.comp f) = q₁₂.comp (q.comp f) := by rw [← hom_comp_assoc, e1, hom_comp_assoc]
  have a2 : q₂₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e2]
  have a3 : q₁₃.comp (p.comp f) = q₁₂.comp (p.comp f) := by rw [← hom_comp_assoc, e3, hom_comp_assoc]
  have a4 : q₁₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e4]
  rw [S.ε_nat, S.ε_nat, S.ε_nat, a1, a2, a3, a4, S.ε_trans]

end GlobalTheory.BSP.LevH
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isStablePrismHom_of_finite_product_components : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∀ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) → ∀ (B : Obj l R) (h : Hom B Q), (∀ i, Stable ((π i).comp h)) → Stable h := by
  first | exact @GlobalTheory.ProdStable.prodStable | exact GlobalTheory.ProdStable.prodStable | (intros; apply GlobalTheory.ProdStable.prodStable <;> assumption)
end
