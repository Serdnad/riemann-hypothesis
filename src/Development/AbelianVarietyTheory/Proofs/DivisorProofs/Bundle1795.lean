module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishOfTrivialFlags
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitSatake

theorem hasSatGL_of_isCompAlong_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ →
    ∀ T : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ₁ T → GlobalTheory.LFun.HasSatGL w ρ₂ T := by
  intro E _ _ _ n π hπ w hw V W _ _ _ _ ρ₁ ρ₂ h₁ h₂ T hT
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  let P : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have key : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ →
      ∃ f : τ.IntertwiningMap (P.rep.comp s), f ≠ 0 := by
    rintro X _ _ τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict π hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key ρ₁ h₁
  obtain ⟨f', hf'⟩ := key ρ₂ h₂
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  obtain ⟨q⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ P.rep s ρ₁ ρ₂ P.isIrreducible_rep h₁.1 h₂.1 hcomm f hf).2 f' hf'
  exact GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv q.toLinearEquiv
    (fun g x => LinearMap.congr_fun (q.toIntertwiningMap.isIntertwining' g) x) hT

end GlobalTheory.SplitSatake
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefStab

variable {p : ℕ} [Fact p.Prime]

theorem psi_bound (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : ∃ K : ℝ, ∀ y : GlobalTheory.LKCx.grp G B.β,
    ∀ (w : InfinitePlace G.F) (a b : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
      K * Real.sqrt ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  let f : InfinitePlace G.F → (Fin G.n → ℂ) → ℝ := fun w x =>
    if sigPosH (G.gram_herm w) = 1 then (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
    else -(star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
  have hK : ∀ w, ∃ K : ℝ, ∀ (A : Matrix (Fin G.n) (Fin G.n) ℂ) (s : ℝ), 0 ≤ s →
      (∀ x, f w (A *ᵥ x) = s * f w x) → ∀ a b, ‖A a b‖ ≤ K * Real.sqrt s := by
    intro w
    apply GlobalTheory.LKCx.PsiBound.bound_of_form
    · by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; fun_prop
      · simp only [f, h, if_false]; fun_prop
    · intro t x
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]
      · simp only [f, h, if_false]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]; ring
    · intro x hx
      have hp := B.posR w x hx
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; exact hp.1 h
      · have h2 : (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re < 0 := hp.2 h
        simp only [f, h, if_false]; linarith
  choose K hK using hK
  refine ⟨∑ w, |K w|, fun y w a b => ?_⟩
  set s : ℝ := ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast y.2.2
  set A := G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hA
  have hsim : ∀ x : Fin G.n → ℂ, star (A *ᵥ x) ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ (A *ᵥ x) =
      (s : ℂ) * (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x) := by
    intro x
    have h := GlobalTheory.LKCx.grp_similitude_herm p G w B.β y
    have h' : Aᴴ * GlobalTheory.LKCx.herm G w B.β * A =
        (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) : ℂ) • GlobalTheory.LKCx.herm G w B.β := h
    rw [← GlobalTheory.LKCx.PsiBound.form_conj, h', smul_mulVec, dotProduct_smul, smul_eq_mul, hs, Complex.ofReal_ratCast]
  have hinv : ∀ x, f w (A *ᵥ x) = s * f w x := by
    intro x
    by_cases h : sigPosH (G.gram_herm w) = 1
    · simp only [f, h, if_true]; rw [hsim, Complex.re_ofReal_mul]
    · simp only [f, h, if_false]; rw [hsim, Complex.re_ofReal_mul]; ring
  calc ‖A a b‖ ≤ K w * Real.sqrt s := hK w A s hs0.le hinv a b
    _ ≤ |K w| * Real.sqrt s := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
    _ ≤ (∑ u, |K u|) * Real.sqrt s := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun u => |K u|) (fun u _ => abs_nonneg _) (Finset.mem_univ w))
        (Real.sqrt_nonneg _)

theorem isTest_indicator_comm (G : HTGroup p) (K' : Subgroup (Gr G 1))
    (hK : Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw)) :
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' (Set.indicator (K' : Set (Gr G 1)) 1) := by
  have hθ : ∀ g, sigG G 1 g = g := GlobalTheory.LKCx.sigG_one G
  refine ⟨hK, ?_, fun k hk g => ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩; rw [hθ]; exact hk
  · rw [hθ]
    by_cases hg : g ∈ K'
    · have h' : k⁻¹ * g * k ∈ K' := K'.mul_mem (K'.mul_mem (K'.inv_mem hk) hg) hk
      simp [Set.indicator_apply, hg, h']
    · have h' : k⁻¹ * g * k ∉ K' := fun h => hg (by
        have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
        rw [e]; exact K'.mul_mem (K'.mul_mem hk h) (K'.inv_mem hk))
      simp [Set.indicator_apply, hg, h']
  · set K₀ := KHT p G.m G.n 1 G.Fw
    haveI : (K₀.subgroupOf K').FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hK.2
    haveI : Finite (K' ⧸ K₀.subgroupOf K') := Subgroup.finite_quotient_of_finiteIndex
    haveI : Fintype (K' ⧸ K₀.subgroupOf K') := Fintype.ofFinite _
    refine ⟨Finset.univ.image fun q : K' ⧸ K₀.subgroupOf K' => ((Quotient.out q : K') : Gr G 1), fun g hg => ?_⟩
    have hgK : g ∈ K' := by
      by_contra hn; exact hg (by simp [Set.indicator_apply, hn])
    set q : K' ⧸ K₀.subgroupOf K' := QuotientGroup.mk ⟨g, hgK⟩
    have hq : (Quotient.out q)⁻¹ * (⟨g, hgK⟩ : K') ∈ K₀.subgroupOf K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hq
    refine ⟨((Quotient.out q : K') : Gr G 1), Finset.mem_image_of_mem _ (Finset.mem_univ _), 1, K₀.one_mem, _, hq,
      ?_⟩
    simp

theorem finite_locPart : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
    Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  intro p _ G _ L K' hK B x
  have hp : p.Prime := Fact.out
  obtain ⟨xx, tt, hx, heq⟩ : ∃ (xx : (AfP p ⊗[ℚ] G.C)ˣ) (tt : (AfP p)ˣ) (hx : Triv G (AfP p) B.β xx tt),
      B.emb = B.embAt xx tt hx := ⟨_, _, B.trivAf.choose_spec.choose_spec, rfl⟩
  set fK : G.GAf → ℂ := Set.indicator (L.K.toSubgroup : Set G.GAf) 1 with hfK
  set fK' : Gr G 1 → ℂ := Set.indicator (K' : Set (Gr G 1)) 1 with hfK'
  have hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup fK := isTest_indicator _ _ (by simp)
  have hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' fK' := isTest_indicator_comm G K' hK
  set S : Set (GlobalTheory.LKCx.grp G B.β) := {y | fK (x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1) ≠ 0 ∧
    fK' (x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2) ≠ 0} with hS
  have hSfin : S.Finite := by
    obtain ⟨D, hD, hAf⟩ := GlobalTheory.LKCx.BoundedDen.main p G B.β xx tt hx L fK hf x.1
    obtain ⟨k, hP⟩ := GlobalTheory.AtP.main p G B.β K' fK' hf' x.2
    obtain ⟨R, hR⟩ := GlobalTheory.CoordArch.coord_bound p G
    obtain ⟨Kb, hKb⟩ := psi_bound G B
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = D * p ^ k := ⟨_, rfl⟩
    have hN : 0 < N := hNdef ▸ Nat.mul_pos hD (pow_pos hp.pos k)
    obtain ⟨R', hR'⟩ : ∃ R' : ℝ,
        R' = |R| * (Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N)) := ⟨_, rfl⟩
    let φ : GlobalTheory.LKCx.grp G B.β → (Fin (Module.finrank ℚ G.C) → ℚ) :=
      fun y => (Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
    have hφ : Function.Injective φ := fun y y' h =>
      GlobalTheory.FinFix.grp_val_injective G B.β ((Module.finBasis ℚ G.C).repr.injective (Finsupp.ext fun i => congrFun h i))
    refine Set.Finite.subset
      (Set.Finite.preimage hφ.injOn (Set.Finite.pi fun _ => GlobalTheory.FinFix.finite_den_bdd N hN R')) ?_
    rintro y ⟨hf1, hf2⟩
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [hNdef, ← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hN) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
      have h3 : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have := mul_le_mul_of_nonneg_right h2 hs.le
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one] at this
      exact_mod_cast h3
    intro i _
    obtain ⟨m2, hm2⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD (φ y i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    refine ⟨⟨m2, ?_⟩, ?_⟩
    · rw [hNdef, mul_comm]; exact hm2
    · show |((φ y i : ℚ) : ℝ)| ≤ R'
      refine (hR _ i).trans ?_
      have hb : ∀ w a b, ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤ max Kb 0 * Real.sqrt N := by
        intro w a b
        exact (hKb y w a b).trans
          (mul_le_mul (le_max_left _ _) (Real.sqrt_le_sqrt hsN) (Real.sqrt_nonneg _) (le_max_right _ _))
      have hsum : ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
          Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N) := by
        calc _ ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, max Kb 0 * Real.sqrt N :=
              Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hb w a b
          _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
      have hnn : 0 ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ := by positivity
      rw [hR']
      calc R * _ ≤ |R| * _ := mul_le_mul_of_nonneg_right (le_abs_self R) hnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg R)
  have hsub : ((GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x : Subgroup (G.GAf × Gr G 1)) :
      Set (G.GAf × Gr G 1)) ⊆ B.emb '' S := by
    intro e he
    rw [SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map] at he
    obtain ⟨⟨y, rfl⟩, ⟨c, hc, hce⟩⟩ := he
    rw [Subgroup.mem_prod] at hc
    have hc' : x⁻¹ * B.emb y * x = c := by
      rw [← hce]; simp [MulAut.conj_apply, mul_assoc]
    have he1 : (B.emb y).1 = GlobalTheory.LKCx.toAfF G B.β xx tt hx y := by rw [heq]; rfl
    have he2 : (B.emb y).2 = GlobalTheory.LKCx.toP1 G B.β y := by rw [heq]; rfl
    have h1 : x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1 = c.1 := by
      rw [← he1, ← hc']; rfl
    have h2 : x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2 = c.2 := by
      rw [← he2, ← hc']; rfl
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · rw [hfK, h1, Set.indicator_of_mem hc.1]; exact one_ne_zero
    · rw [hfK', h2, Set.indicator_of_mem hc.2]; exact one_ne_zero
  exact ((hSfin.image _).subset hsub).to_subtype

end GlobalTheory.DefStab
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.splitPart_baseLinks_of_primitiveRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s : ℕ, A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ A3.A.fam.Ok s ∧ BaseLinks R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.LowRow.baseLinks_of_prims | exact GlobalTheory.LowRow.baseLinks_of_prims | (intros; apply GlobalTheory.LowRow.baseLinks_of_prims <;> assumption)
end

section

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpan

theorem exists_form {G Γ W X Y : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [AddCommGroup Y]
    [Module ℂ Y] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (h : G)
    (hfin : Finite (Bridge.stab ι J h)) (w : W) (p : X → G) (Φ : X → W →ₗ[ℂ] Y) (v : Y)
    (law : ∀ x γ (k : J), p x = ι γ * h * k → Φ x (ρ γ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • v) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, ∃ N : G → ℕ, (∀ x, Φ x (f (p x)) = (N (p x) : ℂ) • v) ∧
      ∀ γ (k : J), N (ι γ * h * k) ≠ 0 := by
  let S : G → Set Γ := fun x => {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}
  have hS : ∀ x, (S x).Finite := by
    intro x
    rcases (S x).eq_empty_or_nonempty with e | ⟨γ₀, h₀⟩
    · rw [e]; exact Set.finite_empty
    · refine (Set.finite_range fun δ : Bridge.stab ι J h => γ₀ * δ.1).subset fun γ hγ => ⟨⟨γ₀⁻¹ * γ, ?_⟩, by simp⟩
      rw [Bridge.mem_stab]
      have := J.mul_mem h₀ (J.inv_mem hγ)
      convert this using 1
      simp only [map_mul, map_inv]
      group
  let term : G → Γ → W := fun x γ =>
    if hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J then ((χ ⟨_, hm⟩ : ℂˣ) : ℂ) • ρ γ w else 0
  have hsupp : ∀ x, Function.support (term x) ⊆ (hS x).toFinset := by
    intro x γ hγ
    by_contra hn
    have : ¬ h⁻¹ * (ι γ)⁻¹ * x ∈ J := fun hm => hn ((hS x).mem_toFinset.2 hm)
    exact hγ (dif_neg this)
  have hterm : ∀ δ x (k : J) γ, term (ι δ * x * k) (δ * γ) = ((χ k : ℂˣ) : ℂ) • ρ δ (term x γ) := by
    intro δ x k γ
    have e : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
      simp only [map_mul]; group
    by_cases hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J
    · have hm' : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := e ▸ J.mul_mem hm k.2
      have e' : (⟨_, hm'⟩ : J) = ⟨_, hm⟩ * k := Subtype.ext e
      simp only [term, dif_pos hm, dif_pos hm']
      rw [e', map_mul χ, map_mul ρ, map_smul, smul_smul, Units.val_mul, mul_comm]
      rfl
    · have hm' : ¬ h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := fun hh =>
        hm ((J.mul_mem_cancel_right k.2).1 (e ▸ hh))
      simp only [term, dif_neg hm, dif_neg hm', map_zero, smul_zero]
  refine ⟨fun x => ∑ᶠ γ, term x γ, ?_, fun x => (hS x).toFinset.card, fun x => ?_, fun γ k => ?_⟩
  · intro δ x k
    show ∑ᶠ γ, term (ι δ * x * k) γ = ((χ k : ℂˣ) : ℂ) • ρ δ (∑ᶠ γ, term x γ)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
    have hf : (Function.support (term x)).Finite := (hS x).toFinset.finite_toSet.subset (hsupp x)
    have := (((χ k : ℂˣ) : ℂ) • ρ δ).toAddMonoidHom.map_finsum hf
    refine Eq.trans ?_ this.symm
    exact finsum_congr fun γ => hterm δ x k γ
  · show Φ x (∑ᶠ γ, term (p x) γ) = _

    rw [finsum_eq_sum_of_support_subset _ (hsupp _), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hm : h⁻¹ * (ι γ)⁻¹ * p x ∈ J := (hS _).mem_toFinset.1 hγ
    simp only [term, dif_pos hm]
    rw [map_smul, law x γ ⟨_, hm⟩ (by simp only []; group), smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  · refine (Finset.card_pos.2 ⟨γ, (hS _).mem_toFinset.2 ?_⟩).ne'
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    convert k.2 using 1
    group

theorem law_abstract {H G' W X : Type} [Group H] [Group G'] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (L : W →ₗ[ℂ] (X → ℂ))
    (x h γ k a : H) (hu : h⁻¹ * γ⁻¹ * x = k * a) (c : ℂ) (hk : ρ k⁻¹ = 1) (hh : ρ h⁻¹ = 1) (hx : ρ x = 1)
    (hLk : ∀ w, om (k, 1) (L w) = c • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (w : W) (g : G') :
    om (x, g) (L (ρ γ w)) = om (γ, 1) (c • om (h, g) (L w)) := by
  have e4 : x = γ * h * k * a := by rw [mul_assoc _ k, ← hu]; group
  have e5 : (x, g) = ((γ, 1) : H × G') * ((h, g) * ((k, 1) * (a, 1))) := by
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e4]; simp only [mul_assoc]
  have e6 : ρ a * ρ γ = 1 := by
    have : a = k⁻¹ * h⁻¹ * γ⁻¹ * x := by rw [e4]; group
    rw [this, map_mul, map_mul, map_mul, hx, hk, hh, one_mul, one_mul, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [e5, map_mul om, Module.End.mul_apply, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa,
    ← Module.End.mul_apply (ρ a), e6, Module.End.one_apply, hLk, map_smul]

theorem map_quot {H G : Type} [Group H] [Group G] (p : H →* G) (x h γ : H) (k : G) (e : p x = p γ * p h * k) :
    p (h⁻¹ * γ⁻¹ * x) = k := by
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

theorem kernel_law {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (c : CoefA S) (hc : c.Is) (J : Subgroup (Bridge.Gf S)) (χ : J →* ℂˣ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ J, ∀ w, om (k, 1) (Λ w) = ((χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {h x : GA D S} (hh : h ∈ GfC S) (hx : x ∈ GfC S) (γ : GQ S) (k : J)
    (e : fin S x = Bridge.ratF S γ * fin S h * k) (w : c.W) (g : GA D T) :
    thetaKO om x g (Λ (c.ρ γ w)) = ((χ k : ℂˣ) : ℂ)⁻¹ * thetaKO om h g (Λ w) := by
  refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S (h⁻¹ * (γ : GA D S)⁻¹ * x)).elim fun k' hk0 => hk0.2.elim fun a ha0 => ?_
  have hk := hk0.1
  have ha := ha0.1
  have e2 : fin S k' = k := ha0.2.2.trans (map_quot (finHom S).rangeRestrict x h γ k e)
  have hk' : fin S k' ∈ J := by rw [e2]; exact k.2
  have e3 : (⟨fin S k', hk'⟩ : J) = k := Subtype.ext e2
  have h1 : ∀ w, om (k', 1) (Λ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • Λ w := fun w =>
    (hΛk k' hk hk' w).trans (congrArg (fun z : J => ((χ z : ℂˣ) : ℂ)⁻¹ • Λ w) e3)
  have h2 := law_abstract om c.ρ Λ x h γ k' a ha0.2.1 _ (hc.1 _ (inv_mem hk)) (hc.1 _ (inv_mem hh)) (hc.1 _ hx)
    h1 (hΛa a ha) w g
  refine (congrFun h2 0).trans ?_
  have h3 := hom.om_aut γ γ.2 1 (one_mem _) _ (hom.om_pres (h, g) _ (hΛ w))
  refine (congrFun ((om ((γ : GA D S), 1)).map_smul _ _) 0).trans ?_
  exact congrArg (fun z : ℂ => ((χ k : ℂˣ) : ℂ)⁻¹ * z) h3

theorem ne_zero_of_coset {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (N : G → ℕ) (h y : G)
    (hN : ∀ γ (k : J), N (ι γ * h * k) ≠ 0) (γ : Γ) (u : J) (e : h = ι γ * y * u) : N y ≠ 0 := by
  have := hN γ⁻¹ u⁻¹
  rwa [e, map_inv, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left] at this

theorem coeff_ne_zero {I : Type} [Fintype I] (r : ℕ) (s N : I → ℕ) (hr : r ≠ 0) (hs : ∀ i, s i ≠ 0) (i₀ : I)
    (hN : N i₀ ≠ 0) : ∑ i, (r : ℂ)⁻¹ * (s i : ℂ)⁻¹ * (N i : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < ∑ i, (r : ℝ)⁻¹ * (s i : ℝ)⁻¹ * (N i : ℝ) :=
    Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, by have := hs i₀; positivity⟩
  have h' := Complex.ofReal_ne_zero.2 h.ne'
  push_cast at h'
  exact h'

theorem exists_integral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : MeasureTheory.Measure (GA D S)} {𝓕 : Set (GA D S)}
    (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (Cl : Type) [Fintype Cl] (y : Cl → GA D S)
    (hy : Bridge.IsReps (Bridge.ratF S) (levEnv S β L).J (fun k => fin S (y k)))
    (hyf : ∀ k, Finite (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k))))
    (hh : ∀ k, y k ∈ GfC S) {h : GA D S} (hf : h ∈ GfC S) (w : c.W) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ, ∃ a : ℂ, a ≠ 0 ∧
      ∀ g, ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = a * thetaKO om h g (Λ w) := by
  let Φ : Cl → c.W →ₗ[ℂ] (GA D T → ℂ) := fun k =>
    LinearMap.pi fun g => LinearMap.proj (0 : WO S T) ∘ₗ om (y k, g) ∘ₗ Λ
  have hex := exists_form (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ (fin S h)
    (GlobalTheory.SplitReps.finite_stab_of_reps _ le_rfl hy hyf _) w (fun k => fin S (y k)) Φ
    (fun g => thetaKO om h g (Λ w)) (fun x γ k e => funext fun g =>
      kernel_law hom c hc _ _ Λ hΛ hΛa hΛk hf (hh x) γ k e w g)
  refine hex.elim fun f hf0 => hf0.2.elim fun N hN => ?_
  have hrel : (levEnv S β L).J.relIndex (levEnv S β L).J ≠ 0 := by simp
  have h0 : ∃ k, N (fin S (y k)) ≠ 0 := by
    refine (hy (fin S h)).exists.elim fun k hk => hk.elim fun γ hγ => hγ.elim fun u e => ⟨k, ?_⟩
    exact ne_zero_of_coset (Bridge.ratF S) _ N _ _ hN.2 γ u e
  refine h0.elim fun k₀ hk₀ => ⟨f, hf0.1, _, coeff_ne_zero _
    (fun k => Nat.card (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k)))) (fun k => N (fin S (y k))) hrel
    (fun k => (have := hyf k; Nat.card_pos.ne')) k₀ hk₀, fun g => ?_⟩
  refine (GlobalTheory.LiftUnfold.integral_theta hom hs hp c hc β L hL hf0.1 Λ hΛ hΛa hΛk hν _ Cl y le_rfl hrel hy hh g).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : thetaKO om (y k) g (Λ (f (fin S (y k)))) = (N (fin S (y k)) : ℂ) * thetaKO om h g (Λ w) :=
    congrFun (hN.1 k) g
  rw [h1, ← mul_assoc]

theorem mem_span_of_linear {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (j : I → H)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (T : H →ₗ[ℂ] Y) (y : H) (a : ℂ) (ha : a ≠ 0) (v : Y) (e : T y = a • v) :
    v ∈ Submodule.span ℂ (Set.range fun x => T (j x)) := by
  have h1 : T y ∈ (Submodule.span ℂ (Set.range j)).map T := Submodule.mem_map_of_mem (hj ▸ Submodule.mem_top)
  rw [Submodule.map_span, ← Set.range_comp, e] at h1
  exact (Submodule.smul_mem_iff _ ha).1 h1

theorem span_eq_top_of_model {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (e : H →ₗ[ℂ] Y)
    (he : Function.Injective e) (j : I → H) (x : I → Y) (hj : ∀ i, e (j i) = x i)
    (hx : Submodule.span ℂ (Set.range x) = LinearMap.range e) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine Submodule.map_injective_of_injective he ?_
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, ← hx]
  exact congrArg (fun z => Submodule.span ℂ (Set.range z)) (funext hj)

end GlobalTheory.KernelSpan
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.congruence_on_selfDual_lattice_completion : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  first | exact @GlobalTheory.LatHatCong.cong_on_hat | exact GlobalTheory.LatHatCong.cong_on_hat | (intros; apply GlobalTheory.LatHatCong.cong_on_hat <;> assumption)
end
