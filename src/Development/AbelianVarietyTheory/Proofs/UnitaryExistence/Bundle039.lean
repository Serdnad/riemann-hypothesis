module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DiagDifferent

theorem trace_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (a : E) :
    Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem conj_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : cc (H.rt : E) = -(H.rt : E) := by
  apply GlobalTheory.OneSpace.cc_rt <;> assumption

theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h2 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h1
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  rw [conj_rt] at h2
  have : (2 : E) * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h1 + h2
  exact mul_left_cancel₀ two_ne_zero this

theorem trace_even_real_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (∀ a ∈ I, cc a ∈ I) → cc x = x → ((∀ s ∈ I, cc s = s → ∃ n : ℤ, Algebra.trace ℚ E (x * s) = 2 * n) ↔ ∀ s ∈ I, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) := by
  intro E _ _ _ H I x hI hx
  have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => map_mul _ a b
  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => map_add _ a b
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro h s hs
    have hm : s + cc s ∈ I := Submodule.add_mem (I : Submodule (𝓞 E) E) hs (hI s hs)
    obtain ⟨n, hn⟩ := h (s + cc s) hm (by rw [hadd, hcc, add_comm])
    refine ⟨n, ?_⟩
    have e : x * cc s = cc (x * s) := by rw [hmul, hx]
    rw [mul_add, map_add (f := _), e, trace_conj] at hn
    linarith
  · intro h s hs hcs
    have hm : (H.w0 : E) * s ∈ I := Submodule.smul_mem (I : Submodule (𝓞 E) E) H.w0 hs
    obtain ⟨n, hn⟩ := h _ hm
    refine ⟨n, ?_⟩
    have e : x * s = x * ((H.w0 : E) * s) + cc (x * ((H.w0 : E) * s)) := by
      rw [hmul, hmul, hx, hcs]
      linear_combination (-(x * s)) * cmField_host_element_add_conj_eq_one H
    rw [e, map_add (f := _), trace_conj, hn]
    ring

end GlobalTheory.DiagDifferent
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Tower

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
lemma fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i; simp [fv, TensorProduct.tmul_sub]

omit [NumberField E] in
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i; simp [fv]

omit [NumberField E] in
lemma fv_nsmul (N : ℕ) (x : Fin n → E) : fv F (N • x) = N • fv F x := by
  induction N with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

omit [NumberField E] in
lemma fv_smul (c : 𝓞 E) (x : Fin n → E) :
    fv F (c • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • fv F x := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

omit [NumberField E] in
lemma nsmul_cancel {N : ℕ} (hN : 0 < N) {z u : Fin n → RA F E} (h : N • z = N • u) : z = u := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun t => (N : F)⁻¹ • t) h
  simpa [smul_smul, inv_mul_cancel₀ hN'] using this

omit [NumberField E] in
lemma smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (c : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma exists_div {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ v, fv F v ∈ hat F (M : Set (Fin n → E)) ↔ v ∈ M) {N : ℕ} (hN : 0 < N)
    (x : M) {u : Fin n → RA F E} (hu : u ∈ hat F (M : Set (Fin n → E)))
    (h : fv F (x : Fin n → E) = N • u) : ∃ v : M, x = N • v := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : N • ((N : E)⁻¹ • (x : Fin n → E)) = x := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hN', one_smul]
  have h2 : fv F ((N : E)⁻¹ • (x : Fin n → E)) = u := by
    apply nsmul_cancel hN
    rw [← fv_nsmul, h1, h]
  refine ⟨⟨_, (hM _).1 (h2 ▸ hu)⟩, Subtype.ext ?_⟩
  exact h1.symm

lemma projective_of_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Module.Projective (𝓞 E) L := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) L := inferInstance
  exact Module.Flat.projective_of_finitePresentation

omit [NumberField E] in
lemma mulVec_nsmul (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) (z : Fin n → RA F E) :
    g *ᵥ (N • z) = N • (g *ᵥ z) := map_nsmul g.mulVecLin N z

def rel (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) :
    Submodule (𝓞 E) (L × Λ) where
  carrier := {p | ∃ w ∈ hat F (L : Set (Fin n → E)),
    fv F (p.2 : Fin n → E) = g *ᵥ (fv F (p.1 : Fin n → E) + N • w)}
  zero_mem' := ⟨0, zero_mem _, by simp [fv_zero]⟩
  add_mem' := by
    rintro p q ⟨w, hw, hp⟩ ⟨w', hw', hq⟩
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, fv_add, hp, hq]
    rw [← Matrix.mulVec_add, smul_add]
    congr 1
    abel
  smul_mem' := by
    rintro c p ⟨w, hw, hp⟩
    refine ⟨_, smul_mem_hat L c hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, fv_smul, hp]
    rw [← Matrix.mulVec_smul, smul_add, smul_comm]

end GlobalTheory.AdLat.Tower

open GlobalTheory.AdLat.Tower in
theorem GlobalTheory.AdLat.exists_linear_approx_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (Λ : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L → ∃ f : ℕ → (L →ₗ[𝓞 E] Λ), (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (L : Set (Fin n → E))), fv F (f N a : Fin n → E) = (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (a : Fin n → E) + N • w)) ∧ (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧ ∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v := by
  intro F E _ _ _ _ _ n L g Λ hL hsp hΛ
  obtain ⟨Λ', h1, hΛfg, hΛsp, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨hLc, hLa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hsp
  obtain ⟨hΛc, hΛa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛfg hΛsp
  set G : Matrix (Fin n) (Fin n) (RA F E) := g.val with hG
  have hto : ∀ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u ∈ hat F (Λ : Set (Fin n → E)) := by
    intro u hu
    rw [← SetLike.mem_coe, hhat]
    exact ⟨u, hu, rfl⟩
  have hfrom : ∀ z ∈ hat F (Λ : Set (Fin n → E)), ∃ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u = z := by
    intro z hz
    rw [← SetLike.mem_coe, hhat] at hz
    exact hz
  have hinj : ∀ u u' : Fin n → RA F E, G *ᵥ u = G *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (fun t => ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ t) h
    simp only [hG, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    exact this
  haveI := projective_of_fg L hL
  have key : ∀ N : ℕ, ∃ f : L →ₗ[𝓞 E] Λ, 0 < N → ∀ a : L, ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (f a : Fin n → E) = G *ᵥ (fv F (a : Fin n → E) + N • w) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact ⟨0, fun h => absurd h (by omega)⟩
    have hsurj : Function.Surjective
        ((LinearMap.fst (𝓞 E) L Λ).comp (rel L Λ G N).subtype) := by
      intro a
      obtain ⟨x, hx, w, hw, e⟩ := hΛa N hN _ (hto _ ((hLc a).2 a.2))
      obtain ⟨u, hu, rfl⟩ := hfrom w hw
      refine ⟨⟨(a, ⟨x, hx⟩), -u, neg_mem hu, ?_⟩, rfl⟩
      rw [Matrix.mulVec_add, mulVec_nsmul, Matrix.mulVec_neg, e]
      simp
    obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
    refine ⟨(LinearMap.snd (𝓞 E) L Λ).comp ((rel L Λ G N).subtype.comp s), fun _ a => ?_⟩
    obtain ⟨w, hw, e⟩ := (s a).2
    have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
    rw [ha] at e
    exact ⟨w, hw, e⟩
  choose f hf using key
  refine ⟨f, hf, ?_, ?_⟩
  · intro N m hN hm a
    obtain ⟨w, hw, e⟩ := hf N hN a
    obtain ⟨w', hw', e'⟩ := hf (N * m) (Nat.mul_pos hN hm) a
    obtain ⟨v, hv⟩ := exists_div hΛc hN (f (N * m) a - f N a)
      (hto _ (sub_mem (nsmul_mem hw' m) hw)) (by
        rw [Submodule.coe_sub, fv_sub, e, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub,
          mul_smul]
        congr 1
        abel)
    exact ⟨v, by rw [← hv]; abel⟩
  · intro N hN
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, e⟩ := hf N hN a
      obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc v).2 v.2)
      have e2 : fv F (f N a : Fin n → E) = G *ᵥ (N • u) := by
        rw [mulVec_nsmul, eu, ← fv_nsmul, hv]; rfl
      have e3 := hinj _ _ (e.symm.trans e2)
      exact exists_div hLc hN a (sub_mem hu hw) (by rw [smul_sub, ← e3]; abel)
    · rintro ⟨v, rfl⟩
      exact ⟨f N v, map_nsmul _ _ _⟩
    · obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc a').2 a'.2)
      obtain ⟨x, hx, w, hw, rfl⟩ := hLa N hN u hu
      obtain ⟨w', hw', e'⟩ := hf N hN ⟨x, hx⟩
      obtain ⟨v, hv⟩ := exists_div hΛc hN (a' - f N ⟨x, hx⟩) (hto _ (sub_mem hw hw')) (by
        rw [Submodule.coe_sub, fv_sub, ← eu, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub]
        congr 1
        abel)
      exact ⟨⟨x, hx⟩, v, by rw [← hv]; abel⟩
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.VVRank (pullS isPullSec_pullS)
open GlobalTheory.TwistBaseChange (eq_pullS_of_isPullSec)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaRuleCompare

section Descent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem sec_ext {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

omit [GrpObj A] in
theorem chart_ge {T T' : Over S} (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  have h1 : ((h ▷ A).left ≫ (snd T A).left).base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  rw [← Over.comp_left, whiskerRight_snd] at h1
  exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1

theorem gs_pullS {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((pullS A a h s).f j) = gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    pullS A a h' (pullS A a h s) = pullS A a (h' ≫ h) s :=
  sec_ext fun j => fn_ext fun y hy => by
    refine (gs_pullS h' _ _ y j hy).trans ((gs_pullS h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

end Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

section Auxiliary

variable (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end Auxiliary

section Translates

variable (Xo : Moduli Dw l)

variable {Xo}

end Translates

section Values

variable {Xo : Moduli Dw l} {c : Coeff l}

end Values

end GlobalTheory.ThetaRuleCompare
end
end

section

noncomputable section

namespace GlobalTheory.TangentLinear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

section Comb

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]

theorem smT_prod {κ : Type} (s : Finset κ) (a : S) (u : κ → (overAt x0 (DualNumber S) ⟶ G)) :
    smT x0 a (∏ i ∈ s, u i) = ∏ i ∈ s, smT x0 a (u i) := map_prod (smHom x0 a) u s

theorem smT_sum {κ : Type} (s : Finset κ) (c : κ → S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) :
    smT x0 (∑ i ∈ s, c i) v = ∏ i ∈ s, smT x0 (c i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, smT_add x0 v h0, ih]

theorem combT_combT {m m' : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S) :
    combT x0 (fun i => combT x0 v (fun j => A j i)) N = combT x0 v (A.mulVec N) := by
  simp only [combT, smT_prod, smT_smT]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_sum x0 _ _ _ (hv j)]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _

end Comb

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

theorem isCombAtG_mulVec {m m' : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ j, IsTanAtG t x0 (v j))
    (w : Fin m' → (Sp (DualNumber S) ⟶ t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : Sp (DualNumber S) ⟶ t.G.left) (h1 : ∀ i, IsCombAtG t x0 v (fun j => A j i) (w i))
    (h2 : IsCombAtG t x0 w N w') : IsCombAtG t x0 v (A.mulVec N) w' := by
  have hw : w = fun i => (combT x0 (fun j => ovT (hv j)) (fun j => A j i)).left :=
    funext fun i => ((isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).1 (h1 i)).symm
  subst hw
  rw [isCombAtG_iff, combT_combT x0 _ (fun j => smT_zero_ovT (hv j))] at h2
  exact (isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).2 h2

end Group

theorem isCombAt_mulVec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, IsTanAt x (v j)) {m' : ℕ}
    (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hw : ∀ i, IsCombAt x v (fun j => A j i) (w i))
    (hw' : IsCombAt x w N w') : IsCombAt x v (A.mulVec N) w' :=
  isCombAtG_mulVec (t := Xo.univ.t) (x0 := x) v hv w A N w' hw hw'

end GlobalTheory.TangentLinear
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.span_cuspCentre_arithmeticGroup_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ), (Submodule.span ℤ (FJ.zGam X cu)).FG := by
  first | exact @GlobalTheory.CuspCentre.span_zGam_fg | exact GlobalTheory.CuspCentre.span_zGam_fg | (intros; apply GlobalTheory.CuspCentre.span_zGam_fg <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exponentMatching_independent_of_cuspBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  first | exact @GlobalTheory.CuspBasis.expoMatch_of_basis_change | exact GlobalTheory.CuspBasis.expoMatch_of_basis_change | (intros; apply GlobalTheory.CuspBasis.expoMatch_of_basis_change <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.skew_matrix_multiple_in_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), FJ.IsSkew β → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
  first | exact @GlobalTheory.CuspCentre.exists_nsmul_mem_zGam | exact GlobalTheory.CuspCentre.exists_nsmul_mem_zGam | (intros; apply GlobalTheory.CuspCentre.exists_nsmul_mem_zGam <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_principalCongruence_inter_cuspCentre_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  first | exact @GlobalTheory.CuspCentre.mem_zGam_principal_iff | exact GlobalTheory.CuspCentre.mem_zGam_principal_iff | (intros; apply GlobalTheory.CuspCentre.mem_zGam_principal_iff <;> assumption)
end
