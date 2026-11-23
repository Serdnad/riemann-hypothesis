module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle140
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle422
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaPull

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄

theorem pull_square {R : Type} [CommRing R]
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R}
    {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (m : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₃ (RingHom.id R))
    (b' : CH.Mor F₁ F₄ (RingHom.id R)) (q : CH.Mor F₄ F₃ (RingHom.id R))
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x))
    (n : ℕ) (x : CH.H F₁ n) : b.pull n (m.pull n x) = q.pull n (b'.pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m b n x).1,
    ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b' q n x).1]
  exact CrystallineSemistableComparison.P.prism (m.comp b) (b'.comp q) η hτ n x

theorem pt_nat {P P' : CommRingCat.{0} ⥤ Type} (a : P ⟶ P') {B C : CommRingCat.{0}} (f : B ⟶ C)
    (g : C ⟶ C) (hg : g = 𝟙 C) (y : P.obj B) :
    P'.map g (a.app C (P.map f y)) = P'.map f (a.app B y) := by
  subst hg
  rw [P'.map_id]
  exact ConcreteCategory.congr_hom (a.naturality f) y

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
  (u : Fn.Map F F') (k : Bool) (n : ℕ)

theorem units_pullback_empty_product_one {B B' : Type} [CommRing B] [CommRing B'] (i : B' →+* B) (a : B'ˣ) (ha : a = 1)
    (e : Empty → Bˣ) : (1 : Bˣ) =
      (∏ j, e j) * Units.map (RingHom.id B).toMonoidHom ((1 : Bˣ) ^ 1 * (Units.map i.toMonoidHom a)⁻¹) := by
  subst ha
  simp

def cmpHom (T : El (F.pt κ)) :
    (gT F κ k n ⋙ (pullMorC κ u k n).G).obj T ⟶ ((pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G).obj T where
  φ := RingHom.id _
  u := fun j => j.elim
  comm _ := rfl
  dp := (DPMorphism.id _).isDPMorphism
  hle := fun _ h => h
  pt := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    · exact pt_nat u.u (CommRingCat.ofHom (uJ k T.1.obj n))
        (CommRingCat.ofHom (Ideal.quotientMap _ (RingHom.id _) fun _ h => h))
        (CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))) T.2.1
  hx := fun j => j.elim
  hs := units_pullback_empty_product_one _ _ rfl _
  hv := fun j => j.elim

def cmpNat : gT F κ k n ⋙ (pullMorC κ u k n).G ⟶ (pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G where
  app T := cmpHom κ u k n T
  naturality T T' f := Thick.Hom.ext rfl (funext fun j => j.elim)

theorem beta_pull {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
    (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j) :
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  pull_square (pullMorC κ u k n) (βMor F κ k n) (βMor F' κ k n) (pullMor (u.pt κ) n)
    (cmpNat κ u k n) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaPull
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsFacts

variable {l : ℕ} [Fact l.Prime]

theorem geom_sum_eq_zero {R : Type*} [CommRing R] [IsDomain R] {z : R} {m : ℕ} (h : z ^ m = 1) (h1 : z ≠ 1) :
    ∑ i ∈ Finset.range m, z ^ i = 0 := by
  have e := mul_geom_sum z m
  rw [h, sub_self] at e
  exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 h1)

theorem pow_chain {M : Type*} [Monoid M] {m : ℕ} (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ m = e k) (k j : ℕ) :
    e (k + j) ^ m ^ j = e k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ m j, mul_comm, pow_mul, ← add_assoc, hs, ih]

theorem prim_chain {M : Type*} [CommMonoid M] (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ l = e k) (h0 : e 0 = 1)
    (h1 : e 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (e m) (l ^ m) := by
  cases m with
  | zero => simpa [h0] using IsPrimitiveRoot.one
  | succ k =>
    have a : e (k + 1) ^ l ^ k = e 1 := by
      have := pow_chain e hs 1 k
      rwa [add_comm 1 k] at this
    have b : e (k + 1) ^ l ^ (k + 1) = 1 := by
      have := pow_chain e hs 0 (k + 1)
      rwa [zero_add, h0] at this
    have o : orderOf (e (k + 1)) = l ^ (k + 1) :=
      orderOf_eq_prime_pow (by rw [a]; exact h1) b
    exact o ▸ IsPrimitiveRoot.orderOf _

theorem coeff_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] (a : R) (ha : ¬ IsUnit (a - 1)) (i : ℕ) :
    ¬ IsUnit ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) := by
  have h1 : IsLocalRing.residue R a = 1 := by
    have : IsLocalRing.residue R (a - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 ha)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have h2 : WittVector.map (IsLocalRing.residue R) (WittVector.teichmuller l a - 1 : WittVector l R) = 0 := by
    rw [map_sub, map_one, WittVector.map_teichmuller, h1, map_one, sub_self]
  have h3 : IsLocalRing.residue R ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) = 0 := by
    rw [← WittVector.map_coeff, h2, WittVector.zero_coeff]
  exact (IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3)

variable (l) in
theorem isLocalRing_oc : IsLocalRing (OC l) := ValuationRing.isLocalRing (OC l)

variable (l) in
theorem isLocalRing_ob : IsLocalRing (Ob l) :=
  haveI := isLocalRing_oc l
  GlobalTheory.preTilt_isLocalRing l (OC l)

variable (l) in
theorem pFlat_not_isUnit : ¬ IsUnit (pFlat l) := fun h => by
  have h1 : IsUnit (theta0 l (WittVector.teichmuller l (pFlat l))) := (h.map (WittVector.teichmuller l)).map (theta0 l)
  rw [WittVector.fontaineTheta_teichmuller, untilt_pFlat] at h1
  exact (inferInstance : Fact (¬ IsUnit (l : OC l))).out h1

theorem integral_prime_dvd_epsilon_zero_sub_one (ε : Eps l) : pFlat l ∣ ((ε.e 0 : Ob l) - 1) := by
  have h := ((RL.sharp_cong (base l)).2.1 (ε.e 0 : Ob l) 1).1 (by
    have h0 : (base l).sharp (ε.e 0 : Ob l) = 1 := ε.sharp_e (base l)
    rw [h0, map_one, sub_self]
    exact zero_mem _)
  exact Ideal.mem_span_singleton.1 h

theorem epsilon_one_sub_one_not_isUnit (ε : Eps l) : ¬ IsUnit ((ε.e 1 : Ob l) - 1) := fun h => by
  haveI : CharP (Ob l) l := inferInstance
  have h1 : IsUnit (((ε.e 1 : Ob l) - 1) ^ l) := h.pow l
  have e : (ε.e 1 : Ob l) ^ l = ε.e 0 := by
    have := congrArg Units.val (ε.succ 0)
    rwa [Units.val_pow_eq_pow_val] at this
  rw [sub_pow_char, e, one_pow] at h1
  exact pFlat_not_isUnit l (isUnit_of_dvd_unit (integral_prime_dvd_epsilon_zero_sub_one ε) h1)

theorem theta_e_succ (ε : Eps l) (k : ℕ) :
    theta0 l (WittVector.teichmuller l (ε.e (k + 1) : Ob l)) ^ l = theta0 l (WittVector.teichmuller l (ε.e k : Ob l)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]

theorem qk_succ (ε : Eps l) (k : ℕ) : ε.qk (k + 1) ^ l = ε.qk k := by
  rw [Eps.qk, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ, Eps.qk]

theorem sum_mem_ker (ε : Eps l) :
    ∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i ∈ RingHom.ker (theta0 l) := by

  rw [RingHom.mem_ker, map_sum]
  simp only [map_pow]
  exact geom_sum_eq_zero ((theta_e_succ ε 0).trans ε.one) ε.prim

theorem cris_sum_mem (ε : Eps l) (A : PAlg l) (n : ℕ) :
    A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1 := by
  have e : ∑ i ∈ Finset.range l, ε.qk 1 ^ i =
      algebraMap (Ainf l) (Acris l) (∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, Eps.qk]
  have h := sum_mem_ker ε
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [e, cris_algebraMap, ← hc, map_mul, map_mul]
  change _ * A.toAcr n A.xi ∈ _
  rw [toAcr_xi]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem mu_eq (ε : Eps l) : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i := by
  rw [mul_geom_sum, qk_succ ε 0, Eps.μ]

theorem eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  intro l _ ε
  haveI := isLocalRing_ob l
  exact ⟨fun i => coeff_not_isUnit _ (epsilon_one_sub_one_not_isUnit ε) i, qk_succ ε, cris_sum_mem ε, mu_eq ε,
    prim_chain (fun m => theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (theta_e_succ ε) ε.one ε.prim⟩

end GlobalTheory.CompanionTheory.EpsFacts
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.HeckeEigenspaces

theorem exists_closed_common_ker {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (𝒯 : Set (X →L[ℂ] X)) :
    ∃ Y : Submodule ℂ X, IsClosed (Y : Set X) ∧ ∀ φ, φ ∈ Y ↔ ∀ T ∈ 𝒯, T φ = 0 := by
  refine ⟨{ carrier := {φ | ∀ T ∈ 𝒯, T φ = 0}
            add_mem' := fun {x y} hx hy T hT => by rw [map_add (f := _), hx T hT, hy T hT, add_zero]
            zero_mem' := fun T _ => map_zero T
            smul_mem' := fun c x hx T hT => by rw [map_smul, hx T hT, smul_zero] }, ?_, fun _ => Iff.rfl⟩
  have e : ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X) = ⋂ T ∈ 𝒯, T ⁻¹' {0} := by
    ext φ; simp
  change IsClosed ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X)
  rw [e]
  exact isClosed_biInter fun T _ => isClosed_singleton.preimage T.continuous

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_heckeOp (w : Pl E) {h : GL (Fin a) (w.adicCompletion E) → ℂ} (hh : h ∈ Hecke ℂ (KGL w (n := a))) :
    ∃ T : XB E a →L[ℂ] XB E a, (∀ x, heckeVec (repW a w) (KGL w (n := a)) h x = T x) ∧
      ∀ A : XB E a →L[ℂ] XB E a, (∀ u, Commute A (Rt E a (fl a w u))) → Commute A T := by
  classical
  have hs := Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) hh.2
  refine ⟨∑ c ∈ hs.toFinset, h c.out • Rt E a (fl a w c.out), fun x => ?_, fun A hA => ?_⟩
  · rw [heckeVec, finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · simp
    · intro c hc
      refine Finset.mem_coe.2 (hs.mem_toFinset.2 fun h0 => hc (by simp [h0]))
  · exact Commute.sum_right _ _ _ fun c _ => (hA c.out).smul_right _

theorem hecke_eigenfunctions_closed : G0 → G2c := by
  intro h0 E _ _ _ a w B hB
  have hcomm : ∀ g : GA E a, cLoc w g = 1 → ∀ u, Commute (Rt E a g) (Rt E a (fl a w u)) := fun g hg u => by
    have e := (h0 E a).2.2.2.2.2.2.2.1 w g hg u
    change Rt E a g * Rt E a (fl a w u) = Rt E a (fl a w u) * Rt E a g
    rw [← map_mul, ← map_mul, e]
  choose T hT hC using fun (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ) =>
    exists_heckeOp (a := a) w (Tj_mem_hecke (n := a) p.2 j)
  obtain ⟨Y, hcl, hY⟩ := exists_closed_common_ker
    ({R | (∃ k ∈ KGL w (n := a), R = Rt E a (fl a w k) - 1) ∨
      ∃ (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ), j ≤ a ∧ R = T p j - satEig (qV E w) a B j • 1} :
      Set (XB E a →L[ℂ] XB E a))
  refine ⟨Y, hcl, fun g hg φ hφ => ?_, fun φ => ?_⟩
  · rw [hY] at hφ ⊢
    intro R hR
    have hRc : Commute (Rt E a g) R := by
      rcases hR with ⟨k, -, rfl⟩ | ⟨p, j, -, rfl⟩
      · exact (hcomm g hg k).sub_right (Commute.one_right _)
      · exact (hC p j _ (hcomm g hg)).sub_right ((Commute.one_right _).smul_right _)
    have e : R (Rt E a g φ) = Rt E a g (R φ) := (DFunLike.congr_fun hRc.eq φ).symm
    rw [e, hφ R hR, map_zero]
  · rw [hY]
    constructor
    · intro h
      by_cases hφ : φ = 0
      · exact Or.inl hφ
      · refine Or.inr ⟨hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hB, fun ϖ hϖ j hj => ?_⟩
        · have := h _ (Or.inl ⟨k, hk, rfl⟩)
          simpa [sub_eq_zero] using this
        · have := h _ (Or.inr ⟨⟨ϖ, hϖ⟩, j, hj, rfl⟩)
          rw [hT ⟨ϖ, hϖ⟩ j]
          simpa [sub_eq_zero] using this
    · rintro (rfl | ⟨-, hfix, -, heig⟩) R hR
      · exact map_zero R
      · rcases hR with ⟨k, hk, rfl⟩ | ⟨p, j, hj, rfl⟩
        · have := GlobalTheory.LGrp.mem_fixed.1 hfix k hk
          simpa [sub_eq_zero] using this
        · have := heig p.1 p.2 j hj
          rw [hT p j] at this
          simpa [sub_eq_zero] using this

end GlobalTheory.CompanionTheory.HeckeEigenspaces
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.SmoReg

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem Rt_mul_apply (g h : GA E a) (φ : XB E a) : Rt E a (g * h) φ = Rt E a g (Rt E a h φ) := by
  rw [map_mul]; rfl

theorem polyBd_repI [_root_.NumberField.IsTotallyComplex E] : PolyBd (repI E a) :=
  ⟨1, 0, zero_le_one, fun g x => by
    have : ‖repI E a g x‖ = ‖x‖ := norm_Rt _ _
    simp [this]⟩

theorem conj_stab {G H X : Type} [Group G] [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : H →* G) (c : G →* H) (R : G → X → X) (hR : ∀ g h x, R (g * h) x = R g (R h x))
    (hf : ∀ u, c (f u) = u) (hcomm : ∀ g, c g = 1 → ∀ u, g * f u = f u * g)
    (g : G) (x : X) (hx : {u : H | R (f u) x = x} ∈ 𝓝 (1 : H)) :
    {u : H | R (f u) (R g x) = R g x} ∈ 𝓝 (1 : H) := by
  obtain ⟨k, hk⟩ : ∃ k, k = c g := ⟨_, rfl⟩
  have hg1 : c ((f k)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hf, ← hk, inv_mul_cancel]
  have hcont : Continuous fun u : H => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hat : Tendsto (fun u : H => k⁻¹ * u * k) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    simpa using this
  filter_upwards [hat hx] with u hu
  have key : f u * g = g * f (k⁻¹ * u * k) := by
    have h := hcomm _ hg1 (k⁻¹ * u * k)
    have e : f (k⁻¹ * u * k) = (f k)⁻¹ * f u * f k := by simp only [map_mul, map_inv]
    rw [e] at h ⊢
    have h2 := congrArg (f k * ·) h
    simpa only [mul_assoc, mul_inv_cancel_left] using h2.symm
  have hu' : R (f (k⁻¹ * u * k)) x = x := hu
  change R (f u) (R g x) = R g x
  rw [← hR, key, hR, hu']

theorem lev_Rt [_root_.NumberField.IsTotallyComplex E] (hfl : ∀ (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)),
      cLoc w (fl a w u : GA E a) = u)
    (hcomm : ∀ (w : Pl E) (g : GA E a), cLoc w g = 1 → ∀ u, g * fl a w u = fl a w u * g)
    (S : Finset (Pl E)) (g : GA E a) (φ : XB E a) (hφ : Lev S φ) : Lev S (Rt E a g φ) := by
  intro w hw
  have hx := hφ w hw
  simp only [repW_apply] at hx ⊢
  exact conj_stab (fl a w) (cLoc w) (fun g x => Rt E a g x) Rt_mul_apply (hfl w) (hcomm w) g φ hx

theorem g5b : S2 → G0 → G5b := by
  intro hS2 hG0 E _ _ _ a S
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hG0 E a
  obtain ⟨-, -, -, hgrp, hT, -⟩ := hS2 _ a (XB E a) (repI E a) polyBd_repI
  refine ⟨?_, fun g φ hφ => lev_Rt h4 h8 S g φ hφ, ?_, ?_, ?_⟩
  · intro g φ hφ
    set y := cInf g with hy
    set gf : GA E a := (infGL E a y)⁻¹ * g with hgf
    have hgf1 : cInf gf = 1 := by
      rw [hgf, map_mul, map_inv, h1, ← hy, inv_mul_cancel]
    have hg : g = infGL E a y * gf := by rw [hgf, mul_inv_cancel_left]
    have hc : ∀ (z : GL (Fin a) (Cinf E)) (x : XB E a),
        Rt E a gf (repI E a z x) = repI E a z (Rt E a gf x) := by
      intro z x
      change Rt E a gf (Rt E a (infGL E a z) x) = Rt E a (infGL E a z) (Rt E a gf x)
      rw [← Rt_mul_apply, ← Rt_mul_apply, h7 gf hgf1 z]
    have := hgrp y _ (hT (Rt E a gf) hc φ hφ)
    have e : Rt E a g φ = repI E a y (Rt E a gf φ) := by
      change Rt E a g φ = Rt E a (infGL E a y) (Rt E a gf φ)
      rw [← Rt_mul_apply, ← hg]
    rw [e]
    exact this
  · intro c φ hφ w hw
    filter_upwards [hφ w hw] with u hu
    have hu' : repW a w u φ = φ := hu
    change repW a w u (c • φ) = c • φ
    rw [map_smul, hu']
  · intro φ φ' hφ hφ' w hw
    filter_upwards [hφ w hw, hφ' w hw] with u hu hu'
    have e : repW a w u φ = φ := hu
    have e' : repW a w u φ' = φ' := hu'
    change repW a w u (φ + φ') = φ + φ'
    rw [map_add (f := _), e, e']
  · intro w hw
    filter_upwards with u
    change repW a w u 0 = 0
    rw [map_zero]

end GlobalTheory.CompanionTheory.SmoReg

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.JSInfStep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

variable [_root_.NumberField.IsTotallyComplex E]

def chiInf (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHomClass.toAddMonoidHom (sInf E))

theorem chiInf_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chiInf ψ z = ψ (sInf E z) := rfl

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem chiInf_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E)
    (h : ∀ w, chiInf ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by
    have e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c)) := by
      refine ad_ext ?_ ?_
      · rw [map_mul, pInf_sInf, pInf_sInf]
      · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]
    rw [e]
    exact h _
  obtain ⟨w⟩ := nonempty_pl (E := E)
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0 := by
    change pFin E (algebraMap E (Ad E) d) = 0
    rw [← hd, pFin_sInf]
  have hd0 : d = 0 := (injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

end GlobalTheory.CompanionTheory.JSInfStep

end
end

section


theorem _root_.GlobalTheory.T.right_derivative_calculus_holds : PositivityTheory.RgBcC.RCalc := by
  first | exact @GlobalTheory.CompanionTheory.RCalc.rcalc | exact GlobalTheory.CompanionTheory.RCalc.rcalc | (intros; apply GlobalTheory.CompanionTheory.RCalc.rcalc <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.degBasis_of_degBasisG' : DegBasisG → DegBasis := by
  first | exact @GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | exact GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG <;> assumption)
end
