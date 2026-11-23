module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle028
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle029
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)], (∀ a (x y : Γ a), x * y = y * x) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (∀ a, Γ a) Y) (H : ∀ a, Subgroup (Γ a)), τ.IsIrreducible →
    (∀ a, fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a) ≠ ⊥) → ∀ g : ∀ a, Γ a, (∀ a, g a ∈ H a) → τ g = 1 := by
  intro α _ _ Γ _ hcomm Y _ _ τ H hirr hne g hg
  have hfixall : ∀ a (h : H a) (y : Y), τ (Pi.mulSingle a (h : Γ a)) y = y := by
    intro a
    have hc : ∀ (x : Γ a) (g' : ∀ b, Γ b), Pi.mulSingle a x * g' = g' * Pi.mulSingle a x := by
      intro x g'
      funext b
      simp only [Pi.mul_apply]
      exact hcomm b _ _
    let R : Subrepresentation τ :=
      { toSubmodule := fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a)
        apply_mem_toSubmodule := by
          intro g' y hy h
          have hy' := hy h
          simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply,
            MonoidHom.mulSingle_apply] at hy' ⊢
          rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hy'] }
    have hR : R = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top R with h | h
      · exfalso
        apply hne a
        have := congrArg Subrepresentation.toSubmodule h
        exact this
      · exact h
    intro h y
    have hy : y ∈ R.toSubmodule := by
      rw [hR]
      exact Submodule.mem_top
    have := hy h
    simpa using this
  letI : ∀ a, CommGroup (Γ a) := fun a => { (inferInstance : Group (Γ a)) with mul_comm := hcomm a }
  have hs : ∀ (s : Finset α) (y : Y), τ (∏ a ∈ s, Pi.mulSingle a (g a)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      rw [Finset.prod_empty, map_one, Module.End.one_apply]
    | insert a s ha ih =>
      intro y
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply, ih]
      exact hfixall a ⟨g a, hg a⟩ y
  have hg' : g = ∏ a, Pi.mulSingle a (g a) := (Finset.univ_prod_mulSingle g).symm
  ext y
  rw [Module.End.one_apply]
  conv_lhs => rw [hg']
  exact hs Finset.univ y
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel


theorem UpperTheory.weilDeligne_unipotent_monodromy :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (r s : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r) (d' : Fin s → ℕ) (e' : (Σ b, Fin (d' b)) ≃ Fin (d j)) (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N),
    (∀ p q, blk f p < blk f q → (blk e p < blk e q ∨ ∃ p' q', p = e ⟨j, p'⟩ ∧ q = e ⟨j, q'⟩ ∧ blk e' p' < blk e' q')) →
    Subsingleton (Jacquet π (unipRad k f)) →
    Subsingleton (Jacquet ((jac e π).comp (MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) (Jacquet π (unipRad k e))) (unipRad k e')) := by
  intro k _ _ _ _ N V _ _ π r s d e j d' e' t c f hord hsub
  classical
  have hKf : twKer π (unipRad k f) 1 = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  apply Submodule.Quotient.subsingleton_iff.mpr
  have hfblk : ∀ (a : Fin t) (i : Fin (c a)), blk f (f ⟨a, i⟩) = a := fun a i => by simp only [blk, Equiv.symm_apply_apply]
  have heblk : ∀ (a : Fin r) (i : Fin (d a)), blk e (e ⟨a, i⟩) = a := fun a i => by simp only [blk, Equiv.symm_apply_apply]
  have he'blk : ∀ (b : Fin s) (i : Fin (d' b)), blk e' (e' ⟨b, i⟩) = b := fun b i => by simp only [blk, Equiv.symm_apply_apply]
  suffices key : twKer π (unipRad k f) 1 ≤
      (twKer ((jac e π).comp (MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) j))
        (unipRad k e') 1).comap (twKer π (unipRad k e) 1).mkQ by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact key (hKf ▸ Submodule.mem_top)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨n, hn⟩, w, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  obtain ⟨hnf, hnd⟩ := mem_unipRad.mp hn
  have hoff : ∀ p q, p ≠ q → (n : Matrix (Fin N) (Fin N) k) p q ≠ 0 → blk f p < blk f q := by
    intro p q hpq h0
    rcases lt_trichotomy (blk f p) (blk f q) with h | h | h
    · exact h
    · exfalso
      obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective p
      obtain ⟨⟨b, i'⟩, rfl⟩ := f.surjective q
      rw [hfblk, hfblk] at h
      subst h
      rw [hnd a i i'] at h0
      have hii : i = i' := by
        by_contra hii
        exact h0 (Matrix.one_apply_ne hii)
      exact hpq (by rw [hii])
    · exact absurd (mem_parab.mp hnf p q h) h0
  have hdiag : ∀ p, (n : Matrix (Fin N) (Fin N) k) p p = 1 := by
    intro p
    obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective p
    rw [hnd a i i, Matrix.one_apply_eq]
  have hA : n ∈ parab k e := by
    rw [mem_parab]
    intro p q hlt
    by_contra h0
    have hpq : p ≠ q := fun h => by
      subst h
      exact lt_irrefl _ hlt
    rcases hord p q (hoff p q hpq h0) with h | ⟨p', q', rfl, rfl, -⟩
    · exact lt_asymm h hlt
    · rw [heblk, heblk] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨u', hu'eq⟩ : ∃ u', leviProj k e ⟨n, hA⟩ j = u' := ⟨_, rfl⟩
  have hu'e : ∀ i i', (u' : Matrix (Fin (d j)) (Fin (d j)) k) i i' =
      (n : Matrix (Fin N) (Fin N) k) (e ⟨j, i⟩) (e ⟨j, i'⟩) := by
    intro i i'
    rw [← hu'eq, leviProj_apply]
  have hu' : u' ∈ unipRad k e' := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro i i' hlt
      rw [hu'e]
      by_contra h0
      have hii : i ≠ i' := fun h => by
        subst h
        exact lt_irrefl _ hlt
      have hpq : e ⟨j, i⟩ ≠ e ⟨j, i'⟩ := fun h => hii (by simpa using e.injective h)
      rcases hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, h2, h3⟩
      · rw [heblk, heblk] at h
        exact lt_irrefl _ h
      · obtain rfl : i = p' := by simpa using e.injective h1
        obtain rfl : i' = q' := by simpa using e.injective h2
        exact lt_asymm h3 hlt
    · intro b x y
      rw [hu'e]
      by_cases hxy : x = y
      · subst hxy
        rw [hdiag, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hxy]
        by_contra h0
        have hpq : e ⟨j, e' ⟨b, x⟩⟩ ≠ e ⟨j, e' ⟨b, y⟩⟩ := fun h => hxy (by simpa using e.injective h)
        rcases hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, h2, h3⟩
        · rw [heblk, heblk] at h
          exact lt_irrefl _ h
        · obtain rfl : e' ⟨b, x⟩ = p' := by simpa using e.injective h1
          obtain rfl : e' ⟨b, y⟩ = q' := by simpa using e.injective h2
          rw [he'blk, he'blk] at h3
          exact lt_irrefl _ h3
  have hproj : leviProj k e ⟨n, hA⟩ = Pi.mulSingle j u' := by
    funext a
    by_cases ha : a = j
    · subst ha
      rw [Pi.mulSingle_eq_same, hu'eq]
    · rw [Pi.mulSingle_eq_of_ne ha]
      apply Units.ext
      ext i i'
      rw [leviProj_apply, Units.val_one]
      by_cases hii : i = i'
      · subst hii
        rw [hdiag, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hii]
        by_contra h0
        have hpq : e ⟨a, i⟩ ≠ e ⟨a, i'⟩ := fun h => hii (by simpa using e.injective h)
        rcases hord _ _ (hoff _ _ hpq h0) with h | ⟨p', q', h1, -, -⟩
        · rw [heblk, heblk] at h
          exact lt_irrefl _ h
        · exact ha (congrArg Sigma.fst (e.injective h1))
  obtain ⟨L, hLeq⟩ : ∃ L, leviEmb k e (Pi.mulSingle j u') = L := ⟨_, rfl⟩
  have hLpar : L ∈ parab k e := hLeq ▸ leviEmb_mem_parab k e _
  have hLproj : leviProj k e ⟨L, hLpar⟩ = Pi.mulSingle j u' := by
    subst hLeq
    exact leviProj_leviEmb k e _
  have hupar : n * L⁻¹ ∈ parab k e := mul_mem hA (inv_mem hLpar)
  have huproj : leviProj k e ⟨n * L⁻¹, hupar⟩ = 1 := by
    have hsplit : (⟨n * L⁻¹, hupar⟩ : parab k e) = ⟨n, hA⟩ * (⟨L, hLpar⟩ : parab k e)⁻¹ := rfl
    rw [hsplit, map_mul, map_inv, hproj, hLproj, mul_inv_cancel]
  have hu : n * L⁻¹ ∈ unipRad k e := by
    rw [mem_unipRad]
    refine ⟨hupar, fun a i i' => ?_⟩
    have h := leviProj_apply k e ⟨n * L⁻¹, hupar⟩ a i i'
    rw [huproj] at h
    exact h.symm
  have hdelta : deltaHalf k (fun a => Fin (d a)) (Pi.mulSingle j u') = 1 := by
    unfold deltaHalf
    rw [MonoidHom.finsetProd_apply]
    apply Finset.prod_eq_one
    intro a _
    rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
    unfold detChar
    rw [MonoidHom.comp_apply]
    have hdet : Matrix.GeneralLinearGroup.det ((Pi.mulSingle j u' : Levi k (fun a => Fin (d a))) a) = 1 := by
      by_cases ha : a = j
      · subst ha
        rw [Pi.mulSingle_eq_same]
        exact det_eq_one_of_mem_unipRad k hu'
      · rw [Pi.mulSingle_eq_of_ne ha, map_one]
    rw [hdet, map_one]
  have hsplit : π n w - w = (π (n * L⁻¹) (π L w) - π L w) + (π L w - w) := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right]
    abel
  rw [hsplit, map_add (f := _)]
  refine add_mem ?_ ?_
  · rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr]
    · exact zero_mem _
    · exact Submodule.subset_span ⟨⟨n * L⁻¹, hu⟩, π L w, by simp⟩
  · rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply Submodule.subset_span
    refine ⟨⟨u', hu'⟩, Submodule.Quotient.mk w, ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
    rw [show jac e π = twist (jacU e π) (deltaHalf k (fun a => Fin (d a)))⁻¹ from rfl, twist_apply,
      MonoidHom.inv_apply, hdelta, inv_one, Units.val_one, one_smul, ← hLeq]
    rfl
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (b : ℕ) (s : _root_.Formalism.ConjugateSelfDual.G F Ω),
    ‖((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1‖ ≤ ‖((p ^ b : ℕ) : Qbar p)‖ → ∀ ζ : Ω, ζ ^ p ^ b = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ p _ b s h ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (p ^ i) := fun i => inferInstance
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [pow_zero, pow_one] at hζ
    rw [hζ, map_one]
  set j : ℤ_[p] := ((cycZ F Ω p s : ℤ_[p]ˣ) : ℤ_[p]) with hj
  have hn : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖ = ‖x‖ := fun x => PadicAlgCl.norm_extends p x
  have e1 : ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1 = algebraMap ℚ_[p] (PadicAlgCl p) (((j - 1 : ℤ_[p])) : ℚ_[p]) := by
    rw [show ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (j : ℚ_[p]) from rfl]
    simp
  have e2 : ((p ^ b : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) ((((p : ℤ_[p]) ^ b : ℤ_[p])) : ℚ_[p]) := by
    simp
  rw [e1, e2, hn, hn] at h
  have h' : ‖j - 1‖ ≤ (p : ℝ) ^ (-(b : ℤ)) := by
    rw [← PadicInt.norm_p_pow]
    exact h
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (j - 1) b).mp h'
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hspec := cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (_root_.Formalism.ConjugateSelfDual.G F Ω) Ω s) ζ hζ
  have hone : (p ^ b : ℕ) ≠ 1 := by
    have := Nat.one_lt_pow hb.ne' (Fact.out : p.Prime).one_lt
    omega
  have hval : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (_root_.Formalism.ConjugateSelfDual.G F Ω) Ω s)).val.toZModPow b).val = 1 := by
    have hj' : (cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (_root_.Formalism.ConjugateSelfDual.G F Ω) Ω s)).val = j := rfl
    rw [hj', hmem]
    exact ZMod.val_one'' hone
  rw [hval, pow_one] at hspec
  exact hspec
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_inter {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N) (h : ∀ x, f (T x) = T' (f x))
    (p : Polynomial ℂ) (x : M) : f (Polynomial.aeval T p x) = Polynomial.aeval T' p (f x) :=
  _root_.UpperTheory.Reformulated.B.Qe22.aeval_inter f T T' h p x

theorem UpperTheory.siegelLevi_block_aeval_stable :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S Z : Submodule ℂ (archSmooth K n)) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), (∀ ψ ∈ Z, ∀ g ∈ Γ, ∀ m, ψ.1 (g * emb e m) = 0) → (∀ τ u, AlgMod S Z (archCapBlock D e τ u)) → Centre (slSp e Γ S) := by
  intro K _ _ a n e Γ S Z ι _ D hZ hS z hz
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ {x | ∃ τ u, x = capOp D a τ u} ?_ ?_ _ (UpperTheory.centerU_action_mem_adjoin_capOp K a ι D z hz)
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨σ, v, rfl⟩
    exact Zc_comm (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D τ u) (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D σ v)
  · rintro _ ⟨τ, u, rfl⟩
    obtain ⟨p, hp, hpS⟩ := hS τ u
    refine ⟨p, hp, fun x hx => ?_⟩
    have hle : slSp e Γ S ≤ LinearMap.ker (Polynomial.aeval (capOp D a τ u) p) := by
      refine Submodule.span_le.2 ?_
      rintro φ ⟨ψ, hψ, g, hg, hφ⟩
      obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
      have hfφ : φ = f ψ := Subtype.ext (funext fun m => (hφ m).trans (hf ψ m).symm)
      have hgen : ∀ i j y, f (gen D (lam K n) τ (e i) (e j) y) = gen D (lam K a) τ i j (f y) := fun i j y =>
        gen_inter D (lam K n) (lam K a) τ (e i) (e j) i j (f ∘ₗ LinearMap.applyₗ y) (LinearMap.applyₗ (f y))
          fun t => by
            change f (lam K n (Matrix.single (e i) (e j) t) y) = lam K a (Matrix.single i j t) (f y)
            rw [← matrixExtendByZero_single, hl]
      have hq : ∀ y, f (archCapBlock D e τ u y) = capOp D a τ u (f y) :=
        UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ hgen u
      change Polynomial.aeval (capOp D a τ u) p φ = 0
      rw [hfφ, ← aeval_inter f _ _ hq]
      exact Subtype.ext (funext fun m => (hf _ m).trans (hZ _ (hpS ψ hψ) g hg m))
    exact hle hx
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_automorphic_properties :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), Bdd S → Sat S → ctSp r S ≤ NInv K (r + s) r ∧ Growth (ctSp r S) ∧ Level (ctSp r S) ∧ Sat (ctSp r S) ∧ ∀ ψ ∈ ctSp r S, ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g, ψ.1 (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) = ψ.1 g := by
  intro K _ _ r s S hB hS
  have hrt : ∀ (φ φ' : AdelicGLn.AdelicGL K (r + s) → ℂ) (k : AdelicGLn.AdelicGL K (r + s)),
      (∀ x, φ' x = φ (x * k)) → ∀ g, constantTerm r φ (g * k) = constantTerm r φ' g := by
    intro φ φ' k h g
    unfold constantTerm
    simp only [h, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro ψ ⟨φ, hφ, e⟩ X g
    rw [e]
    exact UpperTheory.constantTerm_unipotent_left_invariant K _ r φ.1 (hB.left φ hφ) X g
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨φ, hφ, e⟩ := h
      rw [e]
      exact UpperTheory.hasModerateGrowth_constantTerm K _ r φ.1 (hB.growth φ hφ)
    | zero => exact hasModerateGrowth_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c
  · obtain ⟨L, hL, h⟩ := hB.level
    refine ⟨L, hL, fun ψ hψ u hu g => ?_⟩
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact hrt φ.1 φ.1 _ (fun x => (h φ hφ u hu x).symm) g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
  · intro k hk ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      refine Submodule.subset_span ⟨rt k φ, hS k hk φ hφ, funext fun g => ?_⟩
      rw [rt_apply, e]
      exact hrt φ.1 _ k (rt_apply k φ) g
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · intro ψ hψ γ₁ γ₂ g
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact UpperTheory.constantTerm_levi_rational_left_invariant K r s φ.1 (hB.left φ hφ) γ₁ γ₂ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
end
