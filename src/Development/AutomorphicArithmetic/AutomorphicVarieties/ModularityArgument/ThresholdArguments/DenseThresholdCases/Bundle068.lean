module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.HeckeIdealEnd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdWinA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle008
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFree
public import Formalism.PrimeAboveExistence.LenEqPlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LocLOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RegOfTan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing



section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.EG
namespace UpperTheory.V.Z.Sym.Unl
private theorem quad_pair {K : Type} [Field K] {a d u v : K} (hu : u ^ 2 - a * u + d = 0) (hv : v ^ 2 - a * v + d = 0)
    (hne : u ≠ v) : v + u = a ∧ v * u = d := by
  have h1 : u + v - a = 0 :=
    (mul_eq_zero.1 (by linear_combination hu - hv : (u - v) * (u + v - a) = 0)).resolve_left (sub_ne_zero.2 hne)
  exact ⟨by linear_combination h1, by linear_combination u * h1 - hu⟩
private theorem charpoly_quad {K : Type} [Field K] (B : Matrix (Fin 2) (Fin 2) K) {u : K} (h : B.charpoly.IsRoot u) :
    u ^ 2 - B.trace * u + B.det = 0 := by
  rw [Matrix.charpoly_fin_two] at h
  simpa [Polynomial.IsRoot] using h
private theorem inv_charpoly_root {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) {x : K}
    (h : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x) :
    x ≠ 0 ∧ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x⁻¹ := by
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  exact ⟨hx0, Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi⟩
private theorem norm_xi {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (ξ : G ℚ Ω →* (Qbar l)ˣ) (h : IsOpen (ξ.ker : Set (G ℚ Ω))) (s : G ℚ Ω) : ‖ι (ξ s : Qbar l)‖ = 1 := by
  haveI : Finite (G ℚ Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ s ^ ξ.ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ s)
  have h2 : (ι (ξ s : Qbar l)) ^ ξ.ker.index = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 h0
private theorem det_inv {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 3 ≤ k)
    (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (ξ : G ℚ Ω →* (Qbar l)ˣ)
    (h : Matrix.GeneralLinearGroup.det.comp r = cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) (s : G ℚ Ω) :
    (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * ((ξ s)⁻¹ : (Qbar l)ˣ) := by
  have h1 : Matrix.GeneralLinearGroup.det (r s⁻¹) = (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ := DFunLike.congr_fun h s⁻¹
  have h2 : (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ = cycBar ℚ Ω l s ^ (k - 1) * (ξ s)⁻¹ := by
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, MonoidHom.mul_apply, map_inv, map_inv,
      MonoidHom.inv_apply, MonoidHom.pow_apply, inv_inv]
  have h3 := congrArg Units.val (h1.trans h2)
  simpa using h3
theorem half_of_printed_hida : _root_.UpperTheory.V.Af.HypothesesH' → HalfOf := by
  intro P Ω _ _ _ l _ ι k N _ hk χ hχ g hg ξ c m a π r hO hU hS w hwl A hA s hs x y hx hy heq
  have hp := normV_prime w
  obtain ⟨hx0, hxr⟩ := inv_charpoly_root (r s) hx
  obtain ⟨hy0, hyr⟩ := inv_charpoly_root (r s) hy
  rw [← map_inv] at hxr hyr
  have hp1 : (1 : ℝ) < (normV w : ℝ) := by exact_mod_cast hp.one_lt
  have hnx : 0 < ‖ι x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hny : 0 < ‖ι y‖ := norm_pos_iff.2 (by simpa using hy0)
  by_cases hpN : normV w ∣ N
  · have hb := badAbs k N hk χ hχ g (normV w) hp hpN
    have hR : 0 < ‖g.a (normV w)‖ := by
      have : 0 < ‖g.a (normV w)‖ ^ 2 := by rw [hb]; positivity
      rcases (norm_nonneg (g.a (normV w))).lt_or_eq with h | h
      · exact h
      · rw [← h] at this
        simp at this
    have hn : N.factorization (normV w) ≠ 0 := (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne'
    obtain ⟨u₀, hu₀, hun⟩ := _root_.UpperTheory.V.Z.Sym.W.tieU_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl _ _ hn (norm_pos_iff.1 hR) (hU w) A hA s hs
    have hAq := (over_iff hA _).2 (dvd_refl (normV w))
    have hpl : ¬ normV w ∣ l := fun h => hwl ((mem_iff w l).2 h)
    have hd : ‖ι (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det‖ = (normV w : ℝ) ^ (k - 1) := by
      rw [det_inv hk r ξ hO.det s, cyc_frob hp hAq hpl hs, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast,
        Units.val_inv_eq_inv_val, map_inv₀, norm_inv, norm_xi ι ξ hO.ξ_open s, inv_one, mul_one]
    have hall : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u → ‖ι u‖ = ‖g.a (normV w)‖ := fun u hu => by
      by_cases e : u = u₀
      · rw [e, hun]
      · have h1 := (quad_pair (charpoly_quad _ hu) (charpoly_quad _ hu₀) e).2
        have h2 : ‖ι u₀‖ * ‖ι u‖ = (normV w : ℝ) ^ (k - 1) := by rw [← norm_mul, ← map_mul, h1, hd]
        rw [hun, ← hb] at h2
        exact mul_left_cancel₀ hR.ne' (h2.trans (sq _))
    have e1 := hall _ hxr
    have e2 := hall _ hyr
    rw [map_inv₀, norm_inv] at e1 e2
    have e3 : ‖ι x‖ = ‖ι y‖ := inv_injective (e1.trans e2.symm)
    rw [e3] at heq
    have : (1 : ℝ) * ‖ι y‖ ^ 2 = (normV w : ℝ) * ‖ι y‖ ^ 2 := by rw [one_mul]; exact heq
    have := mul_right_cancel₀ (pow_pos hny 2).ne' this
    exact hp1.ne this
  · obtain ⟨B, hB, e⟩ := hS w hpN
    have hF := _root_.UpperTheory.V.Z.Sym.W.tieS_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl B hB
    have hP := ((hF A hA).2 s hs).trans e
    have hq : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u →
        (ι u) ^ 2 - g.a (normV w) * ι u + χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) = 0 := fun u hu => by
      have h1 := congrArg (Polynomial.eval (ι u)) hP
      have h2 : (Polynomial.eval (ι u) (((r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly).map ι.toRingHom)) = 0 := by
        have := Polynomial.eval₂_at_apply (p := (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly) ι.toRingHom u
        rw [Polynomial.eval_map]
        refine this.trans ?_
        rw [hu.eq_zero, map_zero]
      rw [h2] at h1
      simpa using h1.symm
    have hU' := hq _ hxr
    have hV' := hq _ hyr
    have hfin : ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι x⁻¹‖ ^ 2 := by
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_pow, inv_pow, heq]
      field_simp
    by_cases e : ι x⁻¹ = ι y⁻¹
    · rw [e] at hfin
      have h3 : ‖ι y⁻¹‖ ≠ 0 := by rw [map_inv₀, norm_inv]; exact (inv_pos.2 hny).ne'
      have : (1 : ℝ) * ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι y⁻¹‖ ^ 2 := by rw [one_mul]; exact hfin
      have := mul_right_cancel₀ (pow_ne_zero 2 h3) this
      exact hp1.ne this
    · obtain ⟨h1, h2⟩ := quad_pair hU' hV' e
      exact goodHalf k N hk χ hχ g hg (normV w) hp hpN _ _ h1 h2 hfin
end UpperTheory.V.Z.Sym.Unl
end
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv
private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
private theorem flag_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (κ : Fin n → ↥H →* kˣ) (g : GL (Fin n) k)
    (hg : ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
      ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)) :
    W.HasFlag ((tw r χ).comp H.subtype) fun i => κ i * χ.comp H.subtype := by
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := (hg s).1 i j hij
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [conj_tw, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 i
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
    exact mul_comm _ _
private theorem pow_fixes (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ (s : _root_.Formalism.ConjugateSelfDual.G F Ω) (ζ : Ω), ζ ^ M = 1 → (s ^ k) ζ = ζ := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine ((Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet).subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M by omega)] using hζ
  haveI : Finite {ζ : Ω // ζ ^ M = 1} := hfin
  let f : _root_.Formalism.ConjugateSelfDual.G F Ω →* Equiv.Perm {ζ : Ω // ζ ^ M = 1} :=
    { toFun := fun s => Equiv.Perm.subtypePerm (s : Ω ≃ₐ[F] Ω).toEquiv fun x => by
        change s x ^ M = 1 ↔ x ^ M = 1
        rw [← map_pow, map_eq_one_iff _ (s : Ω ≃ₐ[F] Ω).injective]
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1}), Nat.card_pos, fun s ζ hζ => ?_⟩
  have h1 : f (s ^ Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1})) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg (fun p : Equiv.Perm {ζ : Ω // ζ ^ M = 1} => (p ⟨ζ, hζ⟩ : Ω)) h1
theorem UpperTheory.V.Z.J.free_at_of_unlinked_of_automorphic_cyclotomic_twist :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (a : ℤ) (M : ℕ) (m : Fin n → ℤ), Continuous r →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw r (cycBar F Ω l ^ a)) → 1 ≤ M → StrictAnti m → Unl l M m r → FreeAt l r := by
  intro P F Ω _ _ _ _ _ _ l _ hl ι n hn r a M m hr haut hM hm hun A' hA'
  obtain ⟨w, hw', hw⟩ := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A' l).2 hA'
  obtain ⟨A, hA, κ, ⟨χ, hk, ⟨g, hg⟩, hκ⟩, hne⟩ := hun w hw
  have hAl : A.valuation (l : Ω) < 1 := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A l).1 ⟨w, hA, hw⟩
  obtain ⟨k, hk0, hkf⟩ := pow_fixes F Ω hM
  have hz : Continuous fun s : _root_.Formalism.ConjugateSelfDual.G F Ω => ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ F Ω l)
  have hcyc : Continuous fun s : _root_.Formalism.ConjugateSelfDual.G F Ω => (cycBar F Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : _root_.Formalism.ConjugateSelfDual.G F Ω => cycBar F Ω l s ^ a := (cont_units _ hcyc).zpow a
  have hc : Continuous (tw r (cycBar F Ω l ^ a)) := by
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  obtain ⟨s, hs1, hs2⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar P F Ω l hl ι n hn _ hc haut A hAl
    (fun i => κ i * (cycBar F Ω l ^ a).comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) (fun i => m i + a) k
    (flag_tw r _ _ κ g hg)
    (fun i j hij => by have := hm hij; dsimp only; omega) hk0
    (fun i s hs => by
      show (κ i s * cycBar F Ω l s ^ a * cycBar F Ω l s ^ (-(m i + a))) ^ k = 1
      rw [hκ i s hs, mul_right_comm _ (χ i s), ← zpow_add, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul,
        ← map_pow]
      exact hk i _ (hkf s))
    (by
      intro i j e
      apply hne i j
      rw [mul_right_comm] at e
      exact mul_right_cancel e)
  have hb : cycBar F Ω l s = 1 := by
    simp only [cycBar, MonoidHom.comp_apply, hs1, map_one]
  have hfr : Pr.FreeRatios fun i => κ i s := by
    have e : (fun i => (κ i * (cycBar F Ω l ^ a).comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) s) = fun i => κ i s := by
      funext i
      show κ i s * cycBar F Ω l s ^ a = κ i s
      rw [hb, one_zpow, mul_one]
    rwa [e] at hs2
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hw'
  refine ⟨t * s * t⁻¹, ?_, ?_, fun i => κ i s, hfr, ?_⟩
  · rw [mem_Dec, mul_smul, inv_smul_smul, mul_smul, mem_Dec.1 s.2]
  · rw [map_mul, map_mul, hs1, mul_one, map_inv, mul_inv_cancel]
  · have e : r (t * s * t⁻¹) = (r t * g⁻¹) * (g * r s * g⁻¹) * (r t * g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    show (r (t * s * t⁻¹)).val.charpoly = _
    rw [e, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
end
end

section




section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Ws.Eb
private theorem tan_one {K H : Type} [CommRing K] [Group H] {n : ℕ} {ρ : H →* GL (Fin n) K} {y : H → Matrix (Fin n) (Fin n) K}
    {ρ' : H →* GL (Fin n) (DualNumber K)} (h : IsTan ρ y ρ') (g : H) (hg : ρ' g = 1) : y g = 0 := by
  have e1 := h g
  rw [hg] at e1
  have e2 : (ρ g : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    have := congrArg TrivSqZeroExt.fst (e1 i j)
    by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
  ext i j
  have := congrArg TrivSqZeroExt.snd (e1 i j)
  rw [e2, mul_one] at this
  by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
private theorem at_l (hP : Loc.LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n}
    (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (hΛ : ∀ a, (x' (Λ.toPair B.u a)).snd = 0)
    {ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)} {y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} {ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))}
    (hcont : Continuous ρ) (hy : y ∈ Z1 (Loc.adGL ρ)) (htan : IsTan ρ y ρ') {P : GL (Fin n) (PadicAlgCl l)}
    {R : Representation (PadicAlgCl l) F.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))} (hR : IsAdExt F ρ P R)
    {z : F.Γ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} (hzy : ∀ g : F.G₀, z g = y g) (v : F.Vl)
    (hfl : W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i))
    (m : Fin n → ℤ) (k : ℕ) (hm : ∀ i j, i < j → m j + 2 ≤ m i) (hk : 0 < k) (φ : F.Gv v →* Formalism.BasicNotions.Loc.GQ l)
    (hφ : Topology.IsOpenEmbedding φ) (h1 : ∀ g, φ g ∈ Loc.Iq l ↔ g ∈ F.Iv v)
    (h2 : ∀ i, ∀ g ∈ F.Iv v, (W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) g *
      Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) :
    (fun g : F.Gv v => z (F.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (F.η.ker.subtype.comp (F.φ v)) :
      Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) := by
  have e1 : (R.comp (F.η.ker.subtype.comp (F.φ v)) : Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) =
      Loc.adGL (ρ.comp (F.φ v)) := MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad _ X
  rw [e1]
  simp only [hzy]
  refine locL hP φ hφ (ρ.comp (F.φ v)) (hcont.comp (F.φ_cont v)) _
    ⟨hy.1.comp (F.φ_cont v), fun g h => ?_⟩ _ (htan.comp (F.φ v)) _ m k hfl hm hk fun i g hg => ⟨?_, h2 i g ((h1 g).1 hg)⟩
  · exact (congrArg y (map_mul _ g h)).trans (hy.2 _ _)
  · have e2 := congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) ⟨g, (h1 g).1 hg⟩)
    exact (congrArg (fun b => (x' b).snd) e2).symm.trans (hΛ _)
section
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
private theorem over_l (v : W.Vl l L) : (s.A v).valuation (l : Ω) < 1 := by
  simpa using (s.hA v _).2 v.2
private theorem arith (hP : _root_.UpperTheory.V.Af.HypothesesH') (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : x.Arith fun v j _ => -m v j := by
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using over_l (s := s) v
  refine ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (Ws.Pt.psi_cont x v j) (m v j) k hk (hw v j)
private theorem noRatio (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) (v : W.Vl l L) (i j : Fin n) :
    x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
  intro hij
  have hne : 1 - m v i + m v j ≠ 0 := by
    rcases lt_trichotomy i j with h | h | h
    · have := hm v i j h
      omega
    · subst h
      omega
    · have := hm v j i h
      omega
  obtain ⟨g, hg, hg1⟩ := Ws.Pt.cycIne L Ω l (s.A v) (over_l v) ((1 - m v i + m v j) * k)
    (mul_ne_zero hne (by exact_mod_cast hk.ne'))
  have hgD : g ∈ Dec (F := L) (s.A v) :=
    (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
  have h1 := hw v i ⟨g, hgD⟩ hg
  have h2 := hw v j ⟨g, hgD⟩ hg
  have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
    rw [hij]; rfl
  apply hg1
  have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
      (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
    rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
    congr 2
    ring
  change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
  change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
  rw [e2, mul_pow, h2, one_mul] at h1
  rw [zpow_mul, zpow_natCast, h1]
private theorem par (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Par x := fun v =>
  ⟨m v, k, fun i j h => by have := hm v i j h; omega, hk, fun i j g hg => by
    have e : x.psi v i g / x.psi v j g * cycBar L Ω l g ^ (m v j - m v i) =
        (x.psi v i g * cycBar L Ω l g ^ (-m v i)) / (x.psi v j g * cycBar L Ω l g ^ (-m v j)) := by
      rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
      congr 2
      ring
    rw [e, div_pow, hw v i g hg, hw v j g hg, div_one]⟩
private theorem free (hP : _root_.UpperTheory.V.Af.HypothesesH') (hn : 1 ≤ n) (ι : PadicAlgCl l ≃+* ℂ) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l))
    (m : W.Vl l L → Fin n → ℤ) (hρ : Continuous ρ) (haut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i)
    (hfl : ∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Free V.frame fun v => x.psi v := fun v : W.Vl l L => by
  obtain ⟨g, hg, hf⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar hP L Ω l s.odd ι n hn ρ hρ haut (s.A v) (over_l v) (x.psi v) (m v) k (hfl v)
    (fun i j h => by have := hm v i j h; omega) hk (hw v) (noRatio x m hm k hk hw v)
  refine ⟨g, ?_, hf⟩
  have e : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ (W.Lp L) Ω l (W.resP L Ω g) := DFunLike.congr_fun V.hε _
  exact e.trans hg
end
theorem UpperTheory.V.Th.eigenbasis_rank_four :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) → ∀ (c : Coef l), W.Large L c → ∀ (r : W.Resid V.frame c.O 4) (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.HidaPropsAlt ι J Λ → r.V0ok → (∀ η : V.frame.G₀ →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (V.frame.eps c.O (ResidueField c.O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) → (∃ i j, ∀ m : ℕ, 0 < m → m ≤ 4 → (r.chib i / r.chib j) ^ m ≠ 1) → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin 4) (PadicAlgCl l)) (m : W.Vl l L → Fin 4 → ℤ), J ≤ RingHom.ker x → x.IsRep ρ → Continuous ρ →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) → (∀ v i j, i < j → m v j + 2 ≤ m v i) →
          (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) →
          (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) →
          ∀ q : Ideal B.B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro hU hAd l _ L Ω _ _ _ _ _ _ s V hV hζ c hc r B Λ ι J hJ h0 hC hD4 x ρ m hJx hx hρ haut hv0 hirr hm hfl ⟨k, hk, hkk⟩
  obtain ⟨Λ', ⟨e'⟩⟩ := hU.lam l L Ω s V c 4 r
  obtain ⟨e₁⟩ := lamIso Λ' Λ
  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →ₐ[c.O] Λ.Λ, Function.Bijective e :=
    ⟨(e'.symm.trans e₁ :), (e'.symm.trans e₁).bijective⟩
  refine regOfTan c _ B.B ((Λ.toPair B.u).comp e) J ?_ (fun a ha b hb => ?_) x hJx fun x' hx' hΛ => ?_
  · exact hJ.ring.fin.comp (RingHom.Finite.of_surjective (e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →+* Λ.Λ) he.2)
  · exact hJ.ring.tf (e a) ((map_ne_zero_iff e he.1).2 ha) b hb
  have hΛ' : ∀ a, (x' (Λ.toPair B.u a)).snd = 0 := fun a => by
    obtain ⟨a, rfl⟩ := he.2 a
    exact hΛ a
  have hxx : (dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l)) = (x : B.B →+* PadicAlgCl l) := RingHom.ext hx'
  have hn1 : 1 ≤ 4 := by omega
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := factor V B x ρ hn1 hx hirr
  obtain ⟨ρ', y, hD', hred, hfull', hcont, hy, htan⟩ := liftRep B x' ρ₀ hn1 hfull (by rw [hxx, hD])
  obtain ⟨hO, hI⟩ := relKill B x' ρ' hfull' hD'
  obtain ⟨P', hP'⟩ := relForm B x' ρ' hfull' hD'
  obtain ⟨hP, hrel⟩ := cocRel V.frame c.O ρ₀ y ρ' P' htan hP'
  obtain ⟨R, hR⟩ := adExt V.frame c.O ρ₀ _ hfull hP
  obtain ⟨Z, hZ⟩ := hrel R hR
  obtain ⟨z, hz, hzy⟩ := cocExt V.frame ρ₀ _ R hfull hcont hR y hy Z hZ
  have hinj : ∀ v : V.frame.Vl, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    refine psiInj (s.A v.1) (s.w v.1) (s.hw v.1) ?_ (x.psi v) (m v) k
      (StrictAnti.injective fun i j h => by have := hm v i j h; omega) hk (hkk v)
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  have hfl₀ : ∀ v : V.frame.Vl, W.HasFlag (ρ₀.comp (V.frame.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    exact hfl v
  have hfl' : ∀ v : V.frame.Vl, W.HasFlag (ρ'.comp (V.frame.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i) := fun v =>
    flagDual _ _ (hinj v) (by rw [← hred] at hfl₀; exact hfl₀ v) (hO v)
  have hbk := bkAb V R z hz
    (fun v φ hφ h1 h2 => at_l hU.coh.loc B Λ x' hΛ' hcont hy htan hR hzy v (hfl' v) (m v) k (hm v) hk φ hφ h1 fun i g hg => by
      rw [hxx, h2]
      exact hkk v i g hg)
    (bkAw V hV r R z hz (fun u g hg => (hzy g).trans (tan_one htan g (hI u g hg)))
      fun g hg => (hzy g).trans (cocycle_vanishes_on_inertia_of_point_pseudodeformation V B x ρ₀ h0 hD hcont y hy g hg))
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ₀ := ⟨hcont, hx, ⟨_, arith hU.pr x m hm k hk hkk⟩, haut, by
    rintro _ ⟨g, hg, rfl⟩
    exact hv0 g hg, hfl⟩
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ₀) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ₀)).2 hfull N fun g v hv => hN g trivial v hv
  have hnice := _root_.UpperTheory.V.Th.nice0four_alt ι x ρ₀ hapt hirr₀ (free hU.pr hn1 ι x _ m hρ haut hm hfl k hk hkk) hC hD4
  obtain ⟨X, hX⟩ := hAd l L Ω s V hV hζ c hc 4 (by omega) le_rfl r h0 B ι x ρ₀ hnice (par x m hm k hk hkk) _ R hP hR z hz hbk
  obtain ⟨Q, hQ⟩ := conjOf ρ₀ y ρ' X htan fun g => by rw [← hzy, hX, hR.ad]
  exact constOf B x' ρ₀ ρ' Q hD' hQ hinj hfl₀ hfl'
end
end
