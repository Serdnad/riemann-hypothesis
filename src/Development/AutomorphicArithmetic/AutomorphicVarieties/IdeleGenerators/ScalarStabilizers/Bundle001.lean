module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

theorem UpperTheory.V.Sd.Hm.trzero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F), IsOfFinOrder ω → ∀ φ : TR.Sm F 2,
        (∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
        ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0 := by
  intro F _ _ _ ω hω φ hφ v
  classical
  rw [← lie_scalar hω hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

theorem UpperTheory.V.Sd.Hm.mulsm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ ψ : TR.Sm F a),
        φ.1 * ψ.1 ∈ TR.Sm F a ∧ ∀ (χ : TR.Sm F a), χ.1 = φ.1 * ψ.1 → ∀ X : TR.Lie F a,
          (TR.lie F a X χ).1 = (TR.lie F a X φ).1 * ψ.1 + φ.1 * (TR.lie F a X ψ).1 := by
  intro F _ _ _ a φ ψ
  have e : ∀ g, TR.chart (φ.1 * ψ.1) g = TR.chart φ.1 g * TR.chart ψ.1 g := by
    intro g
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [TR.chart, h]
  have v : ∀ (f : GA F a → ℂ) g, TR.chart f g (TR.oneL F a) = f g := by
    intro f g
    have h := TR.chart_val f g 1
    rw [map_one, mul_one] at h
    exact h
  refine ⟨fun g => ?_, fun χ hχ X => ?_⟩
  · rw [e]
    exact (φ.2 g).mul (ψ.2 g)
  · funext g
    change TR.lieD X χ.1 g = TR.lieD X φ.1 g * ψ.1 g + φ.1 g * TR.lieD X ψ.1 g
    unfold TR.lieD
    rw [hχ, e, fderiv_mul (TR.differentiableAt_chart φ.2 g) (TR.differentiableAt_chart ψ.2 g), v, v]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem stab_open {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (h : {k | ρ k v = v} ∈ nhds (1 : G)) : IsOpen {k | ρ k v = v} :=
  _root_.UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open ρ v h

private theorem fin_mul {X ι : Type*} (S : Submodule ℂ (X → ℂ)) (f g h : ι → S) (e : ∀ i, (h i).1 = (f i).1 * (g i).1)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)))
    (hg : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range h)) := by
  have h1 : ((Submodule.span ℂ (Set.range f)).map S.subtype).FG := (Module.Finite.iff_fg.1 hf).map _
  have h2 : ((Submodule.span ℂ (Set.range g)).map S.subtype).FG := (Module.Finite.iff_fg.1 hg).map _
  have h3 := Module.Finite.iff_fg.2 (h1.mul h2)
  have h4 : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range h)).map S.subtype) := by
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range f)).map S.subtype *
      (Submodule.span ℂ (Set.range g)).map S.subtype) (Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.subtype_apply, e]
    exact Submodule.mul_mem_mul ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩ ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype (Module.Finite.iff_fg.1 h4))

theorem UpperTheory.V.Sd.Hm.mulaut :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ ψ χ : TR.Sm F a), χ.1 = φ.1 * ψ.1 →
        TR.IsAutForm φ → TR.IsAutForm ψ →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z χ) '' TR.Zalg F a)) → TR.IsAutForm χ := by
  intro F _ _ _ a φ ψ χ e hφ hψ hz
  have hrt : ∀ g, (TR.rt F a g χ).1 = (TR.rt F a g φ).1 * (TR.rt F a g ψ).1 := fun g => by
    funext x
    simp only [TR.rt_apply, Pi.mul_apply, e]
  refine ⟨fun γ g => ?_, ?_, ?_, hz, fun g => ?_⟩
  · rw [e, Pi.mul_apply, Pi.mul_apply, hφ.left, hψ.left]
  · refine stab_open _ _ (Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)
    have h1 : TR.rt F a (finGL F a k) φ = φ := hk.1
    have h2 : TR.rt F a (finGL F a k) ψ = ψ := hk.2
    change TR.rt F a (finGL F a k) χ = χ
    exact Subtype.ext (by rw [hrt, h1, h2, e])
  · exact fin_mul _ _ _ _ (fun k => hrt _) hφ.kfin hψ.kfin
  · obtain ⟨C, N, h1⟩ := hφ.growth g
    obtain ⟨C', N', h2⟩ := hψ.growth g
    refine ⟨C * C', N + N', fun y => ?_⟩
    rw [e, Pi.mul_apply, norm_mul]
    refine (mul_le_mul (h1 y) (h2 y) (norm_nonneg _) ((norm_nonneg _).trans (h1 y))).trans_eq ?_
    ring
end
