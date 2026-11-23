module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle910
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle881
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle912
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifC
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem isRayL_top_wideInd_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ),
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  intro F _ _ C Z
  refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
  let g : IdealsIn C → {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} :=
    fun I => ⟨I.1.1, nonZeroDivisors.coe_ne_zero I.1, sup_top_eq _⟩
  have hg : Function.Injective g := fun I J h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} => x.1) h))
  rw [← hg.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} =>
    (wideInd C I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) fun I hI => by
      have : cls I.1 ≠ C := fun h => hI ⟨⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩,
        by rw [← h, cls_of_ne_bot I.2.1]⟩, rfl⟩
      simp [wideInd, this]]
  refine iff_of_eq (congrArg (HasSum · (Z s)) (funext fun I => ?_))
  have h1 : cls (I.1 : Ideal (𝓞 F)) = C := by
    rw [cls_of_ne_bot (nonZeroDivisors.coe_ne_zero I.1)]
    exact I.2
  simp [g, wideInd, h1]

end GlobalTheory.ZetaDenom
end
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_perm_of_blockSize_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  first | exact @GlobalTheory.exists_perm_of_block_bijection | exact GlobalTheory.exists_perm_of_block_bijection | (intros; apply GlobalTheory.exists_perm_of_block_bijection <;> assumption)
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.equiv_of_ne_zero_map_isotypicSumOfCopies : ∀ (H : Type) [Group H] [Finite H] (V V' W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ H V) (τ' : Representation ℂ H V') (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W'), ρ.IsIrreducible → ρ'.IsIrreducible → IsIsotypicOf τ ρ → IsIsotypicOf τ' ρ' → ∀ T : Representation.IntertwiningMap τ τ', T ≠ 0 → Nonempty (Representation.Equiv ρ ρ') := by
  first | exact @GlobalTheory.IsotypicMap.equiv_of_isotypic_map | exact GlobalTheory.IsotypicMap.equiv_of_isotypic_map | (intros; apply GlobalTheory.IsotypicMap.equiv_of_isotypic_map <;> assumption)
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_ne_zero_intertwining_of_commuting_isotypicFactors : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  first | exact @GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero | exact GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero | (intros; apply GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.virtualCharacter_coset_normOne_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  first | (exact @GlobalTheory.Shin.virt_coset_norm_one_single) | (exact GlobalTheory.Shin.virt_coset_norm_one_single) | (intros; apply GlobalTheory.Shin.virt_coset_norm_one_single <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {V : Type} [CommRing V] [IsDomain V]

theorem torsion_points (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) :
    ∃ x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
      (∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
        (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧
      ∀ z : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :) (by simp)) ρ.pt (S.r * S.N)
    ρ.pt_add (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

theorem frames (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) (lb : LBIso A.L (ρ.P.L.pull φ))
    (x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A))
    (hx : ∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
      (ρ.pt a).left) :
    ∃ (rig : LB.Gen (A.L.pull (eSec A.A)))
      (e : ∀ a, LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) (AlgebraicClosure (FractionRing V))).left) (K := Fin 1)
        (fun _ => (x a).left) (fun _ => 1))),
      rig.IsGen ∧ (∀ a, IsTorsFrame A rig (S.r * S.N) (x a) (e a)) ∧
      ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))),
        ∃ t : SecA A (AlgebraicClosure (FractionRing V)) k, ∀ (a : S.Gam) (c : S.R),
          IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) →
          ∀ z J, Good A.L z J → sA t (ptSecT A.A (x a)).left z J =
            @id ((TFK (R := V) (AlgebraicClosure (FractionRing V))).left.presheaf.stalk z)
              (cst (R := V) (AlgebraicClosure (FractionRing V)) z
                ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK c)) *
            (val (powFrame A.A A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  have hh : (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).left ⟶ (baseOver (Sp S.R)).left) ≫ (baseOver (Sp S.R)).hom =
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _)))
  obtain ⟨rig, e, h₁, h₂, h₃⟩ := GlobalTheory.FrameMove.exists_move (T := baseOver (Sp S.R))
    (T' := TFK (R := V) (AlgebraicClosure (FractionRing V))) cart lb hh ρ.rig_gen hx ρ.fr_tors
  refine ⟨rig, e, h₁, h₂, fun k σ => ?_⟩
  obtain ⟨t, ht⟩ := h₃ k σ
  exact ⟨t, fun a c hc z J hJ => (ht a _ hc z J hJ).trans (congrArg (· * _) (GlobalTheory.FrameMove.gs_spMap _ z c))⟩

end GlobalTheory.ThetaDvr
end

namespace GlobalTheory.ThetaDvr

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_mul_of_val_le {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {x y : FractionRing V} (hy : y ≠ 0)
    (h : v (algebraMap (FractionRing V) F y) ≤ v (algebraMap (FractionRing V) F x)) :
    ∃ w : V, x = algebraMap V (FractionRing V) w * y ∧
      (v (algebraMap (FractionRing V) F y) < v (algebraMap (FractionRing V) F x) → w ∈ IsLocalRing.maximalIdeal V) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero, zero_mul], fun _ => zero_mem _⟩
  obtain ⟨n, u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ x hx
  obtain ⟨m, u', hu'⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ y hy
  have hn := hv x n ⟨u, hu⟩
  have hm := hv y m ⟨u', hu'⟩
  rw [hn, hm, WithTop.coe_le_coe, Int.cast_le] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hu'1 : algebraMap V (FractionRing V) (↑u'⁻¹ : V) * algebraMap V (FractionRing V) (u' : V) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨ϖ ^ k * u * ↑u'⁻¹, ?_, fun hlt => ?_⟩
  · rw [hu, hu', hk, zpow_add₀ hϖ0, zpow_natCast, map_mul, map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) ϖ ^ k *
      algebraMap V (FractionRing V) (u : V))) * hu'1
  · rw [hn, hm, WithTop.coe_lt_coe, Int.cast_lt] at hlt
    have hk0 : k ≠ 0 := by omega
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ?_ k (Nat.pos_of_ne_zero hk0)))
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.ThetaDvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGeneric

theorem exists_th_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] [CharZero K] (yK : S.R →+* K), ∃ a : S.Gam, yK ⟨S.th a, S.th_mem a⟩ ≠ 0 := by
  intro hL hL₂ o Ω _ _ _ S ρ K _ _ yK
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem hL hL₂ ρ ⟨RingHom.ker yK, RingHom.ker_isPrime yK⟩ 0
  exact ⟨0 + c, fun e => h (RingHom.mem_ker.2 e)⟩

end GlobalTheory.ThetaGeneric
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_affine_le_of_cover {X : Scheme.{0}} {N : Type} (𝒰 : N → X.Opens) (h𝒰 : ⨆ i, 𝒰 i = ⊤) (e : Sp ℂ ⟶ X) :
    ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ⊤ ≤ e ⁻¹ᵁ U := by
  have pt : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have h1 : e pt ∈ ⨆ i, 𝒰 i := by rw [h𝒰]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h1
  obtain ⟨U, hU, hx, hle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hi
  refine ⟨i, U, hU, hle, fun y _ ↦ ?_⟩
  obtain rfl : y = pt := Subsingleton.elim _ _
  exact hx

theorem exists_charts_subordinate : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k) := by
  intro I _ g Λ _ F B _ X s σ u hX N 𝒰 h𝒰
  let Q : Opens (Tot I g) → Prop := fun W ↦ ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U
  obtain ⟨r, hr, hx⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u hX (Charts.std F Q) fun k ↦ by
    obtain ⟨i, U, h1, -, h3⟩ := k.2.2
    exact ⟨U, h1, h3⟩
  refine ⟨Charts.std F Q, r, fun k ↦ k.2.2.choose, ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩, fun l k' ↦ ?_, hr,
    fun k ↦ ?_⟩
  · obtain ⟨i, U, hU, hle, hp'⟩ := exists_affine_le_of_cover 𝒰 h𝒰 (u.E p)
    exact ⟨⟨⟨_, (u.hol U 0).1⟩, fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ hq.2⟩, hp, hp'⟩
  · have hc : ContinuousOn (F.shift l) (k₁.1 : Set (Tot I g)) := (F.shift_analytic l k₁.2.1).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k₁.2.2
    refine ⟨⟨⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' k₂.1, hc.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩,
      fun q hq ↦ k₁.2.1 q hq.1, i, U, hU, hle, fun q hq ↦ hW q hq.1⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]; exact hq.1
  · have hc : ContinuousOn (F.shift (-l)) (F.tot : Set (Tot I g)) := (F.shift_analytic (-l) fun _ h ↦ h).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k'.2.2
    refine ⟨⟨⟨(F.tot : Set (Tot I g)) ∩ F.shift (-l) ⁻¹' k'.1, hc.isOpen_inter_preimage F.tot.isOpen k'.1.isOpen⟩,
      fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ ?_⟩, fun q hq ↦ ⟨k'.2.1 q hq, ?_⟩, fun q hq ↦ hq.2⟩
    · rw [← u.per (-l) q hq.1]
      exact hW _ hq.2
    · change F.shift (-l) (F.shift l q) ∈ k'.1
      rwa [← F.shift_add, neg_add_cancel, F.shift_zero]
  · obtain ⟨U, hU, hle, hW⟩ := k.2.2.choose_spec
    exact fun y hy ↦ hle (hx k U hU hW hy)

end GlobalTheory.AnPer
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isPeriod_pull1_eq_comap : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂), X₁.IsSeparated → X₂.IsSeparated → ∀ (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ p : Tot I₁ g₁, p.1 ∈ F₁.V → u₁.E p ≫ φ = u₂.E (b p.1, M p.2)) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), IsPeriod u₂ c per₂ → IsPeriod u₁ (m.pull1 c) per₁ → ∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l)) := by
  intro I₁ _ g₁ Λ₁ _ F₁ B₁ _ X₁ s₁ σ₁ I₂ _ g₂ Λ₂ _ F₂ B₂ _ X₂ s₂ σ₂ u₁ u₂ h₁ h₂ b hb hbV M A hτ β φ m hσ hE
    c per₂ per₁ hp₂ hp₁ l
  obtain ⟨K₁, K₂, κ, hR, hs₁, hs₂, hW, hle⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₁ u₂ b hb hbV M A hτ
  obtain ⟨r₁, hr₁, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₁ h₁ K₁ hs₁
  obtain ⟨r₂, hr₂, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₂ h₂ K₂ hs₂
  have hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k) := fun k p hp ↦
    ((hb _ (K₁.base k p hp)).comp analyticAt_fst).prod
      (((LinearMap.toContinuousLinearMap M).analyticAt p.2).comp analyticAt_snd)
  have hx : ∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ := by
    intro k
    refine GlobalTheory.T.holomorphicPoint_ext_of_isSeparated (K₁.W k) h₂ _ _ fun p hp ↦ ?_
    have e : (Hol.ev p hp).toRingHom.comp (Hol.comap _ (hΦ k) (hW k)).toRingHom =
        (Hol.ev ((b p.1, M p.2) : Tot I₂ g₂) (hW k p hp)).toRingHom := by
      refine RingHom.ext fun f ↦ ?_
      change Hol.ev p hp (Hol.comap _ (hΦ k) (hW k) f) = Hol.ev _ (hW k p hp) f
      rw [Hol.ev_apply, Hol.ev_apply, Hol.fn_comap _ _ _ f hp]
    rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, e, hr₂ (κ k) _ (hW k p hp), hr₁ k p hp,
      hE p (K₁.base k p hp)]
  let per : Λ₁ →+ Hol F₁.V :=
    ((Hol.comap b hb hbV).toRingHom.toAddMonoidHom.comp per₂).comp A
  have key := GlobalTheory.T.period_pullback_eq_of_chartMap_class b hb hbV M A hτ K₁ K₂ κ hΦ hW hle r₁ r₂ β φ m hσ hx c per₂ per (fun _ ↦ rfl)
    (hp₂ K₂ r₂ hr₂)
  have := GlobalTheory.T.periodClass_injective_of_rich_charts K₁ hR per₁ per ((hp₁ K₁ r₁ hr₁).symm.trans key)
  rw [this]
  rfl

end GlobalTheory.AnPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.log_cocycle_cohomologous_alt : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
  first | exact @GlobalTheory.AnPer.log_cocycle_cohomologous | exact GlobalTheory.AnPer.log_cocycle_cohomologous | (intros; apply GlobalTheory.AnPer.log_cocycle_cohomologous <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem deg_le_rank_mul_of_linesLE : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  intro r
  induction r with
  | zero =>
    intro k F _ _ _ _ _ _ g _ b _
    have : deg g = 0 := by simp [deg, ord, Matrix.det_isEmpty]
    simp [this]
  | succ r ih =>
    intro k F _ _ _ _ _ hF g hg b hb

    set S : Set ℝ := {c | LinesLE g c} with hS
    have hbS : b ∈ S := hb

    have hbdd : BddBelow S := by
      refine ⟨(degLine (pullAd (id : Place k F → Place k F) g) (Pi.single 0 1) : ℝ), ?_⟩
      intro c hc
      have hres : IsRes (k := k) (F := F) (E := F) (id : Place k F → Place k F) := by
        intro p x; rfl
      have h1 := hc F id hres (Pi.single 0 1) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Module.finrank_self] using h1
    set a := sInf S with ha
    have hab : a ≤ b := csInf_le hbdd hbS
    have haS : LinesLE g a := by
      intro E _ _ _ _ _ ρ hρ w hw
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      have : (degLine (pullAd ρ g) w : ℝ) / Module.finrank F E ≤ a := by
        refine le_csInf ⟨b, hbS⟩ ?_
        intro c hc
        rw [div_le_iff₀ hn]
        exact hc E ρ hρ w hw
      rwa [div_le_iff₀ hn] at this
    have key : ∀ ε : ℝ, 0 < ε → (deg g : ℝ) ≤ (r + 1) * a + r * ε := by
      intro ε hε
      have hnot : ¬ LinesLE g (a - ε) := fun h => by
        have := csInf_le hbdd (show a - ε ∈ S from h); linarith
      simp only [LinesLE, not_forall, not_le] at hnot
      obtain ⟨E, _, _, _, _, _, ρ, hρ, x, hx, hlt⟩ := hnot
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      obtain ⟨hGadm, hGdeg, -, hGlines⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
      have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
      have hLG : LinesLE (pullAd ρ g) (a * Module.finrank F E) := hGlines a haS
      have hδle : (degLine (pullAd ρ g) x : ℝ) ≤ a * Module.finrank F E := haS E ρ hρ x hx
      obtain ⟨h, u, -, -, hzero, hadm', hadmq, hdeg, hsum, hlines⟩ :=
        GlobalTheory.T.iwasawa_decomposition_admissible_family k E hE r (pullAd ρ g) hGadm x hx
      have hLq := GlobalTheory.T.quotient_line_degree_le_of_triangular_family k E hE r (fun v => u v * pullAd ρ g v * h) hadm' hzero hadmq
        (a * Module.finrank F E) (hlines _ hLG)
      rw [hsum] at hLq
      have hq := ih k E hE _ hadmq _ hLq
      have hdegZ : (Module.finrank F E : ℤ) * deg g =
          degLine (pullAd ρ g) x + deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) := by
        rw [← hGdeg, hdeg]
      have hdegR : (Module.finrank F E : ℝ) * (deg g : ℝ) =
          (degLine (pullAd ρ g) x : ℝ) + (deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) : ℝ) := by
        exact_mod_cast hdegZ
      set n : ℝ := (Module.finrank F E : ℝ)
      set δ : ℝ := (degLine (pullAd ρ g) x : ℝ)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h2 : (r : ℝ) * (a * n - δ) ≤ r * (ε * n) := by
        apply mul_le_mul_of_nonneg_left _ hr; nlinarith
      have h3 : n * (deg g : ℝ) ≤ n * ((r + 1) * a + r * ε) := by nlinarith
      exact le_of_mul_le_mul_left h3 hn
    have hfin : (deg g : ℝ) ≤ (r + 1) * a := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := key (ε / (r + 1)) (by positivity)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (r : ℝ) * (ε / (r + 1)) ≤ ε := by
        rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

private theorem resG_resG_sameDiv {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem SameDiv.trans_of_isLB : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec),
    M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  intro X L M N σ τ υ _ h₁ h₂ x
  obtain ⟨U₁, i, j, hi, hj, u₁, hx₁, e₁⟩ := h₁ x
  obtain ⟨U₂, j', k, hj', hk, u₂, hx₂, e₂⟩ := h₂ x
  have hV : U₁ ⊓ U₂ ≤ M.U j ⊓ M.U j' := le_inf (inf_le_left.trans hj) (inf_le_right.trans hj')
  have c := congrArg (resG X hV) (τ.compat j j')
  have e₁' := congrArg (resG X (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) e₁
  have e₂' := congrArg (resG X (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) e₂
  change resG X hV (resG X inf_le_left (τ.f j)) =
    resG X hV ((M.g j j' : Γ(X, M.U j ⊓ M.U j')) * resG X inf_le_right (τ.f j')) at c
  simp only [map_mul, resG_resG_sameDiv] at c e₁' e₂'
  refine ⟨U₁ ⊓ U₂, i, k, inf_le_left.trans hi, inf_le_right.trans hk,
    res inf_le_left u₁ * res hV (M.g j j') * res inf_le_right u₂, ⟨hx₁, hx₂⟩, ?_⟩
  simp only [Units.val_mul, res, Units.coe_map, MonoidHom.coe_coe]
  rw [e₁', c, e₂']
  simp only [resG, mul_assoc]

end GlobalTheory.LogPair
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.same_divisor_trans : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec), M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  first | exact @_root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB | exact _root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB | (intros; apply _root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB <;> assumption)

end
end
