module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle195
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.thetaSystem_exists_rootOfUnity_sum_norm_attained : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  first | exact @GlobalTheory.thetaSys_exists_norm_FF_eq | exact GlobalTheory.thetaSys_exists_norm_FF_eq | (intros; apply GlobalTheory.thetaSys_exists_norm_FF_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.thetaSystem_sum_character_orthogonal_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  first | exact @GlobalTheory.thetaSys_sum_perp_char_eq_zero | exact GlobalTheory.thetaSys_sum_perp_char_eq_zero | (intros; apply GlobalTheory.thetaSys_sum_perp_char_eq_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.thetaSystem_weightProjector_fixes_eigenvector : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (y : o →+* F) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N), S.IsoFree T → ∀ (b E : S.J → F), (∀ t : T, ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j = y S.ζN ^ (c t).val * ∑ j, b j * E j) → ∑ i, b i * ∑ j, y (S.proj T c j i) * E j = ∑ j, b j * E j := by
  first | exact @GlobalTheory.TestFibre.proj_fixes_eigen | exact GlobalTheory.TestFibre.proj_fixes_eigen | (intros; apply GlobalTheory.TestFibre.proj_fixes_eigen <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem exists_expandsF_and_nuGe_of_isComb : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → (∀ t : SecA A F k, ∃ σ, U.ExpandsF F k w₀ t σ) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k) (t : SecA A F k) (q r : ℚ), IsComb s c t → (∀ i, (q : WithTop ℚ) ≤ v (c i)) → (∀ i σ, U.ExpandsF F k w₀ (s i) σ → NuGe D Q F v k σ r) → ∀ σ, U.ExpandsF F k w₀ t σ → NuGe D Q F v k σ (r + q) := by
  intro hL V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ hw k hk
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨h₁, -⟩ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F k hk w₀ hw
  refine ⟨fun t => (h₁ t).exists, ?_⟩
  intro I _ c s t q r ht hq hs σ hσ
  choose Φ hΦ using fun i => (h₁ (s i)).exists
  have e := (GlobalTheory.TestFibre.isComb_iff_expandsF_sum hL V _ hA D A G hG U F k hk w₀ hw I s Φ c t hΦ).1 ht
  obtain rfl : σ = ∑ i, c i • Φ i := (h₁ t).unique hσ e
  refine Finset.sum_induction _ (fun x => NuGe D Q F v k x (r + q)) (fun a b ha hb => ?_) ?_ fun i _ => ?_
  · exact NuGe.add Q (s := a) (s' := b) (fun _ _ => rfl) ha hb
  · intro χ
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun j => by rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl⟩
  · exact NuGe.smul Q (hq i) ((isSmul_iff (c i) (Φ i) _).2 rfl) (hs i _ (hΦ i))

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem labels_exist : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → Nonempty u.Lab := by
  intro h₁ h₂ h₃ o Ω _ _ _ _ S ρ p _ y₀ u hy
  obtain ⟨q, hq, hq'⟩ := GlobalTheory.ZH.PsiForm.main o Ω S ρ p y₀ u
  obtain ⟨yy, hs, he⟩ := GlobalTheory.T.exists_labelMap_torsion_characters h₁ h₂ h₃ o Ω S ρ p y₀ u
  have hk := GlobalTheory.T.label_map_kernel_eq_integral_torsion h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he hy
  obtain ⟨hi, wt, hw⟩ := GlobalTheory.T.isoFree_perp_labelKernel_weights h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he
  exact ⟨⟨q, hq, hq', yy, hs, he, hk, hi, wt, hw⟩⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.torsion_points_polarised_abelianVariety_galois : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ), l.Prime → (∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))) ∧ (∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ ∀ (τ : Ω ≃ₐ[K] Ω) n (x y x' y' : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l ^ n = 1 → y ^ l ^ n = 1 → x'.left = spMap τ.toRingEquiv.toRingHom ≫ x.left → y'.left = spMap τ.toRingEquiv.toRingHom ≫ y.left → (e n x y : Ω) ^ l ^ n = 1 ∧ (e n x' y' : Ω) = τ (e n x y)) ∧ ((∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ n, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧ ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 → ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left) := by
  first | exact @GlobalTheory.torsion_points_galois_module | exact GlobalTheory.torsion_points_galois_module | (intros; apply GlobalTheory.torsion_points_galois_module <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.modelSystems_jointProperties_of_laws : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  first | exact @GlobalTheory.LN.partI_of_inputs | exact GlobalTheory.LN.partI_of_inputs | (intros; apply GlobalTheory.LN.partI_of_inputs <;> assumption)
end
