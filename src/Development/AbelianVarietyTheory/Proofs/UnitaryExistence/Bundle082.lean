module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle005
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetNeZeroOfOrth
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.Topology.Algebra.Group.Matrix

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_one_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h1 : L.FG) (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    GlobalTheory.AdLat.latOf F (1 : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (L : Set (Fin n → E)) = L := by
  ext v
  have h := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L h1 h2).1 v
  simp only [GlobalTheory.AdLat.latOf, Set.mem_ofPred_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe]
  exact h

theorem latG_eq_span_latOf (D : D7) (V : HSp D) (g : GA D V) :
    latG V g = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA,
      ∃ v ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latC V : Set (Fin V.rank → D.host.E)), w = a • v} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latG gLat
  rw [hh]
  rfl

theorem latGHat_eq_closure (D : D7) (V : HSp D) (g : GA D V) :
    latGHat V g = AddSubgroup.closure {w | ∃ a ∈ D.host.AA,
      ∃ z ∈ (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E))),
        w = fun i => ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) * z i} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latGHat gLat
  rw [hh]

theorem latG_lattice_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  intro D V g
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have h6 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
    rw [latG_eq_span_latOf, map_one, Units.val_one, latOf_one_eq _ _ _ _ hfg hsp]
    rfl
  obtain ⟨s1, s2, s3, s4⟩ := GlobalTheory.AdLat.scale_latOf D.host.F D.host.E V.rank (latC V) (finHom V g) D.host.AA
    (latG V 1) hfg hsp hA h6
  have h3 : (latG V g : Set (Fin V.rank → D.host.E)) =
      GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    rw [latG_eq_span_latOf D V g]; exact s1
  have h4 : (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) =
      (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
    rw [latGHat_eq_closure D V g]; exact s2
  obtain ⟨Λ, l1, l2, l3, l4⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) s3 s4
  have hΛ : Λ = latG V g := SetLike.coe_injective (l1.trans h3.symm)
  subst hΛ
  exact ⟨l2, l3, h3, h4, SetLike.coe_injective (h4.trans l4.symm), h6⟩

end GlobalTheory.Member
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧ (∀ h : GA D V, h ∈ GinfC V → h ∈ GfC V → h = 1) ∧ (∀ g : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ (g.1 *ᵥ x) (g.1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) → ∃ k ∈ GfC V, finHom V k = g) ∧ ∀ g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E), g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram → ∃ a ∈ GinfC V, infHom V a = g := by
  first | exact @GlobalTheory.UnitarySplit.real_finite_split | exact GlobalTheory.UnitarySplit.real_finite_split | (intros; apply GlobalTheory.UnitarySplit.real_finite_split <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.finitePart_preserves_form_det_norm_one : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  first | exact @GlobalTheory.Member.finHom_herm_det | exact GlobalTheory.Member.finHom_herm_det | (intros; apply GlobalTheory.Member.finHom_herm_det <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.congruence_lattice_fractionalMultiple_agree : ∀ (D : D7) (V : HSp D), ∀ k : GA D V, ((∀ z ∈ latGHat V 1, (finHom V k).1 *ᵥ z ∈ latGHat V 1) ↔ FinCong V 1 k) ∧ ∀ (M : ℕ) (I : Ideal (𝓞 D.host.E)), (∀ b ∈ I, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1 *ᵥ halfVec V b z - halfVec V b z = M • y) ↔ ∀ a ∈ I • latG V 1, ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  first | exact @GlobalTheory.Member.AALev.congruences_agree | exact GlobalTheory.Member.AALev.congruences_agree | (intros; apply GlobalTheory.Member.AALev.congruences_agree <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.rational_points_adelicUnitary_eq_unitary : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  first | exact @GlobalTheory.Member.RatElt.rational_elements | exact GlobalTheory.Member.RatElt.rational_elements | (intros; apply GlobalTheory.Member.RatElt.rational_elements <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.transvection_mem_principalCongruenceGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  first | exact @GlobalTheory.PrincTransv.transv_mem_princ | exact GlobalTheory.PrincTransv.transv_mem_princ | (intros; apply GlobalTheory.PrincTransv.transv_mem_princ <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_chart_holomorphic_coordinates_near_frame : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b₀ ∈ T.co ⁻¹' (M.X k).dom, ∃ (p : TRing c.F) (y₀ : FrPt Xo c p.R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (p.R →ₐ[c.F] CAt σ)), IsOpen B ∧ b₀ ∈ B ∧ B ⊆ T.co ⁻¹' (M.X k).dom ∧ (∀ b ∈ B, F.u k (T.Pf (T.co b)) = spMap (ψ b).toRingHom ≫ y₀.x) ∧ ∀ t : p.R, DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (ψ b t)) B := by
  first | exact @GlobalTheory.HolChart.exists_chart_holomorphic | exact GlobalTheory.HolChart.exists_chart_holomorphic | (intros; apply GlobalTheory.HolChart.exists_chart_holomorphic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoint_reduced_from_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c := by
  first | exact @GlobalTheory.Frames.allTest_of_secBaseChange | exact GlobalTheory.Frames.allTest_of_secBaseChange | (intros; apply GlobalTheory.Frames.allTest_of_secBaseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoint_field_from_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), SpreadSt Xo c := by
  first | exact @GlobalTheory.Frames.framedPoint_field_fromTest | exact GlobalTheory.Frames.framedPoint_field_fromTest | (intros; apply GlobalTheory.Frames.framedPoint_field_fromTest <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

theorem _root_.GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  first | exact @GlobalTheory.UnitaryGlue.adelic_glue | exact GlobalTheory.UnitaryGlue.adelic_glue | (intros; apply GlobalTheory.UnitaryGlue.adelic_glue <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def archHom (V : HSp D) (τ : D.host.E →+* ℂ) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  if h : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ then
    h.choose.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (infHom V))
  else 1

theorem archHom_eq (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) : archHom V τ g = Pj.archM V θ g := by
  have h' : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := ⟨θ, h⟩
  rw [archHom, dite_eq_left h', GlobalTheory.LettersCheck.isInfEmb_unique τ _ θ h'.choose_spec h]
  rfl

theorem isHermitian_gram (V : HSp D) (τ : D.host.E →+* ℂ) : (V.gram.map τ).IsHermitian := by
  ext a b
  have h := V.herm.eq (V.frame b) (V.frame a)
  show star (τ (V.hT (V.frame b) (V.frame a))) = τ (V.hT (V.frame a) (V.frame b))
  rw [← h]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem lintegral_adelic (V : HSp D) {Comp : Type} [Fintype Comp] {r : ℕ} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hU : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (hΨ : ∀ k k', (X k).Ψ = (X k').Ψ ∧ (X k).p0 = (X k').p0) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : ∀ k, Frame (X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (X k).Ψ r, ∀ x ∈ (X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun g => F (dict g).1 (dict g).2) ∧
        ∫⁻ g in 𝓕, F (dict g).1 (dict g).2 ∂μ = κ * ∑ k, IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt (X k) (F k) := by
  subst hr
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : μ.IsMulRightInvariant := ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) μ h𝓕 h0 h1⟩
  have hmem : ∀ h, h ∈ (Kf.map (finHom V)).comap (finHom V) ↔ ∃ a ∈ GinfC V, ∃ z ∈ Kf, h = a * z := by
    intro h
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨h * z⁻¹, ?_, z, hz, (inv_mul_cancel_right _ _).symm⟩
      show finHom V (h * z⁻¹) = 1
      rw [map_mul, map_inv, e, mul_inv_cancel]
    · rintro ⟨a, ha, z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [map_mul, show finHom V a = 1 from ha, one_mul]
  have hopen : IsOpen (((Kf.map (finHom V)).comap (finHom V) : Subgroup (GA D V)) : Set (GA D V)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK 1) ?_)
    rintro _ ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [one_mul, map_mul, show finHom V a = 1 from ha, mul_one]
  have hg := fun k => (GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have ha : ∀ k (τ : (X k).Ψ) g, archHom V τ.1 g = Pj.archM V (th k τ) g := fun k τ g => archHom_eq V (hth k τ) g
  have htr : ∀ (u J : Matrix (Fin V.rank) (Fin V.rank) ℂ), uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ ↔
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u J
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨dL, dR, ⟨x0, d0, dI⟩, dD, -, dF⟩ := hd
  refine lintegral_dict X μ (GQ V) (GinfC V) Kf _ h𝓕 h0 h1 hopen.measurableSet hmem dict (archHom V)
    (fun τ => (V.gram.map τ)ᵀ) x0 hΨ (fun τ => ⟨(isHermitian_gram V τ).transpose, ?_⟩) (fun k τ => ?_)
    (fun k τ g => ?_) (fun k u hu => ?_) (fun k τ z hz => ?_) (fun k γ hγ h => ?_) dL dR d0 (fun g h hh => ?_) dD dF hU
  · rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)
  · exact ((hg k).2.2.1 τ).congr fun g => (ha k τ g).symm
  · rw [htr, ha]
    exact GlobalTheory.RecDictModel.archM_unitary V (hth k τ) g
  · obtain ⟨h, hh, e⟩ := (hg k).2.2.2 u fun τ => (htr _ _).1 (hu τ)
    exact ⟨h, hh, fun τ => (ha k τ h).trans (e τ)⟩
  · rw [ha, Pj.archM, show infHom V z = 1 from ((hK z).1 hz).1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ (X k).Ψ
      · exact ⟨⟨τ, hτ⟩⟩
      · exact ⟨⟨_, not_not.1 (mt ((X k).cmType τ).2 hτ)⟩⟩
    obtain ⟨γ₀, -, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have e1 : (matHom V γ).1 = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (AF D.host.F)) := (congrArg Units.val e0).symm
    have e2 : Pj.archM V (th k τ) γ = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
      have : ((γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Ainf D.host.F))).map (th k τ) =
          (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
        ext i j
        exact (hth k τ).1 _
      rw [← this, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← e1]
      rfl
    have e3 : (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 := by
      refine Matrix.map_injective τ.1.injective ?_
      show (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1
      rw [← e2, ← ha, h τ, Matrix.map_one _ (map_zero _) (map_one _)]
    refine Subtype.ext (Units.ext (e1.trans ?_))
    rw [e3]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · simp only [ha]
    exact dI g h hh

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Pj.Unf Xo c σ r)

theorem measurable_onQ_adel (V : HSp D) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hm : Pj.MuUnit V dict mu) (hc : Continuous mu) (P : Pj.FDSec X) (hP : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) :
    Measurable (Pj.onQ V (Pj.adel V dict mu P)) := by
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((hK k).1 hk).1)
    (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK) fun k τ => ⟨τ.1, hth k τ⟩
  have hC : Continuous fun g => mu g * P (dict g).1 (dict g).2 := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨M, hM, k, x, hx, hs⟩ := hloc g₀
    have h1 : ContinuousOn (fun g => mu g * P k (x g)) M :=
      hc.continuousOn.mul ((hP k).comp hx fun g hg => (hs g hg).1)
    refine (h1.continuousAt hM).congr ?_
    filter_upwards [hM] with g hg
    obtain ⟨hxd, γ, hγ, he⟩ := hs g hg
    rw [he]
    exact congrArg (mu g * ·) (hΓ k γ hγ _ hxd).symm
  have hL : ∀ g g', g * g'⁻¹ ∈ GQ V → mu g' * P (dict g').1 (dict g').2 = mu g * P (dict g).1 (dict g).2 := by
    intro g g' h4
    obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 g'
    have e' := hm.1 (g * g'⁻¹) g'
    rw [inv_mul_cancel_right] at e e'
    rw [hm.2.2.1 _ h4, one_mul] at e'
    rw [e, e']
    exact congrArg (mu g' * ·) (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  rw [measurable_from_quotient]
  have : (Pj.onQ V (Pj.adel V dict mu P) ∘ Quotient.mk'') = fun g => mu g * P (dict g).1 (dict g).2 :=
    funext fun g => hL g (Pj.autMk V g).out (QuotientGroup.rightRel_apply.1 (Quotient.mk_out g))
  rw [this]
  exact hC.measurable

end GlobalTheory.PeterssonCompare
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_det_matHom (D : D7) (V : HSp D) :
    Continuous fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have hm : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  exact Matrix.GeneralLinearGroup.continuous_det.comp hm

theorem exists_muVal : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  intro D V χ hχ hF
  obtain ⟨hex, huniq, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → χ (r g) = χ x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', χ (r (g * g')) = χ (r g) * χ (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => χ (r g)) hm
  have hcont : Continuous m := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    refine continuous_of_continuousAt_one m ?_
    intro U hU
    rw [map_one] at hU
    have hW : χ ⁻¹' U ∈ 𝓝 (1 : (AE D)ˣ) := hχ.1.continuousAt.preimage_mem_nhds (by rwa [map_one])
    obtain ⟨N, hN, hNW⟩ := GlobalTheory.Member.exists_root_near_one D _ hW
    have hN' : (fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g)) ⁻¹' N ∈ 𝓝 (1 : GA D V) :=
      (continuous_det_matHom D V).continuousAt.preimage_mem_nhds (by rwa [map_one, map_one])
    refine Filter.mem_map.2 (Filter.mem_of_superset hN' ?_)
    intro g hg
    obtain ⟨x, hxW, hx⟩ := hNW _ hg (GlobalTheory.Member.finHom_herm_det D V g).2.2
    have : m g = χ x := hval g x hx
    show m g ∈ U
    rw [this]
    exact hxW
  refine ⟨fun g => (m g : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun g => ⟨r g, hr g⟩, fun g x hx => congrArg (fun z : Circle => (z : ℂ)) (hval g x hx)⟩
  · intro g g'
    simp only [map_mul, Circle.coe_mul]
  · intro g
    exact Circle.norm_coe _
  · intro γ hγ
    obtain ⟨x, hx⟩ := hrat γ hγ
    have : m γ = 1 := (hval γ _ hx).trans (hχ.2 x)
    simp only [this, Circle.coe_one]
  · exact continuous_subtype_val.comp hcont

end GlobalTheory.Member
end
