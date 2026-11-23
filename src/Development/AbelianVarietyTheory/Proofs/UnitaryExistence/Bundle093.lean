module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  first | exact @GlobalTheory.Member.exists_iotaOK | exact GlobalTheory.Member.exists_iotaOK | (intros; apply GlobalTheory.Member.exists_iotaOK <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance : ∀ (D : D7) (V : HSp D), (∀ γ γ' h, IsRat V γ γ' → (∀ v, v ∈ latG V h ↔ (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V (γ * h)) ∧ ∀ w, w ∈ latGHat V h ↔ (finHom V γ).1 *ᵥ w ∈ latGHat V (γ * h)) ∧ (∀ h h', finHom V h = finHom V h' → latG V h = latG V h' ∧ latGHat V h = latGHat V h') ∧ (∀ (N : ℕ) h k, FinCong V N k → latG V (h * k) = latG V h ∧ latGHat V (h * k) = latGHat V h) ∧ ∀ h h', latG V h = latG V h' → FinCong V 1 (h⁻¹ * h') := by
  first | exact @GlobalTheory.Member.latG_move | exact GlobalTheory.Member.latG_move | (intros; apply GlobalTheory.Member.latG_move <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem markMove_finVec_mem {D : D7} (V : HSp D) (g : GA D V) {v : Fin V.rank → D.host.E} (hv : v ∈ latG V g) :
    finVec V v ∈ latGHat V g := by
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.2.1]
  exact AddSubgroup.subset_closure ⟨1, fun w => one_mem _, v, hv, rfl⟩

theorem markMove_mulVec_mem {D : D7} (V : HSp D) (g : GA D V)
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ latGHat V 1) :
    (finHom V g).1 *ᵥ y ∈ latGHat V g := by
  have h := (GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.1
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1] at hy
  rw [← SetLike.mem_coe, h]
  exact ⟨y, hy, rfl⟩

theorem markMove_finVec_add_nsmul {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) (n : ℕ) :
    finVec V (x + n • y) = finVec V x + n • finVec V y := by
  funext i
  simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
  congr 1
  exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) n (y i)

theorem markMove_mulVec_nsmul {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (n : ℕ)
    (y : Fin m → R) : A *ᵥ (n • y) = n • (A *ᵥ y) := Matrix.mulVec_smul _ _ _

theorem markMove_finHom_mul {D : D7} (V : HSp D) (g h : GA D V)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ y = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ y) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]



theorem mark_move : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k γ, C.Mark h k γ → (∀ γ₀ ∈ GQ V, C.Mark (γ₀ * h) k (γ * γ₀⁻¹)) ∧ (∀ u, FinCong V l.M u → C.Mark (h * u) k γ) ∧ (∀ u ∈ GinfC V, C.Mark (h * u) k γ) ∧ ∀ δ ∈ (C.M.X k).Γ, ∃ γ₁ ∈ GQ V, C.Mark h k (γ₁ * γ) ∧ C.fr (γ₁ * γ * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h k γ hM
  obtain ⟨hγ, hΛ, hmk⟩ := hM
  refine ⟨fun γ₀ hγ₀ => ?_, fun u hu => ?_, fun u hu => ?_, fun δ hδ => ?_⟩
  · have e : γ * γ₀⁻¹ * (γ₀ * h) = γ * h := by group
    refine ⟨mul_mem hγ (inv_mem hγ₀), ?_, ?_⟩
    · rw [e]; exact hΛ
    · rw [e]; exact hmk
  · have e : γ * (h * u) = γ * h * u := (mul_assoc _ _ _).symm
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.2.1 l.M (γ * h) u hu
    refine ⟨hγ, ?_, ?_⟩
    · rw [e, e1]; exact hΛ
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hιa : C.ι a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • latG V 1 := by
        rw [← hC.iota.emb.2, ← Submodule.map_top, ← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem ha
      obtain ⟨y, hy, hy'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 l.M _).1 (((GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).1 u).1 hu) _ hιa
      rw [e, e2]
      refine ⟨w - (finHom V (γ * h)).1 *ᵥ y, sub_mem hw (markMove_mulVec_mem V _ hy), ?_⟩
      rw [markMove_finHom_mul, sub_eq_iff_eq_add'.1 hy', Matrix.mulVec_add, markMove_mulVec_nsmul, nsmul_sub, ← hw',
        sub_add_eq_sub_sub]
  · have e : finHom V (γ * (h * u)) = finHom V (γ * h) := by
      have hu' : finHom V u = 1 := hu
      rw [← mul_assoc, map_mul _ _ u, hu', mul_one]
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.1 _ _ e
    refine ⟨hγ, ?_, ?_⟩
    · rw [e1]; exact hΛ
    · rw [e2, e]; exact hmk
  · have hr := C.hr
    subst hr
    obtain ⟨⟨hU, hS⟩, hcong, -⟩ := (hC.base.gam k δ).1 hδ
    have hG : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
    rw [hG] at hU
    obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.Member.RatElt.rational_elements D V
    obtain ⟨γ₁, hγ₁⟩ := r3 δ hU
    have hq : γ₁ ∈ GQ V := (r1 γ₁).2 ⟨δ, hγ₁⟩
    obtain ⟨m1, m2⟩ := (GlobalTheory.Member.latG_move D V).1 γ₁ δ (γ * h) hγ₁
    obtain ⟨f1, f2⟩ := r5 γ₁ δ hγ₁
    have hΛ' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
      rw [← SetLike.mem_coe, hΛ]
      exact ⟨fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx, fun hv => ⟨v, hv, rfl⟩⟩
    have hΛ'' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ₁ * (γ * h)) := fun v => by
      have e : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
          (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have h0 := ((hS _).symm.trans (hΛ' (((δ⁻¹ : GL (Fin V.rank) D.host.E) :
        Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v))).trans (m1 _)
      rwa [e] at h0
    refine ⟨γ₁, hq, ⟨mul_mem hq hγ, ?_, ?_⟩, ?_⟩
    · rw [mul_assoc]
      ext v
      rw [SetLike.mem_coe, hΛ'']
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx⟩
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hta : C.F.t k a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) •
          (⊤ : Submodule (𝓞 D.host.E) (C.F.Di k).La) := by
        have h1 := Submodule.mem_map_of_mem (f := C.F.t k) ha
        rw [Submodule.map_smul''] at h1
        exact Submodule.smul_mono le_rfl le_top h1
      obtain ⟨b, hb⟩ := hcong _ hta
      rw [mul_assoc]
      refine ⟨(finHom V γ₁).1 *ᵥ w - finVec V (C.M.φ k b : Fin V.rank → D.host.E),
        sub_mem ((m2 w).1 hw) (markMove_finVec_mem V _ ((hΛ'' _).1 (C.M.φ k b).2)), ?_⟩
      have hw2 : finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
          (finHom V (γ * h)).1 *ᵥ (finVec V (C.ι a)) = (l.M : ℕ) • w := hw'
      have h3 := f1 (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E)
      rw [hb, markMove_finVec_add_nsmul] at h3
      show finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      rw [markMove_finHom_mul, nsmul_sub, ← markMove_mulVec_nsmul, ← hw2, Matrix.mulVec_sub, h3]
      abel
    · funext τ
      have a1 := ((GlobalTheory.Member.Arch.archM_spec D V C.θ hC.inf).1 τ.1).2.1 γ₁ (γ * h)
      have a2 := f2 τ.1 (C.θ τ.1) (hC.inf τ.1)
      show (archM V (C.θ τ.1) (γ₁ * γ * h) * C.x₀ τ.1 : Matrix _ _ ℂ) =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [mul_assoc γ₁, a1, a2, Matrix.mul_assoc]

end GlobalTheory.Member
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm : ∀ (D : D7) (V : HSp D), ∀ (g : GA D V) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), J = D.host.AA * D.host.AAbar → (∀ z : D.host.E, z ∈ J ↔ ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) ∧ (∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ J) ↔ v ∈ latG V g) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔ v ∈ latG V g := by
  first | exact @GlobalTheory.Member.latG_selfDual | exact GlobalTheory.Member.latG_selfDual | (intros; apply GlobalTheory.Member.latG_selfDual <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem reindex_finCongr_self {n : ℕ} {α : Type} (h : n = n) (A : Matrix (Fin n) (Fin n) α) :
    Matrix.reindex (finCongr h) (finCongr h) A = A := by
  ext a b
  rfl

theorem fr_orthonormal_unit : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat (C.fr h k) τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧ C.fr h k ∈ (C.M.X k).dom ∧ (∀ τ i, ‖dmin (C.M.X k).Gm (C.fr h k) τ i‖ = 1) ∧ Continuous (fun u => C.fr u k) ∧ (∀ u ∈ GfC V, C.fr (h * u) k = C.fr h k) ∧ (∀ u, C.fr (h * u) k = rmul (C.fr h k) (archMat V C.th C.hr (fun k => C.fr 1 k) u k)) ∧ ∀ x : Frame (C.M.X k).Ψ r, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) → ∃ u ∈ GinfC V, C.fr u k = x := by
  intro D H Dw l Xo c σ V r C hC h k
  have hr := C.hr
  subst hr
  obtain ⟨hA, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf
  have hG : (C.M.X k).Gm = -V.gramᵀ := by
    rw [(hC.modelW k).1, reindex_finCongr_self]
  have hfr : ∀ u (τ : (C.M.X k).Ψ), mat (C.fr u k) τ = archM V (C.θ τ.1) u * C.x₀ τ.1 := fun u τ => rfl
  have hext : ∀ x y : Frame (C.M.X k).Ψ V.rank, (∀ τ, mat x τ = mat y τ) → x = y :=
    fun x y hxy => funext fun τ => hxy τ
  obtain ⟨-, h2, h3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  have horth : ∀ u (τ : (C.M.X k).Ψ), gram τ.1 (C.M.X k).Gm (mat (C.fr u k) τ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ) := by
    intro u τ
    rw [hfr, h3 τ.1 _ _ (by rw [hG]; exact (hA τ.1).2.2.2.2 u)]
    exact hC.orth k τ.1 τ.2
  refine ⟨horth h, (h2 _ (horth h)).1, (h2 _ (horth h)).2, ?_, fun u hu => ?_, fun u => ?_, fun x hx => ?_⟩
  · refine continuous_pi fun τ => ?_
    exact (hA τ.1).2.2.2.1.matrix_mul (continuous_const (y := C.x₀ τ.1))
  · refine hext _ _ fun τ => ?_
    rw [hfr, hfr, (hA τ.1).2.1, (hA τ.1).2.2.1 u hu, mul_one]
  · refine hext _ _ fun τ => ?_
    have hd : IsUnit (C.x₀ τ.1).det := by
      have := ((h2 _ (horth 1)).1 τ).1
      rw [hfr, (hA τ.1).1, one_mul] at this
      exact isUnit_iff_ne_zero.2 this
    show _ = mat (C.fr h k) τ * ((mat (C.fr 1 k) τ)⁻¹ * archM V (C.θ τ.1) u * mat (C.fr 1 k) τ)
    rw [hfr, hfr, hfr, (hA τ.1).2.1, (hA τ.1).1, one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ (C.M.X k).Ψ ↔
        τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
      intro τ
      rw [(hC.base.type k).2 τ, hC.iota.rt, hC.iota.rt0]
    have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (C.M.X k).Ψ,
        uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x ⟨τ, hτ⟩ = u * C.x₀ τ := by
      intro τ
      by_cases hτ : τ ∈ (C.M.X k).Ψ
      · obtain ⟨u, hu⟩ := h4 τ (C.x₀ τ) (mat x ⟨τ, hτ⟩) (hC.orth k τ hτ)
          ((hx ⟨τ, hτ⟩).trans (hC.orth k τ hτ).symm)
        rw [hG] at hu
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' hτ⟩
    choose u hu using hex
    obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem τ).2 hτ)).1
    refine ⟨a, ha, hext _ _ fun τ => ?_⟩
    rw [hfr, hau τ.1 ((hmem τ.1).1 τ.2)]
    exact ((hu τ.1 τ.2).2).symm

end GlobalTheory.Member
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ModelsExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {r : ℕ}

theorem rt0_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have h2 : (H.d : ℂ) = 0 := by simpa using h1
  exact H.d_prime.ne_zero (by exact_mod_cast h2)

theorem rt0_conj_neg_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h1 : (starRingEnd ℂ H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h2
    nlinarith [mul_self_nonneg H.rt0.re]
  · exact h

theorem emb_rt_eq_or (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have h : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [← map_pow, h, H.sqrt_neg_disc_sq]; simp

theorem cm_type (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hne : -H.rt0 ≠ H.rt0 := fun h => rt0_ne_zero H (by linear_combination (-1 / 2 : ℂ) * h)
  rcases emb_rt_eq_or H τ with h | h
  · rw [h, rt0_conj_neg_ne_zero]; simp [hne]
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]; simp [hne]

theorem exists_emb (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0
  · exact ⟨_, h⟩
  · exact ⟨τ, (cm_type H τ).2 h⟩

def dataOf (l : Level H) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (ξ₀ : E) (q : ℕ)
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (hherm : ∀ a b, cc (Gm a b) = Gm b a) (hdet : Gm.det ≠ 0) (hq : q ≤ r)
    (hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ))
    (hξ : cc ξ₀ = -ξ₀) (hξ0 : ξ₀ ≠ 0) (hκ : ∀ τ : Ψ, (τ.1 (2 * ξ₀)).im < 0)
    (Di : Datum H) (hL : LatModel l Ψ Gm ξ₀ q Di) : Data E r where
  Ψ := Ψ
  cmType := hΨ
  Gm := Gm
  Gm_herm := hherm
  Gm_det := hdet
  p0 := q
  p0_le := hq
  signature := hsig
  Λ := LinearMap.range hL.choose
  Λ_fg := by
    have := Di.fin
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  Λ_span := hL.choose_spec.2.2.1
  den := hL.choose_spec.2.2.2.1.choose
  den_ne := hL.choose_spec.2.2.2.1.choose_spec.1
  Λ_int := hL.choose_spec.2.2.2.1.choose_spec.2
  Γ := GlobalTheory.FrameUnif.princ l Gm Di hL.choose
  Γ_stab := fun _ hγ => hγ.1
  Γ_index := hL.choose_spec.2.2.2.2.1
  Γ_free := hL.choose_spec.2.2.2.2.2.1
  χ := fun _ _ => 1
  χ_mul := fun _ _ _ _ _ => (mul_one 1).symm
  χ_add := fun _ _ _ _ => (mul_one 1).symm
  χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩
  ξ0 := ξ₀
  ξ0_im := hξ
  ξ0_ne := hξ0
  κ0 := 2 * ξ₀
  κ0_xi := Or.inl rfl
  κ0_sign := hκ
  m := hL.choose_spec.2.2.2.2.2.2.choose
  m_pos := hL.choose_spec.2.2.2.2.2.2.choose_spec.1
  transv := fun ξ hξ h0 s hs hsi =>
    hL.choose_spec.2.2.2.2.2.2.choose_spec.2 _ (Or.inl rfl) ξ hξ h0 s hs hsi

theorem exists_modelsOf : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ M : _root_.GlobalTheory.FrameUnif.ModelsOf F r, ModelBase M ∧ NegXi M ∧ ∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀ := by
  classical
  intro hN E _ _ _ H Dw l Xo σ' g ty F r ξ₀ Gm φ hξ hneg hφ
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hmem : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  have hξ' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hξ ⊢
    rw [map_neg, hξ]
  have hrk : r = Dw.p + Dw.q := (GlobalTheory.HermModel.rank_integral_selfDual E H Dw r (-ξ₀) Gm φ hξ' hφ).1
  have hq : Dw.q ≤ r := by omega
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := fun τ => by
    rw [hmem, hmem]; exact cm_type H τ
  have hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ) := fun τ => by
    have hτ := (hmem τ.1).1 τ.2
    refine (GlobalTheory.T.signature_hermitian_model_of_datum E H Dw r (-ξ₀) Gm φ hξ' hφ τ.1 hτ).1 ?_
    have := hneg τ.1 hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ0 : ξ₀ ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := exists_emb H
    simpa using hneg τ hτ
  have hκ : ∀ τ : Ψ, (τ.1 (2 * ξ₀)).im < 0 := fun τ => by
    have := hneg τ.1 ((hmem τ.1).1 τ.2)
    rw [two_mul, map_add (f := _), Complex.add_im]
    linarith
  have hL : ∀ i, LatModel l Ψ Gm ξ₀ Dw.q (F.Di i) := fun i =>
    GlobalTheory.T.latticeModel_of_same_signature_hasseNorm hN E H l Dw (F.Di i) r Ψ ξ₀ Gm φ (F.sig i).1 (F.sig i).2 hmem hξ hφ
  refine ⟨⟨fun i => dataOf l Ψ Gm ξ₀ Dw.q hΨ hφ.2.2.1 hφ.2.2.2.1 hq hsig hξ hξ0 hκ (F.Di i) (hL i),
    fun i => LinearEquiv.ofInjective (hL i).choose (hL i).choose_spec.1⟩, ?_,
    fun k τ hτ => hneg τ ((hmem τ).1 hτ), fun k => ⟨rfl, rfl⟩⟩
  exact
    { rank := hrk
      type := fun k => ⟨rfl, hmem⟩
      chi := fun _ _ _ => rfl
      ef := fun k a b => (hL k).choose_spec.2.1 a b
      gam := fun k γ => Iff.rfl
      domStab := fun k x hx => ⟨fun b hb => dom_rmul _ hx hb, fun γ hγ => dom_lact _ hx hγ.1⟩ }

end GlobalTheory.ModelsExist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_perm_periodSpaces_complexAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  first | exact @GlobalTheory.ConjPermutes.exists_perm | exact GlobalTheory.ConjPermutes.exists_perm | (intros; apply GlobalTheory.ConjPermutes.exists_perm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore' : ∀ (D : D7) (T : Core D), LawsCore T → GlobalTheory.RunIn.GamAt T :=
  fun D T h j hj σ hσ => GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ

end GlobalTheory.RunIn
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) := by
  first | exact @GlobalTheory.semiAbelian_hom_extends_uniquely_dvr | exact GlobalTheory.semiAbelian_hom_extends_uniquely_dvr | (intros; apply GlobalTheory.semiAbelian_hom_extends_uniquely_dvr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.intFrExt_of_good_level : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c := by
  first | exact @GlobalTheory.Exist.intFrExt_of_good | exact GlobalTheory.Exist.intFrExt_of_good | (intros; apply GlobalTheory.Exist.intFrExt_of_good <;> assumption)
end
