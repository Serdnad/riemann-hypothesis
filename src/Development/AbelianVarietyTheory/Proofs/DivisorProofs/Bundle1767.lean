module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle292
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle522
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatHatCong

theorem cong_zero {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ) :
    t • (K *ᵥ 0 - 0) = M • (0 : Fin n → R) := by
  rw [Matrix.mulVec_zero, sub_zero, smul_zero, smul_zero]

theorem cong_add {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u w y y' : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) (e' : t • (K *ᵥ w - w) = M • y') :
    t • (K *ᵥ (u + w) - (u + w)) = M • (y + y') := by
  rw [Matrix.mulVec_add, add_sub_add_comm, smul_add, e, e', smul_add]

theorem cong_neg {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (-u) - (-u)) = M • (-y) := by
  rw [Matrix.mulVec_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, smul_neg, e, smul_neg]

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t c : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (c • u) - c • u) = M • (c • y) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, e, smul_comm]

theorem cong_on_hat : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  intro D V β Λ hβ K t M h z hz
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl] at h hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    obtain ⟨y, hy, e⟩ := h x hx
    have hm : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hy' := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ hm y hy
    have hc : (Algebra.TensorProduct.comm D.host.F _ D.host.E).symm ((1 : D.host.E) ⊗ₜ[D.host.F] a) =
        a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc] at hy'
    have hv : (fun i => a ⊗ₜ[D.host.F] x i) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • finVec V x := by
      funext i
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    refine ⟨_, hy', ?_⟩
    rw [hv]
    exact cong_smul e
  | zero =>
    exact ⟨0, AddSubgroup.zero_mem _, cong_zero K t M⟩
  | add u w _ _ hu hw =>
    obtain ⟨y, hy, e⟩ := hu
    obtain ⟨y', hy', e'⟩ := hw
    exact ⟨y + y', add_mem hy hy', cong_add e e'⟩
  | neg u _ hu =>
    obtain ⟨y, hy, e⟩ := hu
    exact ⟨-y, neg_mem hy, cong_neg e⟩

end GlobalTheory.LatHatCong
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.LevelLatticeCong

theorem cong_add {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ)
    {u₁ u₂ y₁ y₂ : Fin n → R} (f₁ : t • (K *ᵥ u₁ - u₁) = M • y₁) (f₂ : t • (K *ᵥ u₂ - u₂) = M • y₂) :
    t • (K *ᵥ (u₁ + u₂) - (u₁ + u₂)) = M • (y₁ + y₂) := by
  rw [smul_add, ← f₁, ← f₂, Matrix.mulVec_add, ← smul_add]
  congr 1
  abel

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t s : R) (M : ℕ)
    {u w : Fin n → R} (f : t • (K *ᵥ u - u) = M • w) :
    t • (K *ᵥ (s • u) - s • u) = M • (s • w) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, f, smul_comm]

end GlobalTheory.LevelLatticeCong

namespace GlobalTheory.LevelLatticeCong

theorem cong_on_sdLattice : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  intro D V β Λ hβ La _ _ ι hι K t M h
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [← GlobalTheory.OneMapRef.Lift.hatV_eq hβ]; rfl

  have hfv : ∀ (e : D.host.E) (v : Fin V.rank → D.host.E),
      finVec V (e • v) = ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] e) • finVec V v := by
    intro e v; funext i
    simp only [finVec, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

  have hint : ∀ c : 𝓞 D.host.E, ∀ z ∈ latHat V,
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latHat V := by
    intro c z hz
    rw [hl] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int Λ c hz

  have hinv : ∀ b ∈ ((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      ∀ w ∈ latGHat V 1, ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w ∈ latHat V := by
    intro b hb
    let s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
      (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b
    let H : AddSubgroup (Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
      (latHat V).comap (DistribSMul.toAddMonoidHom _ s)
    suffices hle : latGHat V 1 ≤ H from fun w hw => hle hw
    rw [GlobalTheory.LevelActionPinned.latGHat_one, AddSubgroup.closure_le]
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
      have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
        rw [← inv_mul_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
        exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hba
      have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) •
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) • z) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z := by
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 2
        exact hc.symm
      show s • _ ∈ latHat V
      rw [e]; exact hint c z hz
  let P : D.host.E → Prop := fun e => ∀ x ∈ Λ, ∃ y ∈ latHat V,
    t • (K *ᵥ finVec V (e • x) - finVec V (e • x)) = M • y
  have hadd : ∀ e₁ e₂ : D.host.E, P e₁ → P e₂ → P (e₁ + e₂) := by
    intro e₁ e₂ h₁ h₂ x hx
    obtain ⟨y₁, hy₁, f₁⟩ := h₁ x hx
    obtain ⟨y₂, hy₂, f₂⟩ := h₂ x hx
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    have e0 : finVec V ((e₁ + e₂) • x) = finVec V (e₁ • x) + finVec V (e₂ • x) := by
      rw [add_smul]; funext i; exact TensorProduct.tmul_add _ _ _
    rw [e0]
    exact cong_add K t M f₁ f₂
  have hmul : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E),
      ∀ b ∈ (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E), P (a * b) := by
    intro a ha b hb x hx
    have hxL : finVec V x ∈ latHat V := by
      rw [hl]; exact GlobalTheory.Member.AALev.fv_mem_hat _ hx
    have hax : a • x ∈ latG V 1 := by
      refine Submodule.subset_span ⟨a, ha, x, ?_, rfl⟩
      refine ⟨finVec V x, hxL, ?_⟩
      simp only [map_one, Units.val_one, Matrix.one_mulVec]
    rw [← hι.2] at hax
    obtain ⟨a', ha'⟩ := hax
    obtain ⟨w, hw, e⟩ := h a'
    rw [ha'] at e
    refine ⟨((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w, hinv b hb w hw, ?_⟩
    have e1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    rw [e1, hfv b]
    exact cong_smul K t _ M e
  have h1 : (1 : D.host.E) ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have hP : P 1 := Submodule.mul_induction_on h1 hmul hadd
  intro x hx
  simpa only [one_smul] using hP x hx

end GlobalTheory.LevelLatticeCong
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_rationalPoints_conj_in_support : ∀ (G H : Type) [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite := by
  first | exact @GlobalTheory.finite_support_conj_points | exact GlobalTheory.finite_support_conj_points | (intros; apply GlobalTheory.finite_support_conj_points <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableClosed
open GlobalTheory.RationalPoint

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (π : 𝓞 E), IsSemiAbelian G → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ G _ act π hG hπ hπu C Z hZ hC hstab htor
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨T⟩ := GlobalTheory.TorsionDense.nonempty_torusExtension G hG
  letI := T.addCommGroup
  letI := T.free
  letI := T.finite
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  haveI := T.isAbelian.proper
  haveI := T.isAbelian.smooth
  haveI := act.hom π
  obtain ⟨actB, actT, hB, hT⟩ := GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient (𝓞 E) k G act hG T
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ T.B) :=
    MonoidHom.mk' (fun x => x ≫ T.q) fun x y => MonObj.mul_comp x y T.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ T.i) fun x y => MonObj.mul_comp x y T.i
  let m : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ act.act π) fun x y => MonObj.mul_comp x y _
  have hj : Function.Injective j := fun x y hxy =>
    T.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨T.isKernel.lift x (toUnit _) hx, T.isKernel.lift_fst _ _ _⟩
  have hTf : Finite (C.comap j) := by
    refine GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion E k T.X actT π hπ hπu _ (T.i.left ⁻¹' Z)
      (hZ.preimage T.i.left.continuous) (fun x => ?_) (fun a x hx => ?_) (fun x hx h1 => ?_)
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · rw [Subgroup.mem_comap] at hx ⊢
      change (x ≫ actT.act a) ≫ T.i ∈ C
      rw [Category.assoc, hT a, ← Category.assoc]
      exact hstab a _ hx
    · apply hj
      rw [map_one]
      refine htor _ hx ?_
      change (x ≫ T.i) ≫ act.act π = 1
      rw [Category.assoc, ← hT π, ← Category.assoc, h1, MonObj.one_comp]
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ T.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G T.B T.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion E k T.B actB π T.isAbelian hπ hπu _ Z' hZ' (fun y => ?_) (fun a y hy => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · obtain ⟨x, rfl⟩ := hy
      refine ⟨⟨x.1 ≫ act.act a, hstab a _ x.2⟩, ?_⟩
      change (x.1 ≫ act.act a) ≫ T.q = (x.1 ≫ T.q) ≫ actB.act a
      rw [Category.assoc, Category.assoc, hB]
    · rintro _ ⟨y, rfl⟩ hy
      have hmC : ∀ z : C, m z.1 ∈ C := fun z => hstab π _ z.2
      have hmK : ∀ z : ψ.ker, ψ ⟨m z.1.1, hmC z.1⟩ = 1 := fun z => by
        change (z.1.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        change ψ z.1 ≫ actB.act π = 1
        rw [MonoidHom.mem_ker.1 z.2]
        haveI := actB.hom π
        exact MonObj.one_comp _
      let f : ψ.ker → ψ.ker := fun z => ⟨⟨m z.1.1, hmC z.1⟩, hmK z⟩
      have hf : Function.Injective f := fun z₁ z₂ h => by
        have h1 : m z₁.1.1 = m z₂.1.1 := congrArg (fun z : ψ.ker => z.1.1) h
        have h2 : z₁.1.1 / z₂.1.1 = 1 := htor _ (C.div_mem z₁.1.2 z₂.1.2) (by
          change m (z₁.1.1 / z₂.1.1) = 1
          rw [map_div, h1, div_self'])
        exact Subtype.ext (Subtype.ext (div_eq_one.1 h2))
      have hw : ψ ⟨m y.1, hmC y⟩ = 1 := by
        change (y.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        exact hy
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨⟨m y.1, hmC y⟩, hw⟩
      have h1 : m z.1.1 = m y.1 := congrArg (fun z : ψ.ker => z.1.1) hz
      have h2 : y.1 / z.1.1 = 1 := htor _ (C.div_mem y.2 z.1.2) (by
        change m (y.1 / z.1.1) = 1
        rw [map_div, h1, div_self'])
      have h3 : y = z.1 := Subtype.ext (div_eq_one.1 h2)
      rw [h3]
      exact z.2
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory.OStableClosed
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDimField

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' →
    IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g A'.hom := by
  intro K _ _ A A' _ _ g q hA hA' hfin hsurj hg
  have := hA.geomConnected
  have := hA'.geomConnected
  have := hA'.smooth
  have : ConnectedSpace A.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) (𝟙 _) (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected A'.hom (Classical.arbitrary A'.left)
  have hw : q.left ≫ A'.hom = A.hom := Over.w q
  have hg' : SmoothOfRelativeDimension g (q.left ≫ A'.hom) := by rw [hw]; exact hg
  have e := GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := K) q.left A'.hom hg' hm
  subst e
  exact hm

end GlobalTheory.FiniteSurjDimField
end
