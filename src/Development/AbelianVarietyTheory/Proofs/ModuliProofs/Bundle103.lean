module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle096
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isThetaPtOver_pull_of_gen {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T)
    (hg : ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 h th)) :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, hg _ hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem exists_basicOpen_isGenSec (hS : SecBaseChangeAnySt) [IsAffine T.left] (V : T.left.Opens) (p : T.left)
    (hp : p ∈ V) : ∃ f : Γ(T.left, ⊤), p ∈ T.left.basicOpen f ∧
      ∃ j : overRes (T.left.basicOpen f) ⟶ overRes V, j ≫ overResι V = overResι _ ∧
        ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 j th) := by
  obtain ⟨V₀, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := V ⊓ T.hom ⁻¹ᵁ V₀) ⟨p, hp, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V₀ := Over.homMk
    (IsOpenImmersion.lift V₀.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact (hf y.2).2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hle : W ≤ V := hf.trans inf_le_left
  let j : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hj : j ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  refine ⟨f, hpf, j, hj, fun th H s => ?_⟩
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := EmbPull.exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (pullS P.A 1 (overResι V) (SecM.toSec P.A u))
  have hr' : pullM P.A P.L 1 (overResι V) u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have e₁ := congrArg (pullM P.A P.L 1 j) hr'
  rw [pullM_comp _ P.isLB, hj, hu, LinearMap.map_smulₛₗ] at e₁
  obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W).left, ⊤), SecM.ofSec P.A s =
      d • pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)) := by
    have := c.sum_repr (SecM.ofSec P.A s)
    rw [Fintype.sum_unique, hc] at this
    exact ⟨_, this.symm⟩
  have hf₁ : IsUnit (W.ι.appTop.hom f) := by
    refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    rw [← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨a, ha⟩ : IsUnit ((overResι W).left.appTop.hom (f ^ n)) := by
    rw [map_pow]
    exact hf₁.pow n
  have key : SecM.ofSec P.A s = (d * (a⁻¹ : Γ((overRes W).left, ⊤)ˣ) * j.left.appTop.hom r) •
      pullM P.A P.L 1 j (SecM.ofSec P.A th) := by
    rw [mul_smul, ← e₁, ← ha, ← mul_smul, Units.inv_mul_cancel_right, hd]
  exact ⟨_, fun i => congrArg (fun q => q.1 i) key⟩

theorem isThetaPt_pull (hS : SecBaseChangeAnySt) [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T) {n : ℕ} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P n x v) :
    IsThetaPt P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  obtain ⟨h₁, h₂, H⟩ := H
  refine ⟨h₁, by simpa using h₂.map h.left.appTop.hom, fun p => ?_⟩
  obtain ⟨V, hV, H⟩ := H (h.left p)
  obtain ⟨f, hf, j, hj, hg⟩ := exists_basicOpen_isGenSec P hS V _ hV
  let f' := h.left.appTop.hom f
  have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
  let W := T.left.basicOpen f
  let W' := T'.left.basicOpen f'
  let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf'.ge y.2)
  have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
  let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
    change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
    rw [← Category.assoc, hk₀, Category.assoc, Over.w])
  have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
  have : IsAffine (overRes W).left := hW
  have : IsAffine (overRes W').left := hW'
  have Q := isThetaPtOver_pull_of_gen P (isThetaPtOver_pull_of_gen P H j hg) k
    fun _ => EmbPull.isGenSec_pullS P hS k
  have e : k ≫ j ≫ overResι V = overResι W' ≫ h := by rw [hj]; exact hk
  refine ⟨W', hf'.le hf, ?_⟩
  convert Q using 2 with a a
  · rw [← Category.assoc, ← e]
    simp only [Category.assoc]
  · exact (congrArg (fun q => q.left.appTop.hom (v a)) e).symm

end GlobalTheory.ThetaBaseChange

theorem GlobalTheory.hasTh_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  intro hl o _ g N' J b S s t R R' _ _ φ x v H
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap φ ≫ x)).left := inferInstanceAs (IsAffine (Spec _))
  have Q := GlobalTheory.ThetaBaseChange.isThetaPt_pull t.pol hl.secBaseChangeAny
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) H
  unfold TObj.HasTh
  convert Q using 2 with a a
  · exact Over.OverMorphism.ext (Category.assoc (spMap φ) x (t.lab a).left)
  · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaLevelPullback_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) := by
  first | exact @GlobalTheory.ZM.tmap_id_comp_cancel | exact GlobalTheory.ZM.tmap_id_comp_cancel | (intros; apply GlobalTheory.ZM.tmap_id_comp_cancel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

theorem fix_geometric_torsion {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S : Scheme.{0}}
    {s : S ⟶ Sp o} (t : TObj g k J b s) (θ : t.A ⟶ t.A) [IsMonHom θ] (hpt : ∀ i, t.pt i ≫ θ = t.pt i)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ t.A) (hy : y ^ k = 1) : y ≫ θ = y := by
  obtain ⟨c, rfl, -⟩ := t.bij K x y hy
  let F : (Over.mk x ⟶ t.A) →* (Over.mk x ⟶ t.A) := IsMonHom.monoidHom θ (Over.mk x)
  refine (map_list_prod F _).trans (congrArg List.prod ?_)
  rw [List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => (map_pow F _ _).trans (congrArg (· ^ (c i).val) ?_))
  show (_ ≫ t.pt i) ≫ θ = _
  rw [Category.assoc, hpt]

theorem tObj_rigid : Out.Laws → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (f : S ⟶ S'), 3 ≤ k → ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A f φ → IsGrpPullback t.A t'.A f φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  intro hL o _ g k J b S S' s s' t t' f hk φ φ' hφ hφ' hl hl' hpt
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso hφ hφ'
  have hη : ∀ i, t.pt i ≫ θ.hom = t.pt i := fun i => by
    apply Over.OverMorphism.ext
    apply hφ'.1.hom_ext
    · rw [Over.comp_left, Category.assoc, e]
      exact hpt i
    · rw [Over.w, Over.w]
  have h₁ : LBIso (t.L.pull θ.hom.left) (t'.L.pull φ) :=
    LBIso.chartPull (chartPullPull t.L _ θ.hom.left rfl) (chartPullSame t'.L _ _ _ θ.hom.left fun _ => e.symm) hl'
  obtain ⟨w, hw⟩ : LBIso t.L (t.L.pull θ.hom.left) :=
    LBIso.trans t.isLB (LB.isLB_pull t'.isLB φ) (LB.isLB_pull t.isLB _) hl h₁.symm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    simpa using b.unit.map ((Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ s.appTop).hom
  have := t.ab.comm
  have := t.ab.smooth
  have : Etale (Out.mulA t.A k).left := GrpTangent.etale_id_pow t.A hku
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL t.pol k hk θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t.A k θ.hom (fix_geometric_torsion t θ.hom hη))
    obtain ⟨u, hu⟩ := gen_of_iso ((isGen_iff w).1 hw) (t.A.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut t.L _ _ _ _ fun n => ?_) u hu
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← e, h, Over.id_left, Category.id_comp]

end GlobalTheory.TUniq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_isPullback :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → IsPullback ρ₀ A'.hom A₀.hom (spMap (algebraMap K (DualNumber K))) → j ≫ ρ₀ = 𝟙 _ → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro L K _ A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ
  obtain ⟨ρ, h₁, h₂⟩ := exists_isGrpPullback_retraction L.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ
  exact ⟨ρ, h₁, hj, h₂⟩

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GoodRedUnitBall

theorem finiteType_closure (s : Set ℂ) (hs : s.Finite) :
    (algebraMap ℤ (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) := Algebra.FiniteType.adjoin_of_finite hs
  rw [RingHom.finiteType_algebraMap]
  have e : (Algebra.adjoin ℤ s).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_int]; rfl
  refine Algebra.FiniteType.of_surjective (R := ℤ) (A := Algebra.adjoin ℤ s)
    (RingEquiv.subringCongr e).toRingHom.toIntAlgHom (RingEquiv.subringCongr e).surjective

theorem valuationRing_of_unitBall {V C : Type} [CommRing V] [NormedField C] [Algebra V C] (h : IsUnitBall V C) :
    ∃ _ : IsDomain V, ValuationRing V ∧ IsFractionRing V C := by
  have hd : IsDomain V := h.1.isDomain _
  refine ⟨hd, ?_⟩
  have key : ∀ x : C, IsLocalization.IsInteger V x ∨ IsLocalization.IsInteger V x⁻¹ := by
    intro x
    rcases le_total ‖x‖ 1 with hx | hx
    · exact Or.inl ((h.2 x).2 hx)
    · exact Or.inr ((h.2 x⁻¹).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx))
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 h.1
  have hf : IsFractionRing V C := by
    refine IsFractionRing.of_field V C fun x => ?_
    rcases key x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, 1, by simp [ha]⟩
    · exact ⟨1, a, by simp [ha]⟩
  exact ⟨(ValuationRing.iff_isInteger_or_isInteger V C).2 key, hf⟩

theorem goodRedExt_unitBall : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), Raises B Y → ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra V C], IsUnitBall V C → Y.GoodRedExt V C := by
  intro hext E _ _ _ H D Xo n N T l₀ B l c O _ β Y hR V C _ _ _ _ hV b y hy ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, hab, _, _, h₁, h₂, _⟩
  obtain ⟨_, _, _⟩ := valuationRing_of_unitBall hV
  obtain ⟨b₀, r, ν, -, -, ⟨ab⟩⟩ := hR
  have hp : IsProper Y.s := projProper _ _ _ Y.proj
  have hp' : IsProper B.C.s := projProper _ _ _ B.C.proj
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨q⟩⟩ := hE
    { R := V
      K := C
      i₁ := y ≫ Y.j
      i₂ := spMap b
      commSq := ⟨by rw [Category.assoc]; exact hy⟩ }
  obtain ⟨y', hs, hl⟩ : ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V C) ≫ y' = y ≫ Y.j :=
    ⟨q.l, q.fac_right, q.fac_left⟩
  obtain ⟨π, hπ⟩ : ∃ π : Y.X ⟶ B.C.X, π = ab.π := ⟨_, rfl⟩
  refine ⟨y', hs, hl, ?_⟩
  have hz : LocallyOfFiniteType (spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact finiteType_closure _ (Set.toFinite _)
  have hc : IsGrpPullback Y.t.G B.C.t.G π ab.mu.φ := hπ ▸ ab.mu.cart
  have h₃ := (h₂.comp Y.m.cart).comp hc
  have h₄ : IsGrpPullback A B.C.t.G (spMap (algebraMap V C) ≫ (y' ≫ π)) ((φ₂ ≫ Y.m.φ) ≫ ab.mu.φ) := by
    rw [← Category.assoc, hl]
    exact h₃
  have h₅ := GlobalTheory.T.range_subset_abelianLocus_of_goodReduction hext B.C.X (B.C.s ≫ spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) B.C.t.G V C (y' ≫ π) 𝒜 A φ₁ _
    inferInstance B.C.t.semi hab h₁ h₄
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne B.C.t.semi hc.1 _).1 (h₅ ⟨x, rfl⟩)

end GlobalTheory.GoodRedUnitBall
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingComb

open CommutatorPairing

theorem exists_gen_linComb {X X' Y' : Scheme.{0}} {D : LB X} {I K : Type} [Fintype I] [Fintype K]
    (F : I → (X' ⟶ X)) (e : I → ℤ) (ψ : K → (Y' ⟶ X')) (ε : K → ℤ) {Y : I → Scheme.{0}} (h : ∀ i, Y' ⟶ Y i)
    (φ : ∀ i, K → (Y i ⟶ X)) (hc : ∀ i k, ψ k ≫ F i = h i ≫ φ i k)
    (t : ∀ i, LB.Gen (LB.LinComb D (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb D F e) ψ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₀ : (Z ⟶ X) → D.ι), Good D z J₀ →
        val u r z (fun χ i => J₀ (χ ≫ F i)) = ∏ i, val (t i) (r ≫ h i) z J₀ ^ e i := by
  have le : ∀ (jj : K → I → D.ι) (i : I), LB.wchart (LB.LinComb D F e) ψ jj ≤
      h i ⁻¹ᵁ LB.wchart D (φ i) (fun k => jj k i) := fun jj i y hy => Set.mem_iInter.2 fun k => by
    have h₁ : (ψ k ≫ F i) y ∈ D.U (jj k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
    rw [hc] at h₁
    exact h₁
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jj : K → I → D.ι), r z ∈ LB.wchart (LB.LinComb D F e) ψ jj →
      gm r z (LB.wchart (LB.LinComb D F e) ψ jj) (∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i) =
        ∏ i, gm (r ≫ h i) z (LB.wchart D (φ i) fun k => jj k i) ((t i).s fun k => jj k i) ^ e i := by
    intro Z r z jj hz
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, gm_res r z _ hz]
    exact congrArg (· ^ e i) (gm_pull r (h i) z _ (le jj i hz) _)
  refine ⟨⟨fun jj => ∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i⟩,
    (CechPic.isGen_iff_germ _).2 fun y j j' hj hj' => ?_, fun Z r z J₀ hJ => ?_⟩
  · refine (v _ (𝟙 Y') y j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_linComb (LB.LinComb D F e) ψ ε (𝟙 Y') y j j' hj hj') (v _ (𝟙 Y') y j' hj')).symm)
    have a : ∀ i, gm (𝟙 Y' ≫ h i) y (LB.wchart D (φ i) fun k => j k i) ((t i).s fun k => j k i) = _ := fun i =>
      gen_trans (ht i) (𝟙 Y' ≫ h i) y (le j i hj) (le j' i hj')
    have b : ∀ k, _ := fun k => gm_linComb D F e (𝟙 Y' ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)
    simp only [a, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    refine Eq.trans ?_ (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (b k)).symm
    simp only [trF, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, hc]
    rw [Finset.prod_comm]
    simp only [mul_comm]
  · have hz : r z ∈ LB.wchart (LB.LinComb D F e) ψ (fun k i => J₀ ((r ≫ ψ k) ≫ F i)) :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => hJ ((r ≫ ψ k) ≫ F i)
    refine (v Z r z _ hz).trans (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_)
    exact (val_of (t i) (r ≫ h i) z J₀ _ fun k => by rw [Category.assoc, Category.assoc, hc]).symm

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] {D : LB A.left} {I : Type} [Fintype I]

theorem exists_theta_linComb (φ : I → (G ⟶ A)) (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S}
    {T' : I → Over S} (m : ∀ i, T ⟶ T' i) (x : T ⟶ G) (θ₀ : ∀ i, ThetaGrp A D n (T' i))
    (hx : ∀ i, m i ≫ (θ₀ i).pt = x ≫ φ i) :
    ∃ θ : ThetaGrp G (LB.LinComb D (fun i => (φ i).left) e) n T, θ.pt = x ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ G) (z : Z.left) (J₀), Good D z J₀ →
        thetaVal θ t a z (fun χ i => J₀ (χ ≫ (φ i).left)) = ∏ i, thetaVal (θ₀ i) (t ≫ m i) (a ≫ φ i) z J₀ ^ e i := by
  have hc : ∀ i (k : Fin 2), ![(snd T G).left, (translPt G x).left] k ≫ (φ i).left =
      (lift (fst T G ≫ m i) (snd T G ≫ φ i)).left ≫ ![(snd (T' i) A).left, (translPt A (θ₀ i).pt).left] k := by
    intro i k
    have := hφ i
    fin_cases k
    · exact congrArg CommaMorphism.left (lift_snd (fst T G ≫ m i) (snd T G ≫ φ i)).symm
    · refine congrArg CommaMorphism.left (?_ : translPt G x ≫ φ i = _ ≫ translPt A (θ₀ i).pt)
      rw [lift_translPt, Category.assoc, hx]
      show ((fst T G ≫ x) * snd T G) ≫ φ i = _
      rw [MonObj.mul_comp, Category.assoc]
  obtain ⟨u, hu, hv⟩ := exists_gen_linComb (fun i => (φ i).left) e _ ![n, -n] _ _ hc (fun i => (θ₀ i).φ)
    (fun i => (θ₀ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J₀ hJ => (hv _ (lift t a).left z J₀ hJ).trans ?_⟩
  refine Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  rfl

theorem weilIs_linComb (hG : GlobalFnsSt) (hA : IsAbelianScheme G) (hD : D.IsLB) (φ : I → (G ⟶ A))
    (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S} {x y : T ⟶ G} (c : I → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A D n (x ≫ φ i) (y ≫ φ i) (c i)) :
    WeilIs G (LB.LinComb D (fun i => (φ i).left) e) n x y (∏ i, c i ^ e i) := by
  have hL := LB.isLB_linComb hD (fun i => (φ i).left) e
  refine WeilIsogeny.weilIs_of_local hG hA hL fun p => ?_
  choose V hV H using fun i => h i p
  choose θx₀ θy₀ ex ey using fun i => (H i).1
  let V₀ : T.left.Opens := ⟨⋂ i, (V i : Set T.left), isOpen_iInter_of_finite fun i => (V i).isOpen⟩
  have le : ∀ i, V₀ ≤ V i := fun i _ hz => Set.mem_iInter.1 hz i
  obtain ⟨θx, fx, vx⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ x) θx₀
    (fun i => by rw [ex, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ y) θy₀
    (fun i => by rw [ey, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨c', hc'⟩ := exists_commIsOf hG hA hL θx θy
  refine ⟨V₀, Set.mem_iInter.2 hV, θx, θy, fx, fy, ?_⟩
  obtain rfl : c' = unitRes V₀ (∏ i, c i ^ e i) := by
    refine unit_ext fun z _ => ?_
    choose J₀ hJ₀ using fun χ : (overRes V₀).left ⟶ A.left => exists_chart hD (χ z)
    have e₁ := (commIsOf_iff hL _ _ _).1 hc' _ (𝟙 _) 1 z (fun χ i => J₀ (χ ≫ (φ i).left))
      (fun χ => Set.mem_iInter.2 fun i => hJ₀ (χ ≫ (φ i).left))
    have e₂ : ∀ i, _ := fun i => (commIsOf_iff hD _ _ _).1 ((H i).2 (θx₀ i) (θy₀ i) (ex i) (ey i)) _
      (𝟙 _ ≫ overLE (le i)) (1 ≫ φ i) z J₀ hJ₀
    have gx : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θx₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θx.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ex, fx, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have gy : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θy₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θy.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ey, fy, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have e₃ : ∀ i, gm (𝟙 _ ≫ overLE (le i)).left z ⊤ (unitRes (V i) (c i)) = gm (𝟙 _ ≫ V₀.ι) z ⊤ (c i) := fun i => by
      refine (gm_unitRes (V i) (c i) _ z).trans ?_
      exact congrArg (fun q => gm q z ⊤ (c i)) (congrArg CommaMorphism.left
        ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) (overLE_ι (le i)))))
    refine e₁.symm.trans (Eq.trans ?_ (gm_unitRes V₀ _ (𝟙 _) z).symm)
    unfold commVal
    rw [vx _ _ _ _ _ hJ₀, vx _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, map_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← e₃, ← e₂, commVal, gx, gy]
    simp only [mul_zpow, inv_zpow]
  exact hc'

end GlobalTheory.PairingComb
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem pol_pull :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') :=
  PolPull.pol_pull_of_relAmple_local GlobalTheory.T.relAmple_of_locally_on_base

end GlobalTheory
end
end
