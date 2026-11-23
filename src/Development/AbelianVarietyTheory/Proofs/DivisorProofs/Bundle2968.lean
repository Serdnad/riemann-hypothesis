module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecGeneratesSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endOn_exists : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ f : ρ.P.A ⟶ ρ.P.A, IsMonHom f → ∃ Fm : FinalForm.G ⟶ FinalForm.G, EndOn FinalForm f Fm := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm hU f₁ hf₁
  have : IsMonHom f₁ := hf₁
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ f₁
  have hw'l : w'.left ≫ ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ f₁.left := by
    have := congrArg (fun z => z.left) (pa (𝟙 _))
    simpa [pushPt] using this
  obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
  refine ⟨F, ?_⟩
  unfold EndOn
  have hsep : IsSeparated FinalForm.G.hom := FinalForm.semi.separated
  have hsm : Smooth FinalForm.G.hom := FinalForm.semi.smooth
  have hQf : Flat Q.hom := MorphismProperty.of_isPullback (P := @Flat) FinalForm.cart.1 inferInstance
  have hqc : QuasiCompact M.pt := by
    have : IsSeparated M.s := M.sep
    have : QuasiCompact (M.pt ≫ M.s) := by rw [M.pt_s]; infer_instance
    exact QuasiCompact.of_comp M.pt M.s
  have hdom : IsSchemeTheoreticallyDominant M.pt := .of_isDominant M.pt
  let p : pullback ρ.P.A.hom FinalForm.u₀ ⟶ M.Z := Q.hom ≫ U₀.ι
  let j := pullback.fst p M.pt
  have hj : j ≫ Q.hom = pullback.snd p M.pt ≫ x := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, hx]
    exact pullback.condition
  let k : pullback p M.pt ⟶ pullback FinalForm.G.hom M.pt := pullback.lift (j ≫ FinalForm.φ) (pullback.snd p M.pt) (by
    rw [Category.assoc, FinalForm.cart.1.w]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst FinalForm.G.hom M.pt = j ≫ FinalForm.φ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd p M.pt := pullback.lift_snd _ _ _
  have hkν : k ≫ ν = j := by
    apply FinalForm.cart.1.hom_ext
    · rw [Category.assoc, hν₁, hk₁]
    · rw [Category.assoc, hν₂, ← Category.assoc, hk₂, hj]
  have hF' : ((Over.pullback M.pt).map F).left ≫ pullback.fst FinalForm.G.hom M.pt = pullback.fst FinalForm.G.hom M.pt ≫ F.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hw₂ : w'.left ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd FinalForm.G.hom M.pt := Over.w w'
  have key : k ≫ w'.left ≫ ν = j ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hw'l]
      simp only [← Category.assoc]
      rw [hkν]
      simp only [Category.assoc, Over.pullback_map_left]
      exact congrArg (j ≫ ·) (pullback.lift_fst _ _ _).symm
    · have e : ((Over.pullback FinalForm.u₀).map f₁).left ≫ Q.hom = Q.hom := Over.w ((Over.pullback FinalForm.u₀).map f₁)
      show (k ≫ w'.left ≫ ν) ≫ Q.hom = (j ≫ ((Over.pullback FinalForm.u₀).map f₁).left) ≫ Q.hom
      simp only [Category.assoc]
      rw [hν₂, e, hj, ← Category.assoc w'.left, hw₂, ← Category.assoc, hk₂]
  refine GlobalTheory.SS.GenProj.ext_of_dense j FinalForm.G.hom ?_ ?_
  · have e1 : j ≫ FinalForm.φ ≫ F.left = k ≫ w'.left ≫ ν ≫ FinalForm.φ := by
      rw [hν₁, ← hFw, hF', ← Category.assoc k, hk₁, Category.assoc]
    rw [e1]
    simp only [← Category.assoc] at key ⊢
    rw [key]
  · rw [Category.assoc, Category.assoc, Over.w F, FinalForm.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.Poinc.Sep.Spz
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeGen

section
variable {X Y Z : Scheme.{0}} {L : LB X}

def Triv (L : LB X) (Y : Scheme.{0}) (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h

theorem Triv.mul {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (h' : Triv L Y F') :
    Triv L Y (fun U _ g => F U g * F' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g))⟩

theorem Triv.inv {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) :
    Triv L Y (fun U _ g => (F U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_⟩
  simp only [zpow_neg, Finset.prod_inv_distrib, e U g]

theorem Triv.pull {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (r : Z ⟶ Y) :
    Triv L Z (fun U _ g => F U (fun ψ => g (r ≫ ψ))) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  exact ⟨K, inferInstance, _, _, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _,
    fun U _ g => e U (fun ψ => g (r ≫ ψ))⟩

theorem Triv.exists_gen (hL : L.IsLB) {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F)
    (f : Y ⟶ X) (hf : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), F U g = g f) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => f) (ε' := fun _ => 1)
    (fun U _ g => by rw [e, hf]; simp) t ht
  exact ⟨t', ht'⟩

theorem triv_of_sec (θ : L.Sec) (f : Y ⟶ X) (hf : ∀ y, f y ∈ secNz θ) : Triv L Y (fun _ _ g => g f) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ f).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hf y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ f hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  exact ⟨Fin 1, inferInstance, _, _, ⟨fun j => (hu j).unit⟩,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ f).compat i j), fun U _ g => by simp⟩

end

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {T : Over S}

theorem triv_cub (c : CubicalStr G L) (x x' y : T ⟶ G) : Triv L.L T.left (fun _ _ h =>
    h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G).left)⁻¹) :=
  ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub x x' y h⟩

theorem triv_one (L : RigLB G) (T : Over S) : Triv L.L T.left (fun _ _ h => h (1 : T ⟶ G).left) :=
  ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ => eSec G) (fun _ => 1) L.rig T.hom,
    DVR.pullGen_isGen _ _ _ _ L.rigGen _, fun _ _ h => by rw [GlobalTheory.UU.one_left]; simp⟩

end GlobalTheory.Mum.CubeGen

namespace GlobalTheory.Mum

open CubeGen

theorem exists_gen_of_cubeTen (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G)
    (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens)
    (hW : ∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) :
    ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  have s : ∀ f ∈ cubeTen x a b c, Triv P.L.L W (fun _ _ g => g (W.ι ≫ f.left)) := fun f hf =>
    triv_of_sec θ _ fun y => hW f hf y.2
  have s₁ := s (x * a) (by simp [cubeTen])
  have s₂ := s (x * a⁻¹) (by simp [cubeTen])
  have s₃ := s a (by simp [cubeTen])
  have s₄ := s a⁻¹ (by simp [cubeTen])
  have s₅ := s (x * b) (by simp [cubeTen])
  have s₆ := s (x * c) (by simp [cubeTen])
  have s₇ := s (x * (b * c)⁻¹) (by simp [cubeTen])
  have s₈ := s b (by simp [cubeTen])
  have s₉ := s c (by simp [cubeTen])
  have s₀ := s (b * c)⁻¹ (by simp [cubeTen])
  have e := (triv_one P.L T).pull W.ι
  have c₁ := (triv_cub P.c x a a⁻¹).pull W.ι
  have c₂ := (triv_cub P.c x b c).pull W.ι
  have c₃ := (triv_cub P.c x (b * c) (b * c)⁻¹).pull W.ι
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  refine ((t₃.mul t₂.inv).mul e).exists_gen P.L.isLB _ fun U _ g => ?_
  simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closure_pow_lift {L L' : Type*} [CommRing L] [CommRing L'] (ρ : L →+* L') (C : Subring L) (u : L)
    (hu : u ∈ C) (G : Set L') (hG : ∀ g ∈ G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * g) :
    ∀ z ∈ Subring.closure G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * z := by
  intro z hz
  induction hz using Subring.closure_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨0, 0, C.zero_mem, by simp⟩
  | one => exact ⟨0, 1, C.one_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, u ^ l * w + u ^ k * v,
      C.add_mem (C.mul_mem (C.pow_mem hu _) hw) (C.mul_mem (C.pow_mem hu _) hv), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, e, e']
    ring
  | neg a _ ha =>
    obtain ⟨k, w, hw, e⟩ := ha
    exact ⟨k, -w, C.neg_mem hw, by rw [map_neg, e]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, w * v, C.mul_mem hw hv, ?_⟩
    rw [map_mul, e, e']
    ring

theorem exists_pow_mul_res {S : Scheme.{0}} {U : S.Opens} (hc : IsCompact (U : Set S))
    (hq : IsQuasiSeparated (U : Set S)) (g : Γ(S, U)) (U' : S.Opens) (hle : U' ≤ U) (hU' : U' = S.basicOpen g)
    (a : Γ(S, U')) : ∃ (k : ℕ) (b : Γ(S, U)), (S.presheaf.map (homOfLE hle).op).hom b =
      (S.presheaf.map (homOfLE hle).op).hom g ^ k * a := by
  subst hU'
  letI := (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom.toAlgebra
  have := isLocalization_basicOpen_of_qcqs hc hq g
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers g) a
  refine ⟨k, y, ?_⟩
  rw [← map_pow, mul_comm]
  simpa [RingHom.algebraMap_toAlgebra] using hy.symm

theorem presheaf_map_bijective_of_eq {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (e : A = B) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 A := Subsingleton.elim _ _
  simpa [this] using Function.bijective_id

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finFam_basicOpen_loc : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  intro S K _ gp _ r V t W hW f x hx
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : Sp K := (IsLocalRing.closedPoint K : PrimeSpectrum K)
  have pre : ∀ U U' : S.Opens, (gp.base p ∈ U ↔ gp.base p ∈ U') → gp ⁻¹ᵁ U = gp ⁻¹ᵁ U' := by
    intro U U' h
    ext q
    rw [Subsingleton.elim q p]
    exact h
  have bij : ∀ {U U' : S.Opens} (h : U' ≤ U), (gp.base p ∈ U ↔ gp.base p ∈ U') →
      Function.Bijective (resK gp h) := fun h e => presheaf_map_bijective_of_eq _ (pre _ _ e)
  by_cases hs : gp.base p ∈ S.basicOpen f
  swap
  · have e : gp ⁻¹ᵁ S.basicOpen f = ⊥ := by
      ext q
      rw [Subsingleton.elim q p]
      exact ⟨fun h => (hs h).elim, fun h => by simp at h⟩
    haveI : Subsingleton Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f) := by rw [e]; infer_instance
    exact ⟨0, 0, Subring.zero_mem _, Subsingleton.elim _ _⟩
  have hsW : gp.base p ∈ W := S.basicOpen_le f hs
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hNW : TopologicalSpace.NoetherianSpace (W : Set S) := noetherianSpace_of_isAffineOpen W hW
  have hcpt : ∀ T ⊆ (W : Set S), IsCompact T := (TopologicalSpace.noetherianSpace_set_iff _).mp hNW
  have hle : ∀ i, S.basicOpen f ⊓ V i ≤ W ⊓ V i := fun i => inf_le_inf_right _ (S.basicOpen_le f)
  rw [mem_finFam] at hx
  have step : ∀ i, ∃ k : ℕ, ∃ w ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)),
      resK gp (hle i) w = resK gp (hle i) (resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f)) ^ k *
        resK gp (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f) x := by
    intro i
    refine closure_pow_lift _ _ _ ?_ _ ?_ _ (hx i)
    · rw [resK_app]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
    · have hU' : S.basicOpen f ⊓ V i =
          S.basicOpen ((S.presheaf.map (homOfLE (inf_le_left : W ⊓ V i ≤ W)).op).hom f) := by
        rw [Scheme.basicOpen_res]
        exact le_antisymm (le_inf (le_inf (inf_le_left.trans (S.basicOpen_le f)) inf_le_right) inf_le_left)
          (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      have hWi : (↑(W ⊓ V i) : Set S) ⊆ W := fun z hz => hz.1
      obtain ⟨k, b, e⟩ := exists_pow_mul_res (hcpt _ hWi)
        (fun A B hA _ _ hB _ _ => hcpt _ ((Set.inter_subset_left.trans hA).trans hWi)) _ _ (hle i) hU' a
      refine ⟨k, (gp.app (W ⊓ V i)).hom b, Subring.subset_closure (Or.inl ⟨_, rfl⟩), ?_⟩
      rw [resK_app, resK_app, resK_app, e, map_mul, map_pow, ← CommRingCat.comp_apply]
    · refine ⟨0, resK gp (inf_le_right : W ⊓ V i ≤ V i) c, Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩), ?_⟩
      rw [pow_zero, _root_.one_mul, resK_resK]
  choose k w hw e using step
  let N := Finset.univ.sup k
  obtain ⟨y, hy⟩ := (bij (S.basicOpen_le f) ⟨fun _ => hs, fun _ => hsW⟩).2
    (resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ N * x)
  refine ⟨N, y, ?_, hy⟩
  rw [mem_finFam]
  intro i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hmem : resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f) ^ (N - k i) * w i ∈
      Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
        resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
    refine Subring.mul_mem _ (Subring.pow_mem _ ?_ _) (hw i)
    rw [resK_app]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  have inj := (bij (hle i) (by simp [hs, hsW])).1
  convert hmem using 1
  apply inj
  rw [map_mul, map_pow, e i, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hki, resK_resK, resK_resK,
    ← resK_resK gp (S.basicOpen_le f) (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f), hy, map_mul, map_pow,
    resK_resK]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isUnit_gs_id_iff {X : Scheme.{0}} (z : X) (U : X.Opens) (h : z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) z U a) ↔ z ∈ X.basicOpen a := by
  rw [gs_eq (𝟙 X) z U h, X.mem_basicOpen a z h]
  rfl

theorem exists_frame_of_isUnit_on_fibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  intro X Y β hβ L hL V s hs y hy hu
  let N : X.Opens := ⨆ k, X.basicOpen (s k)
  have hN : ∀ z : X, β z = y → z ∈ N := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_chart hL z
    have hm : z ∈ β ⁻¹ᵁ V ⊓ L.U k := ⟨show β z ∈ V from hz ▸ hy, hk⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_id_iff z _ hm _).1 (hu z k hz hk)⟩
  let V₀ : Y.Opens := ⟨(β '' (N : Set X)ᶜ)ᶜ, (hβ _ N.2.isClosed_compl).isOpen_compl⟩
  have hy₀ : y ∈ V₀ := by
    rintro ⟨p, hp, e⟩
    exact hp (hN p e)
  have hV₀ : ∀ p : X, β p ∈ V₀ → p ∈ N := by
    intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩
  have hle : ∀ k, β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k ≤ β ⁻¹ᵁ V ⊓ L.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have hunit : ∀ k, IsUnit ((X.presheaf.map (homOfLE (hle k)).op).hom (s k)) := by
    intro k
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV₀ z hz.1.2)
    have hm' : z ∈ β ⁻¹ᵁ V ⊓ L.U k' := X.basicOpen_le _ hk'
    have h1 : IsUnit (gs (𝟙 X) z _ (s k)) := by
      rw [hs z k k' hm'.1 hz.2 hm'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_id_iff z _ hm' _).2 hk')
    rw [← gs_res (𝟙 X) z (hle k) hz, gs_eq (𝟙 X) z _ hz] at h1
    exact h1
  have key : ∀ (f : X ⟶ X) (z : X) (k : L.ι), f z ∈ β ⁻¹ᵁ (V ⊓ V₀) → f z ∈ L.U k →
      (gm f z _ (hunit k).unit : X.presheaf.stalk z) = gs f z _ (s k) := by
    intro f z k h1 h2
    have hm : f z ∈ β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k := ⟨h1, h2⟩
    rw [← gs_unit f z _ hm, IsUnit.unit_spec, gs_res f z (hle k) hm]
  refine ⟨V ⊓ V₀, ⟨hy, hy₀⟩, inf_le_left, fun k => (hunit k).unit, ?_, ?_⟩
  · intro k k'
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz]
    apply Units.ext
    rw [Units.val_mul, key (𝟙 X) z k hz.1.1 hz.1.2, key (𝟙 X) z k' hz.2.1 hz.2.2]
    exact hs z k k' hz.1.1.1 hz.1.2 hz.2.2
  · intro f w hw z j k hz hfz hk hj
    apply Units.ext
    rw [Units.val_mul, key f z j hfz hj, key (𝟙 X) z k hz hk]
    exact hw z j k hz.1 hfz.1 hk hj

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.formalSum_twist_cube_identity : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  first | exact @GlobalTheory.MumCmp.formEq_twist_cube | exact GlobalTheory.MumCmp.formEq_twist_cube | (intros; apply GlobalTheory.MumCmp.formEq_twist_cube <;> assumption)
end
