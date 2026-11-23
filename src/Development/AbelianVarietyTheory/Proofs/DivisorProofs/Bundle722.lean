module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.PUnit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

open Opposite TopologicalSpace

theorem uConst_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → UConst A.hom := by
  intro R _ A _ hA R' _ _ X' s' φ hpb
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsm : Smooth s' := MorphismProperty.of_isPullback hpb ‹_›
  have hpr : IsProper s' := MorphismProperty.of_isPullback hpb ‹_›
  have hgc : GeometricallyConnected s' := MorphismProperty.of_isPullback hpb ‹_›
  haveI : GeometricallyIntegral s' :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X' _ s' hsm hgc
  have hiso : IsIso s'.appTop := GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth s' ⊤
  have hbij := ConcreteCategory.bijective_of_isIso s'.appTop
  intro g hg
  have hc : ∀ (U V : X'.affineOpens) (h : V.1 ≤ U.1),
      X'.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, htu⟩ := X'.sheaf.existsUnique_gluing' (fun U : X'.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X').ge (fun U ↦ g (op U)) (by
      intro U V
      refine X'.sheaf.eq_of_locally_eq' (fun W : {W : X'.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens X'} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(X', a)),
            X'.presheaf.map f'.op (X'.presheaf.map f.op x) = X'.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))

  have hres : ∀ (r : R') (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) =
        algebraMap R' (Sec s' U.1) r := by
    intro r U
    rfl
  have hres' : ∀ (x : Γ(Sp R', ⊤)) (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop x) =
        algebraMap R' (Sec s' U.1) ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) := by
    intro x U
    have := hres ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) U
    rw [Iso.hom_inv_id_apply] at this
    exact this
  obtain ⟨r₀, hr₀⟩ := hbij.2 t
  subst hr₀
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R')).hom r₀, ?_, ?_⟩
  · intro U
    exact (ht U.unop).symm.trans (hres' r₀ U.unop)
  · intro r hr
    have h1 : s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r) = s'.appTop r₀ := by
      apply htu
      intro U
      exact (hres r U).trans (hr (op U)).symm
    have h2 := hbij.1 h1
    rw [← h2, Iso.inv_hom_id_apply]

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.LowBaseChange

theorem krullDimLE_isLocalRing_quot_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 2 1 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩

variable {R : Type} [CommRing R]

theorem one_tmul_eq_zero_iff {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) (x : M) :
    (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R)
    (t : (R ⧸ I) ⊗[R] M) : ∃ x : M, (1 : R ⧸ I) ⊗ₜ[R] x = t :=
  TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective t

theorem projective_coker_of_approx [IsNoetherianRing R] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (hyp : ∀ (m : Ideal R) [m.IsMaximal] (n : ℕ) (a : A), f a ∈ m • (⊤ : Submodule R B) →
      ∃ y : A, f y ∈ m ^ (n + 1) • (⊤ : Submodule R B) ∧ f a - f y ∈ m • LinearMap.range f) :
    Module.Projective R (B ⧸ LinearMap.range f) := by
  haveI : IsNoetherian R B := isNoetherian_of_isNoetherianRing_of_finite R B
  have hinjq : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor (R ⧸ m)) := by
    intro m _
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨⟨_, a, rfl⟩, rfl⟩ := exists_one_tmul m t
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, one_tmul_eq_zero_iff] at ht
    set N := B ⧸ (m • LinearMap.range f)
    have hq : (m • LinearMap.range f).mkQ (f a) ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R N) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨y, hy, hay⟩ := hyp m n a ht
      have e : (m • LinearMap.range f).mkQ (f a) = (m • LinearMap.range f).mkQ (f y) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hay
      rw [e]
      have hle : m ^ (n + 1) • (⊤ : Submodule R B) ≤
          (m ^ n • (⊤ : Submodule R N)).comap (m • LinearMap.range f).mkQ := by
        refine Submodule.smul_le.2 fun r hr x _ => ?_
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) hr) Submodule.mem_top
      exact hle hy
    obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff _).1 hq
    have h1 : f a - (r : R) • f a ∈ m • LinearMap.range f := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul]
      exact hr.symm
    have hsplit : (⟨f a, LinearMap.mem_range_self f a⟩ : LinearMap.range f) =
        ⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a) (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ +
          (r : R) • ⟨f a, LinearMap.mem_range_self f a⟩ := by
      ext; simp
    rw [hsplit, TensorProduct.tmul_add, ← TensorProduct.smul_tmul]
    have h2 : (1 : R ⧸ m) ⊗ₜ[R] (⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a)
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ : LinearMap.range f) = 0 := by
      rw [one_tmul_eq_zero_iff, Submodule.mem_smul_top_iff]; exact h1
    rw [h2, zero_add, Algebra.smul_def, _root_.mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 r.2, TensorProduct.zero_tmul]
  have hinj : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor m.ResidueField) := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have hL : RingHom.ker (algebraMap R (R ⧸ m)) = m := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have := GlobalTheory.exact_lTensor_iff_residueField m (R ⧸ m) hL
      (0 : PUnit →ₗ[R] LinearMap.range f) (LinearMap.range f).subtype
    rw [LinearMap.lTensor_zero, LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective,
      LinearMap.exact_zero_iff_injective] at this
    exact this.1 (hinjq m)
  obtain ⟨l, hl⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
    (LinearMap.range f).subtype hinj
  have hex := (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    Subtype.val_injective (Submodule.mkQ_surjective _)).out 1 2
  obtain ⟨s, hs⟩ := hex.2 ⟨l, hl⟩
  exact Module.Projective.of_split s _ hs

end GlobalTheory.AbCoh.LowBaseChange


open GlobalTheory.AbCoh.LowBaseChange in
theorem GlobalTheory.AbCoh.projective_coker_of_liftsAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) →
      (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R']
        (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) →
      ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  intro R _ _ K hK _ hL i hi
  haveI := (hK (i + 1)).1
  haveI := (hK (i + 1)).2
  refine projective_coker_of_approx (K.d i (i + 1)).hom ?_
  intro m _ n a ha
  obtain ⟨h0, h1⟩ := krullDimLE_isLocalRing_quot_pow m n
  haveI := h1
  haveI : IsArtinianRing (R ⧸ m ^ (n + 1)) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, h0⟩
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hle : m ^ (n + 1) ≤ m := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let α : (R ⧸ m ^ (n + 1)) →ₐ[R] (R ⧸ m) := Ideal.Quotient.factorₐ R hle
  have hα : Function.Surjective α := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hz : dB K (R ⧸ m) i (i + 1) ((1 : R ⧸ m) ⊗ₜ[R] a) = 0 := by
    rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]
    exact ha
  obtain ⟨y, b, hy, hyb⟩ := hL i hi (R ⧸ m ^ (n + 1)) (R ⧸ m) α hα _ hz
  obtain ⟨y₀, rfl⟩ := exists_one_tmul _ y
  obtain ⟨b₀, rfl⟩ := exists_one_tmul _ b
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hy
  refine ⟨y₀, hy, ?_⟩
  rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    ← TensorProduct.tmul_add] at hyb
  have hdd : (K.d i (i + 1)).hom ((K.d (i - 1) i).hom b₀) = 0 := by
    have := congrArg (fun g => g.hom b₀) (K.d_comp_d (i - 1) i (i + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have hm : a - (y₀ + (K.d (i - 1) i).hom b₀) ∈ m • (⊤ : Submodule R (K.X i)) := by
    rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, ← hyb, sub_self]
  have := Submodule.mem_map_of_mem (f := (K.d i (i + 1)).hom) hm
  rw [Submodule.map_smul'', ← LinearMap.range_eq_map, map_sub, map_add (f := _), hdd, add_zero] at this
  exact this
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Transfer

theorem coneExact_baseChange_of_quasiIso {R R' : Type} [CommRing R] [CommRing R'] [inst : Algebra R R']
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    GlobalTheory.ConeExact (K := fun p => R' ⊗[R] K.X p) (C := fun p => R' ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.baseChange R') (fun p => (C.d p (p + 1)).hom.baseChange R')
      (fun p => (φ.f p).hom.baseChange R') := by
  have key := (GlobalTheory.quasiIso_iff_coneExact _).1 h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

variable {R : Type} [CommRing R] {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
  (R' : Type) [CommRing R'] [Algebra R R']

theorem dB_comm (i j : ℕ) (x : R' ⊗[R] K.X i) :
    dB C R' i j ((φ.f i).hom.baseChange R' x) = (φ.f j).hom.baseChange R' (dB K R' i j x) := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, φ.comm]

theorem dB_dB (L : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ) (x : R' ⊗[R] L.X i) :
    dB L R' j k (dB L R' i j x) = 0 := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, L.d_comp_d,
    ModuleCat.hom_zero, LinearMap.baseChange_zero, LinearMap.zero_apply]

def cycMap (i j : ℕ) : LinearMap.ker (dB K R' i j) →ₗ[R'] LinearMap.ker (dB C R' i j) :=
  ((φ.f i).hom.baseChange R').restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [dB_comm, hx, map_zero])

theorem cycMap_val (i j : ℕ) (z : LinearMap.ker (dB K R' i j)) :
    (cycMap φ R' i j z).1 = (φ.f i).hom.baseChange R' z.1 := rfl

theorem ext_comm {R'' : Type} [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) (y : R' ⊗[R] K.X i) :
    (φ.f i).hom.baseChange R'' (ext α _ y) = ext α _ ((φ.f i).hom.baseChange R' y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [ext]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exact_comp {H : Type} [AddCommGroup H] [Module R' H] (i j k : ℕ)
    (θ : LinearMap.ker (dB C R' j k) →ₗ[R'] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (dB C R' i j))
    (surj : ∀ c, dB C R' j k c = 0 → ∃ (c' : R' ⊗[R] C.X i) (k' : R' ⊗[R] K.X j),
      dB K R' j k k' = 0 ∧ dB C R' i j c' + (φ.f j).hom.baseChange R' k' = c)
    (inj : ∀ (k' : R' ⊗[R] K.X j) (c : R' ⊗[R] C.X i), dB K R' j k k' = 0 →
      (φ.f j).hom.baseChange R' k' = dB C R' i j c → k' ∈ LinearMap.range (dB K R' i j)) :
    Function.Surjective (θ.comp (cycMap φ R' j k)) ∧
      ∀ z, θ.comp (cycMap φ R' j k) z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' i j) := by
  refine ⟨fun x => ?_, fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hs x
    obtain ⟨c', k', hk', hsum⟩ := surj z.1 z.2
    have hm : dB C R' i j c' ∈ LinearMap.ker (dB C R' j k) := dB_dB R' C i j k c'
    have hz : z = cycMap φ R' j k ⟨k', hk'⟩ + ⟨_, hm⟩ := Subtype.ext (by
      rw [Submodule.coe_add, cycMap_val, ← hsum, add_comm])
    refine ⟨⟨k', hk'⟩, ?_⟩
    rw [LinearMap.comp_apply, hz, map_add (f := _), (hk ⟨_, hm⟩).2 ⟨c', rfl⟩, add_zero]
  · rw [LinearMap.comp_apply, hk, cycMap_val]
    constructor
    · rintro ⟨c, hc⟩
      exact inj z.1 c z.2 hc.symm
    · rintro ⟨b, hb⟩
      exact ⟨(φ.f i).hom.baseChange R' b, by rw [dB_comm, hb]⟩

end Transfer

theorem nonempty_model_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S],
      QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) →
    Model s C → Nonempty (Model s K) := by
  intro R _ X s K C φ hq M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    show IsPullback (𝟙 X) s s (spMap (RingHom.id R))
    rw [Cris.spMap_id]; exact IsPullback.id_horiz s
  obtain ⟨e1, -⟩ := M.θ0_one h0
  obtain ⟨y, hy1, hy2⟩ := (coneExact_baseChange_of_quasiIso φ (hq R)).zero ((1 : R) ⊗ₜ[R] M.one) 0
    ((LinearMap.mem_ker.1 e1).trans (map_zero _).symm) (map_zero _)
  let oneK : K.X 0 := TensorProduct.lid R (K.X 0) y
  have hy : (1 : R) ⊗ₜ[R] oneK = y := by
    rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
  have hinj : ∀ {M : ModuleCat.{0} R} (a b : M), (1 : R) ⊗ₜ[R] a = (1 : R) ⊗ₜ[R] b → a = b := fun a b hab => by
    rw [← TensorProduct.lid_symm_apply, ← TensorProduct.lid_symm_apply] at hab
    exact (TensorProduct.lid R _).symm.injective hab
  have hφone : (φ.f 0).hom oneK = M.one := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy]; exact hy1)
  have hdone : (K.d 0 1).hom oneK = 0 := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy, TensorProduct.tmul_zero]; exact hy2)
  refine ⟨{
    θ0 := fun {R'} _ _ {X'} {s'} {ψ} h => (LinearEquiv.ofBijective (cycMap φ R' 0 1) ⟨?_, ?_⟩).trans (M.θ0 h)
    one := oneK
    θ0_one := ?_
    θ1 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ1 h).comp (cycMap φ R' 1 2)
    θ2 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ2 h).comp (cycMap φ R' 2 3)
    exact := ?_
    nat := ?_ }⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext ((coneExact_baseChange_of_quasiIso φ (hq _)).inj z.1 (congrArg Subtype.val hz) z.2)
  · intro w
    obtain ⟨x, hx1, hx2⟩ := (coneExact_baseChange_of_quasiIso φ (hq _)).zero w.1 0
      ((LinearMap.mem_ker.1 w.2).trans (map_zero _).symm) (map_zero _)
    exact ⟨⟨x, hx2⟩, Subtype.ext hx1⟩
  · intro R' _ _ X' s' ψ h
    have e : (1 : R') ⊗ₜ[R] oneK ∈ LinearMap.ker (dB K R' 0 1) := by
      rw [LinearMap.mem_ker, dB, LinearMap.baseChange_tmul, hdone, TensorProduct.tmul_zero]
    obtain ⟨e', he'⟩ := M.θ0_one h
    refine ⟨e, fun T => ?_⟩
    have hc : cycMap φ R' 0 1 ⟨_, e⟩ = ⟨_, e'⟩ := Subtype.ext (by
      rw [cycMap_val, LinearMap.baseChange_tmul, hφone])
    show (M.θ0 h (cycMap φ R' 0 1 ⟨_, e⟩)).1 T = 1
    rw [hc]; exact he' T
  · intro R' _ _ X' s' ψ h
    have hc := coneExact_baseChange_of_quasiIso φ (hq R')
    obtain ⟨s1, k1, s2, k2⟩ := M.exact h
    have A := exact_comp φ R' 0 1 2 (M.θ1 h) s1 k1
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 0 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨x, -, hx⟩ := hc.zero c k' hkc.symm hk'
        exact ⟨x, hx⟩)
    have B := exact_comp φ R' 1 2 3 (M.θ2 h) s2 k2
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 1 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨c', k'', -, hx⟩ := hc.succ 0 c k' hkc.symm hk'
        exact ⟨k'', hx⟩)
    exact ⟨A.1, A.2, B.1, B.2⟩
  · intro R' _ _ X' s' ψ h R'' _ _ X'' s'' ψ' h' α χ w hχ
    obtain ⟨n1, n2⟩ := M.nat h h' α χ w hχ
    refine ⟨fun z z' hz => ?_, fun z z' hz => ?_⟩
    · show M.θ1 h' (cycMap φ R'' 1 2 z') = pullHO1 w (M.θ1 h (cycMap φ R' 1 2 z))
      exact n1 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])
    · show M.θ2 h' (cycMap φ R'' 2 3 z') = pullHO2 w (M.θ2 h (cycMap φ R' 2 3 z))
      exact n2 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])

end GlobalTheory.AbCoh
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem trace_rho_eq_zero_of_free {K Γ V X : Type} [Field K] [Group Γ] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ)
    [MulAction H X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (A : X → Submodule K V) (hA : DirectSum.IsInternal A)
    (hmap : ∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) (h : H) (hne : h ≠ 1) :
    LinearMap.trace K V (ρ h) = 0 := by
  classical
  refine LinearMap.trace_eq_zero_of_mapsTo_ne hA (fun x => h • x) (fun x hx => hne (hfree h x hx)) ?_
  intro x v hv
  exact hmap h x v hv

theorem card_mul_finrank_eig_of_free : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap Hb hle lam
  classical
  haveI : Fintype Hb := Fintype.ofFinite Hb
  set n : K := (Fintype.card Hb : K) with hn
  have hn0 : n ≠ 0 := by simp [hn, Fintype.card_ne_zero]
  let P : Module.End K V := n⁻¹ • ∑ h : Hb, (((lam h)⁻¹ : Kˣ) : K) • ρ h
  have hproj : LinearMap.IsProj (eig ρ Hb lam) P := by
    constructor
    · intro v
      rw [mem_eig]
      intro g

      simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
      rw [smul_comm]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, mul_inv, Units.val_mul]
      congr 1
      simp only [← Units.val_mul]
      congr 1
      group
    · intro v hv
      rw [mem_eig] at hv
      simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, hv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← hn, inv_mul_cancel₀ hn0, one_smul]
  have htr : LinearMap.trace K V P = n⁻¹ * (finrank K V : K) := by

    simp only [P, map_smul, map_sum, smul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp [LinearMap.trace_one]
    · intro h _ hne
      have h0 : LinearMap.trace K V (ρ h) = 0 :=
        trace_rho_eq_zero_of_free ρ H hfree A hA hmap ⟨h, hle h.2⟩ (by
          intro e; apply hne; ext; simpa using congrArg Subtype.val e)
      rw [h0, mul_zero]
    · simp
  have h1 := hproj.trace
  rw [htr] at h1
  rw [Nat.card_eq_fintype_card]
  have : ((Fintype.card Hb * finrank K (eig ρ Hb lam) : ℕ) : K) = (finrank K V : K) := by
    push_cast
    rw [← h1, ← hn, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  exact_mod_cast this

end GlobalTheory.BadCount
end
