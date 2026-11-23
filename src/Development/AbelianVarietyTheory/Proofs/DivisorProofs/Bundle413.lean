module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacquetBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem hasFiniteLength_twist_iff (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.apply_mem_toSubmodule g hv
        rw [twist_apply] at h1
        have h2 := S.toSubmodule.smul_mem ((χ g : F)⁻¹) h1
        rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_surjective {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : HasFiniteLength ρ) :
    HasFiniteLength σ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_blk {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    subst hij
    rw [h a x y]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply, e.injective.eq_iff]


omit [LinearOrder α] in
theorem leviEmb_apply_of_blk_ne [DecidableEq α] (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by
  letI : DecidableEq α := Classical.typeDecidableEq α
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  have hab : a ≠ b := by simpa using h
  simpa [leviEmb, Matrix.reindex_apply] using
    (Matrix.blockDiagonal'_apply_ne (fun c => (g c : Matrix (m c) (m c) R)) x y hab)

theorem leviEmb_leviProj_of_blk (e : (Σ a, m a) ≃ n) (p : parab R e)
    (h : ∀ i j, blk e i ≠ blk e j → ((p : GL n R) : Matrix n n R) i j = 0) :
    leviEmb R e (leviProj R e p) = p := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    simp [leviEmb, Matrix.reindex_apply, leviProj_apply]
  · have hblk : blk e (e ⟨a, x⟩) ≠ blk e (e ⟨b, y⟩) := by simpa using hab
    rw [leviEmb_apply_of_blk_ne e _ hblk, h _ _ hblk]

theorem leviProj_eq_of_coe_eq (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, h]
  simp [leviEmb, Matrix.reindex_apply]

end Blocks

section Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_of_transport (e : (Σ a, m a) ≃ n) (e' : (Σ b, m' b) ≃ n')
    (Φ : GL n' k →* GL n k) (Ψ : Levi k m' →* Levi k m) (hΨ : Function.Surjective Ψ)
    (hU : ∀ u ∈ unipRad k e', Φ u ∈ unipRad k e)
    (hL : ∀ g, Φ (leviEmb k e' g) = leviEmb k e (Ψ g)) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e' (π.comp Φ))) : HasFiniteLength (jacU e π) := by
  have hle : twKer (π.comp Φ) (unipRad k e') 1 ≤ twKer π (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨Φ u, hU u u.2⟩, v, by simp⟩
  let f : (jacU e' (π.comp Φ)).IntertwiningMap ((jacU e π).comp Ψ) :=
    ⟨(twKer (π.comp Φ) (unipRad k e') 1).mapQ (twKer π (unipRad k e) 1) LinearMap.id hle,
      fun g => by
        ext v
        show Submodule.Quotient.mk (π (Φ (leviEmb k e' g)) v) =
          (Submodule.Quotient.mk (π (leviEmb k e (Ψ g)) v) : Jacquet π (unipRad k e))
        rw [hL]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  rw [← hasFiniteLength_comp_iff _ Ψ hΨ]
  exact hasFiniteLength_of_surjective f hf h

end Transport

section Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_reindex (e : (Σ b, m' b) ≃ n') (ψ : n' ≃ n)
    (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e (π.comp
      (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom))) :
    HasFiniteLength (jacU (e.trans ψ) π) := by
  set Φ : GL n' k →* GL n k := (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦ : ∀ (g : GL n' k) (i j : n), (Φ g : Matrix n n k) i j = (g : Matrix n' n' k) (ψ.symm i) (ψ.symm j) :=
    fun _ _ _ => rfl
  refine hasFiniteLength_jacU_of_transport (e.trans ψ) e Φ (MonoidHom.id _) Function.surjective_id
    (fun u hu => ?_) (fun g => ?_) π h
  · rw [mem_unipRad] at hu ⊢
    refine ⟨mem_parab_iff.2 fun a b x y hab => ?_, fun a x y => ?_⟩
    · rw [hΦ]
      simpa using mem_parab_iff.1 hu.1 a b x y hab
    · rw [hΦ]
      simpa using hu.2 a x y
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hΦ]
    rfl

end Stages

end GlobalTheory.JacquetBlocks

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorSub

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (X : Representation ℂ G V) (T : Representation ℂ H W)

def up (U : Subrepresentation X) : Subrepresentation (extTensor X T) where
  toSubmodule := LinearMap.range (U.toSubmodule.subtype.rTensor W)
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u w =>
      refine ⟨⟨X g.1 u, U.apply_mem_toSubmodule g.1 u.2⟩ ⊗ₜ T g.2 w, ?_⟩
      simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy

def down (S : Subrepresentation (extTensor X T)) : Subrepresentation X where
  toSubmodule :=
    { carrier := {v | ∀ w : W, v ⊗ₜ[ℂ] w ∈ S.toSubmodule}
      add_mem' := fun ha hb w => by rw [TensorProduct.add_tmul]; exact add_mem (ha w) (hb w)
      zero_mem' := fun w => by rw [TensorProduct.zero_tmul]; exact zero_mem _
      smul_mem' := fun c v hv w => by
        rw [← TensorProduct.smul_tmul']; exact S.toSubmodule.smul_mem c (hv w) }
  apply_mem_toSubmodule g v hv w := by
    have := S.apply_mem_toSubmodule (g, 1) (hv w)
    simpa using this

theorem exists_asAlgebraHom_eq {T : Representation ℂ H W} (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1)
    (A : Module.End ℂ W) (s : Finset W) :
    ∃ r : MonoidAlgebra ℂ H, ∀ v ∈ s, T.asAlgebraHom r v = A v := by
  classical
  set R := MonoidAlgebra ℂ H
  have hsimple : IsSimpleModule R T.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule T).1 hirr
  set E := T.asModuleEquiv
  have hsc : ∀ φ : Module.End R T.asModule, ∃ c : ℂ, ∀ x, E (φ x) = c • E x := by
    intro φ
    let B : Module.End ℂ W :=
      { toFun := fun v => E (φ (E.symm v))
        map_add' := fun a b => by simp
        map_smul' := fun c v => by
          rw [RingHom.id_apply, Representation.asModuleEquiv_symm_map_smul, map_smul,
            Representation.asModuleEquiv_map_smul, AlgHom.commutes,
            Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] }
    obtain ⟨c, hc⟩ := hschur B fun m => by
      ext v
      simp only [Module.End.mul_apply, B, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
        Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
        Representation.asAlgebraHom_single_one]
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun F : Module.End ℂ W => F (E x)) hc
    simpa [B] using this
  let f : Module.End (Module.End R T.asModule) T.asModule :=
    { toFun := fun x => E.symm (A (E x))
      map_add' := fun a b => by simp
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        show E.symm (A (E (φ x))) = φ (E.symm (A (E x)))
        apply E.injective
        rw [hc, hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f (s.image E.symm)
  refine ⟨r, fun v hv => ?_⟩
  have := hr (E.symm v) (Finset.mem_image_of_mem _ hv)
  have h2 := congrArg E this
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
  rw [h2, Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]

theorem map_mem (S : Subrepresentation (extTensor X T)) (r : MonoidAlgebra ℂ H) {z : V ⊗[ℂ] W}
    (hz : z ∈ S.toSubmodule) : TensorProduct.map LinearMap.id (T.asAlgebraHom r) z ∈ S.toSubmodule := by
  induction r using MonoidAlgebra.induction_on with
  | of m =>
    have h1 : extTensor X T (1, m) = TensorProduct.map LinearMap.id (T m) :=
      TensorProduct.ext' fun v w => by simp
    rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, ← h1]
    exact S.apply_mem_toSubmodule _ hz
  | add f g hf hg =>
    rw [map_add (f := _), TensorProduct.map_add_right, LinearMap.add_apply]
    exact S.toSubmodule.add_mem hf hg
  | smul c f hf =>
    rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]
    exact S.toSubmodule.smul_mem c hf

theorem up_down (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1)
    (S : Subrepresentation (extTensor X T)) : up X T (down X T S) = S := by
  classical
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul u w => simpa using u.2 w
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  · intro y hy
    let b := Module.Basis.ofVectorSpace ℂ W
    let F := TensorProduct.equivFinsuppOfBasisRight (M := V) b
    have hy' : y = (F y).sum fun j a => a ⊗ₜ[ℂ] b j := by
      conv_lhs => rw [← F.symm_apply_apply y]
      exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F y)
    have hmem : ∀ j₀, F y j₀ ∈ (down X T S).toSubmodule := by
      intro j₀ w
      by_cases hj₀ : F y j₀ = 0
      · rw [hj₀, TensorProduct.zero_tmul]; exact zero_mem _
      let A : Module.End ℂ W := b.constr ℂ fun j => if j = j₀ then w else 0
      obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hirr hschur A ((F y).support.image b)
      have := map_mem X T S r hy
      rw [hy', map_finsuppSum] at this
      convert this using 1
      rw [Finsupp.sum, Finset.sum_eq_single j₀]
      · rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _
          (Finsupp.mem_support_iff.2 hj₀))]
        simp [A]
      · intro j hj hjj
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _ hj)]
        simp [A, hjj]
      · intro h
        exact absurd (Finsupp.mem_support_iff.2 hj₀) h
    rw [hy', Finsupp.sum]
    exact Submodule.sum_mem _ fun j _ => ⟨⟨F y j, hmem j⟩ ⊗ₜ b j, by simp⟩

theorem down_up [Nontrivial W] (U : Subrepresentation X) : down X T (up X T U) = U := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
      by_contra! h
      exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 h)
    let f : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V φ
    have key : ∀ x, f (U.toSubmodule.subtype.rTensor W x) ∈ U.toSubmodule := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | tmul u w' => simpa [f] using U.toSubmodule.smul_mem (φ w') u.2
      | add x y hx hy =>
        simp only [map_add]
        exact add_mem hx hy
    obtain ⟨x, hx⟩ := hv w
    have h2 := key x
    rw [hx] at h2
    simp only [f, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul] at h2
    exact (U.toSubmodule.smul_mem_iff hφ).1 h2
  · intro hv w
    exact ⟨⟨v, hv⟩ ⊗ₜ w, by simp⟩

def orderIso (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1) :
    Subrepresentation X ≃o Subrepresentation (extTensor X T) :=
  haveI := Model.nontrivial_of_isIrreducible hirr
  { toFun := up X T
    invFun := down X T
    left_inv := down_up X T
    right_inv := up_down X T hirr hschur
    map_rel_iff' := by
      intro U U'
      constructor
      · intro h v hv
        have h1 : v ∈ (down X T (up X T U')).toSubmodule := fun w => h ⟨⟨v, hv⟩ ⊗ₜ w, by simp⟩
        rwa [down_up X T U'] at h1
      · intro h
        rintro _ ⟨x, rfl⟩
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem (up X T U').toSubmodule
        | tmul u w => exact ⟨⟨u, h u.2⟩ ⊗ₜ w, by simp⟩
        | add x y hx hy => rw [map_add (f := _)]; exact (up X T U').toSubmodule.add_mem hx hy }

end GlobalTheory.ExtTensorSub
end
end

section

namespace GlobalTheory.CuspGL

theorem finsum_le_oneValue_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (A : Submodule K U) :
    ∑ᶠ B : {B : Submodule K U // B ≤ A}, oneValue (Nat.card K) (Module.finrank K B.1) =
      (Module.finrank K A : ℂ) := by
  classical
  haveI : Finite A := Module.finite_of_finite K
  haveI : Fintype (Submodule K A) := Fintype.ofFinite _
  rw [← sum_oneValue_finrank K A, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (Submodule.MapSubtype.orderIso A).toEquiv]
  refine finsum_congr fun W => ?_
  congr 1
  exact Submodule.finrank_map_subtype_eq A W

theorem eq_of_finsum_le_eq {α : Type} [PartialOrder α] [Finite α] (G H : α → ℂ)
    (h : ∀ A : α, ∑ᶠ B : {B : α // B ≤ A}, G B.1 = ∑ᶠ B : {B : α // B ≤ A}, H B.1) (A : α) :
    G A = H A := by
  classical
  induction A using WellFoundedLT.induction with
  | ind A ih =>
    haveI : Fintype {B : α // B ≤ A} := Fintype.ofFinite _
    have h1 := h A
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A})),
      ← Finset.add_sum_erase _ (fun B : {B : α // B ≤ A} => H B.1)
        (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A}))] at h1
    have h2 : ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), G B.1 =
        ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), H B.1 := by
      refine Finset.sum_congr rfl fun B hB => ih B.1 (lt_of_le_of_ne B.2 fun e => ?_)
      exact (Finset.mem_erase.1 hB).1 (Subtype.ext e)
    rw [h2] at h1
    exact add_right_cancel h1

theorem moebius_affine_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ) (hU : 0 < Module.finrank K U)
    (hG : ∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 =
      c₀ + c * (Module.finrank K A : ℂ)) :
    G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  classical
  haveI : Finite U := Module.finite_of_finite K
  have key := eq_of_finsum_le_eq G
    (fun B => (if B = ⊥ then c₀ else 0) + c * oneValue (Nat.card K) (Module.finrank K B)) (fun A => by
      haveI : Fintype {B : Submodule K U // B ≤ A} := Fintype.ofFinite _
      rw [hG A, ← finsum_le_oneValue_finrank K U A, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_eq_single (⟨⊥, bot_le⟩ : {B : Submodule K U // B ≤ A})]
      · simp
      · intro B _ hB
        exact if_neg fun e => hB (Subtype.ext e)
      · intro h
        exact absurd (Finset.mem_univ _) h) ⊤
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos hU
  rw [key, if_neg top_ne_bot, zero_add, finrank_top, oneValue, if_neg hU.ne']

end GlobalTheory.CuspGL
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section
namespace GlobalTheory.CechOne

theorem isLimit_widePullback_tensor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B B)
  have e0 : y1 A B 0 = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := rfl
  have e1 : y1 A B 1 = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) := rfl
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => H.lift (t.π 0) (t.π 1) ?_) ?_ ?_ ?_⟩
  · exact (t.condition 0).trans (t.condition 1).symm
  · intro t
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = _
    rw [← hy1 A B 0, ← Category.assoc, e0, H.lift_fst]
    exact t.condition 0
  · intro t i
    fin_cases i
    · exact H.lift_fst _ _ _
    · exact H.lift_snd _ _ _
  · intro t m _ hm
    apply H.hom_ext
    · rw [H.lift_fst, ← hm 0]; rfl
    · rw [H.lift_snd, ← hm 1]; rfl

end GlobalTheory.CechOne
end
end
