module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle834
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kaehler_liftSemi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B') (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B'), (∀ b, f b = α b) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi h.m1) := by
  intro R R' _ _ _ B B' _ _ _ _ α h f hf hb
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  let g : B →ₗ[R] B' := (IsScalarTower.toAlgHom R B B').toLinearMap
  have e1 : ⇑(g.liftBaseChange R') = ⇑(liftSemi f) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [g, hf]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange R') (e1 ▸ hb)) fun n ↦ by simp [g]⟩
  have e2 : ∀ ω : Ω[B⁄R], h.m1 ω = KaehlerDifferential.map R R' B B' ω := by
    intro ω
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [SemiHom.m1_D, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul b x _ hx =>
      rw [SemiHom.oneFormMap_smul_semilinear, hx, LinearMap.map_smul_of_tower]
      exact algebraMap_smul B' b _
  have e3 : ⇑(liftSemi h.m1) = ⇑(KaehlerDifferential.tensorKaehlerEquivBase R R' B B') := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x ω => rw [liftSemi_tmul, KaehlerDifferential.tensorKaehlerEquivBase_tmul, e2]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e3]
  exact (KaehlerDifferential.tensorKaehlerEquivBase R R' B B').bijective

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct GlobalTheory.CechDR GlobalTheory.DeRham

namespace GlobalTheory.FormsBaseChange

theorem bijective_liftSemi_iff {R R' B B' M N : Type} [CommRing R] [CommRing R'] [CommRing B]
    [CommRing B'] [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R R' B'] [Algebra.IsPushout R R' B B']
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [AddCommGroup N] [Module B N] [Module B' N] [Module R' N] [IsScalarTower B B' N]
    [IsScalarTower R' B' N] (φ : M →ₗ[B] N) (g : M →ₛₗ[algebraMap R R'] N) (e : ∀ x, g x = φ x) :
    Function.Bijective (liftSemi g) ↔ IsBaseChange B' φ := by
  have hc : (liftSemi g : R' ⊗[R] M → N) =
      φ.liftBaseChange B' ∘ (Algebra.IsPushout.cancelBaseChange R R' B B' M).symm := by
    funext z
    induction z with
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  rw [hc, Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]
  constructor
  · intro H
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ H) fun x ↦ by simp
  · intro H
    have : (φ.liftBaseChange B' : B' ⊗[B] M → N) = H.equiv := by
      funext z
      induction z with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s m => simp
    rw [this]
    exact H.equiv.bijective

theorem bijective_liftSemi_mOm (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type)
    [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B')
    (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h0 : Function.Bijective (liftSemi f)) (h1 : Function.Bijective (liftSemi h.m1)) (j : ℕ) :
    Function.Bijective (liftSemi (h.mOm j)) := by
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h0) fun x ↦ by
      change liftSemi f (1 ⊗ₜ x) = α x
      rw [liftSemi_tmul, one_smul, hf]⟩
  let φ : Ω[B⁄R] →ₗ[B] Ω[B'⁄R'] :=
    { toFun := h.m1
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.oneFormMap_smul_semilinear, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  have hφ : IsBaseChange B' φ := (bijective_liftSemi_iff φ h.m1 fun _ ↦ rfl).1 h1
  refine (bijective_liftSemi_iff _ (h.mOm j) ?_).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ j)
  let ψ : Om R B j →ₗ[B] Om R' B' j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.mOm_smul, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  suffices H : ψ = _ from fun x ↦ LinearMap.congr_fun H x
  apply exteriorPower.linearMap_ext
  ext1 v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
  refine Subtype.ext ?_
  change h.mDR (exteriorPower.ιMulti B j v : DR R B) = _
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext k
  exact h.mDR_ι _

end GlobalTheory.FormsBaseChange
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.localization_pullback_injective : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  first | (exact @GlobalTheory.EtC.MVEtale.mv_etale_mid) | (exact GlobalTheory.EtC.MVEtale.mv_etale_mid) | (intros; apply GlobalTheory.EtC.MVEtale.mv_etale_mid <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistReductionResolutionMap_generator : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  first | (exact @GlobalTheory.EtC.RedExists.red_exists) | (exact GlobalTheory.EtC.RedExists.red_exists) | (intros; apply GlobalTheory.EtC.RedExists.red_exists  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isTateTwistResolution_tensor_flat : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ) := by
  first
  | exact @GlobalTheory.EtC.isTwRes_tensor
  | exact GlobalTheory.EtC.isTwRes_tensor
  | (intros; apply GlobalTheory.EtC.isTwRes_tensor <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  first | (exact @GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (exact GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (intros; apply GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res  <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.pDivGroupBaseChange_isConn_isEt_perfect : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k), (G.IsConn → (G.baseChange k').IsConn) ∧ (G.IsEt → (G.baseChange k').IsEt) := by
  first | exact @GlobalTheory.Dieu.baseChange_isConn_isEt | exact GlobalTheory.Dieu.baseChange_isConn_isEt | (intros; apply GlobalTheory.Dieu.baseChange_isConn_isEt <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem exists_perfect_idempotent (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) :
    ∃ e : G ⟶ G, e ≫ e = e ∧ (∀ (n : ℕ) (a : G.A n), IsNilpotent (a - e.app n a)) ∧
      ∀ (n : ℕ) (a : G.A n), IsNilpotent (e.app n a) → e.app n a = 0 := by
  choose π hπ using fun n => GlobalTheory.T.exists_perfectPart_algHom_finiteAlgebra p k (G.A n)
  have hk : (∀ a : k, IsNilpotent (a - AlgHom.id k k a)) ∧
      ∀ a : k, ∃ b : k, AlgHom.id k k a = AlgHom.id k k b ^ p :=
    ⟨fun a => by simp, fun a => by
      obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 a
      exact ⟨b, hb.symm⟩⟩
  have nat := fun n m => GlobalTheory.T.perfectProjection_natural_idempotent_reduced p k (G.A n) (G.A m) (π n) (π m) (hπ n) (hπ m)
  let b : ∀ n, G.A n →ₐc[k] G.A n := fun n => BialgHom.ofAlgHom (π n)
    (AlgHom.ext fun a => (GlobalTheory.T.perfectProjection_natural_idempotent_reduced p k (G.A n) k (π n) (AlgHom.id k k) (hπ n) hk).1
      (counitAlgHom k (G.A n)) a)
    (AlgHom.ext fun a => ((GlobalTheory.T.perfectProjection_natural_idempotent_reduced p k (G.A n) (G.A n ⊗[k] G.A n) (π n) _ (hπ n)
      (GlobalTheory.T.tensor_map_nilpotent_sub_and_pow_of_projection p k (G.A n) (π n) (hπ n))).1 (comulAlgHom k (G.A n)) a).symm)
  refine ⟨⟨b, fun n => ?_⟩, ?_, fun n a => (hπ n).1 a, fun n a => (nat n n).2.2 a⟩
  · refine BialgHom.ext fun a => ?_
    exact (nat (n + 1) n).1 (G.res n : G.A (n + 1) →ₐ[k] G.A n) a
  · exact Hom.ext (funext fun n => BialgHom.ext fun a => (nat n n).2.1 a)

end GlobalTheory.PDivGroup
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G), g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  first | exact @GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul | exact GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul | (intros; apply GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.cartierDual_convPow_primePow_apply_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n), (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  first | exact @GlobalTheory.PDivGroup.convPow_primePow_apply_pow | exact GlobalTheory.PDivGroup.convPow_primePow_apply_pow | (intros; apply GlobalTheory.PDivGroup.convPow_primePow_apply_pow <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  first | exact @GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap | exact GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap | (intros; apply GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n → Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  first | exact @GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | exact GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | (intros; apply GlobalTheory.Dieu.finrank_quot_kerIdeal_eq <;> assumption)
end
