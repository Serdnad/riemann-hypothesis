module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitCentreDerivative_commute_central_eigen : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  exact GlobalTheory.ResW.zc_comm_mem_eigen
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

theorem _root_.GlobalTheory.T.unipotent_radical_closed_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), H'.x ≠ 0 → IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  first | exact @GlobalTheory.UnipClosed.isClosed_unip | exact GlobalTheory.UnipClosed.isClosed_unip | (intros; apply GlobalTheory.UnipClosed.isClosed_unip <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FieldTw

theorem res_ofRings_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (j : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res j (ofRings.sec M U x) = ofRings.sec M V ((M.map (Scheme.Γ.map j.op)).hom x) := by
  have h := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
  exact h.symm

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ) 1) := by
  change (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) :
    (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B) = _
  rw [Finsupp.mapDomain_single]

theorem res_twGen {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (j : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res j (twGen i ζ) = twGen i (Prim.map (Scheme.Γ.map j.op).hom ζ) := by
  unfold twGen
  refine (res_ofRings_sec (twF q i) j _).trans ?_
  exact congrArg (ofRings.sec (twF q i) V) (twF_map_mk i (Scheme.Γ.map j.op) ζ)

theorem quot_pow {q : ℕ} (i : ℤ) {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)) • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩

theorem twGen_pow {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen i ξ = (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)) • twGen i ζ := by
  have := congrArg (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom) (quot_pow i ζ ξ a h)
  exact this.trans (LinearMap.map_smul _ _ _)

theorem res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

end GlobalTheory.EtC.FieldTw

namespace GlobalTheory.EtC.FieldTw

theorem cyclotomic_aeval_eq_zero {Ω : Type} [Field Ω] {q : ℕ} [NeZero q] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) :
    Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ.isRoot_cyclotomic (Nat.pos_of_ne_zero (NeZero.ne q))

theorem field_tw_coh_eq_galois : B7 := by
  intro q _ K Ω _ _ _ _ hq i M _ ζ hζ b hM n
  have hqΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap K Ω)
  let S : Scheme.{0} := Spec (CommRingCat.of Ω)
  let ι : Ω →+* Γ(S, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  let ζ0 : Prim q Ω := ⟨ζ, hqΩ, cyclotomic_aeval_eq_zero hζ⟩
  let ζ' : Prim q Γ(S, ⊤) := Prim.map ι ζ0
  let g : Sec (tw q (i : ℤ)) S := twGen (i : ℤ) ζ'
  obtain ⟨e, he1, -⟩ := GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant (ZMod q) (tw q (i : ℤ)) S g (GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζ')
  have hconst := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) Ω
  let φ : ZMod q →+ Sec (tw q (i : ℤ)) S :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • g
      map_zero' := by
        show (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • g = 0
        exact zero_smul _ _
      map_add' := fun a c => by
        show (ULift.up (a + c) : ULift.{1} (ZMod q)) • g = _
        rw [show (ULift.up (a + c) : ULift.{1} (ZMod q)) = ULift.up a + ULift.up c from rfl, add_smul] }
  have hφ : Function.Bijective φ := by
    have : (φ : ZMod q → Sec (tw q (i : ℤ)) S) = e S (𝟙 S) ∘ fun c => LocallyConstant.const S c := by
      funext c
      simp only [Function.comp_apply, he1, res_id']
      rfl
    rw [this]
    exact (e S (𝟙 S)).bijective.comp hconst
  let E1 : ZMod q ≃+ Sec (tw q (i : ℤ)) S := AddEquiv.ofBijective φ hφ
  let E0 : M ≃+ ZMod q := (b.equivFun.trans (LinearEquiv.funUnique Unit (ZMod q) (ZMod q))).toAddEquiv
  have hE0 : ∀ m, E0 m = b.repr m () := fun m => rfl
  refine GlobalTheory.T.nonempty_cohomology_addEquiv_galois_cohomology (ZMod q) (tw q (i : ℤ)) (GlobalTheory.T.tateTwist_finitary q i) K Ω M (E0.trans E1) ?_ n
  intro σ m

  have hσ : IsPrimitiveRoot (σ ζ) q := hζ.map_of_injective σ.injective
  obtain ⟨a, ha, hpow⟩ := hζ.eq_pow_of_pow_eq_one hσ.pow_eq_one
  have hcop : a.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 (hpow ▸ hσ)
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a hcop
  have hmρ := hM σ a hpow.symm

  have hm : m = b.repr m () • b () := by
    simpa using (b.sum_repr m).symm
  have hrep : b.repr (M.ρ σ m) () = b.repr m () * (a : ZMod q) ^ i := by
    have h1 : M.ρ σ m = (b.repr m () * (a : ZMod q) ^ i) • b () := by
      conv_lhs => rw [hm]
      rw [LinearMap.map_smul, hmρ, smul_smul]
    rw [h1, LinearEquiv.map_smul, b.repr_self]
    simp

  let ξ : Prim q Γ(S, ⊤) := Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))).op).hom ζ'
  have hξ : ξ.1 = ζ'.1 ^ (u : ZMod q).val := by
    rw [hu, ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    show (Scheme.Γ.map (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))).op).hom (ι ζ) = (ι ζ) ^ a
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : Ω →+* Ω))
    have := congrArg (fun f => f.hom ζ) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← map_pow, hpow]
    try exact this.symm
  have hg : Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) g =
      (ULift.up ((a : ZMod q) ^ i) : ULift.{1} (ZMod q)) • g := by
    rw [res_twGen, twGen_pow (i : ℤ) ζ' ξ u hξ]
    congr 2
  show (ULift.up (E0 (M.ρ σ m)) : ULift.{1} (ZMod q)) • g = Sec.res _ ((ULift.up (E0 m) : ULift.{1} (ZMod q)) • g)
  have hlin : ∀ c : ULift.{1} (ZMod q), Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (c • g) =
      c • Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) g := fun c => LinearMap.map_smul _ _ _
  rw [hE0, hE0, hrep, hlin, hg, smul_smul]
  rfl

end GlobalTheory.EtC.FieldTw
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtCover

theorem exists_faithfullyFlat_pow_eq :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ n : ℕ, 0 < n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D') (ψ : D →ₐ[R] D') (z : Pt A D'),
        (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x := by
  intro R _ A _ hA n hn D _ _ x
  obtain ⟨hf, hfl⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn
  have hs := AbelianLimit.surjective_pow A hA n hn
  let m : A.left ⟶ A.left := ((𝟙 A) ^ n : A ⟶ A).left
  have : IsFinite m := hf
  have : Flat m := hfl
  have : Surjective m := hs
  let x₀ : Spec (CommRingCat.of D) ⟶ A.left := x.left
  let Y := Limits.pullback x₀ m
  have : IsAffine Y := isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)
  let q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D) := Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m
  let φ : CommRingCat.of D ⟶ Γ(Y, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 (by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩)
  letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra
  let ψ : D →ₐ[R] Γ(Y, ⊤) := { φ.hom with commutes' := fun _ ↦ rfl }
  have hψ : (spOver ψ).left = q := hφ
  have hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]
  let z : Pt A Γ(Y, ⊤) := Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by
    rw [← Over.w (spOver ψ ≫ x), ← hc]
    simp only [Category.assoc]
    rw [Over.w ((𝟙 A) ^ n : A ⟶ A)])
  refine ⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩
  rw [← Category.comp_id z, ← MonObj.comp_pow]
  exact Over.OverMorphism.ext hc

end GlobalTheory.PtCover
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_zero_of_forall_apply_hodgePrimitive_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ x : G.Lie, (∀ c, x (ψ c) = 0) → x = 0 :=
  @GlobalTheory.PDivGroup.eq_zero_of_forall_apply_psi_eq_zero
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeToOmega_canonical_extension_base_change :
    ∀ (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
      (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
      (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ),
      IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A')
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega) (ψ' : PrimitiveSubmodule A' →ₗ[R'] G'.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
      (∀ c : PrimitiveSubmodule A', PtExt.IsCan t' c.1 (G'.rigOfOmega (ψ' c))) →
    ∀ (c : PrimitiveSubmodule A)
      (hc : (GlobalTheory.Published.AbelianDeRham.bcMor h).pull c.1 ∈ PrimitiveSubmodule A'),
      ψ' ⟨_, hc⟩ = (t'.semiHom t (grpMor_of_isGrpPullback h)).omega (ψ c) :=
  @GlobalTheory.PtExt.psi_baseChange
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.CocExt

theorem sm_comp {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (x : Pt X D)
    (h : Sm W x) : Sm W (D := E) (spOver ψ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun z _ ↦ ?_⟩
  have := hi (Set.mem_univ ((spOver ψ).left.base z))
  simpa [Over.comp_left, Scheme.Hom.comp_base, Scheme.Hom.comp_apply] using this

theorem cocycle_extends : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  intro R _ X K W hW u hu
  choose σ hσ using GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover R X K W hW u hu
  have uniq : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D) (d d' : D),
      (∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        Sm W (D := E) (spOver ψ ≫ y) → ψ d = ψ d') → d = d' := by
    intro D _ _ y d d' h
    obtain ⟨e, -, he⟩ := GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D y (fun E _ _ ψ ↦ ψ d) (fun _ _ _ _ _ _ _ _ _ ↦ rfl)
    exact (he d (fun _ _ _ _ _ ↦ rfl)).trans (he d' (fun E _ _ ψ hψ ↦ h E ψ hψ)).symm
  have hA : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D),
      ∃ d : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E),
        Sm W (D := E) (spOver ψ ≫ spOver φ ≫ x) →
          σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ = ψ d := by
    intro D _ _ D' _ _ φ x
    refine (GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D' (spOver φ ≫ x)
      (fun E _ _ ψ ↦ σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ) ?_).exists
    intro E _ _ E' _ _ ψ θ hψ
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    have h1 := hσ D x E E' (ψ.comp φ) θ (by rw [← e]; exact hψ)
    have h2 := hσ D' (spOver φ ≫ x) E E' ψ θ hψ
    rw [← e] at h1
    simp only [map_sub]
    rw [show (θ.comp ψ).comp φ = θ.comp (ψ.comp φ) from rfl]
    linear_combination h1 - h2
  choose u' hu' using hA
  refine ⟨u', ?_, ?_⟩
  · intro D _ _ D' _ _ D'' _ _ φ ψ x _
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    apply uniq D'' (spOver (ψ.comp φ) ≫ x)
    intro E _ _ ρ hρ
    have h2 : Sm W (D := E) (spOver (ρ.comp ψ) ≫ spOver φ ≫ x) := by
      rw [← spOver_comp, Category.assoc, e]; exact hρ
    have h3 : Sm W (D := E) (spOver ρ ≫ spOver ψ ≫ spOver φ ≫ x) := by rw [e]; exact hρ
    rw [map_add (f := _), ← AlgHom.comp_apply, ← hu' D D'' (ψ.comp φ) x E ρ hρ, ← hu' D D' φ x E (ρ.comp ψ) h2,
      ← hu' D' D'' ψ (spOver φ ≫ x) E ρ h3, e]
    rw [show (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) from rfl]
    ring
  · refine ⟨fun D _ _ x ↦ σ D x D (AlgHom.id R D), ?_⟩
    intro D _ _ D' _ _ φ x hx
    have hx' : Sm W (D := D) (spOver (AlgHom.id R D) ≫ x) := by
      simpa only [spOver_id, Category.id_comp] using hx
    have h1 := hσ D x D D' (AlgHom.id R D) φ hx'
    rw [spOver_id, Category.id_comp, AlgHom.comp_id] at h1
    have hφx : Sm W (D := D') (spOver (AlgHom.id R D') ≫ spOver φ ≫ x) := by
      simpa only [spOver_id, Category.id_comp] using sm_comp φ x hx
    have h2 := hu' D D' φ x D' (AlgHom.id R D') hφx
    rw [AlgHom.id_comp, AlgHom.id_apply] at h2
    show u D D' φ x + -u' D D' φ x = _
    linear_combination h2 - h1

end GlobalTheory.PtExt.CocExt
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalOpen

theorem exists_mul_isInteger (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ f : A, f ≠ 0 ∧ ∀ y : K, IsIntegral A y → ∃ a : A, algebraMap A K a = f • y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A K => (z : K))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun y hy => ?_⟩
  have key : ∀ z ∈ Submodule.span A (s : Set (integralClosure A K)),
      ∃ a : A, algebraMap A K a = (b : A) • (z : K) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hb _ (Finset.mem_image_of_mem _ hx)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [map_add (f := _), ha, hc, Subalgebra.coe_add, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_mul, ha, Subalgebra.coe_smul, smul_comm, ← Algebra.smul_def]
  exact key ⟨y, hy⟩ (hs ▸ Submodule.mem_top)

theorem exists_isIntegrallyClosed_away (A : Type*) [CommRing A] [IsDomain A]
    [Module.Finite A (integralClosure A (FractionRing A))] :
    ∃ f : A, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let K := FractionRing A
  obtain ⟨f, hf, h⟩ := exists_mul_isInteger A K
  refine ⟨f, hf, ?_⟩
  let B := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hg : ∀ y : Submonoid.powers f, IsUnit (algebraMap A K y) := fun y =>
    IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ hle
  letI : Algebra B K := (IsLocalization.lift (S := B) hg).toAlgebra
  have : IsScalarTower A B K := .of_algebraMap_eq fun a => (IsLocalization.lift_eq hg a).symm
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B K
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers f)
    (Rₘ := B) x hx
  obtain ⟨a, ha⟩ := h _ hm
  let t : Submonoid.powers f := ⟨f, Submonoid.mem_powers f⟩ * m
  refine ⟨IsLocalization.mk' B a t, ?_⟩
  have e := congrArg (algebraMap B K) (IsLocalization.mk'_spec B a t)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at e
  refine (hg t).mul_right_cancel ?_
  rw [e, mul_comm, ← Algebra.smul_def, Submonoid.smul_def, smul_smul]
  rfl

theorem exists_normal_opens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  intro k _ X p D h
  have := h.isIntegral
  have := h.finite
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, hft, -⟩ := RegGenSmooth.chart_props h i hi
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance hft
  have := finite_integralClosure_of_essFiniteType_int A
  obtain ⟨f, hf, hc⟩ := exists_isIntegrallyClosed_away A
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hB : GlobalTheory.IsNormalScheme (Sp B) := GlobalTheory.IsNormalScheme.spec (.of B)
  have : GlobalTheory.IsNormalScheme j.opensRange.toScheme := .of_isIso j.isoOpensRange.hom
  refine ⟨j.opensRange, ?_, GlobalTheory.IsNormalScheme.pred _⟩
  exact ⟨j (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), _, rfl⟩

end GlobalTheory.NormalOpen
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.dominant_projArith_surjective_complexPoints : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  first | exact @GlobalTheory.DomSurj.surjective_cxPts_map | exact GlobalTheory.DomSurj.surjective_cxPts_map | (intros; apply GlobalTheory.DomSurj.surjective_cxPts_map <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.semiPos_pullback_generically_birational : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  first | exact @GlobalTheory.SemiPullBir.semiPos_pull | exact GlobalTheory.SemiPullBir.semiPos_pull | (intros; apply GlobalTheory.SemiPullBir.semiPos_pull <;> assumption)
end
