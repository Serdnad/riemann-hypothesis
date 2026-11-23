module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Mathlib.FieldTheory.Separable
public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.EtaleCohomology.EtaleSheaves.Bundle009
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Topology.Sheaves.Presheaf
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.SchemePresentationCover

private theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

private theorem pb {Y : Scheme.{0}} {A B C D : Y.Opens} (hC : C = A ⊓ B) (hCA : C ≤ A) (hCB : C ≤ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    IsPullback (Y.homOfLE hCA) (Y.homOfLE hCB) (Y.homOfLE hA) (Y.homOfLE hB) := by
  subst hC
  exact isPullback_opens_inf_le hA hB

private theorem cov (R : Type) [CommRing R] {Y : Scheme.{0}} {A B D : Y.Opens} (hD : D = A ⊔ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    Cover2 R (sch.map (Y.homOfLE hA)) (sch.map (Y.homOfLE hB)) := by
  subst hD
  apply UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective
  · infer_instance
  · infer_instance
  · intro y
    have hy : (y.1 : Y) ∈ A ⊔ B := y.2
    rcases (by simpa using hy : (y.1 : Y) ∈ A ∨ (y.1 : Y) ∈ B) with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩
    · exact Or.inr ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩

end UpperTheory.SchemePresentationCover

private theorem sq_lemma' {T S : Scheme.{0}} (f : T ⟶ S) {P Q : S.Opens} (h : P ≤ Q) (h' : f ⁻¹ᵁ P ≤ f ⁻¹ᵁ Q) :
    T.homOfLE h' ≫ f ∣_ Q = f ∣_ P ≫ S.homOfLE h := by
  rw [← cancel_mono Q.ι]
  simp [morphismRestrict_ι]

open UpperTheory.SchemePresentationCover in
theorem UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish :
    ∀ (R : Type) [CommRing R] (F : Shv R) {S : Scheme.{0}} (U V : S.Opens) (n : ℤ)
        (x : H R (sch.obj (U ⊔ V).toScheme) F (n + 1)),
        pull R (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) F (n + 1) x = 0 →
        pull R (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V))) F (n + 1) x = 0 →
        ∃ y : H R (sch.obj (U ⊓ V).toScheme) F n,
          ∀ {T : Scheme.{0}} (f : T ⟶ S) (a : H R (sch.obj (f ⁻¹ᵁ U).toScheme) F n)
            (b : H R (sch.obj (f ⁻¹ᵁ V).toScheme) F n),
            pull R (sch.map (f ∣_ (U ⊓ V))) F n y =
              pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_left))) F n a -
                pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_right))) F n b →
            pull R (sch.map (f ∣_ (U ⊔ V))) F (n + 1) x = 0 := by
  intro R _ F S U V n x hx1 hx2
  obtain ⟨d, hd, hnat⟩ := mayerVietoris R F
  haveI := sch_pres
  have hc := cov R (rfl : U ⊔ V = U ⊔ V) le_sup_left le_sup_right
  obtain ⟨c, hc'⟩ := ((hd _ _ hc n).2.2 x).1 ⟨hx1, hx2⟩
  have P := (pb (rfl : U ⊓ V = U ⊓ V) inf_le_left inf_le_right
    (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
  intro T f a b hab
  have hD : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := by
    ext; simp
  have hC : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := by
    ext; simp
  have hcT := cov R hD (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)
  have PT := (pb hC (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)).map sch
  have hu : sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ U) ≫ sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have hv : sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ V) ≫ sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have key := hnat (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))))
    (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    (sch.map (f ∣_ (U ⊔ V))) (sch.map (f ∣_ U)) (sch.map (f ∣_ V)) hu hv hcT hc n c
  rw [← hc', key, ((hd (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V)))) hcT n).2.1)]
  refine ⟨a, b, ?_⟩
  have inj : Function.Injective (pull R PT.isoPullback.hom F n) := by
    intro z w h
    have h2 := congrArg (pull R PT.isoPullback.inv F n) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h2
  apply inj
  rw [map_sub, ← pull_comp, ← pull_comp, ← pull_comp, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd, ← hab, ← pull_comp]
  refine congrArg (fun φ => pull R φ F n c) ?_
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.twist_generator_smul_eq_zero_imp :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (C : CommRingCat.{0}) [Nontrivial C] (ζ : Prim q C) (c : ULift.{1} (ZMod q)), c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj C) = 0 → c = 0 := by
  intro q _ i C _ ζ c h
  obtain ⟨f, hf⟩ := (GlobalTheory.T.tateTwistModule_free_and_generator_summand q i C).2 ζ
  have h' : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) :
      (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) = 0 := h
  have h2 := congrArg f h'
  rw [map_smul, hf, map_zero] at h2
  simpa using h2
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.GmInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def coord {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.GmInj

private theorem gmInj_coord_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.GmInj.coord (UpperTheory.GmInj.toLine a) = a := by
  unfold UpperTheory.GmInj.coord UpperTheory.GmInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.GmInj.evalT]

private theorem comp_gmInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.GmInj.toLine a = UpperTheory.GmInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.GmInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.GmInj.evalT]
  · simp [UpperTheory.GmInj.evalT]

theorem UpperTheory.eq_of_unitGlobalSection_eq :
    ∀ (U : Scheme.{0}) (u v : (Γ(U, ⊤))ˣ), unitSec u = unitSec v → u = v := by
  intro U u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op U)
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.GmInj.toLine (u : Γ(U, ⊤)) = UpperTheory.GmInj.toLine (v : Γ(U, ⊤)) := by
    refine (UpperTheory.GmInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.GmInj.toLine (u : Γ(U, ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.GmInj.toLine _ = f ≫ UpperTheory.GmInj.toLine _
    rw [comp_gmInj_toLine, comp_gmInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(U, ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.GmInj.coord key
  rw [gmInj_coord_toLine, gmInj_coord_toLine] at h4
  exact Units.ext h4
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace UpperTheory.DeRhamTrace

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

private noncomputable abbrev beta : L ⊗[K] Ω[K⁄k] →ₗ[L] L ⊗[K] DR k K :=
  LinearMap.baseChange L (ι1 (R := k) (B := K))

private theorem beta_anti (x y : L ⊗[K] Ω[K⁄k]) :
    beta k K L x * beta k K L y + beta k K L y * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), add_mul, mul_add]
    calc _ = (beta k K L a * beta k K L y + beta k K L y * beta k K L a) +
          (beta k K L b * beta k K L y + beta k K L y * beta k K L b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  | tmul a ω =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd =>
      rw [map_add (f := _), add_mul, mul_add]
      calc _ = (beta k K L (a ⊗ₜ ω) * beta k K L c + beta k K L c * beta k K L (a ⊗ₜ ω)) +
            (beta k K L (a ⊗ₜ ω) * beta k K L d + beta k K L d * beta k K L (a ⊗ₜ ω)) := by abel
        _ = 0 := by rw [hc, hd, add_zero]
    | tmul b ω' =>
      simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm b a, ← TensorProduct.tmul_add]
      have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω' +
          ι1 (R := k) (B := K) ω' * ι1 (R := k) (B := K) ω = 0 :=
        ExteriorAlgebra.ι_add_mul_swap ω ω'
      rw [this, TensorProduct.tmul_zero]

private theorem beta_sq (x : L ⊗[K] Ω[K⁄k]) : beta k K L x * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero]
    exact beta_anti k K L a b
  | tmul a ω =>
    simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω = 0 := ExteriorAlgebra.ι_sq_zero ω
    rw [this, TensorProduct.tmul_zero]

variable [Algebra.FormallyEtale K L]

private noncomputable def phi : Ω[L⁄k] →ₗ[L] L ⊗[K] DR k K :=
  beta k K L ∘ₗ (KaehlerDifferential.isBaseChange_of_formallyEtale k K L).equiv.symm.toLinearMap

private theorem phi_sq (x : Ω[L⁄k]) : phi k K L x * phi k K L x = 0 := beta_sq k K L _

private noncomputable def psi : DR k L →ₐ[L] L ⊗[K] DR k K :=
  ExteriorAlgebra.lift L ⟨phi k K L, phi_sq k K L⟩

private theorem psi_mapDR (ω : DR k K) : psi k K L (GlobalTheory.W1.mapDR k K L ω) = 1 ⊗ₜ ω := by
  have key : ((psi k K L).restrictScalars K).comp (GlobalTheory.W1.mapDR k K L) =
      Algebra.TensorProduct.includeRight := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun η ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply]
    simp only [GlobalTheory.W1.map1, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [psi, ExteriorAlgebra.lift_ι_apply]
    simp only [phi, LinearMap.comp_apply, LinearEquiv.coe_coe, IsBaseChange.equiv_symm_apply,
      beta, LinearMap.baseChange_tmul]
  exact congrArg (fun f ↦ f ω) key

end UpperTheory.DeRhamTrace

open UpperTheory.DeRhamTrace in
theorem UpperTheory.exists_deRhamTrace_of_separable :
    ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], ∃ T : DR k L →ₗ[k] DR k K, GlobalTheory.W1.IsTrDR k K L T := by
  intro k K L _ _ _ _ _ _ _ _ _
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let Tr : (L ⊗[K] DR k K) →ₗ[K] DR k K :=
    (TensorProduct.lid K (DR k K)).toLinearMap ∘ₗ LinearMap.rTensor (DR k K) (Algebra.trace K L)
  refine ⟨(Tr.restrictScalars k) ∘ₗ ((psi k K L).toLinearMap.restrictScalars k), ?_⟩
  intro b ω
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]
  rw [map_smul, psi_mapDR, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [Tr]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def invFn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Ob b A ⥤ Ob a A where
  obj y := ⟨(Equiv.ofBijective _ h1).symm y.pt⟩
  map {x y} f := ⟨(Equiv.ofBijective _ h2).symm f.1, h1.1 (by
    have e1 : φ.d.app A ((Equiv.ofBijective _ h1).symm x.pt) = x.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e2 : φ.d.app A ((Equiv.ofBijective _ h1).symm y.pt) = y.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm f.1) = f.1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.d.app A _ = φ.d.app A _
    rw [φ.eq, e1, e2, e3]
    exact f.2)⟩
  map_id x := Subtype.ext (h2.1 (by
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm 1) = 1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A 1
    rw [map_one (φ.g.app A).hom]
    exact e3))
  map_comp {x y z} f g := Subtype.ext (h2.1 (by
    have e : ∀ u : b.G.obj A, φ.g.app A ((Equiv.ofBijective _ h2).symm u) = u := fun u =>
      (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A (_ * _)
    rw [map_mul (φ.g.app A).hom, e, e, e]
    rfl))

private theorem fn_inv {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    φ.fn A ⋙ invFn φ A h1 h2 = 𝟭 _ := by
  have ho : ∀ x : Ob a A, (φ.fn A ⋙ invFn φ A h1 h2).obj x = (𝟭 _ : Ob a A ⥤ Ob a A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).symm_apply_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).symm_apply_apply f.1

private theorem inv_fn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    invFn φ A h1 h2 ⋙ φ.fn A = 𝟭 _ := by
  have ho : ∀ x : Ob b A, (invFn φ A h1 h2 ⋙ φ.fn A).obj x = (𝟭 _ : Ob b A ⥤ Ob b A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).apply_symm_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).apply_symm_apply f.1

private theorem comp_bij {C D : Type} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (G : D ⥤ C)
    (h : F ⋙ G = 𝟭 _) (h' : G ⋙ F = 𝟭 _) (k : ℕ) :
    Function.Bijective (fun s : ComposableArrows C k => s ⋙ F) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun t => t ⋙ G, fun s => ?_, fun t => ?_⟩
  · show (s ⋙ F) ⋙ G = s
    rw [Functor.assoc, h, Functor.comp_id]
  · show (t ⋙ G) ⋙ F = t
    rw [Functor.assoc, h', Functor.comp_id]

theorem UpperTheory.isIso_stackProductMap_of_bijective :
    ∀ (E : Spc) {a b : Act} (φ : Act.Hom a b), (∀ A, Function.Bijective (fun x : a.D.obj A => φ.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) → IsIso (Sp.map E φ) := by
  intro E a b φ h1 h2
  apply isIso_of_bijective_on_simplices
  intro k T
  have hb := (Function.bijective_id (α := Sx E k T)).prodMap
    (comp_bij (C := Ob a (Scheme.Γ.obj (op T))) (D := Ob b (Scheme.Γ.obj (op T)))
      (φ.fn _) (invFn φ _ (h1 _) (h2 _)) (fn_inv φ _ (h1 _) (h2 _)) (inv_fn φ _ (h1 _) (h2 _)) k)
  exact hb
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem leib {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (W : Scheme.{0})
    (s s' t w w' : ℤ) (h : s + t = w) (h' : s' + t = w') (hs : s' = s + 1)
    (a : Sec (I.X s) W) (b : Sec (J.X t) W) (hb : Sec.map (J.d t (t + 1)) b = 0) :
    Sec.map (K.d w w') (μ.mul W s t w h a b) = μ.mul W s' t w' h' (Sec.map (I.d s s') a) b := by
  subst hs
  obtain rfl : w' = w + 1 := by omega
  rw [μ.leibniz W s t w h a b, hb, map_zero, smul_zero, add_zero]

private theorem res_usmul {R : Type} [CommRing R] {F : Shv R} {V W : Scheme.{0}} (g : V ⟶ W)
    (u : ℤˣ) (x : Sec F W) : Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Sec.res, Units.smul_def, map_zsmul]

private theorem map_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {W : Scheme.{0}}
    (u : ℤˣ) (x : Sec F W) : Sec.map φ (u • x) = u • Sec.map φ x := by
  simp only [Sec.map, Units.smul_def, map_zsmul]

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {V W X : Scheme.{0}} (g : V ⟶ W)
    (f : W ⟶ X) (x : Sec F X) : Sec.res (g ≫ f) x = Sec.res g (Sec.res f x) := by
  simp only [Sec.res, op_comp, Functor.map_comp]
  rfl

private theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V W : Scheme.{0}}
    (g : V ⟶ W) (x : Sec F W) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op) x

private noncomputable def prodFam {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K)
    {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X)
    (hU : Sec.res U.ι β = 0) (p : ℕ) (s : ℤ) :
    Fam (Sub.bot E) p (I.X (s + 0)) →+
      Fam (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) p (K.X (s + m)) where
  toFun a := ⟨fun W z => (m * (p : ℕ)).negOnePow •
      μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β), fun V W g z => by
      beta_reduce
      rw [res_usmul, μ.nat, a.2.1 V W g z, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.1 V g, res_comp],
    fun W z h => by
      obtain ⟨w, hw⟩ := (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1.1 h
      beta_reduce
      rw [← hw, res_comp, hU]
      simp⟩
  map_zero' := by ext W z; simp
  map_add' a b := by ext W z; simp

theorem UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X), Sec.map (J.d m (m + 1)) β = 0 → Sec.res U.ι β = 0 →
    ∃ Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m), IsProd μ π β Φ ∧ Φ.Ok := by
  intro R _ I J K μ X U E π m β hd hU
  refine ⟨fun p s => prodFam μ U π m β hU p s, fun p s a W z => rfl, ?_, ?_⟩
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    change (m * (p : ℕ)).negOnePow • μ.mul W (s + 1 + 0) m (s + 1 + m) (by omega)
        (Sec.map (I.d (s + 0) (s + 1 + 0)) (a.1 W z)) (Sec.res (under π z) β) =
      Sec.map (K.d (s + m) (s + 1 + m)) ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β))
    rw [map_usmul, leib μ W (s + 0) (s + 1 + 0) m (s + m) (s + 1 + m) (by omega) (by omega) (by omega)
      _ _ (by rw [map_res, hd]; simp)]
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    have hf : ∀ i : Fin (p + 2), under π (z.face i) = under π z := fun i =>
      (UpperTheory.mem_pullbackImage_iff_factors_through_open U π (p + 1) W z).2.2 p (SimplexCategory.δ i)
    change ((m * ((p + 1 : ℕ) : ℤ))).negOnePow • μ.mul W (s + 0) m (s + m) (by omega)
        ((0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W (z.face i)) (Sec.res (under π z) β) =
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W (z.face i)) (Sec.res (under π (z.face i)) β))
    simp only [hf]
    have hsign : (m * ((p + 1 : ℕ) : ℤ)).negOnePow = m.negOnePow * (m * (p : ℕ)).negOnePow := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm, Int.negOnePow_add]
    generalize Sec.res (under π z) β = b
    let f := ((μ.mul W (s + 0) m (s + m) (by omega)).flip b).toAddMonoidHom
    change _ • f _ = _ • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (_ • f _)
    have e : ∀ (u : ℤˣ) (i : Fin (p + 2)) (y : Sec (K.X (s + m)) W),
        (-1 : ℤ) ^ (i : ℕ) • (u • y) = u • ((-1 : ℤ) ^ (i : ℕ) • y) := by
      intro u i y
      simp only [Units.smul_def]
      exact smul_comm _ _ _
    simp only [e]

    rw [← Finset.smul_sum, hsign, mul_smul, Int.negOnePow_zero, one_smul, map_sum]
    simp only [map_zsmul]
end
