module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle410
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  have ev_eq {F : Spc} {J : Cx R} (α : Cochain ((chains R).obj F) J n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx F p U) :
      ev α p s h U x = Sec.map ((chainsXIso R F p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α β p s h U x
    have hadd (a b : Cochain ((chains R).obj E) I n) :
        ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
      simp [ev, Cochain.add_v]
    let eval : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
      AddMonoidHom.mk' (fun a => ev a p s h U x) hadd
    exact ⟨hadd α β, map_sub eval α β, map_zero eval, fun c => map_zsmul eval c α⟩
  · intro α p s h V U g x
    rw [ev_eq, CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  · intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U x => H k s hs U x)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  · intro E' f α p s h U x
    rw [ev_eq, ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      ← Category.assoc, CupSpec.chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h)
      (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  · intro J m α p s h U x
    rw [ev_eq, ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      ← Category.assoc]
    rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KInjPull

variable {C : Type*} [Category C] [Abelian C]

theorem cls_eq_zero_of_acyclic {A I : CochainComplex C ℤ} (hA : A.Acyclic) [I.IsKInjective] {n : ℤ}
    (z : Cocycle A I n) : CohomologyClass.mk z = 0 := by
  let g : A ⟶ I⟦n⟧ := Cocycle.homOf (z.rightShift n 0 (zero_add n))
  let H := IsKInjective.homotopyZero g hA
  have h1 : δ (-1) 0 (Cochain.ofHomotopy H) = (z.1.rightShift n 0 (zero_add n)) := by
    rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]
    have := Cocycle.ofHom_homOf_eq_self (z.rightShift n 0 (zero_add n))
    exact congrArg Subtype.val this
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (Cochain.ofHomotopy H).rightUnshift (n - 1) (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega), h1]
  simp [smul_smul]

end GlobalTheory.EtC.KInjPull

theorem GlobalTheory.EtC.cpull_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  intro R _ K L f _ I _ n
  have hA := GlobalTheory.EtC.mappingCone_acyclic R f
  have hz : ∀ m (x : CohomologyClass (mappingCone f) I m), x = 0 := by
    intro m x
    obtain ⟨z, rfl⟩ := x.mk_surjective
    exact KInjPull.cls_eq_zero_of_acyclic hA z
  obtain ⟨e1, e2, -⟩ := GlobalTheory.EtC.coneSeq_exact R f I n
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := (e1 x).1 hx
    rw [hz n w, map_zero]
  · exact (e2 y).1 (hz (n + 1) _)
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧ (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧ resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G), resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧ resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  first | exact @GlobalTheory.EtC.ResBasic.res_basic | exact GlobalTheory.EtC.ResBasic.res_basic | (intros; apply GlobalTheory.EtC.ResBasic.res_basic <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  first | (exact @GlobalTheory.EtC.ConeConn.cone_connecting_class) | (exact GlobalTheory.EtC.ConeConn.cone_connecting_class) | (intros; apply GlobalTheory.EtC.ConeConn.cone_connecting_class  <;> assumption)
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_mulPow_fibreRank_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (G : _root_.GlobalTheory.PDivGroup p O) (k m : ℕ) :
    ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)), Function.Surjective r ∧
      RingHom.ker r = torsionIdeal (R := O) (A := G.A (k + m)) (p ^ k) ∧
      (∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a) ∧
      ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  obtain ⟨r, hr, hk⟩ := G.exists_res_le (m := k) (n := k + m) (by omega)
  have hle : RingHom.ker r ≤ RingHom.ker (mulBy (R := O) (A := G.A (k + m)) (p ^ m)) := by
    rw [hk]
    refine (kerIdeal_le_ker_iff _
      (mulBy (R := O) (A := G.A (k + m)) (p ^ m) : G.A (k + m) →ₐ[O] G.A (k + m))).2 fun c => ?_
    change mulBy (R := O) (A := G.A (k + m)) (p ^ m)
      (mulBy (R := O) (A := G.A (k + m)) (p ^ k) c) = _
    rw [mulBy_mulBy, ← pow_add, add_comm m k, mulBy_pow_self]
  let μ := liftSurj r hr (mulBy (R := O) (A := G.A (k + m)) (p ^ m)) hle
  have hμ : ∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a :=
    liftSurj_apply r hr _ hle
  refine ⟨r, μ, hr, hk, hμ, fun q => ?_⟩
  obtain ⟨f, hf, hfk⟩ := G.exists_res_le (m := m) (n := k + m) (by omega)
  have hker : kerIdeal μ = RingHom.ker (f : G.A (k + m) →ₐ[O] G.A m) := by
    rw [← kerIdeal_comp_of_surjective μ hr, show μ.comp r =
      mulBy (R := O) (A := G.A (k + m)) (p ^ m) from BialgHom.ext hμ]
    exact hfk.symm
  have h1 := fibreDim_eq_ker_mul_range μ q
  rw [hker, fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
    (f := (f : G.A (k + m) →ₐ[O] G.A m)) hf).toLinearEquiv, fibreDim_eq, fibreDim_eq,
    add_mul, pow_add, mul_comm (p ^ (k * G.height))] at h1
  rw [fibreDim_eq]
  have hp : 0 < p ^ (m * G.height) := pow_pos (Fact.out : p.Prime).pos _
  exact (Nat.eq_of_mul_eq_mul_left hp h1).symm

end GlobalTheory.PDivGroup
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  first | exact @GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | exact GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | (intros; apply GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents <;> assumption)
end

section

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory

open PDiv

theorem PDivGroup.natCast_smul_mem_augSq_sup_map : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ),
    ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))),
      (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔
        (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
          ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha0 : counit (R := R) a = 0 := ha
  have hb : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha0]
  have h1 : PDiv.mulBy (R := R) (A := G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hb
  have h2 : dUnit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) = 0 := by
    have e1 : dUnit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) =
        dUnit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a) - dUnit (R := R) ((p : R) • a) :=
      map_sub (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    have e2 : dUnit (R := R) ((p : R) • a) = (p : R) • dUnit (R := R) a :=
      map_smul (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    rw [e1, e2, ← cotMap_d, cotMap_mulBy, sub_self]
  have h3 : PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have h := (AugCot.d_eq_zero_iff _ _).1 h2
    have he : Bialgebra.counitAlgHom R (G.A (n + 1)) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha0, smul_zero, sub_zero]
    rwa [he, map_zero, sub_zero] at h
  have : (p : R) • a = PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h3)

end GlobalTheory
end
end

section

open scoped TensorProduct
open Coalgebra GlobalTheory.PDiv in

theorem _root_.GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha₀ : counit (R := R) a = 0 := ha
  have hres : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha₀]
  have hmap : mulBy R (G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hres
  have hdiff : mulBy R (G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have hd : dUnit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change GlobalTheory.AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul]
      change dUnit (R := R) (mulBy R (G.A (n + 1)) p a) - (p : R) • dUnit (R := R) a = 0
      rw [← cotMap_d, cotMap_mulBy, sub_self]
    have h := (GlobalTheory.AugCot.d_eq_zero_iff _ _).1 hd
    have hc : Bialgebra.counitAlgHom R (G.A (n + 1))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha₀, smul_zero, sub_zero]
    rwa [hc, map_zero, sub_zero] at h
  have hsmul : (p : R) • a = mulBy R (G.A (n + 1)) p a - (mulBy R (G.A (n + 1)) p a - (p : R) • a) :=
    (sub_sub_cancel _ _).symm
  rw [hsmul]
  exact sub_mem (Ideal.mem_sup_right hmap) (Ideal.mem_sup_left hdiff)
end

section

open scoped TensorProduct

namespace GlobalTheory

open PDiv

theorem omega_eq_zero_of_p_smul_eq_zero :
    ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R),
      (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) →
        ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  intro p R _ G hinj w hw
  refine Subtype.ext (funext fun n => ?_)
  have hp : (p : R) • w.1 (n + 1) = 0 := congrArg (fun v : G.omega => v.1 (n + 1)) hw
  apply hinj n
  change cotMap (G.mulP n) (w.1 n) = cotMap (G.mulP n) 0
  rw [map_zero, ← w.2 n, ← LinearMap.comp_apply, ← cotMap_comp, G.mulP_comp_res,
    cotMap_mulBy, hp]

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_comp_of_app_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G) (hfg : f ≫ g = (p : ℤ_[p]) • 𝟙 G)
    (a : G.A 1) (ha : g.app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp (f.app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp (f.app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp (f.app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp (f.app 2 : H.A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := H.A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : f.app 2 (mulBy R _ p z) = G.mulP 1 (f.app 1 (H.res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx (H.res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : g.app 2 b ∈ torsionIdeal (R := R) (A := H.A 2) p := by
    have : g.app 2 b ∈ torsionIdeal (R := R) (A := H.A 2) (p ^ 1) := by
      rw [← H.ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x (f.app 2 (g.app 2 b)) = 0 := hy hb
  have e2 : f.app 2 (g.app 2 b) = mulBy R _ p b := by
    have := congrArg (fun φ : G ⟶ G => φ.app 2 b) hfg
    simp only [comp_app, natCast_smul_id_app] at this
    exact this
  rw [e2] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup


open GlobalTheory.PDivGroup in
theorem GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G →
    g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  intro p _ K _ G H f g hfg _ a ha
  have hmulP : Function.Injective (G.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := K) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := G.dual_mulP_surjective 1 φ
    change ψ.ofConv (G.mulP 1 a) = ψ.ofConv (G.mulP 1 b)
    rw [e]
  have h1 := mulP_mem_kerIdeal_comp_of_app_eq_zero p K G H f g hfg a ha
  rw [kerIdeal_comp] at h1
  rw [← GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective K _ _ (G.mulP 1) hmulP (kerIdeal (f.app 1))]
  exact h1
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthCount

variable {C : Type} [Field C]

theorem prod_X_col {i : ℕ} (b : Fin i) (d : Fin i →₀ ℕ) :
    (d.prod fun s e => (X (⟨b, s⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ e)
      = monomial (Finsupp.mapDomain (Sigma.mk b) d) 1 := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add s n d hs hn ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp), X_pow_eq,
      monomial_mul_monomial, one_mul]

theorem hasSubst_col {i : ℕ} (b : Fin i) :
    HasSubst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)

theorem constantCoeff_col {i : ℕ} (b : Fin i) (g : MvPowerSeries (Fin i) C)
    (hg : constantCoeff g = 0) :
    constantCoeff (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)
      = 0 := by
  have hs := hasSubst_col (C := C) b
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst hs]
  convert finsum_zero with d
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · have hd : d = 0 := by
      have h' := h.symm
      rw [← Finsupp.mapDomain_zero (f := Sigma.mk b)] at h'
      exact Finsupp.mapDomain_injective (sigma_mk_injective (i := b)) h'
    subst hd
    simp [hg]
  · simp

theorem wt_col {i : ℕ} (v : AddValuation C (WithTop ℝ)) (ρ : Fin i → ℝ) (b : Fin i)
    (g : MvPowerSeries (Fin i) C) (hg : OrdGe v ρ g 0) (β : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    (((0 - β.sum (fun y e => ρ y.2 * (e : ℝ)) : ℝ)) : WithTop ℝ) ≤
      v (coeff β (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)) := by
  have hs := hasSubst_col (C := C) b
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs g β)]
  apply v.map_le_sum
  intro d _
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [mul_one]
    subst h
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_fintype _ _ (by simp)]
    exact hg d
  · simp

theorem depth_count : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  intro C _ _ v i d c ρ t B ht0 ht hP f hf
  have hw := GlobalTheory.WeightSubst.weight_subst_nonneg C v (Σ _ : Fin i, Fin i) (Σ _ : Fin i, Fin d)
    (fun y => ρ y.2) f
    (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i =>
      (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) hf
    (fun x => constantCoeff_col x.1 _ (ht0 x.2)) (fun x => wt_col v ρ x.1 _ (ht x.2))
  unfold derivAt0
  apply v.map_le_sum
  intro α hα
  have hrow := ((GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c).2.2.2 α hα).1
  rw [v.map_mul]
  have e : B = (B + c * ∑ a, ρ a) + (0 - α.sum (fun y e => ρ y.2 * (e : ℝ))) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hc : ∀ a : Fin i, (∑ b : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := fun a => by
      exact_mod_cast hrow a
    simp_rw [hc]
    rw [← Finset.sum_mul]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hP α hα) (hw α)

end GlobalTheory.DepthCount
end

section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

theorem _root_.GlobalTheory.T.integral_unipotentRadical_coefficient_coinvariant_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  first | exact @GlobalTheory.UnipCoefInt.integral_coef_eq_zero | exact GlobalTheory.UnipCoefInt.integral_coef_eq_zero | (intros; apply GlobalTheory.UnipCoefInt.integral_coef_eq_zero <;> assumption)
end
