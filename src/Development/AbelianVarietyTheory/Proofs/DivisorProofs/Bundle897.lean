module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem rAug_comp_toZ_eq_zero_of_kill (S : Type) [CommRing S] (F : Shv S) (R : Type) [CommRing R] (G : Shv R) (δ : SemiMap (res S F) (res R G))
    (hδ : ∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) :
    rAug (Int.castRingHom S) (resAug F) ≫ δ.toZ = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  apply Sheaf.hom_ext
  ext U b
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
  let a : Sec ((restr (Int.castRingHom S)).obj F) U.unop := Sec.map e.hom b
  have hb : b = Sec.map (sglι ((restr (Int.castRingHom S)).obj F)) a := by
    change b = Sec.map (e.hom ≫ e.inv) b
    rw [Iso.hom_inv_id]; rfl
  have h1 := rAug_f_zero (Int.castRingHom S) (resAug F) U.unop a
  change Sec.map (δ.toZ.f 0) (Sec.map ((rAug (Int.castRingHom S) (resAug F)).f 0) b) = 0
  rw [hb]
  have key : δ.app U.unop 0 (Sec.map ((resAug F).f 0) (Sec.map (sglι F) (show Sec F U.unop from a))) = 0 := by
    have h6 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) (show Sec F U.unop from a)) = Sec.map (resι S F) a := by
      rw [← h5]; rfl
    rw [h6]; exact hδ _ _
  exact (congrArg (δ.app U.unop 0) h1).trans key

theorem cpush_zero_hom {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [cpost_mk]
  have : zcomp z (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := by
    ext1; simp [zcomp]
  rw [this, CohomologyClass.mk_zero]

theorem cpush_toZ_eq_zero_of_kill (S : Type) [CommRing S] (F : Shv S) (R : Type) [CommRing R] (G : Shv R) (δ : SemiMap (res S F) (res R G))
    (hδ : ∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) (E : Spc) (n : ℤ)
    (y : CohomologyClass ((chains ℤ).obj E) ((rcx (Int.castRingHom S)).obj (res S F)) n) :
    cpush ((chains ℤ).obj E) δ.toZ n y = 0 := by
  obtain ⟨-, -, -, hqF, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  obtain ⟨-, hinjG, hgeG, hqG, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G
  let G' := (restr (Int.castRingHom R)).obj G
  obtain ⟨hKI', -, hGE', -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ G'
  haveI := hqF; haveI := hqG; haveI := hgeG; haveI := hKI'; haveI := hGE'
  haveI : QuasiIso (rAug (Int.castRingHom S) (resAug F)) := rAug_quasiIso _ _
  haveI : QuasiIso (rAug (Int.castRingHom R) (resAug G)) := rAug_quasiIso _ _
  obtain ⟨v, hv⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective ℤ G' ((rcx (Int.castRingHom R)).obj (res R G)) (res ℤ G')
    (rAug (Int.castRingHom R) (resAug G))).1 (resAug G')
  have hacyc : ∀ (t : ℤ) (P : PSh) (m : ℤ), 0 < m →
      Subsingleton (H ℤ (disc.obj P) (((rcx (Int.castRingHom R)).obj (res R G)).X t) m) :=
    fun t P m hm => GlobalTheory.T.restrictScalars_injective_sheaf_acyclic ℤ R (Int.castRingHom R) ((res R G).X t) P m hm
  have hbij := GlobalTheory.T.acyclic_resolution_computes_etale_cohomology ℤ G' ((rcx (Int.castRingHom R)).obj (res R G)) (rAug (Int.castRingHom R) (resAug G)) v hv
    hacyc E n
  have hzero := rAug_comp_toZ_eq_zero_of_kill S F R G δ hδ
  obtain ⟨hom⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective ℤ ((restr (Int.castRingHom S)).obj F) ((rcx (Int.castRingHom S)).obj (res S F)) (res ℤ G')
    (rAug (Int.castRingHom S) (resAug F))).2 (δ.toZ ≫ v) 0 (by rw [← Category.assoc, hzero]; simp)
  have h1 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial ℤ).2.2.2.2 _ _ ⟨hom⟩ ((chains ℤ).obj E) n).2
  have h2 : cpush ((chains ℤ).obj E) v n (cpush ((chains ℤ).obj E) δ.toZ n y) = cpush ((chains ℤ).obj E) v n 0 := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial ℤ).2.2.1, h1, cpush_zero_hom, map_zero]
  exact hbij.1 h2

theorem semiMap_op_eq_zero_of_kill : ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R)
    (δ : SemiMap (res S F) (res R G)), (∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) →
    ∀ (E : Spc) (n : ℤ) (x : H S E F n), δ.op.app E n x = 0 := by
  intro S R _ _ F G δ hδ E n x
  let ιA := idSemi (Int.castRingHom S) (res S F)
  let ιB := idSemi (Int.castRingHom R) (res R G)
  let ρ' : SemiMap (res S F) ((rcx (Int.castRingHom R)).obj (res R G)) :=
    { app := fun U s => δ.app U s
      nat := fun g s a => δ.nat g s a
      comm := fun U s t a => δ.comm U s t a }
  have hA := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S ℤ ιA ρ' δ.toZ (fun _ _ _ => rfl)).1 E n x
  have hB := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ ιB ιB (𝟙 _) (fun _ _ _ => rfl)).2
    (fun _ _ => ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩) E n
  have hcomp : ρ'.op.app E n x = ιB.op.app E n (δ.op.app E n x) := by
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R δ).1 E n α
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ ιB).1 E n β
    rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R δ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ ιB).2 E n β γ hγ,
      (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S ℤ ρ').2 E n α γ ?_]
    intro p s h U y
    rw [hγ p s h U y, hβ p s h U y]
    rfl
  apply hB.1
  rw [map_zero, ← hcomp, hA, cpush_toZ_eq_zero_of_kill S F R G δ hδ E n]

end GlobalTheory.EtC

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg

theorem ev_finset_sum {R : Type} [CommRing R] {S : Spc} {I : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (c : ι → Cochain ((chains R).obj S) I n) (p : ℕ) (t : ℤ) (h : -(p : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S p U) :
    ev (∑ j ∈ s, c j) p t h U x = ∑ j ∈ s, ev (c j) p t h U x := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ev_add, ih]

theorem col_identity (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (a : ℕ) (n m : ℤ) (hnm : n + -(a : ℤ) = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (c : ∀ j : Fin N, Cochain (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ)))) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ)))
    (ha : ∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X (-(a : ℤ))) ≫ (c j).v 0 r hr = (α j).v (-(a : ℤ)) r hr')
    (β : Cochain ((biChains (ZMod q) (twX E V)).X (-(a : ℤ))) (res _ (tw q i)) m)
    (hb : ∀ (k t : ℤ) (h : -(a : ℤ) + k = t) r hr hr', β.v k r hr =
      (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) k t h ≫ (phi q V ℓ i z n α).v t r hr')
    (γ : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a)))) (res _ (tw q i)) m)
    (hγ : ∀ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).IsAW (sub_add_cancel m _)
      ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _))
      ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) (γ j)) :
    (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m) = β := by
  ext k r hkr : 1
  by_cases hk : k ≤ 0
  · obtain ⟨b', rfl⟩ : ∃ b' : ℕ, k = -(b' : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [← cancel_epi (biChainsXIso (ZMod q) (twX E V) a b').inv]
    refine free_ext _ _ fun U y => ?_
    have e1 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫
        ((Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m)).v (-(b' : ℤ)) r hkr)
        (freeGen (ZMod q) _ U y) = ev (∑ j, γ j) b' r hkr U y := by
      rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% colCx_f]
      rfl
    have e2 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫ β.v (-(b' : ℤ)) r hkr) (freeGen (ZMod q) _ U y) =
        evT (phi q V ℓ i z n α) a b' r (by push_cast; omega) U y := by
      rw [hb (-(b' : ℤ)) (-((a + b' : ℕ) : ℤ)) (by push_cast; ring) r hkr (by push_cast; omega)]
      rfl
    rw [e1, e2, ev_finset_sum, GlobalTheory.T.projectiveBundleCochain_apply_bisimplex]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hA : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = t) (U' : Scheme.{0})
        (x : Sx ((twX E V).obj (op (SimplexCategory.mk a))) s U'), 0 < s →
        ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) s t h U' x = 0 := by
      intro s t h U' x hs
      erw [ev_pull]
      exact ev_prE_pos _ E a (c j) s t h U' _ hs
    rw [GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel m _) _ _ (γ j) (hγ j) hA b' r hkr U y]
    have hAv : ∀ (h0 : -((0 : ℕ) : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = m - 2 * ((j : ℕ) : ℤ)) (h00 : 0 + 0 ≤ b'),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) 0 (m - 2 * ((j : ℕ) : ℤ)) h0 U
          (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00) =
        Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 (m - 2 * ((j : ℕ) : ℤ)) (by simpa using h0))
          (freeGen (ZMod q) _ U (baseS V y)) := fun h0 h00 =>
      (ev_pull (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N))
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) 0 _ h0 U
        (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00)).trans
        (ev_prE_zero _ E a (c j) _ h0 U _)
    have hZv : ∀ (h2 : -(b' : ℤ) + 2 * ((j : ℕ) : ℤ) = -(b' : ℤ) + 2 * ((j : ℕ) : ℤ)),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) b'
          (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) h2 U y = EtC.ev (z j) b' _ rfl U (vertS V ℓ y) := fun h2 =>
      ev_pull (ℓ.app (op (SimplexCategory.mk a))) (z j) b' _ h2 U y
    refine (congrArg₂ (fun u v => (twPairI q i ((j : ℕ) : ℤ)).mul U (m - 2 * ((j : ℕ) : ℤ))
      (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r (by omega) u v) (hAv _ _) (hZv _)).trans ?_
    have key : ∀ (s : ℤ) (hs : -(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ)) = s) (h0 : 0 + (m - 2 * ((j : ℕ) : ℤ)) = s)
        (h1 : s + (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) = r),
        (twPairI q i ((j : ℕ) : ℤ)).mul U s (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r h1
          (Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 s h0) (freeGen (ZMod q) _ U (baseS V y)))
          (ev (z j) b' _ rfl U (vertS V ℓ y)) =
        (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r
          (by omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b' _ rfl U (vertS V ℓ y)) := by
      intro s hs
      subst hs
      intro h0 h1
      rw [ha j _ h0 (by omega)]
      rfl
    exact key _ (by omega) _ _
  · exact (biChains_isZero (twX E V) (-(a : ℤ)) k (Or.inr (by omega))).eq_of_src _ _

theorem graded_bijective : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  intro q _ E N V hE B ℓ i z hz hD p hp
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a : ℤ) := ⟨(-p).toNat, by omega⟩
  set P : PSh := E.obj (op (SimplexCategory.mk a)) with hPdef
  have hP : Inv q (disc.obj P) := fun U ⟨x⟩ =>
    hE U ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk a) 0).op).app (op U) x⟩
  have hpbf := hD P (trivV N (disc.obj P)) hP
  have hpi : ∀ m, Function.Bijective (fun (x : ∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ))))
      (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (j : Fin N) => cpull (prE _ E a) _ _ (x j)) := by
    intro m
    have hb := fun (j : Fin N) => LevelCmp.cpull_bij_of_heq (prEquiv (ZMod q) E a) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ))
    refine ⟨fun x y hxy => funext fun j => (hb j).1 (congrFun hxy j), fun y => ?_⟩
    exact ⟨fun j => ((hb j).2 (y j)).choose, funext fun j => ((hb j).2 (y j)).choose_spec⟩
  refine ⟨fun m x => cpull (colCx _ (twX E V) a).hom _ m (pull _ (colIso P (trivV N (disc.obj P))).hom _ m
    (pbfMap q (trivV N (disc.obj P)) m i (fun j => cpull (prE _ E a) _ _ (x j)))), fun m => ?_, ?_⟩
  · exact (LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso (colCx _ (twX E V) a)) _ m).comp
      ((LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso ((chains (ZMod q)).mapIso (colIso P (trivV N (disc.obj P))))) _ m).comp
        ((hpbf m i).comp (hpi m)))
  · intro n m hnm α hα ac b ha hb
    let A : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ptimes.fst P (Fib N))))
        (zcomp (Cocycle.ofHom (prE _ E a)) (ac j) (zero_add _)) (zero_add _)
    let Z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)
    choose γ hγ using fun j : Fin N => Pair.aw_exists (twPairI q i ((j : ℕ) : ℤ)) ((twX E V).obj (op (SimplexCategory.mk a)))
      (sub_add_cancel m (2 * ((j : ℕ) : ℤ))) (A j) (Z j)
    have hterm : ∀ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _
        (cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) =
        CohomologyClass.mk (γ j) := by
      intro j
      rw [← hz a j]
      exact GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney q i j m (A j) (Z j) (γ j) (hγ j)
    change cpull _ _ m (pull _ _ _ m (pbfMap q (trivV N (disc.obj P)) m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))) = _
    have h1 := pull_colIso_pbfMap q P (trivV N (disc.obj P)) hP m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j)))
    erw [h1]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    erw [mk_sum_cocycle]
    change CohomologyClass.mk (zcomp _ _ _) = _
    congr 1
    apply Cocycle.ext
    change (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j).1 (zero_add m) = b.1
    have hsum : ∀ s : Finset (Fin N), (∑ j ∈ s, γ j).1 = ∑ j ∈ s, (γ j).1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | @insert j s hj ih => simp only [Finset.sum_insert hj, Cocycle.coe_add, ih]
    rw [hsum]
    exact col_identity q V ℓ i (fun j => (z j).1) a n m hnm α (fun j => (ac j).1) ha b.1 hb (fun j => (γ j).1) hγ

end GlobalTheory.PBFg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

theorem rosati_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → ∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ G hA' hψ hG hact m P' hP' hIso r₁ r₂ c
  haveI := act'.hom c
  haveI := act'.hom (D.star c).unop
  have e₁ : sq2 ψ ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left ≫ sq2 ψ := by
    simp only [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have e₂ : sq2 ψ ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left ≫ sq2 ψ := by
    simp only [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have u₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      𝟙 _ ≫ (lift (1 : A' ⟶ A') (𝟙 A')).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have u₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      (act'.act c).left ≫ (lift (𝟙 A') (1 : A' ⟶ A')).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      (act'.act (D.star c).unop).left ≫ (lift (1 : A' ⟶ A') (𝟙 A')).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      𝟙 _ ≫ (lift (𝟙 A') (1 : A' ⟶ A')).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp

  have hL := o.isLB
  have hX₁ : ((P'.pull (lift (fst A' A' ≫ act'.act c) (snd A' A')).left).pull (sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hP' _) _
  have hX₂ : ((P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left).pull (sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hP' _) _
  have hL₁ : (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have hL₂ : (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have I₁ : LBIso (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m)
      ((P'.pull (lift (fst A' A' ≫ act'.act c) (snd A' A')).left).pull (sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin m) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => sq2 ψ) (fun _ => sq2 ψ) (fun _ => 1) _ (fun _ => e₁)) hIso
  have I₂ : LBIso (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m)
      ((P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left).pull (sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin m) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => sq2 ψ) (fun _ => sq2 ψ) (fun _ => 1) _ (fun _ => e₂)) hIso
  have Rm : LBIso (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m)
      (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (o.rosati c) _ _
  have hsq := LBIso.trans hX₁ hL₁ hX₂ I₁.symm (LBIso.trans hL₁ hL₂ hX₂ Rm I₂)
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  exact GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A A' G ψ o.ab hA' hψ hG _ _ (pull_isLB hP' _) (pull_isLB hP' _)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₁)) t₁ ht₁)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₂)) t₂ ht₂)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₁)) t₁ ht₁)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₂)) t₂ ht₂)
    hsq

end GlobalTheory.UPel.HT.Hecke
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

theorem nablaBdd_rename_eq_rowAct {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    rename (Prod.map σ id) f = rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0) f := by
  classical
  have : (rename (Prod.map σ id) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] _) =
      rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [rowAct, rename_X]
  rw [this]

theorem nablaBdd_rowDeg_bounds {M : ℕ} (ν : Fin (M + 1) → ℕ) (f : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ)
    (hf : f ∈ dualWeyl ℚ (M + 1) (M + 1) ν) (m : Fin (M + 1) × Fin (M + 1) →₀ ℕ) (hm : m ∈ f.support)
    (c : Fin (M + 1)) : rowDeg m c ≤ ν 0 ∧ ν (Fin.last M) ≤ rowDeg m c := by
  classical
  have key : ∀ σ : Equiv.Perm (Fin (M + 1)), rename (Prod.map σ id) f ∈ dualWeyl ℚ (M + 1) (M + 1) ν ∧
      Finsupp.mapDomain (Prod.map σ id) m ∈ (rename (Prod.map σ id) f).support ∧
      rowDeg (Finsupp.mapDomain (Prod.map σ id) m) (σ c) = rowDeg m c := by
    intro σ
    have hinj : Function.Injective (Prod.map σ (id : Fin (M + 1) → Fin (M + 1))) :=
      σ.injective.prodMap Function.injective_id
    refine ⟨?_, ?_, ?_⟩
    · rw [nablaBdd_rename_eq_rowAct]
      exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ _ _ ν _ f hf
    · rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
      exact mem_support_iff.mp hm
    · unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Finsupp.mapDomain_apply_of_injective hinj m (c, s)
  constructor
  · obtain ⟨h1, h2, h3⟩ := key (Equiv.swap c 0)
    have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2).1 1
    have e : (Finset.univ.filter fun a : Fin (M + 1) => a.val < 1) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
      omega
    rw [e, Finset.sum_singleton, Finset.sum_singleton] at dom
    rw [Equiv.swap_apply_left] at h3
    omega
  · obtain ⟨h1, h2, h3⟩ := key (Equiv.swap c (Fin.last M))
    have dom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2
    have e2 : ∀ g : Fin (M + 1) → ℕ, ∑ a, g a = (∑ a : Fin (M + 1) with a.val < M, g a) + g (Fin.last M) := by
      intro g
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin (M + 1) => a.val < M) g]
      congr 1
      have : (Finset.univ.filter fun a : Fin (M + 1) => ¬ a.val < M) = {Fin.last M} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
        omega
      rw [this, Finset.sum_singleton]
    have d1 := dom.1 M
    have d2 := dom.2
    rw [e2, e2] at d2
    rw [Equiv.swap_apply_left] at h3
    omega

theorem nablaBdd : NablaBdd := by
  intro N ν _ K hK a ha b hb n x hx hn
  by_contra hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := support_nonempty.mpr hx0'
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hea : ∀ (c : ℕ) (hc : c < M + 1) (y : dualWeyl ℚ (M + 1) (M + 1) ν),
      ((eV (M + 1) ν c c y : dualWeyl ℚ (M + 1) (M + 1) ν) : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) =
        Formalism.CohomologicalDescent.LR.der (M + 1) (M + 1) ⟨c, hc⟩ ⟨c, hc⟩ (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) := by
    intro c hc y
    unfold eV
    rw [dite_eq_left ⟨hc, hc⟩]
    rfl
  have hc := congrArg (fun y : dualWeyl ℚ (M + 1) (M + 1) ν => AddMonoidAlgebra.coeff (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) m) hx
  simp only [Submodule.coe_sub, Submodule.coe_smul, hea a ha, hea b hb, MvPolynomial.coeff_sub,
    Formalism.CohomologicalDescent.LR.coeff_der_diag, MvPolynomial.coeff_smul, smul_eq_mul, Formalism.GradedWeylDivisibility.ldrow_weight_rowW] at hc
  have hne : AddMonoidAlgebra.coeff (x : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) m ≠ 0 := mem_support_iff.mp hm
  have key : (((rowDeg m ⟨a, ha⟩ : ℕ) : ℚ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℚ)) = (n : ℚ) := by
    apply mul_right_cancel₀ hne
    rw [sub_mul]
    exact hc
  have key' : ((rowDeg m ⟨a, ha⟩ : ℕ) : ℤ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℤ) = n := by exact_mod_cast key
  have B1 := (nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨a, ha⟩).1
  have B2 := (nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨b, hb⟩).2
  have B3 := hK 0 (Fin.last M)
  omega

end GlobalTheory.LeviCut
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  first | exact @GlobalTheory.WachExp.exists_locExp_expAt | exact GlobalTheory.WachExp.exists_locExp_expAt | (intros; apply GlobalTheory.WachExp.exists_locExp_expAt <;> assumption)
end
