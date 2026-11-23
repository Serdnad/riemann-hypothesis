module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle097
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.Bundle001
import Formalism.PieriBlockIdeals.LemmaWFromLattice

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppAcyc

variable {R : Type} [CommRing R]

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

theorem map_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem res_zero' {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

theorem cpush_zero (K I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpush, cpost_mk]
  have : zcomp x (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := Cocycle.ext (by simp [zcomp])
  rw [this]
  exact CohomologyClass.mk_zero _ _ _

theorem delta_comp_ofHom {K I J : Cx R} {n : ℤ} (a : Cochain K I n) (f : I ⟶ J) :
    δ n (n + 1) (a.comp (Cochain.ofHom f) (add_zero n)) = (δ n (n + 1) a).comp (Cochain.ofHom f) (add_zero _) := by
  rw [δ_comp _ _ (add_zero n) (n + 1) 1 (n + 1) rfl rfl (zero_add 1)]
  simp

end GlobalTheory.EtC.SuppAcyc


open GlobalTheory.EtC.SuppAcyc in
theorem GlobalTheory.EtC.subsingleton_of_locExact_supp : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  intro R _ E C _ hC n
  let Z : Scheme.{0} → Prop := fun U => Nonempty (Sx E 0 U)
  have hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V := fun V U g ⟨x⟩ => ⟨Sx.res g x⟩
  obtain ⟨D, ι, hinj, hchar⟩ := SuppSub.exists_supp_sub R C Z hZ
  obtain ⟨ltop, lmono, -, -, ltrans, -, -⟩ := GlobalTheory.EtC.loc_calculus
  have hin : ∀ k U (a : Sec (C.X k) U), Z U → ∃ b, Sec.map (ι.f k) b = a := fun k U a hU =>
    (hchar k U a).2 (ltop _ _ fun V g => Or.inl (hZ V U g hU))

  have hD : D.Acyclic := by
    intro k
    rw [HomologicalComplex.exactAt_iff' D (k - 1) k (k + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
    intro U (b : Sec (D.X k) U) hb
    change Sec.map (D.d k (k + 1)) b = 0 at hb
    have hc : Sec.map (C.d k (k + 1)) (Sec.map (ι.f k) b) = 0 := by
      rw [← map_comp, ι.comm, map_comp, hb, map_zero']
    have hloc := (hchar k U (Sec.map (ι.f k) b)).1 ⟨b, rfl⟩
    refine ltrans _ _ (lmono _ _ _ hloc fun V g hg => ?_)
    rcases hg with hV | h0
    · have hc' : Sec.map (C.d k (k + 1)) (Sec.res g (Sec.map (ι.f k) b)) = 0 := by
        have := congrArg (Sec.res g) hc
        rwa [SuppSub.res_map, res_zero'] at this
      refine lmono _ _ _ (hC V hV k _ hc') fun W h => ?_
      rintro ⟨a, ha⟩
      obtain ⟨a', rfl⟩ := hin (k - 1) W a (hZ W V h hV)
      refine ⟨a', hinj k W ?_⟩
      change Sec.map (ι.f k) (Sec.map (D.d (k - 1) k) a') = Sec.map (ι.f k) (Sec.res (h ≫ g) b)
      rw [← map_comp, ← ι.comm, map_comp, ha, SuppSub.res_comp, SuppSub.res_map, SuppSub.res_map]
    · have h0' : Sec.res g b = 0 := hinj k V (by rw [← SuppSub.res_map, h0, map_zero'])
      refine ltop _ _ fun W h => ⟨0, ?_⟩
      change Sec.map (D.d (k - 1) k) 0 = Sec.res (h ≫ g) b
      rw [map_zero', SuppSub.res_comp, h0', res_zero']
  have hnull : Nonempty (Homotopy ι 0) := IsKInjective.nonempty_homotopy_zero ι hD
  have hpush : cpush ((chains R).obj E) ι n = cpush _ (0 : D ⟶ C) n :=
    ((GlobalTheory.EtC.ZcFun.main R).2.2.2.2 ι 0 hnull ((chains R).obj E) n).2
  have hbasic :
      ∀ {I : Cx R} {n : ℤ},
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
    intro I n
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
  obtain ⟨-, hnat, hdet, -, -⟩ := hbasic (I := C) (n := n)
  obtain ⟨-, -, -, -, hpost⟩ := hbasic (I := D) (n := n)
  obtain ⟨haddD1, -, hdetD, -, hpost1⟩ := hbasic (I := D) (n := n + 1)
  obtain ⟨haddC1, -, -, -, -⟩ := hbasic (I := C) (n := n + 1)
  have hzero : ∀ c : CohomologyClass ((chains R).obj E) C n, c = 0 := by
    intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective

    have hv : ∀ (p : ℕ) (U : Scheme.{0}), Sx E p U → Z U := fun p U x =>
      ⟨Sx.along x (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk p) 0)⟩
    let v : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (D.X s) U :=
      fun p s h U x => Classical.choose (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvspec : ∀ p s h U x, Sec.map (ι.f s) (v p s h U x) = ev α.1 p s h U x :=
      fun p s h U x => Classical.choose_spec (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (v p s h U x) = v p s h V (x.res g) := by
      intro p s h V U g x
      apply hinj s V
      rw [← SuppSub.res_map, hvspec, hvspec, (hnat α.1 p s h V U g x)]
    have hex : ∃ α : Cochain ((chains R).obj E) D n, ∀ p s h U x, ev α p s h U x = v p s h U x := by
      have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ D.X j,
          ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
            Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
              (freeGen R _ U x) = v p j (hp ▸ hij) U x := by
        intro i j hij
        by_cases hi : i ≤ 0
        · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
          obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (v k j hij) (hvnat k j hij)
          refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
          obtain rfl : k = p := by omega
          rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
          exact hφ U x
        · exact ⟨0, fun p hp => by omega⟩
      choose φ hφ using components
      refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
      have hEval := hφ _ _ h p rfl U x
      rw [eqToHom_refl, Category.id_comp] at hEval
      exact hEval
    obtain ⟨α', hα'⟩ := hex
    have hcomp : α'.comp (Cochain.ofHom ι) (add_zero n) = α.1 := by
      apply hdet
      intro p s h U x
      rw [hpost, hα', hvspec]
    have hcoc : δ n (n + 1) α' = 0 := by
      apply hdetD
      intro p s h U x
      apply hinj s U
      rw [← hpost1, ← delta_comp_ofHom, hcomp, (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2, (haddC1 0 0 p s h U x).2.2.1,
        (haddD1 0 0 p s h U x).2.2.1, map_zero']
    let β : Cocycle ((chains R).obj E) D n := Cocycle.mk α' (n + 1) rfl hcoc
    have hαβ : α = zcomp β (Cocycle.ofHom ι) (add_zero n) := Cocycle.ext hcomp.symm
    rw [hαβ, ← cpost_mk, ← cpush, hpush, cpush_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory.AnPer

open GlobalTheory.CatCoh

attribute [local instance] Charts.Obj.cAlg

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {D : Type} [CommRing D] [Algebra ℂ D]

def Charts.Obj.tenContract (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) : T.ten D →ₗ[ℂ] T.C :=
  (TensorProduct.lid ℂ T.C).toLinearMap ∘ₗ LinearMap.rTensor T.C ℓ

theorem Charts.Obj.tenContract_tmul (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) (d : D) (c : T.C) :
    T.tenContract ℓ (d ⊗ₜ c) = ℓ d • c := rfl

theorem Charts.Hom.tenContract_ten (ℓ : D →ₗ[ℂ] ℂ) {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.tenContract ℓ (Charts.Hom.ten D f x) = f.φ (T.tenContract ℓ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    rw [Charts.Hom.ten_tmul, Charts.Obj.tenContract_tmul, Charts.Obj.tenContract_tmul]
    exact (map_smul (Charts.Hom.φc f) (ℓ d) c).symm

theorem Charts.tenZ_eq_zero (K : Charts F) (hK : K.Rich) (hz : ∃ z, z ∈ F.V) {D : Type} [CommRing D] [Algebra ℂ D]
    (p : Λ →+ D) (h : H1.mk _ (K.tenZ p) = 0) : p = 0 := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨G, hG⟩ := H1.mk_eq_zero.1 h
  refine AddMonoidHom.ext fun l ↦ (Module.forall_dual_apply_eq_zero_iff ℂ (p l)).1 fun ℓ ↦ ?_
  let q : Λ →+ Hol F.V := ((algebraMap ℂ (Hol F.V)).toAddMonoidHom.comp ℓ.toAddMonoidHom).comp p
  have h0 : K.perZ 0 = 0 := Subtype.ext (by
    funext T T' f
    exact map_zero (algebraMap (Hol F.V) T'.C))
  have hq : K.perCl q = K.perCl 0 := by
    unfold Charts.perCl
    rw [h0, map_zero]
    refine H1.mk_eq_zero.2 ⟨fun T ↦ T.tenContract ℓ (G T), ?_⟩
    funext T T' f
    have e : G T' - Charts.Hom.ten D f (G T) = (p f.deg ⊗ₜ[ℂ] (1 : T'.C) : T'.ten D) :=
      congrFun (congrFun (congrFun hG T) T') f
    have e' := congrArg (T'.tenContract ℓ) e
    rw [map_sub, Charts.Hom.tenContract_ten, Charts.Obj.tenContract_tmul, ← Algebra.algebraMap_eq_smul_one] at e'
    exact e'
  have h1 : algebraMap ℂ (Hol F.V) (ℓ (p l)) = 0 := DFunLike.congr_fun (GlobalTheory.T.periodClass_injective_of_rich_charts K hK q 0 hq) l
  have h2 := congrArg (Hol.ev z hz) h1
  rwa [AlgHom.commutes, map_zero] at h2

end GlobalTheory.AnPer
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.DualCover

variable {A B : Type} [CommRing A] [CommRing B]

def dualMap (g : A →+* B) : DualNumber A →+* DualNumber B :=
  letI : Algebra A B := g.toAlgebra
  (DualNumber.lift ⟨(Algebra.ofId A (DualNumber B), DualNumber.eps), by simp, fun _ ↦ Commute.all _ _⟩).toRingHom

theorem dualMap_apply (g : A →+* B) (x : DualNumber A) :
    dualMap g x = TrivSqZeroExt.inl (g x.fst) + TrivSqZeroExt.inr (g x.snd) := by
  letI : Algebra A B := g.toAlgebra
  show (DualNumber.lift _ : DualNumber A →ₐ[A] DualNumber B) x = _
  rw [DualNumber.lift_apply_apply]
  ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]

@[simp] theorem dualMap_fst (g : A →+* B) (x : DualNumber A) : (dualMap g x).fst = g x.fst := by
  simp [dualMap_apply]

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover
variable {A B : Type} [CommRing A] [CommRing B]

theorem isPushout_dualMap (g : A →+* B) :
    IsPushout (CommRingCat.ofHom (algebraMap A (DualNumber A))) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (dualMap g)) (CommRingCat.ofHom (algebraMap B (DualNumber B))) := by
  letI : Algebra A B := g.toAlgebra
  have hc : ∀ a : A, dualMap g (algebraMap A (DualNumber A) a) = algebraMap A (DualNumber B) a := by
    intro a
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let ψ₀ : DualNumber A →ₐ[A] DualNumber B := AlgHom.mk (dualMap g) hc
  have hψ₀ : ∀ x, ψ₀ x = dualMap g x := fun _ ↦ rfl
  let j : B →ₐ[A] DualNumber B := TrivSqZeroExt.inlAlgHom A B B
  let G : TensorProduct A (DualNumber A) B →ₐ[A] DualNumber B :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber B → TensorProduct A (DualNumber A) B := fun x ↦
    (1 : DualNumber A) ⊗ₜ[A] x.fst + (DualNumber.eps : DualNumber A) ⊗ₜ[A] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, G (h x) = x := by
    intro x
    simp only [h, G, map_add (f := _), Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀, dualMap_apply]
  have hhg : ∀ x, h (G x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber A) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[A] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add (f := _), hadd, hx, hy]
  have hbij : Function.Bijective G := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  let eR : TensorProduct A (DualNumber A) B ≃+* DualNumber B := (AlgEquiv.ofBijective G hbij).toRingEquiv
  refine (CommRingCat.isPushout_tensorProduct A (DualNumber A) B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    eR.toCommRingCatIso (by simp) (by ext; simp [RingHom.algebraMap_toAlgebra]) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (x ⊗ₜ[A] 1) = dualMap g x
    simp [G, hψ₀]
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (1 ⊗ₜ[A] x) = algebraMap B (DualNumber B) x
    simp [G, j, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover

theorem epi_spMap_dualMap {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
    (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (x : Sp A ⟶ Y) (x' : Sp B ⟶ X) (hsq : IsPullback (spMap g) x' x π) : Epi (spMap (dualMap g)) := by
  have h2 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_dualMap g)
  have h3 : IsPullback (spMap (dualMap g)) (spMap (algebraMap B (DualNumber B)) ≫ x')
      (spMap (algebraMap A (DualNumber A)) ≫ x) π :=
    (IsPullback.paste_horiz h2.flip hsq.flip).flip
  have he := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG (spMap (algebraMap A (DualNumber A)) ≫ x)
  rw [← h3.isoPullback_hom_fst]
  exact epi_comp _ _

theorem exists_dualCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  intro X Y π Ga _ ρ hG R' _ x
  haveI : IsFinite π := hG.fin
  haveI : IsAffine (pullback x π) := isAffine_of_isAffineHom (pullback.fst x π)
  let X' := pullback x π
  let g₁ : R' →+* Γ(X', ⊤) := (Spec.preimage (X'.isoSpec.inv ≫ pullback.fst x π)).hom
  have hg₁ : spMap g₁ = X'.isoSpec.inv ≫ pullback.fst x π := Spec.map_preimage _
  let x'' : Sp Γ(X', ⊤) ⟶ X := X'.isoSpec.inv ≫ pullback.snd x π
  have hsq : IsPullback (spMap g₁) x'' x π := by
    rw [hg₁]
    exact IsPullback.of_iso_pullback ⟨by simp [x'', pullback.condition]⟩ X'.isoSpec.symm (by simp) (by simp [x''])
  refine ⟨Γ(X', ⊤), inferInstance, g₁, x'', dualMap g₁, hsq.w.symm, ?_, ?_, ?_, epi_spMap_dualMap hG g₁ x x'' hsq⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl']
  · refine RingHom.ext fun a ↦ ?_
    simp
  · intro r
    refine RingHom.ext fun a ↦ ?_
    ext <;> simp [epsScaleR, dualMap_apply] <;> ring

end GlobalTheory.DualCover
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem exists_square_matrix_of_submodule_between
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | (apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq ..)
end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

namespace GlobalTheory.Glue

variable {T : Scheme.{0}} {F G : T.Modules}

theorem le_iSup_affine (U : T.Opens) :
    U ≤ ⨆ k : {W : T.Opens // IsAffineOpen W ∧ W ≤ U}, k.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hxW⟩

variable (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V))
  (hj : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(F, V)), j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s))


include hj in
theorem agree {U W W' V : T.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWU : W ≤ U)
    (hW'U : W' ≤ U) (h₁ : V ≤ W) (h₂ : V ≤ W') (s : Γ(F, U)) :
    GlobalTheory.Twist.resM G h₁ (j W hW (GlobalTheory.Twist.resM F hWU s)) =
      GlobalTheory.Twist.resM G h₂ (j W' hW' (GlobalTheory.Twist.resM F hW'U s)) := by
  refine GlobalTheory.Twist.sec_ext_of_cover (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ V} => k.1)
    (fun k => k.2.2) (le_iSup_affine V) fun k => ?_
  rw [GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM, ← hj _ _ hW k.2.1, ← hj _ _ hW' k.2.1,
    GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM]

include hj in
theorem exists_glue (U : T.Opens) (s : Γ(F, U)) :
    ∃ t : Γ(G, U), ∀ (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U),
      GlobalTheory.Twist.resM G hWU t = j W hW (GlobalTheory.Twist.resM F hWU s) := by
  obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover
    (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (le_iSup_affine U)
    (fun k => j k.1 k.2.1 (GlobalTheory.Twist.resM F k.2.2 s))
    fun k l => agree j hj k.2.1 l.2.1 k.2.2 l.2.2 _ _ s
  exact ⟨t, fun W hW hWU => ht ⟨W, hW, hWU⟩⟩

def glue (U : T.Opens) (s : Γ(F, U)) : Γ(G, U) := Classical.choose (exists_glue j hj U s)


end GlobalTheory.Glue
end
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.exists_smaller_unitary_group_embedding : GlobalTheory.SatakeWeyl.EmbExists := by
  first | exact @GlobalTheory.SatakeWeyl.embExists | exact GlobalTheory.SatakeWeyl.embExists | (intros; apply GlobalTheory.SatakeWeyl.embExists <;> assumption)
end
