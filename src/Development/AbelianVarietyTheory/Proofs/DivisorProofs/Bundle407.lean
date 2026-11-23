module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SubSub

theorem hom_ext_val' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ v : Fin (a + 1), ((f.toOrderHom v : Fin (b + 1)) : ℕ) = (g.toOrderHom v : Fin (b + 1))) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun v => Fin.ext (h v)))

theorem along_along' {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  unfold Sx.along
  rw [op_comp, E.map_comp]
  rfl

theorem sub_eq_along {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    x.sub j l h = x.along (SimplexCategory.subinterval j l h) := rfl

theorem res_along {E : Spc} {U V : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (g : V ⟶ U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.res g).along a = (x.along a).res g := by
  unfold Sx.along Sx.res
  have h1 := congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) ((E.map a.op).naturality g.op)) x
  simpa only [ConcreteCategory.comp_apply] using h1

theorem map_along {E E' : Spc} {U : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (f : E ⟶ E')
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.map f).along a = (x.along a).map f := by
  unfold Sx.along Sx.map
  have := f.naturality a.op
  have h2 := congrArg (fun φ => φ.app (op U)) this
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) x).symm

theorem main : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  intro E U N x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    rw [sub_eq_along, sub_eq_along, sub_eq_along, along_along']
    congr 1
    exact hom_ext_val' _ _ fun v => by
      show ((v : ℕ) + j') + j = v + (j + j')
      omega
  · have : SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ :=
      hom_ext_val' _ _ fun v => by
        show (v : ℕ) + 0 = v
        omega
    rw [sub_eq_along, this]
    unfold Sx.along
    simp
  · intro j l h
    refine ⟨fun g => res_along x g _, fun f => map_along x f _, rfl⟩
  · intro p r a b
    exact along_along' x a b

end GlobalTheory.EtC.SubSub
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ShiftCocycle

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K L n →+ CohomologyClass K (L⟦a⟧) n' :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K (L⟦a⟧) n').comp (Cocycle.rightShiftAddEquiv n a n' h).toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + -a, by omega, a.negOnePow • β.rightShift a (m + -a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightShift β a (m + -a) n' (by omega) n h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

def runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K (L⟦a⟧) n' →+ CohomologyClass K L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K L n).comp (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm.toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + a, by omega, a.negOnePow • β.rightUnshift (m + a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightUnshift β (m + a) (by omega) n n' h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem runsh_rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    runsh K L a n n' h (rsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm_apply_apply x

theorem rsh_runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    rsh K L a n n' h (runsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).apply_symm_apply x

def sgn (d : ℤ) : ℤˣ := ((-d) * 0 + ((-d) * (-d - 1)) / 2).negOnePow

theorem zcomp_rightShift_homOf_leftShift {K L M : CochainComplex C ℤ} (d n : ℤ) (α : Cocycle K L (n - d)) (ψ : Cocycle L M d) :
    zcomp (sgn d • α.rightShift (-d) n (by omega)) (Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega))))
      (add_zero n) = zcomp α ψ (by omega) := by
  ext p q hpq
  have e1 : (↑(Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)))) : Cochain (L⟦-d⟧) M 0) =
      (ψ.leftShift (-d) 0 (by omega) : Cochain _ _ 0) := by
    rw [Cocycle.ofHom_coe, Cocycle.cochain_ofHom_homOf_eq_coe]
  simp only [zcomp, Cocycle.mk_coe, e1, Cocycle.coe_units_smul, Cochain.units_smul_comp,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q),
    Cochain.comp_v _ _ (show n - d + d = n by omega) p (p + (n - d)) q rfl (by omega),
    Cochain.units_smul_v, Cocycle.rightShift_coe, Cocycle.leftShift_coe,
    Cochain.rightShift_v _ (-d) n (show n + -d = n - d by omega) p q hpq (p + (n - d)) rfl,
    Cochain.leftShift_v _ (-d) 0 (show d + -d = 0 by omega) q q (add_zero q) (p + (n - d)) (by omega)]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Category.assoc, Iso.inv_hom_id_assoc]
  have hs : sgn d * (-d * 0 + -d * (-d - 1) / 2).negOnePow = 1 := Int.units_mul_self _
  rw [hs, one_smul]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem smul_mk {K L : CochainComplex C ℤ} {n : ℤ} (u : ℤˣ) (z : Cocycle K L n) :
    CohomologyClass.mk (u • z) = u • CohomologyClass.mk z := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, CohomologyClass.mk_neg]

theorem smul_smul_self {G : Type*} [AddCommGroup G] (u : ℤˣ) (x : G) : u • u • x = x := by
  rw [smul_smul, Int.units_mul_self, one_smul]

theorem map_units_smul' {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (u : ℤˣ) (x : G) :
    f (u • x) = u • f x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, map_neg]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC

open ShiftCocycle in
theorem cocycle_as_chainMap_of_shift : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d),
    ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧
      ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧
      ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n,
        ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  intro R _ L C d ψ
  refine ⟨L⟦-d⟧, Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)), ?_, ?_, ?_⟩
  · intro m hm
    exact L.isStrictlyGE_shift m (-d) (m + d) (by omega)
  · intro hI n
    exact Injective.of_iso (L.shiftFunctorObjXIso (-d) n (n + -d) rfl).symm (hI _)
  · intro K n
    refine ⟨{ toFun := fun x => sgn d • rsh K L (-d) (n - d) n (by omega) x
              invFun := fun y => sgn d • runsh K L (-d) (n - d) n (by omega) y
              left_inv := fun x => by
                simp only [map_units_smul', runsh_rsh, smul_smul_self]
              right_inv := fun y => by
                simp only [map_units_smul', rsh_runsh, smul_smul_self] }, ?_⟩
    intro a
    obtain ⟨α, rfl⟩ := a.mk_surjective
    show cpush K _ n (sgn d • CohomologyClass.mk (α.rightShift (-d) n (by omega))) = _
    rw [← smul_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (zcomp_rightShift_homOf_leftShift d n α ψ)

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeSeq

variable {R : Type} [CommRing R]

theorem cls_eq {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeSeq

theorem GlobalTheory.EtC.coneSeq_exact : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ), Function.Exact (cpull (mappingCone.inr f) I n) (cpull f I n) ∧ Function.Exact (cpull f I n) (cpre (mappingCone.fst f) I n (n + 1) (by omega)) ∧ Function.Exact (cpre (mappingCone.fst f) I n (n + 1) (by omega)) (cpull (mappingCone.inr f) I (n + 1)) := by
  intro R _ K L f I n
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hb
      obtain ⟨b, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ b _) = 0 at hb
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb
      obtain ⟨β, hβ⟩ := hb
      refine ⟨CohomologyClass.mk (mappingCone.descCocycle f (n.negOnePow • β) b (by omega) ?_), ?_⟩
      · rw [δ_units_smul, hβ]; simp [zcomp]
      · change CohomologyClass.mk (zcomp _ _ _) = _
        congr 1; ext1; simp [zcomp]
    · rintro ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ c _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • (mappingCone.inl f).comp (c : Cochain _ I n) (by omega), ?_⟩
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul]
  · intro y
    constructor
    · intro ha
      obtain ⟨a, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ a _) = 0 at ha
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at ha
      obtain ⟨γ, hγ⟩ := ha
      have hβ : δ n (n + 1) ((Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n)) = 0 := by
        rw [δ_ofHom_comp, hγ]; simp [zcomp]
      refine ⟨CohomologyClass.mk (Cocycle.mk (-(n.negOnePow • (Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n))) (n + 1) rfl (by rw [δ_neg, δ_units_smul, hβ]; simp)), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ (n - 1) (by omega) (-((mappingCone.inl f).comp γ (by omega))) ?_
      have key := δ_comp (mappingCone.inl f) γ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) rfl
      rw [hγ] at key
      simp [zcomp] at key
      simp [zcomp, key, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    · rintro ⟨z, rfl⟩
      obtain ⟨b, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ b _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      refine ⟨-(n.negOnePow • (mappingCone.snd f).comp (b : Cochain _ I n) (zero_add n)), ?_⟩
      rw [δ_neg, δ_units_smul, δ_comp _ _ _ 1 (n + 1) (n + 1) rfl (zero_add 1) rfl]
      simp [zcomp, smul_smul, Cochain.comp_assoc_of_second_is_zero_cochain]
  · intro y
    constructor
    · intro hc
      obtain ⟨c, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ c _) = 0 at hc
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at hc
      obtain ⟨β, hβ⟩ := hc
      set a : Cochain K I n := (mappingCone.inl f).comp (c : Cochain _ I (n + 1)) (by omega) +
        n.negOnePow • (Cochain.ofHom f).comp β (zero_add n) with ha_def
      have hsnd := δ_comp (mappingCone.snd f) β (zero_add n) 1 (n + 1) (n + 1) rfl (zero_add 1) rfl
      rw [hβ] at hsnd
      simp [zcomp] at hsnd
      have hdec : (c : Cochain _ I (n + 1)) = (mappingCone.fst f).1.comp a (by omega) +
          δ n (n + 1) ((mappingCone.snd f).comp β (zero_add n)) := by
        rw [mappingCone.ext_cochain_from_iff f n (n + 1) rfl]
        constructor
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
      have hcoc : δ n (n + 1) a = 0 := by
        have h1 := congrArg (δ (n + 1) (n + 2)) hdec
        rw [δ_add, δ_δ, add_zero, Cocycle.δ_eq_zero c (n + 2)] at h1
        rw [δ_comp _ _ _ 2 (n + 1) (n + 2) (by omega) rfl rfl] at h1
        simp at h1
        have h2 := congrArg (fun x => (mappingCone.inl f).comp x (show -1 + (n + 2) = n + 1 by omega)) h1
        simpa using h2.symm
      refine ⟨CohomologyClass.mk (Cocycle.mk a (n + 1) rfl hcoc), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ n rfl (-((mappingCone.snd f).comp β (zero_add n))) ?_
      simp [zcomp, hdec]
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ a _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      exact ⟨0, by simp [zcomp]⟩
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeTgt

variable {R : Type} [CommRing R]

theorem cls_eq' {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeTgt

private theorem coe_zcomp {R : Type} [CommRing R] {K L M : Cx R} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    ((zcomp a b h : Cocycle K M k) : Cochain K M k) = a.1.comp b.1 h := rfl

private theorem cohomologyClass_mk_eq_zero_of_eq_δ {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (x : Cocycle K L n)
    (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m) (h : (x : Cochain K L n) = δ m n β) :
    CohomologyClass.mk x = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
  exact ⟨β, h.symm⟩

theorem GlobalTheory.EtC.coneSeqTgt_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  intro R _ K I J f n
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := c.mk_surjective
    constructor
    · intro hy
      simp only [cpush, cpost_mk] at hy
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
      obtain ⟨γ, hγ⟩ := hy
      rw [coe_zcomp] at hγ
      have ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0 := by
        rw [δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl,
          Cocycle.δ_eq_zero, hγ]
        simp [Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega)
        (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_
      rw [coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]
      simp [Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨x, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_
      rw [δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1),
        mappingCone.δ_inl, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]
  · obtain ⟨z, rfl⟩ := c.mk_surjective
    constructor
    · intro hz
      rw [cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      rw [coe_zcomp] at hc₀
      have hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) +
          c₀.comp (Cochain.ofHom f) (add_zero n)) = 0 := by
        rw [δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀,
          Cocycle.δ_eq_zero]
        simp [Cochain.comp_assoc_of_third_is_zero_cochain]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega)
        (c₀.comp (mappingCone.inl f) rfl) ?_
      rw [coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl
        (neg_add_cancel 1), mappingCone.δ_inl, hc₀]
      rw [mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]
      constructor
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain,
          Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨y, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
  · obtain ⟨w, rfl⟩ := c.mk_surjective
    constructor
    · intro hw
      simp only [cpush, cpost_mk] at hw
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hw
      obtain ⟨b, hb⟩ := hw
      rw [coe_zcomp] at hb
      refine ⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl
        (by rw [δ_neg, hb]; simp)), ?_⟩
      rw [cpost_mk]
      congr 1
      apply Cocycle.ext
      rw [coe_zcomp]
      simp [mappingCone.liftCochain_fst]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨z, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_
      rw [δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC

theorem Pair.isTensor_of_compat_isIso (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K')
    (u : K ⟶ K') : IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  intro hu hc hτ
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), ν.lift U w x = Sec.map (u.f w) (τ.lift U w x) := by
    intro U w x
    have h : ν.lift U w = ((u.f w).hom.app (op U)).hom ∘ₗ τ.lift U w := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
      exact (hc U p.1.1 p.1.2 w p.2 a b).symm
    exact LinearMap.congr_fun h x
  have hinv : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K'.X w) U), Sec.map (u.f w) (Sec.map ((inv u).f w) y) = y := by
    intro w U y
    change Sec.map ((inv u).f w ≫ u.f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f]
    rfl
  have hinv' : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K.X w) U), Sec.map ((inv u).f w) (Sec.map (u.f w) y) = y := by
    intro w U y
    change Sec.map (u.f w ≫ (inv u).f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  have hnat : ∀ {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U),
      Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
    intro F G φ V U g z
    exact congrArg (fun f => f.hom z) (φ.hom.naturality g.op)
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := hτ.1 U w (Sec.map ((inv u).f w) y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    rw [hlift, hx, hnat, hinv]
  · apply hτ.2 U w x
    rw [hlift] at hx
    have h2 := congrArg (Sec.map ((inv u).f w)) hx
    rw [hinv'] at h2
    rw [h2]
    exact map_zero _

end GlobalTheory.EtC

end
end
