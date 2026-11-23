module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic

def liftSec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec C U :=
  Function.surjInv (hb U (hE U ⟨x.face 0⟩)).2 (unitSec (lineUnit L x))

theorem liftSec_spec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec.map qb (liftSec qb L hE hb U x) = unitSec (lineUnit L x) :=
  Function.surjInv_eq _ _

theorem liftSec_res {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    Sec.res g (liftSec qb L hE hb U x) = liftSec qb L hE hb V (x.res g) := by
  apply (hb V (hE V ⟨(x.res g).face 0⟩)).1
  rw [← CupSpec.map_res, liftSec_spec, liftSec_spec, PicSpec.unitSec_res, PicSpec.lineUnit_res]

theorem liftSec_face {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 2 U) :
    liftSec qb L hE hb U (x.face 1) = liftSec qb L hE hb U (x.face 0) + liftSec qb L hE hb U (x.face 2) := by
  apply (hb U (hE U ⟨(x.face 0).face 0⟩)).1
  rw [PicSpec.sec_map_add, liftSec_spec, liftSec_spec, liftSec_spec, PicSpec.lineUnit_face, PicSpec.unitSec_mul]

def liftFam {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((sgl C).X s) U
  | 1, s, h, U, x => Sec.map ((sgl C).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (sglι C) (liftSec qb L hE hb U x))
  | _, _, _, _, _ => 0

theorem liftFam_nat {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (liftFam qb L hE hb p s h U x) = liftFam qb L hE hb p s h V (x.res g) := by
  match p with
  | 0 => exact map_zero _
  | 1 =>
    simp only [liftFam]
    rw [CupSpec.map_res, CupSpec.map_res, liftSec_res]
  | p + 2 => exact map_zero _

end GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic

theorem liftFam_one {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) :
    liftFam qb L hE hb 1 0 h U x = Sec.map (sglι C) (liftSec qb L hE hb U x) := by
  simp [liftFam, Sec.map]

theorem liftFam_cocycle {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (α : Cochain ((chains ℤ).obj E) (sgl C) 1)
    (hα : ∀ p s h U x, ev α p s h U x = liftFam qb L hE hb p s h U x) : δ 1 2 α = 0 := by
  apply CupSpec.ev_ext
  intro p t ht U x
  rw [CupSpec.ev_zero]
  by_cases h0 : t = 0
  · subst h0
    obtain rfl : p = 2 := by omega
    rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
    simp only [hα]
    rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl, PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
    simp only [liftFam_one]
    rw [liftSec_face, PicSpec.sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _

theorem lift_cocycle : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  refine ⟨Cocycle.mk α 2 (by norm_num) (liftFam_cocycle qb L hE hb α hα), fun U x => ⟨liftSec qb L hE hb U x,
    liftSec_spec qb L hE hb U x, ?_⟩⟩
  refine (hα 1 0 _ U x).trans ?_
  exact liftFam_one qb L hE hb _ U x

end GlobalTheory.EtC.KumPic
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic.PostVal

theorem ev_comp_ofHom {E : Spc} {I J : Cx ℤ} {n : ℤ} (α : Cochain ((chains ℤ).obj E) I n) (m : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem sglι_resAug (C : Shv ℤ) : sglι C ≫ (resAug C).f 0 = resι ℤ C := rfl

theorem resι_resMap {C G : Shv ℤ} (φ : C ⟶ G) : resι ℤ C ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  unfold resι resMap res
  rw [InjectiveResolution.ι'_f_zero, InjectiveResolution.ι'_f_zero,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
  simp [InjectiveResolution.cochainComplexXIso]

theorem post_eq_picClass (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1))
    (a : Cocycle ((chains ℤ).obj E) (sgl C) 1)
    (ha : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧
      ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) :
    HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  let β := zcomp (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))
    (Cocycle.ofHom (resMap ℤ qb)) (add_zero 1)
  change CohomologyClass.mk β = picClass L
  have hβ₀ (U : Scheme.{0}) (x : Sx E 0 U) : ev β.1 0 1 (by simp) U x = 0 := by
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      0 1 _ U x = 0
    rw [ev_comp_ofHom, ev_comp_ofHom,
      GlobalTheory.EtC.PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)) (ev a.1 0 1 _ U x),
      GlobalTheory.EtC.PicSpec.sec_map_zero, GlobalTheory.EtC.PicSpec.sec_map_zero]
  have hβ₁ (U : Scheme.{0}) (x : Sx E 1 U) :
      ev β.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
    obtain ⟨c, hc, hv⟩ := ha U x
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      1 0 _ U x = _
    rw [ev_comp_ofHom, ev_comp_ofHom, hv, GlobalTheory.EtC.PicSpec.sec_map_comp, GlobalTheory.EtC.PicSpec.sec_map_comp, ← hc,
      GlobalTheory.EtC.PicSpec.sec_map_comp, ← Category.assoc, sglι_resAug, resι_resMap]
  let P (c : H ℤ E Gm 1) : Prop :=
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))
  have hspec : P (picClass L) := by
    change P (pick P)
    exact pick_spec ⟨_, β, rfl, hβ₀, hβ₁⟩
  obtain ⟨γ, hγ, hγ₀, hγ₁⟩ := hspec
  have hEq : β = γ := by
    refine Cocycle.ext (CupSpec.ev_ext β.1 γ.1 fun p s h U x => ?_)
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      exact (hβ₀ U x).trans (hγ₀ U x).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      exact (hβ₁ U x).trans (hγ₁ U x).symm
    | p + 2 =>
      have hZ := GlobalTheory.EtC.PicSpec.res_isZero Gm s (by omega)
      exact (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).trans
        (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).symm
  rw [hEq, hγ]

end GlobalTheory.EtC.KumPic.PostVal
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEpi

theorem exists_prime_over (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hs : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (hi : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})
    (p : PrimeSpectrum A) (hp : f ∈ p.asIdeal) :
    ∃ q : PrimeSpectrum A', PrimeSpectrum.comap (algebraMap A A') q = p := by
  set I : Ideal A := Ideal.span {f} with hI
  set J : Ideal A' := Ideal.span {algebraMap A A' f} with hJ
  have hIJ : I ≤ J.comap (algebraMap A A') := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span rfl
  let φ : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J (algebraMap A A') hIJ
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hi a ha)
    · intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨a, ha⟩ := hs b
      refine ⟨Ideal.Quotient.mk I a, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
      have := J.neg_mem ha
      simpa using this
  let e : A ⧸ I ≃+* A' ⧸ J := RingEquiv.ofBijective φ hφ
  have hIp : I ≤ p.asIdeal := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hp
  let p0 : Ideal (A ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
  have hp0 : p0.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  let q : Ideal A' := (p0.comap (e.symm : A' ⧸ J →+* A ⧸ I)).comap (Ideal.Quotient.mk J)
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨q, hq⟩, ?_⟩
  ext a
  have he : e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) = Ideal.Quotient.mk I a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  change Ideal.Quotient.mk J (algebraMap A A' a) ∈ p0.comap (e.symm : A' ⧸ J →+* A ⧸ I) ↔ a ∈ p.asIdeal
  rw [Ideal.mem_comap]
  change e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) ∈ p0 ↔ _
  rw [he]
  exact Ideal.mem_quotient_iff_mem hIp

theorem loc_point {X B : Scheme.{0}} (e : B ⟶ X) [Etale e] {T : Scheme.{0}} (x : T ⟶ X) (t : T)
    (ht : x t ∈ Set.range e) :
    ∃ (V : Scheme.{0}) (g : V ⟶ T), IsAffine V ∧ Etale g ∧ t ∈ Set.range g ∧ ∃ y : V ⟶ B, y ≫ e = g ≫ x := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := e) t b hb.symm
  obtain ⟨W0, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (pullback x e).isBasis_affineOpens)
    (show z ∈ (⊤ : (pullback x e).Opens) from trivial)
  let W : (pullback x e).Opens := W0
  haveI : IsAffine W := hW
  refine ⟨W, W.ι ≫ pullback.fst x e, inferInstance, inferInstance, ⟨⟨z, hzW⟩, ?_⟩, W.ι ≫ pullback.snd x e, ?_⟩
  · exact hz1
  · simp [pullback.condition]

theorem epi_of_loc (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E)
    (h : ∀ (T : Scheme.{0}) (x : E.obj (op T)),
      Loc T fun (V : Scheme.{0}) (k : V ⟶ T) => (∃ y, f.app (op V) y = E.map k.op x) ∨ (∃ y, g.app (op V) y = E.map k.op x)) :
    Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  refine ⟨fun {F} φ ψ hφψ => ?_⟩
  have ef : (free R).map f ≫ φ = (free R).map f ≫ ψ := by
    simpa using congrArg (biprod.inl ≫ ·) hφψ
  have eg : (free R).map g ≫ φ = (free R).map g ≫ ψ := by
    simpa using congrArg (biprod.inr ≫ ·) hφψ
  have res_map : ∀ {G H : Shv R} (χ : G ⟶ H) {V U : Scheme.{0}} (k : V ⟶ U) (s : Sec G U),
      Sec.res k (Sec.map χ s) = Sec.map χ (Sec.res k s) := by
    intro G H χ V U k s
    exact (NatTrans.naturality_apply χ.hom k.op s).symm
  have map_comp : ∀ {G H K : Shv R} (χ : G ⟶ H) (ω : H ⟶ K) {U : Scheme.{0}} (s : Sec G U),
      Sec.map (χ ≫ ω) s = Sec.map ω (Sec.map χ s) := by
    intros; rfl
  obtain ⟨-, hext, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R E F
  obtain ⟨-, -, -, hmapP⟩ := GlobalTheory.T.free_sections_ext_res_map R P F
  obtain ⟨-, -, -, hmapQ⟩ := GlobalTheory.T.free_sections_ext_res_map R Q F
  apply hext
  intro T x
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1
  obtain ⟨S, hS, hP⟩ := h T x
  refine ⟨S, hS, fun V k hk => ?_⟩
  rcases hP V k hk with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [res_map, res_map, hres, ← hy, ← hmapP, ← map_comp, ← map_comp, ef]
  · rw [res_map, res_map, hres, ← hy, ← hmapQ, ← map_comp, ← map_comp, eg]

end GlobalTheory.EtC.MVEpi

namespace GlobalTheory.EtC.MVEpi

theorem mv_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  intro R _ A A' _ _ _ _ f hs hi
  haveI hd : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  apply epi_of_loc
  intro T (x : T ⟶ Spec (CommRingCat.of A))
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    by_cases hf : f ∈ (x t).asIdeal
    · obtain ⟨q, hq⟩ := exists_prime_over A A' f hs hi (x t) hf
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A A'))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inr ⟨y, hy⟩⟩
    · have hr : x t ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
        exact hf
      obtain ⟨q, hq⟩ := hr
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inl ⟨y, hy⟩⟩
  · rintro V W g k (⟨y, hy⟩ | ⟨y, hy⟩)
    · refine Or.inl ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]
    · refine Or.inr ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]

end GlobalTheory.EtC.MVEpi
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace CupPull

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map f).sub j l h = (x.sub j l h).map f := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply] at this
  exact this.symm

theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cochain ((chains R).obj E') I n} {β : Cochain ((chains R).obj E') J m}
    {γ : Cochain ((chains R).obj E') K k} (h : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w hw U x
  rw [CupSpec.ev_pull, h N w hw U (x.map f)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [CupSpec.ev_pull, CupSpec.ev_pull, sub_map, sub_map]

end CupPull

theorem Pair.cup_pull : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  intro R _ I J K μ E E' f n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := Pair.aw_exists μ E' hk α β
  rw [Pair.cup_spec μ E' hk α β γ hγ, cpre_mk, cpre_mk, cpre_mk]
  refine (Pair.cup_spec μ E hk _ _ _ ?_).symm
  have e : ((Cocycle.ofHom ((chains R).map f) : Cocycle _ _ 0) : Cochain _ _ 0) = Cochain.ofHom ((chains R).map f) :=
    Cocycle.ofHom_coe _
  simp only [zcomp, Cocycle.mk_coe, e]
  exact CupPull.isAW_pull μ f hk hγ

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem SemiMap.op_image_spec : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  fun _ _ _ _ _ _ ρ => ⟨fun E n α => (cup_op_spec.2 ρ E n α).1, fun E n α β h => (cup_op_spec.2 ρ E n α).2 β h⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.OpComp

theorem ev_comp_ofHom' {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (u : I ⟶ K) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x =
      Sec.map (u.f s) (ev (R := R) α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

def invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat g s a := by
    apply (hb _ s).1
    change ρ.app _ s (Sec.res g ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm a)) =
      ρ.app _ s ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm (Sec.res g a))
    rw [← ρ.nat]
    have e1 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply (Sec.res g a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]
  comm U s t a := by
    apply (hb U t).1
    change ρ.app U t (Sec.map (I.d s t) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)) =
      ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a))
    rw [← ρ.comm]
    have e1 := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply (Sec.map (J.d s t) a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]

theorem invSemi_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invSemi ρ hb).app U s (ρ.app U s a) = a := by
  change (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm (AddEquiv.ofBijective (ρ.app U s) (hb U s) a) = a
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

theorem app_invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (b : Sec (J.X s) U) :
    ρ.app U s ((invSemi ρ hb).app U s b) = b := by
  change AddEquiv.ofBijective (ρ.app U s) (hb U s) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm b) = b
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply b

theorem op_comp_bij : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  intro S R _ _ I J J' ρ ρ' u hu
  refine ⟨fun E n x => ?_, fun hb E n => ?_⟩
  · obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := ρ.image_exists E n α
    rw [ρ.op_spec E n α β hβ]
    change _ = CohomologyClass.mk (zcomp β (Cocycle.ofHom u) (add_zero n))
    refine ρ'.op_spec E n α _ (fun p s h U y => ?_)
    change ev (R := R) (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom', hβ, hu]
  · set σ := invSemi ρ hb
    have h1 : ∀ x, σ.op.app E n (ρ.op.app E n x) = x := by
      intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := ρ.image_exists E n α
      rw [ρ.op_spec E n α β hβ]
      refine σ.op_spec E n β α (fun p s h U y => ?_)
      rw [hβ, invSemi_app]
    have h2 : ∀ y, ρ.op.app E n (σ.op.app E n y) = y := by
      intro y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      obtain ⟨α, hα⟩ := σ.image_exists E n β
      rw [σ.op_spec E n β α hα]
      refine ρ.op_spec E n α β (fun p s h U y => ?_)
      rw [hα, app_invSemi]
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end GlobalTheory.EtC.OpComp
end
end
