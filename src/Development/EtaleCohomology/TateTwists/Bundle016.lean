module

public import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma zc_pull_mk {K L I : Cx R} (f : K ⟶ L) (n : ℤ) (b : Cocycle L I n) :
    cpull f I n (CohomologyClass.mk b) =
      CohomologyClass.mk (Cocycle.mk ((Cochain.ofHom f).comp b.1 (zero_add n)) (n + 1) rfl
        (by rw [δ_ofHom_comp, Cocycle.δ_eq_zero, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

lemma zc_push_mk {K I J : Cx R} (g : I ⟶ J) (n : ℤ) (a : Cocycle K I n) :
    cpush K g n (CohomologyClass.mk a) =
      CohomologyClass.mk (Cocycle.mk (a.1.comp (Cochain.ofHom g) (add_zero n)) (n + 1) rfl
        (by rw [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp])) := by
  rw [cpost_mk]; congr 1

end

theorem twpair_zc_fun_of : twpair_zc_fun := by
  intro R _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    constructor
    · rw [zc_pull_mk]; congr 1; apply Cocycle.ext; simp [Cochain.id_comp]
    · rw [zc_push_mk]; congr 1; apply Cocycle.ext; simp [Cochain.comp_id]
  · intro K L M f g I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_pull_mk, zc_pull_mk, zc_pull_mk]; congr 1; apply Cocycle.ext
    simp [Cochain.ofHom_comp]
  · intro K I J M f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_push_mk, zc_push_mk]
    congr 1
  · intro K L I J f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_pull_mk, zc_pull_mk, zc_push_mk]; congr 1; apply Cocycle.ext
    simp
  · intro K L f g ⟨ho⟩ I n
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g ho
    constructor
    · ext x
      obtain ⟨b, rfl⟩ := x.mk_surjective
      rw [zc_pull_mk, zc_pull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • z.comp b.1 (by omega), ?_⟩
      have hb : δ n (n + 1) (b : Cochain L I n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp only [hb, Cochain.comp_zero, zero_add, smul_smul, Int.units_mul_self, one_smul, hz',
        Cochain.sub_comp]
      rfl
    · ext x
      obtain ⟨a, rfl⟩ := x.mk_surjective
      rw [zc_push_mk, zc_push_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨a.1.comp z (by omega), ?_⟩
      have ha : δ n (n + 1) (a : Cochain I K n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega)]
      simp only [ha, Cochain.zero_comp, smul_zero, add_zero, hz', Cochain.comp_sub]
      rfl

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensUnivPf

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
  have := congrArg (fun φ : F ⟶ F => (φ.hom.app (op U)).hom x) h1
  simpa using this

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

def postPair {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (μ.mul _ s t w h a b)) ((u.f w).hom.naturality g.op)).symm
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = Sec.map (u.f (w+1)) (Sec.map (K.d w (w+1)) (μ.mul U s t w h a b)) := by
      rw [← secMap_comp, ← secMap_comp, u.comm]
    change Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz]
    simp [map_add (f := _)]

theorem part3 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {K' : Cx R} (u : K ⟶ K') :
    ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u :=
  ⟨postPair τ u, fun U s t w h a b => rfl⟩

theorem sep {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sep_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  exact sep S hS y z hh

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (h _ _).trans (h _ _).symm

theorem lift_ind {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (V : Scheme.{0}) (w : ℤ)
    (P : Sec (K.X w) V → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V), P (μ.mul V s t w h a b))
    (x : Tens I J V w) : P (μ.lift V w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using h0
  | of p t =>
    simp only [Pair.lift]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa using hm p.1.1 p.1.2 p.2 a b
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb

theorem part2 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) :
    I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0 := by
  intro hI hJ
  rw [CochainComplex.isStrictlyGE_iff]
  intro w hw
  apply isZero_of_sec
  intro U y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hh V g hg
  rw [← hx]
  simp only [map_zero]
  refine lift_ind τ V w (fun z => z = 0) rfl (fun a b ha hb => by rw [ha, hb]; simp) ?_ x
  intro s t h a b
  rcases (show s < 0 ∨ t < 0 by omega) with hs | ht
  · rw [sec_eq_zero_of_isZero (I.isZero_of_isStrictlyGE 0 s hs) a]; simp
  · rw [sec_eq_zero_of_isZero (J.isZero_of_isStrictlyGE 0 t ht) b]; simp

theorem uniq {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u v : K ⟶ K')
    (hu : τ.Compat ν f g u) (hv : τ.Compat ν f g v) : u = v := by
  ext w U y
  obtain ⟨U⟩ := U
  change Sec.map (u.f w) y = Sec.map (v.f w) y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  have nu : ∀ (φ : K ⟶ K') (z : Sec (K.X w) U), Sec.res e (Sec.map (φ.f w) z) = Sec.map (φ.f w) (Sec.res e z) :=
    fun φ z => (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) ((φ.f w).hom.naturality e.op)).symm
  rw [nu, nu, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (u.f w) z = Sec.map (v.f w) z) (by simp) ?_ ?_ x
  · intro a b ha hb
    simp only [Sec.map, map_add (f := _)] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    rw [hu, hv]

theorem nat_sec {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (e : V ⟶ U) (z : Sec F U) :
    Sec.res e (Sec.map φ z) = Sec.map φ (Sec.res e z) :=
  (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) (φ.hom.naturality e.op)).symm

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

theorem secMap_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (a : Sec F U) :
    Sec.map φ (n • a) = n • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ a

theorem exists_of_degreewise {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : ∀ w, K.X w ⟶ K'.X w)
    (hm : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (m w) (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)) :
    ∃ u : K ⟶ K', τ.Compat ν f g u := by
  refine ⟨{ f := m, comm' := ?_ }, fun U s t w h a b => hm U s t w h a b⟩
  rintro w _ rfl
  ext U y
  obtain ⟨U⟩ := U
  change Sec.map (K'.d w (w+1)) (Sec.map (m w) y) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) y)
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  rw [nat_sec, nat_sec, nat_sec, nat_sec, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (K'.d w (w+1)) (Sec.map (m w) z) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) z))
    (by simp [Sec.map]) ?_ ?_ x
  · intro a b ha hb
    simp only [secMap_add] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    have cf : Sec.map (f.f (s+1)) (Sec.map (I.d s (s+1)) a) = Sec.map (I'.d s (s+1)) (Sec.map (f.f s) a) := by
      rw [← secMap_comp, ← secMap_comp, f.comm]
    have cg : Sec.map (g.f (t+1)) (Sec.map (J.d t (t+1)) b) = Sec.map (J'.d t (t+1)) (Sec.map (g.f t) b) := by
      rw [← secMap_comp, ← secMap_comp, g.comm]
    rw [hm, τ.leibniz, secMap_add, secMap_zsmul, hm, hm, ν.leibniz, cf, cg]

end LateralTheory.EtaleFoundations.TensUnivPf

def LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ),
      ∃ m : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
        Sec.map m (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise (hdeg : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists) :
    LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  intro R _ I J K τ hτ
  refine ⟨fun {I' J' K'} ν f g => ?_, LateralTheory.EtaleFoundations.TensUnivPf.part2 τ hτ,
    fun u => LateralTheory.EtaleFoundations.TensUnivPf.part3 τ u⟩
  obtain ⟨u, hu⟩ := LateralTheory.EtaleFoundations.TensUnivPf.exists_of_degreewise τ hτ ν f g
    (fun w => (hdeg R τ hτ ν f g w).choose) (fun U s t w h a b => (hdeg R τ hτ ν f g w).choose_spec U s t h a b)
  exact ⟨u, hu, fun v hv => LateralTheory.EtaleFoundations.TensUnivPf.uniq τ hτ ν f g v u hv hu⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def twGenR {q : ℕ} (A : CommRingCat.{0}) (ζ : Prim q A) : (twF q 1).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

def ExistsEtaleMonoMuTwistKillingRootRelations : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) ∧
    ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0

def EtaleMuTwistMonoExtendsToTorsorSheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) →
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

theorem exists_etale_mono_muTwist_into_torsorSheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : EtaleMuTwistMonoExtendsToTorsorSheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist := by
  intro q _
  obtain ⟨T, τ, hm, hl⟩ := h1 q
  exact h2 q T τ hm hl
end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsKumCoc (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ)
    (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
    ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_uniq : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γ → IsKumCoc q u γ' → CohomologyClass.mk γ = CohomologyClass.mk γ'

def kum_mul_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γu γv : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γu → IsKumCoc q v γv →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        IsKumCoc q (u * v) γ ∧ CohomologyClass.mk γ = CohomologyClass.mk γu + CohomologyClass.mk γv

def kum_pow_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q (u ^ q) γ ∧ CohomologyClass.mk γ = 0

theorem kum_add_of (he : kum_exists) (hu : kum_uniq) (hm : kum_mul_coc) (hp : kum_pow_coc) : kum_add := by
  intro q _ X u v hq
  obtain ⟨γu, eu, ku⟩ := kum_spec_of_exists he q X u hq
  obtain ⟨γv, ev', kv⟩ := kum_spec_of_exists he q X v hq
  obtain ⟨γuv, euv, kuv⟩ := kum_spec_of_exists he q X (u * v) hq
  obtain ⟨γp, epw, kpw⟩ := kum_spec_of_exists he q X (u ^ q) hq
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ, hsum⟩ := hm q X u v hq γu γv ku kv
    rw [← euv, ← eu, ← ev', ← hsum]
    exact hu q X (u * v) hq γuv γ kuv hγ
  · obtain ⟨γ, hγ, h0⟩ := hp q X u hq
    rw [← epw, ← h0]
    exact hu q X (u ^ q) hq γp γ kpw hγ

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy : Prop :=
  ∀ (R : Type) [CommRing R] (K L I : Cx R) [I.IsKInjective] (f : K ⟶ L) [QuasiIso f],
    (∀ a : K ⟶ I, ∃ m : L ⟶ I, Nonempty (Homotopy (f ≫ m) a)) ∧
    ∀ m m' : L ⟶ I, Nonempty (Homotopy (f ≫ m) (f ≫ m')) → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0] (a b : sgl F ⟶ I),
    Nonempty (Homotopy a b) → a = b

theorem LateralTheory.EtaleFoundations.etale_sheaf_ext_hom_injective_resolution_of_lift_and_rigidity (hA : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy)
    (hB : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual) : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m, hm⟩ := (hA R (sgl F) T I ε).1 a
    exact ⟨m, hB R F I _ _ hm⟩
  · exact (hA R (sgl F) T I ε).2 m m' ⟨Homotopy.ofEq h⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem res_neg_isZero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (by intro i h; change ((i : ℕ) : ℤ) = s at h; omega)

theorem units_map_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (g ≫ x).appTop.hom.toMonoidHom u =
      Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) := by
  ext; simp; rfl

theorem isUnit_q_map {U X : Scheme.{0}} (x : U ⟶ X) (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_unique (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) (q : ℕ) [NeZero q] (X : Scheme.{0})
    (u : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤)))
    (γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1)
    (h1 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h1' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ'.1 1 0 (by simp) U x = 0)
    (h2' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ'.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  apply Cocycle.ext
  apply (hev (ZMod q)).2.2.1
  intro p s h U x
  match p, s, h with
  | 0, s, h =>
    obtain rfl : s = 1 := by omega
    revert x
    show ∀ x : U ⟶ X, _
    intro x
    apply (hsg (ZMod q) _ U).1
    obtain ⟨S, hS, hroot⟩ := (hpl q U).2.2.2 (isUnit_q_map x q hq) (Units.map x.appTop.hom.toMonoidHom u)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨v, hv⟩ := hroot V g hg
    have hv' : v ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by rw [units_map_comp]; exact hv
    exact ((hev (ZMod q)).2.1 γ.1 0 1 h V U g x).trans ((h2 V (g ≫ x) v hv').trans
      ((h2' V (g ≫ x) v hv').symm.trans ((hev (ZMod q)).2.1 γ'.1 0 1 h V U g x).symm))
  | 1, s, h =>
    obtain rfl : s = 0 := by omega
    exact (h1 U x).trans (h1' U x).symm
  | p + 2, s, h =>
    have hz := res_neg_isZero (ZMod q) (tw q 1) s (by omega)
    have hv : γ.1.v (-((p + 2 : ℕ) : ℤ)) s h = γ'.1.v (-((p + 2 : ℕ) : ℤ)) s h := hz.eq_of_tgt _ _
    unfold ev
    rw [hv]

theorem kum_nat_of (he : kum_exists) (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) : kum_nat := by
  intro q _ Y X f u hq
  obtain ⟨γ, hc, h1, h2⟩ := kum_spec_of_exists he q X u hq
  have hqY := isUnit_q_map f q hq
  obtain ⟨γ', hc', h1', h2'⟩ := kum_spec_of_exists he q Y (Units.map f.appTop.hom.toMonoidHom u) hqY
  rw [← hc, ← hc']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine kum_unique hev hpl hsg q Y _ hqY _ γ' ?_ ?_ h1' h2'
  · intro U x
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 (by simp) U x).trans (h1 U (x ≫ f))
  · intro U x v hv
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 (by simp) U x).trans
      (h2 U (x ≫ f) v (by rw [hv, units_map_comp]))

end LateralTheory.EtaleFoundations
end
