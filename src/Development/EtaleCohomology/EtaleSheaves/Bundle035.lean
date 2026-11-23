module

public import Development.EtaleCohomology.EtaleSheaves.Bundle020
public import Development.EtaleCohomology.EtaleSheaves.Bundle021
public import Development.EtaleCohomology.EtaleSheaves.Bundle022
public import Development.EtaleCohomology.EtaleSheaves.Bundle026
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Sites.Adjunction
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.SecPrePf
open LateralTheory.E.t_E3Cut

theorem id_mem (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {S : Sieve (Spec A)}
    (hS : S ∈ Scheme.etaleTopology (Spec A)) : S.arrows (𝟙 _) := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have : IsLocalRing A := hA.elim fun h _ => h.toIsLocalRing
  obtain ⟨hcov, -⟩ := (Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨j, y, hy⟩ := hcov (IsLocalRing.closedPoint A : PrimeSpectrum A)
  have : Etale (𝒰.f j) := 𝒰.map_prop j
  have hsurj : Function.Surjective (𝒰.f j) := by
    intro z
    have hopen : IsOpen (Set.range (𝒰.f j)) := (𝒰.f j).isOpenMap.isOpen_range
    have hmem : (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ Set.range (𝒰.f j) := ⟨y, hy⟩
    exact (IsLocalRing.specializes_closedPoint (z : PrimeSpectrum A)).mem_open hopen hmem
  have : Surjective (𝒰.f j) := ⟨hsurj⟩
  obtain ⟨s, hs⟩ := hSec A hA (𝒰.f j)
  have h1 : S.arrows (𝒰.f j) := hle _ _ (Presieve.ofArrows.mk j)
  have h2 := S.downward_closed h1 s
  rwa [hs] at h2

theorem mem_of_cov (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {V : Scheme.{0}} (h : Spec A ⟶ V)
    (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) : S.arrows h := by
  have := id_mem hSec A hA (Scheme.etaleTopology.pullback_stable h hS)
  simpa using this

variable {R : Type} [CommRing R]

def sky (U : Scheme.{0}) (N : ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ ((U ⟶ V.unop) → N)
  map g := ModuleCat.ofHom
    { toFun := fun φ h => φ (h ≫ g.unop)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

theorem sky_isSheaf (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (N : ModuleCat.{1} (ULift.{1} R)) : Presheaf.IsSheaf Scheme.etaleTopology (sky U N) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  have hc := hx.to_sieveCompatible
  refine ⟨fun h => x h (hU h S hS) (𝟙 U), ?_, ?_⟩
  · intro W f hf
    funext k
    have e := congrFun (hc f k hf) (𝟙 U)
    change x (k ≫ f) _ (𝟙 U) = x f hf k
    rw [e]
    change x f hf (𝟙 U ≫ k) = _
    rw [Category.id_comp]
  · intro t ht
    funext h
    have e := congrFun (ht h (hU h S hS)) (𝟙 U)
    change t (𝟙 U ≫ h) = _ at e
    rw [Category.id_comp] at e
    exact e

@[simps]
def toSky (Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) {N : ModuleCat.{1} (ULift.{1} R)}
    (g : Q.obj (op U) ⟶ N) : Q ⟶ sky U N where
  app V := ModuleCat.ofHom
    { toFun := fun p h => g.hom ((Q.map h.op).hom p)
      map_add' := fun _ _ => by funext h; simp
      map_smul' := fun _ _ => by funext h; simp }
  naturality V W f := by
    ext p
    funext h
    change g.hom ((Q.map h.op).hom ((Q.map f).hom p)) = g.hom ((Q.map (h ≫ f.unop).op).hom p)
    rw [op_comp, Quiver.Hom.op_unop, Q.map_comp]
    rfl

theorem toSheafify_bij (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    Function.Bijective ((toSheafify Scheme.etaleTopology P).app (op U)).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e := toSheafify_sheafifyLift Scheme.etaleTopology (toSky P U (𝟙 _)) (sky_isSheaf U hU _)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom x) e) (𝟙 U)
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] at e2
    have e3 : (P.map (𝟙 U).op).hom x = 0 := e2.symm
    rwa [op_id, P.map_id] at e3
  · intro y
    let η := toSheafify Scheme.etaleTopology P
    let Q := sheafify Scheme.etaleTopology P
    let g : Q.obj (op U) ⟶ ModuleCat.of _ (Q.obj (op U) ⧸ LinearMap.range (η.app (op U)).hom) :=
      ModuleCat.ofHom (Submodule.mkQ _)
    have e := sheafify_hom_ext Scheme.etaleTopology (toSky Q U g) 0 (sky_isSheaf U hU _) (by
      ext V p
      funext h
      have nat : (Q.map h.op).hom ((η.app V).hom p) = (η.app (op U)).hom ((P.map h.op).hom p) :=
        (congrArg (fun φ => φ.hom p) (η.naturality h.op)).symm
      simp only [NatTrans.comp_app, toSky_app, Limits.comp_zero]
      change (Submodule.mkQ _) ((Q.map h.op).hom (η.app V |>.hom p)) = 0
      rw [nat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom y) e) (𝟙 U)
    simp only [toSky_app] at e2
    change (Submodule.mkQ _) ((Q.map (𝟙 U).op).hom y) = 0 at e2
    rw [op_id, Q.map_id, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at e2
    obtain ⟨x, hx⟩ := e2
    exact ⟨x, hx⟩

theorem SecPre_of (hSec : SHSection) : LateralTheory.E.SHEqvPf.SecPre := by
  intro _ q i A hA
  exact toSheafify_bij (R := ZMod q) (Spec A) (fun h S hS => mem_of_cov hSec A hA h S hS) (Scheme.Γ ⋙ twF q i)

end LateralTheory.E.SecPrePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.stupidPf

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.ofHom_comp]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  exact Cochain.id_comp _

theorem cpull_iso {R : Type} [CommRing R] {K L : Cx R} (e : K ≅ L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, e.inv_hom_id, cpull_id]
  · rw [← cpull_comp, e.hom_inv_id, cpull_id]

def trunc0 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ∃ (eK : tr K 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (K.X (-((0 : ℕ) : ℤ))))
    (eL : tr L 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (L.X (-((0 : ℕ) : ℤ)))),
    trm g 0 ≫ eL.hom = eK.hom ≫ (CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))

def incl : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0] {K L : Cx R} (g : K ⟶ L) (N : ℕ),
  ∃ (ιK : tr K N ⟶ K) (ιL : tr L N ⟶ L), trm g N ≫ ιL = ιK ≫ g ∧
    ∀ n : ℤ, n + 1 ≤ (N : ℤ) → Function.Bijective (cpull ιK I n) ∧ Function.Bijective (cpull ιL I n)

theorem stupid_of (h0 : trunc0) (hI : incl) : LateralTheory.E.CxDescPf.stupid := by
  intro R _ I _ _ K L _ _ g
  refine ⟨fun hb j => ?_, fun m N hN hG => ?_⟩
  · obtain ⟨eK, eL, hsq⟩ := h0 R g
    have hc : (cpull (trm g 0) I j) ∘ (cpull eL.hom I j) =
        (cpull eK.hom I j) ∘ (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j) := by
      funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    have hb' : Function.Bijective ((cpull (trm g 0) I j) ∘ (cpull eL.hom I j)) := by
      rw [hc]; exact (cpull_iso eK I j).comp (hb j)
    exact (Function.Bijective.of_comp_iff _ (cpull_iso eL I j)).1 hb'
  · obtain ⟨ιK, ιL, hsq, hbij⟩ := hI R I g N
    have hc : ∀ j, (cpull ιK I j) ∘ (cpull g I j) = (cpull (trm g N) I j) ∘ (cpull ιL I j) := by
      intro j; funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    refine ⟨fun j hj => ?_, ?_⟩
    · have hb' : Function.Bijective ((cpull ιK I j) ∘ (cpull g I j)) := by
        rw [hc]; exact (hG.1 j hj).comp (hbij j (by omega)).2
      exact (Function.Bijective.of_comp_iff' (hbij j (by omega)).1 _).1 hb'
    · have hi : Function.Injective ((cpull ιK I m) ∘ (cpull g I m)) := by
        rw [hc]; exact hG.2.comp (hbij m hN).2.1
      exact Function.Injective.of_comp hi

end LateralTheory.E.stupidPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.longPf
open LateralTheory.E.CxDescPf

def LES : Prop := ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x)

theorem four_inj {A B C D A' B' C' D' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D']
    (α : A →+ B) (β : B →+ C) (γ : C →+ D) (α' : A' →+ B') (β' : B' →+ C') (γ' : C' →+ D')
    (a : A →+ A') (b : B →+ B') (c : C →+ C') (d : D →+ D')
    (h2 : Function.Exact α β) (h2' : Function.Exact α' β') (h3 : Function.Exact β γ)
    (s1 : ∀ x, b (α x) = α' (a x)) (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x))
    (ha : Function.Surjective a) (hb : Function.Injective b) (hd : Function.Injective d) : Function.Injective c := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have : γ x = 0 := hd (by rw [s3, hx, map_zero, map_zero])
  obtain ⟨y, rfl⟩ := (h3 x).1 this
  have : β' (b y) = 0 := by rw [← s2]; exact hx
  obtain ⟨z', hz'⟩ := (h2' (b y)).1 this
  obtain ⟨z, rfl⟩ := ha z'
  have : α z = y := hb (by rw [s1, hz'])
  rw [← this]; exact h2.apply_apply_eq_zero z

theorem four_surj {B C D E B' C' D' E' : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D'] [AddCommGroup E']
    (β : B →+ C) (γ : C →+ D) (δ : D →+ E) (β' : B' →+ C') (γ' : C' →+ D') (δ' : D' →+ E')
    (b : B →+ B') (c : C →+ C') (d : D →+ D') (e : E →+ E')
    (h2' : Function.Exact β' γ') (h3 : Function.Exact γ δ) (h3' : Function.Exact γ' δ')
    (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x)) (s4 : ∀ x, e (δ x) = δ' (d x))
    (hb : Function.Surjective b) (hd : Function.Surjective d) (he : Function.Injective e) : Function.Surjective c := by
  intro x'
  obtain ⟨y, hy⟩ := hd (γ' x')
  have : δ y = 0 := he (by rw [s4, hy, map_zero, h3'.apply_apply_eq_zero])
  obtain ⟨w, rfl⟩ := (h3 y).1 this
  have : γ' (x' - c w) = 0 := by rw [map_sub, ← s3, hy, sub_self]
  obtain ⟨u', hu'⟩ := (h2' _).1 this
  obtain ⟨u, rfl⟩ := hb u'
  exact ⟨w + β u, by rw [map_add (f := _), s2, hu', add_sub_cancel]⟩

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_sq {R : Type} [CommRing R] {A B C D : Cx R} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (w : f ≫ g = f' ≫ g') (I : Cx R) (n : ℤ) (x) :
    cpull f I n (cpull g I n x) = cpull f' I n (cpull g' I n x) := by
  rw [← cpull_comp, ← cpull_comp, w]

def Ses : Prop := ∀ (R : Type) [CommRing R] (N : ℕ), ∃ (i : ∀ K : Cx R, tr K N ⟶ tr K (N + 1))
  (p : ∀ K : Cx R, tr K (N + 1) ⟶ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ))))
  (w : ∀ K, i K ≫ p K = 0), (∀ K, (ShortComplex.mk (i K) (p K) (w K)).ShortExact) ∧
  ∀ {K L : Cx R} (g : K ⟶ L), i K ≫ trm g (N + 1) = trm g N ≫ i L ∧
    p K ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) = trm g (N + 1) ≫ p L

theorem long_of (hLES : LES) (hSes : Ses) : LateralTheory.E.CxDescPf.long := by
  intro R _ I _ hI K L _ _ g m N h3 h1
  obtain ⟨d, hex, hnat⟩ := hLES R I hI
  obtain ⟨i, p, w, hse, hn⟩ := hSes R N
  let MainNotions := ShortComplex.mk (i K) (p K) (w K)
  let SL := ShortComplex.mk (i L) (p L) (w L)
  let φ : MainNotions ⟶ SL := ShortComplex.Hom.mk (trm g N) (trm g (N + 1))
    ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) (hn g).1.symm (hn g).2.symm
  have sf : ∀ j x, cpull φ.τ₁ I j (cpull SL.f I j x) = cpull MainNotions.f I j (cpull φ.τ₂ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₁₂ I j x
  have sg : ∀ j x, cpull φ.τ₂ I j (cpull SL.g I j x) = cpull MainNotions.g I j (cpull φ.τ₃ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₂₃ I j x
  have inj : ∀ n : ℤ, n + 1 ≤ m → Function.Injective (cpull φ.τ₂ I (n + 1)) := by
    intro n hn
    refine four_inj (d SL (hse L) n) (cpull SL.g I (n + 1)) (cpull SL.f I (n + 1))
      (d MainNotions (hse K) n) (cpull MainNotions.g I (n + 1)) (cpull MainNotions.f I (n + 1))
      (cpull φ.τ₁ I n) (cpull φ.τ₃ I (n + 1)) (cpull φ.τ₂ I (n + 1)) (cpull φ.τ₁ I (n + 1))
      (hex SL (hse L) n).2.2 (hex MainNotions (hse K) n).2.2 (hex SL (hse L) (n + 1)).1
      (fun x => hnat MainNotions SL (hse K) (hse L) φ n x) (sg (n + 1)) (sf (n + 1))
      (h1.1 n (by omega)).2 ?_ ?_
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h3.1 _ h).1
      · rw [h]; exact h3.2
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h1.1 _ h).1
      · rw [h]; exact h1.2
  have surj : ∀ j : ℤ, j < m → Function.Surjective (cpull φ.τ₂ I j) := by
    intro j hj
    refine four_surj (cpull SL.g I j) (cpull SL.f I j) (d SL (hse L) j)
      (cpull MainNotions.g I j) (cpull MainNotions.f I j) (d MainNotions (hse K) j)
      (cpull φ.τ₃ I j) (cpull φ.τ₂ I j) (cpull φ.τ₁ I j) (cpull φ.τ₃ I (j + 1))
      (hex MainNotions (hse K) j).1 (hex SL (hse L) j).2.1 (hex MainNotions (hse K) j).2.1
      (sg j) (sf j) (fun x => hnat MainNotions SL (hse K) (hse L) φ j x)
      (h3.1 j hj).2 (h1.1 j hj).2 ?_
    rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
    · exact (h3.1 _ h).1
    · rw [h]; exact h3.2
  have inj' : ∀ j : ℤ, j ≤ m → Function.Injective (cpull φ.τ₂ I j) := by
    intro j hj
    have := inj (j - 1) (by omega)
    rwa [sub_add_cancel] at this
  exact ⟨fun j hj => ⟨inj' j hj.le, surj j hj⟩, inj' m le_rfl⟩

end LateralTheory.E.longPf
end
end

section

open Polynomial

namespace LateralTheory.E.FracAICPf

open Classical in
theorem FracAIC_of : LateralTheory.E.ULAStalkPf.FracAIC := by
  intro T K _ _ _ _ _ hT p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (p.support.image p.coeff)
  set s : K := algebraMap T K b with hs
  have hs0 : s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  set q := p.scaleRoots s with hq
  have hqm : q.Monic := (monic_scaleRoots_iff _).mpr hp
  have hqd : q.natDegree = p.natDegree := natDegree_scaleRoots _ _
  have hlift : q ∈ lifts (algebraMap T K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hq, coeff_scaleRoots]
    by_cases hi : p.coeff i = 0
    · rw [hi, zero_mul]; exact ⟨0, map_zero _⟩
    have hile : i ≤ p.natDegree := le_natDegree_of_ne_zero hi
    rcases lt_or_eq_of_le hile with hlt | heq
    · obtain ⟨c, hc⟩ := hb (p.coeff i) (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (b : T) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, Algebra.smul_def, pow_succ, hs]
      ring
    · subst heq
      rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]
      exact ⟨1, map_one _⟩
  obtain ⟨q', hq'map, hq'deg, hq'm⟩ := lifts_and_natDegree_eq_and_monic hlift hqm
  obtain ⟨r, hr⟩ := hT q' hq'm (by rw [hq'deg, hqd]; exact hdeg)
  refine ⟨algebraMap T K r / s, ?_⟩
  have h1 : q.eval (algebraMap T K r) = 0 := by
    rw [← hq'map, eval_map, eval₂_at_apply, hr, map_zero]
  have h2 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap T K r / s) s
  simp only [RingHom.id_apply, eval₂_id] at h2
  rw [mul_div_cancel₀ _ hs0, ← hq, h1] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hs0)

end LateralTheory.E.FracAICPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.FreeCoprodPf

variable {ι : Type} (X : ι → Scheme.{0})

def P0 : PSh where
  obj U := Σ j, (unop U ⟶ X j)
  map {U V} h := ↾fun (s : Σ j, (unop U ⟶ X j)) => (⟨s.1, h.unop ≫ s.2⟩ : Σ j, (unop V ⟶ X j))
  map_id U := by ext s <;> simp
  map_comp f g := by ext s <;> simp

def inj (j : ι) : yoneda.obj (X j) ⟶ P0 X where
  app U := ↾fun f => (⟨j, f⟩ : Σ j, (unop U ⟶ X j))

def isColimitCofanSigmaOfRepresentablePresheaves : IsColimit (Cofan.mk (P0 X) (inj X)) :=
  Cofan.IsColimit.mk _
    (fun s => { app := fun U => ↾fun (x : Σ j, (unop U ⟶ X j)) => (s.inj x.1).app U x.2
                naturality := fun U V h => by
                  ext x
                  exact NatTrans.naturality_apply (s.inj x.1) h x.2 })
    (fun s j => by ext U f; rfl)
    (fun s m hm => by
      ext U ⟨j, f⟩
      exact ConcreteCategory.congr_hom (congr_app (hm j) U) f)

def φ : P0 X ⟶ yoneda.obj (∐ X) where
  app U := ↾fun (x : Σ j, (unop U ⟶ X j)) => x.2 ≫ Sigma.ι X x.1

lemma inj_φ (j : ι) : inj X j ≫ φ X = yoneda.map (Sigma.ι X j) := rfl

abbrev ψ := Functor.whiskerRight (φ X) uliftFunctor.{1}

instance : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (ψ X) where
  imageSieve_mem {U} s := by
    let 𝒰 := (sigmaOpenCover X).pullback₁ s.down
    apply Scheme.etaleTopology.superset_covering _
      (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰))
    refine (Sieve.generate_le_iff _ _).2 ?_
    rintro _ _ ⟨i⟩
    refine ⟨⟨⟨i, pullback.snd _ _⟩⟩, ?_⟩
    apply ULift.ext
    exact (pullback.condition (f := s.down) (g := (sigmaOpenCover X).f i)).symm

instance : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (ψ X) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨⟨j, a⟩⟩ := x
    obtain ⟨⟨k, b⟩⟩ := y
    have h' : a ≫ Sigma.ι X j = b ≫ Sigma.ι X k := congrArg ULift.down h
    by_cases hjk : j = k
    · subst hjk
      obtain rfl := (cancel_mono (Sigma.ι X j)).1 h'
      refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.top_mem _)
      intro V g _
      simp [Presheaf.equalizerSieve]
    · have := isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hjk
      exact Scheme.etaleTopology.superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

variable (R : Type) [CommRing R]

instance : (ModuleCat.free (ULift.{1} R)).IsLeftAdjoint := ⟨_, ⟨ModuleCat.adj _⟩⟩

instance : PreservesColimitsOfShape (Discrete ι) (freeP R) := by
  unfold freeP; infer_instance

instance : PreservesColimitsOfShape (Discrete ι) (free R) := by
  unfold free; infer_instance

lemma isIso_free_φ : IsIso ((free R).map (φ X)) := by
  have h1 : Scheme.etaleTopology.W (ψ X) := GrothendieckTopology.W_of_isLocallyBijective _ _
  have h2 := Scheme.etaleTopology.W_of_preservesSheafification (ModuleCat.free (ULift.{1} R)) _ h1
  rw [GrothendieckTopology.W_iff] at h2
  exact h2

theorem FreeCoprod_of : LateralTheory.E.CoprodPf.FreeCoprod := by
  intro R _ ι X
  have := isIso_free_φ X R
  have h0 := isColimitCofanMkObjOfIsColimit (free R) _ _ (isColimitCofanSigmaOfRepresentablePresheaves X)
  refine ⟨IsColimit.ofIsoColimit h0 (Cofan.ext (asIso ((free R).map (φ X))) fun j => ?_)⟩
  show (free R).map (inj X j) ≫ (free R).map (φ X) = (free R).map (yoneda.map (Sigma.ι X j))
  rw [← Functor.map_comp, inj_φ]

end LateralTheory.E.FreeCoprodPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ImgPf

theorem Img_of : LateralTheory.E.ChowCut.Img := by
  intro A _ Z X h p _ hh hZ
  have := hh
  have := hZ
  have : QuasiCompact h := inferInstance
  have : IsIntegralHom (h.toImage ≫ h.imageι) := by rw [Scheme.Hom.toImage_imageι]; exact hh
  refine ⟨h.image, h.toImage, h.imageι ≫ p, inferInstance, inferInstance,
    IsIntegralHom.of_comp h.toImage h.imageι, inferInstance, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc]

end LateralTheory.E.ImgPf
end
