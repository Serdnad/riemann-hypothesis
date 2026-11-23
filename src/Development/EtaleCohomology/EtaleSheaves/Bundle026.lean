module

public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Mathlib.RingTheory.Etale.StandardEtale
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafA6suppPf

def LeafAWSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
  (α : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n)
  (β : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q j)) m),
  ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q (i + j))) (n + m),
    (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
    cup q (CohomologyClass.mk α : Ht q E n i) (CohomologyClass.mk β : Ht q E m j) = CohomologyClass.mk γ

def LeafRepVanish : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ (F : Shv R) (n : ℤ)
  (a : H R E F n), pull R f F n a = 0 →
  ∃ α : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk α = a ∧
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y), ev α.1 N w h Y ((f.app _).app _ y) = 0

def LeafCochainVanish : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (K : Cx R) (k : ℤ) (γ : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0) →
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) →
    γ = 0

theorem sub_map {U E : Spc} (f : U ⟶ E) {N : ℕ} {Y : Scheme.{0}} (y : Sx U N Y) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((f.app _).app _ y) j l h = (f.app _).app _ (Sx.sub y j l h) := by
  unfold Sx.sub
  have e := NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op Y)
  exact (ConcreteCategory.congr_hom e y).symm

theorem LeafA6supp_of (h1 : LeafAWSpec) (h2 : LeafRepVanish) (h3 : LeafCochainVanish) : LateralTheory.E.D2.LeafA6supp := by
  intro q _ U V E f g hc n m i j a b ha hb
  obtain ⟨α, rfl, hα⟩ := h2 (ZMod q) f hc.1 (tw q i) n a ha
  obtain ⟨β, rfl, hβ⟩ := h2 (ZMod q) g hc.2.1 (tw q j) m b hb
  obtain ⟨γ, hAW, hcup⟩ := h1 q E α β
  rw [hcup]
  have : γ.1 = 0 := by
    apply h3 (ZMod q) f g hc
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map f y 0 (p : ℕ), hα]
      simp
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map g y (p : ℕ) (N - p), hβ]
      simp
  have hγ : γ = 0 := Subtype.ext this
  rw [hγ]
  exact CohomologyClass.mk_zero _ _ _

end LateralTheory.E.LeafA6suppPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ZModFlatnessFromBaerCriterion

def TensTwRes : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)}
  (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U),
  IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor →
  IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def LeafInjSecInj : Prop := ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}),
  Module.Injective (ULift.{1} (ZMod q)) (Sec M U)

def LeafInjFlatZMod : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 M.obj, fun U y => ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x hx => ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ?_⟩, fun U _ => h U⟩
  have hx' : x = 0 := hx
  subst hx'
  exact map_zero _

instance resGE (q : ℕ) (i : ℤ) : (res (ZMod q) (tw q i)).IsStrictlyGE 0 := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem res_isTwRes (q : ℕ) [NeZero q] (i : ℤ) :
    IsTwRes q i (res (ZMod q) (tw q i)) (fun _ ζ => resGen i ζ) := by
  refine ⟨resGE q i, resAug (tw q i), ?_, fun U ζ => ?_⟩
  · unfold resAug
    exact (inferInstance : QuasiIso (injectiveResolution (tw q i)).ι')
  · simp only [resGen, resι, sglι, Sec.map]
    rfl

theorem res_flat (hA : LeafInjSecInj) (hB : LeafInjFlatZMod) (q : ℕ) [NeZero q] (j t : ℤ) :
    FlatS ((res (ZMod q) (tw q j)).X t) := by
  refine flatS_of_sec _ fun U => hB q _ ?_
  have : Injective ((res (ZMod q) (tw q j)).X t) := by
    unfold res; infer_instance
  exact hA q _ U

end LateralTheory.E.ZModFlatnessFromBaerCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of (h97 : TensTwRes) (hA : LeafInjSecInj) (hB : LeafInjFlatZMod) :
    LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := by
  intro q _ i j T τ hτ
  exact h97 q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) (res_isTwRes q i) (res_isTwRes q j)
    (res_flat hA hB q j) τ hτ
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafRootLocPf

def kpair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) : StandardEtalePair A where
  f := X ^ q - C u
  monic_f := monic_X_pow_sub_C _ (NeZero.ne q)
  g := X
  cond := ⟨C c * X, 0, q, by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    subst hk
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [show (C (((k + 1 : ℕ) : A)) * X ^ k) * (C c * X) = C (c * ((k + 1 : ℕ) : A)) * X ^ (k + 1) by
      rw [C_mul, pow_succ]; ring]
    rw [hc, C_1, one_mul]⟩

theorem kpair_root {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) :
    (kpair q c hc u).X ^ q = algebraMap A (kpair q c hc u).Ring u := by
  have h : aeval (kpair q c hc u).X (X ^ q - C u) = 0 := (kpair q c hc u).hasMap_X.1
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

theorem kpair_surj {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : Aˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (kpair q c hc (u : A)).Ring)) := by
  intro p
  let K := p.asIdeal.ResidueField
  let Ω := AlgebraicClosure K
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω u) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hu : IsUnit (algebraMap A Ω u) := u.isUnit.map _
  have hzu : IsUnit z := by
    rw [← hz] at hu; exact (isUnit_pow_iff (NeZero.ne q)).mp hu
  have hm : (kpair q c hc (u : A)).HasMap z := by
    refine ⟨?_, ?_⟩
    · simp [kpair, hz]
    · simpa [kpair] using hzu
  let ψ := (kpair q c hc (u : A)).lift z hm
  refine ⟨⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  ext1
  change Ideal.comap _ (RingHom.ker ψ.toRingHom) = p.asIdeal
  rw [RingHom.comap_ker, show ψ.toRingHom.comp (algebraMap A _) = algebraMap A Ω from ψ.comp_algebraMap]
  rw [IsScalarTower.algebraMap_eq A K Ω, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap K Ω).injective, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

theorem loc_of_cover {U Y : Scheme.{0}} (π : Y ⟶ U) [Etale π] [Surjective π]
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : ∀ (V : Scheme.{0}) (h : V ⟶ Y), P V (h ≫ π)) : Loc U P := by
  let 𝒰 : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => Y) (fun _ => π)
      (fun x => ⟨PUnit.unit, π.surjective x⟩) inferInstance
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V g hg
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact hP V h

theorem LeafRootLoc_of : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc := by
  intro q _ U hq u
  obtain ⟨c, hc⟩ := hq.exists_left_inv
  let P := kpair q c hc (u : Γ(U, ⊤))
  let B : CommRingCat.{0} := CommRingCat.of P.Ring
  let φ : Γ(U, ⊤) ⟶ B := CommRingCat.ofHom (algebraMap _ P.Ring)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨kpair_surj q c hc u⟩
  refine loc_of_cover (pullback.fst U.toSpecΓ (Spec.map φ)) _ fun V h => ?_
  have hX : IsUnit P.X := (isUnit_pow_iff (NeZero.ne q)).mp (by rw [kpair_root]; exact u.isUnit.map _)
  have e : (h ≫ pullback.snd _ _) ≫ Spec.map φ = (h ≫ pullback.fst _ _) ≫ U.toSpecΓ := by
    simp [pullback.condition]
  have hcomp : φ ≫ (Scheme.ΓSpecIso B).inv ≫ (h ≫ pullback.snd _ _).appTop = (h ≫ pullback.fst _ _).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop, e,
      Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨Units.map ((h ≫ pullback.snd _ _).appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom).toMonoidHom hX.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [← map_pow, kpair_root]
  exact congrArg (fun f => f.hom (u : Γ(U, ⊤))) hcomp

end LateralTheory.E.LeafRootLocPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ContPf

def PC (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

def ContAff : Prop := Hyp → ∀ (X : Scheme.{0}) [IsAffine X], PC X

def ContStep : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PC X

def ContInd : Prop := ∀ (P : Scheme.{0} → Prop), (∀ (X : Scheme.{0}) [IsAffine X], P X) →
  (∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X) →
  ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X], P X

theorem Cont_of (hMV : MV) (hA : ContAff) (hS : ContStep) (hI : ContInd) : Cont := by
  intro h q J _ _ D c hc ha hcs hqs hu n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have := hcs j0
  have := hqs j0
  have key : PC (D.obj j0) := hI PC (fun X _ => hA h X) (fun X U V hU hV hUV pU pV pW => hS h hMV X U V hU hV hUV pU pV pW)
    (D.obj j0)
  exact key q D c hc ha hcs hqs hu j0 ⟨Iso.refl _⟩ n i

end LateralTheory.E.ContPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.HZeroPf

open LateralTheory.E.t_E2Cut

def RootAIC : Prop := ∀ (q : ℕ) (X : Scheme.{0}), AICSch X → IsUnit (q : Γ(X, ⊤)) → Nonempty (Prim q Γ(X, ⊤))

def ResBij : Prop := ∀ (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X), ConnectedSpace Y → ConnectedSpace X →
  Nonempty (Prim q Γ(X, ⊤)) → Function.Bijective (Sec.res (F := tw q i) f)

theorem connected_of_AICSch {X : Scheme.{0}} (h : AICSch X) : ConnectedSpace X := by
  have := h.1
  infer_instance

theorem HZero_of (hR : RootAIC) (hB : ResBij) : LateralTheory.E.t_E2Cut.HZero := by
  intro hyp q Y X f hX hY hq i
  obtain ⟨_, e, he, _⟩ := hyp.a9 (ZMod q) (tw q i)
  have := connected_of_AICSch hX
  have hres := hB q i f hY (connected_of_AICSch hX) (hR q X hX hq)
  have key : (pull (ZMod q) (sch.map f) (tw q i) 0) = (e Y).toAddMonoidHom.comp
      ((AddMonoidHom.mk' (Sec.res (F := tw q i) f) (fun a b => map_add _ a b)).comp (e X).symm.toAddMonoidHom) := by
    ext x
    obtain ⟨s, rfl⟩ := (e X).surjective x
    simp [he]
  rw [key]
  exact (e Y).bijective.comp (hres.comp (e X).symm.bijective)

end LateralTheory.E.HZeroPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ZLGPf

variable {Y X S : Scheme.{0}}

abbrev overO (p : X ⟶ S) (U : S.Opens) : Scheme.{0} := pullback p U.ι

abbrev resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : overO p V ⟶ overO p U :=
  pullback.map p V.ι p U.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp)

abbrev fO (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : overO (f ≫ p) U ⟶ overO p U :=
  pullback.map (f ≫ p) U.ι p U.ι f (𝟙 _) (𝟙 _) (by simp) (by simp)

def Germ (q : ℕ) (i n : ℤ) (f : Y ⟶ X) (p : X ⟶ S) (s : S) : Prop :=
  (∀ (U : S.Opens), s ∈ U → ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ (U : S.Opens), s ∈ U → ∀ y : Ht q (sch.obj (overO (f ≫ p) U)) n i,
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ ∃ x : Ht q (sch.obj (overO p V)) n i,
      pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y)

def StalkGerm : Prop := Cont → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, ∀ s : S,
  Eqv _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) →
  ∀ n : ℤ, Germ q i n f p s

def ZarInd : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, (∀ (s : S) (n : ℤ), Germ q i n f p s) → Eqv _ (sch.map f) (tw q i)

theorem ZLG_of (hC : Cont) (hM : MV) (h1 : StalkGerm) (h2 : ZarInd) : ZLG := by
  intro hH q Y X S f p _ _ _ _ _ _ hq i hs
  exact h2 hM hH q f p hq i fun s n => h1 hC hH q f p hq i s (hs s) n

end LateralTheory.E.ZLGPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SteinPf
open LateralTheory.E.t_E2Cut

def RelNorm : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], AICSch Z →
  ∃ (T : Scheme.{0}) (c : Z ⟶ T) (k : T ⟶ S), IsIntegral T ∧ IsDominant c ∧ IsIntegralHom k ∧ c ≫ k = g ∧
    ∀ V : T.Opens, IsAffineOpen V → (V : Set T).Nonempty →
      ((c ⁻¹ᵁ V : Set Z).Nonempty ∧ Function.Injective (c.app V) ∧
        ∀ b : Γ(Z, c ⁻¹ᵁ V), (c.app V).hom.IsIntegralElem b → ∃ a, c.app V a = b)

def AICOpen : Prop := ∀ {Z : Scheme.{0}}, AICSch Z → ∀ W : Z.Opens, (W : Set Z).Nonempty → AIC Γ(Z, W)

theorem aic_of_int {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hB : AIC B) (hi : Function.Injective φ)
    (hc : ∀ b : B, φ.IsIntegralElem b → ∃ a, φ a = b) (hn : Nontrivial B) : AIC A := by
  intro p hm hd
  obtain ⟨b, hb⟩ := hB (p.map φ) (hm.map φ) (by rw [hm.natDegree_map]; exact hd)
  obtain ⟨a, rfl⟩ := hc b ⟨p, hm, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  refine ⟨a, hi ?_⟩
  rw [map_zero, ← Polynomial.eval_map_apply]; exact hb

theorem Stein_of (hR : RelNorm) (hA : AICOpen) : Stein := by
  intro Z S g _ _ hZ
  obtain ⟨T, c, k, hT, hc, hk, hck, hV⟩ := hR g hZ
  refine ⟨T, c, k, ⟨hT, fun V hV' hne => ?_⟩, hc, hk, hck⟩
  obtain ⟨hne', hi, hcl⟩ := hV V hV' hne
  have hB := hA hZ _ hne'
  have : IsIntegral Z := hZ.1
  have : Nonempty (c ⁻¹ᵁ V) := hne'.to_subtype
  exact aic_of_int (c.app V).hom hB hi hcl inferInstance

end LateralTheory.E.SteinPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineZeroCut

def LZNonempty : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)),
  UniversallyClosed p → Nonempty X → Nonempty ↑(pullback p (cpt A))

theorem lzNonempty : LZNonempty := by
  intro A _ _ X p hp hX
  obtain ⟨x⟩ := hX
  have hc : IsClosed (Set.range p.base) := p.isClosedMap.isClosed_range
  have h1 : IsLocalRing.closedPoint A ∈ Set.range p.base := by
    have : IsLocalRing.closedPoint A ∈ closure {p.base x} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).1 (IsLocalRing.le_maximalIdeal (p.base x).isPrime.ne_top)
    exact closure_minimal (by simp) hc this
  obtain ⟨z, hz⟩ := h1
  have h2 : (cpt A) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) = IsLocalRing.closedPoint A :=
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) :=
      (inferInstance : IsLocalHom (IsLocalRing.residue A))
    Spec_closedPoint
  obtain ⟨w, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := cpt A) z
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) (by rw [hz, h2])
  exact ⟨w⟩

end LateralTheory.E.LineZeroCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowCut

def Img : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → IsIntegral Z → ∃ (X₁ : Scheme.{0}) (h₁ : Z ⟶ X₁) (p₁ : X₁ ⟶ Spec (CommRingCat.of A)),
    IsIntegral X₁ ∧ IsProper p₁ ∧ IsIntegralHom h₁ ∧ IsDominant h₁ ∧ h₁ ≫ p₁ = h ≫ p

def ChowL : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (X' : Scheme.{0}) (π : X' ⟶ X₁) (U : X₁.Opens) (s : U.toScheme ⟶ X'),
    (U : Set X₁).Nonempty ∧ s ≫ π = U.ι ∧ IT π ∧ IT (π ≫ p₁)

def Norm : Prop := ∀ {Z W : Scheme.{0}} (f : W ⟶ Z) [QuasiSeparated f], AICSch Z →
  (∃ (U : Z.Opens) (s : U.toScheme ⟶ W), (U : Set Z).Nonempty ∧ s ≫ f = U.ι) →
  ∃ (Z' : Scheme.{0}) (v : Z' ⟶ W), IsIntegralHom v ∧ AICSch Z' ∧ IsDominant (v ≫ f)

theorem goal_of (hI : Img) (hC : ChowL) (hN : Norm) : LateralTheory.E.t_E2Cut.Chow := by
  intro A _ Z X h p _ hh hZ
  obtain ⟨X₁, h₁, p₁, hX₁, hp₁, hh₁, hd₁, e⟩ := hI A h p hh hZ.1
  have := hp₁
  have := hh₁
  have := hd₁
  obtain ⟨X', π, U, s, hU, hs, hπ, hπp⟩ := hC A p₁ hX₁
  obtain ⟨_, _⟩ := (hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip).qc
  have hU' : ((h₁ ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hxU, y, rfl⟩ := h₁.denseRange.inter_open_nonempty _ U.isOpen hU
    exact ⟨y, hxU⟩
  have sec : ∃ (V : Z.Opens) (t : V.toScheme ⟶ pullback h₁ π), (V : Set Z).Nonempty ∧ t ≫ pullback.fst h₁ π = V.ι :=
    ⟨h₁ ⁻¹ᵁ U, pullback.lift (h₁ ⁻¹ᵁ U).ι ((h₁ ∣_ U) ≫ s) (by rw [Category.assoc, hs, morphismRestrict_ι]), hU',
      pullback.lift_fst _ _ _⟩
  obtain ⟨Z', v, hv, hZ', hd⟩ := hN (pullback.fst h₁ π) hZ sec
  refine ⟨Z', v ≫ pullback.fst h₁ π, hZ', hd, hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip |>.pre v hv, ?_⟩
  have : (v ≫ pullback.fst h₁ π) ≫ h ≫ p = (v ≫ pullback.snd h₁ π) ≫ π ≫ p₁ := by
    rw [← e, Category.assoc, reassoc_of% pullback.condition, Category.assoc]
  rw [this]
  exact hπp.pre _ inferInstance

end LateralTheory.E.ChowCut

end
end
