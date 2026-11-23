module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.Divisibility.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosets
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle043
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
variable {k : Type} [CommRing k] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {s'' : X'' ⟶ Sp k} {f : X' ⟶ X} {g : X'' ⟶ X'}

theorem formPull_formPull (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (U : X.Opens) (j : ℕ) (x : OmU s U j) :
    formPull hg (f ⁻¹ᵁ U) j (formPull hf U j x) = formPull hgf U j x := by
  refine SemiHom.mOm_mOm (semiHom_appSec hf U) (semiHom_appSec hg (f ⁻¹ᵁ U))
    (semiHom_appSec hgf U) (fun b ↦ ?_) x
  change (f.app U ≫ g.app (f ⁻¹ᵁ U)).hom b = ((g ≫ f).app U).hom b
  rw [Scheme.Hom.comp_app]
  rfl

theorem omega_hom_ext {j : ℕ} {M : X.Modules} (φ ψ : Omega s j ⟶ M)
    (h : ∀ (U : X.Opens) (x : OmU s U j), φ.val.app (op U) ((toOmega s j).app (op U) x) =
      ψ.val.app (op U) ((toOmega s j).app (op U) x)) : φ = ψ := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  have e₁ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M φ
  have e₂ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M ψ
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  ext U x
  exact h U.unop x

theorem omegaPull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j : ℕ) :
    omegaPull hgf j = omegaPull hf j ≫ (Scheme.Modules.pushforward f).map (omegaPull hg j) := by
  refine omega_hom_ext _ _ fun U x ↦ ?_
  rw [omegaPull_toOmega]
  change _ = (omegaPull hg j).val.app (op (f ⁻¹ᵁ U)) ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x))
  rw [omegaPull_toOmega, omegaPull_toOmega, formPull_formPull hf hg hgf]
  rfl

theorem hodgePull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j q : ℕ) (x : hodgeH s j q) :
    hodgePull hg j q (hodgePull hf j q x) = hodgePull hgf j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ s''
  apply (cohOn.toH' (Omega s'' j) ⊤ q).injective
  have e₁ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hg) (omegaPull hg j)
    (le_refl (g ⁻¹ᵁ ⊤)) (hodgePull hf j q x)
  have e₂ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hf) (omegaPull hf j)
    (le_refl (f ⁻¹ᵁ ⊤)) x
  have e₃ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hgf) (omegaPull hgf j)
    (le_refl ((g ≫ f) ⁻¹ᵁ ⊤)) x
  refine e₁.trans (Eq.trans ?_ e₃.symm)
  refine (congrArg (SheafPull.pull.{0, 0} g.base (toAbSheafPush (omegaPull hg j)) q _) e₂).trans ?_
  refine (SheafPull.pull_pull.{0, 0, 0} f.base g.base _ _ q _ _ _).trans ?_
  rw [omegaPull_comp hf hg hgf]
  rfl

theorem hodgePull_hodgePull {X X' X'' : Scheme.{0}} (s : X ⟶ Sp k) (f : X' ⟶ X)
    (g : X'' ⟶ X') (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (s' := g ≫ f ≫ s) rfl j q (hodgePull (s' := f ≫ s) rfl j q x) =
      hodgePull (f := g ≫ f) (s' := g ≫ f ≫ s) (Category.assoc g f s) j q x :=
  hodgePull_comp rfl rfl (Category.assoc g f s) j q x

end GlobalTheory.HodgeCoh
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

section CyclicComplexMaps

variable {R : Type} [CommRing R]

theorem chainMap_f {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) (p : ℕ) :
    (chainsXIso R (sch.obj X) p).inv ≫ (chainMap R t).f (-(p : ℤ)) = t ≫ (chainsXIso R (sch.obj Z) p).inv := by
  have h1 : (chainMap R t).f (-(p : ℤ)) =
      (chainsXIso R (sch.obj X) p).hom ≫ ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simpMap R t)).f p ≫
        (chainsXIso R (sch.obj Z) p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

theorem ev_chainMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) {I : Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj Z)) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (y : Sx (sch.obj X) p U) :
    ev ((Cochain.ofHom (chainMap R t)).comp α (zero_add n)) p s h U y =
      Sec.map ((chainsXIso R (sch.obj Z) p).inv ≫ α.v _ _ h) (Sec.map t (freeGen R (yoneda.obj X) U y)) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainMap_f]
  rfl

end CyclicComplexMaps

section Key

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem secMap_sum {F G : Shv R} {ι : Type*} (s : Finset ι) (g : ι → (F ⟶ G)) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (∑ j ∈ s, g j) a = ∑ j ∈ s, Sec.map (g j) a :=
  map_sum (mapHom F G a) g s

theorem exists_free_restr (P : PSh) : ∃ ι : (free R).obj P ⟶ (restr φ).obj ((free S).obj P),
    ∀ U x, Sec.map ι (freeGen R P U x) = (show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x) :=
  free_exists P _ (fun U x => show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x)
    (fun V U g x => freeGen_res P g x)

theorem isTransfer_reduce {Z X : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z} (ht : IsTransfer R f t)
    (ι : freeSch R Z ⟶ (restr φ).obj (freeSch S Z))
    (hι : ∀ U x, Sec.map ι (freeGen R (yoneda.obj Z) U x) =
      (show Sec ((restr φ).obj (freeSch S Z)) U from freeGen S (yoneda.obj Z) U x))
    (t' : freeSch S X ⟶ freeSch S Z)
    (ht' : ∀ U x, Sec.map t' (freeGen S (yoneda.obj X) U x) =
      (show Sec (freeSch S Z) U from Sec.map ι (Sec.map t (freeGen R (yoneda.obj X) U x)))) :
    IsTransfer S f t' := by
  intro T x m s hs hiso
  apply free_ext
  intro V w
  have e := congrArg (fun g => Sec.map ι (Sec.map g (freeGen R (yoneda.obj T) V w))) (ht T x m s hs hiso)
  change Sec.map ι (Sec.map t (Sec.map ((free R).map (yoneda.map x)) (freeGen R (yoneda.obj T) V w))) =
    Sec.map ι (Sec.map (∑ j, (free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) at e
  change Sec.map t' (Sec.map ((free S).map (yoneda.map x)) (freeGen S (yoneda.obj T) V w)) =
    Sec.map (∑ j, (free S).map (yoneda.map (s j))) (freeGen S (yoneda.obj T) V w)
  rw [freeGen_map, ht']
  rw [freeGen_map] at e
  refine e.trans ?_
  rw [secMap_sum, secMap_sum]
  refine (map_sum (ι.hom.app (op V)).hom _ Finset.univ).trans (Finset.sum_congr rfl fun j _ => ?_)
  change Sec.map ι (Sec.map ((free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) = _
  rw [freeGen_map, freeGen_map, hι]

theorem key_free {Z X : Scheme.{0}} {f : Z ⟶ X} {I : Shv R} {J : Shv S} (A : freeSch R Z ⟶ I) (B : freeSch S Z ⟶ J)
    (ρ' : I ⟶ (restr φ).obj J)
    (hAB : ∀ V z, Sec.map B (freeGen S (yoneda.obj Z) V z) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z)))
    {tR : freeSch R X ⟶ freeSch R Z} (htR : IsTransfer R f tR) {tS : freeSch S X ⟶ freeSch S Z}
    (huniq : ∀ t, IsTransfer S f t → t = tS) (U : Scheme.{0}) (y : U ⟶ X) :
    Sec.map B (Sec.map tS (freeGen S (yoneda.obj X) U y)) =
      Sec.map ρ' (Sec.map A (Sec.map tR (freeGen R (yoneda.obj X) U y))) := by
  obtain ⟨ι, hι⟩ := exists_free_restr φ (yoneda.obj Z)
  obtain ⟨t', ht'⟩ := free_exists (R := S) (yoneda.obj X) (freeSch S Z)
    (fun U y => show Sec (freeSch S Z) U from Sec.map ι (Sec.map tR (freeGen R (yoneda.obj X) U y)))
    (fun V U g y => by
      refine (map_res ι g _).trans ?_
      change Sec.map ι (Sec.res g (Sec.map tR (freeGen R (yoneda.obj X) U y))) = _
      rw [map_res, freeGen_res])
  have hT := huniq t' (isTransfer_reduce φ htR ι hι t' ht')
  subst hT
  rw [ht']
  have hm : ι ≫ (restr φ).map B = A ≫ ρ' := free_ext _ _ (fun V z => by
    change Sec.map B (Sec.map ι (freeGen R (yoneda.obj Z) V z)) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z))
    rw [hι]
    exact hAB V z)
  exact congrArg (fun g => Sec.map g (Sec.map tR (freeGen R (yoneda.obj X) U y))) hm

end Key

theorem redCompat_of_finite_etale (l : ℕ) [Fact l.Prime] {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (hex : ∀ (R : Type) [CommRing R], ∃! t, IsTransfer R f t) (n i : ℤ) : RedCompat l f n i := by
  intro k x
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl⟩
  have hd : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨t0, ht0, -⟩ := hex (ZMod (l ^ (k + 1)))
  have htQ := transfer_spec (ZMod (l ^ (k + 1))) ⟨t0, ht0⟩
  obtain ⟨t1, ht1, hu1⟩ := hex (ZMod (l ^ k))
  have huniq : ∀ t, IsTransfer (ZMod (l ^ k)) f t → t = transfer (ZMod (l ^ k)) f := fun t ht =>
    (hu1 t ht).trans (hu1 _ (transfer_spec _ ⟨t1, ht1⟩)).symm
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (redMap (l ^ (k + 1)) (l ^ k) i).image_exists (sch.obj Z) n α
  have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj Z) n i (CohomologyClass.mk α) = CohomologyClass.mk β :=
    (redMap (l ^ (k + 1)) (l ^ k) i).op_spec _ n α β hβ
  rw [h1]
  have key := (redMap (l ^ (k + 1)) (l ^ k) i).op_spec (sch.obj X) n
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) α (zero_add n))
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) β (zero_add n)) (by
      intro p s h U y
      change ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp β.1 (zero_add n)) p s h U y =
        (redMap (l ^ (k + 1)) (l ^ k) i).app U s
          (ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp α.1 (zero_add n)) p s h U y)
      rw [ev_chainMap, ev_chainMap]
      exact key_free (ZMod.castHom hd (ZMod (l ^ k))) _ _
        (ScalarExt.semiHom (redMap (l ^ (k + 1)) (l ^ k) i) (ScalarExt.zmod_semilinear hd _) s)
        (fun V z => (ev_def β.1 p s h V z).symm.trans ((hβ p s h V z).trans (congrArg _ (ev_def α.1 p s h V z))))
        htQ huniq U y)
  exact key

end GlobalTheory.EtC.Tr
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.BlockRename

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  {f : γ' → γ} {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]


omit [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in
theorem blk_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (j : n) : blk e j = f (blk e₂ j) := by
  obtain ⟨⟨c', x⟩, rfl⟩ := e₂.surjective j
  calc
    blk e (e₂ ⟨c', x⟩) = f c' := by rw [he]; simp [blk]
    _ = f (blk e₂ (e₂ ⟨c', x⟩)) := by simp [blk]


omit [Fintype γ] [Fintype γ'] [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in
theorem mem_parab_rename (hf : StrictMono f) {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (g : GL n k) : g ∈ parab k e ↔ g ∈ parab k e₂ := by
  simp only [mem_parab, blk_rename he, hf.lt_iff_lt]


omit [∀ c, DecidableEq (m c)] in
theorem modExp_rename (hf : StrictMono f) (hs : Function.Surjective f) (c' : γ') :
    modExp (fun c' => m (f c')) c' = modExp m (f c') := by
  unfold modExp
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  congr 1
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl

theorem deltaHalf_rename (hf : StrictMono f) (hs : Function.Surjective f) (g : Levi k m) :
    deltaHalf k (fun c' => m (f c')) (fun c' => g (f c')) = deltaHalf k m g := by
  rw [deltaHalf_apply, deltaHalf_apply]
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  exact Fintype.prod_equiv E _ _ fun c' => by rw [modExp_rename hf hs]; rfl

theorem leviProj_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (p : parab k e₂) (q : parab k e) (hpq : (p : GL n k) = q) :
    leviProj k e₂ p = fun c' => leviProj k e q (f c') := by
  funext c'
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, leviProj_apply, he, he, hpq]

def kappa (hf : StrictMono f) (hs : Function.Surjective f) (X : γ → Type) [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] : (⨂[ℂ] c, X c) ≃ₗ[ℂ] ⨂[ℂ] c', X (f c') :=
  PiTensorProduct.reindex ℂ X (Equiv.ofBijective f ⟨hf.injective, hs⟩).symm

theorem kappa_tprod (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type} [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] (x : ∀ c, X c) :
    kappa hf hs X (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun c' => x (f c') := by
  exact PiTensorProduct.reindex_tprod (R := ℂ) (s := X) _ x

theorem piTensor_rename (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type}
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c))
    (g : Levi k m) (w : ⨂[ℂ] c, X c) :
    piTensor (fun c' => σ (f c')) (fun c' => g (f c')) (kappa hf hs X w) = kappa hf hs X (piTensor σ g w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp only [map_smul, kappa_tprod, piTensor_tprod]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.SmGL.BlockRename

namespace GlobalTheory.SmGL.BlockRename

theorem multiProd_rename : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  intro k _ _ _ _ γ γ' n _ _ _ _ _ _ f hf hs m _ _ e e₂ he X _ _ σ
  let κ := kappa hf hs X
  have key : ∀ (p : parab k e₂) (q : parab k e), (p : GL n k) = q → ∀ w,
      ((twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂)) p (κ w) =
        κ (((twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e)) q w) := by
    intro p q hpq w
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, leviProj_rename he p q hpq, twist_apply, twist_apply,
      deltaHalf_rename hf hs, piTensor_rename hf hs]
    exact (map_smul κ _ _).symm
  have hP := mem_parab_rename (k := k) hf he
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (τ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (MonoidHom.id _) continuous_id κ.toLinearMap fun p => ⟨⟨p, (hP p).2 p.2⟩, rfl, fun w => key p _ rfl w⟩)
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (τ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (MonoidHom.id _) continuous_id κ.symm.toLinearMap fun q => ⟨⟨q, (hP q).1 q.2⟩, rfl, fun w =>
        κ.injective (by
          simp only [LinearEquiv.coe_coe]
          rw [LinearEquiv.apply_symm_apply, ← key ⟨q, (hP q).1 q.2⟩ q rfl, LinearEquiv.apply_symm_apply])⟩) ?_ ?_) fun g => ?_⟩
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.apply_symm_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.symm_apply_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => rfl))

end GlobalTheory.SmGL.BlockRename
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitSieve_mem_of_fibrePointsLE : ∀ (n : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    FibrePointsLE f n → splitSieve f (𝟙 X) ∈ Scheme.etaleTopology X := by
  intro n
  induction n with
  | zero =>
    intro Z X f _ _ h
    have : IsEmpty Z := GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero f h
    have hs : Splits f (𝟙 X ≫ 𝟙 X) := GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f _ (Function.isEmpty (pullback.fst f (𝟙 X ≫ 𝟙 X)))
    have hmem : splitSieve f (𝟙 X) (𝟙 X) := ⟨X, 𝟙 X, 𝟙 X, hs, Category.id_comp _⟩
    rw [Sieve.id_mem_iff_eq_top] at hmem
    rw [hmem]; exact (Scheme.etaleTopology).top_mem X
  | succ n ih =>
    intro Z X f _ _ h
    obtain ⟨hfin, het⟩ := GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale f
    have hg := ih (diagComplHom f) (GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection f n h)
    refine GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale f _ ?_ (fun {V} v hv => ?_)
    · refine (Scheme.etaleTopology).superset_covering ?_ hg
      rintro V u ⟨W, w, v, hv, rfl⟩
      have h1 : Splits (pullback.snd f f) (v ≫ 𝟙 Z) := GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement f _ hv
      have h2 : Splits f ((v ≫ 𝟙 Z) ≫ f) := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f f _ h1
      exact ⟨W, w, v ≫ f, by simpa using h2, by simp⟩
    · exact ⟨V, 𝟙 V, v, by simpa using GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f v hv, Category.id_comp _⟩

theorem splitSieve_mem : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X),
    splitSieve f x ∈ Scheme.etaleTopology S := by
  intro Z X S f _ _ x
  let 𝒰 := S.affineCover
  have hU : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.etaleTopology S :=
    Scheme.zariskiTopology_le_etaleTopology _ (𝒰.mem_grothendieckTopology)
  refine (Scheme.etaleTopology).transitive hU _ ?_
  rintro Y u ⟨W, w, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable w ?_
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine (pullback.snd f (𝒰.f i ≫ x))
  have hi := splitSieve_mem_of_fibrePointsLE n (pullback.snd f (𝒰.f i ≫ x)) hn
  refine (Scheme.etaleTopology).superset_covering ?_ hi
  rintro V u ⟨W', w', v, hv, rfl⟩
  have h1 := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f (𝒰.f i ≫ x) (v ≫ 𝟙 _) hv
  exact ⟨W', w', v ≫ 𝒰.f i, by simpa using h1, by simp⟩

end GlobalTheory.EtC.Tr
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory

theorem cmData_sig_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  intro F E _ _ _ _ _ _ hc
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => (hc.fixed e).1 he⟩
  have hs : Function.Surjective (algebraMap F E) := fun e => (hc.fixed e).1 (AlgHom.congr_fun h0 e)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩)).symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.finite_image_heckeSet_split_place_cosets : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)), (∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → κ ∈ J) → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (NumberField.maximalRealSubfield L)) (k : ℕ), Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFinCong.finite_image_tSet_cong | exact GlobalTheory.TSetFinCong.finite_image_tSet_cong | (intros; apply GlobalTheory.TSetFinCong.finite_image_tSet_cong <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  first | exact @GlobalTheory.LatticeDuality.dual_subset | exact GlobalTheory.LatticeDuality.dual_subset | (intros; apply GlobalTheory.LatticeDuality.dual_subset <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.SplitDetermines

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_unr (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) : A.unr (spehLoc N A p w) := by
  unfold spehLoc
  induction List.range p.d with
  | nil => exact A.lpZero_unr w
  | cons k l ih => exact (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 h, ih⟩

theorem isoLoc_unr_ae (P : List (Part A.CG)) : ∀ᶠ w in Filter.cofinite, A.unr (isoLoc N A P w) := by
  induction P with
  | nil => exact Filter.Eventually.of_forall fun w => A.lpZero_unr w
  | cons p P ih =>
    filter_upwards [ih, A.locG_unr_ae p.π] with w h1 h2
    exact (A.unr_sum _ _).2 ⟨spehLoc_unr N A p w h2, h1⟩

end GlobalTheory.SplitDetermines

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

end GlobalTheory.RowTie
end
end
