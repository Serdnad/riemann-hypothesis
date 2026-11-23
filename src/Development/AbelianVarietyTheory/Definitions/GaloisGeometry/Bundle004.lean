module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD

namespace GlobalTheory.W1

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

def map1 : Ω[K⁄k] →ₗ[K] DR k L :=
  ((ι1 (R := k) (B := L)).restrictScalars K).comp (KaehlerDifferential.map k k K L)

set_option autoImplicit false in
open KaehlerDifferential in
variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] in
theorem _root_.GlobalTheory.W1.kaehlerOneFormsToExtensionDeRham_mul_self (ω : Ω[K⁄k]) :
    _root_.GlobalTheory.W1.map1 k K L ω * _root_.GlobalTheory.W1.map1 k K L ω = 0 := by
  unfold _root_.GlobalTheory.W1.map1 _root_.GlobalTheory.CechDR.ι1
  exact ExteriorAlgebra.ι_sq_zero _

def mapDR : DR k K →ₐ[K] DR k L := ExteriorAlgebra.lift K ⟨map1 k K L, kaehlerOneFormsToExtensionDeRham_mul_self k K L⟩

def IsTrDR (T : DR k L →ₗ[k] DR k K) : Prop :=
  ∀ (b : L) (ω : DR k K), T (b • mapDR k K L ω) = Algebra.trace K L b • ω


open scoped Classical in
open Classical in
def trDR : DR k L →ₗ[k] DR k K := if h : ∃ T, IsTrDR k K L T then h.choose else 0

variable {k K L} {ι : Type}

def trC (c : Finset ι → DR k L) : Finset ι → DR k K := fun s => trDR k K L (c s)

end GlobalTheory.W1
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u v' u' v'' u''

section Complex

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def OmF (q : ℕ) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (Om R (F.obj T) q)
  map φ := ModuleCat.ofHom (pOm F q φ)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_id F x)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_comp F φ ψ x)

def dOmNat (q : ℕ) : OmF F q ⟶ OmF F (q + 1) where
  app T := ModuleCat.ofHom (dOm R (F.obj T) q)
  naturality _ _ φ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ (pOm_dOm F φ x).symm)

abbrev Term (a q : ℕ) : Type (max u v) := CatH.Cn (OmF F q) a

abbrev dH (a q : ℕ) : Term F a q →ₗ[R] Term F (a + 1) q := CatH.d (OmF F q) a

def dV (a q : ℕ) : Term F a q →ₗ[R] Term F a (q + 1) :=
  (CatH.Mor.ofNatTrans (dOmNat F q)).pullC a

theorem dV_apply {a q : ℕ} (c : Term F a q) (s : ComposableArrows C a) :
    dV F a q c s = dOm R (F.obj (s.obj (Fin.last a))) q (c s) := rfl

abbrev Bidegree (n : ℕ) : Type := {p : ℕ × ℕ // p.1 + p.2 = n}

abbrev Tot (n : ℕ) : Type (max u v) := ∀ p : Bidegree n, Term F p.1.1 p.1.2

def totH (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, q), h⟩ => dH F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n)

def totV (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, q + 1), h⟩ => (-1 : ℤ) ^ a • (dV F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n))

def dTot (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) := totH F n + totV F n

section
variable {F} {n : ℕ} (c : Tot F n)

@[simp] theorem totH_zero {q : ℕ} (h : 0 + q = n + 1) : totH F n c ⟨(0, q), h⟩ = 0 := rfl

@[simp] theorem totH_succ {a q : ℕ} (h : a + 1 + q = n + 1) :
    totH F n c ⟨(a + 1, q), h⟩ = dH F a q (c ⟨(a, q), by omega⟩) := rfl

@[simp] theorem totV_succ {a q : ℕ} (h : a + (q + 1) = n + 1) :
    totV F n c ⟨(a, q + 1), h⟩ = (-1 : ℤ) ^ a • dV F a q (c ⟨(a, q), by omega⟩) := rfl

theorem dTot_apply (p : Bidegree (n + 1)) : dTot F n c p = totH F n c p + totV F n c p := rfl

end

def ZTot (n : ℕ) : Submodule R (Tot F n) := LinearMap.ker (dTot F n)

def BTot : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dTot F n)

def Hyp (n : ℕ) : Type (max u v) := ZTot F n ⧸ (BTot F n).submoduleOf (ZTot F n)

instance (n : ℕ) : AddCommGroup (Hyp F n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (n : ℕ) : Module R (Hyp F n) := inferInstanceAs (Module R (_ ⧸ _))

def Hyp.mk (n : ℕ) : ZTot F n →ₗ[R] Hyp F n := Submodule.mkQ _

theorem Hyp.mk_surjective (n : ℕ) : Function.Surjective (Hyp.mk F n) := Submodule.mkQ_surjective _


variable {F} in
theorem Hyp.mk_eq_zero {n : ℕ} {c : ZTot F n} : Hyp.mk F n c = 0 ↔ c.1 ∈ BTot F n :=
  Submodule.Quotient.mk_eq_zero _

def TotF (p n : ℕ) : Submodule R (Tot F n) where
  carrier := {c | ∀ b : Bidegree n, b.1.2 < p → c b = 0}
  add_mem' hc hc' b hb := by rw [Pi.add_apply, hc b hb, hc' b hb, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r c hc b hb := by rw [Pi.smul_apply, hc b hb, smul_zero]

theorem TotF_zero (n : ℕ) : TotF F 0 n = ⊤ :=
  eq_top_iff.2 fun _ _ _ hb ↦ absurd hb (Nat.not_lt_zero _)

theorem TotF_eq_bot {p n : ℕ} (h : n < p) : TotF F p n = ⊥ :=
  eq_bot_iff.2 fun _ hc ↦ funext fun b ↦ hc b (by have := b.2; omega)

def ZF (p n : ℕ) : Submodule R (Tot F n) := TotF F p n ⊓ ZTot F n

def BF (p : ℕ) : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => (TotF F p n).map (dTot F n)

theorem BF_le_BTot (p : ℕ) : ∀ n : ℕ, BF F p n ≤ BTot F n
  | 0 => le_rfl
  | _ + 1 => LinearMap.map_le_range

def HypF (p n : ℕ) : Type (max u v) := ZF F p n ⧸ (BF F p n).submoduleOf (ZF F p n)

instance (p n : ℕ) : AddCommGroup (HypF F p n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (p n : ℕ) : Module R (HypF F p n) := inferInstanceAs (Module R (_ ⧸ _))

def HypF.mk (p n : ℕ) : ZF F p n →ₗ[R] HypF F p n := Submodule.mkQ _

theorem HypF.mk_surjective (p n : ℕ) : Function.Surjective (HypF.mk F p n) :=
  Submodule.mkQ_surjective _


variable {F} in
theorem HypF.mk_eq_zero {p n : ℕ} {c : ZF F p n} : HypF.mk F p n c = 0 ↔ c.1 ∈ BF F p n :=
  Submodule.Quotient.mk_eq_zero _

def HypF.toHyp (p n : ℕ) : HypF F p n →ₗ[R] Hyp F n :=
  Submodule.mapQ _ _ (Submodule.inclusion inf_le_right) fun _ hc ↦ BF_le_BTot F p n hc

def Hyp.fil (p n : ℕ) : Submodule R (Hyp F n) := LinearMap.range (HypF.toHyp F p n)


variable {F} in
theorem Hyp.mem_fil {p n : ℕ} {x : Hyp F n} :
    x ∈ Hyp.fil F p n ↔ ∃ c : ZTot F n, c.1 ∈ TotF F p n ∧ Hyp.mk F n c = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n y
    exact ⟨⟨c.1, c.2.2⟩, c.2.1, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨HypF.mk F p n ⟨c.1, hc, c.2⟩, rfl⟩

theorem Hyp.fil_zero (n : ℕ) : Hyp.fil F 0 n = ⊤ := eq_top_iff.2 fun x _ ↦ by
  obtain ⟨c, rfl⟩ := Hyp.mk_surjective F n x
  exact Hyp.mem_fil.2 ⟨c, by rw [TotF_zero]; trivial, rfl⟩

theorem Hyp.fil_eq_bot {p n : ℕ} (h : n < p) : Hyp.fil F p n = ⊥ := eq_bot_iff.2 fun x hx ↦ by
  obtain ⟨c, hc, rfl⟩ := Hyp.mem_fil.1 hx
  rw [TotF_eq_bot F h] at hc
  rw [show c = 0 from Subtype.ext hc, map_zero]; rfl

theorem dH_lead {a p n : ℕ} (h : a + p = n) (c : ZF F p n) : dH F a p (c.1 ⟨(a, p), h⟩) = 0 := by
  have e := congrFun (show dTot F n c.1 = 0 from c.2.2) ⟨(a + 1, p), by omega⟩
  have hV : totV F n c.1 ⟨(a + 1, p), by omega⟩ = 0 := by
    rcases p with _ | p
    · rfl
    · rw [totV_succ, c.2.1 _ (Nat.lt_succ_self p), map_zero, smul_zero]
  rwa [dTot_apply, hV, add_zero] at e

end Complex

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

def omMor (q : ℕ) : CatH.Mor (OmF F q) (OmF F' q) σ where
  G := m.G
  τ T := qOm m q T
  nat φ x := qOm_pOm m φ x

abbrev pullTerm (a q : ℕ) : Term F a q →ₛₗ[σ] Term F' a q := (omMor m q).pullC a

def pullTot (n : ℕ) : Tot F n →ₛₗ[σ] Tot F' n where
  toFun c b := pullTerm m _ _ (c b)
  map_add' c c' := funext fun b ↦ map_add _ (c b) (c' b)
  map_smul' r c := funext fun b ↦ map_smulₛₗ (pullTerm m _ _) r (c b)

theorem pullTot_id {n : ℕ} (c : Tot F n) : pullTot (CoefMap.id F) n c = c :=
  funext fun b ↦ funext fun s ↦ SemiHom.mOm_id _ (fun _ ↦ rfl) (c b s)

theorem pullTot_comp (m' : CoefMap τ F' F'') {n : ℕ} (c : Tot F n) :
    pullTot (m.comp m') n c = pullTot m' n (pullTot m n c) :=
  funext fun b ↦ funext fun s ↦
    (SemiHom.mOm_mOm (semiHom_coef m _) (semiHom_coef m' _) _ (fun _ ↦ rfl)
      (c b (s ⋙ m'.G ⋙ m.G))).symm

end Pull

end GlobalTheory.HodgeCoh
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def castHQ {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : HQ l E n i ≃ₗ[ℚ_[l]] HQ l E n' i' := by
  subst hn; subst hi; exact LinearEquiv.refl _ _

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def idx (m : ℕ) (a : ℤ) : Finset ℕ := (Finset.range m).filter fun s => -a ≤ (s : ℤ) ∧ a + 2 * (s : ℤ) < m

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

def res (t : ℕ) (n i : ℤ) : HQ l (sch.obj (Ystr J t)) n i →ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J (t + 1))) n i :=
  ∑ j : Fin (t + 2), ((-1 : ℚ_[l]) ^ (j : ℕ)) • pullHQ l (sch.map (δ J t j)) n i

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

variable (a b w : ℤ)

end Galois

end GlobalTheory.EtC.WSS
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Sites
variable {Z Y U Z' Y' U' : Scheme.{0}}


set_option backward.isDefEq.respectTransparency.types false in
def bcSq {a : Z ⟶ Z'} {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (h : a ≫ i' = i ≫ b) :
    bc i' ⋙ bc a ≅ bc b ⋙ bc i :=
  (MorphismProperty.Over.pullbackComp a i').symm ≪≫ MorphismProperty.Over.pullbackCongr h ≪≫
    MorphismProperty.Over.pullbackComp i b


set_option backward.isDefEq.respectTransparency.types false in
def bcComp {f : U ⟶ Z} {g : Z ⟶ Y} {k : U ⟶ Y} (h : f ≫ g = k) : bc g ⋙ bc f ≅ bc k :=
  (MorphismProperty.Over.pullbackComp f g).symm ≪≫ MorphismProperty.Over.pullbackCongr h


set_option backward.isDefEq.respectTransparency.types false in
def bcFst (f : U ⟶ Y) : bc f ⋙ (Scheme.Etale.forget U ⋙ Over.forget U) ⟶ Scheme.Etale.forget Y ⋙ Over.forget Y where
  app V := pullback.fst V.hom f
  naturality V W g := pullback.lift_fst _ _ _

end Sites

variable (R : Type) [CommRing R]

section Functors
variable {Z Y U Z' Y' U' : Scheme.{0}}

instance (f : U ⟶ Y) : (bc f ⋙ (Scheme.Etale.forget U ⋙ Over.forget U)).IsContinuous Y.smallEtaleTopology
    Scheme.etaleTopology :=
  Functor.isContinuous_comp _ _ _ U.smallEtaleTopology _

def resUnit (f : U ⟶ Y) : Rel.res R Y ⟶ Rel.res R U ⋙ push R f :=
  Functor.sheafPushforwardContinuousNatTrans (bcFst f) _ _ _

def nb (i : Z ⟶ Y) (j : U ⟶ Y) : Shv R ⥤ ShvS R Z := Rel.res R U ⋙ push R j ⋙ Rel.pull R i

instance (X : Scheme.{0}) : (Rel.res R X).Additive where
  map_add := rfl

instance (i : Z ⟶ Y) (j : U ⟶ Y) : (nb R i j).Additive := by
  unfold nb; infer_instance

instance {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology] (i' : Z' ⟶ Y') :
    (bc i' ⋙ A).IsContinuous Y'.smallEtaleTopology Z.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Z'.smallEtaleTopology _

instance (i : Z ⟶ Y) (b : Y ⟶ Y') :
    (bc b ⋙ bc i).IsContinuous Y'.smallEtaleTopology Z.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

def pushSq {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) :
    push R i ⋙ push R b ⟶ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ ⋙ push R i' :=
  Functor.sheafPushforwardContinuousNatTrans α _ _ _

def bcMap {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) :
    push R b ⋙ Rel.pull R i' ⟶ Rel.pull R i ⋙ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ :=
  ((mateEquiv (adj (R := R) i) (adj (R := R) i')).symm (TwoSquare.mk _ _ _ _ (pushSq R α))).natTrans

def trans {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {j' : U' ⟶ Y'} {i : Z ⟶ Y} {j : U ⟶ Y} {b : Y ⟶ Y'} {c : U ⟶ U'}
    (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) (hc : c ≫ j' = j ≫ b) :
    nb R i' j' ⟶ nb R i j ⋙ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ :=
  Functor.whiskerRight (Functor.whiskerRight (resUnit R c) (push R j') ≫
      Functor.whiskerLeft (Rel.res R U) (pushSq R (bcSq hc).inv)) (Rel.pull R i') ≫
    Functor.whiskerLeft (Rel.res R U ⋙ push R j) (bcMap R α)

end Functors

end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

variable (R : Type) [CommRing R]

section Flat
variable {Z Y U Z' Y' U' : Scheme.{0}}

def nbC (i : Z ⟶ Y) (j : U ⟶ Y) (F : Shv R) : CochainComplex (ShvS R Z) ℤ :=
  ((nb R i j).mapHomologicalComplex _).obj (GlobalTheory.EtC.res R F)

def nbCMap (i : Z ⟶ Y) (j : U ⟶ Y) {F G : Shv R} (φ : F ⟶ G) : nbC R i j F ⟶ nbC R i j G :=
  ((nb R i j).mapHomologicalComplex _).map (resMap R φ)

end Flat

section HX
variable {Z Z' : Scheme.{0}}

end HX

end GlobalTheory.EtC.Psi
end
end
