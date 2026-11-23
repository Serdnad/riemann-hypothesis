module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle002
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle003
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle007
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat
public import Formalism.SharpRestriction.GrowthBounds.JointsLit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

section

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G

noncomputable section

namespace Formalism.L2.G.Cmp

section GlobalTheory

variable {K : Type} [Field K] {k n : ℕ}

theorem eval_rowAct (g : Matrix (Fin k) (Fin k) K) (f : MvPolynomial (Fin k × Fin n) K) (z : Matrix (Fin k) (Fin n) K) :
    eval (fun x => z x.1 x.2) (rowAct K g f) = eval (fun x => (g * z) x.1 x.2) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.mul_apply]

theorem even_block_row_action_eval (g : Matrix (Fin k) (Fin k) K) (e : ℤ) (f : MvPolynomial (Fin k × Fin k) K)
    (z : Matrix (Fin k) (Fin k) K) :
    z.det ^ e * eval (fun x => z x.1 x.2) (g.det ^ (-e) • rowAct K g⁻¹ f) =
      (g⁻¹ * z).det ^ e * eval (fun x => (g⁻¹ * z) x.1 x.2) f := by
  rw [MvPolynomial.smul_eval, eval_rowAct, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    mul_zpow, _root_.inv_zpow']
  ring

theorem even_block_weyl_mem {O : Type} [CommRing O] [Algebra O K] (hinj : Function.Injective (algebraMap O K)) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hF : F ∈ Dl0 O m lam (colSpan O g)) :
    ∃ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
        (g⁻¹ * z).det ^ lam (Fin.last m) * eval (fun x => (g⁻¹ * z) x.1 x.2) (map (algebraMap O K) f) := by
  rw [dw_eq hinj m lam hlam g hg] at hF
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.1 hF
  obtain ⟨f, hf, hfeq⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hF0)
  refine ⟨f, hf, fun z => ?_⟩
  have e1 : map (algebraMap O K) f = rowAct K g F0 := hfeq
  have key : eval (fun x => (g⁻¹ * z) x.1 x.2) (map (algebraMap O K) f) = eval (fun x => z x.1 x.2) F0 := by
    rw [e1, eval_rowAct, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, MvPolynomial.smul_eval]
  rw [key, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_zpow, _root_.inv_zpow']
  ring

def lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -lam i.rev

def revCol {m : ℕ} (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  z.submatrix id Fin.rev

def OddFact (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : Prop :=
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit g.det →
    (∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') ∧
    (∀ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ), ∃ F ∈ Dl0 O m lam (colSpan O g),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F')

end GlobalTheory

section Prod

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_prod (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (y : Formalism.L2.Forms.Frames G) :
    evC P h pos G M (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (F v s))) y =
      ∏ v, ∏ s : Fin (P.n' v), ((zAt P h pos M y.1 v s).det ^ (eAt P v s) *
        eval (fun x => zAt P h pos M y.1 v s x.1 x.2) (F v s)) := by
  simp only [evC, LinearMap.coe_mk, AddHom.coe_mk, map_prod, blockEmb, MvPolynomial.eval_rename]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

end Prod

end Formalism.L2.G.Cmp
end
end

section

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embFr (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) :
    ((D.fm u).lat 0).V →ₛₗ[D.what₂.embLL] ((D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ) where
  toFun x := fun cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z)
  map_add' x y := by funext cl z; rw [map_add (f := _)]; rfl
  map_smul' a x := by funext cl z; rw [LinearMap.map_smulₛₗ]; rfl

structure CmpIn (D : D7) (X : Formalism.L2.Herm.Herm0 D) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B
  fr_B : ∀ u w hg, FrRat X u w hg B

variable {X : Formalism.L2.Herm.Herm0 D}

def cmpRec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V → (D.gat u w hg).Fn :=
  cmpC ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg) (I.embW u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

structure CmpHyp (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  uniq : ∀ u w hg, ValUniq ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (fun a => cmpRec T Gt I u w hg (((D.fm u).lat 0).b a))

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

def latCmpC (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) : LatCmp D where
  embW := I.embW
  embW_int := I.embW_int
  cmp := fun u w hg => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).toAddMonoidHom
  cmp_smul := fun u w hg a x => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).map_smulₛₗ a x
  cmp_li := H.li
  cmp_M := H.latM

def latticeComparisonCompatible (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) :
    CmpTied D X T Gt (latCmpC T Gt I H) where
  B := I.B
  B_std := I.B_std
  fr_B := I.fr_B
  tie := fun u w hg => cmpC_tie (tEL D) (H.ex u w hg) (H.pos u w hg) (H.chi u w hg)

end Formalism.L2.G.Cmp

end
end

section

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reGL_apply {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) (x y : Fin b) :
    (reGL h R g : Matrix (Fin b) (Fin b) R) x y = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm x) (Fin.cast h.symm y) := by
  rfl

theorem reGL_mem_UJ {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (g : GL (Fin a) R)
    (hg : g ∈ UJ σ J) : reGL h R g ∈ UJ σ J' := by
  subst h
  have hJ' : J' = J := by
    ext x y
    rw [hJ]
    simp
  subst hJ'
  have hg' : reGL rfl R g = g := by
    ext x y
    rw [reGL_apply]
    simp
  rw [hg']
  exact hg

theorem LocAt.actB_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ}
    {G : GAtP p} (A : LocAt F E n G) {k : ℕ} (hk : k = n) (B0 : GL (Fin k) E) (γ0 : ∀ i, (G.lev i).Γ → GL (Fin k) E)
    (hB : A.B = reGL hk E B0) (hγ : ∀ i γ, A.gamI i γ = reGL hk E (γ0 i γ))
    (hact : ∀ i v (γ : (G.lev i).Γ) (a b : Fin (G.P.m + 1)) (a' b' : Fin k), (a : ℕ) = a' → (b : ℕ) = b' →
      A.eQ v (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) a b) =
        (((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a' b') :
    A.ActB := by
  intro i v γ
  have key : ((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) =
      bc (A.phE v) (B0⁻¹ * γ0 i γ * B0) := by
    simp only [map_mul, map_inv]
  have key2 : (A.B⁻¹ * A.gamI i γ * A.B : GL (Fin n) E) = reGL hk E (B0⁻¹ * γ0 i γ * B0) := by
    rw [hB, hγ]
    simp only [map_mul, map_inv]
  have hiw : ∀ z, A.eQ v (A.iw v z) = A.phE v z := fun z => by
    simp [LocAt.iw]
  ext x y
  apply (A.eQ v).injective
  have h1 := hact i v γ (Fin.cast A.rk.symm x) (Fin.cast A.rk.symm y) (Fin.cast hk.symm x)
    (Fin.cast hk.symm y) rfl rfl
  rw [key] at h1
  rw [key2]
  exact h1.trans (hiw _).symm

variable {D : D7}

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem gramN_zero (D : D7) (x y : Fin (D.R.N 0)) :
    gramN D 0 (Nat.zero_le _) x y = D.sp.gram0 (Fin.cast (rank_eq_first_level D.R).symm x) (Fin.cast (rank_eq_first_level D.R).symm y) := rfl

variable {X : Formalism.L2.Herm.Herm0 D}

theorem locAt_UJ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) :
    (locAt X u w hg B).gamI i γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by
  exact reGL_mem_UJ (rank_eq_first_level D.R) (sigD D : D.host.E →+* D.host.E) D.sp.gram0 _ (fun x y => gramN_zero D x y) _
    ((X.g u w hg).gamI i γ).2



theorem locAt_actB (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B) : (locAt X u w hg B).ActB := by
  refine LocAt.actB_of (locAt X u w hg B) (rank_eq_first_level D.R) B
    (fun i γ => ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) rfl (fun i γ => rfl) ?_
  intro i v γ a b a' b' ha hb
  have h1 := (X.g u w hg).act_eq i v _ rfl ((X.g u w hg).pl v).2 γ a b a' b' ha hb
  rw [hB _ ((X.g u w hg).pl v).2] at h1
  have hbc : bc ((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom)
      (bc (inclE (F := D.host.F) _) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom).comp
        (inclE (F := D.host.F) _)) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E) := by
    ext x y
    rfl
  rw [hbc] at h1
  exact h1

theorem locAt_std (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (hB : StdB D B) :
    cT (sigD D : D.host.E →+* D.host.E) (locAt X u w hg B).B.1 * gramN D 0 (Nat.zero_le _) * (locAt X u w hg B).B.1 = 1 := by
  exact hB.1

end Formalism.L2.G.Cmp

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)

def clsR (i : compL L p) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : C.cls 0 :=
  clsOf L (clsC I hdet hk i Lt)

include hH in
theorem stab_card1 (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v)) :
    Nat.card {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt = Lt} =
      Nat.card (C.stab 0 (clsR hk I hdet i Lt)) := by
  have h1 := (Nat.card_congr (fixEquiv hS r lam0 dom hk I ψ hdet hH i y hy (gOf Lt))).trans (card_stabU _)
  rw [← gOf_spec Lt h] at h1
  exact h1

include hH hdet in
theorem trivStab1 (hT : TrivStabU L) (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y = (repP L p i).1) (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v))
    (hfix : (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt = Lt) :
    γ = 1 := by
  rw [level_action_lattice_eq] at hfix
  have h1 := (fix_iff hk I hdet hH i (gOf Lt) γ.1).2 ⟨hy ▸ γ.2, by rw [← gOf_spec Lt h]; exact hfix⟩
  exact Subtype.ext (hT _ _ h1)



include hH in
theorem clsR_iff (i i' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt Lt' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt)
    (h' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt') :
    clsR hk I hdet i Lt = clsR hk I hdet i' Lt' ↔
      i = i' ∧ ∃ γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ,
        Lt' = ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt :=
  clsOf_inj.eq_iff.trans (clsC_iff hS r lam0 dom hk I ψ e hdet hH i i' Lt Lt' h h')


include hH in
theorem clsR_surj (c : C.cls 0) :
    ∃ (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp) (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup),
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt ∧ clsR hk I hdet i Lt = c := by
  obtain ⟨c', rfl⟩ := clsOf_surj (L := L) c
  obtain ⟨i, Lt, h1, h2⟩ := clsC_surj hS r lam0 dom hk I ψ e hdet hH c'
  exact ⟨i, Lt, h1, congrArg (clsOf L) h2⟩



include hH in
theorem stab_card (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt) :
    Nat.card {γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ //
      ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt = Lt} = Nat.card (C.stab 0 (clsR hk I hdet i Lt)) :=
  stab_card1 hS r lam0 dom hk I ψ hdet hH i _ rfl Lt h



include hH hdet in
theorem trivStab (hT : TrivStabU L) : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).TrivStab :=
  fun i γ Lt h hfix => trivStab1 hS r lam0 dom hk I ψ hdet hH hT i _ rfl γ Lt h hfix

end Formalism.L2.G.Cmp
end
end

section

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Rat

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem li_step (j : ℕ) (f : ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j)
    (hinj : Function.Injective f)
    (hrat : ∀ x, RatFnP (Fl.Pj j) (Lv.comp j) (c.embW u w h) (f x)) :
    LinearIndependent (D.gat u w h).Kf fun a => f (((Tw.fm u (D.what₂.muAt w)).lat j).b a) := by
  refine li_of_rat (e := c.embW u w h) (ev := evP (P := Fl.Pj j) (α := Lv.comp j)) (cmp := f.toAddMonoidHom)
    ?_ (fun a x => f.map_smulₛₗ a x) ?_ hinj _
    ((Tw.fm u (D.what₂.muAt w)).lat j).b.linearIndependent
  · intro F hF
    funext a L
    ext m
    simpa [evP] using hF (a, L, m)
  · intro x t
    obtain ⟨Q, hQ⟩ := hrat x t.1 t.2.1
    exact ⟨Q.coeff t.2.2, by simp [evP, ← hQ, MvPolynomial.coeff_map]⟩

def CmpUp.ofRat (cmpS : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1))
    (injS : ∀ j, j + 1 ≤ D.R.m → Function.Injective (cmpS j))
    (ratS : ∀ j, j + 1 ≤ D.R.m → ∀ x, RatFnP (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (cmpS j x)) :
    CmpUp c Tw u w h Lv where
  cmpS := cmpS
  liS := fun j hj => li_step (j + 1) (cmpS j) (injS j hj) (ratS j hj)

end Rat

section Forced

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

variable [Fact (D.what₂.places.resChar w).Prime] {Gt : GatTies D} {Ch : Chain Lv}

end Forced

end Formalism.L2.G.Cmp

end
end

section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

variable {D : D7} (c : LatCmp D)

theorem yvRat (h : ValRat c) : Formalism.MainNotions.G.Joints.Lit.YvRat c :=
  fun u w hg v => yvRat_of_valRat c h u w hg v

theorem npDesc_of_valRat {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (hv : c.VramDef Y) (h : ValRat c) : c.NPDesc X Y K :=
  Formalism.MainNotions.G.Joints.Lit.NPDesc_of c hT X Y K hv (yvRat c h)

end Formalism.L2.G.Cmp
end
