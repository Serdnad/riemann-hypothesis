module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle005
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle002
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOf
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle002
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.HermitianColumns.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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

def StabU (L : ColLevel R F E sp gp C A clsLat) (x : GA sp) : Type :=
  {γ : UJ (sp.cm.sig : E →+* E) sp.gram0 // x⁻¹ * ratA sp γ * x ∈ KA L}

def TrivStabU (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (x : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0), x⁻¹ * ratA sp γ * x ∈ KA L → γ = 1

def stabConj (x x' : GA sp) (h0 : UJ (sp.cm.sig : E →+* E) sp.gram0) (κ : GA sp) (hκ : κ ∈ KA L)
    (e : x' = ratA sp h0 * x * κ) : StabU L x ≃ StabU L x' where
  toFun γ := ⟨h0 * γ.1 * h0⁻¹, by
    have : x'⁻¹ * ratA sp (h0 * γ.1 * h0⁻¹) * x' = κ⁻¹ * (x⁻¹ * ratA sp γ.1 * x) * κ := by
      rw [e, map_mul, map_mul, map_inv]; group
    rw [this]
    exact (KA L).mul_mem ((KA L).mul_mem ((KA L).inv_mem hκ) γ.2) hκ⟩
  invFun γ := ⟨h0⁻¹ * γ.1 * h0, by
    have key : ∀ γ0 : UJ (sp.cm.sig : E →+* E) sp.gram0,
        x⁻¹ * ratA sp (h0⁻¹ * γ0 * h0) * x = κ * (x'⁻¹ * ratA sp γ0 * x') * κ⁻¹ := by
      intro γ0
      rw [e, map_mul, map_mul, map_inv]; group
    rw [key]
    exact (KA L).mul_mem ((KA L).mul_mem hκ γ.2) ((KA L).inv_mem hκ)⟩
  left_inv γ := Subtype.ext (by show h0⁻¹ * (h0 * γ.1 * h0⁻¹) * h0 = γ.1; group)
  right_inv γ := Subtype.ext (by show h0 * (h0⁻¹ * γ.1 * h0) * h0⁻¹ = γ.1; group)

def stabRec (c : C.cls 0) : C.stab 0 c ≃ StabU L (L.y c) :=
  Equiv.ofBijective (fun s => ⟨L.stabI c s, by
      have h := (L.stabI_range c (L.stabI c s : GL (Fin R.k) E) (L.stabI c s).2).1 ⟨s, rfl⟩
      exact (mem_map_conj L.U _ _).1 h⟩)
    ⟨fun a b hab => L.stabI_inj c (congrArg Subtype.val hab), fun γ => by
      obtain ⟨s, hs⟩ := (L.stabI_range c (γ.1 : GL (Fin R.k) E) γ.1.2).2 ((mem_map_conj L.U _ _).2 γ.2)
      exact ⟨s, Subtype.ext hs⟩⟩

def clsOf (L : ColLevel R F E sp gp C A clsLat) (c : ClassSet (HA sp) (KA L)) : C.cls 0 :=
  (Equiv.ofBijective _ L.y_bij).symm c

theorem clsOf_spec (c : ClassSet (HA sp) (KA L)) : Fib.mkC (HA sp) (KA L) (L.y (clsOf L c)) = c :=
  (Equiv.ofBijective _ L.y_bij).apply_symm_apply c

theorem clsOf_inj : Function.Injective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.injective

theorem clsOf_surj : Function.Surjective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.surjective

theorem card_stabU (x : GA sp) : Nat.card (StabU L x) = Nat.card (C.stab 0 (clsOf L (Fib.mkC (HA sp) (KA L) x))) := by
  obtain ⟨h, hh, κ, hκ, e⟩ := (Fib.mk_eq_iff (HA sp) (KA L) _ _).1 (clsOf_spec (L := L) (Fib.mkC (HA sp) (KA L) x))
  obtain ⟨h0, rfl⟩ := exists_ratA h hh
  exact (Nat.card_congr ((stabRec _).trans (stabConj _ x h0 κ hκ e))).symm

variable (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)


include hH in
theorem fix_iff (i : compL L p) (g : Fin nV → GL (Fin (m + 1)) Qq) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    (repP L p i * jQ I hdet hk g)⁻¹ * ratA sp γ * (repP L p i * jQ I hdet hk g) ∈ KA L ↔
      γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (repP L p i).1 ∧
        (fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v)) = tupOf W g := by
  refine ((fibP I hdet hk hH).stab_iff (HA sp) (repP L p) (prP_repP I hk) i g (ratA sp γ) (prP_repP I hk)).trans
    (and_congr (mem_gamC_iff (repP L p i) γ).symm ?_)
  show g⁻¹ * (prP I hk (ratA sp γ) * g) ∈ _ ↔ _
  rw [← tupOf_eq_iff]
  have : tupOf W (prP I hk (ratA sp γ) * g) = fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v) := by
    funext v
    exact gMap_mul W _ _ _
  rw [this]


include hH in
def fixEquiv (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (g : Fin nV → GL (Fin (m + 1)) Qq) :
    {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ (tupOf W g) = tupOf W g} ≃
      StabU L (repP L p i * jQ I hdet hk g) where
  toFun γ := ⟨γ.1.1, (fix_iff hk I hdet hH i g γ.1.1).2 ⟨hy ▸ γ.1.2, by
    have := γ.2
    rwa [level_action_lattice_eq] at this⟩⟩
  invFun γ := ⟨⟨γ.1, hy ▸ ((fix_iff hk I hdet hH i g γ.1).1 γ.2).1⟩, by
    rw [level_action_lattice_eq]
    exact ((fix_iff hk I hdet hH i g γ.1).1 γ.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

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


include hH in
theorem class_eq_iff_translate_level_one (i i' : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y = (repP L p i).1) (Lt Lt' : Fin nV → Submodule W (Fin (m + 1) → Qq))
    (h : ∀ v, IsLattice W (Lt v)) (h' : ∀ v, IsLattice W (Lt' v)) :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y,
        Lt' = (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt := by
  simp only [level_action_lattice_eq]
  subst hy
  exact class_eq_iff_translate_level_zero hk I hdet hH i i' Lt Lt' h h'



include hH in
theorem clsC_iff (i i' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt Lt' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt)
    (h' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt') :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ,
        Lt' = ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt :=
  class_eq_iff_translate_level_one hS r lam0 dom hk I ψ hdet hH i i' _ rfl Lt Lt' h h'


include hH in
theorem clsC_surj (c : ClassSet (HA sp) (KA L)) :
    ∃ (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp) (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup),
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt ∧ clsC I hdet hk i Lt = c := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  obtain ⟨i, g, hg⟩ := (fibP I hdet hk hH).cls_surj (HA sp) (repP L p)
    (repP_mk L p) x (repP_mk L p)
  exact ⟨i, tupOf W g, tupOf_lat W g, (clsC_tupOf I hdet hk hH i g).trans hg⟩


include hH hdet in
theorem finClasses : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).FinClasses := by
  intro i
  have := finite_classSet_U L
  let f : {Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup //
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt} → ClassSet (HA sp) (KA L) :=
    fun Lt => clsC I hdet hk i Lt.1
  let s : Set.range f → (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup := fun c => (Classical.choose c.2).1
  have hs : ∀ c : Set.range f, f (Classical.choose c.2) = c.1 := fun c => Classical.choose_spec c.2
  refine ⟨(Set.finite_range s).toFinset, ?_, ?_⟩
  · intro L0 hL0
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hL0
    exact (Classical.choose c.2).2
  · intro Lt hLt
    let c : Set.range f := ⟨f ⟨Lt, hLt⟩, Set.mem_range_self _⟩
    refine ⟨s c, (Set.Finite.mem_toFinset _).2 ⟨c, rfl⟩, ?_⟩
    exact ((clsC_iff hS r lam0 dom hk I ψ e hdet hH i i (s c) Lt (Classical.choose c.2).2 hLt).1 (hs c)).2

end Formalism.L2.G.Cmp
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G

theorem natAct_rat {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {LL : Type} [Field LL] (e : LL →+* Kf) (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v))
    (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) LL)
    (hg : ∀ v s, Matrix.GeneralLinearGroup.map e (g v s) = gPosGL P v s (A v)) (Q : XR P LL) :
    MvPolynomial.map e (natActR P LL g Q) = P.natAct A (MvPolynomial.map e Q) := by
  have hinv : ∀ v s a b, e ((((g v s)⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL) a b) =
      P.gPos v s (((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) a b := by
    intro v s a b
    have h1 : Matrix.GeneralLinearGroup.map e ((g v s)⁻¹) = gPosGL P v s ((A v)⁻¹) := by
      rw [map_inv, map_inv, hg]
    have h2 := congrArg (fun M : GL (Fin (P.m + 1)) Kf => (M : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) a b) h1
    exact h2
  have hdet : ∀ v s, e ((g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).det) =
      (P.gPos v s (A v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det := by
    intro v s
    rw [RingHom.map_det]
    congr 1
    have h2 := congrArg (fun M : GL (Fin (P.m + 1)) Kf => (M : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf)) (hg v s)
    exact h2
  have hsub : ∀ R : XR P LL, MvPolynomial.map e
      (substR P LL (fun v s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL)) R) =
      P.subst (fun v s => P.gPos v s (((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))) (MvPolynomial.map e R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a => simp [substR, Places.subst]
    | add f q hf hq => simp only [map_add (f := _), hf, hq]
    | mul_X f x hf =>
      simp only [map_mul, hf]
      congr 1

      simp only [substR, Places.subst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_X, hinv]
  simp only [natActR, Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hsub]
  congr 2
  simp only [map_prod, map_zpow₀, hdet]
  rfl

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatLev : Prop :=
  (∀ (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)), ∃ g : GL (Fin (G.P.m + 1)) LL,
    Matrix.GeneralLinearGroup.map e g = gPosGL G.P v s ((G.lev i).act v γ)) ∧
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

theorem ratActG_of (h : RatLev G e) : RatActG G e := by
  intro i γ ξ hξ
  obtain ⟨Q, hQ⟩ := hξ
  choose g hg using fun v s => h.1 i γ v s
  obtain ⟨a, ha⟩ := h.2 i γ
  refine ⟨a • natActR G.P LL g Q, ?_⟩
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    natAct_rat G.P e (fun v => (G.lev i).act v γ) g hg Q, hQ, ← MvPolynomial.smul_eq_C_mul, ha,
    algebraMap_smul]
  rfl

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

def tEL (D : D7) : D.what₂.Tau → D.host.E →+* D.what₂.LL :=
  fun τ => D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

theorem tEL_emb (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (tEL D τ x) = embT D τ x := by
  simp only [tEL, embT, Formalism.BasicNotions.Host.emb, RingHom.comp_apply]
  first
    | exact RingHom.congr_fun D.embE_φ₀ _
    | exact D.embE_φ₀ _
    | (rw [← D.embE_φ₀]; rfl)

def locAt (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w hg) where
  rk := (X.g u w hg).rk.trans (rank_eq_first_level D.R)
  pl := (X.g u w hg).pl
  eQ := fun v => (X.g u w hg).eQ v _ rfl
  spl := fun v => (X.g u w hg).spl _ ((X.g u w hg).pl v).2
  B := reGL (rank_eq_first_level D.R) _ B
  yG := fun i => reGL (rank_eq_first_level D.R) _ ((X.g u w hg).yG i).1
  gamI := fun i => (reGL (rank_eq_first_level D.R) D.host.E).toMonoidHom.comp
    ((UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0).subtype.comp ((X.g u w hg).gamI i))

def FrRat (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (X.g u w hg).fr w' h =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

def StdB (D : D7) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rank_eq_first_level D.R) D.host.E B).1 * gramN D 0 (Nat.zero_le _) *
      (reGL (rank_eq_first_level D.R) D.host.E B).1 = 1 ∧
  ∀ x : Fin (D.R.N 0) → D.host.E, x ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔
    ∀ a, (((reGL (rank_eq_first_level D.R) D.host.E B)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 *ᵥ x) a ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range



structure CmpTied (D : D7) (X : Formalism.L2.Herm.Herm0 D) (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D)
    (c : LatCmp D) where

  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B

  fr_B : ∀ u w hg, FrRat X u w hg B
  tie : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    CmpTie ((T u).cls0).lev (embT D) D.what₂.embLL (tEL D) (D.gat u w hg) (c.embW u w hg)
      (locAt X u w hg B) (Gt.gat_pos u w hg)
      (fun x cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z))
      ((T u).cls0).y (c.cmp u w hg)

end Formalism.L2.G.Cmp

end
end
