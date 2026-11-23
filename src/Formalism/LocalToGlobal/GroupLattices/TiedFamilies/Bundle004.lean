module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle010
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle003
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle007
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle005
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle008
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle003
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

structure CmpHyp0P (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  evInj : ∀ u w hg, EvInj (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg)
    (J := gramN D 0 (Nat.zero_le _))

  ptEx : ∀ u w hg, PtEx ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B)
    ((T u).cls0).y

  ptAll : ∀ u w hg, PtAll ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B)
    ((T u).cls0).y

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

theorem CmpHyp0P.toHyp0 {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (H : CmpHyp0P T Gt I)
    (pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
      I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
        (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))) : Cmp.CmpHyp0 T Gt I := by
  exact Cmp.CmpHyp0.mk H.ex H.evInj H.ptEx H.ptAll pos H.chi H.latM

end Formalism.L2.G
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG Formalism.L2.G.Cmp Matrix

namespace Formalism.L2.G

def BlockRationalityField : Prop :=
  ∀ {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (h : P.m + 1 = n)
    (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ) (embLL : LL →+* ℂ)
    (lam : Tau → DomWeight n), WtTie P h pos lam → (∀ τ, ∃ M0 : GL (Fin n) LL, M τ = M0.1.map embLL) →
    BlockRational P h pos G M embLL lam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem blkRatRec_of_stmt (hS : BlockRationalityField) (X : Formalism.L2.Herm.Herm0 D) (Gt : GatTies D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    BlockRationalityAtPlace X Gt u w hg B := by
  refine hS (D.gat u w hg).P (locAt X u w hg B).rk (Gt.gat_pos u w hg) _ _ D.what₂.embLL ((D.fm u).lam 0) ?_ ?_
  · intro v s i
    exact Gt.gat_lam u w hg v s i
  · intro τ
    refine ⟨bc (tEL D τ) ((locAt X u w hg B).B)⁻¹, ?_⟩
    ext a b
    exact (tEL_emb D τ _).symm

end Formalism.L2.G
end
end

section

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  apply Units.ext; ext x y; rfl

theorem bc_reGL {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin a) R) :
    bc φ (reGL h R g) = reGL h S (bc φ g) := by
  subst h
  rw [reGL_rfl, reGL_rfl]

theorem isHerm_re {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (hh : IsHerm σ J) :
    IsHerm σ J' := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this]; exact hh

theorem det_re {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (hh : IsUnit J.det) :
    IsUnit J'.det := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this]; exact hh

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_mem_UPts {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin a) (E ⊗[F] R)) (hg : g ∈ UPts σ J R) :
    reGL h _ g ∈ UPts σ J' R := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this, reGL_rfl]; exact hg

theorem comp_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    {ι : Type} (yG : ι → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (K : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hs : Function.Surjective (fun i => (Quotient.mk'' (yG i) : ClassSet
      ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))))))
    (x : UPts σ J' (FiniteAdeleRing (𝓞 F) F)) :
    ∃ (i : ι) (γ : GL (Fin b) E) (k : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J' ∧ k ∈ K ∧
      k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * reGL h _ (yG i).1 * reGL h _ k := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  obtain ⟨i, hi⟩ := hs (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ (yG i) x).1 hi
  obtain ⟨γ, hγ, eγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  refine ⟨i, γ, k.1, hγ, Subgroup.mem_subgroupOf.1 hk, k.2, ?_⟩
  rw [reGL_rfl, reGL_rfl, eγ, e]; rfl

end Re

section Away

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem mem_awayP_iff (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (k : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    k ∈ Formalism.L2.Herm.awayFrom₂ L p ↔ k ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) k ∈ L.Uloc w := by
  unfold Formalism.L2.Herm.awayFrom₂
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

end Away

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)



theorem locGood_locAt (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) : LocGood (sigD D) (gramN D 0 (Nat.zero_le _)) (locAt X u w hg B) := by
  refine { herm := isHerm_re (rank_eq_first_level D.R) _ D.sp.gram0 _ (gramN_zero D) D.sp.baseGram_isHermitian
           det := det_re (rank_eq_first_level D.R) D.sp.gram0 _ (gramN_zero D) (isUnit_det_gram0 D.sp)
           sig := fun v x => (X.g u w hg).spl_sig _ ((X.g u w hg).pl v).2 x
           yG_mem := fun i => reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ ((X.g u w hg).yG i).2
           yG_p := ?_ }
  intro i v
  have h1 := (X.g u w hg).yG_p i _ ((X.g u w hg).pl v).2
  have h2 := bc_reGL (rank_eq_first_level D.R) (prV (E := D.host.E) ((X.g u w hg).pl v).1) ((X.g u w hg).yG i).1
  rw [h1, map_one] at h2
  exact h2



theorem ptEx_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    PtEx ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) ((T u).cls0).y :=
  ptEx_of (locGood_locAt X u w hg B) _ _ ((T u).cls0).y_bij.2

def SameUloc (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) : Prop :=
  ∀ v, ((T u).cls0).lev.Uloc v = ((X.lev0 u).Uloc v).map (reGL (rank_eq_first_level D.R) _).toMonoidHom

theorem sameUloc_of_joint (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hJ : Joint0 X.lev0 u (T u)) :
    SameUloc X T u := hJ.Uloc_eq



theorem ptAll_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    PtAll ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) ((T u).cls0).y := by
  refine ptAll_of (locGood_locAt X u w hg B) _ _ fun x => ?_
  obtain ⟨i, γ, k, hγ, hk, hkU, e⟩ := comp_re (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) (X.g u w hg).yG
    (Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w)) (X.g u w hg).yG_bij.2 x
  refine ⟨i, γ, reGL (rank_eq_first_level D.R) _ k, hγ, reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ hkU, e,
    fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, ((mem_awayP_iff _ _ k).1 hk).2 w' hw', rfl⟩



theorem awayEx_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) :
    ∃ κ : ((T u).cls0).lev.U, (locAt X u w hg B).IsAway i γ κ.1 := by
  refine awayEx_of (locGood_locAt X u w hg B) _ (fun i γ => ?_) i γ
  have h1 : (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 ∈ Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w) :=
    (mem_map_conj _ _ _).1 (((X.g u w hg).gamI_range i _).1 ⟨γ, rfl⟩)
  have e : ((locAt X u w hg B).yG i)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((locAt X u w hg B).gamI i γ) * (locAt X u w hg B).yG i = reGL (rank_eq_first_level D.R) _ ((((X.g u w hg).yG i).1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1) := by
    rw [map_mul, map_mul, map_inv, ← bc_reGL]
    rfl
  rw [e]
  obtain ⟨h2, h3⟩ := (mem_awayP_iff _ _ _).1 h1
  refine ⟨reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ h2, fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, h3 w' hw', rfl⟩

end Formalism.L2.G
end
end

section

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p} {A : LocAt F E n G}

def LocInt (A : LocAt F E n G) : Prop :=
  ∀ v (x : G.P.Qq v), x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ A.eQ v x ∈ (A.pl v).1.adicCompletionIntegers F

def LocHyp (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) : Prop :=
  ∀ v (x : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ UPts σ J ((A.pl v).1.adicCompletion F) →
    (∀ a b, (((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) →
    (∀ a b, ((((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) → x ∈ S.Uloc (A.pl v).1

theorem int_of_stab (hW : LocInt A) (v : Fin G.P.nV) (h : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hh : ∀ a b, (h : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) a b ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range)
    (a b : Fin n) :
    (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F := by
  have h1 : (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b =
      A.eQ v ((castGL A.rk (G.P.Qq v) h : Matrix (Fin n) (Fin n) _) a b) := rfl
  rw [h1, castGL_apply]
  exact (hW v _).1 (hh _ _)

theorem locHyp_of {k : ℕ} (hk : k = n) (A : LocAt F E n G) (S : StepLevel F E σ J T f bad) (J0 : Matrix (Fin k) (Fin k) E)
    (hJ : ∀ x y, J x y = J0 (Fin.cast hk.symm x) (Fin.cast hk.symm y)) (B0 : GL (Fin k) E) (hB : A.B = reGL hk E B0)
    (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)))
    (hU : ∀ v, S.Uloc v = (Uloc0 v).map (reGL hk _).toMonoidHom)
    (h0 : ∀ v (x : GL (Fin k) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ UPts σ J0 ((A.pl v).1.adicCompletion F) →
      (∀ a b, (((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) →
      (∀ a b, ((((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0)⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) → x ∈ Uloc0 (A.pl v).1) : LocHyp S A := by
  subst hk
  obtain rfl : J = J0 := by ext x y; exact hJ x y
  have hre : ∀ (R : Type) [CommRing R] (g : GL (Fin k) R), reGL (rfl : k = k) R g = g := by
    intro R _ g; apply Units.ext; ext x y; rfl
  rw [hre] at hB
  intro v x hx h1 h2
  rw [hB] at h1 h2
  rw [hU]
  exact Subgroup.mem_map.2 ⟨x, h0 v x hx h1 h2, hre _ x⟩

theorem ptOne_of (S : StepLevel F E σ J T f bad) (hW : LocInt A) (hH : LocHyp S A)
    (hbad : ∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) : PtOne S G A := by
  intro i L g g' x x' hL hL' hx hx'
  have hoff : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) (x.1⁻¹ * x'.1) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hx.1 w hw, hx'.1 w hw, inv_mul_cancel]
  have hmem : x.1⁻¹ * x'.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2
  have hU : x.1⁻¹ * x'.1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨hmem, fun w => ?_⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · obtain ⟨v, rfl⟩ := LocGood.exists_pl A w hw
      have hst : (g v)⁻¹ * g' v ∈ stabStd (k := G.P.m + 1) (Qq := G.P.Qq v) (G.P.W v) := by
        rw [← gMap_std_eq_iff, ← colSpan_eq, ← colSpan_eq, ← hL v, ← hL' v]
      have e : (bc (A.phE v) A.B)⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (x.1⁻¹ * x'.1)) * bc (A.phE v) A.B =
          bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) ((g v)⁻¹ * g' v)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx.2 v, hx'.2 v, map_mul, map_mul, map_inv, map_inv]
        group
      obtain ⟨h1, h2⟩ := (stabStd_iff _ _).1 hst
      refine hH v _ (Formalism.UG.P.afsplit_bc_mem σ J (A.pl v).1 _ hmem) ?_ ?_
      · rw [e]
        exact int_of_stab hW v _ h1
      · rw [e, ← map_inv, ← map_inv]
        exact int_of_stab hW v _ h2
    · rw [hoff w hw]
      exact Subgroup.one_mem _
  refine ⟨⟨_, hU⟩, by group, ?_⟩
  rw [S.chi_triv ⟨_, hU⟩ fun w hw => hoff w (hbad w hw)]
  rfl

end Formalism.L2.G
end
end
