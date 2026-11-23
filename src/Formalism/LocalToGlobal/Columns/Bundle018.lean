module

public import Formalism.LocalToGlobal.Columns.Bundle015
public import Formalism.LocalToGlobal.Columns.Bundle017
public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.HermitianColumns.Bundle001
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.Bundle016
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (Am : Amb X) (u : Pr.Word)

def oneAl (j : ℕ) (h : j ≤ m2 + 1) : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β j := ⟨(), h⟩

variable {Λ sel mu}

variable (Λ sel mu)

def FixE : Prop :=
  ∀ h ∈ (Λ (m2 + 1)).grp, ∀ w : Pr.vGs,
    ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)).mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k

variable {W Λ Ch sel mu cst hQ m2 Am u}

end Eq

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec}

theorem hx_hform (i : ℕ) (hi : i ≤ D.R.m) (x y : (D.sp.X i).V) :
    (D.sp.X i).hT x y = hform (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.crdN D i hi x) (CF.crdN D i hi y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) x y]
  unfold hform
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  exact Finset.sum_congr rfl fun b _ => rfl

variable (u : D.what₂.Word)

theorem hx_clsCrd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c = (D.clsLat u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl

theorem hx_Ld_eq (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.Ld D u i hi c = (CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  have key : (((CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.clsCrd D u i hi c) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) x).1 hx y hy
      rw [hx_hform i hi] at this
      exact this
    · intro ht
      refine ⟨(CF.crdN D i hi).symm t, ?_, (CF.crdN D i hi).apply_symm_apply t⟩
      refine (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) _).2 fun y hy => ?_
      rw [hx_hform i hi, LinearEquiv.apply_symm_apply]
      exact ht (CF.crdN D i hi y) ⟨y, hy, rfl⟩
  show Submodule.span (𝓞 D.host.E) (dualSet _ _ _) = _
  rw [← key, Submodule.span_eq]

theorem hx_mem_map {i : ℕ} (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ M.map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) ↔ x ∈ M := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := (CF.crdN D i hi).injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem hx_mem_Ld (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Ld D u i hi c ↔ x ∈ CH.Ld D u i c := by
  rw [hx_Ld_eq, hx_mem_map]

theorem hx_smul_Ld (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    I • CF.Ld D u i hi c = (I • CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_Ld_eq, Submodule.map_smul'']

theorem hx_Lk_eq (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c ⊔ I • CF.Ld D u i hi c = (CH.Lk D u I i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_smul_Ld, hx_clsCrd, ← Submodule.map_sup]

variable {u} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_mem_Lk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Lk A i hi v c ↔ x ∈ CH.Lk D u (A.Pv v) i c := by
  show CF.crdN D i hi x ∈ CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c ↔ _
  rw [hx_Lk_eq, hx_mem_map]

def hxLd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ ↥(CF.Ld D u i hi c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Ld u i hi c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def hxLk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    ↥(CH.Lk D u (A.Pv v) i c) →+ ↥(CF.Lk A i hi v c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Lk A i hi v c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)


open Classical in
def hxPr (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ (D.fm u).lv i v c :=
  if hi : i ≤ D.R.m then ((P i hi).pr v c).comp (hxLd i hi c) else 0


open Classical in
def hxPrk (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Lk D u (A.Pv v) i c) →+ (D.fm u).lk i v c :=
  if hi : i ≤ D.R.m then ((P i hi).prk v c).comp (hxLk A i hi v c) else 0

theorem hxPr_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = (P i hi).pr v c (hxLd i hi c z) := by
  unfold hxPr; rw [dite_eq_left hi]; rfl

theorem hxPrk_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = (P i hi).prk v c (hxLk A i hi v c z) := by
  unfold hxPrk; rw [dite_eq_left hi]; rfl

theorem hxPr_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPr A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).pr_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Ld u i hi c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPr_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPr_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c (r • z) = A.res v r • hxPr A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPr_eq A P i hi, hxPr_eq A P i hi, ← (P i hi).pr_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPr; rw [dite_eq_right hi]; simp

theorem hxPr_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Ld D u i c := by
  rw [hxPr_eq A P i hi, (P i hi).pr_ker, hx_smul_Ld]
  exact hx_mem_map hi _ z.1

theorem hx_fv_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    (D.fm u).fv i v c (hxPr A P i v c z) = 0 ↔ z.1 ∈ CH.Lk D u (A.Pv v) i c := by
  rw [hxPr_eq A P i hi, (P i hi).fv_ker]
  exact hx_mem_Lk A i hi v c z.1

theorem hxPrk_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPrk A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).prk_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Lk A i hi v c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPrk_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPrk_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c (r • z) = A.res v r • hxPrk A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPrk_eq A P i hi, hxPrk_eq A P i hi, ← (P i hi).prk_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPrk; rw [dite_eq_right hi]
    change (0 : (D.fm u).lk i v c) = A.res v r • 0
    exact (smul_zero _).symm

theorem hxPrk_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Lk D u (A.Pv v) i c := by
  rw [hxPrk_eq A P i hi, (P i hi).prk_ker]
  show CF.crdN D i hi z.1 ∈ A.Pv v • (CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c) ↔ _
  rw [hx_Lk_eq, ← Submodule.map_smul'']
  exact hx_mem_map hi _ z.1

theorem hx_te (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c))
    (hz : (D.fm u).fv i v c (hxPr A P i v c z) = 1)
    (h : ((D.mem u).A.T : D.host.E) • z.1 ∈ CH.Lk D u (A.Pv v) i c) :
    hxPrk A P i v c ⟨_, h⟩ = (D.fm u).te i v c := by
  rw [hxPr_eq A P i hi] at hz
  have e : CF.crdN D i hi (((D.mem u).A.T : D.host.E) • z.1) = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 := by
    rw [map_smul]
    show _ = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • CF.crdN D i hi z.1
    rw [Algebra.smul_def' , map_natCast] <;> rfl
  have h' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 ∈ CF.Lk A i hi v c := by
    rw [← e]; exact (hx_mem_Lk A i hi v c _).2 h
  rw [hxPrk_eq A P i hi, ← (P i hi).te v c (hxLd i hi c z) hz h']
  congr 1
  exact Subtype.ext e

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Yb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.yOf (d : Deco E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : Set (Sp E n) :=
  {z | ∀ w : SG, (qOf w.1 : E) • z ∈ d.at w.1 ∧ d.be w ((qOf w.1 : E) • z) = v w}

def Deco.y0 (d : Deco E n ST SG) (k : ℕ) : Set (Sp E n) := d.yOf fun w => Loc.eN (𝓞 E ⧸ w.1.asIdeal) n k

end Yb

section Ref

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))


variable {sel mu} in
def liftQ (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    DecoF X.E n ST SG (QE sel (mu : Chr X.F X.E X.K)) :=
  ⟨(p, fun _ => 1), fun P _ => absurd (hQ ▸ P.2 : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E)))) (Finset.notMem_empty _)⟩

def XiRef {u : Pr.Word} (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if h : i < m2 then XiEntry Ch sel mu cst L i (al i (by omega)) (al (i + 1) (by omega)) p p' x
  else if h' : i = m2 then XiCpl1 Ch sel mu cst L i (al i (by omega)) p p' (p'.deco.1.y0 R.k) x
  else if i = m2 + 1 then XiTop Ch sel mu cst i p (p.deco.1.y0 R.k) p' x
  else 0

end Ref

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl)

section QDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (Pl E))


variable (F) in
abbrev qv (P : Pl E) : HeightOneSpectrum (𝓞 F) := underPl F P

abbrev qGL (g : Sp E n ≃ₗ[E] Sp E n) : GL (Fin n) E := toGLm E n g

instance qdAct {K : Type} [Field K] (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (Θ : LevQFam E K n Q) :
    MulAction (UF E n × H × Θ.grp) (DecoF E n ST SG Q) :=
  MulAction.compHom _ (MonoidHom.prodMap (MonoidHom.id _) (MonoidHom.prodMap H.subtype Θ.grp.subtype))

structure QLoc {K : Type} [Field K] (Θ : LevQFam E K n Q) where
  sp : ∀ P : Q, E ⊗[F] (qv F P.1).adicCompletion F ≃+* (qv F P.1).adicCompletion F × (qv F P.1).adicCompletion F
  sp_sig : ∀ P x, sp P (Formalism.UG.sigR hc.sig ((qv F P.1).adicCompletion F) x) = Formalism.UG.swapR _ (sp P x)
  sp_alg : ∀ P (a : (qv F P.1).adicCompletion F), sp P ((1 : E) ⊗ₜ[F] a) = (a, a)

  sp_int : ∀ (P : Q) (x : E ⊗[F] (qv F P.1).adicCompletion F), x ∈ Formalism.BasicNotions.intV E (qv F P.1) ↔
    (sp P x).1 ∈ (qv F P.1).adicCompletionIntegers F ∧ (sp P x).2 ∈ (qv F P.1).adicCompletionIntegers F

  sp_P : ∀ (P : Q) (r : 𝓞 E), Valued.v (sp P (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E))).1 < 1 ↔ r ∈ P.1.asIdeal

  U : ∀ P : Q, Subgroup (GL (Fin n) ((qv F P.1).adicCompletion F))
  U_int : ∀ P : Q, ∀ k ∈ U P, ∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F

  U_rat : ∀ (P : Q) (g : GLint E n P.1),
    Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1) ∈ U P ↔
      g ∈ (Θ P).H

  U_dense : ∀ (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)),
    (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F) →
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F) →
    ∃ g : GLint E n P.1,
      (Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1))⁻¹ * k ∈ U P
  chr : ∀ P : Q, U P →* Kˣ
  chr_rat : ∀ (P : Q) (g : GLint E n P.1) (hg : g ∈ (Θ P).H)
    (h : Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1) ∈ U P),
    chr P ⟨_, h⟩ = (Θ P).lam ⟨g, hg⟩

variable {K : Type} [Field K] {Θ : LevQFam E K n Q}


variable {hc n Q} in
abbrev QLoc.phi (q : QLoc hc n Q Θ) (P : Q) : E →+* (qv F P.1).adicCompletion F :=
  (RingHom.fst _ _).comp ((q.sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))


variable {hc n Q} in
abbrev QLoc.at (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : GL (Fin n) ((qv F P.1).adicCompletion F) :=
  Formalism.UG.bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) (Formalism.UG.bc (Formalism.UG.prV (E := E) (qv F P.1)) x)

def levUQ (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  levU hc n ST SG H ⊓ ⨅ P : Q, (q.U P).comap ((Formalism.UG.bc ((RingHom.fst _ _).comp (q.sp P).toRingHom)).comp
    (Formalism.UG.bc (Formalism.UG.prV (E := E) (qv F P.1))))

variable {hc n ST SG Q}

def FrOver (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, (Formalism.UG.bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x ∈ q.U P

variable (hc n ST SG Q)

abbrev DecoFCl (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (Θ' : LevQFam E K n Q) : Type :=
  MulAction.orbitRel.Quotient (UF E n × H × Θ'.grp) (DecoF E n ST SG Q)

abbrev RecClsF (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) : Type :=
  RecCls hc (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) (levUQ hc n ST SG Q H q)
    (fun c => MulAction.stabilizer (UF E n × H × Θ.grp) (s c)) (fun c => (s c).deco.1.L)

end QDict

end Formalism.L2.Col
end
end
