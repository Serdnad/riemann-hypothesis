module

public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Divisibility.Bundle001
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
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
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.Bundle006
public import Formalism.LocalToGlobal.Columns.Bundle007
import Formalism.LocalToGlobal.GlobalTheory.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem SameAt.symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

theorem SameAt.trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', k1, k2⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]
    exact h1 _ (k1 _ hx)
  · rw [mul_smul]
    exact k2 _ (h2 _ hx)

theorem SameAt.sup {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (S : Submodule (𝓞 E) (Sp E n)) : SameAt Q (N ⊔ S) (N' ⊔ S) := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)

end Loc

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.IsUp.sameAt {d d' : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (h : Deco.IsUp P q d d') {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ≠ P.1) (hQ' : Q ≠ conjPrime₂ P.1) :
    SameAt Q d.N d'.N := by
  obtain ⟨x, hx, -, rfl⟩ := h
  exact (upN_spec hd.lat hd.uni P.1 hP.ne hx).2.2.1 Q hQ hQ'

theorem Deco.IsUp.f_ne {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') {Q : ST}
    (hQ : Q ≠ P) : d'.f Q = d.f Q := by
  obtain ⟨x, _, _, rfl⟩ := h
  simp only [Deco.up, Function.update, dif_neg hQ]

theorem Deco.IsUp.be_eq {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') : d'.be = d.be := by
  obtain ⟨x, _, _, rfl⟩ := h
  rfl

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.mem b).outSec

abbrev rep (c : F.Cl) : F.D c.1 := (F.mem c.1).outSec.rep c.2

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

def Free : Prop := ∀ b, (F.mem b).Free

@[reducible] def toH (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K where
  V := F.Forms
  ι := Fin (F.toCSD h).dim
  b := (F.toCSD h).basis.map (F.res h).symm
  X := stdFrame (F.toCSD h).H
  L := L



variable {F}

variable (F)

variable {F}

variable (F)

variable {F}

end GFam

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

def intOf (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : Submodule (𝓞 K) F.Forms :=
  Submodule.pi Set.univ fun b => (F.mem b).intOf (N b)

end GFam

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end GSD

section FormFam

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]


variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : β → LevFam X.E X.K n SG)

end FormFam

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def gloPhi : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp spl.toRingHom

variable (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

include halg in
theorem gloPhi_int (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ Formalism.BasicNotions.intV E v) :
    gloPhi v spl x ∈ v.adicCompletionIntegers F :=
  ((Formalism.L2.G.split_integral_completion F E v spl halg x).1 hx).1

def gloRho : Formalism.L2.Herm.intAf F E →+* kv F v :=
  (IsLocalRing.residue (v.adicCompletionIntegers F)).comp
    ((((gloPhi v spl).comp (prV (E := E) v)).comp (Formalism.L2.Herm.intAf F E).subtype).codRestrict (v.adicCompletionIntegers F)
      fun s => gloPhi_int v spl halg _ (afsplit_prV_int v _ s.2))

theorem gloRho_apply (s : Formalism.L2.Herm.intAf F E) :
    gloRho v spl halg s = IsLocalRing.residue (v.adicCompletionIntegers F)
      ⟨gloPhi v spl (prV (E := E) v (s : E ⊗[F] Formalism.L2.Herm.Af F)), gloPhi_int v spl halg _ (afsplit_prV_int v _ s.2)⟩ := rfl

variable (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

def gloK : kP w →+* kv F v := Ideal.Quotient.lift w.asIdeal ((gloRho v spl halg).comp (oToS F E)) hw

theorem gloRho_eq (s : Formalism.L2.Herm.intAf F E) : gloRho v spl halg s = gloK v spl halg w hw (resS F w s) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resS F w s)
  have h1 : resS F w (s - oToS F E a) = 0 := by rw [map_sub, resS_oToS, ha, sub_self]
  rw [resS_eq_zero_iff] at h1
  have h2 : idS F w.asIdeal ≤ RingHom.ker (gloRho v spl halg) := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact hw b hb
  have h3 : gloRho v spl halg (s - oToS F E a) = 0 := h2 h1
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, ← ha]
  rfl

theorem glo_res_zero (x : v.adicCompletionIntegers F) (h : Valued.v (x : v.adicCompletion F) < 1) :
    IsLocalRing.residue (v.adicCompletionIntegers F) x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have h1 : ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) = 1 := by
    have := congrArg (Subtype.val) u.mul_inv
    exact this
  have h2 := congrArg Valued.v h1
  rw [map_mul, map_one] at h2
  have h3 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Subtype.mem _)
  have h4 := mul_le_mul' h.le h3
  rw [h2, one_mul] at h4
  have h5 : Valued.v ((u : v.adicCompletionIntegers F) : v.adicCompletion F) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤
      Valued.v ((u : v.adicCompletionIntegers F) : v.adicCompletion F) := mul_le_of_le_one_right' h3
  rw [h2] at h5
  exact absurd h (not_lt.2 h5)

theorem glo_algMap_int (r : 𝓞 F) : algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, csApprox_val_int]
  exact HeightOneSpectrum.intValuation_le_one v r

theorem glo_res_surj (z : kv F v) : ∃ r : 𝓞 F,
    IsLocalRing.residue (v.adicCompletionIntegers F) ⟨algebraMap (𝓞 F) (v.adicCompletion F) r, glo_algMap_int v r⟩ = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨D, hDv, hD⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := integral_adele_approximation_holds F D hD (afsplitI v (x : v.adicCompletion F)) (afsplitI_mem_intAd v _ x.2)
  refine ⟨r, ?_⟩
  have ev : (x : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) D * y v := by
    have := congrArg (fun z : Formalism.L2.Herm.Af F => z v) e
    rw [afsplitI_self] at this
    exact this
  have hDval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by
    rw [csApprox_val_int]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v D).2 hDv
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v)
  have hlt : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D * y v) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hyv) hDval
  have hmem : algebraMap (𝓞 F) (v.adicCompletion F) D * y v ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hlt.le
  have hx : x = ⟨algebraMap (𝓞 F) (v.adicCompletion F) r, glo_algMap_int v r⟩ + ⟨_, hmem⟩ := Subtype.ext ev
  rw [hx, map_add (f := _), glo_res_zero v ⟨_, hmem⟩ hlt, add_zero]

theorem gloRho_algMap (r : 𝓞 F) : gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) =
    IsLocalRing.residue (v.adicCompletionIntegers F) ⟨algebraMap (𝓞 F) (v.adicCompletion F) r, glo_algMap_int v r⟩ := by
  rw [gloRho_apply]
  congr 1
  apply Subtype.ext
  show gloPhi v spl (prV (E := E) v (inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)))) = _
  rw [afsplit_prV_inclE]
  have h1 : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) =
      (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) r) := by
    show (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]
  rw [h1]
  show (spl _).1 = _
  rw [halg]

theorem gloK_bijective : Function.Bijective (gloK v spl halg w hw) := by
  constructor
  · haveI : w.asIdeal.IsMaximal := w.isMaximal
    letI := Ideal.Quotient.field w.asIdeal
    exact RingHom.injective (gloK v spl halg w hw)
  · intro z
    obtain ⟨r, rfl⟩ := glo_res_surj v z
    refine ⟨Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 F) (𝓞 E) r), ?_⟩
    rw [← gloRho_algMap v spl halg r]
    rfl

def gloE : kP w ≃+* kv F v := RingEquiv.ofBijective (gloK v spl halg w hw) (gloK_bijective v spl halg w hw)

theorem gloE_resS (s : Formalism.L2.Herm.intAf F E) : gloE v spl halg w hw (resS F w s) = gloRho v spl halg s :=
  (gloRho_eq v spl halg w hw s).symm

end Loc

end Formalism.L2.Col
end
end
