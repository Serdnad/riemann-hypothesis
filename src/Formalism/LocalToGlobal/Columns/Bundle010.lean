module

public import Formalism.GL3MeanSquares.Bundle002
public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LogVandermondeBounds.Bundle001
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.LevGSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Columns.GSetLemmas

@[expose] public section

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section Orth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

def brzo_perp (x : A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | ∀ v, majAt A.b A.X v x y = 0}
  add_mem' := by
    intro a b ha hb v
    have h : majAt A.b A.X v x (a + b) = majAt A.b A.X v x a + majAt A.b A.X v x b := ((isSesq_maj A.b A.X) v).2.1 x a b
    rw [h, ha v, hb v, add_zero]
  zero_mem' := by
    intro v
    have h : majAt A.b A.X v x ((0 : K) • (0 : A.V)) = v.embedding (0 : K) * majAt A.b A.X v x 0 :=
      ((isSesq_maj A.b A.X) v).2.2.2 (0 : K) x 0
    simpa using h
  smul_mem' := by
    intro c y hy v
    have h : majAt A.b A.X v x (algebraMap (𝓞 K) K c • y) = v.embedding (algebraMap (𝓞 K) K c) * majAt A.b A.X v x y :=
      ((isSesq_maj A.b A.X) v).2.2.2 (algebraMap (𝓞 K) K c) x y
    rw [algebraMap_smul] at h
    rw [h, hy v, mul_zero]

variable {A} {γ : Type} [DecidableEq γ] (N : γ → Submodule (𝓞 K) A.V)

theorem brzo_orth_sup (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (a : γ) (s : Finset γ) (ha : a ∉ s) : ∀ x ∈ N a, ∀ y ∈ ⨆ c ∈ s, N c,
    inner ℝ (realize A.b A.X x) (realize A.b A.X y) = 0 := by
  intro x hx y hy
  have hle : (⨆ c ∈ s, N c) ≤ brzo_perp A x :=
    iSup₂_le fun c hc z hz v => horth a c (fun h => ha (h ▸ hc)) x hx z hz v
  rw [Formalism.HN.HeightGram.inner_realize]
  exact Finset.sum_eq_zero fun v _ => by rw [hle hy v]; rfl

theorem hlat_orth_fin (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0) (s : Finset γ) :
    Formalism.HN.deg (realize A.b A.X) (⨆ c ∈ s, N c) = ∑ c ∈ s, Formalism.HN.deg (realize A.b A.X) (N c) ∧
    (s.Nonempty → (⨆ c ∈ s, N c) ≠ ⊥ ∧ ∀ θ : ℝ, (∀ c ∈ s, Formalism.HN.muMax (realize A.b A.X) (N c) ≤ θ) →
      Formalism.HN.muMax (realize A.b A.X) (⨆ c ∈ s, N c) ≤ θ) := by
  have hlat : ∀ L : Submodule (𝓞 K) A.V, L.FG → Formalism.HN.IsLat (realize A.b A.X) L :=
    fun L hL => (Formalism.HN.plLat K A.V A.ι A.b A.X hA L hL).1
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun h => absurd h Finset.not_nonempty_empty⟩
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Finset.sum_empty]
    exact (Formalism.HN.satBasic (𝓞 K) A.V _ (realize A.b A.X) ⊥ (hlat ⊥ Submodule.fg_bot)).2.2.2.2.1
  | insert a s ha ih =>
    have hfs : (⨆ c ∈ s, N c).FG := Submodule.fg_biSup s N fun c _ => hfg c
    obtain ⟨-, h2, h3⟩ := (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) A.V _ (realize A.b A.X)).2 (N a) (⨆ c ∈ s, N c) (hlat _ (hfg a)) (hlat _ hfs)
      (brzo_orth_sup N horth a s ha)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨by rw [h2, ih.1], fun _ => ⟨fun h => hne a (eq_bot_iff.2 (h ▸ le_sup_left)), fun θ hθ => ?_⟩⟩
    by_cases hs : s.Nonempty
    · obtain ⟨i1, i2⟩ := ih.2 hs
      rw [(h3 (hne a) i1).1]
      exact max_le (hθ a (Finset.mem_insert_self _ _)) (i2 θ fun c hc => hθ c (Finset.mem_insert_of_mem hc))
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq]
      exact hθ a (Finset.mem_insert_self _ _)

theorem hlat_orth_sum [Fintype γ] [Nonempty γ] (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (r : ℕ) (hr : 0 < r) (hrk : ∀ c, Formalism.HN.rkK (N c) = r) (hrkT : Formalism.HN.rkK (⨆ c, N c) = Fintype.card γ * r) :
    (withL A (⨆ c, N c)).mu = mean (fun c => (withL A (N c)).mu) ∧
    ∃ c, (withL A (⨆ c, N c)).muMax ≤ (withL A (N c)).muMax := by
  have hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c := by simp
  obtain ⟨h1, h2⟩ := hlat_orth_fin N hA hfg hne horth Finset.univ
  rw [← hsup] at h1 h2
  have hfT : (⨆ c, N c).FG := by rw [hsup]; exact Submodule.fg_biSup _ N fun c _ => hfg c
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsl : ∀ c, Formalism.HN.slope (realize A.b A.X) (N c) =
      Formalism.HN.deg (realize A.b A.X) (N c) / ((Module.finrank ℚ K : ℝ) * r) := by
    intro c
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA (N c) (hfg c)).2.1
    show Formalism.HN.deg (realize A.b A.X) (N c) / ((Formalism.HN.rk (realize A.b A.X) (N c) : ℕ) : ℝ) = _
    rw [this, hrk c]
    push_cast
    rfl
  have hslT : Formalism.HN.slope (realize A.b A.X) (⨆ c, N c) =
      (∑ c, Formalism.HN.deg (realize A.b A.X) (N c)) / ((Module.finrank ℚ K : ℝ) * (Fintype.card γ * r)) := by
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA _ hfT).2.1
    show Formalism.HN.deg (realize A.b A.X) (⨆ c, N c) / ((Formalism.HN.rk (realize A.b A.X) (⨆ c, N c) : ℕ) : ℝ) = _
    rw [this, hrkT, h1]
    push_cast
    rfl
  constructor
  · show Formalism.HN.muDef A.b A.X (⨆ c, N c) = mean fun c => Formalism.HN.muDef A.b A.X (N c)
    unfold Formalism.HN.muDef mean
    rw [hslT]
    simp only [hsl]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    field_simp
  · obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset γ)
      (fun c => Formalism.HN.muMax (realize A.b A.X) (N c)) Finset.univ_nonempty
    refine ⟨c, ?_⟩
    show Formalism.HN.muMaxDef A.b A.X (⨆ c, N c) ≤ Formalism.HN.muMaxDef A.b A.X (N c)
    unfold Formalism.HN.muMaxDef
    have := (h2 Finset.univ_nonempty).2 _ hc
    linarith

end Orth

section GSDOrth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (hf : S.Free)




end GSDOrth

section GSDOrth2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end GSDOrth2

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

section

noncomputable section

namespace Formalism.L2.Col

open Module Module.End Polynomial

section Link

variable {L Pl Pt : Type} [Field L]

end Link

section Conc

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Conc

section Genus

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def UnimodGenusLoc (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  IsCMUnram E → ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
    SameGenus (hStd E n) (stdLat E n) N

def UnimodGenusLocAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), UnimodGenusLoc E n

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def UnimodGenus : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N →
    ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

end Genus

section Counting

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def wSeq {n : ℕ} (lam : DomWeight n) : ℕ → ℝ := fun i => if h : i < n then ((lam.w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylDim {n : ℕ} (lam : DomWeight n) : Prop :=
  (Nat.card (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ℝ) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n

end Counting

section Alcove

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Alcove

abbrev MinkowskiBound : Prop := Formalism.HermitianLatticeCounting.S6.MinkowskiBound

section FormalDegree

open MeasureTheory

end FormalDegree

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

def levU : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := (JH hc n ST SG H).map (J0 hc n ST).subtype

theorem mem_levU {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ levU hc n ST SG H ↔ ∃ h : x ∈ J0 hc n ST, redG hc n ST SG ⟨x, h⟩ ∈ H := by
  unfold levU
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem unipotentLevel_le_mirabolicLevel : levU hc n ST SG H ≤ J0 hc n ST := Subgroup.map_subtype_le _

theorem levU_le_UAd : levU hc n ST SG H ≤ UAd hc n := fun x hx =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (unipotentLevel_le_mirabolicLevel hc n ST SG H hx)).1).1

theorem kOne_le_unipotentLevel : K1 hc n ST SG ≤ levU hc n ST SG H := by
  unfold K1 levU
  apply Subgroup.map_mono
  intro y hy
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hy]
  exact H.one_mem

def levRed : levU hc n ST SG H →* H :=
  ((redG hc n ST SG).comp (Subgroup.inclusion (unipotentLevel_le_mirabolicLevel hc n ST SG H))).codRestrict H
    (fun x => ((mem_levU hc n ST SG H).1 x.2).2)

variable {hc n ST SG H}

def levChr {M : Type} [CommGroup M] (lam : H →* M) : levU hc n ST SG H →* M := lam.comp (levRed hc n ST SG H)

def levTyp {M : Type} [CommGroup M] (lam : H →* M) : levU hc n ST SG H →* M := (levChr lam)⁻¹

variable (hc n ST SG H)

def levLoc (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)) :=
  (levU hc n ST SG H).map (Formalism.UG.bc (Formalism.UG.prV (E := E) v))

end Lev

def IsOver {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (P : Pl E) : Prop :=
  v.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))

def plUnder (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (Pl E)) : Set (HeightOneSpectrum (𝓞 F)) := {v | ∃ P ∈ S, IsOver v P}

section Base

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) [NeZero n] (ST : Finset (Pl E))

def baseLb : Submodule (𝓞 E) (Fin n → E) := (Deco.base E n ST (∅ : Finset (Pl E))).L

def baseSh : Submodule (𝓞 E) (Fin n → E) := (Deco.base E n ST (∅ : Finset (Pl E))).Lsh

def baseKer : Submodule (𝓞 E) (Fin n → E) :=
  baseSh E n ST ⊓ ⨅ P ∈ ST, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (baseLb E n ST)

end Base

section Fun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))

abbrev baseDual : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))

abbrev baseDualV (v : HeightOneSpectrum (𝓞 F)) : Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseDual hc n ST)

abbrev fMod (v : HeightOneSpectrum (𝓞 F)) : Type :=
  baseDualV hc n ST v ⧸ (Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
    (baseDualV hc n ST v).subtype

def fLoc (v : HeightOneSpectrum (𝓞 F)) : baseDualV hc n ST v →ₗ[Formalism.BasicNotions.intV E v] fMod hc n ST v :=
  Submodule.mkQ _

end Fun

section Cls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

abbrev AdCl : Type := Formalism.L2.DIV.Cl hc (1 : Matrix (Fin n) (Fin n) E) (levU hc n ST SG H)

abbrev DecoCl : Type := MulAction.orbitRel.Quotient (UF E n × H) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG))

def decoCls (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : DecoCl n ST SG H := Quotient.mk (MulAction.orbitRel (UF E n × H) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG))) d

def ptOf (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : UAd hc n :=
  open Classical in
  if h : ∃ x : UAd hc n, decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d then h.choose else 1

def adClsOf (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : AdCl hc n ST SG H := Quotient.mk'' (ptOf hc n ST SG d)

def decoOfD (c : DiaG (E := E) (ST := ST)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) := (decoOf ST SG x).dia c

def ptOfD (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : UAd hc n := ptOf hc n ST SG (d.dia c⁻¹)

def stabRat (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : MulAction.stabilizer (UF E n × H) d →* URat hc n :=
  (ratEquiv hc n).symm.toMonoidHom.comp ((MonoidHom.fst (UF E n) H).comp (Subgroup.subtype _))

end Cls

section Par

variable {E K : Type} [Field E] [NumberField E] [Field K] {r n : ℕ}

def parFam (h : r ≤ n) (t s : ℕ) {SG : Finset (Pl E)} (P : LevFam E K r SG)
    (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) : LevFam E K n SG := fun w =>
  ⟨HPar n (𝓞 E ⧸ w.1.asIdeal) h (List.replicate s t) (P w).H, lamPar h (List.replicate s t) (P w).lam (χ w)⟩


open Classical in
def parDat (h : r ≤ n) (t s : ℕ) {SG : Finset (Pl E)} (P : LevFam E K r SG)
    (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) : Formalism.L2.DIV.LevDat E K n where
  r := r
  hr := h
  t := t
  s := s
  Pg := SG
  Q := ∅
  P := Formalism.L2.DIV.LevelP.ofLocal (fun w => (P w).H) (fun w => (P w).lam)
  cg := fun c PP => if hP : PP ∈ SG then χ ⟨PP, hP⟩ (c - 1) else 1
  xq := fun _ => 1

end Par

section Cols

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem N_eq_blocks (R : Ranks) (j : ℕ) : R.N j = (R.k + j) + j * R.t := by
  simp only [Ranks.N, Nat.mul_add, Nat.mul_one]
  omega

instance neZeroN (R : Ranks) (j : ℕ) : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩

def colLevS (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j + 1 < R.m then colLev Ch j w
  else if j + 1 = R.m then
    ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j ⊓ fixCol (R.N j) (𝓞 X.E ⧸ w.1.asIdeal) R.k,
      (lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j).comp (Subgroup.inclusion inf_le_left)⟩
  else
    ⟨HXmsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m,
      lamXmsharp (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m⟩

variable (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)


open Classical in
def diaT (u : Pr.Word) : DiaG (E := X.E) (ST := Pr.vT u) := fun P =>
  if h : IsUnit (Ideal.Quotient.mk P.1.asIdeal (X.conjO (Pr.piT u))) then h.unit else 1

def colDia (R : Ranks) (u : Pr.Word) (j : ℕ) : DiaG (E := X.E) (ST := Pr.vT u) := if j < R.m then 1 else diaT u

def colPt (u : Pr.Word) (j : ℕ) (d : ColDeco X Pr u (R.N j)) : UAd hc (R.N j) :=
  ptOfD hc (R.N j) (Pr.vT u) Pr.vGs (colDia R u j) d

end Cols

end Formalism.L2.Col
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section RBlockSym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rPsymF : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsymF (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSymF (Ch.psi0 w) R.r R.k R.rS⟩

theorem rowTyG_PsymF_H (w : {w // w ∈ Pr.vGs}) :
    (rowTyG Ch (rPsymF Ch) w).H = HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := rfl

end RBlockSym

end Formalism.L2.Col
end
end
