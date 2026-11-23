module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle561
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LowAvoid

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

def lowPre (P : Pre) : Finset ℕ := by
  classical
  exact if h : ∃ X : Stages, X.B.toPre = P then lowAll h.choose.toD7 else ∅

theorem lowAll_congr {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : lowAll s.toD7 = lowAll s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem lowAll_eq_lowPre (s : Stages) : lowAll s.toD7 = lowPre s.B.toPre := by
  have h : ∃ X : Stages, X.B.toPre = s.B.toPre := ⟨s, rfl⟩
  simp only [lowPre, dif_pos h]
  exact lowAll_congr h.choose_spec.symm

theorem prime_of_mem_lowAll (D : D7) {p : ℕ} (hp : p ∈ lowAll D) : p.Prime := by
  simp only [lowAll, lowPr, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with ((rfl | rfl | hp | hp) | rfl | rfl | rfl | rfl)
  · exact Nat.prime_two
  · exact (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  · exact Nat.prime_of_mem_primeFactors hp
  · exact Nat.prime_of_mem_primeFactors hp
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1
  · exact D.host.pde_prime
  · exact D.host.pde'_prime

theorem eq_of_mem_placesOver {E : Type} [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hu : (Ideal.absNorm u.asIdeal).Prime) (h : u ∈ placesOver E p) : Ideal.absNorm u.asIdeal = p := by
  by_contra e
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem _
  obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ((p : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hu hp).2 e)
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ (show ((p : ℕ) : 𝓞 E) ∈ u.asIdeal from h))))

theorem conductors_avoid_lowAll :
    AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  refine evG_all fun K => ?_
  refine large₂.imp (p := fun B _ T => T.Avoids fun _ => lowPre B.toPre)
    ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun B _ _ _ _ => lowPre B, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ h => h⟩ ?_
  intro B f T _ hA _ _ _ w _ P x v u hu p hp hup
  have hl : lowAll (Dof x) = lowPre B.toPre := lowAll_eq_lowPre (w.st x.o.Z)
  obtain ⟨-, h1, -, -⟩ := (T.psi_tw v).2.2.2 u fun h => ((T.psi_is v).ram u).1 h hu
  have e : Ideal.absNorm u.asIdeal = p := eq_of_mem_placesOver u (prime_of_mem_lowAll _ hp) h1 hup
  exact hA v u hu (by rw [e, ← hl]; exact hp)

end GlobalTheory.LowAvoid

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.HeightCounting.ThetaSt

section Gen

variable {D : D7}

theorem baseLevelCharacter_eq_prod_superdiagonalSum {Pg : Finset (Pl D.host.E)} {r : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL)
    (y : (Formalism.L2.DIV.P0 Pg r ψ).H) :
    (((Formalism.L2.DIV.P0 Pg r ψ).chi y : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge ((y : G0 Pg r) PP)) := by
  change ↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) at y
  change (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
    (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) y : D.what₂.LLˣ) : D.what₂.LL) = _
  letI : IsOneApply (↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) →* D.what₂.LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) →* D.what₂.LLˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, Units.coe_prod]
  rfl

theorem supSum_map {κ : Type} [CommRing κ] {n : ℕ} (e : κ →+* ZMod n) {r : ℕ} (g : GL (Fin r) κ) :
    Formalism.L2.NX.supSum r ((Matrix.GeneralLinearGroup.map e g : GL (Fin r) (ZMod n)) : Matrix (Fin r) (Fin r) (ZMod n)) =
      e (edgeSum supEdge g) := by
  unfold Formalism.L2.NX.supSum edgeSum

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (b : ℕ) = a + 1
  · have h' : supEdge a b := h
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ supEdge a b := h
    rw [if_neg h, if_neg h', map_zero]

def thOf (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) :
    Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ :=
  ((AddChar.zmodChar (D.host.g k) (hp k)).toMonoidHom.toHomUnits)⁻¹

theorem thOf_val (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) (z : ZMod (D.host.g k)) :
    (((thOf ζ hp k (Multiplicative.ofAdd z) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = ((ζ k : D.what₂.LL) ^ z.val)⁻¹ := by
  simp [thOf, MonoidHom.inv_apply, AddChar.toMonoidHom_apply, AddChar.zmodChar_apply]

theorem pow_of_emb (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) (k : Fin 2) :
    ζ k ^ D.host.g k = 1 := by
  have hg : (D.host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  apply Subtype.ext
  apply D.what₂.embLL.injective
  have e1 : ((ζ k ^ D.host.g k : ↥D.LL0) : D.what₂.LL) = (ζ k : D.what₂.LL) ^ D.host.g k := rfl
  rw [e1, map_pow, hζ, ← Complex.exp_nat_mul]
  have e2 : ((D.host.g k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (D.host.g k : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [e2, Complex.exp_two_pi_mul_I]
  simp

end Gen

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem roots_g (x : St P) (k : Fin 2) : ∃ ζ : ↥(Dof x).LL0,
    (Dof x).what₂.embLL (ζ : (Dof x).what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / ((Dof x).host.g k : ℂ)) := by
  have hmem : (w.st x.o.Z).B.host.g k * ((w.st x.o.Z).B.host.g k - 1) ∈ [(w.st x.o.Z).B.restRowsFiniteGroupCard,
      (w.st x.o.Z).B.host.g 0 * ((w.st x.o.Z).B.host.g 0 - 1), (w.st x.o.Z).B.host.g 1 * ((w.st x.o.Z).B.host.g 1 - 1), 3 ^ 4,
      5 ^ 4] := by
    fin_cases k <;> simp
  obtain ⟨z, hz, hz'⟩ := (w.st x.o.Z).B.roots_Ks _ hmem
  have hg1 : 1 < (Dof x).host.g k := ((Dof x).host.g_prime k).one_lt
  refine ⟨⟨z ^ ((Dof x).host.g k - 1), (w.st x.o.Z).B.Ks_le (pow_mem hz _)⟩, ?_⟩
  show (w.st x.o.Z).B.embLL (z ^ ((Dof x).host.g k - 1)) = _
  rw [map_pow, hz', ← Complex.exp_nat_mul]
  congr 1
  have hc : (((Dof x).host.g k - 1 : ℕ) : ℂ) = ((Dof x).host.g k : ℂ) - 1 := by
    rw [Nat.cast_sub hg1.le, Nat.cast_one]
  have hg0 : ((Dof x).host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg1' : ((Dof x).host.g k : ℂ) - 1 ≠ 0 := by
    rw [← hc]; exact Nat.cast_ne_zero.2 (by omega)
  change (((Dof x).host.g k - 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (((Dof x).host.g k * ((Dof x).host.g k - 1) : ℕ) : ℂ)) = _
  rw [Nat.cast_mul, hc]
  field_simp

end State

section Gen

end Gen

end GlobalTheory.HeightCounting.ThetaSt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) := by
  first | exact @GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | exact GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | (intros; apply GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.HeightCounting.Fin3

theorem grpTie_of_LC : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : LC hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) := by
  intro hL K B f T w P x l
  have hc := GlobalTheory.Mem.R3.pins_card_index_ranks _ _ _ _ _ _ _ _ _ _ x.m.z.pins
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  obtain ⟨_, _, _, he0, _, _⟩ := x.m.z.pins.keep.grp
  refine ⟨hc.1, he0, ?_, ?_, hc.2.1, x.m.z.pins.keep.psi.lvl⟩
  · intro g
    rw [hU]
    exact l.rat.rat.lvl g
  · intro u hu i b
    have hu' : (x.m.z.R.eG.trans x.m.z.cG) u ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ hu
    refine ⟨psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩, l.rat.rat.psi u hu', ?_⟩
    exact l.b.Bs.psiU i b _ hu hu'

end GlobalTheory.HeightCounting.Fin3
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false ≠ ⊥ := by
  first | exact @GlobalTheory.RowsAtBase.exists_base_row_of_pins | exact GlobalTheory.RowsAtBase.exists_base_row_of_pins | (intros; apply GlobalTheory.RowsAtBase.exists_base_row_of_pins <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenTranslate

section Act
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem extV_act (hr : R.grp_red_L) (hj : R.models_jV) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (g : G)
    (κ : GA D (Vc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (u : (A.fam.L i t).S.Forms)
    (h : GA D (Vc D i)) :
    R.extV i t (R.jV i t ((A.fam.L i t).r g u)) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t (R.jV i t u) (h * κ) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g u
  have hq : (finHom (Vc D i)).rangeRestrict κ ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    have h1 := hκ.2.1
    exact ⟨h1, trivial⟩
  let q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) q (R.eG g) := hκ.2.2
  have e := hT.2 q hl ((finHom (Vc D i)).rangeRestrict h)
  have hk : (R.cV i).ρ κ⁻¹ = 1 := (hc i).1 _ (inv_mem hκ.1)
  have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
    rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
  have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) = (finHom (Vc D i)).rangeRestrict h * (q : Bridge.Gf (Vc D i)) := map_mul _ _ _
  show (R.cV i).ρ h⁻¹ ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g u)) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e (R.jV i t u) ((finHom (Vc D i)).rangeRestrict (h * κ)))
  have hch : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn (R.βV i) (flagL (R.datVt i t))) (finE_eq (Vc D i) κ)).trans
      (GlobalTheory.LiftEquivariance.ch_eq q).symm)
  refine (congrArg ((R.cV i).ρ h⁻¹) e).trans ?_
  refine (LinearMap.map_smul _ _ _).trans ?_
  exact congrArg₂ (fun (a : ℂ) w => a • w) ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hch.symm))
    (congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e (R.jV i t u)) hrr.symm))
end Act

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem liftForm_lvlOp (hOk : A3.A.fam.Ok 1) (i : Fin D.R.m) (t : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) :
    liftForm A3.A F.P0 F.ψ0 i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x) =
      ∑ g, a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hOk.conj (A3.A.fam.L i t).S ((hOk.lifts i t).hpos _) (A3.A.fam.L i t).r (hOk.lifts i t).act
    _ _ a ha x

theorem read_rat (hB : R.BaseW F) (hOk : A3.A.fam.Ok 1) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (hC : CenRead Y cG) (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i))
    (hκ : ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g))
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (hza : ∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g))
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) (h : GA D (Vc D i)) :
    (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)))).1 h =
      ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
        (Y.IL.jMt (Y.tup t) ht i (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))).1 (h * κ g) := by
  have e1 := congrArg (fun y => (Y.IL.jMt (Y.tup t) ht i y).1 h) (hC i t z a hza x)
  refine e1.trans ?_
  refine (congrFun (Y.mtRead i t ht _) h).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun g _ =>
    congrArg (fun w => ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • w) (congrFun (Y.mtRead i t ht x) (h * κ g)).symm)
  have e2 := liftForm_lvlOp (F := F) hOk i t a ha x
  refine (congrArg (fun v => R.extV i t (R.jV i t v) h) e2).trans ?_
  have e3 := map_sum (R.jV i t) (fun g => a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)) Finset.univ
  have e4 := map_sum (R.extV i t) (fun g => (R.jV i t) (a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))) Finset.univ
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e3).trans e4)).trans ?_
  refine (Finset.sum_apply h _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (R.jV i t) (a.coeff g) ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))
  have e6 := LinearMap.map_smul (R.extV i t) (D.what₂.embLL (a.coeff g)) (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e5).trans e6)).trans ?_
  refine (Pi.smul_apply (D.what₂.embLL (a.coeff g)) (R.extV i t (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))) h).trans ?_
  have e7 := extV_act hB.grp.red_L hB.models.jV hB.models.cV i t g (κ g) (hκ g) (liftForm A3.A F.P0 F.ψ0 i t x) h
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) e7).trans ?_
  refine (smul_smul _ _ _).trans ?_
  exact congrArg (fun c : ℂ => (c * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
    R.extV i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) (h * κ g)) (hza g)

end Read

theorem sum_reindex {G H W : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup W] [Module ℂ W] (e : G ≃* H)
    (c : H → ℂ) (ch : G → ℂ) (w : G → W) :
    ∑ g, (c (e g) * ch g) • w g = ∑ g₀, c g₀ • (ch (e.symm g₀) • w (e.symm g₀)) :=
  Fintype.sum_equiv e.toEquiv _ _ fun g => by simp [smul_smul]

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.BaseW F → A3.A.fam.Ok 1 → CenRead Y cG → ∀ (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i)), (∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)) → ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (y : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)) (h : GA D (Vc D i)), (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z y)).1 h = ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • (Y.IL.jMt (Y.tup t) ht i y).1 (h * κ g) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y cG hB hOk hC i t ht κ hκ z y h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G (R.eG.trans cG).toEquiv
  let ad : GA D (Vc D i) → D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W := fun h' =>
    { toFun := fun y' => (Y.IL.jMt (Y.tup t) ht i y').1 h'
      map_add' := fun y₁ y₂ => by rw [map_add (f := _)]; rfl
      map_smul' := fun c y₁ => by rw [map_smul]; rfl }
  let ch : G → ℂ := fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹
  have key : ∀ (g₁ : G0g D.nd) (y' : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)),
      ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩ y') =
        ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g) y' := by
    intro g₁
    have tie : ∀ g, D.what₂.embLL ((GlobalTheory.CenLocAt.avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff g) =
        (GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) := fun g => by
      rw [GlobalTheory.CenLocAt.avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      (ad h).comp (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩)
    let F2 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g)
    have hb := (D.what₂.jMt_basis (Y.tup t) ((i : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt i t).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)) b)
      rw [← hx']
      refine (read_rat hB hOk Y cG hC i t ht κ hκ ⟨_, GlobalTheory.CenLocAt.avgC_mem g₁⟩ _ (GlobalTheory.CenLocAt.avgK_comm _ _) tie x' h).trans ?_
      simp only [F2, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    intro y'
    have := LinearMap.congr_fun hF y'
    simpa only [F1, F2, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] using this
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV i).W :=
    { toFun := fun z' => ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z' y)
      map_add' := fun z₁ z₂ => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c z₁ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hl := GlobalTheory.CenLocAt.lin_center Φ (fun g₀ => ch ((R.eG.trans cG).symm g₀) • ad (h * κ ((R.eG.trans cG).symm g₀)) y)
    (fun g₁ => (key g₁ y).trans (sum_reindex _ _ _ _)) z
  exact hl.trans (sum_reindex (R.eG.trans cG) _ ch (fun g => ad (h * κ g) y)).symm

end GlobalTheory.CenTranslate
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def sgTw (x : St P) (N : TwNew (Dof x)) : SameGrp (B := B) (C := w.C) x.o.Z (oTw x N).Z where
  e _ := Equiv.refl _
  pl _ _ := rfl
  e0 _ := rfl

def datTw (x : St P) (N : TwNew (Dof x)) : Dat (w.st (oTw x N).Z) w.I P.hX T P.Wt :=
  DatCopy.copy (a := x.o.Z) (oTw x N).Z (sgTw x N) x.m.z

def sideTw (x : St P) (N : TwNew (Dof x)) : Side0 (oTw x N) where
  cen := x.s.cen
  tie := x.s.tie
  is := x.s.is
  RR := x.s.RR
  frames := x.s.frames
  jEE := x.s.jEE
  basis := x.s.basis
  norm := x.s.norm

theorem fitsTw (x : St P) (N : TwNew (Dof x)) : (oTw x N).Fits := ⟨x.fits.div, x.fits.grp, ⟨(by with_unfolding_all exact (x.fits.grpAt.pl :)), (by with_unfolding_all exact (x.fits.grpAt.idem :)), (by with_unfolding_all exact (x.fits.grpAt.cen :))⟩,
  fun eR h => ⟨(by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).amb : _)), (by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).mt : _))⟩⟩

def stTw (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) : St P :=
  ⟨oTw x N, fitsTw x N, x.G_eq, x.etaF, x.bk, m, hc, hh, sideTw x N, r, hp⟩

end GlobalTheory.HeightCounting.Up

end
end
