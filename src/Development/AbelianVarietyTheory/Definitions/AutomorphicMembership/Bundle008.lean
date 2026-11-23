module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.GaloisCohomology.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle001
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

def ShaOK (B : Pre) (s : ℕ → ℕ → ℚ) : Prop :=
  ∃ ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p,
    ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → s p e = (n : ℚ)

abbrev Chi (B : Pre) : Type := ∀ k : Fin 2, Fin B.R.f → Fin B.R.m → (ZMod (B.host.g k))ˣ

structure IsSer (r g N : ℕ) (e : Polynomial (ZMod g) → MonoidAlgebra ℂ (GL (Fin r) (ZMod g))) : Prop where
  idem : ∀ f, e f * e f = e f
  central : ∀ f a, e f * a = a * e f
  orth : ∀ f f', f ≠ f' → e f * e f' = 0
  zero : ∀ f, e f = 0 ↔ ¬ (f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0)
  sum : ∃ S : Finset (Polynomial (ZMod g)),
    (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, e f = 1
  rat : ∀ f x, (e f).coeff x ∈
    IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}

end GlobalTheory.MemN
end
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem baseLattice_full {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    Submodule.IsFullLattice E S.L0 :=
  { toIsLattice := S.standardTuple_isLattice
    span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular
      S.hT S.herm S.nondeg S.standardTuple_isLattice S.baseLattice_isUnimodular }

structure Cols0 (B : Pre) where
  mem : ∀ u : B.Word, Member B.R (Tau B.R) (B.hcW u)
  A_T : ∀ u, (mem u).A.T = B.T u
  A_duStar : ∀ u, (mem u).A.duStar = B.duStar u
  A_Dstar : ∀ u, (mem u).A.Dstar = B.Dstar
  A_GamP : ∀ u, (mem u).A.GamP = B.GamP
  clsLat : letI := B.host.cmStar; ∀ u i, (mem u).C.cls i → Submodule (𝓞 B.host.E) (B.sp.X i).V
  clsLat_lat : letI := B.host.cmStar; ∀ u i c, Submodule.IsFullLattice B.host.E (clsLat u i c)

  Tup : Type
  mu0 : Tup
  muStar : Tup
  muStar' : Tup

  chTw : ∀ u, Tup → ColumnChain B.R (Tau B.R) (B.hcW u)
  memberColumns_twistedChain_base : ∀ u, chTw u mu0 = (mem u).C
  e0Tw : ∀ u μ, ((mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((chTw u μ).cls 0 → (chTw u μ).Y 0 → ℂ)
  PTw : ∀ u μ, PeriodMap B.R (chTw u μ)

  Dt : Type
  [instDt : CommGroup Dt]
  detCls : ∀ u i, (mem u).C.cls i → Dt
  muTil : ℕ → Dt →* ℂˣ
  chiD : Dt →* ℂˣ
  UO : Subgroup Dt
  chiD_UO : ∀ x ∈ UO, chiD x = 1
  e1Dt : letI := B.host.cmStar; unitary B.host.E →* Dt
  rest_detCharacter_on_unitary_eq : letI := B.host.cmStar; ∀ z : unitary B.host.E,
    ((chiD (e1Dt z) : ℂˣ) : ℂ) = ∏ τ : (Tau B.R), (B.host.emb ((τ : B.R.Psi) : B.R.GG) (z : B.host.E))⁻¹
  relDet : letI := B.host.cmStar; ∀ N, SDLat B.host.E N → SDLat B.host.E N → Dt ⧸ UO
  relDet_self : letI := B.host.cmStar; ∀ N L, relDet N L L = 1
  relDet_mul : letI := B.host.cmStar; ∀ N L L' L'', relDet N L L' * relDet N L' L'' = relDet N L L''
  relDet_smul : letI := B.host.cmStar; ∀ N (L L' : SDLat B.host.E N) (γ : Matrix.unitaryGroup (Fin N) B.host.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) B.host.E) L.1 → relDet N L L' = QuotientGroup.mk (e1Dt ⟨(γ : Matrix (Fin N) (Fin N) B.host.E).det, Matrix.det_of_mem_unitary γ.2⟩)
  rhoDet_eq_inv_muTilde_chiD_pow : ∀ u i (c : (mem u).C.cls i),
    (mem u).C.rhoDet i c = (((muTil (i + 1) (detCls u i c))⁻¹ *
      (chiD (detCls u i c)) ^ (-(((B.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ u i (c : (mem u).C.cls (i + 1)),
    (mem u).C.rhoDet' i c = ((muTil (i + 1) (detCls u (i + 1) c) *
      (chiD (detCls u (i + 1) c)) ^ ((((B.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

attribute [instance] Cols0.instDt

structure Cols (B : Base) extends Cols0 B.toPre where
  fm : ∀ u, MemberForms B.LL B.embLL B.places (Tau B.R) (B.hcW u) (mem u).C (mem u).A (mem u).P

end GlobalTheory.Mem

end
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure PreX (B : Pre) where
  piG : Fin 2 → 𝓞 B.host.E
  piG_K : ∀ i, (piG i : B.host.E) ∈ B.host.K
  piG_norm : ∀ i, (piG i : B.host.E) * B.host.conj (piG i : B.host.E) = (B.host.g i : B.host.E)
  piG_cong : ∀ i, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∣ piG i - 1
  piT : B.Word → 𝓞 B.host.E
  piT_K : ∀ u, (piT u : B.host.E) ∈ B.host.K
  piT_norm : ∀ u, (piT u : B.host.E) * B.host.conj (piT u : B.host.E) = (B.T u : B.host.E)
  piT_cong : ∀ u, ((B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) : 𝓞 B.host.E) ∣ piT u - 1
  pde_split : (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E
  ccK_top : B.host.ccK = ⊤
  e_even : ∀ j : Fin B.R.m, UpperTheory.MUQ (fun τ : Tau B.R => B.host.emb (τ : B.R.GG)) (fun τ => (B.hc τ).e j)

  hcW_inj : Function.Injective B.hcW

  a : ℝ
  g_big : ∀ i, 2 * B.R.f * B.R.k < B.host.g i - 1
  T_gt : ∀ u, 4 * a < (B.T u : ℝ)
  a_gt : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < 4 * a
  spread_le : ∀ u j, j ≤ B.R.m → ∀ τ, ((Formalism.BasicNotions.Examples₂.lamOf (B.hcW u τ) j).spread : ℝ) ≤ 2 * a

def Base.tauLL (B : Base) (τ : Tau B.R) : B.host.E →+* B.LL :=
  B.embE.comp (B.host.sigmaOf (τ : B.R.GG) : B.host.E →+* B.host.E)

end GlobalTheory.Mem

end
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

def DiagSpaces {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (S : Spaces R F E) : Prop :=
  ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
    (∀ j, S.X j = Formalism.BasicNotions.Examples₂.posSpace hstar (R.N j)) ∧ S.X' = Formalism.BasicNotions.Examples₂.posSpace hstar R.rankX' ∧
    (∀ j, S.Y j = Formalism.BasicNotions.Examples₂.stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
    (∀ j, 1 ≤ j → j ≤ R.m →
      S.W j = Formalism.BasicNotions.Examples₂.stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
    ∀ j, S.V j = Formalism.BasicNotions.Examples₂.stdSpace hstar R.nV (fun _ => S.Vneg j) (if S.Vneg j then 0 else R.nV) (if S.Vneg j then R.nV else 0)

structure PreCh where
  R : Ranks
  H : Host R
  ccK_top : H.ccK = ⊤
  level_cond : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1
  BB_disj : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1))
  Word : Type
  [wordFin : Fintype Word]
  u₀ : Word
  hcW : Word → Tau R → HCParam R
  hcW_v : ∀ u τ, (hcW u τ).v = (hcW u₀ τ).v
  hcW_b : ∀ u τ, (hcW u τ).b = (hcW u₀ τ).b
  hcW_e : ∀ u τ, (hcW u τ).e = (hcW u₀ τ).e
  hcW_first : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u₀ τ).u ⟨0, h⟩
  hcW_last : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u₀ τ).u ⟨R.k - 1, by omega⟩

attribute [instance] PreCh.wordFin

structure LevCh (P : PreCh) where
  T : P.Word → ℕ
  T_prime : ∀ u, (T u).Prime
  T_cond : ∀ u, T u % (P.H.QS * P.H.q * P.H.d) = 1
  piT : P.Word → 𝓞 P.H.E
  piT_K : ∀ u, (piT u : P.H.E) ∈ P.H.K
  piT_norm : ∀ u, (piT u : P.H.E) * P.H.conj (piT u : P.H.E) = (T u : P.H.E)
  piT_cong : ∀ u, piT u - 1 ∈
    Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)}
  T_ne_pde : ∀ u, T u ≠ P.H.pde ∧ T u ≠ P.H.pde'
  duStar : P.Word → ℕ
  duStar_pos : ∀ u, 0 < duStar u
  Dstar : ℝ
  Dstar_pos : 0 < Dstar
  GamP : ℝ
  one_lt_gammaP : 1 < GamP
  T_win : ∀ u, (Dstar / duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamP ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) *
      ((Dstar / duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamP ^ (-(2 : ℝ) / (P.R.f * P.R.k)))

@[reducible] def LevCh.host {P : PreCh} (L : LevCh P) : Host P.R :=
  { P.H with
    levelPrimes := P.H.levelPrimes ∪ Finset.univ.image L.T
    g_level := fun i => Finset.mem_union_left _ (P.H.g_level i)
    pde_level := ⟨Finset.mem_union_left _ P.H.pde_level.1, Finset.mem_union_left _ P.H.pde_level.2⟩
    ccK_coprime := fun p _ => by rw [P.ccK_top, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := fun p hp => by
      rcases Finset.mem_union.1 hp with h | h
      · exact P.H.level_coprimeS p h
      · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
        have h1 : Nat.gcd (L.T u) P.H.QS ∣ P.H.QS * P.H.q * P.H.d :=
          ((Nat.gcd_dvd_right _ _).mul_right _).mul_right _
        have h2 := (Nat.dvd_mod_iff h1).2 (Nat.gcd_dvd_left (L.T u) P.H.QS)
        rw [L.T_cond u] at h2
        exact Nat.dvd_one.1 h2 }

theorem LevCh.piT_ne {P : PreCh} (L : LevCh P) (u : P.Word) : (L.piT u : P.H.E) ≠ 0 := by
  intro h
  have h1 := L.piT_norm u
  rw [h, zero_mul] at h1
  exact (L.T_prime u).ne_zero (by exact_mod_cast h1.symm)

def Pre.ofCh (P : PreCh) (L : LevCh P) (sp : @Spaces P.R L.host.F L.host.E _ _ _ _ L.host.cmStar _)
    (hT : letI := L.host.cmStar; sp.T = L.T P.u₀)
    (hY : letI := L.host.cmStar; ∀ j, j ≤ P.R.m → ∀ τ : L.host.E →+* ℂ, (sp.Y j).sig τ = sigYD P.R j)
    (hA : letI := L.host.cmStar; ∀ j, 0 < j → j < P.R.m → HasHyperbolicAuxiliaryFrame sp j)
    (hV : letI := L.host.cmStar; ∀ j, 1 ≤ j → j ≤ P.R.m → sp.Vneg j = false)
    (hz : letI := L.host.cmStar; (sp.X P.R.m).hT sp.z sp.z = (sp.T : L.host.E)) : Pre where
  R := P.R
  host := L.host
  sp := sp
  Y_sigval := hY
  auxiliaryFrame := hA
  V_pos := hV
  z_norm := hz
  ccK_top := P.ccK_top
  BB_disj := P.BB_disj
  level_cond := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact P.level_cond p h
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
      exact ⟨L.T_prime u, L.T_cond u⟩
  Word := P.Word
  u₀ := P.u₀
  hc := P.hcW P.u₀
  hcW := P.hcW
  hcW_base := rfl
  hcW_v := P.hcW_v
  hcW_b := P.hcW_b
  hcW_e := P.hcW_e
  hcW_first := P.hcW_first
  hcW_last := P.hcW_last
  T := L.T
  T_level := fun u => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  T_norm := fun u => ⟨L.piT u, L.piT_K u, L.piT_norm u, L.piT_cong u⟩
  sp_T := hT
  cOf := fun u => ((L.piT P.u₀ : P.H.E) / (L.piT u : P.H.E) : P.H.E)
  cOf_ne := fun u => div_ne_zero (L.piT_ne _) (L.piT_ne _)
  cOf_eq := fun u => by
    have h1 := L.piT_ne u
    have h2 : P.H.conj (L.piT u : P.H.E) ≠ 0 := (map_ne_zero _).2 h1
    show ((L.piT P.u₀ : P.H.E) / (L.piT u : P.H.E)) * P.H.conj ((L.piT P.u₀ : P.H.E) / (L.piT u : P.H.E)) * (L.T u : P.H.E) =
      (L.T P.u₀ : P.H.E)
    rw [← L.piT_norm u, ← L.piT_norm P.u₀, map_div₀]
    field_simp
  T_ne_pde := L.T_ne_pde
  duStar := L.duStar
  duStar_pos := L.duStar_pos
  Dstar := L.Dstar
  Dstar_pos := L.Dstar_pos
  GamP := L.GamP
  one_lt_gammaP := L.one_lt_gammaP
  T_win := L.T_win

end GlobalTheory.Mem

end
end
