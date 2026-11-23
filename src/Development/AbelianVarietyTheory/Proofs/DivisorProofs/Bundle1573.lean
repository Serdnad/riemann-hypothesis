module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle252
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle131
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dite_eq_left h]⟩

end GlobalTheory.LKCx.Regroup
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime]

def PLv (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type := Projectivization ℂ (Fin G.n → ℂ)

theorem toV_injective (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) :
    Function.Injective (Matrix.toLin' (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) := by
  intro a b h
  have h' := congrArg (Matrix.toLin' (((toV G v β y)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ)) h
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h'

instance (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : MulAction (grp G β) (PLv G v β) where
  smul y l := Projectivization.map (Matrix.toLin' (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))
    (toV_injective G v β y) (l : Projectivization ℂ (Fin G.n → ℂ))
  one_smul l := by
    change Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = l
    induction (l : Projectivization ℂ (Fin G.n → ℂ)) using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk]
      congr 1
      simp [Matrix.toLin'_apply]
  mul_smul y y' l := by
    change Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.map _ _ (Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)))
    induction (l : Projectivization ℂ (Fin G.n → ℂ)) using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk, Projectivization.map_mk, Projectivization.map_mk]
      congr 1
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

abbrev Ys (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  LeftCosets ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') × PLv G v β

def cxF (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (a : Ys G v β x t hx Kf K') (y : grp G β) : ℂ :=
  if 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) then
    f ((LeftCosets.rep _ _ a.1).1⁻¹ * toAfF G β x t hx y * (LeftCosets.rep _ _ a.1).1) *
      f' ((LeftCosets.rep _ _ a.1).2⁻¹ * toP1 G β y * (LeftCosets.rep _ _ a.1).2) *
      wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
  else 0

end GlobalTheory.CxUnfold
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem herm_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → (herm G v β).IsHermitian ∧ (herm G v β).det ≠ 0 ∧
      ∃ Z : GL (Fin G.n) ℂ, herm G v β =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G v β _ hR
  obtain ⟨z, hz⟩ := hR
  have hc : ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
    set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
    change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
    have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
      change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
      rw [psiR_tmul, one_smul]
    have h1 := congrArg (G.psiR v) hz
    rw [map_mul, map_mul, psiR_starT, hb] at h1
    simp only [Units.val_one, map_one] at h1
    rw [← hZm] at h1
    have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
    set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
    have hMb : M * G.psi v (β : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
      have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
        Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
      simpa [Matrix.mul_assoc] using this
    have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
      calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
    rw [h3]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ := hc
  refine ⟨?_, ?_, Z, hZ⟩
  · rw [hZ]
    exact isHermitian_conjTranspose_mul_mul _ (G.gram_herm v)
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hZd : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse
      (show ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * Z = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one])).ne_zero
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hZd) (G.gram_det v)) hZd

end GlobalTheory.LKCx
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn GlobalTheory.RunDepth

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_kaR {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m)
    (w : WeightFamilies.Wt D ((i : ℕ) + 1))
    (hP : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).1), w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k)
    (hM : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).2),
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k)
    (hn : w.n = D.R.nV) : w = kaR Tp hK ((i : ℕ) + 1) := by
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have h1 := (inR_succ i).1
  have h2 := (inR_succ i).2
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ h1 h2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  have eP : w.aP = (kaR Tp hK ((i : ℕ) + 1)).aP := by
    funext τ a
    have h := (hK _ h1 h2 τ).1 a
    have h' := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have e := kaWt_big D hK (even_nV Tp) _ h1 h2 τ a
    rw [← h, ← hp, ← e] at h'
    rw [hP τ a, hs τ]
    exact_mod_cast h'
  have eM : w.aM = (kaR Tp hK ((i : ℕ) + 1)).aM := by
    funext τ c
    have h := (hK _ h1 h2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := GlobalTheory.RecordWeightVec.aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have e := kaWt_small D hK (even_nV Tp) _ h1 h2 τ c
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h, ← Int.cast_neg, ← e] at h'
    rw [hM τ c, hs τ]
    exact_mod_cast h'
  have en : w.n = (kaR Tp hK ((i : ℕ) + 1)).n := hn.trans (kaWt_n _ _ _ _).symm
  generalize kaR Tp hK ((i : ℕ) + 1) = u at eP eM en
  cases w; cases u
  simp only at eP eM en
  subst eP eM en
  rfl

theorem exists_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst), J.Q.Canon → HalfEX J.toCore EX → RunsOk fw r → ∃ O : OnObj ((R.toCx F).data F.cr false) (Mir R) c, IsRec Tp hK EX F fw r O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c _ hE ok
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hc : LawsCore J.toCore := (ok.laws v₁).p.toLawsCore
  have hinj : Function.Injective D.what₂.OtoLL := fun x y hxy => by
    obtain ⟨x, rfl⟩ := J.Q.eO.surjective x
    obtain ⟨y, rfl⟩ := J.Q.eO.surjective y
    rw [← fw.alg_eq, ← fw.alg_eq] at hxy
    exact congrArg _ (RingOfIntegers.ext ((algebraMap J.Q.c.F D.what₂.LL).injective hxy))
  have hκ : ∀ i : Fin D.R.m, κ i = kaR Tp hK ((i : ℕ) + 1) := fun i =>
    eq_kaR Tp hK i (κ i) (fun τ => (fw.kap i τ).1) (fun τ => (fw.kap i τ).2.1)
      (fw.kap i (plOf D (false, Classical.arbitrary _))).2.2
  choose ρ hρ using fun i : Fin D.R.m =>
    ActionPin.exists_rep (T := (r.used v₁).full) (inst := inst) (R := R) (ok.action v₁ i) (mirIncl R)
  obtain ⟨O, z, act, y, ht⟩ := exists_tiedObj (F := F) (fw := fw) (hc := hc) (run := r.used) (h := fun v => (ok.laws v).p)
    (hinj := hinj) (EX := EX) (p := ownAt D) (wL := fun _ i => lR Tp hK ((i : ℕ) + 1))
    (wF := fun _ i => fR Tp hK ((i : ℕ) + 1)) (nT := Tp.TO) (ℓ := r.lev) (ph := fun _ => 1) (c := c) (mirIncl R)
    (blankObj D _ (Mir R) c fun i => R.nW i) ok.action ρ (fun _ i => hρ i)
  letI st : StarRing (𝓞 D.host.E) := J.Q.H.starRing
  letI := hostAlg D
  letI : ∀ s : GlobalTheory.RealIndexBound.RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  have hφ : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.what₂.LL x =
      algebraMap J.Q.c.F D.what₂.LL ((iE D hinj (recB hc) x : 𝓞 J.Q.c.F) : J.Q.c.F) := fun x => by
    refine Eq.trans ?_ (fw.alg_eq _).symm
    refine (oEOsFun_spec D x).symm.trans (congrArg D.what₂.OtoLL ?_)
    exact (J.Q.eO.apply_symm_apply _).symm
  have hσ : ∀ v (i : Fin D.R.m), O.σ v i =
      sigAt (Dw := J.Q.Dw ((i : ℕ) + 1)) (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((i : ℕ) + 1) := fun v i => by
    letI : Algebra (recB (ok.laws v).p.toLawsCore).KO D.what₂.LL := inst
    refine (ht v i).1.toFormTieK.σ_eq.trans ?_
    rw [hκ i]
    exact (GlobalTheory.ScalarOfRun.sigAt_eq_sigRec D L Pm Tp hK (r.used v).full.toTop (ok.laws v).p hinj EX _ (inR_succ i) hE
      D.what₂.LL (algebraMap J.Q.c.F D.what₂.LL) hφ).symm
  refine ⟨{ O with
    E := fun v (j : Fin D.R.m) =>
      EAt (Xo := J.Q.Xo ((j : ℕ) + 1)) (c := J.Q.c) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) v ((j : ℕ) + 1)
    nnK := fun j : Fin D.R.m => nnKAt (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((j : ℕ) + 1)
    T := (Tp.TO : ℝ)
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := (D.R.k : ℝ)
    m := (D.R.m : ℝ)
    f := (D.R.f : ℝ)
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1)) : ℕ) : ℝ)
    rr := (D.R.r : ℝ)
    Nc := L.Nc
    T2 := D.host.T2.card
    pde := D.host.pde }, ok, hκ, ⟨hc, hinj, z, act, y, fun v i => ⟨{ (ht v i).1 with }, (ht v i).2⟩⟩, ⟨st, ?_⟩,
    rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun j => inR_succ j, fun _ => rfl, fun a => ?_, fun _ _ => rfl, hσ, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun j => ?_⟩
  · show star (D.embE (a : D.host.E)) = D.embE ((J.toCore.Q.H.bar a : 𝓞 D.host.E) : D.host.E)
    rw [bar_core, barE_eq_conj, D.embE_conj]
  · exact Nat.cast_le.2 (Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1))) (Finset.mem_univ j))

end GlobalTheory.BigOn

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), ∃ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁

  have hD : ∀ p q, symp (cA σ) (-1) (incM F X.J) (incM F W.J) p q =
      (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2 := M.co.form
  have hcross := GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic F E σ n d d₁ X.J W.J H' (fun u => (hH.orth u).1)
  have hiso : ∀ a ∈ lagr M M₁ H', ∀ b ∈ lagr M M₁ H', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    intro a ha b hb
    obtain ⟨u, hu, z, hz, hea⟩ := ha
    obtain ⟨u', hu', z', hz', heb⟩ := hb
    have ea : hat a = M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [← hea, LinearEquiv.apply_symm_apply]
    have eb : hat b = M.co.e (u' + incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) := by
      rw [← heb, LinearEquiv.apply_symm_apply]
    have h1 := GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic F E σ n d d₁ X.J W.J H' hH.xx u hu u' hu'
    have h2 := hcross u' hu' z
    have h3 := hcross u hu z'
    have h4 := GlobalTheory.T.symplectic_form_restricted_plane F E σ n d d₁ X.J W.J W₁.J H'.ι hH.gram z z'
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W₁.J) z z' at h4
    rw [M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_zero] at h4
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = 0 at h4
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 at h1
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) u' = 0 at h2
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) u = 0 at h3
    rw [hD] at h1 h2 h3 h4
    apply (AdeleRing.algebraMap_injective (𝓞 F) F)
    have ha1 : (fun i => algebraMap F (AF F) (a.1 i)) = (hat a).1 := rfl
    have ha2 : (fun i => algebraMap F (AF F) (a.2 i)) = (hat a).2 := rfl
    have hb1 : (fun i => algebraMap F (AF F) (b.1 i)) = (hat b).1 := rfl
    have hb2 : (fun i => algebraMap F (AF F) (b.2 i)) = (hat b).2 := rfl
    rw [RingHom.map_dotProduct, RingHom.map_dotProduct]
    simp only [Function.comp_def]
    rw [ha1, ha2, hb1, hb2, ea, eb]
    simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination h1 + h2 - h3 + h4
  refine ⟨lagr M M₁ H', hiso, ?_, ?_⟩
  ·
    have hrat := GlobalTheory.T.rational_model_coordinates F E σ n d X W M hP.good.rat
    have hrat₁ := GlobalTheory.T.rational_model_coordinates F E σ n d₁ X W₁ M₁ hP₁.good.rat
    obtain ⟨f, hf, hfe⟩ := hrat
    obtain ⟨f₁, hf₁, hfe₁⟩ := hrat₁
    have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
    obtain ⟨K, hK, hKz⟩ := GlobalTheory.T.rational_lagrangian_subspace_exists F E σ n d₁ X W₁ M₁ h2 f₁ hf₁ hfe₁
    have hinj := mul_transpose_injective F E σ n d d₁ W.J W₁.J H'.ι hH.gram
      (GlobalTheory.T.skew_determinant_ne_zero_first_space F E σ B d₁ W₁ r₁ s₁ hP₁.skew)
    refine le_antisymm ?_ ?_
    · exact GlobalTheory.T.lagrangian_dimension_bound F _ _ hiso
    · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact GlobalTheory.T.quadratic_injective_plane_coordinates F E σ n d d₁ X W W₁ M M₁ H' h2 hH.rank hH.xy (fun u => (hH.orth u).2) hinj f hf hfe K hK hKz
  ·
    intro t w hw
    obtain ⟨u, ⟨y, rfl⟩, z, hz, he⟩ := hw
    have ew : hat w = M.co.e (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [← he, LinearEquiv.apply_symm_apply]
    refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], fun φ => ?_⟩
    have h0 := hcross _ ⟨t • y, rfl⟩ (t • z)
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)
      (Matrix.vecMulVec (t • y) (incV F H'.x)) = 0 at h0
    rw [hD] at h0
    rw [Darboux.rho, Darboux.rho, schr_comp, ← map_add (f := _)]
    have hs : (M.co.e (Matrix.vecMulVec (t • y) (incV F H'.x))).1 ⬝ᵥ
          (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)).2 -
        (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
          (M.co.e (Matrix.vecMulVec (t • y) (incV F H'.x))).2 = 0 := by linear_combination -h0
    rw [hs, mul_zero, AddChar.map_zero_eq_one, one_smul]
    have hm : Matrix.vecMulVec (t • y) (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ =
        t • (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]
    rw [hm, LinearEquiv.map_smul, ← ew]
    rfl

end GlobalTheory.MixedLagr

end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ),
      (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
      ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A) (c : primDR A) (x : G.RigExt),
        GlobalTheory.PtExt.IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ R _ N hN A _ hA G t c x hx h0
  have : IsCommMonObj A := hA.comm
  obtain ⟨d, z, w, hz, -, rfl⟩ := hx
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow]; exact hN

  have hmk : (Submodule.Quotient.mk z : G.VecExt) = 0 := h0
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmk
  have hcob : d.coc N = cobOne R (G.A N) (B.1 N) := by
    rw [← hz N, ← hB]; rfl

  have hchiN : chi (p ^ N) d.g (G.A N) (t.y N) = 0 := by
    rw [← Dat.diagSum_coc R A p G t c d N hN, hcob]
    exact diagSum_cobOne_eq_zero p R G N hN (B.1 N)

  have hchi : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt A D), y ^ (p ^ N) = 1 →
      chi (p ^ N) d.g D y = 0 := by
    intro D _ _ y hy
    obtain ⟨φ, rfl⟩ := t.surj N D y hy
    have h1 : t.y N ^ (p ^ N) = 1 := t.y_pow N
    have hn := chi_natural (p ^ N) R hq A (fv d.f) d.g d.add (G.A N) D φ (t.y N)
    rw [h1, hchiN, map_zero, sub_zero, sub_self] at hn
    exact hn
  have hcoc := (fv_isCoc_and_ev_eq R A d.f).1
  have hsym := isSymCoc_of_isAdd R A hA (fv d.f) d.g d.add
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  obtain ⟨k, hk⟩ := Descent.exists_isCob (p ^ N) R hq A (fv d.f) d.g hcoc d.add hsym hchi
    (fun D _ _ y ↦ PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) hpos D y)
  have hF := (mem_hodgeFiltration_iff_pointwiseCoboundary R A d.f).2 ⟨k, hk⟩
  rw [d.cl] at hF
  exact hF

end GlobalTheory.PtExt
end
