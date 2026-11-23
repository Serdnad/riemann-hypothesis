module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle040
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle041
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle037
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle637
public import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Tactic.Basify
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.TrueCx GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


open Classical in
theorem expo_detSym (τ : GlobalTheory.AllWt.Psi H) (a : ℕ → Bool) (R : Option ℝ) (z : Letter Dw) :
    expo Dw (detSym Dw a R τ.1) z = if z.1 = τ.1 then 1 else if z.1 = conjEmb τ.1 then -1 else 0 := by
  obtain ⟨ρ, i⟩ := z
  have hne : conjEmb τ.1 ≠ τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e.symm ▸ τ.2)
  have hp : Dw.mult τ.1 = Dw.p := if_pos τ.2
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := if_neg (GlobalTheory.AllWt.conj_not_mem τ)
  have hl : ∀ (ρ' : E →+* ℂ) (k : ℕ), letterOf Dw (.inl (ρ', k)) = some ⟨ρ, i⟩ ↔ ρ' = ρ ∧ k = i := fun ρ' k => by
    constructor
    · intro h
      simp only [letterOf] at h
      split_ifs at h
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj h)
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩
    · rintro ⟨rfl, rfl⟩
      exact dif_pos i.2
  have h1 : expo Dw (detSym Dw a R τ.1) ⟨ρ, i⟩ = ∑ k ∈ Finset.range (Dw.p + Dw.q), expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ :=
    (Finsupp.sum_finsetSum_index (h := fun (a : Sym E) (n : ℤ) => if letterOf Dw a.2.2 = some ⟨ρ, i⟩ then n else 0)
      (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)).symm
  have h2 : ∀ k, expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ = if k < Dw.p then (if τ.1 = ρ ∧ k = i then 1 else 0)
      else if conjEmb τ.1 = ρ ∧ Dw.p + Dw.q - 1 - k = i then -1 else 0 := fun k => by
    unfold expo rootSym
    split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> simp only [hl] <;> simp [*]
  have hi := i.2
  simp only [h1, h2]
  split_ifs with e1 e2
  · subst e1
    rw [Finset.sum_eq_single (i : ℕ) (fun k _ hk => by simp [hk, hne]) fun h => absurd (Finset.mem_range.2 (by omega)) h,
      if_pos (by omega), if_pos ⟨rfl, rfl⟩]
  · subst e2
    rw [Finset.sum_eq_single (Dw.p + Dw.q - 1 - i) (fun k hk hk' => by
        have := Finset.mem_range.1 hk
        split_ifs with b1 b2 b3
        · exact absurd b2.1.symm hne
        · rfl
        · omega
        · rfl) fun h => absurd (Finset.mem_range.2 (by omega)) h,
      if_neg (by omega), if_pos ⟨rfl, by omega⟩]
  · exact Finset.sum_eq_zero fun k _ => by simp [Ne.symm e1, Ne.symm e2]

theorem expo_detSym_eq (τ : GlobalTheory.AllWt.Psi H) (a : ℕ → Bool) (R : Option ℝ) :
    expo Dw (detSym Dw a R τ.1) = fun z => -GlobalTheory.AllWt.exOf Dw (flatWt Dw τ) 0 (some z) := by
  funext ⟨ρ, i⟩
  rw [expo_detSym]
  show _ = -(GlobalTheory.AllWt.wtOf Dw (flatWt Dw τ) 0).1 (ρ, i)
  by_cases h : ρ (H.rt : E) = H.rt0
  · have h1 : ρ ≠ conjEmb τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e ▸ h)
    rw [GlobalTheory.AllWt.wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i ((if_pos h : Dw.mult ρ = Dw.p) ▸ i.2)]
    by_cases e : ρ = τ.1 <;> simp [flatWt, parWt, Subtype.ext_iff, e, h1]
  · have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
    have := GlobalTheory.AllWt.wtOf_small (flatWt Dw τ) 0 ⟨_, GlobalTheory.AllWt.conj_mem h⟩ i ((if_neg h : Dw.mult ρ = Dw.q) ▸ i.2)
    simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at this
    rw [this]
    have h2 : conjEmb ρ = τ.1 ↔ ρ = conjEmb τ.1 :=
      ⟨fun e => by rw [← e, GlobalTheory.AllWt.conjEmb_conjEmb], fun e => by rw [e, GlobalTheory.AllWt.conjEmb_conjEmb]⟩
    have h3 : (⟨_, GlobalTheory.AllWt.conj_mem h⟩ : GlobalTheory.AllWt.Psi H) = τ ↔ ρ = conjEmb τ.1 := Subtype.ext_iff.trans h2
    simp only [flatWt, parWt, if_neg h1]
    by_cases e : ρ = conjEmb τ.1
    · rw [if_pos e, if_pos (h3.2 e)]; rfl
    · rw [if_neg e, if_neg (mt h3.1 e)]; rfl

end Expo

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A)

abbrev cmAt (k : s.Comp) : D.what₂.Tau ≃ ((s.U κ.σ₀).X k).Ψ := cmEquiv _ s.isUnf L.ψ k

def bettiCo (k : s.Comp) (τ : D.what₂.Tau) (x : Frame ((s.U κ.σ₀).X k).Ψ N) : ℂ :=
  (hodgeC ((s.U κ.σ₀).X k) (cmAt s L k) τ : ℂ) ^ S.Dw.q * horizGen (cmAt s L k τ) x

abbrev detEx (S : Sig A N j) (τ : D.what₂.Tau) : Letter S.Dw → ℤ :=
  expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))

theorem detEx_eq (S : Sig A N j) (L : CmList A) (τ : D.what₂.Tau) :
    detEx S τ = fun z => -GlobalTheory.AllWt.exOf S.Dw (flatWt S.Dw (L.ψ τ)) 0 (some z) := by
  rw [← expo_detSym_eq S.Dw (L.ψ τ) (fun _ => false) none, L.ψ_val]

def IsBetti (k : s.Comp) (τ : D.what₂.Tau) (σ : (Φ.C k).Y.Fn) (b : ℂˣ) : Prop :=
  ∀ (x : ((s.U κ.σ₀).X k).dom) (a : ℂ),
    CoordAtC (Φ.C k) ((s.U κ.σ₀).un k x) (detEx S τ) σ a ↔ a = b * bettiCo s L k τ x.1


open Classical in
def flBetti (k : s.Comp) (τ : D.what₂.Tau) : ℂˣ :=
  if h : ∃ b, IsBetti s Φ L k τ (flatSec s Φ k τ) b then h.choose else 1

variable {s Φ L} {k : s.Comp} {τ : D.what₂.Tau} {σ : (Φ.C k).Y.Fn} {b b' : ℂˣ}

end GlobalTheory.ShFam.Pad
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open GlobalTheory.CechPic (cls tens dual)

namespace GlobalTheory.ShFam.Pad

abbrev FibCrv (p : ℕ) (X : Scheme.{0}) : Type :=
  {C : Closeds X // IsIrreducible (C : Set X) ∧ topologicalKrullDim (C : Set X) = 1 ∧
    ∀ x ∈ C, (p : X.residueField x) = 0}

namespace FibCrv

variable {p : ℕ} {X : Scheme.{0}} (c : FibCrv p X)

abbrev sch : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal c.1).subscheme

abbrev ι : c.sch ⟶ X := redι c.1

instance isIntegral : IsIntegral c.sch := isIntegral_red c.2.1

theorem natCast_eq_zero : (p : Γ(c.sch, ⊤)) = 0 := by
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  refine absurd hy ((c.sch.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) y trivial _).1 ?_)
  rw [map_natCast, ← map_natCast (c.ι.residueFieldMap y).hom, c.2.2.2 _ ((range_redι c.1).le ⟨y, rfl⟩), map_zero]

instance algebra : Algebra (ZMod p) Γ(c.sch, ⊤) := ZMod.algebra' _ (ringChar _) (ringChar.dvd c.natCast_eq_zero)

def ofImm {C : Scheme.{0}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] (hd : topologicalKrullDim C = 1)
    (hp : (p : Γ(C, ⊤)) = 0) : FibCrv p X :=
  ⟨⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩,
    by simpa using (IrreducibleSpace.isIrreducible_univ C).image i i.continuous.continuousOn,
    (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding rfl).trans hd, by
      rintro _ ⟨y, rfl⟩
      apply (i.residueFieldMap y).hom.injective
      rw [map_natCast, map_zero, ← map_natCast (C.Γevaluation y).hom, hp, map_zero]⟩

variable [Fact p.Prime] {L M N H : LB X}

def deg (L : LB X) : ℤ := interNumRed (ZMod p) (⊤ : Closeds c.sch) ![L.pull c.ι]

theorem deg_eq_of_imm {C : Scheme.{0}} [Algebra (ZMod p) Γ(C, ⊤)] (i : C ⟶ X) [IsClosedImmersion i] [IsReduced C]
    (h : Set.range i = c.1) (hL : L.IsLB) : c.deg L = interNum (ZMod p) (structureModule C) ![L.pull i] := by
  have e : Scheme.IdealSheafData.vanishingIdeal c.1 = i.ker := by
    rw [← InterModel.radical_ker i, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, h, c.1.isClosed.closure_eq]
  let j : C ⟶ c.sch := IsClosedImmersion.lift c.ι i (by rw [← e]; simp)
  have hj : j ≫ c.ι = i := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j ≫ c.ι) := hj ▸ inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j c.ι
  have hr : Set.range j = (⊤ : Closeds c.sch) := Set.eq_univ_of_forall fun y => by
    obtain ⟨x, hx⟩ := h.ge ((range_redι c.1).le ⟨y, rfl⟩)
    exact ⟨x, c.ι.isClosedEmbedding.injective (by rw [← hx, ← hj]; rfl)⟩
  have hL' := LB.isLB_pull hL c.ι
  rw [deg, InterModel.interNumRed_eq_interNumOn (ZMod p) j ⊤ hr, interNumOn_eq_interNum_pull (fun r =>
    RingHom.congr_fun (RingHom.ext_zmod (j.appTop.hom.comp (algebraMap _ _)) (algebraMap _ _)) r) (isLB_vecOne hL')]
  refine interNum_congr_cls _ _ (fun a => LB.isLB_pull (isLB_vecOne hL' a) j) (isLB_vecOne (LB.isLB_pull hL i)) fun a => ?_
  fin_cases a
  exact ((CechPic.pull_comp j c.ι (cls L hL)).symm.trans (by rw [hj])).trans (CechPic.cls_pull hL i _).symm

end FibCrv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev Crv (z : admitted Y i₀) : Type := FibCrv p z.Z.X

def cov (z : admitted Y i₀) : ℕ := levDeg z.Z.dvd (Xo i₀.l) i₀.c (Xo z.Z.i.l) z.Z.i.c

theorem cov_pos (z : admitted Y i₀) : 0 < cov z := levDeg_pos _ _ _ _ _

theorem natCast_mem_nonunits {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp)
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_comap] at h'
    simpa using h'

theorem natCast_eq_zero_iff (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : LocM.Mdl Y i₀) (x : Z.X) :
    (p : Z.X.residueField x) = 0 ↔ ¬ Z.inQ x := by
  refine ⟨fun h (k : CharZero _) => hp.ne_zero (Nat.cast_eq_zero.1 h), fun h => ?_⟩
  let φ : Z.i.c.V W →+* Z.X.residueField x :=
    ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv ≫ Z.s.appTop ≫ Z.X.Γevaluation x).hom
  have hq : (ringChar (Z.X.residueField x)).Prime :=
    (CharP.char_is_prime_or_zero (Z.X.residueField x) _).resolve_right fun k =>
      h ((CharP.ringChar_zero_iff_CharZero _).1 k)
  by_contra hne
  have hc : (ringChar (Z.X.residueField x)).Coprime p :=
    hq.coprime_iff_not_dvd.2 fun k => hne ((ringChar.spec _ _).2 k)
  have := (GlobalTheory.CoeffRings.isUnit_of_coprime _ (natCast_mem_nonunits Z.i.c hp.ne_zero hW) hc).map φ
  rw [map_natCast, ringChar.Nat.cast_ringChar] at this
  exact not_isUnit_zero this

variable [Fact p.Prime]

variable {z : admitted Y i₀}

def degLine (L : FinLB z.Z.X) (c : Crv z) : ℤ := FibCrv.deg c L.lb

variable (z) (c : Crv z)

def degStep (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : ℤ :=
  match h : letterOf Dw st with
  | some x => degLine (z.line b st x h).L c
  | none => 0

def degRoot (τ : E →+* ℂ) (i : ℕ) : ℝ :=
  if i < Dw.p then (degStep z c true (.inl (τ, i)) : ℝ)
  else -(degStep z c true (.inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) : ℝ)

section Line

open ProjSpace

variable (p) {O : Type} [CommRing O] (φ : O →+* ZMod p)

instance isClosedImmersion_baseChange (N : ℕ) : IsClosedImmersion (baseChange N φ) :=
  MorphismProperty.of_isPullback (isPullback_baseChange N φ).flip
    (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective φ))

def lineCrv : FibCrv p (PSpace O 1) :=
  FibCrv.ofImm (baseChange 1 φ) (topologicalKrullDim_eq (ZMod p) 1)
    (by rw [← map_natCast (algebraMap (ZMod p) _), ZMod.natCast_self, map_zero])

theorem degree_twistingSheaf_line : (lineCrv p φ).deg (O1 O 1) = 1 := by
  have h := interNum_const_of_polynomial (ZMod p) (structureModule (PSpace (ZMod p) 1)) (O1_isLB (ZMod p) 1) (d := 1)
    (Polynomial.preHilbertPoly ℚ 1 0) (Polynomial.natDegree_preHilbertPoly ℚ 1 0).le
    (ProjCoh.chi_sheafO_eq_eval (ZMod p) 1)
  rw [Polynomial.coeff_preHilbertPoly_self, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero 1))] at h
  rw [(lineCrv p φ).deg_eq_of_imm (baseChange 1 φ) rfl (O1_isLB O 1),
    interNum_congr_lbIso (ZMod p) _ (L' := fun _ => O1 (ZMod p) 1) (isLB_vecOne (LB.isLB_pull (O1_isLB O 1) _))
      (fun _ => O1_isLB _ 1) fun i => by fin_cases i; exact lbIso_pull_O1 1 φ]
  exact_mod_cast h

end Line

end GlobalTheory.ShFam.Pad
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.GradedPieces GlobalTheory.TotalFrame

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

section Graded

variable {Z B : Mdl Y i₀}

def HasCoord (g : Z.X ⟶ B.X) (L : Lat B) {V : B.X.Opens} {n : ℕ} (m : Fin n → Γ(L.N.toMod, V)) {k : Type} [Field k]
    (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (c : ∀ σ, Fin (Dw.mult σ) → Fin n → k) : Prop :=
  ∃ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V),
    LocM.IsTrans B.i Z.i τ mu ∧ ∀ σ i, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v),
      v ≫ B.tMap.φ = u σ i ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = c σ i l


variable (Z) in
structure LatChart (L : Lat B) : Type where

  g : Z.X ⟶ B.X

  U : Z.X.Opens

  V : B.X.Opens

  n : ℕ

  m : Fin n → Γ(L.N.toMod, V)

  c : ∀ σ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)

  adapted : ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn →
    ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l)


variable (Z) in
def HasLatFlags (L : Lat B) : Prop :=
  (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) ∧ ∀ x : Z.X, ∃ q : LatChart Z L, x ∈ q.U

variable {L : Lat B}

namespace LatChart

def FrameAt (q : LatChart Z L) {k : Type} [Field k] (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ q.U ∧ Z.FlagAt x u ∧ HasCoord q.g L q.m x u fun σ i l => valR x q.U (q.c σ i l)

def IsTr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (a : Γ(Z.X, q.U ⊓ q'.U)) : Prop :=
  ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (u u' : Vecs Dw (Y Z.i).t k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    q.FrameAt x u → q'.FrameAt x u' → (∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) (d σ)) →
      valR x _ a = ∏ σ, ∏ i, d σ i ^ e σ i


open Classical in
def tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : Γ(Z.X, q.U ⊓ q'.U)ˣ :=
  if h : ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val then h.choose else 1

end LatChart


variable (Z L) in
def latLB (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : LB Z.X := ⟨LatChart Z L, LatChart.U, fun q q' => q.tr q' e⟩


variable (L) in
def Curve.degLat {k : Type} [Field k] (c : Curve k Z.X) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : ℤ :=
  c.degOf (latLB Z L e)

end Graded

section Descent

def Mdl.SecVal (Q : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) {U : Q.X.Opens}
    (f : ∀ a, Γ(Q.X, U ⊓ (Q.U a).1)ˣ) {k : Type} [Field k] (x : Sp k ⟶ Q.X) (u : Vecs Dw (Y Q.i).t k) (r : k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ U ∧ ∃ (a : Fin Q.m) (φ : Γ(Q.X, (Q.U a).1) →+* k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ Q.chart a = x ∧ (∀ σ, DiagAt (Y Q.i).t (x ≫ Q.π) ((Q.fr a).bc φ σ) (u σ) (d σ)) ∧
      r = valR x _ (f a).val * ∏ σ, ∏ i, d σ i ^ e σ i

def Mdl.IsAutLB (Q : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (N : LB Q.X)
    (f : ∀ i a, Γ(Q.X, N.U i ⊓ (Q.U a).1)ˣ) : Prop :=
  N.IsLB ∧ ∀ (i i' : N.ι) (k : Type) [Field k] (x : Sp k ⟶ Q.X) (u : Vecs Dw (Y Q.i).t k) (r r' : k), Q.FlagAt x u →
    Q.SecVal e (f i) x u r → Q.SecVal e (f i') x u r' → r' = valR x _ (N.g i i').val * r

def Mdl.cst (Z : Mdl Y i₀) (a : Z.i.c.V W) : Γ(Z.X, ⊤) := Z.s.appTop ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv a)

instance isPrincipal_map_different {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) :
    ((differentIdeal ℤ (𝓞 E)).map (embV c W σ)).IsPrincipal :=
  IsBezout.isPrincipal_of_FG _ (Ideal.FG.map (IsNoetherian.noetherian _) _)

def diffGen {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : c.V W :=
  Submodule.IsPrincipal.generator ((differentIdeal ℤ (𝓞 E)).map (embV c W σ))

def Descends {B : Mdl Y i₀} (Z : Mdl Y i₀) (L : Lat B) (l : Level H) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ)
    (b : (E →+* ℂ) → ℤ) : Prop :=
  HasLatFlags Z L ∧ ∃ (m : ℕ) (Q : Mdl Y i₀) (π : Z.X ⟶ Q.X) (N : LB Q.X) (f : ∀ i a, Γ(Q.X, N.U i ⊓ (Q.U a).1)ˣ),
    0 < m ∧ Q.i.l = l ∧ (∀ σ, Q.ty σ = Finset.range (Dw.mult σ + 1)) ∧ IsMap Z Q π ∧ IsFinite π ∧
    Q.IsAutLB (m • e) N f ∧
    ∀ (q : LatChart Z L) (i : N.ι), ∃ ε : Γ(Z.X, q.U ⊓ π ⁻¹ᵁ N.U i)ˣ,
      ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (τ : (Y Z.i).X ⟶ (Y Q.i).X)
        (mu : SABMap (Y Z.i).t (Y Q.i).t τ) (r : k), q.FrameAt x u → LocM.IsTrans Q.i Z.i τ mu →
        Q.SecVal (m • e) (f i) (x ≫ π) (fun σ a => u σ a ≫ mu.φ) r →
        r * (∏ σ, valR x ⊤ (Z.cst (diffGen Z.i.c W σ)) ^ b σ) ^ m = valR x _ ε.val

end Descent

end GlobalTheory.LocM
end
end
