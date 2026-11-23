module

public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.XtLamGvSCongr
public import Formalism.LocalToGlobal.Columns.ChainOneB
public import Formalism.LocalToGlobal.Columns.RecLevelSym
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle008
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
public import Formalism.LocalToGlobal.Columns.Bundle019
import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}


variable (ST SG Q) in
def FrExists : Prop :=
  ∀ (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : Q), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ y, f y ∈ d.1.at P.1 ↔ y ∈ stdAt E n P.1

theorem qdf_toGLm_ratHom (γ : URat hc n) : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) := by
  simp [toGLm, ratHom, Formalism.UG.glEquiv]

variable (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem qdf_rel_of_orbit (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p : DecoF E n ST SG Q} (a : UF E n × H × Θ.grp)
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 (a • p)) :
    ∃ (γ : URat hc n) (κ : levUQ hc n ST SG Q H q), ratHom hc n γ = a.1 ∧
      (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((a.1, a.2.1) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hx'.1, hx.1]; rfl
  obtain ⟨γ, k, h1, -, e⟩ := rlc_rel_of_orbit hc n ST SG H (a.1, a.2.1) hd
  have hkQ : ∀ P : Q, q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ q.U P := by
    intro P
    have hke : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [e]; group
    have hA := hx'.2 P
    have hB := hx.2 P
    have hθ : (a.2.2.1 P) ∈ (Θ P).H := (Subgroup.mem_pi _).1 a.2.2.2 P (Set.mem_univ _)
    have hC := (q.U_rat P (a.2.2.1 P)).2 hθ
    have hfr : (a • p).fr P = a.1.1 * p.fr P * ((a.2.2.1 P)⁻¹).1 := rfl
    have hγ : toGLm E n a.1.1 = (γ : GL (Fin n) E) := by rw [← h1]; exact qdf_toGLm_ratHom γ
    have key : q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        ((bc (q.phi P) (qGL n ((a • p).fr P)))⁻¹ * q.at P x')⁻¹ * bc (q.phi P) (qGL n (a.2.2.1 P).1) *
          ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x) := by
      rw [hke, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat, hfr]
      simp only [qGL, map_mul, map_inv, Subgroup.coe_inv]
      rw [hγ]
      group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hA) hC) hB
  exact ⟨γ, ⟨k.1, k.2, Subgroup.mem_iInf.2 hkQ⟩, h1, e⟩

theorem qdf_over_exists (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q) (x : UAd hc n) :
    ∃ p : DecoF E n ST SG Q, FrOver q x.1 p := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ∀ P : Q, Sp E n ≃ₗ[E] Sp E n,
      ∀ (P : Q) y, f P y ∈ (decoOf ST SG x.1).1.at P.1 ↔ y ∈ stdAt E n P.1 :=
    ⟨fun P => (hE (decoOf ST SG x.1) P).choose, fun P => (hE (decoOf ST SG x.1) P).choose_spec⟩
  let p0 : DecoF E n ST SG Q := ⟨(decoOf ST SG x.1, f), fun P y => hf P y⟩
  have hk := fun P : Q => hF x p0 rfl P
  choose g hg using fun P : Q => q.U_dense P _ (hk P).1 (hk P).2
  refine ⟨⟨(decoOf ST SG x.1, fun P => f P * (g P).1), fun P y => ?_⟩, rfl, fun P => ?_⟩
  · show f P ((g P).1 y) ∈ _ ↔ _
    rw [hf P]
    exact (g P).2 y
  · show (Formalism.UG.bc (q.phi P) (qGL n (f P * (g P).1)))⁻¹ * q.at P x.1 ∈ q.U P
    rw [show qGL n (f P * (g P).1) = qGL n (f P) * qGL n (g P).1 from map_mul _ _ _, map_mul, _root_.mul_inv_rev,
      mul_assoc]
    exact hg P

end QCls

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Mid

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem xtIntAt_piInv {w : HeightOneSpectrum (𝓞 E)} {pi : 𝓞 E} (h : pi ∉ w.asIdeal) : IntAt w ((algebraMap (𝓞 E) E pi)⁻¹) :=
  yIntAt_inv (IntAt.coe w pi) (by rw [reduction_coe]; exact mk_ne_zero h)

theorem xtMid (hN : N = n + 1) (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : SG) (F' : Sp E N ≃ₗ[E] Sp E N) (hF' : (DecoSet.tilH (ST := ST) hN pi d).1.IsLift w F')
    (f0 : Sp E n ≃ₗ[E] Sp E n) (hf0 : d.1.IsLift w f0) (v : Sp E N) :
    ((∀ i, IntAt w.1 (F'.symm v i)) ↔
      (∀ i, IntAt w.1 (f0.symm (fun i : Fin n => v ⟨i.1, by omega⟩) i)) ∧ IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩)) ∧
    ((∀ i, IntAt w.1 (F'.symm v i)) →
      (∀ i : Fin n, redP w.1 (F'.symm v ⟨i.1, by omega⟩) = redP w.1 (f0.symm (fun i : Fin n => v ⟨i.1, by omega⟩) i)) ∧
        redP w.1 (F'.symm v ⟨n, by omega⟩) = redP w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩)) := by
  set v0 : Sp E n := fun i : Fin n => v ⟨i.1, by omega⟩ with hv0def
  have hpi0 : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro h
    have : pi = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    exact hG w (this ▸ zero_mem _)
  have hv1 : (∀ i, IntAt w.1 (F'.symm v i)) ↔ v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w.1 := by
    rw [← ciMem_stdAt, ← hF'.1 (F'.symm v), LinearEquiv.apply_symm_apply]
  have hv2 : (∀ i, IntAt w.1 (f0.symm v0 i)) ↔ v0 ∈ d.1.at w.1 := by
    rw [← ciMem_stdAt, ← hf0.1 (f0.symm v0), LinearEquiv.apply_symm_apply]
  have hv3 : IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩) ↔ IntAt w.1 (v ⟨n, by omega⟩) := by
    constructor
    · intro h
      have := (IntAt.coe w.1 pi).mul h
      rwa [← mul_assoc, mul_inv_cancel₀ hpi0, one_mul] at this
    · intro h
      exact (xtIntAt_piInv (hG w)).mul h
  refine ⟨by rw [hv1, xtTilH_mem hN d hT hG w.1 v, hv2, hv3], fun hall => ?_⟩
  have hvD := hv1.1 hall
  have hbe : (DecoSet.tilH (ST := ST) hN pi d).1.be w v = redV w.1 (F'.symm v) := by
    have := hF'.2 (F'.symm v) ((ciMem_stdAt _ _).2 hall)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hv0 : v0 ∈ d.1.at w.1 := ((xtTilH_mem hN d hT hG w.1 v).1 hvD).1
  have hbe0 : d.1.be w v0 = redV w.1 (f0.symm v0) := by
    have := hf0.2 (f0.symm v0) ((ciMem_stdAt _ _).2 (hv2.2 hv0))
    rwa [LinearEquiv.apply_symm_apply] at this
  constructor
  · intro i
    have h1 := xtTilH_be hN d hT hG w v hvD ⟨i.1, by omega⟩
    rw [dite_eq_left i.2, hbe] at h1
    have h2 := congrFun hbe0 i
    exact h1.trans h2
  · have h1 := xtTilH_be hN d hT hG w v hvD ⟨n, by omega⟩
    rw [dite_eq_right (lt_irrefl n), hbe] at h1
    rw [inv_mul_eq_div]
    exact h1

end Mid

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem xt_a_eq {m2 : ℕ} (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t = R.N (m2 + 1) := by
  unfold Ranks.r Ranks.N
  have h1 : R.m - 1 = m2 + 1 := by omega
  have h2 : R.k + R.m - 1 = R.k + (m2 + 1) := by omega
  rw [h1, h2]
  ring

theorem xt_a_le {m2 : ℕ} (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t ≤ (R.N R.m - 1) + 0 := by
  rw [xt_a_eq hm]
  unfold Ranks.N
  rw [hm]
  have e : (m2 + 2) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
  omega

theorem xt_cOf {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R (m2 + 1) = 0 := by
  unfold cOf
  omega

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xtPhiTop_congr (hX : X.Ok) (hPr : Pr.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0))
    (hD : ∀ p p', p < (R.N R.m - 1) + 0 → p' < R.N (m2 + 1) → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTop Ch mu sharp m2 P x' = PhiTop Ch mu sharp m2 P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have ha := xt_a_eq (R := R) hm
  have hle := xt_a_le (R := R) hm
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTop
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [if_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')

theorem xtPhiTop_int {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (h : PhiTop Ch mu sharp m2 P x ≠ 0) :
    ∀ p p', p < (R.N R.m - 1) + 0 → p' < R.N (m2 + 1) →
      IntAt P (LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  have ha := xt_a_eq (R := R) hm
  unfold PhiTop at h
  rw [if_pos hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, if_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (ha.symm ▸ hp')
  · simp only [if_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (ha.symm ▸ hp')


open Classical in
theorem xtRepY_int {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := Pr.vGs)) (Y : Set (Sp X.E n))
    (hY : Y ∈ ybSet sel mu cst d.1.N) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (j : Fin n) :
    IntAt P.1 ((qOf P.1 : X.E) * (d.1.liftFr ⟨P.1, hP⟩).symm (repY Y) j) := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hrep : repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} ∈
      {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} :=
    Classical.epsilon_spec (p := fun z => z ∈ {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))})
      ⟨y, by
        show y - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))
        rw [sub_self]
        exact zero_mem _⟩
  set ρ := repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 hrep P
  simp only [if_pos hP, _root_.zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul] at h1 h2
  have h3 : (qOf P.1 : X.E) • ρ ∈ d.1.at P.1 := by
    have e : (qOf P.1 : X.E) • ρ = (qOf P.1 : X.E) • (ρ - y) + (qOf P.1 : X.E) • y := by rw [← smul_add, sub_add_cancel]
    rw [e]
    exact add_mem (yInt_smul_mem ciIntAt_q h2) h1
  have hl := Deco.liftFr_spec (d.2.hasLift ⟨P.1, hP⟩)
  have h4 := (hl.1 ((d.1.liftFr ⟨P.1, hP⟩).symm ((qOf P.1 : X.E) • ρ))).1 (by rw [LinearEquiv.apply_symm_apply]; exact h3)
  have h5 := (ciMem_stdAt _ _).1 h4 j
  rwa [map_smul, Pi.smul_apply, smul_eq_mul] at h5

end Fin

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Bridge

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem clL_base (hok : ChIdx.Ok Ch sel mu cst L G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok)
    (hs : cst.sharp = true) :
    OcbBase Ch sel mu cst m2 := by
  exact
    { hX := hX
      hPr := hPr
      hCh := hCh
      hm := hok.hm
      cst_ok := hok.cst_ok
      sharp := hs
      psi0 := hok.psi0
      depthG := hok.depthG }

end Bridge

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def OcbLevIsSym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → OcbLevIs Ch (colLevSym Ch) m2

end Formalism.L2.Col
end
end

section

namespace Formalism.L2.Col

theorem residueFieldUnfolding_claims_hold : ResidueFieldUnfoldingSupport ∧ ResidueFieldUnfoldingNonzero := by
  refine ⟨?_, ?_⟩
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2

end Formalism.L2.Col
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

theorem qsp_exists_pi (P : Pl E) (hP : conjPrime₂ P ≠ P) : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal := by
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem (Ne.symm hP)
  exact ⟨s, hs, fun h => hns ((mem_conjP P s).2 h)⟩


include hc in
theorem qsp_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem qsp_isOver (P : Pl E) : IsOver (underPl F P) P := rfl


include hc in
theorem qsp_exists (P : Pl E) (hP : conjPrime₂ P ≠ P) :
    ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal ∧ Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E)) := by
  obtain ⟨ϖ, hϖ, hcϖ⟩ := qsp_exists_pi P hP
  obtain ⟨t, ht⟩ := gls_trace_mem hc ϖ
  obtain ⟨N, hN⟩ := qsp_norm_mem hc ϖ
  have hsig : ∀ x : E, hc.sig x = star x := fun _ => rfl
  have hsig0 : hc.sig (ϖ : E) = ((cO E ϖ : 𝓞 E) : E) := by rw [hsig]; exact (algebraMap_cO ϖ).symm
  have hN' : algebraMap F E (N : F) = (ϖ : E) * hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hN
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have ht' : algebraMap F E (t : F) = (ϖ : E) + hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_add (f := _), ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have hNv : N ∈ (underPl F P).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    rw [hN]; exact Ideal.mul_mem_right _ _ hϖ
  have htv : t ∉ (underPl F P).asIdeal := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 E) t ∈ P.asIdeal := h
    rw [ht] at h1
    exact hcϖ (by simpa using P.asIdeal.sub_mem h1 hϖ)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 (underPl F P) ϖ t N ht' hN' hNv htv
  have hN2 : ((cO E ϖ : 𝓞 E) : E) * hc.sig ((cO E ϖ : 𝓞 E) : E) = algebraMap F E (N : F) := by
    rw [hN', ← hsig0, mul_comm, hsig, hsig, star_star]
  obtain ⟨sa⟩ := Formalism.MainNotions.Gaps.LG.sc_orient s (cO E ϖ) N hNv hN2
  have e : hc.sig ((cO E ϖ : 𝓞 E) : E) = (ϖ : E) := by rw [← hsig0, hsig, hsig, star_star]
  exact ⟨ϖ, hϖ, hcϖ, ⟨e ▸ sa⟩⟩

end Split

end Formalism.L2.Col
end
end
