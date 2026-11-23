module

public import Formalism.LocalToGlobal.HermitianForms.Bundle010
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle099
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle062
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open scoped TensorProduct

def chartWiden {D : D7} {T : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))} (hb : bad ⊆ bad') {i : ℕ} {hi : i ≤ D.R.m}
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) : LevelChart D T bad' i hi stab lat where
  lev :=
    { K.lev with
      Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (hb h)) hT
      chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (hb hv)) }
  y := K.y
  y_bij := K.y_bij
  y_lat := K.y_lat
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

def chartAll {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m}
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (β : Unit) :
    LevelChart D T bad i hi (fun c : {c : cl // (fun _ : cl => ()) c = β} => stab c.1) (fun c => lat c.1) where
  lev := K.lev
  y c := K.y c.1
  y_bij := by
    have e : Function.Bijective (fun c : {c : cl // (fun _ : cl => ()) c = β} => c.1) :=
      ⟨Subtype.val_injective, fun c => ⟨⟨c, rfl⟩, rfl⟩⟩
    exact K.y_bij.comp e
  y_lat c := K.y_lat c.1
  stabI c := K.stabI c.1
  stabI_inj c := K.stabI_inj c.1
  stabI_range c := K.stabI_range c.1

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))



structure TwLevJ {Ch0 : B.Word → ℕ → Type} {chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i}
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)))
    (u : B.Word) (a : I.ι) {Ch : Type} (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _)
      (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1)
      (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) where

  levJ : Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f Q

  Yb : Type
  [YbFin : Finite Yb]
  [YbAct : MulAction levJ.U Yb]

  yb : Ch → Yb
  yb_orbit : ∀ y : Yb, ∃! β, ∃ κ : levJ.U, κ • yb β = y

  lb : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) levJ.Lb
  le : ∀ β, (K β).lev.U ≤ levJ.U.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom
  stab : ∀ β (κ : levJ.U), reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 ∈ (K β).lev.U ↔ κ • yb β = yb β

  chiJ : levJ.U →* ℂˣ
  chiJ_eq : ∀ β (κ : levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (K β).lev.chi κ' = chiJ κ

  J_g : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
    ∀ x ∈ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v levJ.Lb,
      x ∈ levJ.Uloc v ↔ ∃ M ∈ HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v,
        (M : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) (kv (I.rec7 l Z).host.F v)) = redJS F u j v hv x

  J_off : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Q → v ∉ badG (I.rec7 l Z) →
    (levJ.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom = (F u).levJ.Uloc v

  yG : Yb → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)),
    ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v
  yG_smul : ∀ (κ : levJ.U) y j v hv,
    yG (κ • y) j v hv = redJS F u j v hv (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) *ᵥ yG y j v hv

  YQ : Type
  yQ : Yb → YQ
  y_inj : ∀ y y', yG y = yG y' → yQ y = yQ y' → y = y'
  yQ_off : ∀ (κ : levJ.U) y, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → yQ (κ • y) = yQ y

attribute [instance] TwLevJ.YbFin TwLevJ.YbAct

end GlobalTheory.Mem.Col2.TC

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.LocBasisChange

theorem norm_le_one_of_isIntegral_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_det_le_one {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (h : ∀ a b, ‖M a b‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, M (σ i) i‖ ≤ 1 := by
    rw [norm_prod]; exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

theorem norm_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {s : ℕ} (hs : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs

theorem basis_change : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm Bs hR hL
  have hm : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  set ρ : D.host.E →+* ℂ_[p] := lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar hm) with hρ
  have hρe : ∀ x, TaylorLogMetric.tauEmb D lam τ x = ρ x := fun x => dif_pos (hm x)
  have hint : ∀ y : 𝓞 D.host.E, ‖ρ (y : D.host.E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (map_isIntegral_int ρ y.isIntegral_coe)
  have hunit : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact norm_natCast_of_not_dvd hs
  set Mm : Matrix (Fin N) (Fin N) D.host.E := (Bm : Matrix (Fin N) (Fin N) D.host.E) with hMm
  set Mi : Matrix (Fin N) (Fin N) D.host.E := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) with hMi
  have hMMi : Mm * Mi = 1 := Bm.mul_inv
  have hMiM : Mi * Mm = 1 := Bm.inv_mul
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := Mm.map ρ with hA
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := Mi.map ρ with hAi
  have hAAi : A * Ai = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMMi, map_one]
  have hAiA : Ai * A = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMiM, map_one]
  set g : Matrix (Fin N) (Fin N) ℂ_[p] := Ai * Bs with hg
  have hBs : Bs = A * g := by rw [hg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hgi : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hB⟩ := hR.2.2 b
    have e : g a b = ∑ k, r k * ρ ((Mi *ᵥ x k) a) := by

      simp only [hg, Matrix.mul_apply, hB, hρe, hAi, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum,
      map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    obtain ⟨s, hs, hmem⟩ := (hL (x k)).1 ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using hx k⟩
    obtain ⟨z, hz⟩ := hmem a
    have h1 : ‖ρ ((s : D.host.E) * (Mi *ᵥ x k) a)‖ ≤ 1 := by rw [← hz]; exact hint z
    rw [map_mul, norm_mul, hunit s hs, one_mul] at h1
    rw [norm_mul]
    calc ‖r k‖ * ‖ρ ((Mi *ᵥ x k) a)‖ ≤ 1 * 1 := by gcongr; exact hr k
      _ = 1 := one_mul 1
  have hBsu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hR.1
  set h : Matrix (Fin N) (Fin N) ℂ_[p] := Bs⁻¹ * A with hh
  have hgh : g * h = 1 := by
    rw [hg, hh, Matrix.mul_assoc, ← Matrix.mul_assoc Bs, Matrix.mul_nonsing_inv _ hBsu, Matrix.one_mul, hAiA]
  have hhi : ∀ a b, ‖h a b‖ ≤ 1 := by
    intro a b
    set xb : Fin N → D.host.E := fun j => Mm j b with hxb
    have hcol : ∀ a, (Mi *ᵥ xb) a = (1 : Matrix (Fin N) (Fin N) D.host.E) a b := by
      intro a; rw [← hMiM]; rfl
    obtain ⟨s, hs, hmem⟩ := (hL xb).2 ⟨1, (Fact.out : p.Prime).not_dvd_one, fun a => by
      rw [hcol, Nat.cast_one, one_mul, Matrix.one_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩⟩
    have hb := hR.2.1 _ hmem a
    have key : (Bs⁻¹ *ᵥ fun i => TaylorLogMetric.tauEmb D lam τ (((s : D.host.E) • xb) i)) a = ρ s * h a b := by
      simp only [hρe, Pi.smul_apply, smul_eq_mul, map_mul, hh, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hA, Matrix.map_apply, hxb, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key, norm_mul, map_natCast, norm_natCast_of_not_dvd hs, one_mul] at hb
    exact hb
  have hd1 := norm_det_le_one g hgi
  have hd2 := norm_det_le_one h hhi
  have hprod : ‖g.det‖ * ‖h.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, hgh, Matrix.det_one, norm_one]
  refine ⟨g, hgi, le_antisymm hd1 ?_, ?_⟩
  swap
  · rw [hBs]; congr 1; ext i j; simp only [hA, Matrix.map_apply, hρe]
  calc (1 : ℝ) = ‖g.det‖ * ‖h.det‖ := hprod.symm
    _ ≤ ‖g.det‖ * 1 := by gcongr
    _ = ‖g.det‖ := mul_one _

end GlobalTheory.LocBasisChange

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocBasisBasR

open Matrix

theorem norm_det_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {N : ℕ}
    (g : Matrix (Fin N) (Fin N) K) (hg : ∀ a b, ‖g a b‖ ≤ 1) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hg _ _)

theorem main : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm M hL hM
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  have hp : p.Prime := Fact.out
  have hns : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact GlobalTheory.KapSplitNorm.norm_natCast_eq_one p s hs
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := (Bm : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAdef
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hAiA : Ai * A = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hMu : IsUnit M.det := Ne.isUnit hM.1

  have hcoord : ∀ x ∈ L, ∀ a, ‖(Ai *ᵥ fun i => ρ (x i)) a‖ ≤ 1 := by
    intro x hx a
    obtain ⟨s, hs, hint⟩ := (hL x).1 ⟨1, hp.not_dvd_one, by simpa using hx⟩
    obtain ⟨c, hc⟩ := hint a
    have e : (Ai *ᵥ fun i => ρ (x i)) a = ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) := by
      rw [RingHom.map_mulVec]; rfl
    have hs1 := hns s hs
    have hs0 : ρ (s : D.host.E) ≠ 0 := by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1
    have e2 : ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) =
        (ρ (s : D.host.E))⁻¹ * ρ (algebraMap (𝓞 D.host.E) D.host.E c) := by
      rw [hc, map_mul]; field_simp
    rw [e, e2, norm_mul, norm_inv, hs1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ c
  have hg : ∀ a b, ‖(Ai * M) a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hcol⟩ := hM.2.2 b
    have : (Ai * M) a b = ∑ k, r k * (Ai *ᵥ fun i => ρ (x k i)) a := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hr k) (norm_nonneg _) (hcoord _ (hx k) a)
  refine ⟨Ai * M, hg, ?_, ?_⟩
  · have hh : ∀ b a, ‖(M⁻¹ * A) b a‖ ≤ 1 := by
      intro b a
      let x : Fin N → D.host.E := fun j => (Bm : Matrix (Fin N) (Fin N) D.host.E) j a
      have hxe : x = (Bm : Matrix (Fin N) (Fin N) D.host.E) *ᵥ Pi.single a 1 := by
        funext j; simp [x, Matrix.mulVec_single]
      have hrhs : ∃ s : ℕ, ¬ p ∣ s ∧ ∀ c, (s : D.host.E) *
          (((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        refine ⟨1, hp.not_dvd_one, fun c => ?_⟩
        rw [hxe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
          Nat.cast_one, one_mul, Pi.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      obtain ⟨s, hs, hmem⟩ := (hL x).2 hrhs
      have h := hM.2.1 _ hmem b
      rw [hρ] at h
      have e : (fun j => ρ (((s : D.host.E) • x) j)) = ρ (s : D.host.E) • fun j => ρ (x j) := by
        funext j
        change ρ ((s : D.host.E) * x j) = ρ (s : D.host.E) * ρ (x j)
        rw [map_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hns s hs, one_mul] at h
      convert h using 2
      simp [A, x, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hprod : (Ai * M) * (M⁻¹ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, hAiA]
    have hd := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hd
    have hn := congrArg norm hd
    rw [norm_mul, norm_one] at hn
    have h1 := norm_det_le_one _ hg
    have h2 := norm_det_le_one _ (fun b a => hh b a)
    by_contra hne
    have hlt : ‖(Ai * M).det‖ < 1 := lt_of_le_of_ne h1 hne
    have : ‖(Ai * M).det‖ * ‖(M⁻¹ * A).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
    linarith
  · rw [hρ, ← Matrix.mul_assoc]
    change M = A * Ai * M
    rw [hAAi, Matrix.one_mul]

end GlobalTheory.LocBasisBasR
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HermTransport

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_refl_apply' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_refl_hom' {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_refl_apply' R g

omit [StarRing E] in
theorem reL_refl' {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem classTie_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {U' : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))} {Lb' : Submodule (𝓞 E) (Fin n → E)}
    {cl cl' : Type} (e : cl' ≃ cl) {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) S.V)
    (y : cl → UPts σ J (Formalism.L2.Herm.Af F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) :
      ClassSet ((ratPts σ J (Formalism.L2.Herm.Af F)).subgroupOf (UPts σ J (Formalism.L2.Herm.Af F)))
        (U'.subgroupOf (UPts σ J (Formalism.L2.Herm.Af F))))))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      x ∈ Formalism.L2.Herm.hatL (F := F) (reL h (Formalism.L2.Herm.crdLat S (lat c))) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Lb')
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (Formalism.L2.Herm.Af F)) γ.1 ∈ U'.map (MulAut.conj (y c).1).toMonoidHom)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) (U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (hLb : Lb' = reL h Lb) (hU : U' = U.map (reGL h _).toMonoidHom) :
    ∃ C : Formalism.L2.Herm.ClassTie hc S Lb U (fun c' => stab (e c')) (fun c' => lat (e c')),
      (∀ c', (y (e c')).1 = reGL h _ (C.y c').1) ∧ ∀ c' s, (stabI (e c') s).1 = reGL h _ (C.stabI c' s).1 := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  subst hLb
  subst hU
  have hU0 : U.map (reGL (rfl : S.rank = S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)).toMonoidHom = U := by
    rw [reGL_refl_hom', Subgroup.map_id]
  rw [hU0] at y_bij stabI_range
  simp only [reL_refl'] at y_lat
  refine ⟨⟨fun c' => y (e c'), y_bij.comp e.bijective, fun c' x => y_lat (e c') x, fun c' => stabI (e c'),
    fun c' => stabI_inj (e c'), fun c' γ => stabI_range (e c') γ⟩,
    fun c' => (reGL_refl_apply' _ _).symm, fun c' s => (reGL_refl_apply' _ _).symm⟩

end Gen

theorem latCrd_eq_reL (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    latCrd D i hi L = reL (rankN D i hi) (Formalism.L2.Herm.crdLat (D.sp.X i) L) := by
  ext x
  simp [latCrd, reL, Formalism.L2.Herm.crdLat, reV, Formalism.L2.Herm.crd]

theorem classTie_of_chart : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  intro D i hi T bad cl cl' e stab _ lat K T' f' L hLb hU
  exact classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hi) rfl (fun a b => rfl) e lat K.y K.y_bij
    (fun c x => by rw [← latCrd_eq_reL]; exact K.y_lat c x) K.stabI K.stabI_inj K.stabI_range L.Lb L.U hLb hU

end GlobalTheory.HermTransport
end
end
