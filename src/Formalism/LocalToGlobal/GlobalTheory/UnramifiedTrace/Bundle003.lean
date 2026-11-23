module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.Bundle002
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.LocalUnitaryOfMatchingZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle004
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TripMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Common
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.Bundle001
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

theorem nat_smul_inv {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) (hN : (N : E) ≠ 0) (a : 𝓞 E) (w : Fin n → E) :
    ((N : ℕ) : 𝓞 E) • (a • (((N : ℕ) : E)⁻¹ • w)) = a • w := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_natCast]
  rw [mul_left_comm, mul_inv_cancel_left₀ hN]

variable {D : D7} {u : D.what₂.Word}




theorem comp_cmp (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c3 : (D.mem u).C.cls 0)
    (w1 w3 : Fin (D.R.N 0) → D.host.E)
    (g1 g3 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (Γ1 Γ3 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h1 h3 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (k1 k3 : T.cls0.lev.U)
    (H1 : IsCompMv T v c c1 w1 g1 Γ1 h1 k1) (H3 : IsCompMv T v c c3 w3 g3 Γ3 h3 k3)
    (hw : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3}))
    (hw1 : w1 ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hg : ∀ l ∈ clsCrd D u 0 (Nat.zero_le _) c, ∀ (e : 𝓞 D.host.E)
      (hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      g1 (T.lv0.prk v c ⟨_, hY⟩) = g3 (T.lv0.prk v c ⟨_, hY⟩)) :
    h3.1⁻¹ * h1.1 ∈ T.cls0.lev.U := by
  obtain ⟨s1, e1, p1, d1, f1⟩ := H1
  obtain ⟨s3, e3, p3, d3, f3⟩ := H3
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have eM : ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      ((Γ3.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Γ1.1.1 := Units.val_mul _ _
  have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ (CrossDiaZero.use₄ (T.atT.Pv v) Γ3.1 p3) p1
  have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ (CrossDiaZero.use₄ (T.atT.Pv v) Γ3.1 d3) (d1.trans hw)
  have hΓU : Γ3.1⁻¹ * Γ1.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (inv_mem Γ3.2) Γ1.2
  have hQd := local_dual_Q_eq_of_P T.atT v c3 c1 (Γ3.1⁻¹ * Γ1.1) hΓU hP
  have eback : ∀ y : Fin (D.R.N 0) → D.host.E,
      Γ3.1.1 *ᵥ (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) =
        Γ1.1.1 *ᵥ y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
  refine trip_mem T v c c1 c3 Γ1 Γ3 h1 h3 k1 k3 s1 s3 e1 e3 hP hPd ?_
  intro z hz
  obtain ⟨b, hbP, hbQ, hb⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPd.le hQd.le
    (x := ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ⟨z, hz, rfl⟩
  obtain ⟨r, hr, b', hb'⟩ := rlv_norm T.atT v b hbP hbQ
  set R := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r with hR
  have hmem : R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
      Ld D u 0 (Nat.zero_le _) c3 := by
    rw [hb', mul_smul]; exact Submodule.smul_mem _ _ hb
  refine ⟨r, hr, hmem, ?_⟩
  have hRz : R • z ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz

  have hloc : Γ1.1.1 *ᵥ (R • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) := by
    rw [← d1]; exact mem_localization_of_mem₂ _ ⟨_, hRz, rfl⟩
  obtain ⟨t0, ht0, ht0m⟩ := (rlv_mem_locP _ _ _).1 hloc
  obtain ⟨l0, hl0, m0, hm0, em⟩ := Submodule.mem_sup.1 ht0m
  obtain ⟨e0, rfl⟩ := Submodule.mem_span_singleton.1 hm0
  obtain ⟨t1, ht1, ht1w⟩ := (rlv_mem_locP _ _ _).1 hw1
  set t := t1 * t0 with ht
  have htP : t ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht1 ht0
  have eW : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (t • (R • z))) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 := by
    rw [Matrix.mulVec_smul, ht, mul_smul, ← em, smul_add, smul_add]
    congr 1
    rw [show t1 • (e0 • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1)) = (t1 * e0) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) from
      smul_smul _ _ _, nat_smul_inv _ hTne, mul_comm]
  have hl : t1 • l0 ∈ clsCrd D u 0 (Nat.zero_le _) c := Submodule.smul_mem _ _ hl0
  have hYL : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 ∈ clsCrd D u 0 (Nat.zero_le _) c := by
    refine add_mem (Submodule.smul_mem _ _ hl) ?_
    rw [mul_smul]; exact Submodule.smul_mem _ _ ht1w
  have hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left hYL
  have hX1m : t • (R • z) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hRz
  have hX1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (⟨_, hX1m⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (t • (R • z))) ∈ _
    rw [eW]; exact hY
  have hX3m : t • (R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) ∈
      Ld D u 0 (Nat.zero_le _) c3 := Submodule.smul_mem _ _ hmem
  have eX3 : Γ3.1.1 *ᵥ (t • (R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))) =
      Γ1.1.1 *ᵥ (t • (R • z)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, eback, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hX3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ (⟨_, hX3m⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ _) ∈ _
    rw [eX3]; exact hX1
  have q1 := f1 ⟨_, hX1m⟩ hX1
  have q3 := f3 ⟨_, hX3m⟩ hX3
  have qg := hg _ hl _ hY
  have k1e : T.lv0.prk v c ⟨_, hX1⟩ = T.lv0.prk v c ⟨_, hY⟩ := congrArg _ (Subtype.ext eW)
  have k3e : T.lv0.prk v c ⟨_, hX3⟩ = T.lv0.prk v c ⟨_, hY⟩ := by
    refine congrArg _ (Subtype.ext ?_)
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ _) = _
    rw [eX3, eW]
  rw [k1e] at q1
  rw [k3e] at q3
  have pr1 : T.lv0.pr v c1 ⟨_, hX1m⟩ = T.atT.res v t • T.lv0.pr v c1 ⟨_, Submodule.smul_mem _ _ hz⟩ :=
    T.lv0.pr_smul v c1 t ⟨_, Submodule.smul_mem _ _ hz⟩
  have pr3 : T.lv0.pr v c3 ⟨_, hX3m⟩ = T.atT.res v t • T.lv0.pr v c3 ⟨_, hmem⟩ :=
    T.lv0.pr_smul v c3 t ⟨_, hmem⟩
  rw [pr1, map_smul] at q1
  rw [pr3, map_smul] at q3
  have hres : T.atT.res v t ≠ 0 := fun h0 => htP (RingHom.mem_ker.2 h0)
  exact smul_right_injective _ hres (q3.trans (qg.symm.trans q1.symm))

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def DUPt0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0),
  ∃ (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    DnMvs T v c γ η κ ∧ (∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) ∧
    ∃ (ι : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
        {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} → (D.fm u).lk 0 v c)
      (τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ),
      (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c), g ≠ 0 → ∀ x, g (ι g x) = 1) ∧
      (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c), g ≠ 0 → ∀ y, g y = 1 → ∃! x, ι g x = y) ∧
      ∀ G ∈ AdFun T.cls0.lev (embT D),
        (∀ p : PD D u v c, ι p.1.1 p.2 = (D.fm u).te 0 v c →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) = G (T.cls0.y c)) ∧
        (∀ (p : PD D u v c) (q : PE D u v c), ι p.1.1 p.2 = ι q.1.1 q.2 →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ p q : PE D u v c, ι p.1.1 p.2 = ι q.1.1 q.2 →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ (a : ((D.mem u).A.Fv v)ˣ) (q : PE D u v c), ι q.1.1 q.2 = (a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c →
          ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
          ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2)) = G (T.cls0.y c * δ))


theorem duFib_of_pt (T : Forms0 D u) (h : DUPt0F T) : DUFib0F T := by
  intro v c
  obtain ⟨γ, η, κ, Mu, hmv, hMu, ι, τ, hι, hu, hval⟩ := h v c
  have hK : Fintype.card ((D.mem u).A.Fv v) = (D.mem u).A.T := (D.mem u).A.card_Fv v
  have hr : Module.finrank ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) = D.R.N 0 := (D.fm u).lk_rank 0 v c
  have hte := (D.fm u).te_ne 0 v c
  refine ⟨γ, η, κ, Mu, hmv, hMu, fun p => ι p.1.1 p.2, fun q => ι q.1.1 q.2, τ, fun y => ?_, fun y => ?_, hval⟩
  · refine (card_sig_fib (A := {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ≠ 0})
      (fun g x => ι g.1 x) (fun g y => g.1 y = 1) (fun g x => hι g.1 g.2 x) (fun g y hy => hu g.1 g.2 y hy) y).trans ?_
    rw [card_filter_subtype (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ≠ 0) (fun g => g y = 1)]
    split_ifs with hy
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨-, h1⟩
      rw [hy, map_zero] at h1
      exact zero_ne_one h1
    · rw [Finset.filter_congr (q := fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g y = 1)
        (fun g _ => ⟨fun h => h.2, fun h => ⟨fun h0 => by rw [h0, LinearMap.zero_apply] at h; exact zero_ne_one h, h⟩⟩),
        card_dual_one y hy, hK, hr]
  · refine (card_sig_fib (A := {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ((D.fm u).te 0 v c) = 1})
      (fun g x => ι g.1 x) (fun g y => g.1 y = 1) (fun g x => hι g.1 (fun h0 => ?_) x)
      (fun g y hy => hu g.1 (fun h0 => ?_) y hy) y).trans ?_
    · have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    · have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    rw [card_filter_subtype (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ((D.fm u).te 0 v c) = 1)
      (fun g => g y = 1)]
    split_ifs with h1 h2
    · rw [h1, Finset.filter_congr (q := fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) =>
        g ((D.fm u).te 0 v c) = 1) (fun g _ => and_self_iff), card_dual_one _ hte, hK, hr]
    · exact card_dual_line _ y h2 h1
    · rw [card_dual_two _ y hte h2, hK, hr]

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end
