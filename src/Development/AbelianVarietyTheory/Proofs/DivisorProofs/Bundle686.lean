module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle608
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle489
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem pullTwo_mulBy_pow_self {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (t : G.A n ⊗[O] G.A n) :
    pullbackTwo (mulBy O (G.A n) (p ^ n)) t = algebraMap O _
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n))
        (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b =>
    have h : pullbackTwo (mulBy O (G.A n) (p ^ n)) (a ⊗ₜ[O] b) =
        mulBy O (G.A n) (p ^ n) a ⊗ₜ[O] mulBy O (G.A n) (p ^ n) b := rfl
    rw [h, G.mulBy_pow_self, G.mulBy_pow_self, Algebra.TensorProduct.lift_tmul,
      Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, Algebra.TensorProduct.one_def]

theorem Chart.ev_nmul_pow : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, c.ev n (subst (nmul c.μ (p ^ n)) f) = algebraMap O _ (constantCoeff f)) ∧ (∀ s, c.ev₂ n (pull2 (nmul c.μ (p ^ n)) s) = algebraMap O _ (constantCoeff s)) ∧ ∀ f, c.ev (n + 1) (subst (nmul c.μ p) f) = G.mulP n (c.ev n f) := by
  intro p O _ _ G d c n
  refine ⟨fun f => ?_, fun s => ?_, fun f => ?_⟩
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c n (p ^ n)).2.1, G.mulBy_pow_self,
      ((GlobalTheory.T.ev_res_counit_compat p O G d c n).1 f).2]
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c n (p ^ n)).2.2, pullTwo_mulBy_pow_self,
      (GlobalTheory.T.ev_res_counit_compat p O G d c n).2]
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c (n + 1) p).2.1, ← ((GlobalTheory.T.ev_res_counit_compat p O G d c n).1 f).1, mulP_res]

end GlobalTheory.QLog
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCongr

variable {Q : Type} [CommRing Q]

theorem frob_eq_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem subst_frob {σ τ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    subst a (frob p s g) = subst (fun i => a i ^ p) (map s g) := by
  rw [frob, subst_comp_subst_apply (HasSubst.X_pow hp) ha]
  congr 1
  funext i
  rw [subst_pow ha, subst_X ha]

theorem frob_subst {σ τ : Type} [Finite σ] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    frob p s (subst a g) = subst (fun i => expand p hp (map s (a i))) (map s g) := by
  have ha' : HasSubst fun i => map s (a i) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by
      rw [constantCoeff_map]; exact (ha.const_coeff i).map s
  rw [frob_eq_expand p hp, map_subst ha, expand_subst p hp ha']

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem coeff_pow_sub_expand_mem {B τ : Type} [CommRing B] (p : ℕ) [hp : Fact p.Prime]
    (hnu : ¬IsUnit (p : B)) (σ : B →+* B) (hσ : ∀ b, (p : B) ∣ σ b - b ^ p)
    (g : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (g ^ p - expand p hp.out.ne_zero (map σ g)) ∈ Ideal.span {(p : B)} := by
  haveI : CharP (B ⧸ Ideal.span {(p : B)}) p := CharP.quotient B p hnu
  set π := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hπσ : π.comp σ = (frobenius (B ⧸ Ideal.span {(p : B)}) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
  change coeff α (map π (g ^ p - expand p hp.out.ne_zero (map σ g))) = 0
  rw [map_sub, map_pow, map_expand, map_map, hπσ, ← map_map, ← map_expand,
    map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem dIn_comb {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (he : ∀ i, DIn (⊤ : Ideal B) (e i)) :
    DIn (⊤ : Ideal B) (comb b e) := by
  intro α j
  choose c _ hc using fun i => he i α j
  refine ⟨∑ i, b i * c i, trivial, ?_⟩

  simp only [comb, map_sum, coeff_smul, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc i]; ring

theorem dIn_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (φ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b)) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) (map s f) := by
  intro α j
  obtain ⟨c, -, hc⟩ := hf α j
  refine ⟨φ c, trivial, ?_⟩
  rw [coeff_map, ← hs, ← hc, map_mul, map_natCast]

theorem frob_cong : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  intro p hp O _ hO _ ε F d μ' hμ ι _ e he b
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set f := comb b e with hfdef
  set M := up F.Q μ' with hM
  have hM0 : ∀ i, constantCoeff (M i) = 0 := fun i => by
    rw [hM, up, constantCoeff_map, hμ.const i, map_zero]
  have hsM : HasSubst M := hasSubst_of_constantCoeff_zero hM0
  have hsL : HasSubst fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

  have hX : ∀ (a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.Q), (∀ i, ∃ j, a i = X j) → HasSubst a →
      subst a (frob p F.s f) = frob p F.s (subst a f) := by
    intro a ha has
    rw [subst_frob p hp0 F.s has, frob_subst p hp0 F.s has]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := ha i
    rw [hj, map_X, expand_X]
  have hL := hX _ (fun i => ⟨_, rfl⟩) hsL
  have hR := hX _ (fun i => ⟨_, rfl⟩) hsR

  set u : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => μ' i ^ p with hu
  set v : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => expand p hp0 (map F.σ (μ' i)) with hv
  have hsalg : F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ :=
    RingHom.ext fun x => F.s_alg x
  have hup_u : up F.Q u = fun i => M i ^ p := by
    funext i; rw [up, hu, hM, up, map_pow]
  have hup_v : up F.Q v = fun i => expand p hp0 (map F.s (M i)) := by
    funext i; rw [up, hv, hM, up, map_expand, map_map, map_map, hsalg]
  have key : cob1 M (frob p F.s f) - frob p F.s (cob1 M f) =
      subst (up F.Q u) (map F.s f) - subst (up F.Q v) (map F.s f) := by
    rw [hup_u, hup_v, ← subst_frob p hp0 F.s hsM, ← frob_subst p hp0 F.s hsM]
    have hfs : ∀ a c : MvPowerSeries (Fin d ⊕ Fin d) F.Q,
        frob p F.s (a - c) = frob p F.s a - frob p F.s c := fun a c => by
      simp only [frob_eq_expand p hp0, map_sub]
    unfold cob1 inL inR
    rw [hfs, hfs, hL, hR]
    abel
  rw [key, ← Ideal.mul_top (Ideal.span {(p : F.B)})]
  have hnu : ¬IsUnit (p : F.B) := fun h => hO.out (by simpa using h.map F.θ)
  refine GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ ?_ (Fin d) (Fin d ⊕ Fin d) ⊤
    (map F.s f) u v ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨z ^ p * (p : F.B) ^ (p - 1),
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.sub_pos_of_lt hp.out.one_lt)), ?_⟩
    rw [mul_pow, mul_left_comm, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  · exact dIn_map F.σ F.s F.s_alg f
      (dIn_comb b e fun i => GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hμ ⊤ (e i) (he i))
  · intro i; rw [hu, map_pow, hμ.const i, zero_pow hp0]
  · intro i; rw [hv, constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero]
  · intro i α
    exact coeff_pow_sub_expand_mem p hnu F.σ F.σ_pow (μ' i) α

end GlobalTheory.FrobCongr
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem semiHom_constantCoeff_and_ev : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, (s.app 0).counit_map, c.aug, map_zero]
  refine ⟨hconst, fun n g => ?_⟩
  have hy : ∀ j, IsNilpotent (s.app n (c.x n j)) := fun j => (c.nil n j).map (s.app n).toRingHom
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k' (Fin d) (G'.A n)).1 (Fin e) (c'.ev n)
    (fun t => by
      change IsNilpotent (evA k' (c'.x n) (c'.nil n) (X t))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c'.nil n t) φ hconst _ hy (fun j => hφ n j) (MvPowerSeries.map σ g)
  rw [h1]
  letI : Algebra k (G'.A n) := ((algebraMap k' (G'.A n)).comp σ).toAlgebra
  let S : G.A n →ₐ[k] G'.A n :=
    { (s.app n).toRingHom with commutes' := fun r => (s.app n).map_algebraMap r }
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G'.A n) S (c.x n) (c.nil n) _ hy (fun _ => rfl) g
  change _ = S (evA k (c.x n) (c.nil n) g)
  rw [h2]
  let M : MvPowerSeries (Fin d) k →ₐ[k] G'.A n :=
    { (evA k' _ hy : MvPowerSeries (Fin d) k' →+* G'.A n).comp (MvPowerSeries.map σ) with
      commutes' := fun r => by
        change evA k' _ hy (MvPowerSeries.map σ (algebraMap k _ r)) = algebraMap k' _ (σ r)
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.map_C, ← (evA k' _ hy).commutes (σ r), MvPowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  have hM : M = evA k _ hy := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) (G'.A n) M _
    (fun i => by
      change IsNilpotent (evA k' _ hy (MvPowerSeries.map σ (X i)))
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact hy i)
    (fun i => by
      change evA k' _ hy (MvPowerSeries.map σ (X i)) = _
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate])
  exact AlgHom.congr_fun hM g

end GlobalTheory.Katz
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_evA_eq_of_presents (k : Type) [CommRing k] (σ : Type) [Finite σ]
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n)
    (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n)
    (hr : ∀ n i, r n (y (n + 1) i) = y n i) (hP : Presents k y hy) (b : ∀ n, B n)
    (hb : ∀ n, r n (b (n + 1)) = b n) :
    ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  classical
  have hX : ∀ n i, evA k (y n) (hy n) (X i) = y n i := by
    intro n i
    change constantCoeff (substAlgHom (R := k) (a := fun i => (C (y n i) : MvPowerSeries Empty (B n)))
      (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hy n i) (X i)) = _
    rw [substAlgHom_X, constantCoeff_C]
  have hres : ∀ n f, r n (evA k (y (n + 1)) (hy (n + 1)) f) = evA k (y n) (hy n) f := fun n f =>
    (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (B (n + 1))).2 (B n) (r n) _ _ _ _ (hr n) f
  have hdown : ∀ n m, n ≤ m → ∀ f, evA k (y m) (hy m) f = b m → evA k (y n) (hy n) f = b n := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => exact fun _ h => h
    | succ m _ ih =>
      intro f hf
      exact ih f (by rw [← hres, hf, hb])
  choose F hF using fun n => hP.1 n (b n)
  choose ν hν using hP.2
  have hcoef : ∀ (α : σ →₀ ℕ) (g g' : MvPowerSeries σ k),
      evA k (y _) (hy (ν (α.degree + 1))) g = b _ → evA k (y _) (hy (ν (α.degree + 1))) g' = b _ →
      coeff α g = coeff α g' := by
    intro α g g' h h'
    have := hν (α.degree + 1) (g - g') (by rw [map_sub, h, h', sub_self]) α (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  let f : MvPowerSeries σ k := fun α => coeff α (F (ν (α.degree + 1)))
  have hf : ∀ α, coeff α f = coeff α (F (ν (α.degree + 1))) := fun _ => rfl
  refine ⟨f, fun n => ?_, fun g hg => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ (B n) (evA k (y n) (hy n)) fun i => by
      rw [hX]; exact hy n i
    let m := max n ((Finset.range (N + 1)).sup ν)
    have h0 := hN (f - F m) fun α hα => by
      rw [map_sub, hf, sub_eq_zero]
      refine hcoef α _ _ (hF _) (hdown _ m ?_ _ (hF m))
      exact le_max_of_le_right (Finset.le_sup (f := ν) (Finset.mem_range.2 (by omega)))
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact hdown n m (le_max_left _ _) _ (hF m)
  · ext α
    rw [hf]
    exact hcoef α _ _ (hg _) (hF _)

end Katz

end GlobalTheory
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.prime_tensor_polynomial_isMaximal_of_mem_image : ∀ (T : Type) [CommRing T] [IsDomain T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → ∀ g : Polynomial T, g ≠ 0 → algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P → P.IsMaximal ∧ ∀ x : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ∃ c d : T, d ≠ 0 ∧ algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) d * x - algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) c ∈ P := by
  first | (exact @GlobalTheory.ClosedFibre.isMaximal_of_mem) | (exact GlobalTheory.ClosedFibre.isMaximal_of_mem) | (intros; apply GlobalTheory.ClosedFibre.isMaximal_of_mem  <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_mul_mem_algebraicClosure {f g : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ)
    (hg : ∀ n, PowerSeries.coeff n g ∈ algebraicClosure ℚ ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) ∈ algebraicClosure ℚ ℂ := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ ↦ mul_mem (hf _) (hg _)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_pow_mem_algebraicClosure {f : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ) (e : ℕ) :
    ∀ n, PowerSeries.coeff n (f ^ e) ∈ algebraicClosure ℚ ℂ := by
  induction e with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ e ih =>
    rw [pow_succ]
    exact coeff_mul_mem_algebraicClosure ih hf

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_exp_two_pi_I_mul_rat (q : ℚ) :
    IsAlgebraic ℚ (Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ))) := by
  refine (IsIntegral.of_pow q.den_pos ?_).isAlgebraic
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hq : (q : ℂ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have hmul : (q.den : ℂ) * (2 * ↑Real.pi * Complex.I * (q : ℂ)) =
        (q.num : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      linear_combination (2 * ↑Real.pi * Complex.I) * hq
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [h]
  exact isIntegral_one

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_realEmbedding_apply {F : Type} [Field F] [NumberField F]
    (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F) : IsAlgebraic ℚ ((i y : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.isAlgebraic y).algHom (Complex.ofRealHom.comp i).toRatAlgHom

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma ecoef_mem_algebraicClosure_of_isCoef {F : Type} [Field F] [NumberField F] {k : ℕ}
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a) (ha₀ : IsAlgebraic ℚ a₀) (N : ℕ)
    (x : F) (μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (n : ℕ) :
    _root_.GlobalTheory.HilbFam.ecoef N a x μ n ∈ algebraicClosure ℚ ℂ := by
  unfold _root_.GlobalTheory.HilbFam.ecoef
  refine finsum_mem_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun ξ _ ↦ ?_
  refine mul_mem (mul_mem ?_ ?_) (prod_mem fun i _ ↦ pow_mem ?_ _)
  · rw [mem_algebraicClosure_iff]
    by_cases hξ : ξ = 0
    · rw [hξ, ha.1]
      exact ha₀
    · obtain ⟨m, hm⟩ := ha.2.1 ξ hξ
      rw [hm]
      exact isAlgebraic_int _
  · rw [mem_algebraicClosure_iff]
    unfold _root_.GlobalTheory.HilbFam.eTr
    exact isAlgebraic_exp_two_pi_I_mul_rat _
  · rw [mem_algebraicClosure_iff]
    exact isAlgebraic_realEmbedding_apply i ξ


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N κ c n hk ha ha₀ hc
  rw [← mem_algebraicClosure_iff]
  unfold _root_.GlobalTheory.HilbFam.hser

  simp only [map_smul, map_sum, smul_eq_mul]
  refine mul_mem ?_ (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _) ?_)
  · rw [hk, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    exact SubfieldClass.ratCast_mem _ _
  · refine coeff_mul_mem_algebraicClosure
      (coeff_pow_mem_algebraicClosure (fun m ↦ ?_) _) (fun m ↦ ?_) n
    · rw [PowerSeries.coeff_mk, mem_algebraicClosure_iff]
      exact hc m
    · rw [PowerSeries.coeff_mk]
      exact ecoef_mem_algebraicClosure_of_isCoef ha ha₀ N x μ m

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F), 0 < N → HasLevel N L → ∃ (𝔞 𝔟 : Frac F) (x : F), L = split 𝔞 𝔟 x := by
  first | exact @GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | exact GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | (intros; apply GlobalTheory.HilbFam.exists_eq_split_of_hasLevel <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue : ∀ (k n : ℕ) (c y : ℂ), iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 = lag k n c y := by
  first | exact @GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | exact GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | (intros; apply GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F), L ≤ stdLat F → (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔ ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  first | exact @GlobalTheory.HilbFam.TwistMem.mem_twist_iff | exact GlobalTheory.HilbFam.TwistMem.mem_twist_iff | (intros; apply GlobalTheory.HilbFam.TwistMem.mem_twist_iff <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) (G : ℂ), IsGVal k L b a G → gval k L b a = G := by
  first | exact @GlobalTheory.HilbFam.gval_eq_of_isGVal | exact GlobalTheory.HilbFam.gval_eq_of_isGVal | (intros; apply GlobalTheory.HilbFam.gval_eq_of_isGVal <;> assumption)
end
