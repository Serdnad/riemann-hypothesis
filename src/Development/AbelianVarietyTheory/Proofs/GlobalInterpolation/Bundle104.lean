module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowsOfExplicitParameters
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortInterval
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle095
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle094
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle097
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.windows_of_explicitParameters : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C8 D.host → (∀ t, s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ 2 * s.b') → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → let η : ℝ := (D.R.m : ℝ) * (h0v s ch : ℝ); let S : ℝ := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ)); (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3) ∧ (∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ s.b ^ 2) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → s.b ≤ wj D j τ ∧ wj D j τ ≤ s.b + η + 1) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → (bT t : ℝ) + s.b' / s.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + s.b' / s.x + η) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) → s.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ s.w'' D.R.n + η) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → S ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * S) ∧ (∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧ (((D.hc τ).v i : ℚ) : ℝ) ≤ S) ∧ (∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η) ∧ 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ 10 * ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ + 20 ≤ D.host.Lw ∧ 0 < D.host.T2.card ∧ D.host.T2.card ≤ D.R.n := by
  first | exact @GlobalTheory.EX.windows_of_large_scale | exact GlobalTheory.EX.windows_of_large_scale | (intros; apply GlobalTheory.EX.windows_of_large_scale <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

theorem weightWindowRequirement_host_of_point : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → Formalism.MainNotions.AuxBlock8.WeightVectorExists p.D p.L p.ta.Gx C.GK → ∃ a' b' : R.A → ℤ, (∀ t, t ∉ H.TT → a' t = 0 ∧ b' t = 0) ∧ WinOK p.L.sc C.GK H a' b' ∧ WOK p.L.sc cD ch C.GK H a' b' := by
  intro C cD ch p R H a b M c u0 _ hV hF hC hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, -, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  obtain ⟨a', ha, b', hb, hW⟩ := hW
  have ha' := Fintype.mem_piFinset.1 ha
  have hb' := Fintype.mem_piFinset.1 hb
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  refine ⟨a', b', fun t ht => ?_, fun t ht => ?_, ?_⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_false, Finset.mem_singleton] at h1 h2
    exact ⟨h1, h2⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_true, G.winA, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar] at h1 h2
    exact ⟨h1, h2⟩
  · have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
        p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
        (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
         open Classical in
         ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
          (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l then (1 : ℝ) else 0) +
            4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) := by
      intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6
      obtain rfl : G.hP p.D = hf := funext e6
      subst e1 e2 e0 e3 e4 e5
      unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands at hW
      simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1] at hW
      exact hW
    exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh'

end GlobalTheory.EX

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem kit_of_points : ∀ (Q : PtProp) (C : FC) (cD ch : ℝ) (s : Scale) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool), (∀ u0 : ℕ, u0 < R.n → ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q) → ∃ k : Kit C cD ch s, ∀ i, (∃ u0, (k.pt i).From H a b c u0) ∧ CanonInst (k.pt i).ta.Gx ∧ (k.pt i).Has Q := by
  intro Q C cD ch s R H a b M c hObj
  have hn : 0 < R.n := by unfold Ranks.n; exact R.ord_pos
  choose pt hsc hval har hfrom hcan hhas using fun i : Fin R.n => hObj i.1 i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ⟨⟨i.1, hfrom i⟩, hcan i, hhas i⟩⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩

end GlobalTheory.EX.DC
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT.UKS

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

theorem emb_mem_Fi (X : Ch D u) (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by

  rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem inv_natCast_mem (w : D.what₂.places.Pl) (n : ℕ) (hn : ¬ D.what₂.places.resChar w ∣ n) :
    ((n : D.what₂.LL))⁻¹ ∈ Ow D w := by
  set p := D.what₂.places.resChar w with hp
  have hpr : p.Prime := D.what₂.places.resChar_prime w
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hpr).2 hn
  have hint : ∀ z : ℤ, 0 ≤ D.what₂.places.val w (z : D.what₂.LL) := fun z => intCast_mem (Ow D w) z
  have hbez : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
    have := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hbez' : (p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL) + (n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : D.what₂.LL)) hbez
  have hvp : 0 < D.what₂.places.val w (p : D.what₂.LL) := by
    rw [hp, D.what₂.places.val_resChar w]
    have := D.what₂.places.ramIdx_pos w
    exact_mod_cast this
  have hvn : D.what₂.places.val w (n : D.what₂.LL) = 0 := by
    have h0 : 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by exact_mod_cast hint n
    by_contra hne
    have hpos : 0 < D.what₂.places.val w (n : D.what₂.LL) := lt_of_le_of_ne h0 (Ne.symm hne)
    have h1 : 0 < D.what₂.places.val w ((p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hvp (hint _)
    have h2 : 0 < D.what₂.places.val w ((n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hpos (hint _)
    have h3 := (D.what₂.places.val w).map_lt_add h1 h2
    rw [hbez', AddValuation.map_one] at h3
    exact lt_irrefl _ h3
  show 0 ≤ D.what₂.places.val w ((n : D.what₂.LL))⁻¹
  rw [AddValuation.map_inv, hvn]
  simp

section
variable {i : ℕ} {M : PtModel X i} (Co : M.Coord)

def ExtIn (w : D.what₂.places.Pl) (V : Finset X.A.vT) (φ : Fn X i) : Prop :=
  ∃ Φ, M.IsExt φ Φ ∧ ∀ p, Φ p ∈ Co.valB w V p

variable {Co}

theorem extIn_of_valIn (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i)
    (h : M.ValIn (Co.valB w V) φ) : ExtIn Co w V φ := by
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  refine ⟨Φ, hΦ, fun p => ?_⟩
  obtain ⟨c, g, rfl⟩ := M.rep_surj p
  obtain ⟨y, hy, hyc⟩ := h c
  have : Φ (M.rep c) = y := Subtype.ext ((hΦ.1 c).symm.trans hyc)
  rw [hΦ.2, this]
  exact (GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw V _).2.2.2 g y hy

theorem ExtIn.mem_Fi {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : φ ∈ X.fm.Fi i := by
  obtain ⟨Φ, hΦ, -⟩ := h
  exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).2 ⟨Φ, hΦ⟩

theorem ExtIn.valIn {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : M.ValIn (Co.valB w V) φ := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact fun c => ⟨_, h _, hΦ.1 c⟩

theorem isExt_smul {φ : Fn X i} {Φ} (h : M.IsExt φ Φ) (a : ℂ) : M.IsExt (a • φ) (fun p => a • Φ p) := by
  refine ⟨fun c => ?_, fun g p => ?_⟩
  · show a • φ c = _
    rw [h.1 c]; rfl
  · simp only [h.2, map_smul]

theorem pow_smul_mem (hC : Co.Ok) {w} (hw : OverT X w) {V p y} (hy : y ∈ Co.valB w V p) (n : ℕ) :
    ((X.A.T : ℂ) ^ n) • y ∈ Co.valB w V p := by
  have := (GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw V p).2.2.1 ((X.A.T : D.what₂.LL) ^ n)
    (pow_mem (natCast_mem _ _) n) y hy
  simpa using this

theorem ExtIn.pow_smul (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (h : ExtIn Co w V φ) (n : ℕ) :
    ExtIn Co w V (((X.A.T : ℂ) ^ n) • φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact ⟨_, isExt_smul hΦ _, fun p => pow_smul_mem hC hw (h p) n⟩

theorem ExtIn.uop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V v} (hv : v ∈ V)
    {φ : Fn X i} (h : ExtIn Co w V φ) : ExtIn Co w (V.erase v) (Uop X i v φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ, fun p => ?_⟩
  have hv' := GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw (V.erase v) p
  refine finsum_mem_induction (fun y => y ∈ Co.valB w (V.erase v) p) hv'.1
    (fun y y' hy hy' => hv'.2.1 y hy y' hy') fun p₁ hp₁ => ?_
  rw [← GlobalTheory.LvT.valB_of_inc D u X i M Co w V v p p₁ hs hv hp₁]
  exact h p₁

theorem ExtIn.uops (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (l : List X.A.vT) (hl : l.Nodup) (hV : ∀ v ∈ l, v ∈ V) :
    ExtIn Co w (V \ l.toFinset) (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id φ) := by
  induction l with
  | nil => simpa using h
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    have h1 := ih hl.2 (fun v' hv' => hV v' (List.mem_cons_of_mem _ hv'))
    have h2 := h1.uop hC hw hs (v := v) (by simp [hl.1, hV v List.mem_cons_self])
    have e : (V \ l.toFinset).erase v = V \ (v :: l).toFinset := by
      ext x; simp; tauto
    rw [e] at h2
    exact h2

theorem ExtIn.drop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (A : Finset X.A.vT) (hA : A ⊆ V) :
    ExtIn Co w (V \ A)
      (((X.A.T : ℂ) ^ (∑ v ∈ A, (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩)) • φ) := by
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  induction A using Finset.induction_on with
  | empty => simpa using h
  | insert v A hv ih =>
    obtain ⟨Φ, hΦ, h1⟩ := ih ((Finset.subset_insert _ _).trans hA)
    have e : (V \ A).erase v = V \ insert v A := by
      ext x; simp; tauto
    rw [Finset.sum_insert hv, zpow_add₀ hT, mul_smul, ← e]
    exact ⟨_, isExt_smul hΦ _, fun p => GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase D u X i M Co hC w hw hs _ v
      (by simp [hv, hA (Finset.mem_insert_self _ _)]) p _ (h1 p)⟩

end

theorem extIn_K {i : ℕ} {M : PtModel X i} {M' : PtModel X (i + 1)} {Co : M.Coord} {Co' : M'.Coord}
    (hC' : Co'.Ok) (K : KerPt M M') (hK : K.TgtEq) {w} (hw : OverT X w)
    (hst : ∀ c, ¬ X.A.T ∣ Nat.card (X.C.stab i c)) (a : ℂ) {V}
    (ha : ∀ p p', ∀ y ∈ Co.valB w ∅ p, a • K.k p p' y ∈ Co'.valB w V p')
    {φ : Fn X i} (h : ExtIn Co w ∅ φ) : ExtIn Co' w V (a • KT X i φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, isExt_smul (GlobalTheory.LvT.isExt_KT D u X i M M' K φ Φ hK hΦ) a, fun p' => ?_⟩
  have hv := GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X (i + 1) M' Co' hC' w hw V p'
  simp only [Finset.smul_sum]
  refine Finset.sum_induction _ (fun y => y ∈ Co'.valB w V p') (fun y y' hy hy' => hv.2.1 y hy y' hy') hv.1
    fun c _ => ?_
  rw [smul_comm]
  have := hv.2.2.1 _ (inv_natCast_mem w (Nat.card (X.C.stab i c)) (by rw [show _ = _ from hw]; exact hst c)) _
    (ha _ p' _ (h (M.rep c)))
  simpa [ColumnChain.wt] using this

theorem ukSharp (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Vt : ValTie Lv) (Kt : KerTie Lv)
    (hK : KerLaws Vt Kt) (hst : StabUnit X) (hW : WtBounds X) : UKSharp X := by
  intro w hw i hi x hx
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  have hC := (Vt i hi.le).2
  have hC' := (Vt (i + 1) hi).2
  have h0 : ExtIn (Vt i hi.le).1 w ∅ (X.fm.emb i x) :=
    extIn_of_valIn hC hw (emb_mem_Fi X i x) ((hC.S_on w hw _ (emb_mem_Fi X i x)).1 ⟨x, hx, rfl⟩)
  suffices h : ExtIn (Vt (i + 1) hi).1 w ∅
      (tpow X (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) •
        Uprod X (i + 1) w (KT X i (X.fm.emb i x))) from (hC'.S_on w hw _ h.mem_Fi).2 h.valIn
  by_cases hs : X.fm.seenP w = true
  · have h1 := extIn_K hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) _ (hK.intP i hi w hw hs) h0
    have h2 := h1.uops hC' hw hs (VVT X w).toList (Finset.nodup_toList _) (fun v _ => Finset.mem_univ v)
    have h3 := h2.drop hC' hw hs _ (Finset.Subset.refl _)
    rw [Finset.sdiff_self, Finset.toList_toFinset, map_smul, smul_smul, ← zpow_add₀ hT] at h3
    set e : ℤ := ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ +
      (((D.R.f * D.R.N i : ℕ) : ℤ) + ∑ τ, X.C.sDiv i τ) with he
    have hle : e ≤ ((2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by
      have a1 : ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ ≤
          ∑ τ, (Wt X τ : ℤ) := by
        rw [← Equiv.sum_comp (X.fm.tauOf w)]
        refine le_trans (Finset.sum_le_sum fun v hv => (hW.2 i hi _).2.2.2 ?_)
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Int.natCast_nonneg _)
        simpa [VVT, hs] using hv
      have a2 : ∑ τ, X.C.sDiv i τ ≤ ∑ τ, (Wt X τ : ℤ) := Finset.sum_le_sum fun τ _ => (hW.2 i hi τ).2.1
      have a3 : D.R.f * D.R.N i ≤ D.R.f * D.R.N D.R.m :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _)
      have a3' : ((D.R.f * D.R.N i : ℕ) : ℤ) ≤ ((D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by exact_mod_cast a3
      rw [he, Nat.cast_add, Nat.cast_mul 2, Nat.cast_sum]
      simp only [Nat.cast_ofNat]
      linarith
    obtain ⟨n, hn⟩ := Int.le.dest hle
    have h4 := h3.pow_smul hC' hw n
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ hT, add_comm (n : ℤ), hn, zpow_natCast] at h4
    rw [if_pos hs]
    exact h4
  · have hs' : X.fm.seenP w = false := by simpa using hs
    have h1 := extIn_K (V := ∅) hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) 1 (fun p p' y hy => by
      obtain ⟨y', hy', e⟩ := hK.bar i hi w hw hs' p p' y hy
      rw [one_smul, e]
      exact pow_smul_mem hC' hw hy' _) h0
    rw [if_neg hs]
    simpa [tpow, Uprod, VVT, hs'] using h1

end GlobalTheory.LvT.UKS
end
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.exists_lam_zero_sum_shortInterval_ge : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (𝓕 : LFam) (X h : ℝ), 1 ≤ X → Real.log 𝓕.B ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / 𝓕.B ^ A ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
  first | exact @GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | exact GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | (intros; apply GlobalTheory.Hk.ShortInt.trivialClass_shortInterval <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.LatFin


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.MomT.LatFin.per_lattice_facts : ∀ (X : _root_.Formalism.L2.Col.Fields) (A : _root_.Formalism.L2.Ker.Amb X) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E b)),
    A.AA.FG → A.AA ≠ ⊥ → _root_.Formalism.L2.Col.IsSdLat N → _root_.Formalism.L2.Col.IsSdLat N' → (_root_.GlobalTheory.MomT.per A N N').FG ∧
    (∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N') ∧
    (∀ r : 𝓞 X.E, r ≠ 0 → (_root_.GlobalTheory.MomT.smulLat (r : X.E)
      (_root_.GlobalTheory.MomT.per A N N')).toAddSubgroup.relIndex
        (_root_.GlobalTheory.MomT.per A N N').toAddSubgroup ≠ 0) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A.AA =
      _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : _root_.Formalism.L2.Col.HomE X.E a b,
      y ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (_root_.GlobalTheory.MomT.per A N N') ↔
        ∀ v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, y v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := by
  intro X A a b N N' hAfg hA hN hN'
  have full_of_sd {n : ℕ} {L : Submodule (𝓞 X.E) (Sp X.E n)}
      (hL : IsSdLat L) : Submodule.IsFullLattice X.E L := by
    let := hL.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span X.E (L : Set (Sp X.E n))
    change W = ⊤
    by_contra hW
    let e : Sp X.E n ≃ₗ⋆[X.E] Sp X.E n := starLinearEquiv X.E
    let g : Sp X.E n →ₗ[X.E] Module.Dual X.E W :=
      (LinearMap.domRestrict' W).comp ((hStd X.E n).comp e.toLinearMap)
    have hdim : Module.finrank X.E (Module.Dual X.E W) < Module.finrank X.E (Sp X.E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (c : X.E) : c • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd X.E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual X.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : X.E →ₗ[𝓞 X.E] L :=
      ((LinearMap.toSpanSingleton X.E _ (e x)).restrictScalars (𝓞 X.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 X.E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 X.E) X.E := Module.Finite.of_injective i fun c d hcd =>
      smul_left_injective X.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hcd)
    exact RingOfIntegers.not_isField X.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
  have hNfull := full_of_sd hN
  have hN'full := full_of_sd hN'
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨hN'l, -⟩ := hN'
  have hfull : _root_.GlobalTheory.ThetaMove.Full (_root_.Formalism.L2.Ker.perO A.AA N N') :=
    _root_.GlobalTheory.ThetaMove.PeriodComp.full A.AA N N' hNl.fg hN'full hA
  have hfg : (_root_.GlobalTheory.MomT.per A N N').FG :=
    _root_.GlobalTheory.ThetaMove.VolumePos.perO_fg hAfg
      (_root_.GlobalTheory.ThetaMove.VolumePos.homO_fg hNl.fg hN'l.fg (by
        let := hNfull
        exact Submodule.IsFullLattice.span_eq_top))
  have hmult : ∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧
      (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N' := by
    intro x
    obtain ⟨n, hn, hx⟩ := hfull x
    refine ⟨n, hn, ?_⟩
    unfold _root_.GlobalTheory.MomT.per
    rw [Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at hx
  refine ⟨hfg, hmult, ?_, ?_⟩
  · intro r hr
    refine _root_.GlobalTheory.ThetaMove.VolumePos.relIndex_ne_zero ?_ hfg
    intro x
    obtain ⟨n, hn, hx⟩ := hmult ((r : X.E)⁻¹ • x)
    refine ⟨n, hn, ?_⟩
    rw [_root_.GlobalTheory.MomT.mem_smulLat]
    refine ⟨_, hx, ?_⟩
    have hr' : (r : X.E) ≠ 0 := by exact_mod_cast hr
    rw [smul_smul, smul_smul, mul_comm (r : X.E), mul_assoc, mul_inv_cancel₀ hr', mul_one,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · intro P hP y
    unfold _root_.GlobalTheory.MomT.per
    constructor
    · intro hy v hv
      obtain ⟨s, hs, hsy⟩ := (_root_.Formalism.L2.Col.mem_locP P _ y).mp hy
      refine _root_.GlobalTheory.MomT.IdxBound.mem_localization_of_smul_mem P N' hs ?_
      simpa using _root_.GlobalTheory.MomT.IdxBound.per_apply_mem hP hsy hv
    · intro hy
      exact _root_.GlobalTheory.MomT.IdxBound.mem_localization_perO hP hNl.fg fun v hv =>
        hy v (_root_.GlobalTheory.ThetaMove.mem_localization_of_mem P hv)

end GlobalTheory.MomT.LatFin
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.weylHeisenbergOperator_calculus_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  first | exact @GlobalTheory.MomT.Heis.calculus | exact GlobalTheory.MomT.Heis.calculus | (intros; apply GlobalTheory.MomT.Heis.calculus <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  first | exact @GlobalTheory.MomGood.main | exact GlobalTheory.MomGood.main | (intros; apply GlobalTheory.MomGood.main <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.GLSchemeSubmodule_stable_under_row_perm : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ σ : Equiv.Perm (Fin N), ∀ f ∈ M, rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ M := by
  first | exact @GlobalTheory.AlcPerm.perm_stable | exact GlobalTheory.AlcPerm.perm_stable | (intros; apply GlobalTheory.AlcPerm.perm_stable <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M := by
  first | exact @GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule | exact GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule | (intros; apply GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.dualWeyl_highestWeight_space_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν, IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  first | exact @GlobalTheory.Alc.hw_line_field | exact GlobalTheory.Alc.hw_line_field | (intros; apply GlobalTheory.Alc.hw_line_field <;> assumption)
end
