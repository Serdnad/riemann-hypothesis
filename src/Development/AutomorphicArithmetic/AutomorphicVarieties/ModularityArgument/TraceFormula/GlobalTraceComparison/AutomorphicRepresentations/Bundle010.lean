module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.GlobalHarmonicExistence.InvolutionIntegrals.IntegralCompInvol
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import GroundTheory.LocalFields.PadicLogSeries
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

open scoped Classical

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def sing (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool) :
    ∀ v : Pl E, Bool → GLw n v → ℂ :=
  Function.update (fun v _ => (N v : Set (GLw n v)).indicator 1) w
    (fun b => if b = b₀ then f else (N w : Set (GLw n w)).indicator 1)

private theorem sing_self (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool) :
    sing N w f b₀ w b₀ = f := by
  simp [sing]

private theorem sing_ne (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool)
    (v : Pl E) (b : Bool) (h : (v, b) ≠ (w, b₀)) :
    sing N w f b₀ v b = (N v : Set (GLw n v)).indicator 1 := by
  by_cases hv : v = w
  · subst hv
    have hb : b ≠ b₀ := fun e => h (by rw [e])
    simp [sing, hb]
  · simp [sing, Function.update_of_ne hv]

private theorem sing_fam (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ)
    (b₀ : Bool) (hs : Sl S (w, b₀)) (hf : IsHecke (N w) f) :
    Fam S N {(w, b₀)} (sing N w f b₀) := by
  refine ⟨fun i hi => ?_, fun i _ hi => ?_⟩
  · rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨hs, by rw [sing_self]; exact hf⟩
  · exact sing_ne N w f b₀ i.1 i.2 (by simpa using hi)

private theorem sing_cross (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (v : Pl E) :
    sing N w f false v true = sing N w f true v false := by
  rw [sing_ne N w f false v true (by simp), sing_ne N w f true v false (by simp)]

private theorem sing_diag (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (v : Pl E) :
    sing N w f false v false = sing N w f true v true := by
  by_cases hv : v = w
  · subst hv
    rw [sing_self, sing_self]
  · rw [sing_ne N w f false v false (by simp [hv]), sing_ne N w f true v true (by simp [hv])]

private theorem pf_sing_twist (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E)
    (f : GLw n w → ℂ) (hw : IsSplitAt w) (hth : ∀ g, thF E n (thF E n g) = g)
    (hin : ∀ v : Pl E, ¬ IsSplitAt v → ∀ g, qw n v true g ∈ KGL v (n := n) ↔ qw n v false g ∈ KGL v (n := n))
    (hN : ∀ v : Pl E, ¬ IsSplitAt v → N v = KGL v (n := n)) (g : GF E n) :
    pf S (sing N w f false) (thF E n g) = pf S (sing N w f true) g := by
  unfold pf
  refine finprod_congr fun v => finprod_congr fun _ => ?_
  have q0 : qw n v false (thF E n g) = qw n v true g := rfl
  have q1 : qw n v true (thF E n g) = qw n v false g := by
    show GeneralLinearGroup.map (pLoc E v) (thF E n (thF E n g)) = _
    rw [hth]
    rfl
  rw [q0, q1]
  by_cases hs : IsSplitAt v
  · rw [if_pos hs, if_pos hs, sing_cross, sing_diag, mul_comm]
  · have hv : v ≠ w := fun e => hs (e ▸ hw)
    rw [if_neg hs, if_neg hs, mul_one, mul_one, sing_ne N w f false v false (by simp [hv]),
      sing_ne N w f true v false (by simp [hv]), hN v hs]
    have h := hin v hs g
    by_cases hm : qw n v false g ∈ KGL v (n := n)
    · rw [Set.indicator_of_mem (show qw n v true g ∈ (KGL v (n := n) : Set (GLw n v)) from h.2 hm),
        Set.indicator_of_mem (show qw n v false g ∈ (KGL v (n := n) : Set (GLw n v)) from hm)]
      rfl
    · rw [Set.indicator_of_notMem (show qw n v true g ∉ (KGL v (n := n) : Set (GLw n v)) from fun e => hm (h.1 e)),
        Set.indicator_of_notMem (show qw n v false g ∉ (KGL v (n := n) : Set (GLw n v)) from hm)]

end SlopeTestRemainingChoices

theorem ySwap_pf : SlotBasic → PfHecke → ProdOp → YSwap := by
  intro hSF hPH hPO E _ _ _ n S Z N hS hZ hG π y w hw f hf x x' hx
  obtain ⟨hth, -, -, -, -, hin, -⟩ := hSF E n S hS
  have hwS := hZ w hw
  have hN : ∀ v : Pl E, ¬ IsSplitAt v → N v = KGL v (n := n) :=
    fun v hv => (hG v).2.2.2 fun hvZ => hv (hZ v hvZ).2
  have F0 := sing_fam S N w f false ⟨hwS.1, by simp⟩ hf
  have F1 := sing_fam S N w f true ⟨hwS.1, fun _ => hwS.2⟩ hf
  have h0 := hPH E n S Z N hS hZ hG _ _ F0
  have h1 := hPH E n S Z N hS hZ hG _ _ F1
  have e : (fun g => pf S (sing N w f false) (thF E n g)) = pf S (sing N w f true) :=
    funext (pf_sing_twist S N w f hwS.2 hth hin hN)
  have t := y.tw _ h0
  rw [e] at t
  have a0 : y.r (pf S (sing N w f false)) x = x' := by
    apply Subtype.ext
    rw [y.act _ h0, hPO E n S Z N hS hZ hG _ _ F0 _ (y.fix x.2), hx]
    simp [sing_self]
  have t' := congrArg (fun T : Module.End ℂ y.Y => T x) t
  simp only [Module.End.mul_apply, a0] at t'
  rw [t', y.act _ h1, hPO E n S Z N hS hZ hG _ _ F1 _ (y.fix (y.A x).2)]
  simp [sing_self]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

private theorem conj_of_central {G : Type} [Group G] (a b : G) (h : a⁻¹ * b ∈ Subgroup.center G) (t : G) :
    b * t * b⁻¹ = a * t * a⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp h t
  calc b * t * b⁻¹ = a * ((a⁻¹ * b) * t) * (a⁻¹ * b)⁻¹ * a⁻¹ := by group
    _ = a * (t * (a⁻¹ * b)) * (a⁻¹ * b)⁻¹ * a⁻¹ := by rw [hc]
    _ = a * t * a⁻¹ := by group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.translF_pf :
    TranslF := by
  intro E _ _ _ n u hu
  have hz : (ratF E n u)⁻¹ * PhiU n (Af E) ∈ Subgroup.center (GL (Fin n) (Af E)) := by
    have h := GeneralLinearGroup.map_center_le (algebraMap E (Af E)) (translad_central E n u hu)
    rw [Subgroup.mem_comap, map_mul, map_inv, translad_map_PhiU] at h
    exact h
  have hc := conj_of_central (ratF E n u) (PhiU n (Af E)) hz
  refine ⟨fun g => ?_, ?_, PhiU n (Af E), ?_, fun g => (hc g).symm⟩
  · rw [← hc, Tw.thetaF_eq]
    exact thetaGL_eq n (Af E) _ g
  · rw [← GlobalTheory.EulerTw.Comm.thF_ratF, hu.1, hu.2, one_mul, map_inv]
  · refine Subgroup.mem_iInf.mpr fun w => ?_
    rw [Subgroup.mem_comap, translad_map_PhiU]
    exact GlobalTheory.ThetaSatake.phiU_mem _ n
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem lv_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    Lv ρ K ((K : Set G).indicator 1) v = v := by
  have hc : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := by
    have h : (QuotientGroup.mk (QuotientGroup.mk 1 : G ⧸ K).out : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.out_eq' _
    simpa using QuotientGroup.eq.1 h
  have hq : ∀ q : G ⧸ K, q ≠ QuotientGroup.mk 1 → q.out ∉ K := by
    intro q hne hmem
    apply hne
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using hmem)
  unfold Lv levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)
    (fun q hne => by rw [Set.indicator_of_notMem (hq q hne), zero_smul]),
    Set.indicator_of_mem (show _ ∈ (K : Set G) from hc)]
  simpa using hv ⟨_, hc⟩

private theorem trOn_of_id {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    [FiniteDimensional ℂ M] (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v = v) :
    trOn M L = (Module.finrank ℂ M : ℂ) := by
  have h : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [hL v hv]; exact hv
  have hid : L.restrict h = LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, hL v.1 v.2]
  unfold trOn
  rw [dite_eq_left h, hid]
  exact LinearMap.trace_id ℂ _

private theorem finFn_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) : (fun g => finFn S φ₁ φ₂ (g, 1)) = pf S (two φ₁ φ₂) := by
  funext g
  have h1 : ∀ w : Pl E, atW w ((g, 1) : Gf E n 0) = (qw n w false g, 1) :=
    fun w => Prod.ext rfl (map_one (GeneralLinearGroup.map (pLoc E w)))
  have h2 : ∀ w : Pl E, atW w (thP E n 0 (g, 1)) = (qw n w true g, 1) := by
    intro w
    refine Prod.ext rfl ?_
    simp [atW, thP]
  unfold finFn pf
  simp only [h1, h2]
  rfl

private theorem ind_hecke {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (M N' : Subgroup (GLw n w)) (ho : IsOpen (M : Set (GLw n w))) (hM : M ≤ KGL w (n := n)) (hN : N' ≤ M) :
    IsHecke N' ((M : Set (GLw n w)).indicator 1) := by
  have hcl : IsClosed (M : Set (GLw n w)) := M.isClosed_of_isOpen ho
  have hcomp : IsCompact (M : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2.of_isClosed_subset hcl hM
  refine ⟨hcomp.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal Set.support_indicator_subset hcl), fun k hk x => ?_⟩
  have a1 : k * x ∈ M ↔ x ∈ M := M.mul_mem_cancel_left (hN hk)
  have a2 : x * k ∈ M ↔ x ∈ M := M.mul_mem_cancel_right (hN hk)
  simp only [Set.indicator, SetLike.mem_coe, a1, a2, Pi.one_apply, and_self]

theorem levelTr_pf : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → ZTr → SeenTr → TTr → LevelTr := by
  intro hAdm hZ hSeen hT E _ _ _ n S Z N hSec hSp hG π y B τ hB hτ
  obtain ⟨hne, d₀, hd₀, hd⟩ := hZ E n S Z N hSec hSp hG π y τ hτ
  have hc : ∀ w ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (two φ₁ φ₂ w false) * Lv (τ w).ρ (N w) (two φ₁ φ₂ w true)) =
        c * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) :=
    fun w hw => hSeen E n w (hSp w hw).2 (τ w) (N w) (hG w).1 (hG w).2.1
  choose! c hc0 hc using hc
  refine ⟨?_, d₀ * ∏ w ∈ Z, c w, mul_ne_zero hd₀ (Finset.prod_ne_zero_iff.2 hc0), ?_⟩
  · let φ₀ : ∀ w : Pl E, LF n 0 w := fun w p => (N w : Set (GLw n w)).indicator 1 p.1
    have h2 : ∀ w b, two φ₀ φ₀ w b = (N w : Set (GLw n w)).indicator 1 := by
      intro w b
      cases b <;> rfl
    refine ⟨φ₀, fun w _ N' hN' b => ?_, Finset.prod_ne_zero_iff.2 fun w hw h0 => ?_⟩
    · rw [h2]
      exact ind_hecke w (N w) N' (hG w).1 (hG w).2.1 hN'
    · haveI : FiniteDimensional ℂ (fixed (τ w).ρ (N w)) := hAdm E n w (τ w) (N w) (hG w).1
      have e := hc w hw φ₀ φ₀ fun b => by
        rw [h2]
        exact ind_hecke w (N w) (N w) (hG w).1 (hG w).2.1 le_rfl
      rw [h0, mul_zero, h2, h2, trOn_of_id _ _ fun v hv => by
        rw [Module.End.mul_apply, lv_unit _ _ v hv, lv_unit _ _ v hv]] at e
      exact hne w hw (Submodule.finrank_eq_zero.1 (Nat.cast_eq_zero.1 e))
  · intro φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    obtain ⟨h1, h2, h3⟩ := hT E n S Z N hSec hSp hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    have hF : ∀ w ∈ Z, ∀ b, two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w b = two φ₁ φ₂ w b := by
      intro w hw b
      cases b <;> simp [two, intersection_update_fsHerm_neg_one, hw]
    have hP : ∀ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w))
        (Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w false) *
          Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) := by
      intro w hw
      rw [hF w hw, hF w hw]
      exact hc w hw φ₁ φ₂ (hφ w hw)
    rw [finFn_one S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)]
    refine ⟨h1, ?_⟩
    rw [h3, smul_mul_assoc, map_smul, hd _ h2, smul_eq_mul, Finset.prod_congr rfl hP, Finset.prod_mul_distrib]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

private theorem cv_eq_conv {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) {f g : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke K f) (hg : GlobalTheory.BCT.IsHecke K g) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv K f g = Formalism.UG.conv K f g := by
  funext y
  have hst : K ≤ GlobalTheory.BCT.rStab (fun z => f z * g (z⁻¹ * y)) := by
    intro k hk z
    show f (z * k) * g ((z * k)⁻¹ * y) = f z * g (z⁻¹ * y)
    rw [(hf.2 k hk z).2, mul_inv_rev, mul_assoc, (hg.2 k⁻¹ (K.inv_mem hk) _).1]
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ K K _ le_rfl hst (by simp [Subgroup.relIndex_self]),
    Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul]
  rfl

private theorem biInv_of_hecke {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {f : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke K f) : Formalism.UG.IsBiInv K f := by
  intro a b x
  rw [(hf.2 b b.2 _).2, (hf.2 a a.2 x).1]

private theorem cv_comm {E : Type} [Field E] [NumberField E] (n : ℕ) (w : GlobalTheory.BCT.Pl E)
    {f g : GlobalTheory.BCT.GLw n w → ℂ} (hf : GlobalTheory.BCT.IsHecke (GlobalTheory.LFun.KGL w (n := n)) f)
    (hg : GlobalTheory.BCT.IsHecke (GlobalTheory.LFun.KGL w (n := n)) g) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv (GlobalTheory.LFun.KGL w (n := n)) f g = UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv (GlobalTheory.LFun.KGL w (n := n)) g f := by
  rw [cv_eq_conv _ hf hg, cv_eq_conv _ hg hf]
  exact Formalism.UG.P.heckecomm_gelfand (GlobalTheory.LFun.KGL w (n := n)) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x hx => Formalism.UG.P.heckecomm_tr_mem _ x hx)
    (Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n) f g (biInv_of_hecke hf) (biInv_of_hecke hg)

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.sphOp_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SphOp := by
  intro hCv E _ _ _ n w V _ _ ρ f g hf hg x hx
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have h₁ := (hCv _ _ hKo hKc V ρ f g hf hg x hx).1
  have h₂ := (hCv _ _ hKo hKc V ρ g f hg hf x hx).1
  rw [cv_comm n w hf hg] at h₁
  exact h₁.symm.trans h₂
end

section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem traceForm_pf : TraceForm := by
  intro J M Y _ _ _ _ _ _ α a C hs hk hc p
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx

  let lam : FreeAlgebra ℂ J →ₗ[ℂ] ℂ :=
    LinearMap.trace ℂ Y ∘ₗ LinearMap.mulRight ℂ C ∘ₗ (FreeAlgebra.lift ℂ a).toLinearMap
  have lam_apply : ∀ r, lam r = LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a r * C) := fun _ => rfl
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective
    (FreeAlgebra.lift ℂ α).toLinearMap (LinearMap.range_eq_top.2 surj)
  have sec : ∀ T, FreeAlgebra.lift ℂ α (s T) = T := fun T => LinearMap.congr_fun hs' T

  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' → lam r = lam r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    have h1 : lam (r - r') = 0 := by rw [lam_apply, h0, zero_mul, map_zero]
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  let g : Module.End ℂ M →ₗ[ℂ] ℂ := lam ∘ₗ s
  have g_apply : ∀ r, g (FreeAlgebra.lift ℂ α r) = lam r := fun r => same _ _ (sec _)
  obtain ⟨c, hc'⟩ := DiscreteGroups.T1.Desc.Swap3.trace_unique g (by
    intro x y
    obtain ⟨r, rfl⟩ := surj x
    obtain ⟨r', rfl⟩ := surj y
    rw [← map_mul, ← map_mul, g_apply, g_apply, lam_apply, lam_apply,
      map_mul (FreeAlgebra.lift ℂ a), map_mul (FreeAlgebra.lift ℂ a)]
    exact hc r r')
  have hp : lam p = c * LinearMap.trace ℂ M (FreeAlgebra.lift ℂ α p) := by
    rw [← g_apply, hc']
  have h1 : LinearMap.trace ℂ Y C = c * (Module.finrank ℂ M : ℂ) := by
    have := g_apply 1
    rw [hc', map_one (FreeAlgebra.lift ℂ α), LinearMap.trace_one, lam_apply, map_one (FreeAlgebra.lift ℂ a), one_mul] at this
    exact this.symm
  rw [← lam_apply, hp, h1]
  ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end
