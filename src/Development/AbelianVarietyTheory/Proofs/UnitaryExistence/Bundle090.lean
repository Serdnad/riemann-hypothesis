module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle087
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatMove

variable {D : D7} (V : HSp D)

theorem mem_hat_iff (g : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V g ↔ ∃ z ∈ latGHat V 1, (finHom V g).1 *ᵥ z = w := by
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  have h2 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
  rw [h2, ← SetLike.mem_coe, h1]
  rfl

theorem mem_lat_iff (g : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V g ↔ finVec V v ∈ latGHat V g := by
  have h0 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  rw [← SetLike.mem_coe, h0, ← SetLike.mem_coe, h1]
  rfl

theorem fin_mul (g h : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ z = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem fin_one (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V 1).1 *ᵥ z = z := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem move_mem (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V h) : (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  obtain ⟨z, hz, rfl⟩ := (mem_hat_iff V h w).1 hw
  exact (mem_hat_iff V _ _).2 ⟨z, hz, fin_mul V g h z⟩

theorem move_iff (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V h ↔ (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  refine ⟨move_mem V g h w, fun hw => ?_⟩
  have := move_mem V g⁻¹ _ _ hw
  rwa [← fin_mul, inv_mul_cancel, fin_one, inv_mul_cancel_left] at this

theorem lat_eq_of_hat_eq {h h' : GA D V} (e : latGHat V h = latGHat V h') : latG V h = latG V h' := by
  ext v
  rw [mem_lat_iff, mem_lat_iff, e]

theorem finCong_one {N : ℕ} {k : GA D V} (hk : FinCong V N k) : FinCong V 1 k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  exact ⟨N • y, AddSubgroup.nsmul_mem _ hy N, by rw [one_nsmul, e]⟩

theorem hat_eq_of_finCong {N : ℕ} {k : GA D V} (hk : FinCong V N k) : latGHat V k = latGHat V 1 := by
  have h1 := (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V k).1.2 (finCong_one V hk)
  have h2 : ∀ z ∈ latGHat V 1, (finHom V k⁻¹).1 *ᵥ z ∈ latGHat V 1 := by
    have hh := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
    rw [hh] at h1 ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latG V 1) (finHom V k) (cF D)
      (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1 h1 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).2.1
  ext w
  rw [mem_hat_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact h1 z hz
  · intro hw
    exact ⟨_, h2 w hw, by rw [← fin_mul, mul_inv_cancel, fin_one]⟩

end GlobalTheory.Member.LatMove


open GlobalTheory.Member.LatMove in
theorem GlobalTheory.Member.latG_move : ∀ (D : D7) (V : HSp D), (∀ γ γ' h, IsRat V γ γ' → (∀ v, v ∈ latG V h ↔ (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V (γ * h)) ∧ ∀ w, w ∈ latGHat V h ↔ (finHom V γ).1 *ᵥ w ∈ latGHat V (γ * h)) ∧ (∀ h h', finHom V h = finHom V h' → latG V h = latG V h' ∧ latGHat V h = latGHat V h') ∧ (∀ (N : ℕ) h k, FinCong V N k → latG V (h * k) = latG V h ∧ latGHat V (h * k) = latGHat V h) ∧ ∀ h h', latG V h = latG V h' → FinCong V 1 (h⁻¹ * h') := by
  intro D V
  refine ⟨fun γ γ' h hγ => ⟨fun v => ?_, fun w => move_iff V γ h w⟩, fun h h' e => ?_, fun N h k hk => ?_,
    fun h h' e => ?_⟩
  · rw [mem_lat_iff, mem_lat_iff, move_iff V γ h, ((GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V).2.2.2.2 γ γ' hγ).1 v]
  · have : latGHat V h = latGHat V h' := by
      ext w
      rw [mem_hat_iff V h, mem_hat_iff V h', e]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have : latGHat V (h * k) = latGHat V h := by
      ext w
      rw [move_iff V h⁻¹ (h * k), move_iff V h⁻¹ h, inv_mul_cancel_left, inv_mul_cancel,
        hat_eq_of_finCong V hk]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have e' : latGHat V h = latGHat V h' := by
      rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V h).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V h').2.2.2.2.1, e]
    refine (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V (h⁻¹ * h')).1.1 fun z hz => ?_
    have h1 := move_mem V h' 1 z hz
    rw [mul_one, ← e'] at h1
    have h2 := move_mem V h⁻¹ h _ h1
    rwa [← fin_mul, inv_mul_cancel] at h2
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D), (∀ k : GA D V, FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y) ∧ ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  first | exact @GlobalTheory.Member.finCong_iff_half_and_kfHalf | exact GlobalTheory.Member.finCong_iff_half_and_kfHalf | (intros; apply GlobalTheory.Member.finCong_iff_half_and_kfHalf <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatSelfDual

variable {D : D7}

theorem cF_eq_conj (D : D7) (x : D.host.E) : cF D x = D.host.conj x :=
  bridge_star_holds D.R D.host x

noncomputable def frameForm (V : HSp D) (v y : Fin V.rank → D.host.E) : D.host.E :=
  ∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)

theorem frameForm_smul_left (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (e • v) y = e * frameForm V v y := by
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_smul_right (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (e • y) = D.host.conj e * frameForm V v y := by
  rw [← cF_eq_conj]
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_add_left (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V (v + w) y = frameForm V v y + frameForm V w y := by
  simp only [frameForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem frameForm_add_right (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V v (w + y) = frameForm V v w + frameForm V v y := by
  simp only [frameForm, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem frameForm_int_smul_left (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (c • v) y = c • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c v, frameForm_smul_left, Algebra.smul_def]

theorem frameForm_int_smul_right (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (c • y) = (D.host.conj • c) • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c y, frameForm_smul_right, Algebra.smul_def, algebraMap_conj_smul]

theorem mem_iff_trace (D : D7) (z : D.host.E) :
    z ∈ D.host.AA * D.host.AAbar ↔
      ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  constructor
  · intro hz a
    have h : a • z ∈ NAA D := Submodule.smul_mem _ a hz
    rw [Algebra.smul_def] at h
    exact trace_int_of_mem hP D h
  · intro h
    have hz : D.host.xi0 * z ∈
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [FractionalIdeal.mem_dual
        (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro a ha
      rw [FractionalIdeal.mem_one_iff] at ha
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨n, hn⟩ := h c
      rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
      exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
    rw [← dual_eq hP D] at hz
    have h4 := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
    have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
        D.host.AA * D.host.AAbar := by
      rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
        FractionalIdeal.spanSingleton_one, one_mul]
    rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  intro h
  have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h, mul_zero, zero_mul] at h1
  exact zero_ne_one h1

theorem selfDual_one (V : HSp D) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V 1, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V 1 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  have hAb := AAbar_ne_zero D
  have hC : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, frameForm V v y ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V :=
    (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.2.2.2.2.2
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2]
  constructor
  · intro h
    have h5 : ∀ y0 ∈ latC V, frameForm V v y0 ∈ D.host.AA := by
      intro y0 hy0
      have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) *
          D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
        rw [FractionalIdeal.spanSingleton_mul_le_iff]
        intro b hb
        have := h (D.host.conj b • y0) (Submodule.subset_span ⟨_, conj_mem_AA D hb, y0, hy0, rfl⟩)
        rw [frameForm_smul_right, conj_conj, mul_comm b] at this
        exact this
      have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) ≤
          D.host.AA := by
        calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0)
            = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
                (frameForm V v y0) * D.host.AAbar) := by
              rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
          _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
          _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)
    have h6 : ∀ c ∈ D.host.AA⁻¹, c • v ∈ latC V := by
      intro c hc
      refine (hC _).1 fun y hy => ?_
      rw [frameForm_smul_left, ← inv_mul_cancel₀ hAA]
      exact FractionalIdeal.mul_mem_mul hc (h5 y hy)
    have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
      intro e he
      refine FractionalIdeal.mul_induction_on (C := fun e => e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x}) he (fun a ha c hc => ?_) (fun u w hu hw => ?_)
      · show (a * c) • v ∈ _
        rw [mul_smul]; exact Submodule.subset_span ⟨a, ha, c • v, h6 c hc, rfl⟩
      · show (u + w) • v ∈ _
        rw [add_smul]; exact add_mem hu hw
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    rwa [one_smul] at this
  · intro hv w hw
    show frameForm V v w ∈ NAA D
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hv
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨b, hb, y, hy, rfl⟩ := hw
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((hC x).2 hx y hy)
        rw [frameForm_smul_left, frameForm_smul_right, ← hr, ← mul_assoc, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
      | zero => simp [frameForm]
      | add w w' _ _ h h' => rw [frameForm_add_right]; exact add_mem h h'
      | smul c w _ h => rw [frameForm_int_smul_right]; exact Submodule.smul_mem _ _ h
    | zero => simp [frameForm]
    | add v v' _ _ h h' => rw [frameForm_add_left]; exact add_mem h h'
    | smul c v _ h => rw [frameForm_int_smul_left]; exact Submodule.smul_mem _ _ h

theorem selfDual (V : HSp D) (g : GA D V) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V g, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V g := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg, hspan, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  have hlat := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E V.rank (latG V 1) (cF D) V.gramᵀ
    (D.host.AA * D.host.AAbar) (finHom V g) hfg hspan hcc hG hdet
    (mul_ne_zero (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (AAbar_ne_zero D))
    (selfDual_one V) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V g).1 v
  rw [← hlat] at key
  exact key

end GlobalTheory.Member.LatSelfDual

namespace GlobalTheory.Member

open LatSelfDual

theorem latG_selfDual : ∀ (D : D7) (V : HSp D), ∀ (g : GA D V) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), J = D.host.AA * D.host.AAbar → (∀ z : D.host.E, z ∈ J ↔ ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) ∧ (∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ J) ↔ v ∈ latG V g) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔ v ∈ latG V g := by
  intro D V g J hJ
  subst hJ
  refine ⟨mem_iff_trace D, selfDual V g, fun v => ?_⟩
  have hcc := (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.1
  have hh : ∀ y, herm (-V.gramᵀ) v y = - frameForm V v y := by
    intro y
    simp only [herm, frameForm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  have ht : ∀ y, (∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * frameForm V v y) = n := by
    intro y
    rw [hh, neg_neg, mul_neg, map_neg]
    exact ⟨fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩,
      fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, hn]⟩⟩
  simp only [ht]
  rw [← selfDual V g v]
  constructor
  · intro h y hy
    refine (mem_iff_trace D _).2 fun a => ?_
    have h1 := h _ ((latG V g).smul_mem (D.host.conj⁻¹ • a) hy)
    rw [frameForm_int_smul_right, smul_inv_smul, Algebra.smul_def] at h1
    exact h1
  · intro h y hy
    exact trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (h y hy)

end GlobalTheory.Member
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_isSplit_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty _ hc i
  have hp : (F.Di i).p = D.p := (F.sig i).1
  have hq : (F.Di i).q = D.q := (F.sig i).2
  refine GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit E H (F.Di i) g ty (by rw [hp, hq]; exact hty) ?_
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H (F.Di i) (by rw [hp, hq]; exact h0)
  · have h1 : D.p ≠ 0 := fun h => h0 (Or.inl h)
    have h2 : D.q ≠ 0 := fun h => h0 (Or.inr h)
    rcases hc with h | h | ⟨h3, h4⟩
    · exact absurd h h1
    · exact absurd h h2
    · exact GlobalTheory.T.hermitianLatticeSignatureSplit_of_indefinite E H (F.Di i) h4 (by omega) (by omega) (by omega)

end GlobalTheory.CompRat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_split_period_any_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  first | exact @GlobalTheory.CompRat.exists_isSplit_period_anyLevel | exact GlobalTheory.CompRat.exists_isSplit_period_anyLevel | (intros; apply GlobalTheory.CompRat.exists_isSplit_period_anyLevel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_borelPairs_universalFrame_openChart : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := by
  first | exact @GlobalTheory.Frames.univFrame_borelPairs | exact GlobalTheory.Frames.univFrame_borelPairs | (intros; apply GlobalTheory.Frames.univFrame_borelPairs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.integralLattice_structure_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntLatU Xo c := by
  first | exact @GlobalTheory.Frames.intLatU_holds | exact GlobalTheory.Frames.intLatU_holds | (intros; apply GlobalTheory.Frames.intLatU_holds <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  first | exact @GlobalTheory.Member.Arch.archM_spec | exact GlobalTheory.Member.Arch.archM_spec | (intros; apply GlobalTheory.Member.Arch.archM_spec <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem _root_.GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M := by
  first | exact @GlobalTheory.PrincCore.hasPrinc_core | exact GlobalTheory.PrincCore.hasPrinc_core | (intros; apply GlobalTheory.PrincCore.hasPrinc_core <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.integralFrame_change_integral_invertible_matrix : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Formalism.L2.PjFree.IntRebase Xo c := by
  first | exact @GlobalTheory.IntRebase.intRebase | exact GlobalTheory.IntRebase.intRebase | (intros; apply GlobalTheory.IntRebase.intRebase <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem semiAbelian_hom_extends_uniquely_dvr :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) :=
  existsUnique_hom_extension_semiAbelian_dvr AbelianSubgroupFinite.finite_of_torsionFree

end GlobalTheory
end
