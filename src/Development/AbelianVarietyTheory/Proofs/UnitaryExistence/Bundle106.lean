module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle096
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle105
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Occ

open GlobalTheory.AdLat GlobalTheory.AdLat.Half
open scoped nonZeroDivisors

theorem form_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : FractionalIdeal (𝓞 E)⁰ E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (hL : ∀ x ∈ L, ∀ y ∈ L, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J)
    (hg : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y) {N : ℕ} (hN : 0 < N)
    {x y x' y' : Fin n → E} (hx : x ∈ L) (hy : y ∈ L) {w w' : Fin n → RA F E}
    (hw : w ∈ hat F (L : Set (Fin n → E))) (hw' : w' ∈ hat F (L : Set (Fin n → E)))
    (ex : fv F x' = g *ᵥ (fv F x + N • w)) (ey : fv F y' = g *ᵥ (fv F y + N • w')) :
    ∃ z ∈ J, (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) = N * z := by
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, hL x hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  have both : ∀ u ∈ hat F (L : Set (Fin n → E)), ∀ v ∈ hat F (L : Set (Fin n → E)),
      hermA c G u v ∈ hat1 F (J : Set E) := fun u hu v hv => herm_mem_of_fv c G _ _ _ (back u hu) v hv
  have hMs : ∀ x : Fin n → RA F E, N • x = (N : RA F E) • x := fun x =>
    (Nat.cast_smul_eq_nsmul _ _ _).symm
  have hsM : sg (FiniteAdeleRing (𝓞 F) F) c (N : RA F E) = N := map_natCast _ N
  have hfx := fv_mem_hat' (F := F) (L : Set (Fin n → E)) x hx
  have hfy := fv_mem_hat' (F := F) (L : Set (Fin n → E)) y hy
  have hu : hermA c G w (fv F y + N • w') + hermA c G (fv F x) w' ∈ hat1 F (J : Set E) :=
    add_mem (both _ hw _ (add_mem hfy (nsmul_mem hw' N))) (both _ hfx _ hw')
  have e1 : hermA c G (fv F x') (fv F y') - hermA c G (fv F x) (fv F y) =
      (N : RA F E) * (hermA c G w (fv F y + N • w') + hermA c G (fv F x) w') := by
    rw [ex, ey, hg, Half.herm_add_left, hMs w, Half.herm_smul_left, Half.herm_add_right c G (fv F x), hMs w',
      Half.herm_smul_right, hsM]
    ring
  have e2 : ∀ x y : Fin n → E, hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) :=
    fun x y => hermA_tmul_fv c G 1 x y
  rw [e2, e2, ← TensorProduct.tmul_sub] at e1
  set d := (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) with hd
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : RA F E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E) :=
    (map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) N).symm
  refine ⟨(N : E)⁻¹ * d, ((adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 ?_, by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]⟩
  have e3 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E)⁻¹ * d) : RA F E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [e3, e1, hNt, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hN',
    ← Algebra.TensorProduct.one_def, one_mul]
  exact hu

theorem herm_neg' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : herm (-G) x y = -∑ a, ∑ b, x a * G a b * cc (y b) := by
  simp [herm]

theorem trace_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, cc (G a b) = G b a) (ξ : E) (hξ : cc ξ = -ξ) (x y : Fin n → E) :
    Algebra.trace ℚ E (ξ * -herm G y x) = Algebra.trace ℚ E (ξ * herm G x y) := by
  have h1 : cc (herm G x y) = herm G y x := by
    unfold herm
    unfold cc at *
    rw [Finset.sum_comm]

    simp only [map_sum, map_mul, hG, IsCMField.complexConj_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (ξ * herm G x y)
  rw [← h2, ← h1]
  congr 1
  unfold cc at *
  change _ = IsCMField.complexConj E _
  rw [map_mul, hξ]
  ring

theorem mark_congr {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (RA F E)) {N : ℕ} {x x' t w : Fin n → E} {w' : Fin n → RA F E}
    (e : A *ᵥ fv F x' = fv F (t + N • w)) (e' : fv F x' = B *ᵥ (fv F x + N • w')) :
    fv F t - (A * B) *ᵥ fv F x = N • ((A * B) *ᵥ w' - fv F w) := by
  rw [e', Matrix.mulVec_mulVec, Tower.fv_add, Tower.fv_nsmul, Matrix.mulVec_add, Tower.mulVec_nsmul] at e
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← e, add_comm]

end GlobalTheory.Member.Occ


open GlobalTheory.Member.Occ GlobalTheory.AdLat in
theorem GlobalTheory.Member.exists_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  intro D H Dw l Xo c σ V r C hC h
  obtain ⟨hr, g, e, F, M, ι, θ, x₀⟩ := C
  subst hr
  obtain ⟨⟨-, -, ⟨hinj, hrange⟩, hisom⟩, -, hA, hgood, hbase, hW, -, -⟩ := hC
  dsimp only at hinj hrange hisom hbase hW
  obtain ⟨-, hfv, -, -, -, hcc, -, hGc, hGdet, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg1, hsp1, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  obtain ⟨hfg, hsp, hlat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  obtain ⟨hJ, hsd1, -⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl
  obtain ⟨-, -, hsd⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V h _ rfl
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1)
    (finHom V h) (latG V h) hfg1 hsp1 hlat
  let ε : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hε : ∀ a, (ε a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  have hk : ∀ k, (M.X k).Gm = -V.gramᵀ ∧ (M.X k).ξ0 = -D.host.xi0 := fun k => by
    obtain ⟨h1, h2⟩ := hW k
    exact ⟨by rw [h1]; rfl, h2⟩
  have hξ : cc D.host.xi0 = -D.host.xi0 := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg] at h
    exact neg_injective h
  have hG' : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [← hcc, Matrix.neg_apply, Matrix.neg_apply, map_neg, hGc]
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    rw [hisom, hT, trace_swap _ hG' _ hξ, neg_neg]
  obtain ⟨k, γ', hu, hl, hm⟩ := GlobalTheory.selfDual_lattice_occurs GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ g _ F V.rank M
    (-D.host.xi0) (-V.gramᵀ) ι (latG V h) (fun N => f N ∘ₗ ε.toLinearMap) hA hgood
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hgood).2.2.2 Dw g e) hbase hk
    ⟨hinj, by rw [← LinearMap.coe_range, hrange]; exact hsp1, hG', by
      rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGdet, hEF⟩ hfg hsp hsd
    (fun n m hn hm a => hf2 n m hn hm (ε a))
    (fun n hn => ⟨fun a => ((hf3 n hn).1 (ε a)).trans
      ⟨fun ⟨v, hv⟩ => ⟨ε.symm v, ε.injective (by rw [hv, map_nsmul, ε.apply_symm_apply])⟩,
        fun ⟨v, hv⟩ => ⟨ε v, by rw [hv, map_nsmul]⟩⟩, fun a' => by
      obtain ⟨a, v, hv⟩ := (hf3 n hn).2 a'
      exact ⟨ε.symm a, v, by simpa using hv⟩⟩)
    (fun n hn a a' => by
      obtain ⟨w, hw, ew⟩ := hf1 n hn (ε a)
      obtain ⟨w', hw', ew'⟩ := hf1 n hn (ε a')
      obtain ⟨z, hz, ez⟩ := form_congr (latG V 1) (cF D) V.gramᵀ _ _
        (fun x hx => (hsd1 x).2 hx) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).1 hn (ε a).2 (ε a').2 hw hw' ew ew'
      obtain ⟨t, ht⟩ := (hJ z).1 hz 1
      refine ⟨-t, ?_⟩
      simp only [hcc, hε] at ez
      rw [hEF, ← map_sub, ← mul_sub, herm_neg', herm_neg', neg_sub_neg, ← neg_sub]
      erw [ez]
      have : -(-D.host.xi0) * -((n : D.host.E) * z) =
          (-(n : ℚ)) • (D.host.xi0 * (((1 : 𝓞 D.host.E) : D.host.E) * z)) := by
        simp [Algebra.smul_def]; ring
      rw [this, map_smul, ht]
      simp)
  obtain ⟨hQ, -, hex, -, hfin⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨γ, hγ⟩ := hex γ' hu
  obtain ⟨hmv, -⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ γ' h hγ
  obtain ⟨-, -, -, hhat1, hhat2, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V (γ * h)
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
    have e : v = γ'.val *ᵥ ((γ'⁻¹).val *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, ← hl, ← hmv]
  refine ⟨k, γ, (hQ γ).2 ⟨γ', hγ⟩, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · intro hv
      exact ⟨v, (hΛ v).1 hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hΛ v).2 hv
  · obtain ⟨w, hw, ew⟩ := hm a ha
    obtain ⟨w', hw', ew'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ε a)
    have m1 : (finHom V (γ * h)).1 *ᵥ w' ∈ latGHat V (γ * h) := by
      rw [← SetLike.mem_coe, hhat1]
      exact ⟨w', hw', rfl⟩
    have m2 : fv D.host.F w ∈ latGHat V (γ * h) := by
      rw [hhat2]
      exact Half.fv_mem_hat' _ _ ((hΛ w).1 hw)
    refine ⟨_, sub_mem m1 m2, ?_⟩
    have e1 := (hfin γ γ' hγ).1 (f l.M (ε a))
    have ew2 : γ'.val *ᵥ (f l.M (ε a) : Fin V.rank → D.host.E) =
        (M.φ k (F.t k a) : Fin V.rank → D.host.E) + l.M • w := ew
    rw [ew2] at e1
    have e2 := mark_congr (finHom V γ).1 (finHom V h).1 e1 ew'
    rw [← Units.val_mul, ← map_mul] at e2
    exact e2
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.MarkUniq

lemma nsmul_cancel (F : Type) [Field F] {M : Type} [AddCommGroup M] [Module F M] {N : ℕ} (hN : (N : F) ≠ 0)
    {x y : M} (h : N • x = N • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective _ hN h

lemma sub_eq_nsmul_sub {M : Type} [AddCommGroup M] {N : ℕ} {x y z w w' : M} (h : x - z = N • w) (h' : y - z = N • w') :
    x - y = N • (w - w') := by
  rw [smul_sub, ← h, ← h']; abel

lemma exists_of_finVec_eq_nsmul {D : D7} (V : HSp D) (g : GA D V) (N : ℕ) (hN : N ≠ 0)
    (u : Fin V.rank → D.host.E) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V g)
    (h : finVec V u = N • w) : ∃ x ∈ latG V g, u = N • x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V g
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hu : u = N • ((N : D.host.E)⁻¹ • u) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  refine ⟨(N : D.host.E)⁻¹ • u, ?_, hu⟩
  refine ((GlobalTheory.T.adelicCompletion_rational_points_and_approximation D.host.F D.host.E V.rank (latG V g) h1 h2).1 _).1 ?_
  have e : N • finVec V ((N : D.host.E)⁻¹ • u) = N • w := by
    rw [← h]
    conv_rhs => rw [hu]
    funext i
    simp only [finVec, Pi.smul_apply]
    exact (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) N _).symm
  have e' := nsmul_cancel D.host.F hNF e
  rw [h5, ← e'] at hw
  exact hw

lemma finVec_sub {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    finVec V (u - v) = finVec V u - finVec V v := by
  funext i
  simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]

lemma half_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (t : A →ₗ[𝓞 E] B) (ht : ∀ b, ∃ a e, b = t a + l.M • e) (b : B)
    (hb : b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) B)) :
    ∃ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) A), ∃ e, b = t a + l.M • e := by
  obtain ⟨a, e, hae⟩ := ht b
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have h2 : x • b ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) B) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hx hb
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨e', -, he'⟩ := h2
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, e' + y • e, ?_⟩
  rw [Nat.cast_smul_eq_nsmul] at he'
  have : b = x • b + y • b := by rw [← add_smul, hxy, one_smul]
  rw [this, ← he', map_smul, smul_add, smul_comm l.M y e]
  conv_lhs => rw [hae]
  rw [smul_add]
  abel

lemma matched {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} (C : Ctx Xo c σ V V.rank) (h : GA D V) (k k' : Fin C.F.n)
    (γ γ' : GA D V) (hm : C.Mark h k γ) (hm' : C.Mark h k' γ') :
    ∃ δ : GL (Fin V.rank) D.host.E, IsRat V (γ' * γ⁻¹) δ ∧
      (∀ v, v ∈ (C.M.X k).Λ ↔ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ (C.M.X k').Λ) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ (C.M.X k').Λ,
          (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) =
            (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) + l.M • w := by
  obtain ⟨r1, -, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨hγ, hΛ, hk⟩ := hm
  obtain ⟨hγ', hΛ', hk'⟩ := hm'
  obtain ⟨δ, hδ⟩ := (r1 _).1 ((GQ V).mul_mem hγ' ((GQ V).inv_mem hγ))
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 _ δ (γ * h) hδ
  have hg : γ' * γ⁻¹ * (γ * h) = γ' * h := by group
  rw [hg] at m1 m2
  have hL : (C.M.X k).Λ = latG V (γ * h) := SetLike.ext' (hΛ.trans (Set.image_id _))
  have hL' : (C.M.X k').Λ = latG V (γ' * h) := SetLike.ext' (hΛ'.trans (Set.image_id _))
  refine ⟨δ, hδ, fun v => by rw [hL, hL']; exact m1 v, fun a ha => ?_⟩
  obtain ⟨w, hw, e⟩ := hk a ha
  obtain ⟨w', hw', e'⟩ := hk' a ha
  change finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _ at e
  change finVec V (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) - _ = _ at e'
  have e2 := congrArg (fun z => (finHom V (γ' * γ⁻¹)).1 *ᵥ z) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
  rw [(r5 _ δ hδ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hg] at e2
  obtain ⟨x, hx, hx'⟩ := exists_of_finVec_eq_nsmul V (γ' * h) l.M (by have := l.three_le; omega)
    ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
      (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E)) ((finHom V (γ' * γ⁻¹)).1 *ᵥ w - w')
    (sub_mem ((m2 w).1 hw) hw') ((finVec_sub V _ _).trans (sub_eq_nsmul_sub e2 e'))
  exact ⟨x, hL' ▸ hx, by rw [← hx']; abel⟩

theorem mark_unique : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, r2, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  have hG : ∀ k, (C.M.X k).Gm = -V.gramᵀ := fun k => (hC.modelW k).1
  refine ⟨fun k k' γ γ' hm hm' => ?_, fun k γ γ' hm hm' => ?_⟩
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k' γ γ' hm hm'
    refine GlobalTheory.ClassUniq.eq_of_matched GlobalTheory.T.thetaUniformisation_complexAbelianVariety GlobalTheory.firstFiveLaws.1 _ H Dw l Xo _ C.g _ C.F _ C.M k k' δ
      hC.pos hC.good ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hC.good).2.2.2 Dw C.g C.e) hC.base
      ((hG k').trans (hG k).symm) ((hC.modelW k').2.trans (hC.modelW k).2.symm)
      (by rw [hG k]; exact r2 _ δ hδ) hΛ hmk (fun a => ?_)
    refine ⟨_ - _, sub_mem ((hΛ _).1 (C.M.φ k (C.F.t k a)).2) (C.M.φ k' (C.F.t k' a)).2, ?_⟩
    rw [hC.lA, one_smul]; abel
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k γ γ' hm hm'
    have hφ : ∀ w ∈ (C.M.X k).Λ, ∃ b, (C.M.φ k b : Fin V.rank → D.host.E) = w := fun w hw =>
      ⟨(C.M.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
    refine ⟨δ, (hC.base.gam k δ).2 ⟨⟨by rw [hG k]; exact r2 _ δ hδ, hΛ⟩, fun b hb => ?_, fun a => ?_⟩, ?_⟩
    · have hM : l.M' = l.M := by rw [Level.M', hC.lA, Nat.lcm_one_right]
      obtain ⟨a, ha, e, rfl⟩ := half_surj l (C.F.t k) (fun b => hM ▸ C.F.t_surj k b) b hb
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      obtain ⟨b', hb'⟩ := hφ _ (sub_mem (add_mem hw ((hΛ _).1 (C.M.φ k e).2)) (C.M.φ k e).2)
      refine ⟨b', ?_⟩
      rw [hb', map_add (f := _), map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul, Matrix.mulVec_add,
        Matrix.mulVec_smul, hw', smul_sub, smul_add]
      abel
    · obtain ⟨b', hb'⟩ := hφ _ (sub_mem ((hΛ _).1 (C.M.φ k a).2) (C.M.φ k a).2)
      refine ⟨b', ?_⟩
      rw [hb', hC.lA, one_smul]; abel
    · funext τ
      have hg : γ' * h = γ' * γ⁻¹ * (γ * h) := by group
      have e := ((GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf).1 τ.1).2.1 (γ' * γ⁻¹) (γ * h)
      rw [← hg, (r5 _ δ hδ).2 τ.1 _ (hC.inf τ.1)] at e
      change archM V (C.θ τ.1) (γ' * h) * C.x₀ τ.1 =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [e, Matrix.mul_assoc]

end GlobalTheory.MarkUniq
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  first | exact @GlobalTheory.Member.exists_ctx | exact GlobalTheory.Member.exists_ctx | (intros; apply GlobalTheory.Member.exists_ctx <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_hom_of_pureType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ _ C i P hP ε a ha
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t
  obtain ⟨φ, -, hφ⟩ := exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq
    C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.CompRat
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_hom_of_pureType_of_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP ε a ha
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t
  obtain ⟨φ, -, hφ⟩ := exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq
    C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.CompRat
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ _root_.Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  first | exact @GlobalTheory.ThetaPtChg.thetaPt_change | exact GlobalTheory.ThetaPtChg.thetaPt_change | (intros; apply GlobalTheory.ThetaPtChg.thetaPt_change <;> assumption)
end
