module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle309
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle084
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle006
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

theorem _root_.GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  exact @GlobalTheory.Transport.TwistRead.qread
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.FlatFix

variable {D : D7}

theorem two_ne_zero_at (w : Pl D) : (2 : Fv D.host.F w) ≠ 0 := by
  rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]
  exact (map_ne_zero_iff _ (algebraMap D.host.F (Fv D.host.F w)).injective).2 two_ne_zero

theorem two_inv_int (w : Pl D) (hw : (2 : 𝓞 D.host.F) ∉ w.asIdeal) :
    (2⁻¹ : Fv D.host.F w) ∈ w.adicCompletionIntegers D.host.F := by
  have h3 : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (2 : 𝓞 D.host.F)
    rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hw] at this
    rw [← this]
    congr 1
  have h2 : ((2 : D.host.F) : Fv D.host.F w) = 2 := by
    rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]; rfl
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← h2,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h3, inv_one]

theorem finite_two (P : Pl D → Prop) : {v : Pl D | P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv.2


open Classical in
def halfOff (P : Pl D → Prop) : Af D.host.F :=
  RestrictedProduct.mk (fun w => if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0)
    (Filter.Eventually.of_forall fun w => by
      split_ifs with h
      · exact two_inv_int w h.2
      · exact zero_mem _)

open Classical in
theorem evalV_halfOff (P : Pl D → Prop) (w : Pl D) :
    evalV D.host.F w (halfOff P) = if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0 := rfl

theorem halfOff_int (P : Pl D → Prop) : halfOff P ∈ intAf D.host.F := by
  classical
  intro w
  rw [evalV_halfOff]
  split_ifs with h
  · exact two_inv_int w h.2
  · exact zero_mem _

theorem pair_add (a b : Af D.host.F) : pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
  Prod.ext (add_zero (0 : Ainf D.host.F)).symm rfl

theorem sum_pair {ι : Type} (s : Finset ι) (α : ι → Af D.host.F) :
    ∑ i ∈ s, pairA D.host.F 0 (α i) = pairA D.host.F 0 (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Prod.ext rfl rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, pair_add]

theorem indicatorIdempotent_eq_add_sum (P : Pl D → Prop) (Qs : Finset (Pl D)) (hQ : ∀ v, v ∈ Qs ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Pl D → AF D.host.F) (hε : ∀ v ∈ Qs, IsPlaceIdem D v (ε v)) :
    GlobalTheory.SelfDualAt.cP P = pairA D.host.F 0 (halfOff P + halfOff P) + ∑ v ∈ Qs, ε v := by
  classical
  choose! α hα h1 h0 using hε
  rw [Finset.sum_congr rfl hα, sum_pair, ← pair_add]
  unfold GlobalTheory.SelfDualAt.cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  change evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) = evalV D.host.F w (halfOff P + halfOff P + ∑ i ∈ Qs, α i)

  rw [map_add (f := _), map_add (f := _), map_sum, GlobalTheory.SelfDualAt.evalV_indP, evalV_halfOff]
  by_cases hw : w ∈ Qs
  · obtain ⟨hP, h2⟩ := (hQ w).1 hw
    rw [Finset.sum_eq_single_of_mem w hw (fun v hv hvw => h0 v hv w (Ne.symm hvw)), h1 w hw, if_pos hP,
      if_neg (fun h => h.2 h2), zero_add, zero_add]
  · rw [Finset.sum_eq_zero (fun v hv => h0 v hv w (fun h => hw (h ▸ hv))), add_zero]
    by_cases hP : P w
    · have h2 : (2 : 𝓞 D.host.F) ∉ w.asIdeal := fun h2 => hw ((hQ w).2 ⟨hP, h2⟩)
      rw [if_pos hP, if_pos ⟨hP, h2⟩, ← two_mul, mul_inv_cancel₀ (two_ne_zero_at w)]
    · rw [if_neg hP, if_neg (fun h => hP h.1), add_zero]

theorem int_alg_pair {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) ∈ intAE D := by
  have e : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) = pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) =
      β ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
    show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]; rfl
  rw [e, e2]
  exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩

theorem fix_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} {z : WO S T}
    (hiso : ∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) {a b : AE D}
    (ha : heisO ψ S T (a • z) f = f) (hb : heisO ψ S T (b • z) f = f) : heisO ψ S T ((a + b) • z) f = f := by
  have key := GlobalTheory.LatVac.heisO_heisO ψ (a • z) (b • z) f
  rw [hb, ha, hiso a b, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
  exact key.symm

end GlobalTheory.FinPl.FlatFix


open GlobalTheory.FinPl.FlatFix in
theorem GlobalTheory.FinPl.FlatFix.fix_of_isotropic : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), IsSelfDualC S LS → IsSelfDualC T LT → (∀ v, P v → Tame D v) → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f → ∀ z ∈ latO S T (LS : Set _) (LT : Set _) P, (∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) → heisO ψ S T z f = f := by
  intro D ψ S T LS LT P _ _ hT f hf z hz hiso
  classical
  have hfix_split : ∀ e, IsSplitIdem D e → heisO ψ S T (e • z) f = f := fun e he =>
    hf.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P e (GlobalTheory.SplitHomLattice.idem_int he) z hz)
      (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
  have hQ := finite_two (D := D) P
  have hmemQ : ∀ v, v ∈ hQ.toFinset ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal := fun v => hQ.mem_toFinset
  have hch : ∀ v, v ∈ hQ.toFinset → ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
    intro v hv
    obtain ⟨hPv, h2⟩ := (hmemQ v).1 hv
    rcases (hT v hPv).2 with h | h
    · exact absurd h2 h
    · exact h
  choose! e ε he hε hsum using hch
  have hdec := indicatorIdempotent_eq_add_sum P hQ.toFinset hmemQ ε hε
  have hzc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP P) • z = z := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul P _ (LatMem.latO_mxAt hz i j)

  rw [← hzc, hdec, map_add (f := _), map_sum]
  refine fix_add hiso ?_ ?_
  · have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P _ (int_alg_pair (halfOff_int P)) z hz
    have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P + halfOff P)) • z =
        2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P)) • z) := by
      rw [pair_add, map_add (f := _), add_smul, two_nsmul]
    rw [e2]
    exact hf.1 _ hm
  · refine Finset.sum_induction _ (fun c => heisO ψ S T (c • z) f = f) (fun a b ha hb => fix_add hiso ha hb) ?_ ?_
    · rw [zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
    · intro v hv
      rw [← hsum v hv]
      exact fix_add hiso (hfix_split _ (he v hv)) (hfix_split _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (he v hv)))

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW


theorem scalar_diag_mod_g : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  intro D X u β hβ c hc hN
  have hg1 : 1 ≤ X.B.g := Formalism.L2.SG.PoincareInHH.Cut.one_le_g X
  obtain ⟨M6, hM6, hz6⟩ := GlobalTheory.T.exists_coprime_multiplier_one_sub_norm_congr_zero D X u
  have hTg : Nat.Coprime (D.mem u).A.T X.B.g := GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level X.B.I X.B.g _ M6 hg1 hM6 hz6
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  obtain ⟨Mb, hMb, hb7⟩ := GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference D X
  obtain ⟨Mc, hMc, hc7⟩ := GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near D X u
  have hc' : c.1 * sigA X.B.I c.1 = 1 := by
    have := congrArg Subtype.val hc
    simpa [sigInt_coe] using this
  obtain ⟨hfix, hfz, hidem⟩ := GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent D X u
  obtain ⟨h, hh, hhi⟩ := GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent X.B.I (GlobalTheory.ScalW.prjM X u) c.1
    (fun y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, hidem])
    (fun x y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint]) hc'
  have hh' : X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c.1 := hh
  have hhi' : X.B.I.fmat h⁻¹ = GlobalTheory.ScalW.hMat X u (sigA X.B.I c.1) := hhi
  obtain ⟨hH, hcomm⟩ := GlobalTheory.T.scalarBlend_projection_mem_stabilizer_and_commutes D X u c.1 h hfix hfz hh'
  obtain ⟨hP0, hfl⟩ := GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level D X

  set P' : VA X.B.I → VA X.B.I := fun y => X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y)
    with hP'
  set M := Mb * Mc * M6 * (D.mem u).A.T with hMdef
  have hMg : Nat.Coprime M X.B.g := by
    simp only [hMdef, Nat.coprime_mul_iff_left]
    exact ⟨⟨⟨hMb, hMc⟩, hM6⟩, hTg⟩
  have smulL : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ X.B.I.Lf → s • y ∈ X.B.I.Lf := fun hs _ hy => X.B.I.Lf.smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have smulM : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ mL X.B.I X.B.g → s • y ∈ mL X.B.I X.B.g := fun hs _ hy => (mL X.B.I X.B.g).smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have hnear : ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro y hy
    rw [hP']
    beta_reduce
    rw [GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq]
    simp only [GlobalTheory.ScalW.prj0]
    have hA1 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) -
        ∑ a, hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).1
    have hA2 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) -
        ∑ a, hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).2
    have hZ := hc7 y hy
    have hw0 : hA X.B.I X.z0 y • X.z0 ∈ X.B.I.Lf :=
      X.B.I.Lf.smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int X.vectorsInLattice.2.1 hy⟩ : IntAf X.B.I.F X.B.I.E) X.vectorsInLattice.2.1
    have hW : ((M6 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) •
        (hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X hz6 hw0
    have hTd : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
        divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) =
        hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y := Formalism.L2.SG.Pf.unitaryCongruence.gmul_divN X.B.I _ hT0 _
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) = S1 at hA1 ⊢
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) = S2 at hA2 ⊢
    generalize (∑ a, hA X.B.I (X.f0 a) y • X.e0 a) = S3 at hA1 ⊢
    generalize (∑ a, hA X.B.I (X.e0 a) y • X.f0 a) = S4 at hA2 ⊢
    generalize X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u = z' at hZ hTd ⊢
    generalize divN X.B.I (D.mem u).A.T (hA X.B.I z' y) = dd at hTd ⊢
    generalize hA X.B.I X.z0 y • X.z0 = w0 at hZ hW ⊢
    rw [← hTd] at hZ
    rw [hMdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, GlobalTheory.ScalW.scalW_ident]
    have hN' : ∀ m : ℕ, (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E := fun m => natCast_mem _ m
    exact sub_mem (sub_mem (add_mem (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA1)
      (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA2)) (smulM (mul_mem (hN' _) (hN' _)) hZ))
      (smulM (mul_mem (hN' _) (hN' _)) hW)
  have key : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, ZMod' X.B.I M (1 - s) → ∀ y ∈ X.B.I.Lf,
      (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro s hzs y hy
    obtain ⟨t, ht, e⟩ := hzs
    rw [e, mul_comm, mul_smul]
    exact smulM ht (hnear y hy)
  have hint : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, s ∈ IntAf X.B.I.F X.B.I.E → ZMod' X.B.I M (1 - s) →
      ∀ y ∈ X.B.I.Lf, s • y + (1 - s) • P' y ∈ X.B.I.Lf := by
    intro s hs hzs y hy
    have e : s • y + (1 - s) • P' y = s • y + (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) + (1 - s) • GlobalTheory.ScalW.prj0 X y := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (add_mem (smulL hs hy) (GlobalTheory.St.G.FrameClose.mL_le _ (key s hzs y hy)))
      (smulL (sub_mem (one_mem _) hs) (hP0 y hy))
  have hact : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.Gf), X.B.I.fmat k = GlobalTheory.ScalW.hMat X u s →
      ∀ y, X.B.I.fmat ((X.xu u)⁻¹ * k * X.xu u) *ᵥ y = s • y + (1 - s) • P' y := by
    intro s k hk y
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hk,
      GlobalTheory.ScalW.hMat_mulVec, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec,
      Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul, one_mulVec]
  have hcM : ZMod' X.B.I M (1 - c.1) := hN M hMg
  have hsM : ZMod' X.B.I M (1 - sigA X.B.I c.1) := by
    have := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I M hcM
    rwa [map_sub, map_one] at this
  have hinvY : ((X.xu u)⁻¹ * h * X.xu u)⁻¹ = (X.xu u)⁻¹ * h⁻¹ * X.xu u := by group
  set d : Fin X.B.I.n → Formalism.L2.Herm.intAf X.B.I.F X.B.I.E :=
    fun i => if D.R.rS ≤ i.val ∧ i.val < D.R.rS + D.R.k then c else 1 with hd
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.frame_matrix_diagonal_mod_level_of_diagonal_action X.B.I X.B.g _ β ((X.xu u)⁻¹ * h * X.xu u) d hβ
    (fun y hy => by rw [hact _ h hh']; exact hint _ c.2 hcM y hy)
    (fun y hy => by
      rw [hinvY, hact _ _ hhi']
      exact hint _ (Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem X.B.I c.2) hsM y hy)
    (fun j => by
      obtain ⟨hbL, hW, hnW⟩ := hfl j.val
      rw [hact _ h hh']
      have hk := key c.1 hcM _ hbL
      by_cases hj : D.R.rS ≤ j.val ∧ j.val < D.R.rS + D.R.k
      · have e1 : (d j).1 = c.1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          rw [smul_sub]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hW hj))
      · have e1 : (d j).1 = 1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • (GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hnW hj)))
  refine ⟨h, hH, hcomm, x, hx1, fun i j => ?_⟩
  have e : midDiag X.B.I.n D.R.rS D.R.k 1 c = Matrix.diagonal d := by
    simp only [midDiag, hd]
  rw [e]
  exact hx2 i j

end GlobalTheory.ScalW
end
end
