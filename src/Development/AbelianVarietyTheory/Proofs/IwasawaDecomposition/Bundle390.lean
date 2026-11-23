module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle366
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle335
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.HermitianForms.Bundle008
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.Columns.TiedValBwG
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle002
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle365
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle348
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle368
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.twistedSourceValue_read_in_changed_bases : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z))
    (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs →
    (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) →
    ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m)
    (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY →
    ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ)
    (P0 : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N i) × Fin ((I.rec7 l Z).R.N i)) ℂ),
    (∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P0 (eY z)) →
    ∀ (R0 : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N i) × Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL),
    MvPolynomial.map (I.rec7 l Z).what₂.embLL R0 = P0 →
    ∀ (k : (I.rec7 l Z).what₂.Tau → ℕ),
    (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) →
    ∀ (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)
    (g : (I.rec7 l Z).what₂.Tau → Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) ℂ_[(I.rec7 l Z).what₂.places.resChar w]),
    (∀ τ, Bs u μ w i c τ = (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) * g τ) →
    ∀ v : ValQ O u μ i, evC O u μ i v = f →
    srcFun Pl Bs u μ w i c (secC O u μ i v) = fun y =>
      (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) * ((∏ τ, (g τ * y τ).det ^ k τ) *
        polFun (MvPolynomial.map (Pl.iL w) (twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0))
          (fun τ => g τ * y τ)) := by
  first | exact @GlobalTheory.Mem.SrcFunRead.srcFun_secC_read | exact GlobalTheory.Mem.SrcFunRead.srcFun_secC_read | (intros; apply GlobalTheory.Mem.SrcFunRead.srcFun_secC_read <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SymChar.CharProd
open Classical

theorem wInt_le {D : D7} (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ GlobalTheory.Mem.SymChar.wInt X w) :
    c ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    exact Formalism.L2.SG.Pf.unitaryCongruence.inclE_mem X.B.I ⟨a, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact mul_mem c.2 hx

theorem addChar_sum {ι A M : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι)
    (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

instance neZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def cK (D : D7) (k : Fin 2) : ZMod (D.host.g k) := ((D.host.g (k + 1) : ℕ) : ZMod (D.host.g k))⁻¹

def psiK (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  (ZMod.stdAddChar (N := D.host.g k)).mulShift (cK D k)

theorem cK_ne_zero (D : D7) (k : Fin 2) : cK D k ≠ 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  unfold cK
  refine inv_ne_zero ?_
  rw [Ne, CharP.cast_eq_zero_iff (ZMod (D.host.g k)) (D.host.g k)]
  intro hd
  have h := (Nat.prime_dvd_prime_iff_eq (D.host.g_prime k) (D.host.g_prime (k + 1))).1 hd
  have hne := D.host.g_ne
  fin_cases k
  · exact hne h
  · exact hne h.symm

theorem psiK_ne_one (D : D7) (k : Fin 2) : psiK D k ≠ 1 :=
  ZMod.isPrimitive_stdAddChar _ (cK_ne_zero D k)

theorem psiEf_conj_eq_prod : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ, (∀ kv, ψ' kv ≠ 1) ∧ ∀ (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t u : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1)), (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) s (t kv)) → (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I s) (u kv)) → star (X.psiEf (divN X.B.I X.B.g s)) = ∏ kv, ψ' kv (t kv + u kv) := by
  intro D X _h _hι hg
  refine ⟨fun kv => psiK D kv.1, fun kv => psiK_ne_one D kv.1, ?_⟩
  intro s t u ht hu
  obtain ⟨_, _, hcard0⟩ := GlobalTheory.T.places_over_typePrime_chosen_and_conj D 0
  obtain ⟨v0⟩ : Nonempty (D.nd.PlG 0) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have h0 : Module.finrank ℚ D.host.E = 0 := by rw [← hcard0]; simp
    exact (Module.finrank_pos (R := ℚ) (M := D.host.E)).ne' h0
  have hs : s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
    have h1 := wInt_le X _ (ht ⟨0, v0⟩)
    have h2 : (((t ⟨0, v0⟩).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      natCast_mem _ _
    simpa using add_mem h1 h2
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor D X s hs
  set a := Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) with ha
  have hg0 : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hstep : X.psiEf (divN X.B.I X.B.g s) = X.psiEf (divN X.B.I X.B.g a) := by
    conv_lhs => rw [show s = a + (s - a) by ring]
    rw [Formalism.L2.SG.Pf.unitaryCongruence.divN_add, X.psiEf_add,
      Formalism.L2.SG.Pf.unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg0 hα, mul_one]
  rw [hstep, GlobalTheory.T.star_finiteAddChar_div_nat_eq_exp_trace D X α]
  have hres : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      α - (((t kv).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal ∧
      α - (((u kv).val : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw kv.1 kv.2)).asIdeal := by
    intro kv
    have hZ : s - a ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) :=
      GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 (hg kv) hα
    constructor
    · apply GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan D X
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm (((α - (((t kv).val : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E)) =
          (s - (((t kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) - (s - a) := by
        rw [ha]; push_cast; rw [map_sub, map_natCast, map_sub, map_natCast]; ring
      rw [e]; exact sub_mem (ht kv) hZ
    · rw [GlobalTheory.IdemSupport.mem_cP, map_sub, map_natCast]
      apply GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan D X
      have hZ' : sigA X.B.I s - sigA X.B.I a ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
        rw [← map_sub]
        exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 (hg kv) (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g hα)
      have hsa : sigA X.B.I a = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm ((GlobalTheory.IdemSupport.cO D α : 𝓞 D.host.E) : D.host.E)) := by
        rw [ha, Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE]
        congr 1
        apply X.ιE.injective
        rw [X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, GlobalTheory.IdemSupport.cO_coe]
        exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm (((GlobalTheory.IdemSupport.cO D α - (((u kv).val : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E)) =
          (sigA X.B.I s - (((u kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) -
            (sigA X.B.I s - sigA X.B.I a) := by
        rw [hsa]; push_cast; rw [map_sub, map_natCast, map_sub, map_natCast]; ring
      rw [e]; exact sub_mem (hu kv) hZ'
  have htr : ∀ k : Fin 2, ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ZMod (D.host.g k)) =
      ∑ v : D.nd.PlG k, (t ⟨k, v⟩ + u ⟨k, v⟩) := by
    intro k
    obtain ⟨hinj, hcov, hcard⟩ := GlobalTheory.T.places_over_typePrime_chosen_and_conj D k
    rw [GlobalTheory.T.intTrace_modEq_sum_residues_split_prime (D.host.g k) (D.host.g_prime k) _ hinj hcov hcard α
      (Sum.elim (fun v => (((t ⟨k, v⟩).val : ℕ) : ℤ)) (fun v => (((u ⟨k, v⟩).val : ℕ) : ℤ))) ?_]
    · rw [Fintype.sum_sum_type, Finset.sum_add_distrib]; simp
    · rintro (v | v)
      · simpa using (hres ⟨k, v⟩).1
      · simpa using (hres ⟨k, v⟩).2
  rw [Fintype.prod_sigma]
  have hk : ∀ k : Fin 2, ∏ v : D.nd.PlG k, psiK D k (t ⟨k, v⟩ + u ⟨k, v⟩) =
      psiK D k ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ZMod (D.host.g k)) := by
    intro k; rw [htr k, addChar_sum]
  simp only [hk, Fin.prod_univ_two]
  simp only [psiK, cK, AddChar.mulShift_apply]
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [X.g_eq]
  exact GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime (D.host.g 0) (D.host.g 1) hcop _

end GlobalTheory.Mem.SymChar.CharProd
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelCharacterAtQ_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  exact @GlobalTheory.Mem.Col2.TopCh.topChi_finite_order_and_trivial
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem toGLm_entry {E : Type} [Field E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    ((toGLm E n f : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = f (Pi.single j 1) i := by
  simp [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem localComponent_eq_frame {hc : CMData F E} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) :
    rhoP F P.1 g = Formalism.UG.bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (p.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [h.fr P i j, toGLm_entry]

theorem rhoT_eq_iota {hc : CMData F E} {k t y x : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : GLG (E := E) (n := n) (SG := SG)) (θ : GLQ E n Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x * (k * t)) (((1, h, θ) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) (P : Q) :
    rhoT F P.1 t x = iotaP P.1 ((θ P)⁻¹) := by
  have e0 : rhoT F P.1 t x = (rhoP F P.1 (y * (k * t)))⁻¹ * rhoP F P.1 (y * x * (k * t)) := by
    rw [← map_inv, ← map_mul, show (y * (k * t))⁻¹ * (y * x * (k * t)) = t⁻¹ * (k⁻¹ * (x * k)) * t by group,
      map_mul, map_mul, map_mul, map_mul, map_inv (rhoP F P.1) k, hk P, inv_one, one_mul, mul_one]
    simp [rhoT]
  rw [e0, localComponent_eq_frame h1 P, localComponent_eq_frame h2 P]
  show _ * Formalism.UG.bc _ (toGLm E n ((1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((θ P)⁻¹).1)) = _
  rw [one_mul, map_mul, map_mul, inv_mul_cancel_left]
  rfl

theorem topChi_eq {K : Type} [Field K] (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E))
    (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ)
    (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (x : topU U t Θ d) (θ : Θ.grp) (hx : ∀ P : Q, rhoT F P.1 t x.1 = iotaP P.1 ((θ.1 P)⁻¹)) :
    topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Θ.chr θ) := by
  have hθ : ∀ P : Q, θ.1 P ∈ (Θ P).H := fun P => θ.2 P (Set.mem_univ P)
  have key : ∀ P : Q, locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ =
      ((Θ P).lam ⟨θ.1 P, hθ P⟩)⁻¹ := by
    intro P
    have mem : iotaP P.1 ((θ.1 P)⁻¹) ∈ locLev P.1 (Θ P) (d P) := hx P ▸ rhoT_mem x.2 P
    have e : (⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ : locLev P.1 (Θ P) (d P)) = ⟨iotaP P.1 ((θ.1 P)⁻¹), mem⟩ := Subtype.ext (hx P)
    rw [e, ← map_inv]
    exact qbChr_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P) (hΘ P)
      ((θ.1 P)⁻¹) (inv_mem (hθ P)) mem
  have ec : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, hθ P⟩ := by
    unfold LevQFam.chr piChar
    exact MonoidHom.finsetProd_apply (M := ↥(Subgroup.pi Set.univ fun P : Q => (Θ P).H)) _ _ _
  unfold topChi
  rw [MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ec, map_prod, ← _root_.inv_inj, inv_inv, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  show Units.map (σ : K →* ℂ) (locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩) = _
  rw [key, map_inv]

theorem chi_eq_of_J0 {K : Type} [Field K] [NeZero n] {hc : CMData F E} (Λ : LevFam E K n SG) (σ : K →+* ℂ)
    {U : Subgroup (GL (Fin n) (AfE F E))} (χ : U →* ℂˣ) {k t : GL (Fin n) (AfE F E)} (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : U) (h : Λ.grp) (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ x = Units.map (σ : K →* ℂ) (Λ.chr h) := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  refine hχ x (t' * ⟨_, hz⟩ * t'⁻¹) h ?_ ?_
  · show t'.1 * ((k * t'.1)⁻¹ * x.1 * (k * t'.1)) * t'.1⁻¹ = _
    group
  · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 ht', hr, one_mul, inv_one, mul_one]

theorem chr_of_J0 {K : Type} [Field K] [NeZero n] (hc : CMData F E) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E)
    (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p))
    (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  rw [chi_eq_of_J0 Λ σ χ ht hχ ⟨x.1, topU_le _ _ _ _ x.2⟩ h hz hr,
    topChi_eq σ U t Θ d hd N hdN hΘ x θ fun P => rhoT_eq_iota h.1 θ.1 hk h1 h2 P, map_mul]

theorem chi_mul_topChi_moved : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ σ U χ k t y p _ hk ht hχ x h θ h1 h2
  have e : y * (k * t) * ((k * t)⁻¹ * x.1 * (k * t)) = y * x.1 * (k * t) := by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * (k * t)) ((k * t)⁻¹ * x.1 * (k * t)) p
    (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) h.1).1 h1 (e ▸ h2)).2 rfl
  exact chr_of_J0 hc Λ Θ d hd N hdN hΘ σ U χ k t y p hk ht hχ x h θ h1 h2 hz hr

end GlobalTheory.Mem.Col2.TopCh

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwLat

open GlobalTheory.Mem.Col2.RowTie

theorem natW_shW' {N : ℕ} (l : DomWeight N) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
  congr 1
  ring

theorem delStd_shW' {K ι : Type} [Field K] [NumberField K] [Fintype ι] {N : ℕ} (lam : ι → DomWeight N) (c : ℤ) :
    delStd K (fun τ => GlobalTheory.Mem.Col2.shW (lam τ) c) = delStd K lam := by
  unfold delStd delSq
  simp only [natW_shW']

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)

theorem locW_lat_iff (hS : S.Ok) {G : ι → Matrix (Fin n) (Fin n) ℂ} {sh : ι → ℤ} (hsh : sh = shiftOf lam) {e : ι → E →+* ℂ}
    (he : e = embAt σ emb) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (w : Pl.Pl)
    (Sp : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ))
    (hSp : ∀ Q, Q ∈ Sp ↔ ∃ z₀ ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam), Q = MvPolynomial.map σ z₀)
    (lat : S.Cl → Submodule (𝓞 E) (Fin n → E)) (hlat : ∀ c, S.Lsh c.1 (S.rep c) = lat c)
    (hspan : ∀ c, Submodule.span E (lat c : Set (Fin n → E)) = ⊤) (x : (S.hlat emb lam h).V) :
    x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (lat c : Set _) B →
      ∃ Q ∈ Sp, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G sh (Formalism.L2.Forms.atInf e (B⁻¹ : GL (Fin n) E).1) Q := by
  subst hsh he
  have hL : ∀ c, Submodule.IsLattice E (lat c) := fun c => hlat c ▸ hS.lsh_lat c.1 _
  have hfull : ∀ c, Submodule.IsFullLattice E (lat c) := fun c =>
    { toIsLattice := hL c, span_eq_top := hspan c }
  have key : ∀ (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (lat c : Set _) B →
      (x.1 c ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam (lat c)) ↔
      ∃ Q ∈ Sp, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G (shiftOf lam) (Formalism.L2.Forms.atInf (embAt σ emb) (B⁻¹ : GL (Fin n) E).1) Q) := by
    intro c B hB
    refine (BwLat.mem_localization_delAtr_fn emb σ lam (pw w) (by first | exact hfull c | exact (hfull c).toIsLattice) (fun _ => B) (fun τ => BwLat.isBasisAt_of_isLocBasis
      (Pl.resChar_prime w) _ ((bc_mem_below _ _ _).2 (by rw [map_natCast]; exact Formalism.L2.Col.vl_resChar_mem Pl pw hval w)) hB)
      (x.1 c)).trans ⟨?_, ?_⟩
    · rintro ⟨z, hz, e⟩
      exact ⟨_, (hSp _).2 ⟨z, hz, rfl⟩, e⟩
    · rintro ⟨Q, hQ, e⟩
      obtain ⟨z, hz, rfl⟩ := (hSp Q).1 hQ
      exact ⟨z, hz, e⟩
  rw [GlobalTheory.Mem.Col2.mem_locW_hlat_iff emb Pl pw hval S lam h hS w x]
  simp only [hlat]
  unfold locW
  simp only [Formalism.L2.Col.vl_mem_span_intW_iff Pl pw hval w]
  refine ⟨fun H c B hB => (key c B hB).1 (H c), fun H c => ?_⟩
  haveI : Fact (Pl.resChar w).Prime := ⟨Pl.resChar_prime w⟩
  obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E _ (hL c).fg (hspan c)
  exact (key c B hB).2 (H c B hB)

end Gen

end GlobalTheory.Mem.Col2.TwLat

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.Col2.RowTie GlobalTheory.Mem.Col2.TwLat


set_option backward.isDefEq.respectTransparency false in

theorem tw_lat_at : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ w, Formalism.L2.Forms.okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T w → ∀ x : (I.fm l u a).ptLat.V, x ∈ (I.fm l u a).SP w ↔ ∀ (c : (I.fm l u a).clsP) (Bm : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E), IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (K.lat c : Set _) Bm → ∃ Pc ∈ IntSpan (I.rec7 l Z) w (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a ((I.fm l u a).ptEmb x) c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E).1) Pc := by
  intro B X I hI hP l Z u a Q K hQ hQT hK w hw x
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = sgTG (D := I.rec7 l Z) (I.fm l u a) := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg.symm
  have hS : (I.stX a).Ok := (l.per u a).step
  exact locW_lat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP hS hsh hemb
    (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w (IntSpan (I.rec7 l Z) w B.wts.sgW)
    (fun Q => by
      have h := GlobalTheory.LvT.Built.ValLat.mem_closure_iff B.embLL ((I.rec7 l Z).plEq w) (intW (I.rec7 l Z).what₂.places w)
        ((I.rec7 l Z).val_nonneg_iff w) B.wts.sgW Q
      rw [← delStd_shW' B.wts.sgW (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))] at h
      exact h)
    K.lat (fun c => (RowTie.Lsh_empty _).trans (hK.lat c).symm) (fun c => by
      have hG := Formalism.UG.P.csGlob_lattice (F := (I.rec7 l Z).host.F) K.lev.Lb K.lev.Lb_fin K.lev.Lb_span (K.y c).1
      rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
      intro z hz
      exact Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span (F := (I.rec7 l Z).host.F) _ z ((K.y_lat c _).2 hz)) x

end GlobalTheory.Mem.Col2.TC

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.couplingCosetInFrames_eq_iff_reduction_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  exact @GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt | exact GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | exact GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec <;> assumption)
end
