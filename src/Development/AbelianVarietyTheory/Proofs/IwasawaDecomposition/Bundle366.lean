module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_row {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (K U : Fin n → P.adicCompletion E)
    {c s : 𝓞 E ⧸ P.asIdeal} (hK : ∀ j, HasRes P (K j) (if j = r then c else 0)) (hU : ∀ j, Valued.v (U j) ≤ 1)
    (hs : HasRes P (U r) s) : HasRes P (∑ j, K j * U j) (c * s) := by
  obtain ⟨s, rfl, hs⟩ := hs
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, DilPt.hasRes_mk_iff]
  have hC : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : (∑ j, K j * U j) - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (c * s)) =
      ∑ j, (K j - if j = r then algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) else 0) * U j +
        algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) *
          (U r - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_) ?_
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' (hU j)) ?_
    have := hK j
    by_cases hj : j = r
    · rw [if_pos hj, DilPt.hasRes_mk_iff] at this
      rwa [if_pos hj]
    · rw [if_neg hj] at this
      rw [if_neg hj, sub_zero]
      exact DilPt.hasRes_lt_one this
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hC) hs

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoSet_ext {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (hN : d.1.N = d'.1.N) (hf : ∀ P, ∀ x ∈ d'.1.N, d.1.f P x = d'.1.f P x)
    (hbe : ∀ w, ∀ x ∈ d'.1.N, d.1.be w x = d'.1.be w x) : d = d' := by
  have hat : ∀ P, d.1.at P = d'.1.at P := fun P => by unfold Deco.at; rw [hN]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E), s ∉ P.asIdeal → Ideal.Quotient.mk P.asIdeal s ≠ 0 :=
    fun P s hs h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  refine Subtype.ext (Deco.ext hN (funext fun P => funext fun x => ?_) (funext fun P => funext fun x => ?_))
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hf P _ h
      rw [d.2.f_smul P s x (hat _ ▸ hx), d'.2.f_smul P s x hx] at this
      have hp := P.1.isPrime
      exact mul_left_cancel₀ (h0 _ s hs) this
    · rw [d.2.f_off P x (hat _ ▸ hx), d'.2.f_off P x hx]
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hbe P _ h
      rw [d.2.be_smul P s x (hat _ ▸ hx), d'.2.be_smul P s x hx] at this
      have hp := P.1.isPrime
      funext i
      exact mul_left_cancel₀ (h0 _ s hs) (congrFun this i)
    · rw [d.2.be_off P x (hat _ ▸ hx), d'.2.be_off P x hx]

theorem decoOf_dia_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG (E := E) (ST := ST)), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = Formalism.L2.Col.stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g k p c h ⟨p₀, hk, hk0⟩ htriv hrow
  classical
  have hg : g ∈ UAd hc n := by
    have := mul_mem h.uni (inv_mem hk.uni)
    rw [mul_inv_cancel_right] at this
    exact this
  have hkc := hk.lat
  rw [hk0] at hkc
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
    let L := p.deco.1.N
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let f : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) hspan]
    ext w
    refine (mem_globLat g w).trans ((hkI _).trans ?_)
    have e : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Formalism.L2.Col.pullV g w =
        GlobalTheory.Mem.Col2.pullV (g * k) w := (DilPt.pullbackVector_mul_right g k w).symm
    rw [e]
    refine (mem_latS_std _).symm.trans ((h.lat _).symm.trans ?_)
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hone : ∀ w ∈ SG, ∀ i j, adAt F w ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if j = i then 1 else 0 := by
    intro w hw i j
    have h1 : bc (prV (E := E) (w.under (𝓞 F))) k⁻¹ = 1 := by rw [map_inv, htriv w hw, inv_one]
    have h2 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0 := by
      have := congrArg (fun x : GL (Fin n) _ => x.1 i j) h1
      simp only [Units.val_one, Matrix.one_apply] at this
      exact this
    have h3 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j - if j = i then 1 else 0) = 0 := by
      rw [map_sub, h2]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h3 w rfl
    rw [map_sub, sub_eq_zero] at h4
    rw [h4]
    split_ifs <;> simp
  have hraw := rlc_decoOf_val hc n ST SG hg
  have hint : ∀ x ∈ p.deco.1.N, ∀ i, GlobalTheory.Mem.Col2.pullV g x i ∈ RInt F E := fun x hx =>
    (mem_globLat g x).1 (hN ▸ hx)
  refine ⟨hg, decoSet_ext ?_ (fun P x hx => ?_) fun w x hx => ?_⟩
  · show (decoOf ST SG g).1.N = _
    rw [hraw]
    exact hN
  · show (c P).1 * (decoOf ST SG g).1.f P x = _
    have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
    have h1 := h.f P x hx _ hl
    rw [DilPt.pullbackVector_mul_right] at h1

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1
    have h2 := hasRes_row (lastIdx n) _ (fun j => adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x j)) (fun j => hrow P _ j hl)
      (fun j => (mem_rInt_iff F E _).1 (hint x hx j) P.1) (PtExist.hasRes_redA P.1 (hint x hx _))
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    exact h2.unique h1
  · show (decoOf ST SG g).1.be w x = _
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    funext i
    have h1 := h.be w x hx i
    rw [DilPt.pullbackVector_mul_right] at h1

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hone w.1 w.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
    exact (PtExist.hasRes_redA w.1 (hint x hx i)).unique h1

end GlobalTheory.Mem.Col2.DiaPt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.Mem.SrcFunRead

open MvPolynomial

theorem map_twSubK_field {E K K' ι : Type} [Field E] [Field K] [Field K'] [Fintype ι] {n : ℕ} (t : ι → E →+* K)
    (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K) (φ : K →+* K') :
    map φ (twSubK t M s P) = twSubK (fun τ => φ.comp (t τ)) M s (map φ P) := by
  simp only [twSubK, map_mul, map_C, map_prod, map_zpow₀, RingHom.comp_apply]
  congr 1
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, MvPolynomial.bind₁_X_right]

theorem eq_of_eval_invertible {LL ι : Type} [Field LL] [Fintype ι] {n : ℕ} (e : LL →+* ℂ)
    {A B : MvPolynomial (ι × Fin n × Fin n) LL}
    (h : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ).det ≠ 0) →
      eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (map e A) =
        eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (map e B)) : A = B := by
  classical
  let d : MvPolynomial (ι × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hd : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) d = ∏ τ, (y τ).det := by
    intro y
    simp only [d, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 := hd (fun _ => 1)
    rw [h0] at h1
    simp at h1
  have hm : d * map e A = d * map e B := by
    apply MvPolynomial.funext
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : ι → Matrix (Fin n) (Fin n) ℂ, x = fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2 :=
      ⟨fun τ a b => x (τ, a, b), rfl⟩
    rw [eval_mul, eval_mul, hd]
    by_cases hy : ∀ τ, (y τ).det ≠ 0
    · rw [h _ hy]
    · push_neg at hy
      obtain ⟨τ, hτ⟩ := hy
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul, zero_mul]
  exact MvPolynomial.map_injective e e.injective (mul_left_cancel₀ hd0 hm)

end GlobalTheory.Mem.SrcFunRead

namespace GlobalTheory.Mem.SrcFunRead
open MvPolynomial

theorem srcFun_secC_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
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
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hId c f P0 hf R0 hR0 k hk Bm g hBs v hv

  have hPI : (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL) *
      ∏ τ, frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ ^ (((I.rec7 l Z).chTw u μ).sSharp i τ - twB (I.rec7 l Z) u μ i τ).toNat =
      R0 * ∏ τ, frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ ^ k τ := by
    apply eq_of_eval_invertible (I.rec7 l Z).what₂.embLL
    intro y hy
    obtain ⟨z, hz⟩ : ∃ z : (I.chain l u μ).Y i, z.1 = y := by
      refine ⟨eY.symm ⟨y, fun τ => isUnit_iff_ne_zero.2 (hy τ)⟩, ?_⟩
      have h2 := hId (eY.symm ⟨y, fun τ => isUnit_iff_ne_zero.2 (hy τ)⟩)
      exact h2.symm.trans (congrArg Subtype.val (eY.apply_symm_apply _))
    have h1 : evP O u μ i (secC O u μ i v) z = f z :=
      (congrFun (evC_sec O u μ i v) z).symm.trans (congrFun hv z)
    rw [hf z] at h1
    have hfr : (O u μ).frm i z = y := (hStd.frm u μ i z).trans hz
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de i z τ = (y τ).det := fun τ =>
      ((O u μ).frm_de i hi.le z τ).trans (congrArg (fun M => (M τ).det) hfr)
    have hez : (eY z).1 = y := (hId z).trans hz
    simp only [evP, LinearMap.coe_mk, AddHom.coe_mk, fnOf, GL3Theta.evFr, hfr, hde, hez, Matrix.one_mul, Pi.one_apply] at h1
    rw [← hR0] at h1
    simp only [map_mul, map_prod, map_pow, eval_mul, eval_prod, eval_pow, eval_detP (D := I.rec7 l Z)]
    have e1 : ∀ τ, (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ - twB (I.rec7 l Z) u μ i τ).toNat =
        (y τ).det ^ (-twB (I.rec7 l Z) u μ i τ) * (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ) := by
      intro τ
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (twLe (I.rec7 l Z) u μ i hi τ)), ← zpow_add₀ (hy τ)]
      congr 1
      ring
    have e2 : ∀ τ, (y τ).det ^ k τ =
        (y τ).det ^ shiftOf (lamTG (I.fm l u μ) i) τ * (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ) := by
      intro τ
      rw [← zpow_natCast, hk τ, zpow_add₀ (hy τ)]
    simp only [e1, e2, Finset.prod_mul_distrib]
    linear_combination (∏ τ, (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ)) * h1
  funext y
  simp only [srcFun, atBas, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.mulRight_apply, Submodule.coe_subtype, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [hPI]
  have hφ : ∀ τ x, ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) x = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
    intro τ x
    have hx : (I.rec7 l Z).what₂.embLL (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ x) ∈ algebraicClosure ℚ ℂ := embLL_alg w _
    have he := Formalism.L2.G.Cmp.tEL_emb (I.rec7 l Z) τ x
    rw [RingHom.comp_apply, Pl.iL_lam' w _ hx]
    unfold TaylorLogMetric.tauEmb TaylorLogMetric.lamC
    rw [dite_eq_left (he ▸ hx)]
    exact congrArg (Pl.lam w) (Subtype.ext he)
  have hA : ∀ τ, (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) =
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) := fun τ => by
    ext a b
    exact (hφ τ _).symm
  have hdetA : ∀ τ, ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))).det =
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det :=
    fun τ => (RingHom.map_det _ _).symm
  have ha : ∀ τ, ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ≠ 0 :=
    fun τ => ((Matrix.isUnits_det_units Bm).map _).ne_zero
  simp only [hBs, hA]
  rw [map_twSubK_field, polFun_apply, eval_twSubK _ _ _ _ (fun τ => g τ * y τ)]
  simp only [map_mul, map_prod, map_pow, eval_mul, eval_prod, eval_pow, eval_detP (D := I.rec7 l Z),
    Matrix.mul_assoc, Matrix.det_mul, hdetA]
  have hev : ∀ τ, eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) =>
      ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) k.1)) * (g k.1 * y k.1)) k.2.1 k.2.2)
      (MvPolynomial.map (Pl.iL w) (frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ)) =
      ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) * (g τ * y τ)).det :=
    fun τ => eval_detP (D := I.rec7 l Z) (Pl.iL w) (fun t =>
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) t)) * (g t * y t)) τ
  simp only [hev, Matrix.det_mul, hdetA]
  have hper : ∀ τ, (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
        (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det * (g τ).det) ^
          (-((I.rec7 l Z).chTw u μ).sSharp i τ) *
      (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
        (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det *
          ((g τ).det * (y τ).det)) ^ k τ =
      ((g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) * ((g τ).det * (y τ).det) ^ k τ) *
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
          (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ^
            shiftOf (lamTG (I.fm l u μ) i) τ := by
    intro τ
    have h0 := ha τ
    rw [mul_zpow, mul_pow, ← zpow_natCast (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det), hk τ,
      zpow_add₀ h0, _root_.zpow_neg]
    have h1 : ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ^
        (((I.rec7 l Z).chTw u μ).sSharp i τ) ≠ 0 := zpow_ne_zero _ h0
    field_simp
  rw [mul_left_comm, ← mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun τ _ => hper τ,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.Mem.SrcFunRead
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitian_e0_symmetric_frame : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.hA_e0_symVec | exact GlobalTheory.Mem.SymChar.hA_e0_symVec | (intros; apply GlobalTheory.Mem.SymChar.hA_e0_symVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conj_idempotent_sub_one_mem_placeIdeal : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt | exact GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianForm_middle_symmetricFrame_not_oneAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt | exact GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E), Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w → α ∈ w.asIdeal := by
  first | exact @GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt | exact GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.symEdge_conjWeighted_sum_eq_flag_and_unipotent_pairs : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq | exact GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq | (intros; apply GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  first | exact @GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | exact GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | (intros; apply GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitian_z0_symmetric_frame : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec | exact GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec | (intros; apply GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec <;> assumption)
end
