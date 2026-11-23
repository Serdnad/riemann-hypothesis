module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
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
public import Mathlib.NumberTheory.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FilStable

theorem ι_σB {l : ℕ} [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (g : Per.Gq l) (β : Per.Bcris l) :
    C.ι (Per.σB g β) = Per.σD g (C.ι β) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := C.ι.comp (Per.σB g)) (g := (Per.σD g).comp C.ι) fun x => ?_) β
  have h1 : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (GlobalTheory.MemLoc.sigA g x) :=
    GlobalTheory.CrisMaps.σB_sigA g x
  change C.ι (Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x)) =
    Per.σD g (C.ι (algebraMap (Per.Acris l) (Per.Bcris l) x))
  rw [h1, C.ι_j, C.ι_j, GlobalTheory.MemLoc.FilLaws.σD_alg, GlobalTheory.MemLoc.CrisUnique.equivariant C.j_cris]

theorem fil_zero_stable : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (C : GlobalTheory.MemLoc.Core l), ∀ v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}, actB (sQ l) T g v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g C v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨β, x, hβ, rfl⟩ := hw
    refine Submodule.subset_span ⟨Per.σB (sQ l g) β, T.actT g x, ?_, ?_⟩
    rotate_left 1
    · simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, galOB,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    · rw [ι_σB]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.1 _ 0 _ hβ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BKGal.FilStable
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem theta_algebraMap_inj {z z' : ℤ_[l]}
    (h : Per.θ l (algebraMap ℤ_[l] (Ainf l) z) = Per.θ l (algebraMap ℤ_[l] (Ainf l) z')) : z = z' := by
  have h1 := GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z
  have h2 := GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z'
  have h3 : (algebraMap ℚ_[l] ℂ_[l]) (z : ℚ_[l]) = (algebraMap ℚ_[l] ℂ_[l]) (z' : ℚ_[l]) := by
    rw [← h1, ← h2]
    exact congrArg Subtype.val h
  exact PadicInt.ext ((algebraMap ℚ_[l] ℂ_[l]).injective h3)

theorem one_tmul_injective (LL : FinExt l) {y y' : Ainf l}
    (h : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] y = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] y') : y = y' := by
  have hA : Function.Injective (algebraMap ℤ_[l] (Ainf l)) := fun z z' hz =>
    theta_algebraMap_inj (congrArg (Per.θ l) hz)
  have : Module.IsTorsionFree ℤ_[l] (Ainf l) := Module.isTorsionFree_iff_algebraMap_injective.2 hA
  have hO : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := fun z z' hz => by
    refine theta_algebraMap_inj ?_
    rw [← intToOC_algebraMap, ← intToOC_algebraMap, hz]
  exact Algebra.TensorProduct.includeRight_injective (R := ℤ_[l]) (A := ↥(OL LL)) (B := Ainf l) hO h

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem ratio_pow {e : ℕ} (ϖ : PiSys l e) (g : GQ l) (n m : ℕ) : ϖ.ratio g (n + m) ^ l ^ m = ϖ.ratio g n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, ← add_assoc, ϖ.ratio_succ, ih]

theorem seq_fixed {e : ℕ} [NeZero e] (ϖ : PiSys l e) {g : GQ l} (hg : ϖ.kummer g = 1) (n : ℕ) :
    g (ϖ.seq n) = ϖ.seq n := by
  have hd : ∀ j, ((l : ℕ) : OC l) ∣ ϖ.ratio g j - 1 := fun j => by
    have h1 := ϖ.coeff_kummer g j
    rw [hg, map_one] at h1
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_one, ← h1]
  have hr : ϖ.ratio g n = 1 := by
    rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {((l : ℕ) : OC l)})]
    intro m
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rcases m with _ | m
    · simp
    · have := dvd_sub_pow_of_dvd_sub (hd (n + m)) m
      rwa [ratio_pow, one_pow] at this
  have h2 := congrArg Subtype.val hr
  rw [PiSys.coe_ratio, OneMemClass.coe_one, ← map_one (algebraMap (Om l) ℂ_[l])] at h2
  exact (div_eq_one_iff_eq (ϖ.seq_ne_zero n)).1 ((algebraMap (Om l) ℂ_[l]).injective h2)

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem unr_fixed (a : ℕ) [NeZero a] {g : GQ l} (hg : ∀ w, Per.σA g (wA l a w) = wA l a w) {x : Om l}
    (hx : x ^ l ^ a = x) : g x = x := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := congrArg (fun y => ((Per.θ l y : OC l) : ℂ_[l])) (hg (WittVector.teichmuller l z))
  simp only [GlobalTheory.RingBasics.θ_σA, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
  have h2 : Per.σC g (ω : ℂ_[l]) = (ω : ℂ_[l]) := by
    rw [← GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    exact (GlobalTheory.RingIface.sigO_coe l g _).symm.trans h1
  rw [GlobalTheory.RingBasics.σC_coe] at h2
  have hω' : g ω = ω := UniformSpace.Completion.coe_injective _ h2
  rcases eq_or_ne x 0 with rfl | h0
  · exact map_zero g
  have h3 := one_lt_pow_l l a
  have h4 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, hx, one_mul])
  have : NeZero (l ^ a - 1) := ⟨by omega⟩
  obtain ⟨i, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h4
  rw [map_pow, hω']

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l), Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) → k ∈ ϖ.GfieldInf a := by
  intro l _ a e _ _ ϖ LL _ _ k hc
  have hfix : ∀ f, galOA ↥(OL LL) k (ϖ.iTot (thetaW a LL) ↥LL.1 f) = ϖ.iTot (thetaW a LL) ↥LL.1 f :=
    fun f => hc f f fun τ => by rw [map_one]; rfl
  have hev : ∀ x, Per.σA k (ϖ.ev a x) = ϖ.ev a x := fun x => by
    have h := hfix (toAc (thetaW a LL) ↥LL.1 x)
    rw [PiSys.iTot_toAc, galOA_tmul] at h
    exact one_tmul_injective LL h
  have hteich : Per.σA k ϖ.teich = ϖ.teich := by simpa using hev X
  have h0 : ϖ.teich ≠ 0 := fun h => ϖ.flat_ne_zero (by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa [PiSys.teich] using this)
  have hkum : ϖ.kummer k = 1 := by
    rw [PiSys.gal_teich, PiSys.mu, add_sub_cancel] at hteich
    have h1 := mul_right_cancel₀ h0 (hteich.trans (one_mul _).symm)
    have h2 := congrArg (fun w : Ainf l => w.coeff 0) h1
    simpa using h2
  have hseq := seq_fixed ϖ hkum
  have hw : ∀ w, Per.σA k (wA l a w) = wA l a w := fun w => by simpa using hev (C w)
  have hz : ∀ x, k x = x → x ∈ IntermediateField.fixedField (Subgroup.zpowers k) := fun x hx => by
    rintro ⟨_, m, rfl⟩
    exact MulAction.mem_fixedBy_zpow (α := Om l) (g := k) (a := x) hx m
  rw [PiSys.GfieldInf, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => hz x (unr_fixed a hw hx)
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact hz _ (hseq 0)
  · exact IntermediateField.adjoin_le_iff.2 fun x ⟨n, hn⟩ => hn ▸ hz _ (hseq n)

end GlobalTheory.CoverOne
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverBridge

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem galF_val {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (z : Fq l a) :
    Per.σF k (Fq.val l a z) = Fq.val l a z ^ l ^ s := by
  obtain ⟨z₀, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hω' : k ω = ω ^ l ^ s := hk ω (by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  have h2 : Per.σF k (Fq.val l a z₀) = Fq.val l a z₀ ^ l ^ s := by
    refine GlobalTheory.UnramIdem.tilt_pow (k := l ^ s) hd dvd_rfl hz fun n => ?_
    obtain ⟨y, y1, y2, y3⟩ := hz n
    refine ⟨Per.σO k y, ?_, by rw [← map_pow, y2, map_one], ?_⟩
    · rw [GlobalTheory.RingIface.sigO_coe l, ← map_pow, y1, GlobalTheory.RingBasics.σC_coe, hω']
    · exact GlobalTheory.AdicMaps.coeff_galois l k _ n y y3
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, map_zero, map_zero, zero_pow (pow_pos hl.out.pos s).ne']
  · obtain ⟨j, rfl⟩ := h z h0
    rw [map_pow, map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem galA_wA {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (w : Wq l a) :
    Per.σA k (wA l a w) = wA l a ((sigma l a ^ s) w) := by
  refine WittVector.ext fun n => ?_
  refine (GlobalTheory.RingIface.sigA_coeff l k _ n).trans ?_
  change Per.σF k (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ s) w).coeff n)
  rw [coeff_sigma_pow, map_pow, galF_val hk]

variable {e : ℕ} [NeZero e]

theorem isTiltOf_kummer (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) : IsTiltOf ζ e (ϖ.kummer k) := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  intro n
  refine ⟨ϖ.ratio k n, ?_, ?_, ϖ.coeff_kummer k n⟩
  · rw [PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_pow, hζ,
      mul_div_cancel_right₀ _ (ϖ.seq_ne_zero 0)]
    rfl
  · refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow,
      hfix _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩), div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)),
      map_one]
    rfl

theorem emb_sigma_pow {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O) (n : ℕ)
    (τ : ZMod a) (w : Wq l a) : emb t τ ((sigma l a ^ n) w) = emb t (τ - n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, emb_sigma]
    congr 1
    push_cast
    ring

theorem kummer_mem_resSub (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) (he : e + 1 = l ^ a) : ϖ.kummer k ∈ resSub l a := by
  rw [mem_resSub, ← he, pow_succ, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one (isTiltOf_kummer ϖ hk hζ), one_mul]

theorem galA_ev (ϖ : PiSys l e) {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s)
    (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (x : (Wq l a)⟦X⟧) :
    Per.σA k (ϖ.ev a x) = ϖ.ev a (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) x)) := by
  refine RingHom.congr_fun (ringHom_ext_of_sep ((Per.σA k).comp (ϖ.ev a))
    ((ϖ.ev a).comp ((rescale (WittVector.teichmuller l z)).comp
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a)))) (fun w => ?_) ?_
    fun y hy => ϖ.sep_teich y fun n => ?_) x
  · simp only [RingHom.comp_apply, PiSys.ev_C, galA_wA hk, map_C]
    have : rescale (WittVector.teichmuller l z) (C ((sigma l a ^ s) w)) = C ((sigma l a ^ s) w) := by
      refine PowerSeries.ext fun m => ?_
      rw [coeff_rescale, coeff_C]
      split_ifs with h
      · rw [h, pow_zero, one_mul]
      · rw [mul_zero]
    rw [RingHom.coe_coe, this, PiSys.ev_C]
  · simp only [RingHom.comp_apply, PiSys.ev_X, map_X, rescale_X, map_mul, PiSys.ev_C, PiSys.gal_teich,
      PiSys.mu, wA_teich, hz, add_sub_cancel]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, PiSys.ev_X, PiSys.gal_teich, mul_pow]
    exact dvd_mul_left _ _

theorem thetaW_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    {ζ : ↥LL.1} (hζ : k (ϖ.seq 0) = (ζ : Om l) * ϖ.seq 0) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) :
    ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) = ζ := by
  refine Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective ?_)
  have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
  simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller, hz] at h1
  exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq (isTiltOf_kummer ϖ hk hζ))

theorem toAc_rescale {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (γ : TameGal K l e a) (c : Wq l a)
    (hc : ∀ τ, algebraMap O K (emb t τ c) = γ.root τ) (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    (toAc t K (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x)) τ : K⟦X⟧) = ringAct γ (fun σ => (toAc t K x σ : K⟦X⟧)) τ := by
  refine PowerSeries.ext fun n => ?_
  rw [ringAct_apply, coeff_rescale, coeff_toAc, coeff_toAc, coeff_rescale, coeff_map, map_mul, map_pow,
    map_mul, map_pow, hc]
  congr 2
  rw [RingHom.coe_coe, emb_sigma_pow, ZMod.natCast_zmod_val]

theorem algebraMap_emb_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a)
    (hζ : k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0) (z : Fq l a)
    (hz : Fq.val l a z = ϖ.kummer k) (τ : ZMod a) :
    algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ (WittVector.teichmuller l z)) = γ.root τ := by
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) : ↥(OL LL)) : ↥LL.1) = _
  rw [sigma_pow_teich, map_pow, SubmonoidClass.coe_pow, thetaW_teich ϖ hk LL hζ z hz, TameGal.root, powL_apply]
  simp

theorem covers_of_root {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (γ : TameGal K l e a) {k : GQ l}
    (hunr : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k)
    (hroot : ∀ τ, algebraMap O K (emb t τ (WittVector.teichmuller l z)) = γ.root τ) : Covers K t ϖ k γ := by
  intro f f' hf'
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
  set o := Module.Free.chooseBasis ℤ_[l] O
  have hf : f' = ∑ j, o j • toAc t K (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) (x j))) := by
    funext τ
    refine Subtype.ext ?_
    rw [hf' τ]
    have h1 : (fun σ => (((∑ j, o j • toAc t K (x j)) σ : A O K) : K⟦X⟧)) =
        ∑ j, algebraMap O K (o j) • (fun σ => (toAc t K (x j) σ : K⟦X⟧)) := by
      funext σ
      simp [Finset.sum_apply, algebraMap_smul]

    rw [h1, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
    simp [algebraMap_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toAc_rescale t γ _ hroot]
  subst hf

  simp only [map_sum, map_smul, PiSys.iTot_toAc, galOA_tmul, galA_ev ϖ hunr z hz]

end GlobalTheory.BKGal.CoverBridge


open GlobalTheory.BKGal.CoverBridge in
theorem GlobalTheory.BKGal.covers_of_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf,
    (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) →
    k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  intro l _ a e _ _ ϖ LL _ _ γ k hk hunr hζ
  have hmem := kummer_mem_resSub ϖ hk hζ (TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a))
  exact covers_of_root (thetaW a LL) ϖ γ hunr ⟨ϖ.kummer k, hmem⟩ rfl
    (algebraMap_emb_teich ϖ hk LL γ hζ ⟨ϖ.kummer k, hmem⟩ rfl)
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.BKGal.CoversConv

open GlobalTheory.BKReal

variable {l : ℕ} [Fact l.Prime]

def toOC (LL : FinExt l) : OA l ↥(OL LL) →+* OC l :=
  letI : Algebra ℤ_[l] (OC l) := ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  (Algebra.TensorProduct.lift (R := ℤ_[l]) (S := ℤ_[l])
    ({ intToOC LL with commutes' := fun z => intToOC_algebraMap LL z } : ↥(OL LL) →ₐ[ℤ_[l]] OC l)
    ({ Per.θ l with commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] OC l)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toOC_tmul (LL : FinExt l) (o : ↥(OL LL)) (x : Ainf l) :
    toOC LL (o ⊗ₜ x) = intToOC LL o * Per.θ l x := rfl

theorem toOC_constA (a : ℕ) [NeZero a] (LL : FinExt l) [HasUnr a LL] (c : ZMod a → ↥(OL LL)) :
    toOC LL (constA (thetaW a LL) c) = intToOC LL (c 0) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective (thetaW a LL)).2 c
  rw [constA_splitHom]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, toOC_tmul, splitHom_tmul, emb_zero, map_mul,
      intToOC_thetaW]
  | add y y' h h' => simp only [map_add (f := _), Pi.add_apply, h, h']

theorem iTot_const {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {a e : ℕ} [NeZero a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (c : ZMod a → O) :
    ϖ.iTot t K (fun τ => algebraMap O (A O K) (c τ)) = constA t c := by
  rw [PiSys.iTot, glue_apply, eq_sum_idem]
  simp only [AlgHom.commutes]

end GlobalTheory.BKGal.CoversConv


open GlobalTheory.BKGal.CoversConv GlobalTheory.BKReal in
theorem GlobalTheory.BKGal.covers_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) ∧ k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 := by
  intro l _ a e _ _ ϖ LL _ _ k γ hc
  set t := thetaW a LL with ht
  have hW : ∀ w : Wq l a, Per.σO k (Per.θ l (wA l a w)) =
      Per.θ l (wA l a ((sigma l a ^ γ.shift.val) w)) := by
    intro w
    have h1 := hc (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t τ w))
      (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t (τ - γ.shift) w)) (fun τ => by
        change _ = rescale (γ.root τ) _
        beta_reduce
        have hC : ∀ (c : ↥(OL LL)) (m : ℕ), coeff m ((algebraMap _ (A ↥(OL LL) ↥LL.1) c : A _ _) : (↥LL.1)⟦X⟧) =
            if m = 0 then algebraMap _ ↥LL.1 c else 0 := fun c m =>
          (congrArg (coeff m) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) c)).trans (coeff_C ..)
        ext1 n
        rw [coeff_rescale, hC]
        split_ifs with h
        · rw [h, pow_zero, one_mul]
        · rw [mul_zero])
    rw [iTot_const, iTot_const, constA_emb, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [toOC_tmul, toOC_constA, map_one, one_mul, GlobalTheory.RingBasics.θ_σA] at h2
    rw [h2, ← intToOC_thetaW a LL]
    congr 1
    show t ((sigma l a ^ (-(0 - γ.shift)).val) w) = _
    rw [zero_sub, neg_neg]
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have hpow : ∀ j : ℕ, ((Per.θ l (wA l a (WittVector.teichmuller l (z ^ j))) : OC l) : ℂ_[l]) =
      ((ω ^ j : Om l) : ℂ_[l]) := by
    intro j
    rw [wA_teich, WittVector.fontaineTheta_teichmuller, map_pow, map_pow, SubmonoidClass.coe_pow,
      GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    first
    | exact (map_pow (algebraMap (Om l) ℂ_[l]) ω j).symm
    | norm_cast
    | exact (UniformSpace.Completion.coe_pow ..).symm
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx0
    · rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
    · have h1 := one_lt_pow_l l a
      have : NeZero (l ^ a - 1) := ⟨by omega⟩
      have hx1 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by
        rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
      obtain ⟨j, -, rfl⟩ := hω.eq_pow_of_pow_eq_one hx1
      have h2 := congrArg (fun y : OC l => (y : ℂ_[l])) (hW (WittVector.teichmuller l (z ^ j)))
      rw [sigma_pow_teich, map_pow (wA l a), map_pow (Per.θ l), SubmonoidClass.coe_pow, hpow] at h2
      replace h2 := (GlobalTheory.RingIface.sigO_coe l k _).symm.trans h2
      rw [hpow, GlobalTheory.RingBasics.σC_coe] at h2
      exact (algebraMap (Om l) ℂ_[l]).injective (h2.trans (map_pow (algebraMap (Om l) ℂ_[l]) _ _).symm)
  · have hr : ∀ τ, IsIntegral ℤ_[l] (γ.root τ) := fun τ =>
      IsIntegral.of_pow (NeZero.pos e) (by rw [γ.root_pow]; exact isIntegral_one)
    let r : ZMod a → ↥(OL LL) := fun τ => ⟨γ.root τ, hr τ⟩
    have h1 := hc (fun _ => uIn (A ↥(OL LL) ↥LL.1))
      ((fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ)) * fun _ => uIn (A ↥(OL LL) ↥LL.1)) (fun τ => by
        change ((algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ) : A _ _) : (↥LL.1)⟦X⟧) *
          ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧) =
          rescale (γ.root τ) ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧)
        rw [coe_uIn, rescale_X]
        exact congrArg (· * X) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) (r τ)))
    rw [map_mul (ϖ.iTot t ↥LL.1), iTot_const, PiSys.iTot_u, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [map_mul (toOC LL), toOC_tmul, toOC_constA, toOC_tmul, map_one, one_mul, one_mul, GlobalTheory.RingBasics.θ_σA,
      PiSys.theta_teich] at h2
    have h3 := (GlobalTheory.RingIface.sigO_coe l k (ϖ.seqO 0)).symm.trans (congrArg (fun y : OC l => (y : ℂ_[l])) h2)
    have h4 := (GlobalTheory.RingBasics.σC_coe k (ϖ.seq 0)).symm.trans h3
    have hr0 : ((r 0 : ↥LL.1) : Om l) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
      simp [r, TameGal.root]
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_mul (algebraMap (Om l) ℂ_[l]), ← hr0]
    exact h4
end
end
