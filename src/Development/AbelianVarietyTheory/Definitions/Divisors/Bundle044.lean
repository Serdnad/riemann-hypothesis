module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X} {ρ : k →+* K}

def bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : CxPts p (τ.comp ρ) := CxPts.bcMap w τ z

theorem bcPt_val (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : (bcPt w τ z).1 = z.1 ≫ j := rfl

theorem continuous_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) : Continuous (bcPt w τ) :=
  CxPts.continuous_of_comp (bcPt_val w τ)

theorem cInfAt_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) {f : CxPts p (τ.comp ρ) → ℝ} {z : CxPts q τ}
    (h : CInfAt f (bcPt w τ z)) : CInfAt (fun y => f (bcPt w τ y)) z := by
  have hm : ∀ y, (bcPt w τ y).1 = y.1 ≫ j := bcPt_val w τ
  unfold CInfAt at h ⊢
  obtain ⟨W, ι, hι, g, F, O, hW, hO, hmem, hF, he⟩ := h
  refine ⟨j ⁻¹ᵁ W, ι, hι, fun a => j.app W (g a), F, O, (CxPts.mem_ptsIn_preimage hm).2 hW, hO, ?_, hF, ?_⟩
  · simpa only [CxPts.ev_of_comp hm] using hmem
  · filter_upwards [(continuous_bcPt w τ).continuousAt.tendsto.eventually he] with y hy
    simpa only [CxPts.ev_of_comp hm] using hy

def MLine.bc (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) : MLine q τ where
  B := A.B.pull j
  φ := A.φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => bcPt w τ) fun _ _ => rfl
  cInf i z hz := (cInfAt_bcPt w τ (A.cInf _ _ (mem_of_mem_linComb (m := fun _ => bcPt w τ z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun y => by simp [Weight.linComb])

end GlobalTheory.Mix
end
end

section

noncomputable section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical
namespace GlobalTheory.LKRes.Model
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem sigKQ_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigKQ_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) = (1 : K) ⊗ₜ[ℚ_[p]] frobQ p r b
  rw [Algebra.TensorProduct.map_tmul, map_one]

theorem frobQ_norm (r : ℕ) (b : Qr p r) : ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ = ‖(b : PadicAlgCl p)‖ :=
  norm_map_GK p (Q0 p) (frobK p (Q0 p)) b

theorem frobQ_intR (r : ℕ) (b : Qr p r) (hb : b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r) :
    frobQ p r b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
  simp only [GlobalTheory.LKLoc.intR, Subring.mem_comap] at *
  have := (mem_Obar_iff (p := p)).1 hb
  exact (mem_Obar_iff (p := p)).2 (by
    show ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ ≤ 1
    rw [frobQ_norm]; exact this)

theorem sigKQ_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : sigKQ p K r x ∈ intKQ p K r := by
  have : intKQ p K r ≤ (intKQ p K r).comap (sigKQ p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclK]; exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclQ]; exact Subring.subset_closure (Or.inr ⟨⟨_, frobQ_intR p r b.1 b.2⟩, rfl⟩)
  exact this hx

theorem sigRes_Kres (n r : ℕ) (g : GL (Fin n) (KQ p K r)) (hg : g ∈ Kres p K n r) :
    sigRes p K n r g ∈ Kres p K n r := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.map ((sigKQ p K r).toRingHom.restrict (intKQ p K r) (intKQ p K r)
    (fun x hx => sigKQ_intKQ p K r x hx)) h, ?_⟩
  ext i j
  simp [sigRes, GeneralLinearGroup.map]

def mulMap (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.productMap K.val (Qr p r).val

theorem mulMap_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : ‖mulMap p K r x‖ ≤ 1 := by
  have : intKQ p K r ≤ (Obar p).toSubring.comap (mulMap p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r (a.1 ⊗ₜ[ℚ_[p]] (1 : Qr p r))) ∈ Obar p
      show (a.1 : PadicAlgCl p) * 1 ∈ Obar p
      rw [mul_one]; exact a.2
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r ((1 : K) ⊗ₜ[ℚ_[p]] b.1)) ∈ Obar p
      show 1 * (b.1 : PadicAlgCl p) ∈ Obar p
      rw [one_mul]; exact b.2
  exact (mem_Obar_iff (p := p)).1 (this hx)

theorem sigHT_KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (g : GHT p m n r Kw)
    (hg : g ∈ KHT p m n r Kw) : sigHT p m n r Kw g ∈ KHT p m n r Kw := by
  refine ⟨?_, fun i hi => sigRes_Kres p (Kw i) n r _ (hg.2 i hi)⟩
  obtain ⟨h, e⟩ := hg.1
  refine ⟨GeneralLinearGroup.map ((frobQ p r).toRingHom.restrict (GlobalTheory.LKLoc.intR p (Q0 p) r)
    (GlobalTheory.LKLoc.intR p (Q0 p) r) (fun x hx => frobQ_intR p r x hx)) h, ?_⟩
  show _ = GlobalTheory.LKLoc.sig p (Q0 p) 1 r g.1
  rw [← e]
  ext i j
  rfl

end GlobalTheory.LKRes.Model
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

namespace PolyTower

variable (R : Subring K) [IsLocalRing R] (r : ℕ)

end PolyTower


theorem IsEtTower.ker_eq_span {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    RingHom.ker ψ = Ideal.span (Set.range τ) := by
  haveI := h.top.isLocalRing
  haveI : IsNoetherianRing T := by
    letI := (cL.codRestrict T h.top.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType k T := h.top.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k T
  let P := MvPolynomial (Fin r) R
  letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  set I := RingHom.ker ψ
  set J : Ideal T := Ideal.span (Set.range τ)
  have hJI : J ≤ I := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h.zero i)
  have hsub : ∀ x, x - ι (ψ x) ∈ I := fun x => by
    show ψ _ = 0
    rw [map_sub, h.retr, sub_self]
  let Q : Ideal T := J ⊔ I * I
  let g : T →ₐ[P] T ⧸ Q :=
    { (Ideal.Quotient.mk Q).comp (ι.comp ψ) with
      commutes' := fun x => by
        have : ((Ideal.Quotient.mk Q).comp (ι.comp ψ)).comp (MvPolynomial.eval₂Hom ι τ) =
            (Ideal.Quotient.mk Q).comp (MvPolynomial.eval₂Hom ι τ) := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [h.retr]
          · intro i
            have : τ i ∈ Q := Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
            simp [h.zero, Ideal.Quotient.eq_zero_iff_mem.2 this]
        exact RingHom.congr_fun this x }
  have hn : IsNilpotent (I.map (Ideal.Quotient.mk Q)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have he : Ideal.Quotient.mkₐ P Q = g := by
    refine Algebra.FormallyUnramified.ext _ hn fun x => ?_
    rw [Ideal.Quotient.eq]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk Q) (hsub x)
    rw [map_sub] at this
    exact this
  have hIQ : I ≤ J ⊔ I • I := fun x hx => by
    have e := AlgHom.congr_fun he x
    have hx' : ψ x = 0 := hx
    have : Ideal.Quotient.mk Q x = 0 := by
      refine e.trans ?_
      show Ideal.Quotient.mk Q (ι (ψ x)) = 0
      rw [hx', map_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hI : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hI hIQ) hJI

theorem IsEtTower.bijective_of_zero {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {ι : R →+* T} {ψ : T →+* R} {τ : Fin 0 → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Bijective ψ := by
  refine ⟨(RingHom.injective_iff_ker_eq_bot ψ).2 ?_, fun a => ⟨ι a, h.retr a⟩⟩
  rw [h.ker_eq_span, Set.range_eq_empty, Ideal.span_empty]

end GlobalTheory.FieldPair
end
end

section

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.PairModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finite_levQc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (l : Level H) : Finite (LevQc Dw l) := by
  have hM : Mfr l ≠ ⊥ := by
    intro h
    have h₁ : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := (Mfr l).finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul (Mfr l) (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem hatC_phiHat {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}
    (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    inC c (phiHat c φ q) = hatC l (fun x => inC c (φ x)) q := by
  haveI := finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  have hz : inC c (zetaM c) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    rw [zetaM, map_pow]
    show zeta l.M' ^ (l.M' / l.M) = _
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have h0 : 0 < l.M := by have := l.three_le; omega
    have h1 : l.M' ≠ 0 := Nat.lcm_ne_zero h0.ne' l.A_pos.ne'
    have h2 : (m : ℂ) ≠ 0 := by rintro h; apply h1; rw [hm, Nat.cast_eq_zero.1 h, mul_zero]
    have h3 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [zeta, ← Complex.exp_nat_mul, hm, Nat.mul_div_cancel_left _ h0]
    congr 1
    push_cast
    field_simp

  rw [phiHat, hatC, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀, hz]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

end

end GlobalTheory.AdTh.PairModel
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)





end GlobalTheory.HilbertSamuel.Model
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal

namespace GlobalTheory.TamSU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

def lieInt (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) :
    AddSubgroup (Matrix (Fin M) (Fin M) E) where
  carrier := {X | X.trace = 0 ∧ (X.map σ)ᵀ * J + J * X = 0 ∧ ∀ x ∈ Λ, X *ᵥ x ∈ Λ}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], ?_, fun x hx => ?_⟩
    · have e : (X + Y).map σ = X.map σ + Y.map σ := by ext; simp
      rw [e, transpose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX.2.1, hY.2.1, add_zero]
    · rw [add_mulVec]; exact Λ.add_mem (hX.2.2 x hx) (hY.2.2 x hx)
  neg_mem' {X} hX := by
    refine ⟨by rw [trace_neg, hX.1, neg_zero], ?_, fun x hx => ?_⟩
    · have e : (-X).map σ = -X.map σ := by ext; simp
      rw [e, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.2.1, neg_zero]
    · rw [neg_mulVec]; exact Λ.neg_mem (hX.2.2 x hx)

def stabSet (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) :
    Set (GlobalTheory.Published.SUAdelic σ J) :=
  {h | GlobalTheory.Mem.Vol.StabHat F (Λ : Set (Fin M → E)) (finMat σ J h.1)}

def locCount (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : ℕ :=
  Nat.card (Quot fun a b : stabSet σ J Λ => ∀ y ∈ latHat F E (Λ : Set (Fin M → E)),
    (finMat σ J a.1.1 - finMat σ J b.1.1) *ᵥ y ∈
      latHat F E ((((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ : Submodule (𝓞 E) (Fin M → E)) : Set (Fin M → E)))

def locVol (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  limUnder atTop fun k : ℕ => (locCount σ J Λ v k : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ (k * (M ^ 2 - 1))

def IsTamagawa (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) (Ψ : Finset (E →+* ℂ))
    (θ : Ψ → (Ainf F ⊗[F] E →+* ℂ)) (e : Fin (M ^ 2 - 1) → Matrix (Fin M) (Fin M) E)
    (μ : Measure (GlobalTheory.Published.SUAdelic σ J)) : Prop :=
  μ.IsHaarMeasure ∧
    Tendsto (fun ε : ℝ => μ {h | h ∈ stabSet σ J Λ ∧
        ∀ ρ a b, ‖infMat σ J (θ ρ) h.1 a b - (1 : Matrix (Fin M) (Fin M) ℂ) a b‖ < ε} /
        GlobalTheory.SUVol.formLie Ψ e (GlobalTheory.SUVol.tanBall Ψ M ε)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (|(discr F : ℝ)| ^ (-((M : ℝ) ^ 2 - 1) / 2) *
        ((Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.relIndex (lieInt σ J Λ) : ℝ) * ∏' v, locVol σ J Λ v)))

end GlobalTheory.TamSU
end
end
