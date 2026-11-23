module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def SiegelWeilStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → min r s = 0 →
    (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def StdEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x

theorem stdEx_of (h1 : FrameConj) (h2 : HgtEx) : StdEx := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_, fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Φ : Fn F n d}
    (h : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) :
    ∀ γ ∈ ratU σ W.J, ∀ x, M.I om Φ (γ * x) = M.I om Φ x := fun γ hγ x => by
  unfold Model.I
  have e : ∀ g, theta om Φ g (γ * x) = theta om Φ g x := fun g => by simpa only [one_mul] using h 1 (one_mem _) γ hγ g x
  simp only [e]

theorem swap_bdd {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : A × B → ℂ} (c : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ∫ a, ∫ b, f (a, b) ∂ν ∂μ = ∫ b, ∫ a, f (a, b) ∂μ ∂ν :=
  integral_integral_swap (f := fun a b => f (a, b)) (Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC))

theorem int_th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Ψ : Fn F n d}
    (cX : Cpt σ X.J) (cW : Cpt σ W.J) (h1 : M.μ.IsHaarMeasure) (h2 : IsFundamentalDomain (ratU σ X.J) M.dom M.μ)
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    (hc : Continuous fun x : UA σ X.J × UA σ W.J => theta om Ψ x.1 x.2)
    (hi : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Ψ (γ * g) (γ' * h) = theta om Ψ g h)
    {φ : UA σ W.J → ℂ} (pc : Continuous φ) (pi : ∀ γ ∈ ratU σ W.J, ∀ g, φ (γ * g) = φ g) :
    ∫ g in M.dom, th om μ D φ Ψ g ∂M.μ = pet μ D φ (M.I om Ψ) := by
  haveI := cX.sc; haveI := cW.sc
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 (cX.fin _ _ h1 h2).ne
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have c : Continuous fun x : UA σ X.J × UA σ W.J => φ x.2 * star (theta om Ψ x.1 x.2) := (pc.comp continuous_snd).mul hc.star
  obtain ⟨C, hC⟩ := cX.bdd₂ cW c fun γ hγ δ hδ g g' => by simp only [pi δ hδ, hi γ hγ δ hδ]
  unfold th pet Model.I
  refine (swap_bdd _ _ c hC).trans <| integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]
  exact congrArg _ integral_conj

theorem polZero_of (hC : CptAll) (hH : HermLine) (hL : CoefLine) (hT : ThConst) (hN : NonZeroAn) (hM : MatchEx)
    (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : PolZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq
  have t := h.triple
  have cW := hC F E σ B _ G.W _ _ t.base (Or.inr t.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ t.base (Or.inl t.geo.hV') (by omega)
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨m1, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1
  have s1 : ∀ y ∈ pairs B G X R Rf, y.1 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ (m3 _ _ hy.1 hy.2).1
  have s2 : ∀ y ∈ pairs B G X R Rf, y.2 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ (m3 _ _ hy.1 hy.2).2.1
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1 (Or.inr (by omega))
  have cc : ∀ s u, ∀ y ∈ pairs B G X R Rf, Continuous (comb G om om' s u y) := fun s u y hy =>
    ((c1 _ (s1 y hy)).const_smul s).add ((c2 _ (s2 y hy)).const_smul u)
  have ci : ∀ s u, ∀ y ∈ pairs B G X R Rf, ∀ γ ∈ ratU σ G.W.J, ∀ g, comb G om om' s u y (γ * g) = comb G om om' s u y g :=
    fun s u y hy γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_left G.M (b1 _ (s1 y hy)).2.1 γ hγ, I_left G.M' (b2 _ (s2 y hy)).2.1 γ hγ]
  have e01 : ∀ y, comb G om om' 0 1 y = G.M'.I om' y.2 := fun y => by simp [comb]
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have ig : ∀ s u s' u', ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      Integrable (fun g => comb G om om' s u y g * star (comb G om om' s' u' y' g)) (μ.restrict D) := fun s u s' u' y hy y' hy' => by
    have c := (cc s u y hy).mul (cc s' u' y' hy').star
    obtain ⟨C, hC⟩ := cW.bdd c fun γ hγ g => by
      change comb G om om' s u y (γ * g) * star (comb G om om' s' u' y' (γ * g)) =
        comb G om om' s u y g * star (comb G om om' s' u' y' g)
      rw [ci s u y hy γ hγ, ci s' u' y' hy' γ hγ]
    exact Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC)
  obtain ⟨c, hc⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 0 0 1
  have orth : ∀ y ∈ pairs B G X R Rf, pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) = 0 := fun y hy => by
    have e : pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) =
        pet μ D (comb G om om' 1 0 y) (comb G om om' 0 1 y) - c * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y) := by
      unfold pet
      rw [← integral_const_mul, ← integral_sub (ig _ _ _ _ y hy y hy) ((ig _ _ _ _ y hy y hy).const_mul c)]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, hc y hy y hy, sub_self]
  obtain ⟨lam, hl⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) 1 (-c)
  obtain ⟨⟨Φ₀, q1, q2⟩, Φ', r1, r2⟩ := And.imp (fun f => f hp) (fun f => f hq) (hN F E σ B a a' G X om om' t)
  obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
  have hy : (Φ, Φ') ∈ pairs B G X R Rf := ⟨r1.2, hΦ⟩
  have v0 := cV.vol_ne t.geo.hM'.haar t.geo.hM'.dom
  have key : ∀ s u, th om' μ D (comb G om om' s u (Φ, Φ')) Φ' =
      fun _ => pet μ D (comb G om om' s u (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) / (G.M'.μ.real G.M'.dom : ℂ) := fun s u => by
    have k := (hT F E σ B a a' G X om om' R Rf h s u (fun y hy => cW.rapid (cc s u y hy) (ci s u y hy)) μ D hμ hD _ hy).2 Φ'
      (s2 _ hy)
    have i := int_th G.M' cV cW t.geo.hM'.haar t.geo.hM'.dom hμ hD (b2 _ (s2 _ hy)).1 (b2 _ (s2 _ hy)).2.1 (cc s u _ hy) (ci s u _ hy)
    simp only [k, setIntegral_const, Complex.real_smul] at i
    funext g
    rw [k, e01, ← i, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 v0)]
  have n0 : pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) ≠ 0 := fun h0 =>
    r2 (e01 (Φ, Φ') ▸ cW.eq_zero hμ hD (cc 0 1 _ hy) (ci 0 1 _ hy) h0)
  have l0 : lam = 0 := by
    have := hL F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) lam hl _ hy Φ' r1.1
    rw [key, key, orth _ hy] at this
    generalize pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) = x at this n0
    simpa [pet, n0, v0] using this
  have main : PolConst B G X om om' R Rf c := fun Ψ Ψ' h1 h2 g => by
    have hz : (Ψ, Ψ') ∈ pairs B G X R Rf := ⟨h1, h2⟩
    have := congrFun (cW.eq_zero hμ hD (cc 1 (-c) _ hz) (ci 1 (-c) _ hz) (by rw [hl _ hz _ hz, l0, zero_mul])) g
    simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this
  refine ⟨c, fun c0 => q2 (funext fun g => ?_), main⟩
  obtain ⟨Ψ', h1, h2⟩ := m1 Φ₀ q1
  rw [main Φ₀ Ψ' h1 h2 g, c0, zero_mul]; rfl

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def Law (χ : Chr F E) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x

variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem Law.rat (h : Law χ z f) (hχ : IsHecke F E χ) {p : G2 σ Y} (a : p ∈ par2 σ Y) (b : p ∈ rat2 σ Y) (x) : f (p * x) = f x := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 a
  obtain ⟨T, hT⟩ := par_rat ht b
  obtain ⟨u, hu⟩ := det_rat hT
  rw [h p t x ht, hu, hχ.2, GlobalTheory.Doubling.absE_inclR]; simp

theorem Law.diag (h : Law χ z f) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h'))) (g : UA σ Y.J) (x) :
    f (e (g, g) * x) * detInv χ g = f x := by
  rw [h _ _ x (he g g).par, absE_det hJ, detInv, mul_right_comm]; simp

theorem Law.hasSum (h : Law χ z f) (hχ : IsHecke F E χ) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h'))) {x v}
    (hs : HasSum (eisTerm f x) v) : HasSum (fun δ : ratU σ Y.J => f (e (1, δ) * x)) v := by
  let i : ratU σ Y.J → Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y))) :=
    fun δ => Quotient.mk _ ⟨e (1, δ), (he _ _).rat (one_mem _) δ.2⟩
  have hi : Function.Bijective i := by
    refine ⟨fun δ δ' h => ?_, fun q => ?_⟩
    · obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.rightRel_apply.1 (Quotient.exact (s := QuotientGroup.rightRel
        ((par2 σ Y).subgroupOf (rat2 σ Y))) h)))
      change IsPar (e (1, δ') * (e (1, δ))⁻¹) t at ht
      rw [← map_inv, ← map_mul, isPar_iff, he] at ht
      simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add,
        Matrix.one_mul] at ht
      obtain ⟨a, b⟩ := Matrix.fromRows_inj ht
      have : (1 : UA σ Y.J) * 1⁻¹ = δ'.1 * δ.1⁻¹ := Subtype.ext (Units.ext (a.trans b.symm))
      rw [inv_one, mul_one, eq_mul_inv_iff_mul_eq, one_mul] at this
      exact Subtype.ext this
    · obtain ⟨γ, rfl⟩ := Quotient.exists_rep q
      obtain ⟨δ, hδ, hp⟩ := orbit hJ (γ⁻¹).2
      refine ⟨⟨δ, hδ⟩, (Quotient.sound (QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_))).symm⟩
      exact hp _ (he _ _)
  convert (Equiv.ofBijective i hi).hasSum_iff.2 hs using 2 with δ
  have := QuotientGroup.rightRel_apply.1 (Quotient.exact (i δ).out_eq)
  exact Eq.trans (by simp [mul_assoc]) (h.rat hχ this (mul_mem ((he _ _).rat (one_mem _) δ.2) (inv_mem (i δ).out.2)) _)

theorem Law.eis_inv (h : Law χ z f) (hχ : IsHecke F E χ) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h')))
    {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {γ δ : UA σ Y.J} (hγ : γ ∈ ratU σ Y.J) (hδ : δ ∈ ratU σ Y.J) (x) :
    Ê (e (γ, δ) * x) = Ê x := by
  refine (h.hasSum hχ hJ he (hs _)).unique ?_
  have := ((Equiv.mulLeft (⟨γ, hγ⟩ : ratU σ Y.J)⁻¹).trans (Equiv.mulRight ⟨δ, hδ⟩)).hasSum_iff.2 (h.hasSum hχ hJ he (hs x))
  convert this using 2 with η
  have := h.diag hJ he γ (e (1, γ⁻¹ * η * δ) * x)
  rw [detInv_rat hχ hγ, mul_one, ← mul_assoc, ← map_mul] at this
  rw [← mul_assoc, ← map_mul]
  simpa [mul_assoc] using this

theorem countable_ratU : Countable (ratU σ Y.J) := by
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  exact (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).preimage
    Subtype.val_injective

theorem unfold0 : Unfold0 := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h
  have hJ := aniso_of hB hY h0
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * (detInv χ g * φ (h * g))
  have ik : Integrable k μ := hi.mul_bdd (c := C)
    ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
    (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have := An.unfold hD (ik.comp_mul_left h⁻¹)
  rw [integral_mul_left_eq_self k] at this
  simp only [mul_assoc]
  refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this
  refine (((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)
  simp only [k]
  rw [← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]
  have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
  simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
  linear_combination (-(f (e (h, δ * g)) * detInv χ g * φ g)) * this

end GlobalTheory.ThK.Dbl

end
end
