module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle486
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle494
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.ClozelCohomologicalOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle501
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist

@[expose] public section

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.lowering_words_span : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.pres_rho | exact GlobalTheory.CompanionTheory.PresRho.pres_rho | (intros; apply GlobalTheory.CompanionTheory.PresRho.pres_rho <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.twisted_trace_weyl_character : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective (fun a => z a ^ 2) → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | exact GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | (intros; apply GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv <;> assumption)
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.IntegrateK

variable {n : ℕ}

theorem exp_smul_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

def onePar (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_smul_mem_unitary X hX s⟩

theorem onePar_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : onePar X hX 0 = 1 := by
  apply Subtype.ext
  simp [onePar]

theorem onePar_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (h s : ℝ) :
    onePar X hX (h + s) = onePar X hX h * onePar X hX s := by
  apply Subtype.ext
  have hc : Commute ((h : ℂ) • X) ((s : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  show NormedSpace.exp (((h + s : ℝ) : ℂ) • X) = _ * _
  simp only [onePar]
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

theorem inner_sum_left {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Kf : Fin n → Fin n → Module.End ℂ V)
    (hs : ∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (x y : V) :
    ⟪∑ a, ∑ b, X a b • Kf a b x, y⟫_ℂ = -⟪x, ∑ a, ∑ b, X a b • Kf a b y⟫_ℂ := by
  have hent : ∀ a b, (starRingEnd ℂ) (X a b) = -X b a := by
    intro a b
    have := congrFun (congrFun hX b) a
    simpa [Matrix.conjTranspose_apply] using this
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hs, hent]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem intertwines_unitary : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  intro n H V _ _ _ _ _ ρ G hG σ Kf hK hskew T hT k w
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryExp.exists_skew_exp_eq n k
  have hk1 : onePar X hX 1 = k := by
    apply Subtype.ext
    have hk_val : k.1 = (GLK.expG X 1).val := congrArg Units.val hk
    delta GLK.expG at hk_val
    exact (hk_val.trans (IsUnit.unit_spec _)).symm
  let Tc : H →L[ℝ] V :=
    (⟨T, T.continuous_of_finiteDimensional⟩ : H →L[ℂ] V).restrictScalars ℝ
  have hsub : ∀ u s : ℝ, onePar X hX (u - s) * onePar X hX s = onePar X hX u := by
    intro u s
    rw [← onePar_add, sub_add_cancel]
  have hY : ∀ s, HasDerivAt (fun s => T (ρ (onePar X hX s) w))
      (∑ a, ∑ b, X a b • Kf a b (T (ρ (onePar X hX s) w))) s := by
    intro s
    have h0 := hG X (onePar X hX) hX (fun _ => rfl) (ρ (onePar X hX s) w)
    have h1 : HasDerivAt (fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
        (T (∑ a, ∑ b, X a b • G a b (ρ (onePar X hX s) w))) 0 :=
      Tc.hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := HasDerivAt.comp_sub_const (f := fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
      s s (by simpa using h1)
    have e : (fun u => T (ρ (onePar X hX (u - s)) (ρ (onePar X hX s) w)))
        = fun u => T (ρ (onePar X hX u) w) := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    simpa only [map_sum, map_smul, hT] using h2
  have hU : ∀ (v : V) (s : ℝ), HasDerivAt (fun s => σ (onePar X hX s) v)
      (∑ a, ∑ b, X a b • Kf a b (σ (onePar X hX s) v)) s := by
    intro v s
    obtain ⟨S, _, hmem, _, _, hd⟩ := hK.2 (σ (onePar X hX s) v)
    have h0 := hd X (onePar X hX) (fun _ => rfl) _ hmem
    have h2 := HasDerivAt.comp_sub_const (f := fun t => σ (onePar X hX t) (σ (onePar X hX s) v))
      s s (by simpa using h0)
    have e : (fun u => σ (onePar X hX (u - s)) (σ (onePar X hX s) v))
        = fun u => σ (onePar X hX u) v := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    exact h2
  have hconst : ∀ v : V, ⟪T (ρ k w), σ k v⟫_ℂ = ⟪T w, v⟫_ℂ := by
    intro v
    have hf : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => ⟪T (ρ (onePar X hX s) w), σ (onePar X hX s) v⟫_ℂ) 0 s := by
      intro s
      have h := (hY s).inner ℂ (hU v s)
      rw [inner_sum_left Kf hskew X hX, add_neg_cancel] at h
      exact h
    have h := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
      (fun s => (hf s).deriv) 1 0
    simp only [hk1, onePar_zero, map_one] at h
    simpa using h
  have horth : ∀ v : V, ⟪T (ρ k w) - σ k (T w), σ k v⟫_ℂ = 0 := by
    intro v
    rw [inner_sub_left, hconst v, hK.1 k, sub_self]
  have hsurj : σ k (σ k⁻¹ (T (ρ k w) - σ k (T w))) = T (ρ k w) - σ k (T w) := by
    have : (σ k * σ k⁻¹) (T (ρ k w) - σ k (T w)) = T (ρ k w) - σ k (T w) := by
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    exact this
  have hz := horth (σ k⁻¹ (T (ρ k w) - σ k (T w)))
  rw [hsurj, inner_self_eq_zero] at hz
  exact sub_eq_zero.1 hz

end GlobalTheory.CompanionTheory.RealCount.IntegrateK
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SplitPlace

section Generic

variable {G : Type} [Group G]

def toFull (H : Subgroup G) (hH : ∀ g, g ∈ H) : G →* H where
  toFun g := ⟨g, hH g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def quotEquiv (H : Subgroup G) (hH : ∀ g, g ∈ H) (K : Subgroup H) : H ⧸ K ≃ G ⧸ K.map H.subtype :=
  Quotient.congr (Equiv.ofBijective H.subtype ⟨Subtype.val_injective, fun g => ⟨⟨g, hH g⟩, rfl⟩⟩) fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel (K.map H.subtype) a.1 b.1
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      have : x = a⁻¹ * b := Subtype.ext hxe
      exact this ▸ hx

theorem finite_cosets [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → ℂ)
    (hc : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have h1 : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) := hc.image continuous_quotient_mk'
  refine h1.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem hasCompactSupport_val [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (e : G → ℂ)
    (hc : HasCompactSupport e) : HasCompactSupport fun x : H => e x.1 := by
  have hcl : IsClosed {a : G | a ∈ H} := by
    have : {a : G | a ∈ H} = Set.univ := Set.eq_univ_of_forall hH
    rw [this]
    exact isClosed_univ
  exact hc.comp_isClosedEmbedding (Topology.IsClosedEmbedding.subtypeVal hcl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_full [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : ∀ g, g ∈ H)
    (ρ : Representation ℂ H V) (K K' : Subgroup H) (hK' : IsOpen (K' : Set H)) (hr : K'.relIndex K ≠ 0) (e : G → ℂ)
    (hc : HasCompactSupport e) (hinv : ∀ k ∈ K'.map H.subtype, ∀ g, e (g * k) = e g) (y : V) (hy : y ∈ fixed ρ K') :
    levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ∑ᶠ q : G ⧸ K'.map H.subtype, e q.out • (ρ.comp (toFull H hH)) q.out y := by
  have hr' : ((K'.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr
  have hfin := finite_cosets K' hK' _ (hasCompactSupport_val H hH e hc)
  have hs : (Function.support fun q : H ⧸ K' =>
      ((fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id) : V →ₗ[ℂ] V)).Finite := by
    refine hfin.subset fun q hq h0 => hq ?_
    have h0' : e q.out.1 = 0 := h0
    simp [h0']
  have h1 : levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V).toAddMonoidHom
        (∑ᶠ q : H ⧸ K', (fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id)) := rfl
  rw [h1, AddMonoidHom.map_finsum _ hs, smul_finsum, ← finsum_comp_equiv (quotEquiv H hH K')]
  refine finsum_congr fun q => ?_
  have hq : quotEquiv H hH K' q = ((q.out.1 : G) : G ⧸ K'.map H.subtype) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K'.map H.subtype) q.out.1
  rw [hq, hk, hinv k.1 k.2]
  have hk' : (toFull H hH k.1) ∈ K' := by
    obtain ⟨x, hx, hxe⟩ := k.2
    have : toFull H hH k.1 = x := Subtype.ext hxe.symm
    exact this ▸ hx
  have hfix := (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' y).1 hy _ hk'
  have h2 : (ρ.comp (toFull H hH)) (q.out.1 * k.1) y = ρ q.out y := by
    have : toFull H hH (q.out.1 * k.1) = q.out * toFull H hH k.1 := Subtype.ext rfl
    rw [MonoidHom.comp_apply, this, map_mul, Module.End.mul_apply, hfix]
  rw [h2]
  simp [smul_smul, hr']

def fullIrr [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : SmIrr H) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp (toFull H hH)
  smooth v := (σ.smooth v).preimage (Continuous.subtype_mk continuous_id hH)
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact hW g.1 v hv

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_UL {w : Pl E} (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  unfold UL
  rw [if_pos hw]
  exact Subgroup.mem_top g

theorem splitDict : PositivityTheory.Rg.BcB.F.Eig.SplitDict := by
  intro E _ _ _ n w hw σ
  have hH := mem_UL (n := n) hw
  refine ⟨fullIrr (UL n w) hH σ, LinearEquiv.refl ℂ σ.V, fun _ _ => rfl, ?_, ?_⟩
  · rintro π ⟨p, hp, -, f, hf0, hfm, hfe⟩
    refine ⟨(fullIrr (UL n w) hH σ).irred, f, hf0, hfm, fun x v => ?_⟩
    have hpx : toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
    change f (σ.ρ (toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x)) v) = _
    rw [hpx]
    exact hfe x v
  · intro K' hlev e hk
    obtain ⟨-, -, hcs, hinv⟩ := hk
    have hKK : ∀ k ∈ K', ∀ x : UL n w, (k.1 * x.1 * 1 : GLw n w) = (k * x).1 := fun k _ x => by simp
    refine ⟨⟨hasCompactSupport_val _ hH e hcs, fun k hk x => ⟨?_, ?_⟩⟩, fun y hy => ⟨?_, ?_⟩⟩
    · have := hinv k.1 ⟨k, hk, rfl⟩ 1 (by simp) x.1
      simpa using this
    · have := hinv 1 (by simp) k.1 ⟨k, hk, rfl⟩ x.1
      simpa using this
    · refine (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (GlobalTheory.TwTrLin.mem_fixed_iff σ.ρ K' y).1 hy k hk
    · have hr := (GlobalTheory.TwTrUnit.twTr_unit E n w K' hlev σ).2.1
      exact levOp_full (UL n w) hH σ.ρ (KL n w) K' hlev.1 hr e hcs
        (fun k hk g => by simpa using hinv 1 (by simp) k hk g) y hy

end GlobalTheory.CompanionTheory.SplitPlace

end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace GlobalTheory.CompanionTheory.RgCz

theorem exists_fin_map_eq {a : ℕ} (m : Multiset ℂ) (hm : Multiset.card m = a) :
    ∃ χ : Fin a → ℂ, Multiset.map χ Finset.univ.val = m := by
  subst hm
  induction m using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp

theorem charInt_at {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (hr : (CG.mk π).IsRegAlg) (τ : E →+* ℂ) :
    ∃ l : Fin a → ℤ, Function.Injective l ∧
      PositivityTheory.Rg.Cz.HasChar (cx τ (lieOp π)) fun k => (l k : ℂ) := by
  obtain ⟨hnd, hint⟩ := hr τ
  obtain ⟨χ, hχ⟩ := exists_fin_map_eq ((CG.mk π).infChar τ) (CG.card_infChar (CG.mk π) τ)
  have hinf : π.HasInfChar τ (Multiset.map χ Finset.univ.val) := by
    rw [hχ]
    exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ
  have hcap := (GlobalTheory.capelli_cuspSub E a π τ χ hinf).2
  rw [← hχ] at hnd hint
  have hχinj : Function.Injective χ := by
    have h := Multiset.inj_on_of_nodup_map hnd
    intro s t hst
    exact h s (by simp) t (by simp) hst
  have hn : ∀ s, ∃ n : ℤ, χ s = (n : ℂ) + ((a : ℂ) - 1) / 2 := fun s =>
    hint _ (Multiset.mem_map_of_mem χ (by simp))
  choose l hl using hn
  refine ⟨l, fun s t hst => hχinj (by rw [hl, hl, hst]), fun u => ?_⟩
  have h := hcap (u - ((a : ℂ) - 1) / 2)
  rw [sub_add_cancel] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hl k]
  ring

theorem charInt : PositivityTheory.Rg.Cz.CharInt := by
  intro E _ _ _ a π hr
  choose l hl using charInt_at π hr
  exact ⟨l, fun τ => (hl τ).1, fun τ => (hl τ).2⟩

end GlobalTheory.CompanionTheory.RgCz

end
end

section


theorem _root_.GlobalTheory.T.constant_multiplier_mirabolic : PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.MirGen → PositivityTheory.RgEis.CMMir := by
  first | exact @GlobalTheory.CompanionTheory.CMMirror.cmMir | exact GlobalTheory.CompanionTheory.CMMirror.cmMir | (intros; apply GlobalTheory.CompanionTheory.CMMirror.cmMir <;> assumption)
end

section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing NumberField.LiesOver TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.RgEisSo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E) (x : F) :
    w.embedding (algebraMap F E x) = (w.comap (algebraMap F E)).embedding x := by
  have hreal : ComplexEmbedding.IsReal (w.comap (algebraMap F E)).embedding :=
    InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
  have h : InfinitePlace.mk (w.embedding.comp (algebraMap F E)) =
      InfinitePlace.mk (w.comap (algebraMap F E)).embedding := by
    rw [InfinitePlace.mk_embedding, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · exact congrArg (fun f : F →+* ℂ => f x) h
  · have h' : w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
      have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (w.embedding.comp (algebraMap F E))) =
          w.embedding.comp (algebraMap F E) := star_star _
      rw [← h2, h]
      exact ComplexEmbedding.isReal_iff.1 hreal
    exact congrArg (fun f : F →+* ℂ => f x) h'

theorem extensionEmbedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E)
    (z : (w.comap (algebraMap F E)).Completion) :
    extensionEmbedding w (algebraMap (w.comap (algebraMap F E)).Completion w.Completion z) =
      extensionEmbedding (w.comap (algebraMap F E)) z := by
  rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver (w.comap (algebraMap F E)).1 w.1]
  have h := (denseRange_coe (v := w.comap (algebraMap F E))).equalizer
    (g := fun z => extensionEmbedding w (AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 z))
    (h := fun z => extensionEmbedding (w.comap (algebraMap F E)) z)
    ((isometry_extensionEmbedding w).continuous.comp (AbsoluteValue.Completion.continuous_map _ _))
    (isometry_extensionEmbedding _).continuous (funext fun k => ?_)
  · exact congrFun h z
  · have e := LiesOver.completionMap_coe (v := w.comap (algebraMap F E)) (w := w) k
    show extensionEmbedding w (AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 (k : (w.comap (algebraMap F E)).Completion)) =
      extensionEmbedding (w.comap (algebraMap F E)) (k : (w.comap (algebraMap F E)).Completion)
    rw [e, extensionEmbedding_coe, extensionEmbedding_coe]
    exact embedding_algebraMap_of_totallyReal hF w _

theorem phi_nuCM (σ : E →ₐ[F] E) (χ : Chr F E) (hF : IsTotallyReal F) (w : InfinitePlace E) (x : 𝔸[F]) :
    (adCM σ χ).φ w (nuCM F E x) = (adStd F).φ (w.comap (algebraMap F E)) x := by
  have h : eqv F E (nuCM F E x) = GroundTheory.Global.AdeleBaseChange.adeleMap F E x :=
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap x
  show extensionEmbedding w (GroundTheory.Automorphic.Reduction.infEval w (eqv F E (nuCM F E x))) =
    extensionEmbedding _ (GroundTheory.Automorphic.Reduction.infEval _ x)
  rw [h]
  exact extensionEmbedding_algebraMap_of_totallyReal hF w _

end GlobalTheory.CompanionTheory.RgEisSo

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem bInf : BInf := by
  intro F E _ _ _ _ _ σ χ c hcm _ _ _
  haveI : IsTotallyReal F := hcm.1
  refine ⟨fun w => ⟨w.comap (algebraMap F E), fun x => phi_nuCM σ χ hcm.1 w x⟩, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  exact ⟨w, fun x => phi_nuCM σ χ hcm.1 w x⟩

end GlobalTheory.CompanionTheory.RgEisSo
end
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.pole_reality : PoleReal := by
  first | exact @GlobalTheory.CompanionTheory.PoleBound.poleReal | exact GlobalTheory.CompanionTheory.PoleBound.poleReal | (intros; apply GlobalTheory.CompanionTheory.PoleBound.poleReal <;> assumption)
end
