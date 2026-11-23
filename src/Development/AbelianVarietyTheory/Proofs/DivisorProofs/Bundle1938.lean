module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
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
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetApprox

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (y : AE D)
    (hy : y ∈ hatId D 𝔪) : ∃ b ∈ 𝔪, ∃ t ∈ IhE D ⊤, inc D (b : D.host.E) - y = (m : AE D) * t := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    obtain ⟨r, w, hw, e⟩ := GlobalTheory.AdelicApprox.exists_approx D m hm s hs
    have hr : inc D r ∈ OhE D := by
      have : inc D r = s - (m : AE D) * w := by rw [e]; ring
      rw [this]
      exact sub_mem hs (mul_mem (natCast_mem _ m) hw)
    have hri : IsIntegral ℤ r := Formalism.UG.P.csGlob_int (F := ℚ) _ hr
    let r' : 𝓞 D.host.E := ⟨r, hri⟩
    have hbr : b * r' ∈ 𝔪 := Ideal.mul_mem_right _ _ hb
    have hbw : inc D (b : D.host.E) * w ∈ OhE D := mul_mem (Formalism.UG.P.adelstab_incl_int b) hw
    refine ⟨b * r', hbr, -(inc D (b : D.host.E) * w), neg_mem ?_, ?_⟩
    · have := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ _ hbw
      simpa using this
    · have hc : ((b * r' : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) * r := rfl
      rw [hc, map_mul, e]
      ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    obtain ⟨b', hb', t', ht', e'⟩ := hy
    refine ⟨b + b', add_mem hb hb', t + t', add_mem ht ht', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination e + e'
  | neg x _ hx =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    refine ⟨-b, neg_mem hb, -t, neg_mem ht, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -e

theorem matrix_approx : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  intro D 𝔪 a d Y hY m hm
  choose b hb t ht e using fun i j => exists_mem_approx D 𝔪 m hm (Y i j) (hY i j)
  refine ⟨Matrix.of fun i j => ((b i j : 𝓞 D.host.E) : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩,
    fun i j => ⟨t i j, ht i j, ?_⟩⟩
  simpa using e i j

end GlobalTheory.FunObj.CosetApprox
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CommPhase

theorem kap_add (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.kap D T x (y + z) = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Formalism.MainNotions.TaylorLogMetric.kap D T x z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.kap, GlobalTheory.NormSum.VacMove.hf_add_right, Complex.add_im, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem kap_eq_one_of_int (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (m : ℤ)
    (h : (Hf D T x y).im = m) : Formalism.MainNotions.TaylorLogMetric.kap D T x y = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.kap, h]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem chars : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  intro D δ hc 𝔪 a d x hx
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d)
  have hint : ∀ y ∈ La0 D (tor0 D ⊤ δ) a d, ∃ m : ℤ, (Hf D (tor0 D ⊤ δ) x y).im = m :=
    (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc a d _ k0).2.2.1 x hx
  set Lp := La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)
  set S := (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf Lp
  have hwd : ∀ u v : Lp, (QuotientAddGroup.leftRel S) u v →
      Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d) := by
    intro u v huv
    rw [QuotientAddGroup.leftRel_apply] at huv
    have hm : ((-u + v : Lp) : VC D a d) ∈ La0 D (tor0 D ⊤ δ) a d := AddSubgroup.mem_addSubgroupOf.mp huv
    obtain ⟨m, hm⟩ := hint _ hm
    have h1 := kap_eq_one_of_int D (tor0 D ⊤ δ) x _ m hm
    have hv : (v : VC D a d) = (u : VC D a d) + ((-u + v : Lp) : VC D a d) := by
      push_cast; abel
    rw [hv, kap_add, h1, mul_one]
  let χ : AddChar (Lp ⧸ S) ℂ :=
    { toFun := fun q => Quotient.liftOn' q (fun y : Lp => Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d)) hwd
      map_zero_eq_one' := by
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((0 : Lp) : VC D a d) = 1
        exact kap_eq_one_of_int D (tor0 D ⊤ δ) x _ 0 (by simp [Hf])
      map_add_eq_mul' := by
        intro q r
        induction q using QuotientAddGroup.induction_on
        induction r using QuotientAddGroup.induction_on
        rename_i u v
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((u + v : Lp) : VC D a d) =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) * Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d)
        push_cast
        exact kap_add _ _ _ _ _ }
  exact ⟨χ, fun y => rfl⟩

end GlobalTheory.CommPhase
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le (k : Type) [Field k] [Infinite k] : ∀ d : ℕ,
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro d
  induction d with
  | zero => exact isAmpleLB_tens_of_isNef_of_dim_le_zero k
  | succ d ih => exact GlobalTheory.T.ample_plus_nef_induction k d ih

theorem isAmpleLB_of_cls_eq_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  intro k _ _ X p hp A N P hA hN hP hcls
  letI := algebraΓOfHom p
  have hs : strHom k X = p := strHom_eq fun _ => rfl
  have hp' : IsProjOver (strHom k (X := X)) := hs ▸ hp
  obtain ⟨n, i, hi, -⟩ := hp
  have hd : topologicalKrullDim X ≤ (n : ℕ) :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      (ProjSpace.topologicalKrullDim_eq k n).le
  have hT : IsAmpleLB (tens A N) := isAmpleLB_tens_of_isNef_of_dim_le k n X hp' hd A N hA hN
  refine IsAmpleLB.of_lbIso hT hP ((cls_eq_iff hP hT.isLB).1 ?_)
  rw [hcls, cls_tens hA.isLB hN.isLB hT.isLB]

end GlobalTheory
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open GlobalTheory.Orb (archMat)

namespace GlobalTheory.UAut.TorusLevi

theorem prodTens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have key : ∀ x : (A × B) ⊗[F] E, TensorProduct.prodLeft F F A B E x =
      (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x,
        Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp <;> rfl
    | tmul p e =>
      obtain ⟨p₁, p₂⟩ := p
      simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [key, key, a, b]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem adele_ext {z z' : AF F ⊗[F] E} (a : ∀ w, compInf F E w z = compInf F E w z')
    (b : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z') : z = z' := by
  classical
  have key : ∀ x : AF F ⊗[F] E, ∀ w : InfinitePlace F,
      TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)
        (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) x) w = compInf F E w x := by
    intro x w
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [map_zero (compInf F E w)]
      erw [map_zero]
      try erw [map_zero]
      try rfl
    | tmul p e => rfl
    | add x y hx hy =>
      rw [map_add (compInf F E w), ← hx, ← hy]
      erw [map_add, map_add]
      try rfl
  have hinf : Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z' := by
    apply (TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)).injective
    funext w
    rw [key, key, a]
  exact prodTens_ext hinf b

theorem exists_diagonal (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (s : Fin r → ℝ) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    ∃ δ : Fin r → AF F ⊗[F] E, (matHom _ σ J a).1 * adMat F Z = adMat F Z * diagonal δ := by
  classical
  have hR : ∀ w : InfinitePlace F, w.IsReal := fun w => h.1.isReal w
  let c : Fin r → Ainf F := fun i w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hR w)).symm (s i)
  refine ⟨fun i => (pairA F (c i) 1 : AF F) ⊗ₜ[F] (1 : E), ?_⟩
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  refine adele_ext (fun w => ?_) ?_
  · obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have harch : ∀ k l, archMat σ J τ (projArch σ J w a) k l =
        infEmb τ (compInf F E w ((matHom _ σ J a).1 k l)) := by
      intro k l
      show infEmb τ (((matHom _ σ J (projArch σ J w a)) : Matrix (Fin n) (Fin n) _) k l) = _
      rw [matHom_projArch]
      rfl
    have hZ : ∀ k l, infEmb τ (compInf F E w (inclR (F := F) (AF F) (Z k l))) = τ.1 (Z k l) := by
      intro k l
      simp [compInf, inclR, infEmb_tmul]
    have hev : evInf F w (pairA F (c j) 1) = c j w := rfl
    have hc : infEmb τ (compInf F E w ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E))) = (s j : ℂ) := by
      simp only [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, hev, infEmb_tmul, map_one, mul_one]
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hR w),
        ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hR w), RingEquiv.apply_symm_apply]
    have hij := congrFun (congrFun (hs w τ) i) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at hij

    simp only [map_sum, map_mul, Matrix.map_apply, hZ, hc, ← harch]
    simpa only [Matrix.map_apply] using hij
  · have hfin : ∀ k l, (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom ((matHom _ σ J a).1 k l) =
        (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l := fun k l =>
      congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l)
        (MonoidHom.mem_ker.mp ha)
    have hδ : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
        ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E)) = 1 := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
      rfl

    simp only [map_sum, map_mul, hfin, hδ, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem mem_parFlag (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (d : Fin r → ℕ) (s : Fin r → ℝ) (h0 : ∀ i, s i ≠ 0) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    a ∈ parFlag σ J Z d := by
  have hinv : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
    intro w τ
    have h1 : archMat σ J τ (projArch σ J w a⁻¹) * archMat σ J τ (projArch σ J w a) = 1 := by
      rw [← map_mul (archMat σ J τ), ← map_mul (projArch σ J w), inv_mul_cancel, map_one, map_one]
    have h2 : diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (h0 i))]
    calc archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1
        = archMat σ J τ (projArch σ J w a⁻¹) * (Z.map τ.1 *
            (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)))) := by
          rw [h2, Matrix.mul_one]
      _ = (archMat σ J τ (projArch σ J w a⁻¹) * (archMat σ J τ (projArch σ J w a) * Z.map τ.1)) *
            diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [hs w τ]
          simp only [Matrix.mul_assoc]
      _ = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨δ, hδ⟩ := exists_diagonal h ha Z s hs
  obtain ⟨δ', hδ'⟩ := exists_diagonal h (inv_mem ha) Z (fun i => (s i)⁻¹) hinv
  exact ⟨⟨diagonal δ, blockTriangular_diagonal δ, hδ⟩, diagonal δ', blockTriangular_diagonal δ', hδ'⟩

theorem torus_mem_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J _ r X Y d _ _ _ t a ht ha
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨mem_parFlag h ha1 X d t ht fun w τ => (ha2 w τ).1, ?_⟩
  refine mem_parFlag h ha1 Y d (fun i => (t i)⁻¹) (fun i => inv_ne_zero (ht i)) fun w τ => ?_
  simpa only [Complex.ofReal_inv] using (ha2 w τ).2.1

end GlobalTheory.UAut.TorusLevi

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut

theorem exists_blockTriangular_of_keeps_weights {A ι : Type} [CommRing A] [Fintype ι] {n r : ℕ}
    {ε : ι → Matrix (Fin n) (Fin n) A} {w : ι → ℤ} (h1 : ∑ a, ε a = 1) {C : Matrix (Fin n) (Fin r) A}
    {L : Matrix (Fin r) (Fin n) A} (hL : L * C = 1) (e : Fin r → ι) (he : ∀ j, ε (e j) = C * single j j (1 : A) * L)
    {d : Fin r → ℕ} (hw : ∀ a j, w a = w (e j) → ∃ i, a = e i) (hd : ∀ i j, d j < d i → w (e i) ≠ w (e j))
    {z : Matrix (Fin n) (Fin n) A} (hz : ∀ a b, w a ≠ w b → ε a * z * ε b = 0) :
    ∃ B : Matrix (Fin r) (Fin r) A, B.BlockTriangular d ∧ z * C = C * B := by
  refine ⟨L * z * C, fun i j hij => ?_, ?_⟩
  · have := hz _ _ (hd i j hij)
    rw [he, he] at this
    exact (sandwich_eq_zero hL z j i).1 this
  · have h2 : (1 - C * L) * C = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 : ∀ j, (1 - C * L) * (z * ε (e j)) = 0 := fun j => by
      rw [← Matrix.one_mul (z * ε (e j)), ← h1, Finset.sum_mul, h1, Finset.mul_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases h : w a = w (e j)
      · obtain ⟨i, rfl⟩ := hw a j h
        rw [← Matrix.mul_assoc, he i, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
        simp
      · rw [← Matrix.mul_assoc (ε a), hz _ _ h, Matrix.mul_zero]
    have h4 : ∑ j, ε (e j) = C * L := by
      simp only [he]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
    have h5 : (1 - C * L) * (z * (C * L)) = 0 := by
      conv_lhs => rw [← h4, Finset.mul_sum, Finset.mul_sum, h4]
      exact Finset.sum_eq_zero fun j _ => h3 j
    have h6 := congrArg (· * C) h5
    simp only [Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.zero_mul] at h6
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h6
    rw [h6]
    simp only [Matrix.mul_assoc]

theorem mem_leviFlag_of_keeps_weights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ g : GAd σ J, (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g⁻¹).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → g ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y d M hd _ _ xy g hg hg'
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  set φ := inclR (F := F) (E := E) (AF F)
  have m1 : ∀ {L : Matrix (Fin r) (Fin n) E} {C : Matrix (Fin n) (Fin r) E}, L * C = 1 → L.map φ * C.map φ = 1 :=
    fun h => by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ∑ a, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) a = 1 := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _
  have cs : ∀ j : Fin r, Formalism.UG.cT (σ : E →+* E) (single j j (1 : E)) = single j j (1 : E) := fun j => by
    rw [Formalism.UG.cT, Matrix.map_single, transpose_single, map_one]
  have eY : ∀ j, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) (some (.inr j)) =
      Y.map φ * single j j (1 : AF F ⊗[F] E) * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun j => by
    rw [← idemA_eq]
    change adjA σ J (idemA X _ j) = _
    rw [idemA, idemA, adjA_map, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, cs]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
  have kX : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * X.map φ = X.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 yx) (fun j => some (.inl j))
      (fun j => idemA_eq _ _ j)
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · exact ⟨i, rfl⟩
        · have := hd j; have := hd i; simp [wt] at h; omega)
      (fun i j h => by simp [wt]; omega) hz
  have kY : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * Y.map φ = Y.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 xy) (fun j => some (.inr j)) eY
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · have := hd j; have := hd i; simp [wt] at h; omega
        · exact ⟨i, rfl⟩)
      (fun i j h => by simp [wt]; omega) hz
  exact ⟨⟨kX hg, kX hg'⟩, kY hg, kY hg'⟩

end GlobalTheory.UAut
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AuxiliarySplitPlace

theorem exists_auxiliarySplitPlace_notMem_finset : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ U : AuxiliaryPlaceHermitianSpace V, U.u ∉ S := fun D V S =>
  exists_auxiliaryPlace_not_mem_finset (isCMExt_host D) (isHermND_gram V) (SelfDual.isSelfDualAt_frameLat D V) S

end GlobalTheory.AuxiliarySplitPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.typePart_le_eigensystemPart_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  first | exact @GlobalTheory.PartTypeW.part_in_eigenpart | exact GlobalTheory.PartTypeW.part_in_eigenpart | (intros; apply GlobalTheory.PartTypeW.part_in_eigenpart <;> assumption)
end

end

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ample_add_nef_is_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  first | exact @_root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | exact _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | (intros; apply _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef <;> assumption)

end
end
