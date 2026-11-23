module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPoints
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.universalFrame_classifies_framedPoints : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (z : FrPt Xo c T) (ψ : R →ₐ[c.F] T), z.x = spMap ψ.toRingHom ≫ y₀.x → ∃! a : A →ₐ[c.F] T, a.comp π = ψ ∧ FrMap a u z := by
  first | exact @GlobalTheory.Frames.univFrame_classifies | exact GlobalTheory.Frames.univFrame_classifies | (intros; apply GlobalTheory.Frames.univFrame_classifies <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.ExtCore

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring


end GlobalTheory.ExtCore
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem level_good_and_sign : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
  rintro D Q ⟨⟨-, hrt, hrt0, -⟩, ⟨hM, hA⟩, -, -⟩
  refine ⟨fun p hp => ?_, hA, fun τ hτ => ?_⟩
  · have hodd := Q.l.odd
    rw [hM] at hodd
    have h3 : ∀ a : ℕ, a.Prime → Odd a → 3 ≤ a := fun a ha ho => by
      have h2 := ha.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    have ha := h3 _ (D.host.g_prime 0) (Nat.Odd.of_mul_left hodd)
    have hb := h3 _ (D.host.g_prime 1) (Nat.Odd.of_mul_right hodd)
    have hab : (D.host.g 0).Coprime (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    have hM0 : Q.l.M ≠ 0 := by have := Q.l.three_le; omega
    have key : ∀ c, 3 ≤ c → c ∣ Q.l.M → ¬ p ∣ c → 3 ≤ Q.l.M / p ^ Q.l.M.factorization p :=
      fun c hc hd hn => hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
    by_cases h : p ∣ D.host.g 0
    · refine key _ hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
      exact Nat.eq_one_of_dvd_coprimes hab h h'
    · exact key _ ha (hM ▸ dvd_mul_right _ _) h
  · rw [hrt, hrt0] at hτ
    have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [hφ]
      have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
      simpa using hd
    rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
    rw [map_neg, Complex.neg_im]
    linarith

end GlobalTheory.RecDict
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i

      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this

    rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem det_mul_sigR_det {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (g : GL (Fin M) (R ⊗[F] E))
    (hg : g ∈ HR R σ J) : g.1.det * sigR R σ g.1.det = 1 := by
  have h : Formalism.UG.cT (sigR R σ) g.1 * JR R J * g.1 = JR R J := hg
  have h2 := congrArg Matrix.det h
  have hu : IsUnit (JR (F := F) R J).det := by
    have : (JR (F := F) R J).det = inclR (F := F) R J.det := ((inclR (F := F) R).map_det J).symm
    rw [this]
    exact (IsUnit.mk0 _ hJ).map _
  have h3 : (Formalism.UG.cT (sigR R σ) g.1).det = sigR R σ g.1.det := by
    rw [Formalism.UG.cT, Matrix.det_transpose]
    exact ((sigR R σ).map_det g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, h3] at h2
  apply hu.mul_left_cancel
  linear_combination h2

theorem det_finHom_norm {D : D7} (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig (finHom V k).1.det = 1 := by
  have h := det_mul_sigR_det (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) (matHom V k) k.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : (finHom V k).1.det = φ (matHom V k).1.det := (φ.map_det _).symm
  have c : ∀ x, sigR (Af D.host.F) D.sp.cm.sig (φ x) = φ (sigR (AF D.host.F) D.sp.cm.sig x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φ, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e, c, ← map_mul, h, map_one]

theorem finHom_inv_mulVec_mem {D : D7} (V : HSp D) (k : GA D V)
    (hk : ∀ z ∈ latHat V, (finHom V k).1.mulVec z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1.mulVec z ∈ latHat V := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change a • e x ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          have hh := V.herm.eq (e x) y
          simpa [hxy] using hh.symm
        simp [map_smul, hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofBijective D.sp.cm.sig (D.sp.cm.sig.bijective)
  rw [hL] at hk ⊢
  rw [map_inv]
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat _ _ _ L (finHom V k) c hfg hsp hk (det_finHom_norm V k)

theorem exists_level_subgroup {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (H : Subgroup G)
    (Λ : AddSubgroup (Fin n → A)) (N : ℕ)
    (hinv : ∀ k : G, (∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ) → ∀ z ∈ Λ, (f k⁻¹).1.mulVec z ∈ Λ) :
    ∃ K : Subgroup G, (∀ k, k ∈ K ↔ k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) ∧
      ∀ k ∈ K, (f k).1.mulVec '' (Λ : Set (Fin n → A)) = Λ := by
  have hin : ∀ k : G, (∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) →
      ∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ := by
    intro k hk z hz
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [sub_eq_iff_eq_add.1 e]
    exact add_mem (nsmul_mem hy N) hz
  have hmul : ∀ (a b : G) z, (f (a * b)).1.mulVec z = (f a).1.mulVec ((f b).1.mulVec z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1.mulVec z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ carrier := {k | k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun k => Iff.rfl, ?_⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := hb' z hz
    obtain ⟨y', hy', e'⟩ := ha' _ (hin b hb' z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [hmul, nsmul_add, ← e, ← e']
    abel
  · exact ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by rw [hone, sub_self, nsmul_zero]⟩⟩
  · rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := ha' _ (hinv a (hin a ha') z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [← hmul, mul_inv_cancel, hone] at e
    rw [neg_nsmul, ← e, neg_sub]
  · rintro k ⟨-, hk⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hin k hk z hz
    · intro z hz
      exact ⟨_, hinv k (hin k hk) z hz, (hmul k k⁻¹ z).symm.trans (by rw [mul_inv_cancel, hone])⟩

theorem exists_isLevelK : ∀ (D : D7) (V : HSp D) (N : ℕ), ∃ Kf : Subgroup (GA D V), IsLevelK V N Kf ∧ ∀ k ∈ Kf, (finHom V k).1.mulVec '' (latHat V : Set _) = latHat V :=
  fun _ V N => exists_level_subgroup (finHom V) (GfC V) (latHat V) N (finHom_inv_mulVec_mem V)

end GlobalTheory.RecDict
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkUnit

theorem infMat_unitary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h : HA (AF F) σ J) :
    ((Formalism.MainNotions.StandardLattice.infMat σ J θ h).map (starRingEnd ℂ)).transpose * J.map τ * Formalism.MainNotions.StandardLattice.infMat σ J θ h =
      J.map τ := by
  let φ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hφ : ∀ (a : AF F) (x : E), φ (a ⊗ₜ x) =
      GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) (fstA F a) * τ x := fun a x =>
    GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 (fstA F a) x
  have h1 : ∀ z, φ (sigR (AF F) σ z) = starRingEnd ℂ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (AF F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, hφ, hφ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, hτ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ x, φ (inclR (AF F) x) = τ x := by
    intro x
    have : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ x := rfl
    rw [this, hφ, map_one, map_one, one_mul]
  have hu : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1 * JR (AF F) J * (HA.mat (AF F) σ J h).1 =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  have hm : Formalism.MainNotions.StandardLattice.infMat σ J θ h = (HA.mat (AF F) σ J h).1.map φ := rfl
  have hJ : (JR (AF F) J).map φ = J.map τ := by
    ext a b
    exact h2 _
  have hc : (Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1).map φ =
      (((HA.mat (AF F) σ J h).1.map φ).map (starRingEnd ℂ)).transpose := by
    ext a b
    exact h1 _
  have := congrArg (fun m => Matrix.map m φ) hu
  simp only [Matrix.map_mul] at this
  rw [hJ, hc] at this
  rw [hm]
  exact this


end GlobalTheory.MarkUnit
end
