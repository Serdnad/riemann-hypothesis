module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Formalism.LocalToGlobal.Columns.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle167
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle300
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle301
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameAgree

theorem inv_mul_cong {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K) (hπ0 : π ≠ 0)
    (hπ : Valued.v π < 1) (a a₁ : GL (Fin N) K)
    (ha : ∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1)
    (ha₁ : ∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) :
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 :=
  GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer π hπ0 hπ a a₁ ha ha₁

theorem glint_of_cong {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b)))
    (hg' : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) :
    g ∈ GLint E n P ∧ ∀ w ∈ stdAt E n P, ((qOf P : E) ^ d)⁻¹ • (g w - w) ∈ stdAt E n P :=
  GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow P d g hg hg'

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

abbrev locM (Q : HeightOneSpectrum (𝓞 E)) : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL (Fin N) (Q.adicCompletion E) :=
  bc (GlobalTheory.Mem.Col2.adAt F Q)

theorem congAt_loc (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : CongAt (F := F) Q n k) : ∀ a b, Valued.v ((algebraMap E (Q.adicCompletion E) (((qOf Q : ℕ) : E) ^ n))⁻¹ *
      (((locM Q k : GL (Fin N) (Q.adicCompletion E)) : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) - 1) a b) ≤ 1 := by
  have hι : IsAdIso (GlobalTheory.Mem.Col2.afIso F E) := ⟨GlobalTheory.Mem.Col2.afIso_tmul_one F E, GlobalTheory.Mem.Col2.mem_rInt_iff F E⟩
  intro a b
  have h1 := hι.val_le (h a b)
  have e1 : ∀ z, GlobalTheory.Mem.Col2.afIso F E z Q = GlobalTheory.Mem.Col2.adAt F Q z := fun z => rfl
  rw [e1, map_mul, GlobalTheory.Mem.Col2.adAt_inclE, map_inv₀, Matrix.sub_apply, map_sub] at h1
  have e2 : GlobalTheory.Mem.Col2.adAt F Q ((1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) =
      (1 : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) a b := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2] at h1
  rw [Matrix.sub_apply]
  exact h1

theorem loc_agree (Q : HeightOneSpectrum (𝓞 E)) {x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : bc (prV (E := E) (Q.under (𝓞 F))) x₁ = bc (prV (E := E) (Q.under (𝓞 F))) x) : locM Q x₁ = locM Q x := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have h1 := congrArg (fun g : GL (Fin N) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => Units.val g a b) h
  change prV (E := E) (Q.under (𝓞 F)) ((x₁ : Matrix (Fin N) (Fin N) _) a b) =
    prV (E := E) (Q.under (𝓞 F)) ((x : Matrix (Fin N) (Fin N) _) a b) at h1
  have h0 : prV (E := E) (Q.under (𝓞 F)) ((x₁ : Matrix (Fin N) (Fin N) _) a b - (x : Matrix (Fin N) (Fin N) _) a b) = 0 := by
    rw [map_sub, sub_eq_zero]; exact h1
  have h2 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h0 Q rfl
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem val_alg (Q : HeightOneSpectrum (𝓞 E)) (e : E) :
    Valued.v (algebraMap E (Q.adicCompletion E) e) = Q.valuation E e :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q e

theorem intAt_of_val (Q : HeightOneSpectrum (𝓞 E)) (c m o : E)
    (h : Valued.v ((algebraMap E (Q.adicCompletion E) c)⁻¹ * (algebraMap E (Q.adicCompletion E) m - algebraMap E (Q.adicCompletion E) o)) ≤ 1) :
    IntAt Q (c⁻¹ * (m - o)) := by
  rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val, ← val_alg, map_mul, map_inv₀, map_sub]
  exact h

theorem one_entry {E₀ : Type} [Field E₀] (Q : HeightOneSpectrum (𝓞 E)) (ψ : E₀ ≃+* E) (a b : Fin N) :
    (1 : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) a b = algebraMap E (Q.adicCompletion E) (ψ ((1 : Matrix (Fin N) (Fin N) E₀) a b)) := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Loc

theorem map_expr {E₀ E : Type} [Field E₀] [Field E] (σ : E₀ ≃+* E) (q d : ℕ) (m o : E₀) :
    ((q : E) ^ d)⁻¹ * (σ m - σ o) = σ (((q : E₀) ^ d)⁻¹ * (m - o)) := by
  simp [map_mul, map_inv₀, map_pow, map_natCast, map_sub]

theorem qOf_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [← (RingOfIntegers.mapRingEquiv s.iE).apply_symm_apply y, mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro hy; exact ⟨_, hy, rfl⟩
    · rintro ⟨z, hz, e⟩
      rw [(RingOfIntegers.mapRingEquiv s.iE).injective e] at hz
      exact hz
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (seamP s P).asIdeal (RingOfIntegers.mapRingEquiv s.iE) hI).toEquiv).symm

theorem intAt_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (e : X.E) :
    IntAt (seamP s P) (s.iE e) ↔ IntAt P e := by
  have hc : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv s.iE y) = s.iE (algebraMap (𝓞 X.E) X.E y) :=
    fun y => rfl
  constructor
  · rintro ⟨r, c, hc', h⟩
    refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
    · rw [← mem_seamP s, RingEquiv.apply_symm_apply]; exact hc'
    · apply s.iE.injective
      rw [map_mul, ← hc, ← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact h
  · rintro ⟨r, c, hc', h⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, RingOfIntegers.mapRingEquiv s.iE c, ?_, ?_⟩
    · rw [mem_seamP s]; exact hc'
    · rw [hc, hc, ← map_mul, h]

end GlobalTheory.FrameAgree

namespace GlobalTheory.FrameAgree

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem core (hTie : AdTie A dtU a) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j) (hp : IsPtAd A a j hj β x p) (hp₁ : IsPtAd A a j hj β x₁ p₁)
    (hx : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1)
    (P : SB t μ) : ∀ a b, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (LinearMap.toMatrix' ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm).toLinearMap a b -
        (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) t.X.E) a b)) := by
  set Q := seamP t.seam P.1 with hQdef
  have hQ : Q ∈ ssRec t u μ := (mem_ssRec t u μ P.1).2 (by rw [hTie.isChainTop.1]; classical exact Finset.mem_union.2 (Or.inr P.2))
  have hv : Q.under (𝓞 D.host.F) ∈ plUnder D.host.F (ssRec t u μ) := ⟨Q, hQ, rfl⟩
  have hag := loc_agree Q (hx _ hv)
  have c0 := congAt_loc Q _ _ (hp.frame P)
  have c1 := congAt_loc Q _ _ (hp₁.frame P)
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hq0 : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hπ0 : algebraMap D.host.E (Q.adicCompletion D.host.E) (((qOf Q : ℕ) : D.host.E) ^ (t.cst μ).D P) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap D.host.E _).injective]
    exact pow_ne_zero _ (by exact_mod_cast hq0)
  have hπ : Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (((qOf Q : ℕ) : D.host.E) ^ (t.cst μ).D P)) < 1 := by
    rw [val_alg, map_pow]
    refine pow_lt_one₀ zero_le' ?_ (by omega)
    have e : ((qOf Q : ℕ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (qOf Q : 𝓞 D.host.E) := by rw [map_natCast]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (Q.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key := inv_mul_cong _ hπ0 hπ _ _ c0 c1
  have hs : (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm =
      (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P := by
    ext w; rfl
  have e : (locM Q (((ratA D.host.F) (A.crd j hj) * x.1 * (ratA D.host.F) (A.fb j hj β P))⁻¹ *
        (ratA D.host.F) ((seamGL t.seam) (frsF t.sel (t.tup μ) p P))))⁻¹ *
      locM Q (((ratA D.host.F) (A.crd j hj) * x₁.1 * (ratA D.host.F) (A.fb j hj β P))⁻¹ *
        (ratA D.host.F) ((seamGL t.seam) (frsF t.sel (t.tup μ) p₁ P))) =
      locM Q (ratA D.host.F (seamGL t.seam ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    rw [hag]
    group
  rw [e] at key
  intro a b
  have k := key a b
  obtain ⟨g, hg⟩ : ∃ g, g = (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm := ⟨_, rfl⟩
  rw [← hg] at k ⊢
  have ent : ((locM Q (ratA D.host.F (seamGL t.seam g)) : GL (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) :
      Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) a b =
      algebraMap D.host.E _ (t.seam.iE (LinearMap.toMatrix' g.toLinearMap a b)) := by
    show GlobalTheory.Mem.Col2.adAt D.host.F Q (inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) a b)) = _
    rw [GlobalTheory.Mem.Col2.adAt_inclE]
    rfl
  have one : (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) a b =
      algebraMap D.host.E _ (t.seam.iE ((1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) t.X.E) a b)) := by
    exact one_entry Q t.seam.iE a b
  rw [Matrix.sub_apply, ent, one] at k
  have k2 := intAt_of_val Q _ _ _ k
  rw [hQdef, qOf_seamP, map_expr] at k2
  exact (intAt_seamP t.seam P.1 _).1 k2

end GlobalTheory.FrameAgree

namespace GlobalTheory.FrameAgree

theorem frame_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have h1 := core hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have h2 := core hTie j hj β x₁ x p₁ p hp₁ hp (fun v hv => (hx v hv).symm) P
  have hsymm : ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm).symm =
      (frsF t.sel (t.tup μ) p P).trans (frsF t.sel (t.tup μ) p₁ P).symm := by
    ext w; rfl
  exact glint_of_cong P.1 ((t.cst μ).D P) _ h1 (by rw [hsymm]; exact h2)

end GlobalTheory.FrameAgree
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.RatEntry

theorem unitV_det_red_one {X : Fields} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (χ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ)
    (k : GLint X.E n P) (hk : redGL n P k = 1) : LocE.unitV χ ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 :=
  tqk_unitV_one χ (by rw [(det_glint k).2, ← redGL_val, hk, Units.val_one, Matrix.det_one])

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem red_pass_one {u : Pr.Word} {j : ℕ} {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (g : UF X.E (R.N j)) (p : ChPt (R := R) sel mu u j) (κ : GLQ X.E (R.N j) (rowSG Pr sel mu))
    (hκ : ∀ P, frsF sel mu (((g, 1, 1) : FrmG Λ Θ) • p) P = g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) (P : rowSG Pr sel mu) :
    redGL (R.N j) P.1 (κ P) = 1 := by
  classical
  have h := hκ P
  by_cases hP : P.1 ∈ Pr.vGs
  · have e : κ P = passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩ := by
      apply Subtype.ext
      unfold frsF at h
      simp only [dif_pos hP] at h
      show (κ P).1 = ((((g, 1, 1) : FrmG Λ Θ) • p).deco.1.liftFr ⟨P.1, hP⟩)⁻¹ * g.1 * p.deco.1.liftFr ⟨P.1, hP⟩
      rw [h, Subgroup.coe_inv]
      group
    rw [e]
    exact redGL_passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩
  · unfold frsF at h
    simp only [dif_neg hP] at h
    have h1 : ((κ P)⁻¹).1 = 1 := by
      have h' : g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * ((κ P)⁻¹).1) =
          g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * 1) := by
        rw [← h]
        show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
        simp [mul_assoc]
      exact mul_left_cancel (mul_left_cancel h')
    have h2 : κ P = 1 := inv_eq_one.1 (Subtype.ext h1)
    rw [h2, map_one]

theorem rho_pass_one (i : ℕ) (κ : GLQ X.E (R.N i) (rowSG Pr sel mu)) (κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu))
    (hκ : ∀ P : rowSG Pr sel mu, redGL (R.N i) P.1 (κ P) = 1) (hκ' : ∀ P : rowSG Pr sel mu, redGL (R.N (i + 1)) P.1 (κ' P) = 1) :
    ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
      rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) = 1 := by
  refine Finset.prod_eq_one fun P _ => ?_
  have h1 : redGL _ P.1 ((κ P)⁻¹) = 1 := by rw [map_inv, hκ P, inv_one]
  have h2 : redGL _ P.1 ((κ' P)⁻¹) = 1 := by rw [map_inv, hκ' P, inv_one]
  rw [Pi.inv_apply, Pi.inv_apply]
  unfold rhoS rhoT
  rw [unitV_det_red_one _ ((κ P)⁻¹) h1, unitV_det_red_one _ ((κ' P)⁻¹) h2, mul_one]

theorem xiEntry_rat {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (g : UF X.E (R.N i)) (g' : UF X.E (R.N (i + 1))) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiEntry Ch sel mu cst L i al be
        (((g, 1, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := Pr.vGs) × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p)
        (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG (E := X.E) (n := R.N (i + 1)) (SG := Pr.vGs) × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p')
        (g'.1.toLinearMap ∘ₗ x ∘ₗ g.1.symm.toLinearMap) = XiEntry Ch sel mu cst L i al be p p' x := by
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have e1 : (((g, 1, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := Pr.vGs) × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p) =
      ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) • p := rfl
  have e2 : (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG (E := X.E) (n := R.N (i + 1)) (SG := Pr.vGs) × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p') =
      ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) • p' := rfl
  rw [e1, e2]
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) p'
  have key := GlobalTheory.MatLaw.xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  rw [rho_pass_one i κ κ' (red_pass_one g p κ hκ) (red_pass_one g' p' κ' hκ'), mul_one, ec, ec'] at key
  rw [key]
  simp

end GlobalTheory.RatEntry

namespace GlobalTheory.RatEntry

theorem xiPt_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i < t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _hT i hi hlt β β' x x' p p' _hp _hp' g g' w
  unfold xiPt
  rw [dif_pos hlt, dif_pos hlt]
  exact GlobalTheory.RatEntry.xiEntry_rat hP.fields.ok t.pr_ok hP.sel ⟨hP.avoid.2, hP.avoid.1⟩ (t.idx_ok μ) hlt _ _ g g' p p' w

end GlobalTheory.RatEntry
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU

theorem repY_yb_coset_bdd {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (c : (D.chTw u μ).cls (t.m2 + 1)) (P : SB t μ) :
    SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)))
        (A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) P) ∧
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M)) *
        (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) l) := by
  obtain ⟨w, hw1, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  have hmem : repY (A.yb c) ∈ A.yb c := Classical.epsilon_spec (p := fun y => y ∈ A.yb c) ⟨w, hwm⟩
  refine ⟨H.coset c _ hmem P, ?_⟩
  have hd := (Set.ext_iff.1 hw (repY (A.yb c))).1 hmem
  rw [Set.mem_setOf_eq] at hd
  have h0 := (Submodule.mem_iInf _).1 hd P
  have h1 := (Submodule.mem_iInf _).1 hw1 P
  rw [Submodule.mem_comap] at h0 h1
  have hf := GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)
  set fr := frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) with hfr
  have toStd : ∀ v, v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.pt (t.m2 + 1) (cpl_lt t μ).le c).deco.1.N → ∀ l, IntAt P.1 ((fr P).symm v l) := by
    intro v hv
    refine GlobalTheory.TopStep.mem_stdAt.1 ((hf P _).1 ?_)
    rwa [LinearEquiv.apply_symm_apply]
  have k0 := toStd _ h0
  have k1 := toStd _ h1
  simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at k0 k1
  intro l
  have hq : (qOf P.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ipow : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  have a0 := k0 l
  have a1 := k1 l
  by_cases hP : P.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ 1 * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ 1 * (((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l - ((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-1 : ℤ))⁻¹ * (fr P).symm w l := by
      simp only [zpow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, pow_one]
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow 1) a0) a1
  · simp only [hP, if_false] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ (2 * (t.cst μ).M) * (((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l -
          ((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-((t.cst μ).M : ℤ)))⁻¹ * (fr P).symm w l := by
      simp only [_root_.zpow_neg, inv_inv, zpow_natCast]
      field_simp
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow _) a0) a1

theorem baseCosetRepresentative_bounded_at_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))), IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H β x Q l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St _ (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' x)
  subst hc
  obtain ⟨hs, hb⟩ := repY_yb_coset_bdd H c Q
  set w := (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) Q).symm (repY (A.yb c)) with hw
  have hsl := hs l
  have hbl := hb l
  simp only [Pi.sub_apply] at hsl
  have hq : (qOf Q.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => Q.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ineg : ∀ n : ℕ, IntAt Q.1 (-((qOf Q.1 : t.X.E) ^ n)) := fun n => by
    simpa using IntAt.coe Q.1 (-((qOf Q.1 : 𝓞 t.X.E) ^ n))
  by_cases hP : Q.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ 1 * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ 1 * w l + (-((qOf Q.1 : t.X.E) ^ 1)) *
          (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      simp only [pow_zero, inv_one, one_mul]
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg 1) hsl)
  · simp only [hP, if_false] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ (t.cst μ).M * w l + (-((qOf Q.1 : t.X.E) ^ (2 * (t.cst μ).M))) *
          (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      field_simp
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg _) hsl)

end GlobalTheory.TwU
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mu_det_rat_y_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ k < D.R.m, ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → muT (k + 1) (Matrix.GeneralLinearGroup.det x.1) = muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) * (((t.O u μ).mt (k + 1) ((t.O u μ).dt i c) : ℂˣ) : ℂ) * muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) ≠ 0 ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ≠ 0) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT H k hk i hi c x γ _ κ e
  have hJ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi
  have hyU : ((St i hi).y c).1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((St i hi).y c).2
  have hκU : κ.1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    ((((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2).1
  have hγU : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    have e' : ratA D.host.F γ = x.1 * κ.1⁻¹ * (((St i hi).y c).1)⁻¹ := by rw [e]; group
    rw [e']
    exact mul_mem (mul_mem x.2 (inv_mem hκU)) (inv_mem hyU)
  have dγ := det_mem_normOne_of_mem_unitaryPoints hJ hγU
  have dy := det_mem_normOne_of_mem_unitaryPoints hJ hyU
  have dκ := det_mem_normOne_of_mem_unitaryPoints hJ hκU
  refine ⟨?_, H.mu_ne hk dγ, H.mu_ne hk dκ⟩
  rw [e, map_mul, map_mul, (H.mu_mul k hk).2 _ (mul_mem dγ dy) _ dκ, (H.mu_mul k hk).2 _ dγ _ dy, H.mu_cls k hk i hi c]

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.finiteAdele_iso_component_zero_of_infinitely_divisible : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  first | exact @GlobalTheory.TwV.Xc.adIso_comp_zero_of_div | exact GlobalTheory.TwV.Xc.adIso_comp_zero_of_div | (intros; apply GlobalTheory.TwV.Xc.adIso_comp_zero_of_div <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

theorem _root_.GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence : ∀ {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ) (g : Sp X.E N ≃ₗ[X.E] Sp X.E N), (∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ * (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) → ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) := by
  first | exact @GlobalTheory.SeamCong.cong_seam | exact GlobalTheory.SeamCong.cong_seam | (intros; apply GlobalTheory.SeamCong.cong_seam <;> assumption)
end
