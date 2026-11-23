module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeZeroOfNotMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle022
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle030
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle029
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle001
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019

@[expose] public section

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def gramK (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) : Matrix κ κ K := Matrix.of fun i j => h (b i) (b j)

theorem form_repr (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (x y : V) :
    h x y = star (b.equivFun x) ⬝ᵥ (gramK h b *ᵥ b.equivFun y) := by
  calc h x y = h (∑ i, b.equivFun x i • b i) (∑ j, b.equivFun y j • b j) := by
        rw [b.sum_equivFun x, b.sum_equivFun y]
    _ = ∑ i, ∑ j, star (b.equivFun x i) * (b.equivFun y j * h (b i) (b j)) := by

        simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
        simp only [dotProduct, mulVec, Pi.star_apply, gramK, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramK_conjTranspose {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (b : Basis κ K V) :
    (gramK h b)ᴴ = gramK h b := by
  ext i j
  exact hs.eq (b j) (b i)

theorem smul_basis_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) {a : K} (ha : a ∈ SP K 𝔭)
    (i : κ) : a • b i ∈ locF 𝔭 (spanO b) := by
  obtain ⟨t, ht, z, e⟩ := (mem_SP (𝔭 := 𝔭) (a := a)).mp ha
  refine (mem_locF 𝔭 _ _).2 ⟨t, ht, ?_⟩
  rw [← algebraMap_smul K (ι t), smul_smul, ← e, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_locF_iff_repr {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (x : V) :
    x ∈ locF 𝔭 (spanO b) ↔ ∀ i, b.equivFun x i ∈ SP K 𝔭 := by
  constructor
  · intro hx i
    obtain ⟨t, ht, h1⟩ := (mem_locF 𝔭 _ _).1 hx
    have h2 : ι t • x = _ := coe_eq_sum b ⟨_, h1⟩
    generalize crd b ⟨_, h1⟩ = c at h2
    refine mem_SP.2 ⟨t, ht, c i, ?_⟩
    have h3 := congrArg (fun v => b.equivFun v i) h2

    simp only [← algebraMap_smul K (ι t), map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
    Basis.equivFun_self, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h3
    exact h3.symm
  · intro hx
    rw [← b.sum_equivFun x]
    exact Submodule.sum_mem _ fun i _ => smul_basis_mem b (hx i) i

theorem mem_smul_locF_iff_repr {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ) (x : V) :
    x ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) ↔ ∀ i, InP 𝔭 k (b.equivFun x i) := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y hy =>
      intro i
      rw [← algebraMap_smul K r, map_smul, Pi.smul_apply, smul_eq_mul]
      exact (inP_jK hr).mul (l := 0) ((mem_locF_iff_repr b y).1 hy i)
    | add y _ z _ hy hz =>
      intro i
      rw [map_add (f := _)]
      exact (hy i).add (hz i)
  · intro hx
    rw [← b.sum_equivFun x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨t, ht, z, hz, e⟩ := hx i
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    have h1 : (jK (ι t))⁻¹ ∈ SP K 𝔭 := mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ ht0]⟩
    have h2 : b.equivFun x i • b i = z • ((jK (ι t))⁻¹ • b i) := by
      rw [← algebraMap_smul K z, smul_smul, e]
      congr 1
      field_simp
    rw [h2]
    exact Submodule.smul_mem_smul hz (smul_basis_mem b h1 i)

theorem equivFun_toLin (b : Basis κ K V) (G : Matrix κ κ K) (x : V) :
    b.equivFun (Matrix.toLin b b G x) = G *ᵥ b.equivFun x := by
  have := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b G) x
  rw [LinearMap.toMatrix_toLin] at this
  funext i
  exact (congrFun this i).symm

def equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin b b G) (Matrix.toLin b b G')
    (by rw [← Matrix.toLin_mul, hG, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, mul_eq_one_comm.1 hG, Matrix.toLin_one])

theorem equivFun_equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_toLin b G x

theorem equivFun_equivOfMatrix_symm (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun ((equivOfMatrix b G G' hG).symm x) = G' *ᵥ b.equivFun x := equivFun_toLin b G' x

theorem equivOfMatrix_mem_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (hU : Gᴴ * gramK h b * G = gramK h b) :
    equivOfMatrix b G G' hG ∈ Formalism.HermitianLatticesTheory.isom h := by
  intro x y
  rw [form_repr h b, form_repr h b x y, equivFun_equivOfMatrix, equivFun_equivOfMatrix, form_mulVec, hU]

theorem mulVec_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) {v : κ → K}
    (hv : ∀ i, v i ∈ SP K 𝔭) (i : κ) : (G *ᵥ v) i ∈ SP K 𝔭 :=
  (SP K 𝔭).sum_mem fun j _ => (SP K 𝔭).mul_mem (hG i j) (hv j)

theorem gmap_equivOfMatrix {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (h1 : Ent (SP K 𝔭) G) (h2 : Ent (SP K 𝔭) G') :
    Formalism.HermitianLatticesTheory.gmap (equivOfMatrix b G G' hG) (locF 𝔭 (spanO b)) = locF 𝔭 (spanO b) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_locF_iff_repr]
    intro i
    have : b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_equivOfMatrix b G G' hG x
    show b.equivFun (equivOfMatrix b G G' hG x) i ∈ _
    rw [this]
    exact mulVec_mem h1 ((mem_locF_iff_repr b x).1 hx) i
  · intro x hx
    refine ⟨(equivOfMatrix b G G' hG).symm x, ?_, (equivOfMatrix b G G' hG).apply_symm_apply x⟩
    show _ ∈ locF 𝔭 (spanO b)
    rw [mem_locF_iff_repr]
    intro i
    rw [equivFun_equivOfMatrix_symm]
    exact mulVec_mem h2 ((mem_locF_iff_repr b x).1 hx) i

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section

open NumberField Module Filter Topology


set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem tendsto_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    Tendsto (fun j : ℕ => (ballCount h L ((j : ℝ) ^ 2) : ℝ) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L))) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  obtain ⟨b, hbL, ho⟩ := BallB.exists_orth_basis_mem hK hs hd hL
  have hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
  have hB : Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range b)) :=
    { toIsLattice := BallB.isLattice_span b
      span_eq_top := by
        apply top_unique
        rw [← b.span_eq]
        exact Submodule.span_mono Submodule.subset_span }
  obtain ⟨N, hN, hNx⟩ := LocF.exists_zsmul_le hL.toIsLattice hB
  have hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := BallD.lat_span b
  have hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L := by
    rw [← hlat1]
    intro y hy
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hBL hx, rfl⟩
  have hNy : ∀ y ∈ BallD.lat b L,
      N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := by
    intro y hy
    rw [← hlat1]
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩
  have hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re :=
    fun w i => hd (b i) (b.ne_zero i) w.1.embedding
  obtain ⟨hidx, hT⟩ := BallA.tendsto_card_of_le (μ := MeasureTheory.volume)
    (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy
    (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)
  have hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]
    ring
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    rw [BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]
  have hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
      (BallD.lat b L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hlat1]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)
  have hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [← hidx']; exact hidx
  have hnorm := BallB.normD_mul_relIndex hK hLi b hbL hI0
  have hgdet := BallB.prod_place_gdet hK hs hd b ho
  have hvol := BallD.volume_ballSet hA
  have hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re :=
    Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i
  have hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hI0
  have hND : normD h L ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hgdet] at hnorm
    linarith
  have hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0 := pow_ne_zero _ (vInv_pos K).ne'
  have hlim : MeasureTheory.volume.real (BallD.ballSet h b) *
      ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
        (BallD.lat b L).toAddSubgroup : ℝ) /
      ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L) := by
    rw [hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]
    field_simp
  rw [← hlim]
  refine Tendsto.congr' ?_ hT
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [BallD.card_eq hK ho L hj, hfr]

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_inf_ne_zero {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  rw [IA.card_eq_relIndex h𝔭 hr]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭

theorem card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsFullLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁)
    (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by
  obtain ⟨r₁, hr₁⟩ := IA.exists_pow_smul h𝔭 hM₁.toIsLattice hM₂
  obtain ⟨r₂, hr₂⟩ := IA.exists_pow_smul h𝔭 hM₂.toIsLattice hM₁
  have e₁ := IA.card_eq_relIndex h𝔭 hr₁
  have e₂ := IA.card_eq_relIndex h𝔭 hr₂
  rw [inf_comm (locF 𝔭 M₂) (locF 𝔭 M₁)] at e₂
  have hAB : vd h (M₁ ⊓ locF 𝔭 M₂) 𝔭 = vd h (M₂ ⊓ locF 𝔭 M₁) 𝔭 := by
    rw [← localizedQuotients.vd_locF hF h (M₁ ⊓ locF 𝔭 M₂) h𝔭,
      ← localizedQuotients.vd_locF hF h (M₂ ⊓ locF 𝔭 M₁) h𝔭,
      IA.locF_inf 𝔭 h𝔭.isPrime M₁ M₂, IA.locF_inf 𝔭 h𝔭.isPrime M₂ M₁, inf_comm]
  rw [e₁, e₂, localizedQuotients.vd_locF hF h M₁ h𝔭, localizedQuotients.vd_locF hF h M₂ h𝔭,
    IA.vd_mul hF hK hs hd hM₁ hM₁i hM₂ h𝔭, IA.vd_mul hF hK hs hd hM₂ hM₂i hM₁ h𝔭, hAB]

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace U3

open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup

theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F))
    (k : ℕ) : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← absNorm_eq_card, map_pow, ThirdPropositionSlot.absNorm_extP hK hF, ← pow_mul]

theorem absNorm_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 (ne_bot_of_isMaximal h𝔭))

theorem akCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hvk : vd h L 𝔭 ≤ k) :
    akCount h L 𝔭 k = Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭) *
      normRepCount K (extP K 𝔭 ^ (k - vd h L 𝔭)) 1 1 := by
  obtain ⟨e, he⟩ := exists_isGen hL h1 h𝔭
  obtain ⟨n, hn⟩ := MeanB.exists_val hF hs hLi ⟨e, he.1⟩
  obtain ⟨hv, hv'⟩ := vd_spec hF hd h1 h𝔭 he hn
  generalize vd h L 𝔭 = v at hv hv' hvk ⊢
  have hq := absNorm_pos h𝔭
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Nat.finite_of_card_ne_zero (by
    rw [absNorm_extP_pow hK hF]
    positivity)
  let π : (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - v)) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k v))
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have s1 : akCount h L 𝔭 k =
      Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} := by
    unfold akCount
    refine (Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ (endHom_bijective h𝔭 he k)) fun a => ?_)).symm
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Equiv.ofBijective_apply, endHom_mk, cond_iff hF hs hLi h𝔭 he hn hv hv' hvk b]
    exact normOne_mk_iff hF 𝔭 (k - v) b
  have s2 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (NormOne (extP K 𝔭 ^ (k - v)))
  have s3 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // True} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial),
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), absNorm_extP_pow hK hF,
    absNorm_extP_pow hK hF] at s3
  have s4 : Nat.card π.toAddMonoidHom.ker = Ideal.absNorm 𝔭 ^ (2 * v) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * (k - v)))
    rw [← s3, ← pow_add]
    congr 1
    omega
  rw [s1, s2, s4, card_normOne]

theorem alphaStd_one_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : alphaStd K 𝔭 1 ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    have h0 := absNorm_pos h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := mt Ideal.absNorm_eq_one_iff.1 h𝔭.ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by omega)
  have h3 : (Ideal.absNorm 𝔭 : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h4 : 0 < (Ideal.absNorm 𝔭 : ℝ)⁻¹ := inv_pos.2 (by linarith)
  rw [ThirdPropositionSlot.alphaStd_one]
  unfold etaF
  split_ifs
  · nlinarith
  · nlinarith

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    alphaL h L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * alphaStd K 𝔭 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (absNorm_pos h𝔭).ne'
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (vd h L 𝔭 + 1)] with k hk
  rw [akCount_eq hK hF hs hd hL hLi h1 h𝔭 (by omega), h1]
  push_cast
  rw [ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 (by omega), eq_div_iff (pow_ne_zero _ hq)]
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ (k - vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (k * 1 ^ 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [one_pow, mul_one]
    omega
  linear_combination (-alphaStd K 𝔭 1) * e1

end U3

theorem localFactor_rank_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    lamP h L 𝔭 = 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (U3.absNorm_pos h𝔭).ne'
  unfold lamP
  rw [U3.alphaL_eq hK hF hs hd hL hLi h1 h𝔭, h1, one_mul, mul_comm]
  exact div_self (mul_ne_zero (pow_ne_zero _ hq) (U3.alphaStd_one_ne_zero h𝔭))

end Formalism.HermitianLattices.Ext.L3
end
end
